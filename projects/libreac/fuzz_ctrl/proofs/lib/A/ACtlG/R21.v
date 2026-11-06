(* lib/A/ACtlG/R21.v -- the GLUE of stage seg_R21 of fuzz_ctrl image A's walk of LLVMFuzzerTestOneInput.
   Owner: a Theorem Labs lane (single writer of this file).  rule 24: no function proved (kind: segment lemma).

   WHAT IS PROVED.  `glue_seg_R21` is, text for text, ACtl.v's Section Ctl hypothesis seg_R21 (ACtl.v a3c6b7b35017
   :567-568): from the cut at 0x815cc at turn S b, the cut at 0x81ac0 and the cut at 0x81ac8, the cut at 0x81924 at
   turn b.  The three runs it is proved from are a Theorem Labs lane's footprint runs of the stage:
     - r21_latch_next_F  (Seg/R21F.v): b <= 5, the eight shadow stores of the round-trip latch, back to 0x815cc;
     - r21_latch_last_F  (Seg/R21F.v): b = 6, the same stores, through to the tail head 0x81990;
     - r21_tail_pre_Fs   (Seg/R21Fs.v, THIS LANE, the narrowed twin of a Theorem Labs lane's r21_tail_pre_F, pinned to it by
       constr_eq in r21_tail_pre_F_of_Fs_verbatim): the tail's reads, to either the exit 0x81ac8 (no name to
       compare) or the call to __wrap_strcmp at 0x81abc.
   r21_tail_post_F is the EMPTY stretch at the return pc 0x81ac0 and is not used: the strcmp rule's continuation is
   the return address itself, which is the exit cut (glue-pattern G4, split points).

   THE SPLIT POINT (a Theorem Labs lane 00:45Z).  strcmp_wrap has no `_F` in this tree, so the tail run is SPLIT at the call.
   The callee's fact is a Theorem Labs lane's astrcmp_realizes at 0x42964 (lib/Reusable/AStrcmpDef.v), now the PROVED theorem
   A.Rt.Strcmp.ctrl_strcmp_tramp (lib/A/Rt/Strcmp.v (at head lib/A/Rt/Strcmp.v:467), taken by path from a working branch faf0dd1d3b0),
   cited as the lemma H_strcmp with its body; r21g_aj_strcmp_at puts it in journal form, in the shape of the
   core's aj_bcmp_at (YCbq.v:2062-2110).  strcmp itself is NOT re-proved here.  The guarded reads of the source
   (the row word at mr + 280 and the record byte at S5 + 20, read only when h <> 0) stay guarded, in the run, in the
   narrowed stretch and in the rng rows.

   SECTION HYPOTHESES, all named, with what each becomes:
     LAWS, TFIB_SYMS            ACtl.v's own Section hypotheses, passed down.
     RELRO_CAT                  ACtl.v's own Section hypothesis too, its text verbatim (ACtl.v a3c6b7b35017:205): the
                                catalogue [CAT, CAT + CAT_N * CAT_ROW) (11 * 296 = 3256 bytes) lies in ctl_base's
                                read-only span [RLO, RHI).  Its segment is WRITABLE, so ro_agree does not cover it;
                                the core's only source is arodata_okS.
     H_strcmp                   no longer a hypothesis: the lemma H_strcmp, by A.Rt.Strcmp.ctrl_strcmp_tramp B LAWS
                                TFIB_SYMS (its body is astrcmp_realizes segs B 0x42964 unfolded).
   ROUTE (C), a working branch 1899bed1aee: ctl_from's runtime premise is A.ACtlRtC.ctl_rt_C B ly3 S3 mem3 (ACtlCut.v:243).
   The three runs and the strcmp rule take no shadow_rw premise; the stage's own keeps r21g_ctlrt_munch (the latch's
   eight shadow stores) and r21g_ctlrt_view (the strcmp call) carry ctl_rt_C's two regions (cut_shadow B ly3 S3,
   img_shadow) at the same state; r21g_str_facts reads only its ro_agree part.  No VIS0 / OWNED_RO.
   The catalogue names' shadow (a row name is range_addressable and its shadow hull visible, at every state with AR)
   was the named hypothesis NAME_SHADOW; it is now PROVED here (r21g_name_shadow) from AR's own facts: the record
   AF0m's shadow const rows (am_const under TFIB_SYMS) and zero-shadow ranges (LAWS' al_zshadow).  The base's
   corrected ctl_gshadow_of_AR facts (A.ProgWorldShadow) are not used: they give AsanRT.addressable over the raw
   memory, not these view-level facts.
   Kit.v's kit_wx / kit_segs_low / kit_frac_move are cited from A.ACtlG.Kit (no copies).
   The six twin modules are named only as `K11.n` / `K1b.n` (Module aliases of the CORE copies) and every other core
   module as `lib.Reusable.X.n`.  Every ajournal and sink-taking constant carries (SK := A.AE2k.tfib_sink_head).
   No frame-route identifier appears in the statement; the proof cites Seg/R21.v's byte lemmas and B3Rtm's model
   facts, which are Qed-closed and reached through the `_F` files' own closure. *)

From Stdlib Require Import ZArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
(* The core's Reusable modules by their EXPLICIT path (porter a Theorem Labs lane 04:24Z; stage gate a Theorem Labs lane 05:00Z): six
   of them (YI04 YI16 YK11 YK1b YM05 YO09) also exist as lib/A/Reusable, lib/B/Reusable and lib/U/Reusable copies. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK1b YM05 YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YA0n YA0nR YG0f YG01 YG0d YC5d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0n YG0v YK04 YG00 YE01 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YConstIn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.AB1v A.AE2k A.Img0 A.AsanRT A.ACtlK A.ACfn A.AF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlCut A.ACtlCutP A.ProgBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ProgWorldVisFrame A.ProgWorldVisWin.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF Regs6ss Mem Frame PropExec.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.Lib Require MState Step Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.SlotModel A.Prog.strcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.R21 A.Prog.Seg.R21F A.Prog.Seg.R21Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.Prog.Seg.B3Rtm A.Prog.Seg.Tac_rt2_b2.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Prog.RcSynth Prog.RcEmit Prog.RcIdentModel Prog.RcDecl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ACtlG.Kit.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ACtlRtC A.Rt.Strcmp.
Import ListNotations.
Local Open Scope Z_scope.

(* The core's segment list, as ACtlCut.v:74 and ACtl.v:163 bind it. *)
Local Notation segs := A.AB1v.tfibsegs.

(* The two twin modules this file names, in the allowed `M.n` form (porter a Theorem Labs lane 04:24Z): the CORE copies. *)
Module K11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK11.
Module K1b := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YK1b.
Module MEM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module FRM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module ART := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.AsanRT.
Module SM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.SlotModel.
Module R21S := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R21.
Module R21R := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R21F.
Module R21N := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.R21Fs.
Module RTM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.B3Rtm.
(* The binding table of the doubled Lib families this file names (ctrlgate dcb362e1c42f; a Theorem Labs lane 07:0xZ), each alias
   bound by full path to exactly the copy `About` reports in this file's own context at 20a34d3456a: LBMS.MS,
   LBST.rw_cells and LBCE.* bind image A's copies A.Bz.Lib.* (the copies ACtlCutP's cut bodies are stated
   in); lib.Lib.PropExec.seg_rom binds the core copy; the bare stdpp.bitvector.definitions.Z_to_bv_bv_unsigned binds stdpp's lemma. *)
Module LBMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.Lib.MState.
Module LBST := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.Lib.Step.
Module LBCE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.Lib.Cells.

(* ---------------------------------------------------------------------------------------------------------
   1. Pure facts about the latch's shadow window [S(fr) + 296, S(fr) + 313). *)

Definition r21g_win (fr : Z) : list FRM.ivl := [(ART.shadow_addr fr + 296, ART.shadow_addr fr + 313)].

(* A shadow byte of the window is the shadow of a frame byte in [fr + 2368, fr + 2504). *)
Lemma r21g_win_shadow : forall fr y, fr mod 8 = 0 -> ~ (fr + 2368 <= y < fr + 2504) ->
  FRM.outside (r21g_win fr) (ART.shadow_addr y).
Proof.
  intros fr y H8 Hy. unfold r21g_win. cbn [FRM.outside]. split; [|exact I]. unfold ART.shadow_addr.
  intros [H1 H2]. apply Hy. apply Z.mod_divide in H8 as [q Hq]; [|lia]. subst fr.
  rewrite Z.div_mul in H1, H2 by lia.
  pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)). lia.
Qed.

(* The window is shadow memory: no application byte (low or high memory) is in it. *)
Lemma r21g_win_app : forall fr x, 0 <= fr -> fr + 4096 <= ART.APPMEM_END ->
  (x < ART.LOWMEM_END \/ ART.HIGHMEM_BEG <= x) -> FRM.outside (r21g_win fr) x.
Proof.
  intros fr x H0 H1 Hx. unfold r21g_win. cbn [FRM.outside]. split; [|exact I].
  unfold ART.shadow_addr, ART.ASAN_K, ART.APPMEM_END, ART.LOWMEM_END, ART.HIGHMEM_BEG in *.
  pose proof (Z.div_pos fr 8 H0 ltac:(lia)) as D0.
  assert (D1 : (fr + 313 * 8) / 8 <= 0x800000000000 / 8) by (apply Z.div_le_mono; lia).
  rewrite Z.div_add in D1 by lia. change (0x800000000000 / 8) with 0x100000000000 in D1. lia.
Qed.

(* A shadow_rw_on region across a write confined to [lo, hi) whose bytes stay present and writable. *)
Lemma r21g_srwon_munch : forall (P : Z -> Prop) lo hi (m m' : word -> option byte),
  A.ShadowRwOn.shadow_rw_on P m -> FRM.munch [(lo, hi)] m m' -> FRM.stk A.Img0.rsegs m' lo hi ->
  A.ShadowRwOn.shadow_rw_on P m'.
Proof.
  intros P lo hi m m' Hs MU ST a HP Hin.
  assert (Ha : 0 <= a < 2 ^ 64) by (unfold ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END,
    ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG in Hin; lia).
  destruct (Z_lt_le_dec a lo) as [H1 | H1]; [| destruct (Z_lt_le_dec a hi) as [H2 | H2]].
  2: { exact (proj2 (proj2 ST) a (conj H1 H2)). }
  all: assert (E : m' (MEM.wa a) = m (MEM.wa a))
         by (apply MU; rewrite MEM.wa_unsigned by lia; cbn [FRM.outside]; split; [lia | exact I]).
  all: pose proof (Hs a HP Hin) as HH; unfold wview, MEM.mrd in HH |- *; rewrite E; exact HH.
Qed.

(* ctl_rt_C (route C) across a write confined to [lo, hi) above the image, whose bytes stay present and writable:
   the state (ly, S) is unchanged, so both regions carry over. *)
Lemma r21g_ctlrt_munch : forall (B : lib.Reusable.YG0f.asyms) ly (S : lib.Reusable.YG00.astate) lo hi
    (m m' : word -> option byte),
  A.ACtlRtC.ctl_rt_C B ly S m -> FRM.munch [(lo, hi)] m m' -> FRM.stk A.Img0.rsegs m' lo hi -> 0x5fe000 <= lo ->
  A.ACtlRtC.ctl_rt_C B ly S m'.
Proof.
  intros B ly S lo hi m m' (Hc & Hcut & Himg & Hr) MU ST Hlo.
  assert (KB : forall a bs, MEM.bytes_at A.Img0.rsegs m a bs -> a + Z.of_nat (length bs) <= lo ->
                 MEM.bytes_at A.Img0.rsegs m' a bs).
  { intros a bs Hb Hl. apply (FRM.bytes_at_transport _ [(lo, hi)] m m' a bs Hb MU). cbn. split; [left; lia | exact I]. }
  split; [|split; [|split]].
  - unfold A.ACtlK.asan_cells_at, ART.asan_cells in *.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat match goal with |- _ /\ _ => split end;
      (apply KB; [eassumption|]);
      rewrite ?MEM.length_le8, ?MEM.length_le4; cbn [length Z.of_nat Pos.of_succ_nat];
      unfold ART.CELL_K, ART.GOT_CELL_K, ART.INITED, ART.REPLACE, ART.GOT_REPLACE, ART.UAR, ART.GOT_UAR,
        ART.CANPOISON, ART.HIEND, ART.GOT_HIEND, ART.MIDBEG, ART.GOT_MIDBEG, ART.MIDEND, ART.GOT_MIDEND,
        ART.REAL_MEMCPY, ART.REAL_MEMSET, ART.GOT_REAL_MEMSET; lia.
  - exact (r21g_srwon_munch _ lo hi m m' Hcut MU ST).
  - exact (r21g_srwon_munch _ lo hi m m' Himg MU ST).
  - unfold A.ACtlK.ro_agree_at in *.
    apply (R21S.r21_ro_keep m m' [(lo, hi)] Hr MU).
    intros a Ha. pose proof (R21S.r21_ro_lt a Ha). cbn [FRM.outside]. split; [lia | exact I].
Qed.

(* A spill's own base is the base A that register 9 holds, when A + off + 8 fits in 64 bits. *)
Lemma r21g_spill_A : forall regs m off v A,
  ACtlCut.rgv regs 9 A -> 0 <= A -> 0 <= off -> A + off + 8 <= 2 ^ 64 ->
  ACtlCutP.spill regs m off v -> ACtlCutP.q64 m (A + off) v.
Proof.
  intros regs m off v A HA HA0 Hoff HAb (A0 & HA0' & Hq). unfold ACtlCut.rgv in *. rewrite HA in HA0'.
  pose proof Hq as Hq'. unfold ACtlCutP.q64 in Hq'. apply MEM.bytes_at_bound in Hq'.
  rewrite MEM.length_le8 in Hq'. cbn [Z.of_nat Pos.of_succ_nat] in Hq'.
  assert (E : A0 = A).
  { apply (f_equal bv_unsigned) in HA0'. rewrite !Z_to_bv_unsigned in HA0'. unfold bv_wrap in HA0'.
    change (bv_modulus 64) with (2 ^ 64) in HA0'.
    rewrite (Z.mod_small A) in HA0' by lia. Z.div_mod_to_equations. nia. }
  subst A0. exact Hq.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   1b. The strcmp rule's two definitions, AStrcmpDef.v:36 / :39-44 (a Theorem Labs lane; relocated as this unit's
   lib/Reusable/AStrcmpDef.v), verbatim over this unit's core names; H_strcmp below states the rule with its body
   and is proved by A.Rt.Strcmp.ctrl_strcmp_tramp (conversion through these two definitions). *)
Definition r21g_strcmp_res (c1 c2 : Z) : Z := if c1 =? c2 then 0 else if c1 <? c2 then -1 else 1.
Definition r21g_str_meet (W : lib.Reusable.YA0n.world segs) (mem : word -> option byte) (x y k c1 c2 : Z) : Prop :=
  0 <= k /\
  (forall i, 0 <= i < k -> exists b, lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem (x + i) = Some b /\
                                     lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem (y + i) = Some b /\ b <> 0) /\
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem (x + k) = Some c1 /\
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem (y + k) = Some c2 /\
  (c1 <> c2 \/ c1 = 0).

(* Two readings of the same register agree, inside the 64-bit range. *)
Lemma r21g_rgv_uniq : forall regs r A A', ACtlCut.rgv regs r A -> ACtlCut.rgv regs r A' ->
  0 <= A < 2 ^ 64 -> 0 <= A' < 2 ^ 64 -> A' = A.
Proof.
  intros regs r A A' H H' HA HA'. unfold ACtlCut.rgv in *. rewrite H in H'.
  apply (f_equal bv_unsigned) in H'. rewrite !Z_to_bv_unsigned in H'. unfold bv_wrap in H'.
  change (bv_modulus 64) with (2 ^ 64) in H'. rewrite !Z.mod_small in H' by lia. symmetry. exact H'.
Qed.

(* ---------------------------------------------------------------------------------------------------------
   2. The stage. *)
Section GlueR21.

Context {fx : K11.FPState} {rc : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YM05.RunCeil}
        {LS : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable.YO09.lib_shape}.
Variable B : lib.Reusable.YG0f.asyms.
Variable MT : lib.Reusable.YC5d.ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.

(* ACtl.v's notation block (ACtl.v a3c6b7b35017 :257, :261-262, :277, :292-294), verbatim. *)
Local Notation ix_cut := ACtlCut.ix_cut.
Local Notation CF POST X :=
  (ACtlCut.ctl_from (SK := A.AE2k.tfib_sink_head) B MT XM_LIB RLO RHI [] POST X).
Local Notation C_A815cc_at := (ACtlCutP.C_A815cc_at B).
Local Notation C_A81924_at := (ACtlCutP.C_A81924_at B).
Local Notation C_A81ac0 := (ACtlCutP.C_A81ac0 B).
Local Notation C_A81ac8 := (ACtlCutP.C_A81ac8 B).

(* The core's AR laws (YCbq.v:207; ACtl.v a3c6b7b35017:210). *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws segs B.
(* the core's bundle law for B, as ACtl.v a3c6b7b35017:225 states it *)
Hypothesis TFIB_SYMS : A.AF0m.CtrlTSyms B.
(* the catalogue lies in the read-only span the core's arodata_okS speaks of: ACtl.v a3c6b7b35017:205, verbatim *)
Hypothesis RELRO_CAT : RLO <= A.Prog.SlotModel.CAT /\ A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_N * A.Prog.SlotModel.CAT_ROW <= RHI.

(* AStrcmpDef.v:46-66, astrcmp_realizes segs B 0x42964 (ctrl A's __wrap_strcmp trampoline, strcmp_wrap_c.v:8),
   stated with its body; PROVED by a Theorem Labs lane's ctrl_strcmp_tramp (A/Rt/Strcmp.v (at head lib/A/Rt/Strcmp.v:467; from a working branch faf0dd1d3b0)). *)
Lemma H_strcmp :
  forall ly S (W : lib.Reusable.YA0n.world segs) regs mem md x y k c1 c2,
  lib.Reusable.YG0d.ecall_pre segs B ly S W regs mem md ->
  lib.Reusable.YG0f.ly_stk_lo ly + 2 * lib.Reusable.YG0d.ESTACK <= lib.Reusable.YG0d.spZ regs ->
  (forall a, lib.Reusable.YG0d.spZ regs - 2 * lib.Reusable.YG0d.ESTACK <= a < lib.Reusable.YG0d.spZ regs ->
     lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem a) ->
  K11.getr regs 10 = lib.Reusable.YG0d.w64 x -> K11.getr regs 11 = lib.Reusable.YG0d.w64 y -> 0 < x -> 0 < y ->
  k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 -> y + k + 1 <= 2 ^ 63 ->
  r21g_str_meet W mem x y k c1 c2 ->
  lib.Reusable.YG0d.src_ok segs W regs mem x (k + 1) -> lib.Reusable.YG0d.src_ok segs W regs mem y (k + 1) ->
  (forall a, x <= a <= x + k ->
     ~ (lib.Reusable.YG0d.spZ regs - 2 * lib.Reusable.YG0d.ESTACK <= a < lib.Reusable.YG0d.spZ regs)) ->
  (forall a, y <= a <= y + k ->
     ~ (lib.Reusable.YG0d.spZ regs - 2 * lib.Reusable.YG0d.ESTACK <= a < lib.Reusable.YG0d.spZ regs)) ->
  lib.Reusable.YG0d.amem_range x (k + 1) -> lib.Reusable.YG0d.amem_range y (k + 1) ->
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem)
    lib.Reusable.YG0f.SHADOW_OFF x (k + 1) ->
  lib.Reusable.YG0d.shadow_hull_vis (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem) x (k + 1) ->
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem)
    lib.Reusable.YG0f.SHADOW_OFF y (k + 1) ->
  lib.Reusable.YG0d.shadow_hull_vis (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem) y (k + 1) ->
  lib.Reusable.YA0n.SRr segs W (lib.Reusable.YG0d.cfg_at segs 0x42964 regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = lib.Reusable.YG0d.cfg_at segs (lib.Reusable.YG0d.raZ regs) regs' mem' md' /\
       lib.Reusable.YG0n.AR segs B ly S W mem' md' /\ lib.Reusable.YG0d.aregs_preserved regs regs' /\
       lib.Reusable.YK04.same_but_materialized md md' /\
       K11.getr regs' 10 = lib.Reusable.YG0d.w64 (r21g_strcmp_res c1 c2) /\
       (forall a, 0 <= a < 2 ^ 64 ->
          ~ (lib.Reusable.YG0d.spZ regs - 2 * lib.Reusable.YG0d.ESTACK <= a < lib.Reusable.YG0d.spZ regs) ->
          lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem' a =
          lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem a) /\
       (forall a, lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem a ->
          lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem' a)).
Proof. exact (A.Rt.Strcmp.ctrl_strcmp_tramp B LAWS TFIB_SYMS). Qed.

(* The catalogue names' shadow (formerly the named Section hypothesis NAME_SHADOW), PROVED from AR's own facts.  Each
   row name with an identity record is a 32-byte-aligned asan global of at most 9 bytes, so its shadow is one 8-byte
   shadow block.  Each byte of that block is either a row of the record's shadow const table A.AF0m.Tfib_const_shadow
   (AF0m.v:2167: the partial last granule, value n mod 8, and the 0xf9 redzone bytes), which AR's am_const
   (YG0n.v:211) gives under TFIB_SYMS' ts_const (AF0m.v:3002), or a byte of a range of A.AF0m.Tfib_zero_shadow
   (AF0m.v:2955: the full granules), which LAWS' al_zshadow (YG0d.v:435-438) gives under ts_zsh (AF0m.v:3006).
   range_addressable follows by YG0v.block_shadow_range, shadow_hull_vis byte by byte.  Each row's name address and
   length are computed (vm_compute), as B3Rtm.a_row_facts computes them. *)
Lemma r21g_ns_row : forall ly S (W : lib.Reusable.YA0n.world segs) m md s v,
  lib.Reusable.YG0n.AR segs B ly S W m md ->
  existsb (lib.Reusable.YConstIn.row_eqb (lib.Reusable.YG0f.z1 (lib.Reusable.YG0f.ANum s) v))
    A.AF0m.Tfib_const_shadow = true ->
  0 <= v < 256 ->
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m s = Some v.
Proof.
  intros ly S W m md s v (M & _) Hb Hv.
  pose proof (lib.Reusable.YG0n.am_const _ _ _ _ M) as C.
  rewrite (A.AF0m.ts_const B TFIB_SYMS ly), Forall_forall in C.
  specialize (C _ (in_or_app _ _ _ (or_intror (in_or_app _ _ _
                 (or_intror (lib.Reusable.YConstIn.existsb_row_In _ _ Hb)))))).
  unfold lib.Reusable.YG0f.cell_holds, lib.Reusable.YG0f.z1, lib.Reusable.YG0f.c1 in C.
  cbn [lib.Reusable.YG0f.c_at lib.Reusable.YG0f.c_w lib.Reusable.YG0f.c_val lib.Reusable.YG0f.aeval] in C.
  specialize (C 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in C. rewrite Z.add_0_r in C.
  rewrite C. f_equal.
  unfold lib.Reusable.YG0f.le_byte. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. exact Hv.
Qed.

Lemma r21g_ns_zero : forall ly S (W : lib.Reusable.YA0n.world segs) m md s,
  lib.Reusable.YG0n.AR segs B ly S W m md ->
  existsb (fun r => (lib.Reusable.YG0f.SHADOW_OFF + fst r / 8 <=? s) &&
                    (s <? lib.Reusable.YG0f.SHADOW_OFF + fst r / 8 + snd r / 8)) A.AF0m.Tfib_zero_shadow = true ->
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m s = Some 0.
Proof.
  intros ly S W m md s HAR Hb. apply existsb_exists in Hb as (r & Hr & Hb).
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  pose proof (lib.Reusable.YG0d.al_zshadow _ _ LAWS ly S W m md r HAR) as Hz.
  specialize (Hz ltac:(unfold lib.Reusable.YG0n.zero_shadow_ranges; right;
                       rewrite (A.AF0m.ts_zsh B TFIB_SYMS); exact Hr)).
  specialize (Hz (s - (lib.Reusable.YG0f.SHADOW_OFF + fst r / 8)) ltac:(lia)).
  unfold lib.Reusable.YG0v.shadow_of_addr in Hz.
  replace (lib.Reusable.YG0f.SHADOW_OFF + fst r / 8 + (s - (lib.Reusable.YG0f.SHADOW_OFF + fst r / 8))) with s
    in Hz by lia.
  exact Hz.
Qed.

(* One shadow byte of a name's block: a zero-shadow byte, or a const row of value 0xf9 or 1..7; then `fin`. *)
Local Ltac r21g_ns_cell HAR fin :=
  first [ rewrite (r21g_ns_zero _ _ _ _ _ _ HAR) by (vm_compute; reflexivity); fin
        | rewrite (r21g_ns_row _ _ _ _ _ _ 0xf9 HAR) by (first [vm_compute; reflexivity | lia]); fin
        | rewrite (r21g_ns_row _ _ _ _ _ _ 1 HAR) by (first [vm_compute; reflexivity | lia]); fin
        | rewrite (r21g_ns_row _ _ _ _ _ _ 2 HAR) by (first [vm_compute; reflexivity | lia]); fin
        | rewrite (r21g_ns_row _ _ _ _ _ _ 3 HAR) by (first [vm_compute; reflexivity | lia]); fin
        | rewrite (r21g_ns_row _ _ _ _ _ _ 4 HAR) by (first [vm_compute; reflexivity | lia]); fin
        | rewrite (r21g_ns_row _ _ _ _ _ _ 5 HAR) by (first [vm_compute; reflexivity | lia]); fin
        | rewrite (r21g_ns_row _ _ _ _ _ _ 6 HAR) by (first [vm_compute; reflexivity | lia]); fin
        | rewrite (r21g_ns_row _ _ _ _ _ _ 7 HAR) by (first [vm_compute; reflexivity | lia]); fin ].

(* One name, at its computed address a and length l: block_shadow by cells, then the hull's 8 bytes. *)
Local Ltac r21g_ns_name HAR :=
  match goal with
  | |- lib.Reusable.YG0v.range_addressable _ _ ?a ?l /\ _ =>
      split;
      [ apply (lib.Reusable.YG0v.block_shadow_range _ _ a l a l); [ | lia | lia ];
        split; [vm_compute; reflexivity|]; split; [lia|];
        let k := fresh "k" in let Hk := fresh "Hk" in let Ek := fresh "Ek" in
        intros k Hk; assert (Ek : k = 0 \/ k = 1) by lia;
        destruct Ek as [-> | ->];
        first [ exfalso; lia | r21g_ns_cell HAR ltac:(vm_compute; reflexivity) ]
      | let s := fresh "s" in let Hs := fresh "Hs" in let j := fresh "j" in let Hj := fresh "Hj" in
        let Ej := fresh "Ej" in
        intros s Hs;
        let lo := eval vm_compute in (lib.Reusable.YG0f.shadow_addr a / 8 * 8) in
        assert (Ej : exists j, 0 <= j < 8 /\ s = lo + j)
          by (exists (s - lo); unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF in Hs; lia);
        destruct Ej as (j & Hj & ->); clear Hs;
        assert (Ej : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia;
        destruct Ej as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
        r21g_ns_cell HAR ltac:(discriminate) ]
  end.

Lemma r21g_name_shadow : forall ly S (W : lib.Reusable.YA0n.world segs) m md,
  lib.Reusable.YG0n.AR segs B ly S W m md ->
  forall i, 0 <= i < 11 -> Prog.RcEmit.em_hid (A.Prog.SlotModel.rowb i) <> 0 ->
  let nm := Prog.RcSynth.rname (A.Prog.SlotModel.rowb i) in
  let n := Z.of_nat (length (A.Prog.SlotModel.img_cstr nm 16)) in
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m)
    lib.Reusable.YG0f.SHADOW_OFF nm n /\
  lib.Reusable.YG0d.shadow_hull_vis (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m) nm n.
Proof.
  intros ly S W m md HAR i Hi Hh. cbv zeta.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  clear Hi.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
    (* the rows without an identity record (em_hid = 0) *)
    try (exfalso; apply Hh; vm_compute; reflexivity);
    clear Hh;
    (* the row's name address and length, computed *)
    match goal with
    | |- context [Prog.RcSynth.rname (A.Prog.SlotModel.rowb ?k)] =>
        let a := eval vm_compute in (Prog.RcSynth.rname (A.Prog.SlotModel.rowb k)) in
        let l := eval vm_compute in
          (Z.of_nat (length (A.Prog.SlotModel.img_cstr (Prog.RcSynth.rname (A.Prog.SlotModel.rowb k)) 16))) in
        let En := fresh "En" in let Ea := fresh "Ea" in
        assert (En : Z.of_nat (length (A.Prog.SlotModel.img_cstr (Prog.RcSynth.rname (A.Prog.SlotModel.rowb k)) 16))
                     = l) by (vm_compute; reflexivity);
        assert (Ea : Prog.RcSynth.rname (A.Prog.SlotModel.rowb k) = a) by (vm_compute; reflexivity);
        rewrite En, Ea; clear En Ea
    end;
    r21g_ns_name HAR.
Qed.

(* ---- the three runs, at the canonical start map Regs6ss.mkR_of regs (G3) and with the core's getr ---- *)

Lemma r21g_latch_next_run : forall RNG (regs : bvmap 5 word) (m : word -> option byte) (SH A bz v : Z),
  K11.getr regs 19 = Z_to_bv 64 SH -> K11.getr regs 9 = Z_to_bv 64 A -> K11.getr regs 23 = Z_to_bv 64 bz ->
  0 <= bz <= 5 -> 0 <= SH -> SH + 313 <= A -> A + 136 <= 2 ^ 64 ->
  FRM.stk A.Img0.rsegs m (SH + 296) (SH + 313) ->
  MEM.bytes_at A.Img0.rsegs m (A + 128) (MEM.le8 (Z_to_bv 64 v)) ->
  Lib.ExecF.rng RNG (SH + 296) 17 -> Lib.ExecF.rng RNG (A + 128) 8 ->
  Lib.ExecF.evtF A.Img0.rsegs RNG
    (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
       ms' = LBMS.MS R K11.fp_regs (Z_to_bv 64 0x815cc) K11.fp_csr None m' (K11.seg_rom A.Img0.rsegs) /\
       K11.getr R 2 = K11.getr regs 2 /\ K11.getr R 3 = K11.getr regs 3 /\ K11.getr R 4 = K11.getr regs 4 /\
       K11.getr R 8 = K11.getr regs 8 /\ K11.getr R 9 = K11.getr regs 9 /\ K11.getr R 19 = K11.getr regs 19 /\
       K11.getr R 21 = K11.getr regs 21 /\ K11.getr R 22 = K11.getr regs 22 /\
       K11.getr R 23 = Z_to_bv 64 (bz + 1) /\
       K11.getr R 25 = K11.getr regs 25 /\ K11.getr R 26 = K11.getr regs 26 /\
       K11.getr R 10 = Z_to_bv 64 v /\ K11.getr R 24 = Z_to_bv 64 36 /\
       FRM.munch [(SH + 296, SH + 313)] m m' /\ FRM.wmono A.Img0.rsegs m m' /\
       FRM.stk A.Img0.rsegs m' (SH + 296) (SH + 313))
    (LBMS.MS (Lib.Regs6ss.mkR_of regs) K11.fp_regs (Z_to_bv 64 0x81924) K11.fp_csr None m
       (K11.seg_rom A.Img0.rsegs)).
Proof.
  intros RNG regs m SH A bz v H19 H9 H23 Hb HS0 HSA HA ST HQ G1 G2.
  unfold Lib.Regs6ss.mkR_of.
  eapply Lib.ExecF.evtF_mono.
  - eapply (R21R.r21_latch_next_F RNG) with (SH := SH) (A := A) (bz := bz) (v := v);
      [exact H19 | exact H9 | exact H23 | exact Hb | exact HS0 | exact HSA | exact HA | exact ST | exact HQ
      | exact G1 | exact G2].
  - intros ms' (R & m' & E & P2 & P3 & P4 & P8 & P9 & P19 & P21 & P22 & P23 & P25 & P26 & P10 & P24 & MU & WM & STk).
    exists R, m'. split; [exact E|].
    split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|]. split; [exact P9|].
    split; [exact P19|]. split; [exact P21|]. split; [exact P22|]. split; [exact P23|].
    split; [exact P25|]. split; [exact P26|]. split; [exact P10|]. split; [exact P24|].
    split; [exact MU|]. split; [exact WM | exact STk].
Qed.

Lemma r21g_latch_last_run : forall RNG (regs : bvmap 5 word) (m : word -> option byte) (SH A v : Z),
  K11.getr regs 19 = Z_to_bv 64 SH -> K11.getr regs 9 = Z_to_bv 64 A -> K11.getr regs 23 = Z_to_bv 64 6 ->
  0 <= SH -> SH + 313 <= A -> A + 136 <= 2 ^ 64 ->
  FRM.stk A.Img0.rsegs m (SH + 296) (SH + 313) ->
  MEM.bytes_at A.Img0.rsegs m (A + 128) (MEM.le8 (Z_to_bv 64 v)) ->
  Lib.ExecF.rng RNG (SH + 296) 17 -> Lib.ExecF.rng RNG (A + 128) 8 ->
  Lib.ExecF.evtF A.Img0.rsegs RNG
    (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
       ms' = LBMS.MS R K11.fp_regs (Z_to_bv 64 0x81990) K11.fp_csr None m' (K11.seg_rom A.Img0.rsegs) /\
       K11.getr R 2 = K11.getr regs 2 /\ K11.getr R 3 = K11.getr regs 3 /\ K11.getr R 4 = K11.getr regs 4 /\
       K11.getr R 8 = K11.getr regs 8 /\ K11.getr R 9 = K11.getr regs 9 /\ K11.getr R 19 = K11.getr regs 19 /\
       K11.getr R 21 = K11.getr regs 21 /\ K11.getr R 22 = K11.getr regs 22 /\
       K11.getr R 25 = K11.getr regs 25 /\ K11.getr R 26 = K11.getr regs 26 /\
       FRM.munch [(SH + 296, SH + 313)] m m' /\ FRM.wmono A.Img0.rsegs m m' /\
       FRM.stk A.Img0.rsegs m' (SH + 296) (SH + 313))
    (LBMS.MS (Lib.Regs6ss.mkR_of regs) K11.fp_regs (Z_to_bv 64 0x81924) K11.fp_csr None m
       (K11.seg_rom A.Img0.rsegs)).
Proof.
  intros RNG regs m SH A v H19 H9 H23 HS0 HSA HA ST HQ G1 G2.
  unfold Lib.Regs6ss.mkR_of.
  eapply Lib.ExecF.evtF_mono.
  - eapply (R21R.r21_latch_last_F RNG) with (SH := SH) (A := A) (v := v);
      [exact H19 | exact H9 | exact H23 | exact HS0 | exact HSA | exact HA | exact ST | exact HQ
      | exact G1 | exact G2].
  - intros ms' (R & m' & E & P2 & P3 & P4 & P8 & P9 & P19 & P21 & P22 & P25 & P26 & MU & WM & STk).
    exists R, m'. split; [exact E|].
    split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|]. split; [exact P9|].
    split; [exact P19|]. split; [exact P21|]. split; [exact P22|].
    split; [exact P25|]. split; [exact P26|].
    split; [exact MU|]. split; [exact WM | exact STk].
Qed.

(* A present byte (in the core's sense) is a present, writable byte in ctrl's. *)
Lemma r21g_present_stk : forall (H : word -> bool) (m : word -> option byte) a,
  lib.Reusable.YG0n.apresent H m a ->
  wview A.Img0.rsegs m (MEM.wa a) <> None /\ exists b, MEM.mrd A.Img0.rsegs m (MEM.wa a) = Some b.
Proof.
  intros H m a (_ & b & Hb). unfold wview, MEM.mrd, MEM.wa. rewrite Hb. split; [discriminate | exists b; reflexivity].
Qed.

(* The cut's own frame, from the journal (frames_bounds, AR_frames_law) and the frame law of ctl_from. *)
Lemma r21g_frame : forall cx fr k ly3 S3 (W3 : lib.Reusable.YA0n.world segs) mem3 md3,
  lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  lib.Reusable.YG01.frames S3 = ACtlCut.own6 cx ->
  (forall cid pos, In (cid, pos) (ACtlCut.own6 cx) -> fr = lib.Reusable.YG0f.frame_addr (ACtlCut.c_ly cx) cid pos) ->
  lib.Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr /\ 4096 <= fr /\
  fr + 4096 <= lib.Reusable.YM05.alloc_ceiling /\ lib.Reusable.YG0f.in_app fr 4096 /\ fr mod 32 = 0 /\
  (forall a, fr <= a < fr + 4096 -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W3) mem3 a) /\
  (forall i, 0 <= i < 512 ->
     lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W3) mem3 (lib.Reusable.YG0f.shadow_addr fr + i)).
Proof.
  intros cx fr k ly3 S3 W3 mem3 md3 HJ HF HL.
  pose proof HJ as (HAR & Hly & _).
  assert (Hin : In (6, ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
  assert (Efr : lib.Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr).
  { rewrite (HL 6 (ACtlCut.c_fpos cx) ltac:(left; reflexivity)). unfold lib.Reusable.YG0f.frame_addr.
    destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  assert (E64 : lib.Reusable.YG00.fs_frame_bytes 6 = 4096) by reflexivity.
  destruct (lib.Reusable.YCbq.frames_bounds segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (H4096 & Hceil & Happ).
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) HAR Hin)
    as (H32 & _ & Hb & Hsh).
  rewrite E64, Efr in *.
  split; [reflexivity|]. split; [exact H4096|]. split; [exact Hceil|]. split; [exact Happ|]. split; [exact H32|].
  split.
  - intros a Ha. exact (proj1 (Hb a Ha)).
  - intros i Hi. exact (proj1 (Hsh i ltac:(change (4096 / 8) with 512; lia))).
Qed.

(* The journal across the latch's eight shadow stores: they write only the owned frame's shadow (in_frames). *)
Lemma r21g_latch_journal : forall cx fr k ly3 S3 (W3 : lib.Reusable.YA0n.world segs) mem3 md3 m' md',
  lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k ->
  lib.Reusable.YG0f.frame_addr ly3 6 (ACtlCut.c_fpos cx) = fr -> 0 <= fr ->
  FRM.munch (r21g_win fr) mem3 m' ->
  FRM.stk A.Img0.rsegs m' (ART.shadow_addr fr + 296) (ART.shadow_addr fr + 313) ->
  (forall x : word, lib.Reusable.YA0n.w_H W3 x = true -> m' x = mem3 x) ->
  lib.Reusable.YK04.same_but_materialized md3 md' ->
  lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx)
    (ACtlCut.own6 cx) ly3 S3 W3 m' md' k.
Proof.
  intros cx fr k ly3 S3 W3 mem3 md3 m' md' HJ Efr Hfr0 MU ST Hhid Hsbm.
  eapply (lib.Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with
    (Wr := fun a => ART.shadow_addr fr + 296 <= a < ART.shadow_addr fr + 313); [exact HJ | | | exact Hhid | exact Hsbm |].
  - intros x Hx. unfold lib.Reusable.YK04.mrestrict. destruct (lib.Reusable.YA0n.w_H W3 x); [reflexivity|].
    apply MU. unfold r21g_win. cbn [FRM.outside]. split; [exact Hx | exact I].
  - intros x Hx. unfold lib.Reusable.YK04.mrestrict in *. destruct (lib.Reusable.YA0n.w_H W3 x); [exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x) (ART.shadow_addr fr + 296)) as [L1 | L1];
      [| destruct (Z_lt_le_dec (bv_unsigned x) (ART.shadow_addr fr + 313)) as [L2 | L2]].
    2: { destruct (proj2 (proj2 ST) (bv_unsigned x) (conj L1 L2)) as (_ & b & Hb).
         unfold MEM.mrd, MEM.wa in Hb. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hb.
         destruct (m' x) as [b'|] eqn:E; [discriminate|].
         pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
         assert (Hnimg : ~ lib.Reusable.YG0d.in_img segs (bv_unsigned x)).
         { intros Hi. pose proof (A.ACtlG.Kit.kit_segs_low _ Hi) as Hlow.
           unfold lib.Reusable.YG0f.kLowMemEnd, ART.shadow_addr, ART.ASAN_K in *.
           pose proof (Z.div_pos fr 8 Hfr0 ltac:(lia)). lia. }
         pose proof (lib.Reusable.YCbq.seg_rom_none segs (bv_unsigned x) Rx Hnimg) as Hn.
         rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Hn. change (lib.Lib.PropExec.seg_rom A.Img0.rsegs x = None) in Hn.
         rewrite Hn in Hb. discriminate Hb. }
    all: rewrite (MU x); [exact Hx|]; unfold r21g_win; cbn [FRM.outside]; split; [lia | exact I].
  - intros a Ha. right; right; right. exists 6, (ACtlCut.c_fpos cx). split; [left; reflexivity|]. right.
    unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite Efr.
    change (lib.Reusable.YG00.fs_frame_bytes 6 / 8) with 512.
    unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, ART.shadow_addr, ART.ASAN_K in *. lia.
Qed.

(* ---- memory transport, pointwise: two memories agree (mrd) and keep writability on an address set G ---- *)
Definition r21g_keeps (m m' : word -> option byte) (G : Z -> Prop) : Prop :=
  forall a, G a ->
    MEM.mrd A.Img0.rsegs m' (MEM.wa a) = MEM.mrd A.Img0.rsegs m (MEM.wa a) /\
    (wview A.Img0.rsegs m (MEM.wa a) <> None -> wview A.Img0.rsegs m' (MEM.wa a) <> None).

Lemma r21g_keeps_munch : forall W (m m' : word -> option byte),
  FRM.munch W m m' -> r21g_keeps m m' (fun a => 0 <= a < 2 ^ 64 /\ FRM.outside W a).
Proof.
  intros W m m' MU a (Ha & Ho).
  assert (E : m' (MEM.wa a) = m (MEM.wa a)) by (apply MU; rewrite MEM.wa_unsigned by lia; exact Ho).
  unfold MEM.mrd, wview. rewrite E. split; [reflexivity | exact (fun H => H)].
Qed.

Lemma r21g_keeps_sub : forall m m' (G G' : Z -> Prop), r21g_keeps m m' G -> (forall a, G' a -> G a) ->
  r21g_keeps m m' G'.
Proof. intros m m' G G' H HG a Ha. exact (H a (HG a Ha)). Qed.

Lemma r21g_bytes_keeps : forall m m' G a bs, MEM.bytes_at A.Img0.rsegs m a bs -> r21g_keeps m m' G ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> G (a + i)) -> MEM.bytes_at A.Img0.rsegs m' a bs.
Proof.
  intros m m' G a bs (H0 & H1 & H) HK HG. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (proj1 (HK (a + Z.of_nat i) (HG (Z.of_nat i) ltac:(lia)))). exact (H i Hi).
Qed.

Lemma r21g_q64_keeps : forall m m' G a v, ACtlCutP.q64 m a v -> r21g_keeps m m' G ->
  (forall i, 0 <= i < 8 -> G (a + i)) -> ACtlCutP.q64 m' a v.
Proof.
  intros m m' G a v H HK HG. unfold ACtlCutP.q64 in *. apply (r21g_bytes_keeps m m' G a _ H HK).
  rewrite MEM.length_le8. exact HG.
Qed.

Lemma r21g_addr_keeps : forall m m' G p n, ART.addressable m p n -> r21g_keeps m m' G ->
  (forall i, 0 <= i < n -> G (ART.shadow_addr (p + i))) -> ART.addressable m' p n.
Proof.
  intros m m' G p n (H1 & H2 & H3 & H) HK HG. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  rewrite (proj1 (HK _ (HG i Hi))). exact Hb.
Qed.

Lemma r21g_rwcb_keeps : forall m m' G a n bs,
  LBST.rw_cells A.Img0.rsegs m a [LBCE.CB n bs] -> r21g_keeps m m' G ->
  (forall i, 0 <= i < Z.of_nat n -> G (a + i)) -> LBST.rw_cells A.Img0.rsegs m' a [LBCE.CB n bs].
Proof.
  intros m m' G a n bs ((Hwf & Hb) & Hw) HK HG.
  assert (Hlen : length bs = n) by (destruct Hwf as (Hl & _); exact Hl).
  split; [split; [exact Hwf|]|].
  - apply (r21g_bytes_keeps m m' G a _ Hb HK). intros i Hi.
    cbn [LBCE.cells_bytes LBCE.cbytes] in Hi. rewrite app_nil_r, Hlen in Hi. exact (HG i Hi).
  - destruct Hw as (Hw0 & Hw1 & Hw). split; [exact Hw0|]. split; [exact Hw1|].
    intros i Hi. cbn [LBCE.cells_size LBCE.csize] in Hi.
    exact (proj2 (HK _ (HG i ltac:(lia))) (Hw i ltac:(cbn [LBCE.cells_size LBCE.csize]; lia))).
Qed.

Lemma r21g_spill_keeps : forall m m' G regs regs' off v A,
  ACtlCut.rgv regs 9 A -> 0 <= A -> 0 <= off -> A + off + 8 <= 2 ^ 64 ->
  K11.getr regs' 9 = K11.getr regs 9 -> r21g_keeps m m' G -> (forall i, 0 <= i < 8 -> G (A + off + i)) ->
  ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v.
Proof.
  intros m m' G regs regs' off v A HA HA0 Hoff Hb E9 HK HG HS.
  exists A. split; [unfold ACtlCut.rgv in *; rewrite E9; exact HA|].
  exact (r21g_q64_keeps m m' G _ _ (r21g_spill_A regs m off v A HA HA0 Hoff Hb HS) HK HG).
Qed.

Lemma r21g_PRO_keeps : forall m m' G cx fr regs regs' A,
  ACtlCutP.PRO cx fr regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 312 <= 2 ^ 64 ->
  K11.getr regs' 9 = K11.getr regs 9 -> r21g_keeps m m' G ->
  (forall a, A <= a < A + 312 -> G a) ->
  (forall i, 0 <= i < 6 -> G (ART.shadow_addr (fr + 2624 + i))) ->
  (forall i, 0 <= i < Z.of_nat (length (ACtlCut.c_in cx)) -> G (ACtlCut.c_p cx + i)) ->
  (0 < ACtlCut.c_n cx -> forall i, 0 <= i < ACtlCut.c_n cx -> G (ART.shadow_addr (ACtlCut.c_p cx + i))) ->
  ACtlCutP.PRO cx fr regs' m'.
Proof.
  intros m m' G cx fr regs regs' A HPRO HA HA0 HAb E9 HK HGA HGs HGp HGps.
  destruct HPRO as (P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Pad & Pin & Pg & P184 & P256 & P264 &
    P272 & P32).
  assert (KS : forall off v, 0 <= off <= 304 -> ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v).
  { intros off v Ho Hs. apply (r21g_spill_keeps m m' G regs regs' off v A HA HA0 ltac:(lia) ltac:(lia) E9 HK);
      [|exact Hs].
    intros i Hi. apply HGA. lia. }
  refine (conj (KS 40 _ ltac:(lia) P40) (conj (KS 120 _ ltac:(lia) P120) (conj (KS 136 _ ltac:(lia) P136)
    (conj (KS 160 _ ltac:(lia) P160) (conj (KS 168 _ ltac:(lia) P168) (conj (KS 176 _ ltac:(lia) P176)
    (conj (KS 208 _ ltac:(lia) P208) (conj (KS 248 _ ltac:(lia) P248) (conj _ (conj _ (conj _
    (conj (KS 184 _ ltac:(lia) P184) (conj (KS 256 _ ltac:(lia) P256) (conj (KS 264 _ ltac:(lia) P264)
    (conj (KS 272 _ ltac:(lia) P272) (KS 32 _ ltac:(lia) P32)))))))))))))))).
  - exact (r21g_addr_keeps m m' G _ _ Pad HK HGs).
  - exact (r21g_bytes_keeps m m' G _ _ Pin HK HGp).
  - intros Hn. exact (r21g_addr_keeps m m' G _ _ (Pg Hn) HK (HGps Hn)).
Qed.

Lemma r21g_RXS_keeps : forall m m' G cx fr regs regs' A,
  ACtlCutP.RXS cx fr regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> A + 312 <= 2 ^ 64 ->
  K11.getr regs' 9 = K11.getr regs 9 -> r21g_keeps m m' G ->
  (forall a, A <= a < A + 312 -> G a) ->
  (forall i, 0 <= i < 72 -> G (ART.shadow_addr (fr + 2256 + i))) ->
  ACtlCutP.RXS cx fr regs' m'.
Proof.
  intros m m' G cx fr regs regs' A HRXS HA HA0 HAb E9 HK HGA HGs.
  destruct HRXS as (X48 & X56 & X88 & X80 & X72 & X8 & X0 & X200 & X216 & Xad).
  assert (KS : forall off v, 0 <= off <= 304 -> ACtlCutP.spill regs m off v -> ACtlCutP.spill regs' m' off v).
  { intros off v Ho Hs. apply (r21g_spill_keeps m m' G regs regs' off v A HA HA0 ltac:(lia) ltac:(lia) E9 HK);
      [|exact Hs].
    intros i Hi. apply HGA. lia. }
  exact (conj (KS 48 _ ltac:(lia) X48) (conj (KS 56 _ ltac:(lia) X56) (conj (KS 88 _ ltac:(lia) X88)
    (conj (KS 80 _ ltac:(lia) X80) (conj (KS 72 _ ltac:(lia) X72) (conj (KS 8 _ ltac:(lia) X8)
    (conj (KS 0 _ ltac:(lia) X0) (conj (KS 200 _ ltac:(lia) X200) (conj (KS 216 _ ltac:(lia) X216)
    (r21g_addr_keeps m m' G _ _ Xad HK HGs)))))))))).
Qed.

Lemma r21g_saved_len : forall cx, length (ACtlCutP.saved_bytes cx) = 104%nat.
Proof. intros cx. unfold ACtlCutP.saved_bytes. rewrite !length_app, !MEM.length_le8. reflexivity. Qed.

(* FRAC (ACtlCutP.v:982-997) across a memory change that keeps the spill window [A, A + 312), the saved registers
   at [c_sp - 104, c_sp), every byte of the owned frame, and leaves every frame-shadow byte readable; the registers
   move by Kit's kit_frac_move.  The frame premise is the WHOLE frame [fr, fr + 4096), so it also keeps Batch3's
   trailer word q64 m (fr + 4088) (flag_addr (c_ly cx) 6 (c_fpos cx)), FRAC's last conjunct (ACtlCutP.v:997). *)
Lemma r21g_FRAC_keeps : forall m m' G cx fr sel (regs regs' : bvmap 5 word) A,
  ACtlCutP.FRAC B cx fr sel regs m -> ACtlCut.rgv regs 9 A -> 0 <= A -> 0 <= fr ->
  A + 416 <= ACtlCut.c_sp cx -> r21g_keeps m m' G ->
  (forall a, A <= a < A + 312 -> G a) ->
  (forall a, ACtlCut.c_sp cx - 104 <= a < ACtlCut.c_sp cx -> G a) ->
  (forall a, fr <= a < fr + 4096 -> G a) ->
  (forall i, 0 <= i < 392 -> exists b, MEM.mrd A.Img0.rsegs m' (MEM.wa (ACtlCutP.Sfr fr + i)) = Some b) ->
  K11.getr regs' 2 = K11.getr regs 2 -> K11.getr regs' 3 = K11.getr regs 3 -> K11.getr regs' 4 = K11.getr regs 4 ->
  K11.getr regs' 8 = K11.getr regs 8 -> K11.getr regs' 9 = K11.getr regs 9 -> K11.getr regs' 19 = K11.getr regs 19 ->
  K11.getr regs' 26 = K11.getr regs 26 ->
  ACtlCutP.FRAC B cx fr sel regs' m'.
Proof.
  intros m m' G cx fr sel regs regs' A HFRAC R9 HA0 Hfr0 HA416 HK HGA HGsv HGf HSh E2 E3 E4 E8 E9 E19 E26.
  apply (A.ACtlG.Kit.kit_frac_move B cx fr sel regs regs' m'); [|exact E2 | exact E3 | exact E4 | exact E8
    | exact E9 | exact E19 | exact E26].
  destruct HFRAC as (A0 & sp & R2 & Hsp16 & HspZ & R4 & R8 & R9' & R3 & R19 & R26 & Hfr32 & HA32 & HAS & HspA &
    HfrA & HA416' & HSsp & HSapp & Q304 & Q24 & Q16 & Qh1 & Qh2 & (sh & Hsh & Hshl) & Hsaved & Qtr).
  assert (EA : A0 = A).
  { apply (r21g_rgv_uniq regs 9 A A0 R9 R9');
      [unfold ART.APPMEM_END in *; lia | unfold ACtlCutP.FRAME_BYTES, ART.APPMEM_END in *; lia]. }
  subst A0.
  exists A, sp.
  do 17 (split; [assumption|]).
  split; [apply (r21g_q64_keeps m m' G _ _ Q304 HK); intros i Hi; apply HGA; lia|].
  split; [apply (r21g_q64_keeps m m' G _ _ Q24 HK); intros i Hi; apply HGA; lia|].
  split; [apply (r21g_q64_keeps m m' G _ _ Q16 HK); intros i Hi; apply HGA; lia|].
  split; [apply (r21g_q64_keeps m m' G _ _ Qh1 HK); intros i Hi; apply HGf; lia|].
  split; [apply (r21g_q64_keeps m m' G _ _ Qh2 HK); intros i Hi;
          replace (fr + 16 + i) with (fr + (16 + i)) by lia; apply HGf; lia|].
  split.
  - pose proof Hsh as Hb. apply MEM.bytes_at_bound in Hb. rewrite Hshl in Hb.
    change (Z.to_nat ACtlCutP.FRAME_SHADOW) with 392%nat in Hb, Hshl.
    destruct (A.Prog.Seg.R21.a_bytes_of_present 392 m' (ACtlCutP.Sfr fr) ltac:(lia) ltac:(lia)) as (sh' & Hsh' & Hl').
    { intros kk Hk. apply HSh. lia. }
    exists sh'. split; [exact Hsh' | rewrite Hl'; reflexivity].
  - split; [apply (r21g_bytes_keeps m m' G _ _ Hsaved HK); rewrite r21g_saved_len; intros i Hi; apply HGsv; lia|].
    apply (r21g_q64_keeps m m' G _ _ Qtr HK). intros i Hi. apply HGf. lia.
Qed.

Lemma r21g_b_view_mrd : forall (H : word -> bool) (m : word -> option byte) a,
  H (Z_to_bv 64 a) = false ->
  lib.Reusable.YG0n.aview segs H m a =
  option_map (fun b : byte => bv_unsigned b) (MEM.mrd A.Img0.rsegs m (MEM.wa a)).
Proof.
  intros H m a Hh.
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict, MEM.mrd, MEM.wa.
  rewrite Hh. destruct (m (Z_to_bv 64 a)); reflexivity.
Qed.

(* Equal views at a visible address give equal mrd bytes. *)
Lemma r21g_b_mrd_eq : forall (H : word -> bool) (m m2 : word -> option byte) a,
  H (Z_to_bv 64 a) = false ->
  lib.Reusable.YG0n.aview segs H m2 a = lib.Reusable.YG0n.aview segs H m a ->
  MEM.mrd A.Img0.rsegs m2 (MEM.wa a) = MEM.mrd A.Img0.rsegs m (MEM.wa a).
Proof.
  intros H m m2 a Hh E.
  rewrite (r21g_b_view_mrd H m2 a Hh), (r21g_b_view_mrd H m a Hh) in E.
  destruct (MEM.mrd A.Img0.rsegs m2 (MEM.wa a)) as [b2|], (MEM.mrd A.Img0.rsegs m (MEM.wa a)) as [b|];
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* A client byte (live chunk user byte, live fake frame byte or its shadow) is visible at a state with AR:
   AR's am_client (YG0n.v:221) over aclient (YG0n.v:129-132). *)
Lemma r21g_b_aclient_vis : forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md a,
  lib.Reusable.YG0n.AR segs B ly S W m md -> lib.Reusable.YG0n.aclient_byte B ly S a ->
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m a <> None.
Proof.
  intros ly S W m md a HAR Hcl.
  pose proof (lib.Reusable.YG0n.am_client _ _ _ _ (proj1 HAR)) as HC. rewrite Forall_forall in HC.
  assert (G : forall r, In r (lib.Reusable.YG0n.aclient S) ->
                lib.Reusable.YG0f.aeval B ly (fst r) <= a < lib.Reusable.YG0f.aeval B ly (fst r) + snd r ->
                lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m a <> None).
  { intros r Hr Hb. pose proof (HC r Hr (a - lib.Reusable.YG0f.aeval B ly (fst r)) ltac:(lia)) as X.
    replace (lib.Reusable.YG0f.aeval B ly (fst r) + (a - lib.Reusable.YG0f.aeval B ly (fst r))) with a in X
      by lia.
    exact X. }
  destruct Hcl as [(k & Hk & Hst & Hr) | (cp & Hcp & [Hr | Hr])].
  - eapply G.
    + unfold lib.Reusable.YG0n.aclient. apply in_or_app. left. apply in_flat_map. exists k. split; [exact Hk|].
      unfold lib.Reusable.YG0n.chunk_user. rewrite Hst. apply in_eq.
    + exact Hr.
  - eapply G.
    + unfold lib.Reusable.YG0n.aclient. apply in_or_app. right. apply in_or_app. left.
      apply in_map_iff. exists cp. split; [reflexivity | exact Hcp].
    + exact Hr.
  - eapply G.
    + unfold lib.Reusable.YG0n.aclient. apply in_or_app. right. apply in_or_app. right.
      apply in_map_iff. exists cp. split; [reflexivity | exact Hcp].
    + exact Hr.
Qed.

(* ===== SB1: the strcmp rule in journal form, in the shape of the core's aj_bcmp_at (YCbq.v:2062-2110) ===== *)
Lemma r21g_aj_strcmp_at :
  forall (W : lib.Reusable.YA0n.world segs) regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k
         x y kk c1 c2 (o : Z) raw,
  lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  K11.getr regsT 10 = lib.Reusable.YG0d.w64 x -> K11.getr regsT 11 = lib.Reusable.YG0d.w64 y -> 0 < x -> 0 < y ->
  kk + 1 < 2 ^ 32 -> x + kk + 1 <= 2 ^ 63 -> y + kk + 1 <= 2 ^ 63 ->
  lib.Reusable.YG0d.spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * lib.Reusable.YG0d.ESTACK - o <= STK ->
  K11.getr regsT 3 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_gp B) ->
  K11.getr regsT 4 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B) ->
  K11.getr regsT 1 = raw -> lib.Reusable.YK0s.ret_ok raw ->
  r21g_str_meet W memT x y kk c1 c2 ->
  lib.Reusable.YG0d.src_ok segs W regsT memT x (kk + 1) -> lib.Reusable.YG0d.src_ok segs W regsT memT y (kk + 1) ->
  (forall a, x <= a <= x + kk -> ~ (sp0 + o - 2 * lib.Reusable.YG0d.ESTACK <= a < sp0 + o)) ->
  (forall a, y <= a <= y + kk -> ~ (sp0 + o - 2 * lib.Reusable.YG0d.ESTACK <= a < sp0 + o)) ->
  lib.Reusable.YG0d.amem_range x (kk + 1) -> lib.Reusable.YG0d.amem_range y (kk + 1) ->
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) memT)
    lib.Reusable.YG0f.SHADOW_OFF x (kk + 1) ->
  lib.Reusable.YG0d.shadow_hull_vis (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) memT) x (kk + 1) ->
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) memT)
    lib.Reusable.YG0f.SHADOW_OFF y (kk + 1) ->
  lib.Reusable.YG0d.shadow_hull_vis (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) memT) y (kk + 1) ->
  lib.Reusable.YA0n.SRr segs W (mkCfg (K11.mkst regsT (Z_to_bv 64 0x42964) memT (K11.seg_rom segs)) mdc)
    (fun W2 cc => W2 = W /\ exists regs2 mem2 md2,
       cc = mkCfg (K11.mkst regs2 raw mem2 (K11.seg_rom segs)) md2 /\
       lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B STK sp0 FP ly S W0 mem md own lyc Sc W
         mem2 md2 k /\
       lib.Reusable.YG0n.AR segs B lyc Sc W mem2 md2 /\
       lib.Reusable.YG0d.aregs_preserved regsT regs2 /\
       K11.getr regs2 10 = lib.Reusable.YG0d.w64 (r21g_strcmp_res c1 c2) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * lib.Reusable.YG0d.ESTACK <= a < sp0 + o) ->
          lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) mem2 a =
          lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) memT a) /\
       (forall a, lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) memT a ->
          lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem2 a)).
Proof.
  intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y kk c1 c2 o raw
    HJ Ha0 Ha1 Hx0 Hy0 Hkk Hxk Hyk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hmeet Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
  pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
  pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  assert (Hes : lib.Reusable.YG0d.ESTACK = 4096) by reflexivity.
  assert (HPRE : lib.Reusable.YG0d.ecall_pre segs B lyc Sc W regsT memT mdc).
  { eapply (lib.Reusable.YCbq.ecall_pre_at (SK := A.AE2k.tfib_sink_head) segs B STK sp0 FP ly S W0 mem md own lyc Sc W
      memT mdc k regsT o); try eassumption; [lia|]. rewrite Hra. exact Hraw. }
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  assert (Hlo2 : lib.Reusable.YG0f.ly_stk_lo lyc + 2 * lib.Reusable.YG0d.ESTACK <= lib.Reusable.YG0d.spZ regsT)
    by (rewrite Eslo, Hsp'; lia).
  assert (Hpres2E : forall a, lib.Reusable.YG0d.spZ regsT - 2 * lib.Reusable.YG0d.ESTACK <= a <
                                lib.Reusable.YG0d.spZ regsT ->
            lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) memT a)
    by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; lia).
  eapply lib.Reusable.YA0n.SRr_mono.
  { exact (H_strcmp lyc Sc W regsT memT mdc x y kk c1 c2 HPRE Hlo2 Hpres2E Ha0 Ha1 Hx0 Hy0 Hkk Hxk Hyk Hmeet Hsx Hsy
      ltac:(rewrite Hsp'; exact Hbx) ltac:(rewrite Hsp'; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy). }
  cbv beta. intros W2 cc _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
  rewrite Hsp' in Hfr.
  split; [reflexivity|]. exists regs2, mem2, md2.
  split; [unfold lib.Reusable.YG0d.cfg_at, lib.Reusable.YG0d.raZ; rewrite Hra; unfold lib.Reusable.YG0d.w64;
          rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned; reflexivity|].
  split.
  { eapply (lib.Reusable.YCbq.ajournal_after_write (SK := A.AE2k.tfib_sink_head) segs B LAWS A.ACtlG.Kit.kit_segs_low
      STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
      (fun a => sp0 + o - 2 * lib.Reusable.YG0d.ESTACK <= a < sp0 + o) Sc own HJ).
    - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
    - exact Hpres2.
    - exact Hsame.
    - intros a Ha; left; left; lia.
    - exact HAR2.
    - reflexivity.
    - reflexivity.
    - lia.
    - exact Hfrs.
    - exact HQT. }
  split; [exact HAR2|]. split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

(* ===== SB2: ctl_rt_C after a call whose post is view-level (the strcmp rule's frame condition and presence
   clause), outside a window at or above HIGHMEM_BEG, at a state with AR ===== *)
Lemma r21g_ctlrt_view : forall ly S (W : lib.Reusable.YA0n.world segs) (m m2 : word -> option byte) md2 lo hi,
  A.ACtlRtC.ctl_rt_C B ly S m -> lib.Reusable.YG0n.AR segs B ly S W m2 md2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
     lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m2 a =
     lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m a) ->
  (forall a, lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m a ->
     lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m2 a) ->
  ART.HIGHMEM_BEG <= lo ->
  A.ACtlRtC.ctl_rt_C B ly S m2.
Proof.
  intros ly S W m m2 md2 lo hi (Hc & Hcut & Himg & Hr) HAR Hv Hp Hlo.
  assert (KM : forall x, 0 <= x < 2 ^ 64 -> x < lo -> lib.Reusable.YA0n.w_H W (Z_to_bv 64 x) = false ->
                 MEM.mrd A.Img0.rsegs m2 (MEM.wa x) = MEM.mrd A.Img0.rsegs m (MEM.wa x)).
  { intros x Hx Hxl Hh. apply (r21g_b_mrd_eq _ m m2 x Hh). apply Hv; [exact Hx | lia]. }
  (* a shadow_rw_on region of m carries to m2: hidden bytes from AR's ahs_pres at m2, visible ones by the view *)
  assert (KS : forall P, A.ShadowRwOn.shadow_rw_on P m -> A.ShadowRwOn.shadow_rw_on P m2).
  { intros P Hs a HPa Hin.
    assert (Ha : 0 <= a < 2 ^ 64 /\ a < ART.HIGHMEM_BEG /\ ART.LOWMEM_END <= a)
      by (unfold ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END, ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG in *; lia).
    destruct Ha as (Ha & Hah & Hal).
    destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:Hh.
    - (* hidden: AR's ahs_pres at m2; a client byte would be visible *)
      pose proof HAR as (_ & _ & _ & _ & (HP & _)).
      assert (Hnz : m2 (MEM.wa a) <> None).
      { apply (HP a).
        - unfold lib.Reusable.YG0f.in_band_rw, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kLowShadowEnd,
            lib.Reusable.YG0f.kHighShadowBeg, lib.Reusable.YG0f.kHighShadowEnd.
          unfold ART.in_shadow, ART.LOWMEM_END, ART.LOWSHADOW_END, ART.HIGHSHADOW_BEG, ART.HIGHMEM_BEG in Hin. lia.
        - intros Hcl. pose proof (r21g_b_aclient_vis ly S W m2 md2 a HAR Hcl) as Hv'.
          apply (A.ProgWorldVisFrame.vis_of_aview segs W m2 a) in Hv'. rewrite Hh in Hv'. discriminate.
        - left. exact Hh. }
      destruct (m2 (MEM.wa a)) as [b2|] eqn:E2; [|exfalso; exact (Hnz eq_refl)].
      split; [unfold wview; rewrite E2; discriminate | exists b2; unfold MEM.mrd; rewrite E2; reflexivity].
    - (* visible: the view equality, and no segment byte at a shadow address *)
      pose proof (KM a Ha ltac:(lia) Hh) as E.
      destruct (Hs a HPa Hin) as [_ [b Hb]].
      assert (Hni : ~ lib.Reusable.YG0d.in_img segs a).
      { intros Himg'. pose proof (A.ACtlG.Kit.kit_segs_low a Himg') as Hl.
        unfold lib.Reusable.YG0f.kLowMemEnd, ART.LOWMEM_END in *. lia. }
      assert (Hrom : forall mm : word -> option byte, mm (MEM.wa a) = None ->
                       MEM.mrd A.Img0.rsegs mm (MEM.wa a) = None).
      { intros mm Hmm. unfold MEM.mrd. rewrite Hmm. exact (lib.Reusable.YCbq.seg_rom_none segs a Ha Hni). }
      split.
      + unfold wview. destruct (m2 (MEM.wa a)) as [b2|] eqn:E2; [discriminate|].
        exfalso. rewrite (Hrom m2 E2) in E. rewrite <- E in Hb. discriminate.
      + exists b. rewrite E. exact Hb. }
  split; [|split; [|split]].
  - (* asan_cells: every cell lies in the runtime's data range [RT_LO, RT_HI), visible and below lo *)
    assert (KB : forall x bs, MEM.bytes_at A.Img0.rsegs m x bs ->
                   ART.RT_LO <= x /\ x + Z.of_nat (length bs) <= ART.RT_HI ->
                   MEM.bytes_at A.Img0.rsegs m2 x bs).
    { intros x bs (H0 & H1 & H2) [Hl Hh]. split; [exact H0|]. split; [exact H1|].
      intros i Hi. rewrite <- (H2 i Hi). apply KM.
      - lia.
      - unfold ART.RT_LO, ART.RT_HI, ART.HIGHMEM_BEG in *; lia.
      - pose proof (A.ProgBridge.rt_vis_W W) as (_ & _ & V). apply V. lia. }
    unfold A.ACtlK.asan_cells_at, ART.asan_cells in Hc |- *.
    repeat lazymatch type of Hc with _ /\ _ => destruct Hc as [? Hc] end.
    repeat match goal with |- _ /\ _ => split end;
      (apply KB; [eassumption|]);
      rewrite ?MEM.length_le8, ?MEM.length_le4; cbn [length Z.of_nat Pos.of_succ_nat];
      unfold ART.RT_LO, ART.RT_HI, ART.CELL_K, ART.GOT_CELL_K, ART.INITED, ART.REPLACE, ART.GOT_REPLACE, ART.UAR,
        ART.GOT_UAR, ART.CANPOISON, ART.HIEND, ART.GOT_HIEND, ART.MIDBEG, ART.GOT_MIDBEG, ART.MIDEND, ART.GOT_MIDEND,
        ART.REAL_MEMCPY, ART.REAL_MEMSET, ART.GOT_REAL_MEMSET; lia.
  - exact (KS _ Hcut).
  - exact (KS _ Himg).
  - (* ro_agree: a read-only address is in the image, visible and below lo *)
    unfold A.ACtlK.ro_agree_at in *. intros a Hro. rewrite <- (Hr a Hro).
    pose proof (R21S.r21_ro_lt a Hro) as Hlt.
    pose proof (bv_unsigned_in_range _ a) as Hra. change (bv_modulus 64) with (2 ^ 64) in Hra.
    assert (Hh : lib.Reusable.YA0n.w_H W a = false).
    { destruct (lib.Reusable.YA0n.w_H W a) eqn:E; [|reflexivity]. exfalso.
      assert (Hn : find_segment A.Img0.rsegs (bv_unsigned a) 1 = None) by exact (lib.Reusable.YA0n.w_Hoff W a E).
      unfold MEM.ro_addr in Hro. rewrite Hn in Hro. discriminate. }
    assert (Hh' : lib.Reusable.YA0n.w_H W (Z_to_bv 64 (bv_unsigned a)) = false)
      by (rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned; exact Hh).
    pose proof (KM (bv_unsigned a) Hra ltac:(unfold ART.HIGHMEM_BEG in Hlo; lia) Hh') as E.
    unfold MEM.wa in E. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in E. exact E.
Qed.

(* ===== SB3: the pointwise keep of two memories on an address set, and its view-level instance ===== *)
Lemma r21g_keeps_view : forall (W : lib.Reusable.YA0n.world segs) (m m2 : word -> option byte) lo hi,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
     lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m2 a =
     lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m a) ->
  (forall a, lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m a ->
     lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m2 a) ->
  r21g_keeps m m2 (fun a => 0 <= a < 2 ^ 64 /\ lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false /\ ~ (lo <= a < hi)).
Proof.
  intros W m m2 lo hi Hv Hp a (Ha & Hh & Hlo). split.
  - apply (r21g_b_mrd_eq _ m m2 a Hh). exact (Hv a Ha Hlo).
  - unfold wview, MEM.wa. destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
    + assert (Hpa : lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m a)
        by (split; [exact Hh | exists b; exact Em]).
      destruct (Hp a Hpa) as [_ [b2 Hb2]]. rewrite Hb2. intros _. discriminate.
    + destruct (m2 (Z_to_bv 64 a)) as [b2|]; [intros _; discriminate | exact (fun H => H)].
Qed.

(* ===== a Theorem Labs lane's helpers ===== *)
(* A catalogue byte is a byte of the image's third segment [0x9e000, 0xa1000). *)
Lemma r21g_a_in_img : forall a, SM.CAT <= a < SM.CAT + 3256 -> lib.Reusable.YG0d.in_img segs a.
Proof.
  intros a Ha. unfold SM.CAT in Ha.
  assert (Hin : In (0x9e000, 0x3000) (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) segs)).
  { rewrite A.ProgBridge.tfibsegs_rsegs, A.ProgBridge.rsegs_spans. cbn [In]. tauto. }
  apply in_map_iff in Hin as (s & Es & Hs). injection Es as E1 E2.
  unfold lib.Reusable.YG0d.in_img. exists s. split; [exact Hs | lia].
Qed.

(* No catalogue byte is in a static range the bundle owns (decided over the build's own table). *)
Lemma r21g_a_not_owned : forall a, SM.CAT <= a < SM.CAT + 3256 ->
  ~ Exists (lib.Reusable.YG0n.in_zr a) (lib.Reusable.YG0f.as_owned_static B).
Proof.
  intros a Ha. rewrite (A.AF0m.ts_owned B TFIB_SYMS).
  assert (C : forallb (fun r : Z * Z => (SM.CAT + 3256 <=? fst r) || (fst r + snd r <=? SM.CAT))
                A.AF0m.Tfib_owned_static = true) by (vm_compute; reflexivity).
  intros X. apply Exists_exists in X as (r & Hr & Hz).
  pose proof (proj1 (forallb_forall _ _) C r Hr) as Hb. cbn beta in Hb.
  destruct Hz as [Z1 Z2].
  apply orb_prop in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.

(* No catalogue byte is in the errno word. *)
Lemma r21g_a_not_errno : forall a, SM.CAT <= a < SM.CAT + 3256 ->
  ~ (lib.Reusable.YG0f.as_errno B <= a < lib.Reusable.YG0f.as_errno B + 4).
Proof. intros a Ha. rewrite (A.AF0m.ts_errno B TFIB_SYMS). unfold A.AF0m.TFIB_ERRNO, SM.CAT in *. lia. Qed.

(* At a visible address, the core's view is ctrl's mrd, as a number. *)
Lemma r21g_a_mrd_view : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) x,
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 x) = false ->
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m x =
  option_map (fun b : byte => bv_unsigned b) (MEM.mrd A.Img0.rsegs m (MEM.wa x)).
Proof.
  intros W m x Hh.
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict, MEM.mrd, MEM.wa.
  cbv beta. rewrite Hh. reflexivity.
Qed.

(* option_map bv_unsigned is injective on bytes. *)
Lemma r21g_a_omap_inj : forall o1 o2 : option byte,
  option_map (fun b : byte => bv_unsigned b) o1 = option_map (fun b : byte => bv_unsigned b) o2 -> o1 = o2.
Proof.
  intros [b1|] [b2|] E; cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* The k-th byte of Lib.Image's image_bytes is the segment byte at a0 + k (R21S.a_img_nth is stated over
   A.Tk.UL.Image, a different constant from the Lib.Image that RTM.a_row_img uses, and the conversion between the
   two costs 15 s per use). *)
Lemma r21g_a_img_nth : forall (sg : list Segment) n a0 bs,
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Image.image_bytes sg a0 n = Some bs ->
  forall k, (k < n)%nat ->
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.seg_rom sg (MEM.wa (a0 + Z.of_nat k)) = nth_error bs k.
Proof.
  intros sg. induction n as [|n IH]; intros a0 bs H k Hk; [lia|].
  cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Image.image_bytes] in H.
  destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.seg_rom sg (MEM.wa a0)) as [b|] eqn:E1;
    [|discriminate H].
  destruct (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Image.image_bytes sg (a0 + 1) n) as [bs'|] eqn:E2;
    [|discriminate H].
  injection H as <-. destruct k as [|k]; cbn [nth_error].
  - replace (a0 + Z.of_nat 0) with a0 by lia. exact E1.
  - replace (a0 + Z.of_nat (S k)) with (a0 + 1 + Z.of_nat k) by lia. exact (IH (a0 + 1) bs' E2 k ltac:(lia)).
Qed.

(* ===== SA1: the catalogue's bytes in the view at a cut: the entry's read-only view (ctl_base's arodata_okS over
   [RLO, RHI), RELRO_CAT) kept by the journal (FP = []) ===== *)
Lemma r21g_cat_view : forall cx own ly3 S3 (W3 : lib.Reusable.YA0n.world segs) mem3 md3 k,
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) own ly3 S3 W3 mem3 md3 k ->
  forall a, A.Prog.SlotModel.CAT <= a < A.Prog.SlotModel.CAT + 3256 ->
    lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W3) mem3 a =
    option_map (fun b : byte => bv_unsigned b) (K11.seg_rom segs (Z_to_bv 64 a)).
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k [Hpre _] HJ a Ha.
  destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Haro & _).
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a (r21g_a_in_img a Ha) (r21g_a_not_owned a Ha) (r21g_a_not_errno a Ha)
             (lib.Reusable.YCbq.fp_spares_closed (SK := A.AE2k.tfib_sink_head) [] a
                lib.Reusable.YCbq.sink_closed_nil)).
  pose proof RELRO_CAT as HRC. unfold A.Prog.SlotModel.CAT_N, A.Prog.SlotModel.CAT_ROW in HRC.
  apply Haro; [right; lia | exact (r21g_a_not_owned a Ha) | exact (r21g_a_not_errno a Ha)].
Qed.

(* ===== SA2: the catalogue rows as bytes in memory ===== *)
Lemma r21g_cat_rows : forall cx own ly3 S3 (W3 : lib.Reusable.YA0n.world segs) mem3 md3 k,
  ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) []
    (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) own ly3 S3 W3 mem3 md3 k ->
  forall i, 0 <= i < 11 ->
    MEM.bytes_at A.Img0.rsegs mem3 (A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_ROW * i) (A.Prog.SlotModel.rowb i).
Proof.
  intros cx own ly3 S3 W3 mem3 md3 k HB HJ i Hi.
  pose proof (RTM.a_row_img i Hi) as HI.
  pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Image.image_bytes_length A.Img0.rsegs 296 _ _ HI)
    as HL.
  pose proof (A.ProgBridge.img_vis_W W3) as (_ & _ & HV).
  split; [unfold SM.CAT, SM.CAT_ROW; lia|]. split; [rewrite HL; unfold SM.CAT, SM.CAT_ROW; lia|].
  intros j Hj. rewrite HL in Hj.
  rewrite <- (r21g_a_img_nth A.Img0.rsegs 296 _ _ HI j Hj).
  assert (Hx : SM.CAT <= SM.CAT + SM.CAT_ROW * i + Z.of_nat j < SM.CAT + 3256)
    by (unfold SM.CAT, SM.CAT_ROW; lia).
  assert (Hw : lib.Reusable.YA0n.w_H W3 (Z_to_bv 64 (SM.CAT + SM.CAT_ROW * i + Z.of_nat j)) = false)
    by (apply HV; unfold A.Prog.ImgBounds.IMG_LO, A.Prog.ImgBounds.IMG_HI, SM.CAT in *; lia).
  apply r21g_a_omap_inj.
  rewrite <- (r21g_a_mrd_view W3 mem3 _ Hw).
  rewrite (r21g_cat_view cx own ly3 S3 W3 mem3 md3 k HB HJ _ Hx).
  reflexivity.
Qed.

(* ===== SA3: the catalogue's shadow is zero and visible at every state with AR (AR_zshadow_law over the
   bundle's as_zero_shadow, TFIB_SYMS's ts_zsh) ===== *)
Lemma r21g_cat_shadow : forall ly S (W : lib.Reusable.YA0n.world segs) m md,
  lib.Reusable.YG0n.AR segs B ly S W m md ->
  forall q, A.Prog.SlotModel.CAT <= q < A.Prog.SlotModel.CAT + 3256 ->
    MEM.mrd A.Img0.rsegs m (MEM.wa (ART.shadow_addr q)) = Some (Z_to_bv 8 0) /\
    lib.Reusable.YA0n.w_H W (Z_to_bv 64 (ART.shadow_addr q)) = false.
Proof.
  intros ly S W m md HAR q Hq.
  assert (C : existsb (fun r : Z * Z => (fst r <=? SM.CAT) && ((SM.CAT + 3255) / 8 <? fst r / 8 + snd r / 8))
                A.AF0m.Tfib_zero_shadow = true) by (vm_compute; reflexivity).
  apply existsb_exists in C as ((lo & len) & Hr & Hb). cbn [fst snd] in Hb.
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  pose proof (lib.Reusable.YG0d.al_zshadow _ _ LAWS ly S W m md (lo, len) HAR
    ltac:(unfold lib.Reusable.YG0n.zero_shadow_ranges; right; rewrite (A.AF0m.ts_zsh B TFIB_SYMS); exact Hr)) as HZ.
  cbn [fst snd] in HZ.
  assert (Hd1 : lo / 8 <= q / 8) by (apply Z.div_le_mono; lia).
  assert (Hd2 : q / 8 <= (SM.CAT + 3255) / 8) by (apply Z.div_le_mono; lia).
  specialize (HZ (q / 8 - lo / 8) ltac:(lia)).
  unfold lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF in HZ.
  replace (0x7fff8000 + lo / 8 + (q / 8 - lo / 8)) with (ART.shadow_addr q) in HZ
    by (unfold ART.shadow_addr, ART.ASAN_K; lia).
  assert (Hvis : lib.Reusable.YA0n.w_H W (Z_to_bv 64 (ART.shadow_addr q)) = false)
    by (apply (A.ProgWorldVisFrame.vis_of_aview segs W m); rewrite HZ; discriminate).
  split; [|exact Hvis].
  rewrite (r21g_a_mrd_view W m _ Hvis) in HZ. revert HZ.
  destruct (MEM.mrd A.Img0.rsegs m (MEM.wa (ART.shadow_addr q))) as [b|]; cbn; intros HZ; [|discriminate].
  injection HZ as HZ. f_equal. apply bv_eq. rewrite HZ. reflexivity.
Qed.

(* The narrowed tail stretch (Seg/R21Fs.v r21_tail_pre_Fs), at the canonical start map, with the core's getr. *)
Lemma r21g_tail_run : forall RNG (regs : bvmap 5 word) (m : word -> option byte)
    (A S5 mr fw maj mnr pat h nm w144 : Z),
  K11.getr regs 9 = Z_to_bv 64 A -> K11.getr regs 21 = Z_to_bv 64 S5 -> K11.getr regs 26 = Z_to_bv 64 ART.ASAN_K ->
  0 <= A -> A + 152 <= 2 ^ 64 -> 0 <= S5 -> S5 + 38 <= 2 ^ 64 ->
  0 <= mr -> mr + 296 <= 2 ^ 63 -> 0 <= h < 2 ^ 32 ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa (S5 + 2)) 1 = Some [Z_to_bv 8 1] ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa (A + 144)) 8 = Some (MEM.le8 (Z_to_bv 64 w144)) ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa (A + 112)) 8 = Some (MEM.le8 (Z_to_bv 64 mr)) ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa (Z.shiftr (mr + 266) 3 + ART.ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa (Z.shiftr (mr + 268) 3 + ART.ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa (Z.shiftr (mr + 270) 3 + ART.ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa (Z.shiftr (mr + 272) 3 + ART.ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa (Z.shiftr (mr + 56) 3 + ART.ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa (Z.shiftr (mr + 280) 3 + ART.ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa S5) 2 = Some (MEM.le2 (Z_to_bv 64 fw)) ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa (mr + 266)) 2 = Some (MEM.le2 (Z_to_bv 64 fw)) ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa (S5 + 36)) 1 = Some [Z_to_bv 8 1] ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa (S5 + 22)) 2 = Some (MEM.le2 (Z_to_bv 64 maj)) ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa (mr + 268)) 2 = Some (MEM.le2 (Z_to_bv 64 maj)) ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa (S5 + 24)) 2 = Some (MEM.le2 (Z_to_bv 64 mnr)) ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa (mr + 270)) 2 = Some (MEM.le2 (Z_to_bv 64 mnr)) ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa (S5 + 26)) 2 = Some (MEM.le2 (Z_to_bv 64 pat)) ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa (mr + 272)) 2 = Some (MEM.le2 (Z_to_bv 64 pat)) ->
  ov_read_bytes A.Img0.rsegs m (MEM.wa (mr + 56)) 4 = Some (MEM.le4 (Z_to_bv 64 h)) ->
  (h <> 0 ->
     ov_read_bytes A.Img0.rsegs m (MEM.wa (S5 + 20)) 1 = Some [Z_to_bv 8 1] /\
     ov_read_bytes A.Img0.rsegs m (MEM.wa (mr + 280)) 8 = Some (MEM.le8 (Z_to_bv 64 nm)) /\ 0 < nm < 2 ^ 64) ->
  Lib.ExecF.rng RNG (S5 + 2) 1 -> Lib.ExecF.rng RNG (A + 144) 8 -> Lib.ExecF.rng RNG (A + 112) 8 ->
  Lib.ExecF.rng RNG (Z.shiftr (mr + 266) 3 + ART.ASAN_K) 1 -> Lib.ExecF.rng RNG (Z.shiftr (mr + 268) 3 + ART.ASAN_K) 1 ->
  Lib.ExecF.rng RNG (Z.shiftr (mr + 270) 3 + ART.ASAN_K) 1 -> Lib.ExecF.rng RNG (Z.shiftr (mr + 272) 3 + ART.ASAN_K) 1 ->
  Lib.ExecF.rng RNG (Z.shiftr (mr + 56) 3 + ART.ASAN_K) 1 -> Lib.ExecF.rng RNG (Z.shiftr (mr + 280) 3 + ART.ASAN_K) 1 ->
  Lib.ExecF.rng RNG S5 2 -> Lib.ExecF.rng RNG (mr + 266) 2 -> Lib.ExecF.rng RNG (S5 + 36) 1 ->
  Lib.ExecF.rng RNG (S5 + 22) 2 -> Lib.ExecF.rng RNG (mr + 268) 2 -> Lib.ExecF.rng RNG (S5 + 24) 2 ->
  Lib.ExecF.rng RNG (mr + 270) 2 -> Lib.ExecF.rng RNG (S5 + 26) 2 -> Lib.ExecF.rng RNG (mr + 272) 2 ->
  Lib.ExecF.rng RNG (mr + 56) 4 ->
  (h <> 0 -> Lib.ExecF.rng RNG (S5 + 20) 1 /\ Lib.ExecF.rng RNG (mr + 280) 8) ->
  Lib.ExecF.evtF A.Img0.rsegs RNG
    (fun ms' =>
       (h = 0 /\ exists R0 : bvmap 5 word,
          ms' = LBMS.MS R0 K11.fp_regs (Z_to_bv 64 0x81ac8) K11.fp_csr None m (K11.seg_rom A.Img0.rsegs) /\
          K11.getr R0 10 = Z_to_bv 64 0 /\
          K11.getr R0 2 = K11.getr regs 2 /\ K11.getr R0 3 = K11.getr regs 3 /\ K11.getr R0 4 = K11.getr regs 4 /\
          K11.getr R0 8 = K11.getr regs 8 /\ K11.getr R0 9 = K11.getr regs 9 /\
          K11.getr R0 19 = K11.getr regs 19 /\ K11.getr R0 26 = K11.getr regs 26 /\
          K11.getr R0 27 = Z_to_bv 64 w144 /\ K11.getr R0 22 = K11.getr regs 22 /\ K11.getr R0 25 = K11.getr regs 25) \/
       (h <> 0 /\ exists regsT : bvmap 5 word,
          ms' = LBMS.MS regsT K11.fp_regs (Z_to_bv 64 0x42964) K11.fp_csr None m (K11.seg_rom A.Img0.rsegs) /\
          K11.getr regsT 1 = Z_to_bv 64 0x81ac0 /\
          K11.getr regsT 10 = Z_to_bv 64 (S5 + 3) /\ K11.getr regsT 11 = Z_to_bv 64 nm /\
          K11.getr regsT 2 = K11.getr regs 2 /\ K11.getr regsT 3 = K11.getr regs 3 /\
          K11.getr regsT 4 = K11.getr regs 4 /\ K11.getr regsT 8 = K11.getr regs 8 /\
          K11.getr regsT 9 = K11.getr regs 9 /\ K11.getr regsT 19 = K11.getr regs 19 /\
          K11.getr regsT 21 = K11.getr regs 21 /\ K11.getr regsT 22 = K11.getr regs 22 /\
          K11.getr regsT 25 = K11.getr regs 25 /\ K11.getr regsT 26 = K11.getr regs 26 /\
          K11.getr regsT 27 = Z_to_bv 64 w144))
    (LBMS.MS (Lib.Regs6ss.mkR_of regs) K11.fp_regs (Z_to_bv 64 0x81990) K11.fp_csr None m
       (K11.seg_rom A.Img0.rsegs)).
Proof.
  intros RNG regs m A S5 mr fw maj mnr pat h nm w144 H9 H21 H26 HA0 HA1 HS0 HS1 Hm0 Hm1 Hh
    R2 R144 R112 K266 K268 K270 K272 K56 K280 R0 M266 R36 R22 M268 R24 M270 R26 M272 M56 HN
    G2 G144 G112 GK266 GK268 GK270 GK272 GK56 GK280 G0 GM266 G36 G22 GM268 G24 GM270 G26 GM272 GM56 GHN.
  unfold Lib.Regs6ss.mkR_of.
  eapply Lib.ExecF.evtF_mono.
  - eapply (R21N.r21_tail_pre_Fs RNG) with (A := A) (S5 := S5) (mr := mr) (fw := fw) (maj := maj) (mnr := mnr)
      (pat := pat) (h := h) (nm := nm) (w144 := w144);
      [exact H9 | exact H21 | exact H26 | exact HA0 | exact HA1 | exact HS0 | exact HS1 | exact Hm0 | exact Hm1
      | exact Hh | exact R2 | exact R144 | exact R112 | exact K266 | exact K268 | exact K270 | exact K272 | exact K56
      | exact K280 | exact R0 | exact M266 | exact R36 | exact R22 | exact M268 | exact R24 | exact M270 | exact R26
      | exact M272 | exact M56 | exact HN | exact G2 | exact G144 | exact G112 | exact GK266 | exact GK268
      | exact GK270 | exact GK272 | exact GK56 | exact GK280 | exact G0 | exact GM266 | exact G36 | exact G22
      | exact GM268 | exact G24 | exact GM270 | exact G26 | exact GM272 | exact GM56 | exact GHN].
  - intros ms' [(E0 & R0' & E & P10 & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P27 & P22 & P25)
               | (E0 & c5 & c6 & c7 & c12 & c13 & c14 & c15 & c16 & c17 & c28 & c29 & c30 & c31 & E)].
    + left. split; [exact E0|]. exists R0'. split; [exact E|].
      split; [exact P10|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P27|].
      split; [exact P22 | exact P25].
    + right. split; [exact E0|]. eexists. split; [exact E|].
      repeat split; reflexivity.
Qed.


Lemma r21g_keeps_trans : forall m1 m2 m3 (G1 G2 : Z -> Prop),
  r21g_keeps m1 m2 G1 -> r21g_keeps m2 m3 G2 -> r21g_keeps m1 m3 (fun a => G1 a /\ G2 a).
Proof.
  intros m1 m2 m3 G1 G2 H1 H2 a (Ha1 & Ha2). destruct (H1 a Ha1) as (E1 & W1). destruct (H2 a Ha2) as (E2 & W2).
  split; [rewrite E2; exact E1 | intros Hw; exact (W2 (W1 Hw))].
Qed.

(* The body of the two exits A81ac0 / A81ac8 (ACtlCutP.v:1710-1746, the same predicate), from the entry body's
   facts at (regs3, mem3), a memory m that keeps mem3 on G, and the exit map R. *)
Lemma r21g_exit_body : forall cx fr (regs3 R : bvmap 5 word) (mem3 m : word -> option byte) (G : Z -> Prop) bl A,
  Permutation bl (lib.Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)) ->
  ACtlCutP.FRAC B cx fr fr regs3 mem3 -> ACtlCut.c_n cx < 2 ^ 26 ->
  ACtlCut.rgv regs3 9 A -> 0 <= A -> 0 <= fr -> A + 416 <= ACtlCut.c_sp cx -> ACtlCut.c_sp cx - 4096 < A ->
  ACtlCutP.OURb cx fr mem3 -> ACtlCutP.CUR cx 7 regs3 -> ACtlCutP.PRO cx fr regs3 mem3 ->
  ACtlCutP.spill regs3 mem3 144 (fr + 2688) -> ACtlCutP.spill regs3 mem3 192 (fr + 2768) ->
  (exists idb, LBST.rw_cells segs mem3 (fr + 2688) [LBCE.CB 38 idb]) ->
  (exists junk, LBST.rw_cells segs mem3 (fr + 2768) [LBCE.CB 72 junk]) ->
  ACtlCutP.spill regs3 mem3 280 (fr + 3040) -> ACtlCutP.spill regs3 mem3 240 (fr + 3056) ->
  (exists jy, LBST.rw_cells segs mem3 (fr + 3040) [LBCE.CB 1 jy]) ->
  (exists junk, LBST.rw_cells segs mem3 (fr + 3056) [LBCE.CB 32 junk]) ->
  ACtlCutP.spill regs3 mem3 152 (ACtlCutP.Sfr fr + 68) ->
  A.Prog.SlotModel.c0 (ACtlCut.c_in cx) = 7 ->
  r21g_keeps mem3 m G ->
  (forall a, A <= a < A + 312 -> G a) ->
  (forall a, ACtlCut.c_sp cx - 104 <= a < ACtlCut.c_sp cx -> G a) ->
  (forall a, fr <= a < fr + 4096 -> G a) ->
  (forall i, 0 <= i < 6 -> G (ART.shadow_addr (fr + 2624 + i))) ->
  (forall i, 0 <= i < Z.of_nat (length (ACtlCut.c_in cx)) -> G (ACtlCut.c_p cx + i)) ->
  (0 < ACtlCut.c_n cx -> forall i, 0 <= i < ACtlCut.c_n cx -> G (ART.shadow_addr (ACtlCut.c_p cx + i))) ->
  (forall i, 0 <= i < 392 -> exists b, MEM.mrd A.Img0.rsegs m (MEM.wa (ACtlCutP.Sfr fr + i)) = Some b) ->
  (forall i, 0 <= i < 8 -> lib.Reusable.YP09.writable_at A.Img0.rsegs m (A + 192 + i)) ->
  K11.getr R 2 = K11.getr regs3 2 -> K11.getr R 3 = K11.getr regs3 3 -> K11.getr R 4 = K11.getr regs3 4 ->
  K11.getr R 8 = K11.getr regs3 8 -> K11.getr R 9 = K11.getr regs3 9 -> K11.getr R 19 = K11.getr regs3 19 ->
  K11.getr R 22 = K11.getr regs3 22 -> K11.getr R 25 = K11.getr regs3 25 -> K11.getr R 26 = K11.getr regs3 26 ->
  K11.getr R 10 = Z_to_bv 64 0 -> K11.getr R 27 = Z_to_bv 64 (fr + 2688) ->
  ACtlCut.cut_body C_A81ac0 cx [] bl fr fr R m.
Proof.
  intros cx fr regs3 R mem3 m G bl A HP HFRAC Hn R9 HA0 Hfr0 HA416 HAsp HOUR HCUR HPRO S144 S192 Hid Hjk S280 S240 Hjy
    Hjk32 S152 Ec0 HK HGA HGsv HGF HGs HGp HGps HSh HW K2 K3 K4 K8 K9 K19 K22 K25 K26 K10 K27.
  (* batch 4 B5.4: FRAC states c_sp cx <= APPMEM_END (ACtlCutP.v:1073); every step below needs only A + 416 <= c_sp cx
     <= 2 ^ 47 (the spills below c_sp), never c_sp cx strictly below 2 ^ 47 *)
  assert (HSapp : ACtlCut.c_sp cx <= 2 ^ 47).
  { destruct HFRAC as (A' & sp' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _).
    unfold ACtlCutP.ART.APPMEM_END in H. lia. }
  assert (KS : forall off v, 0 <= off <= 304 -> ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R m off v).
  { intros off v Ho Hs. apply (r21g_spill_keeps mem3 m G regs3 R off v A R9 HA0 ltac:(lia) ltac:(lia) K9 HK);
      [|exact Hs].
    intros i Hi. apply HGA. lia. }
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81ac0].
  split; [exact HP|].
  split.
  { apply (r21g_FRAC_keeps mem3 m G cx fr fr regs3 R A HFRAC R9 HA0 Hfr0 HA416 HK HGA HGsv HGF HSh);
      [exact K2 | exact K3 | exact K4 | exact K8 | exact K9 | exact K19 | exact K26]. }
  split; [exact Hn|].
  split.
  { unfold ACtlCutP.OURb in *. apply (r21g_bytes_keeps mem3 m G _ _ HOUR HK).
    rewrite A.Prog.SlotModel.OUR_length. intros i Hi. apply HGF. lia. }
  split.
  { rewrite Ec0. destruct HCUR as (Hc0 & Hc22 & Hc25). unfold ACtlCutP.CUR, ACtlCut.rgv in *.
    split; [exact Hc0|]. split; [rewrite K22; exact Hc22 | rewrite K25; exact Hc25]. }
  split.
  { apply (r21g_PRO_keeps mem3 m G cx fr regs3 R A HPRO R9 HA0 ltac:(lia) K9 HK HGA HGs HGp HGps). }
  split; [exact (KS 144 _ ltac:(lia) S144)|].
  split; [unfold ACtlCut.a0v, ACtlCut.rgv; exact K10|].
  split.
  { exists (ACtlCutP.Sfr fr + 68). split; [exact (KS 152 _ ltac:(lia) S152)|].
    unfold ACtlCutP.Sfr. lia. }
  exists A.
  destruct Hid as (idb & Hidb). destruct Hjk as (jk & Hjkb). exists idb, jk.
  split; [unfold ACtlCut.rgv in R9; rewrite K9; exact R9|].
  split; [unfold ACtlCut.rgv; exact K27|].
  split; [lia|].
  split.
  { apply A.Prog.Seg.R21.r21_rw_c8; [| exact HW].
    exact (r21g_q64_keeps mem3 m G _ _ (r21g_spill_A regs3 mem3 192 (fr + 2768) A R9 HA0 ltac:(lia) ltac:(lia) S192)
             HK ltac:(intros i Hi; apply HGA; lia)). }
  split; [apply (r21g_rwcb_keeps mem3 m G _ _ _ Hidb HK); intros i Hi; apply HGF; cbn in Hi; lia|].
  split; [apply (r21g_rwcb_keeps mem3 m G _ _ _ Hjkb HK); intros i Hi; apply HGF; cbn in Hi; lia|].
  split; [exact (r21g_q64_keeps mem3 m G _ _ (r21g_spill_A regs3 mem3 280 (fr + 3040) A R9 HA0 ltac:(lia)
                   ltac:(lia) S280) HK ltac:(intros i Hi; apply HGA; lia))|].
  split; [exact (r21g_q64_keeps mem3 m G _ _ (r21g_spill_A regs3 mem3 240 (fr + 3056) A R9 HA0 ltac:(lia)
                   ltac:(lia) S240) HK ltac:(intros i Hi; apply HGA; lia))|].
  destruct Hjy as (jy & Hjyb). destruct Hjk32 as (j32 & Hj32b). exists jy, j32.
  split; [apply (r21g_rwcb_keeps mem3 m G _ _ _ Hjyb HK); intros i Hi; apply HGF; cbn in Hi; lia|].
  apply (r21g_rwcb_keeps mem3 m G _ _ _ Hj32b HK); intros i Hi; apply HGF; cbn in Hi; lia.
Qed.


(* A readable byte read in one access. *)
Lemma r21g_rd1_of_mrd : forall m a b, 0 <= a < 2 ^ 64 ->
  MEM.mrd A.Img0.rsegs m (MEM.wa a) = Some b -> ov_read_bytes A.Img0.rsegs m (MEM.wa a) 1 = Some [b].
Proof.
  intros m a b Ha H. apply (R21S.r21_rdn m a [b] 1%nat); [|reflexivity].
  split; [lia|]. split; [cbn [length Z.of_nat Pos.of_succ_nat]; lia|].
  intros i Hi. destruct i as [|i]; [cbn [nth_error Z.of_nat]; rewrite Z.add_0_r; exact H | cbn [length] in Hi; lia].
Qed.

(* The loaded image tiles [0x10000, 0x5fe000) (A/ProgBridge.v rsegs_spans). *)
Lemma r21g_in_img : forall a, 0x10000 <= a < 0x5fe000 -> lib.Reusable.YG0d.in_img segs a.
Proof.
  intros a Ha. pose proof A.ProgBridge.rsegs_spans as E.
  assert (H : exists bz, In bz (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) A.Img0.rsegs) /\
                         fst bz <= a < fst bz + snd bz).
  { rewrite E. destruct (Z_lt_le_dec a 0x30000); [exists (0x10000, 0x20000); split; [left; reflexivity | cbn; lia]|].
    destruct (Z_lt_le_dec a 0x9e000); [exists (0x30000, 0x6e000); split; [right; left; reflexivity | cbn; lia]|].
    destruct (Z_lt_le_dec a 0xa1000); [exists (0x9e000, 0x3000); split; [right; right; left; reflexivity | cbn; lia]|].
    exists (0xa1000, 0x55d000); split; [right; right; right; left; reflexivity | cbn; lia]. }
  destruct H as ((b0 & z0) & Hin & Hr). apply in_map_iff in Hin as (sg & Esg & Hsg). injection Esg as Eb Ez.
  exists sg. split; [exact Hsg|]. cbn [fst snd] in Hr. lia.
Qed.

(* The input block of the entry (ctl_base): its length is c_n and it is empty or a live entry block. *)
Lemma r21g_base_input : forall cx, ACtlCut.ctl_base B MT XM_LIB RLO RHI cx ->
  ACtlCut.c_n cx = Z.of_nat (length (ACtlCut.c_in cx)) /\
  ((ACtlCut.c_n cx = 0 /\ ACtlCut.c_p cx = A.ACfn.A_EMPTY) \/
   (0 < ACtlCut.c_n cx < 2 ^ 26 /\
    In (ACtlCut.c_p cx, ACtlCut.c_n cx) (lib.Reusable.YG0d.ablocks B (ACtlCut.c_ly cx) (ACtlCut.c_S cx)))).
Proof. intros cx ((_ & _ & _ & _ & Hpn & Hlen & _) & _). split; [exact Hlen | exact Hpn]. Qed.

Lemma r21g_c_saddr : forall (a : Z) (b : byte),
  ART.shadow_ok a (bv_signed b) -> lib.Reusable.YG0v.saddr_ok a (bv_unsigned b).
Proof.
  intros a b H. unfold ART.shadow_ok, lib.Reusable.YG0v.saddr_ok in *.
  pose proof (bv_unsigned_in_range _ b) as Hr. change (bv_modulus 8) with 256 in Hr.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H.
  Z.div_mod_to_equations. lia.
Qed.

(* A present byte (in the core's sense) is read by the core's view. *)
Lemma r21g_c_present_view : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) a,
  lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m a ->
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m a <> None.
Proof.
  intros W m a (Hh & b & Hb). rewrite (r21g_a_mrd_view W m a Hh). unfold MEM.mrd, MEM.wa. rewrite Hb.
  cbn. discriminate.
Qed.

(* A visible byte of a byte run in memory is read by the core's view. *)
Lemma r21g_c_vis_range : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) x bs,
  MEM.bytes_at A.Img0.rsegs m x bs ->
  forall a, x <= a < x + Z.of_nat (length bs) -> lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m a <> None.
Proof.
  intros W m x bs (_ & _ & HB) a Ha Hh.
  destruct (nth_error bs (Z.to_nat (a - x))) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
  pose proof (HB (Z.to_nat (a - x)) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia.
  replace (x + (a - x)) with a in E by lia. rewrite Ec in E.
  rewrite (r21g_a_mrd_view W m a Hh), E. cbn. discriminate.
Qed.

(* Two visible NUL-terminated copies of one NUL-free string meet (r21g_str_meet) at its length, both ending in 0. *)
Lemma r21g_c_meet : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) x y (l : list byte),
  MEM.bytes_at A.Img0.rsegs m x (l ++ [Z_to_bv 8 0]) ->
  MEM.bytes_at A.Img0.rsegs m y (l ++ [Z_to_bv 8 0]) ->
  ~ In (Z_to_bv 8 0) l ->
  (forall a, x <= a <= x + Z.of_nat (length l) -> lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false) ->
  (forall a, y <= a <= y + Z.of_nat (length l) -> lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false) ->
  r21g_str_meet W m x y (Z.of_nat (length l)) 0 0.
Proof.
  intros W m x y l (_ & _ & HX) (_ & _ & HY) Hnz HVX HVY.
  rewrite length_app in HX, HY. cbn [length] in HX, HY.
  unfold r21g_str_meet. split; [lia|]. split; [|split; [|split; [|right; reflexivity]]].
  - intros i Hi.
    destruct (nth_error l (Z.to_nat i)) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    assert (Ec' : nth_error (l ++ [Z_to_bv 8 0]) (Z.to_nat i) = Some c)
      by (rewrite nth_error_app1 by lia; exact Ec).
    pose proof (HX (Z.to_nat i) ltac:(lia)) as Ex. rewrite Z2Nat.id in Ex by lia. rewrite Ec' in Ex.
    pose proof (HY (Z.to_nat i) ltac:(lia)) as Ey. rewrite Z2Nat.id in Ey by lia. rewrite Ec' in Ey.
    exists (bv_unsigned c). split; [|split].
    + rewrite (r21g_a_mrd_view W m (x + i) (HVX (x + i) ltac:(lia))), Ex. reflexivity.
    + rewrite (r21g_a_mrd_view W m (y + i) (HVY (y + i) ltac:(lia))), Ey. reflexivity.
    + intros E0. apply Hnz. assert (Ec0 : c = Z_to_bv 8 0) by (apply bv_eq; rewrite E0; reflexivity).
      subst c. exact (nth_error_In l (Z.to_nat i) Ec).
  - pose proof (HX (length l) ltac:(lia)) as Ex. rewrite nth_error_app2, Nat.sub_diag in Ex by lia.
    cbn [nth_error] in Ex.
    rewrite (r21g_a_mrd_view W m (x + Z.of_nat (length l)) (HVX (x + Z.of_nat (length l)) ltac:(lia))), Ex.
    reflexivity.
  - pose proof (HY (length l) ltac:(lia)) as Ey. rewrite nth_error_app2, Nat.sub_diag in Ey by lia.
    cbn [nth_error] in Ey.
    rewrite (r21g_a_mrd_view W m (y + Z.of_nat (length l)) (HVY (y + Z.of_nat (length l)) ltac:(lia))), Ey.
    reflexivity.
Qed.

(* A checked read-only image run (Lib.Image.ro_bytes_b) is in memory (ro_agree_at) and visible (w_Hoff: a hidden
   byte lies in no segment, a read-only byte lies in one). *)
Lemma r21g_c_ro_bytes : forall (W : lib.Reusable.YA0n.world segs) (bs : list byte) (m : word -> option byte) A0,
  A.ACtlK.ro_agree_at m ->
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Image.ro_bytes_b A.Img0.rsegs A0 bs = true ->
  0 <= A0 -> A0 + Z.of_nat (length bs) <= 2 ^ 64 ->
  MEM.bytes_at A.Img0.rsegs m A0 bs /\
  (forall a, A0 <= a < A0 + Z.of_nat (length bs) -> lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false).
Proof.
  intros W. induction bs as [|b bs IH]; intros m A0 Hro HB HA Hl.
  - split.
    + split; [lia|]. split; [cbn [length Z.of_nat]; lia|]. intros i Hi; cbn [length] in Hi; lia.
    + intros a Ha. cbn [length Z.of_nat] in Ha. lia.
  - cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Image.ro_bytes_b] in HB.
    match type of HB with context [match ?s with Some _ => _ | None => _ end] =>
      destruct s as [b'|] eqn:E; [|cbv beta iota in HB; discriminate HB] end.
    cbv beta iota in HB.
    apply andb_prop in HB as [HB1 HB3]. apply andb_prop in HB1 as [HBe HBro].
    unfold bv_eqb in HBe. apply Z.eqb_eq in HBe. apply bv_eq in HBe. subst b'.
    cbn [length] in Hl.
    destruct (IH m (A0 + 1) Hro HB3 ltac:(lia) ltac:(lia)) as [HB' HV'].
    split.
    + split; [lia|]. split; [cbn [length]; lia|].
      intros i Hi. destruct i as [|i].
      * replace (A0 + Z.of_nat 0) with A0 by lia. cbn [nth_error]. exact (eq_trans (Hro _ HBro) E).
      * replace (A0 + Z.of_nat (S i)) with (A0 + 1 + Z.of_nat i) by lia. cbn [nth_error].
        cbn [length] in Hi. exact (proj2 (proj2 HB') i ltac:(lia)).
    + intros a Ha. cbn [length] in Ha. destruct (Z.eq_dec a A0) as [->|Hne]; [|apply HV'; lia].
      destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 A0)) eqn:Hh; [|reflexivity]. exfalso.
      assert (Hn : find_segment A.Img0.rsegs (bv_unsigned (Z_to_bv 64 A0)) 1 = None)
        by exact (lib.Reusable.YA0n.w_Hoff W _ Hh).
      change (MEM.ro_addr A.Img0.rsegs (Z_to_bv 64 A0) = true) in HBro.
      unfold MEM.ro_addr in HBro. rewrite Hn in HBro. discriminate HBro.
Qed.

(* The core's range_addressable over a sub-range of ctrl's addressable range whose shadow bytes are visible. *)
Lemma r21g_c_raddr : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) p n q k,
  ART.addressable m p n -> p <= q -> q + k <= p + n ->
  (forall a, q <= a < q + k -> lib.Reusable.YA0n.w_H W (Z_to_bv 64 (ART.shadow_addr a)) = false) ->
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m)
    lib.Reusable.YG0f.SHADOW_OFF q k.
Proof.
  intros W m p n q k (_ & _ & _ & HA) Hq Hk HV a Ha.
  destruct (HA (a - p) ltac:(lia)) as (_ & b & Hb & Hok).
  replace (p + (a - p)) with a in Hb, Hok by lia.
  exists (bv_unsigned b).
  replace (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF a) with (ART.shadow_addr a)
    by (unfold lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF, ART.shadow_addr, ART.ASAN_K; lia).
  rewrite (r21g_a_mrd_view W m _ (HV a Ha)).
  split; [|exact (r21g_c_saddr a b Hok)].
  assert (Hb' : MEM.mrd A.Img0.rsegs m (MEM.wa (ART.shadow_addr a)) = Some b) by exact Hb.
  rewrite Hb'. reflexivity.
Qed.

(* A shadow byte of a frame byte in [fr, fr + 4080] is one of the frame's 512 shadow bytes. *)
Lemma r21g_c_fsh : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) fr a,
  (forall i, 0 <= i < 512 ->
     lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m (lib.Reusable.YG0f.shadow_addr fr + i)) ->
  fr <= a <= fr + 4080 -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m (ART.shadow_addr a).
Proof.
  intros W m fr a HS Ha.
  assert (Hi : 0 <= ART.shadow_addr a - lib.Reusable.YG0f.shadow_addr fr < 512).
  { unfold ART.shadow_addr, ART.ASAN_K, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
    Z.div_mod_to_equations. lia. }
  pose proof (HS _ Hi) as H.
  replace (lib.Reusable.YG0f.shadow_addr fr + (ART.shadow_addr a - lib.Reusable.YG0f.shadow_addr fr))
    with (ART.shadow_addr a) in H by lia.
  exact H.
Qed.

(* The shadow hull of a range inside [fr + 64, fr + 4000) lies in the frame's 512 shadow bytes, so it is read. *)
Lemma r21g_c_hull : forall (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) fr x n,
  (forall i, 0 <= i < 512 ->
     lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m (lib.Reusable.YG0f.shadow_addr fr + i)) ->
  fr + 64 <= x -> x + n <= fr + 4000 ->
  lib.Reusable.YG0d.shadow_hull_vis (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m) x n.
Proof.
  intros W m fr x n HS Hx Hxn s Hs.
  assert (Hi : 0 <= s - lib.Reusable.YG0f.shadow_addr fr < 512).
  { unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF in *. Z.div_mod_to_equations. lia. }
  pose proof (HS _ Hi) as H.
  replace (lib.Reusable.YG0f.shadow_addr fr + (s - lib.Reusable.YG0f.shadow_addr fr)) with s in H by lia.
  exact (r21g_c_present_view W m s H).
Qed.

(* ===== the strcmp call's two strings, at any state with AR: the record's name field (fr + 2176 + 3) and the
   catalogue row's name string (read-only image), in the CORE's premise forms.  A Theorem Labs lane. ===== *)
Lemma r21g_str_facts : forall ly S (W : lib.Reusable.YA0n.world segs) (m : word -> option byte) md (inp : list byte) (fr : Z),
  lib.Reusable.YG0n.AR segs B ly S W m md ->
  A.ACtlRtC.ctl_rt_C B ly S m ->
  MEM.bytes_at A.Img0.rsegs m (fr + 2176) (A.Prog.SlotModel.RID inp 7) ->
  ART.addressable m (fr + 2176) 38 ->
  (forall a, fr <= a < fr + 4096 -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m a) ->
  (forall i, 0 <= i < 512 -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m (lib.Reusable.YG0f.shadow_addr fr + i)) ->
  0 <= fr -> fr + 4096 <= lib.Reusable.YM05.alloc_ceiling ->
  (fr + 4096 <= ART.LOWMEM_END \/ ART.HIGHMEM_BEG <= fr) ->
  Prog.RcSynth.rw32 (A.Prog.SlotModel.rowb (A.Prog.SlotModel.istar inp)) 56 <> 0 ->
  let nm := Prog.RcSynth.rname (A.Prog.SlotModel.rowb (A.Prog.SlotModel.istar inp)) in
  let kk := Z.of_nat (length (removelast (A.Prog.SlotModel.rt_nb inp))) in
  r21g_str_meet W m (fr + 2176 + 3) nm kk 0 0 /\
  (forall a, fr + 2176 + 3 <= a < fr + 2176 + 3 + (kk + 1) ->
     lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m a <> None) /\
  (forall a, nm <= a < nm + (kk + 1) ->
     lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m a <> None) /\
  lib.Reusable.YG0d.amem_range (fr + 2176 + 3) (kk + 1) /\ lib.Reusable.YG0d.amem_range nm (kk + 1) /\
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m)
    lib.Reusable.YG0f.SHADOW_OFF (fr + 2176 + 3) (kk + 1) /\
  lib.Reusable.YG0d.shadow_hull_vis (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m)
    (fr + 2176 + 3) (kk + 1) /\
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m)
    lib.Reusable.YG0f.SHADOW_OFF nm (kk + 1) /\
  lib.Reusable.YG0d.shadow_hull_vis (lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m) nm (kk + 1) /\
  0 < nm /\ nm + kk + 1 <= 2 ^ 63 /\ kk + 1 < 2 ^ 32 /\ kk + 1 <= 16.
Proof.
  intros ly S W m md inp fr HAR Hrt HID HADid Hfp Hsp Hfr0 Hfrc Hlh Hh0. cbv zeta.
  destruct Hrt as (_ & _ & _ & Hro).
  pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [Hce _]. unfold lib.Reusable.YG0f.ASAN_CEIL in Hce.
  pose proof (RTM.a_istar_range inp) as Hi11.
  destruct (RTM.a_row_facts (A.Prog.SlotModel.istar inp) Hi11) as (_ & Ehid & Hnmf).
  assert (Hhid : Prog.RcEmit.em_hid (A.Prog.SlotModel.rowb (A.Prog.SlotModel.istar inp)) <> 0)
    by (intros E; apply Hh0; apply Ehid; exact E).
  destruct (Hnmf Hhid) as (Hnm0 & Hnm1 & HRO & _).
  (* the round trip's name string rt_nb: NUL-terminated, NUL-free before, 2 to 16 bytes (B3Rtm.v RTM) *)
  assert (Hn6 : A.Prog.SlotModel.rt_n inp 6 <> 0) by (apply (proj2 (RTM.a_rtm_hid inp)); exact Hhid).
  destruct (RTM.a_rtm_name inp Hn6) as (_ & Efn & Elast & Hall & Hlen16).
  apply andb_true_iff in Hlen16 as [Hl1 Hl2]. apply Nat.leb_le in Hl1. apply Nat.leb_le in Hl2.
  assert (Elast' : last (A.Prog.SlotModel.rt_nb inp) (Z_to_bv 8 1) = Z_to_bv 8 0) by exact Elast.
  assert (Enb : A.Prog.SlotModel.rt_nb inp = removelast (A.Prog.SlotModel.rt_nb inp) ++ [Z_to_bv 8 0]).
  { rewrite <- Elast'. apply app_removelast_last. intros E. rewrite E in Hl1. cbn [length] in Hl1. lia. }
  assert (HLsx : (length (removelast (A.Prog.SlotModel.rt_nb inp)) + 1 = length (A.Prog.SlotModel.rt_nb inp))%nat)
    by (rewrite Enb at 2; rewrite length_app; cbn [length]; lia).
  assert (HNin : ~ In (Z_to_bv 8 0) (removelast (A.Prog.SlotModel.rt_nb inp))).
  { intros Hin. pose proof (proj1 (forallb_forall _ _) Hall (Z_to_bv 8 0) Hin) as X.
    vm_compute in X. discriminate X. }
  (* x: the record's name field fr + 2176 + 3 holds rt_nb (Seg/R21.v:1712-1719) *)
  pose proof (R21S.a_RID_len inp 7) as HIDL.
  assert (HBX : MEM.bytes_at A.Img0.rsegs m (fr + 2176 + 3) (A.Prog.SlotModel.rt_nb inp)).
  { assert (Es : firstn (length (A.Prog.SlotModel.rt_nb inp)) (skipn 3 (A.Prog.SlotModel.RID inp 7)) =
                 A.Prog.SlotModel.rt_nb inp).
    { rewrite <- Efn at 2. unfold Prog.RcIdentModel.model_name, Prog.RcIdentModel.get,
        Prog.RcIdentModel.OFF_NAME, Prog.RcIdentModel.NAME_CAP. rewrite firstn_firstn. f_equal. lia. }
    pose proof (R21S.a_sub m (fr + 2176) (A.Prog.SlotModel.RID inp 7) 3 (length (A.Prog.SlotModel.rt_nb inp)) HID
                  ltac:(rewrite HIDL; lia)) as X.
    rewrite Es in X. replace (fr + 2176 + Z.of_nat 3) with (fr + 2176 + 3) in X by lia. exact X. }
  (* y: the row's name string nm holds rt_nb, read-only image bytes, visible *)
  destruct (r21g_c_ro_bytes W (A.Prog.SlotModel.rt_nb inp) m
              (Prog.RcSynth.rname (A.Prog.SlotModel.rowb (A.Prog.SlotModel.istar inp))) Hro HRO ltac:(lia) ltac:(lia))
    as [HBY HVY].
  pose proof HBX as HBX'. rewrite Enb in HBX'.
  pose proof HBY as HBY'. rewrite Enb in HBY'.
  (* nm's shadow: r21g_name_shadow, at length img_cstr nm 16 = rt_nb = kk + 1 *)
  pose proof (r21g_name_shadow ly S W m md HAR (A.Prog.SlotModel.istar inp) Hi11 Hhid) as HNS. cbv zeta in HNS.
  change (A.Prog.SlotModel.img_cstr (Prog.RcSynth.rname (A.Prog.SlotModel.rowb (A.Prog.SlotModel.istar inp))) 16)
    with (A.Prog.SlotModel.rt_nb inp) in HNS.
  replace (Z.of_nat (length (A.Prog.SlotModel.rt_nb inp)))
    with (Z.of_nat (length (removelast (A.Prog.SlotModel.rt_nb inp))) + 1) in HNS by lia.
  destruct HNS as [HRAy HHVy].
  split.
  { apply (r21g_c_meet W m _ _ (removelast (A.Prog.SlotModel.rt_nb inp)) HBX' HBY' HNin).
    - intros a Ha. exact (proj1 (Hfp a ltac:(lia))).
    - intros a Ha. apply HVY. lia. }
  split.
  { intros a Ha. apply (r21g_c_present_view W m a). apply Hfp. lia. }
  split.
  { intros a Ha. apply (r21g_c_vis_range W m _ _ HBY); [lia | apply HVY; lia]. }
  split.
  { unfold lib.Reusable.YG0d.amem_range, lib.Reusable.YG0f.kLowMemEnd, lib.Reusable.YG0f.kHighMemBeg,
      lib.Reusable.YG0f.kHighMemEnd.
    unfold ART.LOWMEM_END, ART.HIGHMEM_BEG in Hlh.
    destruct Hlh as [Hl|Hh]; [left | right]; lia. }
  split.
  { unfold lib.Reusable.YG0d.amem_range, lib.Reusable.YG0f.kLowMemEnd. left. lia. }
  split.
  { apply (r21g_c_raddr W m (fr + 2176) 38); [exact HADid | lia | lia |].
    intros a Ha. exact (proj1 (r21g_c_fsh W m fr a Hsp ltac:(lia))). }
  split.
  { apply (r21g_c_hull W m fr); [exact Hsp | lia | lia]. }
  split; [exact HRAy|]. split; [exact HHVy|].
  split; [lia|]. split; [lia|]. split; lia.
Qed.

(* ===================================================================================================== *)
Lemma glue_seg_R21 : forall POST (b : nat),
  CF POST (ix_cut C_A815cc_at [Z.of_nat (S b)]) -> CF POST C_A81ac0 -> CF POST C_A81ac8 -> CF POST (ix_cut C_A81924_at [Z.of_nat b]).
Proof.
  intros POST b HX5 HX0 HX8 cx idx fr k ly3 S3 W3 regs3 mem3 md3 HB HJ HF HL Hk Hbody Hrt.
  (* G1: the entry cut at index [Z.of_nat b] (ix_cut, ACtlCut.v:232-234; C_A81924_at, ACtlCutP.v:1683-1706). *)
  destruct Hbody as [Hidx Hb]. subst idx.
  cbv beta iota zeta delta [ACtlCut.cut_body ACtlCutP.C_A81924_at ACtlCutP.ixn ACtlCutP.ixz nth] in Hb.
  rewrite Nat2Z.id in Hb.
  destruct Hb as (HP & HFRAC & Hn & Hb6 & R23 & HOUR & HOUTA & HRB & S128 & HPRO & S104 & S96 & S64 & R21 &
    S112 & S144 & S192 & Hid & Hjk & S280 & S240 & Hjy & Hjk32 & S152 & HAD & HRXS).
  cbv beta iota zeta delta [ACtlCut.cut_kmax ACtlCut.ix_cut ACtlCutP.C_A81924_at ACtlCutP.ixn nth] in Hk.
  rewrite Nat2Z.id in Hk.
  (* G2: the frame, the spill base and the stack, from visible state *)
  destruct (r21g_frame cx fr k ly3 S3 W3 mem3 md3 HJ HF HL)
    as (Efr & Hfr4096 & Hfrceil & Hfrapp & Hfr32 & Hfrpres & Hshpres).
  pose proof HFRAC as (A & sp & R2 & Hsp16 & HspZ & R4 & R8 & R9 & R3 & R19 & R26 & Hfr32' & HA32 & HAS & HspA &
    HfrA & HA416 & HSsp & HSapp & Q304 & Q24 & Q16 & Qh1 & Qh2 & Hsh & Hsaved & _).
  pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
  pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
  pose proof lib.Reusable.YCbq.asan_consts as (Cc & _).
  unfold ACtlCutP.FRAME_BYTES, ART.APPMEM_END, A.ACfn.LLVMF_STK in *.
  assert (Hfr8 : fr / 8 <= fr) by (apply Z.div_le_upper_bound; lia).
  assert (ESH : lib.Reusable.YG0f.shadow_addr fr = ART.shadow_addr fr)
    by (unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, ART.shadow_addr, ART.ASAN_K; lia).
  assert (HSHb : 0 <= ART.shadow_addr fr /\ ART.shadow_addr fr + 512 <= A).
  { unfold ART.shadow_addr, ART.ASAN_K. pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)). lia. }
  assert (HSTK : FRM.stk A.Img0.rsegs mem3 (ART.shadow_addr fr + 296) (ART.shadow_addr fr + 313)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    apply (r21g_present_stk (lib.Reusable.YA0n.w_H W3) mem3 a).
    replace a with (lib.Reusable.YG0f.shadow_addr fr + (a - lib.Reusable.YG0f.shadow_addr fr)) by lia.
    apply Hshpres. lia. }
  assert (HQ128 : MEM.bytes_at A.Img0.rsegs mem3 (A + 128) (MEM.le8 (Z_to_bv 64 (fr + 544))))
    by exact (r21g_spill_A regs3 mem3 128 (fr + 544) A R9 ltac:(lia) ltac:(lia) ltac:(lia) S128).
  assert (GSH : Lib.ExecF.rng (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) (ART.shadow_addr fr + 296) 17).
  { apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|]. intros a Ha.
    replace a with (lib.Reusable.YG0f.shadow_addr fr + (a - lib.Reusable.YG0f.shadow_addr fr)) by lia.
    exact (proj1 (Hshpres (a - lib.Reusable.YG0f.shadow_addr fr) ltac:(lia))). }
  assert (GSTK : forall lo len, ACtlCut.c_sp cx - 32768 <= lo -> lo + len <= ACtlCut.c_sp cx -> 0 <= len ->
                   A.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W3) lo len).
  { intros lo len H1 H2 H3. split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (Hpres a ltac:(lia))). }
  assert (G128 : Lib.ExecF.rng (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) (A + 128) 8)
    by (apply A.ProgBridge.rng_of_visible; apply GSTK; lia).
  (* G3: the cut's configuration in the runs' state form, and the walk moved to mkR_of regs3 *)
  rewrite A.ProgBridge.cfg_at_MS.
  change (ACtlCut.cut_pc (ix_cut C_A81924_at [Z.of_nat b])) with 0x81924.
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of regs3) regs3 K11.fp_regs
           (Z_to_bv 64 0x81924) K11.fp_csr None mem3 (K11.seg_rom segs) md3 (POST cx));
    [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv regs3))].
  (* the latch window: every application byte and every shadow byte off [fr + 2368, fr + 2504) is outside it *)
  assert (Hwapp : forall x, (x < ART.LOWMEM_END \/ ART.HIGHMEM_BEG <= x) -> FRM.outside (r21g_win fr) x)
    by (intros x Hx; apply r21g_win_app; [lia | unfold ART.APPMEM_END; lia | exact Hx]).
  assert (Hfrlow : fr + 4096 <= ART.LOWMEM_END \/ ART.HIGHMEM_BEG <= fr).
  { destruct Hfrapp as (_ & [Hl | (Hh & _)]); [left | right];
      unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg, ART.LOWMEM_END, ART.HIGHMEM_BEG in *; lia. }
  assert (HG : forall a, (a < ART.LOWMEM_END \/ ART.HIGHMEM_BEG <= a) -> 0 <= a < 2 ^ 64 ->
                 0 <= a < 2 ^ 64 /\ FRM.outside (r21g_win fr) a)
    by (intros a Ha Hb64; split; [exact Hb64 | exact (Hwapp a Ha)]).
  assert (HGsh : forall y, 0 <= y -> ~ (fr + 2368 <= y < fr + 2504) -> y < 2 ^ 63 ->
                   0 <= ART.shadow_addr y < 2 ^ 64 /\ FRM.outside (r21g_win fr) (ART.shadow_addr y)).
  { intros y Hy0 Hy Hy1. split; [unfold ART.shadow_addr, ART.ASAN_K; pose proof (Z.div_pos y 8 Hy0 ltac:(lia));
      assert (y / 8 <= y) by (apply Z.div_le_upper_bound; lia); lia|].
    apply r21g_win_shadow; [lia | exact Hy]. }
  assert (HAhi : ART.HIGHMEM_BEG <= A) by (unfold ART.HIGHMEM_BEG; lia).
  assert (HGA : forall a, A <= a < A + 312 -> 0 <= a < 2 ^ 64 /\ FRM.outside (r21g_win fr) a)
    by (intros a Ha; apply HG; [right; lia | lia]).
  assert (HGS : forall a, ACtlCut.c_sp cx - 4096 < a < ACtlCut.c_sp cx ->
                  0 <= a < 2 ^ 64 /\ FRM.outside (r21g_win fr) a)
    by (intros a Ha; apply HG; [right; unfold ART.HIGHMEM_BEG; lia | lia]).
  assert (HGF : forall a, fr <= a < fr + 4096 -> 0 <= a < 2 ^ 64 /\ FRM.outside (r21g_win fr) a)
    by (intros a Ha; apply HG; [destruct Hfrlow; [left | right]; lia | lia]).
  assert (HGFs : forall o n i, 0 <= o -> o + n <= 2368 \/ 2504 <= o -> o + n <= 4096 -> 0 <= i < n ->
                   0 <= ART.shadow_addr (fr + o + i) < 2 ^ 64 /\
                   FRM.outside (r21g_win fr) (ART.shadow_addr (fr + o + i)))
    by (intros o n i Ho Hon Hn4 Hi; apply HGsh; lia).
  destruct (r21g_base_input cx HB) as (Hlen & Hpn).
  assert (HIN : forall i, 0 <= i < Z.of_nat (length (ACtlCut.c_in cx)) ->
                  (ACtlCut.c_p cx + i < ART.LOWMEM_END \/ ART.HIGHMEM_BEG <= ACtlCut.c_p cx + i) /\
                  0 <= ACtlCut.c_p cx + i < 2 ^ 63 /\ ~ (fr <= ACtlCut.c_p cx + i < fr + 4096) /\
                  lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W3) mem3 (ACtlCut.c_p cx + i) /\
                  ACtlCut.c_p cx + i < lib.Reusable.YM05.alloc_ceiling).
  { intros i Hi. destruct Hpn as [(Hn0 & _) | (Hn0 & Hpin)]; [lia|].
    assert (Hin3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (lib.Reusable.YG0d.ablocks B ly3 S3))
      by exact (Permutation_in _ (Permutation_sym HP) Hpin).
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin3)
      as (_ & Hp4096 & Hpceil & Hpapp & Hppres & _).
    pose proof (lib.Reusable.YCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)) as Hrq.
    assert (Hinf : In (6, ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
    pose proof (lib.Reusable.YCbq.sep_block_frame segs B LAWS ly3 S3 W3 mem3 md3 _ _ 6 (ACtlCut.c_fpos cx)
                  HAR Hin3 Hinf) as Hd.
    unfold lib.Reusable.YG0f.zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efr in Hd.
    change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096 in Hd.
    assert (Hpres0 : lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W3) mem3 (ACtlCut.c_p cx + i))
      by exact (proj1 (Hppres (ACtlCut.c_p cx + i) ltac:(lia))).
    destruct Hpapp as (_ & [Hl | (Hh & _)]);
      unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg, ART.LOWMEM_END,
        ART.HIGHMEM_BEG in *;
      (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; [exact Hpres0 | lia]). }
  pose proof (@lib.Reusable.YM05.alloc_ceiling_value rc) as Hceilv.
  (* a shadow byte of the frame: visible, and below the allocator ceiling (so below the callee stack windows) *)
  assert (HshFr : forall j, 0 <= j < 4096 ->
            lib.Reusable.YA0n.w_H W3 (Z_to_bv 64 (ART.shadow_addr (fr + j))) = false /\
            0 <= ART.shadow_addr (fr + j) < lib.Reusable.YM05.alloc_ceiling).
  { intros j Hj.
    assert (Hd8 : (32 | fr)) by (apply Z.mod_divide; [lia | exact Hfr32]).
    destruct Hd8 as (q & Hq).
    assert (E8 : ART.shadow_addr (fr + j) = lib.Reusable.YG0f.shadow_addr fr + j / 8).
    { unfold ART.shadow_addr, ART.ASAN_K, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF.
      rewrite Hq. replace (q * 32 + j) with (j + q * 4 * 8) by lia. rewrite Z.div_add by lia.
      replace (q * 32) with (q * 4 * 8) by lia. rewrite Z.div_mul by lia. lia. }
    split.
    - rewrite E8.
      exact (proj1 (Hshpres (j / 8)
               ltac:(split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]))).
    - unfold ART.shadow_addr, ART.ASAN_K.
      assert (Hle : (fr + j) / 8 <= fr + j) by (apply Z.div_le_upper_bound; lia).
      assert (Hge : 0 <= (fr + j) / 8) by (apply Z.div_pos; lia). lia. }
  (* a shadow byte of the live input block: visible (its view reads the block's shadow), below the ceiling *)
  assert (HshIn : 0 < ACtlCut.c_n cx -> forall i, 0 <= i < ACtlCut.c_n cx ->
            lib.Reusable.YA0n.w_H W3 (Z_to_bv 64 (ART.shadow_addr (ACtlCut.c_p cx + i))) = false /\
            0 <= ART.shadow_addr (ACtlCut.c_p cx + i) < lib.Reusable.YM05.alloc_ceiling).
  { intros Hn0 i Hi. destruct Hpn as [(Hz & _) | (_ & Hpin)]; [lia|].
    assert (Hin3 : In (ACtlCut.c_p cx, ACtlCut.c_n cx) (lib.Reusable.YG0d.ablocks B ly3 S3))
      by exact (Permutation_in _ (Permutation_sym HP) Hpin).
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin3)
      as (_ & Hp4096 & Hpceil & _ & _ & _).
    destruct (lib.Reusable.YG0d.al_shadow _ _ LAWS ly3 S3 W3 mem3 md3 _ _ HAR Hin3) as (Hbs & _).
    pose proof (lib.Reusable.YCbq.req_size_pos (ACtlCut.c_n cx) ltac:(lia)) as Hrq.
    destruct Hbs as (Hp8 & Hn8 & Hbs).
    assert (Hd8 : (8 | ACtlCut.c_p cx)) by (apply Z.mod_divide; [lia | exact Hp8]).
    destruct Hd8 as (q & Hq).
    assert (E8 : ART.shadow_addr (ACtlCut.c_p cx + i) =
                 lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF (ACtlCut.c_p cx) + i / 8).
    { unfold ART.shadow_addr, ART.ASAN_K, lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF.
      rewrite Hq. replace (q * 8 + i) with (i + q * 8) by lia. rewrite Z.div_add by lia.
      rewrite Z.div_mul by lia. lia. }
    split.
    - apply (A.ProgWorldVisFrame.vis_of_aview segs W3 mem3). rewrite E8.
      rewrite (Hbs (i / 8) ltac:(split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia])).
      discriminate.
    - unfold ART.shadow_addr, ART.ASAN_K.
      assert (Hle : (ACtlCut.c_p cx + i) / 8 <= ACtlCut.c_p cx + i) by (apply Z.div_le_upper_bound; lia).
      assert (Hge : 0 <= (ACtlCut.c_p cx + i) / 8) by (apply Z.div_pos; lia). lia. }
  (* the frame's 392 shadow bytes stay readable across the latch (stk inside the window, munch outside) *)
  assert (HFSH : forall m', FRM.munch (r21g_win fr) mem3 m' ->
                   FRM.stk A.Img0.rsegs m' (ART.shadow_addr fr + 296) (ART.shadow_addr fr + 313) ->
                   forall i, 0 <= i < 392 -> exists b, MEM.mrd A.Img0.rsegs m' (MEM.wa (ACtlCutP.Sfr fr + i)) = Some b).
  { intros m' MU STk i Hi. unfold ACtlCutP.Sfr.
    destruct (Z_lt_le_dec i 296) as [L1 | L1]; [| destruct (Z_lt_le_dec i 313) as [L2 | L2]].
    2: { exact (proj2 (proj2 (proj2 STk) (ART.shadow_addr fr + i) ltac:(lia))). }
    all: assert (Hg : 0 <= ART.shadow_addr fr + i < 2 ^ 64 /\ FRM.outside (r21g_win fr) (ART.shadow_addr fr + i))
           by (split; [lia | unfold r21g_win; cbn [FRM.outside]; split; [lia | exact I]]).
    all: rewrite (proj1 (r21g_keeps_munch _ mem3 m' MU _ Hg)).
    all: rewrite <- ESH; exact (proj2 (r21g_present_stk _ _ _ (Hshpres i ltac:(lia)))). }
  destruct HRB as (_ & HCUR & _ & _ & HIDB & HFGB).
  destruct (Nat.eq_dec b 6) as [E6 | E6].
  - (* b = 6: the latch falls through to the tail at 0x81990 (turn 7's identity record against the catalogue row istar) *)
    subst b.
    pose proof (r21g_latch_last_run (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) regs3 mem3 (ART.shadow_addr fr)
                  A (fr + 544) R19 R9 R23 ltac:(lia) ltac:(lia) ltac:(lia) HSTK HQ128 GSH G128) as HRUN.
    pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
    rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
    apply (lib.Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3
             (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) _ (POST cx) HFS).
    { exact (A.ProgBridge.fp_avoids_RNG_W _). }
    intros ms' md' HQ0 Hhid Hsbm.
    destruct HQ0 as (R & m' & Ems & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K25 & K26 & MU & WM & STk).
    subst ms'. cbn [ms_mem LBMS.MS] in Hhid.
    pose proof (r21g_latch_journal cx fr k ly3 S3 W3 mem3 md3 m' md' HJ Efr ltac:(lia) MU STk Hhid Hsbm) as HJ'.
    pose proof (r21g_ctlrt_munch _ _ _ _ _ mem3 m' Hrt MU STk ltac:(unfold ART.shadow_addr, ART.ASAN_K;
                  pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)); lia)) as Hrt'.
    pose proof (r21g_keeps_munch _ mem3 m' MU) as HK.
    pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres' & _).
    (* the turn-7 identity record and the catalogue row istar, at m' *)
    pose proof (RTM.a_istar_range (ACtlCut.c_in cx)) as Hi11.
    assert (Hmr : A.Prog.SlotModel.mrow (ACtlCut.c_in cx) =
                  A.Prog.SlotModel.CAT + A.Prog.SlotModel.CAT_ROW * A.Prog.SlotModel.istar (ACtlCut.c_in cx))
      by reflexivity.
    assert (Hmrlo : A.Prog.SlotModel.CAT <= A.Prog.SlotModel.mrow (ACtlCut.c_in cx) /\
                    A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 296 <= A.Prog.SlotModel.CAT + 3256)
      by (rewrite Hmr; unfold A.Prog.SlotModel.CAT_ROW; lia).
    assert (Hmr8 : A.Prog.SlotModel.mrow (ACtlCut.c_in cx) mod 8 = 0)
      by (rewrite Hmr; unfold A.Prog.SlotModel.CAT, A.Prog.SlotModel.CAT_ROW; Z.div_mod_to_equations; lia).
    pose proof (A.Prog.Seg.Tac_rt2_b2.a_row_len (A.Prog.SlotModel.istar (ACtlCut.c_in cx))) as HROWL.
    pose proof (R21S.a_RID_len (ACtlCut.c_in cx) 7) as HIDL.
    assert (Hfrnimg : forall a, fr <= a < fr + 4096 -> ~ lib.Reusable.YG0d.in_img segs a).
    { intros a Ha. assert (Hinf : In (6, ACtlCut.c_fpos cx) (lib.Reusable.YG01.frames S3)) by (rewrite HF; left; reflexivity).
      apply (lib.Reusable.YCbq.frm_img segs B LAWS ly3 S3 W3 mem3 md3 6 (ACtlCut.c_fpos cx) a HAR Hinf).
      rewrite Efr. change (lib.Reusable.YG00.fs_frame_bytes 6) with 4096. exact Ha. }
    assert (HGcat : forall a, A.Prog.SlotModel.CAT <= a < A.Prog.SlotModel.CAT + 3256 ->
                      0 <= a < 2 ^ 64 /\ FRM.outside (r21g_win fr) a)
      by (intros a Ha; apply HG; [left; unfold A.Prog.SlotModel.CAT, ART.LOWMEM_END in *; lia
                                 | unfold A.Prog.SlotModel.CAT in *; lia]).
    assert (IDB7 : MEM.bytes_at A.Img0.rsegs m' (fr + 2176) (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7)).
    { apply (r21g_bytes_keeps mem3 m' _ _ _ HIDB HK). change (S 6) with 7%nat in *.
      rewrite HIDL. intros i Hi. apply HGF. lia. }
    assert (NROW : MEM.bytes_at A.Img0.rsegs m' (A.Prog.SlotModel.mrow (ACtlCut.c_in cx))
                     (A.Prog.SlotModel.rowb (A.Prog.SlotModel.istar (ACtlCut.c_in cx)))).
    { apply (r21g_bytes_keeps mem3 m' _ _ _
               (r21g_cat_rows cx (ACtlCut.own6 cx) ly3 S3 W3 mem3 md3 k HB HJ _ Hi11) HK).
      rewrite HROWL. intros i Hi. apply HGcat. lia. }
    assert (HCATSH : forall q, A.Prog.SlotModel.CAT <= q < A.Prog.SlotModel.CAT + 3256 ->
               MEM.mrd A.Img0.rsegs m' (MEM.wa (ART.shadow_addr q)) = Some (Z_to_bv 8 0) /\
               lib.Reusable.YA0n.w_H W3 (Z_to_bv 64 (ART.shadow_addr q)) = false).
    { intros q Hq. destruct (r21g_cat_shadow ly3 S3 W3 mem3 md3 HAR q Hq) as (E & Hv). split; [|exact Hv].
      assert (Hg : 0 <= ART.shadow_addr q < 2 ^ 64 /\ FRM.outside (r21g_win fr) (ART.shadow_addr q)).
      { apply HGsh; [unfold A.Prog.SlotModel.CAT in Hq; lia | | unfold A.Prog.SlotModel.CAT in Hq; lia].
        intros Hqf. apply (Hfrnimg q ltac:(lia)). apply r21g_in_img. unfold A.Prog.SlotModel.CAT in Hq. lia. }
      rewrite (proj1 (HK _ Hg)). exact E. }
    assert (RK : forall q, A.Prog.SlotModel.CAT <= q < A.Prog.SlotModel.CAT + 3256 ->
               ov_read_bytes A.Img0.rsegs m' (MEM.wa (Z.shiftr q 3 + ART.ASAN_K)) 1 = Some [Z_to_bv 8 0]).
    { intros q Hq. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      apply r21g_rd1_of_mrd; [| exact (proj1 (HCATSH q Hq))].
      unfold A.Prog.SlotModel.CAT, ART.ASAN_K in *. pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
      assert (q / 8 <= q) by (apply Z.div_le_upper_bound; lia). lia. }
    assert (GK : forall q, A.Prog.SlotModel.CAT <= q < A.Prog.SlotModel.CAT + 3256 ->
               Lib.ExecF.rng (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) (Z.shiftr q 3 + ART.ASAN_K) 1).
    { intros q Hq. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. apply A.ProgBridge.rng_of_visible.
      unfold A.Prog.SlotModel.CAT in Hq. pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
      assert (q / 8 <= q) by (apply Z.div_le_upper_bound; lia).
      split; [unfold ART.ASAN_K; lia|]. split; [unfold ART.ASAN_K; lia|]. intros a Ha.
      replace a with (ART.shadow_addr q) by (unfold ART.shadow_addr; lia). exact (proj2 (HCATSH q ltac:(unfold A.Prog.SlotModel.CAT; lia))). }
    assert (Gcat : forall lo len, A.Prog.SlotModel.CAT <= lo -> lo + len <= A.Prog.SlotModel.CAT + 3256 -> 0 <= len ->
                     Lib.ExecF.rng (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) lo len).
    { intros lo len H1 H2 H3. apply A.ProgBridge.rng_of_visible.
      apply (A.ProgBridge.range_visible_sub _ ImgBounds.IMG_LO (ImgBounds.IMG_HI - ImgBounds.IMG_LO));
        [exact (A.ProgBridge.img_vis_W W3) | | | ]; unfold ImgBounds.IMG_LO, ImgBounds.IMG_HI, A.Prog.SlotModel.CAT in *; lia. }
    assert (Gfr : forall lo len, fr <= lo -> lo + len <= fr + 4096 -> 0 <= len ->
                    Lib.ExecF.rng (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) lo len).
    { intros lo len H1 H2 H3. apply A.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
      intros a Ha. exact (proj1 (Hfrpres a ltac:(lia))). }
    assert (Gst : forall lo len, ACtlCut.c_sp cx - 32768 <= lo -> lo + len <= ACtlCut.c_sp cx -> 0 <= len ->
                    Lib.ExecF.rng (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) lo len)
      by (intros lo len H1 H2 H3; apply A.ProgBridge.rng_of_visible; apply GSTK; lia).
    (* the model facts of turn 7 (B3Rtm.v) *)
    destruct (RTM.a_rtm_fw (ACtlCut.c_in cx)) as (Ehf & Efw).
    destruct (RTM.a_rtm_ver (ACtlCut.c_in cx)) as (Ehv & Emaj & Emin & Epat).
    destruct (RTM.a_row_facts (A.Prog.SlotModel.istar (ACtlCut.c_in cx)) Hi11) as (Hh32 & Ehid & Hnmf).
    destruct (RTM.a_row_le (A.Prog.SlotModel.istar (ACtlCut.c_in cx)) Hi11) as (L56 & L280).
    (* the tail's reads (Seg/R21.v:1568-1642, the same derivations over this unit's facts) *)
    assert (R2' : ov_read_bytes A.Img0.rsegs m' (MEM.wa (fr + 2176 + 2)) 1 = Some [Z_to_bv 8 1]).
    { pose proof (R21S.a_rd1 m' (fr + 2176) (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7) 2 IDB7
                    ltac:(rewrite HIDL; lia)) as H.
      replace (fr + 2176 + Z.of_nat 2) with (fr + 2176 + 2) in H by lia.
      rewrite (R21S.a_byte1 (nth 2 (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7) (Z_to_bv 8 0)) Ehf) in H. exact H. }
    assert (R36 : ov_read_bytes A.Img0.rsegs m' (MEM.wa (fr + 2176 + 36)) 1 = Some [Z_to_bv 8 1]).
    { pose proof (R21S.a_rd1 m' (fr + 2176) (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7) 36 IDB7
                    ltac:(rewrite HIDL; lia)) as H.
      replace (fr + 2176 + Z.of_nat 36) with (fr + 2176 + 36) in H by lia.
      rewrite (R21S.a_byte1 (nth 36 (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7) (Z_to_bv 8 0)) Ehv) in H. exact H. }
    assert (R0 : ov_read_bytes A.Img0.rsegs m' (MEM.wa (fr + 2176)) 2 =
                 Some (MEM.le2 (Z_to_bv 64 (Prog.RcIdentModel.fw_milli (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7))))).
    { pose proof (R21S.a_rd2 m' (fr + 2176) (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7) 0 IDB7
                    ltac:(rewrite HIDL; lia)) as H.
      replace (fr + 2176 + Z.of_nat 0) with (fr + 2176) in H by lia. exact H. }
    assert (R22 : ov_read_bytes A.Img0.rsegs m' (MEM.wa (fr + 2176 + 22)) 2 =
                  Some (MEM.le2 (Z_to_bv 64 (Prog.RcIdentModel.major (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7))))).
    { pose proof (R21S.a_rd2 m' (fr + 2176) (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7) 22 IDB7
                    ltac:(rewrite HIDL; lia)) as H.
      replace (fr + 2176 + Z.of_nat 22) with (fr + 2176 + 22) in H by lia. exact H. }
    assert (R24 : ov_read_bytes A.Img0.rsegs m' (MEM.wa (fr + 2176 + 24)) 2 =
                  Some (MEM.le2 (Z_to_bv 64 (Prog.RcIdentModel.minor (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7))))).
    { pose proof (R21S.a_rd2 m' (fr + 2176) (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7) 24 IDB7
                    ltac:(rewrite HIDL; lia)) as H.
      replace (fr + 2176 + Z.of_nat 24) with (fr + 2176 + 24) in H by lia. exact H. }
    assert (R26' : ov_read_bytes A.Img0.rsegs m' (MEM.wa (fr + 2176 + 26)) 2 =
                   Some (MEM.le2 (Z_to_bv 64 (Prog.RcIdentModel.patch (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7))))).
    { pose proof (R21S.a_rd2 m' (fr + 2176) (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7) 26 IDB7
                    ltac:(rewrite HIDL; lia)) as H.
      replace (fr + 2176 + Z.of_nat 26) with (fr + 2176 + 26) in H by lia. exact H. }
    assert (M266 : ov_read_bytes A.Img0.rsegs m' (MEM.wa (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 266)) 2 =
                   Some (MEM.le2 (Z_to_bv 64 (Prog.RcIdentModel.fw_milli (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7))))).
    { pose proof (R21S.a_rd2 m' _ _ 266 NROW ltac:(rewrite HROWL; lia)) as H.
      replace (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + Z.of_nat 266)
        with (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 266) in H by lia.
      rewrite Efw. exact H. }
    assert (M268 : ov_read_bytes A.Img0.rsegs m' (MEM.wa (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 268)) 2 =
                   Some (MEM.le2 (Z_to_bv 64 (Prog.RcIdentModel.major (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7))))).
    { pose proof (R21S.a_rd2 m' _ _ 268 NROW ltac:(rewrite HROWL; lia)) as H.
      replace (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + Z.of_nat 268)
        with (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 268) in H by lia.
      rewrite Emaj. exact H. }
    assert (M270 : ov_read_bytes A.Img0.rsegs m' (MEM.wa (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 270)) 2 =
                   Some (MEM.le2 (Z_to_bv 64 (Prog.RcIdentModel.minor (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7))))).
    { pose proof (R21S.a_rd2 m' _ _ 270 NROW ltac:(rewrite HROWL; lia)) as H.
      replace (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + Z.of_nat 270)
        with (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 270) in H by lia.
      rewrite Emin. exact H. }
    assert (M272 : ov_read_bytes A.Img0.rsegs m' (MEM.wa (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 272)) 2 =
                   Some (MEM.le2 (Z_to_bv 64 (Prog.RcIdentModel.patch (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7))))).
    { pose proof (R21S.a_rd2 m' _ _ 272 NROW ltac:(rewrite HROWL; lia)) as H.
      replace (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + Z.of_nat 272)
        with (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 272) in H by lia.
      rewrite Epat. exact H. }
    assert (M56 : ov_read_bytes A.Img0.rsegs m' (MEM.wa (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 56)) 4 =
                  Some (MEM.le4 (Z_to_bv 64 (Prog.RcSynth.rw32 (A.Prog.SlotModel.rowb
                          (A.Prog.SlotModel.istar (ACtlCut.c_in cx))) 56)))).
    { pose proof (R21S.a_rd4 m' _ _ 56 NROW ltac:(rewrite HROWL; lia)) as H.
      replace (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + Z.of_nat 56)
        with (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 56) in H by lia.
      rewrite <- L56. exact H. }
    assert (R144 : ov_read_bytes A.Img0.rsegs m' (MEM.wa (A + 144)) 8 = Some (MEM.le8 (Z_to_bv 64 (fr + 2688)))).
    { apply (R21S.r21_rdn m' _ _ 8%nat); [| apply MEM.length_le8].
      exact (r21g_q64_keeps mem3 m' _ _ _ (r21g_spill_A regs3 mem3 144 (fr + 2688) A R9 ltac:(lia) ltac:(lia)
               ltac:(lia) S144) HK ltac:(intros i Hi; apply HGA; lia)). }
    assert (R112 : ov_read_bytes A.Img0.rsegs m' (MEM.wa (A + 112)) 8 =
                   Some (MEM.le8 (Z_to_bv 64 (A.Prog.SlotModel.mrow (ACtlCut.c_in cx))))).
    { apply (R21S.r21_rdn m' _ _ 8%nat); [| apply MEM.length_le8].
      exact (r21g_q64_keeps mem3 m' _ _ _ (r21g_spill_A regs3 mem3 112 _ A R9 ltac:(lia) ltac:(lia)
               ltac:(lia) S112) HK ltac:(intros i Hi; apply HGA; lia)). }
    (* has_identity_record <> 0: the name record (Seg/R21.v:1690-1711) *)
    assert (HNT : Prog.RcSynth.rw32 (A.Prog.SlotModel.rowb (A.Prog.SlotModel.istar (ACtlCut.c_in cx))) 56 <> 0 ->
       ov_read_bytes A.Img0.rsegs m' (MEM.wa (fr + 2176 + 20)) 1 = Some [Z_to_bv 8 1] /\
       ov_read_bytes A.Img0.rsegs m' (MEM.wa (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 280)) 8 =
         Some (MEM.le8 (Z_to_bv 64 (Prog.RcSynth.rname (A.Prog.SlotModel.rowb (A.Prog.SlotModel.istar (ACtlCut.c_in cx)))))) /\
       0 < Prog.RcSynth.rname (A.Prog.SlotModel.rowb (A.Prog.SlotModel.istar (ACtlCut.c_in cx))) < 2 ^ 64).
    { intros Hh0.
      assert (Hhid0 : Prog.RcEmit.em_hid (A.Prog.SlotModel.rowb (A.Prog.SlotModel.istar (ACtlCut.c_in cx))) <> 0)
        by (intros E; apply Hh0; apply Ehid; exact E).
      destruct (Hnmf Hhid0) as (Hnm0 & Hnm1 & _).
      assert (Hn6 : A.Prog.SlotModel.rt_n (ACtlCut.c_in cx) 6 <> 0) by (apply (proj2 (RTM.a_rtm_hid _)); exact Hhid0).
      destruct (RTM.a_rtm_name (ACtlCut.c_in cx) Hn6) as (Ehn & _).
      split.
      { pose proof (R21S.a_rd1 m' (fr + 2176) (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7) 20 IDB7
                      ltac:(rewrite HIDL; lia)) as H.
        replace (fr + 2176 + Z.of_nat 20) with (fr + 2176 + 20) in H by lia.
        rewrite (R21S.a_byte1 (nth 20 (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7) (Z_to_bv 8 0)) Ehn) in H. exact H. }
      split; [|lia].
      pose proof (R21S.a_rd8 m' _ _ 280 NROW ltac:(rewrite HROWL; lia)) as H.
      replace (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + Z.of_nat 280)
        with (A.Prog.SlotModel.mrow (ACtlCut.c_in cx) + 280) in H by lia.
      rewrite <- L280. exact H. }
    (* G3 again: the walk moved from R to mkR_of R at 0x81990 *)
    apply (lib.Reusable.YA0nR.SRr_xregs_eqv segs W3 (Lib.Regs6ss.mkR_of R) R K11.fp_regs
             (Z_to_bv 64 0x81990) K11.fp_csr None m' (K11.seg_rom segs) md' (POST cx));
      [| exact (Lib.Regs6ss.xregs_eqv_sym _ _ (Lib.Regs6ss.mkR_of_eqv R))].
    set (MR := A.Prog.SlotModel.mrow (ACtlCut.c_in cx)) in *.
    destruct Hmrlo as (Hmrlo1 & Hmrlo2).
    pose proof (r21g_tail_run (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) R m' A (fr + 2176) MR
                  (Prog.RcIdentModel.fw_milli (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7))
                  (Prog.RcIdentModel.major (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7))
                  (Prog.RcIdentModel.minor (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7))
                  (Prog.RcIdentModel.patch (A.Prog.SlotModel.RID (ACtlCut.c_in cx) 7))
                  (Prog.RcSynth.rw32 (A.Prog.SlotModel.rowb (A.Prog.SlotModel.istar (ACtlCut.c_in cx))) 56)
                  (Prog.RcSynth.rname (A.Prog.SlotModel.rowb (A.Prog.SlotModel.istar (ACtlCut.c_in cx))))
                  (fr + 2688)) as HTR.
    specialize (HTR ltac:(rewrite K9; exact R9)).
    specialize (HTR ltac:(rewrite K21; exact R21)).
    specialize (HTR ltac:(rewrite K26; exact R26)).
    specialize (HTR ltac:(lia)). specialize (HTR ltac:(lia)).
    specialize (HTR ltac:(lia)). specialize (HTR ltac:(lia)).
    specialize (HTR ltac:(unfold A.Prog.SlotModel.CAT in Hmrlo1, Hmrlo2; lia)).
    specialize (HTR ltac:(unfold A.Prog.SlotModel.CAT in Hmrlo1, Hmrlo2; lia)).
    specialize (HTR Hh32).
    specialize (HTR R2'). specialize (HTR R144). specialize (HTR R112).
    specialize (HTR (RK (MR + 266) ltac:(lia))). specialize (HTR (RK (MR + 268) ltac:(lia))).
    specialize (HTR (RK (MR + 270) ltac:(lia))). specialize (HTR (RK (MR + 272) ltac:(lia))).
    specialize (HTR (RK (MR + 56) ltac:(lia))). specialize (HTR (RK (MR + 280) ltac:(lia))).
    specialize (HTR R0). specialize (HTR M266). specialize (HTR R36). specialize (HTR R22).
    specialize (HTR M268). specialize (HTR R24). specialize (HTR M270). specialize (HTR R26').
    specialize (HTR M272). specialize (HTR M56). specialize (HTR HNT).
    specialize (HTR (Gfr (fr + 2176 + 2) 1 ltac:(lia) ltac:(lia) ltac:(lia))).
    specialize (HTR (Gst (A + 144) 8 ltac:(lia) ltac:(lia) ltac:(lia))).
    specialize (HTR (Gst (A + 112) 8 ltac:(lia) ltac:(lia) ltac:(lia))).
    specialize (HTR (GK (MR + 266) ltac:(lia))). specialize (HTR (GK (MR + 268) ltac:(lia))).
    specialize (HTR (GK (MR + 270) ltac:(lia))). specialize (HTR (GK (MR + 272) ltac:(lia))).
    specialize (HTR (GK (MR + 56) ltac:(lia))). specialize (HTR (GK (MR + 280) ltac:(lia))).
    specialize (HTR (Gfr (fr + 2176) 2 ltac:(lia) ltac:(lia) ltac:(lia))).
    specialize (HTR (Gcat (MR + 266) 2 ltac:(lia) ltac:(lia) ltac:(lia))).
    specialize (HTR (Gfr (fr + 2176 + 36) 1 ltac:(lia) ltac:(lia) ltac:(lia))).
    specialize (HTR (Gfr (fr + 2176 + 22) 2 ltac:(lia) ltac:(lia) ltac:(lia))).
    specialize (HTR (Gcat (MR + 268) 2 ltac:(lia) ltac:(lia) ltac:(lia))).
    specialize (HTR (Gfr (fr + 2176 + 24) 2 ltac:(lia) ltac:(lia) ltac:(lia))).
    specialize (HTR (Gcat (MR + 270) 2 ltac:(lia) ltac:(lia) ltac:(lia))).
    specialize (HTR (Gfr (fr + 2176 + 26) 2 ltac:(lia) ltac:(lia) ltac:(lia))).
    specialize (HTR (Gcat (MR + 272) 2 ltac:(lia) ltac:(lia) ltac:(lia))).
    specialize (HTR (Gcat (MR + 56) 4 ltac:(lia) ltac:(lia) ltac:(lia))).
    specialize (HTR ltac:(intros _; split; [apply (Gfr (fr + 2176 + 20) 1); lia
                                           | apply (Gcat (MR + 280) 8); lia])).
    pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HTR) as HFS2.
    rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS2.
    apply (lib.Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md'
             (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) _ (POST cx) HFS2).
    { exact (A.ProgBridge.fp_avoids_RNG_W _). }
    intros ms2 md2 HQ2 Hhid2 Hsbm2.
    assert (Hc7 : 0 <= 7 <= ACtlCut.c_n cx) by (destruct HCUR as (HH & _); exact HH).
    assert (Ec0 : A.Prog.SlotModel.c0 (ACtlCut.c_in cx) = 7).
    { unfold A.Prog.SlotModel.c0, A.Prog.SlotModel.nlen. rewrite <- Hlen. lia. }
    destruct HQ2 as [(E0 & R0' & Ems2 & P10 & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P27 & P22 & P25)
                    | (E0 & regsT & Ems2 & T1 & T10 & T11 & T2 & T3 & T4 & T8 & T9 & T19 & T21 & T22 & T25 &
                       T26 & T27)].
    + (* h = 0: no name to compare, straight to the exit cut A81ac8 at the latch's memory *)
      subst ms2. cbn [ms_mem LBMS.MS] in Hhid2.
      assert (HJ2 : lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK
                      (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx)
                      (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 W3 m' md2 k).
      { eapply (lib.Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ => False);
          [exact HJ' | intros x _; reflexivity | intros x Hx; exact Hx | exact Hhid2 | exact Hsbm2 | intros a []]. }
      change (lib.Reusable.YA0n.SRr segs W3
                (lib.Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A81ac8) R0' m' md2) (POST cx)).
      apply (HX8 cx [] fr k ly3 S3 W3 R0' m' md2 HB HJ2 HF HL).
      * cbv beta iota zeta delta [ACtlCut.cut_kmax ACtlCutP.C_A81ac8]. lia.
      * apply (r21g_exit_body cx fr regs3 R0' mem3 m'
                 (fun a => 0 <= a < 2 ^ 64 /\ FRM.outside (r21g_win fr) a)
                 (lib.Reusable.YG0d.ablocks B ly3 S3) A HP HFRAC Hn R9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                 HOUR HCUR HPRO S144 S192 Hid Hjk S280 S240 Hjy Hjk32 S152 Ec0 HK
                 ltac:(intros a Ha; apply HGA; lia) ltac:(intros a Ha; apply HGS; lia)
                 ltac:(intros a Ha; apply HGF; lia)
                 ltac:(intros i Hi; apply (HGFs 2624 6 i); lia)
                 ltac:(intros i Hi; apply HG; [exact (proj1 (HIN i Hi)) | pose proof (HIN i Hi) as HQi; lia])
                 ltac:(intros Hn0 i Hi; apply HGsh;
                       [pose proof (HIN i ltac:(lia)) as HQi; lia
                        | pose proof (HIN i ltac:(lia)) as HQi; lia
                        | pose proof (HIN i ltac:(lia)) as HQi; lia])
                 (HFSH m' MU STk)
                 ltac:(intros i Hi; exact (proj1 (r21g_present_stk (lib.Reusable.YA0n.w_H W3) m' (A + 192 + i)
                                                   (Hpres' (A + 192 + i) ltac:(unfold A.ACfn.LLVMF_STK; lia)))))
                 (eq_trans P2 K2) (eq_trans P3 K3) (eq_trans P4 K4) (eq_trans P8 K8) (eq_trans P9 K9)
                 (eq_trans P19 K19) (eq_trans P22 K22) (eq_trans P25 K25) (eq_trans P26 K26) P10 P27).
      * exact Hrt'.
    + (* h <> 0: the call to __wrap_strcmp at 0x81abc, return 0x81ac0 (a Theorem Labs lane's astrcmp_realizes at 0x42964) *)
      subst ms2. cbn [ms_mem LBMS.MS] in Hhid2.
      assert (HJ2 : lib.Reusable.YCbq.ajournal (SK := A.AE2k.tfib_sink_head) segs B A.ACfn.LLVMF_STK
                      (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx) (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx)
                      (ACtlCut.c_md cx) (ACtlCut.own6 cx) ly3 S3 W3 m' md2 k).
      { eapply (lib.Reusable.YCbq.ajournal_exec segs B LAWS A.ACtlG.Kit.kit_segs_low) with (Wr := fun _ => False);
          [exact HJ' | intros x _; reflexivity | intros x Hx; exact Hx | exact Hhid2 | exact Hsbm2 | intros a []]. }
      pose proof HJ2 as (HAR2 & _).
      destruct (r21g_frame cx fr k ly3 S3 W3 m' md2 HJ2 HF HL)
        as (_ & _ & _ & _ & _ & Hfrpres2 & Hshpres2).
      assert (Hhid0 : Prog.RcEmit.em_hid (A.Prog.SlotModel.rowb (A.Prog.SlotModel.istar (ACtlCut.c_in cx))) <> 0)
        by (intros Eh; apply E0; apply Ehid; exact Eh).
      destruct (Hnmf Hhid0) as (Hnm0 & Hnm1 & _).
      assert (HAD' : ART.addressable m' (fr + 2176) 38)
        by (apply (r21g_addr_keeps mem3 m' _ _ _ HAD HK); intros i Hi; apply (HGFs 2176 38 i); lia).
      destruct (r21g_str_facts ly3 S3 W3 m' md2 (ACtlCut.c_in cx) fr HAR2 Hrt' IDB7 HAD' Hfrpres2 Hshpres2
                  ltac:(lia) ltac:(lia) Hfrlow E0)
        as (SMT & SX & SY & AMX & AMY & RAX & SHX & RAY & SHY & HNMa & HNMb & HKKa & HKKb).
      assert (EspT : lib.Reusable.YG0d.spZ regsT = sp).
      { unfold lib.Reusable.YG0d.spZ. rewrite T2, K2, R2, Z_to_bv_unsigned. unfold bv_wrap.
        change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. unfold ART.APPMEM_END in *. lia. }
      assert (Egp : K11.getr (ACtlCut.c_regs cx) 3 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_gp B)).
      { destruct HB as (HB1 & _). destruct HB1 as (HBa & _). destruct HBa as (_ & _ & _ & Egp0 & _). exact Egp0. }
      (* every byte below the allocator ceiling is outside strcmp's own two-frame stack window *)
      assert (Esep : forall a, 0 <= a -> a < lib.Reusable.YM05.alloc_ceiling ->
                       ~ (sp - 2 * lib.Reusable.YG0d.ESTACK <= a < sp)).
      { intros a Ha0 Ha1 Hc. unfold lib.Reusable.YG0d.ESTACK in Hc. lia. }
      assert (Esep1 : forall a, 0 <= a -> a < lib.Reusable.YM05.alloc_ceiling ->
                        ~ (sp - lib.Reusable.YG0d.ESTACK <= a < sp)).
      { intros a Ha0 Ha1 Hc. unfold lib.Reusable.YG0d.ESTACK in Hc. lia. }
      change (lib.Reusable.YA0n.SRr segs W3 (lib.Reusable.YG0d.cfg_at segs 0x42964 regsT m' md2) (POST cx)).
      eapply lib.Reusable.YA0n.SRr_bind.
      { apply (r21g_aj_strcmp_at W3 regsT m' A.ACfn.LLVMF_STK (ACtlCut.c_sp cx) [] (ACtlCut.c_ly cx)
                 (ACtlCut.c_S cx) (ACtlCut.c_W cx) (ACtlCut.c_mem cx) (ACtlCut.c_md cx) (ACtlCut.own6 cx)
                 ly3 S3 md2 k (fr + 2176 + 3)
                 (Prog.RcSynth.rname (A.Prog.SlotModel.rowb (A.Prog.SlotModel.istar (ACtlCut.c_in cx))))
                 (Z.of_nat (length (removelast (A.Prog.SlotModel.rt_nb (ACtlCut.c_in cx))))) 0 0
                 (sp - ACtlCut.c_sp cx) (Z_to_bv 64 0x81ac0) HJ2 T10 T11 ltac:(lia) HNMa ltac:(lia) ltac:(lia)
                 ltac:(lia) ltac:(rewrite EspT; lia)
                 ltac:(rewrite Zminus_mod, Hsp16, Hal16; reflexivity) ltac:(lia)
                 ltac:(unfold lib.Reusable.YG0d.ESTACK, A.ACfn.LLVMF_STK; lia)
                 ltac:(rewrite T3, K3, R3; exact Egp) ltac:(rewrite T4, K4; exact R4) T1
                 ltac:(unfold lib.Reusable.YK0s.ret_ok; vm_compute; reflexivity) SMT); clear HTR.
        - intros a Ha. split; [exact (SX a Ha) | rewrite EspT; apply Esep1; lia].
        - intros a Ha. split; [exact (SY a Ha) | rewrite EspT; apply Esep1; lia].
        - intros a Ha. replace (ACtlCut.c_sp cx + (sp - ACtlCut.c_sp cx)) with sp by lia. apply Esep; lia.
        - intros a Ha. replace (ACtlCut.c_sp cx + (sp - ACtlCut.c_sp cx)) with sp by lia. apply Esep; lia.
        - exact AMX.
        - exact AMY.
        - exact RAX.
        - exact SHX.
        - exact RAY.
        - exact SHY. }
      intros W2 cc Hwle HR.
      destruct HR as (EW & regs2 & mem2 & md3' & Ecc & HJ3 & HAR3 & Hregs & Ha0 & Hview & Hpres2).
      subst W2 cc.
      assert (Hview' : forall a, 0 <= a < 2 ^ 64 ->
                 ~ (sp - 2 * lib.Reusable.YG0d.ESTACK <= a < sp) ->
                 lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W3) mem2 a =
                 lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W3) m' a)
        by (intros a Ha Hn2; apply Hview; [exact Ha | lia]).
      assert (KR : forall r : Z, lib.Reusable.YG0d.acallee_saved r ->
                     K11.getr regs2 (Z_to_bv 5 r) = K11.getr regsT (Z_to_bv 5 r)) by exact Hregs.
      assert (U2 : K11.getr regs2 2 = K11.getr regs3 2)
        by (rewrite <- K2, <- T2; exact (KR 2 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
      assert (U3 : K11.getr regs2 3 = K11.getr regs3 3)
        by (rewrite <- K3, <- T3; exact (KR 3 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
      assert (U4 : K11.getr regs2 4 = K11.getr regs3 4)
        by (rewrite <- K4, <- T4; exact (KR 4 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
      assert (U8 : K11.getr regs2 8 = K11.getr regs3 8)
        by (rewrite <- K8, <- T8; exact (KR 8 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
      assert (U9 : K11.getr regs2 9 = K11.getr regs3 9)
        by (rewrite <- K9, <- T9; exact (KR 9 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
      assert (U19 : K11.getr regs2 19 = K11.getr regs3 19)
        by (rewrite <- K19, <- T19; exact (KR 19 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
      assert (U22 : K11.getr regs2 22 = K11.getr regs3 22)
        by (rewrite <- K22, <- T22; exact (KR 22 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
      assert (U25 : K11.getr regs2 25 = K11.getr regs3 25)
        by (rewrite <- K25, <- T25; exact (KR 25 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
      assert (U26 : K11.getr regs2 26 = K11.getr regs3 26)
        by (rewrite <- K26, <- T26; exact (KR 26 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
      assert (U27 : K11.getr regs2 27 = Z_to_bv 64 (fr + 2688))
        by (rewrite <- T27; exact (KR 27 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))).
      assert (U10 : K11.getr regs2 10 = Z_to_bv 64 0)
        by (rewrite Ha0; unfold lib.Reusable.YG0d.w64, r21g_strcmp_res; reflexivity).
      change (lib.Reusable.YA0n.SRr segs W3
                (lib.Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc C_A81ac0) regs2 mem2 md3') (POST cx)).
      apply (HX0 cx [] fr k ly3 S3 W3 regs2 mem2 md3' HB HJ3 HF HL).
      * cbv beta iota zeta delta [ACtlCut.cut_kmax ACtlCutP.C_A81ac0]. lia.
      * apply (r21g_exit_body cx fr regs3 regs2 mem3 mem2
                 (fun a => (0 <= a < 2 ^ 64 /\ FRM.outside (r21g_win fr) a) /\
                           (0 <= a < 2 ^ 64 /\ lib.Reusable.YA0n.w_H W3 (Z_to_bv 64 a) = false /\
                            ~ (sp - 2 * lib.Reusable.YG0d.ESTACK <= a < sp)))
                 (lib.Reusable.YG0d.ablocks B ly3 S3) A HP HFRAC Hn R9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                 HOUR HCUR HPRO S144 S192 Hid Hjk S280 S240 Hjy Hjk32 S152 Ec0
                 (r21g_keeps_trans mem3 m' mem2 _ _ HK (r21g_keeps_view W3 m' mem2 _ _ Hview' Hpres2))).
        -- intros a Ha. split; [apply HGA; lia|].
          split; [lia|]. split; [exact (proj1 (Hpres' a ltac:(unfold A.ACfn.LLVMF_STK; lia))) | lia].
        -- intros a Ha. split; [apply HGS; lia|].
          split; [lia|]. split; [exact (proj1 (Hpres' a ltac:(unfold A.ACfn.LLVMF_STK; lia))) | lia].
        -- intros a Ha. split; [apply HGF; lia|].
          split; [lia|]. split; [exact (proj1 (Hfrpres a ltac:(lia))) | apply Esep; lia].
        -- intros i Hi. split; [apply (HGFs 2624 6 i); lia|].
          pose proof (HshFr (2624 + i) ltac:(lia)) as HS6.
          replace (fr + 2624 + i) with (fr + (2624 + i)) by lia.
          split; [lia|]. split; [exact (proj1 HS6) | apply Esep; lia].
        -- intros i Hi. pose proof (HIN i Hi) as HQi.
          split; [apply HG; [exact (proj1 HQi) | lia]|].
          split; [lia|]. split; [exact (proj1 (proj1 (proj2 (proj2 (proj2 HQi))))) | apply Esep; lia].
        -- intros Hn0 i Hi. pose proof (HshIn Hn0 i Hi) as HSi.
          split; [apply HGsh; [pose proof (HIN i ltac:(lia)) as HQi; lia
                               | pose proof (HIN i ltac:(lia)) as HQi; lia
                               | pose proof (HIN i ltac:(lia)) as HQi; lia]|].
          split; [lia|]. split; [exact (proj1 HSi) | apply Esep; lia].
        -- intros i Hi.
           assert (Hp2 : lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W3) mem2 (ACtlCutP.Sfr fr + i)).
           { apply Hpres2. unfold ACtlCutP.Sfr. rewrite <- ESH. exact (Hshpres2 i ltac:(lia)). }
           exact (proj2 (r21g_present_stk (lib.Reusable.YA0n.w_H W3) mem2 (ACtlCutP.Sfr fr + i) Hp2)).
        -- intros i Hi.
          exact (proj1 (r21g_present_stk (lib.Reusable.YA0n.w_H W3) mem2 (A + 192 + i)
                          (Hpres2 _ (Hpres' (A + 192 + i) ltac:(unfold A.ACfn.LLVMF_STK; lia))))).
        -- exact U2.
        -- exact U3.
        -- exact U4.
        -- exact U8.
        -- exact U9.
        -- exact U19.
        -- exact U22.
        -- exact U25.
        -- exact U26.
        -- exact U10.
        -- exact U27.
      * apply (r21g_ctlrt_view ly3 S3 W3 m' mem2 md3'
                 (sp - 2 * lib.Reusable.YG0d.ESTACK) sp Hrt' HAR3 Hview' Hpres2).
        unfold ART.HIGHMEM_BEG, lib.Reusable.YG0d.ESTACK. lia.
  - (* b <= 5: the latch is taken, back to the round-trip head at turn S b *)
    assert (Hb5 : (b <= 5)%nat) by lia.
    pose proof (r21g_latch_next_run (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) regs3 mem3 (ART.shadow_addr fr)
                  A (Z.of_nat b) (fr + 544) R19 R9 R23 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HSTK HQ128
                  GSH G128) as HRUN.
    pose proof (A.ProgBridge.fevt_of_evtF _ _ _ HRUN) as HFS.
    rewrite <- A.ProgBridge.tfibsegs_rsegs in HFS.
    apply (lib.Reusable.YA0nR.SRr_fevt_hid segs A.ACtlG.Kit.kit_wx W3 _ md3
             (A.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W3)) _ (POST cx) HFS).
    { exact (A.ProgBridge.fp_avoids_RNG_W _). }
    intros ms' md' HQ0 Hhid Hsbm.
    destruct HQ0 as (R & m' & Ems & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K25 & K26 & K10 & K24 &
      MU & WM & STk).
    subst ms'. cbn [ms_mem LBMS.MS] in Hhid.
    change (lib.Reusable.YA0n.SRr segs W3
              (lib.Reusable.YG0d.cfg_at segs (ACtlCut.cut_pc (ix_cut C_A815cc_at [Z.of_nat (S b)])) R m' md')
              (POST cx)).
    pose proof (r21g_keeps_munch _ mem3 m' MU) as HK.
    apply (HX5 cx [Z.of_nat (S b)] fr k ly3 S3 W3 R m' md' HB).
    + exact (r21g_latch_journal cx fr k ly3 S3 W3 mem3 md3 m' md' HJ Efr ltac:(lia) MU STk Hhid Hsbm).
    + exact HF.
    + exact HL.
    + cbv beta iota zeta delta [ACtlCut.cut_kmax ACtlCut.ix_cut ACtlCutP.C_A815cc_at ACtlCutP.ixn nth].
      rewrite Nat2Z.id. lia.
    + (* the exit body, C_A815cc_at at turn S b (ACtlCutP.v:1274-1294) *)
      cbv beta iota zeta delta [ACtlCut.cut_body ACtlCut.ix_cut ACtlCutP.C_A815cc_at ACtlCutP.ixn ACtlCutP.ixz nth].
      split; [reflexivity|]. rewrite Nat2Z.id.
      assert (KS : forall off v, 0 <= off <= 304 -> ACtlCutP.spill regs3 mem3 off v -> ACtlCutP.spill R m' off v).
      { intros off v Ho Hs. apply (r21g_spill_keeps mem3 m' _ regs3 R off v A R9 ltac:(lia) ltac:(lia) ltac:(lia)
                                     K9 HK); [|exact Hs].
        intros i Hi. apply HGA. lia. }
      split; [exact HP|].
      split.
      { apply (r21g_FRAC_keeps mem3 m' _ cx fr fr regs3 R A HFRAC R9 ltac:(lia) ltac:(lia) ltac:(lia) HK
                 ltac:(intros a Ha; apply HGA; lia) ltac:(intros a Ha; apply HGS; lia)
                 ltac:(intros a Ha; apply HGF; lia) (HFSH m' MU STk));
          [exact K2 | exact K3 | exact K4 | exact K8 | exact K9 | exact K19 | exact K26]. }
      split; [exact Hn|].
      split.
      { (* RS at S b *)
        unfold ACtlCutP.RS, ACtlCutP.RB.
        split; [lia|].
        split.
        { destruct HCUR as (Hc0 & Hc22 & Hc25). unfold ACtlCutP.CUR, ACtlCut.rgv in *.
          split; [exact Hc0|]. split; [rewrite K22; exact Hc22 | rewrite K25; exact Hc25]. }
        split.
        { unfold ACtlCutP.OURb in *. apply (r21g_bytes_keeps mem3 m' _ _ _ HOUR HK).
          rewrite SM.OUR_length. intros i Hi. apply HGF. lia. }
        split; [unfold ACtlCut.rgv; rewrite K23; f_equal; lia|].
        split.
        { unfold ACtlCutP.IDBr in *. apply (r21g_bytes_keeps mem3 m' _ _ _ HIDB HK).
          rewrite R21S.a_RID_len. intros i Hi. apply HGF. lia. }
        { unfold ACtlCutP.FGBr in *. apply (r21g_bytes_keeps mem3 m' _ _ _ HFGB HK).
          rewrite (R21S.a_RFG_len _ (S b) ltac:(lia)). intros i Hi. apply HGF. lia. } }
      split.
      { unfold ACtlCutP.OUTA in *. apply (r21g_addr_keeps mem3 m' _ _ _ HOUTA HK). intros i Hi.
        apply (HGFs 544 1492 i); lia. }
      split; [exact (KS 128 _ ltac:(lia) S128)|].
      split.
      { apply (r21g_PRO_keeps mem3 m' _ cx fr regs3 R A HPRO R9 ltac:(lia) ltac:(lia) K9 HK HGA).
        - intros i Hi. apply (HGFs 2624 6 i); lia.
        - intros i Hi. destruct (HIN i Hi) as (H1 & H2 & _). apply HG; [exact H1 | lia].
        - intros Hn0 i Hi. destruct (HIN i ltac:(lia)) as (_ & H2 & H3). apply HGsh; lia. }
      split; [exact (KS 104 _ ltac:(lia) S104)|].
      split; [exact (KS 96 _ ltac:(lia) S96)|].
      split; [unfold ACtlCut.a0v, ACtlCut.rgv; exact K10|].
      split; [unfold ACtlCut.rgv; exact K24|].
      split; [exact (KS 64 _ ltac:(lia) S64)|].
      split; [exact (KS 112 _ ltac:(lia) S112)|].
      split; [unfold ACtlCut.rgv in *; rewrite K21; exact R21|].
      split; [exact (KS 152 _ ltac:(lia) S152)|].
      split; [exact (KS 144 _ ltac:(lia) S144)|].
      split; [apply (r21g_addr_keeps mem3 m' _ _ _ HAD HK); intros i Hi; apply (HGFs 2176 38 i); lia|].
      split; [exact (KS 192 _ ltac:(lia) S192)|].
      split; [destruct Hid as (idb & Hidb); exists idb; apply (r21g_rwcb_keeps mem3 m' _ _ _ _ Hidb HK);
              intros i Hi; apply HGF; cbn in Hi; lia|].
      split; [destruct Hjk as (jk & Hjkb); exists jk; apply (r21g_rwcb_keeps mem3 m' _ _ _ _ Hjkb HK);
              intros i Hi; apply HGF; cbn in Hi; lia|].
      split; [exact (KS 280 _ ltac:(lia) S280)|].
      split; [exact (KS 240 _ ltac:(lia) S240)|].
      split; [destruct Hjy as (jy & Hjyb); exists jy; apply (r21g_rwcb_keeps mem3 m' _ _ _ _ Hjyb HK);
              intros i Hi; apply HGF; cbn in Hi; lia|].
      split; [destruct Hjk32 as (jk & Hjkb); exists jk; apply (r21g_rwcb_keeps mem3 m' _ _ _ _ Hjkb HK);
              intros i Hi; apply HGF; cbn in Hi; lia|].
      apply (r21g_RXS_keeps mem3 m' _ cx fr regs3 R A HRXS R9 ltac:(lia) ltac:(lia) K9 HK HGA).
      intros i Hi. apply (HGFs 2256 72 i); lia.
    + exact (r21g_ctlrt_munch _ _ _ _ _ mem3 m' Hrt MU STk ltac:(unfold ART.shadow_addr, ART.ASAN_K;
               pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)); lia)).
Qed.

End GlueR21.
