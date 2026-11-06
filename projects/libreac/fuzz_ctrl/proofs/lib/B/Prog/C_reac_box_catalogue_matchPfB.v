(* lib/B/Prog/C_reac_box_catalogue_matchPfB.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): THE MIDDLE PIECE (H2)
   of pb_reac_box_catalogue_match, the cgif-form world walk of reac_box_catalogue_match (0x84e40) that proves
   C_reac_box_catalogue_match.treac_box_catalogue_match_spec B.  Brief:
   PB-H2-BRIEF.md (a working note, not in this delivery).  rule 24: no function proved; this file composes
   this lane's own Qed stretches (C_reac_box_catalogue_matchLibW.v, pinned at a working branch
   69fe060f529), the two walked callees' specs by name (TPARSE, TMB) and shared Qed lemmas (core YCbq / YCbqMalloc,
   image-B ProgWorld, ProgBridge, H1's Pf.v, H3's PfV.v).

   cmPfB_mid: from H1's interface C_reac_box_catalogue_matchPf.cmPf_sm2_ret (the class-2 return, pc 0x84eb4) to H3's
   interface C_reac_box_catalogue_matchPfI.cmPf_exit_at (the exit, pc 0x850fc), every path:
     S-B   cmPfB_SB    LibW.cmRBw_post_sm2_side at base m2 (call memory m1, frame j := pos), lifted
                       (cmPfB_jr_lift), journal J3 (cmPfB_jr_journal_pin: window + class-2 frame + its shadow);
                       its inputs at m2 from cmPf_sm2_ret by cmPfB_sb_in (B.ProgWorldAstack.ctl_fs_of_astack 2 with
                       block (e); the window kept from m1 by acall_kept's high-memory clause, YM05's ceiling);
     E2    cmPfB_PC    TPARSE at the parse call (cmPfB_pa_call), its post (cmPfB_pa_ret);
     S-C   cmPfB_PC    LibW.cmRBw_post_parse at base the parse return memory, lifted, journal;
     rows  cmPfB_rows  for row i: TMB at the call (cmPfB_mb_call), its post (cmPfB_mb_ret), LibW.cmRBw_post_mb at
                       base the row's return memory, lifted, journal; induction on k = 11 - i;
     exit  cmPfB_me_exit  each stretch's exit arm into cmPf_exit_at.
   The stretches' footprint premises under RNG := RNG_W (w_H W) are visibility facts (cmPfB_jr_rng*: win_vis,
   win_sh_vis, heap_vis, heap_sh_vis, PfV.cmPf_fs_vis, img_vis_W, rng_bytes_RNG_W, all Qed).
   No ctl_post_* statement is used: the TPARSE / TMB posts are consumed directly (their acall_kept / tcj_kept
   clauses with the journal's AR, aview to raw bytes at present, visible, off-image addresses).

   SECTION HYPOTHESES (core / callee specs only, decisions.md item 15 (a working note, not in this delivery)): LAWS, segs_low, errno_low, ML (as in
   C_reac_box_catalogue_matchPf.v's header); TPARSE (a Theorem Labs lane ea59dbb03aa, lib/B/Prog/C_reac_ctrl_parse.v) and TMB
   (a Theorem Labs lane 5487787da37 / 572f4b58796, lib/B/Prog/C_reac_box_model_block.v blob b8cb937a37f), by name;
   ABCMP = bcmp_wrap_c_on.bcmp_wrap_contract_F_on (inside stretch 4; route (C)).
   FRAME-ROUTE PREMISES (of cmPfB_mid, each named at its premise): HBASE (cmPfB_base_all: cmBase at every journal
   state from the entry with own = [(2, pos)], Lib's CLAUSE MAP; H3's shared cmPf_base_of_AR discharges it), HG17
   (BOX_CATALOGUE's data range in GLOBS), HTRO (pa_relro covers the table); plus the spec file's RELRO_IMG. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require bcmp_wrap_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import C_reac_box_catalogue_matchLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require C_reac_box_catalogue_matchLibW.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds CtrlRo CtrlCallerJ.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YI16 YK04 YK04R YK0s YA0n YA0nR YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0f YG0n YG0v YG0d YCbq YCbqMalloc YE01.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require APostBase YB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgBridge ProgBridgeData.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld B.ProgWorld_Fs B.ProgWorldAstack.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorldVisWin B.ProgWorldVisHeap B.ProgWorldVisFrame.
(* a Theorem Labs lane's shared lift / journal tools (rrB_seg_rom_above), moved from C_reac_ctrl_identity_replyPf.v to GlueLift.v. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require GlueLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require C_reac_box_catalogue_match C_reac_box_catalogue_matchPf
  C_reac_box_catalogue_matchPfI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require C_reac_ctrl_parse C_reac_box_model_block.
(* H3's side-stack visibility (cmPf_fs_vis, 88d3b215222). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require C_reac_box_catalogue_matchPfV.
Import ListNotations.
Open Scope Z_scope.

Section Mid.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
(* The read-only span of arodata_okS (C_reac_box_catalogue_match.v:44-45) and the registered globals (TMB). *)
Variables RLO RHI : Z.
Variable GLOBS : list (Z * Z).
(* Core (as in C_reac_box_catalogue_matchPf.v's header). *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
Hypothesis segs_low : forall a, lib.Reusable.YG0d.in_img rsegs a -> 0 <= a < lib.Reusable.YG0f.kLowMemEnd.
Hypothesis errno_low : lib.Reusable.YCbq.api_env rsegs B.
Hypothesis ML : lib.Reusable.YG0d.model_laws (lib.Reusable.YG0f.as_universe B).
(* The two walked callees, by name (a Theorem Labs lane ea59dbb03aa; a Theorem Labs lane 5487787da37 / 572f4b58796). *)
Hypothesis TPARSE : C_reac_ctrl_parse.treac_ctrl_parse_spec (SK := SK) rsegs B RLO RHI.
Hypothesis TMB : C_reac_box_model_block.treac_box_model_block_spec RLO RHI B GLOBS.
(* The bcmp wrapper inside stretch 4, route (C) (lib/B/Prog/bcmp_wrap_c_on.v). *)
Hypothesis ABCMP : bcmp_wrap_c_on.bcmp_wrap_contract_F_on.

(* FRAME-ROUTE (shared shape of the cmBase premise): cmBase at every state the walk reaches from the entry with
   own = [(2, pos)] (the class-2 return, the parse return, each row's model_block return, the exit), clause by clause
   as at C_reac_box_catalogue_matchPf.cmPf_SA (Lib's CLAUSE MAP; owner of every B twin a Theorem Labs lane, lib/B/ProgWorld.v). *)
Definition cmPfB_base_all (ly : lib.Reusable.YG0f.alayout) (S : lib.Reusable.YG00.astate)
    (W : lib.Reusable.YA0n.world rsegs) (regs : bvmap 5 word) (memc : word -> option byte) (md : Model)
    (f len : Z) (fb : list byte) (pos : Z) : Prop :=
  forall (lyc : lib.Reusable.YG0f.alayout) (Sc : lib.Reusable.YG00.astate) (Wc : lib.Reusable.YA0n.world rsegs)
         (m : word -> option byte) (mdc : Model) (k : Z),
    lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK (lib.Reusable.YG0d.spZ regs) []
      ly S W memc md [(2, pos)] lyc Sc Wc m mdc k ->
    cmBase m (lib.Reusable.YK11.getr regs 4) f len (lib.Reusable.YG0d.spZ regs) (lib.Reusable.YG0f.ly_F ly) fb.


(* ==== sb: the raw-byte bridge and the facts at the class-2 return (cmPf_sm2_ret) ==== *)

(* A visible byte above the image hull whose core view is unchanged and which the old memory holds is kept byte for
   byte (no rom fallback above IMG_HI: GlueLift.rrB_seg_rom_above).  The address side condition
   is IMG_HI <= a (B.Prog.ImgBounds.IMG_HI = 0x5fe000), not ~ in_img. *)
Lemma cmPfB_sb_raw_of_view : forall (W : lib.Reusable.YA0n.world rsegs) (m m' : word -> option byte) (a : Z),
  0 <= a < 2 ^ 64 -> B.Prog.ImgBounds.IMG_HI <= a ->
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  m (Z_to_bv 64 a) <> None ->
  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m' a =
    lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros W m m' a Ra Hhi Hh Hm Hv.
  assert (ROM : lib.Reusable.YK11.seg_rom rsegs (Z_to_bv 64 a) = None)
    by exact (GlueLift.rrB_seg_rom_above a ltac:(lia)).
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in Hv.
  cbv beta in Hv. rewrite Hh in Hv. cbv iota in Hv.
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [|exfalso; exact (Hm eq_refl)].
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E'.
  - cbn [option_map] in Hv. injection Hv as Hb. f_equal. apply bv_eq. exact Hb.
  - rewrite ROM in Hv. cbn [option_map] in Hv. discriminate Hv.
Qed.

(* The same, spelled with lib.Lib.Mem.wa (the form of cmRB_win_kept / cmRB_kept). *)
Lemma cmPfB_sb_raw_of_view_wa : forall (W : lib.Reusable.YA0n.world rsegs) (m m' : word -> option byte) (a : Z),
  0 <= a < 2 ^ 64 -> B.Prog.ImgBounds.IMG_HI <= a ->
  lib.Reusable.YA0n.w_H W (lib.Lib.Mem.wa a) = false ->
  m (lib.Lib.Mem.wa a) <> None ->
  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m' a =
    lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m a ->
  m' (lib.Lib.Mem.wa a) = m (lib.Lib.Mem.wa a).
Proof. intros W m m' a Ra Hhi Hh Hm Hv. exact (cmPfB_sb_raw_of_view W m m' a Ra Hhi Hh Hm Hv). Qed.

(* ... and with the visibility and presence at the old memory given as one apresent. *)
Lemma cmPfB_sb_raw_of_view_pres : forall (W : lib.Reusable.YA0n.world rsegs) (m m' : word -> option byte) (a : Z),
  0 <= a < 2 ^ 64 -> B.Prog.ImgBounds.IMG_HI <= a ->
  lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m a ->
  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m' a =
    lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m a ->
  m' (lib.Lib.Mem.wa a) = m (lib.Lib.Mem.wa a).
Proof.
  intros W m m' a Ra Hhi (Hh & b & Hb) Hv.
  apply (cmPfB_sb_raw_of_view W m m' a Ra Hhi Hh); [rewrite Hb; discriminate | exact Hv].
Qed.

(* The facts H2 takes at the class-2 return state, all from cmPf_sm2_ret: the frame (2, pos) through the PROVED
   B.ProgWorldAstack.ctl_fs_of_astack 2 (premises from blocks (b)-(e)), the window's stk from J2's presence clause and
   (e)'s presence at m1, the window [CA Sp, Sp) kept from m1 to m2 from (c)'s acall_kept high-memory clause (its
   alloc_ceiling and astk_ok's are both lib.Reusable.YM05.alloc_ceiling), and the stack arithmetic from J2's
   astk_ok.  No frame-route premise. *)
Lemma cmPfB_sb_in : forall (W : lib.Reusable.YA0n.world rsegs) (ly : lib.Reusable.YG0f.alayout)
    (S : lib.Reusable.YG00.astate) (regs : bvmap 5 word) (memc : word -> option byte) (md : Model) (f len : Z)
    (m1 : word -> option byte) (md1 : Model) (regsT : bvmap 5 word) (S2 : lib.Reusable.YG00.astate)
    (regs2 : bvmap 5 word) (m2 : word -> option byte) (md2 : Model) (pos : Z),
  C_reac_box_catalogue_matchPf.cmPf_sm2_ret B W ly S regs memc md f len m1 md1 regsT S2 regs2 m2 md2 pos ->
  0 <= pos < fs_M 2 /\
  lib.Reusable.YG0f.frame_addr ly 2 pos = fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos /\
  lib.Reusable.YG0f.flag_addr ly 2 pos = fs_flag (lib.Reusable.YG0f.ly_F ly) 2 pos /\
  lib.Reusable.YK11.getr regs2 10 = Z_to_bv 64 (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos) /\
  cmRB_Fs2 m2 (lib.Reusable.YG0f.ly_F ly) pos /\
  lib.Lib.Frame.stk rsegs m2 (lib.Reusable.YG0d.spZ regs - 9136) (CA (lib.Reusable.YG0d.spZ regs)) /\
  lib.Lib.Frame.stk rsegs m2 (lib.Reusable.YG0d.spZ regs - 9136) (lib.Reusable.YG0d.spZ regs) /\
  lib.Lib.Frame.stk rsegs m1 (CA (lib.Reusable.YG0d.spZ regs)) (lib.Reusable.YG0d.spZ regs) /\
  cmRB_win_kept m1 m2 (lib.Reusable.YG0d.spZ regs) /\
  lib.Reusable.YG0d.spZ regs mod 16 = 0 /\ 9136 <= lib.Reusable.YG0d.spZ regs /\
  lib.Reusable.YG0d.spZ regs < 2 ^ 64 /\ HIGHMEM_BEG <= lib.Reusable.YG0d.spZ regs - 9136 /\
  lib.Reusable.YG0d.spZ regs <= APPMEM_END.
Proof.
  intros W ly S regs memc md f len m1 md1 regsT S2 regs2 m2 md2 pos H.
  unfold C_reac_box_catalogue_matchPf.cmPf_sm2_ret in H.
  destruct H as (ST1 & SV1 & RO1 & MU1 & WM1 & HJ2 & Hfr & Hnin & Hab & Hnev & Hbb & Hz & Hfl & Hkept & R10
    & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HT & HPRE & PRES1 & Hfpres & Hfc & Hwpres).
  pose proof HJ2 as HJ2'. unfold lib.Reusable.YCbq.ajournal in HJ2'.
  destruct HJ2' as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PRES2 & Hstk & _).
  pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs 2)) as RSp.
  unfold bv_modulus in RSp. cbn [Z.of_N] in RSp.
  change (bv_unsigned (lib.Reusable.YK11.getr regs 2)) with (lib.Reusable.YG0d.spZ regs) in RSp.
  set (Sp := lib.Reusable.YG0d.spZ regs) in *.
  unfold lib.Reusable.YCbq.astk_ok in Hstk.
  destruct Hstk as (S16 & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof lib.Reusable.YCbq.asan_consts as (C1 & _).
  unfold C_reac_box_catalogue_match.CM_STK in Hslo, PRES1, PRES2.
  assert (HK : 9136 <= Sp) by lia.
  assert (HHM : HIGHMEM_BEG <= Sp - 9136) by (unfold HIGHMEM_BEG; lia).
  assert (HAE : Sp <= APPMEM_END) by (unfold APPMEM_END; lia).
  destruct (C_reac_box_catalogue_matchPf.cmPf_CA Sp S16) as (CAb & _).
  assert (FB : lib.Reusable.YG00.fs_frame_bytes 2 = 256) by (vm_compute; reflexivity).
  (* the frame (2, pos): B.ProgWorldAstack.ctl_fs_of_astack 2, lo := Sp - 9136, L := 192 *)
  pose proof (B.ProgWorldAstack.ctl_fs_of_astack B 2 B.ProgWorld.ctl_fs_geom LAWS ltac:(lia)
                ly S S2 W regsT regs2 m1 m2 md1 md2 pos (Sp - 9136) 192
                HPRE ltac:(lia) ltac:(rewrite HT; unfold lib.Reusable.YG0d.ESTACK; lia)
                ltac:(intros a Ha; rewrite HT in Ha; unfold lib.Reusable.YG0d.ESTACK in Ha; apply PRES1; lia)
                Hfr Hnin HAR2 R10 Hz Hfl Hwpres Hfc ltac:(rewrite FB; lia)) as FSA.
  cbv zeta in FSA. change (Z.to_nat 2) with 2%nat in FSA.
  destruct FSA as (R0 & R10' & FLAG & WORD & SH & _ & _ & _ & M64 & _ & _ & _ & _).
  assert (EB : fs_B 2 = 256) by reflexivity.
  rewrite EB in WORD, SH.
  destruct (B.ProgWorld.ctl_fs_geom (lib.Reusable.YG0f.ly_F ly) 2 pos ltac:(lia)) as (_ & _ & GF & GL & _).
  change (Z.to_nat 2) with 2%nat in GF, GL.
  (* the window's presence at m2 (J2) and at m1 (e) *)
  assert (P2 : forall a, Sp - 9136 <= a < Sp -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m2 a)
    by exact PRES2.
  assert (P1 : forall a, Sp - 9136 <= a < Sp -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m1 a)
    by exact PRES1.
  split; [exact R0|].
  split; [unfold lib.Reusable.YG0f.frame_addr; symmetry; exact GF|].
  split; [unfold lib.Reusable.YG0f.flag_addr; symmetry; exact GL|].
  split; [exact R10'|].
  split.
  { split; [exact R0|]. split; [exact M64|]. split; [exact FLAG|]. split; [exact WORD|]. exact SH. }
  split; [exact (C_reac_box_catalogue_matchPf.cmPf_stk_of_apresent (lib.Reusable.YA0n.w_H W) m2 (Sp - 9136) (CA Sp)
                   ltac:(lia) ltac:(lia) (fun a Ha => P2 a ltac:(lia)))|].
  split; [exact (C_reac_box_catalogue_matchPf.cmPf_stk_of_apresent (lib.Reusable.YA0n.w_H W) m2 (Sp - 9136) Sp
                   ltac:(lia) ltac:(lia) P2)|].
  split; [exact (C_reac_box_catalogue_matchPf.cmPf_stk_of_apresent (lib.Reusable.YA0n.w_H W) m1 (CA Sp) Sp
                   ltac:(lia) ltac:(lia) (fun a Ha => P1 a ltac:(lia)))|].
  split.
  { intros a Ha.
    apply (cmPfB_sb_raw_of_view_pres W m1 m2 a ltac:(lia)
             ltac:(unfold B.Prog.ImgBounds.IMG_HI; unfold HIGHMEM_BEG in HHM; lia) (P1 a ltac:(lia))).
    apply (proj1 Hkept a); lia. }
  repeat split; lia.
Qed.



(* Item 1: the lift of a footprint run on the real memory.  B.ProgBridge.fevt_of_evtF turns the evtF run into an
   fsteps run; B.ProgWorld.pws_fsteps_mem gives mem_grows and the hidden bytes; YA0nR.SRr_fsteps lifts it
   (wx_segs_nowrap: B.ProgBridgeData.rsegs_wx_nowrap; fp_avoids: B.ProgBridge.fp_avoids_RNG_W). *)
Lemma cmPfB_jr_lift : forall (W : lib.Reusable.YA0n.world rsegs) (ms : machine_state) (md : Model)
    (P : machine_state -> Prop) (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
  ExecF.evtF rsegs (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) P ms ->
  (forall ms' md', P ms' ->
     lib.Reusable.YK1b.mem_grows (ms_mem ms) (ms_mem ms') ->
     (forall x, lib.Reusable.YA0n.w_H W x = true -> ms_mem ms' x = ms_mem ms x) ->
     lib.Reusable.YK04.same_but_materialized md md' ->
     lib.Reusable.YA0n.SRr rsegs W (mkCfg ms' md') Q) ->
  lib.Reusable.YA0n.SRr rsegs W (mkCfg ms md) Q.
Proof.
  intros W ms md P Q Hev Hk.
  destruct (B.ProgBridge.fevt_of_evtF _ P ms Hev) as (ms' & Hrun & HP).
  pose proof (B.ProgBridge.fp_avoids_RNG_W (lib.Reusable.YA0n.w_H W)) as Hfp.
  destruct (B.ProgWorld.pws_fsteps_mem rsegs (lib.Reusable.YA0n.w_H W) _ ms ms' Hrun Hfp) as [Hgr Hhid].
  exact (lib.Reusable.YA0nR.SRr_fsteps rsegs B.ProgBridgeData.rsegs_wx_nowrap W ms ms' md _ Q Hrun Hfp
    (fun md' Hs => Hk ms' md' HP Hgr Hhid Hs)).
Qed.

(* Item 2: the journal across one re-based stretch whose writes are cmWst Sp fr (C_reac_box_catalogue_matchLibW.v:243):
   the window [Sp - 9136, Sp) (awr_byte's window arm, CM_STK = 9136), the class-2 frame [fr, fr + 256) and its shadow
   [shadow_addr fr, shadow_addr fr + 32) (awr_byte's in_frames arm for (2, pos) in own; fs_frame_bytes 2 = 256 and
   B.AsanRT.shadow_addr = YG0f.shadow_addr by unfolding).  YCbq.ajournal_exec with Wr := the bytes inside cmWst, on
   the real memory: off cmWst the run's munch keeps the byte; mem_grows through B.ProgWorld.pws_grows_mrestrict. *)
Lemma cmPfB_jr_journal : forall (Sp : Z) ly0 S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
    (Wc : lib.Reusable.YA0n.world rsegs) (mb : word -> option byte) mdc k (mc : word -> option byte) mdc' (pos fr : Z),
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k ->
  In (2, pos) own ->
  lib.Reusable.YG0f.frame_addr lyc 2 pos = fr ->
  lib.Lib.Frame.munch (C_reac_box_catalogue_matchLibW.cmWst Sp fr) mb mc ->
  lib.Reusable.YK1b.mem_grows mb mc ->
  (forall x, lib.Reusable.YA0n.w_H Wc x = true -> mc x = mb x) ->
  lib.Reusable.YK04.same_but_materialized mdc mdc' ->
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own lyc Sc Wc mc mdc' k.
Proof.
  intros Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k mc mdc' pos fr HJ Hin Hfa MU Hgr Hhid Hsame.
  apply (lib.Reusable.YCbq.ajournal_exec rsegs B LAWS segs_low C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0
           mem0 md0 own lyc Sc Wc mb mdc k mc mdc'
           (fun a => ~ lib.Lib.Frame.outside (C_reac_box_catalogue_matchLibW.cmWst Sp fr) a) HJ).
  - intros x Hx. unfold lib.Reusable.YK04.mrestrict. destruct (lib.Reusable.YA0n.w_H Wc x); [reflexivity|].
    apply MU. destruct (B.ProgWorld.pws_outside_dec (C_reac_box_catalogue_matchLibW.cmWst Sp fr) (bv_unsigned x))
      as [Ho|Ho]; [exact Ho | exfalso; exact (Hx Ho)].
  - exact (B.ProgWorld.pws_grows_mrestrict _ _ _ Hgr).
  - exact Hhid.
  - exact Hsame.
  - intros a Ha. unfold C_reac_box_catalogue_matchLibW.cmWst in Ha. cbn [lib.Lib.Frame.outside] in Ha.
    assert (ESH : lib.Reusable.YG0f.shadow_addr fr = shadow_addr fr)
      by (unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, shadow_addr, ASAN_K; lia).
    assert (EB : lib.Reusable.YG00.fs_frame_bytes 2 = 256) by (vm_compute; reflexivity).
    unfold lib.Reusable.YCbq.awr_byte, C_reac_box_catalogue_match.CM_STK.
    destruct (Z_lt_le_dec a Sp) as [h1|h1]; [destruct (Z_lt_le_dec a (Sp - 9136)) as [h2|h2]; [|left; lia]|];
      right; right; right; exists 2, pos; (split; [exact Hin|]);
      unfold lib.Reusable.YG0n.in_zr; cbn [fst snd]; rewrite Hfa, ESH, EB;
      (destruct (Z_lt_le_dec a fr) as [h3|h3]; [|destruct (Z_lt_le_dec a (fr + 256)) as [h4|h4]; [left; lia|]]);
      right; lia.
Qed.

(* The class-2 frame of the pinned values: ly_F lyc = ly_F ly0 (the journal's layout_le), and
   frame_addr lyc 2 pos = fs_frame (ly_F ly0) 2 pos by B.ProgWorld.ctl_fs_geom (Qed). *)
Lemma cmPfB_jr_lyF : forall (Sp : Z) ly0 S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
    (Wc : lib.Reusable.YA0n.world rsegs) (mb : word -> option byte) mdc k,
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k ->
  lib.Reusable.YG0f.ly_F lyc = lib.Reusable.YG0f.ly_F ly0.
Proof.
  intros Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k HJ.
  destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). exact EF.
Qed.

Lemma cmPfB_jr_frame_addr : forall (Sp : Z) ly0 S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
    (Wc : lib.Reusable.YA0n.world rsegs) (mb : word -> option byte) mdc k (pos : Z),
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k ->
  lib.Reusable.YG0f.frame_addr lyc 2 pos = fs_frame (lib.Reusable.YG0f.ly_F ly0) 2 pos.
Proof.
  intros Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k pos HJ.
  rewrite <- (cmPfB_jr_lyF Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k HJ).
  destruct (B.ProgWorld.ctl_fs_geom (lib.Reusable.YG0f.ly_F lyc) 2 pos ltac:(lia)) as (_ & _ & E & _).
  change (Z.to_nat 2) with 2%nat in E. rewrite E. reflexivity.
Qed.

(* Item 2 at the pinned frame fr := fs_frame (ly_F ly0) 2 pos. *)
Lemma cmPfB_jr_journal_pin : forall (Sp : Z) ly0 S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
    (Wc : lib.Reusable.YA0n.world rsegs) (mb : word -> option byte) mdc k (mc : word -> option byte) mdc' (pos : Z),
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k ->
  In (2, pos) own ->
  lib.Lib.Frame.munch (C_reac_box_catalogue_matchLibW.cmWst Sp (fs_frame (lib.Reusable.YG0f.ly_F ly0) 2 pos)) mb mc ->
  lib.Reusable.YK1b.mem_grows mb mc ->
  (forall x, lib.Reusable.YA0n.w_H Wc x = true -> mc x = mb x) ->
  lib.Reusable.YK04.same_but_materialized mdc mdc' ->
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own lyc Sc Wc mc mdc' k.
Proof.
  intros Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k mc mdc' pos HJ Hin MU Hgr Hhid Hsame.
  exact (cmPfB_jr_journal Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k mc mdc' pos _ HJ Hin
           (cmPfB_jr_frame_addr Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k pos HJ) MU Hgr Hhid Hsame).
Qed.

(* The journal with FP = [] does not depend on the sink head (its one SK clause, fp_spares FP, holds for every a when
   FP holds no sink: YCbq.fp_spares_closed / sink_closed_nil).  B.ProgWorld's statements fix SK to
   lib.Reusable.YE2k.tfib_sink_head; this moves the journal there.  Proof of C_reac_box_catalogue_matchPfZ.cmZ_ajournal_sk. *)
Lemma cmPfB_jr_ajournal_sk : forall (SK1 SK2 : lib.Reusable.YI16.sink_head) STK sp0 ly S
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

(* Item 3, the window [Sp - 9136, Sp): B.ProgWorldVisWin.win_vis (Qed) on the journal, B.ProgBridge.rng_of_visible. *)
Lemma cmPfB_jr_rng_win : forall (Sp : Z) ly0 S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
    (Wc : lib.Reusable.YA0n.world rsegs) (mb : word -> option byte) mdc k,
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k ->
  lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H Wc)) (Sp - 9136) 9136.
Proof.
  intros Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k HJ.
  apply B.ProgBridge.rng_of_visible.
  exact (B.ProgWorldVisWin.win_vis B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k
           (Sp - 9136) 9136 (cmPfB_jr_ajournal_sk SK lib.Reusable.YE2k.tfib_sink_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)
           ltac:(unfold C_reac_box_catalogue_match.CM_STK; lia) ltac:(lia)).
Qed.

(* Item 3, the window's shadow [shadow_addr (Sp - 9136), shadow_addr Sp): B.ProgWorldVisWin.win_sh_vis (Qed) at the
   journal's head AR; the stack bounds ly_stk_lo lyc <= Sp - 9136, Sp <= ly_stk_hi lyc from the journal's astk_ok
   (at ly0) and layout_le; the sh_al8 cover contains the range (B.ProgBridge.range_visible_sub). *)
Lemma cmPfB_jr_rng_win_sh : forall (Sp : Z) ly0 S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
    (Wc : lib.Reusable.YA0n.world rsegs) (mb : word -> option byte) mdc k,
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k ->
  lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H Wc))
    (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)).
Proof.
  intros Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k HJ.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (S16 & _ & Hceil & Hslo & Hshi & _) & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  unfold C_reac_box_catalogue_match.CM_STK in Hslo.
  destruct (B.ProgWorldVisWin.win_sh_vis B LAWS lyc Sc Wc mb mdc (Sp - 9136) 9136 HAR
              ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia) ltac:(lia)) as [E0 | VSH]; [lia|].
  apply B.ProgBridge.rng_of_visible.
  apply (B.ProgBridge.range_visible_sub _ _ _ _ _ VSH);
    unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* Item 3, the request's 50 bytes [f, f + 50) of a live heap block (f, n), 50 <= req_size n:
   B.ProgWorldVisHeap.heap_vis (Qed) at the journal's head AR. *)
Lemma cmPfB_jr_rng_heap : forall (Sp : Z) ly0 S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
    (Wc : lib.Reusable.YA0n.world rsegs) (mb : word -> option byte) mdc k (f len : Z),
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k ->
  (50 <= len -> exists n, In (f, n) (lib.Reusable.YG0d.ablocks B lyc Sc) /\ 50 <= lib.Reusable.YG00.req_size n) ->
  50 <= len -> lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H Wc)) f 50.
Proof.
  intros Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k f len HJ Hblk H50.
  destruct (Hblk H50) as (n & Hin & Hn). pose proof HJ as (HAR & _).
  apply B.ProgBridge.rng_of_visible.
  exact (B.ProgWorldVisHeap.heap_vis B LAWS lyc Sc Wc mb mdc f n f 50 HAR Hin ltac:(lia) ltac:(lia)).
Qed.

(* Item 3, the shadow word cover of every sub-range of [f, f + 50): B.ProgWorldVisHeap.heap_sh_vis (Qed); sh_cover
   (reac_box_model_block_c.v:138) is rng over exactly the sh_al8 cover (rng_asan.sh_al8_lo / sh_al8_hi). *)
Lemma cmPfB_jr_rng_heap_sh : forall (Sp : Z) ly0 S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
    (Wc : lib.Reusable.YA0n.world rsegs) (mb : word -> option byte) mdc k (f len : Z),
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k ->
  (50 <= len -> exists n, In (f, n) (lib.Reusable.YG0d.ablocks B lyc Sc) /\ 50 <= lib.Reusable.YG00.req_size n) ->
  50 <= len -> forall p n, f <= p -> 0 < n -> p + n <= f + 50 ->
  sh_cover (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H Wc)) p n.
Proof.
  intros Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k f len HJ Hblk H50 p n Hp Hn Hpn.
  destruct (Hblk H50) as (nb & Hin & Hnb). pose proof HJ as (HAR & _).
  destruct (B.ProgWorldVisHeap.heap_sh_vis B LAWS lyc Sc Wc mb mdc f nb p n HAR Hin ltac:(lia) ltac:(lia) ltac:(lia))
    as [E0 | V]; [lia|].
  unfold sh_cover. apply B.ProgBridge.rng_of_visible.
  unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi in V. exact V.
Qed.

(* Item 3, the side stack: its header [FS, fs_frame FS 0 0) and every fp_w [0; 1; 2] FS range, FS := ly_F lyc:
   C_reac_box_catalogue_matchPfV.cmPf_fs_vis (Qed, 88d3b215222) at the journal's head AR. *)
Lemma cmPfB_jr_rng_fs : forall (Sp : Z) ly0 S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
    (Wc : lib.Reusable.YA0n.world rsegs) (mb : word -> option byte) mdc k,
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H Wc)) (fst iv) (snd iv - fst iv))
    (fp_w [0%nat; 1%nat; 2%nat] (lib.Reusable.YG0f.ly_F lyc)) /\
  lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H Wc)) (lib.Reusable.YG0f.ly_F lyc)
    (fs_frame (lib.Reusable.YG0f.ly_F lyc) 0 0 - lib.Reusable.YG0f.ly_F lyc).
Proof.
  intros Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k HJ. pose proof HJ as (HAR & _).
  destruct (C_reac_box_catalogue_matchPfV.cmPf_fs_vis B lyc Sc Wc mb mdc HAR) as [VH VF].
  split; [|exact (B.ProgBridge.rng_of_visible _ _ _ VH)].
  eapply Forall_impl; [|exact VF]. intros iv Hv. exact (B.ProgBridge.rng_of_visible _ _ _ Hv).
Qed.

(* Item 3, the image [0x10000, 0x5fe000) (B.ProgBridge.img_vis_W, as C_reac_box_catalogue_matchPf.cmPf_SA) and
   rng_bytes (B.ProgBridge.rng_bytes_RNG_W): every world. *)
Lemma cmPfB_jr_rng_img : forall (Wc : lib.Reusable.YA0n.world rsegs),
  lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H Wc)) 65536 6217728 /\
  RngBytes.rng_bytes (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H Wc)).
Proof.
  intros Wc. split; [|exact (B.ProgBridge.rng_bytes_RNG_W _)].
  pose proof (B.ProgBridge.rng_of_visible _ _ _ (B.ProgBridge.img_vis_W Wc)) as R.
  unfold ImgBounds.IMG_LO, ImgBounds.IMG_HI in R. exact R.
Qed.

(* Item 3, all the footprint premises of a re-based stretch (C_reac_box_catalogue_matchLibW.cmRBw_post_sm2_side
   :1804-1807 and the image / rng_bytes premises of the lifts), RNG := RNG_W (w_H Wc), FS := ly_F lyc. *)
Lemma cmPfB_jr_rng : forall (Sp : Z) ly0 S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
    (Wc : lib.Reusable.YA0n.world rsegs) (mb : word -> option byte) mdc k (f len : Z),
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k ->
  (50 <= len -> exists n, In (f, n) (lib.Reusable.YG0d.ablocks B lyc Sc) /\ 50 <= lib.Reusable.YG00.req_size n) ->
  let RNG := B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H Wc) in
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 /\
  lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) /\
  (50 <= len -> lib.Lib.ExecF.rng RNG f 50) /\
  (50 <= len -> forall p n, f <= p -> 0 < n -> p + n <= f + 50 -> sh_cover RNG p n) /\
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv))
    (fp_w [0%nat; 1%nat; 2%nat] (lib.Reusable.YG0f.ly_F lyc)) /\
  lib.Lib.ExecF.rng RNG (lib.Reusable.YG0f.ly_F lyc)
    (fs_frame (lib.Reusable.YG0f.ly_F lyc) 0 0 - lib.Reusable.YG0f.ly_F lyc) /\
  lib.Lib.ExecF.rng RNG 65536 6217728 /\
  RngBytes.rng_bytes RNG.
Proof.
  intros Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k f len HJ Hblk RNG.
  destruct (cmPfB_jr_rng_fs Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k HJ) as [VF VH].
  destruct (cmPfB_jr_rng_img Wc) as [VI VB].
  split; [exact (cmPfB_jr_rng_win Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k HJ)|].
  split; [exact (cmPfB_jr_rng_win_sh Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k HJ)|].
  split; [exact (cmPfB_jr_rng_heap Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k f len HJ Hblk)|].
  split; [exact (cmPfB_jr_rng_heap_sh Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k f len HJ Hblk)|].
  exact (conj VF (conj VH (conj VI VB))).
Qed.

(* The same at the pinned FS := ly_F ly0 (= ly_F lyc by cmPfB_jr_lyF). *)
Lemma cmPfB_jr_rng_pin : forall (Sp : Z) ly0 S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
    (Wc : lib.Reusable.YA0n.world rsegs) (mb : word -> option byte) mdc k (f len : Z),
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k ->
  (50 <= len -> exists n, In (f, n) (lib.Reusable.YG0d.ablocks B lyc Sc) /\ 50 <= lib.Reusable.YG00.req_size n) ->
  let RNG := B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H Wc) in
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 /\
  lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) /\
  (50 <= len -> lib.Lib.ExecF.rng RNG f 50) /\
  (50 <= len -> forall p n, f <= p -> 0 < n -> p + n <= f + 50 -> sh_cover RNG p n) /\
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv))
    (fp_w [0%nat; 1%nat; 2%nat] (lib.Reusable.YG0f.ly_F ly0)) /\
  lib.Lib.ExecF.rng RNG (lib.Reusable.YG0f.ly_F ly0)
    (fs_frame (lib.Reusable.YG0f.ly_F ly0) 0 0 - lib.Reusable.YG0f.ly_F ly0) /\
  lib.Lib.ExecF.rng RNG 65536 6217728 /\
  RngBytes.rng_bytes RNG.
Proof.
  intros Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k f len HJ Hblk RNG.
  rewrite <- (cmPfB_jr_lyF Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k HJ).
  exact (cmPfB_jr_rng Sp ly0 S0 W0 mem0 md0 own lyc Sc Wc mb mdc k f len HJ Hblk).
Qed.



(* ============================================================================================================
   pa: the reac_ctrl_parse event (E2, return address 0x85058) of reac_box_catalogue_match, image B.
   cmPfB_pa_call : TPARSE (C_reac_ctrl_parse.v:58-73) at the parse call, every premise discharged.
   cmPfB_pa_ret  : from TPARSE's post (C_reac_ctrl_parse.v:45-57), the return state, its journal, and the premises
                   C_reac_box_catalogue_matchLibW.cmRBw_post_parse takes at its base memory (the return memory)
                   with call memory mc: the callee window's stk, the 36 output bytes as rw_cells, cmRB_kept.
   Pinned frame values: FS := ly_F ly, fr := fs_frame FS 2 pos, nn := 1, jj := pos, sp2 := CA Sp.
   Only Section hypotheses LAWS and TPARSE are used; no frame-route premise is needed.
   ============================================================================================================ *)

(* An equal view of a byte present in both worlds is an equal raw byte. *)
Lemma cmPfB_pa_raw_of_view : forall (W1 W2 : lib.Reusable.YA0n.world rsegs) (m1 m2 : word -> option byte) (a : Z),
  lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W1) m1 a ->
  lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W2) m2 a ->
  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W2) m2 a =
  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W1) m1 a ->
  m2 (lib.Lib.Mem.wa a) = m1 (lib.Lib.Mem.wa a).
Proof.
  intros W1 W2 m1 m2 a (H1 & b1 & E1) (H2 & b2 & E2) Hv.
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in Hv.
  rewrite H1, H2, E1, E2 in Hv. cbn [option_map] in Hv. injection Hv as Hb.
  unfold lib.Lib.Mem.wa. rewrite E1, E2. f_equal. apply bv_eq. exact Hb.
Qed.

(* A byte with a non-negative signed value has that value unsigned. *)
Lemma cmPfB_pa_byte_signed : forall b : byte, 0 <= bv_signed b -> bv_unsigned b = bv_signed b.
Proof.
  intros b Hs. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold bv_signed, bv_swrap, bv_wrap in *. change (bv_half_modulus 8) with 128 in *. change (bv_modulus 8) with 256 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* B.ProgWorld.aview_vis_mrd at rsegs (= YB1v.tfibsegs, ProgBridge.tfibsegs_rsegs). *)
Lemma cmPfB_pa_vis_mrd : forall (W : lib.Reusable.YA0n.world rsegs) (mem : word -> option byte) (a : Z),
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem a =
  option_map (fun b : byte => bv_unsigned b) (lib.Lib.Mem.mrd rsegs mem (Z_to_bv 64 a)).
Proof. intros W mem a H. exact (B.ProgWorld.aview_vis_mrd W mem a H). Qed.

(* The pinned class-2 frame: frame_addr ly 2 pos = fs_frame (ly_F ly) 2 pos. *)
Lemma cmPfB_pa_frame_addr : forall (ly : lib.Reusable.YG0f.alayout) (pos : Z),
  lib.Reusable.YG0f.frame_addr ly 2 pos = B.Prog.asan_stack_malloc_c.fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos.
Proof.
  intros ly pos. unfold lib.Reusable.YG0f.frame_addr, lib.Reusable.YG0f.fs_frame_off, B.Prog.asan_stack_malloc_c.fs_frame,
    B.Prog.asan_stack_malloc_c.fs_B, lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG00.kStackSizeLog.
  change (lib.Reusable.YG00.fs_frame_bytes 2) with 256.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 20) with 1048576. change (Z.of_nat 2) with 2. change (2 ^ 2) with 4. lia.
Qed.

(* CA's arithmetic (CA Sp = (Sp - 128) / 32 * 32, reac_box_catalogue_matchF_on.v:316). *)
Lemma cmPfB_pa_CA : forall Sp, CA Sp mod 16 = 0 /\ Sp - 159 <= CA Sp <= Sp - 128.
Proof. intros Sp. unfold CA. Z.div_mod_to_equations. lia. Qed.

(* A live class-2 frame under AR (AR_frames_law, YG0d.v:447-455): aligned, in application memory, its 256 bytes and its
   32 shadow bytes present (so visible). *)
Lemma cmPfB_pa_frame_AR : forall (ly' : lib.Reusable.YG0f.alayout) (S' : lib.Reusable.YG00.astate)
    (W' : lib.Reusable.YA0n.world rsegs) (m' : word -> option byte) (md' : Model) (pos : Z),
  lib.Reusable.YG0n.AR rsegs B ly' S' W' m' md' -> In (2, pos) (lib.Reusable.YG01.frames S') ->
  lib.Reusable.YG0f.frame_addr ly' 2 pos mod 32 = 0 /\
  lib.Reusable.YG0f.in_app (lib.Reusable.YG0f.frame_addr ly' 2 pos) 256 /\
  (forall a, lib.Reusable.YG0f.frame_addr ly' 2 pos <= a < lib.Reusable.YG0f.frame_addr ly' 2 pos + 256 ->
     lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W') m' a) /\
  (forall a, lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr ly' 2 pos) <= a <
             lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr ly' 2 pos) + 32 ->
     lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W') m' a).
Proof.
  intros ly' S' W' m' md' pos HAR Hin.
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS ly' S' W' m' md' 2 pos HAR Hin) as (Hal & Happ & Hby & Hsh).
  change (lib.Reusable.YG00.fs_frame_bytes 2) with 256 in *. change (256 / 8) with 32 in Hsh.
  split; [exact Hal|]. split; [exact Happ|]. split.
  - intros a Ha. exact (proj1 (Hby a Ha)).
  - intros a Ha.
    set (s0 := lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr ly' 2 pos)) in *.
    pose proof (proj1 (Hsh (a - s0) ltac:(lia))) as H.
    replace (s0 + (a - s0)) with a in H by ring. exact H.
Qed.

(* The view's addressability of [p, p + n) from ctrl's raw addressable, where each shadow byte is visible. *)
Lemma cmPfB_pa_range_addr : forall (W : lib.Reusable.YA0n.world rsegs) (m : word -> option byte) (p n : Z),
  B.AsanRT.addressable m p n ->
  (forall x, p <= x < p + n ->
     lib.Reusable.YA0n.w_H W (Z_to_bv 64 (lib.Reusable.YG0f.SHADOW_OFF + x / 8)) = false) ->
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m)
    lib.Reusable.YG0f.SHADOW_OFF p n.
Proof.
  intros W m p n (_ & _ & _ & HA) Hvis x Hx.
  destruct (HA (x - p) ltac:(lia)) as (_ & b & Hb & Hok).
  replace (p + (x - p)) with x in Hb, Hok by ring.
  exists (bv_unsigned b). split.
  - unfold lib.Reusable.YG0v.shadow_of_addr.
    rewrite (cmPfB_pa_vis_mrd W m _ (Hvis x Hx)).
    replace (Z_to_bv 64 (lib.Reusable.YG0f.SHADOW_OFF + x / 8)) with (lib.Lib.Mem.wa (B.AsanRT.shadow_addr x))
      by (unfold lib.Lib.Mem.wa, B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, lib.Reusable.YG0f.SHADOW_OFF; f_equal; lia).
    rewrite Hb. reflexivity.
  - unfold B.AsanRT.shadow_ok in Hok. unfold lib.Reusable.YG0v.saddr_ok.
    destruct Hok as [H0 | (H1 & H2)].
    + left. rewrite (cmPfB_pa_byte_signed b) by lia. exact H0.
    + right. rewrite (cmPfB_pa_byte_signed b) by lia. lia.
Qed.

(* nth of the byte list's values. *)
Lemma cmPfB_pa_nth_map : forall (l : list byte) (i : nat), (i < length l)%nat ->
  nth i (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth i l cp_z).
Proof.
  induction l as [|b l IH]; intros [|i] Hi; cbn [length] in Hi; try lia; [reflexivity|].
  cbn [map nth]. apply IH. lia.
Qed.

(* ---- 1. the parse call: TPARSE with every premise discharged ---- *)
Lemma cmPfB_pa_call :
  forall (ly : lib.Reusable.YG0f.alayout) (S : lib.Reusable.YG00.astate) (W : lib.Reusable.YA0n.world rsegs)
         (memc : word -> option byte) (md : Model) (Sp : Z)
         (lyc : lib.Reusable.YG0f.alayout) (Sc : lib.Reusable.YG00.astate) (Wc : lib.Reusable.YA0n.world rsegs)
         (mc : word -> option byte) (mdc : Model)
         (ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mb : word -> option byte)
         (f len : Z) (fb : list byte) (pos : Z),
  (* RELRO_IMG: the spec's Section hypothesis (C_reac_box_catalogue_match.v:45), discharged by the composer *)
  (forall a, RLO <= a < RHI -> lib.Reusable.YG0d.in_img rsegs a) ->
  (* the journal from the entry to the call, own = the class-2 frame *)
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly S W memc md [(2, pos)]
    lyc Sc Wc mc mdc 0 ->
  lib.Reusable.YG01.frames Sc = (2, pos) :: lib.Reusable.YG01.frames S ->
  lib.Reusable.YG0d.ablocks B lyc Sc = lib.Reusable.YG0d.ablocks B ly S ->
  (* stretch 2's end at the call (C_reac_box_catalogue_matchLibW.v:1690) *)
  C_reac_box_catalogue_matchLibW.cmRBw_AtParse ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp
    (lib.Reusable.YG0f.ly_F ly) fb (B.Prog.asan_stack_malloc_c.fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos)
    (CA Sp) pos 1 mc ->
  (* the entry's spec premises (C_reac_box_catalogue_match.v:87-98) *)
  lib.Reusable.YE01.arodata_okS rsegs B RLO RHI (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc) ->
  0 <= len < 2 ^ 64 -> length fb = 50%nat ->
  (50 <= len -> exists n, In (f, n) (lib.Reusable.YG0d.ablocks B ly S) /\ 50 <= lib.Reusable.YG00.req_size n) ->
  (50 <= len -> lib.Reusable.YI00.garr8 rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) memc) f
                  (map (fun b : byte => bv_unsigned b) fb)) ->
  lib.Reusable.YG01.count_cid 1 (lib.Reusable.YG01.frames S) < lib.Reusable.YG00.fs_frames 1 ->
  forall regsP : bvmap 5 word,
  lib.Reusable.YK11.getr regsP 1 = Z_to_bv 64 0x85058 -> lib.Reusable.YG0d.spZ regsP = CA Sp ->
  lib.Reusable.YK11.getr regsP 3 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_gp B) ->
  lib.Reusable.YK11.getr regsP 4 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B) ->
  lib.Reusable.YK11.getr regsP 10 = lib.Reusable.YG0d.w64 f ->
  lib.Reusable.YK11.getr regsP 11 = lib.Reusable.YG0d.w64 len ->
  lib.Reusable.YK11.getr regsP 12 =
    lib.Reusable.YG0d.w64 (B.Prog.asan_stack_malloc_c.fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos + 32) ->
  lib.Reusable.YA0n.SRr rsegs Wc (lib.Reusable.YG0d.cfg_at rsegs C_reac_ctrl_parse.A_reac_ctrl_parseP regsP mc mdc)
    (C_reac_ctrl_parse.treac_ctrl_parse_post rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly S W memc md [(2, pos)]
       lyc Sc Wc mc 0 regsP len (B.Prog.asan_stack_malloc_c.fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos + 32) fb).
Proof.
  intros ly S W memc md Sp lyc Sc Wc mc mdc ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len fb pos
    RELRO J HFS HBL AT ARO Hlen Hfb HBLK HGA HCNT regsP R1 RSP R3 R4 R10 R11 R12.
  remember (B.Prog.asan_stack_malloc_c.fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos) as fr eqn:Efr.
  pose proof J as (HARc & HLY & _ & _ & _ & _ & _ & _ & _ & JBL & JIMG & _).
  assert (EF : lib.Reusable.YG0f.frame_addr lyc 2 pos = fr).
  { rewrite cmPfB_pa_frame_addr, Efr. destruct HLY as (_ & _ & _ & _ & _ & EFl & _). rewrite EFl. reflexivity. }
  assert (Hin : In (2, pos) (lib.Reusable.YG01.frames Sc)) by (rewrite HFS; left; reflexivity).
  destruct (cmPfB_pa_frame_AR lyc Sc Wc mc mdc pos HARc Hin) as (Hal & Happ & Hby & Hsh).
  rewrite EF in Hal, Happ, Hby, Hsh.
  destruct AT as (L50 & _ & _ & _ & _ & _ & HAD).
  pose proof (cmPfB_pa_CA Sp) as (CA16 & CAlo & CAhi).
  apply (TPARSE C_reac_box_catalogue_match.CM_STK Sp [] ly S W memc md [(2, pos)] lyc Sc Wc mc mdc 0 regsP
           f len (fr + 32) fb J).
  - (* arodata_okS, kept by the journal's image clause *)
    intros a Hro Ho He.
    rewrite (JIMG a); [exact (ARO a Hro Ho He) | | exact Ho | exact He | ].
    + destruct Hro as [(sg & Hs & _ & Hr) | Hr]; [exists sg; split; [exact Hs | exact Hr] | exact (RELRO a Hr)].
    + apply lib.Reusable.YCbq.fp_spares_closed. intros (r & Hr & _). destruct Hr.
  - rewrite R1. apply lib.Reusable.YK0s.ret_ok_even. vm_compute. reflexivity.
  - unfold lib.Reusable.YG0d.raZ. rewrite R1. vm_compute. discriminate.
  - exact R3.
  - exact R4.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact Hlen.
  - rewrite RSP. exact CA16.
  - rewrite RSP. unfold C_reac_box_catalogue_match.CM_STK, C_reac_ctrl_parse.REAC_CTRL_PARSE_STK. lia.
  - rewrite RSP. lia.
  - rewrite HFS. cbn [lib.Reusable.YG01.count_cid Z.eqb Pos.eqb]. exact HCNT.
  - intros L. rewrite HBL. exact (HBLK L).
  - (* afobj: the 36 bytes at fr + 32 in our live class-2 frame, addressable in the view *)
    intros _. split; [|split].
    + exists 2, pos. rewrite EF. split; [exact Hin|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|].
      change (lib.Reusable.YG00.fs_frame_bytes 2) with 256. lia.
    + Z.div_mod_to_equations; lia.
    + apply cmPfB_pa_range_addr; [exact HAD|]. intros x Hx.
      refine (proj1 (Hsh _ _)).
      clear - Hx Hal. unfold lib.Reusable.YG0f.shadow_addr. Z.div_mod_to_equations. lia.
  - (* awr_byte: in_frames lyc [(2, pos)] *)
    intros _ a Ha. right; right; right. exists 2, pos. split; [left; reflexivity|]. left.
    unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite EF. change (lib.Reusable.YG00.fs_frame_bytes 2) with 256. lia.
  - exact Hfb.
  - (* the record's 50 bytes, kept by the journal's block clause *)
    intros L i Hi.
    destruct (HBLK L) as (n & Hn & Hn50).
    assert (Hnc : In (f, n) (lib.Reusable.YG0d.ablocks B lyc Sc)) by (rewrite HBL; exact Hn).
    rewrite (JBL f n (Z.of_nat i) Hn Hnc ltac:(lia) (lib.Reusable.YI04.inFP_nil _)).
    assert (Hi' : (i < length (map (fun b : byte => bv_unsigned b) fb))%nat) by (rewrite length_map; lia).
    pose proof (lib.Reusable.YI00.garr8_mbyte rsegs _ f _ i (HGA L) Hi') as Hm.
    unfold lib.Reusable.YG0n.aview. cbv beta. rewrite Hm. cbn [option_map]. f_equal.
    rewrite (cmPfB_pa_nth_map fb i) by lia. unfold cp_v, cp_b. apply Z_to_bv_small. apply bv_unsigned_in_range.
Qed.

(* ---- 2. after the post: the return state, its journal, and cmRBw_post_parse's premises at the return memory ---- *)
Lemma cmPfB_pa_ret :
  forall (ly : lib.Reusable.YG0f.alayout) (S : lib.Reusable.YG00.astate) (W : lib.Reusable.YA0n.world rsegs)
         (memc : word -> option byte) (md : Model) (Sp : Z)
         (lyc : lib.Reusable.YG0f.alayout) (Sc : lib.Reusable.YG00.astate) (Wc : lib.Reusable.YA0n.world rsegs)
         (mc : word -> option byte) (mdc : Model) (len : Z) (fb : list byte) (pos : Z) (regsP : bvmap 5 word)
         (W2 : lib.Reusable.YA0n.world rsegs) (c2 : config),
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly S W memc md [(2, pos)]
    lyc Sc Wc mc mdc 0 ->
  lib.Reusable.YG01.frames Sc = (2, pos) :: lib.Reusable.YG01.frames S ->
  lib.Reusable.YK11.getr regsP 1 = Z_to_bv 64 0x85058 -> lib.Reusable.YG0d.spZ regsP = CA Sp ->
  C_reac_ctrl_parse.treac_ctrl_parse_post rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly S W memc md [(2, pos)]
    lyc Sc Wc mc 0 regsP len (B.Prog.asan_stack_malloc_c.fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos + 32) fb W2 c2 ->
  exists (ly3 : lib.Reusable.YG0f.alayout) (S3 : lib.Reusable.YG00.astate) (regs3 : bvmap 5 word)
         (mem3 : word -> option byte) (md3 : Model),
    c2 = lib.Reusable.YG0d.cfg_at rsegs 0x85058 regs3 mem3 md3 /\
    lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly S W memc md [(2, pos)]
      ly3 S3 W2 mem3 md3 0 /\
    lib.Reusable.YG01.frames S3 = lib.Reusable.YG01.frames Sc /\
    lib.Reusable.YG0d.ablocks B ly3 S3 = lib.Reusable.YG0d.ablocks B lyc Sc /\
    (exists ff, S3 = lib.Reusable.YG00.set_fs ff Sc) /\
    lib.Reusable.YG0d.aregs_preserved regsP regs3 /\
    lib.Reusable.YK11.getr regs3 10 = lib.Reusable.YG0d.w64 (fst (ctrlparse len fb)) /\
    (* cmRBw_post_parse's return-memory premises (C_reac_box_catalogue_matchLibW.v:1940-1942), call memory mc *)
    lib.Lib.Frame.stk rsegs mem3 (CA Sp - 8800) (CA Sp) /\
    lib.Lib.Step.rw_cells rsegs mem3 (B.Prog.asan_stack_malloc_c.fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos + 32)
      [lib.Lib.Cells.CB 36 (snd (ctrlparse len fb))] /\
    C_reac_box_catalogue_matchLib.cmRB_kept mc mem3
      (C_reac_box_catalogue_matchLib.cmRB_callee_kept Sp
         (B.Prog.asan_stack_malloc_c.fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos) (CA Sp) (CA Sp - 8800) 32 36).
Proof.
  intros ly S W memc md Sp lyc Sc Wc mc mdc len fb pos regsP W2 c2 J HFS R1 RSP PO.
  remember (B.Prog.asan_stack_malloc_c.fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos) as fr eqn:Efr.
  destruct PO as (ly3 & S3 & regs3 & mem3 & md3 & Ec & J3 & Hpres & HF3 & HB3 & HSF & H10 & Hout & K).
  pose proof J as (HARc & HLY & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & JPR & JSTK & _).
  pose proof J3 as (HAR3 & HLY3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & J3PR & _).
  destruct K as (K1 & _ & _ & K4 & _ & K6).
  unfold C_reac_ctrl_parse.REAC_CTRL_PARSE_STK in K1, K6. rewrite RSP in K1, K6.
  assert (EF : lib.Reusable.YG0f.frame_addr lyc 2 pos = fr).
  { rewrite cmPfB_pa_frame_addr, Efr. destruct HLY as (_ & _ & _ & _ & _ & EFl & _). rewrite EFl. reflexivity. }
  assert (EF3 : lib.Reusable.YG0f.frame_addr ly3 2 pos = fr).
  { rewrite cmPfB_pa_frame_addr, Efr. destruct HLY3 as (_ & _ & _ & _ & _ & EFl & _). rewrite EFl. reflexivity. }
  assert (Hin : In (2, pos) (lib.Reusable.YG01.frames Sc)) by (rewrite HFS; left; reflexivity).
  assert (Hin3 : In (2, pos) (lib.Reusable.YG01.frames S3)) by (rewrite HF3; exact Hin).
  destruct (cmPfB_pa_frame_AR lyc Sc Wc mc mdc pos HARc Hin) as (Hal & Happ & Hby & Hsh).
  destruct (cmPfB_pa_frame_AR ly3 S3 W2 mem3 md3 pos HAR3 Hin3) as (_ & _ & Hby3 & Hsh3).
  rewrite EF in Hal, Happ, Hby, Hsh. rewrite EF3 in Hby3, Hsh3.
  (* the window [Sp - 9136, Sp) lies above YM05's alloc_ceiling and below 2 ^ 47 (astk_ok) *)
  destruct JSTK as (_ & _ & Hceil & Hlo & Hhi & H47 & _).
  unfold C_reac_box_catalogue_match.CM_STK in *.
  pose proof (cmPfB_pa_CA Sp) as (_ & CAlo & CAhi).
  assert (P64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (P47 : 2 ^ 47 = 140737488355328) by reflexivity.
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as (Cv & _).
  assert (Hfr0 : 4096 <= fr /\ fr + 256 <= 2 ^ 64).
  { clear - Happ P64 Cv. unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg,
      lib.Reusable.YG0f.kHighMemBeg, lib.Reusable.YG0f.ASAN_CEIL in Happ. lia. }
  exists ly3, S3, regs3, mem3, md3.
  split; [rewrite Ec, R1; reflexivity|].
  split; [exact J3|]. split; [exact HF3|]. split; [exact HB3|]. split; [exact HSF|]. split; [exact Hpres|].
  split; [exact H10|].
  split.
  { (* stk over the callee window: acall_kept's presence clause *)
    split; [lia|]. split; [lia|]. intros a Ha.
    destruct (K6 a Ha) as (_ & b & Eb). unfold lib.Lib.Mem.wa.
    split; [unfold wview; rewrite Eb; discriminate | exists b; unfold lib.Lib.Mem.mrd; rewrite Eb; reflexivity]. }
  split.
  { (* the 36 output bytes: the post's view bytes at visible, present frame bytes *)
    apply B.ProgWorld.rw_cells_CB_of_present; [apply ctrlparse_length | lia | cbn [Z.of_nat]; lia | |].
    - intros i Hi.
      assert (Hv : lib.Reusable.YA0n.w_H W2 (Z_to_bv 64 (fr + 32 + Z.of_nat i)) = false)
        by exact (proj1 (Hby3 (fr + 32 + Z.of_nat i) ltac:(lia))).
      rewrite (B.ProgWorld.mrd_of_aview_some W2 mem3 _ _ Hv (Hout ltac:(lia) i Hi)).
      replace (Z_to_bv 8 (bv_unsigned (nth i (snd (ctrlparse len fb)) cp_z))) with (nth i (snd (ctrlparse len fb)) cp_z)
        by (apply bv_eq; symmetry; apply Z_to_bv_small; apply bv_unsigned_in_range).
      symmetry. apply nth_error_nth'. rewrite ctrlparse_length. exact Hi.
    - intros i Hi. destruct (Hby3 (fr + 32 + i) ltac:(cbn [Z.of_nat] in Hi; lia)) as (_ & b & Eb).
      rewrite Eb. discriminate. }
  (* the kept bytes: an equal view of a byte present at both memories is an equal raw byte *)
  intros a Ha. unfold C_reac_box_catalogue_matchLib.cmRB_callee_kept in Ha.
  destruct Ha as [(Ha1 & Ha2) | [Ha | Ha]].
  - (* the window outside the callee's window: acall_kept's high-memory clause *)
    apply (cmPfB_pa_raw_of_view Wc W2 mc mem3 a (JPR a Ha1) (J3PR a Ha1)).
    apply K1; [lia | exact Ha2].
  - (* the flag word [fr + 248, fr + 256): acall_kept's frame clause *)
    apply (cmPfB_pa_raw_of_view Wc W2 mc mem3 a (Hby a ltac:(lia)) (Hby3 a ltac:(lia))).
    apply (K4 2 pos a Hin); [left | cbv beta; lia].
    unfold lib.Reusable.YCbq.frame_rng, lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite EF.
    change (lib.Reusable.YG00.fs_frame_bytes 2) with 256. lia.
  - (* the output buffer's shadow bytes: inside the frame's shadow, off the buffer *)
    assert (Hs : lib.Reusable.YG0f.shadow_addr fr <= a < lib.Reusable.YG0f.shadow_addr fr + 32 /\
                 ~ (fr + 32 <= a < fr + 32 + 36)).
    { clear - Ha Hal Happ.
      unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF in *.
      unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in Happ.
      destruct Happ as (Hp1 & [Hp2 | (Hp3 & Hp4)]); Z.div_mod_to_equations; lia. }
    destruct Hs as (Hs1 & Hs2).
    apply (cmPfB_pa_raw_of_view Wc W2 mc mem3 a (Hsh a Hs1) (Hsh3 a Hs1)).
    apply (K4 2 pos a Hin); [right | cbv beta; exact Hs2].
    unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite EF.
    change (lib.Reusable.YG00.fs_frame_bytes 2 / 8) with 32. lia.
Qed.



(* ============================================================================================================
   H2MB (prefix mb): row i of the catalogue loop, the reac_box_model_block event (call 0x865d8, return 0x8509c).
     cmPfB_mb_call  TMB (C_reac_box_model_block.treac_box_model_block_spec) at row i's call, every premise discharged
                    from the journal from the entry, row i's ctrl call facts (LibW cmRBw_AtMB) and the entry's spec
                    facts; conclusion: the SRr to treac_box_model_block_post at p = CM_T + 296 i, b = 0,
                    o = fs_frame (ly_F ly) 2 pos + 112, row = cm_row i, nb = [].
     cmPfB_mb_ret   from that post (p <> 0, o <> 0 branch): the return configuration at 0x8509c, the journal, the
                    callee-saved registers, a0 = 1, and the three return-memory premises of
                    C_reac_box_catalogue_matchLibW.cmRBw_post_mb (window stk, the buffer, cmRB_kept from the call
                    memory).
   Frame-route premises: HG17 / HTRO of cmPfB_mb_call (table facts), each named at its premise.
   Core image premise: RELRO_IMG (C_reac_box_catalogue_match.v:45), needed to carry arodata_okS along the journal.
   ============================================================================================================ *)

(* ---- list / image helpers (no frame-route fact) ---- *)

Lemma cmPfB_mb_nth_firstn : forall {A : Type} (l : list A) n j, (j < n)%nat -> nth_error (firstn n l) j = nth_error l j.
Proof. intros A l n j Hj. rewrite nth_error_firstn. destruct (Nat.ltb_spec j n); [reflexivity | lia]. Qed.

(* image_bytes reads the image's read-only bytes one by one *)
Lemma cmPfB_mb_image_nth : forall (segs : list Segment) (n : nat) (A : Z) (bs : list byte),
  lib.Lib.Image.image_bytes segs A n = Some bs ->
  forall j, (j < n)%nat -> lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 (A + Z.of_nat j)) = nth_error bs j.
Proof.
  intros segs n. induction n as [|n IH]; intros A bs H j Hj; [lia|].
  cbn [lib.Lib.Image.image_bytes] in H.
  destruct (lib.Lib.PropExec.seg_rom segs (lib.Lib.Mem.wa A)) as [b|] eqn:E; [|discriminate H].
  destruct (lib.Lib.Image.image_bytes segs (A + 1) n) as [bs'|] eqn:E'; [|discriminate H].
  injection H as <-.
  destruct j as [|j].
  - cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. exact E.
  - cbn [nth_error]. rewrite <- (IH (A + 1) bs' E' j ltac:(lia)). f_equal. f_equal. lia.
Qed.

Lemma cmPfB_mb_row_len : forall i, (i < 11)%nat -> length (cm_row i) = 296%nat.
Proof.
  intros i Hi. unfold cm_row. rewrite length_firstn, length_skipn.
  rewrite (lib.Lib.Image.image_bytes_length rsegs 3256 CM_T CM_TBL CM_TBL_eq). lia.
Qed.

(* byte j of row i is the image's byte at CM_T + 296 i + j (CM_TBL_eq) *)
Lemma cmPfB_mb_row_nth : forall i j, (i < 11)%nat -> (j < 296)%nat ->
  lib.Reusable.YK11.seg_rom rsegs (Z_to_bv 64 (CM_T + 296 * Z.of_nat i + Z.of_nat j)) = nth_error (cm_row i) j.
Proof.
  intros i j Hi Hj. unfold cm_row. rewrite (cmPfB_mb_nth_firstn _ _ _ Hj), nth_error_skipn.
  pose proof (cmPfB_mb_image_nth rsegs 3256 CM_T CM_TBL CM_TBL_eq (296 * i + j) ltac:(lia)) as E.
  replace (CM_T + Z.of_nat (296 * i + j)) with (CM_T + 296 * Z.of_nat i + Z.of_nat j) in E by lia.
  exact E.
Qed.

(* garr8 from the byte reads mbyte makes *)
Lemma cmPfB_mb_garr8 : forall (segs : list Segment) (mem : word -> option byte) (base : Z) (bs : list byte),
  (forall j, (j < length bs)%nat -> lib.Reusable.YP09.mbyte segs mem (base + Z.of_nat j) = nth_error bs j) ->
  lib.Reusable.YI00.garr8 segs mem base (map (fun b : byte => bv_unsigned b) bs).
Proof.
  intros segs mem base bs H j Hj. rewrite length_map in Hj.
  destruct (nth_error bs j) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  assert (Hn : nth j (map (fun b : byte => bv_unsigned b) bs) 0 = bv_unsigned b)
    by (apply nth_error_nth; rewrite nth_error_map, Eb; reflexivity).
  rewrite Hn. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  split; [|lia].
  intros k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, (H j Hj), Eb.
  f_equal. unfold lib.Reusable.YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

(* ---- view helpers (no frame-route fact) ---- *)

(* a present byte is read by the view *)
Lemma cmPfB_mb_view_present : forall (H : word -> bool) (m : word -> option byte) (a : Z),
  lib.Reusable.YG0n.apresent H m a ->
  exists b, m (Z_to_bv 64 a) = Some b /\ lib.Reusable.YG0n.aview rsegs H m a = Some (bv_unsigned b).
Proof.
  intros H m a [Hh [b Hb]]. exists b. split; [exact Hb|].
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict. rewrite Hh, Hb. reflexivity.
Qed.

(* aview-to-raw: off the image, a view equality with a byte present on the right is a raw byte equality *)
Lemma cmPfB_mb_raw_of_view : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z),
  0 <= a < 2 ^ 64 -> ~ lib.Reusable.YG0d.in_img rsegs a -> lib.Reusable.YG0n.apresent H m a ->
  lib.Reusable.YG0n.aview rsegs H' m' a = lib.Reusable.YG0n.aview rsegs H m a ->
  m' (lib.Lib.Mem.wa a) = m (lib.Lib.Mem.wa a).
Proof.
  intros H H' m m' a Ha Hni Hp E.
  destruct (cmPfB_mb_view_present H m a Hp) as (b & Hb & Hv). rewrite Hv in E.
  pose proof (lib.Reusable.YCbq.seg_rom_none rsegs a Ha Hni) as Hn.
  unfold lib.Lib.Mem.wa. rewrite Hb.
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in E.
  destruct (H' (Z_to_bv 64 a)); [rewrite Hn in E; discriminate E|].
  destruct (m' (Z_to_bv 64 a)) as [b'|]; [|rewrite Hn in E; discriminate E].
  cbn [option_map] in E. injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* arodata_okS is kept along a journal with FP = [] (APostBase.arodata_ok_journalP's proof, for arodata_okS) *)
Lemma cmPfB_mb_aro : forall STK sp0 ly S (W : lib.Reusable.YA0n.world rsegs) mem md own lyc Sc
    (Wc : lib.Reusable.YA0n.world rsegs) mc mdc k,
  (forall a, RLO <= a < RHI -> lib.Reusable.YG0d.in_img rsegs a) ->
  lib.Reusable.YCbq.ajournal rsegs B STK sp0 [] ly S W mem md own lyc Sc Wc mc mdc k ->
  lib.Reusable.YE01.arodata_okS rsegs B RLO RHI (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem) ->
  lib.Reusable.YE01.arodata_okS rsegs B RLO RHI (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H Wc) mc).
Proof.
  intros STK sp0 ly S W mem md own lyc Sc Wc mc mdc k HRI HJ HR a Hro Ho He.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Kimg & _).
  rewrite (Kimg a); [exact (HR a Hro Ho He) | | exact Ho | exact He | ].
  - destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (HRI a Hr)].
  - apply lib.Reusable.YCbq.fp_spares_closed. intros (r & Hr & _). destruct Hr.
Qed.

(* row i's bytes at the call memory, through the kept read-only view and the image *)
Lemma cmPfB_mb_row_garr8 : forall (Wc : lib.Reusable.YA0n.world rsegs) (mc : word -> option byte) (i : nat),
  (i < 11)%nat ->
  lib.Reusable.YE01.arodata_okS rsegs B RLO RHI (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H Wc) mc) ->
  RLO <= CM_T -> CM_T + 3256 <= RHI ->
  (forall a, C_reac_box_catalogue_match.A_CM_TBL <= a <
             C_reac_box_catalogue_match.A_CM_TBL + C_reac_box_catalogue_match.CM_ROWS ->
     ~ Exists (lib.Reusable.YG0n.in_zr a) (lib.Reusable.YG0f.as_owned_static B) /\
     ~ (lib.Reusable.YG0f.as_errno B <= a < lib.Reusable.YG0f.as_errno B + 4)) ->
  lib.Reusable.YI00.garr8 rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H Wc) mc)
    (CM_T + 296 * Z.of_nat i) (C_reac_box_model_block.bmb_z (cm_row i)).
Proof.
  intros Wc mc i Hi HRO Hlo Hhi HT. apply cmPfB_mb_garr8. intros j Hj.
  rewrite (cmPfB_mb_row_len i Hi) in Hj.
  destruct (HT (CM_T + 296 * Z.of_nat i + Z.of_nat j)) as [Ho He];
    [unfold C_reac_box_catalogue_match.A_CM_TBL, C_reac_box_catalogue_match.CM_ROWS, CM_T; lia|].
  assert (Hr : RLO <= CM_T + 296 * Z.of_nat i + Z.of_nat j < RHI) by lia.
  pose proof (HRO (CM_T + 296 * Z.of_nat i + Z.of_nat j) (or_intror Hr) Ho He) as E.
  rewrite (cmPfB_mb_row_nth i j Hi Hj) in E.
  destruct (nth_error (cm_row i) j) as [b|] eqn:Eb;
    [|apply nth_error_None in Eb; rewrite (cmPfB_mb_row_len i Hi) in Eb; lia].
  unfold lib.Reusable.YG0n.aview in E. cbn [option_map] in E.
  destruct (lib.Reusable.YP09.mbyte rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H Wc) mc)
              (CM_T + 296 * Z.of_nat i + Z.of_nat j)) as [b'|] eqn:Em; cbn [option_map] in E; [|discriminate E].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* ---- frame arithmetic (no frame-route fact) ---- *)

(* the class-2 frame of the journal's end layout is the stretch's fr (the layout keeps ly_F; ctl_fs_geom) *)
Lemma cmPfB_mb_fr : forall nsecs (ly lyc : lib.Reusable.YG0f.alayout) pos,
  lib.Reusable.YG0f.layout_le nsecs ly lyc ->
  lib.Reusable.YG0f.frame_addr lyc 2 pos = fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos.
Proof.
  intros nsecs ly lyc pos Hly. destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  unfold lib.Reusable.YG0f.frame_addr. rewrite EF.
  destruct (lib.B.ProgWorld.ctl_fs_geom (lib.Reusable.YG0f.ly_F ly) 2 pos ltac:(lia)) as (_ & _ & E & _).
  exact (eq_sym E).
Qed.

Lemma cmPfB_mb_sh_in : forall F x, F mod 32 = 0 -> F <= x < F + 256 ->
  0 <= lib.Reusable.YG0f.shadow_addr x - lib.Reusable.YG0f.shadow_addr F < 32.
Proof. intros F x HF Hx. unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. Z.div_mod_to_equations. lia. Qed.

Lemma cmPfB_mb_hull_in : forall F s, F mod 32 = 0 ->
  lib.Reusable.YG0f.shadow_addr (F + 112) / 8 * 8 <= s <
    lib.Reusable.YG0f.shadow_addr (F + 112 + 32 - 1) / 8 * 8 + 8 ->
  0 <= s - lib.Reusable.YG0f.shadow_addr F < 32.
Proof. intros F s HF Hs. unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF in *. Z.div_mod_to_equations. lia. Qed.

Lemma cmPfB_mb_ksh_in : forall F a, F mod 32 = 0 ->
  B.AsanRT.shadow_addr (F + 112) <= a <= B.AsanRT.shadow_addr (F + 112 + 32 - 1) ->
  0 <= a - lib.Reusable.YG0f.shadow_addr F < 32.
Proof.
  intros F a HF Ha. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr,
    lib.Reusable.YG0f.SHADOW_OFF in *. Z.div_mod_to_equations. lia.
Qed.

Lemma cmPfB_mb_sh_eq : forall x, B.AsanRT.shadow_addr x = lib.Reusable.YG0f.shadow_addr x.
Proof. intros x. unfold B.AsanRT.shadow_addr, B.AsanRT.ASAN_K, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. ring. Qed.

(* a byte of the frame's shadow lies off the 32-byte block at F + 112 and above the low memory *)
Lemma cmPfB_mb_sh_apart : forall F a, lib.Reusable.YG0f.in_app F 256 ->
  0 <= a - lib.Reusable.YG0f.shadow_addr F < 32 ->
  ~ (F + 112 <= a < F + 112 + 32) /\ lib.Reusable.YG0f.kLowMemEnd <= a < 2 ^ 64.
Proof.
  intros F a Happ Ha. pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [CR _].
  unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in Happ.
  unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, lib.Reusable.YG0f.kLowMemEnd in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma cmPfB_mb_amem : forall F, lib.Reusable.YG0f.in_app F 256 -> lib.Reusable.YG0d.amem_range (F + 112) 32.
Proof.
  intros F Happ. pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [CR _].
  unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in Happ.
  unfold lib.Reusable.YG0d.amem_range, lib.Reusable.YG0f.kLowMemEnd, lib.Reusable.YG0f.kHighMemBeg,
    lib.Reusable.YG0f.kHighMemEnd. lia.
Qed.

(* ctrl's shadow_ok (signed byte) is the core's saddr_ok (unsigned byte) *)
Lemma cmPfB_mb_saddr : forall x (b : byte), B.AsanRT.shadow_ok x (bv_signed b) -> lib.Reusable.YG0v.saddr_ok x (bv_unsigned b).
Proof.
  intros x b H. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  assert (E : 0 <= bv_signed b -> bv_signed b = bv_unsigned b).
  { intros Hs. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus in *. change (bv_modulus 8) with 256 in *.
    change (256 / 2) with 128 in *. Z.div_mod_to_equations. lia. }
  unfold B.AsanRT.shadow_ok in H. unfold lib.Reusable.YG0v.saddr_ok.
  destruct H as [H|[H1 H2]]; [left | right]; rewrite <- E by lia; lia.
Qed.

Lemma cmPfB_mb_decl_len : forall i, (i < 11)%nat -> length (nth i DECLS []) = 32%nat.
Proof. intros i Hi. do 11 (destruct i as [|i]; [vm_compute; reflexivity|]). lia. Qed.

(* ---- the call: TMB at row i's call configuration (pc 0x865d8, ra 0x8509c, sp = CA Sp), every premise discharged.
   Premise sources:
     J      the journal from the entry (own = [(2, pos)], k = 0) to the call memory mc: the walk's journal at the
            row's call (H1's J2 carried by the stretches before the row);
     HAT    row i's ctrl call facts, LibW cmRBw_AtMB (C_reac_box_catalogue_matchLibW.v:1730) at the pinned frame
            fr := fs_frame (ly_F ly) 2 pos, sp2 := CA Sp, jj := pos, nn := 1 (of these only i < 11 and
            addressable mc (fr + 112) 32 are read);
     HRO    the spec's P2, C_reac_box_catalogue_match.v:87, at the entry memory;
     HC0    the class-0 room, C_reac_box_catalogue_match.v:99;
     HT     the table facts, C_reac_box_catalogue_match.v:94-95;
     HRI    core image fact RELRO_IMG, C_reac_box_catalogue_match.v:45 (the composer: CtrlImg.ctrl_relro_img at
            [RLO, RHI) := pa_relro); it carries HRO along J (in_img of [RLO, RHI));
     HG17, HTRO  FRAME-ROUTE table premises, below.
   Derived here: o's home (tbmb_o_home_frame), ~ in_img o (AR_client_img_law), twr_ok (in_frames arm, AR_frames_law
   presence and ~ aowned, the frame below YM05's alloc_ceiling <= the stack), tsrc_ok (view and shadow from
   AR_frames_law presence, range_addressable from HAT's addressable through B.ProgWorld.aview_vis_mrd), the row's
   garr8 (arodata_okS at mc and CM_TBL_eq), o above the table (B.ProgWorld_Fs.ctl_frame_above_img). ---- *)
Lemma cmPfB_mb_call : forall (W : lib.Reusable.YA0n.world rsegs) (ly : lib.Reusable.YG0f.alayout)
    (S : lib.Reusable.YG00.astate) (memc : word -> option byte) (md : Model)
    (lyc : lib.Reusable.YG0f.alayout) (Sc : lib.Reusable.YG00.astate) (Wc : lib.Reusable.YA0n.world rsegs)
    (mc : word -> option byte) (mdc : Model) (Sp pos : Z)
    (ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mb : word -> option byte) (f len : Z)
    (fb : list byte) (i : nat),
  (* core image fact RELRO_IMG (C_reac_box_catalogue_match.v:45; composer: CtrlImg.ctrl_relro_img) *)
  (forall a, RLO <= a < RHI -> lib.Reusable.YG0d.in_img rsegs a) ->
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp []
    ly S W memc md [(2, pos)] lyc Sc Wc mc mdc 0 ->
  C_reac_box_catalogue_matchLibW.cmRBw_AtMB ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp
    (lib.Reusable.YG0f.ly_F ly) fb i (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos) (CA Sp) pos 1 mc ->
  lib.Reusable.YE01.arodata_okS rsegs B RLO RHI (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc) ->
  lib.Reusable.YG01.count_cid 0 (lib.Reusable.YG01.frames S) < lib.Reusable.YG00.fs_frames 0 ->
  (forall a, C_reac_box_catalogue_match.A_CM_TBL <= a <
             C_reac_box_catalogue_match.A_CM_TBL + C_reac_box_catalogue_match.CM_ROWS ->
     ~ Exists (lib.Reusable.YG0n.in_zr a) (lib.Reusable.YG0f.as_owned_static B) /\
     ~ (lib.Reusable.YG0f.as_errno B <= a < lib.Reusable.YG0f.as_errno B + 4)) ->
  (* FRAME-ROUTE (table premise HG17): the image's registered globals list holds BOX_CATALOGUE's data range
     [CM_T, CM_T + 3256) (C_reac_box_catalogue_match.v:120 plan, HG17 : In (A_CM_TBL, CM_ROWS) G) *)
  (exists q sz, In (q, sz) GLOBS /\ q <= CM_T /\ CM_T + 3256 <= q + sz) ->
  (* FRAME-ROUTE (table premise HTRO): the B PA instance's pa_relro covers the table
     (C_reac_box_catalogue_match.v:50-51, the composer: arithmetic at [0x9f168, 0xa15e8)) *)
  RLO <= CM_T /\ CM_T + 3256 <= RHI ->
  forall regsM : bvmap 5 word,
  lib.Reusable.YK11.getr regsM 1 = Z_to_bv 64 0x8509c ->
  lib.Reusable.YG0d.spZ regsM = CA Sp ->
  lib.Reusable.YK11.getr regsM 3 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_gp B) ->
  lib.Reusable.YK11.getr regsM 4 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B) ->
  lib.Reusable.YK11.getr regsM 10 = lib.Reusable.YG0d.w64 (CM_T + 296 * Z.of_nat i) ->
  lib.Reusable.YK11.getr regsM 11 = lib.Reusable.YG0d.w64 0 ->
  lib.Reusable.YK11.getr regsM 12 = lib.Reusable.YG0d.w64 (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos + 112) ->
  lib.Reusable.YA0n.SRr rsegs Wc
    (lib.Reusable.YG0d.cfg_at rsegs C_reac_box_model_block.REAC_BOX_MODEL_BLOCK regsM mc mdc)
    (C_reac_box_model_block.treac_box_model_block_post B C_reac_box_catalogue_match.CM_STK Sp [] ly S W memc md
       [(2, pos)] lyc Sc Wc mc 0 regsM (CM_T + 296 * Z.of_nat i) 0
       (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos + 112) (cm_row i) []).
Proof.
  intros W ly S memc md lyc Sc Wc mc mdc Sp pos ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len fb i
    HRI HJ HAT HRO HC0 HT HG17 [HTlo HThi] regsM Hra Hsp Hgp Htp H10 H11 H12.
  destruct HAT as (Hi & _ & ADo).
  pose proof HJ as (HAR & Hly & _ & _ & _ & Hfr & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (S16 & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof (cmPfB_mb_fr _ ly lyc pos Hly) as EFr.
  set (fr := fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos) in *.
  assert (Hin : In (2, pos) (lib.Reusable.YG01.frames Sc)) by (rewrite Hfr; left; reflexivity).
  destruct (lib.Reusable.YCbq.frames_bounds rsegs B LAWS lyc Sc Wc mc mdc 2 pos HAR Hin) as (F0 & Fc & Fapp).
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS lyc Sc Wc mc mdc 2 pos HAR Hin) as (F32 & _ & Fby & Fsh).
  pose proof (lib.B.ProgWorld_Fs.ctl_frame_above_img B lyc Sc Wc mc mdc 2 pos HAR Hin) as Fab.
  change (lib.Reusable.YG00.fs_frame_bytes 2 / 8) with 32 in Fsh.
  change (lib.Reusable.YG00.fs_frame_bytes 2) with 256 in Fc, Fapp, Fby.
  rewrite EFr in F0, Fc, Fapp, F32, Fby, Fsh, Fab.
  pose proof lib.Reusable.YCbq.asan_consts as (C1 & _).
  destruct (C_reac_box_catalogue_matchPf.cmPf_CA Sp S16) as (CAb & _).
  unfold C_reac_box_catalogue_match.CM_STK in Hslo.
  pose proof (cmPfB_mb_aro _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRI HJ HRO) as HROc.
  (* the view facts at mc over o's block, stated over rsegs *)
  assert (V1 : forall a, fr + 112 <= a < fr + 112 + 32 ->
                 lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H Wc) mc a <> None).
  { intros a Ha. destruct (cmPfB_mb_view_present _ _ a (proj1 (Fby a ltac:(lia)))) as (b & _ & Hv).
    rewrite Hv. discriminate. }
  assert (V2 : lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H Wc) mc)
                 lib.Reusable.YG0f.SHADOW_OFF (fr + 112) 32).
  { intros x Hx. destruct ADo as (_ & _ & _ & ADx).
    destruct (ADx (x - (fr + 112)) ltac:(lia)) as (_ & b & Hb & Hok).
    replace (fr + 112 + (x - (fr + 112))) with x in Hb, Hok by ring.
    pose proof (cmPfB_mb_sh_in fr x F32 ltac:(lia)) as Hsi.
    destruct (Fsh (lib.Reusable.YG0f.shadow_addr x - lib.Reusable.YG0f.shadow_addr fr) Hsi) as (Hp & _).
    replace (lib.Reusable.YG0f.shadow_addr fr + (lib.Reusable.YG0f.shadow_addr x - lib.Reusable.YG0f.shadow_addr fr))
      with (lib.Reusable.YG0f.shadow_addr x) in Hp by ring.
    exists (bv_unsigned b). split; [|exact (cmPfB_mb_saddr x b Hok)].
    change (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF x) with (lib.Reusable.YG0f.shadow_addr x).
    etransitivity; [exact (lib.B.ProgWorld.aview_vis_mrd Wc mc _ (proj1 Hp))|].
    rewrite cmPfB_mb_sh_eq in Hb. unfold lib.Lib.Mem.wa in Hb. rewrite Hb. reflexivity. }
  assert (V3 : lib.Reusable.YG0d.shadow_hull_vis (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H Wc) mc)
                 (fr + 112) 32).
  { intros s Hs. pose proof (cmPfB_mb_hull_in fr s F32 Hs) as Hsi.
    destruct (Fsh (s - lib.Reusable.YG0f.shadow_addr fr) Hsi) as (Hp & _).
    replace (lib.Reusable.YG0f.shadow_addr fr + (s - lib.Reusable.YG0f.shadow_addr fr)) with s in Hp by ring.
    destruct (cmPfB_mb_view_present _ _ s Hp) as (b & _ & Hv). rewrite Hv. discriminate. }
  apply (TMB C_reac_box_catalogue_match.CM_STK Sp [] ly S W memc md [(2, pos)] lyc Sc Wc mc mdc 0 regsM
           (CM_T + 296 * Z.of_nat i) 0 (fr + 112) (cm_row i) [] HJ HROc).
  - (* ret_ok *) rewrite Hra. unfold lib.Reusable.YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
  - (* 4096 <= ra *) unfold lib.Reusable.YG0d.raZ. rewrite Hra, lib.B.ProgWorld_Fs.pw_u64 by lia. lia.
  - exact Hgp.
  - exact Htp.
  - exact H10.
  - exact H11.
  - exact H12.
  - unfold CM_T. lia.
  - lia.
  - lia.
  - rewrite Hsp. unfold CA. Z.div_mod_to_equations. lia.
  - rewrite Hsp. unfold C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK, C_reac_box_catalogue_match.CM_STK. lia.
  - rewrite Hsp. lia.
  - (* the class-0 room at the call: frames Sc = (2, pos) :: frames S *)
    rewrite Hfr. cbn [app lib.Reusable.YG01.count_cid Z.eqb]. lia.
  - (* the row *)
    intros _. split; [unfold CM_T; Z.div_mod_to_equations; lia|].
    split; [exact (cmPfB_mb_row_len i Hi)|].
    split; [exact (cmPfB_mb_row_garr8 Wc mc i Hi HROc HTlo HThi HT)|].
    split; [destruct HG17 as (q & sz & Hq & Hq1 & Hq2); exists q, sz; split; [exact Hq | lia]|].
    split; [unfold CtrlRo.IMG_LO, CM_T; lia|].
    split; [unfold CtrlRo.IMG_HI, CM_T; lia|].
    split.
    + intros x Hx. split; [right; lia|]. apply HT.
      unfold C_reac_box_catalogue_match.A_CM_TBL, C_reac_box_catalogue_match.CM_ROWS. unfold CM_T in Hx |- *. lia.
    + right. right. unfold CM_T. lia.
  - (* the name: b = 0 *)
    intros _ [E | E]; discriminate E.
  - (* o = fr + 112 *)
    intros _. split; [|split; [|split; [|split]]].
    + rewrite <- EFr. apply C_reac_box_model_block.tbmb_o_home_frame; [exact Hin | lia | lia |].
      change (lib.Reusable.YG00.fs_frame_bytes 2) with 256. lia.
    + intros x Hx.
      assert (Hx' : exists cid pos', In (cid, pos') (lib.Reusable.YG01.frames Sc) /\
                      lib.Reusable.YG0f.frame_addr lyc cid pos' <= x <
                      lib.Reusable.YG0f.frame_addr lyc cid pos' + lib.Reusable.YG00.fs_frame_bytes cid).
      { exists 2, pos. split; [exact Hin|]. rewrite EFr. change (lib.Reusable.YG00.fs_frame_bytes 2) with 256. lia. }
      exact (proj2 (lib.Reusable.YG0d.al_client_img _ _ LAWS lyc Sc Wc mc mdc x HAR (or_intror (or_introl Hx')))).
    + intros a Ha. split; [|split; [|split]].
      * right. right. right. exists 2, pos. split; [left; reflexivity|]. left.
        unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite EFr.
        change (lib.Reusable.YG00.fs_frame_bytes 2) with 256. lia.
      * exact (proj1 (Fby a ltac:(lia))).
      * exact (proj2 (Fby a ltac:(lia))).
      * rewrite Hsp. unfold lib.Reusable.YG0d.ESTACK. lia.
    + split; [|split; [exact V2 | split; [exact V3 | split; [exact (cmPfB_mb_amem fr Fapp) | lia]]]].
      intros a Ha. split; [exact (V1 a Ha) | rewrite Hsp; unfold lib.Reusable.YG0d.ESTACK; lia].
    + right. rewrite Hsp. unfold C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK. lia.
Qed.

(* ---- the return: from treac_box_model_block_post at row i's call (p = CM_T + 296 i <> 0, o = fr + 112 <> 0, so
   its second branch), the return configuration at 0x8509c, the journal (own = [(2, pos)], k = 0 + EV_BMB = 0), the
   frames and blocks, the callee-saved registers (aregs_preserved spelled out), a0 = rc (cm_row i) 0 = 1 (cm_rc), and
   the return-memory premises of C_reac_box_catalogue_matchLibW.cmRBw_post_mb at mb := mem4, m1 := mc,
   sp2 := CA Sp:
     stk mem4 (CA Sp - 4272) (CA Sp)    <- tcj_kept's window presence (CtrlCallerJ.v:54), cmPf_stk_of_apresent;
     bytes_at mem4 (fr + 112) (nth i DECLS [])
                                        <- the post's garr8 of synth (cm_row i) 0 [] = nth i DECLS [] (cm_rc),
                                           B.ProgWorld.ctl_out_bytes (off the image: AR_client_img_law);
     cmRB_kept mc mem4 (cmRB_callee_kept Sp fr (CA Sp) (CA Sp - 4272) 112 32)
                                        <- tcj_kept (its alloc_ceiling is YM05's, CtrlCallerJ.v:44): the window outside
                                           [CA Sp - 4272, CA Sp) by the high-memory clause (the window lies above YM05's
                                           alloc_ceiling, astk_ok), the flag word [fr + 248, fr + 256) and the buffer's
                                           shadow bytes by the frame clause (the frame (2, pos) of Sc and its shadow),
                                           none of them in E = [fr + 112, fr + 144); each view equality made raw by
                                           cmPfB_mb_raw_of_view (present at mc: J's window presence / AR_frames_law;
                                           off the image: segs_low / AR_client_img_law). ---- *)
Lemma cmPfB_mb_ret : forall (W : lib.Reusable.YA0n.world rsegs) (ly : lib.Reusable.YG0f.alayout)
    (S : lib.Reusable.YG00.astate) (memc : word -> option byte) (md : Model)
    (lyc : lib.Reusable.YG0f.alayout) (Sc : lib.Reusable.YG00.astate) (Wc : lib.Reusable.YA0n.world rsegs)
    (mc : word -> option byte) (mdc : Model) (Sp pos : Z) (i : nat) (regsM : bvmap 5 word)
    (W2 : lib.Reusable.YA0n.world rsegs) (c2 : config),
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp []
    ly S W memc md [(2, pos)] lyc Sc Wc mc mdc 0 ->
  (i < 11)%nat ->
  lib.Reusable.YK11.getr regsM 1 = Z_to_bv 64 0x8509c ->
  lib.Reusable.YG0d.spZ regsM = CA Sp ->
  C_reac_box_model_block.treac_box_model_block_post B C_reac_box_catalogue_match.CM_STK Sp [] ly S W memc md
    [(2, pos)] lyc Sc Wc mc 0 regsM (CM_T + 296 * Z.of_nat i) 0
    (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos + 112) (cm_row i) [] W2 c2 ->
  exists (ly4 : lib.Reusable.YG0f.alayout) (S4 : lib.Reusable.YG00.astate) (regs4 : bvmap 5 word)
         (mem4 : word -> option byte) (md4 : Model),
    c2 = mkCfg (lib.Reusable.YK11.mkst regs4 (Z_to_bv 64 0x8509c) mem4 (lib.Lib.PropExec.seg_rom rsegs)) md4 /\
    lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp []
      ly S W memc md [(2, pos)] ly4 S4 W2 mem4 md4 0 /\
    lib.Reusable.YG01.frames S4 = lib.Reusable.YG01.frames Sc /\
    lib.Reusable.YG0d.ablocks B ly4 S4 = lib.Reusable.YG0d.ablocks B lyc Sc /\
    lib.Reusable.YK11.getr regs4 2 = lib.Reusable.YK11.getr regsM 2 /\
    lib.Reusable.YK11.getr regs4 3 = lib.Reusable.YK11.getr regsM 3 /\
    lib.Reusable.YK11.getr regs4 4 = lib.Reusable.YK11.getr regsM 4 /\
    lib.Reusable.YK11.getr regs4 8 = lib.Reusable.YK11.getr regsM 8 /\
    lib.Reusable.YK11.getr regs4 9 = lib.Reusable.YK11.getr regsM 9 /\
    lib.Reusable.YK11.getr regs4 18 = lib.Reusable.YK11.getr regsM 18 /\
    lib.Reusable.YK11.getr regs4 19 = lib.Reusable.YK11.getr regsM 19 /\
    lib.Reusable.YK11.getr regs4 20 = lib.Reusable.YK11.getr regsM 20 /\
    lib.Reusable.YK11.getr regs4 21 = lib.Reusable.YK11.getr regsM 21 /\
    lib.Reusable.YK11.getr regs4 22 = lib.Reusable.YK11.getr regsM 22 /\
    lib.Reusable.YK11.getr regs4 23 = lib.Reusable.YK11.getr regsM 23 /\
    lib.Reusable.YK11.getr regs4 24 = lib.Reusable.YK11.getr regsM 24 /\
    lib.Reusable.YK11.getr regs4 25 = lib.Reusable.YK11.getr regsM 25 /\
    lib.Reusable.YK11.getr regs4 26 = lib.Reusable.YK11.getr regsM 26 /\
    lib.Reusable.YK11.getr regs4 27 = lib.Reusable.YK11.getr regsM 27 /\
    lib.Reusable.YK11.getr regs4 10 = Z_to_bv 64 1 /\
    lib.Lib.Frame.stk rsegs mem4 (CA Sp - 4272) (CA Sp) /\
    lib.Lib.Mem.bytes_at rsegs mem4 (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos + 112) (nth i DECLS []) /\
    C_reac_box_catalogue_matchLib.cmRB_kept mc mem4
      (C_reac_box_catalogue_matchLib.cmRB_callee_kept Sp (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos) (CA Sp)
         (CA Sp - 4272) 112 32).
Proof.
  intros W ly S memc md lyc Sc Wc mc mdc Sp pos i regsM W2 c2 HJ Hi Hra Hsp HP.
  pose proof HJ as (HAR & Hly & _ & _ & _ & Hfr & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hstk as (S16 & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof (cmPfB_mb_fr _ ly lyc pos Hly) as EFr.
  set (fr := fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos) in *.
  assert (Hin : In (2, pos) (lib.Reusable.YG01.frames Sc)) by (rewrite Hfr; left; reflexivity).
  destruct (lib.Reusable.YCbq.frames_bounds rsegs B LAWS lyc Sc Wc mc mdc 2 pos HAR Hin) as (F0 & Fc & Fapp).
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS lyc Sc Wc mc mdc 2 pos HAR Hin) as (F32 & _ & Fby & Fsh).
  change (lib.Reusable.YG00.fs_frame_bytes 2 / 8) with 32 in Fsh.
  change (lib.Reusable.YG00.fs_frame_bytes 2) with 256 in Fc, Fapp, Fby.
  rewrite EFr in F0, Fc, Fapp, F32, Fby, Fsh.
  pose proof lib.Reusable.YCbq.asan_consts as (C1 & _).
  destruct (C_reac_box_catalogue_matchPf.cmPf_CA Sp S16) as (CAb & _).
  unfold C_reac_box_catalogue_match.CM_STK in Hslo, Hpres.
  (* the frame's bytes are off the image *)
  assert (FNI : forall x, fr <= x < fr + 256 -> ~ lib.Reusable.YG0d.in_img rsegs x).
  { intros x Hx.
    assert (Hx' : exists cid pos', In (cid, pos') (lib.Reusable.YG01.frames Sc) /\
                    lib.Reusable.YG0f.frame_addr lyc cid pos' <= x <
                    lib.Reusable.YG0f.frame_addr lyc cid pos' + lib.Reusable.YG00.fs_frame_bytes cid).
    { exists 2, pos. split; [exact Hin|]. rewrite EFr. change (lib.Reusable.YG00.fs_frame_bytes 2) with 256. lia. }
    exact (proj2 (lib.Reusable.YG0d.al_client_img _ _ LAWS lyc Sc Wc mc mdc x HAR (or_intror (or_introl Hx')))). }
  destruct HP as (ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ2 & HPR & Hfr2 & Hab2 & HB).
  replace ((CM_T + 296 * Z.of_nat i =? 0) || (fr + 112 =? 0)) with false in HB
    by (symmetry; apply Bool.orb_false_iff; split; apply Z.eqb_neq; unfold CM_T; lia).
  destruct HB as (H10 & Hg & HK).
  destruct (cm_rc i [] Hi) as (RC & SY).
  rewrite RC in H10. unfold C_reac_box_model_block.bmb_z in Hg. rewrite SY in Hg.
  rewrite Hra in Ec.
  destruct HK as (Khi & _ & _ & Kfr & _ & Kwin).
  rewrite Hsp in Khi, Kwin.
  unfold C_reac_box_model_block.REAC_BOX_MODEL_BLOCK_STK in Khi, Kwin.
  exists ly2, S2, regs2, mem2, md2.
  split; [exact Ec|]. split; [exact HJ2|]. split; [exact Hfr2|]. split; [exact Hab2|].
  split; [exact (HPR 2 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HPR 3 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HPR 4 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HPR 8 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HPR 9 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HPR 18 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HPR 19 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HPR 20 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HPR 21 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HPR 22 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HPR 23 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HPR 24 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HPR 25 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HPR 26 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HPR 27 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact H10|].
  split.
  { apply (C_reac_box_catalogue_matchPf.cmPf_stk_of_apresent (lib.Reusable.YA0n.w_H W2)); [lia | lia |].
    intros a Ha. exact (Kwin a Ha). }
  split.
  { pose proof (cmPfB_mb_decl_len i Hi) as Hlen.
    refine (proj1 (lib.B.ProgWorld.ctl_out_bytes W2 mem2 (fr + 112) (nth i DECLS []) ltac:(lia)
                     ltac:(rewrite Hlen; lia) _ Hg)).
    intros j Hj. rewrite Hlen in Hj. apply FNI. lia. }
  intros a Ha. unfold C_reac_box_catalogue_matchLib.cmRB_callee_kept in Ha.
  destruct Ha as [(Hw & Hnw) | [Hfl | Hsh]].
  - (* the window outside the callee's: high memory, above YM05's alloc_ceiling *)
    apply (cmPfB_mb_raw_of_view (lib.Reusable.YA0n.w_H Wc) (lib.Reusable.YA0n.w_H W2) mc mem2 a).
    + lia.
    + intros Himg. pose proof (segs_low a Himg) as L. unfold lib.Reusable.YG0f.kLowMemEnd in L. lia.
    + apply Hpres. lia.
    + apply Khi; [lia | lia | unfold C_reac_box_model_block.treac_box_model_block_out; lia].
  - (* the flag word: a byte of the frame (2, pos) of Sc *)
    apply (cmPfB_mb_raw_of_view (lib.Reusable.YA0n.w_H Wc) (lib.Reusable.YA0n.w_H W2) mc mem2 a).
    + lia.
    + apply FNI. lia.
    + exact (proj1 (Fby a ltac:(lia))).
    + apply (Kfr 2 pos a Hin); [|unfold C_reac_box_model_block.treac_box_model_block_out; lia].
      left. unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite EFr.
      change (lib.Reusable.YG00.fs_frame_bytes 2) with 256. lia.
  - (* the buffer's shadow bytes: bytes of the frame's shadow *)
    pose proof (cmPfB_mb_ksh_in fr a F32 Hsh) as Hsi.
    destruct (cmPfB_mb_sh_apart fr a Fapp Hsi) as (Hno & Hlow).
    apply (cmPfB_mb_raw_of_view (lib.Reusable.YA0n.w_H Wc) (lib.Reusable.YA0n.w_H W2) mc mem2 a).
    + unfold lib.Reusable.YG0f.kLowMemEnd in Hlow. lia.
    + intros Himg. pose proof (segs_low a Himg) as L. lia.
    + destruct (Fsh (a - lib.Reusable.YG0f.shadow_addr fr) Hsi) as (Hp & _).
      replace (lib.Reusable.YG0f.shadow_addr fr + (a - lib.Reusable.YG0f.shadow_addr fr)) with a in Hp by ring.
      exact Hp.
    + apply (Kfr 2 pos a Hin); [|unfold C_reac_box_model_block.treac_box_model_block_out; exact Hno].
      right. unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite EFr.
      change (lib.Reusable.YG00.fs_frame_bytes 2 / 8) with 32. lia.
Qed.



(* A live block of at least 50 bytes lies below the machine stack and in application memory (AR_blocks_law). *)
Lemma cmPfB_me_blk : forall (ly' : lib.Reusable.YG0f.alayout) (S' : lib.Reusable.YG00.astate)
    (W' : lib.Reusable.YA0n.world rsegs) (m : word -> option byte) (md' : Model) (Sp f n : Z),
  lib.Reusable.YG0n.AR rsegs B ly' S' W' m md' ->
  lib.Reusable.YCbq.astk_ok C_reac_box_catalogue_match.CM_STK ly' Sp ->
  In (f, n) (lib.Reusable.YG0d.ablocks B ly' S') -> 50 <= lib.Reusable.YG00.req_size n ->
  (0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= Sp - 9136 \/ Sp <= f)) /\ app_mem (f + 50).
Proof.
  intros ly' S' W' m md' Sp f n HAR Hstk Hin Hn.
  destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly' S' W' m md' f n HAR Hin) as (_ & H4096 & Hceil & Happ & _).
  pose proof Hstk as (_ & _ & Hc & Hslo & _).
  pose proof lib.Reusable.YCbq.asan_consts as (C1 & _).
  unfold C_reac_box_catalogue_match.CM_STK in Hslo.
  unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.ASAN_CEIL, lib.Reusable.YG0f.kLowShadowBeg,
    lib.Reusable.YG0f.kHighMemBeg in Happ.
  split; [lia|].
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. lia.
Qed.

(* The canonical register map: a world state at mkst R pc m ro is the footprint runs' MS form over the explicit
   mkR of R's registers (YA0nR.SRr_xregs_eqv, Regs6ss.mkR_of_eqv), as cmPf_to_sm2_ret moves the entry's map. *)
Lemma cmPfB_me_canon : forall (W : lib.Reusable.YA0n.world rsegs) (R : bvmap 5 word) (pc : word)
    (m ro : word -> option byte) (md : Model) (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
  lib.Reusable.YA0n.SRr rsegs W
    (mkCfg (lib.Lib.MState.MS
              (lib.Lib.Frame.mkR (lib.Reusable.YK11.getr R 1) (lib.Reusable.YK11.getr R 2) (lib.Reusable.YK11.getr R 3)
                 (lib.Reusable.YK11.getr R 4) (lib.Reusable.YK11.getr R 5) (lib.Reusable.YK11.getr R 6)
                 (lib.Reusable.YK11.getr R 7) (lib.Reusable.YK11.getr R 8) (lib.Reusable.YK11.getr R 9)
                 (lib.Reusable.YK11.getr R 10) (lib.Reusable.YK11.getr R 11) (lib.Reusable.YK11.getr R 12)
                 (lib.Reusable.YK11.getr R 13) (lib.Reusable.YK11.getr R 14) (lib.Reusable.YK11.getr R 15)
                 (lib.Reusable.YK11.getr R 16) (lib.Reusable.YK11.getr R 17) (lib.Reusable.YK11.getr R 18)
                 (lib.Reusable.YK11.getr R 19) (lib.Reusable.YK11.getr R 20) (lib.Reusable.YK11.getr R 21)
                 (lib.Reusable.YK11.getr R 22) (lib.Reusable.YK11.getr R 23) (lib.Reusable.YK11.getr R 24)
                 (lib.Reusable.YK11.getr R 25) (lib.Reusable.YK11.getr R 26) (lib.Reusable.YK11.getr R 27)
                 (lib.Reusable.YK11.getr R 28) (lib.Reusable.YK11.getr R 29) (lib.Reusable.YK11.getr R 30)
                 (lib.Reusable.YK11.getr R 31))
              lib.Reusable.YK11.fp_regs pc lib.Reusable.YK11.fp_csr None m ro) md) Q ->
  lib.Reusable.YA0n.SRr rsegs W (mkCfg (lib.Reusable.YK11.mkst R pc m ro) md) Q.
Proof.
  intros W R pc m ro md Q H.
  change (lib.Reusable.YK11.mkst R pc m ro) with (lib.Lib.MState.MS R lib.Reusable.YK11.fp_regs pc lib.Reusable.YK11.fp_csr None m ro).
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv rsegs W (Regs6ss.mkR_of R) R);
    [| exact (Regs6ss.xregs_eqv_sym _ _ (Regs6ss.mkR_of_eqv R))].
  exact H.
Qed.


Lemma cmPfB_me_exit : forall (W : lib.Reusable.YA0n.world rsegs) (ly : lib.Reusable.YG0f.alayout)
    (S : lib.Reusable.YG00.astate) (regs : bvmap 5 word) (memc : word -> option byte) (md : Model) (f len : Z)
    (fb : list byte) (pos : Z) (lyc : lib.Reusable.YG0f.alayout) (Sc : lib.Reusable.YG00.astate)
    (Wc : lib.Reusable.YA0n.world rsegs) (mc mb : word -> option byte) (mdc : Model)
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
  cmPfB_base_all ly S W regs memc md f len fb pos ->
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK (lib.Reusable.YG0d.spZ regs) []
    ly S W memc md [(2, pos)] lyc Sc Wc mc mdc 0 ->
  lib.Reusable.YG01.frames Sc = (2, pos) :: lib.Reusable.YG01.frames S ->
  ~ In (2, pos) (lib.Reusable.YG01.frames S) ->
  Permutation (lib.Reusable.YG0d.ablocks B lyc Sc) (lib.Reusable.YG0d.ablocks B ly S) ->
  0 <= pos < fs_M 2 ->
  lib.Reusable.YG0f.frame_addr ly 2 pos = fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos ->
  lib.Reusable.YG0f.flag_addr ly 2 pos = fs_flag (lib.Reusable.YG0f.ly_F ly) 2 pos ->
  C_reac_box_catalogue_matchLibW.cmRBw_J (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 4)
    (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9) (lib.Reusable.YK11.getr regs 18)
    (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21)
    (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24)
    (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27)
    mb f len (lib.Reusable.YG0d.spZ regs) (lib.Reusable.YG0f.ly_F ly) fb
    (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos) (CA (lib.Reusable.YG0d.spZ regs)) pos 1 mc ->
  C_reac_box_catalogue_matchPfI.cmPf_exit_at B W ly S regs memc md f len fb Wc
    (mkCfg (lib.Lib.MState.MS
              (lib.Lib.Frame.mkR x1 (Z_to_bv 64 (CA (lib.Reusable.YG0d.spZ regs)))
                 (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4) u0 u1 u2
                 (Z_to_bv 64 (lib.Reusable.YG0d.spZ regs)) (Z_to_bv 64 (CA (lib.Reusable.YG0d.spZ regs)))
                 y0 y1 y2 y3 y4 y5 y6 y7
                 (Z_to_bv 64 (if 1 =? 0 then 0 else fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos)) z3
                 (Z_to_bv 64 (want CM_T len fb)) z5 z6
                 (Z_to_bv 64 (shadow_addr (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos)))
                 (Z_to_bv 64 (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos)) z9 z10 z11 u3 u4 u5 u6)
              lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x850fc) lib.Reusable.YK11.fp_csr None mc
              (lib.Lib.PropExec.seg_rom rsegs)) mdc).
Proof.
  intros W ly S regs memc md f len fb pos lyc Sc Wc mc mb mdc
    x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6
    HBASE HJ Hfr Hnin Hperm Hpos Hfa Hfl HJw.
  exists lyc, Sc, mc, mdc, pos, x1, u0, u1, u2, y0, y1, y2, y3, y4, y5, y6, y7, z3, z5, z6, z9, z10, z11,
    u3, u4, u5, u6.
  pose proof HJ as (_ & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
  destruct HJw as (FK & _ & _ & _ & _ & _ & _ & STW & _ & SAV & FLG).
  split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfr|]. split; [exact Hnin|]. split; [exact Hperm|].
  split; [exact EF|]. split; [exact Hpos|]. split; [exact Hfa|]. split; [exact Hfl|].
  split; [exact (HBASE lyc Sc Wc mc mdc 0 HJ)|]. split; [exact STW|].
  exact (conj FK (conj SAV FLG)).
Qed.


(* ---- The entry's facts the middle piece reads (the spec's premises, C_reac_box_catalogue_match.v:81-100, and
   the frame-route ones), in one bundle. ---- *)
Definition cmPfB_ctx (W : lib.Reusable.YA0n.world rsegs) (ly : lib.Reusable.YG0f.alayout)
    (S : lib.Reusable.YG00.astate) (regs : bvmap 5 word) (memc : word -> option byte) (md : Model) (f len : Z)
    (fb : list byte) (pos : Z) : Prop :=
  lib.Reusable.YK11.getr regs 3 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_gp B) /\
  lib.Reusable.YK11.getr regs 4 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B) /\
  0 <= f < 2 ^ 64 /\ 0 <= len < 2 ^ 64 /\ length fb = 50%nat /\
  (50 <= len -> exists n, In (f, n) (lib.Reusable.YG0d.ablocks B ly S) /\ 50 <= lib.Reusable.YG00.req_size n) /\
  (50 <= len -> lib.Reusable.YI00.garr8 rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) memc) f
                  (map (fun b : byte => bv_unsigned b) fb)) /\
  lib.Reusable.YE01.arodata_okS rsegs B RLO RHI (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc) /\
  (forall a, C_reac_box_catalogue_match.A_CM_TBL <= a < C_reac_box_catalogue_match.A_CM_TBL + C_reac_box_catalogue_match.CM_ROWS ->
     ~ Exists (lib.Reusable.YG0n.in_zr a) (lib.Reusable.YG0f.as_owned_static B) /\
     ~ (lib.Reusable.YG0f.as_errno B <= a < lib.Reusable.YG0f.as_errno B + 4)) /\
  lib.Reusable.YG01.count_cid 1 (lib.Reusable.YG01.frames S) < lib.Reusable.YG00.fs_frames 1 /\
  lib.Reusable.YG01.count_cid 0 (lib.Reusable.YG01.frames S) < lib.Reusable.YG00.fs_frames 0 /\
  (* FRAME-ROUTE *)
  cmPfB_base_all ly S W regs memc md f len fb pos /\
  (exists q sz, In (q, sz) GLOBS /\ q <= CM_T /\ CM_T + 3256 <= q + sz) /\
  RLO <= CM_T /\ CM_T + 3256 <= RHI /\
  (* the spec file's Section hypothesis RELRO_IMG (C_reac_box_catalogue_match.v:45), the composer's *)
  (forall a, RLO <= a < RHI -> lib.Reusable.YG0d.in_img rsegs a).

(* ---- S-B LIFTED: from the class-2 return (pc 0x84eb4, H1's cmPf_sm2_ret) through the re-based stretch 2
   (C_reac_box_catalogue_matchLibW.cmRBw_post_sm2_side at base m2, call memory m1, frame j := pos) to the exit (into
   cmPf_exit_at) or to the reac_ctrl_parse call (continuation Kp), with the journal J3 across the stretch
   (cmPfB_jr_journal_pin: writes = window + the class-2 frame + its shadow). ---- *)
Lemma cmPfB_SB : forall (W : lib.Reusable.YA0n.world rsegs) (ly : lib.Reusable.YG0f.alayout)
    (S : lib.Reusable.YG00.astate) (regs : bvmap 5 word) (memc : word -> option byte) (md : Model) (f len : Z)
    (fb : list byte) (m1 : word -> option byte) (md1 : Model) (regsT : bvmap 5 word) (S2 : lib.Reusable.YG00.astate)
    (regs2 : bvmap 5 word) (m2 : word -> option byte) (md2 : Model) (pos : Z)
    (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
  cmPfB_ctx W ly S regs memc md f len fb pos ->
  C_reac_box_catalogue_matchPf.cmPf_sm2_ret B W ly S regs memc md f len m1 md1 regsT S2 regs2 m2 md2 pos ->
  (forall (W' : lib.Reusable.YA0n.world rsegs) (c : config),
     C_reac_box_catalogue_matchPfI.cmPf_exit_at B W ly S regs memc md f len fb W' c ->
     lib.Reusable.YA0n.SRr rsegs W' c Q) ->
  (forall (ms' : machine_state) (md' : Model),
     C_reac_box_catalogue_matchLibW.cmRBw_parse_at (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 3)
       (lib.Reusable.YK11.getr regs 4) (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9)
       (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20)
       (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23)
       (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26)
       (lib.Reusable.YK11.getr regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr m2 f len
       (lib.Reusable.YG0d.spZ regs) (lib.Reusable.YG0f.ly_F ly) fb (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos)
       (CA (lib.Reusable.YG0d.spZ regs)) pos 1 ms' ->
     lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK (lib.Reusable.YG0d.spZ regs) []
       ly S W memc md [(2, pos)] ly S2 W (ms_mem ms') md' 0 ->
     lib.Reusable.YA0n.SRr rsegs W (mkCfg ms' md') Q) ->
  lib.Reusable.YA0n.SRr rsegs W
    (mkCfg (lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 544436) m2 (lib.Lib.PropExec.seg_rom rsegs)) md2) Q.
Proof.
  intros W ly S regs memc md f len fb m1 md1 regsT S2 regs2 m2 md2 pos Q Hctx Hret Kx Kp.
  pose proof (cmPfB_sb_in W ly S regs memc md f len m1 md1 regsT S2 regs2 m2 md2 pos Hret)
    as (Hpos & Hfa & Hfl & H10 & HFs2 & STlo & STW2 & ST1 & HKP & S16 & HK & RS & HHM & HAE).
  destruct Hret as (_ & SV1 & _ & _ & _ & HJ2 & Hfr & Hnin & Hab & _ & _ & _ & _ & _ & _ & R2 & R3 & R4 & R8 & R9 &
                    R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & _).
  destruct Hctx as (Hgp & Htp & Rf & Rlen & Hfb & Hblk & Hga & Hro & Htbl & Hc1 & Hc0 & HBASE & HG17 & HTRO).
  assert (Hblk2 : 50 <= len -> exists n, In (f, n) (lib.Reusable.YG0d.ablocks B ly S2) /\
                                         50 <= lib.Reusable.YG00.req_size n) by (rewrite Hab; exact Hblk).
  pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk2 & _).
  assert (HFA : (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\
                  (f + 50 <= lib.Reusable.YG0d.spZ regs - 9136 \/ lib.Reusable.YG0d.spZ regs <= f)) /\
                (50 <= len -> app_mem (f + 50))).
  { split; intros L; destruct (Hblk2 L) as (n & Hin & Hn);
      destruct (cmPfB_me_blk ly S2 W m2 md2 (lib.Reusable.YG0d.spZ regs) f n HAR2 Hstk2 Hin Hn) as [A1 A2];
      assumption. }
  destruct HFA as (HFp & AFp).
  destruct (cmPfB_jr_rng_pin (lib.Reusable.YG0d.spZ regs) ly S W memc md [(2, pos)] ly S2 W m2 md2 0 f len HJ2 Hblk2)
    as (RWIN & RWSH & RFD & RFW & RFPW & _ & _ & _).
  pose proof (HBASE ly S2 W m2 md2 0 HJ2) as HB.
  apply cmPfB_me_canon.
  rewrite R2, R3, R4, R8, R9, H10, R18, R19, R20, R21, R22, R23, R24, R25, R26, R27.
  rewrite <- (lib.Lib.MState.ret_pc_even 544436 ltac:(lia) ltac:(reflexivity)).
  pose proof (C_reac_box_catalogue_matchLibW.cmRBw_post_sm2_side
    (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4)
    (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9) (lib.Reusable.YK11.getr regs 18)
    (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21)
    (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24)
    (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27)
    lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr f len (lib.Reusable.YG0d.spZ regs) (lib.Reusable.YG0f.ly_F ly) fb
    (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) m2
    Rf Rlen RS S16 HK Hfb HFp AFp HHM HAE RWIN RWSH RFD RFW RFPW HB STlo m1 ST1 SV1 HKP pos HFs2) as RUN.
  eapply cmPfB_jr_lift; [exact (RUN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)|].
  intros ms' md' HG Hgr Hhid Hsame. cbn [ms_mem] in Hgr, Hhid.
  destruct HG as [EX | PA].
  - destruct EX as (mc & r & xe & u0 & u1 & u2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z5 & z6 & z9 & z10 &
                    z11 & u3 & u4 & u5 & u6 & Er & HJw & ->).
    cbn [ms_mem] in Hgr, Hhid.
    pose proof HJw as (_ & MUw & _).
    pose proof (cmPfB_jr_journal_pin (lib.Reusable.YG0d.spZ regs) ly S W memc md [(2, pos)] ly S2 W m2 md2 0 mc md'
                  pos HJ2 (or_introl eq_refl) MUw Hgr Hhid Hsame) as HJ3.
    apply Kx. subst r.
    exact (cmPfB_me_exit W ly S regs memc md f len fb pos ly S2 W mc m2 md'
             xe u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6
             HBASE HJ3 Hfr Hnin ltac:(rewrite Hab; apply Permutation_refl) Hpos Hfa Hfl HJw).
  - pose proof PA as (mc & rt0 & rt1 & rt2 & ra3 & ra4 & ra5 & ra6 & ra7 & rs6 & rs9 & rs10 & rs11 & rt3 & rt4 &
                      rt5 & rt6 & Ems & HAt).
    rewrite Ems in Hgr, Hhid. cbn [ms_mem] in Hgr, Hhid.
    pose proof HAt as (_ & _ & _ & _ & _ & (_ & MUw & _) & _).
    pose proof (cmPfB_jr_journal_pin (lib.Reusable.YG0d.spZ regs) ly S W memc md [(2, pos)] ly S2 W m2 md2 0 mc md'
                  pos HJ2 (or_introl eq_refl) MUw Hgr Hhid Hsame) as HJ3.
    apply (Kp ms' md' PA). rewrite Ems. exact HJ3.
Qed.


(* ---- E2 + S-C: from the reac_ctrl_parse call (stretch 2's parse arm) through the parse event (TPARSE,
   cmPfB_pa_call / cmPfB_pa_ret) and the re-based stretch 3 (C_reac_box_catalogue_matchLibW.cmRBw_post_parse at base
   the parse return memory, call memory the parse call memory) to the exit (into cmPf_exit_at) or to the call of
   reac_box_model_block for row 0 (continuation Kr), with the journal across the stretch (cmPfB_jr_journal_pin). ---- *)
Lemma cmPfB_PC : forall (W : lib.Reusable.YA0n.world rsegs) (ly : lib.Reusable.YG0f.alayout)
    (S : lib.Reusable.YG00.astate) (regs : bvmap 5 word) (memc : word -> option byte) (md : Model) (f len : Z)
    (fb : list byte) (pos : Z) (S2 : lib.Reusable.YG00.astate) (m2 : word -> option byte) (ms' : machine_state)
    (md' : Model) (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
  cmPfB_ctx W ly S regs memc md f len fb pos ->
  0 <= pos < fs_M 2 ->
  lib.Reusable.YG0f.frame_addr ly 2 pos = fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos ->
  lib.Reusable.YG0f.flag_addr ly 2 pos = fs_flag (lib.Reusable.YG0f.ly_F ly) 2 pos ->
  lib.Reusable.YG0d.spZ regs mod 16 = 0 -> 9136 <= lib.Reusable.YG0d.spZ regs -> lib.Reusable.YG0d.spZ regs < 2 ^ 64 ->
  HIGHMEM_BEG <= lib.Reusable.YG0d.spZ regs - 9136 -> lib.Reusable.YG0d.spZ regs <= APPMEM_END ->
  (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\
     (f + 50 <= lib.Reusable.YG0d.spZ regs - 9136 \/ lib.Reusable.YG0d.spZ regs <= f)) ->
  (50 <= len -> app_mem (f + 50)) ->
  lib.Reusable.YG01.frames S2 = (2, pos) :: lib.Reusable.YG01.frames S -> ~ In (2, pos) (lib.Reusable.YG01.frames S) ->
  lib.Reusable.YG0d.ablocks B ly S2 = lib.Reusable.YG0d.ablocks B ly S ->
  C_reac_box_catalogue_matchLibW.cmRBw_parse_at (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 3)
    (lib.Reusable.YK11.getr regs 4) (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9)
    (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20)
    (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23)
    (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26)
    (lib.Reusable.YK11.getr regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr m2 f len
    (lib.Reusable.YG0d.spZ regs) (lib.Reusable.YG0f.ly_F ly) fb (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos)
    (CA (lib.Reusable.YG0d.spZ regs)) pos 1 ms' ->
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK (lib.Reusable.YG0d.spZ regs) []
    ly S W memc md [(2, pos)] ly S2 W (ms_mem ms') md' 0 ->
  (forall (W' : lib.Reusable.YA0n.world rsegs) (c : config),
     C_reac_box_catalogue_matchPfI.cmPf_exit_at B W ly S regs memc md f len fb W' c ->
     lib.Reusable.YA0n.SRr rsegs W' c Q) ->
  (forall (lyc : lib.Reusable.YG0f.alayout) (Sc : lib.Reusable.YG00.astate) (Wc : lib.Reusable.YA0n.world rsegs)
          (mb : word -> option byte) (ms'' : machine_state) (mdc : Model),
     lib.Reusable.YG01.frames Sc = (2, pos) :: lib.Reusable.YG01.frames S ->
     lib.Reusable.YG0d.ablocks B lyc Sc = lib.Reusable.YG0d.ablocks B ly S ->
     cm_gate len fb = true ->
     C_reac_box_catalogue_matchLibW.cmRBw_mb_call (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 3)
       (lib.Reusable.YK11.getr regs 4) (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9)
       (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20)
       (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23)
       (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26)
       (lib.Reusable.YK11.getr regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mb f len
       (lib.Reusable.YG0d.spZ regs) (lib.Reusable.YG0f.ly_F ly) fb 0 11 (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos)
       (CA (lib.Reusable.YG0d.spZ regs)) pos 1 ms'' ->
     lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK (lib.Reusable.YG0d.spZ regs) []
       ly S W memc md [(2, pos)] lyc Sc Wc (ms_mem ms'') mdc 0 ->
     lib.Reusable.YA0n.SRr rsegs Wc (mkCfg ms'' mdc) Q) ->
  lib.Reusable.YA0n.SRr rsegs W (mkCfg ms' md') Q.
Proof.
  intros W ly S regs memc md f len fb pos S2 m2 ms' md' Q Hctx Hpos Hfa Hfl S16 HK RS HHM HAE HFp AFp
    Hfr2 Hnin Hab2 PA HJ3 Kx Kr.
  pose proof Hctx as (Hgp & Htp & Rf & Rlen & Hfb & Hblk & Hga & Hro & Htbl & Hc1 & Hc0 & HBASE & HG17 & HTRO1 &
                      HTRO2 & HRELRO).
  destruct PA as (mc & rt0 & rt1 & rt2 & ra3 & ra4 & ra5 & ra6 & ra7 & rs6 & rs9 & rs10 & rs11 & rt3 & rt4 & rt5 & rt6 &
                  -> & HAt).
  cbn [ms_mem] in HJ3.
  pose proof (cmPfB_pa_CA (lib.Reusable.YG0d.spZ regs)) as (CA16 & CAlo & CAhi).
  pose proof HAt as (L50 & E12 & E13 & E16 & E17 & HJw & ADmc).
  pose proof HJw as (FK & _ & _ & _ & _ & _ & _ & STmc & _ & SVmc & FLmc).
  match goal with |- lib.Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (regsP := R) end.
  assert (RSP : lib.Reusable.YG0d.spZ regsP = CA (lib.Reusable.YG0d.spZ regs)).
  { unfold lib.Reusable.YG0d.spZ. exact (lib.Lib.Mem.wa_unsigned (CA (lib.Reusable.YG0d.spZ regs)) ltac:(lia)). }
  eapply lib.Reusable.YA0n.SRr_bind.
  { exact (cmPfB_pa_call ly S W memc md (lib.Reusable.YG0d.spZ regs) ly S2 W mc md'
             (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 4) (lib.Reusable.YK11.getr regs 8)
             (lib.Reusable.YK11.getr regs 9) (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19)
             (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22)
             (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25)
             (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27) m2 f len fb pos
             HRELRO HJ3 Hfr2 Hab2 HAt Hro Rlen Hfb Hblk Hga Hc1 regsP eq_refl RSP Hgp Htp eq_refl eq_refl eq_refl). }
  intros W2 c2 _ HPO.
  destruct (cmPfB_pa_ret ly S W memc md (lib.Reusable.YG0d.spZ regs) ly S2 W mc md' len fb pos regsP W2 c2
              HJ3 Hfr2 eq_refl RSP HPO)
    as (ly3 & S3 & regs3 & mem3 & md3 & -> & J4 & Hfr3 & Hab3 & _ & HP3 & R310 & STc & RWo & KP).
  assert (Hfr3' : lib.Reusable.YG01.frames S3 = (2, pos) :: lib.Reusable.YG01.frames S) by (rewrite Hfr3; exact Hfr2).
  assert (Hab3' : lib.Reusable.YG0d.ablocks B ly3 S3 = lib.Reusable.YG0d.ablocks B ly S) by (rewrite Hab3; exact Hab2).
  assert (Hblk3 : 50 <= len -> exists n, In (f, n) (lib.Reusable.YG0d.ablocks B ly3 S3) /\
                                         50 <= lib.Reusable.YG00.req_size n) by (rewrite Hab3'; exact Hblk).
  destruct (cmPfB_jr_rng_pin (lib.Reusable.YG0d.spZ regs) ly S W memc md [(2, pos)] ly3 S3 W2 mem3 md3 0 f len J4 Hblk3)
    as (RWIN & RWSH & RFD & RFW & RFPW & _ & _ & _).
  pose proof (HBASE ly3 S3 W2 mem3 md3 0 J4) as HB3.
  assert (E2 : lib.Reusable.YK11.getr regs3 2 = Z_to_bv 64 (CA (lib.Reusable.YG0d.spZ regs)))
    by exact (HP3 2 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (E3 : lib.Reusable.YK11.getr regs3 3 = lib.Reusable.YK11.getr regs 3)
    by exact (HP3 3 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (E4 : lib.Reusable.YK11.getr regs3 4 = lib.Reusable.YK11.getr regs 4)
    by exact (HP3 4 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (E8 : lib.Reusable.YK11.getr regs3 8 = Z_to_bv 64 (lib.Reusable.YG0d.spZ regs))
    by exact (HP3 8 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (E9 : lib.Reusable.YK11.getr regs3 9 = Z_to_bv 64 (CA (lib.Reusable.YG0d.spZ regs)))
    by exact (HP3 9 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (E18 : lib.Reusable.YK11.getr regs3 18 =
                Z_to_bv 64 (if 1 =? 0 then 0 else fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos))
    by exact (HP3 18 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (E19 : lib.Reusable.YK11.getr regs3 19 = Z_to_bv 64 f)
    by exact (HP3 19 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (E20 : lib.Reusable.YK11.getr regs3 20 = Z_to_bv 64 len)
    by exact (HP3 20 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (E21 : lib.Reusable.YK11.getr regs3 21 = lib.Lib.Mem.wa ASAN_K)
    by exact (HP3 21 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (E22 : lib.Reusable.YK11.getr regs3 22 = rs6)
    by exact (HP3 22 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (E23 : lib.Reusable.YK11.getr regs3 23 = Z_to_bv 64 (shadow_addr (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos)))
    by exact (HP3 23 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (E24 : lib.Reusable.YK11.getr regs3 24 = Z_to_bv 64 (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos))
    by exact (HP3 24 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (E25 : lib.Reusable.YK11.getr regs3 25 = rs9)
    by exact (HP3 25 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (E26 : lib.Reusable.YK11.getr regs3 26 = rs10)
    by exact (HP3 26 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  assert (E27 : lib.Reusable.YK11.getr regs3 27 = rs11)
    by exact (HP3 27 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)).
  unfold lib.Reusable.YG0d.cfg_at. apply cmPfB_me_canon.
  rewrite E2, E3, E4, E8, E9, R310, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
  unfold lib.Reusable.YG0d.w64.
  rewrite <- (lib.Lib.MState.ret_pc_even 0x85058 ltac:(lia) ltac:(reflexivity)).
  pose proof (C_reac_box_catalogue_matchLibW.cmRBw_post_parse
    (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4)
    (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9) (lib.Reusable.YK11.getr regs 18)
    (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21)
    (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24)
    (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27)
    lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr f len (lib.Reusable.YG0d.spZ regs) (lib.Reusable.YG0f.ly_F ly) fb
    (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W2)) mem3
    Rf Rlen RS S16 HK Hfb HFp AFp HHM HAE RWIN RWSH RFD RFW RFPW HB3
    (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos) (CA (lib.Reusable.YG0d.spZ regs)) pos 1 mc
    FK STmc SVmc FLmc ADmc STc RWo KP L50 E12 E13 E16 E17) as RUN.
  eapply cmPfB_jr_lift; [exact (RUN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rs6 rs9 rs10 rs11)|].
  intros ms'' md'' HG Hgr Hhid Hsame. cbn [ms_mem] in Hgr, Hhid.
  destruct HG as [EX | (G & MC)].
  - destruct EX as (mx & r & xe & u0 & u1 & u2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z5 & z6 & z9 & z10 &
                    z11 & u3 & u4 & u5 & u6 & Er & HJx & ->).
    cbn [ms_mem] in Hgr, Hhid.
    pose proof HJx as (_ & MUx & _).
    pose proof (cmPfB_jr_journal_pin (lib.Reusable.YG0d.spZ regs) ly S W memc md [(2, pos)] ly3 S3 W2 mem3 md3 0 mx md''
                  pos J4 (or_introl eq_refl) MUx Hgr Hhid Hsame) as J5.
    apply Kx. subst r.
    exact (cmPfB_me_exit W ly S regs memc md f len fb pos ly3 S3 W2 mx mem3 md''
             xe u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6
             HBASE J5 Hfr3' Hnin ltac:(rewrite Hab3'; apply Permutation_refl) Hpos Hfa Hfl HJx).
  - pose proof MC as (m0 & zt0 & zt1 & zt2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & Ems & HAtM).
    rewrite Ems in Hgr, Hhid. cbn [ms_mem] in Hgr, Hhid.
    pose proof HAtM as (_ & (_ & MU0 & _) & _).
    pose proof (cmPfB_jr_journal_pin (lib.Reusable.YG0d.spZ regs) ly S W memc md [(2, pos)] ly3 S3 W2 mem3 md3 0 m0 md''
                  pos J4 (or_introl eq_refl) MU0 Hgr Hhid Hsame) as J5.
    apply (Kr ly3 S3 W2 mem3 ms'' md'' Hfr3' Hab3' G MC). rewrite Ems. exact J5.
Qed.


(* ---- THE ROW LOOP: from the reac_box_model_block call of row i (k = 11 - i rows left) through the row's event (TMB,
   cmPfB_mb_call / cmPfB_mb_ret) and the re-based stretch 4 (C_reac_box_catalogue_matchLibW.cmRBw_post_mb at base
   the row's return memory, call memory the row's call memory) to the exit (into cmPf_exit_at) or to the call of row
   S i; an induction on k. ---- *)
Lemma cmPfB_rows : forall (k i : nat) (W : lib.Reusable.YA0n.world rsegs) (ly : lib.Reusable.YG0f.alayout)
    (S : lib.Reusable.YG00.astate) (regs : bvmap 5 word) (memc : word -> option byte) (md : Model) (f len : Z)
    (fb : list byte) (pos : Z) (lyc : lib.Reusable.YG0f.alayout) (Sc : lib.Reusable.YG00.astate)
    (Wc : lib.Reusable.YA0n.world rsegs) (mb : word -> option byte) (ms' : machine_state) (mdc : Model)
    (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
  cmPfB_ctx W ly S regs memc md f len fb pos ->
  0 <= pos < fs_M 2 ->
  lib.Reusable.YG0f.frame_addr ly 2 pos = fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos ->
  lib.Reusable.YG0f.flag_addr ly 2 pos = fs_flag (lib.Reusable.YG0f.ly_F ly) 2 pos ->
  lib.Reusable.YG0d.spZ regs mod 16 = 0 -> 9136 <= lib.Reusable.YG0d.spZ regs -> lib.Reusable.YG0d.spZ regs < 2 ^ 64 ->
  HIGHMEM_BEG <= lib.Reusable.YG0d.spZ regs - 9136 -> lib.Reusable.YG0d.spZ regs <= APPMEM_END ->
  (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\
     (f + 50 <= lib.Reusable.YG0d.spZ regs - 9136 \/ lib.Reusable.YG0d.spZ regs <= f)) ->
  (50 <= len -> app_mem (f + 50)) ->
  ~ In (2, pos) (lib.Reusable.YG01.frames S) ->
  (i + k = 11)%nat -> (0 < k)%nat -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) -> cm_gate len fb = true ->
  lib.Reusable.YG01.frames Sc = (2, pos) :: lib.Reusable.YG01.frames S ->
  lib.Reusable.YG0d.ablocks B lyc Sc = lib.Reusable.YG0d.ablocks B ly S ->
  C_reac_box_catalogue_matchLibW.cmRBw_mb_call (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 3)
    (lib.Reusable.YK11.getr regs 4) (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9)
    (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20)
    (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23)
    (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26)
    (lib.Reusable.YK11.getr regs 27) lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mb f len
    (lib.Reusable.YG0d.spZ regs) (lib.Reusable.YG0f.ly_F ly) fb i k (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos)
    (CA (lib.Reusable.YG0d.spZ regs)) pos 1 ms' ->
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK (lib.Reusable.YG0d.spZ regs) []
    ly S W memc md [(2, pos)] lyc Sc Wc (ms_mem ms') mdc 0 ->
  (forall (W' : lib.Reusable.YA0n.world rsegs) (c : config),
     C_reac_box_catalogue_matchPfI.cmPf_exit_at B W ly S regs memc md f len fb W' c ->
     lib.Reusable.YA0n.SRr rsegs W' c Q) ->
  lib.Reusable.YA0n.SRr rsegs Wc (mkCfg ms' mdc) Q.
Proof.
  intros k. induction k as [|k IH];
    intros i W ly S regs memc md f len fb pos lyc Sc Wc mb ms' mdc Q Hctx Hpos Hfa Hfl S16 HK RS HHM HAE HFp AFp
      Hnin Hik Hk Hnd G Hfrc Habc MC HJ Kx; [lia|].
  pose proof Hctx as (Hgp & Htp & Rf & Rlen & Hfb & Hblk & Hga & Hro & Htbl & Hc1 & Hc0 & HBASE & HG17 & HTRO1 &
                      HTRO2 & HRELRO).
  destruct MC as (m0 & zt0 & zt1 & zt2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & -> & HAtM).
  cbn [ms_mem] in HJ.
  pose proof (cmPfB_pa_CA (lib.Reusable.YG0d.spZ regs)) as (CA16 & CAlo & CAhi).
  pose proof HAtM as (Hi & HJw & ADm0).
  pose proof HJw as (FK & _ & _ & _ & _ & _ & _ & STm0 & _ & SVm0 & FLm0).
  match goal with |- lib.Reusable.YA0n.SRr _ _ (mkCfg (lib.Lib.MState.MS ?R _ _ _ _ _ _) _) _ => set (regsM := R) end.
  assert (RSP : lib.Reusable.YG0d.spZ regsM = CA (lib.Reusable.YG0d.spZ regs)).
  { unfold lib.Reusable.YG0d.spZ. exact (lib.Lib.Mem.wa_unsigned (CA (lib.Reusable.YG0d.spZ regs)) ltac:(lia)). }
  eapply lib.Reusable.YA0n.SRr_bind.
  { exact (cmPfB_mb_call W ly S memc md lyc Sc Wc m0 mdc (lib.Reusable.YG0d.spZ regs) pos
             (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 4) (lib.Reusable.YK11.getr regs 8)
             (lib.Reusable.YK11.getr regs 9) (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19)
             (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22)
             (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25)
             (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27) mb f len fb i
             HRELRO HJ HAtM Hro Hc0 Htbl HG17 (conj HTRO1 HTRO2) regsM eq_refl RSP Hgp Htp eq_refl eq_refl eq_refl). }
  intros W2 c2 _ HPO.
  destruct (cmPfB_mb_ret W ly S memc md lyc Sc Wc m0 mdc (lib.Reusable.YG0d.spZ regs) pos i regsM W2 c2
              HJ Hi eq_refl RSP HPO)
    as (ly4 & S4 & regs4 & mem4 & md4 & -> & J4 & Hfr4 & Hab4 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 &
        E23 & E24 & E25 & E26 & E27 & E10 & STc & BBo & KP).
  assert (Hfr4' : lib.Reusable.YG01.frames S4 = (2, pos) :: lib.Reusable.YG01.frames S) by (rewrite Hfr4; exact Hfrc).
  assert (Hab4' : lib.Reusable.YG0d.ablocks B ly4 S4 = lib.Reusable.YG0d.ablocks B ly S) by (rewrite Hab4; exact Habc).
  assert (Hblk4 : 50 <= len -> exists n, In (f, n) (lib.Reusable.YG0d.ablocks B ly4 S4) /\
                                         50 <= lib.Reusable.YG00.req_size n) by (rewrite Hab4'; exact Hblk).
  destruct (cmPfB_jr_rng_pin (lib.Reusable.YG0d.spZ regs) ly S W memc md [(2, pos)] ly4 S4 W2 mem4 md4 0 f len J4 Hblk4)
    as (RWIN & RWSH & RFD & RFW & RFPW & _ & RIMG & RB).
  pose proof (HBASE ly4 S4 W2 mem4 md4 0 J4) as HB4.
  apply cmPfB_me_canon.
  rewrite E2, E3, E4, E8, E9, E10, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
  pose proof (C_reac_box_catalogue_matchLibW.cmRBw_post_mb
    (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4)
    (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9) (lib.Reusable.YK11.getr regs 18)
    (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21)
    (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24)
    (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27)
    lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr f len (lib.Reusable.YG0d.spZ regs) (lib.Reusable.YG0f.ly_F ly) fb
    (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W2)) mem4
    ABCMP Rf Rlen RS S16 HK Hfb HFp AFp HHM HAE RB RIMG RWIN RWSH RFD RFW RFPW HB4 (Datatypes.S k) G i
    (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos) (CA (lib.Reusable.YG0d.spZ regs)) pos 1 m0
    Hik Hk Hnd FK STm0 SVm0 FLm0 ADm0 STc BBo KP) as RUN.
  eapply cmPfB_jr_lift; [exact (RUN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)|].
  intros ms'' md'' HG Hgr Hhid Hsame. cbn [ms_mem] in Hgr, Hhid.
  destruct HG as [EX | (k' & Hik' & Hk' & Hnd' & MC')].
  - destruct EX as (mx & r & xe & u0 & u1 & u2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z5 & z6 & z9 & z10 &
                    z11 & u3 & u4 & u5 & u6 & Er & HJx & ->).
    cbn [ms_mem] in Hgr, Hhid.
    pose proof HJx as (_ & MUx & _).
    pose proof (cmPfB_jr_journal_pin (lib.Reusable.YG0d.spZ regs) ly S W memc md [(2, pos)] ly4 S4 W2 mem4 md4 0 mx md''
                  pos J4 (or_introl eq_refl) MUx Hgr Hhid Hsame) as J5.
    apply Kx. subst r.
    exact (cmPfB_me_exit W ly S regs memc md f len fb pos ly4 S4 W2 mx mem4 md''
             xe u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6
             HBASE J5 Hfr4' Hnin ltac:(rewrite Hab4'; apply Permutation_refl) Hpos Hfa Hfl HJx).
  - assert (Ek : k' = k) by lia. subst k'.
    pose proof MC' as (m1 & wt0 & wt1 & wt2 & wa3 & wa4 & wa5 & wa6 & wa7 & wt3 & wt4 & wt5 & wt6 & Ems & HAtM').
    rewrite Ems in Hgr, Hhid. cbn [ms_mem] in Hgr, Hhid.
    pose proof HAtM' as (_ & (_ & MU1 & _) & _).
    pose proof (cmPfB_jr_journal_pin (lib.Reusable.YG0d.spZ regs) ly S W memc md [(2, pos)] ly4 S4 W2 mem4 md4 0 m1 md''
                  pos J4 (or_introl eq_refl) MU1 Hgr Hhid Hsame) as J5.
    apply (IH (Datatypes.S i) W ly S regs memc md f len fb pos ly4 S4 W2 mem4 ms'' md'' Q Hctx Hpos Hfa Hfl
             S16 HK RS HHM HAE HFp AFp Hnin Hik' Hk' Hnd' G Hfr4' Hab4' MC'); [|exact Kx].
    rewrite Ems. exact J5.
Qed.


(* ==== THE MIDDLE PIECE (H2) of pb_reac_box_catalogue_match: from the class-2 return (H1's interface cmPf_sm2_ret,
   pc 0x84eb4) to the exit 0x850fc (H3's interface cmPf_exit_at): S-B (cmPfB_SB), the reac_ctrl_parse event and S-C
   (cmPfB_PC), the row loop (cmPfB_rows, rows 0 .. 10).  Premises: the spec's own (C_reac_box_catalogue_match.v:82-101,
   as cmPf_to_sm2_ret's caller has them), the spec file's RELRO_IMG (:46), and the FRAME-ROUTE ones, each named:
     HBASE  cmBase at every state the walk reaches from the entry with own = [(2, pos)] (cmPfB_base_all; clause by
            clause as at C_reac_box_catalogue_matchPf.cmPf_SA, Lib's CLAUSE MAP; owner a Theorem Labs lane, lib/B/ProgWorld.v;
            to be discharged by H3's shared cmPf_base_of_AR, C_reac_box_catalogue_matchPfV.v);
     HG17   the image's registered globals list holds BOX_CATALOGUE's data range [CM_T, CM_T + 3256)
            (C_reac_box_catalogue_match.v:121 plan, `HG17 : In (A_CM_TBL, CM_ROWS) G`);
     HTRO   the B PA instance's pa_relro covers the table (C_reac_box_catalogue_match.v:50-51; the composer: arithmetic
            at [0x9f168, 0xa15e8)). ==== *)
Lemma cmPfB_mid : forall (W : lib.Reusable.YA0n.world rsegs) (ly : lib.Reusable.YG0f.alayout)
    (S : lib.Reusable.YG00.astate) (regs : bvmap 5 word) (memc : word -> option byte) (md : Model) (f len : Z)
    (fb : list byte) (m1 : word -> option byte) (md1 : Model) (regsT : bvmap 5 word) (S2 : lib.Reusable.YG00.astate)
    (regs2 : bvmap 5 word) (m2 : word -> option byte) (md2 : Model) (pos : Z)
    (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
  (* the spec's premises (C_reac_box_catalogue_match.v:83, 88-99) *)
  lib.Reusable.YK11.getr regs 3 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_gp B) ->
  lib.Reusable.YK11.getr regs 4 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B) ->
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> length fb = 50%nat ->
  (50 <= len -> exists n, In (f, n) (lib.Reusable.YG0d.ablocks B ly S) /\ 50 <= lib.Reusable.YG00.req_size n) ->
  (50 <= len -> lib.Reusable.YI00.garr8 rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) memc) f
                  (map (fun b : byte => bv_unsigned b) fb)) ->
  lib.Reusable.YE01.arodata_okS rsegs B RLO RHI (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc) ->
  (forall a, C_reac_box_catalogue_match.A_CM_TBL <= a < C_reac_box_catalogue_match.A_CM_TBL + C_reac_box_catalogue_match.CM_ROWS ->
     ~ Exists (lib.Reusable.YG0n.in_zr a) (lib.Reusable.YG0f.as_owned_static B) /\
     ~ (lib.Reusable.YG0f.as_errno B <= a < lib.Reusable.YG0f.as_errno B + 4)) ->
  lib.Reusable.YG01.count_cid 1 (lib.Reusable.YG01.frames S) < lib.Reusable.YG00.fs_frames 1 ->
  lib.Reusable.YG01.count_cid 0 (lib.Reusable.YG01.frames S) < lib.Reusable.YG00.fs_frames 0 ->
  (* the spec file's Section hypothesis RELRO_IMG (C_reac_box_catalogue_match.v:45; the composer:
     CtrlImg.ctrl_relro_img at pa_relro) *)
  (forall a, RLO <= a < RHI -> lib.Reusable.YG0d.in_img rsegs a) ->
  (* FRAME-ROUTE HBASE (see above) *)
  cmPfB_base_all ly S W regs memc md f len fb pos ->
  (* FRAME-ROUTE HG17 *)
  (exists q sz, In (q, sz) GLOBS /\ q <= CM_T /\ CM_T + 3256 <= q + sz) ->
  (* FRAME-ROUTE HTRO *)
  RLO <= CM_T -> CM_T + 3256 <= RHI ->
  C_reac_box_catalogue_matchPf.cmPf_sm2_ret B W ly S regs memc md f len m1 md1 regsT S2 regs2 m2 md2 pos ->
  (forall (W' : lib.Reusable.YA0n.world rsegs) (c : config),
     C_reac_box_catalogue_matchPfI.cmPf_exit_at B W ly S regs memc md f len fb W' c ->
     lib.Reusable.YA0n.SRr rsegs W' c Q) ->
  lib.Reusable.YA0n.SRr rsegs W
    (mkCfg (lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 544436) m2 (lib.Lib.PropExec.seg_rom rsegs)) md2) Q.
Proof.
  intros W ly S regs memc md f len fb m1 md1 regsT S2 regs2 m2 md2 pos Q
    Hgp Htp Rf Rlen Hfb Hblk Hga Hro Htbl Hc1 Hc0 HRELRO HBASE HG17 HTlo HThi Hret Kx.
  assert (Hctx : cmPfB_ctx W ly S regs memc md f len fb pos).
  { exact (conj Hgp (conj Htp (conj Rf (conj Rlen (conj Hfb (conj Hblk (conj Hga (conj Hro (conj Htbl (conj Hc1
             (conj Hc0 (conj HBASE (conj HG17 (conj HTlo (conj HThi HRELRO))))))))))))))). }
  pose proof (cmPfB_sb_in W ly S regs memc md f len m1 md1 regsT S2 regs2 m2 md2 pos Hret)
    as (Hpos & Hfa & Hfl & _ & _ & _ & _ & _ & _ & S16 & HK & RS & HHM & HAE).
  pose proof Hret as (_ & _ & _ & _ & _ & HJ2 & Hfr & Hnin & Hab & _).
  pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk2 & _).
  assert (HFA : (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\
                  (f + 50 <= lib.Reusable.YG0d.spZ regs - 9136 \/ lib.Reusable.YG0d.spZ regs <= f)) /\
                (50 <= len -> app_mem (f + 50))).
  { split; intros L; destruct (Hblk L) as (n & Hin & Hn);
      rewrite <- Hab in Hin;
      destruct (cmPfB_me_blk ly S2 W m2 md2 (lib.Reusable.YG0d.spZ regs) f n HAR2 Hstk2 Hin Hn) as [A1 A2];
      assumption. }
  destruct HFA as (HFp & AFp).
  apply (cmPfB_SB W ly S regs memc md f len fb m1 md1 regsT S2 regs2 m2 md2 pos Q Hctx Hret Kx).
  intros ms' md' PA HJ3.
  apply (cmPfB_PC W ly S regs memc md f len fb pos S2 m2 ms' md' Q Hctx Hpos Hfa Hfl S16 HK RS HHM HAE HFp AFp
           Hfr Hnin Hab PA HJ3 Kx).
  intros lyc Sc Wc mb ms'' mdc Hfrc Habc G MC J5.
  exact (cmPfB_rows 11 0 W ly S regs memc md f len fb pos lyc Sc Wc mb ms'' mdc Q Hctx Hpos Hfa Hfl S16 HK RS HHM HAE
           HFp AFp Hnin eq_refl ltac:(lia) (fun j Hj => False_ind _ (Nat.nlt_0_r j Hj)) G Hfrc Habc MC J5 Kx).
Qed.

End Mid.
