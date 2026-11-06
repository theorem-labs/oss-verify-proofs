(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module paths and module names changed; 914 of its 1020 lines of code are new or changed and 1096 lines of the source are left out. *)
(* Segment F24 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): 0x825c8-0x825d0, through the call.
   0x825c8 mv a0,s6 (a0 = blk = phi + 18); 0x825cc mv a1,s4 (a1 = q = fr + 128); 0x825d0 jal reac_ports_parse
   @0x8765c.  The callee is composed on its lib/A contract (reac_ports_parse_c.v, a Section Hypothesis) and the
   segment lands at 0x825d4 with a0 = t_rp and the three ports words of PORTS.  The plain twin is plain/Q01.v (its
   parse part). Entry cut Inv_A825c8_at, exit cut Inv_A825d4_at (official SlotInv.v cuts, B7CUT).

   This file also holds the shared B7 call infrastructure used by Seg/F25.v and Seg/F26.v: the FRA transport
   across a run that writes the callee's 16-byte stack window, bytes of the frame body and bytes of the frame's
   shadow (b7_fra_run, with the heap invariant moved by b7_ah_keep; the side arm's frame record FSREC by
   Tac_slot.fsrec_munch_lo), the ENT transport across the same run (b7_ent_run), the FLSI transport (b7_flsi_run)
   and the frame facts the callee contracts need. The frame's place (apart from the callee window, above the side
   stack's metadata, writable) is SlotInv.fra_frame; the callee's stack window [sp - FN_STACK, sp) is
   SlotInv.fra_win. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcFrag RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib
  reac_ports_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs B7Cuts.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module RL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcLeaf.
Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcPorts.
Module RF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcFrag.

(* ======================================================================== *)
(* Image facts: every loaded segment of the image ends below AC.GT, so an    *)
(* address at or above AC.GT is in no segment: there its read view is its    *)
(* write view, and a run that writes only such addresses keeps ro_agree.     *)
(* ======================================================================== *)

Definition b7_tops_below (sg : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) sg.

Lemma b7_segs_below : b7_tops_below rsegs AC.GT = true.
Proof. vm_compute. reflexivity. Qed.

Lemma b7_seg_lt : forall x s, find_segment rsegs x 1 = Some s -> x < AC.GT.
Proof.
  intros x s H. pose proof b7_segs_below as HB. unfold b7_tops_below in HB.
  revert H HB. generalize rsegs as sg. intros sg. revert x s.
  induction sg as [|s0 r IH]; intros x s H HB; cbn [find_segment] in H; [discriminate H|].
  cbn [forallb] in HB. apply andb_prop in HB as [H0 Hr]. apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + 1) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH x s H Hr).
Qed.

Lemma b7_find_none : forall x, AC.GT <= x -> find_segment rsegs x 1 = None.
Proof.
  intros x Hx. destruct (find_segment rsegs x 1) as [s|] eqn:E; [|reflexivity].
  exfalso. pose proof (b7_seg_lt x s E). lia.
Qed.

(* At or above AC.GT the read view and the write view agree: a byte is readable there iff it is writable. *)
Lemma b7_hi_rd : forall m x, AC.GT <= x -> 0 <= x < 2 ^ 64 ->
  writable_at rsegs m x -> exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m x Hgt Hx Hw. unfold writable_at, wview in Hw. unfold mrd, wa.
  destruct (m (Z_to_bv 64 x)) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. apply Hw. rewrite MState.unsigned_lit by lia. rewrite (b7_find_none x Hgt). reflexivity.
Qed.

Lemma b7_hi_wr : forall m x, AC.GT <= x -> 0 <= x < 2 ^ 64 ->
  (exists b, mrd rsegs m (wa x) = Some b) -> writable_at rsegs m x.
Proof.
  intros m x Hgt Hx (b & Hb). unfold writable_at, wview.
  destruct (m (Z_to_bv 64 x)) as [c|] eqn:E; [discriminate|].
  exfalso. unfold mrd, wa in Hb. rewrite E in Hb.
  rewrite (seg_rom_unmapped rsegs (Z_to_bv 64 x)) in Hb; [discriminate Hb|].
  rewrite MState.unsigned_lit by lia. exact (b7_find_none x Hgt).
Qed.

(* ---- footprint helpers: a list of intervals all of whose bases are at or above AC.GT ---- *)

Lemma b7_dj : forall W a n, (forall lo hi, In (lo, hi) W -> a + n <= lo) -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; cbn [disjoint_from]; [exact I|].
  split.
  - left. apply (H lo hi). left. reflexivity.
  - apply IH. intros lo' hi' Hin. apply (H lo' hi'). right. exact Hin.
Qed.

Lemma b7_out_lo : forall W x, (forall lo hi, In (lo, hi) W -> x < lo) -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn [outside]; [exact I|].
  split.
  - pose proof (H lo hi ltac:(left; reflexivity)). lia.
  - apply IH. intros lo' hi' Hin. apply (H lo' hi'). right. exact Hin.
Qed.

Lemma b7_out_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; intros (_ & Hc); exact (H Hc)].
  destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|].
  - right. intros (Hc & _). lia.
  - left. split; [lia | exact H].
  - left. split; [lia | exact H].
Qed.

Lemma b7_in_cases : forall (W : list Frame.ivl) x,
  ~ outside W x -> exists lo hi, In (lo, hi) W /\ lo <= x < hi.
Proof.
  induction W as [|[lo hi] W IH]; intros x Hx; cbn [outside] in Hx; [exfalso; apply Hx; exact I|].
  destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|].
  - exists lo, hi. split; [left; reflexivity | lia].
  - destruct (IH x) as (lo' & hi' & Hin & Hr); [intros Ho; apply Hx; split; [lia | exact Ho]|].
    exists lo', hi'. split; [right; exact Hin | exact Hr].
  - destruct (IH x) as (lo' & hi' & Hin & Hr); [intros Ho; apply Hx; split; [lia | exact Ho]|].
    exists lo', hi'. split; [right; exact Hin | exact Hr].
Qed.

(* ADDR-KEEP over the Lib engine's munch (Tac_slot.sl_addr_keep is stated with the UL engine's). *)
Lemma b7_addr_keep : forall m m' W p n, addressable m p n -> munch W m m' -> all_app W -> addressable m' p n.
Proof.
  intros m m' W p n H MU AW. exact (addressable_kept m m' p n H (munch_meta W m m' MU AW)).
Qed.

Lemma b7_rt_disjoint : forall W, (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> rt_disjoint W.
Proof.
  intros W H. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
    RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
    RT_AGLOB_LEN.
  repeat split; apply b7_dj; intros lo hi Hin; pose proof (H lo hi Hin); unfold AC.GT in *; lia.
Qed.

Lemma b7_ro_keep : forall W m m', ro_agree rsegs m -> munch W m m' ->
  (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> ro_agree rsegs m'.
Proof.
  intros W m m' HRO MU HW a Ha.
  assert (Hlt : bv_unsigned a < AC.GT).
  { unfold ro_addr in Ha. destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate Ha].
    exact (b7_seg_lt _ s E). }
  unfold mrd in *. rewrite (MU a); [exact (HRO a Ha)|].
  apply b7_out_lo. intros lo hi Hin. pose proof (HW lo hi Hin). lia.
Qed.

(* A readable window at or above AC.GT survives any run that keeps writability (wmono). *)
Lemma b7_stk_keep : forall m m' lo hi, stk rsegs m lo hi -> wmono rsegs m m' ->
  AC.GT <= lo -> hi <= 2 ^ 64 -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & H) WM Hgt Hhi. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as (Hv & Hb). split; [exact (WM (wa a) Hv)|].
  apply b7_hi_rd; [lia | lia|]. exact (WM (wa a) Hv).
Qed.

(* The 392 shadow bytes of the frame exist whenever the shadow map is readable and the frame is app memory. *)
Lemma b7_sh_exists : forall m fr, shadow_rw m -> (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  0 <= fr -> fr mod 8 = 0 -> exists sh, bytes_at rsegs m (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros m fr HSW Happ Hfr0 Hfr8.
  assert (HS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  assert (HST : stk rsegs m (Sfr fr) (Sfr fr + FRAME_SHADOW)).
  { split.
    - unfold Sfr, shadow_addr, ASAN_K. pose proof (Z.div_pos fr 8 Hfr0 ltac:(lia)). lia.
    - split.
      + assert (Hs : in_shadow (Sfr fr + (FRAME_SHADOW - 1))) by (apply HS; lia).
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hs. lia.
      + intros a Ha. exact (HSW a (HS a Ha)). }
  destruct (Frame.stk_bytes rsegs m (Sfr fr) (Sfr fr + FRAME_SHADOW) HST ltac:(lia)) as (sh & Hlen & Hb).
  exists sh. split; [exact Hb|]. rewrite Hlen.
  replace (Sfr fr + FRAME_SHADOW - Sfr fr) with FRAME_SHADOW by lia. reflexivity.
Qed.

(* Two word_mem values at one address agree mod 2^64 (plain/P2's p2_wm_congr). *)
Lemma b7_wm_congr : forall (m : word -> option byte) a v1 v2,
  word_mem rsegs m a v1 -> word_mem rsegs m a v2 -> v1 mod 2 ^ 64 = v2 mod 2 ^ 64.
Proof.
  intros m a v1 v2 H1 H2.
  assert (Hb : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2.
    rewrite E1 in E2.
    assert (E2' : Z_to_bv 8 (le_byte v1 8 k) = Z_to_bv 8 (le_byte v2 8 k)) by congruence.
    apply (f_equal (@bv_unsigned 8)) in E2'. rewrite !kb_byte_unsigned in E2'. exact E2'. }
  apply Z.bits_inj'. intros j Hj.
  destruct (Z.ltb_spec j 64) as [Hlt|Hge].
  - set (k := Z.to_nat (j / 8)).
    assert (Hk8 : (k < 8)%nat) by (unfold k; apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      apply Z.div_lt_upper_bound; lia).
    pose proof (Hb k Hk8) as Hbk.
    assert (Hoff : 8 * Z.of_nat k + (j - 8 * Z.of_nat k) = j) by lia.
    assert (Hjk : j - 8 * Z.of_nat k = j mod 8) by (unfold k; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      rewrite (Z.div_mod j 8) at 1 by lia; lia).
    assert (Hoff8 : 0 <= j - 8 * Z.of_nat k < 8) by (rewrite Hjk; apply Z.mod_pos_bound; lia).
    assert (HT : Z.testbit (le_byte v1 8 k) (j - 8 * Z.of_nat k)
               = Z.testbit (le_byte v2 8 k) (j - 8 * Z.of_nat k)) by (rewrite Hbk; reflexivity).
    rewrite !le_byte_testbit in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ 8)) in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) in HT by lia.
    rewrite Hoff in HT.
    rewrite !Z.testbit_mod_pow2 by lia.
    rewrite (proj2 (Z.ltb_lt j 64)) by lia. exact HT.
  - rewrite !Z.testbit_mod_pow2 by lia. rewrite (proj2 (Z.ltb_ge j 64)) by lia. reflexivity.
Qed.

(* Every side-stack metadata cell lies in [FS, FS + 36864). *)
Lemma b7_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* mkR_of made concrete, so the segment's register reads reduce. *)
Lemma b7_mkR_of_expand : forall (fx : FPState) regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros fx regs. reflexivity. Qed.

(* ---- model facts: the 20 ports bytes are the first 20 of the 32 block bytes ---- *)

Lemma b7_pbs_of_blk : forall inp j, t_pbs inp j = firstn 20 (t_blk inp j).
Proof.
  intros inp j. unfold t_pbs, t_blk, RF.bsl.
  change (Z.to_nat 20) with 20%nat. change (Z.to_nat 32) with 32%nat.
  rewrite firstn_firstn. reflexivity.
Qed.

Lemma b7_blk_length : forall inp j, length (t_blk inp j) = 32%nat.
Proof.
  intros inp j. unfold t_blk, RF.bsl, t_g. rewrite length_firstn, length_skipn, fr50_length.
  change (Z.to_nat 32) with 32%nat. change (Z.to_nat 18) with 18%nat. reflexivity.
Qed.

Lemma b7_pbs_length : forall inp j, length (t_pbs inp j) = 20%nat.
Proof.
  intros inp j. rewrite b7_pbs_of_blk, length_firstn, b7_blk_length. reflexivity.
Qed.

Lemma b7_pbs_bytes : forall m a inp j, bytes_at rsegs m a (t_blk inp j) -> bytes_at rsegs m a (t_pbs inp j).
Proof.
  intros m a inp j H. rewrite b7_pbs_of_blk.
  rewrite <- (firstn_skipn 20 (t_blk inp j)) in H.
  exact (proj1 (proj1 (bytes_at_app rsegs m a _ _) H)).
Qed.

Lemma b7_ports_ok : forall p q bs, p <> 0 -> q <> 0 -> RL.ports_ok p q bs = RL.decl bs.
Proof.
  intros p q bs Hp Hq. unfold RL.ports_ok.
  replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp).
  replace (q =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hq).
  reflexivity.
Qed.

Lemma b7_pu_ok : forall p bs, p <> 0 -> RP.pu_ok p bs = RP.pu_decl bs.
Proof.
  intros p bs Hp. unfold RP.pu_ok.
  replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp).
  reflexivity.
Qed.

(* ======================================================================== *)
Section B7.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* ---- The classification of a run's footprint: the callee's stack window [sp - FN_STACK, sp) (SlotInv.fra_win),
   the frame body, the frame shadow. ---- *)
Definition B7W (fr sp : Z) (W : list Frame.ivl) : Prop :=
  (forall lo hi, In (lo, hi) W -> AC.GT <= lo) /\
  (forall x, ~ Frame.outside W x ->
     (sp - FN_STACK <= x < sp \/ fr <= x < fr + FRAME_BYTES \/
      (exists b, fr <= b < fr + FRAME_BYTES /\ x = shadow_addr b))).

(* The Lib-evt -> SR bridge (Tac_slot.sl_run for a Lib.Exec.evt run; the callee contracts live in Lib.Exec). *)
Lemma b7_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* ---- The facts of the allocator laws and of the runtime's side-stack record this file reads, each taken apart
   once here (a Theorem Labs lane 15:32Z: an inner list of a law is destructed in one lemma per law per file). ---- *)
Lemma b7_law_blk : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p mod 16 = 0 /\ 4096 <= p /\ p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, p <= a < p + n -> ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin.
  destruct (AC.a_laws_blocks _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md p n HAH Hin)
    as (H16 & H4096 & Hst & _ & Hby).
  split; [exact H16|]. split; [exact H4096|]. split; [exact Hst|].
  intros a Ha. destruct (Hby a Ha) as (_ & _ & _ & _ & Hnfs). exact Hnfs.
Qed.

Lemma b7_law_store : forall H mem mem' md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH Hs Hw.
  destruct (AC.a_laws_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md HAH Hs Hw)
    as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.

Lemma b7_law_fs_place : forall H mem md b,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) b -> 0 <= b < 2 ^ 64 ->
  b + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem md b HAH Hw Hb.
  destruct (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md b HAH Hw Hb)
    as (_ & H2 & _ & _).
  exact H2.
Qed.

(* The runtime's side-stack word at the thread pointer and its value facts (AsanRT.asan_fs_cells, fs_value_ok). *)
Lemma b7_rt_fs : forall sp m md, AsanRTInv.RT sp m md ->
  exists FS : word, bytes_at rsegs m AsanRT.RT_TP (le8 FS) /\ 0 < bv_unsigned FS /\ bv_unsigned FS mod 4096 = 0 /\
    AsanRT.RT_GT <= bv_unsigned FS /\
    (forall a, bv_unsigned FS <= a < bv_unsigned FS + AsanRT.RT_FS_SIZE -> app_mem a).
Proof.
  intros sp m md HRT.
  pose proof (AsanRTInv.RT_fs_cells _ _ _ HRT) as (_ & _ & _ & _ & (FS & HB & (H0 & H1 & H2 & H3)) & _).
  exists FS. split; [exact HB|]. split; [exact H0|]. split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

(* ---- Frame facts read off FRA (SlotInv.fra_app): the frame is application memory, above AC.GT, below
   APPMEM_END (fr + FRAME_BYTES <= A <= S < APPMEM_END), 8-aligned. ---- *)
Lemma b7_fra_frame : forall g fr hb regs mem md,
  FRA B APIf ra g fr hb regs mem md ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) /\ AC.GT <= fr /\ 0 <= fr /\ fr + FRAME_BYTES <= APPMEM_END /\ fr mod 8 = 0.
Proof.
  pose proof FRAME_BYTES_val as HFBv.
  intros g fr hb regs mem md HFRA.
  destruct (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP & _).
  assert (Hfr8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  split; [exact Happ|]. split; [exact HGT|]. split; [unfold AC.GT in HGT; lia|]. split; [lia | exact Hfr8].
Qed.

(* The callee's stack window [sp - FN_STACK, sp) of SlotInv.fra_win lies in high memory (stklo is high memory),
   and sp is below APPMEM_END (sp <= A <= S < APPMEM_END). *)
Lemma b7_fra_win : forall g fr hb regs mem md,
  FRA B APIf ra g fr hb regs mem md ->
  HIGHMEM_BEG <= AC.aspZ regs - FN_STACK /\ AC.aspZ regs < APPMEM_END /\
  stk rsegs mem (AC.aspZ regs - FN_STACK) (AC.aspZ regs).
Proof.
  intros g fr hb regs mem md HFRA.
  destruct (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & Hstk).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP & _).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) (hb ++ g_H g) mem md HAH)
    as Hhigh.
  split; [lia|]. split; [lia | exact Hstk].
Qed.

(* Every live block of FRA's heap (the cut's own list hb and the entry heap) is below the callee window and apart
   from the frame. *)
Lemma b7_blk_apart : forall g fr hb regs mem md q n,
  FRA B APIf ra g fr hb regs mem md -> In (q, n) (hb ++ g_H g) -> 0 < n ->
  q + n <= AC.aspZ regs - FN_STACK /\ (q + n <= fr \/ fr + FRAME_BYTES <= q).
Proof.
  pose proof FRAME_BYTES_val as HFBv.
  intros g fr hb regs mem md q n HFRA Hin Hn.
  destruct (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  pose proof HFRA as HF2.
  destruct HF2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & _).
  destruct (b7_law_blk (hb ++ g_H g) mem md q n HAH Hin)
    as (Hal & Hlo & Hstk & Hbyt).
  split; [lia|].
  destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
  - left. specialize (Hreal fr ltac:(lia)). lia.
  - destruct (Z_le_gt_dec (q + n) fr) as [Hle|Hgt]; [left; exact Hle|].
    destruct (Z_le_gt_dec (fr + FRAME_BYTES) q) as [Hle2|Hgt2]; [right; exact Hle2|].
    exfalso. set (x := Z.max q fr).
    assert (Hx1 : q <= x < q + n) by (unfold x; lia).
    assert (Hx2 : fr <= x < fr + FRAME_BYTES) by (unfold x; lia).
    pose proof (Hbyt x Hx1) as Hnfs.
    exact (Hnfs (Hfs x Hx2)).
Qed.

(* The single live harness block of FRA's heap is below the callee window and apart from the frame. *)
Lemma b7_hb_apart : forall g fr phi n regs mem md,
  FRA B APIf ra g fr (hb1 phi n) regs mem md -> 0 < n ->
  phi + n <= AC.aspZ regs - FN_STACK /\ (phi + n <= fr \/ fr + FRAME_BYTES <= phi).
Proof.
  intros g fr phi n regs mem md HFRA Hn.
  apply (b7_blk_apart g fr (hb1 phi n) regs mem md phi n HFRA); [cbn [hb1 app]; left; reflexivity | exact Hn].
Qed.

(* ---- The heap invariant moves across a run confined to the window, the frame and the frame's shadow
   (a_laws_store on the real arm, a_fs_ok_store_AH on the side arm): AH, the runtime's ownership, stklo and
   stkhi. ---- *)
Lemma b7_ah_keep : forall g fr hb regs mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' ->
  B7W fr (AC.aspZ regs) W ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem mem' md W HFRA MU WM (HWgt & HWcls).
  destruct (b7_fra_frame g fr hb regs mem md HFRA) as (Happ & HGT & Hfr0 & Hfrhi & Hfr8).
  destruct (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  pose proof HFRA as HF2.
  destruct HF2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS (hb ++ g_H g) mem md HAH) as Hhigh.
  assert (Hwrit : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  rewrite Haspz in Hwlo, HWcls.
  destruct Hloc as [[Hs50 [Hspfr Hreal]]|[Hs5fr [Hfsb [Hfs _]]]].
  - (* real arm: a_laws_store *)
    assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
              ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
              mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { intros x Hx Hnok.
      destruct (b7_out_dec W x) as [Ho|Ho].
      - apply MU. rewrite MState.unsigned_lit by lia. exact Ho.
      - exfalso. apply Hnok. destruct (HWcls x Ho) as [Hw1|[Hw2|(b & Hb1 & Hb2)]].
        + right. left. lia.
        + right. left. specialize (Hreal x Hw2). lia.
        + right. right. right. exists b. split; [exact Hb2|]. right. left. exact (Hreal b Hb1). }
    exact (b7_law_store (hb ++ g_H g) mem mem' md HAH Hmc Hwrit).
  - (* side arm: a_fs_ok_store_AH *)
    destruct (b7_rt_fs _ _ _ HRT) as (FSw & HFSb & HF0 & _ & HFGT & HFapp).
    apply bytes_at_le8_word in HFSb.
    pose proof (u64_range FSw) as HFSr.
    assert (Happtop : app_mem (bv_unsigned FSw + RT_FS_SIZE - 1)) by (apply HFapp; unfold RT_FS_SIZE; lia).
    unfold AsanRT.RT_GT in HFGT.
    assert (HFStp : word_mem rsegs mem (AC.as_tp AC.ASYMS) (bv_unsigned FSw))
      by (change (AC.as_tp AC.ASYMS) with AsanRT.RT_TP; exact HFSb).
    assert (HFSsz : bv_unsigned FSw + AC.FS_SIZE <= 2 ^ 64).
    { unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, RT_FS_SIZE in Happtop.
      unfold AC.FS_SIZE. lia. }
    assert (HC3' : bv_unsigned FSw + 36864 <= fr) by (pose proof (Hfsb _ HFStp HFSr); lia).
    assert (HinFS : forall a0, fr <= a0 < fr + FRAME_BYTES -> bv_unsigned FSw <= a0 < bv_unsigned FSw + AC.FS_SIZE).
    { intros a0 Ha0. pose proof (Happ a0 Ha0) as Hap0.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap0.
      specialize (Hfs a0 Ha0). unfold AC.a_in_fs in Hfs. destruct Hfs as (b & Hbr & Hwm & Hb1 & Hb2).
      change (AC.as_tp AC.ASYMS) with AsanRT.RT_TP in Hwm.
      pose proof (b7_wm_congr mem AsanRT.RT_TP b (bv_unsigned FSw) Hwm HFSb) as Hcong.
      unfold AC.FS_SIZE in Hb2 |- *.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, RT_FS_SIZE in Happtop.
      assert (Hbeq : b = bv_unsigned FSw)
        by (revert Hcong Hb1 Hb2 Happtop HFGT HFSr Ha0 Hap0 Hbr; Z.div_mod_to_equations; lia).
      subst b. lia. }
    assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                      exists b, mbyte rsegs mem' q = Some b).
    { intros q Hq Hb.
      destruct (Z_lt_le_dec q AC.GT) as [Hlo|Hhi].
      - destruct Hb as (b & Hb). exists b. unfold mbyte in *.
        rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
        rewrite MState.unsigned_lit by lia. apply b7_out_lo. intros lo hi Hin.
        pose proof (HWgt lo hi Hin). lia.
      - apply b7_hi_rd; [lia | lia|]. apply Hwrit; [lia|].
        apply b7_hi_wr; [lia | lia | exact Hb]. }
    assert (Hmeta : forall q, fs_meta (bv_unsigned FSw) q -> Frame.outside W q).
    { intros q Hq. pose proof (b7_fs_meta_range _ _ Hq) as Hqr.
      destruct (b7_out_dec W q) as [Ho|Ho]; [exact Ho|].
      exfalso. destruct (HWcls q Ho) as [Hw1|[Hw2|(b & Hb1 & Hb2)]].
      - pose proof (b7_law_fs_place (hb ++ g_H g) mem md (bv_unsigned FSw) HAH HFStp ltac:(lia)) as Hfsle.
        unfold AC.FS_SIZE in Hfsle. lia.
      - lia.
      - assert (Hqa : app_mem q) by (apply HFapp; unfold RT_FS_SIZE; lia).
        rewrite Hb2 in Hqa. exact (app_not_shadow _ Hqa (shadow_of_app b (Happ b Hb1))). }
    assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
              ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
              ~ (bv_unsigned FSw <= q < bv_unsigned FSw + AC.FS_SIZE) ->
              ~ (exists b, bv_unsigned FSw <= b < bv_unsigned FSw + AC.FS_SIZE /\ q = shadow_addr b) ->
              mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq Hnok Hnfs Hnsh.
      destruct (b7_out_dec W q) as [Ho|Ho].
      - apply MU. rewrite MState.unsigned_lit by lia. exact Ho.
      - exfalso. destruct (HWcls q Ho) as [Hw1|[Hw2|(b & Hb1 & Hb2)]].
        + apply Hnok. right. left. lia.
        + exact (Hnfs (HinFS q Hw2)).
        + apply Hnsh. exists b. split; [exact (HinFS b Hb1) | exact Hb2]. }
    exact (a_fs_ok_store_AH AC.ASYMS (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
             (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc))
             (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
             W (hb ++ g_H g) mem mem' md (bv_unsigned FSw) ALAWS HAH HFStp ltac:(lia) HFSsz MU
             Hwrit Hpres Hmeta Hagree).
Qed.

(* ---- FRA moves across a run confined to the window, the frame body and the frame's shadow. A window byte
   outside the frame has its shadow byte outside W (the frame covers whole granules), so the window's
   addressability survives (addr1_munch); the frame_AG globals' addressability after the run is the caller's; the
   side arm's frame record FSREC survives by fsrec_munch_lo (W misses the low image and every app byte below
   stklo off the frame body). ---- *)
Lemma b7_fra_run : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' ->
  B7W fr (AC.aspZ regs) W ->
  (forall x, fr <= x < fr + 24 -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
     forall x, A + 304 <= x < A + 312 -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
     forall x, A + 16 <= x < A + 32 -> Frame.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HBW HWhdr HWspill HWsel HWsaved HAG'
    E2 E3 E4 E8 E9 E19 E26.
  pose proof HBW as (HWgt & HWcls).
  destruct (b7_ah_keep g fr hb regs mem mem' md W HFRA MU WM HBW) as (HAH' & _ & HSTK & _).
  destruct (b7_fra_frame g fr hb regs mem md HFRA) as (Happ & HGT & Hfr0 & Hfrhi & Hfr8).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (_ & _ & _ & Hfw).
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof HFRA as HF2.
  destruct HF2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS (hb ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1048576 - 4096) by reflexivity.
  pose proof Hwin as (Hw0 & Hw1 & Hwv).
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  rewrite Haspz in HWcls.
  pose proof (b7_rt_disjoint W HWgt) as HD.
  assert (HRO : ro_agree rsegs mem') by exact (b7_ro_keep W mem mem' Hro MU HWgt).
  assert (HOUTlo : forall x, 0 <= x < AC.GT -> Frame.outside W x).
  { intros x Hx. apply b7_out_lo. intros lo hi Hin. pose proof (HWgt lo hi Hin). lia. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by (unfold AC.GT in *; lia). apply HOUTlo. unfold AC.GT. lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  (* the shadow map stays readable: shadow addresses are above AC.GT, and writability is monotone *)
  assert (HshR : forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b).
  { intros a Ha. pose proof (in_shadow_range a Ha) as Har.
    assert (Hgt : AC.GT <= a) by (unfold in_shadow, LOWMEM_END, HIGHSHADOW_BEG, AC.GT in *; lia).
    apply b7_hi_rd; [exact Hgt | lia|].
    pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT a Ha) as (Hv & _).
    exact (WM (wa a) Hv). }
  assert (HRT' : AsanRTInv.RT sp mem' md)
    by exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HshR).
  (* a byte whose shadow byte is the shadow byte of a frame byte is a frame byte (fr mod 8 = 0, 3136 mod 8 = 0) *)
  assert (Hgran : forall a b, 0 <= a -> fr <= b < fr + FRAME_BYTES -> shadow_addr a = shadow_addr b ->
                    fr <= a < fr + FRAME_BYTES).
  { intros a b Ha0 Hb Heq. unfold shadow_addr in Heq.
    clear - Ha0 Hb Heq Hfr8 Hfr0 HFBv. Z.div_mod_to_equations. lia. }
  exists A, sp, s5.
  split; [exact HRT'|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo; [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo; [lia | rewrite Hlock in Hx; cbn in Hx; lia].
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]); destruct Hil. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A Hr9 HA64 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0' [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|]. intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0'|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [|exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite KBlo.
          -- exact (Hw k Hk).
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
          -- unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * eapply fsrec_munch_lo with (W := W); [exact Hrec | exact HAH | exact MU | |].
          -- intros x Hx. apply HOUTlo. unfold AC.GT. lia.
          -- intros x Hxa Hxf Hxs. destruct (b7_out_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso.
             destruct (HWcls x Ho) as [Hw|[Hf|(b & Hb1 & Hb2)]].
             ++ lia.
             ++ apply Ho. apply HWhdr. split; [lia|].
                destruct (Z_lt_le_dec x (fr + 24)) as [Hl|Hl]; [exact Hl | exfalso; apply Hxf; lia].
             ++ rewrite Hb2 in Hxa. exact (app_not_shadow _ Hxa (shadow_of_app b (Happ b Hb1))). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { apply (b7_sh_exists mem' fr (AsanRTInv.RT_shadow_rw _ _ _ HRT') Happ ltac:(lia) Hfr8). }
  split.
  { apply (b7_stk_keep mem mem' (g_S g - AF.SLOT_STACK) (g_S g)); [exact Hwin | exact WM | | exact Hw1].
    unfold AC.GT, HIGHMEM_BEG in *. lia. }
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [exact HAG'|].
  split.
  { intros a H1 H2.
    pose proof (HWA a H1 H2) as HadA.
    pose proof (addr1_app mem a HadA) as Happa.
    assert (Ha0 : 0 <= a) by (destruct HadA as (H0 & _); exact H0).
    apply (addr1_munch W mem mem' a MU); [|exact HadA].
    destruct (b7_out_dec W (shadow_addr a)) as [Ho|Ho]; [exact Ho|].
    exfalso. pose proof (shadow_of_app a Happa) as Hsa.
    destruct (HWcls (shadow_addr a) Ho) as [Hw|[Hf|(b & Hb & Heq)]].
    - apply (app_not_shadow (shadow_addr a)); [|exact Hsa].
      right. unfold HIGHMEM_BEG, APPMEM_END in *. lia.
    - exact (app_not_shadow (shadow_addr a) (Happ _ Hf) Hsa).
    - exact (H2 (Hgran a b Ha0 Hb Heq)). }
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

(* ---- ENT moves across the same run (Tac_slot.ent_store): the window [sp - FN_STACK, sp) lies in the slot window
   below S, a frame shadow byte is one of the frame's 392, and b7_ah_keep gives stklo, stkhi and ownership. ---- *)
Lemma b7_ent_run : forall g fr hb regs mem mem' md W,
  ENT APIf g hb mem md -> FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' -> B7W fr (AC.aspZ regs) W ->
  ENT APIf g hb mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem mem' md W HENT HFRA MU WM HBW.
  destruct (b7_ah_keep g fr hb regs mem mem' md W HFRA MU WM HBW) as (_ & Hown & Hlo & Hhi).
  destruct (b7_fra_frame g fr hb regs mem md HFRA) as (_ & _ & Hfr0 & _ & Hfr8).
  pose proof HBW as (_ & HWcls).
  pose proof HFRA as HF2.
  destruct HF2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP & _).
  rewrite Haspz in HWcls.
  assert (HFN : FN_STACK = 1048576 - 4096) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  apply (ent_store B APIf ra g fr hb regs mem mem' md W HENT HFRA MU); [| exact Hlo | exact Hhi |].
  - intros x Hx. destruct (b7_out_dec W x) as [Ho|Ho]; [left; exact Ho|]. right.
    destruct (HWcls x Ho) as [Hw|[Hf|(b & Hb & Heq)]].
    + left. lia.
    + right. left. exact Hf.
    + right. right. rewrite Heq. unfold Sfr, shadow_addr.
      clear - Hb Hfr8 Hfr0 HFBv HFSv. Z.div_mod_to_equations. lia.
  - intros a _ Ho. exact (proj2 (Hown a) Ho).
Qed.

(* ---- FLSI and B7K move across the same run when it also misses the frame's [fr + 2624, fr + 2840) (OUR and LT's
   records) and, v1.9, LT's FIRST body [fr + 2880, fr + 2915), the shadow bytes FLSI's frame buffers read
   (fr + 2624 .. fr + 2629, the identity record fr + 2688 .. fr + 2725 and FLC's 72 bytes at fragb fr) and the
   FIRST body's shadow bytes, and keeps the registers B7K reads. The spill area
   [A, A + 416) is above sp and above the frame and is app memory; the live block and the input block are below
   the callee window, apart from the frame and app memory, and a shadow byte of one of their bytes is not a frame
   shadow byte (the frame covers whole granules). ---- *)
Lemma b7_carry : forall g j phi fr regs regs' mem mem' md W,
  FRA B APIf ra g fr (hb1 phi (flen g j)) regs mem md -> HB mem phi (flen g j) ->
  FLSI g j fr regs mem -> B7K g j phi fr regs mem ->
  munch W mem mem' -> wmono rsegs mem mem' -> B7W fr (AC.aspZ regs) W ->
  (forall x, fr + 2624 <= x < fr + 2840 -> outside W x) ->
  (forall i, 0 <= i < 6 -> outside W (shadow_addr (fr + 2624 + i))) ->
  (forall i, 0 <= i < 38 -> outside W (shadow_addr (fr + 2688 + i))) ->
  (forall i, 0 <= i < 72 -> outside W (shadow_addr (fragb fr + i))) ->
  (forall x, fr + 2880 <= x < fr + 2915 -> outside W x) ->
  (forall i, 0 <= i < 35 -> outside W (shadow_addr (fr + 2880 + i))) ->
  getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 21 = getr regs 21 ->
  getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 ->
  FLSI g j fr regs' mem' /\ B7K g j phi fr regs' mem'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g j phi fr regs regs' mem mem' md W HFRA HHB HF HK MU WM HBW HWrec HWsh6 HWsh38 HWsh72 HWB HWBsh
    E9 E18 E21 E22 E23 E24.
  pose proof HBW as (HWgt & HWcls).
  destruct (b7_fra_frame g fr _ regs mem md HFRA) as (Happ & HGT & Hfr0 & Hfrhi & Hfr8).
  pose proof HK as (_ & _ & _ & Hphi0 & Hphi50 & Hfl & _).
  destruct (b7_hb_apart g fr phi (flen g j) regs mem md HFRA ltac:(lia)) as (Hhb1 & Hhb2).
  pose proof HFRA as HF2.
  destruct HF2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP & _).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1048576 - 4096) by reflexivity.
  rewrite Haspz in HWcls, Hhb1.
  assert (HspH : HIGHMEM_BEG < sp) by lia.
  assert (HAb : 0 <= A /\ A + 416 <= 2 ^ 64) by (unfold HIGHMEM_BEG, APPMEM_END in *; lia).
  (* a byte whose shadow byte is the shadow byte of a frame byte is a frame byte *)
  assert (Hgran : forall a b, 0 <= a -> fr <= b < fr + FRAME_BYTES -> shadow_addr a = shadow_addr b ->
                    fr <= a < fr + FRAME_BYTES).
  { intros a b Ha0 Hb Heq. unfold shadow_addr in Heq.
    clear - Ha0 Hb Heq Hfr8 Hfr0 HFBv. Z.div_mod_to_equations. lia. }
  (* a byte of a live block below the callee window and apart from the frame is outside W, and so is its shadow *)
  assert (Hblk : forall q n x, q + n <= sp - FN_STACK -> (q + n <= fr \/ fr + FRAME_BYTES <= q) -> q <= x < q + n ->
            app_mem x -> outside W x /\ outside W (shadow_addr x)).
  { intros q n x Hq1 Hq2 Hx Hxa. split.
    - destruct (b7_out_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso.
      destruct (HWcls x Ho) as [Hw|[Hf|(b & Hb1 & Hb2)]]; [lia | lia |].
      rewrite Hb2 in Hxa. exact (app_not_shadow _ Hxa (shadow_of_app b (Happ b Hb1))).
    - destruct (b7_out_dec W (shadow_addr x)) as [Ho|Ho]; [exact Ho|]. exfalso.
      pose proof (shadow_of_app x Hxa) as Hsx.
      destruct (HWcls (shadow_addr x) Ho) as [Hw|[Hf|(b & Hb1 & Hb2)]].
      + apply (app_not_shadow (shadow_addr x)); [right; unfold HIGHMEM_BEG, APPMEM_END in *; lia | exact Hsx].
      + exact (app_not_shadow (shadow_addr x) (Happ _ Hf) Hsx).
      + assert (Hx0 : 0 <= x) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxa; lia).
        pose proof (Hgran x b Hx0 Hb1 Hb2). lia. }
  assert (HWA : forall x, A <= x < A + 416 -> outside W x).
  { intros x Hx. destruct (b7_out_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso.
    destruct (HWcls x Ho) as [Hw|[Hf|(b & Hb1 & Hb2)]]; [lia | lia |].
    rewrite Hb2 in Hx.
    apply (app_not_shadow (shadow_addr b)); [right; unfold HIGHMEM_BEG, APPMEM_END in *; lia|].
    exact (shadow_of_app b (Happ b Hb1)). }
  pose proof HF as ((_ & _ & Fstk & _ & _) & _ & _ & _ & (Fin1 & (_ & _ & _ & Hadin) & _) & _).
  split.
  - apply (b7_flsi_keep g j fr regs regs' mem mem' W A HF Hr9 (proj1 HAb) (proj2 HAb) E9 MU HWA HWsh6 HWsh38
             HWsh72).
    + intros x Hx.
      destruct (b7_blk_apart g fr _ regs mem md (g_p g) (g_n g) HFRA
                  (in_or_app _ _ _ (or_intror (Fin1 ltac:(lia)))) ltac:(lia)) as (Hq1 & Hq2).
      rewrite Haspz in Hq1.
      destruct (Hadin (x - g_p g) ltac:(lia)) as (Hxa & _). replace (g_p g + (x - g_p g)) with x in Hxa by lia.
      exact (proj1 (Hblk (g_p g) (g_n g) x Hq1 Hq2 Hx Hxa)).
    + intros i Hi.
      destruct (b7_blk_apart g fr _ regs mem md (g_p g) (g_n g) HFRA
                  (in_or_app _ _ _ (or_intror (Fin1 ltac:(lia)))) ltac:(lia)) as (Hq1 & Hq2).
      rewrite Haspz in Hq1.
      destruct (Hadin i Hi) as (Hxa & _).
      exact (proj2 (Hblk (g_p g) (g_n g) (g_p g + i) Hq1 Hq2 ltac:(lia) Hxa)).
    + apply (b7_stk_keep mem mem' fr (fr + FRAME_BYTES) Fstk WM HGT). lia.
  - apply (b7_B7K_keep g j phi fr regs regs' mem mem' W A HK MU Hr9 (proj1 HAb) (proj2 HAb)
             E9 E18 E21 E22 E23 E24 HWA).
    + intros x Hx. destruct HHB as (_ & (_ & _ & _ & Had)). unfold AC.a_size in Had.
      destruct (Had (x - phi) ltac:(lia)) as (Hxa & _). replace (phi + (x - phi)) with x in Hxa by lia.
      exact (proj1 (Hblk phi (flen g j) x Hhb1 Hhb2 Hx Hxa)).
    + exact HWrec.
    + exact HWB.
    + exact HWBsh.
Qed.

(* ======================================================================== *)
(* The segment proper.                                                      *)
(* ======================================================================== *)
Hypothesis PP : reac_ports_parse_contract.

(* 0x825c8 -> 0x825d4 on explicit registers: two moves and the call, composed on the parse contract. *)
Lemma f24_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi fr lo : Z) (bs : list byte),
    sp = Z_to_bv 64 spv -> s6 = Z_to_bv 64 (phi + 18) -> s4 = Z_to_bv 64 (fr + 128) ->
    0 < phi -> phi + 50 <= 2 ^ 64 -> 0 <= fr -> fr + FRAME_BYTES <= 2 ^ 64 -> fr mod 32 = 0 ->
    0 <= spv < 2 ^ 64 ->
    stk rsegs m lo spv -> lo + 16 <= spv ->
    length bs = 20%nat -> bytes_at rsegs m (phi + 18) bs ->
    wr_at rsegs m (fr + 128) 12 ->
    (fr + 140 <= phi + 18 \/ phi + 38 <= fr + 128) ->
    (phi + 38 <= spv - 16 \/ spv <= phi + 18) ->
    (fr + 140 <= spv - 16 \/ spv <= fr + 128) ->
    asan_cells m -> shadow_rw m -> addressable m (phi + 18) 20 -> addressable m (fr + 128) 12 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(spv - 16, spv); (fr + 128, fr + 140)] x) ->
    LE.evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' t3' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (if RL.decl bs then 0 else -1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6)
                  Fr (Z_to_bv 64 0x825d4) fc None m' (seg_rom rsegs) /\
         munch [(spv - 16, spv); (fr + 128, fr + 140)] m m' /\ wmono rsegs m m' /\
         (RL.decl bs = true ->
            u32 m' (fr + 128) (4 * RL.n_in bs) /\ u32 m' (fr + 132) (4 * RL.n_out bs) /\
            u32 m' (fr + 136) (16 * RL.bt bs 7)) /\
         (RL.decl bs = false -> munch [(spv - 16, spv)] m m'))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x825c8) fc None m (seg_rom rsegs)).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m spv phi fr lo bs -> -> -> Hphi1 Hphi2 Hfr1 Hfr2 Hfr32 Hspv Hstk Hlo Hlen Hbs Hwr Hdj Hdjp Hdjq
    HAC HSW HADp HADq HOUT.
  pose proof (munch_refl [(spv - 16, spv); (fr + 128, fr + 140)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (Hspu : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  step. step. step.
  eapply evt_cut.
  { eapply PP with (p := phi + 18) (q := fr + 128) (bs := bs) (lo := lo).
    - first [reflexivity | f_equal; lia].
    - first [reflexivity | f_equal; lia].
    - lia.
    - lia.
    - rewrite Hspu. exact Hstk.
    - rewrite Hspu. unfold REAC_PORTS_PARSE_FRAME. lia.
    - intros _ _. split; [exact Hlen | exact Hbs].
    - intros _ _. split; [Z.div_mod_to_equations; lia|].
      split; [exact Hwr|]. split; [lia|].
      rewrite Hspu. unfold REAC_PORTS_PARSE_FRAME. split; lia.
    - intros _ _. split; [exact HAC|]. split; [exact HSW|]. split; [exact HADp | exact HADq].
    - intros _ _ x Hx. rewrite Hspu. unfold REAC_PORTS_PARSE_FRAME.
      replace (fr + 128 + 12) with (fr + 140) by lia. exact (HOUT x Hx). }
  intros ms' (t0' & t1' & t2' & t3' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & -> & Hpost).
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ ?pcx _ _ _ _) =>
      replace pcx with (Z_to_bv 64 0x825d4)
        by (symmetry; first [ rewrite ?MState.ret_pc_fold; apply MState.ret_pc_even; lia
                            | apply bv_eq; vm_compute; reflexivity
                            | vm_compute; reflexivity ])
  end.
  assert (Eok : RL.ports_ok (phi + 18) (fr + 128) bs = RL.decl bs)
    by (apply b7_ports_ok; lia).
  rewrite Eok in Hpost |- *.
  apply evt_done.
  destruct Hpost as (WMc & _ & STc & Hbr).
  rewrite Hspu in Hbr.
  revert Hbr. destruct (RL.decl bs) eqn:Ed; intros Hbr.
  - destruct Hbr as (Q0 & Q4 & Q8 & MUc).
    eexists _, _, _, _, _, _, _, _, _, _, _, _, m'. split; [reflexivity|].
    split.
    { eapply munch_weaken; [|exact MUc]. unfold Frame.sub_fp. cbn [outside].
      intros x (Hx1 & Hx2 & _). unfold REAC_PORTS_PARSE_FRAME.
      split; [lia|]. split; [lia | exact I]. }
    split; [exact WMc|].
    split.
    { intros _. unfold u32. split; [exact Q0|]. split.
      - replace (fr + 132) with (fr + 128 + 4) by lia. exact Q4.
      - replace (fr + 136) with (fr + 128 + 8) by lia. exact Q8. }
    intros E; discriminate E.
  - eexists _, _, _, _, _, _, _, _, _, _, _, _, m'. split; [reflexivity|].
    split.
    { eapply munch_weaken; [|exact Hbr]. unfold Frame.sub_fp. cbn [outside].
      intros x (Hx1 & _). unfold REAC_PORTS_PARSE_FRAME. split; [lia | exact I]. }
    split; [exact WMc|].
    split; [intros E; discriminate E|].
    intros _. eapply munch_weaken; [|exact Hbr]. unfold Frame.sub_fp. cbn [outside].
    intros x (Hx1 & _). unfold REAC_PORTS_PARSE_FRAME. split; [lia | exact I].
Qed.

Lemma seg_F24 : forall j : nat,
  Hat B APIf ra (Inv_A825d4_at B APIf ra) j -> Hat B APIf ra (Inv_A825c8_at B APIf ra) j.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hjle & HHB & HFLSI & HK &
    Hs4 & Hq0 & Hq4 & Hq8 & HADq).
  subst c. rewrite SEGS.
  pose proof (b7_asize_flen g j phi fr regs mem HK) as Hasz.
  rewrite Hasz in HFRA, HENT.
  pose proof HK as (HLK & Hs7 & Hs6 & Hphi1 & Hphi2 & Hflen & Hblk & Hsum & Hs8 & HSPL).
  destruct (b7_fra_frame g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Happ & HGT & Hfr0 & Hfrhi & Hfr8).
  destruct (b7_fra_win g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Hwinlo & Hsphi & Hwin).
  destruct (fra_frame B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (HCK & _ & _ & HC4).
  assert (HFN : FN_STACK = 1048576 - 4096) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  pose proof (HCK 16 ltac:(lia)) as HC1.
  destruct (b7_hb_apart g fr phi (flen g j) regs mem md HFRA ltac:(lia)) as (Hhb1 & Hhb2).
  pose proof HFRA as HF2.
  destruct HF2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin0 & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HAC0.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW0.
  assert (HspA : AC.aspZ regs = sp) by exact Haspz.
  rewrite HspA in HC1, Hwin, Hwinlo, Hsphi, Hhb1.
  assert (HAb : 0 <= A /\ A + 416 <= 2 ^ 64) by (unfold HIGHMEM_BEG, APPMEM_END in *; lia).
  assert (HA9 : forall A2, getr regs 9 = Z_to_bv 64 A2 -> - 408 <= A2 -> A2 < 2 ^ 64 -> A2 = A).
  { intros A2 H2 Hlo2 Hhi2. unfold rg in Hr9. rewrite H2 in Hr9.
    apply (f_equal (@bv_unsigned 64)) in Hr9. rewrite !MState.unsigned_lit_wrap in Hr9.
    Z.div_mod_to_equations. lia. }
  set (W := [(sp - 16, sp); (fr + 128, fr + 140)]).
  assert (HWgt : forall lo hi, In (lo, hi) W -> AC.GT <= lo).
  { intros lo hi Hin. unfold W in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold AC.GT, HIGHMEM_BEG, AF.SLOT_STACK in *; lia. }
  assert (HBW : B7W fr sp W).
  { split; [exact HWgt|]. intros x Hx. destruct (b7_in_cases W x Hx) as (lo0 & hi0 & Hin & Hr).
    unfold W in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
    - left. unfold AF.SLOT_STACK in *. lia.
    - right. left. lia. }
  assert (Happw : forall x, sp - 16 <= x < sp -> app_mem x).
  { intros x Hx. right. unfold HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia. }
  (* premises of the parse contract *)
  assert (HADp : addressable mem (phi + 18) 20).
  { destruct HHB as (_ & HADphi). unfold AC.a_size in HADphi.
    apply (addressable_sub mem phi (Z.max (flen g j) 1) 18 20 HADphi); lia. }
  assert (Hwr : wr_at rsegs mem (fr + 128) 12).
  { split; [lia|]. split; [unfold APPMEM_END in *; lia|]. intros i Hi.
    unfold writable_at in HC4. apply (HC4 (fr + 128 + i)). lia. }
  assert (HOUT : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
            outside W x).
  { intros x Hx. unfold W. cbn [outside]. destruct Hx as [Hx|[Hx|Hx]].
    - unfold GOT_CELL_K, AC.GT, HIGHMEM_BEG, AF.SLOT_STACK in *.
      split; [lia|]. split; [lia | exact I].
    - unfold CELL_K, AC.GT, HIGHMEM_BEG, AF.SLOT_STACK in *.
      split; [lia|]. split; [lia | exact I].
    - split.
      + intros Hin. exact (app_not_shadow x (Happw x Hin) Hx).
      + split; [|exact I]. intros Hin. exact (app_not_shadow x (Happ x ltac:(lia)) Hx). }
  (* the run *)
  apply (b7_run_lib regs (Z_to_bv 64 0x825c8) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x825d4 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
       getr R0 21 = getr regs 21 /\ getr R0 26 = getr regs 26 /\
       getr R0 20 = getr regs 20 /\ getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\
       getr R0 24 = getr regs 24 /\ getr R0 18 = getr regs 18 /\
       getr R0 10 = Z_to_bv 64 (if RL.decl (t_pbs (g_in g) j) then 0 else -1) /\
       munch W mem mem' /\ wmono rsegs mem mem' /\
       (RL.decl (t_pbs (g_in g) j) = true ->
          u32 mem' (fr + 128) (4 * RL.n_in (t_pbs (g_in g) j)) /\
          u32 mem' (fr + 132) (4 * RL.n_out (t_pbs (g_in g) j)) /\
          u32 mem' (fr + 136) (16 * RL.bt (t_pbs (g_in g) j) 7)) /\
       (RL.decl (t_pbs (g_in g) j) = false -> munch [(sp - 16, sp)] mem mem'))
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite (b7_mkR_of_expand fx regs). unfold rg in Hs6, Hs4.
    rewrite Hs6, Hs4, Hr2.
    eapply LE.evt_mono.
    { eapply f24_evt with (spv := sp) (phi := phi) (fr := fr) (lo := sp - FN_STACK)
        (bs := t_pbs (g_in g) j).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lia.
      - lia.
      - lia.
      - unfold APPMEM_END in Hfrhi. lia.
      - exact Hfrm.
      - unfold APPMEM_END, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
      - exact Hwin.
      - lia.
      - apply b7_pbs_length.
      - apply b7_pbs_bytes. exact Hblk.
      - exact Hwr.
      - destruct Hhb2 as [H|H]; [right | left]; lia.
      - left. lia.
      - destruct HC1 as [H|H]; [left | right]; lia.
      - exact HAC0.
      - exact HSW0.
      - exact HADp.
      - exact HADq.
      - exact HOUT. }
    { intros ms' (ra' & t0' & t1' & t2' & t3' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & E & MUc & WMc
        & Hok & Hno).
      eexists _, (Z_to_bv 64 0x825d4), m'. split; [exact E|].
      split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split; [exact MUc|]. split; [exact WMc|]. split; [exact Hok | exact Hno]. }
  - intros R0 pc' mem' regs' md' (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er21 & Er26 & Er20 & Er22 & Er23 &
      Er24 & Er18 & Er10 & MU & WM & Hok & Hno) Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 (if RL.decl (t_pbs (g_in g) j) then 0 else -1))
      by (rewrite Hreg; exact Er10).
    assert (Haspz' : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    (* FRA and ENT across the call *)
    assert (HWapp : all_app W).
    { unfold W. cbn [all_app]. split; [|split; [|exact I]].
      - intros x Hx. exact (Happw x Hx).
      - intros x Hx. apply Happ. lia. }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md).
    { apply (b7_fra_run g fr (hb1 phi (flen g j)) regs regs' mem mem' md W HFRA MU WM);
        [ rewrite HspA; exact HBW | | | | | | | | | | | | ].
      - intros x Hx. unfold W. cbn [outside]. split; [|split; [|exact I]].
        + destruct HC1 as [H|H]; lia.
        + lia.
      - intros A' HA' HA'r x Hx.
        assert (EA : A' = A) by (apply HA9; [exact HA' | lia | lia]). subst A'.
        unfold W. cbn [outside]. split; [|split; [|exact I]]; lia.
      - intros A' HA' HA'r x Hx.
        assert (EA : A' = A) by (apply HA9; [exact HA' | lia | lia]). subst A'.
        unfold W. cbn [outside]. split; [|split; [|exact I]]; lia.
      - intros x Hx. unfold W. cbn [outside]. split; [|split; [|exact I]]; lia.
      - intros a Hin. exact (b7_addr_keep mem mem' W a 1 (HAG a Hin) MU HWapp).
      - exact Fr2.
      - exact Fr3.
      - exact Fr4.
      - exact Fr8.
      - exact Fr9.
      - exact Fr19.
      - exact Fr26. }
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md').
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs' regs' mem' md md' HFRA');
        try reflexivity; exact Hmat. }
    assert (HENT' : ENT APIf g (hb1 phi (flen g j)) mem' md)
      by (apply (b7_ent_run g fr (hb1 phi (flen g j)) regs mem mem' md W HENT HFRA MU WM);
          rewrite HspA; exact HBW).
    assert (HENT'' : ENT APIf g (hb1 phi (flen g j)) mem' md')
      by (eapply ent_mat; [exact HENT' | exact Hmat]).
    (* FLSI and B7K: the run writes the callee's window and the ports words fr + 128 .. fr + 139 (app memory) *)
    assert (HBW' : B7W fr (AC.aspZ regs) W) by (rewrite HspA; exact HBW).
    assert (HC : FLSI g j fr regs' mem' /\ B7K g j phi fr regs' mem').
    { apply (b7_carry g j phi fr regs regs' mem mem' md W HFRA HHB HFLSI HK MU WM HBW').
      - intros x Hx. unfold W. cbn [outside]. split; [|split; [|exact I]]; [destruct HC1 as [H|H]; lia | lia].
      - intros i Hi. apply (b7_app_shadow_out W _ HWapp). apply shadow_of_app. apply Happ. lia.
      - intros i Hi. apply (b7_app_shadow_out W _ HWapp). apply shadow_of_app. apply Happ. lia.
      - intros i Hi. apply (b7_app_shadow_out W _ HWapp). apply shadow_of_app. apply Happ. unfold fragb. lia.
      - intros x Hx. unfold W. cbn [outside]. split; [|split; [|exact I]]; [destruct HC1 as [H|H]; lia | lia].
      - intros i Hi. apply (b7_app_shadow_out W _ HWapp). apply shadow_of_app. apply Happ. lia.
      - exact Fr9.
      - exact Fr18.
      - exact Fr21.
      - exact Fr22.
      - exact Fr23.
      - exact Fr24. }
    destruct HC as (HFLSI' & HK').
    assert (HexA : Inv_A825d4_at B APIf ra g j
             (mkCfg (mkst regs' (Z_to_bv 64 0x825d4) mem' (seg_rom rsegs)) md')).
    { exists phi, regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      rewrite ?Hasz.
      split; [exact HFRA''|].
      split; [exact HENT''|].
      split; [exact Hgn|].
      split; [exact Hjle|].
      split.
      { destruct HHB as (Hnz & HAD). split; [exact Hnz|].
        eapply b7_addr_keep; [exact HAD | exact MU | exact HWapp]. }
      split; [exact HFLSI'|].
      split; [exact HK'|].
      split; [unfold rg; rewrite Fr10; unfold t_rp; reflexivity|].
      split.
      { unfold PORTS. split; intros E.
        - apply Hok. unfold t_rp in E.
          destruct (RL.decl (t_pbs (g_in g) j)); [reflexivity | exfalso; lia].
        - assert (Ed : RL.decl (t_pbs (g_in g) j) = false).
          { unfold t_rp in E. destruct (RL.decl (t_pbs (g_in g) j));
              [exfalso; apply E; reflexivity | reflexivity]. }
          specialize (Hno Ed).
          assert (HK2 : forall a, bytes_at rsegs mem a (le4 (Z_to_bv 64 (-7))) ->
                     fr + 128 <= a -> a + 4 <= fr + 140 -> bytes_at rsegs mem' a (le4 (Z_to_bv 64 (-7)))).
          { intros a Hb Ha1 Ha2. eapply fl_bytes; [exact Hb | exact Hno|].
            rewrite length_le4. intros x Hx. cbn [outside]. split; [|exact I].
            destruct HC1 as [H|H]; lia. }
          unfold u32 in *.
          split; [exact (HK2 (fr + 128) Hq0 ltac:(lia) ltac:(lia))|].
          split; [exact (HK2 (fr + 132) Hq4 ltac:(lia) ltac:(lia))
                 | exact (HK2 (fr + 136) Hq8 ltac:(lia) ltac:(lia))]. }
      eapply b7_addr_keep; [exact HADq | exact MU | exact HWapp]. }
    pose proof (Hexit g _ HexA) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End B7.
