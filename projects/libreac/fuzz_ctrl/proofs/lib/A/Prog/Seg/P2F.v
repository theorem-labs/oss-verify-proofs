(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v; 134 of its 423 lines of code are new or changed and 107 lines of the source are left out. *)
(* PROVENANCE (lead condition 4). Image A = fuzz_ctrl.asan, libreac v1.9.0:
   pinned (internal path)
   sha256 aac16e1fe72899697a16d67dbff08390c1096be98a2fab183e80ce995135704d (unstripped
   (internal path) sha256 78efaeda1de51f8cb9208f86af7467cc8cb84e10c53295e7b6c3dce28ddcbebd).
   FACTS ed6b6b7b0ab, PAU pau-libreac-v190. Source: Seg/P2.v d7928842d2aa (the blob this tree had at release c5e779efe8c) at fdd2ed9f9d7.
   Tools: lib/Lib/StepF.v c97545265d26 (the blob this tree had at release c5e779efe8c), lib/Lib/ExecF.v 38b86b5d83a5 (the blob this tree had at release c5e779efe8c), The Rocq Prover 9.2 (OCaml 4.14.3).
   Compare: seg_P2_run re-derives the lib.Lib Exec.evt run at ExecF.RNG_all. There is NO seg_P2_run_of_F_verbatim
   pin in this file, because P2.v states NO run lemma: its one run is the `sl_run` argument inside seg_P2
   (P2.v:169, the second bullet of its proof at P2.v:178), so there is no P2.<r> constant to pin against (the same
   case as Seg/F5F.v, reported to the lead and to the auditor a Theorem Labs lane).
   Mechanical re-run, route (a) (lead 22:15Z); input to the ported walk only. *)

(* The footprint (_F) form of the one segment run of P2.v.  Segment P2 (0x81b10) is the single instruction
   `sb s2,332(s3)` (s3 = S(fr), the frame-base shadow), which writes one frame-shadow byte at S(fr) + 332 and
   falls to P3 at 0x81b14.  P2.v's proof hands that run to Tac_slot.sl_run inline; seg_P2_run_F states it and
   re-steps it with lib.Lib StepF as an ExecF.evtF under a universally quantified footprint RNG, with the same
   start state, the same post-state predicate K that seg_P2's continuation consumes, and one rng premise for the
   one byte the run writes.  The premises are exactly the three facts seg_P2's script holds at the `sl_run`:
   Hr19 (`getr regs 19 = Z_to_bv 64 (Sfr fr)`, P2.v:144 after `unfold rg`), Hin332 (`in_shadow (Sfr fr + 332)`,
   P2.v:163) and Hshadow_rw (`shadow_rw mem`, P2.v:165).  The run makes no instrumented check and no load, so no
   premise names a shadow-of-shadow byte and none names the image.  seg_P2_run re-derives the lib.Lib Exec.evt
   form (the form sl_run takes, through SmLib.ul_entry) from seg_P2_run_F with RNG_all.  P2.v is unchanged apart from comment text. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs Tac_b5 P1 P2.
(* ExecF / StepF are REQUIRED here but imported only inside Module RF below: their Import leaves lib.Lib / UL
   pairs (munch, getr, FPState) pointing at the other member, and the compiled source tie at the end of this file
   must be elaborated in exactly P2.v's name environment. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF StepF.
Import ListNotations.
(* Restore YK11.getr (the register read of rg and of the sl_run post-state) as the default, as P2.v does. *)
Import YK11.
Open Scope Z_scope.

Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module P2UE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Exec.

(* lib.Lib evt -> UL evt, by induction on the lib.Lib step chain (every lib.Lib step is a UL step).  The same
   six lines as Seg/F27F.v f27F_ul_of_lib (a working branch 47a3d558cf1c), Seg/F5F.v f5F_ul_of_lib and
   Seg/F10F.v f10F_ul_of_lib.  It lets the tie below keep P2.v's own `apply (sl_run ...)`, which takes the UL
   form, while seg_P2_run gives the lib.Lib one. *)
Lemma p2F_ul_of_lib : forall Q ms, LE.evt rsegs Q ms -> P2UE.evt rsegs Q ms.
Proof.
  intros Q ms (ms' & H & HQ). exists ms'. split; [clear HQ|exact HQ].
  induction H as [s|s s1 s2 Hs _ IH]; [apply P2UE.msteps_refl|].
  eapply P2UE.msteps_cons; [exact Hs | exact IH].
Qed.

Module RF.
(* Inside this module only: StepF's step / finish (evtF goals) shadow the UL engine's (evt goals), then YK11
   restores getr, exactly as a standalone _F file would order them. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.ExecF.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.
Import YK11.
(* ExecF / StepF re-open bv_scope on Import; this module's arithmetic is Z, as in P2.v. *)
Open Scope Z_scope.

Section RunF.
Context {fx : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.FPState}.

(* ---- seg_P2: 0x81b10 -> 0x81b14.  sb s2,332(s3) with s3 = S(fr): the run writes the one frame-shadow byte
   [S(fr) + 332, S(fr) + 333). ---- *)
Lemma seg_P2_run_F : forall (regs : bvmap 5 word) (mem : word -> option byte) (fr : Z) (RNG : footprint),
  getr regs 19 = Z_to_bv 64 (Sfr fr) ->
  in_shadow (Sfr fr + 332) ->
  shadow_rw mem ->
  rng RNG (Sfr fr + 332) 1 ->
  evtF rsegs RNG
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem'
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x81b14 /\
        getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
        getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 26 = getr regs 26 /\
        getr R 19 = Z_to_bv 64 (Sfr fr) /\ getr R 27 = getr regs 27 /\
        getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\
        exists bs, mem' = write_to_mem mem (wa (Sfr fr + 332)) bs /\ length bs = 1%nat))
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81b10) fp_csr None mem
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs)).
Proof.
  intros regs mem fr RNG Hr19 Hin332 Hshadow_rw Rsh.
  pose proof (in_shadow_range _ Hin332) as Hin332r.
  rewrite p2_mkR_of. rewrite Hr19. cbv [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.mkR].
  assert (HS : store_ok rsegs mem (wa (Sfr fr + 332)) 1 = true).
  { eapply (p2_wv_store_ok mem mem (Sfr fr + 332) 1);
    [ | apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.wmono_refl | lia | lia ].
    intros i Hi. assert (i = 0) by lia. subst i. rewrite Z.add_0_r.
    exact (proj1 (Hshadow_rw _ Hin332)). }
  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.step.
    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.finish.
  all: try reflexivity.
  all: eexists; split; [ reflexivity | first
    [ apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.length_le1 | reflexivity ] ].
Qed.

(* The lib.Lib Exec.evt form (the one Tac_slot.sl_run takes, through SmLib.ul_entry) from seg_P2_run_F at the
   footprint that admits every access. *)
Lemma seg_P2_run : forall (regs : bvmap 5 word) (mem : word -> option byte) (fr : Z),
  getr regs 19 = Z_to_bv 64 (Sfr fr) ->
  in_shadow (Sfr fr + 332) ->
  shadow_rw mem ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = LM.MS R fp_regs pc' fp_csr None mem'
    (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x81b14 /\
        getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
        getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 26 = getr regs 26 /\
        getr R 19 = Z_to_bv 64 (Sfr fr) /\ getr R 27 = getr regs 27 /\
        getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\
        exists bs, mem' = write_to_mem mem (wa (Sfr fr + 332)) bs /\ length bs = 1%nat))
    (LM.MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 0x81b10) fp_csr None mem
      (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.seg_rom rsegs)).
Proof.
  intros regs mem fr Hr19 Hin332 Hshadow_rw.
  pose proof (in_shadow_range _ Hin332) as Hin332r.
  eapply ExecF.evtF_evt, (seg_P2_run_F regs mem fr ExecF.RNG_all); try assumption.
  apply ExecF.rng_all; lia.
Qed.

End RunF.
End RF.

(* The two run lemmas, at this file's top level. *)
Notation seg_P2_run_F := RF.seg_P2_run_F.
Notation seg_P2_run := RF.seg_P2_run.

(* ---- COMPILED SOURCE TIE (auditor a Theorem Labs lane: every no-pin file needs one).  seg_P2_src is seg_P2's own
   statement, proved by P2.v:120-444 up to fully qualified names and line wraps, with exactly ONE step replaced: the evt bullet (P2.v:178-186,
   the inline run) is now `apply p2F_ul_of_lib; apply seg_P2_run` with seg_P2's own three facts.  Everything else,
   `apply (sl_run regs ...)` included, is P2.v's text verbatim.  It compiles only if the extracted run is exactly
   the one seg_P2 consumes.  seg_P2_src_verbatim pins the statement to P2.seg_P2's by constr_eq. *)

Section P2S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_P2_src : Hcut B APIf ra (Inv_A81b14 B APIf ra) -> Hcut B APIf ra (Inv_A81b10 B APIf ra).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros Hbc g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hn & Hour & HCUR & HPRO & HS144 &
    (A0 & idb & junk & HA0 & H27 & HA0r & HC208 & HCidb & HCjunk & Hq280 & Hq240 & (jy & junk2 & HCjy & HCj2))).
  subst c.
  rewrite SEGS.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  unfold rg in Hr19, Hr8, Hr9, Hr26.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  (* frame-base bounds from the header word's bytes_at *)
  assert (Hfrb : 0 <= fr /\ fr + 8 <= 2^64).
  { unfold q64 in Hhdr1. apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.bytes_at_bound in Hhdr1.
    rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8 in Hhdr1. lia. }
  assert (Hfr8 : fr mod 8 = 0). { pose proof Hfrm as Hfrm0. Z.div_mod_to_equations. lia. }
  (* Sfr fr value and range *)
  assert (HSfr : Sfr fr = fr / 8 + ASAN_K) by reflexivity.
  assert (HSfrlo : ASAN_K <= Sfr fr) by (rewrite HSfr; pose proof (Z.div_pos fr 8 (proj1 Hfrb) ltac:(lia)); unfold ASAN_K; lia).
  (* the store target equals the shadow of fr + 2656 *)
  assert (Hstadr : Sfr fr + 332 = shadow_addr (fr + 2656)).
  { unfold Sfr, shadow_addr, ASAN_K. replace (fr + 2656) with (fr + 332 * 8) by lia.
    rewrite Z.div_add by lia. lia. }
  (* the real-stack low bound is in high memory *)
  assert (Hstkhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by (apply (AC.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH)).
  assert (HAlo : HIGHMEM_BEG <= A).
  { assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity. lia. }
  assert (HAhi : A + 312 <= 2^64).
  { unfold q64 in Hspill. apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.bytes_at_bound in Hspill.
    rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8 in Hspill. lia. }
  (* the frame is application memory above the image's writable data, in both arms (fra_app) *)
  pose proof (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGT & Happ).
  (* the cut's s1 = A0 is FRA's spill base A *)
  assert (HA0A : A0 = A).
  { pose proof (f_equal (@bv_unsigned 64) (eq_trans (eq_sym Hr9) HA0)) as E0.
    rewrite !Z_to_bv_unsigned in E0. unfold bv_wrap, bv_modulus in E0.
    change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in E0.
    rewrite (Z.mod_small A (2 ^ 64)) in E0 by (unfold HIGHMEM_BEG in HAlo; lia).
    rewrite (Z.mod_small A0 (2 ^ 64)) in E0 by lia. lia. }
  subst A0.
  (* the store target is in the shadow map (its shadowed address fr + 2656 is application memory) *)
  assert (Hin332 : in_shadow (Sfr fr + 332)).
  { rewrite Hstadr. apply shadow_of_app. apply Happ. lia. }
  assert (Hshadow_rw : shadow_rw mem) by (apply (AsanRTInv.RT_shadow_rw _ _ _ HRT)).
  pose proof (in_shadow_range _ Hin332) as Hin332r.
  (* run the single store instruction *)
  apply (sl_run regs (Z_to_bv 64 0x81b10) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81b14 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 26 = getr regs 26 /\
       getr R 19 = Z_to_bv 64 (Sfr fr) /\ getr R 27 = getr regs 27 /\
       getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\
       exists bs, mem' = write_to_mem mem (wa (Sfr fr + 332)) bs /\ length bs = 1%nat)
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* the evt: the store at S(fr)+332, now the stated run seg_P2_run, carried into the UL form *)
    apply p2F_ul_of_lib. apply seg_P2_run; [ exact Hr19 | exact Hin332 | exact Hshadow_rw ].
  - (* the continuation: build the exit cut Inv_A81b14 *)
    intros R pc' mem' regs'' md' HK Hreg Hmat.
    destruct HK as (Hpc & HR2 & HR3 & HR4 & HR8 & HR9k & HR26 & HR19k & HR27 & HR22 & HR25 & bs & Hmem & Hlen).
    subst pc' mem'. rewrite <- SEGS. apply Hbc.
    exists regs'', (write_to_mem mem (wa (Sfr fr + 332)) bs), md', fr.
    split; [reflexivity|].
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact HR2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact HR3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact HR4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact HR8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact HR9k).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact HR26).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg, HR19k; symmetry; exact Hr19).
    assert (E27 : getr regs'' 27 = getr regs 27) by (rewrite Hreg; exact HR27).
    assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact HR22).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact HR25).
    set (mem' := write_to_mem mem (wa (Sfr fr + 332)) bs).
    pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.munch_write [(Sfr fr + 332, Sfr fr + 333)]
      mem mem (Sfr fr + 332) bs
                  (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.munch_refl _ _) ltac:(lia)
                    ltac:(rewrite Hlen; cbn [Z.of_nat]; lia)
                  ltac:(rewrite Hlen; cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.inside
                    Z.of_nat]; left; lia)) as MU.
    assert (WM : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.wmono rsegs mem mem') by
      (apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.wmono_write;
      apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.wmono_refl).
    (* AH, the runtime's ownership and the stack bounds kept across the shadow store, by arm *)
    assert (AHSTK : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md /\
                    (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem' md a <->
                               AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a) /\
                    AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                      = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                    AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                      = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
    { assert (Hwrit : forall x, 0 <= x < 2^64 -> writable_at rsegs mem x -> writable_at rsegs mem' x).
      { intros x Hx Hwx. exact (WM (Z_to_bv 64 x) Hwx). }
      destruct Hloc as [[Hs50 [Hspfr Hreal]]|[Hs5fr [Hfsb [Hfs Hrec]]]].
      - (* real arm: a_laws_store *)
        assert (Hmc : forall x, 0 <= x < 2^64 ->
                  ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                  mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
        { intros x Hx Hnok. destruct (Z.eq_dec x (Sfr fr + 332)) as [->|Hne].
          - exfalso. apply Hnok. right. right. right. exists (fr + 2656).
            split; [exact Hstadr|]. right. left. specialize (Hreal (fr+2656) ltac:(lia)).
            unfold APPMEM_END in *. lia.
          - unfold mem'. pose proof (MU (Z_to_bv 64 x)) as Hm. rewrite Hm; [reflexivity|].
            rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by exact Hx.
              cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside]. split; [lia | exact I]. }
        exact (p1_laws_store APIf ([] ++ g_H g) mem mem' md HAH Hmc Hwrit).
      - (* side arm: a_laws_fs_store *)
        pose proof (AsanRTInv.RT_fs_cells _ _ _ HRT) as HFSC.
        destruct HFSC as (_ & _ & _ & _ & (FSw & HFSb & Hfsok) & _).
        apply bytes_at_le8_word in HFSb.
        pose proof (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.u64_range FSw) as HFSr.
        destruct Hfsok as (HF0 & _ & HFGT & HFapp).
        assert (Happtop : app_mem (bv_unsigned FSw + RT_FS_SIZE - 1)) by (apply HFapp; unfold RT_FS_SIZE; lia).
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, RT_FS_SIZE in Happtop.
        unfold AsanRT.RT_GT in HFGT.
        (* the frame lies in the side stack region [FS, FS + FS_SIZE) of base FS = bv_unsigned FSw *)
        assert (HinFS : forall a0, fr <= a0 < fr + FRAME_BYTES ->
                  bv_unsigned FSw <= a0 < bv_unsigned FSw + AC.FS_SIZE).
        { intros a0 Ha0. pose proof (Happ a0 Ha0) as Hap0.
          unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap0.
          specialize (Hfs a0 Ha0). unfold AC.a_in_fs in Hfs. destruct Hfs as (b & Hbr & Hwm & Hb1 & Hb2).
          change (AC.as_tp AC.ASYMS) with AsanRT.RT_TP in Hwm.
          pose proof (p2_wm_congr mem AsanRT.RT_TP b (bv_unsigned FSw) Hwm HFSb) as Hcong.
          unfold AC.FS_SIZE in Hb2 |- *.
          assert (Hbeq : b = bv_unsigned FSw)
            by (revert Hcong Hb1 Hb2 Happtop HFGT HFSr Ha0 Hap0 Hfrb; Z.div_mod_to_equations; lia).
          subst b. lia. }
        (* FS base = bv_unsigned FSw ; a_fs_ok preserved *)
        pose proof (p1_fs_ok_of_state APIf ([] ++ g_H g) mem md (bv_unsigned FSw) HAH HFSb ltac:(lia)) as Hfsok0.
        (* every present byte stays present across the one-byte store *)
        assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                  exists b, mbyte rsegs mem' q = Some b).
        { intros q _ (b & Hb). unfold mem'.
          destruct bs as [|b0 [|b1 bs']]; cbn in Hlen; try discriminate.
          unfold mbyte in Hb |- *. cbn [write_to_mem].
          destruct (bv_eqb _ _); [exists b0; reflexivity | exists b; exact Hb]. }
        (* the side stack's metadata is application memory, so the shadow store misses it *)
        assert (Hmeta : forall q, fs_meta (bv_unsigned FSw) q ->
          OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside [(Sfr fr + 332, Sfr fr + 333)] q).
        { intros q Hq. pose proof (p2_fs_meta_range _ _ Hq) as Hqr.
          assert (Hqa : app_mem q) by (apply HFapp; unfold RT_FS_SIZE; lia).
          cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside]. split; [|exact I]. intros Hqt.
          assert (Hqe : q = Sfr fr + 332) by lia. subst q.
          exact (app_not_shadow _ Hqa Hin332). }
        assert (Hfsok' : AC.a_fs_ok mem' (bv_unsigned FSw)).
        { apply (a_fs_ok_pres [(Sfr fr + 332, Sfr fr + 333)] mem _ (bv_unsigned FSw) Hfsok0 MU Hwrit Hpres Hmeta);
            unfold AC.FS_SIZE; lia. }
        assert (Hmc : forall x, 0 <= x < 2^64 ->
                  ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                  ~ (bv_unsigned FSw <= x < bv_unsigned FSw + AC.FS_SIZE) ->
                  ~ (exists b, bv_unsigned FSw <= b < bv_unsigned FSw + AC.FS_SIZE /\ x = shadow_addr b) ->
                  mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
        { intros x Hx Hnok Hnfs Hnsh. destruct (Z.eq_dec x (Sfr fr + 332)) as [->|Hne].
          - exfalso. apply Hnsh. exists (fr + 2656). split; [apply HinFS; lia | exact Hstadr].
          - unfold mem'. pose proof (MU (Z_to_bv 64 x)) as Hm. rewrite Hm; [reflexivity|].
            rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by exact Hx.
              cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside]. split; [lia | exact I]. }
        exact (p1_laws_fs_store APIf ([] ++ g_H g) mem mem' md (bv_unsigned FSw) HAH HFSb ltac:(lia) Hmc Hwrit
                 Hfsok'). }
    destruct AHSTK as (HAH' & Hown' & HSTK' & HSTKhi').
    (* s1 = A (mod 2^64) *)
    assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> A' mod 2 ^ 64 = A).
    { intros A' HA'.
      pose proof (f_equal (@bv_unsigned 64) (eq_trans (eq_sym Hr9) HA')) as E0.
      rewrite !Z_to_bv_unsigned in E0. unfold bv_wrap, bv_modulus in E0.
      change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in E0.
      rewrite (Z.mod_small A (2 ^ 64)) in E0 by (unfold HIGHMEM_BEG in HAlo; lia).
      symmetry; exact E0. }
    pose proof Hin332 as Hsh332.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh332.
    split.
    + (* FRA B APIf ra g fr [] regs'' mem' md' *)
      apply (sl_fra_move B APIf ra g fr [] regs'' regs'' mem' md md');
        [ | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact Hmat ].
      apply (sl_fr_meta B APIf ra empty FF g fr [] regs regs'' mem mem' md
               [(Sfr fr + 332, Sfr fr + 333)] HFRA MU WM); try assumption.
      * (* ro_agree mem' *)
        apply (ro_agree_same rsegs mem); [exact Hro|]. intros x Hxro.
        apply (write_ro_same rsegs bs mem (wa (Sfr fr + 332)) x); [|exact Hxro].
        rewrite Hlen. cbn [all_rw]. split; [|exact I].
        destruct (Hshadow_rw (Sfr fr + 332) Hin332) as (Hwv & bb & Hmrd).
        destruct (mem (wa (Sfr fr + 332))) as [c|] eqn:Em.
        -- (* a frame-shadow byte is never in a read-only segment *)
           exact (sl_shadow_not_ro (Sfr fr + 332) Hin332).
        -- exact (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.wview_not_ro rsegs mem (wa (Sfr fr + 332))
          Hwv Em).
      * (* rt_disjoint W *)
        unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB,
          RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI,
          RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
            cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.disjoint_from]. unfold ASAN_K in HSfrlo.
        repeat split; (lia || exact I).
      * (* the 392 shadow bytes after the write *)
        destruct Hsh as (shl & Hshb & Hshl).
        exists (upd_bytes shl (Z.to_nat 332) bs).
        split.
        -- apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.bytes_at_write_inside rsegs mem (Sfr fr)
          shl 332 bs Hshb ltac:(lia)).
           rewrite Hlen, Hshl, FRAME_SHADOW_val. cbn [Z.to_nat]. lia.
        -- rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.upd_bytes_length;
          [exact Hshl | rewrite Hlen, Hshl, FRAME_SHADOW_val; cbn [Z.to_nat]; lia].
      * (* HWkept: outside W away from the frame body and shadow *)
        intros x Hx Hnb Hnsh. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside].
          split; [|exact I]. lia.
      * (* HWspill: [A + 304, A + 312) is real stack, above the shadow *)
        intros A' HA' HA'r x Hx. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside].
          split; [|exact I].
        pose proof (HA9 A' HA') as HAeq.
        unfold HIGHMEM_BEG in HAlo. unfold ASAN_K in HSfrlo.
        revert Hx. Z.div_mod_to_equations. lia.
      * (* HWsaved: [S - 104, S) is above A + 416 *)
        intros x Hx. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside]. split; [|exact I].
        unfold HIGHMEM_BEG in HAlo. lia.
      * (* HWsel: the fr reload and selector spills [A + 16, A + 32) are real stack, above the shadow *)
        intros A' HA' HA'r x Hx. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside].
          split; [|exact I].
        pose proof (HA9 A' HA') as HAeq.
        unfold HIGHMEM_BEG in HAlo. unfold ASAN_K in HSfrlo.
        revert Hx. Z.div_mod_to_equations. lia.
      * (* HWwin: the entry-anchored slot window [S - SLOT_STACK, S) is at or above stklo, above the shadow *)
        intros x Hx. left. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside].
          split; [|exact I].
        assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
        unfold HIGHMEM_BEG in Hstkhigh. lia.
      * (* frame_AG stays addressable: its globals end below GT <= fr, so their shadow bytes are below S(fr) *)
        intros a Hin. apply (addr1_munch [(Sfr fr + 332, Sfr fr + 333)] mem mem' a MU); [|exact (HAG a Hin)].
        cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside]. split; [|exact I].
        pose proof (p2_ag_range a Hin) as Har. unfold AC.GT in HGT.
        clear - Har HGT Hfrb. unfold Sfr, shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
    + split.
      { (* ENT: the store writes one of the frame's 392 shadow bytes (ent_store), then the model step *)
        assert (HENT1 : ENT APIf g [] mem' md).
        { eapply ent_store;
            [exact HENT | exact HFRA | exact MU | | exact HSTK' | exact HSTKhi'
            | exact (fun a _ Ho => proj2 (Hown' a) Ho)].
          intros x Hx. destruct (Z.eq_dec x (Sfr fr + 332)) as [->|Hne].
          - right. right. right. lia.
          - left. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside]. split; [lia | exact I]. }
        eapply ent_mat; [exact HENT1 | exact Hmat]. }
      split; [exact Hn|].
      split.
      { (* OURb g fr mem' : the OUR app bytes at fr+2624 survive the shadow store *)
        unfold OURb in Hour |- *. unfold mem'.
        apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.bytes_at_write_other rsegs mem (Sfr fr + 332)
          bs (fr + 2624) (OUR (g_in g)) Hour);
          [ lia | rewrite Hlen; cbn [Z.of_nat]; lia | ].
        assert (Hourlen : Z.of_nat (length (OUR (g_in g))) = 6).
        { unfold OUR. rewrite length_map, length_seq. reflexivity. }
        rewrite Hlen, Hourlen. cbn [Z.of_nat].
        pose proof (Happ (fr + 2624) ltac:(lia)) as Happ2624.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happ2624.
        lia. }
      (* CUR: the store writes no register *)
      split.
      { destruct HCUR as (Hc & H22 & H25). split; [exact Hc|].
        unfold rg in *. rewrite E22, E25. split; [exact H22 | exact H25]. }
      (* push 13: PRO (the store writes the frame-shadow byte S(fr) + 332, not our[]'s S(fr) + 328) *)
      split.
      { assert (MUL : LibFr.munch [(Sfr fr + 332, Sfr fr + 333)] mem mem').
        { first [exact MU | exact (proj2 (fr_munch_ul _ mem mem') MU) | exact (proj1 (fr_munch_ul _ mem mem') MU)]. }
        apply (pro_fra B APIf ra g fr [] regs regs'' mem mem' md [(Sfr fr + 332, Sfr fr + 333)] A HFRA HPRO
                 Hr9 ltac:(unfold HIGHMEM_BEG in HAlo; lia) MUL E9).
        apply Forall_cons; [|apply Forall_nil]. unfold pro_iv; cbn [fst snd]. lia. }
      (* push 12: the spill [A + 144] = fr + 2688 (real stack, above HIGHMEM_BEG, apart from the stored byte) *)
      split.
      { destruct HS144 as (A1 & HrA1 & Hq144).
        assert (EA1 : A1 = A).
        { unfold q64 in Hq144. pose proof Hq144 as Hb.
          apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.bytes_at_bound in Hb.
          rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8 in Hb.
          unfold rg in HrA1. rewrite HA0 in HrA1. apply (f_equal (@bv_unsigned 64)) in HrA1.
          rewrite !Z_to_bv_unsigned in HrA1. unfold bv_wrap, bv_modulus in HrA1.
          change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in HrA1.
          rewrite (Z.mod_small A (2 ^ 64)) in HrA1 by (unfold HIGHMEM_BEG in HAlo; lia).
          revert HrA1. clear - Hb HAhi HAlo. unfold HIGHMEM_BEG in HAlo. Z.div_mod_to_equations. lia. }
        subst A1. exists A. split; [unfold rg; rewrite E9; exact HA0|].
        unfold q64 in *. unfold mem'.
        apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.bytes_at_write_other rsegs mem (Sfr fr + 332)
          bs (A + 144) _ Hq144);
          [lia | rewrite Hlen; cbn [Z.of_nat]; lia |].
        rewrite Hlen, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8. cbn [Z.of_nat].
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin332, HAlo. lia. }
      (* the registers and the three frame / stack cells: the store writes one shadow byte, no register; the exit's
         sp value is the entry's sp register *)
      exists (bv_unsigned (getr regs 2)), A, idb, junk.
      split; [rewrite E2; symmetry; apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.Z_to_bv_bv_unsigned|].
      split; [rewrite E9; exact HA0|].
      split; [unfold rg in *; rewrite E27; exact H27|].
      split; [exact HA0r|].
      split; [apply OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.u64_range|].
      (* the store's byte S(fr) + 332 is a shadow byte, the three cells are app bytes (s1-based ones in high
         memory) on one side of it *)
      assert (Hshr : 0x7fff8000 <= Sfr fr + 332 < 0x10007fff8000) by lia.
      assert (HC1 : 0x10007fff8000 <= A + 192) by (unfold HIGHMEM_BEG in HAlo; lia).
      pose proof (Happ (fr + 2688) ltac:(lia)) as Hap1. pose proof (Happ (fr + 2725) ltac:(lia)) as Hap2.
      pose proof (Happ (fr + 2768) ltac:(lia)) as Hap3. pose proof (Happ (fr + 2839) ltac:(lia)) as Hap4.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap1, Hap2, Hap3, Hap4.
      assert (Hside1 : fr + 2726 <= Sfr fr + 332 \/ Sfr fr + 333 <= fr + 2688)
        by (clear - Hshr Hap1 Hap2; lia).
      assert (Hside2 : fr + 2840 <= Sfr fr + 332 \/ Sfr fr + 333 <= fr + 2768)
        by (clear - Hshr Hap3 Hap4; lia).
      assert (Hlen1 : Z.of_nat (length bs) = 1) by (rewrite Hlen; reflexivity).
      split; [unfold mem'; eapply LStep.rw_cells_frame; [exact HC208 | | |];
              rewrite ?Hlen1; cbn [LCells.cells_size LCells.csize Z.of_nat Nat.add];
              clear - Hshr HC1; lia|].
      split; [unfold mem'; eapply LStep.rw_cells_frame; [exact HCidb | | |];
              rewrite ?Hlen1; cbn [LCells.cells_size LCells.csize Z.of_nat Nat.add];
              clear - Hshr Hside1; lia|].
      split; [unfold mem'; eapply LStep.rw_cells_frame; [exact HCjunk | | |];
              rewrite ?Hlen1; cbn [LCells.cells_size LCells.csize Z.of_nat Nat.add];
              clear - Hshr Hside2; lia|].
      (* push 9: the spills [A + 280] / [A + 240] (above HIGHMEM_BEG) and the cells at fr + 3040 / fr + 3056
         (application bytes) are apart from the stored shadow byte *)
      pose proof (Happ (fr + 3040) ltac:(lia)) as Hap5. pose proof (Happ (fr + 3087) ltac:(lia)) as Hap6.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap5, Hap6.
      assert (Hside3 : fr + 3088 <= Sfr fr + 332 \/ Sfr fr + 333 <= fr + 3040)
        by (clear - Hshr Hap5 Hap6; lia).
      split.
      { unfold q64 in *. unfold mem'.
        apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.bytes_at_write_other rsegs mem (Sfr fr + 332)
          bs (A + 280) _ Hq280);
          [lia | rewrite Hlen; cbn [Z.of_nat]; lia |].
        rewrite Hlen, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8. cbn [Z.of_nat].
          clear - Hshr HC1. lia. }
      split.
      { unfold q64 in *. unfold mem'.
        apply (OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.bytes_at_write_other rsegs mem (Sfr fr + 332)
          bs (A + 240) _ Hq240);
          [lia | rewrite Hlen; cbn [Z.of_nat]; lia |].
        rewrite Hlen, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.length_le8. cbn [Z.of_nat].
          clear - Hshr HC1. lia. }
      exists jy, junk2.
      split; [unfold mem'; eapply LStep.rw_cells_frame; [exact HCjy | | |];
              rewrite ?Hlen1; cbn [LCells.cells_size LCells.csize Z.of_nat Nat.add];
              clear - Hshr Hside3; lia|].
      unfold mem'; eapply LStep.rw_cells_frame; [exact HCj2 | | |];
        rewrite ?Hlen1; cbn [LCells.cells_size LCells.csize Z.of_nat Nat.add];
        clear - Hshr Hside3; lia.
Qed.

End P2S.

(* The pin: seg_P2_src's statement is P2.seg_P2's, term for term. *)
Lemma seg_P2_src_verbatim : True.
Proof. let A := type of (@P2.seg_P2) in let B := type of (@seg_P2_src) in constr_eq A B; exact I. Qed.
