(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v; 245 of its 338 lines of code are new or changed and 918 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_f9.v; 50 of its 186 lines of code are new or changed and 202 lines of the source are left out. *)
(* The ENT transport a Theorem Labs lane's seg_P6 needs for the reac_ctrl_identity_reply call at 0x81d7c (v1.9.0; which writes
   its own stack window, the class-1 bytes of the side stack for frames and the shadow bytes of its window): a
   renamed copy
   of f9_ent_Wy / f9_ent_W of a Theorem Labs lane's lib/B/Prog/Seg/Tac_f9.v (a working branch 19225626266), which seg_F9
   uses for the same call at 0x82170, with the frame-location pattern updated to the side arm's FSREC conjunct.
   (Tac_f9's f9_fr_cl is not copied: it predates FSREC; Tac_bp.bp_fra serves instead.)
   bp6_ent_W is Tac_slot's ent_store with three more allowed address classes: the shadow of the slot window below
   the current sp, the side stack for frames, and (added here, for the class-1 frames' shadow the callee may
   write) the shadow of a side-stack byte. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_bp.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* y < Y <= b with Y a multiple of 8: y and b lie in different 8-byte granules, so their shadow bytes differ. *)
Local Lemma bp6_gran_lt : forall y Y b, 0 <= y -> y < Y -> Y <= b -> Y mod 8 = 0 -> y / 8 < b / 8.
Proof. intros y Y b H0 H1 H2 H3. Z.div_mod_to_equations. lia. Qed.

(* y + 8 <= b: their granules differ. *)
Local Lemma bp6_div_lt : forall y b, 0 <= y -> y + 8 <= b -> y / 8 < b / 8.
Proof. intros y b H0 H1. Z.div_mod_to_equations. lia. Qed.

(* The one place a Theorem Labs lane takes ENT apart (a Theorem Labs lane 15:51Z: ENT grows at its end, so the next conjunct breaks this
   line only): its first conjunct, the entry sp. *)
Lemma bp6_ent_parts : forall g hb mem md, ENT APIf g hb mem md -> AC.aspZ (g_regs g) = g_S g.
Proof. intros g hb mem md HENT. destruct HENT as (Hasp & _). exact Hasp. Qed.

(* bp6_ent_W for the shadow of the slot-window bytes below a granule boundary Y <= S: the shadow byte of such a byte
   is never the shadow byte of a byte at or above S, nor of an image byte (image < GT <= HIGHMEM_BEG <= the
   window). The side stack lies in app memory (a_laws_fs_place), at or above GT and below stklo <= S - SLOT_STACK,
   so it is apart from the image, from [S, APPMEM_END) and from every shadow byte; an entry block is not side
   stack (a_laws_blocks).  ent_kept's fifth case, the shadow of the entry blocks, is the caller's premise HK5:
   whether the shadow of a side-stack byte shares a granule with an entry block depends on the run's write set. *)
Local Lemma bp6_ent_Wy : forall g fr hb regs mem mem' md W Y,
  ENT APIf g hb mem md -> FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' ->
  (forall q k i, In (q, k) (g_H g) -> ~ In (q, k) (g_T g) -> 0 <= i < k -> Frame.outside W (shadow_addr (q + i))) ->
  Y <= g_S g -> Y mod 8 = 0 ->
  (forall x, 0 <= x < 2 ^ 64 -> Frame.outside W x \/ (g_S g - AF.SLOT_STACK <= x < g_S g) \/
     (fr <= x < fr + 3136) \/ (Sfr fr <= x < Sfr fr + 392) \/
     (exists y, g_S g - AF.SLOT_STACK <= y < Y /\ x = shadow_addr y) \/
     AC.a_in_fs AC.ASYMS mem x \/ (exists y, AC.a_in_fs AC.ASYMS mem y /\ x = shadow_addr y)) ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, AC.a_in_img a ->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a ->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a) ->
  ENT APIf g hb mem' md.
Proof.
  intros g fr hb regs mem mem' md W Y HENT HFRA MU HK5 HYS HY8 HWin Hlo Hhi Hown.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGTfr & Happfr).
  pose proof (bp6_ent_parts g hb mem md HENT) as Hasp.
  assert (HS0 : 0 <= g_S g) by (rewrite <- Hasp; apply (bv_unsigned_in_range 64)).
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                (hb ++ g_H g) mem md HAH).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  unfold AC.GT in HGTfr. unfold HIGHMEM_BEG in Hhigh.
  assert (Hfr8 : fr mod 8 = 0) by (pose proof (Z.mod_eq fr 32 ltac:(lia)) as X; rewrite Hfrm in X;
                                   replace fr with ((4 * (fr / 32)) * 8) by lia; apply Z_mod_mult).
  assert (Hfr0 : 0 <= fr) by (pose proof (Happfr fr ltac:(lia)) as X;
                              unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in X; lia).
  assert (Hfrd : 0 <= fr / 8) by (apply Z.div_pos; lia).
  assert (Hfrd8 : 8 * (fr / 8) <= fr) by (apply Z.mul_div_le; lia).
  (* every byte of the frame's 392 shadow bytes is the shadow byte of a frame byte *)
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + 392 -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + 3136) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happfr _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  (* every byte of the slot window is (high) app memory *)
  assert (HSY : forall y, g_S g - AF.SLOT_STACK <= y < g_S g -> app_mem y).
  { intros y Hy. unfold app_mem, HIGHMEM_BEG. right. lia. }
  (* the side stack: app memory, at or above GT, below the slot window *)
  assert (Hfsp : forall x, AC.a_in_fs AC.ASYMS mem x ->
            app_mem x /\ AC.GT <= x /\ x < g_S g - AF.SLOT_STACK).
  { intros x (b & Hb & Hwm & Hx).
    destruct (lw_fs_place (APIf rc) (hb ++ g_H g) mem md b HAH Hwm Hb) as [HGb Hbs _ Happ].
    split; [exact (Happ x Hx)|]. lia. }
  (* an app-memory byte is not the shadow of a window byte; a shadow byte is not side stack *)
  assert (Hnsy : forall x, app_mem x -> ~ (exists y, g_S g - AF.SLOT_STACK <= y < Y /\ x = shadow_addr y)).
  { intros x Hx (y & Hy & ->). exact (app_not_shadow _ Hx (shadow_of_app y (HSY y ltac:(lia)))). }
  assert (HshNF : forall x, in_shadow x -> ~ AC.a_in_fs AC.ASYMS mem x).
  { intros x Hs Hf. exact (app_not_shadow x (proj1 (Hfsp x Hf)) Hs). }
  (* an address in none of the six classes is outside W *)
  assert (Hreg : forall x, 0 <= x < 2 ^ 64 -> ~ (g_S g - AF.SLOT_STACK <= x < g_S g) ->
            ~ (fr <= x < fr + 3136) -> ~ (Sfr fr <= x < Sfr fr + 392) ->
            ~ (exists y, g_S g - AF.SLOT_STACK <= y < Y /\ x = shadow_addr y) ->
            ~ AC.a_in_fs AC.ASYMS mem x ->
            ~ (exists y, AC.a_in_fs AC.ASYMS mem y /\ x = shadow_addr y) -> Frame.outside W x).
  { intros x Hx H1 H2 H3 H4 H5 H6. destruct (HWin x Hx) as [Ho|[Hw|[Hf|[Hs|[Hy|[Hfs|Hfy]]]]]];
      [exact Ho | contradiction | contradiction | contradiction | contradiction | contradiction
      | contradiction]. }
  (* an app-memory byte is not the shadow of a side-stack byte *)
  assert (HnFy : forall x, app_mem x -> ~ (exists y, AC.a_in_fs AC.ASYMS mem y /\ x = shadow_addr y)).
  { intros x Hx (y & Hy & ->). exact (app_not_shadow _ Hx (shadow_of_app y (proj1 (Hfsp y Hy)))). }
  (* a byte of the frame's shadow is the shadow of a frame byte, so it is not the shadow of an image byte or of
     a byte at or above S *)
  assert (Hshfr : forall b, 0 <= b -> ~ (fr <= b < fr + 3136) ->
            ~ (Sfr fr <= shadow_addr b < Sfr fr + 392)).
  { intros b Hb0 Hnb Hin. apply Hnb. unfold Sfr, shadow_addr in Hin.
    revert Hin Hfr8 Hb0 Hfr0. clear. intros. Z.div_mod_to_equations. lia. }
  apply (ent_munch APIf g hb mem mem' md W HENT HAH MU); [| exact Hlo | exact Hhi | exact Hown].
  intros x Hk. destruct Hk as [Hblkk | [Hik | [Habk | [(b & Hor & ->) | Hk5]]]].
  - destruct Hblkk as (q & k & i & Hin & Hni & Hi & ->).
    pose proof (lw_blocks (APIf rc) (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin))) as HLB.
    pose proof (lwb_end _ _ _ _ _ _ HLB) as Hend.
    pose proof (proj1 (lwb_byte _ _ _ _ _ _ HLB (q + i) ltac:(lia))) as Happq.
    pose proof (lwb_byte_not_fs (APIf rc) _ _ _ _ _ HLB (q + i) ltac:(lia)) as Hnfs.
    assert (Hqr : 0 <= q + i < 2 ^ 64)
      by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
    apply Hreg; [exact Hqr | lia | | | exact (Hnsy _ Happq) | exact Hnfs | exact (HnFy _ Happq)].
    + intro Hf. destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0' [Hfsb [Hfs _]]]].
      * destruct (Hreal (q + i) Hf) as (Hr1 & _). lia.
      * exact (Hnfs (Hfs (q + i) Hf)).
    + intro Hs. exact (app_not_shadow (q + i) Happq (HshIS (q + i) Hs)).
  - pose proof (img_below_GT x Hik) as Hxg. unfold AC.GT in Hxg.
    assert (Happx : app_mem x) by (unfold app_mem, LOWMEM_END; left; lia).
    apply Hreg; [lia | lia | lia | | exact (Hnsy x Happx) | | exact (HnFy x Happx)].
    + intro Hs. exact (app_not_shadow x Happx (HshIS x Hs)).
    + intro Hf. destruct (Hfsp x Hf) as (_ & HG & _). unfold AC.GT in HG. lia.
  - assert (Happx : app_mem x) by (unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia).
    apply Hreg; [lia | lia | lia | | exact (Hnsy x Happx) | | exact (HnFy x Happx)].
    + intro Hs. exact (app_not_shadow x Happx (HshIS x Hs)).
    + intro Hf. destruct (Hfsp x Hf) as (_ & _ & HL). lia.
  - assert (Hb0 : 0 <= b)
      by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X|]; lia).
    assert (Hnb : ~ (fr <= b < fr + 3136))
      by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X|]; lia).
    assert (Happb : app_mem b).
    { destruct Hor as [Hi|Hr];
        [pose proof (img_below_GT b Hi) as X; unfold AC.GT, app_mem, LOWMEM_END in *; left; lia
        |unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia]. }
    pose proof (shadow_of_app b Happb) as Hsb.
    destruct (in_shadow_range (shadow_addr b) Hsb) as (R1 & R2).
    pose proof Hsb as Hsb'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsb'.
    apply Hreg.
    + lia.
    + lia.
    + intro Hf. exact (app_not_shadow (shadow_addr b) (Happfr _ Hf) Hsb).
    + exact (Hshfr b Hb0 Hnb).
    + intros (y & Hy & Heq). unfold shadow_addr in Heq.
      destruct Hor as [Hi|Hr].
      * pose proof (img_below_GT b Hi) as X. unfold AC.GT in X.
        assert (L : b / 8 < y / 8)
          by (apply (bp6_gran_lt b HIGHMEM_BEG y); unfold HIGHMEM_BEG; first [lia | reflexivity]).
        lia.
      * assert (L : y / 8 < b / 8) by (apply (bp6_gran_lt y Y b); lia).
        lia.
    + exact (HshNF _ Hsb).
    + intros (y & Hy & Heq). destruct (Hfsp y Hy) as (_ & HGy & Hyl). unfold AC.GT in HGy.
      unfold shadow_addr in Heq.
      destruct Hor as [Hi|Hr].
      * pose proof (img_below_GT b Hi) as X. unfold AC.GT in X.
        assert (L : b / 8 < y / 8) by (apply (bp6_gran_lt b 0x5fe000 y); first [lia | reflexivity]).
        lia.
      * assert (L : y / 8 < b / 8) by (apply bp6_div_lt; lia).
        lia.
  - destruct Hk5 as (q & k & i & Hin & Hni & Hi & ->). exact (HK5 q k i Hin Hni Hi).
Qed.

(* ENT across the same kind of run: Tac_slot.ent_store with the shadow of the slot window below the current sp and
   the side stack for frames added to the allowed address classes. Neither class holds an address ENT speaks of:
   the shadow of a window byte below sp (sp mod 16 = 0, sp <= S) is below the shadow of S and far above the shadow
   of the image, and the side stack lies below stklo <= S - SLOT_STACK, off the image and off every entry block.
   The bound is sp, not S: FRA does not state S mod 8 = 0, so the shadow byte of S - 1 may be the one of S. *)
Lemma bp6_ent_W : forall g fr hb regs mem mem' md W,
  ENT APIf g hb mem md -> FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' ->
  (forall q k i, In (q, k) (g_H g) -> ~ In (q, k) (g_T g) -> 0 <= i < k -> Frame.outside W (shadow_addr (q + i))) ->
  (forall x, 0 <= x < 2 ^ 64 -> Frame.outside W x \/ (g_S g - AF.SLOT_STACK <= x < g_S g) \/
     (fr <= x < fr + 3136) \/ (Sfr fr <= x < Sfr fr + 392) \/
     (exists y, g_S g - AF.SLOT_STACK <= y < AC.aspZ regs /\ x = shadow_addr y) \/
     AC.a_in_fs AC.ASYMS mem x \/ (exists y, AC.a_in_fs AC.ASYMS mem y /\ x = shadow_addr y)) ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, AC.a_in_img a ->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a ->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a) ->
  ENT APIf g hb mem' md.
Proof.
  intros g fr hb regs mem mem' md W HENT HFRA MU _ HK5 HWin Hlo Hhi Hown.
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & _ & _ & _ & _ & _ & _ & _ & Hspm & Haspz &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAS & Hspa & _).
  apply (bp6_ent_Wy g fr hb regs mem mem' md W (AC.aspZ regs) HENT HFRA MU HK5);
    [lia | | exact HWin | exact Hlo | exact Hhi | exact Hown].
  rewrite Haspz. clear -Hspm. Z.div_mod_to_equations. lia.
Qed.

End S.
