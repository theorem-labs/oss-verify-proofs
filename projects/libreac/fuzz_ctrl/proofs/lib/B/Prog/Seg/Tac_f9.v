(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v; 245 of its 338 lines of code are new or changed and 918 lines of the source are left out. *)
(* Two transports that segment F9 of LLVMFuzzerTestOneInput (image B, v1.9.0 0x82180-0x821e8) needs and that
   lib/B/Prog/Seg/Tac_slot.v does not carry, because the reac_ctrl_identity_reply call at 0x821e8 writes FIVE
   kinds of address at once: the three reply cells inside the frame body [fr + 256, fr + 312), its own stack
   window, the class-1 bytes of the side stack for frames, the shadow bytes of those class-1 frames, and the
   shadow bytes of its window.
     - sl_fr_run / sl_fr_meta want every write inside the frame body (or the frame's FRAME_SHADOW shadow bytes);
     - sl_win_run / sl_stk_run / sl_fr_cl want every write below sp (sl_fr_cl also wants all_app W, which the
       shadow range breaks);
     - sl_mid / ent_call want an AC.a_call_post, which the reac_ctrl_identity_reply contract does not state.
   f9_fr_cl is Tac_slot's sl_fr_cl with `all_app W` replaced by the shadow premise RT_meta_write needs, and with
   the two addressability conjuncts of FRA taken on mem' (the callee's own post restores its window's shadow).
   f9_ent_W is Tac_slot's ent_store with three more allowed address classes: the shadow of the slot window below
   the current sp, the side stack for frames, and the shadow of the side stack for frames. *)
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

(* FRA across a run whose writes W may include shadow bytes: RT by AsanRTInv.RT_meta_write (every shadow byte is
   readable after the run), the side arm's FakeStack record FSREC from the caller (as Tac_slot.sl_mid: the run
   writes class-1 FakeStack frames below stklo, so sl_fr_cl's fsrec_munch_lo route does not apply), the rest
   exactly as Tac_slot.sl_fr_cl. *)
Lemma f9_fr_cl : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  rt_disjoint W ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall x, 0 <= x < 6283264 -> Frame.outside W x) ->
  (forall x, fr <= x < fr + 24 -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
     forall x, A + 336 <= x < A + 344 -> Frame.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x) ->
  (forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x) ->
  (forall A, getr regs 9 = Z_to_bv 64 A -> 0 <= A < 2 ^ 64 ->
     forall x, A + 40 <= x < A + 56 -> Frame.outside W x) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  (forall x, g_p g <= x < g_p g + g_n g -> Frame.outside W x /\ Frame.outside W (shadow_addr x)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HSHR HAH' HSTK HWlo HWhdr HWspill HWsaved HWsh
    HWsel HWwin HAG' HWA' HREC HWin E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by lia. exact (HWlo x ltac:(lia)). }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HSHR)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo;
          [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo;
          [lia | rewrite Hlock in Hx; cbn in Hx; lia].
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
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
  split; [exact HA448|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr40 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A Hr9 HA64 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split; [|split].
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + exact (HREC Hrec). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
    eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen, Z2Nat.id by lia. intros x Hx.
    exact (HWsh x ltac:(lia)). }
  split; [exact HWwin|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|].
  exact (fra_in_keep_sh g mem mem' W Hinb Hinblk MU HWin).
Qed.

(* y < Y <= b with Y a multiple of 8: y and b lie in different 8-byte granules, so their shadow bytes differ. *)
Local Lemma f9_gran_lt : forall y Y b, 0 <= y -> y < Y -> Y <= b -> Y mod 8 = 0 -> y / 8 < b / 8.
Proof. intros y Y b H0 H1 H2 H3. Z.div_mod_to_equations. lia. Qed.

(* f9_ent_W for the shadow of the slot-window bytes below a granule boundary Y <= S: the shadow byte of such a byte
   is never the shadow byte of a byte at or above S, nor of an image byte (image < GT <= HIGHMEM_BEG <= the
   window). The side stack lies in app memory (a_laws_fs_place), at or above GT and below stklo <= S - SLOT_STACK,
   so it is apart from the image, from [S, APPMEM_END) and from every shadow byte; an entry block is not side
   stack (a_laws_blocks). The shadow byte of a side-stack byte is the same way apart: above the shadow of the
   image (GT mod 8 = 0) and below the shadow of S (at least SLOT_STACK bytes apart).
   v1.9 (ent_kept's fifth class, the entry blocks' shadow bytes): an entry block ends at or below stklo <=
   S - SLOT_STACK, so a window byte at or above S - SLOT_STACK + 8 is in a later granule (the window class starts
   8 bytes up for that: FRA does not make stklo a granule boundary); the side stack is granule-aligned
   (b mod 4096 = 0, FS_SIZE mod 8 = 0) and an entry-block byte is not side stack, so their granules differ too;
   the frame and its shadow as Tac_slot's ent_shadow_store. *)
Local Lemma f9_ent_Wy : forall g fr hb regs mem mem' md W Y,
  ENT APIf g hb mem md -> FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Y <= g_S g -> Y mod 8 = 0 ->
  (forall x, 0 <= x < 2 ^ 64 -> Frame.outside W x \/ (g_S g - AF.SLOT_STACK <= x < g_S g) \/
     (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) \/
     (exists y, g_S g - AF.SLOT_STACK + 8 <= y < Y /\ x = shadow_addr y) \/
     AC.a_in_fs AC.ASYMS mem x \/ (exists y, AC.a_in_fs AC.ASYMS mem y /\ x = shadow_addr y)) ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, AC.a_in_img a ->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a ->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a) ->
  ENT APIf g hb mem' md.
Proof.
  intros g fr hb regs mem mem' md W Y HENT HFRA MU HYS HY8 HWin Hlo Hhi Hown.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGTfr & Happfr).
  pose proof HENT as (Hasp & _).
  assert (HS0 : 0 <= g_S g) by (rewrite <- Hasp; apply (bv_unsigned_in_range 64)).
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 &
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
  (* every byte of the frame's FRAME_SHADOW shadow bytes is the shadow byte of a frame byte *)
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
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
  assert (Hnsy : forall x, app_mem x -> ~ (exists y, g_S g - AF.SLOT_STACK + 8 <= y < Y /\ x = shadow_addr y)).
  { intros x Hx (y & Hy & ->). exact (app_not_shadow _ Hx (shadow_of_app y (HSY y ltac:(lia)))). }
  assert (HshNF : forall x, in_shadow x -> ~ AC.a_in_fs AC.ASYMS mem x).
  { intros x Hs Hf. exact (app_not_shadow x (proj1 (Hfsp x Hf)) Hs). }
  assert (Hnfsh : forall x, app_mem x -> ~ (exists y, AC.a_in_fs AC.ASYMS mem y /\ x = shadow_addr y)).
  { intros x Hx (y & Hy & ->). exact (app_not_shadow _ Hx (shadow_of_app y (proj1 (Hfsp y Hy)))). }
  (* an address in none of the seven classes is outside W *)
  assert (Hreg : forall x, 0 <= x < 2 ^ 64 -> ~ (g_S g - AF.SLOT_STACK <= x < g_S g) ->
            ~ (fr <= x < fr + FRAME_BYTES) -> ~ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) ->
            ~ (exists y, g_S g - AF.SLOT_STACK + 8 <= y < Y /\ x = shadow_addr y) ->
            ~ AC.a_in_fs AC.ASYMS mem x ->
            ~ (exists y, AC.a_in_fs AC.ASYMS mem y /\ x = shadow_addr y) -> Frame.outside W x).
  { intros x Hx H1 H2 H3 H4 H5 H6. destruct (HWin x Hx) as [Ho|[Hw|[Hf|[Hs|[Hy|[Hfs|Hfsy]]]]]];
      [exact Ho | contradiction | contradiction | contradiction | contradiction | contradiction | contradiction]. }
  (* a byte of the frame's shadow is the shadow of a frame byte, so it is not the shadow of an image byte or of
     a byte at or above S *)
  assert (Hshfr : forall b, 0 <= b -> ~ (fr <= b < fr + FRAME_BYTES) ->
            ~ (Sfr fr <= shadow_addr b < Sfr fr + FRAME_SHADOW)).
  { intros b Hb0 Hnb Hin. apply Hnb. unfold Sfr, shadow_addr in Hin.
    revert Hin Hfr8 Hb0 Hfr0. rewrite FRAME_SHADOW_val, FRAME_BYTES_val. clear. intros.
    Z.div_mod_to_equations. lia. }
  (* ent_kept's fifth class: the entry blocks' shadow bytes are none of the seven classes *)
  assert (Hshd_out : forall q k i, In (q, k) (g_H g) -> ~ In (q, k) (g_T g) -> 0 <= i < k ->
            Frame.outside W (shadow_addr (q + i))).
  { intros q k i Hin Hni Hi.
    destruct (lw_blocks (APIf rc) (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin)))
      as [_ _ Hend _ Hall].
    destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
    assert (Hb0 : 0 <= q + i) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
    assert (Hnb : ~ (fr <= q + i < fr + FRAME_BYTES)).
    { intro Hf. destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0' [Hfsb [Hfs _]]]].
      - destruct (Hreal (q + i) Hf) as (Hr1 & _). lia.
      - exact (Hnfs (Hfs (q + i) Hf)). }
    pose proof (shadow_of_app (q + i) Happq) as Hsb.
    destruct (in_shadow_range (shadow_addr (q + i)) Hsb) as (R1 & R2).
    pose proof Hsb as Hsb'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsb'.
    apply Hreg.
    - lia.
    - lia.
    - intro Hf. exact (app_not_shadow (shadow_addr (q + i)) (Happfr _ Hf) Hsb).
    - exact (Hshfr (q + i) Hb0 Hnb).
    - intros (y & Hy & Heq). unfold shadow_addr in Heq.
      assert (L : (q + i) / 8 < y / 8) by (apply (f9_gran_lt (q + i) (q + i + 8 - (q + i) mod 8) y);
        Z.div_mod_to_equations; lia).
      lia.
    - exact (HshNF _ Hsb).
    - intros (y & (b & Hb & Hwm & Hy) & Heq). apply Hnfs. exists b.
      split; [exact Hb|]. split; [exact Hwm|].
      destruct (lw_fs_place (APIf rc) (hb ++ g_H g) mem md b HAH Hwm Hb) as [_ _ Hb4k _].
      assert (HFS : AC.FS_SIZE = 11571200) by reflexivity.
      unfold shadow_addr in Heq. clear -Heq Hb4k HFS Hy Hb0 Hb.
      Z.div_mod_to_equations. lia. }
  apply (ent_munch APIf g hb mem mem' md W HENT HAH MU); [| exact Hlo | exact Hhi | exact Hown].
  intros x Hk.
  destruct Hk as [Hblkk | [Hik | [Habk | [(b & Hor & ->) | (q & k & i & Hin & Hni & Hi & ->)]]]];
    [| | | | exact (Hshd_out q k i Hin Hni Hi)].
  - destruct Hblkk as (q & k & i & Hin & Hni & Hi & ->).
    destruct (lw_blocks (APIf rc) (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin)))
      as [_ _ Hend _ Hall].
    destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
    assert (Hqr : 0 <= q + i < 2 ^ 64)
      by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Happq; lia).
    apply Hreg; [exact Hqr | lia | | | exact (Hnsy _ Happq) | exact Hnfs | exact (Hnfsh _ Happq)].
    + intro Hf. destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0' [Hfsb [Hfs _]]]].
      * destruct (Hreal (q + i) Hf) as (Hr1 & _). lia.
      * exact (Hnfs (Hfs (q + i) Hf)).
    + intro Hs. exact (app_not_shadow (q + i) Happq (HshIS (q + i) Hs)).
  - pose proof (img_below_GT x Hik) as Hxg. unfold AC.GT in Hxg.
    assert (Happx : app_mem x) by (unfold app_mem, LOWMEM_END; left; lia).
    apply Hreg; [lia | lia | lia | | exact (Hnsy x Happx) | | exact (Hnfsh x Happx)].
    + intro Hs. exact (app_not_shadow x Happx (HshIS x Hs)).
    + intro Hf. destruct (Hfsp x Hf) as (_ & HG & _). unfold AC.GT in HG. lia.
  - assert (Happx : app_mem x) by (unfold app_mem, HIGHMEM_BEG, APPMEM_END in *; right; lia).
    apply Hreg; [lia | lia | lia | | exact (Hnsy x Happx) | | exact (Hnfsh x Happx)].
    + intro Hs. exact (app_not_shadow x Happx (HshIS x Hs)).
    + intro Hf. destruct (Hfsp x Hf) as (_ & _ & HL). lia.
  - assert (Hb0 : 0 <= b)
      by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X; unfold AC.GT in X|]; lia).
    assert (Hnb : ~ (fr <= b < fr + FRAME_BYTES))
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
          by (apply (f9_gran_lt b HIGHMEM_BEG y); unfold HIGHMEM_BEG; first [lia | reflexivity]).
        lia.
      * assert (L : y / 8 < b / 8) by (apply (f9_gran_lt y Y b); lia).
        lia.
    + exact (HshNF _ Hsb).
    + intros (y & Hy & Heq). destruct (Hfsp y Hy) as (_ & HGy & HLy). unfold shadow_addr in Heq.
      unfold AC.GT in HGy.
      destruct Hor as [Hi|Hr].
      * pose proof (img_below_GT b Hi) as X. unfold AC.GT in X.
        assert (L : b / 8 < y / 8) by (apply (f9_gran_lt b 6283264 y); first [lia | reflexivity]).
        lia.
      * assert (L : y / 8 < b / 8) by (clear -Hr HLy HSS HGy; Z.div_mod_to_equations; lia).
        lia.
Qed.

(* ENT across the same kind of run: Tac_slot.ent_store with the shadow of the slot window below the current sp and
   the side stack for frames added to the allowed address classes. Neither class holds an address ENT speaks of:
   the shadow of a window byte below sp (sp mod 16 = 0, sp <= S) is below the shadow of S and far above the shadow
   of the image, and the side stack lies below stklo <= S - SLOT_STACK, off the image and off every entry block.
   The bound is sp, not S: FRA does not state S mod 8 = 0, so the shadow byte of S - 1 may be the one of S. The
   window class starts at S - SLOT_STACK + 8 (f9_ent_Wy: an entry block ends at or below stklo, which FRA does not
   make a granule boundary). *)
Lemma f9_ent_W : forall g fr hb regs mem mem' md W,
  ENT APIf g hb mem md -> FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' ->
  (forall x, 0 <= x < 2 ^ 64 -> Frame.outside W x \/ (g_S g - AF.SLOT_STACK <= x < g_S g) \/
     (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) \/
     (exists y, g_S g - AF.SLOT_STACK + 8 <= y < AC.aspZ regs /\ x = shadow_addr y) \/
     AC.a_in_fs AC.ASYMS mem x \/ (exists y, AC.a_in_fs AC.ASYMS mem y /\ x = shadow_addr y)) ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, AC.a_in_img a ->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a ->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a) ->
  ENT APIf g hb mem' md.
Proof.
  intros g fr hb regs mem mem' md W HENT HFRA MU _ HWin Hlo Hhi Hown.
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & _ & _ & _ & _ & _ & _ & _ & Hspm & Haspz &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAS & Hspa & _).
  apply (f9_ent_Wy g fr hb regs mem mem' md W (AC.aspZ regs) HENT HFRA MU);
    [lia | | exact HWin | exact Hlo | exact Hhi | exact Hown].
  rewrite Haspz. clear -Hspm. Z.div_mod_to_equations. lia.
Qed.

End S.
