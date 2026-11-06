(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 405 of its 499 lines of code are new or changed and 917 lines of the source are left out. *)
(* FRA / ENT transport for image-B segment P12 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, libreac v1.9.0
   image B; lib/B/Prog/Seg/P12.v): the frame-loop prologue 0x81e50-0x81ec0 writes seven spills of the save area
   [A + 88, A + 264) and eight frame shadow bytes S(fr) + 370 .. 385, so its write set has two kinds of address.
   Tac_slot's sl_fr_meta takes only the frame body and its shadow, sl_stk_run only addresses outside both; one
   transport, tp_fra_ent, takes the frame body above the header, the frame's FRAME_SHADOW shadow bytes, a callee
   window below sp and the save area [A + 72, A + 336) (above the fr reload / selector cells [A + 40, A + 56)).
   tp_fra_run / tp_fra_ent and the memory helpers below are a copy of prover a Theorem Labs lane's lib/B/Prog/Seg/Tac_f23.v
   tf_fra_run / tf_fra_ent (a working branch 0bebaf13c4e; tf_fra_run is lib/B/Prog/Seg/F12.v's fra_run), copied
   here because Tac_f23.v imports the segment file F27.v; v1.9.0 move of a working branch 509cbbd9bd1. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Exec.
Import ListNotations.
(* lib/Lib's chain may load lib/Reusable/YK11.v, so the short name YK11 could resolve to that copy; the registers
   and FPState here must be image B's, as SlotInv's are (lib/B/Prog/Seg/F26.v). *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module BZB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.BzBridge.
Module UEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Exec.
Module LEx := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.


(* ---- memory helpers (lib/B/Prog/Seg/F12.v) ---- *)

Lemma tp_outside_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; cbn [outside]; intros x; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [Hl|Hl]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [Hh|Hh]; [right; intros (C & _); lia | left; split; [lia | exact H]].
Qed.

Lemma tp_ba_rd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (HA & HL & H) Hx.
  assert (Hi : (Z.to_nat (x - A) < length bs)%nat) by lia.
  pose proof (H (Z.to_nat (x - A)) Hi) as HH. rewrite Z2Nat.id in HH by lia.
  replace (A + (x - A)) with x in HH by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:E; [exists b; exact HH|].
  exfalso. apply nth_error_None in E. lia.
Qed.

(* A stack window survives a run with write set W: outside W the bytes are unchanged, inside W the caller shows
   the post memory is readable. *)
Lemma tp_stk_keep : forall W m m' lo hi,
  stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> ~ outside W x -> exists b, mrd rsegs m' (wa x) = Some b) ->
  stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM HR.
  split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hv & b & Hb).
  split; [apply WM; exact Hv|].
  destruct (tp_outside_dec W a) as [Ho|Ho].
  - exists b. unfold mrd in *. rewrite (MU (wa a)) by (rewrite wa_unsigned by lia; exact Ho). exact Hb.
  - exact (HR a Ha Ho).
Qed.

(* shadow_addr on an 8-aligned base: monotone, and a frame offset gives a shadow index. *)
Lemma tp_sh_ge : forall fr x c, fr mod 8 = 0 -> 0 <= fr -> fr + 8 * c <= x -> Sfr fr + c <= shadow_addr x.
Proof. intros fr x c H8 Hfr Hx. unfold Sfr, shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. Qed.

Lemma tp_sh_lt : forall fr x c, fr mod 8 = 0 -> 0 <= fr -> 0 <= x -> x < fr + 8 * c -> shadow_addr x < Sfr fr + c.
Proof. intros fr x c H8 Hfr Hx0 Hx. unfold Sfr, shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. Qed.

(* A byte whose shadow byte is one of the frame's FRAME_SHADOW lies in the frame. *)
Lemma tp_sh_back : forall fr x, fr mod 8 = 0 -> 0 <= fr -> 0 <= x ->
  Sfr fr <= shadow_addr x < Sfr fr + FRAME_SHADOW -> fr <= x < fr + FRAME_BYTES.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr x H8 Hfr Hx0 Hx. unfold Sfr, shadow_addr, ASAN_K in Hx. Z.div_mod_to_equations. lia.
Qed.

(* Z_to_bv 64 is injective on [0, 2^64): the spill base read twice is the same base. *)
Lemma tp_spill_base : forall regs A A' m off v,
  rg regs 9 A -> rg regs 9 A' -> 0 <= A < APPMEM_END -> 0 <= off <= 440 -> q64 m (A' + off) v -> A' = A.
Proof.
  intros regs A A' m off v HA HA' HAb Hoff Hq.
  pose proof (rg_eq64 _ _ _ _ HA' HA) as Hm.
  unfold q64, bytes_at in Hq. destruct Hq as (Hq0 & Hq1 & _).
  rewrite length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
  unfold APPMEM_END in HAb. change (2 ^ 64) with 18446744073709551616 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* A spill of the save area survives a run whose write set misses its cell. *)
Lemma tp_spill_keep : forall regs regs' m m' W A off v,
  rg regs 9 A -> getr regs' 9 = getr regs 9 -> 0 <= A < APPMEM_END -> 0 <= off <= 440 ->
  spill regs m off v -> munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> outside W x) -> spill regs' m' off v.
Proof.
  intros regs regs' m m' W A off v H9 E9 HAb Hoff (A3 & HA3 & Hq) MU Hout.
  pose proof (tp_spill_base regs A A3 m off v H9 HA3 HAb Hoff Hq) as EA. subst A3.
  exists A. split; [unfold rg in *; rewrite E9; exact H9|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
  rewrite length_le8. intros x Hx. apply Hout. lia.
Qed.

(* A spill read at the cut's own base. *)
Lemma tp_spill_q : forall regs m A off v, rg regs 9 A -> 0 <= A < APPMEM_END -> 0 <= off <= 440 ->
  spill regs m off v -> q64 m (A + off) v.
Proof.
  intros regs m A off v H9 HAb Hoff (A3 & HA3 & Hq).
  pose proof (tp_spill_base regs A A3 m off v H9 HA3 HAb Hoff Hq) as EA. subst A3. exact Hq.
Qed.

(* addressable survives writes that miss the shadow bytes of its own range. *)
Lemma tp_addr_munch : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) MU HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (shadow_of_app (p + i) Hap) as His.
  assert (Hr : 0 <= shadow_addr (p + i) < 2 ^ 64)
    by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in His; lia).
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. exact (HW i Hi).
Qed.

(* Build a list from a function defined on [0, n). *)
Lemma tp_ex_list : forall (f : nat -> option byte) n, (forall i, (i < n)%nat -> f i <> None) ->
  exists l, length l = n /\ forall i, (i < n)%nat -> f i = nth_error l i.
Proof.
  intros f n. induction n as [|n IH]; intros H.
  - exists []. split; [reflexivity|]. intros i Hi. lia.
  - assert (H' : forall i, (i < n)%nat -> f i <> None) by (intros i Hi; apply H; lia).
    destruct (IH H') as (l & Hl & Hf).
    destruct (f n) as [b|] eqn:Eb; [|exfalso; exact (H n ltac:(lia) Eb)].
    exists (l ++ [b]). split; [rewrite length_app, Hl; cbn; lia|].
    intros i Hi. destruct (Nat.lt_ge_cases i n) as [Hlt|Hge].
    + rewrite nth_error_app1 by lia. exact (Hf i Hlt).
    + assert (Ei : i = n) by lia. subst i.
      rewrite nth_error_app2 by lia. rewrite Hl, Nat.sub_diag. cbn. exact Eb.
Qed.

(* The frame's FRAME_SHADOW shadow bytes, readable in a memory, form a FRAME_SHADOW-byte list there. *)
Lemma tp_shF : forall fr mem',
  LOWMEM_END <= Sfr fr -> Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG ->
  (forall i, 0 <= i < FRAME_SHADOW -> exists b, mrd rsegs mem' (wa (Sfr fr + i)) = Some b) ->
  exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW.
Proof.
  pose proof FRAME_SHADOW_val as HFSv.
  intros fr mem' H1 H2 Hrd. rewrite HFSv in *. change (Z.to_nat 392) with 392%nat.
  assert (Hsome : forall i, (i < 392)%nat -> mrd rsegs mem' (wa (Sfr fr + Z.of_nat i)) <> None).
  { intros i Hi. destruct (Hrd (Z.of_nat i) ltac:(lia)) as (b & Hb). rewrite Hb. discriminate. }
  destruct (tp_ex_list (fun i => mrd rsegs mem' (wa (Sfr fr + Z.of_nat i))) 392 Hsome) as (l & Hl & Hf).
  exists l. split; [|exact Hl]. split; [unfold LOWMEM_END in *; lia|].
  split; [rewrite Hl; unfold HIGHMEM_BEG in *; lia|].
  intros i Hi. rewrite Hl in Hi. exact (Hf i Hi).
Qed.

(* The side stack's metadata region starts at its base (the companion of Tac_fs.fs_meta_below). *)
Lemma tp_fs_meta_above : forall FS q, fs_meta FS q -> FS <= q.
Proof.
  intros FS q H. unfold fs_meta in H.
  destruct H as [H | [H | [ (c & Hc & Hr) | (c & jj & Hc & Hj & Heq) ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. assert (Z.of_nat c <= 10)%Z by lia. lia.
  - subst q. exact (proj1 (Tac_fs.a_fs_flag_range FS c jj Hc Hj)).
Qed.

Section TP.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* FRA transports across a memory change (mem -> mem'), at a fixed md and fixed registers, whose write set W misses
   the frame header [fr, fr + 24), the spills s1+336 / s1+40..56 (the fr reload and selector cells), the saved
   registers [S - 104, S) and the low image [0, AC.GT) (lib/B/Prog/Seg/F12.v fra_run). *)
Lemma tp_fra_run : forall g fr hb regs mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  munch W mem mem' -> wmono rsegs mem mem' ->
  rt_disjoint W -> ro_agree rsegs mem' ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall x, fr <= x < fr + 24 -> outside W x) ->
  (forall A, 0 <= A < 2 ^ 64 -> getr regs 9 = Z_to_bv 64 A ->
     forall x, A + 336 <= x < A + 344 -> outside W x) ->
  (forall A, 0 <= A < 2 ^ 64 -> getr regs 9 = Z_to_bv 64 A ->
     forall x, A + 40 <= x < A + 56 -> outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> outside W x) ->
  (forall x, 0 <= x < AC.GT -> outside W x) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  (forall x, app_mem x -> x < AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
     ~ (fr <= x < fr + FRAME_BYTES) -> outside W x) ->
  (forall x, g_p g <= x < g_p g + g_n g -> outside W x /\ outside W (shadow_addr x)) ->
  FRA B APIf ra g fr hb regs mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem mem' md W HFRA MU WM HD HRO' HshR HAH' HSTK HWIN' Hshnew HAG'
    HWhdr HWspill HWsel HWsaved HWlow HWA' HWfs HWin.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by (unfold AC.GT in *; lia).
      apply HWlow. unfold AC.GT. lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HshR)|].
  split; [exact HAH'|].
  split; [exact HRO'|].
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
  split; [exact Hr2|].
  split; [exact Hspm|].
  split; [exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [exact Hr4|].
  split; [exact Hr8|].
  split; [exact Hr9|].
  split; [exact Hr3|].
  split; [exact Hr19|].
  split; [exact Hr26|].
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
    rewrite length_le8. intros x Hx. exact (HWspill A HA64 Hr9 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A HA64 Hr9 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr56 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel A HA64 Hr9 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split; [|split].
      + intros FS Hw HFSr. apply (Hfsb FS); [|exact HFSr].
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
      + eapply fsrec_keep_app_lo with (W := W); [exact Hrec | exact HAH | exact MU | exact HWfs]. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split; [exact Hshnew|].
  split; [exact HWIN'|].
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

(* FRA and ENT across a write set W of the window's kind.  Every address W holds is a frame body byte above the
   header [fr + 24, fr + FRAME_BYTES), one of the frame's FRAME_SHADOW shadow bytes, a byte of a callee's
   stack window [sp - FN_STACK, sp), or a spill of the save area between the fr reload / selector cells and the
   fr spill, [A + 72, A + 336) with A = s1; and the post memory is readable at each of them.  Then:
   - the heap invariant, the ownership of every byte and the two stack bounds move by a_laws_store (real arm: all
     four kinds are a_store_ok, the frame and the window being above stklo, the shadow bytes being the frame's) or
     by Tac_fs.a_fs_ok_store_AH (side arm: the frame and its shadow are side-stack bytes, the window and the save
     area are above stklo, and the side stack's metadata is below the frame);
   - FRA moves by tp_fra_run: the runtime's shadow map stays readable, the entry-anchored window and the frame's
     FRAME_SHADOW shadow bytes are rebuilt from the readable post, the registered globals and the window's bytes outside the
     frame keep their shadow bytes (theirs are not the frame's), and no app byte below stklo outside the frame
     (FSREC, the input block) or shadow byte of one is written;
   - ENT moves by Tac_slot.ent_store: each written byte is in the slot window [S - SLOT_STACK, S), in the frame or
     in the frame's shadow. *)
Lemma tp_fra_ent : forall g fr hb regs mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  ENT APIf g hb mem md ->
  munch W mem mem' -> wmono rsegs mem mem' ->
  rt_disjoint W -> ro_agree rsegs mem' ->
  (forall q, ~ outside W q ->
     (fr + 24 <= q < fr + FRAME_BYTES) \/ (Sfr fr <= q < Sfr fr + FRAME_SHADOW) \/
     (AC.aspZ regs - FN_STACK <= q < AC.aspZ regs) \/
     (bv_unsigned (getr regs 9) + 72 <= q < bv_unsigned (getr regs 9) + 336)) ->
  (forall q, ~ outside W q -> exists b, mrd rsegs mem' (wa q) = Some b) ->
  FRA B APIf ra g fr hb regs mem' md /\ ENT APIf g hb mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem mem' md W HFRA HENT MU WM HD HRO' HCL HRD.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  destruct (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hplace & HfrA & Hfsmeta & _).
  destruct (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  pose proof (fra_in_apart B APIf ra g fr hb regs mem md HFRA) as Hinap.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspillq & Hselq & Hfr56q & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof HRT as HRT0. destruct HRT0 as (HAC0 & HSW0 & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HFSsz : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (unfold stk in Hwin; split; [apply (proj1 Hwin) | apply (proj1 (proj2 Hwin))]).
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; lia).
  rewrite HbvA in HCL, HfrA.
  rewrite Haspz in HCL, Hwlo, Hplace.
  assert (Hhigh : HIGHMEM_BEG <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md)
    by exact (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH).
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (Hfrb : 0 <= fr /\ fr + FRAME_BYTES < 2 ^ 64).
  { pose proof (Happ fr ltac:(lia)) as H1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in H1, H2. lia. }
  assert (Hfr8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
  (* the frame's FRAME_SHADOW shadow bytes are shadow addresses, below the high application memory *)
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  assert (HK3b : LOWMEM_END <= Sfr fr /\ Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { pose proof (HshIS (Sfr fr) ltac:(lia)) as H1. pose proof (HshIS (Sfr fr + FRAME_SHADOW - 1) ltac:(lia)) as H2.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in H1, H2.
    unfold LOWMEM_END, HIGHMEM_BEG. lia. }
  (* the addresses W misses *)
  assert (Hout : forall q, (q < fr + 24 \/ fr + FRAME_BYTES <= q) -> (q < Sfr fr \/ Sfr fr + FRAME_SHADOW <= q) ->
            (q < sp - FN_STACK \/ sp <= q) -> (q < A + 72 \/ A + 336 <= q) -> outside W q).
  { intros q H1 H2 H3 H4. destruct (tp_outside_dec W q) as [Ho|Ho]; [exact Ho|].
    exfalso. destruct (HCL q Ho) as [C|[C|[C|C]]]; lia. }
  assert (HoutSh : forall x, in_shadow x -> ~ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) -> outside W x).
  { intros x Hin Hn. apply Hout.
    - destruct (Z_lt_le_dec x (fr + 24)) as [H1|H1]; [left; exact H1|].
      destruct (Z_lt_le_dec x (fr + FRAME_BYTES)) as [H2|H2]; [|right; exact H2].
      exfalso. exact (app_not_shadow x (Happ x ltac:(lia)) Hin).
    - lia.
    - left. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hin. lia.
    - left. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hin. lia. }
  assert (HoutApp : forall x, app_mem x -> ~ (fr <= x < fr + FRAME_BYTES) -> x < sp - FN_STACK -> outside W x).
  { intros x Hap Hn Hlo. apply Hout.
    - lia.
    - destruct (Z_lt_le_dec x (Sfr fr)) as [H1|H1]; [left; exact H1|].
      destruct (Z_lt_le_dec x (Sfr fr + FRAME_SHADOW)) as [H2|H2]; [|right; exact H2].
      exfalso. exact (app_not_shadow x Hap (HshIS x ltac:(lia))).
    - left. exact Hlo.
    - left. lia. }
  assert (Hwmon : forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q)
    by (intros q Hqb Hw; exact (WM (Z_to_bv 64 q) Hw)).
  (* AH, ownership and the two stack bounds across the write set, by arm *)
  assert (HAHSTK : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
                   (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a
                      <-> AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a) /\
                   AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                     = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                   AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                     = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { destruct Hloc as [[Hs50 [Hspfr Hreal]]|[Hs5fr [Hfsb [Hfs _]]]].
    - (* real arm: the frame body, its shadow, the callee window and the save area are all a_store_ok *)
      assert (Hmc : forall q, 0 <= q < 2 ^ 64 ->
                ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
      { intros q Hq Hns. apply MU. rewrite MState.unsigned_lit by exact Hq.
        apply Hout.
        - destruct (Z_lt_le_dec q (fr + 24)) as [Hl|Hg]; [left; exact Hl|].
          destruct (Z_lt_le_dec q (fr + FRAME_BYTES)) as [Hl2|Hg2]; [|right; exact Hg2].
          exfalso. apply Hns. right. left. specialize (Hreal q ltac:(lia)). lia.
        - destruct (Z_lt_le_dec q (Sfr fr)) as [Hl|Hg]; [left; exact Hl|].
          destruct (Z_lt_le_dec q (Sfr fr + FRAME_SHADOW)) as [Hl2|Hg2]; [|right; exact Hg2].
          exfalso. apply Hns. right. right. right.
          exists (fr + 8 * (q - Sfr fr)). split.
          + unfold shadow_addr.
            replace (fr + 8 * (q - Sfr fr)) with ((q - Sfr fr) * 8 + (fr / 8) * 8)
              by (Z.div_mod_to_equations; lia).
            rewrite Z.div_add by lia. rewrite Z.div_mul by lia. unfold Sfr, shadow_addr. lia.
          + right. left. specialize (Hreal (fr + 8 * (q - Sfr fr)) ltac:(lia)). lia.
        - destruct (Z_lt_le_dec q (sp - FN_STACK)) as [Hl|Hg]; [left; exact Hl|].
          destruct (Z_lt_le_dec q sp) as [Hl2|Hg2]; [|right; exact Hg2].
          exfalso. apply Hns. right. left. lia.
        - destruct (Z_lt_le_dec q (A + 72)) as [Hl|Hg]; [left; exact Hl|].
          destruct (Z_lt_le_dec q (A + 336)) as [Hl2|Hg2]; [|right; exact Hg2].
          exfalso. apply Hns. right. left. lia. }
      destruct (lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH Hmc Hwmon)
        as [HAH2 Hown2 Hstk2 Hhi2].
      split; [exact HAH2|]. split; [exact Hown2|]. split; [exact Hstk2 | exact Hhi2].
    - (* side arm: the frame body and its shadow belong to the side stack for frames *)
      destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FSc & HFScr & HwFSc & HFSlo & HFShi).
      destruct (lw_fs_place (APIf rc) (hb ++ g_H g) mem md FSc HAH HwFSc HFScr)
        as [HFSgt HFSend _ HFSapp].
      pose proof (Hfsmeta FSc HwFSc HFScr) as HFSmeta.
      assert (Hstore : forall q, 0 <= q < 2 ^ 64 ->
                ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                ~ (FSc <= q < FSc + AC.FS_SIZE) ->
                ~ (exists b, FSc <= b < FSc + AC.FS_SIZE /\ q = shadow_addr b) ->
                mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
      { intros q Hq Hns Hnfs Hnsh. apply MU. rewrite MState.unsigned_lit by exact Hq.
        apply Hout.
        - destruct (Z_lt_le_dec q (fr + 24)) as [Hl|Hg]; [left; exact Hl|].
          destruct (Z_lt_le_dec q (fr + FRAME_BYTES)) as [Hl2|Hg2]; [|right; exact Hg2].
          exfalso. apply Hnfs. lia.
        - destruct (Z_lt_le_dec q (Sfr fr)) as [Hl|Hg]; [left; exact Hl|].
          destruct (Z_lt_le_dec q (Sfr fr + FRAME_SHADOW)) as [Hl2|Hg2]; [|right; exact Hg2].
          exfalso. apply Hnsh. exists (fr + 8 * (q - Sfr fr)). split; [lia|].
          unfold shadow_addr.
          replace (fr + 8 * (q - Sfr fr)) with ((q - Sfr fr) * 8 + (fr / 8) * 8)
            by (Z.div_mod_to_equations; lia).
          rewrite Z.div_add by lia. rewrite Z.div_mul by lia. unfold Sfr, shadow_addr. lia.
        - destruct (Z_lt_le_dec q (sp - FN_STACK)) as [Hl|Hg]; [left; exact Hl|].
          destruct (Z_lt_le_dec q sp) as [Hl2|Hg2]; [|right; exact Hg2].
          exfalso. apply Hns. right. left. lia.
        - destruct (Z_lt_le_dec q (A + 72)) as [Hl|Hg]; [left; exact Hl|].
          destruct (Z_lt_le_dec q (A + 336)) as [Hl2|Hg2]; [|right; exact Hg2].
          exfalso. apply Hns. right. left. lia. }
      assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                (exists b, mbyte rsegs mem' q = Some b)).
      { intros q Hq Hb.
        destruct (tp_outside_dec W q) as [Ho|Ho].
        - unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
          rewrite MState.unsigned_lit by exact Hq. exact Ho.
        - destruct (HRD q Ho) as (b2 & Hb2). unfold mbyte, mrd, wa in *.
          destruct (mem' (Z_to_bv 64 q)) as [b'|] eqn:Em; [exists b'; reflexivity | exists b2; exact Hb2]. }
      destruct (Tac_fs.a_fs_ok_store_AH AC.ASYMS _ _ _ _ W (hb ++ g_H g) mem mem' md FSc
                  LAWS HAH HwFSc HFScr ltac:(unfold APPMEM_END in *; lia) MU Hwmon Hpres
                  ltac:(intros q Hq; pose proof (Tac_fs.fs_meta_below FSc q Hq) as HB';
                        pose proof (tp_fs_meta_above FSc q Hq) as HB2';
                        pose proof (HFSapp q ltac:(lia)) as Hapq;
                        apply HoutApp; [exact Hapq | lia | lia])
                  Hstore)
        as (HAH2 & Hown2 & Hstk2 & Hhi2).
      split; [exact HAH2|]. split; [exact Hown2|]. split; [exact Hstk2 | exact Hhi2]. }
  destruct HAHSTK as (HAH2 & Hown2 & Hstk2 & Hhi2).
  (* the runtime's shadow map stays readable *)
  assert (HshR : forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b).
  { intros a Hin. destruct (tp_outside_dec W a) as [Ho|Ho]; [|exact (HRD a Ho)].
    destruct (HSW0 a Hin) as (_ & b & Hb). exists b. unfold mrd in *.
    assert (Hab : 0 <= a < 2 ^ 64)
      by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin; lia).
    rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho. }
  assert (HFRA' : FRA B APIf ra g fr hb regs mem' md).
  { apply (tp_fra_run g fr hb regs mem mem' md W HFRA MU WM HD HRO' HshR HAH2 Hstk2).
    - apply (tp_stk_keep W mem mem' _ _ Hwin MU WM). intros x _ Ho. exact (HRD x Ho).
    - apply (tp_shF fr mem' (proj1 HK3b) (proj2 HK3b)). intros i Hi. apply HshR. apply HshIS. lia.
    - intros a Hin. pose proof (HAG a Hin) as HA1. pose proof HA1 as HA2.
      apply (tp_addr_munch W mem mem' a 1 HA1 MU).
      intros i Hi. destruct HA2 as (Ha0 & _ & _ & HAb1). destruct (HAb1 i Hi) as (Hap & _).
      replace (a + i) with a in * by lia.
      assert (Haglow : a < AC.GT).
      { destruct Hin as (lo2 & len2 & Hil & Hr2'). unfold AF.frame_AG in Hil. cbn in Hil.
        unfold AC.GT. repeat (destruct Hil as [E|Hil]; [injection E as <- <-; lia|]). destruct Hil. }
      apply HoutSh; [apply shadow_of_app; exact Hap|].
      pose proof (tp_sh_lt fr a 0 Hfr8 ltac:(lia) ltac:(lia) ltac:(lia)) as Hlt. lia.
    - intros x Hx. apply Hout; [lia | | | left; lia].
      + destruct (Z_lt_le_dec x (Sfr fr)) as [H1|H1]; [left; exact H1|].
        destruct (Z_lt_le_dec x (Sfr fr + FRAME_SHADOW)) as [H2|H2]; [|right; exact H2].
        exfalso. exact (app_not_shadow x (Happ x ltac:(lia)) (HshIS x ltac:(lia))).
      + destruct (Hplace FN_STACK ltac:(lia)) as [P1|P1]; [left | right]; lia.
    - intros A' HA'b HA' x Hx.
      assert (EA' : A' = A).
      { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in Hr9; rewrite <- HA'; exact Hr9).
        apply (f_equal (bv_unsigned (n := 64))) in E.
        rewrite !MState.unsigned_lit in E by lia. exact E. }
      subst A'. apply Hout; [right; lia | right; lia | right; lia | right; lia].
    - intros A' HA'b HA' x Hx.
      assert (EA' : A' = A).
      { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in Hr9; rewrite <- HA'; exact Hr9).
        apply (f_equal (bv_unsigned (n := 64))) in E.
        rewrite !MState.unsigned_lit in E by lia. exact E. }
      subst A'. apply Hout; [right; lia | right; lia | right; lia | left; lia].
    - intros x Hx. apply Hout; [right; lia | right; lia | right; lia | right; lia].
    - intros x Hx. apply Hout; [left; lia | left; unfold LOWMEM_END in *; lia | left; lia | left; lia].
    - intros a Ha1 Ha2. pose proof (HWA a Ha1 Ha2) as HA1. pose proof HA1 as HA2.
      apply (tp_addr_munch W mem mem' a 1 HA1 MU).
      intros i Hi. destruct HA2 as (Ha0 & _ & _ & HAb1). destruct (HAb1 i Hi) as (Hap & _).
      replace (a + i) with a in * by lia.
      apply HoutSh; [apply shadow_of_app; exact Hap|].
      intros Hsl. pose proof (tp_sh_back fr a Hfr8 ltac:(lia) ltac:(lia) Hsl) as Hfin.
      apply Ha2. lia.
    - intros x Happx Hxlo Hxnf. apply HoutApp; [exact Happx | exact Hxnf | lia].
    - intros x Hx.
      destruct (Hinap x Hx) as (Hxa & Hxlo & Hxfr & _).
      assert (Hx0 : 0 <= x) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hxa; lia).
      split.
      + apply HoutApp; [exact Hxa | exact Hxfr | lia].
      + apply HoutSh; [apply shadow_of_app; exact Hxa|].
        intros Hsl. apply Hxfr. exact (tp_sh_back fr x Hfr8 ltac:(lia) Hx0 Hsl). }
  assert (HENT' : ENT APIf g hb mem' md).
  { eapply ent_store with (W := W) (fr := fr) (regs := regs).
    all: try exact FF.
    all: try exact HENT.
    all: try exact HFRA.
    all: try exact MU.
    all: try exact Hstk2.
    all: try exact Hhi2.
    - intros x Hx. destruct (tp_outside_dec W x) as [Ho|Ho]; [left; exact Ho|].
      destruct (HCL x Ho) as [H1|[H1|[H1|H1]]].
      + right. right. left. lia.
      + right. right. right. exact H1.
      + right. left. lia.
      + right. left. lia.
    - intros a Hia Ho. exact (proj2 (Hown2 a) Ho). }
  split; [exact HFRA' | exact HENT'].
Qed.

End TP.
