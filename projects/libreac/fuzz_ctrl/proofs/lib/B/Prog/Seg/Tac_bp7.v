(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 2004 of its 2120 lines of code are new or changed and 895 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F30.v, with its module paths and module names changed; 139 of its 164 lines of code are new or changed and 2095 lines of the source are left out. *)
(* Helpers of the image-B call segments P7-P11 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, libreac v1.9.0):
   the stretch 0x81d80 .. 0x81e08 between the reac_ctrl_identity_reply call and the kind-name call.  rule 24: no
   function proved (slot segments).
   Each of P7-P11 tests the previous callee's result, loads its arguments and calls one function on its lib/B
   contract.  The call writes the callee's own stack window [sp - K, sp) (K <= FN_STACK), and P10's callee also
   writes the code byte fr + 3040 (patched fr + 2960).  Both are application bytes, so the write set holds no
   shadow byte.  bp7_call wraps Tac_bp.bp_run (the run on the normalized memory, where a callee may need mem_inv)
   and Tac_bp.bp_post (FRA and ENT across the write set).  bp7_keep carries the cut conjuncts that lie outside the
   write set: every addressable range, the spills [A + off] (A >= sp, A >= fr + 3136), our[], the two frame
   records and the local `first` (apart from the window by fra_frame, and below fr + 3040), PRO and PL0. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs Tac_bp.
Import ListNotations.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Open Scope Z_scope.

(* The write set of a P7-P11 call: inside the callee window [S - K, S) and the code byte fr + 3040. *)
Definition bp7_in (fr S K : Z) (W : list ivl) : Prop :=
  forall x, ~ LF.outside W x -> (S - K <= x < S) \/ (fr + 3040 <= x < fr + 3041).

(* Every byte of a stack range that the run leaves readable is readable (the callee window after a call). *)
Lemma bp7_rd_stk : forall m lo hi x, stk rsegs m lo hi -> lo <= x < hi -> exists b, mrd rsegs m (wa x) = Some b.
Proof. intros m lo hi x (_ & _ & H) Hx. exact (proj2 (H x Hx)). Qed.

(* One byte read by `lbu`, as a read-only C1 cell. *)
Lemma bp7_ro1 : forall m a (b : byte), bytes_at rsegs m a [b] -> ro_cells rsegs m a [C1 b].
Proof. intros m a b H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes app]. exact H. Qed.

Section BP7.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The FRA numbers a P7-P11 call needs: the window [sp - FN_STACK, sp) lies in HighMem with sp <= APPMEM_END,
   the spill base A lies in [sp, 2 ^ 64 - 448], the frame is application memory apart from the window and below A. *)
Lemma bp7_fra : forall g fr regs mem md, FRA B APIf ra g fr [] regs mem md ->
  exists A, rg regs 9 A /\
    HIGHMEM_BEG + FN_STACK <= AC.aspZ regs /\ AC.aspZ regs <= A /\ A + 448 <= APPMEM_END /\
    fr + 3136 <= A /\ AC.aspZ regs mod 16 = 0 /\
    (forall a, fr <= a < fr + 3136 -> app_mem a) /\ 0 <= fr /\ fr mod 32 = 0 /\
    (forall K, 0 <= K <= FN_STACK -> fr + 3136 <= AC.aspZ regs - K \/ AC.aspZ regs <= fr).
Proof.
  intros g fr regs mem md HFRA.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & _).
  destruct (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hplace & _ & _ & _).
  destruct (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGT & Happ).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH) as Hhigh.
  pose proof (Happ fr ltac:(lia)) as Hf0.
  exists A. rewrite Haspz in *.
  split; [exact Hr9|].
  unfold AC.GT, app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *.
  repeat split; try lia; try exact Happ; try exact Hplace.
Qed.

(* The run of a P7-P11 segment, from its Lib-level evt on the normalized memory to SR on the real configuration,
   with FRA and ENT moved to the end state by Tac_bp.bp_post.  The evt names the end pc, keeps the FRA registers,
   writes W (inside the callee window and the code byte), and leaves every written byte readable. *)
Lemma bp7_call : forall g fr regs mem md (pc pc' K : Z) W
    (Q : bvmap 5 word -> (word -> option byte) -> Prop) (P : config -> Prop),
  FRA B APIf ra g fr [] regs mem md -> ENT APIf g [] mem md -> 0 <= K <= FN_STACK ->
  bp7_in fr (AC.aspZ regs) K W -> rt_disjoint W ->
  evt rsegs (fun ms => exists R pc0 m0', ms = MS R fp_regs pc0 fp_csr None m0' (seg_rom rsegs) /\
      (pc0 = Z_to_bv 64 pc' /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = getr regs 26 /\
       LF.munch W (normalize rsegs mem) m0' /\ LF.wmono rsegs (normalize rsegs mem) m0' /\
       (forall x, ~ LF.outside W x -> exists b, mrd rsegs m0' (wa x) = Some b) /\ Q R m0'))
    (MS (Regs6ss.mkR_of regs) fp_regs (Z_to_bv 64 pc) fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R m0' regs' mem' md', Q R m0' -> (forall r, getr regs' r = getr R r) -> getr regs' 9 = getr regs 9 ->
     mem_rel rsegs mem' m0' ->
     FRA B APIf ra g fr [] regs' mem' md' -> ENT APIf g [] mem' md' ->
     LF.munch W mem mem' -> LF.wmono rsegs mem mem' ->
     SR rsegs (mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom rsegs)) md) P.
Proof.
  intros g fr regs mem md pc pc' K W Q P HFRA HENT HK HIN HDJ HE HC.
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & _).
  apply (bp_run regs (Z_to_bv 64 pc) mem md
    (fun R pc0 m0' => pc0 = Z_to_bv 64 pc' /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = getr regs 26 /\
       LF.munch W (normalize rsegs mem) m0' /\ LF.wmono rsegs (normalize rsegs mem) m0' /\
       (forall x, ~ LF.outside W x -> exists b, mrd rsegs m0' (wa x) = Some b) /\ Q R m0')
    P Hhalt Hro HE).
  intros R pc0 m0' regs' mem' md' (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & MU0 & WM0 & RD0 & HQ)
    Hreg HRel Hsame Hmat.
  subst pc0.
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
  pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
  assert (RDW : forall x, ~ LF.outside W x -> exists b, mrd rsegs mem' (wa x) = Some b).
  { intros x Hx. rewrite (mrd_rel rsegs mem' m0' (wa x) HRel). exact (RD0 x Hx). }
  assert (HCOV : bp_cover fr (AC.aspZ regs - K) (AC.aspZ regs) W).
  { intros x Hx. destruct (HIN x Hx) as [H|H]; [right; right; exact H | right; left; lia]. }
  destruct (bp_post B APIf ra empty FF g fr regs regs' mem mem' md md' W K HFRA HENT HK MU WM Hsame HDJ HCOV
              RDW ltac:(rewrite Hreg; exact K2) ltac:(rewrite Hreg; exact K3) ltac:(rewrite Hreg; exact K4)
              ltac:(rewrite Hreg; exact K8) ltac:(rewrite Hreg; exact K9) ltac:(rewrite Hreg; exact K19)
              ltac:(rewrite Hreg; exact K26) Hmat) as (HFRA' & HENT').
  exact (HC R m0' regs' mem' md' HQ Hreg ltac:(rewrite Hreg; exact K9) HRel HFRA' HENT' MU WM).
Qed.

(* The cut conjuncts outside the write set, carried across a P7-P11 call. *)
Lemma bp7_keep : forall g fr regs regs' mem mem' md K W,
  FRA B APIf ra g fr [] regs mem md -> 0 <= K <= FN_STACK ->
  bp7_in fr (AC.aspZ regs) K W -> LF.munch W mem mem' ->
  getr regs' 9 = getr regs 9 -> getr regs' 23 = getr regs 23 -> getr regs' 25 = getr regs 25 ->
  (forall p n, addressable mem p n -> addressable mem' p n) /\
  (forall off v, 0 <= off <= 440 -> spill regs mem off v -> spill regs' mem' off v) /\
  (OURb g fr mem -> OURb g fr mem') /\
  (PRO fr regs mem -> PRO fr regs' mem') /\
  (PL0 g fr regs mem -> PL0 g fr regs' mem').
Proof.
  intros g fr regs regs' mem mem' md K W HFRA HK HIN MU E9 E23 E25.
  destruct (bp7_fra g fr regs mem md HFRA)
    as (A & Hr9 & Hsplo & HspA & HA448 & HfrA & _ & Happ & Hfr0 & _ & Hplace).
  pose proof (Hplace K HK) as Hsep.
  set (S := AC.aspZ regs) in *.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (OUT : forall x, ~ (S - K <= x < S) -> ~ (fr + 3040 <= x < fr + 3041) -> LF.outside W x).
  { intros x N1 N2. destruct (bp_out_dec W x) as [Ho|Hno]; [exact Ho|].
    exfalso. destruct (HIN x Hno) as [H|H]; [exact (N1 H) | exact (N2 H)]. }
  assert (Hwapp : forall x, S - K <= x < S -> app_mem x).
  { intros x Hx. unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia. }
  (* every addressable range: its shadow bytes are not application bytes, so not written *)
  assert (HAD : forall p n, addressable mem p n -> addressable mem' p n).
  { intros p n Had. apply (bp_addr_keep W mem mem' p n Had MU). intros i Hi.
    destruct Had as (_ & _ & _ & Hb). destruct (Hb i Hi) as (Hap & _).
    pose proof (shadow_of_app _ Hap) as Hsh.
    apply OUT.
    - intros Hx. exact (app_not_shadow _ (Hwapp _ Hx) Hsh).
    - intros Hx. exact (app_not_shadow (shadow_addr (p + i)) (Happ (shadow_addr (p + i)) ltac:(lia)) Hsh). }
  (* the spills [A + off]: at or above sp and above the frame *)
  assert (HSP : forall off v, 0 <= off <= 440 -> spill regs mem off v -> spill regs' mem' off v).
  { intros off v Hoff (A1 & HA1 & Hq).
    assert (HA1e : A1 = A)
      by (apply (bp_spill_A regs mem off v A A1 HA1 Hq Hr9); unfold HIGHMEM_BEG, APPMEM_END in *; lia).
    subst A1.
    exists A. split; [unfold rg in *; rewrite E9; exact Hr9|].
    unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8.
    intros x Hx. apply OUT; lia. }
  (* frame bytes below the code byte fr + 3040 *)
  assert (HFB : forall a bs, bytes_at rsegs mem a bs -> fr <= a -> a + Z.of_nat (length bs) <= fr + 3040 ->
            bytes_at rsegs mem' a bs).
  { intros a bs Hb Ha1 Ha2. eapply fl_bytes; [exact Hb | exact MU |]. intros x Hx. apply OUT; lia. }
  assert (HOUR : OURb g fr mem -> OURb g fr mem').
  { unfold OURb. intros H. apply (HFB _ _ H); rewrite ?OUR_length; lia. }
  split; [exact HAD|]. split; [exact HSP|]. split; [exact HOUR|].
  split.
  - intros HP. apply (bp_PRO_keep fr regs regs' mem mem' HSP (HAD _ _) HP).
  - unfold PL0, CUR, RAD. intros ((Hc0 & Hc23 & Hc25) & HID & HFG & (HR1 & HR2 & HR3) & H176 & H208 & HFS).
    split; [split; [exact Hc0|]; unfold rg in *; rewrite E23, E25; split; [exact Hc23 | exact Hc25]|].
    split.
    { unfold IDBe in *. apply (HFB _ _ HID); [lia|].
      unfold RcIdentModel.ID0. rewrite repeat_length. unfold RcIdentModel.ID_SIZE. lia. }
    split.
    { unfold FGBe in *. apply (HFB _ _ HFG); [lia|]. unfold z72. rewrite repeat_length. lia. }
    split; [split; [exact (HAD _ _ HR1) | split; [exact (HAD _ _ HR2) | exact (HAD _ _ HR3)]]|].
    split; [apply HSP; [lia | exact H176]|]. split; [apply HSP; [lia | exact H208]|].
    unfold FSj, FSb, u32, b8 in HFS |- *. change (fst_at (g_in g) 0) with fs0 in HFS |- *.
    unfold fs0 in HFS |- *. cbn [fs_have fs_n fs_body] in HFS |- *.
    destruct HFS as (Hhv & Hn & Hbody & H40 & HFI).
    split; [apply (HFB _ _ Hhv); [lia | rewrite length_le4; lia]|].
    split; [apply (HFB _ _ Hn); [lia | cbn [length]; lia]|].
    split; [apply (HFB _ _ Hbody); [lia | cbn [length]; lia]|].
    split; [exact (HAD _ _ H40) | exact HFI].
Qed.

End BP7.
