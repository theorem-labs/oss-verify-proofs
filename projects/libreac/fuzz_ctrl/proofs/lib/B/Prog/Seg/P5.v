(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 809 of its 930 lines of code are new or changed and 890 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/R4.v, with its module names, addresses and numbers changed; 293 of its 442 lines of code are new or changed and 781 lines of the source are left out. *)
(* Segment P5 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): [0x81d28, 0x81d64], 16
   instructions, cut Inv_B81d28 (v1.9 pc 0x81d28) -> cut Inv_B81d68 (v1.9 pc 0x81d68) (plan-asan-ubsan.md section 2,
   row P5; section 4, MSET = checked_memset, 0x52600).
   rule 24: no function proved (a slot segment).  With s3 = S(fr) the code marks two more frame variables usable:
   the one code byte at fr + 3040 (S(fr) + 380 = 01, 0x81d3c) and the 32-byte scratch at fr + 3056 (S(fr) + 382 ..
   385 = 00 00 00 00, 0x81d48 .. 0x81d54); the stores at S(fr) + 370 / 372 / 376 (0x81d30 .. 0x81d38) are the other
   frame-variable marks.  It writes the code byte itself through s8 (0x81d44 sb a0,0(s8), a0 = -18), then reloads
   the scratch pointer [A + 64] = fr + 3056 (0x81d5c; spilled 0x8153c) and calls checked_memset with a2 = 32,
   a1 = 0 (MSET@0x81d64).  The range has no instrumented shadow check and no UBSan trap.
   p5_evt is the Lib-level run with the call taken on its lib/B contract (asan_memset_c.v, a Section hypothesis,
   never its code); seg_P5 lifts it to the cuts on the normalized memory (Tac_bp.bp_run) and moves FRA / ENT
   across the write set (the 16 frame-shadow bytes [S(fr) + 370, S(fr) + 386), the code byte, the 32-byte scratch
   and the callee window [sp - 2208, sp)) by Tac_bp.bp_post.
   The cuts are SlotInv.v's official Inv_B81d28 / Inv_B81d68 (the exit does not carry the identity_reply call's
   side-stack package, which P6 rebuilds from FRA); the exit's window addressability comes from FRA's window
   conjunct and fra_frame, the parse BC bytes from FRA's frame_AG conjunct.  The exit also carries XC (s8 =
   fr + 3040 and that byte addressable, from S(fr) + 380 = 01), the spill [A + 64] = fr + 3056 (the entry's q64
   with s1 = A), PL0 (CUR g c0 in s7 / s9, kept by the callee; the records ID0 at fr + 2688 and z72 at fr + 2768,
   RAD, [A + 176] / [A + 208] and the turn-0 first-fragment state FSj g fr 0 at fr + 2880, all apart from the
   write set), PRO (Tac_bp.bp_PRO_keep: our[]'s shadow byte Sfr fr + 328 is below the stores at Sfr fr + 370 ..
   385) and the kind-name table's addressability (its shadow is in the low shadow, apart from the write set).
   v1.9.0 against the patched image: the pcs move +0x88 and the shadow marks +10 (the frame variables after
   `first` moved +80 bytes), the code byte's pointer is s8 (patched s11), the scratch pointer [A + 64]
   (patched [A + 72]). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require asan_memset_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_bp.
Import ListNotations.
Open Scope Z_scope.

Module MSC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memset_c.

(* ---- the run: the four marks, the code byte, the four scratch marks, and jal checked_memset ---- *)
Lemma p5_evt : MSC.asan_memset_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv Sh Ab Y D lo : Z)
         (xs : list byte) (yb : byte) (junk : list byte),
    sp = Z_to_bv 64 spv -> s3 = Z_to_bv 64 Sh -> s1 = Z_to_bv 64 Ab -> s8 = Z_to_bv 64 Y ->
    RT_HI <= Sh -> Sh + 392 <= lo -> HIGHMEM_BEG <= lo -> lo + 2208 <= spv -> spv <= APPMEM_END ->
    Sh + 392 <= Ab -> Ab + 80 <= 2 ^ 64 ->
    RT_HI <= Y -> app_mem Y -> Y + 16 <= D -> D + 32 <= Sh \/ Sh + 392 <= Y ->
    D mod 8 = 0 -> shadow_addr D = Sh + 382 -> (forall a, D <= a <= D + 32 -> app_mem a) ->
    (D + 32 <= spv - 2208 \/ spv <= D) -> D + 32 <= Ab ->
    length xs = 16%nat -> rw_cells rsegs m (Sh + 370) (map C1 xs) ->
    rw_cells rsegs m Y (map C1 [yb]) -> rw_cells rsegs m D [CB 32 junk] ->
    ro_cells rsegs m (Ab + 64) [C8 (Z_to_bv 64 D)] ->
    mem_inv rsegs m -> stk rsegs m lo spv -> asan_cells m -> shadow_rw m ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81d68) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 24 = s8 /\ getr R 23 = s7 /\ getr R 25 = s9 /\
         munch [(Sh + 370, Sh + 386); (Y, Y + 1); (D, D + 32); (spv - 2208, spv)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo spv /\ shadow_rw m' /\
         bytes_at rsegs m' (Sh + 380) [Z_to_bv 8 1] /\
         (forall x, Sh + 370 <= x < Sh + 386 \/ Y <= x < Y + 1 \/ D <= x < D + 32 \/ spv - 2208 <= x < spv ->
            exists b, mrd rsegs m' (wa x) = Some b))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81d28) fc None m (seg_rom rsegs)).
Proof.
  intros MSET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv Sh Ab Y D lo xs yb junk -> -> -> -> HSrt HSlo HHM HLO HAE HSA HA64 HYrt HYapp HYD HSD
    HD8 HshD HDapp Hsep HDA Hxs CH CHY RWD RO64 HMI ST HAC HSW.
  unfold MSC.asan_memset_contract, MSC.ASAN_MEMSET_K, MSC.ASAN_MEMSET in MSET. cbv zeta in MSET.
  do 16 (destruct xs as [|? xs]; [discriminate Hxs|]).
  destruct xs; [|discriminate Hxs]. clear Hxs. cbn [map] in CH.
  cbn [map] in CHY.
  pose proof (rw_cells_bound rsegs m (Sh + 370) _ CH) as HSb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HSb.
  pose proof (rw_cells_bound rsegs m D _ RWD) as HDb.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HDb.
  unfold HIGHMEM_BEG, APPMEM_END, RT_HI in *.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  pose proof (HDapp (D + 32) ltac:(lia)) as HD32.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HD32.
  pose proof HYapp as HYa. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HYa.
  assert (EU1 : bv_unsigned (Z_to_bv 64 D) = D) by (apply MState.unsigned_lit; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  pose proof (munch_refl [(Sh + 370, Sh + 386); (Y, Y + 1)] m) as MU1.
  pose proof (munch_refl [(Sh + 370, Sh + 386); (Y, Y + 1); (D, D + 32); (spv - 2208, spv)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step.
  bp_sb. bp_sb. bp_sb. bp_sb.
  step.
  bp_sb.
  bp_sb. bp_sb. bp_sb. bp_sb.
  step. step. step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (proj2 (proj1 CH)) as HbC. cbn [cells_bytes cbytes app] in HbC.
  pose proof (proj2 (proj1 CHY)) as HbY. cbn [cells_bytes cbytes app] in HbY.
  assert (HRD1 : forall x, Sh + 370 <= x < Sh + 386 -> exists b, mrd rsegs m1 (wa x) = Some b).
  { intros x Hx. apply (bp_ba_rd m1 (Sh + 370) _ x HbC).
    cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (HRDY : forall x, Y <= x < Y + 1 -> exists b, mrd rsegs m1 (wa x) = Some b).
  { intros x Hx. apply (bp_ba_rd m1 Y _ x HbY). cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. lia. }
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept _ m m1 HAC MU). cbn [disjoint_from]. unfold RT_LO, RT_HI.
    repeat split; first [exact I | lia]. }
  assert (HSW1 : shadow_rw m1).
  { apply (bp_shadow_rw _ m m1 HSW MU1 WM). intros a Ha.
    pose proof Ha as Ha'.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha'.
    destruct (Z_le_gt_dec (Sh + 370) a) as [H1|H1]; [destruct (Z_lt_ge_dec a (Sh + 386)) as [H2|H2]|].
    - right. exact (HRD1 a ltac:(lia)).
    - left. cbn [outside]. split; [lia|]. split; [|exact I].
      intros Hin. replace a with Y in Ha by lia. exact (app_not_shadow Y HYapp Ha).
    - left. cbn [outside]. split; [lia|]. split; [|exact I].
      intros Hin. replace a with Y in Ha by lia. exact (app_not_shadow Y HYapp Ha). }
  (* the store tactics transport the stack window to m1 (the stores are below lo) *)
  pose proof ST as HSTK1.
  assert (ADR1 : addressable m1 D 32).
  { pose proof (bp_ba_sub _ _ _ 12 4 HbC ltac:(cbn [length]; lia)) as B12.
    cbn [firstn skipn] in B12. replace (Sh + 370 + Z.of_nat 12) with (Sh + 382) in B12 by lia.
    apply (bp_addr_z m1 D 4 32); [reflexivity | lia | exact HD8 | unfold APPMEM_END; lia
      | intros i Hi; apply HDapp; lia |].
    rewrite HshD. exact B12. }
  eapply evt_cut.
  { eapply MSET with (junk := junk) (lo := lo).
    all: rewrite ?EU1, ?EU2; try change (bv_unsigned (Z_to_bv 64 32)) with 32.
    - exact RWD.
    - lia.
    - exact ADR1.
    - unfold end_in_app. right. apply HDapp. lia.
    - right. apply HDapp. lia.
    - right. unfold RT_HI. lia.
    - lia.
    - exact HSTK1.
    - lia.
    - unfold HIGHMEM_BEG. lia.
    - unfold APPMEM_END. lia.
    - exact HAC1.
    - exact HSW1.
    - exact HMI. }
  intros ms' PO. unfold MSC.asan_memset_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU2 & WM2 & MI2 & ST2 & RW2 & AC2 & SW2).
  subst ms'.
  unfold MSC.ASAN_MEMSET_K in MU2.
  rewrite EU1, EU2 in MU2. rewrite EU2 in ST2. rewrite EU1 in RW2.
  change (bv_unsigned (Z_to_bv 64 32)) with 32 in MU2, RW2.
  change (bv_unsigned (Z_to_bv 64 0)) with 0 in RW2.
  change (Z.to_nat 32) with 32%nat in RW2.
  change (0 mod 256) with 0 in RW2.
  assert (HDb' : bytes_at rsegs m' D (repeat (Z_to_bv 8 0) 32)).
  { destruct RW2 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (Hsub : sub_fp [(D, D + 32); (spv - 2208, spv)]
                   [(Sh + 370, Sh + 386); (Y, Y + 1); (D, D + 32); (spv - 2208, spv)]).
  { intros x Hx. cbn [outside] in Hx |- *. tauto. }
  pose proof (munch_trans _ m m1 m' MU (munch_weaken _ _ m1 m' Hsub MU2)) as MUf.
  assert (KEEP : forall x, (x < D \/ D + 32 <= x) -> (x < spv - 2208 \/ spv <= x) ->
            mrd rsegs m' (wa x) = mrd rsegs m1 (wa x) \/ ~ (0 <= x < 2 ^ 64)).
  { intros x H1 H2. destruct (Z_le_gt_dec 0 x) as [Hx0|Hx0]; [destruct (Z_lt_ge_dec x (2 ^ 64)) as [Hx1|Hx1]|].
    - left. unfold mrd. rewrite (MU2 (wa x)); [reflexivity|].
      rewrite wa_unsigned by lia. cbn [outside]. split; [lia | split; [lia | exact I]].
    - right. lia.
    - right. lia. }
  assert (RDfin : forall x, Sh + 370 <= x < Sh + 386 \/ Y <= x < Y + 1 \/ D <= x < D + 32 \/
                            spv - 2208 <= x < spv -> exists b, mrd rsegs m' (wa x) = Some b).
  { intros x Hx.
    destruct (Z_le_gt_dec (spv - 2208) x) as [H3|H3]; [destruct (Z_lt_ge_dec x spv) as [H4|H4]|].
    { destruct ST2 as (_ & _ & Hs). exact (proj2 (Hs x ltac:(lia))). }
    all: destruct (Z_le_gt_dec D x) as [H1|H1]; [destruct (Z_lt_ge_dec x (D + 32)) as [H2|H2]|].
    all: try (apply (bp_ba_rd m' D _ x HDb'); rewrite repeat_length; lia).
    all: destruct (KEEP x ltac:(lia) ltac:(lia)) as [Hk|Hk]; [|lia]; rewrite Hk.
    all: destruct (Z_le_gt_dec (Sh + 370) x) as [H5|H5]; [destruct (Z_lt_ge_dec x (Sh + 386)) as [H6|H6]|].
    all: first [exact (HRD1 x ltac:(lia)) | exact (HRDY x ltac:(lia))]. }
  (* the mark of the code byte: S(fr) + 380 = 01 *)
  pose proof (bp_ba_sub _ _ _ 10 1 HbC ltac:(cbn [length]; lia)) as B380.
  cbn [firstn skipn] in B380.
  replace (Sh + 370 + Z.of_nat 10) with (Sh + 380) in B380 by lia.
  pose proof (bytes_at_transport rsegs [(D, D + 32); (spv - 2208, spv)] m1 m' _ _ B380 MU2
    ltac:(cbn [length Z.of_nat Pos.of_succ_nat Pos.succ disjoint_from];
          split; [lia | split; [lia | exact I]])) as B380'.
  replace (ret_pc (Z_to_bv 64 0x81d68)) with (Z_to_bv 64 0x81d68)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [exact MUf|]. split; [exact (wmono_trans rsegs m m1 m' WM WM2)|].
  split; [exact ST2|]. split; [exact SW2|]. split; [exact B380' | exact RDfin].
Qed.

From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require RcAsanFP reac_ctrl_identity_reply_c reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs Tac_bp.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module FP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.RcAsanFP.
Module RIR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_identity_reply_c.
Module RPC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_parse_c.
Open Scope Z_scope.

Section P5.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The ending callee checked_memset (MSET@0x81d64), taken on its lib/B contract, never on its code. *)
Hypothesis MSET : MSC.asan_memset_contract.

Lemma seg_P5 : Hcut B APIf ra (Inv_B81d68 B APIf ra) -> Hcut B APIf ra (Inv_B81d28 B APIf ra).
Proof.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HOUR & HPRO & HCUR & HKN & HIDB & HFGB & HRAD &
                    H176 & H208 & Ac & jy & junk & Hr9c & HAc0 & H24 & Hq64 & RWy & RWd & HFS0).
  subst c.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  destruct (fra_app B APIf ra g fr [] regs mem md HFRA) as (HGT & Happ').
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HMK : MSC.ASAN_MEMSET_K = 2208) by reflexivity.
  assert (HRK : RIR.REAC_CTRL_IDENTITY_REPLY_K = 9072) by reflexivity.
  rewrite Haspz in Hlo, Hstkw.
  pose proof (Hplace 2208 ltac:(lia)) as Hsep. rewrite Haspz in Hsep.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HAeq : Ac = A)
    by (apply (bp_spill_A regs mem 64 (fr + 3056) A Ac Hr9c Hq64 Hr9); unfold APPMEM_END in HAPP; lia).
  subst Ac.
  assert (Hfre : 0 <= fr /\ fr + 3136 <= APPMEM_END).
  { pose proof (Happ' fr ltac:(lia)) as H1. pose proof (Happ' (fr + 3135) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HLH : fr + 3136 <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { pose proof (Happ' fr ltac:(lia)) as H1. pose proof (Happ' (fr + 3135) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  pose proof (bp_sf8 fr Hfrm) as HSf8.
  unfold AC.GT, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in HGT, HSf8, HLH, Hfre, Hhigh.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17592186044416 + 2147450880) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HSfrD : Sfr fr + 392 <= fr \/ fr + 3136 <= Sfr fr) by lia.
  assert (HShm : Sfr fr + 392 <= 17592186044416 + 2147450880) by lia.
  assert (HSK : 2147450880 + 785408 <= Sfr fr) by lia.
  assert (Hsphm : 17592186044416 + 2147450880 <= sp - FN_STACK) by lia.
  assert (HSspa : sp <= g_S g /\ g_S g < 140737488355328) by (unfold APPMEM_END in HAPP; lia).
  assert (HAhi : Sfr fr + 392 <= A) by lia.
  (* the normalized memory the run is stepped on *)
  pose proof (mem_rel_normalize rsegs mem Hro) as HR0.
  pose proof (mem_inv_normalize rsegs mem) as HMI0.
  pose proof (bp_srw_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_shadow_rw _ _ _ HRT)) as HSW0.
  pose proof (bp_cells_rel mem (normalize rsegs mem) HR0 (AsanRTInv.RT_cells _ _ _ HRT)) as HAC0.
  pose proof (bp_stk_rel mem (normalize rsegs mem) (sp - FN_STACK) sp HR0 ltac:(lia) Hstkw) as ST0.
  (* the 16 frame-shadow cells, the code byte and the 32-byte scratch, on the normalized memory *)
  destruct Hsh as (sh & Hshb & Hshl).
  rewrite FRAME_SHADOW_val in Hshl. change (Z.to_nat 392) with 392%nat in Hshl.
  pose proof (bp_ba_sub mem (Sfr fr) sh 370 16 Hshb ltac:(lia)) as Hxs.
  replace (Sfr fr + Z.of_nat 370) with (Sfr fr + 370) in Hxs by lia.
  apply (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ HR0)) in Hxs.
  assert (Hxl : length (firstn 16 (skipn 370 sh)) = 16%nat) by (rewrite length_firstn, length_skipn; lia).
  assert (CHx : rw_cells rsegs (normalize rsegs mem) (Sfr fr + 370) (map C1 (firstn 16 (skipn 370 sh)))).
  { apply bp_rw_C1; [exact Hxs|]. rewrite Hxl. change (Z.of_nat 16) with 16.
    split; [lia|]. split; [lia|]. intros i Hi.
    assert (Hin : in_shadow (Sfr fr + 370 + i)).
    { replace (Sfr fr + 370 + i) with (Sfr fr + (370 + i)) by lia. apply bp_fsh; [exact Happ' | lia]. }
    exact (proj1 (HSW0 _ Hin)). }
  pose proof (bp_frame_stk B APIf ra g fr [] regs mem md HFRA) as Hfstk.
  pose proof (bp_stk_rel mem (normalize rsegs mem) fr (fr + 3136) HR0 ltac:(lia) Hfstk) as Hfstk0.
  destruct (stk_split rsegs _ fr (fr + 3040) (fr + 3136) Hfstk0 ltac:(lia)) as (_ & Hs1).
  destruct (stk_split rsegs _ (fr + 3040) (fr + 3041) (fr + 3136) Hs1 ltac:(lia)) as (Hy & Hs2).
  destruct (stk_split rsegs _ (fr + 3041) (fr + 3056) (fr + 3136) Hs2 ltac:(lia)) as (_ & Hs3).
  destruct (stk_split rsegs _ (fr + 3056) (fr + 3088) (fr + 3136) Hs3 ltac:(lia)) as (Hd & _).
  destruct (stk_bytes rsegs _ _ _ Hy ltac:(lia)) as (yl & Hyl & Hyb).
  replace (fr + 3041 - (fr + 3040)) with 1 in Hyl by lia.
  destruct yl as [|yb [|? ?]]; cbn [length] in Hyl; try lia.
  assert (CHY : rw_cells rsegs (normalize rsegs mem) (fr + 3040) (map C1 [yb])).
  { apply bp_rw_C1; [exact Hyb|]. pose proof (bp_wr_stk _ _ _ Hy) as Hw.
    replace (fr + 3041 - (fr + 3040)) with (Z.of_nat (length [yb])) in Hw by (cbn; lia). exact Hw. }
  destruct (bp_stk_rw _ _ _ Hd ltac:(lia)) as (junk0 & RWD).
  replace (Z.to_nat (fr + 3088 - (fr + 3056))) with 32%nat in RWD by lia.
  (* the scratch pointer spilled at [A + 64], read by the ld *)
  assert (RO0 : ro_cells rsegs (normalize rsegs mem) (A + 64) [C8 (Z_to_bv 64 (fr + 3056))]).
  { apply bp_ro8. unfold q64 in Hq64. exact (proj1 (bytes_at_rel rsegs mem (normalize rsegs mem) _ _ HR0) Hq64). }
  (* p5_evt's arithmetic premises *)
  assert (P1 : RT_HI <= Sfr fr) by (unfold RT_HI; lia).
  assert (P2 : Sfr fr + 392 <= sp - FN_STACK) by lia.
  assert (P3 : HIGHMEM_BEG <= sp - FN_STACK) by (unfold HIGHMEM_BEG; lia).
  assert (P4 : sp - FN_STACK + 2208 <= sp) by lia.
  assert (P5 : sp <= APPMEM_END) by (unfold APPMEM_END; lia).
  assert (P6 : A + 80 <= 2 ^ 64) by lia.
  assert (P7 : RT_HI <= fr + 3040) by (unfold RT_HI; lia).
  assert (P7b : app_mem (fr + 3040)) by (apply Happ'; lia).
  assert (P8 : (fr + 3056) mod 8 = 0) by (replace (fr + 3056) with (fr + 8 * 382) by lia; apply bp_m8; exact Hfrm).
  assert (P9 : shadow_addr (fr + 3056) = Sfr fr + 382)
    by (replace (fr + 3056) with (fr + 8 * 382) by lia; apply bp_sh8).
  assert (P10 : forall a, fr + 3056 <= a <= fr + 3056 + 32 -> app_mem a) by (intros a Ha; apply Happ'; lia).
  assert (P11 : fr + 3056 + 32 <= sp - 2208 \/ sp <= fr + 3056) by lia.
  assert (P12 : fr + 3056 + 32 <= Sfr fr \/ Sfr fr + 392 <= fr + 3040) by lia.
  unfold rg in Hr19, Hr9, H24.
  rewrite SEGS.
  apply (bp_run regs (Z_to_bv 64 0x81d28) mem md
    (fun R pc' m0' => pc' = Z_to_bv 64 0x81d68 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 26 = getr regs 26 /\
       getr R 24 = getr regs 24 /\ getr R 23 = getr regs 23 /\ getr R 25 = getr regs 25 /\
       LF.munch [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1); (fr + 3056, fr + 3056 + 32);
                 (sp - 2208, sp)] (normalize rsegs mem) m0' /\
       LF.wmono rsegs (normalize rsegs mem) m0' /\ stk rsegs m0' (sp - FN_STACK) sp /\ shadow_rw m0' /\
       bytes_at rsegs m0' (Sfr fr + 380) [Z_to_bv 8 1] /\
       (forall x, Sfr fr + 370 <= x < Sfr fr + 386 \/ fr + 3040 <= x < fr + 3040 + 1 \/
                  fr + 3056 <= x < fr + 3056 + 32 \/ sp - 2208 <= x < sp ->
          exists b, mrd rsegs m0' (wa x) = Some b))
    (Post B APIf ra g)).
  - exact Hhalt.
  - exact Hro.
  - rewrite bp_mkR_of.
    eapply evt_mono.
    + apply (p5_evt MSET) with (spv := sp) (Sh := Sfr fr) (Ab := A) (Y := fr + 3040) (D := fr + 3056)
        (lo := sp - FN_STACK) (xs := firstn 16 (skipn 370 sh)) (yb := yb) (junk := junk0).
      all: try assumption.
      all: lia.
    + intros ms' (R & m' & Hms & P2' & P3' & P4' & P8' & P9' & P19' & P26' & P24' & P23' & P25' &
                  MUq & WMq & STq & SWq & Bq & RDq).
      exists R, (Z_to_bv 64 0x81d68), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2'|]. split; [exact P3'|]. split; [exact P4'|].
      split; [exact P8'|]. split; [exact P9'|]. split; [exact P19'|]. split; [exact P26'|].
      split; [exact P24'|]. split; [exact P23'|]. split; [exact P25'|].
      split; [exact MUq|]. split; [exact WMq|]. split; [exact STq|].
      split; [exact SWq|]. split; [exact Bq | exact RDq].
  - intros R pc' m0' regs'' mem' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K24 & K23 & K25 & MU0 & WM0 & ST0' & SW0' & B0q & RD0)
      Hreg HRel Hsame Hmat.
    subst pc'.
    assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
    assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
    assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
    assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
    assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
    assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
    assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
    assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
    assert (HaspE : AC.aspZ regs'' = AC.aspZ regs) by (unfold AC.aspZ; rewrite E2; reflexivity).
    (* back from the normalized memory to the real one *)
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame MU0) as MU.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) mem' m0' HR0 HRel Hsame WM0) as WM.
    pose proof (proj2 (bytes_at_rel rsegs mem' m0' _ _ HRel) B0q) as B380.
    assert (RDW : forall x, ~ LF.outside [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1);
                                          (fr + 3056, fr + 3056 + 32); (sp - 2208, sp)] x ->
              exists b, mrd rsegs mem' (wa x) = Some b).
    { intros x Hx. cbn [LF.outside] in Hx.
      destruct (RD0 x ltac:(lia)) as (b & Hb). exists b.
      rewrite (mrd_rel rsegs mem' m0' _ HRel). exact Hb. }
    assert (HCOV : bp_cover fr (AC.aspZ regs - 2208) (AC.aspZ regs)
                     [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1);
                      (fr + 3056, fr + 3056 + 32); (sp - 2208, sp)]).
    { intros x Hx. cbn [LF.outside] in Hx. rewrite Haspz. lia. }
    assert (HDJ : rt_disjoint [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1);
                               (fr + 3056, fr + 3056 + 32); (sp - 2208, sp)]).
    { unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
        RT_AGLOB_LEN.
      cbn [disjoint_from]. repeat split; first [exact I | lia]. }
    destruct (bp_post B APIf ra empty FF g fr regs regs'' mem mem' md md'
                [(Sfr fr + 370, Sfr fr + 386); (fr + 3040, fr + 3040 + 1); (fr + 3056, fr + 3056 + 32);
                 (sp - 2208, sp)] 2208
                HFRA HENT ltac:(lia) MU WM Hsame HDJ HCOV RDW E2 E3 E4 E8 E9 E19 E26 Hmat) as (HFRA' & HENT').
    (* the stack-window cells after the run (the spills [A + 72 .. A + 96) and [A + 208]) *)
    pose proof HFRA' as HFRA1.
    destruct HFRA1 as (A1 & sp1 & s51 & _ & _ & _ & _ & _ & _ & Hr2' & _ & _ & _ & _ & _ & Hr9' & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin' & _ & _ & HAG' & HWA' & _).
    destruct (bp_q64_stk mem' _ _ (A + 88) Hwin' ltac:(lia) ltac:(lia)) as (pa & Hpa & Hqa).
    destruct (bp_q64_stk mem' _ _ (A + 80) Hwin' ltac:(lia) ltac:(lia)) as (pp & Hpp & Hqp).
    destruct (bp_q64_stk mem' _ _ (A + 72) Hwin' ltac:(lia) ltac:(lia)) as (pn & Hpn & Hqn).
    destruct (bp_q64_stk mem' _ _ (A + 208) Hwin' ltac:(lia) ltac:(lia)) as (f & Hf & Hqf).
    (* the identity_reply window is addressable: FRA's window conjunct, the frame apart from it (fra_frame) *)
    assert (HWADR : addressable mem' (AC.aspZ regs - RIR.REAC_CTRL_IDENTITY_REPLY_K)
                      RIR.REAC_CTRL_IDENTITY_REPLY_K).
    { rewrite HRK, Haspz.
      destruct (fra_frame B APIf ra g fr [] regs'' mem' md' HFRA') as (Hpl' & _ & _ & _).
      pose proof (Hpl' 9072 ltac:(lia)) as Hsep9. rewrite HaspE, Haspz in Hsep9.
      split; [lia|]. split; [lia|]. split; [unfold APPMEM_END; lia|].
      intros i Hi. destruct (HWA' (sp - 9072 + i) ltac:(lia) ltac:(lia)) as (_ & _ & _ & Hb).
      pose proof (Hb 0 ltac:(lia)) as Hb0. rewrite Z.add_0_r in Hb0. exact Hb0. }
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit. exists regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|].
    split.
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |]. rewrite OUR_length.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]. }
    split.
    { split; [unfold rg; rewrite E24; exact H24|].
      apply (bp_addr_r mem' (fr + 3040) 1 (Z_to_bv 8 1)); [lia
        | replace (fr + 3040) with (fr + 8 * 380) by lia; apply bp_m8; exact Hfrm | lia | reflexivity
        | unfold APPMEM_END; lia | intros i Hi; apply Happ'; lia |].
      replace (fr + 3040) with (fr + 8 * 380) by lia. rewrite bp_sh8. exact B380. }
    (* the save area [A, A + 448) is above the frame and the callee window *)
    assert (KSP : forall off v, 0 <= off <= 440 -> spill regs mem off v -> spill regs'' mem' off v).
    { intros off v Hoff (A0 & HA0 & Hq).
      assert (HA0e : A0 = A)
        by (apply (bp_spill_A regs mem off v A A0 HA0 Hq Hr9); unfold APPMEM_END in *; lia).
      subst A0. exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]. }
    split.
    { (* PRO: our[]'s shadow byte Sfr fr + 328 is below the stores' Sfr fr + 370 .. 385 *)
      apply (bp_PRO_keep fr regs regs'' mem mem' KSP); [|exact HPRO].
      intros HOA. apply (bp_addr_keep _ mem mem' (fr + 2624) 6 HOA MU). intros i Hi.
      rewrite (bp_our_sh fr i Hfrm Hi). cbn [LF.outside].
      split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]. }
    split.
    { exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq64 | exact MU |]. rewrite length_le8.
      intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]. }
    split.
    { unfold PL0. split.
      { destruct HCUR as (Hc0 & Hc23 & Hc25). split; [exact Hc0|].
        unfold rg. rewrite E23, E25. split; [exact Hc23 | exact Hc25]. }
      split.
      { unfold IDBe in *. eapply fl_bytes; [exact HIDB | exact MU |].
        unfold RcIdentModel.ID0. rewrite repeat_length. unfold RcIdentModel.ID_SIZE.
        intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]. }
      split.
      { unfold FGBe in *. eapply fl_bytes; [exact HFGB | exact MU |].
        unfold z72. rewrite repeat_length.
        intros x Hx. cbn [LF.outside]. split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]. }
      split.
      { (* RAD: the shadow bytes of the records and of `first` (S(fr) + 336 .. 340 / 346 .. 354 / 360 .. 364)
           are apart from the write set *)
        destruct HRAD as (HRA1 & HRA2 & HRA3). unfold RAD, fragb in *. split; [|split].
        - apply (bp_addr_keep _ mem mem' (fr + 2688) 38 HRA1 MU). intros i Hi.
          pose proof (bp_sh_in fr 2688 i Hfrm ltac:(lia)) as Hs.
          cbn [LF.outside]. split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]].
        - apply (bp_addr_keep _ mem mem' (fr + 2768) 72 HRA2 MU). intros i Hi.
          pose proof (bp_sh_in fr 2768 i Hfrm ltac:(lia)) as Hs.
          cbn [LF.outside]. split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]].
        - apply (bp_addr_keep _ mem mem' (fr + 2880) 40 HRA3 MU). intros i Hi.
          pose proof (bp_sh_in fr 2880 i Hfrm ltac:(lia)) as Hs.
          cbn [LF.outside]. split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]. }
      (* the record-pointer spills [A + 176] = fr + 2688 and [A + 208] = fragb fr *)
      split; [exact (KSP 176 (fr + 2688) ltac:(lia) H176)|].
      split; [exact (KSP 208 (fragb fr) ltac:(lia) H208)|].
      (* the turn-0 first-fragment state: `first`'s bytes and their shadow bytes are apart from the write set *)
      unfold FSj, FSb, u32, b8 in HFS0 |- *. change (fst_at (g_in g) 0) with fs0 in HFS0 |- *.
      unfold fs0 in HFS0 |- *. cbn [fs_have fs_n fs_body] in HFS0 |- *.
      destruct HFS0 as (Hhv & Hn & Hbody & H40 & HFI).
      split; [eapply fl_bytes; [exact Hhv | exact MU |]; rewrite length_le4; intros x Hx; cbn [LF.outside];
              split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]|].
      split; [eapply fl_bytes; [exact Hn | exact MU |]; cbn [length]; intros x Hx; cbn [LF.outside];
              split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]|].
      split; [eapply fl_bytes; [exact Hbody | exact MU |]; cbn [length]; intros x Hx; cbn [LF.outside];
              split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]|].
      split; [|exact HFI].
      apply (bp_addr_keep _ mem mem' (fr + 2880) 40 H40 MU). intros i Hi.
      pose proof (bp_sh_in fr 2880 i Hfrm ltac:(lia)) as Hs.
      cbn [LF.outside]. split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]. }
    split.
    { (* the kind-name table's shadow bytes lie in the low shadow, apart from the write set *)
      apply (bp_addr_keep _ mem mem' KNC.KIND_NAME 112 HKN MU). intros i Hi.
      pose proof (bp_sa_lo (KNC.KIND_NAME + i) ltac:(unfold KNC.KIND_NAME; lia)) as Hk. unfold ASAN_K in Hk.
      cbn [LF.outside]. split; [lia | split; [lia | split; [lia | split; [lia | exact I]]]]. }
    exists A, pa, pp, pn, f.
    split; [unfold rg; rewrite E9; exact Hr9|].
    split; [exact HA64|]. split; [exact Hpa|]. split; [exact Hpp|]. split; [exact Hpn|].
    split; [exact Hqa|]. split; [exact Hqp|]. split; [exact Hqn|]. split; [exact Hqf|].
    rewrite HaspE.
    split; [exact HWADR|].
    apply (bp_ag_addr mem' 0x21200 7 RPC.REAC_CTRL_PARSE_BC 6 HAG');
      [unfold AF.frame_AG; do 4 apply in_cons; apply in_eq | unfold RPC.REAC_CTRL_PARSE_BC; lia | lia
      | unfold RPC.REAC_CTRL_PARSE_BC; lia].
Qed.

End P5.
