(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its module paths and module names changed; 554 of its 593 lines of code are new or changed and 357 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F7.v, with its addresses and numbers changed; 268 of its 371 lines of code are new or changed and 490 lines of the source are left out. *)
(* Segment F19 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): the range 0x8264c-0x82664.
   bnez a0,82fa4 (not taken: the F18 bcmp returned 0); addi a1,s2,6; li a0,7; bltu a1,a0,82fa0 (T43, not taken:
   a1 = Phi + 6 does not wrap and Phi <> 0, so Phi + 6 >= 7); li a2,6; ld a0,96(s1); jal wrapper_bcmp@0x82664; the
   run goes through the call to the return point 0x82668. Entry cut Inv_B8264c_at (F18's exit), exit cut
   Inv_B82668_at (F20's entry), both of lib/B/Prog/SlotInv.v. The image-B port of lib/A/Prog/Seg/F19.v: image B
   keeps Phi in s2 (reg 18), k in s8 (reg 24), the sum flag in s9 (reg 25), the record pointer kp in the spill
   [s1+280], the bcmp operand in [s1+96], and adds the UBSan check T43 at 0x82658. The wrapper's instrumented check of
   [s1+96] and Phi+6 passes from their addressability; the record invariant rec_inv crosses the call (the call writes
   only its stack scratch). The helpers of the call are lib/B/Prog/Seg/F18.v's, whose segment calls the same wrapper:
   the Lib-evt -> SR bridge sl_run_lib, FRA / ENT across the call (bcmp_fra), the runtime cells the wrapper reads
   (bcmp_cells), rec_inv / LK / FM / FTURN / IFS across the scratch write, and the normalized-memory moves that give
   the wrapper's mem_inv premise from FRA's ro_agree (MemNorm.evt_normalize). Adopt 6 (bc14aa7165): both cuts
   carry FTURN and IFS (S j); Phi's live block lies below stklo (a_laws_blocks), the frame records and `first` in the
   frame, so both miss the scratch. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require memcmp_c bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require F18.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_c.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec.StrFun.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module MN := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNorm.
Module S18 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg.F18.

(* The wrapper_bcmp constants: the stack-scratch size of bcmp_wrap_c (the one SlotInv's cuts name), the rest F18.v's. *)
Local Notation BCMP_WRAP_K := BW.BCMP_WRAP_K.
Local Notation BCMP := S18.BCMP.
Local Notation REAL_BCMP := S18.REAL_BCMP.
Local Notation REAL_MEMCMP := S18.REAL_MEMCMP.
Local Notation GOT_CF := S18.GOT_CF.
Local Notation CF := S18.CF.
Local Notation MEMCMP := S18.MEMCMP.
Local Notation memcmp_model := SF.memcmp_model.

(* `bltu x,y` is not taken when y <= x (unsigned); the left operand is compared through its value mod 2^64. *)
Lemma f19_ltu_false : forall x y, 0 <= y < 2 ^ 64 -> y <= x mod 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hy Hxy. unfold bv_ltu. rewrite MState.unsigned_lit_wrap, (MState.unsigned_lit y) by lia.
  apply Z.ltb_ge. lia.
Qed.

(* Two byte lists read at one address with one length are the same list (Seg/F13.v ba_det). *)
Lemma f19_ba_det : forall m a bs cs, bytes_at rsegs m a bs -> bytes_at rsegs m a cs ->
  length bs = length cs -> bs = cs.
Proof.
  intros m a bs cs (_ & _ & Hb) (_ & _ & Hc) HL.
  apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
  - rewrite <- (Hb i Hi), <- (Hc i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs i) Hi), (proj2 (nth_error_None cs i) ltac:(lia)). reflexivity.
Qed.

(* Two words read at one address are the same value (Seg/F13.v q64_det): the record pointer kp of the entry cut,
   read at [A+280], is FLI's fr + 176. *)
Lemma f19_q64_det : forall m a v1 v2, q64 m a v1 -> q64 m a v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> v1 = v2.
Proof.
  intros m a v1 v2 H1 H2 Hb1 Hb2.
  assert (E : le8 (Z_to_bv 64 v1) = le8 (Z_to_bv 64 v2))
    by (apply (f19_ba_det m a); [exact H1 | exact H2 | rewrite !length_le8; reflexivity]).
  apply (f_equal le_bytes_to_word) in E. rewrite !le_bytes_to_word_le8 in E.
  apply (f_equal (bv_unsigned (n:=64))) in E. rewrite !MState.unsigned_lit in E by lia. exact E.
Qed.

(* A spill base A' read through s1 with a cell q64 at A' + off (off < 448) is the spill base A of FRA, when
   0 <= A and A + 448 <= 2^64 (lib/B/Prog/Seg/F7.v f7_base_eq). *)
Lemma f19_base_eq : forall (A A' off v : Z) (m : word -> option byte),
  Z_to_bv 64 A' = Z_to_bv 64 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off < 448 ->
  q64 m (A' + off) v -> A' = A.
Proof.
  intros A A' off v m E HA0 HA1 Hoff Hq.
  unfold q64, bytes_at in Hq. destruct Hq as (Hq0 & Hq1 & _).
  rewrite length_le8 in Hq1. change (Z.of_nat 8) with 8 in Hq1.
  apply (f_equal (bv_unsigned (n:=64))) in E. rewrite !MState.unsigned_lit_wrap in E.
  rewrite (Z.mod_small A) in E by lia.
  Z.div_mod_to_equations. lia.
Qed.

Section F19.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contract of wrapper_bcmp (lib/B/Prog/bcmp_wrap_c.v). *)
Hypothesis HBC : BW.bcmp_wrap_contract.

(* The run 0x8264c -> 0x82668: the bnez on a0 = 0 and the bltu T43 fall through, then the bcmp wrapper call on
   [s1+96] and Phi+6 (R = Phi). *)
Lemma f19_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A L R : Z) (ls rs : list byte) (vcmp lo : Z),
    s1v = Z_to_bv 64 A -> s2v = Z_to_bv 64 R -> a0 = Z_to_bv 64 0 ->
    0 <= L < 2 ^ 64 -> 0 < R -> R + 50 <= 2 ^ 64 ->
    bytes_at rsegs m (A + 96) (le8 (Z_to_bv 64 L)) ->
    bytes_at rsegs m L ls -> (6 <= length ls)%nat ->
    bytes_at rsegs m (R + 6) rs -> (6 <= length rs)%nat ->
    memcmp_model ls rs 6 = Some vcmp ->
    mem_inv rsegs m -> addressable m L 6 -> addressable m (R + 6) 6 ->
    app_mem (L + 6) -> app_mem (L + 7) -> app_mem (R + 12) -> app_mem (R + 13) ->
    (L + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 12 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R + 6) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    LE.evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 R) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82668) fc None m' (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ shadow_rw m')
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x8264c) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A L R ls rs vcmp lo -> -> -> HLb HR0 HR50 H96 HBL HLls HBR HLrs Hmm HMI HADL HADR
    HaL6 HaL7 HaR12 HaR13 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255.
  assert (HL96 : ov_read_bytes rsegs m (wa (A + 96)) 8 = Some (le8 (Z_to_bv 64 L))).
  { pose proof (bytes_at_ov_read rsegs m (A + 96) (le8 (Z_to_bv 64 L)) 0 8 H96 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  (* 0x8264c bnez a0,82fa4: a0 = 0, not taken *)
  step.
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      let v := eval vm_compute in cnd in replace cnd with v by (vm_compute; reflexivity); cbv iota
  | _ => idtac
  end.
  (* 0x82650 addi a1,s2,6 (a1 = Phi + 6); 0x82654 li a0,7; 0x82658 bltu a1,a0,82fa0 (T43): 0 < Phi and
     Phi + 50 <= 2^64, so 7 <= Phi + 6 < 2^64 and the branch to the unimp at 0x82fa0 is not taken *)
  step. step. step.
  lazymatch goal with
  | |- LE.evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      replace cnd with false;
      [cbv iota | symmetry; apply f19_ltu_false; [lia | rewrite Z.mod_small by lia; lia]]
  end.
  (* 0x8265c li a2,6; 0x82660 ld a0,96(s1); 0x82664 jal wrapper_bcmp *)
  step. step. step.
  pose proof HBC as HB. unfold BW.bcmp_wrap_contract, BW.BCMP_WRAP_K in HB. cbv zeta in HB.
  assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (ER6 : bv_unsigned (Z_to_bv 64 (R + 6)) = R + 6) by (apply unsigned_lit; lia).
  assert (E6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  eapply evt_cut.
  { eapply HB with (ls := ls) (rs := rs) (v := vcmp) (lo := lo).
    all: rewrite ?EL, ?ER6, ?E6.
    - exact HBL.
    - exact HBR.
    - change (Z.to_nat 6) with 6%nat; exact Hmm.
    - exact HMI.
    - clear; lia.
    - exact HADL.
    - exact HADR.
    - right; exact HaL6.
    - right; replace (R + 6 + 6) with (R + 12) by lia; exact HaR12.
    - right; exact HaL7.
    - right; replace (R + 6 + 7) with (R + 13) by lia; exact HaR13.
    - exact HdjL.
    - replace (R + 6 + 6) with (R + 12) by lia; exact HdjR.
    - exact HST.
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - exact HAC.
    - exact HSW.
    - exact HRB.
    - exact HRM.
    - exact HGC.
    - exact HC254.
    - exact HC255. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'
              & E & MU & WM & MI' & ST' & AC' & SW' & HBpl & HBpr).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x82668)) with (Z_to_bv 64 0x82668)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply evt_done.
  exists (Z_to_bv 64 0x82668), a1'', a2'', a3'', a4'', a5'', a6'', a7'', t0'', t1'', t2'', t3'', t4'', t5'', t6'', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC' | exact SW'].
Qed.

(* seg_F19 on SlotInv's cuts (S_F19 of the image-B segment forms): from the F19 cut Inv_B8264c_at (F18's exit: a0 = 0,
   the operands [s1+96] / Phi+6 of this bcmp, rec_inv) through the call to the F20 cut Inv_B82668_at. FRA gives what
   the entry cut text leaves out: the frame in app memory (fra_app), the frame apart from the wrapper's scratch
   (fra_frame at K = BCMP_WRAP_K) and sp <= APPMEM_END (sp <= A <= S < APPMEM_END). The exit names the kind record's
   halfword at fr + 196: the record pointer kp of the entry cut is the word [A+280], which FLI gives as fr + 176
   (f19_q64_det), and the sum flag s9 (FM). *)
Lemma seg_F19 : forall j : nat,
  Hat B APIf ra (Inv_B82668_at B APIf ra) j -> Hat B APIf ra (Inv_B8264c_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HLK & Hs4 & HFM &
    (A & kp & L2 & ls2 & rs2 & Hs1 & HAb & HspA & Hs2 & Hs8 & Hs6 & Ha0 & HRI &
     H80 & HL2b & HBL2 & HLls2 & HBR2 & HLrs2 & Hmm2 & HADL2 & HADR2 & HaL26 & HaL27 & HaR212 & HaR213 & HdjL2 & HdjR2 &
     Hdj50 & Hdjkp) & HTURN & HIFS).
  subst c. rewrite SEGS.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof HRI as (Hphi0 & Hphi50 & _).
  pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (_ & Hfrapp).
  assert (Hfrb : 0 <= fr /\ fr + FRAME_BYTES < 2 ^ 64).
  { pose proof (Hfrapp fr ltac:(lia)) as H1. pose proof (Hfrapp (fr + FRAME_BYTES - 1) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in H1, H2. lia. }
  destruct (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hfrw & _ & _ & _).
  assert (Hdisjfr : fr + FRAME_BYTES <= AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= fr)
    by (apply Hfrw; unfold FN_STACK, BW.BCMP_WRAP_K, AF.SLOT_STACK; lia).
  destruct (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hlow & HW0).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspillq & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HaspB : AC.aspZ regs <= APPMEM_END) by lia.
  destruct (S18.bcmp_cells sp mem md HRT) as (HAC0 & HSW0 & HRBc & HRMc & HGC & HC254 & HC255).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH) as Hstkhi.
  (* Phi's live block (Phi, a_size len) ends at or below stklo <= sp - FN_STACK (fra_win), below the scratch *)
  destruct (lw_blocks (APIf rc) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi
              (AC.a_size (flen g j)) HAH ltac:(apply in_or_app; left; unfold hb1; cbn [In]; left; reflexivity))
    as [_ _ Hphiend _ _].
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  (* kp = fr + 176: the cut's word [A+280] and FLI's spill [A+280] = fr + 176 over the same spill base A = s1 *)
  assert (EA2 : A2 = A).
  { assert (E : Z_to_bv 64 A2 = Z_to_bv 64 A) by (unfold rg in Hr9, Hs1; rewrite <- Hr9; exact Hs1).
    apply (f_equal (bv_unsigned (n:=64))) in E.
    rewrite !MState.unsigned_lit in E by (unfold APPMEM_END, HIGHMEM_BEG, AF.SLOT_STACK in *; lia). exact E. }
  subst A2.
  assert (Ekp : kp = fr + 176).
  { pose proof HLK as (_ & _ & _ & HFLI0).
    destruct HFLI0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (A3 & HA3 & Hq3) & _).
    assert (EA3 : A3 = A).
    { apply (f19_base_eq A A3 280 (fr + 176) mem); [| lia | unfold APPMEM_END in *; lia | lia | exact Hq3].
      unfold rg in HA3, Hs1. rewrite <- HA3. exact Hs1. }
    subst A3.
    pose proof HRI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkpub & Hkp0 & _).
    apply (f19_q64_det mem (A + 280) kp (fr + 176) Hs6 Hq3); lia. }
  assert (HK1 : AC.aspZ regs - FN_STACK + BCMP_WRAP_K <= AC.aspZ regs)
    by (unfold FN_STACK, AF.SLOT_STACK, BW.BCMP_WRAP_K; lia).
  assert (HK2 : HIGHMEM_BEG <= AC.aspZ regs - FN_STACK) by lia.
  set (W := [(AC.aspZ regs - BCMP_WRAP_K, AC.aspZ regs)]).
  apply (S18.sl_run_lib regs (Z_to_bv 64 0x8264c) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x82668 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
       getr R0 26 = getr regs 26 /\
       getr R0 18 = getr regs 18 /\ getr R0 22 = getr regs 22 /\ getr R0 24 = getr regs 24 /\
       getr R0 27 = getr regs 27 /\ getr R0 20 = getr regs 20 /\ getr R0 25 = getr regs 25 /\
       getr R0 10 = Z_to_bv 64 0 /\
       Frame.munch W mem mem' /\ Frame.wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs))
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* The wrapper contract asks for mem_inv, which the cut does not carry: run f19_evt on the normalized memory
       (mem_inv_normalize) and carry the run back to mem by MemNorm.evt_normalize from FRA's ro_agree. *)
    pose proof (MN.mem_rel_normalize rsegs mem Hro) as REL0.
    eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply (MN.evt_normalize rsegs); [exact S18.f18_wx | exact Hro |].
      eapply f19_evt with (A := A) (L := L2) (R := phi) (ls := ls2) (rs := rs2) (vcmp := 0)
        (lo := AC.aspZ regs - FN_STACK).
      - unfold rg in Hs1; exact Hs1.
      - unfold rg in Hs2; exact Hs2.
      - unfold rg in Ha0; exact Ha0.
      - exact HL2b.
      - exact Hphi0.
      - exact Hphi50.
      - unfold q64 in H80; exact (MN.bytes_at_normalize rsegs mem _ _ Hro H80).
      - exact (MN.bytes_at_normalize rsegs mem _ _ Hro HBL2).
      - exact HLls2.
      - exact (MN.bytes_at_normalize rsegs mem _ _ Hro HBR2).
      - exact HLrs2.
      - exact Hmm2.
      - exact (MN.mem_inv_normalize rsegs mem).
      - exact (S18.addressable_norm mem L2 6 Hro HADL2).
      - exact (S18.addressable_norm mem (phi + 6) 6 Hro HADR2).
      - exact HaL26.
      - exact HaL27.
      - exact HaR212.
      - exact HaR213.
      - exact HdjL2.
      - exact HdjR2.
      - exact (S18.stk_norm mem _ _ Hro HW0 ltac:(unfold AC.GT, HIGHMEM_BEG in *; lia)).
      - exact HK1.
      - exact HK2.
      - exact HaspB.
      - exact (S18.asan_cells_norm mem Hro HAC0).
      - exact (S18.shadow_rw_norm mem Hro HSW0).
      - exact (MN.bytes_at_normalize rsegs mem _ _ Hro HRBc).
      - exact (MN.bytes_at_normalize rsegs mem _ _ Hro HRMc).
      - exact (MN.bytes_at_normalize rsegs mem _ _ Hro HGC).
      - exact (MN.bytes_at_normalize rsegs mem _ _ Hro HC254).
      - exact (MN.bytes_at_normalize rsegs mem _ _ Hro HC255). }
    { intros ms' (s0 & (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0'
                  & E & MU & WM & MI' & ST' & AC' & SW') & REL & SAME).
      subst s0.
      destruct (S18.ms_rel_MS ms' _ _ _ _ _ _ _ REL) as (Ems & HREL).
      eexists _, (Z_to_bv 64 0x82668), (ms_mem ms'). split; [exact Ems|].
      split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [unfold rg in Hs1; rewrite Hs1; reflexivity|]. split; [reflexivity|].
      split; [reflexivity|].
      split; [unfold rg in Hs2; rewrite Hs2; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|].
      split; [exact (MN.munch_rel rsegs _ mem (MN.normalize rsegs mem) (ms_mem ms') m0' REL0 HREL SAME MU)|].
      split; [exact (MN.wmono_rel rsegs mem (MN.normalize rsegs mem) (ms_mem ms') m0' REL0 HREL SAME WM)|].
      split; [exact (MN.ro_agree_of_mem_rel rsegs (ms_mem ms') m0' HREL)|].
      exact (S18.stk_back (ms_mem ms') m0' _ _ HREL ST'). }
  - intros R0 pc' mem' regs' md' (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er26 & Er18 & Er22 & Er24 & Er27 &
      Er20 & Er25 & Er10 & MU & WM & HRO' & ST') Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 0) by (rewrite Hreg; exact Er10).
    assert (HaspEq : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    destruct (S18.bcmp_fra B APIf ra empty FF g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem mem' md md' A
                HFRA HENT Hs1 HAb HspA Hfrapp MU WM HRO' ST' Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat)
      as (HFRA'' & HENT'').
    assert (Hallapp : all_app W).
    { subst W. cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      rewrite Haspz in *. unfold BW.BCMP_WRAP_K, HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia. }
    assert (HOW : forall x, (x < AC.aspZ regs - BCMP_WRAP_K \/ AC.aspZ regs <= x) -> Frame.outside W x)
      by (intros x Hx; subst W; apply S18.out1; exact Hx).
    assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> forall x, A' <= x < A' + 448 -> Frame.outside W x).
    { intros A' HA' x Hx. subst W.
      apply (S18.spill_outW regs A A' (AC.aspZ regs) x Hs1 HAb HspA HA'); [| unfold APPMEM_END in *; lia | exact Hx].
      rewrite Haspz in *. unfold BW.BCMP_WRAP_K, HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
    assert (HRI' : rec_inv g j phi A kp mem').
    { apply (S18.rec_inv_kept g j phi A kp mem mem' W HRI MU).
      - intros x Hx. apply HOW. destruct Hdj50 as [Hd|Hd]; lia.
      - intros x Hx. apply HOW. lia.
      - intros x Hx. apply HOW. rewrite Haspz. unfold BW.BCMP_WRAP_K, AF.SLOT_STACK in *. lia.
      - intros Hkp0 Hkpb x Hx. apply HOW. destruct Hdjkp as [Hd|Hd]; lia. }
    assert (HWphi : forall x, phi <= x < phi + t_len (g_in g) j -> Frame.outside W x).
    { intros x Hx. apply HOW. left. unfold AC.a_size, flen in Hphiend.
      unfold FN_STACK, AF.SLOT_STACK, BW.BCMP_WRAP_K in *. lia. }
    assert (HWfr : forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x).
    { intros x Hx. apply HOW. destruct Hdisjfr as [Hd|Hd]; lia. }
    destruct HRI' as (Hp0 & Hp50 & Hfl & Htk & Hpap & H312 & H18 & H34 &
      field16 & v14 & v15 & v16 & v17 & H248 & Hf16 & Hkpub & Hkp0 & Hb14 & Hb15 & Hb16 & Hb17 &
      Rv14 & Rv15 & Rv16 & Rv17 & Hz14 & Hz15 & Hz16 & Hz17 & Heq1 & Heq2).
    assert (HIexit : Inv_B82668_at B APIf ra g j (mkCfg (mkst regs' (Z_to_bv 64 0x82668) mem' (seg_rom rsegs)) md')).
    { exists phi, regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA''|]. split; [exact HENT''|]. split; [exact Hgn|]. split; [exact Hj|].
      split.
      { destruct HHB as (Hphinz & Hphiad). split; [exact Hphinz|].
        eapply sl_addr_keep; [exact Hphiad | exact MU | exact Hallapp]. }
      split.
      { destruct HLK as (Hj' & (A3 & HA3 & Hq240) & HOURb & HFLI). split; [exact Hj|]. split.
        - exists A3. split; [unfold rg in *; rewrite Fr9; exact HA3|].
          unfold q64 in *. eapply (fl_bytes W); [exact Hq240 | exact MU |]. rewrite length_le8. intros x Hx.
          subst W. apply (S18.spill_outW regs A A3 (AC.aspZ regs) x Hs1 HAb HspA HA3); [| | lia].
          + rewrite Haspz in *. unfold BW.BCMP_WRAP_K, HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
          + unfold APPMEM_END in *. lia.
        - split.
          + unfold OURb in *. apply (fl_bytes W mem mem' (fr + 2624) (OUR (g_in g)) HOURb MU).
            rewrite OUR_length. intros x Hx. apply HOW. destruct Hdisjfr as [Hd|Hd]; lia.
          + apply (S18.f18_fli_keep g fr regs regs' mem mem' W HFLI Fr9 Fr27 HA9 MU WM Hallapp).
            * intros x Hx. apply HOW. destruct Hdisjfr as [Hd|Hd]; lia.
            * intros x Hx. apply HOW. left.
              rewrite Haspz in *. unfold BW.BCMP_WRAP_K, HIGHMEM_BEG, AF.SLOT_STACK in *. lia. }
      split; [unfold rg in *; rewrite Fr20; exact Hs4|].
      split; [exact (S18.f18_fm_keep g j phi fr regs regs' mem mem' W HFM Fr9 Fr22 Fr24 Fr25 HA9 MU)|].
      split; [unfold rg; rewrite Fr18; exact Hs2|].
      split; [unfold rg; rewrite Fr24; exact Hs8|].
      split; [unfold rg; exact Fr10|].
      split; [exact Hp0|]. split; [exact Hp50|]. split; [exact Hfl|]. split; [exact Htk|].
      split; [exact H18|]. split; [exact H34|].
      split; [destruct HFM as (_ & _ & _ & H25 & _); unfold rg in *; rewrite Fr25; exact H25|].
      split; [rewrite HaspEq; destruct Hdj50 as [Hd|Hd]; [left | right]; unfold BW.BCMP_WRAP_K in *; lia|].
      split; [exact (S18.f18_turn_keep g j phi regs regs' mem mem' W HTURN Fr9 HA9 HWphi MU)|].
      split; [exact (S18.f18_ifs_keep g fr (S j) regs regs' mem mem' W HIFS MU Hallapp HWfr)|].
      exists v14, v15, v16, v17, field16.
      split; [replace (fr + 196) with (kp + 20) by lia; exact Hf16|].
      split; [exact Hb14|]. split; [exact Hb15|]. split; [exact Hb16|]. split; [exact Hb17|].
      split; [exact Rv14|]. split; [exact Rv15|]. split; [exact Rv16|]. split; [exact Rv17|].
      split; [exact Hz14|]. split; [exact Hz15|]. split; [exact Hz16|]. split; [exact Hz17|].
      split; [exact Heq1 | exact Heq2]. }
    pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End F19.
