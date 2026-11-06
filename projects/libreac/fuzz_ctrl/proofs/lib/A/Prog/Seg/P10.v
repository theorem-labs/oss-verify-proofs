(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v, with its addresses and numbers changed; 417 of its 446 lines of code are new or changed and 367 lines of the source are left out. *)
(* Segment P10 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, libreac v1.9.0 image A): 0x81c4c-0x81c5c, 5 instructions
   (v1.8 0x81bcc-0x81bd8, 4 instructions; S_P10 is CHANGED: the v1.8 `bne a0,s2,82b34` became a `beq` over a `j`
   to the error block, branch relaxation after the function grew).
     81c4c beq a0,s2,81c54 (taken: a0 = -1 the second ports_parse result, s2 = -1; NEW-only);
     81c50 j 82bf4 (NEW-only, not reached); 81c54 li a0,0;
     81c58 ld a1,280(s1) (a1 = code = fr + 3040, the frame byte the spill A + 280 points at, set 0x813e0);
     81c5c jal reac_ports_unknown@0x87848.
   (v1.8 -> v1.9 pcs: 81bcc `bne` -> 81c4c / 81c50, 81bd0 -> 81c54, 81bd4 -> 81c58, 81bd8 -> 81c5c; the return
   address 0x81bdc -> 0x81c60; the error block 82b34 -> 82bf4. The cut Inv_A81c4c is RE-ANCHORED on the first
   instruction of the replacement pair, see SlotInv.v.)
   With p = a0 = 0 the callee fails (pu_ok 0 bs = false): it returns -1 and writes its 16-byte stack frame
   [sp - 16, sp) AND the one byte at code, which it clears. The write to the frame byte is why this segment needs
   the frame-location case split: in the real-stack arm the byte is a_store_ok (it lies in [stklo, APPMEM_END)), in
   the side-stack arm it lies in the FakeStack above its metadata (FRA's side-arm clause FS + 6328320 <= fr), so the
   heap invariant moves across the write with Seg/Tac_fs.a_fs_ok_store_AH.
   Both cuts are SlotInv's: the entry Inv_A81c4c and the exit Inv_A81c60 (a0 = -1, the cleared code byte and XC,
   whose spill clause gives the pointer A + 280 = code), which P11 reads at 0x81c6c-0x81c74. Gap 4 (aslot push
   11): CUR is kept (the run keeps s6 / s9), IDBe / FGBe by fl_bytes (both records lie in the frame below the
   cleared byte fr + 3040). Push 12: the spill [s1 + 144] = fr + 2688 is kept by P7's fra_spill (the cell is
   above sp and above the frame) and the 17 bytes at fr + 2691 stay addressable by sl_addr_keep (W is application
   memory; the cleared byte fr + 3040 is apart from them). Push 13: PRO moves by P1's pro_fra (W is the callee
   window, at or above stklo and below A, and one frame byte). v1.9: the fragment-record spill is [s1 + 192]
   (v1.8 [s1 + 208]); the frame is FRAME_BYTES = 3136 bytes (v1.8 3040, whose last bytes held `code`); the cut
   bundle's round 4 adds `addressable m (fr + 2880) 35` (first.sroa.7) last on both cuts, kept by sl_addr_keep.
   v1.9 re-fit BUILT on v1.9 facts: rc=0 on a build machine workspace (internal path) (a copy of (internal path) at a working branch e3c0b7a9d6,
   FACTS ed6b6b7b0ab) with the cut base a working branch cf5ad0d7203, 2026-10-28. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ports_unknown_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs P1 P7 P8 P9.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* reac_ports_unknown fails on a null record: pu_ok 0 bs = false. *)
Lemma pu_ok_p0 : forall bs, pu_ok 0 bs = false.
Proof. intros bs. unfold pu_ok. rewrite (Z.eqb_refl 0). reflexivity. Qed.

(* Its write set for a non-null output byte. *)
Lemma pu_W_eq : forall sp c, c <> 0 ->
  reac_ports_unknown_W sp c = [(sp - REAC_PORTS_UNKNOWN_FRAME, sp); (c, c + 1)].
Proof.
  intros sp c Hc. unfold reac_ports_unknown_W.
  rewrite (proj2 (Z.eqb_neq c 0) Hc). reflexivity.
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The allocator laws this file takes apart, each destructured ONCE here (a Theorem Labs lane's rule, 2026-10-28: append-only
   at every nesting level; the next generation adds named sub-projections, and then only these proofs move). *)
Lemma p10_laws_store : forall H mem mem' md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
     mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
  (forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH Hmc Hw.
  destruct (AC.a_laws_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md HAH Hmc Hw)
    as (H1 & H2 & H3 & H4).
  exact (conj H1 (conj H2 (conj H3 H4))).
Qed.

Lemma p10_laws_fs_place : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  AC.GT <= FS /\ FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md FS HAH Hw Hr.
  destruct (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw Hr)
    as (H1 & H2 & _ & H4).
  exact (conj H1 (conj H2 H4)).
Qed.

(* The heap invariant and stklo survive the callee's write set [sp - 16, sp) + the frame byte code = fr + 3040.
   Real arm: both parts are a_store_ok (in [stklo, APPMEM_END)). Side arm: the stack part is a_store_ok and the
   frame byte lies in the FakeStack above its metadata (FRA's FS clause), so a_fs_ok_store_AH applies. *)
Lemma ah_code : forall g fr hb regs mem mem' md,
  FRA B APIf ra g fr hb regs mem md ->
  munch [(AC.aspZ regs - REAC_PORTS_UNKNOWN_FRAME, AC.aspZ regs); (fr + 3040, fr + 3040 + 1)] mem mem' ->
  wmono rsegs mem mem' ->
  (forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) -> exists b, mbyte rsegs mem' q = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  (forall q, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md q <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md q) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem mem' md HFRA MU WM HPRES.
  destruct (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hlo & _).
  destruct (fra_sp B APIf ra g fr hb regs mem md HFRA) as (Hspb & _ & HaspB & Hhi & _).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  destruct Hloc as [[Hs50 [Hspfr Hreal]] | [Hs5f [Hfsb [Hfs Hrec]]]].
  - (* real arm: the frame body is in [stklo, APPMEM_END), so both written ranges are a_store_ok *)
    assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia.
      cbn [outside]. split; [|split; [|exact I]].
      - intros [H1 H2]. apply Hns. unfold AC.a_store_ok. right; left.
        unfold REAC_PORTS_UNKNOWN_FRAME, FN_STACK, AF.SLOT_STACK in *. lia.
      - intros [H1 H2]. apply Hns. unfold AC.a_store_ok. right; left.
        pose proof (Hreal (fr + 3040) ltac:(lia)) as Hc. lia. }
    destruct (p10_laws_store (hb ++ g_H g) mem mem' md HAH HstoreC HwmL) as (HAH' & Hown & HSTKeq & HSTKhi).
    split; [exact HAH'|]. split; [exact Hown|]. split; [exact HSTKeq | exact HSTKhi].
  - (* side arm: the frame lies in the FakeStack, above its metadata *)
    destruct (Hfs (fr + 3040) ltac:(lia)) as (bb & Hb64 & Hwb & Hb1 & Hb2).
    pose proof (Hfsb bb Hwb Hb64) as Hbm.
    destruct (p10_laws_fs_place (hb ++ g_H g) mem md bb HAH Hwb Hb64) as (HGT & Hbs & Happ).
    assert (Hfsz : bb + AC.FS_SIZE <= 2 ^ 64)
      by (unfold AC.FS_SIZE, FN_STACK, AF.SLOT_STACK, APPMEM_END in *; lia).
    assert (Hmeta : forall q, fs_meta bb q -> outside
      [(AC.aspZ regs - REAC_PORTS_UNKNOWN_FRAME, AC.aspZ regs); (fr + 3040, fr + 3040 + 1)] q).
    { intros q Hq. pose proof (fs_meta_below bb q Hq) as Hlt.
      cbn [outside]. split; [|split; [|exact I]].
      - unfold REAC_PORTS_UNKNOWN_FRAME, FN_STACK, AF.SLOT_STACK, AC.FS_SIZE in *. lia.
      - lia. }
    assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
      ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
      ~ (bb <= q < bb + AC.FS_SIZE) ->
      ~ (exists b0, bb <= b0 < bb + AC.FS_SIZE /\ q = shadow_addr b0) ->
      mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq Hns Hnfs Hnsh. apply MU. rewrite MState.unsigned_lit by lia.
      cbn [outside]. split; [|split; [|exact I]].
      - intros [H1 H2]. apply Hns. unfold AC.a_store_ok. right; left.
        unfold REAC_PORTS_UNKNOWN_FRAME, FN_STACK, AF.SLOT_STACK in *. lia.
      - intros [H1 H2]. apply Hnfs. lia. }
    destruct (a_fs_ok_store_AH _ _ _ _ _
      [(AC.aspZ regs - REAC_PORTS_UNKNOWN_FRAME, AC.aspZ regs); (fr + 3040, fr + 3040 + 1)]
      (hb ++ g_H g) mem mem' md bb LAWS HAH Hwb Hb64 Hfsz MU HwmL HPRES Hmeta Hagree)
      as (HAH' & Hown & HSTKeq & HSTKhi).
    split; [exact HAH'|]. split; [exact Hown|]. split; [exact HSTKeq | exact HSTKhi].
Qed.

(* The callee contract, a Section Hypothesis (it is proved in reac_ports_unknown.v; that proof is not imported). *)
Hypothesis HPU : reac_ports_unknown_contract.

Lemma p10_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A c lo : Z),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 (-1) -> s2 = Z_to_bv 64 (-1) -> 0 < c < 2 ^ 64 ->
    bytes_at rsegs m (A + 280) (le8 (Z_to_bv 64 c)) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_PORTS_UNKNOWN_FRAME <= bv_unsigned sp ->
    asan_cells m -> shadow_rw m ->
    addressable m c 1 -> wr_at rsegs m c 1 ->
    (c + 1 <= bv_unsigned sp - REAC_PORTS_UNKNOWN_FRAME \/ bv_unsigned sp <= c) ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_PORTS_UNKNOWN_FRAME, bv_unsigned sp); (c, c + 1)] x) ->
    LE.evt rsegs
      (fun ms' => exists (a2' a3' a4' a5' a6' a7' t0' t1' t2' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81c60) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1))
                       (Z_to_bv 64 c) a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81c60) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_PORTS_UNKNOWN_FRAME, bv_unsigned sp); (c, c + 1)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' c [Z_to_bv 8 0])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81c4c) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A c lo -> -> -> Hc H280 HST Hlo HAC HSW Hadc Hwrc Hsep Hout.
  assert (HL280 : ov_read_bytes rsegs m (wa (A + 280)) 8 = Some (le8 (Z_to_bv 64 c))).
  { pose proof (bytes_at_ov_read rsegs m (A + 280) (le8 (Z_to_bv 64 c)) 0 8 H280
      ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (Hcu : bv_unsigned (Z_to_bv 64 c) = c) by (apply MState.unsigned_lit; lia).
  (* v1.9: the walk takes the NEW-only `beq` where v1.8 fell through its `bne`. *)
  step. (* 81c4c beq a0,s2,81c54 (NEW-only; taken, a0 = s2 = -1; the NEW-only 81c50 j 82bf4 is not reached) *)
  if_true.
  step. (* 81c54 li a0,0 *)
  step. (* 81c58 ld a1,280(s1) *)
  step. (* 81c5c jal reac_ports_unknown *)
  pose proof HPU as HP. unfold reac_ports_unknown_contract, REAC_PORTS_UNKNOWN in HP.
  eapply evt_cut.
  { eapply HP with (p := 0) (c := c) (lo := lo) (bs := repeat (Z_to_bv 8 0) 20).
    all: rewrite ?Hcu.
    all: try reflexivity.
    all: try assumption.
    all: try (intros HH; exfalso; apply HH; reflexivity).
    - intros _. split; [exact Hwrc|]. split; [intros HH; exfalso; apply HH; reflexivity | exact Hsep].
    - intros _. exact Hadc.
    - rewrite (pu_W_eq (bv_unsigned sp) c ltac:(lia)). exact Hout. }
  intros ms' (a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & m' & E & MU & WM & ST' & MIi & Hbyte).
  subst ms'.
  rewrite (pu_W_eq (bv_unsigned sp) c ltac:(lia)) in MU.
  rewrite pu_ok_p0 in Hbyte |- *. cbv iota in Hbyte |- *.
  replace (ret_pc (Z_to_bv 64 0x81c60)) with (Z_to_bv 64 0x81c60)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done.
  do 9 eexists. exists m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [exact ST' | exact (Hbyte ltac:(lia))].
Qed.

Lemma seg_P10 : Hcut B APIf ra (Inv_A81c60 B APIf ra) -> Hcut B APIf ra (Inv_A81c4c B APIf ra).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hn & HOUR & HCUR & HPRO & HSP & HADR & HSP192 & HADF &
    HADI & HIDB & HFGB & Ha0 &
    Hs2 & HXC & HAD2880).
  subst c. rewrite SEGS.
  pose proof HXC as (HAblk & Hadc).
  pose proof HFRA as (A1 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm2 & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA4161 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWAd & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  pose proof HRT as (HAC0 & HSW0 & _).
  (* fr_place / fra_A / p7_run / p7_ro_keep / p7_rg_inj / fra_spill (P7) and pro_fra / pro_iv (P1) in their v1.9
     form (a Theorem Labs lane: FRAME_BYTES bounds, spill 192). *)
  destruct (fr_place B APIf ra g fr [] regs mem md HFRA) as (HGT & Hfapp).
  destruct (fra_A B APIf ra g fr [] regs mem md HFRA) as (A & HA9 & HAr & HspA & HfrA & HA416).
  destruct (fra_sp B APIf ra g fr [] regs mem md HFRA) as (Hspb & Hspm & HaspB & Hhi & Hwinsp).
  destruct (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hapart & _ & _ & Hfrwr).
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & _).
  pose proof (HAblk A HA9 HAr) as H280.
  unfold AC.aspZ in Hspb, Hspm, HaspB, Hhi, Hwinsp, HspA, Hapart, Hlo, Haspz.
  assert (Hcb : 0 < fr + 3040 < 2 ^ 64).
  { pose proof (Hfapp (fr + 3040) ltac:(lia)) as Happ.
    unfold app_mem, AC.GT, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (Hwrc : wr_at rsegs mem (fr + 3040) 1).
  { split; [lia|]. split; [lia|]. intros i Hi.
    replace (fr + 3040 + i) with (fr + 3040) by lia. exact (Hfrwr (fr + 3040) ltac:(lia)). }
  assert (Hdisj : fr + FRAME_BYTES <= bv_unsigned (getr regs 2) - REAC_PORTS_UNKNOWN_FRAME \/
                  bv_unsigned (getr regs 2) <= fr).
  { destruct (Hapart REAC_PORTS_UNKNOWN_FRAME
      ltac:(unfold REAC_PORTS_UNKNOWN_FRAME, FN_STACK, AF.SLOT_STACK; lia)) as [Hd|Hd]; [left|right]; lia. }
  assert (Hsep : fr + 3040 + 1 <= bv_unsigned (getr regs 2) - REAC_PORTS_UNKNOWN_FRAME \/
                 bv_unsigned (getr regs 2) <= fr + 3040) by (destruct Hdisj as [Hd|Hd]; lia).
  assert (Hout : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
    outside [(bv_unsigned (getr regs 2) - REAC_PORTS_UNKNOWN_FRAME, bv_unsigned (getr regs 2));
             (fr + 3040, fr + 3040 + 1)] x).
  { intros x Hx. cbn [outside]. split; [|split; [|exact I]].
    - intros [H1 H2].
      destruct Hx as [Hx|[Hx|Hx]];
        unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
          REAC_PORTS_UNKNOWN_FRAME, FN_STACK, AF.SLOT_STACK in *; lia.
    - intros [H1 H2].
      assert (Hxc : x = fr + 3040) by lia. subst x.
      pose proof (Hfapp (fr + 3040) ltac:(lia)) as Happ.
      destruct Hx as [Hx|[Hx|Hx]];
        unfold app_mem, GOT_CELL_K, CELL_K, AC.GT, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG,
          HIGHMEM_BEG in *; lia. }
  apply (p7_run regs (Z_to_bv 64 0x81c4c) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81c60 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = getr regs 26 /\ getr R 10 = Z_to_bv 64 (-1) /\
       getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\
       munch [(bv_unsigned (getr regs 2) - REAC_PORTS_UNKNOWN_FRAME, bv_unsigned (getr regs 2));
              (fr + 3040, fr + 3040 + 1)] mem mem' /\
       wmono rsegs mem mem' /\
       stk rsegs mem' (bv_unsigned (getr regs 2) - FN_STACK) (bv_unsigned (getr regs 2)) /\
       bytes_at rsegs mem' (fr + 3040) [Z_to_bv 8 0])
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply p10_evt with (sp := getr regs 2) (A := A) (c := fr + 3040)
        (lo := bv_unsigned (getr regs 2) - FN_STACK).
      - unfold rg in HA9. exact HA9.
      - unfold a0v, rg in Ha0. exact Ha0.
      - unfold rg in Hs2. exact Hs2.
      - exact Hcb.
      - unfold q64 in H280. exact H280.
      - exact Hwinsp.
      - unfold REAC_PORTS_UNKNOWN_FRAME, FN_STACK, AF.SLOT_STACK. lia.
      - exact HAC0.
      - exact HSW0.
      - exact Hadc.
      - exact Hwrc.
      - exact Hsep.
      - exact Hout. }
    { intros ms' (a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & m' &
        E & MU & WM & ST' & Hbyte).
      eexists _, (Z_to_bv 64 0x81c60), m'. split; [exact E|].
      split; [reflexivity|].
      do 8 (split; [reflexivity|]).
      split; [reflexivity|]. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|].
      split; [exact ST' | exact Hbyte]. }
  - intros R pc' mem' regs' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K10 & K22 & K25 & MU & WM & ST' & Hbyte)
      Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact K2).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact K9).
    assert (Easp : AC.aspZ regs = bv_unsigned (getr regs 2)) by reflexivity.
    (* readability after the write: the stack slice from ST', the code byte from its new value *)
    assert (Hrdc : mrd rsegs mem' (wa (fr + 3040)) = Some (Z_to_bv 8 0)).
    { destruct Hbyte as (_ & _ & Hbb). pose proof (Hbb 0%nat ltac:(cbn; lia)) as Hb'.
      cbn [Z.of_nat nth_error] in Hb'. rewrite Z.add_0_r in Hb'. exact Hb'. }
    assert (HPRES : forall q, 0 <= q < 2 ^ 64 ->
      (exists b, mbyte rsegs mem q = Some b) -> exists b, mbyte rsegs mem' q = Some b).
    { intros q Hq (b & Hb).
      destruct (Z.eq_dec q (fr + 3040)) as [Hqc|Hqc].
      - subst q. exists (Z_to_bv 8 0). exact Hrdc.
      - destruct (Z_lt_le_dec q (bv_unsigned (getr regs 2) - REAC_PORTS_UNKNOWN_FRAME)) as [Hlo1|Hge1].
        + exists b. unfold mbyte in *.
          rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
          rewrite MState.unsigned_lit by lia. cbn [outside]. split; [lia|]. split; [lia | exact I].
        + destruct (Z_lt_le_dec q (bv_unsigned (getr regs 2))) as [Hhi1|Hge2].
          * destruct ST' as (_ & _ & Hs).
            destruct (proj2 (Hs q ltac:(unfold FN_STACK, AF.SLOT_STACK, REAC_PORTS_UNKNOWN_FRAME in *; lia)))
              as [b' Hb'].
            exists b'. exact Hb'.
          * exists b. unfold mbyte in *.
            rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
            rewrite MState.unsigned_lit by lia. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
    assert (MU' : munch [(AC.aspZ regs - REAC_PORTS_UNKNOWN_FRAME, AC.aspZ regs);
                         (fr + 3040, fr + 3040 + 1)] mem mem') by (rewrite Easp; exact MU).
    destruct (ah_code g fr [] regs mem mem' md HFRA MU' WM HPRES) as (HAH' & Hown & HSTKeq & HSTKhi).
    set (W := [(bv_unsigned (getr regs 2) - REAC_PORTS_UNKNOWN_FRAME, bv_unsigned (getr regs 2));
               (fr + 3040, fr + 3040 + 1)]).
    assert (HAW : all_app W).
    { subst W. cbn [all_app]. split; [|split; [|exact I]].
      - intros a Ha. unfold app_mem. right.
        unfold REAC_PORTS_UNKNOWN_FRAME, FN_STACK, AF.SLOT_STACK, HIGHMEM_BEG, APPMEM_END in *. lia.
      - intros a Ha. replace a with (fr + 3040) by lia. exact (Hfapp (fr + 3040) ltac:(lia)). }
    assert (HWlo : forall x, 0 <= x < 6283264 -> outside W x).
    { intros x Hx. subst W. cbn [outside]. split; [|split; [|exact I]].
      - unfold REAC_PORTS_UNKNOWN_FRAME, HIGHMEM_BEG, FN_STACK, AF.SLOT_STACK in *. lia.
      - unfold AC.GT in HGT. lia. }
    assert (Hroa : ro_agree rsegs mem') by exact (p7_ro_keep W mem mem' Hro MU HWlo).
    assert (HWA : forall A' x, rg regs 9 A' -> 0 <= A' < 2 ^ 64 -> A' <= x -> outside W x).
    { intros A' x HA' HA'r Hx. rewrite (p7_rg_inj regs 9 A' A HA' HA9 HA'r HAr) in Hx.
      subst W. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
    assert (HWfr : forall x, fr <= x < fr + 3040 \/ fr + 3041 <= x < fr + FRAME_BYTES -> outside W x).
    { intros x Hx. subst W. cbn [outside]. split; [|split; [|exact I]].
      - unfold REAC_PORTS_UNKNOWN_FRAME in *. destruct Hdisj as [Hd|Hd]; lia.
      - lia. }
    assert (HSwin : g_S g - 4096 < bv_unsigned (getr regs 2) /\ bv_unsigned (getr regs 2) <= g_S g) by lia.
    (* the S-anchored window of mem': kept outside W, the stack part from ST', the code byte from Hrdc *)
    assert (HWwin : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { destruct Hwin as (Hw0 & Hw1 & Hw). split; [exact Hw0|]. split; [exact Hw1|].
      intros x Hx. destruct (Hw x Hx) as (Hv & b & Hb). split; [exact (WM _ Hv)|].
      destruct (Z.eq_dec x (fr + 3040)) as [Hxc|Hxc].
      { subst x. exists (Z_to_bv 8 0). exact Hrdc. }
      destruct (Z_lt_le_dec x (bv_unsigned (getr regs 2) - REAC_PORTS_UNKNOWN_FRAME)) as [Hlt|Hge].
      { exists b. unfold mrd in *. rewrite (MU (wa x)); [exact Hb|]. rewrite wa_unsigned by lia.
        subst W. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
      destruct (Z_lt_le_dec x (bv_unsigned (getr regs 2))) as [Hlt2|Hge2].
      { destruct ST' as (_ & _ & Hs).
        exact (proj2 (Hs x ltac:(unfold FN_STACK, AF.SLOT_STACK, REAC_PORTS_UNKNOWN_FRAME in *; lia))). }
      exists b. unfold mrd in *. rewrite (MU (wa x)); [exact Hb|]. rewrite wa_unsigned by lia.
      subst W. cbn [outside]. split; [lia|]. split; [lia | exact I]. }
    (* FSREC's cells are below stklo, outside the stack window and (but for the frame body) outside W *)
    assert (HrecK : FSREC fr mem -> FSREC fr mem').
    { (* fsrec_stklo states munch / outside in Tac_slot's (UL) flavour; fr_munch_ul / fr_outside_lib bridge them *)
      intros Hrec. eapply fsrec_stklo with (W := W);
        [exact Hrec | exact HAH | exact (proj1 (fr_munch_ul _ mem mem') MU) |].
      intros x Hx Hnf. apply (proj2 (fr_outside_lib _ x)). subst W. cbn [outside]. split; [|split; [|exact I]].
      - intros [H1 H2]. unfold REAC_PORTS_UNKNOWN_FRAME, FN_STACK, AF.SLOT_STACK in *. lia.
      - intros [H1 H2]. apply Hnf. lia. }
    assert (HFRAm : FRA B APIf ra g fr [] regs' mem' md).
    { apply (sl_fr_cl B APIf ra empty FF g fr [] regs regs' mem mem' md W HFRA MU WM Hroa HAW).
      - subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
          RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
          RT_AGLOB_LEN.
        cbn [disjoint_from]. unfold REAC_PORTS_UNKNOWN_FRAME, HIGHMEM_BEG, FN_STACK, AF.SLOT_STACK, AC.GT in *.
        repeat split; first [left; lia | exact I].
      - exact HAH'.
      - exact HSTKeq.
      - exact HWlo.
      - intros x Hx. apply HWfr. lia.
      - intros A' HA' HA'r x Hx. apply (HWA A' x HA' HA'r). lia.
      - intros x Hx. apply (HWA A x HA9 HAr). lia.
      - intros x Hx. subst W. cbn [outside]. split; [|split; [|exact I]].
        + assert (Hin : in_shadow x).
          { assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
            { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
            assert (Hinfr : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
            pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Hfapp _ Hinfr)) as His.
            replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
            unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
          unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin.
          unfold REAC_PORTS_UNKNOWN_FRAME, HIGHMEM_BEG, FN_STACK, AF.SLOT_STACK in *. lia.
        + intros [H1 H2].
          assert (Hxc : x = fr + 3040) by lia.
          assert (Hin : in_shadow x).
          { assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
            { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
            assert (Hinfr : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
            pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Hfapp _ Hinfr)) as His.
            replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
            unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
          pose proof (Hfapp (fr + 3040) ltac:(lia)) as Happ.
          rewrite <- Hxc in Happ.
          unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *. lia.
      - intros A' HA' HA'r x Hx. apply (HWA A' x HA' HA'r). lia.
      - exact HWwin.
      - exact HrecK.
      - exact Fr2.
      - rewrite Hreg; exact K3.
      - rewrite Hreg; exact K4.
      - rewrite Hreg; exact K8.
      - exact Fr9.
      - rewrite Hreg; exact K19.
      - rewrite Hreg; exact K26. }
    assert (HFRA' : FRA B APIf ra g fr [] regs' mem' md')
      by exact (sl_fra_move B APIf ra g fr [] regs' regs' mem' md md' HFRAm
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hmat).
    (* ENT: the write set is the callee's window (inside the slot window) and one frame byte *)
    assert (HENT' : ENT APIf g [] mem' md').
    { assert (HENT1 : ENT APIf g [] mem' md).
      { eapply ent_store with (W := W);
          [exact HENT | exact HFRA
          | first [exact MU | exact (proj1 (fr_munch_ul _ mem mem') MU)
                            | exact (proj2 (fr_munch_ul _ mem mem') MU)]
          | | exact HSTKeq | exact HSTKhi | exact (fun a _ Ho => proj2 (Hown a) Ho)].
        intros x Hx.
        destruct (Z.eq_dec x (fr + 3040)) as [Hxc|Hxc]; [right; right; left; lia|].
        destruct (Z_lt_le_dec x (bv_unsigned (getr regs 2) - REAC_PORTS_UNKNOWN_FRAME)) as [Hlt|Hge].
        { left. first [ (subst W; cbn; split; [lia | split; [lia | exact I]])
                      | (apply fr_outside_lib; subst W; cbn; split; [lia | split; [lia | exact I]]) ]. }
        destruct (Z_lt_le_dec x (bv_unsigned (getr regs 2))) as [Hlt2|Hge2].
        { right. left. destruct HSwin as (HSw1 & HSw2).
          unfold REAC_PORTS_UNKNOWN_FRAME, AF.SLOT_STACK in *. lia. }
        left. first [ (subst W; cbn; split; [lia | split; [lia | exact I]])
                    | (apply fr_outside_lib; subst W; cbn; split; [lia | split; [lia | exact I]]) ]. }
      eapply ent_mat; [exact HENT1 | exact Hmat]. }
    assert (HXC' : XC fr regs' mem').
    { apply (xc_run fr regs regs' mem mem' W HXC MU HAW); [|exact Fr9].
      intros A' HA' HA'r x Hx. apply (HWA A' x HA' HA'r). lia. }
    assert (HOUR' : OURb g fr mem').
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |].
      rewrite OUR_length. intros x Hx. apply HWfr. lia. }
    assert (HCUR' : CUR g (c0 (g_in g)) regs').
    { destruct HCUR as (Hc & H22 & H25). split; [exact Hc|]. unfold rg in *.
      split; [rewrite Hreg, K22; exact H22 | rewrite Hreg, K25; exact H25]. }
    (* push 13: PRO (W is the callee window, at or above stklo and below A, and the frame byte fr + 3040) *)
    assert (HPRO' : PRO g fr regs' mem').
    { apply (pro_fra B APIf ra g fr [] regs regs' mem mem' md W A HFRA HPRO HA9 HAr MU Fr9).
      subst W. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold pro_iv; cbn [fst snd].
      - left. unfold REAC_PORTS_UNKNOWN_FRAME, FN_STACK, AF.SLOT_STACK in Hlo |- *. lia.
      - right; left. lia. }
    (* pushes 12 / 14: the spills [s1 + 144] / [s1 + 192] are above sp and above the frame; the 17 bytes at
       fr + 2691, the record ranges (fragb fr, 72) / (fr + 2688, 38) and (round 4) first.sroa.7's 35 bytes at
       fr + 2880 keep their shadow (W is application memory) *)
    assert (HSP' : spill regs' mem' 144 (fr + 2688))
      by exact (fra_spill B APIf ra g fr [] regs regs' mem mem' md W 144 (fr + 2688) HFRA ltac:(lia) HSP MU Fr9 HWA).
    assert (HADR' : addressable mem' (fr + 2691) 17) by exact (sl_addr_keep mem mem' W (fr + 2691) 17 HADR MU HAW).
    assert (HSP192' : spill regs' mem' 192 (fragb fr))
      by exact (fra_spill B APIf ra g fr [] regs regs' mem mem' md W 192 (fragb fr) HFRA ltac:(lia) HSP192 MU Fr9 HWA).
    assert (HADF' : addressable mem' (fragb fr) 72) by exact (sl_addr_keep mem mem' W (fragb fr) 72 HADF MU HAW).
    assert (HADI' : addressable mem' (fr + 2688) 38) by exact (sl_addr_keep mem mem' W (fr + 2688) 38 HADI MU HAW).
    assert (HAD2880' : addressable mem' (fr + 2880) 35)
      by exact (sl_addr_keep mem mem' W (fr + 2880) 35 HAD2880 MU HAW).
    assert (HIDB' : IDBe g fr RcIdentModel.ID0 mem').
    { unfold IDBe in *. eapply fl_bytes; [exact HIDB | exact MU |].
      unfold RcIdentModel.ID0. rewrite repeat_length. unfold RcIdentModel.ID_SIZE.
      intros x Hx. apply HWfr. lia. }
    assert (HFGB' : FGBe g fr z72 mem').
    { unfold FGBe in *. eapply fl_bytes; [exact HFGB | exact MU |].
      unfold z72. rewrite repeat_length. intros x Hx. apply HWfr. lia. }
    assert (HIexit : Inv_A81c60 B APIf ra g (mkCfg (mkst regs' (Z_to_bv 64 0x81c60) mem' (seg_rom rsegs)) md')).
    { exists regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA'|]. split; [exact HENT'|]. split; [exact Hn|]. split; [exact HOUR'|].
      split; [exact HCUR'|]. split; [exact HPRO'|]. split; [exact HSP'|]. split; [exact HADR'|].
      split; [exact HSP192'|]. split; [exact HADF'|]. split; [exact HADI'|].
      split; [exact HIDB'|].
      split; [exact HFGB'|].
      split; [unfold a0v, rg; rewrite Hreg; exact K10|].
      split; [unfold b8; exact Hbyte|]. split; [exact HXC' | exact HAD2880']. }
    pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End S.
