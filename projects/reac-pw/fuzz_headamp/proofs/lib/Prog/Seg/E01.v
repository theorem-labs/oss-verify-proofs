(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 223 of its 253 lines of code are new or changed and 544 lines of the source are left out. *)
(* Segment E01 of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (plain): [0x12f88, 0x13040], ENTRY -> K13044
   (Prog/LLVMFuzzerTestOneInput_c.v's S_E01).
   The prologue (0x12f88 `addi sp,sp,-0x230`; ra, s0 .. s11 saved at S - 8 .. S - 104 by 0x12f8c .. 0x12fbc; fs0,
   fs1, fs2 saved at S - 112 .. S - 128 by 0x12fc0 .. 0x12fc8), the n >= 2^26 exit not taken (0x12fcc `srli
   a2,a1,26`, 0x12fd0 `beqz a2`: GV bounds n below 2^26), the two cursor bytes (fuzz.h's fuzz_u8 twice:
   0x12fd8 `mv s3,a0`, 0x12fdc `beqz a1`: n = 0 gives s7 = s2 = s6 = 0 and s3 = data (0x13000 .. 0x1300c); else
   0x12fe0 `lbu a0,0(s3)`, s7 = data[0] & 1, and 0x12fec `bne a1,a2` with a2 = 1: n = 1 gives s2 = s6 = 0 and
   s3 = data + 1 (0x12ff0 .. 0x12ffc); n >= 2 reads data[1] (0x13010), s2 = n - 2, s3 = data + 2 and s6 =
   data[1] - 10 ((data[1] * 0xcd) >> 11) = data[1] mod 10 (0x13014 .. 0x13030)), s0 = 0x5000 and s1 = 19744
   (0x13034 `lui s0,5`, 0x13038 `addiw s1,s0,-0x2e0`), a0 = s1, and malloc(19744) at 0x13040 with ra = 0x13044
   through Tac_b1.b1_malloc_call from hb = [], whose continuation gives Inv_K13044. No other call.
   Adapted from reac-pw/fuzz_role's Prog/Seg/E01.v (one cursor byte, no FP save), in turn reac-pw/fuzz_pin's
   (libreac/fuzz_ctrl's released segments A01 and F01): the run from Inv_ENTRY on the normalized memory, FR with
   hb = [], malloc as a Kind B step. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.Seg Require Import Tac_slot Tac_b1.
Import ListNotations.
Open Scope Z_scope.

(* ---- The quantities of the two cursor bytes (SlotInv's g_null, g_cap, g_k, g_src for inp = g_in g, p = g_p g) ---- *)
Definition e01_null (inp : list byte) : Z := Z.land (fst (Cursor.fuzz_u8 inp)) 1.
Definition e01_cap (inp : list byte) : Z := fst (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 inp))) mod 10.
Definition e01_k (inp : list byte) : Z := Z.of_nat (length inp) - Z.min 2 (Z.of_nat (length inp)).
Definition e01_src (p : Z) (inp : list byte) : Z := p + Z.min 2 (Z.of_nat (length inp)).

(* ---- Bytes and words ---- *)
Lemma e01_rd0 : forall m (a : word) b l, bytes_at rsegs m (bv_unsigned a) (b :: l) ->
  ov_read_bytes rsegs m a 1 = Some [b].
Proof.
  intros m a b l H.
  assert (E : a = wa (bv_unsigned a + Z.of_nat 0)).
  { unfold wa. rewrite Z.add_0_r. symmetry. apply Z_to_bv_lit_self. }
  rewrite E. rewrite (bytes_at_ov_read rsegs m (bv_unsigned a) (b :: l) 0 1 H) by (cbn; lia). reflexivity.
Qed.

Lemma e01_rd1 : forall m (a : word) b0 b1 l, bytes_at rsegs m (bv_unsigned a) (b0 :: b1 :: l) ->
  ov_read_bytes rsegs m (wa (bv_unsigned a + 1)) 1 = Some [b1].
Proof.
  intros m a b0 b1 l H.
  replace (bv_unsigned a + 1) with (bv_unsigned a + Z.of_nat 1) by lia.
  rewrite (bytes_at_ov_read rsegs m (bv_unsigned a) (b0 :: b1 :: l) 1 1 H) by (cbn; lia). reflexivity.
Qed.

Lemma e01_weq_l : forall (x : word) e, bv_unsigned x mod 2 ^ 64 = e mod 2 ^ 64 -> x = Z_to_bv 64 e.
Proof. intros x e H. rewrite <- (Z_to_bv_lit_self x). apply Z_to_bv_eqm. exact H. Qed.

Lemma e01_byte : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R. Qed.

Lemma e01_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. apply MState.unsigned_lit. pose proof (e01_byte b). lia. Qed.

(* data[1] mod 10 as the code computes it: data[1] - 10 ((data[1] * 0xcd) >> 11). *)
Lemma e01_mod10 : forall b, 0 <= b < 256 -> b - b * 205 / 2048 * 10 = b mod 10.
Proof. intros b Hb. Z.div_mod_to_equations. lia. Qed.

(* 0x12fcc `srli a2,a1,26`; 0x12fd0 `beqz a2`: taken for n < 2^26. *)
Lemma e01_cond : forall u, 0 <= u < 2 ^ 26 ->
  bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0) = true.
Proof. intros u Hu. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. Qed.

(* The saved integer registers lie after the three FP saves. *)
Lemma e01_tail3 : forall m A n j x y z cs,
  Step.rw_cells rsegs m A (Cells.CB n j :: Cells.C8 x :: Cells.C8 y :: Cells.C8 z :: cs) ->
  bytes_at rsegs m (A + Z.of_nat n + 24) (Cells.cells_bytes cs).
Proof.
  intros m A n j x y z cs H.
  pose proof (sl_bytes_cells_tail _ _ _ _ _ H) as SB. cbn [Cells.cells_bytes Cells.cbytes] in SB.
  apply bytes_at_app in SB as [_ SB]. rewrite length_le8 in SB.
  apply bytes_at_app in SB as [_ SB]. rewrite length_le8 in SB.
  apply bytes_at_app in SB as [_ SB]. rewrite length_le8 in SB.
  replace (A + Z.of_nat n + 24) with (A + Z.of_nat n + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact SB.
Qed.

Ltac e01_weq :=
  first [ reflexivity
        | apply e01_weq_l; rewrite ?unsigned_lit_wrap, ?Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia ].

(* A branch: keep the side the facts allow. *)
Ltac e01_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let H := fresh "EC" in if_cases H; zify_cond H; try (exfalso; lia)
  | _ => idtac
  end.

(* ---- The run: ENTRY to malloc's entry with ra = 0x13044 ---- *)
Definition e01_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p : Z) (inp : list byte) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s6' s7' t3' t4' t5' t6' : word)
         (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x13044) (Z_to_bv 64 (bv_unsigned sp + -560)) gp tp t0' t1' t2' s0' s1' a0' a1' a2'
                  a3' a4' a5' a6' a7' s2' s3' s4 s5 s6' s7' s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x1643c) fc None m' (seg_rom rsegs) /\
    s0' = Z_to_bv 64 0x5000 /\ s1' = Z_to_bv 64 POD_PROPS /\ a0' = Z_to_bv 64 POD_PROPS /\
    s2' = Z_to_bv 64 (e01_k inp) /\ s3' = Z_to_bv 64 (e01_src p inp) /\ s6' = Z_to_bv 64 (e01_cap inp) /\
    s7' = Z_to_bv 64 (e01_null inp) /\
    Frame.munch [(bv_unsigned sp - 560, bv_unsigned sp)] m m' /\ Frame.wmono rsegs m m' /\
    bytes_at rsegs m' (bv_unsigned sp - 104)
      (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++
       le8 s1 ++ le8 s0 ++ le8 ra).

Ltac e01_fin sp :=
  lazymatch goal with
  | FR : rw_cells _ _ _ (CB _ _ :: C8 _ :: C8 _ :: C8 _ :: _) |- _ =>
      let SB := fresh "SB" in
      pose proof (e01_tail3 _ _ _ _ _ _ _ _ FR) as SB;
      cbn [Cells.cells_bytes Cells.cbytes] in SB; rewrite ?app_nil_r in SB;
      lazymatch type of SB with bytes_at _ _ ?x _ => replace x with (bv_unsigned sp - 104) in SB by lia end;
      apply evt_done; unfold e01_post;
      do 22 eexists; split; [reflexivity|];
      split; [|split; [|split; [|split; [|split; [|split; [|split; [|split;
        [assumption|split; [assumption|exact SB]]]]]]]]]
  end.

Ltac e01_eqs :=
  unfold e01_k, e01_src, e01_cap, e01_null, POD_PROPS; cbn [length Cursor.fuzz_u8 fst snd]; rewrite ?e01_zxb;
  e01_weq.

Lemma e01_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p : Z) (inp : list byte),
    stk rsegs m lo (bv_unsigned sp) -> lo + 560 <= bv_unsigned sp -> mem_inv rsegs m ->
    bv_unsigned a0 = p -> bv_unsigned a1 = Z.of_nat (length inp) -> Z.of_nat (length inp) < 2 ^ 26 ->
    p + Z.of_nat (length inp) <= lo -> bytes_at rsegs m p inp ->
    evt rsegs (e01_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p inp)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12f88) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo p inp ST LO HMI0 Ep Ha1 H26 Hin Hb.
  subst p.
  pose proof (munch_refl [(bv_unsigned sp - 560, bv_unsigned sp)] m) as MU.
  assert (Hlo : 0 <= lo) by (destruct ST as [H _]; exact H).
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra1.
  carve_frame 560%nat ST.
  do 19 step.
  if_true_by (e01_cond (bv_unsigned a1) ltac:(lia)).
  step. step.
  destruct inp as [|b0 [|b1 rest]]; cbn [length] in Ha1, H26, Hin.
  - (* n = 0: 0x13000 .. 0x13040 *)
    e01_if.
    do 8 step.
    e01_fin sp.
    all: e01_eqs.
  - (* n = 1: data[0], the cursor data + 1, no byte left *)
    e01_if.
    pose proof (e01_rd0 _ _ _ _ Hb) as HB0.
    pose proof (e01_byte b0) as Rb0.
    do 4 step.
    e01_if.
    do 8 step.
    e01_fin sp.
    all: e01_eqs.
  - (* n >= 2: data[0], data[1], the cursor data + 2, n - 2 bytes left *)
    e01_if.
    pose proof (e01_rd0 _ _ _ _ Hb) as HB0.
    pose proof (e01_rd1 _ _ _ _ _ Hb) as HB1.
    pose proof (e01_byte b0) as Rb0.
    pose proof (e01_byte b1) as Rb1.
    pose proof (e01_mod10 (bv_unsigned b1) Rb1) as M10.
    do 4 step.
    e01_if.
    do 13 step.
    e01_fin sp.
    all: e01_eqs.
Qed.

(* ---- The segment ---- *)
Ltac e01_rp RP Hx r :=
  etransitivity; [exact (RP r ltac:(unfold callee_saved; lia))|]; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity.

Section E01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.

Lemma seg_E01 : S_E01 B APIf ra empty.
Proof using fx rc B APIf LS SH SK ra empty FF.
  unfold S_E01. intros H1 g c (Ec & HGV & Hpre & Hsp & Hsn & HMI & Hrel & Hres & Hfrm).
  subst c.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HGV as (Hn26 & Hpl & Hdat & HS16 & HSK & HS47 & _ & HGsp & HGtp).
  pose proof Hpre as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn & Hpp & Hrod).
  pose proof alloc_ceiling_value as Hac.
  pose proof sl_ceil as Hct.
  unfold SLOT_K, SLOT_STACK, SL_TOP in *.
  assert (Esp2 : bv_unsigned (YK11.getr (g_regs g) 2) = g_S g).
  { rewrite Hsp. apply MState.unsigned_lit. lia. }
  assert (Esp : spZ (g_regs g) = g_S g) by exact Esp2.
  (* The input block lies below alloc_ceiling, so below the stack window. *)
  assert (Hpb : 0 <= g_p g /\ g_p g + g_n g <= g_S g - 65536).
  { destruct Hpl as [(Hn0 & Hpe) | (Hn0 & Hin)].
    - rewrite Hn0, Hpe, (ff_empty_val B APIf ra empty FF). lia.
    - destruct (b1_blk B APIf ra empty FF _ _ _ _ _ _ HM Hin) as (_ & Hb1 & Hb2). lia. }
  assert (Ep : bv_unsigned (YK11.getr (g_regs g) 10) = g_p g).
  { rewrite Hp. apply MState.unsigned_lit. lia. }
  assert (En : bv_unsigned (YK11.getr (g_regs g) 11) = Z.of_nat (length (g_in g))).
  { rewrite Hn. apply MState.unsigned_lit. unfold g_n in *. lia. }
  unfold MI in HMI. rewrite SEGS in HMI.
  assert (Hdat' : bytes_at rsegs (normalize rsegs (g_mem g)) (g_p g) (g_in g)).
  { apply (proj1 (bytes_at_rel rsegs _ _ _ _ (mem_rel_normalize rsegs (g_mem g) HMI))).
    split; [lia|]. split; [unfold g_n in Hpb; lia|].
    intros k Hk. pose proof (Hdat (Z.of_nat k) ltac:(lia)) as E. rewrite Nat2Z.id, SEGS in E. exact E. }
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run (g_regs g) (Z_to_bv 64 ENTRY) (g_mem g) (g_md g)); [exact Hh | exact Hl | exact HMI | | |].
  - rewrite sl_mkR_of. unfold ENTRY.
    apply e01_evt with (lo := g_S g - 65536) (p := g_p g) (inp := g_in g).
    + rewrite Esp2. apply sl_stk_norm; [exact HMI | unfold SL_TOP; lia | lia |].
      intros a Ha. rewrite <- SEGS. apply Hstw. rewrite Esp. exact Ha.
    + rewrite Esp2. lia.
    + exact (mem_inv_normalize rsegs (g_mem g)).
    + exact Ep.
    + exact En.
    + unfold g_n in Hn26. lia.
    + unfold g_n in Hpb. lia.
    + exact Hdat'.
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel' Hsame.
    destruct HQ as (t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s6' &
                    s7' & t3' & t4' & t5' & t6' & m'' & HE & E8 & E9 & E10 & E18 & E19 & E22 & E23 & MU & WM & SB).
    injection HE; intros; subst.
    rewrite Esp2 in MU, SB.
    pose proof (mem_rel_normalize rsegs (g_mem g) HMI) as HR0.
    assert (MU' : Frame.munch [(g_S g - 560, g_S g)] (g_mem g) m')
      by exact (munch_rel rsegs _ (g_mem g) (normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame MU).
    assert (WM' : Frame.wmono rsegs (g_mem g) m')
      by exact (wmono_rel rsegs (g_mem g) (normalize rsegs (g_mem g)) m' m'' HR0 Hrel' Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs (g_mem g) m' HMI Hsame).
    pose proof (proj2 (bytes_at_rel rsegs m' m'' _ _ Hrel') SB) as SB'.
    assert (HFR : FR B APIf ra empty g [] (g_L g) (g_A g) regs' m' (g_md g)).
    { apply (sl_fr_of B APIf ra empty FF) with (mem0 := g_mem g).
      - exact HGV.
      - exact HM.
      - exact HW.
      - exact HB.
      - exact HID.
      - exists (m_vmmaps (g_md g)). apply with_vmmaps_self.
      - intros a _ _ _. split; [reflexivity | tauto].
      - intros a _ _ _ _. split; [reflexivity | tauto].
      - intros a k i _ _. reflexivity.
      - intros a k Hin. exact Hin.
      - exact Herr.
      - exact Hsn.
      - exact (resb_start (g_b g) (g_A g) Hres).
      - intros a Ha. apply Hstw. rewrite Esp. unfold SLOT_K, SLOT_STACK in Ha. exact Ha.
      - exact Hrel.
      - apply (sl_unch _ _ _ (g_S g - 65536) (g_S g) MU').
        intros x Hx0 O. destruct (Z_le_dec (g_S g - 560) x); destruct (Z_lt_dec x (g_S g)); try lia;
          exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]).
      - exact WM'.
      - exact Hro'.
      - rewrite (sl_getr_eqv _ _ _ Hx).
        transitivity (Z_to_bv 64 (bv_unsigned (YK11.getr (g_regs g) 2) + -560)); [reflexivity|].
        rewrite Esp2. unfold fsp, SLOT_FRAME. f_equal; lia.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - unfold saved_bytes, SLOT_SAVE. rewrite <- Hra. exact SB'. }
    assert (E1 : YK11.getr regs' 1 = Z_to_bv 64 0x13044) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (E10' : YK11.getr regs' 10 = Z_to_bv 64 POD_PROPS) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    rewrite <- SEGS.
    apply (b1_malloc_call B APIf ra empty FF g [] (g_L g) (g_A g) regs' m' (g_md g) regs' POD_PROPS);
      [exact HFR | cbn [app]; apply Permutation_refl | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity
      | rewrite E1; vm_compute; reflexivity | exact E10' | unfold POD_PROPS; lia |].
    intros L' A' regs'' mem'' md' res HF'' HP'' RP Hres10 Hres0 Hres16 HK HKH.
    rewrite E1. apply H1. exists res, fx, L', A', regs'', mem'', md'.
    split; [reflexivity|]. split; [exact Hfrm|]. split; [exact HF''|]. split; [exact HP''|].
    unfold rg. split; [exact Hres10|]. split; [exact Hres0|]. split; [exact Hres16|].
    split; [e01_rp RP Hx 19|]. split; [e01_rp RP Hx 18|]. split; [e01_rp RP Hx 23|].
    split; [e01_rp RP Hx 22|]. split; [e01_rp RP Hx 9|]. e01_rp RP Hx 8.
Qed.

End E01.
