(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 245 of its 281 lines of code are new or changed and 538 lines of the source are left out. *)
(* Segment E01 of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (UBSan): [0x12fa8, 0x1308c], ENTRY -> K13090
   (U/Prog/LLVMFuzzerTestOneInput_c.v's S_E01). reac-pw/fuzz_role's U/Prog/Seg/E01.v with headamp's code:
   the prologue (0x12fa8 `addi sp,sp,-0x260`; ra, s0 .. s11 saved at S - 8 .. S - 104; fs0 .. fs3 by fsd at
   S - 112 .. S - 136), the n >= 2^26 exit not taken (0x12ff0 `srli a2,a1,26`, 0x12ff4 `beqz a2`: GV bounds n below
   2^26), 0x12ffc `mv s6,a0` and 0x13000 `beqz a1`: for the empty input 0x13038 sets s2 = s3 = 0 and stores 1 in the
   frame cell sp + 0x10; else the pointer-overflow check of data + 1 (0x1300c `bltu a2,a0`, whose other side jumps to
   the trap 0x148a0), dead because the input block starts above 4096 and ends below the allocator ceiling, then
   0x13014 `lbu`, `andi 1`, `seqz` and 0x13020 `sd a3,0x10(sp)` (1 - null into the cell); n = 1: s2 = s3 = 0 and
   s6 = data + 1; n >= 2: the check of data + 2 (0x13054, dead likewise), 0x1305c `lbu a0,1(s6)`, s2 = n - 2,
   s6 = data + 2 and cap = data[1] mod 10 by `mul 0xcd; srli 11; mul 10; sub` (e01_cap_val). All paths join at
   0x13080: s0 = 0x5000, s1 = 19744, a0 = s1, and malloc(19744) at 0x1308c with ra = 0x13090 through
   Tac_b1.b1_malloc_call from hb = [], whose continuation gives Inv_K13090. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.Seg Require Import Tac_slot Tac_b1.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor.
Import ListNotations.
Open Scope Z_scope.

Definition e01_null (inp : list byte) : Z := Z.land (fst (Cursor.fuzz_u8 inp)) 1.
Definition e01_cap (inp : list byte) : Z := fst (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 inp))) mod 10.
Definition e01_k (inp : list byte) : Z := Z.of_nat (length inp) - Z.min 2 (Z.of_nat (length inp)).
Definition e01_src (p : Z) (inp : list byte) : Z := p + Z.min 2 (Z.of_nat (length inp)).

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
  change (bv_unsigned a + 1) with (bv_unsigned a + Z.of_nat 1).
  rewrite (bytes_at_ov_read rsegs m (bv_unsigned a) (b0 :: b1 :: l) 1 1 H) by (cbn; lia). reflexivity.
Qed.

Lemma e01_weq_l : forall (x : word) e, bv_unsigned x mod 2 ^ 64 = e mod 2 ^ 64 -> x = Z_to_bv 64 e.
Proof. intros x e H. rewrite <- (Z_to_bv_lit_self x). apply Z_to_bv_eqm. exact H. Qed.

(* 0x12ff0 `srli a2,a1,26`; 0x12ff4 `beqz a2`: taken for n < 2^26. *)
Lemma e01_cond : forall u, 0 <= u < 2 ^ 26 ->
  bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0) = true.
Proof. intros u Hu. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. Qed.

Ltac e01_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let H := fresh "EC" in if_cases H; zify_cond H; try (exfalso; lia)
  | _ => idtac
  end.

(* ---- The values the code computes ---- *)
Lemma e01_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. unfold zxb. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in *. cbn in *. lia.
Qed.

Lemma e01_byte : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R. Qed.

(* 0x13018 `andi a3,a3,1`; 0x1301c `seqz a3,a3`: 1 - (b & 1). *)
Lemma e01_null_val : forall b : byte,
  v_sltiu (Z_to_bv 64 (Z.land (bv_unsigned (zxb b)) 1)) 1 = Z_to_bv 64 (1 - Z.land (bv_unsigned b) 1).
Proof.
  intros b. rewrite e01_zxb. unfold v_sltiu.
  assert (H : Z.land (bv_unsigned b) 1 = 0 \/ Z.land (bv_unsigned b) 1 = 1).
  { assert (E : Z.land (bv_unsigned b) 1 = Z.land (bv_unsigned b) (Z.ones 1)) by reflexivity.
    rewrite E, (Z.land_ones (bv_unsigned b) 1) by lia. pose proof (Z.mod_pos_bound (bv_unsigned b) (2 ^ 1)).
    change (2 ^ 1) with 2 in *. lia. }
  destruct H as [H|H]; rewrite H; reflexivity.
Qed.

(* b - (b * 205 >> 11) * 10 = b mod 10 for a byte b. *)
Lemma e01_div10 : forall x, 0 <= x < 256 -> x - x * 205 / 2048 * 10 = x mod 10.
Proof.
  intros x Hx.
  assert (E : forallb (fun n => let x := Z.of_nat n in x - x * 205 / 2048 * 10 =? x mod 10) (seq 0 256) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in E. specialize (E (Z.to_nat x)).
  rewrite in_seq in E. rewrite Z2Nat.id in E by lia. apply Z.eqb_eq. apply E. lia.
Qed.

(* 0x13068 .. 0x1307c: s3 = b1 mod 10. *)
Lemma e01_cap_val : forall b : byte,
  Z_to_bv 64 (bv_unsigned (zxb b) - bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.shiftr
    (bv_unsigned (Z_to_bv 64 (bv_unsigned (zxb b) * 205))) 11)) * 10))) = Z_to_bv 64 (bv_unsigned b mod 10).
Proof.
  intros b. rewrite e01_zxb. pose proof (e01_byte b) as Hb.
  set (x := bv_unsigned b) in *.
  rewrite (unsigned_lit_wrap (x * 205)), (Z.mod_small (x * 205)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 11) with 2048.
  assert (Hq : 0 <= x * 205 / 2048 < 26) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (unsigned_lit_wrap (x * 205 / 2048)), (Z.mod_small (x * 205 / 2048)) by lia.
  rewrite (unsigned_lit_wrap (x * 205 / 2048 * 10)), (Z.mod_small (x * 205 / 2048 * 10)) by lia.
  rewrite e01_div10 by exact Hb. reflexivity.
Qed.

(* ---- The run: ENTRY to malloc's entry with ra = 0x13090 ---- *)
Definition e01_post (ra sp gp tp s4 s5 s7 s8 s9 s10 s11 : word) (s0 s1 s2 s3 s6 : word) (F : bvmap 5 word)
    (fc : bv 32) (m : word -> option byte) (p : Z) (inp : list byte) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s6' t3' t4' t5' t6' : word)
         (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x13090) (Z_to_bv 64 (bv_unsigned sp + -608)) gp tp t0' t1' t2' s0' s1' a0' a1' a2'
                  a3' a4' a5' a6' a7' s2' s3' s4 s5 s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x1693c) fc None m' (seg_rom rsegs) /\
    s0' = Z_to_bv 64 0x5000 /\ s1' = Z_to_bv 64 POD_PROPS /\ a0' = Z_to_bv 64 POD_PROPS /\
    s2' = Z_to_bv 64 (e01_k inp) /\ s3' = Z_to_bv 64 (e01_cap inp) /\ s6' = Z_to_bv 64 (e01_src p inp) /\
    Frame.munch [(bv_unsigned sp - 608, bv_unsigned sp)] m m' /\ Frame.wmono rsegs m m' /\
    bytes_at rsegs m' (bv_unsigned sp - 592) (le8 (Z_to_bv 64 (1 - e01_null inp))) /\
    bytes_at rsegs m' (bv_unsigned sp - 104)
      (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++ le8 s2 ++
       le8 s1 ++ le8 s0 ++ le8 ra).

(* The frame is carved in two: the thirteen saved registers at S - 104 (FRS) and, below them, the eight-byte cell
   sp + 0x10 at S - 592 with the 480 bytes above it, where the four fsd land (FRC). *)
Ltac e01_fin sp FRS FRC :=
  let SB := fresh "SB" in let SF := fresh "SF" in
  pose proof (sl_cells_bytes _ _ _ FRS) as SB;
  pose proof (sl_cells_bytes _ _ _ FRC) as SF;
  cbn [Cells.cells_bytes Cells.cbytes] in SB, SF; rewrite ?app_nil_r in SB, SF;
  apply bytes_at_app in SF; destruct SF as [SF _];
  lazymatch type of SB with bytes_at _ _ ?x _ => replace x with (bv_unsigned sp - 104) in SB by lia end;
  lazymatch type of SF with bytes_at _ _ ?y _ => replace y with (bv_unsigned sp - 592) in SF by lia end;
  apply evt_done; unfold e01_post;
  do 21 eexists; split; [reflexivity|];
  split; [|split; [|split; [|split; [|split; [|split; [|split; [assumption|split; [assumption|
    split; [|exact SB]]]]]]]]].

Ltac e01_weq :=
  first [ reflexivity
        | apply e01_weq_l; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ].

Ltac e01_eqs := unfold e01_k, e01_src, e01_cap, e01_null, POD_PROPS; cbn [length Cursor.fuzz_u8 fst snd]; e01_weq.

Lemma e01_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p : Z) (inp : list byte),
    stk rsegs m lo (bv_unsigned sp) -> lo + 608 <= bv_unsigned sp -> mem_inv rsegs m ->
    bv_unsigned a0 = p -> bv_unsigned a1 = Z.of_nat (length inp) -> Z.of_nat (length inp) < 2 ^ 26 ->
    0 < p -> p + Z.of_nat (length inp) <= lo -> bytes_at rsegs m p inp ->
    evt rsegs (e01_post ra sp gp tp s4 s5 s7 s8 s9 s10 s11 s0 s1 s2 s3 s6 F fc m p inp)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12fa8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo p inp ST LO HMI0 Ep Ha1 H26 Hp0 Hin Hb.
  subst p.
  pose proof (munch_refl [(bv_unsigned sp - 608, bv_unsigned sp)] m) as MU.
  assert (Hlo : 0 <= lo) by (destruct ST as [H _]; exact H).
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra1.
  carve_frame 104%nat ST.
  rename FR into FRS.
  carve_frame 488%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 488%nat _ [] [8%nat; 480%nat]) in FR; [|reflexivity].
  cbn [app mk_CB_cells] in FR.
  rename FR into FRC.
  do 20 step.
  if_true_by (e01_cond (bv_unsigned a1) ltac:(lia)).
  step. step.
  destruct inp as [|b0 [|b1 rest]]; cbn [length] in Ha1, H26, Hin.
  - (* n = 0: 0x13038 .. 0x1308c *)
    e01_if. do 9 step.
    e01_fin sp FRS FRC.
    all: try exact SF.
    all: e01_eqs.
  - (* n = 1: the check of data + 1, null into the cell, cap = 0 *)
    e01_if.
    pose proof (e01_rd0 _ _ _ _ Hb) as HB0.
    do 3 step. e01_if. do 5 step. e01_if. do 8 step.
    rewrite e01_null_val in FRC.
    e01_fin sp FRS FRC.
    all: try exact SF.
    all: e01_eqs.
  - (* n >= 2: both checks, null into the cell, cap = data[1] mod 10 *)
    e01_if.
    pose proof (e01_rd0 _ _ _ _ Hb) as HB0.
    do 3 step. e01_if. do 5 step. e01_if.
    pose proof (e01_rd1 _ _ _ _ _ Hb) as HB1.
    do 3 step. e01_if. do 13 step.
    rewrite e01_null_val in FRC. rewrite e01_cap_val.
    e01_fin sp FRS FRC.
    all: try exact SF.
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
Hypothesis FF : frame_facts_ubsan B APIf LS SH SK ra empty.

Lemma seg_E01 : S_E01 B APIf ra empty.
Proof using fx rc B APIf LS SH SK ra empty FF.
  unfold S_E01. intros H1 g c (Ec & HGV & Hpre & Hsp & Hsn & HMI & Hrel & Hres & Hfrm).
  subst c.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof HGV as (Hn26 & Hpl & Hdat & HS16 & HSK & HS47 & _ & HGsp & HGtp).
  pose proof Hpre as (HM & HW & HB & HID & Hra & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn & Hpp & Hrod).
  pose proof alloc_ceiling_value as Hac.
  pose proof sl_ceil as Hct.
  pose proof (ff_empty B APIf ra empty FF) as Hemp.
  unfold SLOT_K, SLOT_STACK, SL_TOP in *.
  assert (Esp2 : bv_unsigned (YK11.getr (g_regs g) 2) = g_S g).
  { rewrite Hsp. apply MState.unsigned_lit. lia. }
  assert (Esp : spZ (g_regs g) = g_S g) by exact Esp2.
  (* The input block lies below alloc_ceiling, so below the stack window; its address is positive
     (an input block starts at 4096 or above; for the empty input the cursor is the `empty` global). *)
  assert (Hpb : 0 < g_p g /\ g_p g + g_n g <= g_S g - 65536).
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
    + lia.
    + unfold g_n in Hpb. lia.
    + exact Hdat'.
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel' Hsame.
    destruct HQ as (t0' & t1' & t2' & s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' &
                    s6' & t3' & t4' & t5' & t6' & m'' & HE & E8 & E9 & E10 & E18 & E19 & E22 & MU & WM & SF & SB).
    injection HE; intros; subst.
    rewrite Esp2 in MU, SB, SF.
    pose proof (mem_rel_normalize rsegs (g_mem g) HMI) as HR0.
    assert (MU' : Frame.munch [(g_S g - 608, g_S g)] (g_mem g) m')
      by exact (munch_rel rsegs _ (g_mem g) (normalize rsegs (g_mem g)) m' _ HR0 Hrel' Hsame MU).
    assert (WM' : Frame.wmono rsegs (g_mem g) m')
      by exact (wmono_rel rsegs (g_mem g) (normalize rsegs (g_mem g)) m' _ HR0 Hrel' Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs (g_mem g) m' HMI Hsame).
    pose proof (proj2 (bytes_at_rel rsegs m' _ _ _ Hrel') SB) as SB'.
    pose proof (proj2 (bytes_at_rel rsegs m' _ _ _ Hrel') SF) as SF'.
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
        intros x Hx0 O. destruct (Z_le_dec (g_S g - 608) x); destruct (Z_lt_dec x (g_S g)); try lia;
          exfalso; apply O; cbn [Frame.outside]; (split; [lia | exact I]).
      - exact WM'.
      - exact Hro'.
      - rewrite (sl_getr_eqv _ _ _ Hx).
        transitivity (Z_to_bv 64 (bv_unsigned (YK11.getr (g_regs g) 2) + -608)); [reflexivity|].
        rewrite Esp2. unfold fsp, SLOT_FRAME. f_equal; lia.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - unfold saved_bytes, SLOT_SAVE. rewrite <- Hra. exact SB'. }
    assert (E1 : YK11.getr regs' 1 = Z_to_bv 64 0x13090) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (E10' : YK11.getr regs' 10 = Z_to_bv 64 POD_PROPS) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    rewrite <- SEGS.
    apply (b1_malloc_call B APIf ra empty FF g [] (g_L g) (g_A g) regs' m' (g_md g) regs' POD_PROPS);
      [exact HFR | cbn [app]; apply Permutation_refl | cbn; lia | cbn; lia | reflexivity | reflexivity | reflexivity
      | rewrite E1; vm_compute; reflexivity | exact E10' | unfold POD_PROPS; lia |].
    intros L' A' regs'' mem'' md' res HF'' HP'' RP Hres10 Hres0 Hres16 HK HKH.
    rewrite E1. apply H1. exists res, fx, L', A', regs'', mem'', md'.
    split; [reflexivity|]. split; [exact Hfrm|]. split; [exact HF''|]. split; [exact HP''|].
    unfold rg. split; [exact Hres10|]. split; [exact Hres0|]. split; [exact Hres16|].
    split; [e01_rp RP Hx 22|]. split; [e01_rp RP Hx 18|]. split; [e01_rp RP Hx 19|].
    split.
    { apply (b1_ba_mbyte m').
      - unfold fsp, SLOT_FRAME. replace (g_S g - 608 + 0x10) with (g_S g - 592) by lia. exact SF'.
      - intros i Hi. rewrite length_le8 in Hi. apply HK. unfold fsp, SLOT_FRAME. lia. }
    split; [e01_rp RP Hx 9|]. e01_rp RP Hx 8.
Qed.

End E01.
