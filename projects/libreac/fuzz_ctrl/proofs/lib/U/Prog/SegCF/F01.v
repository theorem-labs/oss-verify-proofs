(* Segment F01 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x137d0, 0x1381c], U137d0 -> U13820
   (fuzz_record: h = min(2, left), L from the length bytes in[c], in[c + 1], len = min(L, left - h); malloc(len)).
   v1.9 registers: cursor q in s7, left in s6, 1 in s2 (the v1.8 s6 / s7 / a2); the run leaves q + h in s5, len in
   s6, left - h in s3 (v1.8 s4 / s5 / s7); malloc at 0x173c0. T10, T11 (in + 1, in + 2 wrap) are false by PB
   (q = p + c >= 4096) with s2 = 1; T12 (in + h + len wraps) by PB (q + h + len <= p + n). Port of the plain seg_F01
   (a working branch lib/Prog/Seg/F01.v). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require YI08.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcIdentLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u1 Tac_u4.
Import ListNotations.
Open Scope Z_scope.

Lemma f01_ne : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> x <> y ->
  negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) = true.
Proof.
  intros x y Hx Hy Hn. unfold bv_eqb. rewrite !MState.unsigned_lit by lia.
  rewrite (proj2 (Z.eqb_neq x y) Hn). reflexivity.
Qed.

Lemma f01_ltu0 : forall x : word, bv_ltu x (Z_to_bv 64 0) = false.
Proof.
  intros x. unfold bv_ltu. rewrite (MState.unsigned_lit 0) by lia.
  pose proof (bv_unsigned_in_range 64 x) as [H _]. apply Z.ltb_ge. exact H.
Qed.

Lemma f01_ltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !MState.unsigned_lit by lia. reflexivity. Qed.

(* (in[c + 1] << 8) | in[c] is the little-endian u16. *)
Lemma f01_L : forall b0 b1 : byte,
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b1)) 8))) (bv_unsigned (zxb b0)) =
  bv_unsigned b0 + 256 * bv_unsigned b1.
Proof.
  intros b0 b1. rewrite !RcIdentLib.zxb_u.
  pose proof (u4_byte_rng b0). pose proof (u4_byte_rng b1).
  rewrite (MState.unsigned_lit (Z.shiftl (bv_unsigned b1) 8))
    by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia).
  rewrite RcIdentLib.rc_lor_shl8 by lia. lia.
Qed.

(* T12: ~(q + h) < len is false when q + h + len < 2^64. *)
Lemma f01_not : forall x y, 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 x)) 18446744073709551615)) (Z_to_bv 64 y) = false.
Proof.
  intros x y H1 H2 H3. rewrite (MState.unsigned_lit x) by lia.
  change 18446744073709551615 with (2 ^ 64 - 1). rewrite YI08.lxor_allones by lia.
  unfold bv_ltu. rewrite !MState.unsigned_lit by lia. apply Z.ltb_ge. lia.
Qed.

(* T10, T11: `bgeu s2,s5` with s2 = 1 and s5 = q + 1 or q + 2 >= 4097. *)
Ltac f01_bgeu1 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if negb (bv_ltu (Z_to_bv 64 1) (Z_to_bv 64 ?x)) then _ else _) _ _ _ _) =>
      if_false_by (f_equal negb (u4_ltu_true 1 x ltac:(lia) ltac:(lia)))
  end.

Ltac f01_t12 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if bv_ltu (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 ?x)) _)) (Z_to_bv 64 ?y)
                        then _ else _) _ _ _ _) =>
      rewrite (f01_not x y) by lia; cbv iota
  end.

(* 0x137d0 -> malloc's entry (0x173c0) with ra = 0x13820: s5 = q + h, s6 = a0 = len, s3 = left - h, s7 = q. *)
Lemma f01_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q left h len : Z) (b0 b1 : byte),
    s7 = Z_to_bv 64 q -> s6 = Z_to_bv 64 left -> s2 = Z_to_bv 64 1 ->
    4096 <= q -> q + left < 2 ^ 63 -> 1 <= left < 2 ^ 26 ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b0] ->
    (2 <= left -> ov_read_bytes rsegs m (wa (q + 1)) 1 = Some [b1]) ->
    h = Z.min 2 left ->
    len = Z.min (bv_unsigned b0 + (if 2 <=? left then 256 * bv_unsigned b1 else 0)) (left - h) ->
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR (Z_to_bv 64 0x13820) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 len) a1' a2 a3 a4 a5 a6 a7
                       s2 (Z_to_bv 64 (left - h)) s4 (Z_to_bv 64 (q + h)) (Z_to_bv 64 len) (Z_to_bv 64 q)
                       s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x173c0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x137d0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m q left h len b0 b1 -> -> -> Hq0 Hq1 Hl HR0 HR1 Eh Elen.
  pose proof (u4_byte_rng b0) as Hb0. pose proof (u4_byte_rng b1) as Hb1.
  destruct (Z.eq_dec left 1) as [E1|E1].
  - (* left = 1: h = 1, len = 0 *)
    subst left. assert (Eh1 : h = 1) by lia. clear Eh. subst h.
    assert (El0 : len = 0) by (rewrite Elen; change (2 <=? 1) with false; lia). clear Elen. subst len.
    step. step. f01_bgeu1.
    step. step. if_false.
    step. step. step. step. step.
    lazymatch goal with
    | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with false by (symmetry; apply f01_ltu0); cbv iota
    end.
    step. step. step.
    lazymatch goal with
    | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with false by (symmetry; apply f01_ltu0); cbv iota
    end.
    step. step.
    apply evt_done. eexists. reflexivity.
  - (* left >= 2: h = 2, len = min(L, left - 2) *)
    assert (Eh2 : h = 2) by lia. clear Eh. subst h.
    specialize (HR1 ltac:(lia)).
    rewrite (proj2 (Z.leb_le 2 left)) in Elen by lia.
    replace (left - 2) with (left + -2) in Elen |- * by lia.
    step. step. f01_bgeu1.
    step. step. if_true_by (f01_ne left 1 ltac:(lia) ltac:(lia) E1).
    step. step. f01_bgeu1.
    step. step. step. step. step. step.
    rewrite f01_L.
    destruct (Z_lt_dec (bv_unsigned b0 + 256 * bv_unsigned b1) (left + -2)) as [Hlt|Hge].
    + assert (El : len = bv_unsigned b0 + 256 * bv_unsigned b1) by lia. clear Elen. subst len.
      lazymatch goal with
      | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
          replace c with true by (symmetry; rewrite f01_ltu by lia; apply Z.ltb_lt; lia); cbv iota
      end.
      step. step. f01_t12.
      step. step.
      apply evt_done. eexists. reflexivity.
    + assert (El : len = left + -2) by lia. clear Elen. subst len.
      lazymatch goal with
      | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
          replace c with false by (symmetry; rewrite f01_ltu by lia; apply Z.ltb_ge; lia); cbv iota
      end.
      step. step. step. f01_t12.
      step. step.
      apply evt_done. eexists. reflexivity.
Qed.

Section F01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_F01 : forall j : nat, Hat B APIf ra (Inv_U13820_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U137d0_at B APIf ra empty) j.
Proof.
  intros j H g c (L & A & regs & mem & md & -> & HFR & HP & HLI).
  pose proof HLI as (HLK & (Hc & H23 & H22) & Hl & HIFS & _).
  pose proof (u4_LK_s2 g j regs mem HLK) as H18.
  pose proof (sl_fr_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (Hsp & _ & HS1 & HS2 & HMI).
  pose proof HFR as ((Hn26 & _) & _).
  assert (EL : t_left (g_in g) j = g_n g - t_c (g_in g) j) by reflexivity.
  destruct (u4_in_all B APIf ra empty FF g [] L A regs mem md HFR HP ltac:(lia)) as (Hp0 & Hpn & _).
  pose proof alloc_ceiling_value as Hac.
  pose proof (u4_in_rd B APIf ra empty FF g [] L A regs mem md (t_c (g_in g) j) HFR HP ltac:(lia)) as HR0.
  assert (HR1 : 2 <= t_left (g_in g) j ->
    ov_read_bytes rsegs (normalize rsegs mem) (wa (g_p g + t_c (g_in g) j + 1)) 1 =
      Some [RcIdentModel.nthb (g_in g) (Z.to_nat (t_c (g_in g) j + 1))]).
  { intros H2. rewrite <- Z.add_assoc.
    exact (u4_in_rd B APIf ra empty FF g [] L A regs mem md (t_c (g_in g) j + 1) HFR HP ltac:(lia)). }
  pose proof (u4_len_le (g_in g) j) as Hlen.
  eapply (u4_mid B APIf ra empty FF g [] L A regs mem md _ []); [exact HFR | exact HP | | | |].
  - intros x Hx O. exfalso. apply O. exact I.
  - rewrite sl_mkR_of.
    apply f01_evt with (q := g_p g + t_c (g_in g) j) (left := t_left (g_in g) j) (h := t_h (g_in g) j)
      (len := t_len (g_in g) j) (b0 := RcIdentModel.nthb (g_in g) (Z.to_nat (t_c (g_in g) j)))
      (b1 := RcIdentModel.nthb (g_in g) (Z.to_nat (t_c (g_in g) j + 1))).
    + exact H23.
    + rewrite EL. exact H22.
    + exact H18.
    + lia.
    + lia.
    + lia.
    + exact HR0.
    + exact HR1.
    + reflexivity.
    + reflexivity.
  - intros ms (? & ->).
    do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (a1' & HE).
    injection HE; intros; subst.
    assert (E1 : YK11.getr regs' 1 = Z_to_bv 64 0x13820) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (E10 : YK11.getr regs' 10 = Z_to_bv 64 (t_len (g_in g) j))
      by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    apply (u1_malloc_call B APIf ra empty FF g L A regs' m' md regs' (t_len (g_in g) j));
      [exact HFR' | exact HP | reflexivity | reflexivity | reflexivity | rewrite E1; vm_compute; reflexivity
      | exact E10 | lia |].
    intros L' A' regs'' mem'' md' res HF'' HP'' RP Hres10 Hres0 HK.
    rewrite E1. apply H. exists res, L', A', regs'', mem'', md'.
    split; [reflexivity|]. split; [exact HF''|]. split; [exact HP''|].
    assert (K : forall x, fsp g <= x < g_S g -> mbyte rsegs mem'' x = mbyte rsegs mem x).
    { intros x Hx'. rewrite (HK x Hx'). unfold mbyte. rewrite (MU' (Z_to_bv 64 x)); [reflexivity | exact I]. }
    split; [|split; [exact Hl|split; [|split; [|split; [|split; [|split; [exact Hres10 | exact Hres0]]]]]]].
    + apply (u4_LK_frame g j regs regs'' mem mem'' K); [| | | exact HLK].
      * etransitivity; [exact (RP 8 ltac:(unfold callee_saved; lia))|].
        rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * etransitivity; [exact (RP 18 ltac:(unfold callee_saved; lia))|].
        rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * etransitivity; [exact (RP 9 ltac:(unfold callee_saved; lia))|].
        rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + exact (u4_IFS_frame g j mem mem'' K HIFS).
    + unfold rg. etransitivity; [exact (RP 21 ltac:(unfold callee_saved; lia))|].
      rewrite (sl_getr_eqv _ _ _ Hx).
      transitivity (Z_to_bv 64 (g_p g + t_c (g_in g) j + t_h (g_in g) j)); [reflexivity|].
      f_equal. unfold t_body, f_body, t_h, t_c. lia.
    + unfold rg. etransitivity; [exact (RP 22 ltac:(unfold callee_saved; lia))|].
      rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + unfold rg. etransitivity; [exact (RP 19 ltac:(unfold callee_saved; lia))|].
      rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End F01.
