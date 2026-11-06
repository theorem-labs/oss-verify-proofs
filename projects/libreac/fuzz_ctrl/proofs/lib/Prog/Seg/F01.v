(* Segment F01 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13694, 0x136d0], K13694 -> K136d4
   (fuzz_record: h = min(2, left), L from the length bytes in[c], in[c + 1], len = min(L, left - h); malloc(len)). *)
(* libreac v1.9.0 (CHANGED register, segment table 5a S_F01): v1.8 [0x1368c, 0x136c8] K1368c -> K136cc. The walk is
   the v1.8 one with v1.9.0's registers: left in s11 (v1.8 s7), left - h in s11 (v1.8 s1: 0x1369c `li s11,0`,
   0x136b0 `addi s11,s11,-2`), the body pointer q + h in s0 (v1.8 s3); malloc at 0x1649c, return 0x136d4. The exit
   cut K136d4 changed (SlotInv.v: LIp and FCr, s11 holds left - h, no longer the cursor length), so seg_F01 is stated
   on it; its entry cut K13694 is v1.8 K1368c renamed. rule 24: no function proved. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel RcIdentLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b4.
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
  pose proof (b4_byte_nn b0). pose proof (b4_byte_nn b1).
  rewrite (MState.unsigned_lit (Z.shiftl (bv_unsigned b1) 8))
    by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 8) with 256; lia).
  rewrite RcIdentLib.rc_lor_shl8 by lia. lia.
Qed.

(* 0x13694 -> malloc's entry with ra = 0x136d4: s11 = left - h, s0 = q + h, s4 = a0 = len. *)
Lemma f01_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (q left h len : Z) (b0 b1 : byte),
    s11 = Z_to_bv 64 left -> s5 = Z_to_bv 64 q -> 0 <= q -> q + left < 2 ^ 64 -> 1 <= left < 2 ^ 26 ->
    ov_read_bytes rsegs m (wa q) 1 = Some [b0] ->
    (2 <= left -> ov_read_bytes rsegs m (wa (q + 1)) 1 = Some [b1]) ->
    h = Z.min 2 left ->
    len = Z.min (bv_unsigned b0 + (if 2 <=? left then 256 * bv_unsigned b1 else 0)) (left - h) ->
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR (Z_to_bv 64 0x136d4) sp gp tp t0 t1 t2 (Z_to_bv 64 (q + h)) s1 (Z_to_bv 64 len)
                       a1' a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 len) s5 s6 s7 s8 s9 s10 (Z_to_bv 64 (left - h))
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x1649c) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13694) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m q left h len b0 b1 -> -> Hq0 Hq1 Hl HR0 HR1 Eh Elen.
  pose proof (b4_byte_nn b0) as Hb0. pose proof (b4_byte_nn b1) as Hb1.
  destruct (Z.eq_dec left 1) as [E1|E1].
  - (* left = 1: h = 1, len = 0 *)
    subst left. assert (Eh1 : h = 1) by lia. clear Eh. subst h.
    assert (El0 : len = 0) by (rewrite Elen; change (2 <=? 1) with false; lia). clear Elen. subst len.
    step. step. if_false. step. step. step. step. step. step.
    step.
    lazymatch goal with
    | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with false by (symmetry; apply f01_ltu0); cbv iota
    end.
    step. step. step.
    apply evt_done. exists (zxb b0). reflexivity.
  - (* left >= 2: h = 2, len = min(L, left - 2) *)
    assert (Eh2 : h = 2) by lia. clear Eh. subst h.
    specialize (HR1 ltac:(lia)).
    rewrite (proj2 (Z.leb_le 2 left)) in Elen by lia.
    replace (left - 2) with (left + -2) in Elen |- * by lia.
    step. step. if_true_by (f01_ne left 1 ltac:(lia) ltac:(lia) E1).
    step. step. step. step. step. step. step.
    rewrite f01_L.
    destruct (Z_lt_dec (bv_unsigned b0 + 256 * bv_unsigned b1) (left + -2)) as [Hlt|Hge].
    + assert (El : len = bv_unsigned b0 + 256 * bv_unsigned b1) by lia. clear Elen. subst len.
      lazymatch goal with
      | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
          replace c with true by (symmetry; rewrite f01_ltu by lia; apply Z.ltb_lt; lia); cbv iota
      end.
      step. step.
      apply evt_done. exists (zxb b0). reflexivity.
    + assert (El : len = left + -2) by lia. clear Elen. subst len.
      lazymatch goal with
      | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
          replace c with false by (symmetry; rewrite f01_ltu by lia; apply Z.ltb_ge; lia); cbv iota
      end.
      step. step. step.
      apply evt_done. exists (zxb b0). reflexivity.
Qed.

Section F01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_F01 : forall j : nat, Hat B APIf ra (Inv_K136d4_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13694_at B APIf ra empty) j.
Proof.
  intros j H g c (L & A & regs & mem & md & -> & HFR & HP & HLI).
  pose proof HLI as (Hj & H26 & (Hc & H21 & H27) & Hl & _).
  pose proof (sl_fr_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (Hsp & _ & HS1 & HS2 & HMI).
  pose proof HFR as ((Hn26 & _) & _).
  assert (EL : t_left (g_in g) j = g_n g - t_c (g_in g) j) by reflexivity.
  destruct (b4_in_all B APIf ra empty FF g [] L A regs mem md HFR HP ltac:(lia)) as (Hp0 & Hpn & _).
  pose proof alloc_ceiling_value as Hac.
  pose proof (b4_in_rd B APIf ra empty FF g [] L A regs mem md (t_c (g_in g) j) HFR HP ltac:(lia)) as HR0.
  assert (HR1 : 2 <= t_left (g_in g) j ->
    ov_read_bytes rsegs (normalize rsegs mem) (wa (g_p g + t_c (g_in g) j + 1)) 1 =
      Some [RcIdentModel.nthb (g_in g) (Z.to_nat (t_c (g_in g) j + 1))]).
  { intros H2. rewrite <- Z.add_assoc.
    exact (b4_in_rd B APIf ra empty FF g [] L A regs mem md (t_c (g_in g) j + 1) HFR HP ltac:(lia)). }
  pose proof (b4_len_le (g_in g) j) as Hlen.
  eapply (b4_mid B APIf ra empty FF g [] L A regs mem md _ []); [exact HFR | exact HP | | | |].
  - intros x Hx O. exfalso. apply O. exact I.
  - rewrite sl_mkR_of.
    apply f01_evt with (q := g_p g + t_c (g_in g) j) (left := t_left (g_in g) j) (h := t_h (g_in g) j)
      (len := t_len (g_in g) j) (b0 := RcIdentModel.nthb (g_in g) (Z.to_nat (t_c (g_in g) j)))
      (b1 := RcIdentModel.nthb (g_in g) (Z.to_nat (t_c (g_in g) j + 1))).
    + exact H27.
    + exact H21.
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
    assert (E1 : YK11.getr regs' 1 = Z_to_bv 64 0x136d4) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (E10 : YK11.getr regs' 10 = Z_to_bv 64 (t_len (g_in g) j))
      by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    apply (b1_malloc_call B APIf ra empty FF g L A regs' m' md regs' (t_len (g_in g) j));
      [exact HFR' | exact HP | reflexivity | reflexivity | reflexivity | rewrite E1; vm_compute; reflexivity
      | exact E10 | lia |].
    intros L' A' regs'' mem'' md' res HF'' HP'' RP Hres10 Hres0 HK.
    rewrite E1. apply H. exists res, L', A', regs'', mem'', md'.
    split; [reflexivity|]. split; [exact HF''|]. split; [exact HP''|].
    assert (K : b4_keep mem mem'' (spk g 8) (spk g 192)).
    { apply (b4_keep_trans mem m' mem'').
      - apply (b4_keep_munch [] mem m' _ _ MU' I); unfold spk, fsp, SLOT_FRAME, SLOT_K, SLOT_STACK, SL_TOP in *; lia.
      - intros a Ha. apply HK. unfold spk, fsp, SLOT_FRAME in *. lia. }
    split; [|split; [|split; [exact Hres10 | exact Hres0]]].
    + apply (b4_LIp_keep g j regs regs'' mem mem'' K); [| | | exact HLI].
      * etransitivity; [exact (RP 19 ltac:(unfold callee_saved; lia))|].
        rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * etransitivity; [exact (RP 21 ltac:(unfold callee_saved; lia))|].
        rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * etransitivity; [exact (RP 26 ltac:(unfold callee_saved; lia))|].
        rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + unfold FCr, rg. split; [|split].
      * etransitivity; [exact (RP 27 ltac:(unfold callee_saved; lia))|].
        rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * etransitivity; [exact (RP 8 ltac:(unfold callee_saved; lia))|].
        rewrite (sl_getr_eqv _ _ _ Hx).
        transitivity (Z_to_bv 64 (g_p g + t_c (g_in g) j + t_h (g_in g) j)); [reflexivity|].
        f_equal. unfold t_body, f_body, t_h, t_c. lia.
      * etransitivity; [exact (RP 20 ltac:(unfold callee_saved; lia))|].
        rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End F01.
