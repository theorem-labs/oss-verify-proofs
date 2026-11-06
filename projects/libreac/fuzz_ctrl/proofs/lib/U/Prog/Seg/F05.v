(* Segment F05 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13868, 0x13894] and [0x138cc, 0x13950],
   U13868 (v1.8 U1386c) -> U13954 (len >= 50): s9 = k; T15, T16 (Φ + 12, Φ + 13 wrap) not taken by HBR; s3 =
   is_8819 (Φ[12] = 0x88 and Φ[13] = 0x19); s8 = Φ + 18; AF9's room value, the 32-turn block-sum loop (head
   0x138f4, counter a3 = 32 - i; T17 at 0x138f8 not taken: Φ + 18 + i does not wrap; v1.9 compares with a5 = 32 set
   by the NEW-only 0x138f0 `li a5,32` where v1.8 used s2 = 32); s11 = sum_ok; T18, T19 not taken (HBR); AF8: TF to
   sp+16 (v1.8 sp+56); #42 not taken (struct P5.1: k <> 0 exactly when is_8819); s4 = 1. v1.9 registers against
   v1.8: Φ s6 -> s7, k s8 -> s9, is_8819 s1 -> s3, Φ + 18 s7 -> s8, sum_ok s10 -> s11, big s3 -> s4. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u4 Tac_u4b.
Import ListNotations.
Open Scope Z_scope.

(* The loop at 0x138f4, turn i (k = 32 - i turns left): a0 = Φ[18] + ... + Φ[17 + i], a1 = Φ + 18 + i,
   a2 = 2^64 - 18 - Φ, a3 = k, a5 = 32. *)
Lemma f05_loop : forall (bs : list byte) (phi : Z) (k i : nat)
  (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  (1 <= k)%nat -> (i + k = 32)%nat -> 4096 <= phi -> phi + 50 < 2 ^ 63 ->
  a0 = Z_to_bv 64 (RcModel.psum bs i) -> a1 = Z_to_bv 64 (phi + 18 + Z.of_nat i) ->
  a2 = Z_to_bv 64 (18446744073709551598 - phi) -> a3 = Z_to_bv 64 (Z.of_nat k) -> a5 = Z_to_bv 64 32 ->
  (forall j, (j < 32)%nat -> ov_read_bytes rsegs m (wa (phi + 18 + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)]) ->
  evt rsegs
    (fun ms' => exists a3' a4', ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (RcModel.psum bs 32))
                   (Z_to_bv 64 (phi + 50)) a2 a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x13910) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x138f4) fc None m (seg_rom rsegs)).
Proof.
  intros bs phi k. induction k as [|k IH];
    intros i ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      Hk Hik Hphi Hhi E0 E1 E2 E3 E13 Hrd; [lia|].
  subst a0 a1 a2 a3 a5.
  pose proof (Hrd i ltac:(lia)) as HR.
  pose proof (u4b_psum_rng bs i) as Hps.
  step. step. u4b_if_false. step. step. step. step. step.
  rewrite ?u4b_zxb_u.
  destruct (Nat.eq_dec k 0) as [-> | Hk0].
  - assert (Ei : i = 31%nat) by lia. subst i.
    u4b_if_false.
    replace (phi + 18 + Z.of_nat 31 + 1) with (phi + 50) by lia.
    rewrite <- (u4b_psum_S bs 31).
    apply evt_done. do 2 eexists. reflexivity.
  - u4b_if_true.
    apply (IH (S i)); [lia | lia | lia | lia | | | reflexivity | | reflexivity | exact Hrd].
    + rewrite u4b_psum_S. reflexivity.
    + f_equal. lia.
    + f_equal. lia.
Qed.

(* From 0x138cc (s3 = e) to 0x13954: the room value, a5 = 32, the loop, sum_ok, TF to sp+16, #42, s4 = 1. *)
Lemma f05_tail :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi k : Z) (e : bool) (b16 b17 : byte)
         (bs jt : list byte),
    sp = Z_to_bv 64 spv -> s7 = Z_to_bv 64 phi -> s9 = Z_to_bv 64 k -> s3 = Z_to_bv 64 (b2z e) ->
    0 <= k <= 13 -> 4096 <= phi -> phi + 50 < 2 ^ 63 -> (k =? 0) = negb e ->
    ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [b16] ->
    ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [b17] ->
    (forall j, (j < 32)%nat -> ov_read_bytes rsegs m (wa (phi + 18 + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)]) ->
    rw_cells rsegs m (spv + 16) [CB 8 jt] ->
    evt rsegs
      (fun ms' => exists (s3' a0' a1' a2' a3' a4' a5' s4' s8' s9' s11' w : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7
                       s2 s3' s4' s5 s6 s7 s8' s9' s10 s11' t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13954) fc None m' (seg_rom rsegs) /\
         s3' = Z_to_bv 64 (b2z e) /\ s4' = Z_to_bv 64 1 /\ s8' = Z_to_bv 64 (phi + 18) /\
         s9' = Z_to_bv 64 k /\ s11' = Z_to_bv 64 (b2z (RcModel.psum bs 32 mod 256 =? 0)) /\
         munch [(spv + 16, spv + 24)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' (spv + 16) (le8 w) /\
         w = Z_to_bv 64 (b2z ((RcModel.psum bs 32 mod 256 =? 0) ||
                              ((bv_unsigned b16 =? 0) && (bv_unsigned b17 =? 0)))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x138cc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi k e b16 b17 bs jt Hsp Hs7 Hs9 Hs3 Hk Hphi Hhi Hke HR16 HR17 Hrd Hjt.
  subst sp s7 s9 s3.
  pose proof (munch_refl [(spv + 16, spv + 24)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (u4b_psum_rng bs 32) as Hps.
  pose proof (Z.mod_pos_bound (RcModel.psum bs 32) 256 ltac:(lia)) as Hmod.
  step. step. step. step. step. step. step. step. step. step.
  eapply evt_cut.
  { apply (f05_loop bs phi 32 0);
      [lia | lia | lia | lia | reflexivity | f_equal; lia | apply u4b_room; lia | reflexivity | reflexivity
      | exact Hrd]. }
  intros ms' (a3' & a4' & ->).
  step. step. if_false_by (u4_ltu_neg_l phi (-17) ltac:(lia) ltac:(lia) ltac:(lia)).
  step. step. step. step. step.
  destruct (Z.eq_dec (bv_unsigned b16) 0) as [E16|E16].
  - if_false_by (u4b_bne_eq b16 0 ltac:(lia) E16).
    step. step. if_false_by (u4_ltu_neg_l phi (-18) ltac:(lia) ltac:(lia) ltac:(lia)).
    step. step. step. step.
    step. step. step. if_false_by (u4b_bne_snez k e ltac:(lia) Hke).
    step.
    apply evt_done. do 13 eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [first [reflexivity | f_equal; lia]|].
    split; [reflexivity|].
    split; [rewrite u4b_land255 by lia; apply u4b_seqz; lia|].
    split; [exact MU|]. split; [exact WM|]. split; [exact (u4_c_bytes _ _ _ Hjt)|].
    rewrite u4b_land255 by lia. rewrite u4b_seqz_b. rewrite u4b_seqz by lia. rewrite u4b_lor_b2z.
    rewrite (proj2 (Z.eqb_eq _ _) E16). cbn [andb]. rewrite orb_comm. reflexivity.
  - if_true_by (u4b_bne_neq b16 0 ltac:(lia) E16).
    step. step. step. if_false_by (u4b_bne_snez k e ltac:(lia) Hke).
    step.
    apply evt_done. do 13 eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [first [reflexivity | f_equal; lia]|].
    split; [reflexivity|].
    split; [rewrite u4b_land255 by lia; apply u4b_seqz; lia|].
    split; [exact MU|]. split; [exact WM|]. split; [exact (u4_c_bytes _ _ _ Hjt)|].
    rewrite u4b_land255 by lia. rewrite u4b_seqz by lia.
    rewrite (proj2 (Z.eqb_neq _ _) E16). cbn [andb]. rewrite orb_false_r. reflexivity.
Qed.

(* The whole segment from 0x13868: s9 = k, T15, is_8819 (T16 on the 0x88 path), then f05_tail. *)
Lemma f05_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi k : Z) (b12 b13 b16 b17 : byte)
         (bs jt : list byte),
    sp = Z_to_bv 64 spv -> s7 = Z_to_bv 64 phi -> a0 = Z_to_bv 64 k ->
    0 <= k <= 13 -> 4096 <= phi -> phi + 50 < 2 ^ 63 ->
    (k =? 0) = negb ((bv_unsigned b12 =? 136) && (bv_unsigned b13 =? 25)) ->
    ov_read_bytes rsegs m (wa (phi + 12)) 1 = Some [b12] ->
    ov_read_bytes rsegs m (wa (phi + 13)) 1 = Some [b13] ->
    ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [b16] ->
    ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [b17] ->
    (forall j, (j < 32)%nat -> ov_read_bytes rsegs m (wa (phi + 18 + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)]) ->
    rw_cells rsegs m (spv + 16) [CB 8 jt] ->
    evt rsegs
      (fun ms' => exists (s3' a0' a1' a2' a3' a4' a5' s4' s8' s9' s11' w : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7
                       s2 s3' s4' s5 s6 s7 s8' s9' s10 s11' t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13954) fc None m' (seg_rom rsegs) /\
         s3' = Z_to_bv 64 (b2z ((bv_unsigned b12 =? 136) && (bv_unsigned b13 =? 25))) /\
         s4' = Z_to_bv 64 1 /\ s8' = Z_to_bv 64 (phi + 18) /\
         s9' = Z_to_bv 64 k /\ s11' = Z_to_bv 64 (b2z (RcModel.psum bs 32 mod 256 =? 0)) /\
         munch [(spv + 16, spv + 24)] m m' /\ wmono rsegs m m' /\ bytes_at rsegs m' (spv + 16) (le8 w) /\
         w = Z_to_bv 64 (b2z ((RcModel.psum bs 32 mod 256 =? 0) ||
                              ((bv_unsigned b16 =? 0) && (bv_unsigned b17 =? 0)))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13868) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi k b12 b13 b16 b17 bs jt Hsp Hs7 Ha0 Hk Hphi Hhi Hke HR12 HR13 HR16 HR17 Hrd Hjt.
  subst sp s7 a0.
  step. step. step. if_false_by (u4_ltu_neg_l phi (-13) ltac:(lia) ltac:(lia) ltac:(lia)).
  step. step. step.
  destruct (Z.eq_dec (bv_unsigned b12) 136) as [E12|E12].
  - if_false_by (u4b_bne_eq b12 136 ltac:(lia) E12).
    step. step. if_false_by (u4_ltu_neg_l phi (-14) ltac:(lia) ltac:(lia) ltac:(lia)).
    step. step. step. step.
    eapply f05_tail with (spv := spv) (phi := phi) (k := k) (b16 := b16) (b17 := b17) (bs := bs) (jt := jt);
      [reflexivity | reflexivity | reflexivity | | exact Hk | exact Hphi | exact Hhi | exact Hke
      | exact HR16 | exact HR17 | exact Hrd | exact Hjt].
    rewrite (proj2 (Z.eqb_eq _ _) E12). cbn [andb]. rewrite ?u4b_zxb_u.
    apply (u4b_seqz_add (bv_unsigned b13) 25); [pose proof (u4_byte_rng b13); lia | lia].
  - if_true_by (u4b_bne_neq b12 136 ltac:(lia) E12).
    step.
    eapply f05_tail with (spv := spv) (phi := phi) (k := k) (b16 := b16) (b17 := b17) (bs := bs) (jt := jt);
      [reflexivity | reflexivity | reflexivity | | exact Hk | exact Hphi | exact Hhi | exact Hke
      | exact HR16 | exact HR17 | exact Hrd | exact Hjt].
    rewrite (proj2 (Z.eqb_neq _ _) E12). reflexivity.
Qed.

Section F05.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_F05 : forall j : nat, Hat B APIf ra (Inv_U13954_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13868_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HFT & Hb & HIFS & H10 & HB).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof (u4_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  pose proof (u4_len_range (g_in g) j) as (Hl0 & Hb0 & Hbl).
  pose proof (u4_k_range (g_in g) j) as Hkr.
  pose proof HFT as (_ & _ & H23 & Hphi & _).
  destruct (u4b_model (g_in g) j Hb) as (Ebig & E8819 & Esok & ETF & Ek).
  pose proof (bytes_at_normalize rsegs mem phi _ HMI Hphi) as HPn.
  assert (HL50 : (50 <= length (t_phi (g_in g) j))%nat) by (rewrite u4_phi_len; lia).
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 16) 8 ST ltac:(lia) ltac:(lia)) as (jt & Hjt).
  eapply (u4_mid B APIf ra empty FF g _ L A regs mem md _ [(g_S g - 1936 + 16, g_S g - 1936 + 24)]);
    [exact HFR | exact HP | u4_fp_tac | | |].
  - rewrite sl_mkR_of.
    apply f05_evt with (spv := g_S g - 1936) (phi := phi) (k := t_k (g_in g) j)
      (b12 := cp_b (t_g (g_in g) j) 12) (b13 := cp_b (t_g (g_in g) j) 13)
      (b16 := cp_b (t_g (g_in g) j) 16) (b17 := cp_b (t_g (g_in g) j) 17)
      (bs := skipn 18 (t_g (g_in g) j)) (jt := jt);
      [exact Hsp | exact H23 | exact H10 | lia | lia | lia | exact Ek
      | exact (u4b_rd _ phi _ 12 HPn HL50 ltac:(lia)) | exact (u4b_rd _ phi _ 13 HPn HL50 ltac:(lia))
      | exact (u4b_rd _ phi _ 16 HPn HL50 ltac:(lia)) | exact (u4b_rd _ phi _ 17 HPn HL50 ltac:(lia))
      | intros i Hi; exact (u4b_rd_blk _ phi _ i HPn HL50 Hi) | exact Hjt].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & _ & _ & _ & _ & _ & MU & WM & _).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (s3' & a0' & a1' & a2' & a3' & a4' & a5' & s4' & s8' & s9' & s11' & w & m'' &
                    HE & E3 & E4 & E8 & E9 & E11 & _ & _ & HBw & Ew).
    injection HE; intros; subst.
    assert (HK : FTK regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [split|].
    + apply (u4_FT_keep g j phi regs regs' mem m' _ HFT HK MU'); u4_dj.
    + unfold FV, V7, V1, V0, V2, VC, rg. rewrite Ebig, E8819, Esok, ETF.
      rewrite !(sl_getr_eqv _ _ _ Hx).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split.
      * apply (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel)). unfold q64, spk, fsp, SLOT_FRAME. exact HBw.
      * eapply (u4_ba _ mem); [exact HB | exact MU' |]. unfold t_B. rewrite RcParse.ctrlparse_length. u4_dj.
    + apply (u4_IFS_keep g j mem m' _ HIFS MU'); u4_dj.
Qed.

End F05.
