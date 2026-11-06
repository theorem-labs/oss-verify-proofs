From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg BoxregRd memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv.
Import ListNotations.
Open Scope Z_scope.

Lemma top_ub : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold zxb. apply MState.unsigned_lit. lia.
Qed.

Lemma top_land3 : forall z, Z.land z 3 = 0 \/ Z.land z 3 = 1 \/ Z.land z 3 = 2 \/ Z.land z 3 = 3.
Proof.
  intros z. assert (E : Z.land z 3 = z mod 4) by (apply (Z.land_ones z 2); lia).
  rewrite E. pose proof (Z.mod_pos_bound z 4 ltac:(lia)). lia.
Qed.

Lemma top_rd4 : forall m a v, bytes_at rsegs m a (le4 v) -> ov_read_bytes rsegs m (wa a) 4 = Some (le4 v).
Proof.
  intros m a v H. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m a _ 0 4 H) by (rewrite ?length_le4; lia).
  first [ reflexivity | f_equal; apply firstn_all2; rewrite length_le4; lia ].
Qed.

Lemma top_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite MState.unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma top_rw_bytes : forall m A n bs, rw_cells rsegs m A [CB n bs] -> bytes_at rsegs m A bs.
Proof. intros m A n bs [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. Qed.

Lemma top_rwc_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (W0 & W1 & W2)].
  apply cells_wf_app in Hwf. destruct Hwf as [Hw1 Hw2].
  rewrite cells_bytes_app in Hb. apply (proj1 (bytes_at_app rsegs _ _ _ _)) in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact Hw1.
  rewrite cells_size_app in W1, W2.
  split.
  - split; [ split; assumption | ]. split; [ lia | ]. split; [ lia | ].
    intros j Hj. apply W2. lia.
  - split; [ split; assumption | ]. split; [ lia | ]. split; [ lia | ].
    intros j Hj.
    replace (A + Z.of_nat (cells_size cs1) + j) with (A + (Z.of_nat (cells_size cs1) + j)) by lia.
    apply W2. lia.
Qed.

Lemma top_rwc_join : forall m A cs1 cs2 B,
  rw_cells rsegs m A cs1 -> B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m B cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 B [[Hw1 Hb1] (W0 & W1 & W2)] -> [[Hw2 Hb2] (V0 & V1 & V2)].
  split; [ split | ].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply (proj2 (bytes_at_app rsegs _ _ _ _)). split; [ exact Hb1 | ].
    rewrite cells_bytes_length by exact Hw1. exact Hb2.
  - rewrite cells_size_app. split; [ lia | ]. split; [ lia | ].
    intros j Hj. destruct (Z_lt_le_dec j (Z.of_nat (cells_size cs1))) as [L|L].
    + apply W2. lia.
    + replace (A + j) with (A + Z.of_nat (cells_size cs1) + (j - Z.of_nat (cells_size cs1))) by lia.
      apply V2. lia.
Qed.

Lemma top_ovr_munch : forall W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> Frame.outside W a ->
  ov_read_bytes rsegs m' (Z_to_bv 64 a) 1 = ov_read_bytes rsegs m (Z_to_bv 64 a) 1.
Proof. intros W m m' a H Ha O. cbn [ov_read_bytes]. rewrite (lf_munch_at W m m' a H Ha O). reflexivity. Qed.

Ltac top_done :=
  apply evt_done; do 17 eexists; split; [ reflexivity | ];
  split; [ eassumption | ]; split; [ eassumption | ]; split; [ eassumption | ];
  do 2 eexists; eassumption.

Lemma llvm_top_evt : memcpy_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv r ip inn i fab lo hi : Z) (j0 j1 j2 bs : list byte) (vb : byte)
         (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 : word),
    sp = Z_to_bv 64 spv -> s0 = Z_to_bv 64 r -> s2 = Z_to_bv 64 inn -> a0 = Z_to_bv 64 i -> s6 = Z_to_bv 64 1 ->
    rw_cells rsegs m spv (CB 8 j0 :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 fab) :: CB 320 j1 :: C8 (Z_to_bv 64 ip) ::
      CB 8 j2 :: [C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13]) ->
    bytes_at rsegs m r bs -> length bs = 288%nat ->
    ov_read_bytes rsegs m (Z_to_bv 64 ip) 1 = Some [vb] ->
    mem_inv rsegs m ->
    lo <= spv -> spv + 464 <= hi -> r + 288 <= spv -> 1 <= ip -> ip + 1 <= lo -> 0 <= i <= 63 ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 (bv_unsigned vb)) a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 (Z_to_bv 64 (ip + 1)) (Z_to_bv 64 ip) (Z_to_bv 64 (inn - 1)) s6 s7 s8 s9 s10 s11
                       t3' t4' t5' t6')
                  F (Z_to_bv 64 (llvm_case_pc (Z.land (bv_unsigned vb) 3))) fc None m' (seg_rom rsegs) /\
         munch [(lo, hi)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         exists ja jb, rw_cells rsegs m' spv (CB 8 j0 :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 fab) :: CB 8 ja ::
           C8 (Z_to_bv 64 i) :: C8 (Z_to_bv 64 (bx_n bs)) :: CB 288 bs :: CB 8 jb :: C8 (Z_to_bv 64 (ip + 1)) ::
           C8 (Z_to_bv 64 (inn - 1)) ::
           [C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12da8) fc None m (seg_rom rsegs)).
Proof.
  intros MC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv r ip inn i fab lo hi j0 j1 j2 bs vb w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
    -> -> -> -> -> HS HB HL HR MI Hlo Hhi Hr Hip1 Hip2 Hi.
  unfold memcpy_contract in MC.
  assert (BS : 0 <= spv /\ spv + 464 <= 2 ^ 64) by exact (rw_cells_bound rsegs m spv _ HS).
  pose proof (bytes_at_bound rsegs m r bs HB) as BR. rewrite HL in BR. change (Z.of_nat 288) with 288 in BR.
  assert (RB : -2^31 <= bx_n bs < 2^31) by exact (rd4_range bs 280).
  pose proof (munch_refl [(lo, hi)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. step.
  step. if_cases HC0; [ exfalso; zify_cond HC0; rewrite ?unsigned_lit_wrap in HC0; Z.div_mod_to_equations; lia | ].
  clear HC0.
  step. step. step.
  step. try (if_cases HC1; [ exfalso; zify_cond HC1; first [ discriminate HC1 | lia ] | clear HC1 ]).
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HR0 : ov_read_bytes rsegs mm (Z_to_bv 64 ip) 1 = Some [vb])
        by (rewrite (top_ovr_munch [(lo, hi)] m mm ip MU ltac:(lia) ltac:(cbn [Frame.outside]; split; [lia | exact I]));
            exact HR);
      pose proof (rd4_bytes_at mm r bs 280 HB ltac:(lia) ltac:(rewrite HL; lia)) as HN;
      change (rd4 bs 280) with (bx_n bs) in HN;
      pose proof (top_rd4 _ _ _ HN) as RN; clear HN
  end.
  step. step.
  rewrite ?top_sx32 by lia.
  step. step. step. step. step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of HS with rw_cells _ _ _ ?cs0 => split_for_access HS rsegs mm spv cs0 48%nat 288%nat end
  end.
  lazymatch type of HS with
  | rw_cells _ ?mm _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: CB 288 ?jd :: ?rest) =>
      destruct (top_rwc_split mm spv [c0; c1; c2; c3; c4; c5] _ HS) as [HS1 HS23];
      change (Z.of_nat (cells_size _)) with 48 in HS23;
      destruct (top_rwc_split mm (spv + 48) [CB 288 jd] _ HS23) as [HS2 HS3];
      change (Z.of_nat (cells_size _)) with 288 in HS3;
      clear HS HS23;
      eapply evt_cut;
      [ eapply MC with (src := bs) (junk := jd);
        rewrite ?MState.unsigned_lit by lia; first [ assumption | lia ] | ]
  end.
  intros ms' PO. unfold memcpy_post in PO.
  destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m4
                  & E & MUc & WMc & MIc & HD & _).
  subst ms'.
  rewrite !MState.unsigned_lit in MUc, HD by lia.
  change (Z.to_nat 288) with 288%nat in HD.
  lazymatch type of MUc with
  | munch _ ?mm ?mm' => transport_after_call rsegs mm mm' MUc WMc
  end.
  clear MUc WMc MI.
  replace (ret_pc (Z_to_bv 64 0x12de8)) with (Z_to_bv 64 0x12de8)
    by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  pose proof (top_rwc_join m4 (spv + 48) [CB 288 bs] _ (spv + 48 + 288) HD eq_refl HS3) as HS23.
  lazymatch type of HS1 with
  | rw_cells _ _ _ ?pre =>
      pose proof (top_rwc_join m4 spv pre _ (spv + 48) HS1 eq_refl HS23) as HSJ
  end.
  cbn [app] in HSJ. clear HS1 HS3 HD HS23.
  step. rewrite ?top_ub.
  destruct (top_land3 (bv_unsigned vb)) as [E|[E|[E|E]]]; rewrite E; step.
  - if_false. step. if_false. top_done.
  - if_false. step. if_true. top_done.
  - if_true. step. step. if_false. top_done.
  - if_true. step. step. if_true. top_done.
Qed.

Section S.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MEMCPY : memcpy_contract.

Lemma top_payload_rng : forall stk empty L0 A0 regs0 mem0 md0 ra p n b,
  llvm_ctx B API stk empty L0 A0 regs0 mem0 md0 ra p n b -> 0 < n -> 4096 <= p /\ p + n <= YM05.alloc_ceiling.
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b
    ((SEGS & _) & _ & _ & (HM0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpl & _) & _) Hn.
  destruct Hpl as [[E _] | [_ (q & Hq & Hqp)]]; [lia|].
  destruct (mr_blocks B _ (aa_laws API) L0 A0 mem0 md0 q n 0 HM0 Hq ltac:(lia)) as (_ & H1 & H2 & _).
  rewrite Hqp in H1, H2. lia.
Qed.

Theorem llvm_top_holds : llvm_top_ok B API.
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b i k c HC HJ.
  pose proof HC as (BI & Hk & _ & Hpre & _).
  destruct BI as (SEGS & _ & _ & HGG & _ & AX).
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & Hceil & H63 & _).
  destruct HJ as (fx' & regs & mem & md & L & A & r & fab & ip & inn & bs & j0 & j1 & j2 &
    -> & Hfrm & Hbase & H10 & H18 & HS & Hi & Hinn & Hpip & Hipn & Hr & Hinv & Hfab & Halloc & Hk1).
  pose proof Halloc as (FR & Hmine & Hres).
  pose proof Hbase as (E2 & E3 & E4 & E8 & E22 & E23 & E24 & E25 & E26 & E27).
  destruct (llvm_md_ok B API _ _ _ _ _ _ _ _ _ _ FR) as [Hh Hl].
  pose proof FR as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro).
  destruct (llvm_payload_read B API stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md ip HC FR ltac:(lia))
    as [vb HR].
  destruct (top_payload_rng stk empty L0 A0 regs0 mem0 md0 ra p n b HC ltac:(lia)) as [Hp1 Hp2].
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  unfold LLVM_K, LLVM_FRAME in Hk.
  destruct (lf_mine_bytes B API AX L0 A0 L A mem md r 288 (r + 287) HM Hmine ltac:(lia)) as (_ & _ & Hr1 & _).
  assert (HBr : bytes_at rsegs mem r bs) by exact (top_rw_bytes mem r 288 bs Hr).
  assert (HL : length bs = 288%nat) by (destruct Hinv as ((HL & _) & _); exact HL).
  assert (HSn : rw_cells rsegs (normalize rsegs mem) (spZ regs0 - 464)
    (CB 8 j0 :: C8 (Z_to_bv 64 0) :: C8 (Z_to_bv 64 fab) :: CB 320 j1 :: C8 (Z_to_bv 64 ip) :: CB 8 j2 ::
     llvm_saved_cells regs0)).
  { apply (lf_rw_cells_norm B); [ exact SEGS | exact Hro | | exact HS ].
    intros x Hx Himg. pose proof (lf_in_img_top B _ SEGS Himg). lia. }
  unfold llvm_saved_cells in HSn.
  rewrite SEGS.
  eapply (llvm_run_norm fx' regs (Z_to_bv 64 LLVM_TOP) mem md); [ exact Hh | exact Hl | exact Hro | | | ].
  - unfold Regs6ss.mkR_of, LLVM_TOP.
    eapply (llvm_top_evt MEMCPY) with (spv := spZ regs0 - 464) (r := r) (ip := ip) (inn := inn) (i := i)
      (fab := fab) (lo := spZ regs0 - stk) (hi := spZ regs0) (j0 := j0) (j1 := j1) (j2 := j2) (bs := bs) (vb := vb).
    + exact E2.
    + exact E8.
    + exact H18.
    + exact H10.
    + exact E22.
    + exact HSn.
    + exact (bytes_at_normalize rsegs mem r bs Hro HBr).
    + exact HL.
    + rewrite <- (ov_read_rel rsegs mem (normalize rsegs mem) _ _ (mem_rel_normalize rsegs mem Hro)). exact HR.
    + exact (mem_inv_normalize rsegs mem).
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
  - intros ms HQ.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & _).
    do 5 eexists. reflexivity.
  - intros R F pc' fc m0' HQ regs' m' Hx Hrel Hsame.
    destruct HQ as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6'
                    & m'' & HE & MU & WM & MI' & ja & jb & HS').
    injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
    apply SR_ret.
    assert (MU' : munch [(spZ regs0 - stk, spZ regs0)] mem m')
      by exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m'' (mem_rel_normalize rsegs mem Hro) Hrel Hsame MU).
    assert (WM' : wmono rsegs mem m')
      by exact (wmono_rel rsegs mem (normalize rsegs mem) m' m'' (mem_rel_normalize rsegs mem Hro) Hrel Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs mem m' Hro Hsame).
    assert (FR1 : lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A m' md).
    { eapply (lf_fr_evt B API SEGS AX HGG); [ exact FR | lia | lia | exact MU' | exact WM' | exact Hro' | ].
      intros x Hx0 NO. left.
      destruct (Z_le_dec (spZ regs0 - stk) x); destruct (Z_lt_dec x (spZ regs0)); try lia;
        exfalso; apply NO; cbn [Frame.outside]; (split; [ lia | exact I ]). }
    assert (Hrm : rw_cells rsegs m' r [CB 288 bs]).
    { apply (rw_cells_transport rsegs _ mem m' r _ Hr MU' WM').
      change (Z.of_nat (cells_size [CB 288 bs])) with 288. cbn [disjoint_from]. split; [ lia | exact I ]. }
    pose proof (bv_unsigned_in_range 8 vb) as R8. change (bv_modulus 8) with 256 in R8.
    exists (mkFP (@fp_regs fx') (@fp_csr fx')), regs', m', md, L, A, r, fab, ip, inn, bs, (bv_unsigned vb),
      j0, ja, jb.
    unfold llvm_regs_base. rewrite !(lf_getr_eqv _ _ _ Hx).
    split; [ rewrite SEGS; reflexivity | ].
    split; [ exact Hfrm | ].
    split.
    { split; [ exact E2 | ]. split; [ exact E3 | ]. split; [ exact E4 | ]. split; [ exact E8 | ].
      split; [ exact E22 | ]. split; [ exact E23 | ]. split; [ exact E24 | ]. split; [ exact E25 | ].
      split; [ exact E26 | exact E27 ]. }
    split; [ reflexivity | ]. split; [ exact H18 | ]. split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ reflexivity | ].
    split; [ exact (lf_rw_cells_rel m' m'' _ _ Hrel HS') | ].
    split; [ lia | ]. split; [ lia | ]. split; [ lia | ]. split; [ lia | ]. split; [ lia | ].
    split; [ exact Hrm | ]. split; [ exact Hinv | ]. split; [ exact Hfab | ].
    split; [ split; [ exact FR1 | split; [ exact Hmine | exact Hres ] ] | exact Hk1 ].
Qed.

End S.
