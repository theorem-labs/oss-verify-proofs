(* Segment I02 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13874, 0x138c0], K13874 -> K138c4 (pll_r >= 1,
   so 0x13878 is not taken; the record sum loop at 0x1388c over Φ[34 .. 39 + pll_r) (P4d); the address check (P4e);
   reac_identity_ingest(sp+154, addr_r, Φ + 38, pll_r)).
   libreac v1.9.0 (table 5a S_I02, IDENTICAL-RENUMBER): pcs + 0xc, the reply address at sp+1750 (v1.8 1734), id at
   sp+154 (v1.8 138), the frame 1936 bytes. rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv RcModel RcRec RcParse RcReply
  RcIdentModel reac_identity_ingest_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b5.
Import ListNotations.
Open Scope Z_scope.

Lemma i02_land127 : forall x, Z.land x 127 = x mod 128.
Proof. intros x. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma i02_lor8 : forall x y, 0 <= x < 256 -> 0 <= y -> Z.lor (y * 256) x = x + 256 * y.
Proof.
  intros x y Hx Hy. rewrite Z.lor_comm.
  replace (y * 256) with (Z.shiftl y 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  apply Bytes.lor_shiftl8_add; lia.
Qed.

(* 0x138a4-0x138b4: (Φ[36] << 8) | Φ[37]. *)
Lemma i02_addr_eq : forall b36 b37 : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b36)) 8))) (bv_unsigned (zxb b37))) =
  zx16 (Z_to_bv 64 (bv_unsigned b36 * 256 + bv_unsigned b37)).
Proof.
  intros b36 b37. pose proof (b5_byte_rng b36) as R6. pose proof (b5_byte_rng b37) as R7.
  unfold zxb, zx16.
  rewrite (MState.unsigned_lit (bv_unsigned b36)) by lia.
  rewrite (MState.unsigned_lit (bv_unsigned b37)) by lia.
  replace (Z.shiftl (bv_unsigned b36) 8) with (bv_unsigned b36 * 256)
    by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  rewrite (MState.unsigned_lit (bv_unsigned b36 * 256)) by lia.
  rewrite (MState.unsigned_lit (bv_unsigned b36 * 256 + bv_unsigned b37)) by lia.
  rewrite i02_lor8 by lia. f_equal. rewrite Z.mod_small by lia. lia.
Qed.

(* The reply's address slot (sp+1750) as a u16. *)
Lemma i02_raddr : forall g, reply_addr g = le2 (Z_to_bv 64 (r_addr g)).
Proof.
  intros g. unfold reply_addr, r_addr, le2.
  pose proof (cp_v_range' g 36) as R6. pose proof (cp_v_range' g 37) as R7.
  rewrite MState.unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite Z.shiftr_div_pow2 by lia.
  unfold cp_v in *.
  f_equal; [|f_equal]; apply bv_eq; rewrite Z_to_bv_unsigned; change (bv_wrap 8 ?x) with (x mod 2 ^ 8);
    change (2 ^ 8) with 256; lia.
Qed.

Lemma i02_raddr_read : forall m a g, bytes_at rsegs m a (reply_addr g) ->
  ov_read_bytes rsegs m (wa a) 2 = Some (le2 (Z_to_bv 64 (r_addr g))).
Proof.
  intros m a g H. rewrite i02_raddr in H.
  assert (L : (0 + 2 <= length (le2 (Z_to_bv 64 (r_addr g))))%nat) by (rewrite length_le2; lia).
  pose proof (bytes_at_ov_read rsegs m a _ 0 2 H L) as R.
  cbn [Z.of_nat] in R. rewrite Z.add_0_r in R. rewrite R. cbv [skipn].
  rewrite firstn_all2 by (rewrite length_le2; lia). reflexivity.
Qed.

(* The record sum loop 0x1388c-0x13898: a0 = psum bs i, a1 = base + i, a4 = base + |bs|. *)
Lemma i02_loop :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop)
         (bs : list byte) (base : Z),
    bytes_at rsegs m base bs -> 0 <= base -> base + 16 < 2 ^ 64 -> (length bs <= 16)%nat ->
    a4 = Z_to_bv 64 (base + Z.of_nat (length bs)) ->
    (forall a0 a1 a5 : word, a0 = Z_to_bv 64 (psum bs (length bs)) ->
       a1 = Z_to_bv 64 (base + Z.of_nat (length bs)) ->
       evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x1389c) fc None m (seg_rom rsegs))) ->
    forall (k : nat) (a0 a1 a5 : word) (i : nat), (i + S k = length bs)%nat ->
      a0 = Z_to_bv 64 (psum bs i) -> a1 = Z_to_bv 64 (base + Z.of_nat i) ->
      evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x1388c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Q bs base HB Hb0 Hb16 L16 E4 HK.
  subst a4.
  induction k as [|k IH]; intros a0 a1 a5 i Hi E0 E1; subst a0 a1;
    pose proof (b5_byte_read m base bs i HB ltac:(lia)) as HR;
    pose proof (b5_psum_bnd bs i) as Hp;
    pose proof (b5_byte_rng (nth i bs (Z_to_bv 8 0))) as Hr;
    step; step; step; step.
  - b5_br false. eapply HK.
    + replace (length bs) with (S i) by lia. b5_weq.
    + b5_weq.
  - b5_br true. eapply (IH _ _ _ (S i)); [lia | b5_weq | b5_weq].
Qed.

Lemma i02_evt : reac_identity_ingest_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi : Z) (g idb : list byte),
    sp = Z_to_bv 64 spv -> s6 = Z_to_bv 64 (phi + 18) -> a2 = Z_to_bv 64 (phi + 38) ->
    a3 = Z_to_bv 64 (r_pll g) ->
    1 <= r_pll g <= 10 -> 0 < phi -> phi + 50 <= spv -> spv mod 16 = 0 -> spv + 1936 <= 2 ^ 64 ->
    length g = 50%nat -> bytes_at rsegs m phi g -> recsum (ir_rec g) = 0 ->
    bytes_at rsegs m (spv + 1750) (reply_addr g) -> rw_cells rsegs m (spv + 154) [CB 38 idb] ->
    evt rsegs
      (fun ms' => exists (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x138c4) sp gp tp t0' t1' t2 s0 s1
                       (Z_to_bv 64 (fst (ING idb (r_addr g) (r_pl g))))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x138c4) fc None m' (seg_rom rsegs) /\
         munch [(spv + 154, spv + 192)] m m' /\ wmono rsegs m m' /\
         rw_cells rsegs m' (spv + 154) [CB 38 (snd (ING idb (r_addr g) (r_pl g)))])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13874) fc None m (seg_rom rsegs)).
Proof.
  intros ING ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi g idb Hsp Hs6 Ha2 Ha3 Hpll Hphi Hpb H16 Hhi Hg HB Hrs HA Hid.
  subst sp s6 a2 a3.
  assert (Lrec : length (ir_rec g) = Z.to_nat (r_pll g + 5)).
  { unfold ir_rec. rewrite length_firstn, length_skipn, Hg. unfold r_pll in Hpll |- *. lia. }
  assert (Brec : bytes_at rsegs m (phi + 34) (ir_rec g)).
  { unfold ir_rec. exact (b5_ba_slice m phi g 34 _ HB ltac:(lia)). }
  unfold recsum in Hrs.
  assert (Hra : 0 <= r_addr g < 65536).
  { unfold r_addr. pose proof (cp_v_range' g 36). pose proof (cp_v_range' g 37). lia. }
  pose proof (b5_byte_read m phi g 36 HB ltac:(lia)) as HR36.
  pose proof (b5_byte_read m phi g 37 HB ltac:(lia)) as HR37.
  change (Z.of_nat 36) with 36 in HR36. change (Z.of_nat 37) with 37 in HR37.
  pose proof (i02_raddr_read m (spv + 1750) g HA) as HRA.
  step. step.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by (symmetry; unfold bv_eqb; rewrite (MState.unsigned_lit (r_pll g)) by lia;
                               rewrite MState.unsigned_lit_wrap; apply Z.eqb_neq; lia)
  end; cbv iota.
  step. step. step. step.
  eapply i02_loop with (bs := ir_rec g) (base := phi + 34) (k := (Z.to_nat (r_pll g + 5) - 1)%nat) (i := 0%nat);
    [exact Brec | lia | lia | lia | b5_weq | | lia | b5_weq | b5_weq].
  intros x0 x1 x5 E0 E1. subst x0 x1.
  pose proof (b5_psum_bnd (ir_rec g) (length (ir_rec g))) as Hps.
  step.
  rewrite (MState.unsigned_lit (psum (ir_rec g) (length (ir_rec g)))) by lia.
  rewrite i02_land127, Hrs.
  step. b5_br false.
  step. step. step. step. step.
  step.
  rewrite i02_addr_eq.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by (symmetry; apply negb_false_iff; unfold bv_eqb; apply Z.eqb_eq; reflexivity)
  end; cbv iota.
  step. step.
  eapply evt_cut.
  { eapply ING with (id := spv + 154) (ad := r_addr g) (p := phi + 38) (len := r_pll g) (idb := idb)
      (pb := r_pl g);
      [ b5_weq | apply b5_zx16; exact Hra | reflexivity | reflexivity | lia | lia | lia | lia | | | | ].
    - intros _. split; [lia | exact Hid].
    - unfold r_pl, RcFrag.bsl. rewrite length_firstn, length_skipn, Hg. lia.
    - intros _ _. unfold r_pl, RcFrag.bsl. exact (b5_ba_slice m phi g 38 _ HB ltac:(lia)).
    - intros _ _ _. left. lia. }
  intros ms' (t0' & t1' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & E & MUc & WMc & _ & _ & Hrw).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x138c4)) with (Z_to_bv 64 0x138c4)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (Hnr : ingest_refused (spv + 154) (phi + 38) (r_pll g) = false).
  { unfold ingest_refused.
    rewrite (proj2 (Z.eqb_neq (spv + 154) 0)), (proj2 (Z.eqb_neq (r_pll g) 0)), (proj2 (Z.eqb_neq (phi + 38) 0))
      by lia.
    reflexivity. }
  unfold ingest_ret. rewrite Hnr.
  apply evt_done. exists t0', t1', a1', a2', a3', a4', a5', a6', a7', m'.
  replace (spv + 154 + 38) with (spv + 192) in MUc by lia.
  split; [reflexivity|]. split; [exact MUc|]. split; [exact WMc|]. exact (Hrw Hnr).
Qed.

Section I02.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis ING : reac_identity_ingest_contract.
Hypothesis INGOK : reac_identity_ingest_id_ok_kept.

Lemma seg_I02 : forall j, Hat B APIf ra (Inv_K138c4_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13874_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HFB & HIFS & Hir & HRPS & H12 & H13).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof (b5_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  pose proof (b5_len_range (g_in g) j) as (Hl0 & Hb0 & Hbl).
  pose proof HFB as ((Hj & H26 & (H27 & H32 & H20) & H21 & Hphi & _) & (H23 & H25 & H9 & H18 & (H8 & H22 & _))).
  destruct (b5_ir_facts _ _ Hir) as (H50 & Hbig & Hsok & Hpll & _).
  destruct (ir_true _ _ Hir) as (_ & _ & _ & _ & _ & _ & _ & _ & Hrec).
  destruct (proj1 HRPS Hir) as (Ra & _ & _).
  destruct HIFS as ((HI & Hok) & HG & HS).
  pose proof (b5_nb_range (g_in g) j) as Hnb.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME, spk in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 154) 38 ST ltac:(lia) ltac:(lia)) as (jk & Hjk).
  pose proof (b5_rw_ba _ _ _ _ _ Hjk (bytes_at_normalize rsegs mem _ _ HMI HI) (b5_tID_len _ _)) as Hid.
  eapply (b5_mid B APIf ra empty FF g _ L A regs mem md _ [(g_S g - 1936 + 154, g_S g - 1936 + 192)]);
    [exact HFR | exact HP | b5_fp_tac | | |].
  - rewrite sl_mkR_of.
    apply (i02_evt ING) with (spv := g_S g - 1936) (phi := phi) (g := t_g (g_in g) j) (idb := t_ID (g_in g) j);
      [exact Hsp | | exact H12 | exact H13 | exact Hpll | lia | lia | exact H16 | lia | apply b5_tg_len
      | exact (b5_phi_g _ _ _ _ (bytes_at_normalize rsegs mem phi _ HMI Hphi) H50) | exact Hrec
      | exact (bytes_at_normalize rsegs mem _ _ HMI Ra) | exact Hid].
    unfold rg in H22. rewrite H22, Hbig. reflexivity.
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _ & Hrw).
    injection HE; intros; subst.
    assert (HKP : SKP regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [split; [|split; [|split]]|split].
    + apply (b5_FB_keep g j phi regs regs' mem m' _ HFB HKP MU'); b5_dj.
    + unfold t_ir in Hir. split.
      * unfold IDB, t_IDr, rp_id. rewrite Hir.
        apply (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel)). exact (sl_rw_bytes _ _ _ _ Hrw).
      * unfold t_IDr, rp_id. rewrite Hir. exact (INGOK _ _ _ (b5_tID_len _ _) Hok).
    + exact (b5_FGb_keep g _ mem m' _ (b5_tFG_len _ _) HG MU' ltac:(b5_dj)).
    + exact (b5_FSb_keep g _ _ regs regs' mem m' _ HS (proj1 (proj2 (proj2 (proj2 HKP)))) MU' ltac:(b5_dj)
               ltac:(b5_dj)).
    + exact Hir.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End I02.
