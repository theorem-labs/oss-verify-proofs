(* Segment C03 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x13fec, 0x14044], two entries.
   U13fec (classify = 0): #90 not taken (q.src != our, C31 C1.8), #91 (TF = 1 at sp+16, AF8), #92 (ev in 0 .. 5);
   then 0x14008 = U14008: k (s9) != 9 -> U140c0; k = 9 (so len >= 50, struct P5.1): T67-T69 not taken (HBR, Φ in s7),
   Phi[16] != 0xcd or Phi[17] != 0xea -> U140c0 (want_m = 0); else count = 0 at sp+1824 and reac_box_catalogue
   (CAT) -> U14048. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse RcClassify.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF reac_box_catalogue_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u8m Tac_u8.
Import ListNotations.
Open Scope Z_scope.

Lemma c03_zxbu : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof.
  intros b. unfold zxb. apply MState.unsigned_lit. pose proof (bv_unsigned_in_range 8 b) as R.
  unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma c03_firstn1 : forall (l : list byte) k, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l cp_z].
Proof.
  intros l k. revert l. induction k as [|k IH]; intros [|x l] H; cbn [length] in H; try lia.
  - reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.

Ltac c03_cond := unfold_cond; rewrite ?c03_zxbu; rewrite ?MState.unsigned_lit_wrap; solve_cond_rec.
Ltac c03_ifc b :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
      replace c with b by (symmetry; c03_cond); cbv iota
  end.
Ltac c03_if b :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
      replace c with b by (vm_compute; reflexivity); cbv iota
  end.
Ltac c03_by b H :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
      replace c with b by (symmetry; exact H); cbv iota
  end.

(* U13fec: #90, #91, #92 not taken; on to 0x14008. *)
Lemma c03_head :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv e : Z),
    sp = Z_to_bv 64 spv -> 0 <= spv -> spv + 1936 <= 2 ^ 64 -> bv_eqb a0 (Z_to_bv 64 0) = false ->
    ov_read_bytes rsegs m (wa (spv + 16)) 8 = Some (le8 (Z_to_bv 64 1)) ->
    ov_read_bytes rsegs m (wa (spv + 1684)) 4 = Some (le4 (Z_to_bv 64 e)) -> 0 <= e <= 5 ->
    evt rsegs
      (fun ms' => exists a0' a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 0x14008) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13fec) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv e -> Hs0 Hs1 Ha0 R56 Rev He.
  step. c03_by false Ha0.
  step. step. step. c03_if false.
  assert (Ee : e = 0 \/ e = 1 \/ e = 2 \/ e = 3 \/ e = 4 \/ e = 5) by lia.
  destruct Ee as [->|[->|[->|[->|[->| ->]]]]];
    (step; step; step; c03_if false; apply evt_done; do 2 eexists; reflexivity).
Qed.

(* 0x14008, k != 9: to 0x140c0. *)
Lemma c03_kx :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (k : Z),
    s9 = Z_to_bv 64 k -> 0 <= k <= 13 -> k <> 9 ->
    evt rsegs
      (fun ms' => exists a0' a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 0x140c0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14008) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m k -> Hk Hk9.
  step. step. c03_ifc true.
  apply evt_done. do 2 eexists. reflexivity.
Qed.

(* k = 9, Phi[16] != 0xcd: to 0x140c0. *)
Lemma c03_n16 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (b16 : byte),
    s9 = Z_to_bv 64 9 -> s7 = Z_to_bv 64 phi -> 4096 <= phi -> phi + 50 <= 2 ^ 63 ->
    ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [b16] -> bv_unsigned b16 <> 205 ->
    evt rsegs
      (fun ms' => exists a0' a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 0x140c0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14008) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi b16 -> -> Hp0 Hp1 R16 E16.
  step. step. c03_ifc false.
  step. c03_ifc false.
  step. step. c03_ifc false.
  step. step. step. c03_ifc true.
  apply evt_done. do 2 eexists. reflexivity.
Qed.

(* k = 9, Phi[16] = 0xcd, Phi[17] != 0xea: to 0x140c0. *)
Lemma c03_n17 :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi : Z) (b16 b17 : byte),
    s9 = Z_to_bv 64 9 -> s7 = Z_to_bv 64 phi -> 4096 <= phi -> phi + 50 <= 2 ^ 63 ->
    ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [b16] -> bv_unsigned b16 = 205 ->
    ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [b17] -> bv_unsigned b17 <> 234 ->
    evt rsegs
      (fun ms' => exists a0' a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 0x140c0) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14008) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi b16 b17 -> -> Hp0 Hp1 R16 E16 R17 E17.
  step. step. c03_ifc false.
  step. c03_ifc false.
  step. step. c03_ifc false.
  step. step. step. c03_ifc false.
  step. step. c03_ifc false.
  step. step. step. c03_ifc true.
  apply evt_done. do 2 eexists. reflexivity.
Qed.

(* k = 9, cd ea: count = 0 at sp+1824, reac_box_catalogue(&count) (CAT). *)
Lemma c03_cat : reac_box_catalogue_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi : Z) (b16 b17 : byte)
         (junk : list byte),
    sp = Z_to_bv 64 spv -> 0 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 ->
    s9 = Z_to_bv 64 9 -> s7 = Z_to_bv 64 phi -> 4096 <= phi -> phi + 50 <= 2 ^ 63 ->
    ov_read_bytes rsegs m (wa (phi + 16)) 1 = Some [b16] -> bv_unsigned b16 = 205 ->
    ov_read_bytes rsegs m (wa (phi + 17)) 1 = Some [b17] -> bv_unsigned b17 = 234 ->
    rw_cells rsegs m (spv + 1824) [CB 8 junk] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a1' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x14048) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x1fcc8) a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14048) fc None m' (seg_rom rsegs) /\
         munch [(spv + 1824, spv + 1832)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 1824) (le8 (Z_to_bv 64 11)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14008) fc None m (seg_rom rsegs)).
Proof.
  intros CATC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi b16 b17 junk -> Hs0 Hs1 H16 -> -> Hp0 Hp1 R16 E16 R17 E17 HC MI.
  pose proof (munch_refl [(spv + 1824, spv + 1832)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. c03_ifc false.
  step. c03_ifc false.
  step. step. c03_ifc false.
  step. step. step. c03_ifc false.
  step. step. c03_ifc false.
  step. step. step. c03_ifc false.
  step. step. step.
  eapply evt_cut.
  { eapply CATC with (c := spv + 1824).
    - first [reflexivity | apply bv_eq; reflexivity].
    - right. split; [lia | exact (proj2 HC)]. }
  intros ms' (a1' & m' & E & Hif). subst ms'.
  rewrite (proj2 (Z.eqb_neq (spv + 1824) 0) ltac:(lia)) in Hif.
  destruct Hif as (Hb & MUc & WMc & _).
  replace (ret_pc (Z_to_bv 64 0x14048)) with (Z_to_bv 64 0x14048)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists a1', m'. split; [reflexivity|].
  split; [|split; [exact (wmono_trans rsegs _ _ _ WM WMc) | exact Hb]].
  apply (munch_trans _ _ _ _ MU). eapply munch_weaken; [|exact MUc].
  unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | exact I].
Qed.

Section C03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis CATC : reac_box_catalogue_contract.

Lemma seg_C03 : forall j : nat,
  Hat B APIf ra (Inv_U14048_at B APIf ra empty) j -> Hat B APIf ra (Inv_U140c0_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13fec_at B APIf ra empty) j /\ Hat B APIf ra (Inv_U14008_at B APIf ra empty) j.
Proof.
  intros j H1 H2.
  assert (K14 : forall g phi L A regs mem md,
      FR B APIf ra empty g (hb1 phi (t_len (g_in g) j)) L A regs mem md ->
      Permutation (blocks L A) (hb1 phi (t_len (g_in g) j) ++ blocks (g_L g) (g_A g)) ->
      CC g j phi regs mem ->
      SR (ms_segs B) (mkCfg (YK11.mkst regs (Z_to_bv 64 0x14008) mem (YK11.seg_rom (ms_segs B))) md)
        (Post B APIf ra g)).
  { intros g phi L A regs mem md HFR HP HCC.
    pose proof HCC as ((HFT & HVC & HIFS) & H20 & H25).
    pose proof HFT as (_ & _ & H23 & Hphi & _).
    destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
    pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
    pose proof (u8_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
    pose proof (u8_t_facts (g_in g) j) as (_ & _ & _ & _ & HL & _).
    assert (Hk : 0 <= t_k (g_in g) j <= 13) by apply RcParse.ctrlparse_kind_range.
    unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
    (* The exits to U140c0: a run that changes a0, a1 only. *)
    assert (Kcc : forall Q : machine_state -> Prop,
        Exec.evt rsegs Q (MState.MS (rmk regs) fp_regs (Z_to_bv 64 0x14008) fp_csr None (normalize rsegs mem)
                            (seg_rom rsegs)) ->
        (forall ms, Q ms -> exists R, ms = MState.MS R fp_regs (Z_to_bv 64 0x140c0) fp_csr None (normalize rsegs mem)
                                         (seg_rom rsegs) /\
           YK11.getr R 2 = YK11.getr regs 2 /\ YK11.getr R 3 = YK11.getr regs 3 /\
           YK11.getr R 4 = YK11.getr regs 4 /\ CK regs R) ->
        t_rowsel (g_in g) j = false ->
        SR (ms_segs B) (mkCfg (YK11.mkst regs (Z_to_bv 64 0x14008) mem (YK11.seg_rom (ms_segs B))) md)
          (Post B APIf ra g)).
    { intros Q HE HQf Hr.
      eapply (u8_mid B APIf ra empty FF g _ L A regs mem md _ []); [exact HFR | exact HP | u8_fp_tac | | |].
      - rewrite sl_mkR_of. exact HE.
      - intros ms HQ. destruct (HQf ms HQ) as (R & -> & E2 & E3 & E4 & _).
        exists R, (Z_to_bv 64 0x140c0), (normalize rsegs mem).
        split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
        split; [exact E2|]. split; [exact E3 | exact E4].
      - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
        pose proof (fun r => sl_getr_eqv _ _ r Hx) as HG.
        destruct (HQf _ HQ) as (R1 & HE1 & _ & _ & _ & HK).
        injection HE1; intros; subst.
        apply (H2 g). exists phi. apply (u8_cut_close B APIf ra empty _ _ _ _ L A); [exact HFR' | exact HP |].
        split; [|unfold t_want_m; rewrite Hr; reflexivity].
        assert (HK' : CK regs regs').
        { destruct HK as (E8 & E9 & E18 & E21 & E22 & E23 & E24).
          repeat split; rewrite HG; assumption. }
        apply (u8_CC7_keep g j phi regs regs' mem m' _ (proj1 HCC) HK' MU'); u8_dj. }
    destruct (Z.eq_dec (t_k (g_in g) j) 9) as [K9|K9].
    2:{ eapply Kcc.
        - unfold rmk. apply c03_kx with (k := t_k (g_in g) j); [exact H25 | lia | exact K9].
        - intros ms (a0' & a1' & ->). eexists. split; [reflexivity|]. repeat split; reflexivity.
        - unfold t_rowsel. rewrite (proj2 (Z.eqb_neq _ 9) K9). reflexivity. }
    destruct (u8_k_big (g_in g) j ltac:(lia)) as (Hlen & Hbig).
    pose proof (bytes_at_normalize rsegs mem phi _ HMI Hphi) as Hphin.
    assert (HG50 : bytes_at rsegs (normalize rsegs mem) phi (t_g (g_in g) j)).
    { rewrite (u8_g_bytes _ _ Hlen). pose proof (u8_at_slice _ phi _ 0 50 Hphin) as E.
      cbn [Z.of_nat skipn] in E. rewrite Z.add_0_r in E. apply E. rewrite u8_phi_length. lia. }
    assert (R16 : ov_read_bytes rsegs (normalize rsegs mem) (wa (phi + 16)) 1 = Some [cp_b (t_g (g_in g) j) 16]).
    { pose proof (u8_ovr _ _ _ (u8_at_slice _ _ _ 16 1 HG50 ltac:(rewrite u8_tg_len; lia))) as E.
      rewrite c03_firstn1 in E by (rewrite u8_tg_len; lia). exact E. }
    assert (R17 : ov_read_bytes rsegs (normalize rsegs mem) (wa (phi + 17)) 1 = Some [cp_b (t_g (g_in g) j) 17]).
    { pose proof (u8_ovr _ _ _ (u8_at_slice _ _ _ 17 1 HG50 ltac:(rewrite u8_tg_len; lia))) as E.
      rewrite c03_firstn1 in E by (rewrite u8_tg_len; lia). exact E. }
    unfold V7, rg in H25. rewrite K9 in H25.
    destruct (Z.eq_dec (cp_v (t_g (g_in g) j) 16) 205) as [E16|E16].
    2:{ eapply Kcc.
        - unfold rmk. eapply c03_n16; [exact H25 | exact H23 | lia | lia | exact R16 | exact E16].
        - intros ms (a0' & a1' & ->). eexists. split; [reflexivity|]. repeat split; reflexivity.
        - unfold t_rowsel. rewrite K9, (proj2 (Z.eqb_neq _ 205) E16). reflexivity. }
    destruct (Z.eq_dec (cp_v (t_g (g_in g) j) 17) 234) as [E17|E17].
    2:{ eapply Kcc.
        - unfold rmk. eapply c03_n17; [exact H25 | exact H23 | lia | lia | exact R16 | exact E16 | exact R17
                                      | exact E17].
        - intros ms (a0' & a1' & ->). eexists. split; [reflexivity|]. repeat split; reflexivity.
        - unfold t_rowsel. rewrite K9, E16, (proj2 (Z.eqb_neq _ 234) E17). reflexivity. }
    destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 1824) 8 ST ltac:(lia) ltac:(lia)) as (junk & HC).
    eapply (u8_mid B APIf ra empty FF g _ L A regs mem md _ [(g_S g - 1936 + 1824, g_S g - 1936 + 1832)]);
      [exact HFR | exact HP | u8_fp_tac | | |].
    - rewrite sl_mkR_of.
      eapply (c03_cat CATC) with (spv := g_S g - 1936) (phi := phi) (junk := junk);
        [exact Hsp | lia | lia | exact H16 | exact H25 | exact H23 | lia | lia | exact R16 | exact E16 | exact R17
        | exact E17 | exact HC | exact (mem_inv_normalize rsegs mem)].
    - intros ms (a1' & m' & -> & MU & WM & _).
      do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split; reflexivity.
    - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      pose proof (fun r => sl_getr_eqv _ _ r Hx) as HG.
      destruct HQ as (a1' & m'' & HE & _ & _ & H11).
      injection HE; intros; subst.
      apply (H1 g). exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      assert (HK : CK regs regs') by (repeat split; rewrite HG; reflexivity).
      split; [apply (u8_CC_keep g j phi regs regs' mem m' _ HCC HK (eq_trans (HG _) eq_refl)
                       (eq_trans (HG _) eq_refl) MU'); u8_dj|].
      split; [unfold t_rowsel; rewrite K9, E16, E17; reflexivity|].
      split; [unfold rg; rewrite HG; reflexivity|].
      unfold q64, spk, fsp, SLOT_FRAME. apply (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel)). exact H11. }
  split.
  - intros g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HCC & HCLS & Hcn & Hiff)).
    destruct (t_cls (g_in g) j) as [e|] eqn:Ec; [|exfalso; apply Hcn; first [exact Ec | reflexivity]].
    pose proof HCLS as (HB & HV).
    pose proof HCC as ((HFT & HVC & HIFS) & H20 & H25).
    pose proof HVC as (H24 & HTF & HBq).
    destruct (u8_cls_k _ _ _ Ec) as (_ & _ & He).
    rewrite (u8_cls_TF _ _ _ Ec) in HTF.
    try rewrite Ec in HV. cbn [reac_ctrl_classify_box_frame_c.reac_ctrl_classify_box_frame_ev] in HV.
    assert (Ha0 : bv_eqb (YK11.getr regs 10) (Z_to_bv 64 0) = false).
    { destruct (bv_eqb (YK11.getr regs 10) (Z_to_bv 64 0)) eqn:E; [|reflexivity]. exfalso.
      apply (u8_cls_src _ _ _ Ec). apply Hiff. unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq. exact E. }
    destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
    unfold spk in *. unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
    eapply (u8_mid B APIf ra empty FF g _ L A regs mem md _ []); [exact HFR | exact HP | u8_fp_tac | | |].
    + rewrite sl_mkR_of. eapply c03_head with (spv := g_S g - 1936) (e := e);
        [exact Hsp | lia | lia | exact Ha0 | | | lia].
      * exact (u8_ld8 _ _ _ (bytes_at_normalize rsegs mem _ _ HMI HTF)).
      * pose proof (u8_ovr _ _ _ (bytes_at_normalize rsegs mem _ _ HMI HV)) as R. rewrite length_le4 in R. exact R.
    + intros ms (a0' & a1' & ->).
      do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      pose proof (fun r => sl_getr_eqv _ _ r Hx) as HG.
      destruct HQ as (a0' & a1' & HE). injection HE; intros; subst.
      apply (K14 g phi L A regs' m' md HFR' HP).
      assert (HK : CK regs regs') by (repeat split; rewrite HG; reflexivity).
      apply (u8_CC_keep g j phi regs regs' mem m' _ HCC HK (eq_trans (HG _) eq_refl) (eq_trans (HG _) eq_refl)
               MU'); u8_dj.
  - intros g c (phi & L & A & regs & mem & md & -> & HFR & HP & HCC).
    exact (K14 g phi L A regs mem md HFR HP HCC).
Qed.

End C03.
