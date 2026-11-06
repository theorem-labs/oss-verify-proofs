(* Segment F04 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13898, 0x138a4], U13898 (v1.8
   U1389c) -> U138a8 (v1.8 U138ac) (the len <= 49 parse: reac_ctrl_parse(Φ (s7), len (s6), sp+1752); no read
   premise, cp_rd is empty below 50). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u4.
Import ListNotations.
Open Scope Z_scope.

Lemma f04_evt : reac_ctrl_parse_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi len : Z) (fr ja : list byte),
    sp = Z_to_bv 64 spv -> s7 = Z_to_bv 64 phi -> s6 = Z_to_bv 64 len ->
    80 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 -> 0 <= phi < 2 ^ 64 -> 0 <= len <= 49 ->
    stk rsegs m (spv - 80) spv -> mem_inv rsegs m -> length fr = 50%nat ->
    rw_cells rsegs m (spv + 1752) [CB 36 ja] ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x138a8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse len fr)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x138a8) fc None m' (seg_rom rsegs) /\
         munch [(spv + 1752, spv + 1788); (spv - 80, spv)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 1752) (snd (ctrlparse len fr)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13898) fc None m (seg_rom rsegs)).
Proof.
  intros PA ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi len fr ja Hsp Hs7 Hs6 Hspv Hhi H16 Hphi Hlen ST MI Hfr Hja.
  subst sp s7 s6.
  step. step. step. step.
  eapply evt_cut.
  { eapply PA with (f := phi) (n := len) (o := spv + 1752) (S := spv) (fr := fr) (junk := ja);
      rewrite ?MState.unsigned_lit by lia;
      first [ reflexivity | unfold REAC_CTRL_PARSE_K; lia | exact ST | exact MI | exact Hfr
            | intros Hb; lia
            | intros i Hi; unfold cp_rd in Hi; rewrite (proj2 (Z.leb_gt 50 _)) in Hi by lia;
              cbn in Hi; destruct Hi
            | intros _; split; [lia|]; split; [lia|]; split; [exact Hja|]; split; [right; lia | intros; lia] ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & _ & _ & Hok).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x138a8)) with (Z_to_bv 64 0x138a8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MUc; rewrite (proj2 (Z.eqb_neq _ _)) in MUc by lia;
          replace (spv + 1752 + 36) with (spv + 1788) in MUc by lia; exact MUc|].
  split; [exact WMc|].
  exact (sl_rw_bytes _ _ _ _ (Hok ltac:(lia))).
Qed.

Section F04.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PARSE : reac_ctrl_parse_contract.

Lemma seg_F04 : forall j : nat, Hat B APIf ra (Inv_U138a8_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13898_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HFT & Hs & HIFS).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof (u4_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  pose proof (u4_len_range (g_in g) j) as (Hl0 & Hb0 & Hbl).
  pose proof HFT as (_ & (_ & H21 & H22) & H23 & Hphi & H18).
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 1752) 36 ST ltac:(lia) ltac:(lia)) as (ja & Hja).
  eapply (u4_mid B APIf ra empty FF g _ L A regs mem md _
            [(g_S g - 1936 + 1752, g_S g - 1936 + 1788); (g_S g - 1936 - 80, g_S g - 1936)]);
    [exact HFR | exact HP | u4_fp_tac | | |].
  - rewrite sl_mkR_of.
    apply (f04_evt PARSE) with (spv := g_S g - 1936) (phi := phi) (len := t_len (g_in g) j)
      (fr := t_g (g_in g) j) (ja := ja);
      [exact Hsp | exact H23 | exact H22 | lia | lia | lia | lia | lia | | | | exact Hja].
    + apply (u4_stk_sub _ _ _ _ _ ST); lia.
    + exact (mem_inv_normalize rsegs mem).
    + apply u4_tg_len.
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _ & HBo).
    injection HE; intros; subst.
    assert (HK : FTK regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [|split; [exact Hs|split; [|split]]].
    + apply (u4_FT_keep g j phi regs regs' mem m' _ HFT HK MU'); u4_dj.
    + apply (u4_IFS_keep g j mem m' _ HIFS MU'); u4_dj.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + apply (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel)). unfold spk, fsp, SLOT_FRAME. exact HBo.
Qed.

End F04.
