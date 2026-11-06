(* Segment F03 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13844, 0x13864], U13844 (v1.8
   U13848) -> U13868 (v1.8 U1386c); U13898 (v1.8 U1389c). Φ in s7, len in s6 (v1.8 s6 / s5): len < 50 ->
   U13898; T13 (Φ = 0) and T14 (Φ + 18 wraps) not taken by HBR (Φ is a heap block below S - K); the len >= 50 parse:
   reac_ctrl_parse(Φ, len, sp+1752) (0x147b8). *)
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

Lemma f03_small :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (len : Z),
    s6 = Z_to_bv 64 len -> 0 <= len < 50 ->
    evt rsegs
      (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 50) a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x13898) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13844) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m len -> Hl.
  step. step. if_true_by (u4_ltu_true len 50 ltac:(lia) ltac:(lia)).
  apply evt_done. reflexivity.
Qed.

Lemma f03_evt : reac_ctrl_parse_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi len : Z) (fr ja : list byte),
    sp = Z_to_bv 64 spv -> s7 = Z_to_bv 64 phi -> s6 = Z_to_bv 64 len ->
    80 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 -> 0 < phi -> phi + 50 <= spv - 80 ->
    50 <= len < 2 ^ 64 ->
    stk rsegs m (spv - 80) spv -> mem_inv rsegs m -> length fr = 50%nat ->
    (forall i, In i (cp_rd len fr) -> mrd rsegs m (wa (phi + Z.of_nat i)) = nth_error fr i) ->
    rw_cells rsegs m (spv + 1752) [CB 36 ja] ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13868) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse len fr)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13868) fc None m' (seg_rom rsegs) /\
         munch [(spv + 1752, spv + 1788); (spv - 80, spv)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 1752) (snd (ctrlparse len fr)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13844) fc None m (seg_rom rsegs)).
Proof.
  intros PA ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi len fr ja Hsp Hs7 Hs6 Hspv Hhi H16 Hphi Hpb Hlen ST MI Hfr Hrd Hja.
  subst sp s7 s6.
  step. step. if_false_by (u4_ltu_false len 50 ltac:(lia) ltac:(lia)).
  step. if_false_by (u4_eqb0 phi ltac:(lia)).
  step. step. rewrite (u4_ltu_neg phi (-18)) by lia. if_false.
  step. step. step. step.
  eapply evt_cut.
  { eapply PA with (f := phi) (n := len) (o := spv + 1752) (S := spv) (fr := fr) (junk := ja);
      rewrite ?MState.unsigned_lit by lia;
      first [ reflexivity | unfold REAC_CTRL_PARSE_K; lia | exact ST | exact MI | exact Hfr | exact Hrd
            | intros _; unfold REAC_CTRL_PARSE_K; split; [lia|]; split; [lia|]; left; lia
            | intros _; split; [lia|]; split; [lia|]; split; [exact Hja|]; split; [right; lia | intros; right; lia] ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & _ & _ & Hok).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x13868)) with (Z_to_bv 64 0x13868) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split; [unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MUc; rewrite (proj2 (Z.eqb_neq _ _)) in MUc by lia;
          replace (spv + 1752 + 36) with (spv + 1788) in MUc by lia; exact MUc|].
  split; [exact WMc|].
  exact (sl_rw_bytes _ _ _ _ (Hok ltac:(lia))).
Qed.

Section F03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PARSE : reac_ctrl_parse_contract.

Lemma seg_F03 : forall j : nat, Hat B APIf ra (Inv_U13868_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13898_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13844_at B APIf ra empty) j.
Proof.
  intros j H1 H2 g c (phi & L & A & regs & mem & md & -> & HFR & HP & HFT & Hn0 & HIFS).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof (u4_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  pose proof (u4_len_range (g_in g) j) as (Hl0 & Hb0 & Hbl).
  pose proof (proj1 HFR) as (Hn & _).
  pose proof HFT as (_ & (_ & H21 & H22) & H23 & Hphi & H18).
  unfold g_n in Hn.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (Z_lt_le_dec (t_len (g_in g) j) 50) as [Hs|Hb].
  - eapply (u4_mid B APIf ra empty FF g _ L A regs mem md _ []); [exact HFR | exact HP | | | |].
    + intros x Hx O. exfalso. apply O. exact I.
    + rewrite sl_mkR_of. apply f03_small with (len := t_len (g_in g) j); [exact H22 | lia].
    + intros ms ->. do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|].
      split; [apply wmono_refl|]. split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      injection HQ; intros; subst.
      assert (HK : FTK regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
      apply H2. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [|split; [lia|]].
      * apply (u4_FT_keep g j phi regs regs' mem m' _ HFT HK MU'); u4_dj.
      * apply (u4_IFS_keep g j mem m' _ HIFS MU'); u4_dj.
  - destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 1752) 36 ST ltac:(lia) ltac:(lia)) as (ja & Hja).
    eapply (u4_mid B APIf ra empty FF g _ L A regs mem md _
              [(g_S g - 1936 + 1752, g_S g - 1936 + 1788); (g_S g - 1936 - 80, g_S g - 1936)]);
      [exact HFR | exact HP | u4_fp_tac | | |].
    + rewrite sl_mkR_of.
      apply (f03_evt PARSE) with (spv := g_S g - 1936) (phi := phi) (len := t_len (g_in g) j)
        (fr := t_g (g_in g) j) (ja := ja);
        [exact Hsp | exact H23 | exact H22 | lia | lia | lia | lia | lia | lia | | | | | exact Hja].
      * apply (u4_stk_sub _ _ _ _ _ ST); lia.
      * exact (mem_inv_normalize rsegs mem).
      * apply u4_tg_len.
      * intros i Hi.
        pose proof (cp_rd_lt39 _ _ _ Hi) as Hi39.
        pose proof (u4_phi_g _ _ _ _ (bytes_at_normalize rsegs mem phi _ HMI Hphi) Hb) as (_ & _ & HG).
        apply HG. rewrite u4_tg_len. lia.
    + intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU & WM & _).
      do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _ & HBo).
      injection HE; intros; subst.
      assert (HK : FTK regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
      apply H1. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [|split; [exact Hb|split; [|split]]].
      * apply (u4_FT_keep g j phi regs regs' mem m' _ HFT HK MU'); u4_dj.
      * apply (u4_IFS_keep g j mem m' _ HIFS MU'); u4_dj.
      * unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      * apply (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel)). unfold spk, fsp, SLOT_FRAME. exact HBo.
Qed.

End F03.
