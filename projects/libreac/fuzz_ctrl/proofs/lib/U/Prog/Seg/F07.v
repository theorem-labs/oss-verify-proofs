(* Segment F07 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13954, 0x13960], U13954 -> U13964
   (reac_ctrl_parse (0x147b8) on Φ (s7) and len (s6) with no output struct, o = 0; v1.8 had Φ in s6, len in s5).
   Port of the plain seg_F07 (a working branch lib/Prog/Seg/F07.v). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u4.
Import ListNotations.
Open Scope Z_scope.

Lemma f07_evt : reac_ctrl_parse_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi len : Z) (fr : list byte),
    sp = Z_to_bv 64 spv -> s7 = Z_to_bv 64 phi -> s6 = Z_to_bv 64 len ->
    80 <= spv < 2 ^ 64 -> spv mod 16 = 0 -> 0 <= phi < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
    stk rsegs m (spv - 80) spv -> mem_inv rsegs m -> length fr = 50%nat ->
    (50 <= len -> 0 < phi /\ phi + 50 <= spv - 80) ->
    (forall i, In i (cp_rd len fr) -> mrd rsegs m (wa (phi + Z.of_nat i)) = nth_error fr i) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13964) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse len fr)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13964) fc None m' (seg_rom rsegs) /\
         munch [(spv - 80, spv)] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13954) fc None m (seg_rom rsegs)).
Proof.
  intros PA ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi len fr Hsp Hs7 Hs6 Hspv H16 Hphi Hlen ST MI Hfr Hbig Hrd.
  subst sp s7 s6.
  step. step. step. step.
  eapply evt_cut.
  { eapply PA with (f := phi) (n := len) (o := 0) (S := spv) (fr := fr) (junk := []);
      first [ reflexivity | apply bv_eq; reflexivity | unfold REAC_CTRL_PARSE_K; lia | exact ST | exact MI
            | exact Hfr | exact Hrd | intros C; exfalso; apply C; reflexivity
            | intros Hb; destruct (Hbig Hb); unfold REAC_CTRL_PARSE_K; lia ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & _).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x13964)) with (Z_to_bv 64 0x13964) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MUc | exact WMc].
Qed.

Section F07.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PARSE : reac_ctrl_parse_contract.

Lemma seg_F07 : forall j : nat, Hat B APIf ra (Inv_U13964_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13954_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HFB & HIFS).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof (u4_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  pose proof (u4_len_range (g_in g) j) as (Hl0 & Hb0 & Hbl).
  pose proof (proj1 HFR) as (Hn & _).
  pose proof HFB as (((Hj & H9 & _) & (HS24 & H21 & H22) & H23 & Hphi & H18) & _).
  unfold g_n in Hn.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  eapply (u4_mid B APIf ra empty FF g _ L A regs mem md _ [(g_S g - 1936 - 80, g_S g - 1936)]);
    [exact HFR | exact HP | | | |].
  - intros x Hx O. apply (sl_fp1 g (g_S g - 1936 - 80) (g_S g - 1936) x);
      [unfold SLOT_K, SLOT_STACK; lia | lia | exact Hx | exact O].
  - rewrite sl_mkR_of.
    apply (f07_evt PARSE) with (spv := g_S g - 1936) (phi := phi) (len := t_len (g_in g) j)
      (fr := t_g (g_in g) j); [exact Hsp | exact H23 | exact H22 | lia | lia | lia | lia | | | | |].
    + apply (u4_stk_sub _ _ _ _ _ ST); lia.
    + exact (mem_inv_normalize rsegs mem).
    + apply u4_tg_len.
    + intros Hb. lia.
    + intros i Hi.
      destruct (Z_lt_le_dec (t_len (g_in g) j) 50) as [Hs|Hb].
      * unfold cp_rd in Hi. rewrite (proj2 (Z.leb_gt 50 _) Hs) in Hi. cbn in Hi. destruct Hi.
      * pose proof (cp_rd_lt39 _ _ _ Hi) as Hi39.
        pose proof (u4_phi_g _ _ _ _ (bytes_at_normalize rsegs mem phi _ HMI Hphi) Hb) as (_ & _ & HG).
        apply HG. rewrite u4_tg_len. lia.
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU & WM).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _).
    injection HE; intros; subst.
    assert (HKP : SKP regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [|split].
    + apply (u4_FB_keep g j phi regs regs' mem m' _ HFB HKP MU'); u4_dj.
    + apply (u4_IFS_keep g j mem m' _ HIFS MU'); u4_dj.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End F07.
