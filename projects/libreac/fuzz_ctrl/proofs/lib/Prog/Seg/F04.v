(* Segment F04 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13734, 0x13744], K13734 -> K13748
   (len = 0: s9 = Φ + 18, reac_ctrl_parse(Φ, 0, sp+1752) reads nothing: a0 = k_j = 0, p = B_j = 36 zeros). *)
(* libreac v1.9.0 (IDENTICAL-RENUMBER, segment table 5a S_F04): v1.8 [0x13728, 0x13738] K13728 -> K1373c; the parse
   result p sp+1736 -> sp+1752, the frame 1920 -> 1936, reac_ctrl_parse 0x141d0 (contract). FT / IFS are SlotInv.v's
   v1.9 forms. Statement kept on the renamed cuts. rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv RcParse reac_ctrl_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b4.
Import ListNotations.
Open Scope Z_scope.

Lemma f04_evt : reac_ctrl_parse_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi n : Z) (fr junk : list byte),
    sp = Z_to_bv 64 spv -> s5 = Z_to_bv 64 phi -> n = 0 ->
    65536 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 ->
    0 < phi -> phi + 50 <= spv - 80 ->
    stk rsegs m (spv - 80) spv -> mem_inv rsegs m -> length fr = 50%nat ->
    rw_cells rsegs m (spv + 1752) [Cells.CB 36 junk] ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x13748) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse n fr)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 (phi + 18)) s10 s11
                       t3' t4' t5' t6')
                  F (Z_to_bv 64 0x13748) fc None m' (seg_rom rsegs) /\
         munch [(spv + 1752, spv + 1788); (spv - 80, spv)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 1752) (snd (ctrlparse n fr)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13734) fc None m (seg_rom rsegs)).
Proof.
  intros PARSE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi n fr junk Esp E5 En Hsp0 Hsp H16 Hph0 Hph Hst MI Hlen HC.
  subst sp s5 n.
  step. step. step. step. step.
  eapply evt_cut.
  { eapply PARSE with (f := phi) (n := 0) (o := spv + 1752) (S := spv) (fr := fr) (junk := junk).
    all: try unfold REAC_CTRL_PARSE_K.
    all: first [ reflexivity | lia | exact Hst | exact MI | exact Hlen | (intros i Hi; cbn in Hi; destruct Hi)
               | intros _; split; [lia|]; split; [lia|]; split; [exact HC|]; split; [lia | intros _; lia] ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & _ & _ & HZ).
  subst ms'.
  unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MUc.
  rewrite (proj2 (Z.eqb_neq (spv + 1752) 0) ltac:(lia)) in MUc. cbn [app] in MUc.
  replace (spv + 1752 + 36) with (spv + 1788) in MUc by lia.
  specialize (HZ ltac:(lia)).
  rewrite (MState.ret_pc_even 0x13748) by (first [reflexivity | lia]).
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [exact MUc|]. split; [exact WMc|]. exact (sl_rw_bytes _ _ _ _ HZ).
Qed.

Section F04.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PARSE : reac_ctrl_parse_contract.

Lemma seg_F04 : forall j : nat, Hat B APIf ra (Inv_K13748_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13734_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HFT & Hnz & HIFS)).
  pose proof HFT as (Hj & H26 & (H27 & H32 & H20) & H21 & Hphi & HOUR & HM7).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  destruct (b1_hb B APIf ra empty FF g phi (t_len (g_in g) j) L A regs mem md HFR HP) as (_ & Hphi0 & Hphin).
  pose proof alloc_ceiling_value as Hac.
  pose proof HFR as ((_ & _ & _ & _ & HSC & _) & _).
  pose proof (b4_len_range (g_in g) j) as (Hl0 & _).
  pose proof (b4_len_le (g_in g) j) as Hle.
  pose proof (b4_phi_len (g_in g) j) as HL.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 1752) 36 ST ltac:(lia) ltac:(lia)) as (junk & HC).
  assert (ST80 : stk rsegs (normalize rsegs mem) (g_S g - 1936 - 80) (g_S g - 1936)).
  { destruct ST as (S1 & S2 & S3). split; [lia|]. split; [lia|]. intros a Ha. apply S3. lia. }
  set (W := [(g_S g - 1936 + 1752, g_S g - 1936 + 1788); (g_S g - 1936 - 80, g_S g - 1936)]).
  eapply (b4_mid B APIf ra empty FF g _ L A regs mem md _ W); [exact HFR | exact HP | | | |].
  - intros x Hx O. refine (b4_fp g W x _ Hx O). unfold W, SLOT_K, SLOT_STACK.
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
  - rewrite sl_mkR_of.
    apply (f04_evt PARSE) with (spv := g_S g - 1936) (phi := phi) (n := t_len (g_in g) j)
      (fr := t_g (g_in g) j) (junk := junk);
      [exact Hsp | exact H21 | exact Hnz | lia | lia | lia | lia | lia | exact ST80
      | exact (mem_inv_normalize rsegs mem) | apply fr50_length | exact HC].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _ & HZ).
    injection HE; intros; subst.
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    assert (K : b4_keep mem m' (spk g 8) (spk g 192)).
    { apply (b4_keep_munch W mem m' _ _ MU'); [|unfold spk, fsp, SLOT_FRAME; lia..].
      unfold W, spk, fsp, SLOT_FRAME. cbn [disjoint_from]. repeat split; lia. }
    assert (KH : b4_keep mem m' phi (phi + t_len (g_in g) j)).
    { apply (b4_keep_munch W mem m' _ _ MU'); [|lia..].
      unfold W. cbn [disjoint_from]. repeat split; lia. }
    split; [|split; [exact Hnz|split; [|split; [|split]]]].
    + apply (b4_FT_keep g j phi regs regs' mem m' KH); [eapply b4_keep_sub; [exact K | lia | unfold spk; lia]
        | rewrite (sl_getr_eqv _ _ _ Hx); reflexivity .. | exact HFT].
    + apply (b4_IFS_keep g j regs regs' mem m'); [eapply b4_keep_sub; [exact K | unfold spk; lia | lia]
        | rewrite (sl_getr_eqv _ _ _ Hx); reflexivity | exact HIFS].
    + unfold V9, rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + exact (b1_out _ _ _ _ Hrel HZ).
Qed.

End F04.
