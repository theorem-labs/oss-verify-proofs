(* Segment W03 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13d58, 0x13d68], bcmp(blk, decl_i, 32).
   K13d58 -> K13d6c; the exit to K13d70 (declaration_of = 0) is not taken (a0 = 1 at K13d58).
   libreac v1.9.0 (table 5a S_W03: IDENTICAL-RENUMBER, OLD 0x13d28 .. 0x13d38): pcs, decl_i at 1776 -> 1792, frame
   1920 -> 1936; CC7 carries VCm (s6 = Φ + 18, TF at sp+24, B at sp+1752); cuts K13d28 -> K13d58, K13d3c ->
   K13d6c, K13d40 -> K13d70 (SlotInv.v's renames), so seg_W03 is stated on the renamed cuts. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Exec Step Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse RcFrag SlotModel SlotInv bcmp_c bcmp_ro_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b8 Tac_b8m.
Import ListNotations.
Open Scope Z_scope.

Lemma b8_decl_len : forall i, (i < 11)%nat -> length (decl_i (Z.of_nat i)) = 32%nat.
Proof.
  intros i Hi.
  assert (H : forallb (fun i => Nat.eqb (length (decl_i (Z.of_nat i))) 32) (seq 0 11) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Nat.eqb_eq. exact (H i ltac:(apply in_seq; lia)).
Qed.

Lemma kW03 : bcmp_ro_contract -> forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
    x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (sp0 r : Z) (ls rs : list byte) (v : Z),
  x2 = Z_to_bv 64 sp0 -> x10 = Z_to_bv 64 1 -> x22 = Z_to_bv 64 r ->
  0 <= sp0 -> sp0 + 1936 < 2 ^ 64 -> 0 <= r < 2 ^ 64 ->
  bytes_at rsegs m r ls -> bytes_at rsegs m (sp0 + 1792) rs -> memcmp_model ls rs 32 = Some v ->
  MemNorm.ro_agree rsegs m ->
  Exec.evt rsegs
    (fun ms' => exists R pc' m', ms' = MS R F pc' fc None m' (seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x13d6c /\ getr R 10 = Z_to_bv 64 v /\
        getr R 2 = Z_to_bv 64 sp0 /\ getr R 3 = x3 /\ getr R 4 = x4 /\ getr R 8 = x8 /\ getr R 9 = x9 /\
        getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\ getr R 21 = x21 /\ getr R 22 = x22 /\
        getr R 23 = x23 /\ getr R 24 = x24 /\ getr R 25 = x25 /\ getr R 26 = x26 /\ getr R 27 = x27 /\
        munch [] m m' /\ wmono rsegs m m' /\ MemNorm.ro_agree rsegs m'))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13d58) fc None m (seg_rom rsegs)).
Proof.
  intros BCMPC x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m sp0 r ls rs v E2 E10 E22 H0 H1 Hr HL HR HM HRO.
  subst x2 x10 x22. step.
  first [if_cases HC; [exfalso; vm_compute in HC; discriminate HC|] | idtac].
  step. step. step. step.
  eapply evt_cut.
  { eapply BCMPC with (ls := ls) (rs := rs) (v := v).
    - rewrite unsigned_lit by lia. exact HL.
    - rewrite unsigned_lit by lia. exact HR.
    - rewrite (unsigned_lit 32) by lia. exact HM.
    - exact HRO. }
  intros ms' (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & MU & WM & RO & _ & _).
  subst ms'. apply evt_done. eexists _, _, _. split; [reflexivity|].
  split; [apply b8_ret_pc; lia|].
  repeat (split; [reflexivity|]). split; [exact MU|]. split; [exact WM | exact RO].
Qed.

Section W03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis BCMPC : bcmp_ro_contract.

Lemma seg_W03 : forall j i : nat, Hat2 B APIf ra (Inv_K13d6c_at B APIf ra empty) j i ->
  Hat2 B APIf ra (Inv_K13d70_at B APIf ra empty) j i -> Hat2 B APIf ra (Inv_K13d58_at B APIf ra empty) j i.
Proof.
  intros j i H3c _ g c (phi & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP (HWB & H10 & HD).
  pose proof HWB as ((HC7 & Hsel) & Hi & H23 & H8 & Hprev).
  pose proof HC7 as ((Hj & H26 & HFC & H21 & HBphi & HO & HM7) & H18 & (H22 & HT & HB) & HI).
  pose proof (b8_FR_sp B APIf ra empty g _ L A regs mem md HF) as (Hsp & H16 & HSK & HS47).
  pose proof alloc_ceiling_value as HAC.
  assert (Hbig : 50 <= t_len (g_in g) j) by exact (b8_rowsel_big _ _ Hsel).
  assert (Hin : In (phi, t_len (g_in g) j) (blocks L A))
    by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  destruct (b8_block_pos B APIf ra empty g _ L A regs mem md _ _ HF Hin) as [Hph1 Hph2].
  assert (Etb : t_big (g_in g) j = true) by (unfold t_big; apply Z.leb_le; exact Hbig).
  rewrite Etb in H22.
  set (ls := t_blk (g_in g) j).
  set (rs := decl_i (Z.of_nat i)).
  pose proof (b8_phi_length (g_in g) j) as Hpl.
  assert (Hls : length ls = 32%nat).
  { unfold ls. rewrite b8_blk by exact Hbig. rewrite length_firstn, length_skipn. lia. }
  assert (Hrs : length rs = 32%nat) by (unfold rs; apply b8_decl_len; lia).
  assert (HLb : bytes_at rsegs mem (phi + 18) ls).
  { unfold ls. rewrite b8_blk by exact Hbig. apply (b8_ba_sub rsegs mem phi _ 18 32 HBphi). lia. }
  assert (HRb : bytes_at rsegs mem (g_S g - 1936 + 1792) rs).
  { replace (g_S g - 1936 + 1792) with (spk g 1792) by (unfold spk, fsp, SLOT_FRAME; lia). exact HD. }
  destruct (memcmp_model_total ls rs 32 ltac:(lia) ltac:(lia)) as (v & Hv).
  destruct (b8_mm_spec 32 ls rs v Hls Hrs Hv) as [Hiff Hvr].
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & HMR & _).
  unfold MI in HMI. rewrite (b8_segs B APIf ra empty FF) in HMI.
  destruct (b8_md B APIf L A mem md HMR) as [Hh Hz].
  eapply (kb_run B regs (Z_to_bv 64 0x13d58) mem md _ (Post B APIf ra g) Hh Hz).
  { rewrite (b8_segs B APIf ra empty FF). unfold rmk.
    eapply (kW03 BCMPC) with (sp0 := g_S g - 1936) (r := phi + 18) (ls := ls) (rs := rs) (v := v);
      [exact Hsp | exact H10 | exact H22 | lia | lia | lia | exact HLb | exact HRb | exact Hv | exact HMI]. }
  intros R pc' m' regs' (Epc & E10 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 &
    E27 & MU & WM & RO) HG.
  subst pc'. apply H3c. exists phi.
  assert (MUw : forall W, munch W mem m') by (intros W x _; apply MU; exact I).
  apply (b8_cut_close B APIf ra empty _ _ _ _ L A).
  - apply (b8_FR_frame B APIf ra empty FF g _ L A regs' mem md m').
    + apply (b8_FR_regs B APIf ra empty _ _ _ _ _ _ _ _ HF).
      * rewrite HG, E2. symmetry. exact Hsp.
      * rewrite HG, E3. reflexivity.
      * rewrite HG, E4. reflexivity.
    + exact HP.
    + apply MUw.
    + exact WM.
  - exact HP.
  - split; [|split].
    + split; [split; [|exact Hsel]|].
      * apply (b8_CC7_munch g j phi regs' mem m' []); [| apply MUw | intros; exact I].
        apply (b8_CC7_regs _ _ _ regs); [exact HC7 | rewrite HG; assumption ..].
      * split; [exact Hi|]. split; [unfold rg; rewrite HG, E23; exact H23|].
        split; [unfold rg; rewrite HG, E8; exact H8 | exact Hprev].
    + apply (b8_ba_munch rsegs [] mem m' _ _ HD MU). intros; exact I.
    + rewrite HG, E10. rewrite (b8_lit0 v Hvr). exact Hiff.
Qed.

End W03.
