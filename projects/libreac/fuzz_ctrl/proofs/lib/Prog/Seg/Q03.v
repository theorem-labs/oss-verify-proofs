(* Segment Q03 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13b98, 0x13ba4], K13b98 -> K13ba8 (call
   reac_ports_unknown at 0x13ba4 with c = 0): s8 = unk; PU C1.2, C1.3 return unk again and write no byte. *)
(* libreac v1.9.0 (IDENTICAL, segment table 5a S_Q03): v1.8 [0x13b68, 0x13b74] K13b68 -> K13b78, pcs only; VC ->
   VCm in EQ (SlotInv.v). Statement kept on the renamed cuts. rule 24: no function proved. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv reac_ports_unknown_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b7.
Import ListNotations.
Open Scope Z_scope.

(* 0x13b98 -> 0x13ba8 with a0 = unk, s6 = blk = Φ + 18, bs = blk's 20 bytes. *)
Lemma q03_evt : reac_ports_unknown_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (phi uk : Z) (bs : list byte),
    a0 = Z_to_bv 64 uk -> s6 = Z_to_bv 64 (phi + 18) -> 0 < phi -> phi + 50 < 2 ^ 64 ->
    length bs = 20%nat -> bytes_at rsegs m (phi + 18) bs ->
    uk = (if RcPorts.pu_decl bs then 4 * RcPorts.pu_nunk bs 12 else -1) ->
    evt rsegs
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' s8' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 uk)
                       a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8' s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13ba8) fc None m' (seg_rom rsegs) /\
         s8' = Z_to_bv 64 uk /\ munch [] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13b98) fc None m (seg_rom rsegs)).
Proof.
  intros PU ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m phi uk bs -> -> Hp1 Hp2 Hl HB Huk.
  step. step. step. step.
  eapply evt_cut.
  { eapply PU with (p := phi + 18) (c := 0) (bs := bs).
    - rewrite MState.unsigned_lit by lia. lia.
    - first [reflexivity | rewrite MState.unsigned_lit by lia; lia].
    - intros _. split; [lia | split; [exact Hl | exact HB]].
    - intros E. exfalso. apply E. reflexivity. }
  intros ms' (a2' & a3' & a4' & a5' & m' & -> & MUc & WMc & _ & _ & _).
  rewrite (MState.ret_pc_even 0x13ba8) by (first [reflexivity | lia]).
  assert (Eok : RcPorts.pu_ok (phi + 18) bs = RcPorts.pu_decl bs).
  { unfold RcPorts.pu_ok. replace (phi + 18 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  rewrite Eok, <- Huk. cbn [Z.eqb] in MUc.
  apply evt_done. eexists _, _, _, _, _, _, _, m'. split; [reflexivity|].
  split; [first [reflexivity | f_equal; lia]|]. split; [exact MUc | exact WMc].
Qed.

Section Q03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PU : reac_ports_unknown_contract.

Lemma seg_Q03 : forall j, Hat B APIf ra (Inv_K13ba8_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13b98_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & (HQB & H10)).
  pose proof HQB as (HEQ & H25 & HPO & H1792).
  pose proof HEQ as (HFT & H7 & H2 & HVC & HIFS & H88).
  pose proof HFT as (Hj & H26 & HFC & H21 & Hphi & HOUR & HM7).
  pose proof HVC as (H22 & H24 & HB).
  pose proof (b7_big_8819 _ _ H88) as Hbig.
  destruct (b7_phi_bnd B APIf ra empty g _ L A regs mem md phi _ HFR HP ltac:(lia)) as (Hp1 & Hp2).
  destruct (b7_S_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (HS1 & HS2 & HS3 & Hsp & HMI).
  pose proof alloc_ceiling_value as Hac.
  assert (H22' : rg regs 22 (phi + 18)).
  { unfold t_big in H22. rewrite (proj2 (Z.leb_le _ _) Hbig) in H22. exact H22. }
  destruct (ex_intro (fun u => u = t_unk (g_in g) j) _ eq_refl) as (UK & EUK). rewrite <- EUK in H10.
  eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of.
    apply (q03_evt PU) with (phi := phi) (uk := UK) (bs := t_pbs (g_in g) j).
    + exact H10.
    + exact H22'.
    + lia.
    + lia.
    + apply b7_pbs_length.
    + apply b7_pbs_bytes. apply b7_norm; [exact HMI|]. apply b7_g_bytes; [exact Hphi | exact Hbig].
    + rewrite EUK. unfold t_unk. reflexivity.
  - intros ms (ra' & a1' & a2' & a3' & a4' & a5' & s8' & m' & -> & _ & MU & WM).
    do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    exists []. split; [exact MU|]. split; [exact WM|]. intros x _ O. exfalso. apply O. exact I.
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (ra' & a1' & a2' & a3' & a4' & a5' & s8' & m'' & HE & E8 & MU & WM).
    apply b7_MS_inj in HE as (ER & EPC & EM). subst R pc' m0'.
    apply H. unfold Inv_K13ba8_at, FCUT, CUTST. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    assert (MT0 : MT [] mem m') by exact (b7_mt [] mem _ m' HMI MU Hrel).
    rewrite <- EUK.
    split; [|split].
    + apply (b7_QB g j phi regs mem regs' m' []); [exact HQB | exact MT0 | apply b7_DJE_nil | apply b7_DJQ_nil | |].
      * unfold EQR. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split; reflexivity.
      * rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). first [exact E8 | reflexivity].
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End Q03.
