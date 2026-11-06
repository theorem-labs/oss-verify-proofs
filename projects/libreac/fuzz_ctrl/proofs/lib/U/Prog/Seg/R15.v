(* Segment R15 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x13580, 0x135ac], U13580 -> U135b0 (b = 0:
   #15 not taken (ports_parse = 0), T07 not taken (M8: q64 sp+24 = m & 7 = 0), #16, #17 not taken (in_ch, out_ch
   of the row), declaration_of(m, sp+1752) = 1). *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcDecl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import declaration_of_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.Seg Require Import Tac_slot Tac_u2 Tac_u2m.
Import ListNotations.
Open Scope Z_scope.

Lemma r15_evt : declaration_of_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv mr vi vo : Z) (row ob : list byte),
    sp = Z_to_bv 64 spv -> s0 = Z_to_bv 64 mr -> a0 = Z_to_bv 64 0 ->
    65536 <= spv -> spv + 1936 <= 2 ^ 64 -> 0 <= mr -> mr + 296 <= spv - 16 -> mr mod 8 = 0 ->
    ov_read_bytes rsegs m (wa (spv + 24)) 8 = Some (le8 (Z_to_bv 64 0)) ->
    ov_read_bytes rsegs m (wa (spv + 1688)) 4 = Some (le4 (Z_to_bv 64 vi)) ->
    ov_read_bytes rsegs m (wa (mr + 16)) 4 = Some (le4 (Z_to_bv 64 vi)) ->
    ov_read_bytes rsegs m (wa (spv + 1692)) 4 = Some (le4 (Z_to_bv 64 vo)) ->
    ov_read_bytes rsegs m (wa (mr + 20)) 4 = Some (le4 (Z_to_bv 64 vo)) ->
    stk rsegs m (spv - 16) spv -> length row = 296%nat -> bytes_at rsegs m mr row ->
    rw_cells rsegs m (spv + 1752) [CB 32 ob] -> mem_inv rsegs m -> decl_ok row = true ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x135b0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x135b0) fc None m' (seg_rom rsegs) /\
         munch [(spv - 16, spv); (spv + 1752, spv + 1784)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (spv + 1752) (decl row))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13580) fc None m (seg_rom rsegs)).
Proof.
  intros DECL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv mr vi vo row ob -> -> -> Hsp0 Hsp Hmr0 Hmr H8 R0 R1 R2 R3 R4 ST Lr HR HO MI Hok.
  assert (Hspu : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply unsigned_lit; lia).
  assert (Hmru : bv_unsigned (Z_to_bv 64 mr) = mr) by (apply unsigned_lit; lia).
  assert (Ha1u : bv_unsigned (Z_to_bv 64 (spv + 1752)) = spv + 1752) by (apply unsigned_lit; lia).
  step. if_false.
  step. step. if_false.
  step. step. step. lazymatch goal with
    | |- evt _ _ (MS _ _ (if negb (bv_eqb ?x ?x) then _ else _) _ _ _ _) => if_false_by (u2_neqb_refl x)
    end.
  step. step. step. lazymatch goal with
    | |- evt _ _ (MS _ _ (if negb (bv_eqb ?x ?x) then _ else _) _ _ _ _) => if_false_by (u2_neqb_refl x)
    end.
  step. step. step.
  eapply evt_cut.
  { eapply DECL with (lo := spv - 16) (row := row) (ob := ob).
    all: rewrite ?Hspu, ?Hmru, ?Ha1u; unfold DECLARATION_OF_FRAME.
    all: first [ exact ST | lia | exact Lr | exact HR | exact HO | exact MI ]. }
  intros ms' PO. unfold declaration_of_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & _ & _ & HD & _).
  subst ms'. rewrite Hok in *. rewrite ?Hspu, ?Hmru, ?Ha1u in *. unfold DECLARATION_OF_FRAME in MU.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [|exact MU]; intros x Hx; cbn [outside] in *; lia|].
  split; [exact WM|]. exact (sl_rw_bytes _ _ _ _ HD).
Qed.

Section R15.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis DECL : declaration_of_contract.
(* The ubsan image helper of batch u1 (slot-plan-ubsan.md 2.2: the catalogue rows image_bytes (0x1fcc8 + 296 i)
   296 from G_img_c frame_RELRO), until it lands. *)
Hypothesis ROWS : forall mem i, relro B mem -> 0 <= i < CAT_N -> bytes_at rsegs mem (CAT + CAT_ROW * i) (rowb i).

Lemma seg_R15 : Hcut B APIf ra (Inv_U135b0 B APIf ra empty) -> Hcut B APIf ra (Inv_U13580 B APIf ra empty).
Proof.
  intros H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HRF & H21 & H10 & HI & HO & _).
  pose proof HRF as (HRB & Hnz & H20 & HF).
  pose proof HRB as (Hb6 & _ & _ & (H8 & _) & HM8 & H9 & HID & HFG).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & HREL & _).
  destruct (u2_RS_len (g_in g) 0) as (LI & LF).
  pose proof alloc_ceiling_value as Hac.
  pose proof HFR as ((_ & _ & _ & _ & HSC & _) & _).
  pose proof (u2_istar_range (g_in g)) as Hi.
  destruct (u2_mrow_rng (g_in g)) as (Hmr & Hm8).
  destruct (u2_row_io (istar (g_in g)) Hi) as (Eic & Eoc & Bic & Boc).
  pose proof (ROWS mem (istar (g_in g)) HREL Hi) as HROW.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI HROW) as HROWn.
  pose proof (bytes_at_ov_read rsegs (normalize rsegs mem) _ _ 16 4 HROWn ltac:(rewrite u2_row_len; lia)) as R2.
  pose proof (bytes_at_ov_read rsegs (normalize rsegs mem) _ _ 20 4 HROWn ltac:(rewrite u2_row_len; lia)) as R4.
  rewrite Eic in R2. rewrite Eoc in R4. change (Z.of_nat 16) with 16 in R2. change (Z.of_nat 20) with 20 in R4.
  pose proof (u2_rtm_in (g_in g)) as Ein. pose proof (u2_rtm_out (g_in g)) as Eout. unfold rt_mb in Ein, Eout.
  rewrite <- Ein in R2. rewrite <- Eout in R4.
  unfold M8, u32, q64, spk, SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  pose proof (u2_ovr _ _ _ (bytes_at_normalize rsegs mem _ _ HMI HM8)) as R0. rewrite length_le8 in R0.
  pose proof (u2_ovr _ _ _ (bytes_at_normalize rsegs mem _ _ HMI HI)) as R1. rewrite length_le4 in R1.
  pose proof (u2_ovr _ _ _ (bytes_at_normalize rsegs mem _ _ HMI HO)) as R3. rewrite length_le4 in R3.
  assert (ST16 : stk rsegs (normalize rsegs mem) (g_S g - 1936 - 16) (g_S g - 1936))
    by (apply (u2_stk_sub _ _ _ _ _ ST); lia).
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 1752) 32 ST ltac:(lia) ltac:(lia)) as (ob & HOB).
  destruct (u2_hb B APIf ra empty FF g phi (rnb g 0) L A regs mem md HFR HP) as (_ & Hphi & Hphin).
  assert (Hphb : phi + rnb g 0 <= g_S g - 1936 - 16) by lia.
  unfold rt_mb in *.
  eapply (sl_mid B APIf ra empty FF g _ L A regs mem md); [exact HFR | exact HP | | |].
  - rewrite sl_mkR_of.
    apply (r15_evt DECL) with (spv := g_S g - 1936) (mr := mrow (g_in g))
      (vi := 4 * RcLeaf.n_in (rt_pbs (g_in g))) (vo := 4 * RcLeaf.n_out (rt_pbs (g_in g)))
      (row := rowb (istar (g_in g))) (ob := ob);
      [exact Hsp | exact H8 | exact H10 | lia | lia | unfold CAT, CAT_ROW in Hmr; lia | unfold CAT, CAT_ROW in Hmr; lia
      | exact Hm8 | exact R0 | exact R1 | exact R2 | exact R3 | exact R4 | exact ST16 | apply u2_row_len | exact HROWn
      | exact HOB | exact (mem_inv_normalize rsegs mem) | exact (u2_rtm_declok (g_in g))].
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|].
    split; [|split; [reflexivity | split; reflexivity]].
    eexists. split; [exact MU|]. split; [exact WM|].
    intros z Hz O. cbn [outside] in O. unfold SLOT_K, SLOT_STACK. lia.
  - intros R pc' m0' regs' m' HQ Hx Hrel HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & MU & _ & HD).
    injection HE; intros; subst.
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    assert (KR : u2_kr regs' regs).
    { unfold u2_kr. rewrite !(sl_getr_eqv _ _ _ Hx). repeat split. }
    split.
    { apply (u2_RFb_keep g 0 _ _ phi regs regs' mem m'' m' _ HMI MU Hrel LI LF); [| | exact KR | | exact HRF].
      - cbn [disjoint_from]. unfold spk, fsp, SLOT_FRAME. lia.
      - cbn [disjoint_from]. lia.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity. }
    unfold rg, spk, fsp, SLOT_FRAME in *. rewrite !(sl_getr_eqv _ _ _ Hx).
    split; [exact H21|]. split; [reflexivity|].
    exact (u2_out _ _ _ _ Hrel HD).
Qed.

End R15.
