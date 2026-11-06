(* Segment M01 of reac-pw/fuzz_pin LLVMFuzzerTestOneInput (plain): [0x12d1c, 0x12de4), K12d1c -> K12de4
   (LLVMFuzzerTestOneInput_c.v S_M01). The body is pin_mid_contract's evt (memcpy, NUL, strlen, the scan,
   fuzz_catalogue_row, reac_box_pin_parse, check_known/row/label), taken as a Section hypothesis and run on the
   normalized memory with Tac_slot.sl_run, as libreac/fuzz_ctrl's released Prog/Seg/F02.v (origin/ossv/recipes
   25e3d17bdb50) runs f02_evt. Its premises come from FR at K12d1c: s := pin_str (g_in g) at g_src g (Tac_m01.m01_src),
   the live block (phi, k + 1) writable (b1_hb), outside the image (b1_blk_rom) with its slack (b1_slack_ok), the
   stack [S - 65536, S - 64) and the cells [S - 64, S - 48) (sl_fr_stk), the table in frame_RELRO's first block
   (b8_relro_norm), the SSP cells from the allocator relation's statics (m01_ssp). Its writes, [S - 240, S - 48) and
   the block, keep FR (b1_fr_hb); s0 = phi and s5-s11 give K12de4's registers. No function is proved here. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec fuzz_catalogue_row_c reac_box_pin_parse_c
  SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b8 Tac_m01.
Import ListNotations.
Open Scope Z_scope.

Section M01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.
Hypothesis MID : pin_mid_contract.

Lemma seg_M01 : S_M01 B APIf ra empty.
Proof.
  unfold S_M01. intros H1 g c (phi & L & A & regs & mem & md & -> & HFR & HP & (H10 & Hphi0 & H9 & H18 & H19 & HKS)).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & _ & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  destruct (b1_hb B APIf ra empty FF g phi (g_k g + 1) L A regs mem md HFR HP) as (STb & Hphi & Hphin).
  pose proof (b1_blk_rom B APIf ra empty FF g phi (g_k g + 1) L A regs mem md HFR HP) as HROM.
  assert (Hk0 : 0 <= g_k g) by (unfold g_k; lia).
  destruct (b1_slack_ok B APIf ra empty FF g phi (g_k g + 1) L A regs mem md HFR HP ltac:(lia))
    as (slack & HSL & HSLm & HSLc).
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & HMI0 & HRL & HM & _).
  pose proof HGV as (_ & _ & _ & _ & HSKc & _).
  destruct (m01_ssp B APIf ra empty FF L A mem md HM) as (HGOT & can & HGRD).
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof alloc_ceiling_value as (Hac & _).
  assert (HLs : Z.of_nat (length (pin_str (g_in g))) = g_k g) by (rewrite pin_str_length; reflexivity).
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  assert (Hspu : bv_unsigned (YK11.getr regs 2) = g_S g - 64).
  { rewrite Hsp. apply MState.unsigned_lit. lia. }
  destruct (sl_rw_of_stk _ _ _ phi (S (length (pin_str (g_in g)))) STb ltac:(lia) ltac:(lia)) as (junk & HC).
  rewrite SEGS.
  eapply (sl_run regs (Z_to_bv 64 0x12d1c) mem md _ _ Hh Hl HMI).
  - rewrite sl_mkR_of.
    eapply MID with (s := pin_str (g_in g)) (junk := junk) (slack := slack) (fl := g_fl g) (src := g_src g)
      (phi := phi) (lo := g_S g - 65536) (can := can).
    + exact H10.
    + exact Hphi0.
    + rewrite HLs. exact H9.
    + exact H18.
    + exact H19.
    + apply pin_flags_range.
    + apply pin_str_no_nul.
    + exact (bytes_at_normalize rsegs mem _ _ HMI (proj1 (m01_src B APIf ra empty FF g phi L A regs mem md HFR HP))).
    + exact HC.
    + intros a Ha. apply HROM. lia.
    + replace (phi + Z.of_nat (length (pin_str (g_in g))) + 1) with (phi + (g_k g + 1)) by lia. exact HSL.
    + replace (phi + Z.of_nat (length (pin_str (g_in g))) + 1) with (phi + (g_k g + 1)) by lia. exact HSLm.
    + exact (proj2 (m01_src B APIf ra empty FF g phi L A regs mem md HFR HP)).
    + rewrite Hspu. apply (b8_stk_sub _ _ _ _ _ _ ST); lia.
    + rewrite Hspu. unfold MID_STACK. lia.
    + rewrite Hspu. exact (proj1 (proj2 (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR))).
    + rewrite Hspu. unfold MID_OUT. apply (m01_wr_of_stk _ _ _ _ _ ST); lia.
    + rewrite Hspu. unfold MID_OUT. intros a Ha. apply (b8_seg_rom_hi B APIf ra empty FF). lia.
    + left. lia.
    + intros a Ha. apply (b8_relro_norm B APIf ra empty FF mem a HRL HMI0).
      unfold FUZZ_CATALOGUE, CAT_BYTES in Ha. lia.
    + exact (bytes_at_normalize rsegs mem _ _ HMI HGOT).
    + exact (bytes_at_normalize rsegs mem _ _ HMI HGRD).
    + exact (mem_inv_normalize rsegs mem).
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' &
                    HE & MU & WM & _ & _).
    injection HE; intros; subst.
    rewrite Hspu, HLs in MU. unfold MID_STACK, MID_OUT in MU.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) m' _ HR0 Hrel Hsame MU) as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) m' _ HR0 Hrel Hsame WM) as WM'.
    pose proof (ro_agree_same rsegs mem m' HMI Hsame) as Hro'.
    rewrite <- SEGS. apply H1. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split.
    { apply (b1_fr_hb B APIf ra empty FF g phi (g_k g + 1) L A regs mem md regs' m' HFR HP).
      - intros a Ha Hs Hb. unfold SLOT_K, SLOT_STACK in Hs. apply MU'.
        rewrite MState.unsigned_lit by lia. cbn [outside].
        split; [lia | split; [lia | exact I]].
      - exact (m01_blk_present B APIf ra empty FF g phi (g_k g + 1) L A regs mem md m' HFR HP WM').
      - exact WM'.
      - exact Hro'.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity. }
    split; [exact HP|].
    destruct HKS as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
    cbv beta. unfold rg, KS. rewrite !(sl_getr_eqv _ _ _ Hx).
    split; [reflexivity|].
    split; [rewrite <- K1; reflexivity|]. split; [rewrite <- K2; reflexivity|].
    split; [rewrite <- K3; reflexivity|]. split; [rewrite <- K4; reflexivity|].
    split; [rewrite <- K5; reflexivity|]. split; [rewrite <- K6; reflexivity | rewrite <- K7; reflexivity].
Qed.

End M01.
