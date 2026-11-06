(* Cut-free (agreement) copy of lib/U/Prog/Seg/M01.v, over U/Prog/SlotInvCF.v (SR := SRcf) as
   libreac/fuzz_ctrl's released U/Prog/SegCF/*.v copy its U/Prog/Seg/*.v: the same text with SlotInv -> SlotInvCF,
   Seg -> SegCF, the segment statements from SegCF/StmtsCF.v, frame_facts_ubsan -> SlotInvCF.frame_facts_cf and the
   allocator contracts in their cut-free forms (frame_allocator_cf, malloc_contract_cfg, free_contract_cf).
   The text of the original follows. *)
(* Segment S_M01 of reac-pw/fuzz_pin LLVMFuzzerTestOneInput (UBSan): K12d50 -> K12e24, the middle segment
   [0x12d50, 0x12e24) run as pin_mid_contract's evt on the normalized memory (U/Prog/LLVMFuzzerTestOneInput_c.v), the
   frame rebuilt with b1_fr_hb. Shape of libreac/fuzz_ctrl's released U/Prog/Seg/F02.v (its len <> 0 branch: a
   callee contract run on `normalize rsegs mem` through sl_run). pin_mid_contract's instance: s the spec string
   pin_spec.pin_str of the input, fl the flags byte, src the rest's address, lo = S - 65536, sp = S - 80. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U Require Import Contract Img0 FrameAPI MemNorm KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog Require Import fuzz_catalogue_row_c reac_box_pin_parse_c LLVMFuzzerTestOneInput_c SlotInvCF.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog.SegCF Require Import StmtsCF.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.U.Prog.SegCF Require Import Tac_slot Tac_b1 Tac_b8.
Import ListNotations.
Open Scope Z_scope.

Lemma m01_stk_wr : forall segs m lo hi a n, Frame.stk segs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n ->
  wr_at segs m a n.
Proof.
  intros segs m lo hi a n (H1 & H2 & H) Ha Hn Hn0. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

Lemma m01_pin_k_le : forall inp, (pin_k inp <= length (tl inp))%nat.
Proof. intros inp. unfold pin_k, pin_rest. apply nul_idx_le. Qed.

Section M01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_cf B APIf LS SH SK ra empty.
Hypothesis MID : pin_mid_contract.
Let API := APIf rc.

(* The input block's bytes: GV's blk_data on the entry memory and FR's unchanged entry blocks. *)
Lemma m01_in_bytes : forall g hb L A regs mem md, FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> 0 < g_n g ->
  bytes_at rsegs mem (g_p g) (g_in g).
Proof.
  intros g hb L A regs mem md HFR HP Hn.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (b8_p_range B APIf ra empty FF g hb L A regs mem md HFR HP) as (Hp0 & Hpn & _).
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk & _).
  pose proof HGV as (_ & Hpl & Hbd & _).
  destruct Hpl as [[E0 _]|[_ Hin]]; [lia|].
  unfold g_n in *. split; [exact Hp0|]. split; [lia|].
  intros i Hi. pose proof (Hblk (g_p g) (g_n g) (Z.of_nat i) Hin ltac:(unfold g_n; lia)) as E.
  pose proof (Hbd (Z.of_nat i) ltac:(lia)) as D. rewrite Nat2Z.id in D.
  rewrite SEGS in E, D. rewrite <- D, <- E. reflexivity.
Qed.

(* pin_mid_contract's s: the n - 1 bytes after the flags byte cut at the first NUL, at src = p + 1 (n > 0) or the
   empty string at empty (n = 0). *)
Lemma m01_src : forall g hb L A regs mem md, FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  bytes_at rsegs (normalize rsegs mem) (g_src g) (pin_str (g_in g)).
Proof.
  intros g hb L A regs mem md HFR HP.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & HMI & _).
  unfold MI in HMI. rewrite (sl_segs B APIf ra empty FF) in HMI.
  pose proof HGV as (_ & Hpl & _).
  pose proof (b8_empty B APIf ra empty FF) as HE.
  destruct (Z.eq_dec (g_n g) 0) as [Hn0|Hn0].
  - destruct Hpl as [[_ Ep]|[Hn _]]; [|lia].
    assert (Ein : g_in g = []) by (apply length_zero_iff_nil; unfold g_n in Hn0; lia).
    unfold g_src. rewrite Hn0, Ein, Ep. cbn [pin_str pin_k pin_rest nul_idx tl firstn]. apply sl_bytes_nil. lia.
  - assert (Hn : 0 < g_n g) by (unfold g_n in *; lia).
    pose proof (bytes_at_normalize rsegs mem _ _ HMI (m01_in_bytes g hb L A regs mem md HFR HP Hn)) as HB.
    pose proof (m01_pin_k_le (g_in g)) as Hk.
    unfold g_src. replace (Z.min 1 (g_n g)) with (Z.of_nat 1) by lia.
    unfold pin_str, pin_rest.
    destruct (g_in g) as [|x l] eqn:Ein; [unfold g_n in Hn; rewrite Ein in Hn; cbn in Hn; lia|].
    cbn [tl] in *.
    exact (b8_ba_sub rsegs _ _ (x :: l) 1 (pin_k (x :: l)) HB ltac:(cbn [length]; lia)).
Qed.

(* s's bytes and the live harness block (phi, k + 1) are apart: distinct blocks of blocks L A, or s is empty. *)
Lemma m01_src_dj : forall g phi L A regs mem md, FR B APIf ra empty g (hb1 phi (g_k g + 1)) L A regs mem md ->
  Permutation (blocks L A) (hb1 phi (g_k g + 1) ++ blocks (g_L g) (g_A g)) ->
  g_src g + Z.of_nat (length (pin_str (g_in g))) <= phi \/ phi + Z.of_nat (length (pin_str (g_in g))) <= g_src g.
Proof.
  intros g phi L A regs mem md HFR HP.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & _ & _ & HM & _).
  pose proof HGV as (_ & Hpl & _).
  rewrite pin_str_length. pose proof (m01_pin_k_le (g_in g)) as Hk.
  destruct Hpl as [[Hn0 _]|[Hn Hin]].
  - assert (Ein : g_in g = []) by (apply length_zero_iff_nil; unfold g_n in Hn0; lia).
    rewrite Ein. cbn. lia.
  - pose proof (mr_blocks_disjoint B _ (aa_laws API) _ _ _ _ HM) as PD.
    apply (b1_pw_perm _ ranges_disjoint b1_rd_sym _ _ HP) in PD.
    destruct PD as [PD _]. pose proof (PD (g_p g, g_n g) Hin) as Hd. unfold ranges_disjoint in Hd. cbn [fst snd] in Hd.
    unfold g_src, g_n, g_k in *. destruct (g_in g) as [|x l]; cbn [length tl] in *; lia.
Qed.

(* The stack-protector GOT slot holds the guard's address, and the guard is a word: the allocator relation's
   statics (YL01.ax_statics), on the normalized memory. *)
Lemma m01_ssp : forall g hb L A regs mem md, FR B APIf ra empty g hb L A regs mem md ->
  bytes_at rsegs (normalize rsegs mem) PARSE_SSP_GOT (le8 (Z_to_bv 64 PARSE_SSP_GUARD)) /\
  exists can, bytes_at rsegs (normalize rsegs mem) PARSE_SSP_GUARD (le8 can).
Proof.
  intros g hb L A regs mem md HFR.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  unfold MI in HMI. rewrite SEGS in HMI.
  pose proof (b8_syms B APIf ra empty FF) as (_ & _ & _ & EG & EGG & _).
  destruct (ax_statics (b1_ax B APIf ra empty FF) L A mem md HM) as (Hgot & (gv & Hgv & Hguard) & _).
  rewrite EG, EGG, SEGS in Hgot. rewrite EG, SEGS in Hguard.
  split.
  - apply (bytes_at_normalize rsegs mem _ _ HMI).
    apply (word_mem_le8 rsegs mem PARSE_SSP_GOT PARSE_SSP_GUARD Hgot); unfold PARSE_SSP_GOT, PARSE_SSP_GUARD; lia.
  - exists (Z_to_bv 64 gv). apply (bytes_at_normalize rsegs mem _ _ HMI).
    apply (word_mem_le8 rsegs mem PARSE_SSP_GUARD gv Hguard); unfold PARSE_SSP_GUARD; lia.
Qed.

(* The live block's bytes stay present across a run that keeps the writable bytes writable: they are outside the
   image, so writable means present. *)
Lemma m01_blk_present : forall g phi n L A regs mem md m', FR B APIf ra empty g (hb1 phi n) L A regs mem md ->
  Permutation (blocks L A) (hb1 phi n ++ blocks (g_L g) (g_A g)) -> Frame.wmono rsegs mem m' ->
  forall a, phi <= a < phi + n -> exists b, mrd rsegs m' (wa a) = Some b.
Proof.
  intros g phi n L A regs mem md m' HFR HP WM a Ha.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  assert (Hin : In (phi, n) (blocks L A)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  apply blocks_In in Hin as (p & Ep & Hp).
  destruct (mr_blocks_range B _ (aa_laws API) _ _ _ _ _ _ HM Hp) as [R1 R2]. rewrite Ep in R1, R2.
  pose proof alloc_ceiling_value as Hac.
  destruct (mr_blocks B _ (aa_laws API) L A mem md p n (a - phi) HM Hp ltac:(lia)) as ([bb Hb] & _).
  rewrite Ep in Hb. replace (phi + (a - phi)) with a in Hb by lia.
  assert (Hw : wview rsegs mem (wa a) <> None) by (unfold wview, wa; rewrite Hb; discriminate).
  apply WM in Hw.
  assert (Hns : find_segment rsegs (bv_unsigned (wa a)) 1 = None).
  { destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [seg|] eqn:Ef; [|reflexivity]. exfalso.
    rewrite wa_unsigned in Ef by lia.
    apply (ax_blocks_img (b1_ax B APIf ra empty FF) L A mem md p n (a - phi) HM Hp ltac:(lia)).
    rewrite Ep. replace (phi + (a - phi)) with a by lia.
    exact (b1_find_img B a seg SEGS Ef). }
  unfold wview in Hw. destruct (m' (wa a)) as [b|] eqn:E.
  - exists b. unfold mrd. rewrite E. reflexivity.
  - rewrite Hns in Hw. exfalso. apply Hw. reflexivity.
Qed.

Lemma seg_M01 : S_M01 B APIf ra empty.
Proof.
  unfold S_M01.
  intros H1 g c (phi & L & A & regs & mem & md & -> & HFR & HP & (H10 & Hphi0 & H18 & H9 & H19 & HKS)).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  destruct (b1_hb B APIf ra empty FF g phi _ L A regs mem md HFR HP) as (STb & Hphi & Hphin).
  pose proof alloc_ceiling_value as Hac.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI0 & Hrel & HM & _).
  pose proof HFR as (HGV & _). pose proof HGV as (_ & _ & _ & _ & HSKa & _).
  pose proof (pin_str_length (g_in g)) as Hlen.
  pose proof (pin_flags_range (g_in g)) as Hfl.
  unfold SLOT_K, SLOT_STACK, fsp, SLOT_FRAME, SL_TOP in *.
  assert (Esp : bv_unsigned (YK11.getr regs 2) = g_S g - 80) by (rewrite Hsp; apply unsigned_lit; lia).
  assert (Hk0 : 0 <= g_k g) by (unfold g_k; lia).
  assert (Ek : Z.of_nat (length (pin_str (g_in g))) = g_k g) by (unfold g_k; rewrite Hlen; reflexivity).
  destruct (sl_rw_of_stk _ phi (phi + (g_k g + 1)) phi (S (length (pin_str (g_in g)))) STb ltac:(lia) ltac:(lia))
    as (junk & HJ).
  destruct (b1_slack_ok B APIf ra empty FF g phi (g_k g + 1) L A regs mem md HFR HP ltac:(lia))
    as (slack & HSL & HSLM & HSLB).
  destruct (m01_ssp g _ L A regs mem md HFR) as (HGOT & can & HGU).
  pose proof (m01_src g _ L A regs mem md HFR HP) as HSRC.
  pose proof (m01_src_dj g phi L A regs mem md HFR HP) as HDJS.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run regs (Z_to_bv 64 0x12d50) mem md _ _ Hh Hl HMI).
  - rewrite sl_mkR_of.
    eapply MID with (s := pin_str (g_in g)) (junk := junk) (slack := slack) (fl := g_fl g) (src := g_src g)
                    (phi := phi) (lo := g_S g - 65536) (can := can).
    + exact H10.
    + exact Hphi0.
    + rewrite Ek. exact H18.
    + exact H9.
    + exact H19.
    + exact Hfl.
    + exact (pin_str_no_nul (g_in g)).
    + exact HSRC.
    + exact HJ.
    + intros a Ha. apply (b1_blk_rom B APIf ra empty FF g phi (g_k g + 1) L A regs mem md HFR HP). lia.
    + rewrite Ek. replace (phi + g_k g + 1) with (phi + (g_k g + 1)) by lia. exact HSL.
    + rewrite Ek. replace (phi + g_k g + 1) with (phi + (g_k g + 1)) by lia. exact HSLM.
    + exact HDJS.
    + rewrite Esp. apply (b8_stk_sub _ _ _ _ _ _ ST); lia.
    + rewrite Esp. unfold MID_STACK. lia.
    + rewrite Esp. Z.div_mod_to_equations. lia.
    + rewrite Esp. unfold MID_OUT. apply (m01_stk_wr _ _ _ _ _ _ ST); lia.
    + intros a Ha. rewrite Esp in Ha. unfold MID_OUT in Ha. apply (@b8_seg_rom_hi rc B APIf LS SH SK ra empty FF). lia.
    + left. rewrite Ek. lia.
    + intros a Ha. apply (b8_relro_norm B APIf ra empty FF mem a Hrel HMI0).
      unfold FUZZ_CATALOGUE, CAT_BYTES in Ha. lia.
    + exact HGOT.
    + exact HGU.
    + apply mem_inv_normalize.
  - intros ms (ra' & t0' & t1' & t2' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' &
               t3' & t4' & t5' & t6' & m'' & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel' Hsame.
    destruct HQ as (ra' & t0' & t1' & t2' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' &
                    s5' & t3' & t4' & t5' & t6' & m'' & HE & MU & WM & MI' & ST').
    injection HE; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) m' m'' HR0 Hrel' Hsame MU) as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) m' m'' HR0 Hrel' Hsame WM) as WM'.
    pose proof (ro_agree_same rsegs mem m' HMI Hsame) as Hro'.
    rewrite Esp, Ek in MU'. unfold MID_STACK, MID_OUT in MU'.
    rewrite <- SEGS. apply H1. exists phi, L, A, regs', m', md.
    split; [unfold PIN_JOIN; reflexivity|].
    split.
    { apply (b1_fr_hb B APIf ra empty FF g phi (g_k g + 1) L A regs mem md regs' m' HFR HP).
      - intros a Ha Hs Hb. apply MU'. rewrite unsigned_lit by lia. cbn [outside].
        unfold SLOT_K, SLOT_STACK in Hs. split; [lia|]. split; [lia | exact I].
      - exact (m01_blk_present g phi (g_k g + 1) L A regs mem md m' HFR HP WM').
      - exact WM'.
      - exact Hro'.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity. }
    split; [exact HP|].
    split.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + destruct HKS as (K1 & K2 & K3 & K4 & K5 & K6). unfold KS.
      rewrite !(sl_getr_eqv _ _ _ Hx).
      split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact K5 | exact K6].
Qed.

End M01.
