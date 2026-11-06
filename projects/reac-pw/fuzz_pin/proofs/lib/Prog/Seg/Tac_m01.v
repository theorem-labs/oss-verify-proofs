(* Helpers of S_M01 (K12d1c -> K12de4) of reac-pw/fuzz_pin LLVMFuzzerTestOneInput (plain): the input block's bytes
   at a cut and its separation from the live harness block (libreac/fuzz_ctrl's released Prog/Seg/Tac_b4.v
   b4_in_all / b4_hb_disj, origin/ossv/recipes 25e3d17bdb50, restated for pin's GV), the string fuzz_str copies
   (pin_spec.pin_str at g_src) with its separation from the live block, the live block's bytes after a run that keeps
   them writable, and the SSP cells of reac_box_pin_parse_contract from the allocator relation's statics
   (AllocExtra.ax_statics: the GOT word at ms_got_guard holds ms_guard, and the guard word is readable). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib Require KindBGlue.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec SlotInv.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b8.
Import ListNotations.
Open Scope Z_scope.

(* fuzz_str's bytes: for a non-empty input, the first pin_k bytes after the flags byte. *)
Lemma m01_pin_sub : forall inp, (0 < length inp)%nat ->
  (1 + pin_k inp <= length inp)%nat /\ pin_str inp = firstn (pin_k inp) (skipn 1 inp).
Proof.
  intros [|b inp] H; [cbn in H; lia|].
  unfold pin_str, pin_k, pin_rest. cbn [tl skipn length].
  pose proof (nul_idx_le inp). split; [lia | reflexivity].
Qed.

(* The cells [a, a + n) of a stack region are writable. *)
Lemma m01_wr_of_stk : forall m lo hi a n, Frame.stk rsegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n ->
  wr_at rsegs m a n.
Proof.
  intros m lo hi a n (H1 & H2 & H) E1 E2 E3. split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (a + i) ltac:(lia))).
Qed.

(* A byte in no image segment that is writable is present, so it reads Some. *)
Lemma m01_wview_mrd : forall m a, 0 <= a < 2 ^ 64 -> find_segment rsegs a 1 = None ->
  wview rsegs m (wa a) <> None -> exists b, mrd rsegs m (wa a) = Some b.
Proof.
  intros m a Ha Hf W. unfold mrd. destruct (m (wa a)) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. apply W. unfold wview. rewrite E, (wa_unsigned a Ha), Hf. reflexivity.
Qed.

Section M01H.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_plain B APIf LS SH SK ra empty.
Let API := APIf rc.

(* The input block at a cut (n > 0): an entry block, so its bytes are the entry memory's (FR's entry-block clause),
   which holds the input (GV's blk_data). *)
Lemma m01_in_all : forall g hb L A regs mem md,
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> 0 < g_n g ->
  In (g_p g, g_n g) (blocks (g_L g) (g_A g)) /\ 4096 <= g_p g /\ g_p g + g_n g <= YM05.alloc_ceiling /\
  bytes_at rsegs mem (g_p g) (g_in g).
Proof.
  intros g hb L A regs mem md HFR HP Hn.
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & _ & _ & HM & _ & _ & _ & _ & _ & _ & Hblk & _).
  pose proof HGV as (_ & Hpn & Hdat & _).
  destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (b1_blk B APIf ra empty FF L A mem md (g_p g) (g_n g) HM
             (Permutation_in _ (Permutation_sym HP) (in_or_app _ _ _ (or_intror Hin)))) as (_ & H1 & H2).
  pose proof alloc_ceiling_value as (Hac & _).
  split; [exact Hin|]. split; [exact H1|]. split; [exact H2|].
  split; [lia|]. split; [unfold g_n in *; lia|].
  intros k Hk.
  assert (Hk' : 0 <= Z.of_nat k < g_n g) by (unfold g_n; lia).
  pose proof (Hblk (g_p g) (g_n g) (Z.of_nat k) Hin Hk') as E1.
  assert (Hk'' : 0 <= Z.of_nat k < Z.of_nat (length (g_in g))) by lia.
  pose proof (Hdat (Z.of_nat k) Hk'') as E2.
  rewrite E2, Nat2Z.id, SEGS in E1. exact E1.
Qed.

(* The live harness block and an entry block are disjoint (the allocator's blocks are pairwise disjoint). *)
Lemma m01_hb_disj : forall g phi n L A regs mem md a k,
  FR B APIf ra empty g (hb1 phi n) L A regs mem md ->
  Permutation (blocks L A) (hb1 phi n ++ blocks (g_L g) (g_A g)) ->
  In (a, k) (blocks (g_L g) (g_A g)) -> phi + n <= a \/ a + k <= phi.
Proof.
  intros g phi n L A regs mem md a k HFR HP Hin.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  pose proof (mr_blocks_disjoint B _ (aa_laws API) _ _ _ _ HM) as PD.
  apply (b1_pw_perm _ ranges_disjoint b1_rd_sym _ _ HP) in PD.
  destruct PD as [PD _]. pose proof (PD (a, k) Hin) as Hd. unfold ranges_disjoint in Hd. cbn [fst snd] in Hd.
  exact Hd.
Qed.

(* fuzz_str's source at K12d1c: the pin_k bytes at g_src are pin_str of the input (none when n = 0), and they lie
   apart from the live block (phi, k + 1). *)
Lemma m01_src : forall g phi L A regs mem md,
  FR B APIf ra empty g (hb1 phi (g_k g + 1)) L A regs mem md ->
  Permutation (blocks L A) (hb1 phi (g_k g + 1) ++ blocks (g_L g) (g_A g)) ->
  bytes_at rsegs mem (g_src g) (pin_str (g_in g)) /\
  (g_src g + Z.of_nat (length (pin_str (g_in g))) <= phi \/ phi + Z.of_nat (length (pin_str (g_in g))) <= g_src g).
Proof.
  intros g phi L A regs mem md HFR HP.
  pose proof HFR as (HGV & _).
  pose proof HGV as (_ & Hpn & _).
  rewrite pin_str_length.
  destruct Hpn as [(Hn0 & Hpe) | (Hn0 & Hin)].
  - assert (E : g_in g = []) by (apply length_zero_iff_nil; unfold g_n in Hn0; lia).
    assert (Hs : 0 <= g_src g <= 2 ^ 64).
    { unfold g_src. pose proof (b8_empty B APIf ra empty FF). rewrite Hn0, Hpe. lia. }
    rewrite E. change (pin_str []) with (@nil byte). change (pin_k []) with 0%nat.
    split; [exact (sl_bytes_nil mem (g_src g) Hs) | lia].
  - destruct (m01_in_all g _ L A regs mem md HFR HP Hn0) as (_ & _ & _ & HB).
    assert (Hlen : (0 < length (g_in g))%nat) by (unfold g_n in Hn0; lia).
    destruct (m01_pin_sub (g_in g) Hlen) as (Hk & Es).
    pose proof (b8_ba_sub rsegs mem (g_p g) (g_in g) 1 (pin_k (g_in g)) HB Hk) as HS.
    rewrite <- Es in HS.
    pose proof (m01_hb_disj g phi (g_k g + 1) L A regs mem md (g_p g) (g_n g) HFR HP Hin) as HD.
    assert (Hs : g_src g = g_p g + Z.of_nat 1) by (unfold g_src; lia).
    rewrite Hs. split; [exact HS|].
    unfold g_k, g_n in *. lia.
Qed.

(* No image segment holds a byte of a live block. *)
Lemma m01_blk_noseg : forall L A mem md phi n a, aa_MR API L A mem md -> In (phi, n) (blocks L A) ->
  phi <= a < phi + n -> find_segment rsegs a 1 = None.
Proof.
  intros L A mem md phi n a HM Hin Ha.
  apply blocks_In in Hin as (p & Ep & Hp).
  destruct (find_segment rsegs a 1) as [seg|] eqn:Ef; [exfalso|reflexivity].
  apply (ax_blocks_img (b1_ax B APIf ra empty FF) L A mem md p n (a - phi) HM Hp ltac:(lia)).
  rewrite Ep. replace (phi + (a - phi)) with a by lia.
  exact (b1_find_img B a seg (sl_segs B APIf ra empty FF) Ef).
Qed.

(* The live block's bytes are still present after a run that keeps writability (wmono). *)
Lemma m01_blk_present : forall g phi n L A regs mem md m',
  FR B APIf ra empty g (hb1 phi n) L A regs mem md ->
  Permutation (blocks L A) (hb1 phi n ++ blocks (g_L g) (g_A g)) ->
  Frame.wmono rsegs mem m' ->
  forall a, phi <= a < phi + n -> exists b, mrd rsegs m' (wa a) = Some b.
Proof.
  intros g phi n L A regs mem md m' HFR HP WM a Ha.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  assert (Hin : In (phi, n) (blocks L A)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
  pose proof (m01_blk_noseg L A mem md phi n a HM Hin Ha) as Hf.
  pose proof Hin as Hin'. apply blocks_In in Hin' as (p & Ep & Hp).
  destruct (mr_blocks_range B _ (aa_laws API) _ _ _ _ _ _ HM Hp) as [R1 R2]. rewrite Ep in R1, R2.
  pose proof alloc_ceiling_value as (Hac & _).
  destruct (mr_blocks B _ (aa_laws API) L A mem md p n (a - phi) HM Hp ltac:(lia)) as ([b Hb] & _).
  rewrite Ep in Hb. replace (phi + (a - phi)) with a in Hb by lia.
  apply (m01_wview_mrd m' a ltac:(lia) Hf).
  apply WM. unfold wview, wa. rewrite Hb. cbv beta iota. discriminate.
Qed.

(* reac_box_pin_parse's SSP cells: the GOT word at 0x1d478 holds the guard's address 0x4ea60, and the guard word is
   readable (the allocator relation's statics, with frame_facts_plain's ms_got_guard / ms_guard). *)
Lemma m01_ssp : forall L A mem md, aa_MR API L A mem md ->
  bytes_at rsegs mem 0x1d478 (le8 (Z_to_bv 64 0x4ea60)) /\ exists can, bytes_at rsegs mem 0x4ea60 (le8 can).
Proof.
  intros L A mem md HM.
  destruct (ax_statics (b1_ax B APIf ra empty FF) L A mem md HM) as (Hg & (gv & Hgv & Hw) & _).
  rewrite (sl_segs B APIf ra empty FF), (ff_got_guard B APIf ra empty FF), (ff_guard B APIf ra empty FF) in Hg.
  rewrite (sl_segs B APIf ra empty FF), (ff_guard B APIf ra empty FF) in Hw.
  split.
  - apply KindBGlue.word_mem_le8; [exact Hg | lia | lia | lia].
  - exists (Z_to_bv 64 gv). apply KindBGlue.word_mem_le8; [exact Hw | lia | lia | lia].
Qed.

End M01H.
