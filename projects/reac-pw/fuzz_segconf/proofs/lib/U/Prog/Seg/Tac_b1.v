(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 669 of its 757 lines of code are new or changed and 486 lines of the source are left out. *)
(* Helpers of the segments of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan): byte transport across runs, the
   allocator facts of frame_facts_ubsan, malloc and calloc as Kind B steps from any list hb of live harness blocks
   (b1_malloc_call, b1_calloc_call), FR across a run that writes the stack window, a list Wb of blocks of hb and
   longl's written bytes (b1_fr_hb), and a live block's cells, separation from the other blocks, slack and absence
   from the image's bytes and reserved pages (b1_hb, b1_sep, b1_slack_ok, b1_blk_rom, b1_blk_noimg,
   b1_blk_noimg_segs, b1_blk_present, b1_in_all).
   Taken from reac-pw/fuzz_role's Prog/Seg/Tac_b1.v (commit 52bb2f1ed35d), itself
   reac-pw/fuzz_pin's and libreac/fuzz_ctrl's released Prog/Seg/Tac_b1.v (origin/ossv/recipes 25e3d17bdb50)
   adapted, with segconf's numbers (frame 240, saved registers [S - 104, S), malloc at 0x17518, calloc at 0x172a0,
   the sink cells 0x53841, 0x53c68 .. 0x53c6c, 0x53c70 .. 0x53c78, the request bound 2^26 of SlotFR.resb_room).
   From role: b1_FR_malloc / b1_malloc_call take FR with any hb (of at most 16 blocks and 2^24 bytes) to FR with
   (res, n) :: hb, and give res mod 16 = 0 and the bytes of the blocks of hb unchanged (malloc_ret's blocks_kept),
   the clause libreac/fuzz_scene's released ss_malloc_step (Prog/Seg/STac.v:710-722) states. New for segconf:
   - b1_FR_alloc_k: b1_FR_malloc for any callee stack K <= CALLOC_STACK (b1_FR_malloc is its K = ALLOC_STACK case);
   - b1_calloc_call: calloc(m, n) through CallocBigC.calloc_contract_big at CALLOC_PC (the frame's
     ms_calloc is None), call_pre_k CALLOC_STACK, and the m * n zero bytes of the new block in the continuation;
   - b1_fr_hb over a written list Wb of blocks of hb plus longl's [LONGL, LONGL + LONGL_W) (role's took one block):
     every written block's presence comes from wmono (fuzz_pin's Tac_m01.m01_blk_present), the entry blocks are
     apart from each written block (b1_sep's argument), and longl is in the image, unowned (frame_allocator's G
     clause) and in no live block.
   b1_sep, b1_in_all and b1_blk_present are fuzz_pin's Tac_m01.m01_hb_disj, m01_in_all and m01_blk_present for any
   hb. b1_slack_ok is libreac/fuzz_identity's slack_ok (Prog/Seg/Tac_si.v) restated for a live block on the
   normalized memory. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import SlotFR.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require CallocBigC.
Import ListNotations.
Open Scope Z_scope.

(* Bytes a segment does not touch: from the cut's memory through the normalized run to the next cut's memory. *)
Lemma b1_keep : forall W mem m0 m' a bs, ro_agree rsegs mem -> Frame.munch W (normalize rsegs mem) m0 ->
  mem_rel rsegs m' m0 -> Frame.disjoint_from W a (Z.of_nat (length bs)) ->
  bytes_at rsegs mem a bs -> bytes_at rsegs m' a bs.
Proof.
  intros W mem m0 m' a bs Hro MU Hrel HD H.
  apply (proj2 (bytes_at_rel rsegs m' m0 a bs Hrel)).
  exact (bytes_at_transport rsegs W (normalize rsegs mem) m0 a bs (bytes_at_normalize rsegs mem a bs Hro H) MU HD).
Qed.

(* The bytes the run itself leaves at a: from the run's final memory to the next cut's memory. *)
Lemma b1_out : forall m0 m' a bs, mem_rel rsegs m' m0 -> bytes_at rsegs m0 a bs -> bytes_at rsegs m' a bs.
Proof. intros m0 m' a bs Hrel H. exact (proj2 (bytes_at_rel rsegs m' m0 a bs Hrel) H). Qed.

(* beqz / bnez on a non-zero value. *)
Lemma b1_beq0 : forall z, 0 < z < 2 ^ 64 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof. intros z Hz. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

(* An 8-byte load from a q64 cell. *)
Lemma b1_ld8 : forall m a v, bytes_at rsegs m a (le8 v) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 v).
Proof.
  intros m a v H. replace (wa a) with (wa (a + Z.of_nat 0)) by (f_equal; lia).
  rewrite (bytes_at_ov_read rsegs m a (le8 v) 0 8 H) by (rewrite length_le8; lia).
  reflexivity.
Qed.

Lemma b1_byte_rng : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R. Qed.

Lemma b1_dj_sub : forall W a n a' n', Frame.disjoint_from W a n -> a <= a' -> a' + n' <= a + n ->
  Frame.disjoint_from W a' n'.
Proof.
  induction W as [|[lo hi] W IH]; cbn [disjoint_from]; intros a n a' n' H H1 H2; [exact I|].
  destruct H as [H H']. split; [lia | exact (IH a n a' n' H' H1 H2)].
Qed.

Lemma b1_ba_mbyte : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H1 & H2 & H) Hk. split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite <- (H i Hi). pose proof (Hk (Z.of_nat i) ltac:(lia)) as E. unfold mbyte in E.
  unfold Mem.mrd, wa. exact E.
Qed.

Lemma b1_find_img : forall B x seg, ms_segs B = rsegs -> find_segment rsegs x 1 = Some seg -> in_img B x.
Proof.
  intros B x seg HS E. destruct (sl_find_segment_in rsegs x 1 seg E) as (Hin & H1 & H2).
  destruct (sl_rsegs_seg seg Hin) as (R1 & R2 & R3).
  split; [rewrite HS; intros Hn; rewrite Hn in Hin; destruct Hin|].
  exists (segment_reservation seg). split.
  - rewrite HS. unfold segments_reserved. apply in_map_iff. exists seg. split; [reflexivity | exact Hin].
  - lia.
Qed.

Lemma b1_pw_perm : forall (T : Type) (R : T -> T -> Prop), (forall a b, R a b -> R b a) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
  intros T R Hs l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; intros H.
  - exact H.
  - destruct H as [H1 H2]. split; [|exact (IH H2)].
    intros y Hy. apply H1. apply (Permutation_in y (Permutation_sym HP) Hy).
  - destruct H as [Hy [Hx Hl]]. split.
    + intros z [<-|Hz]; [apply Hs, Hy; left; reflexivity | exact (Hx z Hz)].
    + split; [intros z Hz; apply Hy; right; exact Hz | exact Hl].
  - exact (IH2 (IH1 H)).
Qed.

Lemma b1_rd_sym : forall a b, ranges_disjoint a b -> ranges_disjoint b a.
Proof. unfold ranges_disjoint. intros a b H. lia. Qed.

(* A block x of hb moved to the front of hb ++ E: what remains holds E and the other blocks of hb. *)
Lemma b1_perm_front : forall (hb1 hb2 E l : list (Z * Z)) x, Permutation l ((hb1 ++ x :: hb2) ++ E) ->
  Permutation l (x :: hb1 ++ hb2 ++ E).
Proof.
  intros hb1 hb2 E l x HP. eapply Permutation_trans; [exact HP|].
  rewrite <- app_assoc. cbn [app]. apply Permutation_sym, Permutation_middle.
Qed.

Lemma b1_in_hb : forall (hb E l : list (Z * Z)) x, Permutation l (hb ++ E) -> In x hb -> In x l.
Proof.
  intros hb E l x HP Hx. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hx.
Qed.

Lemma b1_in_E : forall (hb E l : list (Z * Z)) x, Permutation l (hb ++ E) -> In x E -> In x l.
Proof.
  intros hb E l x HP Hx. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. exact Hx.
Qed.

(* A byte in no image segment that is writable is present, so it reads Some (fuzz_pin's m01_wview_mrd). *)
Lemma b1_wview_mrd : forall m a, 0 <= a < 2 ^ 64 -> find_segment rsegs a 1 = None ->
  wview rsegs m (wa a) <> None -> exists b, mrd rsegs m (wa a) = Some b.
Proof.
  intros m a Ha Hf W. unfold mrd. destruct (m (wa a)) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. apply W. unfold wview. rewrite E, (wa_unsigned a Ha), Hf. reflexivity.
Qed.

(* A byte outside every image segment that reads Some is present in the memory itself. *)
Lemma b1_present : forall B (m : word -> option byte) x b, ms_segs B = rsegs -> ~ in_img B x -> 0 <= x < 2 ^ 64 ->
  mrd rsegs m (wa x) = Some b -> exists b', m (Z_to_bv 64 x) = Some b'.
Proof.
  intros B m x b HS Hn Hx H. unfold mrd in H. destruct (m (wa x)) as [b'|] eqn:E; [exists b'; exact E|].
  exfalso. destruct (find_segment rsegs (bv_unsigned (wa x)) 1) as [seg|] eqn:Ef.
  - rewrite wa_unsigned in Ef by lia. exact (Hn (b1_find_img B x seg HS Ef)).
  - rewrite (seg_rom_unmapped rsegs (wa x) Ef) in H. discriminate.
Qed.

(* The sink cells of sink_none (0x53841, 0x53c68, 0x53c70) lie in the image: one reserved segment covers
   [__libc, ofl_head + 8) = [0x53840, 0x53c78). *)
Lemma b1_resv_ok : existsb (fun s : word * word => (bv_unsigned (fst s) <=? 0x53840) &&
    (0x53c78 <=? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma b1_img_sink : forall B x, ms_segs B = rsegs -> 0x53840 <= x < 0x53c78 -> in_img B x.
Proof.
  intros B x HS Hx. pose proof b1_resv_ok as H. apply existsb_exists in H as (s & Hs & Hc).
  apply andb_true_iff in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [rewrite HS; intros Hn; rewrite Hn in Hs; cbn in Hs; destruct Hs|].
  exists s. rewrite HS. split; [exact Hs | lia].
Qed.

(* The bytes of mem at a .. a + k - 1 (0 for an absent byte): the slack of b1_slack_ok. *)
Fixpoint b1_rd_list (mem : word -> option byte) (a : Z) (k : nat) : list byte :=
  match k with
  | O => []
  | S k' => (match mem (Z_to_bv 64 a) with Some b => b | None => Z_to_bv 8 0 end) :: b1_rd_list mem (a + 1) k'
  end.

Lemma b1_rd_list_len : forall mem k a, length (b1_rd_list mem a k) = k.
Proof. intros mem k. induction k as [|k IH]; intros a; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma b1_rd_list_nth : forall mem k a j, (j < k)%nat ->
  nth_error (b1_rd_list mem a k) j =
  Some (match mem (Z_to_bv 64 (a + Z.of_nat j)) with Some b => b | None => Z_to_bv 8 0 end).
Proof.
  intros mem k. induction k as [|k IH]; intros a j Hj; [lia|].
  destruct j as [|j]; cbn [b1_rd_list nth_error].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH by lia. replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (S j)) by lia. reflexivity.
Qed.

(* The slack arithmetic: e = 8 * ceil(x / 8) is x + ((- x) mod 8). *)
Lemma b1_slack_arith : forall x, 0 <= x ->
  x <= 8 * ((x + 7) / 8) /\ (- x) mod 8 <= 8 * ((x + 7) / 8) - x /\ 8 * ((x + 7) / 8) - x < 8.
Proof. intros x Hx. Z.div_mod_to_equations. lia. Qed.

Lemma b1_slack_ceil : forall x c, 0 <= x <= c -> c mod 4096 = 0 -> 8 * ((x + 7) / 8) <= c.
Proof. intros x c Hx Hc. Z.div_mod_to_equations. lia. Qed.

Section B1.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_ubsan B APIf LS SH SK ra empty.
Let API := APIf rc.

Lemma b1_alloc : frame_allocator B API.
Proof. exact (ff_alloc B APIf ra empty FF). Qed.

Lemma b1_ax : AllocExtra B (aa_MR API).
Proof.
  destruct b1_alloc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AX & _). exact AX.
Qed.

(* A live block: its bytes are present and not read-only, so the normalized memory holds them. *)
Lemma b1_blk : forall L A mem md a n, aa_MR API L A mem md -> In (a, n) (blocks L A) ->
  stk rsegs (normalize rsegs mem) a (a + n) /\ 4096 <= a /\ a + n <= YM05.alloc_ceiling.
Proof.
  intros L A mem md a n HM Hin.
  apply blocks_In in Hin as (p & <- & Hp).
  destruct (mr_blocks_range B _ (aa_laws API) _ _ _ _ _ _ HM Hp) as [R1 R2].
  pose proof alloc_ceiling_value as Hac.
  split; [|split; lia].
  split; [lia|]. split; [lia|].
  intros x Hx.
  destruct (mr_blocks B _ (aa_laws API) L A mem md p n (x - ptr_addr L p) HM Hp ltac:(lia)) as ([b Hb] & _).
  replace (ptr_addr L p + (x - ptr_addr L p)) with x in Hb by lia.
  assert (Hro : Mem.ro_addr rsegs (wa x) = false).
  { destruct (Mem.ro_addr rsegs (wa x)) eqn:E; [|reflexivity]. exfalso.
    unfold Mem.ro_addr in E. destruct (find_segment rsegs (bv_unsigned (wa x)) 1) as [seg|] eqn:Ef; [|discriminate].
    rewrite wa_unsigned in Ef by lia.
    apply (ax_blocks_img b1_ax L A mem md p n (x - ptr_addr L p) HM Hp ltac:(lia)).
    replace (ptr_addr L p + (x - ptr_addr L p)) with x by lia.
    exact (b1_find_img B x seg (sl_segs B APIf ra empty FF) Ef). }
  assert (E : normalize rsegs mem (wa x) = Some b) by (unfold normalize; rewrite Hro; exact Hb).
  split.
  - exact (YL01.present_writable rsegs _ x (ex_intro _ b E)).
  - exists b. unfold Mem.mrd. rewrite E. reflexivity.
Qed.

Lemma b1_hb : forall g hb phi n L A regs mem md, FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (phi, n) hb ->
  stk rsegs (normalize rsegs mem) phi (phi + n) /\ 4096 <= phi /\ phi + n <= YM05.alloc_ceiling.
Proof.
  intros g hb phi n L A regs mem md HFR HP Hb. pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  exact (b1_blk L A mem md phi n HM (b1_in_hb _ _ _ _ HP Hb)).
Qed.

(* A live block's bytes are outside the image. *)
Lemma b1_blk_rom : forall g hb phi n L A regs mem md, FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (phi, n) hb ->
  forall a, phi <= a < phi + n -> seg_rom rsegs (wa a) = None.
Proof.
  intros g hb phi n L A regs mem md HFR HP Hb a Ha.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  pose proof (b1_in_hb _ _ _ _ HP Hb) as Hin.
  apply blocks_In in Hin as (p & Ep & Hp).
  destruct (mr_blocks_range B _ (aa_laws API) _ _ _ _ _ _ HM Hp) as [R1 R2]. rewrite Ep in R1, R2.
  pose proof alloc_ceiling_value as Hac.
  destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [seg|] eqn:Ef.
  - exfalso. rewrite wa_unsigned in Ef by lia.
    apply (ax_blocks_img b1_ax L A mem md p n (a - phi) HM Hp ltac:(lia)).
    rewrite Ep. replace (phi + (a - phi)) with a by lia.
    exact (b1_find_img B a seg (sl_segs B APIf ra empty FF) Ef).
  - exact (seg_rom_unmapped rsegs (wa a) Ef).
Qed.

(* A live block's bytes lie in no reserved page of the image: in_img B is the page-rounded reservation of every
   segment (Run.segment_reservation), so this is the whole-page form printf's pf_img_free needs. This is all the
   slot gives about where a block is: the abstract allocator laws place a block at 4096 or above and outside the
   reserved pages (mr_blocks_range, ax_blocks_img), not above the image's last page. *)
Lemma b1_blk_noimg : forall g hb phi n L A regs mem md, FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (phi, n) hb ->
  forall a, phi <= a < phi + n -> ~ in_img B a.
Proof.
  intros g hb phi n L A regs mem md HFR HP Hb a Ha Hi.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  pose proof (b1_in_hb _ _ _ _ HP Hb) as Hin.
  apply blocks_In in Hin as (p & Ep & Hp).
  apply (ax_blocks_img b1_ax L A mem md p n (a - phi) HM Hp ltac:(lia)).
  rewrite Ep. replace (phi + (a - phi)) with a by lia. exact Hi.
Qed.

(* b1_blk_noimg in the form of seg_spec.blk_noimg rsegs phi n (commit
   c7b9518dac31: the text of printf_facts_c.pf_img_free with segs := rsegs); its conclusion is that definition's body,
   so `exact (b1_blk_noimg_segs ..)` closes `blk_noimg rsegs phi n` by conversion. *)
Lemma b1_blk_noimg_segs : forall g hb phi n L A regs mem md, FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (phi, n) hb ->
  forall i, 0 <= i < n -> forall s, In s (segments_reserved rsegs) ->
    ~ (bv_unsigned (fst s) <= phi + i < bv_unsigned (fst s) + bv_unsigned (snd s)).
Proof.
  intros g hb phi n L A regs mem md HFR HP Hb i Hi s Hs Hr.
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  apply (b1_blk_noimg g hb phi n L A regs mem md HFR HP Hb (phi + i) ltac:(lia)).
  split.
  - rewrite SEGS. intros E. rewrite E in Hs. cbn in Hs. exact Hs.
  - exists s. rewrite SEGS. split; [exact Hs | exact Hr].
Qed.

(* A live block's slack: the bytes after it up to the next 8-byte boundary, read on the normalized memory
   (libreac/fuzz_identity's slack_ok, from the frame's block_slack_present). *)
Lemma b1_slack_ok : forall g hb phi n L A regs mem md, FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> In (phi, n) hb -> 0 <= n ->
  exists slack, bytes_at rsegs (normalize rsegs mem) (phi + n) slack /\
    (- (phi + n)) mod 8 <= Z.of_nat (length slack) /\
    phi + n + Z.of_nat (length slack) <= YM05.alloc_ceiling.
Proof.
  intros g hb phi n L A regs mem md HFR HP Hb Hn0.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite (sl_segs B APIf ra empty FF) in HMI.
  pose proof (b1_in_hb _ _ _ _ HP Hb) as Hin.
  pose proof Hin as Hin'. apply blocks_In in Hin' as (p & Ep & Hp).
  destruct (mr_blocks_range B _ (aa_laws API) _ _ _ _ _ _ HM Hp) as [R1 R2]. rewrite Ep in R1, R2.
  pose proof alloc_ceiling_value as (Hac1 & Hac2).
  destruct b1_alloc as (_ & _ & _ & _ & _ & HSL & _).
  destruct (b1_slack_arith (phi + n) ltac:(lia)) as (He1 & He3 & He4).
  assert (He2 : 8 * ((phi + n + 7) / 8) <= YM05.alloc_ceiling) by (apply b1_slack_ceil; [lia | exact Hac2]).
  assert (PR : forall a, phi + n <= a < 8 * ((phi + n + 7) / 8) -> present mem a)
    by (intros a Ha; exact (HSL L A mem md phi n a HM Hin Ha)).
  exists (b1_rd_list mem (phi + n) (Z.to_nat (8 * ((phi + n + 7) / 8) - (phi + n)))).
  rewrite b1_rd_list_len.
  split; [|split; lia].
  apply (bytes_at_normalize rsegs mem _ _ HMI).
  split; [lia|]. split; [rewrite b1_rd_list_len; lia|].
  intros i Hi. rewrite b1_rd_list_len in Hi. rewrite b1_rd_list_nth by exact Hi.
  destruct (PR (phi + n + Z.of_nat i) ltac:(lia)) as [b Hb'].
  unfold Mem.mrd, Mem.wa. rewrite Hb'. reflexivity.
Qed.

(* A block x of hb and every other block (the rest of hb and the entry blocks) are disjoint: the allocator's
   blocks are pairwise disjoint (fuzz_pin's m01_hb_disj, for x anywhere in hb). *)
Lemma b1_sep : forall g hb1 x hb2 L A regs mem md y,
  FR B APIf ra empty g (hb1 ++ x :: hb2) L A regs mem md ->
  Permutation (blocks L A) ((hb1 ++ x :: hb2) ++ blocks (g_L g) (g_A g)) ->
  In y (hb1 ++ hb2 ++ blocks (g_L g) (g_A g)) -> fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof.
  intros g hb1 x hb2 L A regs mem md y HFR HP Hy.
  pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  pose proof (mr_blocks_disjoint B _ (aa_laws API) _ _ _ _ HM) as PD.
  apply (b1_pw_perm _ ranges_disjoint b1_rd_sym _ _ (b1_perm_front hb1 hb2 _ _ x HP)) in PD.
  destruct PD as [PD _]. pose proof (PD y Hy) as Hd. unfold ranges_disjoint in Hd. exact Hd.
Qed.

(* No image segment holds a byte of a live block. *)
Lemma b1_blk_noseg : forall L A mem md phi n a, aa_MR API L A mem md -> In (phi, n) (blocks L A) ->
  phi <= a < phi + n -> find_segment rsegs a 1 = None.
Proof.
  intros L A mem md phi n a HM Hin Ha.
  apply blocks_In in Hin as (p & Ep & Hp).
  destruct (find_segment rsegs a 1) as [seg|] eqn:Ef; [exfalso|reflexivity].
  apply (ax_blocks_img b1_ax L A mem md p n (a - phi) HM Hp ltac:(lia)).
  rewrite Ep. replace (phi + (a - phi)) with a by lia.
  exact (b1_find_img B a seg (sl_segs B APIf ra empty FF) Ef).
Qed.

(* A live block's bytes are still present after a run that keeps writability (wmono). *)
Lemma b1_blk_present : forall L A mem md m' phi n, aa_MR API L A mem md -> In (phi, n) (blocks L A) ->
  Frame.wmono rsegs mem m' -> forall a, phi <= a < phi + n -> exists b, mrd rsegs m' (wa a) = Some b.
Proof.
  intros L A mem md m' phi n HM Hin WM a Ha.
  pose proof (b1_blk_noseg L A mem md phi n a HM Hin Ha) as Hf.
  pose proof Hin as Hin'. apply blocks_In in Hin' as (p & Ep & Hp).
  destruct (mr_blocks_range B _ (aa_laws API) _ _ _ _ _ _ HM Hp) as [R1 R2]. rewrite Ep in R1, R2.
  pose proof alloc_ceiling_value as (Hac & _).
  destruct (mr_blocks B _ (aa_laws API) L A mem md p n (a - phi) HM Hp ltac:(lia)) as ([b Hb] & _).
  rewrite Ep in Hb. replace (phi + (a - phi)) with a in Hb by lia.
  apply (b1_wview_mrd m' a ltac:(lia) Hf).
  apply WM. unfold wview, wa. rewrite Hb. cbv beta iota. discriminate.
Qed.

(* The input block at a cut (n > 0): an entry block, so its bytes are the entry memory's (FR's entry-block clause),
   which holds the input (GV's blk_data); fuzz_pin's m01_in_all. *)
Lemma b1_in_all : forall g hb L A regs mem md,
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
  destruct (b1_blk L A mem md (g_p g) (g_n g) HM (b1_in_E _ _ _ _ HP Hin)) as (_ & H1 & H2).
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

Lemma b1_relro_full : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Proof. exact (ff_relro B APIf ra empty FF). Qed.

Lemma b1_relro_img : forall a, in_globals frame_RELRO a -> in_img B a.
Proof. intros a Ha. exact (proj1 (b1_relro_full a Ha)). Qed.

Lemma b1_syms : ms_ctx B = 0x538b8 /\ ms_lock B = 0x538b0 /\ ms_libc B = 0x53840 /\ ms_guard B = 0x53820 /\
  ms_got_guard B = 0x221b0 /\ ms_size_classes B = 0x11350 /\ ms_small_cnt B = 0x113b0 /\ ms_med_cnt B = 0x113cb /\
  ms_debruijn B = 0x11330 /\ ms_vmlock B = None /\ @sk_ofl_head SH = 0x53c70 /\ @sk_ofl_lock SK = 0x53c68 /\
  @sk_threaded SK = 0x53840 + 1.
Proof.
  pose proof (ff_sink B APIf ra empty FF) as (S1 & S2 & S3).
  split; [exact (ff_ctx B APIf ra empty FF)|]. split; [exact (ff_lock B APIf ra empty FF)|].
  split; [exact (ff_libc B APIf ra empty FF)|]. split; [exact (ff_guard B APIf ra empty FF)|].
  split; [exact (ff_got_guard B APIf ra empty FF)|]. split; [exact (ff_size_classes B APIf ra empty FF)|].
  split; [exact (ff_small_cnt B APIf ra empty FF)|]. split; [exact (ff_med_cnt B APIf ra empty FF)|].
  split; [exact (ff_debruijn B APIf ra empty FF)|]. split; [exact (ff_vmlock B APIf ra empty FF)|].
  exact (conj S1 (conj S2 S3)).
Qed.

Lemma b1_malloc_addr : ms_malloc B = 0x17518.
Proof. exact (ff_malloc B APIf ra empty FF). Qed.

(* The sink cells: in the image and outside the allocator's static, ctx and errno bytes. *)
Lemma b1_sink_addr : forall a, (0x53841 <= a < 0x53842 \/ 0x53c68 <= a < 0x53c78) ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Proof.
  intros a Ha. pose proof b1_syms as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _).
  pose proof (sl_errno_val B APIf ra empty FF) as Ev.
  split; [apply (b1_img_sink B a (sl_segs B APIf ra empty FF)); lia|].
  rewrite Ev. unfold static_owned, vml_lo, vml_len. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10.
  rewrite (ff_debruijn_len B APIf ra empty FF). cbv iota. unfold CTX_SIZE. lia.
Qed.

Lemma b1_sink_frame : forall mem mem' md md',
  (forall a, (0x53841 <= a < 0x53842 \/ 0x53c68 <= a < 0x53c78) -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
  m_fds md' = m_fds md -> sink_none B mem md -> sink_none B mem' md'.
Proof.
  intros mem mem' md md' HK Hfd ((V1 & V2) & V3 & V4).
  pose proof b1_syms as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & S3).
  split; [split|split].
  - intros k Hk. rewrite <- (V1 k Hk). apply HK. rewrite S3. lia.
  - intros k Hk. rewrite <- (V2 k Hk). apply HK. rewrite S2. lia.
  - intros k Hk. rewrite <- (V3 k Hk). apply HK. rewrite S1. lia.
  - rewrite Hfd. exact V4.
Qed.

Lemma b1_G_unowned : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Proof.
  destruct b1_alloc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HG & _). exact HG.
Qed.

(* The callee's pre-state at a call from a cut: call_pre_k for any callee stack K <= CALLOC_STACK (the window
   [sp - K, sp) lies in [S - 65536, S - 240)). *)
Lemma b1_call_pre_k : forall g hb L A regs mem md regs_c K, 0 <= K <= CALLOC_STACK ->
  FR B APIf ra empty g hb L A regs mem md -> YK11.getr regs_c 2 = YK11.getr regs 2 ->
  YK11.getr regs_c 4 = YK11.getr regs 4 -> YK0s.ret_ok (YK11.getr regs_c 1) ->
  call_pre_k B (aa_MR API) K L A regs_c mem md.
Proof.
  intros g hb L A regs mem md regs_c K HK HF E2 E4 Hra.
  pose proof HF as (HGV & Hsp & _ & Htp & _ & _ & _ & _ & HMR & HWF & HBD & HIN & _ & _ & _ & _ & HER & _ & _ & HSW).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _ & _ & HTP0 & _).
  pose proof alloc_ceiling_value as HAC. unfold SLOT_K, SLOT_STACK, CALLOC_STACK, ALLOC_STACK in *.
  assert (HSP : spZ regs_c = g_S g - 240).
  { unfold spZ. rewrite E2, Hsp. unfold fsp, SLOT_FRAME. apply MState.unsigned_lit. lia. }
  unfold call_pre_k. rewrite HSP.
  split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact Hra|].
  split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; apply HSW; lia|].
  split; [rewrite E4, Htp; exact HTP0|].
  split; [exact HER|].
  intros H. rewrite HIN in H. discriminate.
Qed.

Lemma b1_call_pre : forall g hb L A regs mem md regs_c,
  FR B APIf ra empty g hb L A regs mem md -> YK11.getr regs_c 2 = YK11.getr regs 2 ->
  YK11.getr regs_c 4 = YK11.getr regs 4 -> YK0s.ret_ok (YK11.getr regs_c 1) -> call_pre B (aa_MR API) L A regs_c mem md.
Proof.
  intros g hb L A regs mem md regs_c HF E2 E4 Hra. apply call_pre_k_alloc.
  apply (b1_call_pre_k g hb L A regs mem md regs_c ALLOC_STACK); [unfold CALLOC_STACK, ALLOC_STACK; lia | exact HF |
    exact E2 | exact E4 | exact Hra].
Qed.

(* FR after an allocation of n bytes whose callee stack is K (malloc: ALLOC_STACK; calloc: CALLOC_STACK) from a cut
   with the live harness blocks hb: the new block (res, n) joins hb at its head, the frame bytes [sp, S) and the
   bytes of the blocks of hb are unchanged. *)
Lemma b1_FR_alloc_k : forall K g hb L A regs mem md regs_c n L' A' regs' mem' md' res b1 b2,
  0 <= K <= CALLOC_STACK ->
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  YK11.getr regs_c 2 = YK11.getr regs 2 -> YK11.getr regs_c 3 = YK11.getr regs 3 ->
  YK11.getr regs_c 4 = YK11.getr regs 4 ->
  call_post_k B (aa_MR API) K L A regs_c mem md (fun _ => False) L' A' regs' mem' md' ->
  blocks L' A' = b1 ++ (res, n) :: b2 -> blocks L A = b1 ++ b2 ->
  blocks_kept B L A mem mem' (fun _ => False) ->
  ro_agree (ms_segs B) mem' -> st_init_done A' = true ->
  res_ok_slots A' (sb_malloc (sb_hb (g_b g) hb) n) ->
  FR B APIf ra empty g ((res, n) :: hb) L' A' regs' mem' md' /\
  Permutation (blocks L' A') (((res, n) :: hb) ++ blocks (g_L g) (g_A g)) /\
  (forall a, fsp g <= a < g_S g -> mbyte rsegs mem' a = mbyte rsegs mem a) /\
  (forall a k i, In (a, k) hb -> 0 <= i < k -> mbyte rsegs mem' (a + i) = mbyte rsegs mem (a + i)).
Proof.
  intros K g hb L A regs mem md regs_c n L' A' regs' mem' md' res b1 b2 HK HF HP E2 E3 E4 POST EB' EB KEPT RO' INIT
    RES'.
  pose proof HK as HK'. unfold CALLOC_STACK, ALLOC_STACK in HK'.
  pose proof (sl_segs B APIf ra empty FF) as ES.
  destruct HF as (HGV & Hsp & Hgp & Htp & Hsav & Hstk & HMI & Hrel & HMR & HWF & Hbd & Hin & Hmd & Hhi & Himg &
                  Hblk & Herr & Hsink & HRES & Hwr).
  pose proof HGV as (Hn0 & Hp0 & Hbd0 & HS16 & HSK & HS47 & Hroom & HgS & Htp0 & HGI).
  destruct POST as (MR' & WF' & BD' & LL' & PA' & RP' & (vm' & Emd) & MEM & UB & SCW).
  pose proof alloc_ceiling_value as HAC. pose proof (sl_errno B APIf ra empty FF) as HEC.
  pose proof (sl_errno_val B APIf ra empty FF) as HEV.
  unfold SLOT_K, SLOT_STACK in *.
  assert (HSP : spZ regs_c = g_S g - 240).
  { unfold spZ. rewrite E2, Hsp. unfold fsp, SLOT_FRAME. apply MState.unsigned_lit. lia. }
  assert (HOW : forall L0 A0 m0 md0 a, aa_MR API L0 A0 m0 md0 -> owned B L0 A0 a -> a < YM05.alloc_ceiling).
  { intros L0 A0 m0 md0 a H Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ H Ho). lia. }
  assert (HI : forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
      ~ (errno_addr B <= a < errno_addr B + 4) ->
      mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
      (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha H1 H2 H3. pose proof (sl_in_img_top B a ES Ha) as Hl. unfold SL_TOP in Hl. apply MEM.
    - right. exact Ha.
    - intros [Ho|Ho]; [exact (H2 (ax_img b1_ax L A mem md a HMR Ha Ho)) | exact (H1 Ho)].
    - intros [Ho|Ho]; [exact (H2 (ax_img b1_ax L' A' mem' md' a MR' Ha Ho)) | exact (H1 Ho)].
    - unfold scratch_k. rewrite HSP. lia.
    - intros []. }
  assert (HH : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ (g_S g - 240 - K <= a < g_S g - 240) ->
      mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
      (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)).
  { intros a Ha Hs. apply MEM.
    - left. exact Ha.
    - intros Ho. pose proof (HOW _ _ _ _ a HMR Ho). lia.
    - intros Ho. pose proof (HOW _ _ _ _ a MR' Ho). lia.
    - unfold scratch_k. rewrite HSP. lia.
    - intros []. }
  assert (HWR : forall a, g_S g - 65536 <= a < g_S g -> writable_at (ms_segs B) mem' a).
  { intros a Ha. destruct (Z_lt_le_dec a (g_S g - 240 - K)) as [Hl|Hl];
      [|destruct (Z_lt_le_dec a (g_S g - 240)) as [Hl2|Hl2]].
    - apply (proj2 (HH a ltac:(lia) ltac:(lia))). apply Hwr. lia.
    - apply SCW. unfold scratch_k. rewrite HSP. lia.
    - apply (proj2 (HH a ltac:(lia) ltac:(lia))). apply Hwr. lia. }
  split; [|split; [|split]].
  2:{ rewrite EB'. cbn [app]. eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
      apply perm_skip. rewrite <- EB. exact HP. }
  2:{ intros a Ha. unfold fsp, SLOT_FRAME in Ha. rewrite <- ES. exact (proj1 (HH a ltac:(lia) ltac:(lia))). }
  2:{ intros a k i Hak Hi. rewrite <- ES. apply (KEPT a k i); [| exact (fun H => H) | exact Hi].
      exact (b1_in_hb _ _ _ _ HP Hak). }
  unfold FR, RESB, SLOT_K, SLOT_STACK.
  split; [exact HGV|].
  split; [etransitivity; [exact (RP' 2 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E2|]; exact Hsp|].
  split; [etransitivity; [exact (RP' 3 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E3|]; exact Hgp|].
  split; [etransitivity; [exact (RP' 4 ltac:(unfold callee_saved; lia))|]; etransitivity; [exact E4|]; exact Htp|].
  split.
  { apply (b1_ba_mbyte mem); [exact Hsav|]. intros i Hi.
    rewrite sl_saved_len in Hi. rewrite <- ES. unfold SLOT_SAVE.
    exact (proj1 (HH (g_S g - 104 + i) ltac:(lia) ltac:(lia))). }
  split; [apply sl_stk_of_writable; [unfold SL_TOP; lia | lia | intros a Ha; rewrite <- ES; apply HWR; exact Ha]|].
  split; [unfold MI; exact RO'|].
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (Hrel a Ha).
    destruct (b1_relro_full a Ha) as (H1 & H2 & H3 & H4). exact (proj1 (HI a H1 H2 H3 H4)). }
  split; [exact MR'|]. split; [exact WF'|]. split; [exact BD'|]. split; [exact INIT|].
  split; [destruct Hmd as (vm & ->); exists vm'; rewrite Emd; reflexivity|].
  split.
  { intros a Ha Hs He. destruct (Hhi a Ha Hs He) as [Q1 Q2]. destruct (HH a Ha ltac:(lia)) as [G1 G2].
    rewrite G1. split; [exact Q1|]. tauto. }
  split.
  { intros a Ha H1 H2 H3 H4. destruct (Himg a Ha H1 H2 H3 H4) as [Q1 Q2]. destruct (HI a Ha H1 H2 H3) as [G1 G2].
    rewrite G1. split; [exact Q1|]. tauto. }
  split.
  { intros a k i Hak Hi. rewrite <- (Hblk a k i Hak Hi). apply (KEPT a k i); [| exact (fun H => H) | exact Hi].
    exact (b1_in_E _ _ _ _ HP Hak). }
  split; [intros a Ha; apply SCW; unfold scratch_k; right; exact Ha|].
  split.
  { apply (b1_sink_frame mem mem' md md'); [|rewrite Emd; reflexivity | exact Hsink].
    intros a Ha. destruct (b1_sink_addr a Ha) as (H1 & H2 & H3 & H4). exact (proj1 (HI a H1 H2 H3 H4)). }
  split; [exact (resb_malloc (g_b g) hb ((res, n) :: hb) A' res n (Permutation_refl _) RES')|].
  intros a Ha. apply HWR. exact Ha.
Qed.

(* FR after malloc(n) from a cut with the live harness blocks hb (b1_FR_alloc_k at K = ALLOC_STACK). *)
Lemma b1_FR_malloc : forall g hb L A regs mem md regs_c n L' A' regs' mem' md' res b1 b2,
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  YK11.getr regs_c 2 = YK11.getr regs 2 -> YK11.getr regs_c 3 = YK11.getr regs 3 ->
  YK11.getr regs_c 4 = YK11.getr regs 4 ->
  call_post_k B (aa_MR API) ALLOC_STACK L A regs_c mem md (fun _ => False) L' A' regs' mem' md' ->
  blocks L' A' = b1 ++ (res, n) :: b2 -> blocks L A = b1 ++ b2 ->
  blocks_kept B L A mem mem' (fun _ => False) ->
  ro_agree (ms_segs B) mem' -> st_init_done A' = true ->
  res_ok_slots A' (sb_malloc (sb_hb (g_b g) hb) n) ->
  FR B APIf ra empty g ((res, n) :: hb) L' A' regs' mem' md' /\
  Permutation (blocks L' A') (((res, n) :: hb) ++ blocks (g_L g) (g_A g)) /\
  (forall a, fsp g <= a < g_S g -> mbyte rsegs mem' a = mbyte rsegs mem a) /\
  (forall a k i, In (a, k) hb -> 0 <= i < k -> mbyte rsegs mem' (a + i) = mbyte rsegs mem (a + i)).
Proof.
  intros g hb L A regs mem md regs_c n L' A' regs' mem' md' res b1 b2 HF HP E2 E3 E4 POST EB' EB KEPT RO' INIT RES'.
  exact (b1_FR_alloc_k ALLOC_STACK g hb L A regs mem md regs_c n L' A' regs' mem' md' res b1 b2
    ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) HF HP E2 E3 E4 POST EB' EB KEPT RO' INIT RES').
Qed.

(* malloc(n) from a cut with the live harness blocks hb (at most 16 blocks, 2^24 bytes), as a Kind B step: the
   continuation gets FR with (res, n) :: hb, res <> 0, res mod 16 = 0, and the bytes of [sp, S) and of the blocks of
   hb unchanged. *)
Lemma b1_malloc_call : forall g hb L A regs mem md regs_c n (Q : config -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (length hb <= 16)%nat -> 0 <= hb_bytes hb <= 2 ^ 24 ->
  YK11.getr regs_c 2 = YK11.getr regs 2 -> YK11.getr regs_c 3 = YK11.getr regs 3 ->
  YK11.getr regs_c 4 = YK11.getr regs 4 ->
  YK0s.ret_ok (YK11.getr regs_c 1) -> YK11.getr regs_c 10 = Z_to_bv 64 n -> 0 <= n <= 2 ^ 26 ->
  (forall L' A' regs' mem' md' res, FR B APIf ra empty g ((res, n) :: hb) L' A' regs' mem' md' ->
     Permutation (blocks L' A') (((res, n) :: hb) ++ blocks (g_L g) (g_A g)) -> regs_preserved regs_c regs' ->
     YK11.getr regs' 10 = Z_to_bv 64 res -> res <> 0 -> res mod 16 = 0 ->
     (forall a, fsp g <= a < g_S g -> mbyte rsegs mem' a = mbyte rsegs mem a) ->
     (forall a k i, In (a, k) hb -> 0 <= i < k -> mbyte rsegs mem' (a + i) = mbyte rsegs mem (a + i)) ->
     SR (ms_segs B) (mkCfg (YK11.mkst regs' (YK11.getr regs_c 1) mem' (YK11.seg_rom (ms_segs B))) md') Q) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs_c (Z_to_bv 64 0x17518) mem (YK11.seg_rom (ms_segs B))) md) Q.
Proof.
  intros g hb L A regs mem md regs_c n Q HF HP Hlen Hbytes E2 E3 E4 Hra H10 Hn K.
  pose proof (b1_call_pre g hb L A regs mem md regs_c HF E2 E4 Hra) as CP.
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
  pose proof HGV as (_ & _ & _ & _ & _ & _ & Hroom & _).
  destruct b1_alloc as (MAL & _).
  rewrite <- b1_malloc_addr.
  eapply SR_bind.
  { exact (MAL L A regs_c mem md n (sb_hb (g_b g) hb) CP HMI H10 Hb (resb_room (g_b g) hb n Hroom Hlen Hbytes Hn)). }
  intros c' (L' & A' & regs' & mem' & md' & res & -> & POST & H10' & Hres & Hal & _ & (b1 & b2 & EB' & EB) & KEPT &
             RO' & _ & _ & INIT & _ & RES').
  pose proof POST as (_ & _ & _ & _ & _ & RP' & _).
  destruct (b1_FR_malloc g hb L A regs mem md regs_c n L' A' regs' mem' md' res b1 b2 HF HP E2 E3 E4 POST EB' EB KEPT
              RO' INIT RES') as (HF' & HP' & HK & HKH).
  exact (K L' A' regs' mem' md' res HF' HP' RP' H10' Hres Hal HK HKH).
Qed.

(* calloc(m, n) from a cut with the live harness blocks hb (at most 16 blocks, 2^24 bytes), as a Kind B step through
   calloc_contract_big at calloc's entry CALLOC_PC (UBSan 0x172a0; the frame's ms_calloc is None, so
   the contract is a premise, discharged at segconf's concrete instance by CallocHolds.calloc_holds): the callee
   stack is CALLOC_STACK = 8224 (b1_call_pre_k), the request m * n <= CALLOC_BIG_CAP has room by resb_room, and the
   continuation gets FR with (res, m * n) :: hb, res <> 0, res mod 16 = 0, the bytes of [sp, S) and of the blocks of
   hb unchanged, and the new block's m * n bytes zero. *)
Lemma b1_calloc_call : forall g hb L A regs mem md regs_c m n (Q : config -> Prop),
  CallocBigC.calloc_contract_big B API CallocBigC.CALLOC_PC ->
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  (length hb <= 16)%nat -> 0 <= hb_bytes hb <= 2 ^ 24 ->
  YK11.getr regs_c 2 = YK11.getr regs 2 -> YK11.getr regs_c 3 = YK11.getr regs 3 ->
  YK11.getr regs_c 4 = YK11.getr regs 4 ->
  YK0s.ret_ok (YK11.getr regs_c 1) -> YK11.getr regs_c 10 = Z_to_bv 64 m -> YK11.getr regs_c 11 = Z_to_bv 64 n ->
  0 <= m -> 0 <= n -> m * n <= CallocBigC.CALLOC_BIG_CAP ->
  (forall L' A' regs' mem' md' res, FR B APIf ra empty g ((res, m * n) :: hb) L' A' regs' mem' md' ->
     Permutation (blocks L' A') (((res, m * n) :: hb) ++ blocks (g_L g) (g_A g)) -> regs_preserved regs_c regs' ->
     YK11.getr regs' 10 = Z_to_bv 64 res -> res <> 0 -> res mod 16 = 0 ->
     (forall a, fsp g <= a < g_S g -> mbyte rsegs mem' a = mbyte rsegs mem a) ->
     (forall a k i, In (a, k) hb -> 0 <= i < k -> mbyte rsegs mem' (a + i) = mbyte rsegs mem (a + i)) ->
     (forall i, 0 <= i < m * n -> mbyte rsegs mem' (res + i) = Some (Z_to_bv 8 0)) ->
     SR (ms_segs B) (mkCfg (YK11.mkst regs' (YK11.getr regs_c 1) mem' (YK11.seg_rom (ms_segs B))) md') Q) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs_c (Z_to_bv 64 CallocBigC.CALLOC_PC) mem (YK11.seg_rom (ms_segs B))) md) Q.
Proof.
  intros g hb L A regs mem md regs_c m n Q CAL HF HP Hlen Hbytes E2 E3 E4 Hra H10 H11 Hm Hn Hcap K.
  pose proof (b1_call_pre_k g hb L A regs mem md regs_c CALLOC_STACK
    ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) HF E2 E4 Hra) as CP.
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hb & _).
  pose proof HGV as (_ & _ & _ & _ & _ & _ & Hroom & _).
  pose proof (sl_segs B APIf ra empty FF) as ES.
  assert (Hmn : 0 <= m * n <= 2 ^ 26) by (unfold CallocBigC.CALLOC_BIG_CAP in Hcap; nia).
  eapply SR_bind.
  { exact (CAL L A regs_c mem md m n (sb_hb (g_b g) hb) CP HMI H10 H11 Hm Hn Hcap Hb
             (resb_room (g_b g) hb (m * n) Hroom Hlen Hbytes Hmn)). }
  intros c' [(L' & A' & regs' & mem' & md' & res & Ec & POST & H10' & Hres & Hal & Hfr & (b1 & b2 & EB' & EB) &
              KEPT & RO' & _ & _ & INIT & _ & RES') (ms' & md'' & Ec' & HZ)].
  rewrite Ec in Ec'. injection Ec' as Ems Emd. subst ms' md''. subst c'.
  pose proof POST as (_ & _ & _ & _ & _ & RP' & _).
  destruct (b1_FR_alloc_k CALLOC_STACK g hb L A regs mem md regs_c (m * n) L' A' regs' mem' md' res b1 b2
              ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) HF HP E2 E3 E4 POST EB' EB KEPT RO' INIT RES')
    as (HF' & HP' & HK & HKH).
  apply (K L' A' regs' mem' md' res HF' HP' RP' H10' Hres Hal HK HKH).
  intros i Hi. pose proof (HZ i Hi) as Z0. cbn [ms_mem ms_regs YK11.mkst] in Z0.
  rewrite H10' in Z0. destruct Hfr as (Hf1 & Hf2 & _). pose proof alloc_ceiling_lt as Hlt.
  rewrite MState.unsigned_lit in Z0 by lia. rewrite <- ES. exact Z0.
Qed.

(* The sink cells keep their bytes across a run that changes no image byte but longl's written ones. *)
Lemma b1_sink_keep : forall (m m' : word -> option byte) md,
  (forall a, in_img B a -> ~ (LONGL <= a < LONGL + LONGL_W) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  sink_none B m md -> sink_none B m' md.
Proof.
  intros m m' md HK (Henv & Hhead & Hn). destruct (sl_sink B APIf ra empty FF) as (E1 & E2 & E3).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  assert (HM : forall a, 0x53840 <= a < 0x53c78 -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a).
  { intros a Ha. unfold mbyte.
    rewrite (HK a (b1_img_sink B a SEGS Ha) ltac:(unfold LONGL, LONGL_W; lia)). reflexivity. }
  destruct Henv as [Ht Hl]. split; [split|split; [|exact Hn]].
  - eapply val_mem_frame; [|exact Ht]. intros x Hx. apply HM. rewrite E3 in Hx. cbn in Hx. lia.
  - eapply val_mem_frame; [|exact Hl]. intros x Hx. apply HM. rewrite E2 in Hx. cbn in Hx. lia.
  - apply (val_mem_word_mem (ms_segs B)). apply (val_mem_word_mem (ms_segs B)) in Hhead.
    eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply HM. rewrite E1 in Hx. cbn in Hx. lia.
Qed.

(* The errno cell [errno_addr B, errno_addr B + 4) = [0x3350c, 0x33510) (Tac_slot.sl_errno_val): in the image (its RW
   PT_LOAD [0x231c8, 0x54088)) and owned by no allocator state (frame_allocator's errno_unowned). A body that calls
   strtol (V01: reac_segconf_declared through reac_declared_vlan_split) writes it; FR lets it change. *)
Lemma b1_errno_img : forall a, errno_addr B <= a < errno_addr B + 4 -> in_img B a.
Proof.
  intros a Ha. rewrite (sl_errno_val B APIf ra empty FF) in Ha.
  assert (Hc : a = 0x3350c \/ a = 0x3350d \/ a = 0x3350e \/ a = 0x3350f) by lia.
  destruct Hc as [-> | [-> | [-> | ->]]];
    match goal with |- in_img _ ?x =>
      destruct (find_segment rsegs x 1) as [seg|] eqn:Ef;
      [exact (b1_find_img B x seg (sl_segs B APIf ra empty FF) Ef) | vm_compute in Ef; discriminate Ef]
    end.
Qed.

Lemma b1_errno_unowned : forall L A mem md a, aa_MR API L A mem md -> errno_addr B <= a < errno_addr B + 4 ->
  ~ owned B L A a.
Proof.
  destruct b1_alloc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EU & _). exact EU.
Qed.

(* b1_sink_keep for a run that may also change the errno cell (no sink cell lies in it). *)
Lemma b1_sink_keep_e : forall (m m' : word -> option byte) md,
  (forall a, in_img B a -> ~ (LONGL <= a < LONGL + LONGL_W) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
     m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  sink_none B m md -> sink_none B m' md.
Proof.
  intros m m' md HK (Henv & Hhead & Hn). destruct (sl_sink B APIf ra empty FF) as (E1 & E2 & E3).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof (sl_errno_val B APIf ra empty FF) as Ev.
  assert (HM : forall a, 0x53840 <= a < 0x53c78 -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a).
  { intros a Ha. unfold mbyte.
    rewrite (HK a (b1_img_sink B a SEGS Ha) ltac:(unfold LONGL, LONGL_W; lia) ltac:(rewrite Ev; lia)).
    reflexivity. }
  destruct Henv as [Ht Hl]. split; [split|split; [|exact Hn]].
  - eapply val_mem_frame; [|exact Ht]. intros x Hx. apply HM. rewrite E3 in Hx. cbn in Hx. lia.
  - eapply val_mem_frame; [|exact Hl]. intros x Hx. apply HM. rewrite E2 in Hx. cbn in Hx. lia.
  - apply (val_mem_word_mem (ms_segs B)). apply (val_mem_word_mem (ms_segs B)) in Hhead.
    eapply val_mem_frame; [|exact Hhead]. intros x Hx. apply HM. rewrite E1 in Hx. cbn in Hx. lia.
Qed.

(* An address in one of the blocks of a write list Wb, and its decision. *)
Definition in_wb (Wb : list (Z * Z)) (a : Z) : Prop := exists phi n, In (phi, n) Wb /\ phi <= a < phi + n.

Lemma in_wb_dec : forall Wb a, {in_wb Wb a} + {~ in_wb Wb a}.
Proof.
  induction Wb as [|[phi n] Wb IH]; intros a.
  - right. intros (p & k & [] & _).
  - destruct (IH a) as [Hy|Hn].
    + left. destruct Hy as (p & k & Hin & Hr). exists p, k. split; [right; exact Hin | exact Hr].
    + destruct (Z_le_dec phi a) as [H1|H1]; [destruct (Z_lt_dec a (phi + n)) as [H2|H2]|].
      * left. exists phi, n. split; [left; reflexivity | lia].
      * right. intros (p & k & [E|Hin] & Hr);
          [injection E as E1 E2; subst p k; lia | apply Hn; exists p, k; split; [exact Hin | exact Hr]].
      * right. intros (p & k & [E|Hin] & Hr);
          [injection E as E1 E2; subst p k; lia | apply Hn; exists p, k; split; [exact Hin | exact Hr]].
Qed.

(* FR across a run that writes the stack window [S - K, S - 104), the blocks Wb of hb, longl's written bytes
   [LONGL, LONGL + LONGL_W) and the errno cell [errno_addr B, errno_addr B + 4); each written block's bytes stay
   present (the run keeps writability). FR's own clauses already let errno change (its image clause and its
   alloc_ceiling clause exclude it; it keeps errno writable), the allocator owns no errno byte (b1_errno_unowned),
   and no entry block, RELRO byte, saved register or sink cell lies in it. *)
Lemma b1_fr_hb_e : forall g hb Wb L A regs mem md regs' mem',
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> (forall x, In x Wb -> In x hb) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (g_S g - SLOT_K <= a < g_S g - 104) -> ~ in_wb Wb a ->
     ~ (LONGL <= a < LONGL + LONGL_W) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  YK11.getr regs' 2 = YK11.getr regs 2 -> YK11.getr regs' 3 = YK11.getr regs 3 ->
  YK11.getr regs' 4 = YK11.getr regs 4 ->
  FR B APIf ra empty g hb L A regs' mem' md.
Proof.
  intros g hb Wb L A regs mem md regs' mem' HFR HP HWb HU WM MI' E2 E3 E4.
  destruct HFR as (HGV & F2 & F3 & F4 & Hsv & Hstk & HMI & Hrel & HM & HWf & HB & HID & Hmd & Hhigh & Himg &
                   Hblk & Herr & Hsn & Hres & Hwin).
  pose proof HGV as (_ & _ & _ & HS16 & HSK & HS47 & _).
  pose proof alloc_ceiling_value as Hac. pose proof (sl_segs B APIf ra empty FF) as SEGS.
  pose proof sl_ceil as Hceil.
  pose proof (sl_errno_val B APIf ra empty FF) as Ev.
  unfold SLOT_K, SLOT_STACK in *.
  assert (HGl : forall a, LONGL <= a < LONGL + LONGL_W -> in_img B a)
    by (intros a Ha; exact (proj1 (ff_G B APIf ra empty FF a (sl_longl_in a Ha)))).
  assert (HGo : forall a, LONGL <= a < LONGL + LONGL_W -> ~ owned B L A a)
    by (intros a Ha; exact (b1_G_unowned L A mem md a HM (sl_longl_in a Ha))).
  assert (HWbB : forall phi n, In (phi, n) Wb -> exists p, ptr_addr L p = phi /\ In (p, n) (user_blocks A)).
  { intros phi n Hw. pose proof (b1_in_hb _ _ _ _ HP (HWb _ Hw)) as Hin. apply blocks_In in Hin as (p & Ep & Hp).
    exists p. split; [exact Ep | exact Hp]. }
  assert (Hnimg : forall a, in_wb Wb a -> ~ in_img B a).
  { intros a (phi & n & Hw & Ha) Hi. destruct (HWbB phi n Hw) as (p & Ep & Hp).
    apply (ax_blocks_img b1_ax L A mem md p n (a - phi) HM Hp ltac:(lia)).
    rewrite Ep. replace (phi + (a - phi)) with a by lia. exact Hi. }
  assert (Hnown : forall a, in_wb Wb a -> ~ owned B L A a).
  { intros a (phi & n & Hw & Ha). destruct (HWbB phi n Hw) as (p & Ep & Hp).
    destruct (mr_blocks B _ (aa_laws API) L A mem md p n (a - phi) HM Hp ltac:(lia)) as (_ & _ & _ & H).
    rewrite Ep in H. replace (phi + (a - phi)) with a in H by lia. exact H. }
  assert (Hpres : forall a, in_wb Wb a -> exists b, mrd rsegs mem' (wa a) = Some b).
  { intros a (phi & n & Hw & Ha).
    exact (b1_blk_present L A mem md mem' phi n HM (b1_in_hb _ _ _ _ HP (HWb _ Hw)) WM a Ha). }
  assert (Hwblo : forall a, in_wb Wb a -> 0 <= a < YM05.alloc_ceiling).
  { intros a (phi & n & Hw & Ha). destruct (HWbB phi n Hw) as (p & Ep & Hp).
    destruct (mr_blocks_range B _ (aa_laws API) _ _ _ _ _ _ HM Hp) as [R1 R2]. rewrite Ep in R1, R2. lia. }
  (* A user block's byte is not an errno byte: the block is outside the image, the errno cell inside it. *)
  assert (Hbne : forall q k i, In (q, k) (user_blocks A) -> 0 <= i < k ->
                   ~ (errno_addr B <= ptr_addr L q + i < errno_addr B + 4)).
  { intros q k i Hq Hi He. apply (ax_blocks_img b1_ax L A mem md q k i HM Hq Hi). exact (b1_errno_img _ He). }
  assert (HL : forall a, 0 <= a < YM05.alloc_ceiling -> ~ in_wb Wb a -> ~ (LONGL <= a < LONGL + LONGL_W) ->
                 ~ (errno_addr B <= a < errno_addr B + 4) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hn Hl He. apply HU; [lia | lia | exact Hn | exact Hl | exact He]. }
  assert (HI : forall a, in_img B a -> ~ (LONGL <= a < LONGL + LONGL_W) -> ~ (errno_addr B <= a < errno_addr B + 4) ->
                 mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hl He. pose proof (sl_in_img_top B a SEGS Ha) as Ht.
    apply HL; [lia | intros Hc; exact (Hnimg a Hc Ha) | exact Hl | exact He]. }
  assert (Hwr : forall a, writable_at (ms_segs B) mem a -> writable_at (ms_segs B) mem' a).
  { intros a W. unfold writable_at in *. rewrite SEGS in *. apply WM. exact W. }
  split; [exact HGV|]. split; [rewrite E2; exact F2|]. split; [rewrite E3; exact F3|].
  split; [rewrite E4; exact F4|].
  split.
  { apply (sl_bytes_keep mem mem' _ _ Hsv). intros i Hi. rewrite sl_saved_len in Hi.
    unfold SLOT_SAVE. apply HU; [lia | lia | intros Hc; pose proof (Hwblo _ Hc); lia | |].
    - unfold SL_TOP, LONGL, LONGL_W in *. lia.
    - rewrite Ev. unfold SL_TOP in *. lia. }
  split.
  { apply sl_stk_of_writable; [unfold SL_TOP, SLOT_K, SLOT_STACK; lia | lia |].
    intros a Ha. rewrite <- SEGS. apply Hwr, Hwin. exact Ha. }
  split; [unfold MI; rewrite SEGS; exact MI'|].
  split.
  { unfold relro, G_img_c in *. intros a Ha. rewrite <- (Hrel a Ha).
    assert (Hl : ~ (LONGL <= a < LONGL + LONGL_W)).
    { destruct Ha as (lo & len & Hin & Hr). unfold frame_RELRO in Hin. cbn in Hin.
      destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold LONGL, LONGL_W; lia. }
    destruct (b1_relro_full a Ha) as (_ & _ & _ & He).
    unfold mbyte. rewrite (HI a (b1_relro_img a Ha) Hl He). reflexivity. }
  split.
  { destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & Hmat).
    eapply (mr_frame B (aa_MR API) (aa_laws API)); [exact HM | | | | reflexivity | exact Hh | exact Hl | exact Hmat].
    - intros a Ho. pose proof (mr_owned_low B (aa_MR API) (aa_laws API) _ _ _ _ a HM Ho) as Ha.
      unfold mbyte. rewrite (HL a Ha (fun Hc => Hnown a Hc Ho) (fun Hc => HGo a Hc Ho)
                               (fun Hc => b1_errno_unowned L A mem md a HM Hc Ho)). reflexivity.
    - intros a Ho [bb Hb]. pose proof (mr_owned_low B (aa_MR API) (aa_laws API) _ _ _ _ a HM Ho) as Ha.
      exists bb. rewrite (HL a Ha (fun Hc => Hnown a Hc Ho) (fun Hc => HGo a Hc Ho)
                           (fun Hc => b1_errno_unowned L A mem md a HM Hc Ho)). exact Hb.
    - intros q k i Hq Hi.
      destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem md q k i HM Hq Hi) as ([bb Hpr] & H1 & H2 & _).
      destruct (in_wb_dec Wb (ptr_addr L q + i)) as [Hw|Hw].
      + destruct (Hpres _ Hw) as (b' & Hb').
        exact (b1_present B mem' _ b' SEGS (Hnimg _ Hw) ltac:(lia) Hb').
      + assert (Hnl : ~ (LONGL <= ptr_addr L q + i < LONGL + LONGL_W)).
        { intros Hc. apply (ax_blocks_img b1_ax L A mem md q k i HM Hq Hi). exact (HGl _ Hc). }
        exists bb. rewrite (HL (ptr_addr L q + i) ltac:(lia) Hw Hnl (Hbne q k i Hq Hi)). exact Hpr. }
  split; [exact HWf|]. split; [exact HB|]. split; [exact HID|]. split; [exact Hmd|].
  split.
  { intros a Ha Hns Hne. destruct (Hhigh a Ha Hns Hne) as [Q1 Q2]. unfold SLOT_K, SLOT_STACK in Hns.
    assert (Hx : mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { apply HU; [lia | lia | intros Hc; pose proof (Hwblo _ Hc); lia | | exact Hne].
      unfold SL_TOP, LONGL, LONGL_W in *. lia. }
    rewrite SEGS in *. destruct (sl_eq_at mem mem' a Hx) as [G1 G2].
    split; [rewrite G1; exact Q1 | rewrite Q2; exact G2]. }
  split.
  { intros a H1 H2 H3 H4 H5. destruct (Himg a H1 H2 H3 H4 H5) as [Q1 Q2].
    destruct (sl_eq_at mem mem' a (HI a H1 H5 H4)) as [G1 G2]. rewrite SEGS in *.
    split; [rewrite G1; exact Q1 | rewrite Q2; exact G2]. }
  split.
  { intros a k i Hin Hi. rewrite <- (Hblk a k i Hin Hi).
    pose proof (b1_in_E _ _ _ _ HP Hin) as HinL.
    apply blocks_In in HinL as (q & Eq & Hq).
    destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem md q k i HM Hq Hi) as (_ & H1 & H2 & _).
    assert (Hnl : ~ (LONGL <= a + i < LONGL + LONGL_W)).
    { intros Hc. apply (ax_blocks_img b1_ax L A mem md q k i HM Hq Hi). rewrite Eq. exact (HGl _ Hc). }
    assert (Hne : ~ (errno_addr B <= a + i < errno_addr B + 4)) by (rewrite <- Eq; exact (Hbne q k i Hq Hi)).
    rewrite Eq in H1, H2.
    assert (Hnw : ~ in_wb Wb (a + i)).
    { intros (phi & n & Hw & Hr).
      destruct (in_split _ _ (HWb _ Hw)) as (h1 & h2 & Eh). rewrite Eh in HP.
      pose proof (mr_blocks_disjoint B _ (aa_laws API) _ _ _ _ HM) as PD.
      apply (b1_pw_perm _ ranges_disjoint b1_rd_sym _ _ (b1_perm_front h1 h2 _ _ (phi, n) HP)) in PD.
      destruct PD as [PD _].
      assert (Hin2 : In (a, k) (h1 ++ h2 ++ blocks (g_L g) (g_A g)))
        by (apply in_or_app; right; apply in_or_app; right; exact Hin).
      pose proof (PD (a, k) Hin2) as Hd. unfold ranges_disjoint in Hd. cbn [fst snd] in Hd. lia. }
    unfold mbyte. rewrite (HL (a + i) ltac:(lia) Hnw Hnl Hne). reflexivity. }
  split; [intros a Ha; apply Hwr; exact (Herr a Ha)|].
  split; [exact (b1_sink_keep_e mem mem' md HI Hsn)|].
  split; [exact Hres|].
  intros a Ha. apply Hwr, Hwin. exact Ha.
Qed.

(* FR across a run that writes the stack window [S - K, S - 104), the blocks Wb of hb and longl's written bytes
   [LONGL, LONGL + LONGL_W) (b1_fr_hb_e with the errno cell untouched); each written block's bytes stay present
   (the run keeps writability). Wb = [] and no longl write is a window-only run; Wb = [(phi, n)] is role's
   one-block b1_fr_hb. *)
Lemma b1_fr_hb : forall g hb Wb L A regs mem md regs' mem',
  FR B APIf ra empty g hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> (forall x, In x Wb -> In x hb) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (g_S g - SLOT_K <= a < g_S g - 104) -> ~ in_wb Wb a ->
     ~ (LONGL <= a < LONGL + LONGL_W) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  YK11.getr regs' 2 = YK11.getr regs 2 -> YK11.getr regs' 3 = YK11.getr regs 3 ->
  YK11.getr regs' 4 = YK11.getr regs 4 ->
  FR B APIf ra empty g hb L A regs' mem' md.
Proof.
  intros g hb Wb L A regs mem md regs' mem' HFR HP HWb HU.
  apply (b1_fr_hb_e g hb Wb L A regs mem md regs' mem' HFR HP HWb).
  intros a Ha H1 H2 H3 _. exact (HU a Ha H1 H2 H3).
Qed.

End B1.
