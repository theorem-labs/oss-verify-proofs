(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 2065 of its 2181 lines of code are new or changed and 895 lines of the source are left out. *)
(* Segment F3 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, patched image A): 0x81dd0-0x81df8 and the reac_ctrl_parse
   call, to its return point 0x81dfc (F4's first entry).
     81dd0 addi s9,s7,18 (s9 = Phi + 18); 81dd4 .. 81de0 sb zero,22(s3) .. sb zero,25(s3); 81de4 li a0,4;
     81de8 sb a0,26(s3) -- the five frame shadow bytes S(fr) + 22 .. 26 (s3 = S(fr)) mark the 36 output cells
     [fr + 176, fr + 212) usable; 81dec mv a0,s7; 81df0 mv a1,s2; 81df4 ld a2,248(s1) (a2 = fr + 176, the prologue
     spill); 81df8 jal reac_ctrl_parse.
   The call runs on the lib/A contract reac_ctrl_parse_c.v (Section Hypothesis HPARSE). Its mem_inv premise is
   reached on the normalized memory (MemNorm.evt_normalize from FRA's ro_agree); its side-stack premises (fp [1] and
   reac_ctrl_parse_tls) come from Tac_fsfree.fra_fp, its window from fra_win / FRA's window conjunct, the bcmp cells
   from the runtime invariant, REAC_CTRL_PARSE_BC from FRA's frame_AG conjunct, the record bytes (long frame) and
   the block's placement from b5_C / the block's AH. Its post gives a0 = fst (ctrlparse len (t_g j)) = t_k j and
   the 36 output cells at fr + 176, whose first four bytes are the u32 kind (C7, f3_c7).
   Cuts: entry Seg/F2.v's Inv_A81dd0_c5_at (the b5_CUT shell at 0x81dd0), exit the official Inv_A81dfc_at. The
   machinery of the five shadow stores and of the call is a Theorem Labs lane's F4.v 0x81e54 path (a working branch
   f291edd614b: f4_fr_ah, f4_fra_sh, f4_dbc_call(n), f4_fr_run, f4_fra_call), renamed f3_ and taken at the record
   length len instead of 0. rule 24: no function proved. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcParse RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c asan_stack_malloc_c
  RcAsanFP reac_ctrl_parse_c reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 Tac_fs F1 F2.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Tac Bytes.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module FP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFP.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.
Module SFA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.

Section S.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contract (lib/A/Prog/reac_ctrl_parse_c.v), a Section Hypothesis. *)
Hypothesis HPARSE : reac_ctrl_parse_contract.

(* ---------------- kit (a Theorem Labs lane's F4.v) ---------------- *)

(* ---------------- kit ---------------- *)

(* Rewrite a known register slot `getr regs r` to its carried concrete value, from H : rg regs r v. *)
Ltac f3_subst_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

Lemma f3_id : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal (@bv_unsigned 64)) in E.
  rewrite !MState.unsigned_lit in E by lia. exact E.
Qed.

(* An interval of high memory is application memory. *)
Lemma f3_app_ivl : forall lo hi, HIGHMEM_BEG <= lo -> hi <= APPMEM_END -> app_ivl lo hi.
Proof. intros lo hi H1 H2 a Ha. unfold app_mem. right. lia. Qed.

(* The record length is a sum of byte values, so it is never negative. *)
Lemma f3_flen_nn : forall g j, 0 <= flen g j.
Proof.
  intros g j. unfold flen, t_len, f_len, f_L, f_h.
  assert (Hb : forall k, 0 <= inb (g_in g) k) by (intros k; unfold inb; exact (proj1 (bv_unsigned_in_range 8 _))).
  pose proof (Hb (fc (g_in g) j)). pose proof (Hb (fc (g_in g) j + 1)).
  destruct (2 <=? f_left (g_in g) (fc (g_in g) j)); lia.
Qed.

(* An 8-byte cell survives a write whose footprint misses it. *)
Lemma f3_q64_keep : forall W m m' a v, q64 m a v -> Frame.munch W m m' ->
  (forall x, a <= x < a + 8 -> Frame.outside W x) -> q64 m' a v.
Proof.
  intros W m m' a v H MU HW. unfold q64 in *.
  eapply fl_bytes; [exact H | exact MU |]. rewrite length_le8. intros x Hx. apply HW. lia.
Qed.

(* A 4-byte cell survives a write whose footprint misses it. *)
Lemma f3_u32_keep : forall W m m' a v, u32 m a v -> Frame.munch W m m' ->
  (forall x, a <= x < a + 4 -> Frame.outside W x) -> u32 m' a v.
Proof.
  intros W m m' a v H MU HW. unfold u32 in *.
  eapply fl_bytes; [exact H | exact MU |]. rewrite length_le4. intros x Hx. apply HW. lia.
Qed.

(* A thread word survives a write whose footprint misses its eight bytes, and is read back unchanged. *)
Lemma f3_word_eq : forall W m m' a, Frame.munch W m m' ->
  (forall x, a <= x < a + 8 -> Frame.outside W x) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  forall v, word_mem rsegs m a v <-> word_mem rsegs m' a v.
Proof.
  intros W m m' a MU HW Ha Hhi v.
  assert (HE : forall k, (k < 8)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))).
  { intros k Hk. apply MU. rewrite MState.unsigned_lit by lia. apply HW; lia. }
  split; intros H k Hk; pose proof (H k Hk) as Hb; unfold mbyte in *.
  - rewrite (HE k Hk). exact Hb.
  - rewrite (HE k Hk) in Hb. exact Hb.
Qed.

(* A frame-loop spill word survives a write that misses its eight bytes. The spill's own existential base names
   the same A as FRA: the cell is inside [A, A + 416) and A is far below 2 ^ 64. *)
Lemma f3_spill_keep : forall regs regs' A off v m m' W,
  spill regs m off v -> rg regs 9 A -> 0 <= A < 2 ^ 64 -> A + 416 <= APPMEM_END -> 0 <= off <= 408 ->
  getr regs' 9 = getr regs 9 -> Frame.munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> Frame.outside W x) ->
  spill regs' m' off v.
Proof.
  intros regs regs' A off v m m' W HS H9 HA HAE Hoff E9 MU HW.
  destruct HS as (A' & H9' & Hq).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HP : 2 ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (Hqb : 0 <= A' + off /\ A' + off + Z.of_nat (length (le8 (Z_to_bv 64 v))) <= 2 ^ 64)
    by (unfold q64 in Hq; exact (bytes_at_bound rsegs m (A' + off) _ Hq)).
  rewrite length_le8 in Hqb.
  assert (HAA : A' = A).
  { pose proof (rg_eq64 regs 9 A' A H9' H9) as Hm.
    assert (Hdz : (A' - A) mod 2 ^ 64 = 0).
    { rewrite Zminus_mod, Hm, Z.sub_diag. apply Zmod_0_l. }
    destruct (proj1 (Zmod_divides (A' - A) (2 ^ 64) ltac:(lia)) Hdz) as (q & Hq2).
    rewrite HP in Hq2. lia. }
  subst A'.
  exists A. split; [unfold rg in *; rewrite E9; exact H9|].
  exact (f3_q64_keep W m m' (A + off) v Hq MU HW).
Qed.

(* ADDR-KEEP for a write list that may touch the shadow: a block stays addressable when the shadow bytes of its
   own granules are outside the writes. *)
Lemma f3_addr_keep : forall W m m' p n, addressable m p n -> Frame.munch W m m' ->
  (forall i, 0 <= i < n -> Frame.outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HW. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (in_shadow_range (shadow_addr (p + i)) (shadow_of_app _ Hap)) as HR.
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite Mem.wa_unsigned by lia. exact (HW i Hi).
Qed.

(* Shadow geometry. *)
Lemma f3_sh_lo : forall a, 0 <= a -> LOWMEM_END <= shadow_addr a.
Proof. intros a Ha. unfold shadow_addr, ASAN_K, LOWMEM_END. assert (0 <= a / 8) by (apply Z.div_pos; lia). lia. Qed.

Lemma f3_sh_hi : forall a, 0 <= a < APPMEM_END -> shadow_addr a < HIGHMEM_BEG.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, HIGHMEM_BEG.
  assert (D : a / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; [lia | unfold APPMEM_END in Ha; lia]).
  lia.
Qed.

Lemma f3_sh_hi_le : forall a, 0 <= a <= APPMEM_END -> shadow_addr a <= HIGHMEM_BEG.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, HIGHMEM_BEG.
  assert (D : a / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; [lia | unfold APPMEM_END in Ha; lia]).
  lia.
Qed.

Lemma f3_sh_mono : forall x y, x <= y -> shadow_addr x <= shadow_addr y.
Proof. intros x y H. unfold shadow_addr. pose proof (Z.div_le_mono x y 8 ltac:(lia) H). lia. Qed.

(* A strict shadow comparison that only needs y 8-aligned. *)
Lemma f3_sh_lt2 : forall x y, 0 <= x -> x < y -> y mod 8 = 0 -> shadow_addr x < shadow_addr y.
Proof.
  intros x y H0 H Hm. unfold shadow_addr.
  assert (x / 8 < y / 8).
  { apply Z.div_lt_upper_bound; [lia|]. Z.div_mod_to_equations. lia. }
  lia.
Qed.

(* The shadow byte of a frame byte from fr + 216 on is one of the frame's shadow bytes 27..379. *)
Lemma f3_sh_frame : forall fr x, fr mod 8 = 0 -> fr + 216 <= x < fr + FRAME_BYTES ->
  Sfr fr + 27 <= shadow_addr x < Sfr fr + FRAME_SHADOW.
Proof. pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs. intros fr x Hm Hx. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* ---------------- path 2: the 0x81e54 block, in the Lib engine ----------------
   The callee contract reac_ctrl_parse_c states its run as a Lib.Exec.evt, so the 0x81e54 block (the six stores
   and the call) is stepped by the Lib engine. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Tac
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Bytes.
Import YK11.
Open Scope Z_scope.

(* mkR_of regs is definitionally the explicit 31-slot register map of the Lib engine. *)
Lemma f3_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* A byte value is below 256. *)
Lemma f3_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as HR. unfold bv_modulus in HR.
  change (2 ^ Z.of_N 8) with 256 in HR. lia.
Qed.

Lemma f3_word_range : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof.
  intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in H. lia.
Qed.

Lemma f3_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0 in HH. rewrite Z.add_0_r, skipn_O in HH.
  rewrite firstn_all2 in HH by lia. exact HH.
Qed.

Lemma f3_bytes_cons : forall m a b bs, bytes_at rsegs m a [b] -> bytes_at rsegs m (a + 1) bs ->
  bytes_at rsegs m a (b :: bs).
Proof.
  intros m a b bs (Ha0 & _ & Hb) (_ & Hbl & Hbs). split; [exact Ha0|].
  split; [cbn [length] in *; lia|].
  intros i Hi. destruct i as [|i].
  - pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as H0. cbn [nth_error] in H0 |- *. exact H0.
  - cbn [nth_error]. cbn [length] in Hi.
    replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
    exact (Hbs i ltac:(lia)).
Qed.

Lemma f3_le1_0 : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

Lemma f3_le1_4 : le1 (Z_to_bv 64 4) = [Z_to_bv 8 4].
Proof. vm_compute. reflexivity. Qed.

(* Every byte of a carried byte list is present. *)
Lemma f3_pres_at : forall m a (l : list byte) q, bytes_at rsegs m a l -> a <= q < a + Z.of_nat (length l) ->
  exists b, mbyte rsegs m q = Some b.
Proof.
  intros m a l q (Ha & Hl & H) Hq.
  assert (Hi : (Z.to_nat (q - a) < length l)%nat) by lia.
  pose proof (H _ Hi) as Hq5. rewrite Z2Nat.id in Hq5 by lia.
  replace (a + (q - a)) with q in Hq5 by lia.
  destruct (nth_error l (Z.to_nat (q - a))) as [b|] eqn:En; [|apply nth_error_None in En; lia].
  exists b. exact Hq5.
Qed.

(* Two word values read at the same address agree modulo 2^64. *)
Lemma f3_wm_eq : forall m a v v', word_mem rsegs m a v -> word_mem rsegs m a v' ->
  v mod 2 ^ 64 = v' mod 2 ^ 64.
Proof.
  intros m a v v' H H'.
  assert (P : 2 ^ 64 <> 0) by lia.
  assert (E : forall k, (k < 8)%nat -> le_byte (v mod 2 ^ 64) 8 k = le_byte (v' mod 2 ^ 64) 8 k).
  { intros k Hk. pose proof (H k Hk) as H1. pose proof (H' k Hk) as H2.
    assert (H3 : Z_to_bv 8 (le_byte v 8 k) = Z_to_bv 8 (le_byte v' 8 k)) by congruence.
    apply (f_equal bv_unsigned) in H3. rewrite !kb_byte_unsigned in H3. clear H1 H2. rename H3 into H2.
    unfold le_byte in H2 |- *. change (8 * Z.of_nat 8) with 64 in H2 |- *. rewrite !Z.mod_mod by exact P.
    exact H2. }
  assert (R1 : 0 <= v mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  assert (R2 : 0 <= v' mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  rewrite (kb_le8_digits _ R1), (kb_le8_digits _ R2).
  rewrite !E by lia. reflexivity.
Qed.

Lemma f3_wm_norm : forall m a x y, word_mem rsegs m a x -> word_mem rsegs m a y ->
  0 <= y < 2 ^ 64 -> - (2 ^ 64) < x < 2 ^ 64 -> x = y \/ x = y - 2 ^ 64.
Proof.
  intros m a x y Hx Hy Hy0 Hx0.
  pose proof (f3_wm_eq m a x y Hx Hy) as E.
  rewrite (Z.mod_small y (2 ^ 64)) in E by lia.
  destruct (Z_le_gt_dec 0 x) as [Hs|Hs].
  - left. rewrite (Z.mod_small x (2 ^ 64)) in E by lia. exact E.
  - right.
    assert (EM : (x + 2 ^ 64) mod 2 ^ 64 = x mod 2 ^ 64).
    { replace (x + 2 ^ 64) with (x + 1 * 2 ^ 64) by lia. apply Z_mod_plus_full. }
    rewrite (Z.mod_small (x + 2 ^ 64) (2 ^ 64)) in EM by lia. lia.
Qed.

Lemma f3_dj_hi : forall (W : list (Z * Z)) a n, (forall lo hi, In (lo, hi) W -> a + n <= lo) ->
  disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; cbn [disjoint_from]; [exact I|].
  split; [left; exact (H lo hi (or_introl eq_refl))|].
  apply IH. intros lo' hi' Hin. exact (H lo' hi' (or_intror Hin)).
Qed.

(* Every range at or above GT is apart from the runtime's cells (all below GT). *)
Lemma f3_rt : forall W, (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> rt_disjoint W.
Proof.
  intros W H. unfold rt_disjoint.
  repeat split; apply f3_dj_hi; intros lo hi Hin; pose proof (H lo hi Hin) as Hl; unfold AC.GT in Hl;
    unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
      RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN; lia.
Qed.

(* Every FakeStack metadata cell is at or above FS. *)
Lemma f3_fs_meta_lo : forall FS q, fs_meta FS q -> FS <= q.
Proof.
  intros FS q H. unfold fs_meta in H.
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* The shadow byte k of the frame base is the shadow of the frame byte fr + 8k. *)
Lemma f3_fr_sh : forall fr k, shadow_addr (fr + 8 * k) = Sfr fr + k.
Proof.
  intros fr k. unfold Sfr, shadow_addr.
  replace (fr + 8 * k) with (fr + k * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.

(* An app byte never falls in the shadow of an app range. *)
Lemma f3_app_out_sh : forall x lo hi, app_mem x -> 0 <= lo -> 0 <= hi <= APPMEM_END ->
  ~ (shadow_addr lo <= x < shadow_addr hi).
Proof.
  intros x lo hi Hx Hlo Hhi HC. pose proof (f3_sh_lo lo Hlo). pose proof (f3_sh_hi_le hi Hhi).
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

(* Every registered global lies in the image, below AC.GT: checked by computation over AF.frame_AG. *)
Definition f3_ag_ok : bool :=
  forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? AC.GT)) AF.frame_AG.

Lemma f3_ag_true : f3_ag_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f3_ag_lt : forall a, in_globals AF.frame_AG a -> 0 <= a < AC.GT.
Proof.
  intros a (lo & n & Hin & Hr).
  pose proof (proj1 (forallb_forall _ _) f3_ag_true (lo, n) Hin) as H.
  apply andb_prop in H as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2. cbn in H1, H2. lia.
Qed.

(* One byte of an addressable range. *)
Lemma f3_addr1 : forall m p n a, addressable m p n -> p <= a < p + n -> addressable m a 1.
Proof.
  intros m p n a (H0 & Hn & Hhi & Hall) Hx.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + i) with (p + (a - p + i)) by lia. apply Hall. lia.
Qed.

(* A byte of a CB cell is present. *)
Lemma f3_cell_byte : forall m a n bs x, rw_cells rsegs m a [CB n bs] -> a <= x < a + Z.of_nat n ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m a n bs x ((Hwf & Hb) & _) Hx.
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  destruct Hwf as (Hlen & _). cbn [cell_wf] in Hlen.
  destruct Hb as (H0 & H1 & Hall).
  assert (Hi : (Z.to_nat (x - a) < length bs)%nat) by (rewrite Hlen; lia).
  pose proof (Hall (Z.to_nat (x - a)) Hi) as Hm.
  rewrite Z2Nat.id in Hm by lia. replace (a + (x - a)) with x in Hm by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:E;
    [exists b; exact Hm | apply nth_error_None in E; lia].
Qed.

(* ---- the five frame shadow bytes ---- *)

(* The five frame shadow bytes the 0x81e54 block writes (s3+22..s3+26, s3 = S(fr)): the shadow of the 36 parse
   output cells [fr + 176, fr + 212) and of the rest of their last granule. *)
Definition f3_Wsh (fr : Z) : list (Z * Z) := [(Sfr fr + 22, Sfr fr + 27)].

Lemma f3_Wsh_cases : forall fr x, Frame.outside (f3_Wsh fr) x \/ (Sfr fr + 22 <= x < Sfr fr + 27).
Proof.
  intros fr x. unfold f3_Wsh. cbn [Frame.outside].
  destruct (Z_le_gt_dec (Sfr fr + 22) x); [destruct (Z_lt_ge_dec x (Sfr fr + 27))|].
  - right; lia.
  - left. split; [lia | exact I].
  - left. split; [lia | exact I].
Qed.

(* Any app byte is outside the five frame shadow bytes (they lie in the shadow, between LOWMEM_END and
   HIGHMEM_BEG). *)
Lemma f3_Wsh_app : forall fr x, 0 <= fr -> fr + 216 <= APPMEM_END -> app_mem x -> Frame.outside (f3_Wsh fr) x.
Proof.
  intros fr x H0 H1 Hx. unfold f3_Wsh. cbn [Frame.outside]. split; [|exact I]. intros HC.
  pose proof (f3_sh_lo fr H0) as L1. pose proof (f3_sh_hi_le (fr + 216) ltac:(lia)) as L2.
  assert (E : shadow_addr (fr + 216) = Sfr fr + 27).
  { unfold Sfr, shadow_addr. replace (fr + 216) with (fr + 27 * 8) by lia. rewrite Z.div_add by lia. lia. }
  unfold Sfr in HC. rewrite E in L2. unfold Sfr in L2.
  unfold app_mem in Hx. lia.
Qed.

(* The 36 output cells [fr+176, fr+212) are addressable once the five frame shadow bytes mark them. *)
Lemma f3_addr_o : forall m fr, 0 <= fr -> fr mod 32 = 0 ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) -> fr + 216 <= APPMEM_END ->
  bytes_at rsegs m (Sfr fr + 22) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] ->
  addressable m (fr + 176) 36.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros m fr H0 Hm32 Happ Hend Hbs.
  assert (Hm8 : fr mod 8 = 0) by (Z.div_mod_to_equations; lia).
  pose proof Hbs as (Hb0 & Hbl & Hb).
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. unfold addr_byte. split; [apply Happ; lia|].
  assert (Hi8lo : 0 <= i / 8) by (apply Z.div_pos; lia).
  assert (Hi8hi : i / 8 <= 4) by (Z.div_mod_to_equations; lia).
  assert (Hshadow : shadow_addr (fr + 176 + i) = Sfr fr + 22 + i / 8).
  { unfold Sfr, shadow_addr.
    assert (E : (fr + 176 + i) / 8 = fr / 8 + 22 + i / 8) by (Z.div_mod_to_equations; lia).
    rewrite E. lia. }
  set (gi := Z.to_nat (i / 8)).
  assert (Hgeq : i / 8 = Z.of_nat gi) by (unfold gi; rewrite Z2Nat.id by lia; reflexivity).
  pose proof (Hb gi ltac:(cbn [length]; unfold gi; lia)) as HE.
  rewrite Hshadow, Hgeq.
  assert (Hmod : (fr + 176 + i) mod 8 = i mod 8) by (Z.div_mod_to_equations; lia).
  destruct gi as [|[|[|[|[|gi]]]]]; cbn [nth_error] in HE;
    try (exfalso; rewrite Hgeq in Hi8hi; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi8hi; lia).
  - exists (Z_to_bv 8 0). split; [exact HE|]. left. reflexivity.
  - exists (Z_to_bv 8 0). split; [exact HE|]. left. reflexivity.
  - exists (Z_to_bv 8 0). split; [exact HE|]. left. reflexivity.
  - exists (Z_to_bv 8 0). split; [exact HE|]. left. reflexivity.
  - exists (Z_to_bv 8 4). split; [exact HE|].
    right. assert (Hsgn : bv_signed (Z_to_bv 8 4) = 4) by (vm_compute; reflexivity).
    rewrite Hsgn. split; [|lia].
    assert (Hieq : i / 8 = 4) by (rewrite Hgeq; reflexivity).
    assert (i mod 8 < 4) by (Z.div_mod_to_equations; lia). lia.
Qed.

(* The new 392-byte frame shadow list after the five stores. *)
Lemma f3_shnew : forall W fr mem mem' sh l5,
  bytes_at rsegs mem (Sfr fr) sh -> length sh = (Z.to_nat FRAME_SHADOW) -> Frame.munch W mem mem' ->
  (forall x, Sfr fr <= x < Sfr fr + 22 -> Frame.outside W x) ->
  (forall x, Sfr fr + 27 <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x) ->
  bytes_at rsegs mem' (Sfr fr + 22) l5 -> length l5 = 5%nat ->
  bytes_at rsegs mem' (Sfr fr) (firstn 22 sh ++ l5 ++ skipn 27 sh) /\
  length (firstn 22 sh ++ l5 ++ skipn 27 sh) = (Z.to_nat FRAME_SHADOW).
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros W fr mem mem' sh l5 Hsh Hlen MU Hlo Hhi H5 Hl5.
  assert (L22 : length (firstn 22 sh) = 22%nat) by (rewrite firstn_length_le; lia).
  assert (L27 : length (skipn 27 sh) = 365%nat) by (rewrite length_skipn; lia).
  split; [|rewrite !length_app, L22, Hl5, L27; reflexivity].
  pose proof Hsh as Hsh1. rewrite <- (firstn_skipn 22 sh) in Hsh1.
  apply Mem.bytes_at_app in Hsh1. destruct Hsh1 as (Hf & _).
  pose proof Hsh as Hsh2. rewrite <- (firstn_skipn 27 sh) in Hsh2.
  apply Mem.bytes_at_app in Hsh2. destruct Hsh2 as (_ & Hs).
  rewrite firstn_length_le in Hs by lia. change (Z.of_nat 27) with 27 in Hs.
  apply Mem.bytes_at_app. split.
  - eapply fl_bytes; [exact Hf | exact MU |]. rewrite L22. change (Z.of_nat 22) with 22.
    intros x Hx. apply Hlo. lia.
  - rewrite L22. change (Z.of_nat 22) with 22. apply Mem.bytes_at_app. split; [exact H5|].
    rewrite Hl5. change (Z.of_nat 5) with 5. replace (Sfr fr + 22 + 5) with (Sfr fr + 27) by lia.
    eapply fl_bytes; [exact Hs | exact MU |]. rewrite L27. change (Z.of_nat 365) with 365.
    intros x Hx. apply Hhi. lia.
Qed.

(* store_ok at an explicit address b inside a carried writable range [a, a + n). *)
Lemma f3_sok_at : forall m a n (j : nat) b,
  wr_at rsegs m a n -> 0 <= b - a -> (b - a) + Z.of_nat j <= n ->
  store_ok rsegs m (wa b) j = true.
Proof.
  intros m a n j b H H1 H2.
  replace b with (a + (b - a)) by lia.
  exact (wr_at_store_ok rsegs m a n (b - a) j H H1 H2).
Qed.

(* store_ok for the current memory at the exact address the engine computes. *)
Ltac f3_sokb W b n :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let H := fresh "HS" in
      assert (H : store_ok rsegs mm (wa b) n = true)
        by (eapply (f3_sok_at mm _ _ n b); [repeat apply wr_at_write; exact W | lia | lia])
  end.

Ltac f3_bw :=
  repeat (apply bytes_at_write_other; [ | lia | simpl_sizes; lia | simpl_sizes; lia]).

(* 0x81e54-0x81e70: the spill of s7 + 18 to [s1 + 192] and the five frame shadow bytes. *)


(* AH, ownership and the stack bounds across the five frame shadow bytes: real arm by a_laws_store (each written
   byte is the shadow of a frame byte, a real-stack byte above stklo); side arm by a_fs_ok_store_AH (the frame lies
   in FS, the written bytes are shadows of FS bytes, and they are not app memory, so not metadata). *)
Lemma f3_fr_ah : forall g fr hb regs mem mem' md,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch (f3_Wsh fr) mem mem' -> Frame.wmono rsegs mem mem' ->
  (forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) -> exists b, mbyte rsegs mem' q = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  (forall q, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md q <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md q) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem mem' md HFRA MU WM HPRES.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  assert (Hw2 : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a _ Hw; exact (WM (Z_to_bv 64 a) Hw)).
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha. unfold APPMEM_END. destruct Ha as [Ha|Ha]; lia. }
  unfold AC.GT in Hgt.
  destruct Hloc as [(_ & _ & Hreal)|(_ & _ & Hfs & _)].
  - (* real arm: every written address is a_store_ok *)
    assert (P1 : forall a, 0 <= a < 2 ^ 64 ->
              ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
              mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hn. apply MU. rewrite MState.unsigned_lit by exact Ha.
      destruct (f3_Wsh_cases fr a) as [Ho | Hb]; [exact Ho | exfalso].
      apply Hn. unfold AC.a_store_ok. right; right; right. exists (fr + 8 * (a - Sfr fr)).
      split; [rewrite f3_fr_sh; lia | right; left; apply Hreal; lia]. }
    exact (AC.a_laws_store _ _ _ _ _ LAWS (hb ++ g_H g) mem mem' md HAH P1 Hw2).
  - (* side arm: the FS word at tp, the frame inside FS *)
    destruct (Hfs fr ltac:(lia)) as (b & Hbr & Hwb & Hbin).
    destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (b' & Hbr' & Hwb' & Hbin').
    assert (Ebb : b' = b).
    { pose proof (f3_wm_eq _ _ _ _ Hwb' Hwb) as E. rewrite !Z.mod_small in E by lia. exact E. }
    subst b'.
    pose proof (AC.a_laws_fs_place _ _ _ _ _ LAWS _ _ _ b HAH Hwb Hbr) as (_ & Hstkb & _ & Happfs).
    assert (Hsz : b + AC.FS_SIZE <= 2 ^ 64) by (unfold AC.FS_SIZE, AF.SLOT_STACK, APPMEM_END in *; lia).
    assert (Hmeta : forall q, fs_meta b q -> Frame.outside (f3_Wsh fr) q).
    { intros q Hq. pose proof (fs_meta_below b q Hq) as Hq1. pose proof (f3_fs_meta_lo b q Hq) as Hq0.
      assert (Hqa : app_mem q) by (apply Happfs; unfold AC.FS_SIZE; lia).
      destruct (f3_Wsh_cases fr q) as [Ho | Hb]; [exact Ho | exfalso].
      apply (AsanRTFacts.app_not_shadow q Hqa).
      replace q with (shadow_addr (fr + 8 * (q - Sfr fr))) by (rewrite f3_fr_sh; lia).
      apply AsanRTFacts.shadow_of_app, Happ. lia. }
    assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
              ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
              ~ (b <= q < b + AC.FS_SIZE) ->
              ~ (exists c, b <= c < b + AC.FS_SIZE /\ q = shadow_addr c) ->
              mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq _ Hnr Hnsh. apply MU. rewrite MState.unsigned_lit by exact Hq.
      destruct (f3_Wsh_cases fr q) as [Ho | Hb]; [exact Ho | exfalso].
      apply Hnsh. exists (fr + 8 * (q - Sfr fr)).
      split; [unfold AC.FS_SIZE in *; lia | rewrite f3_fr_sh; lia]. }
    exact (a_fs_ok_store_AH AC.ASYMS _ _ _ _ (f3_Wsh fr) (hb ++ g_H g) mem mem' md b LAWS HAH Hwb Hbr Hsz MU
      Hw2 HPRES Hmeta Hagree).
Qed.

(* FRA and ENT across the five frame shadow bytes [S(fr)+22, S(fr)+27): sl_fr_meta with the new 392-byte shadow
   list, and ent_store (the bytes are frame shadow bytes). *)
Lemma f3_fra_sh : forall g fr hb regs mem mem' md,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  Frame.munch (f3_Wsh fr) mem mem' -> Frame.wmono rsegs mem mem' ->
  bytes_at rsegs mem' (Sfr fr + 22) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] ->
  FRA B APIf ra g fr hb regs mem' md /\ ENT APIf g hb mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem mem' md HFRA HENT MU WM H5.
  assert (HPRES : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                    exists b, mbyte rsegs mem' q = Some b).
  { intros q Hq Hb. destruct (f3_Wsh_cases fr q) as [Ho | Hin].
    - rewrite (KindBGlue.mbyte_munch rsegs (f3_Wsh fr) mem mem' q MU Hq Ho). exact Hb.
    - apply (f3_pres_at mem' (Sfr fr + 22) _ q H5). cbn [length]. lia. }
  destruct (f3_fr_ah g fr hb regs mem mem' md HFRA MU WM HPRES) as (HAH' & Hown & HSTK & HSTKhi).
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ HAH) as Hhi.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (Hub : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Happ; lia).
    unfold app_mem in Ha. destruct Ha as [Ha|Ha]; lia. }
  assert (Hfr0 : 0 <= fr) by lia.
  assert (HSfr : LOWMEM_END <= Sfr fr /\ Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. }
  assert (Hout : forall x, (x < Sfr fr + 22 \/ Sfr fr + 27 <= x) -> Frame.outside (f3_Wsh fr) x).
  { intros x Hx. unfold f3_Wsh. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = A).
  { intros A' HA' HA'r. apply f3_id; [lia | lia |]. rewrite <- HA'. exact Hr9. }
  assert (HRO : ro_agree rsegs mem').
  { apply (sl_ro_keep (f3_Wsh fr) mem mem' Hro MU). intros x Hx. apply Hout. left. lia. }
  split.
  - apply (sl_fr_meta B APIf ra empty FF g fr hb regs regs mem mem' md (f3_Wsh fr) HFRA MU WM HRO).
    + apply f3_rt. intros lo hi Hin. unfold f3_Wsh in Hin. cbn [In] in Hin.
      destruct Hin as [E|[]]. injection E as <- <-. lia.
    + exact HAH'.
    + exact HSTK.
    + exact Happ.
    + exact Hgt.
    + destruct Hsh as (sh & Hbytes & Hlen).
      exists (firstn 22 sh ++ [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] ++ skipn 27 sh).
      apply (f3_shnew (f3_Wsh fr) fr mem mem' sh _ Hbytes Hlen MU).
      * intros x Hx. apply Hout. left. lia.
      * intros x Hx. apply Hout. right. lia.
      * exact H5.
      * reflexivity.
    + intros x _ _ Hns. apply Hout. lia.
    + intros A' HA' HA'r x Hx. rewrite (HA9 A' HA' HA'r) in Hx. apply Hout. right. lia.
    + intros x Hx. apply Hout. right. lia.
    + intros A' HA' HA'r x Hx. rewrite (HA9 A' HA' HA'r) in Hx. apply Hout. right. lia.
    + intros x Hx. left. apply Hout. right. lia.
    + intros a Ha. pose proof (f3_ag_lt a Ha) as Hab.
      apply (addr1_munch (f3_Wsh fr) mem mem' a MU); [|exact (HAG a Ha)].
      apply Hout. left. pose proof (f3_sh_mono a fr ltac:(lia)). unfold Sfr. lia.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - eapply ent_store with (W := f3_Wsh fr); [exact HENT | exact HFRA | exact MU | | exact HSTK | exact HSTKhi |].
    + intros x Hx. destruct (f3_Wsh_cases fr x) as [Ho|Hin]; [left; exact Ho | right; right; right; lia].
    + intros a _ Ho. exact (proj2 (Hown a) Ho).
Qed.

(* ---- the parse call's write set ---- *)

Lemma f3_fsc : forall FS, fs_hint FS 1 = FS + 8 /\ fs_flag FS 1 0 = FS + 20480 /\ fs_M 1 = 8192 /\
  fs_frame FS 1 0 = FS + 1085440 /\ fs_frame FS 1 (fs_M 1) = FS + 2134016.
Proof.
  intros FS. unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B.
  change (Z.of_nat 1) with 1. change (2 ^ (15 - 1)) with 16384. change (2 ^ (14 - 1)) with 8192.
  repeat split; lia.
Qed.

Lemma f3_fpw1 : forall FS, fp_w [1%nat] FS =
  [(FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016))].
Proof.
  intros FS. unfold fp_w, fp_w1. cbn [flat_map app].
  destruct (f3_fsc FS) as (F1 & F2 & F3 & F4 & F5).
  rewrite F5, F4, F1, F2, F3.
  replace (FS + 8 + 8) with (FS + 16) by lia. replace (FS + 20480 + 8192) with (FS + 28672) by lia.
  reflexivity.
Qed.

Lemma f3_fs_frame0 : forall FS, fs_frame FS 0%nat 0 = FS + 36864.
Proof.
  intros FS. unfold fs_frame, fs_B. cbn [Z.of_nat]. change (2 ^ 20) with 1048576.
  change (2 ^ 0) with 1. lia.
Qed.

Lemma f3_afs_flag1 : forall FS j, AC.a_fs_flag FS 1%nat j = FS + 20480 + j.
Proof.
  intros FS j. unfold AC.a_fs_flag.
  change (2 ^ (15 - Z.of_nat 1)) with 16384. change (2 ^ 15) with 32768. lia.
Qed.

(* A flag byte of a class other than 1 lies at or above FS + 4096 and apart from the class-1 flag bytes
   [FS + 20480, FS + 28672). *)
Lemma f3_flag_other : forall FS c j, (c <= 10)%nat -> c <> 1%nat -> 0 <= j < AC.a_fs_M c ->
  FS + 4096 <= AC.a_fs_flag FS c j /\ (AC.a_fs_flag FS c j < FS + 20480 \/ FS + 28672 <= AC.a_fs_flag FS c j).
Proof.
  intros FS c j Hc Hc1 Hj. unfold AC.a_fs_flag, AC.a_fs_M in *.
  destruct c as [|[|c]].
  - change (2 ^ (14 - Z.of_nat 0)) with 16384 in Hj. change (2 ^ (15 - Z.of_nat 0)) with 32768. lia.
  - exfalso. apply Hc1. reflexivity.
  - assert (P : 2 ^ (15 - Z.of_nat (S (S c))) <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* The writes of the parse call (its munch list) with o <> 0. *)
Definition f3_PW (o S FS : Z) : list (Z * Z) :=
  reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
  [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)].

Lemma f3_PW_eq : forall o S FS, o <> 0 -> f3_PW o S FS =
  [(o, o + 36); (S - 8800, S); (FS + 8, FS + 16); (FS + 20480, FS + 28672); (FS + 1085440, FS + 2134016);
   (shadow_addr (FS + 1085440), shadow_addr (FS + 2134016)); (shadow_addr (S - 8800), shadow_addr S)].
Proof.
  intros o S FS Ho. unfold f3_PW, reac_ctrl_parse_fp, REAC_CTRL_PARSE_K.
  replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ho).
  rewrite f3_fpw1. cbn [app]. reflexivity.
Qed.

Lemma f3_PW_out : forall o S FS x, o <> 0 ->
  ~ (o <= x < o + 36) -> ~ (S - 8800 <= x < S) -> ~ (FS + 8 <= x < FS + 16) ->
  ~ (FS + 20480 <= x < FS + 28672) -> ~ (FS + 1085440 <= x < FS + 2134016) ->
  ~ (shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016)) ->
  ~ (shadow_addr (S - 8800) <= x < shadow_addr S) ->
  Frame.outside (f3_PW o S FS) x.
Proof.
  intros o S FS x Ho N1 N2 N3 N4 N5 N6 N7. rewrite (f3_PW_eq o S FS Ho). cbn [Frame.outside].
  repeat split; try exact I; assumption.
Qed.

(* An app byte apart from the three app ranges of the write set is outside it. *)
Lemma f3_PW_out_app : forall o S FS x, o <> 0 -> app_mem x -> 0 <= FS -> FS + 2134016 <= APPMEM_END ->
  0 <= S - 8800 -> S <= APPMEM_END ->
  ~ (o <= x < o + 36) -> ~ (S - 8800 <= x < S) -> ~ (FS + 8 <= x < FS + 16) ->
  ~ (FS + 20480 <= x < FS + 28672) -> ~ (FS + 1085440 <= x < FS + 2134016) ->
  Frame.outside (f3_PW o S FS) x.
Proof.
  intros o S FS x Ho Hx HF0 HF1 HS0 HS1 N1 N2 N3 N4 N5.
  apply f3_PW_out; try assumption; apply f3_app_out_sh; (assumption || lia).
Qed.

(* The shadow byte of an app byte y is outside the write set when y is apart, granule by granule, from the
   class-1 frames and from the callee window, and the app ranges are in the app halves. *)
Lemma f3_PW_out_sh : forall o S FS y, o <> 0 -> 0 <= y < APPMEM_END ->
  (o + 36 <= LOWMEM_END \/ HIGHMEM_BEG <= o) -> HIGHMEM_BEG <= S - 8800 ->
  (FS + 2134016 <= LOWMEM_END \/ HIGHMEM_BEG <= FS + 8) -> 0 <= FS -> FS mod 8 = 0 -> (S - 8800) mod 8 = 0 ->
  (y < FS + 1085440 \/ FS + 2134016 <= y) -> (y < S - 8800 \/ S <= y) ->
  Frame.outside (f3_PW o S FS) (shadow_addr y).
Proof.
  intros o S FS y Ho Hy Hoa HS HFa HF0 HF8 HS8 Hy1 Hy2.
  pose proof (f3_sh_lo y ltac:(lia)) as L1. pose proof (f3_sh_hi y Hy) as L2.
  apply f3_PW_out; [exact Ho | lia | lia | lia | lia | lia | |].
  - intros [H1 H2]. destruct Hy1 as [Hy1|Hy1].
    + pose proof (f3_sh_lt2 y (FS + 1085440) ltac:(lia) Hy1 ltac:(Z.div_mod_to_equations; lia)). lia.
    + pose proof (f3_sh_mono (FS + 2134016) y Hy1). lia.
  - intros [H1 H2]. destruct Hy2 as [Hy2|Hy2].
    + pose proof (f3_sh_lt2 y (S - 8800) ltac:(lia) Hy2 HS8). lia.
    + pose proof (f3_sh_mono S y Hy2). lia.
Qed.

Lemma f3_PW_lo : forall o S FS lo hi, o <> 0 -> AC.GT <= o -> AC.GT <= FS -> AC.GT + 8800 <= S ->
  In (lo, hi) (f3_PW o S FS) -> AC.GT <= lo.
Proof.
  intros o S FS lo hi Ho H1 H2 H3 Hin. rewrite (f3_PW_eq o S FS Ho) in Hin.
  unfold AC.GT, shadow_addr, ASAN_K in *. cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-;
    first [lia | (assert (0 <= (FS + 1085440) / 8) by (apply Z.div_pos; lia); lia)
               | (assert (0 <= (S - 8800) / 8) by (apply Z.div_pos; lia); lia)] |]); contradiction.
Qed.

(* ---- the side-stack premises of the parse call, built from the base (after Seg/F9.v's f9_fp_call) ---- *)

Lemma f3_dj_pt : forall (Q : Z -> Prop) a b c d, a < b -> c < d ->
  (forall x, a <= x < b -> Q x) -> (forall x, c <= x < d -> ~ Q x) -> RcLay.ly_dj a b c d.
Proof.
  intros Q a b c d Hab Hcd HQ HnQ. unfold RcLay.ly_dj.
  destruct (Z_le_gt_dec b c) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec d a) as [H2|H2]; [right; exact H2|].
  exfalso. apply (HnQ (Z.max a c) ltac:(lia)). apply HQ. lia.
Qed.

Lemma f3_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (f3_byte_range b) as Hb.
  assert (HR : 0 <= bytes_le_to_Z bs).
  { rewrite bytes_le_to_Z_le_val. exact (proj1 (le_val_range _ (bytes_ok_map bs))). }
  rewrite lor_shiftl8_add by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2 ^ 8)%Z.
    change (2 ^ 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
    rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.

Lemma f3_le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs L. unfold le8, word_to_le_bytes. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z_to_le_bytes_mod by (cbn; lia).
  rewrite <- L at 1. apply f3_le_bytes_to_Z.
Qed.

Lemma f3_byte_at : forall m a b, 0 <= a -> a + 1 <= 2 ^ 64 -> mbyte rsegs m a = Some b ->
  bytes_at rsegs m a [b].
Proof.
  intros m a b H0 H1 Hb. split; [exact H0|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i.
  cbn [nth_error]. replace (a + Z.of_nat 0) with a by lia. exact Hb.
Qed.

Lemma f3_bytes_PN : forall (P : byte -> Prop) m a k, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> exists b, mbyte rsegs m (a + i) = Some b /\ P b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = k /\ Forall P bs.
Proof.
  intros P m a k. revert a. induction k as [|k IH]; intros a H0 H1 H.
  - exists []. split; [|split; [reflexivity | constructor]].
    split; [exact H0|]. split; [cbn [length]; lia|]. intros i Hi; cbn [length] in Hi; lia.
  - destruct (H 0 ltac:(lia)) as (b & Hb & HPb).
    assert (Hrec : forall i, 0 <= i < Z.of_nat k -> exists b', mbyte rsegs m (a + 1 + i) = Some b' /\ P b').
    { intros i Hi. destruct (H (1 + i) ltac:(lia)) as (b' & Hb' & HP'). exists b'.
      split; [|exact HP']. replace (a + 1 + i) with (a + (1 + i)) by lia. exact Hb'. }
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) Hrec) as (bs & Hbs & Hlen & HPbs).
    exists (b :: bs). split; [|split; [cbn [length]; lia | constructor; assumption]].
    destruct Hbs as (_ & _ & Hnth).
    split; [exact H0|]. split; [cbn [length]; rewrite Hlen; lia|].
    intros i Hi. destruct i as [|i]; cbn [nth_error].
    + replace (a + Z.of_nat 0) with (a + 0) by lia. exact Hb.
    + replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
      apply Hnth. cbn [length] in Hi. lia.
Qed.

Lemma f3_bytes_P : forall (P : byte -> Prop) m a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> exists b, mbyte rsegs m (a + i) = Some b /\ P b) ->
  exists bs, bytes_at rsegs m a bs /\ Z.of_nat (length bs) = n /\ Forall P bs.
Proof.
  intros P m a n H0 Hn H1 H.
  destruct (f3_bytes_PN P m a (Z.to_nat n) H0 ltac:(rewrite Z2Nat.id by lia; lia)
              ltac:(rewrite Z2Nat.id by lia; exact H)) as (bs & Hbs & Hlen & HP).
  exists bs. split; [exact Hbs|]. split; [rewrite Hlen, Z2Nat.id by lia; reflexivity | exact HP].
Qed.

Lemma f3_word_present : forall m a, 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, 0 <= i < 8 -> exists b, mbyte rsegs m (a + i) = Some b) ->
  exists w : word, bytes_at rsegs m a (le8 w).
Proof.
  intros m a H0 H1 H.
  assert (HP : forall i, 0 <= i < 8 -> exists b, mbyte rsegs m (a + i) = Some b /\ True).
  { intros i Hi. destruct (H i Hi) as (b & Hb). exists b. split; [exact Hb | exact I]. }
  destruct (f3_bytes_P (fun _ => True) m a 8 H0 ltac:(lia) H1 HP) as (bs & Hbs & Hlen & _).
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite f3_le8_of_bytes by lia. exact Hbs.
Qed.

Ltac f3_num :=
  cbv [RcLay.ly_dj TLS_INDEX REAL_TLS_GET_ADDR TSD_KEY_INITED TSD_KEY
       asan_stack_malloc_c.GOT_CF asan_stack_malloc_c.CF bcmp_wrap_c.GOT_CF bcmp_wrap_c.CF
       GOT_VERBOSITY VERBOSITY DTLS_TPOFF
       RT_TP RT_TSDMAIN RT_GT ASAN_GT AC.as_tp AC.ASYMS AC.GT AC.FS_SIZE FS_SIZE RT_FS_SIZE
       REAC_CTRL_PARSE_K AF.SLOT_STACK FN_STACK HIGHMEM_BEG APPMEM_END LOWMEM_END LOWSHADOW_END HIGHSHADOW_BEG
       ASAN_K] in *; lia.

Ltac f3_dj_split := repeat first [apply Forall_nil | apply Forall_cons]; cbn [fst snd].


(* ---- the call on the normalized memory (MemNorm): the contract asks for mem_inv, which no cut carries ---- *)

(* The image's segments all end at or below GT, so no address at or above it is read-only. *)
Definition f3_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Lemma f3_tops_gt : f3_tops rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f3_find_below : forall segs top x n s,
  f3_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold f3_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma f3_ro_gt : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (f3_find_below sg 0x5fe000 x n s f3_tops_gt E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

Lemma f3_stk_rel : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo ->
  stk rsegs m lo hi -> stk rsegs m0 lo hi.
Proof.
  intros m m0 lo hi HR Hlo (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (f3_ro_gt a ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f3_stk_back : forall m m0 lo hi, mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR (H0 & H1 & H). split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (ro_false_of_wview rsegs m m0 (wa a) HR Hw)). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f3_shrw_rel : forall m m0, mem_rel rsegs m m0 -> shadow_rw m -> shadow_rw m0.
Proof.
  intros m m0 HR H a Ha. pose proof (in_shadow_range a Ha) as Hr.
  destruct (H a Ha) as (Hw & b & Hb).
  assert (Hlo : 0x5fe000 <= a) by (unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha; lia).
  split.
  - rewrite (wview_rel_rw rsegs m m0 (wa a) HR (f3_ro_gt a ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f3_shrw_back : forall m m0, mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_rw rsegs m m0 (wa a) HR (ro_false_of_wview rsegs m m0 (wa a) HR Hw)). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f3_addr_rel : forall m m0 p n, mem_rel rsegs m m0 -> addressable m p n -> addressable m0 p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite <- (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma f3_addr_back : forall m m0 p n, mem_rel rsegs m m0 -> addressable m0 p n -> addressable m p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Ltac f3_ba_rel R :=
  first [ apply (proj1 (bytes_at_rel rsegs _ _ _ _ R)); assumption
        | apply (proj2 (bytes_at_rel rsegs _ _ _ _ R)); assumption ].

Lemma f3_cells_rel : forall m m0, mem_rel rsegs m m0 -> asan_cells m -> asan_cells m0.
Proof.
  intros m m0 R H. unfold asan_cells in H |- *.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end; f3_ba_rel R.
Qed.

Lemma f3_tls_rel : forall m m0 TP DT TS C T DB k, mem_rel rsegs m m0 ->
  (asan_tls_cells m TP DT TS C T DB k <-> asan_tls_cells m0 TP DT TS C T DB k).
Proof.
  intros m m0 TP DT TS C T DB k R. unfold asan_tls_cells.
  split; intros (H1 & H2 & H3 & H4 & H5 & Hk & H7 & H8 & H9 & H10 & (tb & te & H11) & H12 & H13 & H14 & H15
                 & H16 & H17 & HDB & H19).
  all: split; [f3_ba_rel R|]. all: split; [f3_ba_rel R|]. all: split; [f3_ba_rel R|].
  all: split; [f3_ba_rel R|]. all: split; [f3_ba_rel R|]. all: split; [exact Hk|].
  all: split; [f3_ba_rel R|]. all: split; [f3_ba_rel R|]. all: split; [f3_ba_rel R|].
  all: split; [f3_ba_rel R|]. all: split; [exists tb, te; f3_ba_rel R|].
  all: split; [f3_ba_rel R|]. all: split; [f3_ba_rel R|]. all: split; [f3_ba_rel R|].
  all: split; [f3_ba_rel R|]. all: split; [f3_ba_rel R|]. all: split; [f3_ba_rel R|].
  all: split; [exact HDB|]. all: f3_ba_rel R.
Qed.

Lemma f3_cls_rel : forall m m0 FS c, mem_rel rsegs m m0 -> (fp_cls m FS c <-> fp_cls m0 FS c).
Proof.
  intros m m0 FS c R. unfold fp_cls.
  split; intros (Hc & h & fl & Hh & Hf & Hl & Hb); (split; [exact Hc|]); exists h, fl;
    (split; [f3_ba_rel R|]); (split; [f3_ba_rel R|]); (split; [exact Hl | exact Hb]).
Qed.

Lemma f3_fp_rel : forall cs m m0 TP FS lo hi W D, mem_rel rsegs m m0 ->
  fp cs m TP FS lo hi W D -> fp cs m0 TP FS lo hi W D.
Proof.
  intros cs m m0 TP FS lo hi W D R
    (DT & TS & C & T & DB & k & Htls & Htp & Hpl & H88 & H96 & Hcls & Hlo & Happ & Hw & Hd).
  exists DT, TS, C, T, DB, k.
  split; [exact (proj1 (f3_tls_rel m m0 TP DT TS C T DB k R) Htls)|].
  split; [f3_ba_rel R|].
  split.
  { destruct Hpl as (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
    split; [exact P4|]. apply (f3_stk_rel m m0 FS (FS + FS_SIZE) R); [unfold ASAN_GT in P3; lia | exact P5]. }
  split; [f3_ba_rel R|]. split; [f3_ba_rel R|].
  split.
  { eapply Forall_impl; [|exact Hcls]. intros c Hc. exact (proj1 (f3_cls_rel m m0 FS c R) Hc). }
  split; [exact Hlo|]. split; [exact Happ|]. split; [exact Hw | exact Hd].
Qed.


(* 0x81dd0-0x81de8: s9 = s7 + 18 and the five frame shadow bytes. *)
Lemma f3_st :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2i s4 s5 s6 s8 s9i s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (fr phi : Z),
    0 <= fr -> 0 <= Sfr fr -> 0 <= phi < 2 ^ 64 -> Sfr fr + 27 <= 2 ^ 64 ->
    wr_at rsegs m (Sfr fr + 22) 5 ->
    LE.evt rsegs
      (fun ms => exists (m2 : word -> option byte) (a0' : word),
         ms = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0' a1i a2i a3 a4 a5 a6 a7 s2i
                      (Z_to_bv 64 (Sfr fr)) s4 s5 s6 (Z_to_bv 64 phi) s8 (Z_to_bv 64 (phi + 18)) s10 s11 t3 t4 t5 t6)
                 Fr (Z_to_bv 64 0x81dec) fc None m2 (seg_rom rsegs) /\
         Frame.munch (f3_Wsh fr) m m2 /\ Frame.wmono rsegs m m2 /\
         (forall lo hi, stk rsegs m lo hi -> stk rsegs m2 lo hi) /\
         bytes_at rsegs m2 (Sfr fr + 22) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4])
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2i
               (Z_to_bv 64 (Sfr fr)) s4 s5 s6 (Z_to_bv 64 phi) s8 s9i s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dd0) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0i a1i a2i a3 a4 a5 a6 a7 s2i s4 s5 s6 s8 s9i s10 s11 t3 t4 t5 t6
    Fr fc m fr phi Hfr0 HSfr0 Hphi HSfrhi Wsh.
  (* 0x81dd0 addi s9,s7,18 *)
  step.
  (* 0x81dd4 sb zero,22(s3) .. 0x81de0 sb zero,25(s3) *)
  f3_sokb Wsh (Sfr fr + 22) 1%nat. step.
  f3_sokb Wsh (Sfr fr + 23) 1%nat. step.
  f3_sokb Wsh (Sfr fr + 24) 1%nat. step.
  f3_sokb Wsh (Sfr fr + 25) 1%nat. step.
  (* 0x81de4 li a0,4 ; 0x81de8 sb a0,26(s3) *)
  step.
  f3_sokb Wsh (Sfr fr + 26) 1%nat. step.
  apply evt_done.
  eexists. eexists.
  split; [reflexivity|].
  split.
  { unfold f3_Wsh.
    repeat (apply munch_write; [ | lia | simpl_sizes; lia | cbn [inside]; simpl_sizes; lia ]).
    apply munch_refl. }
  split.
  { do 5 apply wmono_write. apply wmono_refl. }
  split.
  { intros lo hi Hs. do 5 (apply stk_write; [ | lia | simpl_sizes; lia ]). exact Hs. }
  apply f3_bytes_cons.
  { rewrite <- f3_le1_0. f3_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 22 + 1) with (Sfr fr + 23) by lia.
  apply f3_bytes_cons.
  { rewrite <- f3_le1_0. f3_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 23 + 1) with (Sfr fr + 24) by lia.
  apply f3_bytes_cons.
  { rewrite <- f3_le1_0. f3_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 24 + 1) with (Sfr fr + 25) by lia.
  apply f3_bytes_cons.
  { rewrite <- f3_le1_0. f3_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia]. }
  replace (Sfr fr + 25 + 1) with (Sfr fr + 26) by lia.
  rewrite <- f3_le1_4. f3_bw. apply bytes_at_write_same; [lia | simpl_sizes; lia].
Qed.


(* The run 0x81dec-0x81df8 and the call, on a memory where mem_inv holds (the normalized one): a0 = s7 = f,
   a1 = s2 = N, a2 = [A + 248] = o. *)
Lemma f3_call :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f N o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> o <> 0 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> mem_inv rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= N -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd N bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    (o <> 0 -> o mod 4 = 0 /\ o + 36 <= 2 ^ 64 /\ rw_cells rsegs m o [CB 36 junk] /\
       (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) /\ (50 <= N -> o + 36 <= f \/ f + 50 <= o)) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= N -> addressable m f 50) ->
    (o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f N o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse N bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81dfc) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse N bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         fp [1%nat] m' (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S)
            (reac_ctrl_parse_D f N o))
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dec) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f N o S FS bs junk Hf HN Ho Honz HS HS16 HSK HA0 HAhi HST HMI Hlen HRDcur Hbig HRD Hocell
    HAC HSW HHI HAPP HWA HFA Hoaddr HBC H1 H2 H3 H4 H5 HFP HTLS.
  (* 0x81dec mv a0,s7 ; 0x81df0 mv a1,s2 ; 0x81df4 ld a2,248(s1) ; 0x81df8 jal reac_ctrl_parse *)
  step. step. step. step.
  pose proof HPARSE as HP. unfold reac_ctrl_parse_contract, REAC_CTRL_PARSE in HP.
  eapply evt_cut.
  { eapply HP with (f := f) (n := N) (o := o) (S := S) (FS := FS) (fr := bs) (junk := junk);
      try reflexivity; try assumption; try lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m' &
    E & MU & WM & MI & ST & Hrw & Hac & HSW' & Hadr & FP & Htls).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x81dfc)) with (Z_to_bv 64 0x81dfc)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', tt3, tt4, tt5, tt6, m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact ST|]. split; [exact (Hrw Honz)|].
  split; [exact HSW'|]. split; [exact Hadr | exact FP].
Qed.

(* The same run on the real memory: the call goes through MemNorm.evt_normalize from ro_agree, every premise
   crosses mem_rel to the normalized memory, and the post comes back across mem_rel and ro_same. *)
Lemma f3_calln :
  forall (ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A f N o S FS : Z) (bs junk : list byte),
    0 <= f < 2 ^ 64 -> 0 <= N < 2 ^ 64 -> 0x5fe000 <= o -> o + 36 <= 2 ^ 64 -> S < 2 ^ 64 -> S mod 16 = 0 ->
    REAC_CTRL_PARSE_K <= S -> 0 <= A -> A + 256 <= 2 ^ 64 ->
    stk rsegs m (S - REAC_CTRL_PARSE_K) S -> ro_agree rsegs m -> length bs = 50%nat ->
    ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 o)) ->
    (50 <= N -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= S - REAC_CTRL_PARSE_K \/ S <= f)) ->
    (forall i, In i (cp_rd N bs) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error bs i) ->
    o mod 4 = 0 -> rw_cells rsegs m o [CB 36 junk] -> (o + 36 <= S - REAC_CTRL_PARSE_K \/ S <= o) ->
    (50 <= N -> o + 36 <= f \/ f + 50 <= o) ->
    asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= S - REAC_CTRL_PARSE_K -> S <= APPMEM_END ->
    addressable m (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
    (50 <= N -> addressable m f 50) ->
    addressable m o 36 -> app_mem (o + 36) -> (o + 36 <= GOT_CF \/ CF + 256 <= o) ->
    addressable m REAC_CTRL_PARSE_BC 6 ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    fp [1%nat] m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S (reac_ctrl_parse_W o S) (reac_ctrl_parse_D f N o) ->
    reac_ctrl_parse_tls m (bv_unsigned tp) FS (S - REAC_CTRL_PARSE_K) S ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81dfc) (Z_to_bv 64 S) gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 (fst (ctrlparse N bs))) a1' a2' a3' a4' a5' a6' a7'
                       (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x81dfc) fc None m' (seg_rom rsegs) /\
         munch (reac_ctrl_parse_fp o S ++ fp_w [1%nat] FS ++
                [(shadow_addr (S - REAC_CTRL_PARSE_K), shadow_addr S)]) m m' /\
         wmono rsegs m m' /\ ro_same rsegs m m' /\
         stk rsegs m' (S - REAC_CTRL_PARSE_K) S /\ rw_cells rsegs m' o [CB 36 (snd (ctrlparse N bs))] /\
         shadow_rw m' /\ addressable m' (S - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 1)
      (MS (mkR ra0 (Z_to_bv 64 S) gp tp t0 t1 t2 s0 (Z_to_bv 64 A) a0i a1i a2i a3 a4 a5 a6 a7
               (Z_to_bv 64 N) s3i s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81dec) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A f N o S FS bs junk Hf HN Ho Ho36 HS HS16 HSK HA0 HAhi HST HRO Hlen HRDcur Hbig HRD Ho4 Hocell
    Howin Howf HAC HSW HHI HAPP HWA HFA Hoaddr Hoapp HoCF HBC H1 H2 H3 H4 H5 HFP HTLS.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  set (m0 := normalize rsegs m) in REL.
  assert (HC := f3_call ra0 gp tp t0 t1 t2 s0 a0i a1i a2i a3 a4 a5 a6 a7 s3i s4 s5 s6 s8 s9 s10 s11
                  t3 t4 t5 t6 Fr fc m0 A f N o S FS bs junk Hf HN ltac:(lia) ltac:(lia) HS HS16 HSK HA0 HAhi).
  pose proof (f3_stk_rel m m0 (S - REAC_CTRL_PARSE_K) S REL ltac:(unfold REAC_CTRL_PARSE_K, HIGHMEM_BEG in *; lia) HST)
    as HST0.
  specialize (HC HST0 (mem_inv_normalize rsegs m) Hlen).
  specialize (HC ltac:(rewrite <- (ov_read_rel rsegs m m0 _ _ REL); exact HRDcur)).
  specialize (HC Hbig).
  specialize (HC ltac:(intros i Hi; rewrite <- (mrd_rel rsegs m m0 _ REL); exact (HRD i Hi))).
  specialize (HC ltac:(intros _; split; [exact Ho4|]; split; [lia|]; split;
    [ destruct Hocell as ((Hwf & Hb) & Hw); split; [split; [exact Hwf | f3_ba_rel REL]|];
      apply (wr_at_norm rsegs m m0 o _ REL Hw); intros i Hi; apply f3_ro_gt; cbn in Hi; lia
    | split; [exact Howin | exact Howf]])).
  specialize (HC (f3_cells_rel m m0 REL HAC) (f3_shrw_rel m m0 REL HSW) HHI HAPP (f3_addr_rel m m0 _ _ REL HWA)).
  specialize (HC ltac:(intros Hb; exact (f3_addr_rel m m0 _ _ REL (HFA Hb)))).
  specialize (HC ltac:(intros _; split; [exact (f3_addr_rel m m0 _ _ REL Hoaddr) | split; [exact Hoapp | exact HoCF]])).
  specialize (HC (f3_addr_rel m m0 _ _ REL HBC)).
  specialize (HC ltac:(f3_ba_rel REL) ltac:(f3_ba_rel REL) ltac:(f3_ba_rel REL) ltac:(f3_ba_rel REL)
                 ltac:(f3_ba_rel REL)).
  specialize (HC (f3_fp_rel _ m m0 _ _ _ _ _ _ REL HFP)).
  specialize (HC ltac:(intros DT TS C T DB k HT0; apply HTLS; exact (proj2 (f3_tls_rel m m0 _ DT TS C T DB k REL) HT0))).
  pose proof (evt_normalize rsegs _ _ Fr _ fc None m (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO HC) as HN0.
  eapply evt_mono; [exact HN0|].
  intros ms' (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m0' &
    E0 & MU0 & WM0 & ST0 & RW0 & SW0 & AD0 & FP0) & Hrel & Hro').
  subst s0'.
  destruct Hrel as (ER & EF & EP & ESv & ERes & EFc & ERom & HR').
  destruct ms' as [r' f' p' sv' rv' fc' m' ro'].
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ER, EF, EP, ESv, ERes, EFc,
    ERom, HR', Hro'.
  subst r' f' p' sv' rv' fc' ro'.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', tt3, tt4, tt5, tt6, m'.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m m0 m' m0' REL HR' Hro' MU0)|].
  split; [exact (wmono_rel rsegs m m0 m' m0' REL HR' Hro' WM0)|].
  split; [exact Hro'|].
  split; [exact (f3_stk_back m' m0' _ _ HR' ST0)|].
  split.
  { destruct RW0 as ((Hwf & Hb) & Hw). split; [split; [exact Hwf | f3_ba_rel HR']|].
    exact (wr_at_rel rsegs m' m0' o _ HR' Hw). }
  split; [exact (f3_shrw_back m' m0' HR' SW0)|].
  split; [exact (f3_addr_back m' m0' _ _ HR' AD0)|].
  destruct FP0 as (DT & TS & C & T & DB & k & _ & _ & Hpl & _ & _ & Hcls & _).
  split.
  { destruct Hpl as (_ & _ & _ & _ & P5). exact (f3_stk_back m' m0' _ _ HR' P5). }
  exact (proj2 (f3_cls_rel m' m0' FS 1 HR') (Forall_inv Hcls)).
Qed.


(* ---- FRA and ENT across the call ---- *)

(* FSREC moves across a write that misses its three cells (the tp word, the class-6 flag byte, the slot's last
   word). *)
Lemma f3_fsrec_keep : forall mem mem' W fr,
  FSREC fr mem -> Frame.munch W mem mem' ->
  (forall FS j x, word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 -> 0 <= j < 256 ->
     fr = FS + 6328320 + j * 4096 ->
     (x = FS + 36352 + j \/ fr + 4088 <= x < fr + 4096 \/ AC.as_tp AC.ASYMS <= x < AC.as_tp AC.ASYMS + 8) ->
     Frame.outside W x) ->
  FSREC fr mem'.
Proof.
  intros mem mem' W fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) MU HW.
  assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
  assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
  assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
  rewrite HM6 in Hj.
  assert (HO : forall x, (x = FS + 36352 + j \/ fr + 4088 <= x < fr + 4096 \/
                          AC.as_tp AC.ASYMS <= x < AC.as_tp AC.ASYMS + 8) -> Frame.outside W x)
    by (intros x Hx; exact (HW FS j x Htp HFSr Hj Hfrv Hx)).
  exists FS, j.
  split.
  { intros k Hk.
    assert (Hx : 0 <= AC.as_tp AC.ASYMS + Z.of_nat k < 2 ^ 64) by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
    assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))
                 = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))).
    { apply MU. rewrite MState.unsigned_lit by exact Hx. apply HO. right; right; lia. }
    unfold mbyte. rewrite Hm. exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { eapply fl_bytes; [exact Hflag | exact MU |].
    cbn [length]. intros x Hx. apply HO. left. lia. }
  { eapply fl_bytes; [exact Htail | exact MU |].
    rewrite length_le8. intros x Hx. apply HO. right; left. rewrite HB6 in Hx. lia. }
Qed.

(* The FRA rebuild across a run that may also write shadow bytes and side-stack bytes (the callee's class-1 frames):
   RT by RT_meta_write (every shadow byte readable after the run), AH / stklo, the window, FSREC, the registered
   globals and the slot window's addressability from the caller, the rest kept by fl_bytes (their addresses are
   outside W) and wmono (errno). The form of Tac_slot.sl_fr_meta's rebuild for a write outside the frame. *)
Lemma f3_fr_run : forall g fr hb regs mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch W mem mem' -> Frame.wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall x, fr <= x < fr + 24 -> Frame.outside W x) ->
  (forall x, 0 <= x < AC.GT -> Frame.outside W x) ->
  (forall A, rg regs 9 A -> 0 <= A < 2 ^ 64 -> forall x, A + 16 <= x < A + 312 -> Frame.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x) ->
  (forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  (FSREC fr mem -> FSREC fr mem') ->
  (forall a, in_globals AF.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AF.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  FRA B APIf ra g fr hb regs mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs mem mem' md W HFRA MU WM HRO HD HSH HAH' HSTK HWhdr HWimg HWA9 HWsaved HWsh HWwin
    HrecK HAG' HWA'.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by lia. apply HWimg. unfold AC.GT. lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HSH)|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hthr in Hx. cbn in Hx. lia.
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo.
        * lia.
        * rewrite Hlock in Hx. cbn in Hx. lia.
    - intros k Hk. rewrite KBlo.
      + exact (Hohd k Hk).
      + rewrite Hhead. lia.
      + rewrite Hhead. lia. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [exact Hr2|].
  split; [exact Hspm|].
  split; [exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [exact Hr4|].
  split; [exact Hr8|].
  split; [exact Hr9|].
  split; [exact Hr3|].
  split; [exact Hr19|].
  split; [exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA416|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWA9 A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWA9 A Hr9 HA64 x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWA9 A Hr9 HA64 x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + split; [|exact (HrecK Hrec)].
        intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
    eapply fl_bytes; [exact Hbytes | exact MU |]. rewrite Hlen. intros x Hx. exact (HWsh x ltac:(lia)). }
  split; [exact HWwin|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|].
  split; [exact HSHI2|].
  split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

(* FRA and ENT across the reac_ctrl_parse call at 0x81e80 with o = fr + 176 (the contract's munch list: the 36
   output cells, the callee window, the class-1 side-stack bytes and their shadow, the shadow of the window) and
   the lazy-page step md -> md'. AH / stklo / stkhi and ownership by a_laws_fs_store (the post's fs stk and class-1
   state give a_fs_ok); FRA by f3_fr_run; ENT by ent_munch (no byte ENT names is written: the entry blocks are off
   the side stack and below stklo, the image is below GT, the stack from S on is above the window and the frame,
   and the shadow of those is apart, granule by granule, from the shadow the call writes). *)
Lemma f3_fra_call : forall g fr hb regs regs' mem mem' md md' FS (bs : list byte),
  FRA B APIf ra g fr hb regs mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  Frame.munch (f3_PW (fr + 176) (AC.aspZ regs) FS) mem mem' -> Frame.wmono rsegs mem mem' ->
  ro_same rsegs mem mem' ->
  stk rsegs mem' (AC.aspZ regs - REAC_CTRL_PARSE_K) (AC.aspZ regs) ->
  addressable mem' (AC.aspZ regs - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K ->
  rw_cells rsegs mem' (fr + 176) [CB 36 bs] ->
  shadow_rw mem' ->
  stk rsegs mem' FS (FS + FS_SIZE) -> fp_cls mem' FS 1 ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md' /\ (ENT APIf g hb mem md -> ENT APIf g hb mem' md').
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs regs' mem mem' md md' FS bs HFRA Htp HFS MU WM HRS Hstkw HADw HRW HSRW HFSstk Hcls
    E2 E3 E4 E8 E9 E19 E26 Hmat.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & Happ).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hapart & _ & HFSfr & _).
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ _ _ HAH) as Hhi.
  destruct (AC.a_laws_fs_place _ _ _ _ _ LAWS _ _ _ FS HAH Htp HFS) as (HFSgt & HFSst & HFSal & HFSapp).
  pose proof (proj1 (AC.a_laws_fs_state _ _ _ _ _ LAWS _ _ _ FS HAH Htp HFS)) as Hok.
  pose proof (HFSfr FS Htp HFS) as HFSlow.
  pose proof (Hapart REAC_CTRL_PARSE_K ltac:(unfold REAC_CTRL_PARSE_K, FN_STACK, AF.SLOT_STACK; lia)) as Hwd.
  rewrite Haspz in MU, Hstkw, HADw, Hwd, Hwlo.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HKp : REAC_CTRL_PARSE_K = 8800) by (vm_compute; reflexivity).
  assert (HKf : FS_SIZE = 11571200) by (vm_compute; reflexivity).
  assert (HKf2 : AC.FS_SIZE = 11571200) by (vm_compute; reflexivity).
  assert (HKn : FN_STACK = 1044480) by (vm_compute; reflexivity).
  assert (HKtp : AC.as_tp AC.ASYMS = 6141968) by (vm_compute; reflexivity).
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (Hfr8 : fr mod 8 = 0) by (clear - HFRAMEb HFRAMEs Hfrm; Z.div_mod_to_equations; lia).
  assert (Hsp8 : (sp - 8800) mod 8 = 0) by (clear - HFRAMEb HFRAMEs Hspm; Z.div_mod_to_equations; lia).
  assert (HFS8 : FS mod 8 = 0) by (clear - HFRAMEb HFRAMEs HFSal; Z.div_mod_to_equations; lia).
  assert (Hfrlo : (fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr) /\ fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ fr ltac:(lia)) as P1. pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as P2.
    unfold app_mem in P1, P2. lia. }
  assert (HFSlo : FS + AC.FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS).
  { pose proof (HFSapp FS ltac:(lia)) as P1. pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as P2.
    unfold app_mem in P1, P2. lia. }
  assert (Harm : (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= fr) \/
                 (FS <= fr /\ fr + FRAME_BYTES <= FS + AC.FS_SIZE)).
  { destruct Hloc as [(_ & _ & Hreal)|(_ & _ & Hfs & _)].
    - left. exact (proj1 (Hreal fr ltac:(lia))).
    - right. destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (b & Hbr & Hb & Hb1).
      pose proof (f3_wm_eq _ _ _ _ Hb Htp) as Heq. rewrite !Z.mod_small in Heq by lia. subst b. lia. }
  assert (Ho0 : fr + 176 <> 0) by lia.
  (* the shadow of an app byte apart from the class-1 frames and from the callee window is outside the call's
     writes *)
  assert (HSHO : forall y, 0 <= y < APPMEM_END -> (y < FS + 1085440 \/ FS + 2134016 <= y) ->
            (y < sp - 8800 \/ sp <= y) -> Frame.outside (f3_PW (fr + 176) sp FS) (shadow_addr y)).
  { intros y Hy Hy1 Hy2. apply f3_PW_out_sh; try lia. }
  assert (HAPO : forall x, app_mem x -> ~ (fr + 176 <= x < fr + 212) -> ~ (sp - 8800 <= x < sp) ->
            ~ (FS + 8 <= x < FS + 16) -> ~ (FS + 20480 <= x < FS + 28672) ->
            ~ (FS + 1085440 <= x < FS + 2134016) -> Frame.outside (f3_PW (fr + 176) sp FS) x).
  { intros x Hx N1 N2 N3 N4 N5.
    apply f3_PW_out_app; [lia | exact Hx | lia | lia | lia | lia | lia | lia | lia | lia | lia]. }
  clear Hfrm Hspm HAm HFSal Hfr8 Hsp8 HFS8.
  (* the side stack's state after the call *)
  assert (Hokp : AC.a_fs_ok mem' FS).
  { destruct Hok as (O1 & O2 & O3 & O4 & O5).
    destruct HFSstk as (_ & _ & HS).
    destruct Hcls as (_ & h1 & fl & Hh1 & Hfl & Hfll & Hflb).
    destruct (f3_fsc FS) as (F1 & F2 & F3 & F4 & F5).
    split; [|split; [|split; [|split]]].
    - intros a Ha. exact (HS a ltac:(lia)).
    - apply (kb_word_munch rsegs mem mem' (f3_PW (fr + 176) sp FS) (FS + 88) 20 O2 MU). intros k Hk.
      split; [lia|]. apply f3_PW_out_app; try lia. apply HFSapp. lia.
    - rewrite (KindBGlue.mbyte_munch rsegs (f3_PW (fr + 176) sp FS) mem mem' (FS + 96) MU);
        [exact O3 | lia |].
      apply f3_PW_out_app; try lia. apply HFSapp. lia.
    - intros c Hc. destruct (Nat.eq_dec c 1) as [->|Hc1].
      + exists (bv_unsigned h1). exact (bytes_at_le8_word rsegs mem' (fs_hint FS 1) h1 Hh1).
      + destruct (O4 c Hc) as [h Hh].
        exists h. apply (kb_word_munch rsegs mem mem' (f3_PW (fr + 176) sp FS) _ h Hh MU).
        intros k Hk. unfold AC.a_fs_hint.
        assert (Hcz : Z.of_nat c <> 1) by lia.
        split; [lia|]. apply f3_PW_out_app; try lia. apply HFSapp. lia.
    - intros c j Hc Hj. destruct (Nat.eq_dec c 1) as [->|Hc1].
      + destruct Hfl as (_ & _ & Hfl).
        assert (Hj' : (Z.to_nat j < length fl)%nat).
        { change (AC.a_fs_M 1) with (fs_M 1) in Hj. rewrite F3 in Hfll, Hj. lia. }
        destruct (nth_error fl (Z.to_nat j)) as [b|] eqn:En; [|apply nth_error_None in En; lia].
        pose proof (Hfl (Z.to_nat j) Hj') as Hb. rewrite En, Z2Nat.id in Hb by lia.
        assert (Hin : In b fl) by exact (nth_error_In fl _ En).
        rewrite Forall_forall in Hflb.
        replace (AC.a_fs_flag FS 1 j) with (fs_flag FS 1 0 + j)
          by (rewrite F2, f3_afs_flag1; lia).
        destruct (Hflb b Hin) as [-> | ->]; [left | right]; exact Hb.
      + pose proof (a_fs_flag_range FS c j Hc Hj) as Hr.
        pose proof (f3_flag_other FS c j Hc Hc1 Hj) as Ho.
        rewrite (KindBGlue.mbyte_munch rsegs (f3_PW (fr + 176) sp FS) mem mem' (AC.a_fs_flag FS c j) MU);
          [exact (O5 c j Hc Hj) | lia |].
        apply f3_PW_out_app; try lia. apply HFSapp. lia. }
  (* AH and stklo across the call (law: stores into the side stack and its Shadow) *)
  assert (Hagree : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      ~ (FS <= a < FS + AC.FS_SIZE) -> ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ a = shadow_addr b) ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns Hnf Hnsh. apply MU. rewrite MState.unsigned_lit by exact Ha.
    apply (f3_PW_out (fr + 176) sp FS a Ho0).
    - intro Hin. destruct Harm as [R1|[S1 S2]].
      + apply Hns. right. left. lia.
      + apply Hnf. lia.
    - intro Hin. apply Hns. right. left. lia.
    - intro Hin. apply Hnf. lia.
    - intro Hin. apply Hnf. lia.
    - intro Hin. apply Hnf. lia.
    - intro Hin. apply Hnsh. exists (8 * (a - ASAN_K)). unfold shadow_addr in *. split; lia.
    - intro Hin. apply Hns. right. right. right. exists (8 * (a - ASAN_K)). unfold shadow_addr in *.
      split; [lia | right; left; lia]. }
  assert (Hwm : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a).
  { intros a _ Hw. exact (WM (Z_to_bv 64 a) Hw). }
  destruct (AC.a_laws_fs_store _ _ _ _ _ LAWS (hb ++ g_H g) mem mem' md FS HAH Htp HFS Hagree Hwm Hokp)
    as (HAH' & Hown & Hstkeq & Hstkhieq).
  split.
  - apply (sl_fra_move B APIf ra g fr hb regs regs' mem' md md');
      [| exact E2 | exact E3 | exact E4 | exact E8 | exact E9 | exact E19 | exact E26 | exact Hmat].
    apply (f3_fr_run g fr hb regs mem mem' md (f3_PW (fr + 176) sp FS) HFRA MU WM).
    + exact (ro_agree_same rsegs mem mem' Hro HRS).
    + apply f3_rt. intros lo hi Hin. apply (f3_PW_lo (fr + 176) sp FS lo hi Ho0); [lia | lia | lia | exact Hin].
    + intros a Ha. destruct (HSRW a Ha) as (_ & b & Hb). exists b. exact Hb.
    + exact HAH'.
    + exact Hstkeq.
    + intros x Hx. apply HAPO; [apply Happ; lia | lia | lia | lia | lia | lia].
    + intros x Hx. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
    + intros A' HA' HA'r x Hx.
      assert (EA : A' = A) by (apply f3_id; [lia | lia |]; unfold rg in HA', Hr9; rewrite <- HA'; exact Hr9).
      subst A'. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
    + intros x Hx. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
    + intros x Hx.
      replace x with (shadow_addr (fr + 8 * (x - Sfr fr))) by (rewrite f3_fr_sh; lia).
      apply HSHO; lia.
    + apply (fl_stk _ mem mem' (g_S g - AF.SLOT_STACK) (g_S g) Hwin MU WM).
      intros x Hx.
      destruct (Z_lt_le_dec x (sp - 8800)) as [Hl|Hl];
        [|destruct (Z_lt_le_dec x sp) as [Hl2|Hl2];
          [right; destruct Hstkw as (_ & _ & Hs); exact (proj2 (Hs x ltac:(lia)))|]].
      * destruct (Z_le_gt_dec (fr + 176) x) as [C1|C1]; [destruct (Z_lt_ge_dec x (fr + 212)) as [C2|C2]|].
        -- right. exact (f3_cell_byte mem' (fr + 176) 36 bs x HRW ltac:(change (Z.of_nat 36) with 36; lia)).
        -- left. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
        -- left. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
      * destruct (Z_le_gt_dec (fr + 176) x) as [C1|C1]; [destruct (Z_lt_ge_dec x (fr + 212)) as [C2|C2]|].
        -- right. exact (f3_cell_byte mem' (fr + 176) 36 bs x HRW ltac:(change (Z.of_nat 36) with 36; lia)).
        -- left. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
        -- left. apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
    + intros Hrec. apply (f3_fsrec_keep mem mem' _ fr Hrec MU).
      intros FS' j x Htp' HFS' Hj Hfrv Hx.
      assert (EFS : FS' = FS).
      { pose proof (f3_wm_eq _ _ _ _ Htp' Htp) as E. rewrite !Z.mod_small in E by lia. exact E. }
      subst FS'.
      destruct Hx as [Hx|[Hx|Hx]].
      * apply HAPO; [apply HFSapp; lia | lia | lia | lia | lia | lia].
      * apply HAPO; [apply HFSapp; lia | lia | lia | lia | lia | lia].
      * apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
    + intros a Ha. pose proof (f3_ag_lt a Ha) as Hab.
      apply (addr1_munch _ mem mem' a MU); [|exact (HAG a Ha)].
      apply HSHO; lia.
    + intros a Ha Hnf.
      destruct (Z_le_gt_dec (sp - 8800) a) as [Hw1|Hw1]; [destruct (Z_lt_ge_dec a sp) as [Hw2|Hw2]|].
      * exact (f3_addr1 mem' (sp - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K a HADw ltac:(lia)).
      * apply (addr1_munch _ mem mem' a MU); [|exact (HWA a Ha Hnf)]. apply HSHO; lia.
      * apply (addr1_munch _ mem mem' a MU); [|exact (HWA a Ha Hnf)]. apply HSHO; lia.
  - intros HENT. eapply ent_mat; [|exact Hmat].
    eapply ent_munch; [exact HENT | exact HAH | exact MU | | exact Hstkeq | exact Hstkhieq |].
    + intros x Hk. destruct Hk as [Hblk | [Himg | [Habv | [(b & Hor & ->) | Hblks]]]].
      * destruct Hblk as (q & k & i & Hin & Hni & Hi & ->).
        destruct (AC.a_laws_blocks _ _ _ _ _ LAWS (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin)))
          as (_ & Hq4 & Hend & _ & Hall).
        destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
        assert (HnFS : ~ (FS <= q + i < FS + AC.FS_SIZE)).
        { intros HC. apply Hnfs. exists FS. split; [exact HFS | split; [exact Htp | exact HC]]. }
        apply HAPO; [exact Happq | | lia | lia | lia | lia].
        destruct Harm as [R1|[S1 S2]]; lia.
      * pose proof (img_below_GT x Himg) as Hxg.
        apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
      * apply HAPO; [unfold app_mem; lia | lia | lia | lia | lia | lia].
      * assert (Hb0 : 0 <= b < APPMEM_END)
          by (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X|]; lia).
        apply HSHO; [exact Hb0 | |];
          (destruct Hor as [Hi|Hr]; [pose proof (img_below_GT b Hi) as X|]; lia).
      * (* frame batch 2 item 9: the shadow byte of an entry block byte (app memory below stklo, off the side
           stack, below the callee's window) *)
        destruct Hblks as (q & k & i & Hin & _ & Hi & ->).
        destruct (AC.a_laws_blocks _ _ _ _ _ LAWS (hb ++ g_H g) mem md q k HAH (in_or_app _ _ _ (or_intror Hin)))
          as (_ & Hq4 & Hend & _ & Hall).
        destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
        assert (HnFS : ~ (FS <= q + i < FS + AC.FS_SIZE)).
        { intros HC. apply Hnfs. exists FS. split; [exact HFS | split; [exact Htp | exact HC]]. }
        apply HSHO; [unfold app_mem in Happq; lia | lia | lia].
    + intros a _ Ho. exact (proj2 (Hown a) Ho).
Qed.

(* ---- model and byte facts (no section variable) ---- *)

(* Every byte reac_ctrl_parse reads of the 50-byte frame is one of its first 50. *)
Lemma f3_cp_rd_lt : forall n bs i, In i (cp_rd n bs) -> (i < 50)%nat.
Proof.
  intros n bs i H. unfold cp_rd in H.
  destruct (negb (50 <=? n)); [destruct H|].
  destruct (negb (cp_v bs 12 =? 0x88)); [cbn in H; lia|].
  destruct (negb (cp_v bs 13 =? 0x19)); [cbn in H; lia|].
  apply in_app_iff in H. destruct H as [H|H]; [apply in_seq in H; lia|].
  destruct (cp_rec bs); [|destruct H].
  apply in_app_iff in H. destruct H as [H|H]; [cbn in H; lia|].
  apply in_app_iff in H. destruct H as [H|H].
  - destruct (cp_v bs 32 =? 0x12); cbn in H; lia.
  - destruct (cp_kind bs =? 6); cbn in H; lia.
Qed.

(* The u32 of a kind 0 .. 13 is the kind byte and three zero bytes. *)
Lemma f3_le4_kind : forall k, 0 <= k <= 13 -> le4 (Z_to_bv 64 k) = [Z_to_bv 8 k; cp_z; cp_z; cp_z].
Proof.
  intros k Hk.
  assert (Hc : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/
               k = 10 \/ k = 11 \/ k = 12 \/ k = 13) by lia.
  repeat (destruct Hc as [Hc|Hc]; [subst k; vm_compute; reflexivity|]). subst k. vm_compute. reflexivity.
Qed.

(* C7's producer: the parse's 36 output cells at o hold the kind in their first four bytes, as a u32. At the call
   0x81df8 o = [A + 248] = fr + 176, n = len_j and the frame is t_g j, so the cells give u32 (fr + 176) (t_k j). *)
Lemma f3_c7 : forall m o n bs, rw_cells rsegs m o [CB 36 (snd (ctrlparse n bs))] -> u32 m o (fst (ctrlparse n bs)).
Proof.
  intros m o n bs ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  rewrite <- (firstn_skipn 4 (snd (ctrlparse n bs))) in Hb. apply Mem.bytes_at_app in Hb. destruct Hb as (Hb & _).
  rewrite ctrlparse_kind_bytes in Hb. unfold u32.
  rewrite (f3_le4_kind _ (ctrlparse_kind_range n bs)). exact Hb.
Qed.

(* ---------------- F3: the base facts of the call, the carry, the segment ---------------- *)

Lemma f3_byte1 : forall m a bs (i : nat) b, bytes_at rsegs m a bs -> nth_error bs i = Some b ->
  bytes_at rsegs m (a + Z.of_nat i) [b].
Proof.
  intros m a bs i b (H0 & H1 & H) Hn.
  assert (Hi : (i < length bs)%nat) by (apply nth_error_Some; rewrite Hn; discriminate).
  split; [lia|]. split; [cbn [length]; lia|].
  intros k Hk. cbn [length] in Hk. destruct k as [|k]; [|lia].
  cbn [nth_error]. replace (a + Z.of_nat i + Z.of_nat 0) with (a + Z.of_nat i) by lia.
  rewrite H by exact Hi. exact Hn.
Qed.

(* The runtime cells the bcmp wrapper of reac_ctrl_parse reads, from FRA's AsanRTInv.RT alone (a Theorem Labs lane's
   B5Cuts.v (not in this delivery) b5_rt_cells). *)
Lemma f3_rt_cells : forall sp m md, AsanRTInv.RT sp m md ->
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs m GOT_CF (le8 (wa CF)) /\
  bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
Proof.
  intros sp m md HRT.
  pose proof (AsanRTInv.RT_real_cells sp m md HRT) as HR.
  pose proof (AsanRTInv.RT_cf_cells sp m md HRT) as (Hg & _ & _ & _ & _ & _ & H240 & _).
  split; [exact (AsanRTInv.real_cell_of m REAL_BCMP BCMP HR ltac:(vm_compute; reflexivity))|].
  split; [exact (AsanRTInv.real_cell_of m REAL_MEMCMP MEMCMP HR ltac:(vm_compute; reflexivity))|].
  split; [exact Hg|].
  split.
  - pose proof (f3_byte1 m (RT_CF + 240) _ 14 (Z_to_bv 8 1) H240 eq_refl) as HH.
    replace (RT_CF + 240 + Z.of_nat 14) with (CF + 254) in HH by (unfold RT_CF, CF; lia). exact HH.
  - pose proof (f3_byte1 m (RT_CF + 240) _ 15 (Z_to_bv 8 1) H240 eq_refl) as HH.
    replace (RT_CF + 240 + Z.of_nat 15) with (CF + 255) in HH by (unfold RT_CF, CF; lia). exact HH.
Qed.

(* The block's placement (Seg/F2.v's f2_place, here at this section's variables). *)
Lemma f3_place : forall g j phi fr regs m md,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs m md ->
  forall k, 0 < k <= AC.a_size (flen g j) ->
  (phi + k <= fr \/ fr + FRAME_BYTES <= phi) /\
  phi + k <= AC.aspZ regs - FN_STACK /\
  ~ AC.a_in_fs AC.ASYMS m phi.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g j phi fr regs m md HFRA k Hk.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  destruct (fra_win B APIf ra g fr _ regs m md HFRA) as (Hwlo & _).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & _).
  assert (Hinphi : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (cbn [hb1 app In]; left; reflexivity).
  destruct (AC.a_laws_blocks _ _ _ _ _ ALAWS _ m md phi (AC.a_size (flen g j)) HAH Hinphi)
    as (_ & Hp4096 & Hend & _ & Hall).
  split; [|split].
  - destruct Hloc as [(_ & _ & Hreal) | (_ & _ & Hfs & _)].
    + left. pose proof (Hreal fr ltac:(lia)) as Hr. lia.
    + destruct (Z_le_gt_dec (phi + k) fr) as [Hl|Hl]; [left; exact Hl|].
      destruct (Z_le_gt_dec (fr + FRAME_BYTES) phi) as [Hr|Hr]; [right; exact Hr|].
      exfalso. destruct (Hall (Z.max phi fr) ltac:(lia)) as (_ & _ & _ & _ & Hnfs).
      exact (Hnfs (Hfs (Z.max phi fr) ltac:(lia))).
  - lia.
  - destruct (Hall phi ltac:(lia)) as (_ & _ & _ & _ & Hnfs). exact Hnfs.
Qed.

(* The carry b5_C moves to m' when the save-area words, the fragment record's bytes, the shadow of the two frame
   records, the record's 50 bytes (long frame) and the image below GT with its shadow read the same, and sp, s1,
   s2 and s7 are kept. *)
Lemma b5c_move : forall g j phi fr regs regs' A m m',
  b5_C g j phi fr regs m -> rg regs 9 A -> 0 <= A < 2 ^ 64 -> A + 416 <= APPMEM_END ->
  getr regs' 2 = getr regs 2 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 23 = getr regs 23 ->
  (forall x, A + 32 <= x < A + 304 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  (forall x, fr + 2768 <= x < fr + 2915 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  (forall x, fr + 2688 <= x < fr + 2915 -> mbyte rsegs m' (shadow_addr x) = mbyte rsegs m (shadow_addr x)) ->
  (50 <= flen g j -> forall x, phi <= x < phi + 50 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  (forall x, 0 <= x < AC.GT -> mbyte rsegs m' x = mbyte rsegs m x /\
     mbyte rsegs m' (shadow_addr x) = mbyte rsegs m (shadow_addr x)) ->
  b5_C g j phi fr regs' m'.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g j phi fr regs regs' A m m' HC H9 HA HAE E2 E9 E18 E23 KA KF KFS KP KI.
  destruct HC as (H23 & H18 & (A1 & H9a & HA1 & HSP & H232) & (HPb & HPp & HPfs) &
                  (HFRa & HFRb & HFRc & HFRd) & (HFSa & DB & HDB & HDB0 & HDB1) & (HKNa & HKNb) & HFG & HFSj).
  assert (HAA : A1 = A).
  { pose proof (rg_eq64 regs 9 A1 A H9a H9) as Hm. rewrite !Z.mod_small in Hm by lia. exact Hm. }
  subst A1.
  assert (Htp : 0 <= AC.as_tp AC.ASYMS /\ AC.as_tp AC.ASYMS + 16 <= AC.GT)
    by (unfold AC.as_tp, AC.ASYMS, AC.GT; cbn; lia).
  assert (HKN : KIND_NAME = 0x9e760) by reflexivity.
  assert (HGTv : AC.GT = 6283264) by reflexivity.
  assert (Q : forall off v, 40 <= off <= 296 -> q64 m (A + off) v -> q64 m' (A + off) v).
  { intros off v Ho Hq. unfold q64 in *. apply (f1_bkeep m m'); [|exact Hq].
    rewrite length_le8. intros x Hx. apply KA. lia. }
  assert (WT : forall a v, 0 <= a -> a + 8 <= AC.GT -> word_mem rsegs m a v -> word_mem rsegs m' a v).
  { intros a v Ha Hb Hw. apply (word_mem_frame rsegs m m' a v Hw). intros k Hk.
    exact (proj1 (KI (a + k) ltac:(lia))). }
  assert (WT' : forall a v, 0 <= a -> a + 8 <= AC.GT -> word_mem rsegs m' a v -> word_mem rsegs m a v).
  { intros a v Ha Hb Hw. apply (word_mem_frame rsegs m' m a v Hw). intros k Hk.
    symmetry. exact (proj1 (KI (a + k) ltac:(lia))). }
  split; [unfold rg in *; rewrite E23; exact H23|].
  split; [unfold rg in *; rewrite E18; exact H18|].
  split.
  { exists A. split; [unfold rg in *; rewrite E9; exact H9|]. split; [exact HA|].
    split; [|exact (Q 232 _ ltac:(lia) H232)].
    destruct HSP as (S248 & S256 & S144 & S184 & S208 & S64 & S72 & S80 & S272 & S264).
    split; [exact (Q 248 _ ltac:(lia) S248)|].
    split; [exact (Q 256 _ ltac:(lia) S256)|].
    split; [exact (Q 144 _ ltac:(lia) S144)|].
    split; [exact (Q 184 _ ltac:(lia) S184)|].
    split; [exact (Q 192 _ ltac:(lia) S208)|].
    split; [exact (Q 80 _ ltac:(lia) S64)|].
    split; [exact (Q 88 _ ltac:(lia) S72)|].
    split; [exact (Q 96 _ ltac:(lia) S80)|].
    split; [exact (Q 272 _ ltac:(lia) S272)|].
    exact (Q 264 _ ltac:(lia) S264). }
  split.
  { split; [|split].
    - intros Hl. apply (f1_bkeep m m'); [|exact (HPb Hl)]. unfold t_g. rewrite fr50_length.
      intros x Hx. apply (KP Hl). lia.
    - intros Hl. replace (AC.aspZ regs') with (AC.aspZ regs) by (unfold AC.aspZ; rewrite E2; reflexivity).
      exact (HPp Hl).
    - intros Hl0 (b & Hbr & Hw & Hr). apply (HPfs Hl0). exists b. split; [exact Hbr|].
      split; [|exact Hr]. exact (WT' (AC.as_tp AC.ASYMS) b ltac:(lia) ltac:(lia) Hw). }
  split.
  { split; [apply (f1_addr_keep m m' _ _ HFRa); intros i Hi; apply KFS; unfold fragb; lia|].
    split; [apply (f1_addr_keep m m' _ _ HFRb); intros i Hi; apply KFS; lia|].
    split; [|exact HFRd].
    apply (f1_bkeep m m'); [|exact HFRc]. rewrite HFRd. unfold fragb. intros x Hx. apply KF. lia. }
  split.
  { split.
    - intros FS Hw HFSr Hin. exact (HFSa FS (WT' (AC.as_tp AC.ASYMS) FS ltac:(lia) ltac:(lia) Hw) HFSr Hin).
    - exists DB. split; [exact (WT (AC.as_tp AC.ASYMS + 8) DB ltac:(lia) ltac:(lia) HDB)|]. split; [exact HDB0 | exact HDB1]. }
  split.
  { split.
    - apply (f1_bkeep m m'); [|exact HKNa]. intros x Hx.
      assert (Hl : length kind_name_bytes = 112%nat) by (vm_compute; reflexivity).
      rewrite Hl in Hx. exact (proj1 (KI x ltac:(lia))).
    - apply (f1_addr_keep m m' _ _ HKNb). intros i Hi. exact (proj2 (KI (KIND_NAME + i) ltac:(lia))). }
  split.
  { destruct HFG as (HFGb & Hok). split; [|exact Hok]. unfold FGBe in *.
    apply (f1_bkeep m m'); [|exact HFGb]. destruct (f1_FS_len (g_in g) j) as (_ & L72). rewrite L72.
    intros x Hx. apply KF. lia. }
  destruct HFSj as (S104 & S112 & HBD & HAB & HFI).
  pose proof (f1_body_len (g_in g) j) as L3.
  split; [exact (f1_spill_move regs regs' A 104 _ m m' S104 H9 HA HAE ltac:(lia) E9
                   ltac:(intros x Hx; apply KA; lia))|].
  split; [exact (f1_spill_move regs regs' A 112 _ m m' S112 H9 HA HAE ltac:(lia) E9
                   ltac:(intros x Hx; apply KA; lia))|].
  split; [apply (f1_bkeep m m'); [|exact HBD]; intros x Hx; apply KF; lia|].
  split; [apply (f1_addr_keep m m' (fr + 2880) 35 HAB); intros i Hi; apply KFS; lia|].
  exact HFI.
Qed.


(* ---- b5_PF's parse-made facts (no section variable) ----
   Under cp_hdr (= t_8819 at the turn's length and frame), the parse's output B at o (= fr + 176) holds, by
   RcParse.ctrlparse_fields, the frame bytes 6 .. 11 at o + 4, 0 .. 5 at o + 10 and 14, 15 at o + 20; the frame
   itself is at phi. *)

Lemma f3_nth_skipn : forall (l : list byte) k i d, nth i (skipn k l) d = nth (k + i) l d.
Proof.
  induction l as [|x l IH]; intros k i d.
  - rewrite skipn_nil. destruct i, k; reflexivity.
  - destruct k as [|k]; [reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

Lemma f3_ble2 : forall b0 b1 : byte, bytes_le_to_Z [b0; b1] = bv_unsigned b0 + 256 * bv_unsigned b1.
Proof. intros b0 b1. rewrite bytes_le_to_Z_le_val. cbn [map le_val]. lia. Qed.

Lemma f3_le2_bytes : forall b0 b1 : byte, le2 (Z_to_bv 64 (bytes_le_to_Z [b0; b1])) = [b0; b1].
Proof.
  intros b0 b1. pose proof (f3_byte_range b0). pose proof (f3_byte_range b1).
  unfold le2. rewrite MState.unsigned_lit by (rewrite f3_ble2; lia).
  exact (f3_le_bytes_to_Z [b0; b1]).
Qed.

(* A window of n bytes of B at a + k that agree with the first n of L. *)
Lemma f3_ba_shift : forall m a (Bs L : list byte) (k n : nat), bytes_at rsegs m a Bs ->
  (k + n <= length Bs)%nat -> (n <= length L)%nat ->
  (forall i, (i < n)%nat -> nth (k + i) Bs cp_z = nth i L cp_z) ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n L).
Proof.
  intros m a Bs L k n (H0 & H1 & H) Hk Hn Hi.
  split; [lia|]. rewrite length_firstn. split; [lia|].
  intros i Hlt. rewrite f2_nth_firstn by lia.
  replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite (nth_error_nth' Bs cp_z) by lia. rewrite (nth_error_nth' L cp_z) by lia.
  f_equal. apply Hi. lia.
Qed.

Lemma f3_b8_of : forall m a (bs : list byte) (i : nat), bytes_at rsegs m a bs -> (i < length bs)%nat ->
  b8 m (a + Z.of_nat i) (cp_v bs i).
Proof.
  intros m a bs i H Hi.
  assert (E : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b).
  { intros b. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2 ^ 8)%Z.
    pose proof (f3_byte_range b). apply Z.mod_small. lia. }
  unfold b8, cp_v. rewrite E.
  apply (f3_byte1 m a bs i); [exact H|]. unfold cp_b. apply nth_error_nth'. exact Hi.
Qed.

(* A shadow byte whose granule's last byte x (x mod 8 = 7) is addressable is 0. *)
Lemma f3_sh0 : forall m p n x y, addressable m p n -> p <= x < p + n -> x mod 8 = 7 -> y / 8 = x / 8 ->
  b8 m (Z.shiftr y 3 + ASAN_K) 0.
Proof.
  intros m p n x y (Hp & Hn & Hpn & HA) Hx H7 Hy.
  destruct (HA (x - p) ltac:(lia)) as (_ & b & Hb & Hok).
  replace (p + (x - p)) with x in Hb, Hok by lia.
  assert (Hs : bv_signed b = 0) by (destruct Hok as [H|H]; [exact H | lia]).
  assert (Hu : bv_unsigned b = 0).
  { pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
    unfold bv_signed, bv_swrap, bv_wrap in Hs. change (bv_half_modulus 8) with 128 in Hs.
    change (bv_modulus 8) with 256 in Hs. Z.div_mod_to_equations. lia. }
  assert (Eb : b = Z_to_bv 8 0) by (apply bv_eq; rewrite Hu, Z_to_bv_unsigned; reflexivity).
  subst b.
  assert (Ea : Z.shiftr y 3 + ASAN_K = shadow_addr x).
  { rewrite Z.shiftr_div_pow2 by lia. unfold shadow_addr. change (2 ^ 3) with 8. lia. }
  assert (HK : ASAN_K = 2147450880) by reflexivity.
  assert (Hx0 : 0 <= x) by lia.
  unfold b8. rewrite Ea. split; [unfold shadow_addr; pose proof (Z.div_pos x 8 Hx0 ltac:(lia)); lia|].
  split; [cbn [length]; unfold shadow_addr, APPMEM_END in *;
          assert (x / 8 <= x) by (apply Z.div_le_upper_bound; lia); lia|].
  intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
  cbn [nth_error]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact Hb.
Qed.

Lemma f3_memcmp_refl : forall n (l : list byte), (n <= length l)%nat -> SFA.memcmp_model l l n = Some 0.
Proof.
  induction n as [|n IH]; intros l Hl; [reflexivity|].
  destruct l as [|a l]; cbn [length] in Hl; [lia|]. cbn [SFA.memcmp_model]. rewrite Z.eqb_refl. apply IH. lia.
Qed.

(* The (v16, v17) equation of rec_inv: under cp_hdr, kind 1 is exactly bytes 16 and 17 zero. *)
Lemma f3_k1 : forall n bs, cp_hdr n bs = true ->
  (if cp_v bs 16 =? 0 then (if cp_v bs 17 =? 0 then 1 else 0) else 0) = (if fst (ctrlparse n bs) =? 1 then 1 else 0).
Proof.
  intros n bs Hh. destruct (Z.eqb_spec (fst (ctrlparse n bs)) 1) as [E|E].
  - apply ctrlparse_filler in E. destruct E as (_ & E16 & E17). rewrite E16, E17. reflexivity.
  - destruct (Z.eqb_spec (cp_v bs 16) 0) as [E16|E16]; [|reflexivity].
    destruct (Z.eqb_spec (cp_v bs 17) 0) as [E17|E17]; [|reflexivity].
    exfalso. apply E. apply ctrlparse_filler. auto.
Qed.

(* The parse-made group of rec_inv at o + 20 and phi + 14 .. 17, from the parse output at o and the frame at phi. *)
Lemma f3_pf_fields : forall m o phi n (bs : list byte), length bs = 50%nat -> cp_hdr n bs = true ->
  bytes_at rsegs m o (snd (ctrlparse n bs)) -> bytes_at rsegs m phi bs ->
  addressable m phi 50 -> phi mod 16 = 0 ->
  exists (field16 v14 v15 v16 v17 : Z),
    u16 m (o + 20) field16 /\
    b8 m (phi + 14) v14 /\ b8 m (phi + 15) v15 /\ b8 m (phi + 16) v16 /\ b8 m (phi + 17) v17 /\
    0 <= v14 < 256 /\ 0 <= v15 < 256 /\ 0 <= v16 < 256 /\ 0 <= v17 < 256 /\
    b8 m (Z.shiftr (phi + 14) 3 + ASAN_K) 0 /\ b8 m (Z.shiftr (phi + 15) 3 + ASAN_K) 0 /\
    b8 m (Z.shiftr (phi + 16) 3 + ASAN_K) 0 /\ b8 m (Z.shiftr (phi + 17) 3 + ASAN_K) 0 /\
    field16 = v14 + 256 * v15 /\
    (if v16 =? 0 then (if v17 =? 0 then 1 else 0) else 0) = (if fst (ctrlparse n bs) =? 1 then 1 else 0).
Proof.
  intros m o phi n bs Hl Hh HB HP HA H16.
  assert (Hk : fst (ctrlparse n bs) <> 0)
    by (unfold ctrlparse; rewrite Hh; cbn [fst]; pose proof (cp_kind_range bs); lia).
  pose proof (ctrlparse_fields n bs Hk) as HF. cbv zeta in HF.
  destruct HF as (_ & _ & _ & F20 & F21 & _).
  pose proof (ctrlparse_length n bs) as HL.
  exists (bytes_le_to_Z [cp_b bs 14; cp_b bs 15]), (cp_v bs 14), (cp_v bs 15), (cp_v bs 16), (cp_v bs 17).
  split.
  { unfold u16. rewrite f3_le2_bytes.
    pose proof (f3_ba_shift m o _ [cp_b bs 14; cp_b bs 15] 20 2 HB ltac:(lia) ltac:(cbn; lia)) as Hs.
    cbn [firstn] in Hs. change (Z.of_nat 20) with 20 in Hs. apply Hs.
    intros i Hi. destruct i as [|[|i]]; [exact F20 | exact F21 | lia]. }
  pose proof (f3_b8_of m phi bs 14 HP ltac:(lia)) as B14.
  pose proof (f3_b8_of m phi bs 15 HP ltac:(lia)) as B15.
  pose proof (f3_b8_of m phi bs 16 HP ltac:(lia)) as B16.
  pose proof (f3_b8_of m phi bs 17 HP ltac:(lia)) as B17.
  change (Z.of_nat 14) with 14 in B14. change (Z.of_nat 15) with 15 in B15.
  change (Z.of_nat 16) with 16 in B16. change (Z.of_nat 17) with 17 in B17.
  split; [exact B14|]. split; [exact B15|]. split; [exact B16|]. split; [exact B17|].
  unfold cp_v. pose proof (f3_byte_range (cp_b bs 14)). pose proof (f3_byte_range (cp_b bs 15)).
  pose proof (f3_byte_range (cp_b bs 16)). pose proof (f3_byte_range (cp_b bs 17)).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [apply (f3_sh0 m phi 50 (phi + 15) (phi + 14) HA); [lia | Z.div_mod_to_equations; lia |
                                                             Z.div_mod_to_equations; lia]|].
  split; [apply (f3_sh0 m phi 50 (phi + 15) (phi + 15) HA); [lia | Z.div_mod_to_equations; lia | reflexivity]|].
  split; [apply (f3_sh0 m phi 50 (phi + 23) (phi + 16) HA); [lia | Z.div_mod_to_equations; lia |
                                                             Z.div_mod_to_equations; lia]|].
  split; [apply (f3_sh0 m phi 50 (phi + 23) (phi + 17) HA); [lia | Z.div_mod_to_equations; lia |
                                                             Z.div_mod_to_equations; lia]|].
  split; [apply f3_ble2|].
  exact (f3_k1 n bs Hh).
Qed.

(* The two 6-byte compare groups of F18 / F19: the parse output's bytes 10 .. 15 (frame bytes 0 .. 5) against phi,
   and 4 .. 9 (frame bytes 6 .. 11) against phi + 6. *)
Lemma f3_pf_cmp : forall m o phi n (bs : list byte), length bs = 50%nat -> cp_hdr n bs = true ->
  bytes_at rsegs m o (snd (ctrlparse n bs)) -> bytes_at rsegs m phi bs ->
  (exists (ls rs : list byte),
     bytes_at rsegs m (o + 10) ls /\ (6 <= length ls)%nat /\
     bytes_at rsegs m phi rs /\ (6 <= length rs)%nat /\ SFA.memcmp_model ls rs 6 = Some 0) /\
  (exists (ls2 rs2 : list byte),
     bytes_at rsegs m (o + 4) ls2 /\ (6 <= length ls2)%nat /\
     bytes_at rsegs m (phi + 6) rs2 /\ (6 <= length rs2)%nat /\ SFA.memcmp_model ls2 rs2 6 = Some 0).
Proof.
  intros m o phi n bs Hl Hh HB HP.
  assert (Hk : fst (ctrlparse n bs) <> 0)
    by (unfold ctrlparse; rewrite Hh; cbn [fst]; pose proof (cp_kind_range bs); lia).
  pose proof (ctrlparse_fields n bs Hk) as HF. cbv zeta in HF.
  destruct HF as (F4 & F10 & _).
  pose proof (ctrlparse_length n bs) as HL.
  split.
  - exists (firstn 6 bs), (firstn 6 bs).
    split.
    { pose proof (f3_ba_shift m o _ bs 10 6 HB ltac:(lia) ltac:(lia)) as Hs.
      change (Z.of_nat 10) with 10 in Hs. apply Hs. intros i Hi. rewrite (F10 i Hi). reflexivity. }
    rewrite length_firstn. split; [lia|].
    split; [exact (f2_ba_firstn m phi bs 6 HP)|]. split; [lia|].
    apply f3_memcmp_refl. rewrite length_firstn. lia.
  - exists (firstn 6 (skipn 6 bs)), (firstn 6 (skipn 6 bs)).
    split.
    { pose proof (f3_ba_shift m o _ (skipn 6 bs) 4 6 HB ltac:(lia) ltac:(rewrite length_skipn; lia)) as Hs.
      change (Z.of_nat 4) with 4 in Hs. apply Hs. intros i Hi. rewrite (F4 i Hi).
      unfold cp_b. rewrite f3_nth_skipn. reflexivity. }
    rewrite length_firstn, length_skipn. split; [lia|].
    split; [pose proof (f2_ba_sub m phi bs 6 6 HP ltac:(lia)) as Hs; change (Z.of_nat 6) with 6 in Hs; exact Hs|].
    split; [lia|].
    apply f3_memcmp_refl. rewrite length_firstn, length_skipn. lia.
Qed.


(* b5_PF at 0x81dfc: the record bytes at phi (F2's memcpy, carried), and under t_8819 (= cp_hdr at the turn's
   length and frame) the parse-made group of rec_inv (f3_pf_fields) and the two compare groups (f3_pf_cmp), with
   FLC's spills [A + 72] / [A + 64] and the output cells' addressability. *)
Lemma f3_b5pf : forall g j phi fr regs m md,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs m md ->
  HB m phi (flen g j) -> FLSI g j fr regs m -> b5_C g j phi fr regs m ->
  (50 <= flen g j -> bytes_at rsegs m phi (t_phi (g_in g) j)) ->
  bytes_at rsegs m (fr + 176) (snd (ctrlparse (flen g j) (t_g (g_in g) j))) ->
  addressable m (fr + 176) 36 ->
  b5_PF g j phi fr regs m.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g j phi fr regs m md HFRA HHB HFLSI HC HREC HOUT HADo.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct HC as (_ & _ & (A & H9 & HA & _) & (HPb & _ & _) & _).
  destruct HFLSI as (_ & _ & _ & _ & _ & HFLC).
  destruct HFLC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S72 & S64 & _ & _).
  pose proof HFRA as HF.
  destruct HF as (A' & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP & _).
  assert (HAE : APPMEM_END = 140737488355328) by reflexivity.
  assert (HKg : AC.GT = 6283264) by reflexivity.
  pose proof (fra_app B APIf ra g fr _ regs m md HFRA) as (HGT & _).
  assert (EA : A' = A).
  { pose proof (rg_eq64 regs 9 A' A Hr9 H9) as Hm. rewrite !Z.mod_small in Hm by lia. exact Hm. }
  subst A'.
  assert (Hinphi : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (cbn [hb1 app In]; left; reflexivity).
  destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ m md phi (AC.a_size (flen g j)) HAH Hinphi) as (Hal & _).
  destruct HHB as (_ & Hphiad).
  exists A. split; [exact H9|]. split; [exact HA|]. split.
  - intros Hl. split; [|exact (HREC Hl)].
    exists (t_phi (g_in g) j). split; [exact (HREC Hl)|]. rewrite f2_phi_len. unfold flen in Hl. lia.
  - intros H8819.
    assert (Hhdr : cp_hdr (flen g j) (t_g (g_in g) j) = true) by exact H8819.
    assert (Hl : 50 <= flen g j).
    { unfold t_8819 in H8819. rewrite !andb_true_iff in H8819. destruct H8819 as ((Hb & _) & _).
      unfold t_big in Hb. apply Z.leb_le in Hb. exact Hb. }
    pose proof (HPb Hl) as HP.
    assert (HA50 : addressable m phi 50).
    { pose proof (addressable_sub m phi (AC.a_size (flen g j)) 0 50 Hphiad ltac:(lia) ltac:(lia)
                    ltac:(unfold AC.a_size; lia)) as H50. rewrite Z.add_0_r in H50. exact H50. }
    assert (H16 : phi mod 16 = 0) by exact Hal.
    destruct (f3_pf_cmp m (fr + 176) phi (flen g j) (t_g (g_in g) j)
                (ltac:(unfold t_g; apply fr50_length)) Hhdr HOUT HP)
      as ((ls & rs & Hls & Hlsl & Hrs & Hrsl & Hcmp) & (ls2 & rs2 & Hls2 & Hls2l & Hrs2 & Hrs2l & Hcmp2)).
    replace (fr + 176 + 10) with (fr + 186) in Hls by lia.
    replace (fr + 176 + 4) with (fr + 180) in Hls2 by lia.
    pose proof (addressable_sub m (fr + 176) 36 10 6 HADo ltac:(lia) ltac:(lia) ltac:(lia)) as Ha186.
    pose proof (addressable_sub m (fr + 176) 36 4 6 HADo ltac:(lia) ltac:(lia) ltac:(lia)) as Ha180.
    replace (fr + 176 + 10) with (fr + 186) in Ha186 by lia.
    replace (fr + 176 + 4) with (fr + 180) in Ha180 by lia.
    split; [|split].
    + exact (f3_pf_fields m (fr + 176) phi (flen g j) (t_g (g_in g) j)
               ltac:(unfold t_g; apply fr50_length) Hhdr HOUT HP HA50 H16).
    + exists ls, rs.
      split; [exact (f2_sq regs m A 72 _ S72 H9 HA ltac:(lia) ltac:(lia))|].
      split; [exact Hls|]. split; [exact Hlsl|]. split; [exact Hrs|]. split; [exact Hrsl|].
      split; [exact Hcmp | exact Ha186].
    + exists ls2, rs2.
      split; [exact (f2_sq regs m A 64 _ S64 H9 HA ltac:(lia) ltac:(lia))|].
      split; [exact Hls2|]. split; [exact Hls2l|]. split; [exact Hrs2|]. split; [exact Hrs2l|].
      split; [exact Hcmp2 | exact Ha180].
Qed.

(* seg_F3 (S_F3): the five shadow stores (f3_st; FRA / ENT by f3_fra_sh), the parse call on its contract (f3_calln;
   side-stack package by Tac_fsfree.fra_fp, window by Tac_slot.fra_callee_fp; FRA / ENT by f3_fra_call), and the
   exit body read off the two write sets: the frame's own facts off [fr + 176, fr + 216) and its shadow, the save
   area above sp, the record block and the image below GT apart from the call's ranges; C7 by f3_c7 and b5_PF by
   f3_b5pf. *)
Lemma seg_F3 : forall j : nat,
  Hat B APIf ra (Inv_A81dfc_at B APIf ra) j -> Hat B APIf ra (Inv_A81dd0_at B APIf ra) j.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    (Hgn & Hj & HHB & HFLSI & HLK & HC & (HFC & H22 & HREC & HIDj))).
  subst c. rewrite SEGS.
  pose proof HC as HC0.
  destruct HC0 as (Hs7 & Hs2 & (A & H9 & HA & _) & (HPb & _ & _) & _).
  pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGT & Happ).
  pose proof (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hapart & _ & HFSfr & _).
  pose proof (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hwlo & _).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (Asp & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hshb & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hstkhi.
  assert (HKh : HIGHMEM_BEG = 17594333495296) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
  assert (HKk : ASAN_K = 2147450880) by (vm_compute; reflexivity).
  assert (HKg : AC.GT = 6283264) by (vm_compute; reflexivity).
  assert (HKp : REAC_CTRL_PARSE_K = 8800) by (vm_compute; reflexivity).
  assert (HKn : FN_STACK = 1044480) by (vm_compute; reflexivity).
  assert (HKtp : AC.as_tp AC.ASYMS = 6141968) by (vm_compute; reflexivity).
  assert (HKf2 : AC.FS_SIZE = 11571200) by (vm_compute; reflexivity).
  assert (HC5 : asan_stack_malloc_c.CF = 1287080) by (vm_compute; reflexivity).
  assert (HC4 : asan_stack_malloc_c.GOT_CF = 654016) by (vm_compute; reflexivity).
  assert (HC5' : bcmp_wrap_c.CF = 1287080) by (vm_compute; reflexivity).
  assert (HC4' : bcmp_wrap_c.GOT_CF = 654016) by (vm_compute; reflexivity).
  assert (HAspR : 0 <= Asp < 2 ^ 64).
  { pose proof Hwin as HW0. unfold stk in HW0. destruct HW0 as (Hw0 & Hw1 & _). lia. }
  assert (HAeq : A = Asp) by (apply f3_id; [lia | lia |]; unfold rg in H9, Hr9; rewrite <- H9; exact Hr9).
  subst Asp.
  rewrite Haspz in Hwlo, Hapart.
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Hfr8 : fr mod 8 = 0) by (clear - HFRAMEb HFRAMEs Hfrm; Z.div_mod_to_equations; lia).
  assert (HfrH : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Ha. unfold app_mem in Ha. lia. }
  assert (HSfrlo : LOWMEM_END <= Sfr fr) by (unfold Sfr; apply f3_sh_lo; lia).
  assert (HSfrhi : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { unfold Sfr. pose proof (f3_sh_hi (fr + FRAME_BYTES - 1) ltac:(lia)) as Hh.
    pose proof (f3_sh_mono fr (fr + FRAME_BYTES - 1) ltac:(lia)). unfold shadow_addr in *.
    Z.div_mod_to_equations. lia. }
  pose proof HHB as (Hphinz & Hphiad).
  pose proof (f2_len_range (g_in g) j) as (HN0 & Hbody0 & Hbodyn).
  assert (HNe : flen g j = t_len (g_in g) j) by reflexivity.
  assert (Hgnl : g_n g = nlen (g_in g)) by reflexivity.
  assert (HN64 : 0 <= flen g j < 2 ^ 26) by lia.
  (* the block: below stklo, off the side stack, apart from the frame *)
  assert (Hinphi : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (cbn [hb1 app In]; left; reflexivity).
  destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md phi (AC.a_size (flen g j)) HAH Hinphi)
    as (_ & Hp4096 & Hpst & _ & Hpall).
  assert (HaszP : 1 <= AC.a_size (flen g j)) by (unfold AC.a_size; lia).
  destruct (f3_place g j phi fr regs mem md HFRA (AC.a_size (flen g j)) ltac:(lia)) as (Hphifr & _ & _).
  (* the wr_at premise of the five shadow stores *)
  assert (Wsh : wr_at rsegs mem (Sfr fr + 22) 5).
  { pose proof (AsanRTInv.RT_shadow_rw sp mem md HRT) as HSW0.
    split; [lia|]. split; [lia|]. intros i Hi.
    assert (Ei : Sfr fr + 22 + i = shadow_addr (fr + 176 + 8 * i))
      by (unfold Sfr, shadow_addr; Z.div_mod_to_equations; lia).
    rewrite Ei.
    exact (proj1 (HSW0 (shadow_addr (fr + 176 + 8 * i))
      (shadow_of_app (fr + 176 + 8 * i) (Happ (fr + 176 + 8 * i) ltac:(lia))))). }
  assert (HTPu : bv_unsigned (getr regs 4) = AC.as_tp AC.ASYMS)
    by (rewrite Hr4; apply MState.unsigned_lit; lia).
  (* [A + 248] = fr + 176 (FLSI) *)
  destruct HFLSI as (HFLSH & HS216 & HS224 & HS248 & HIN & HFLC).
  pose proof (f2_sq regs mem A 248 _ HS248 H9 HA ltac:(lia) ltac:(lia)) as Hq248.
  apply (sl_run_lib regs (Z_to_bv 64 0x81dd0) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x81dfc /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 19 = getr regs 19 /\
       getr R0 20 = getr regs 20 /\ getr R0 21 = getr regs 21 /\ getr R0 22 = getr regs 22 /\
       getr R0 26 = getr regs 26 /\
       getr R0 23 = getr regs 23 /\ getr R0 18 = getr regs 18 /\
       getr R0 25 = Z_to_bv 64 (phi + 18) /\
       getr R0 10 = Z_to_bv 64 (fst (ctrlparse (flen g j) (t_g (g_in g) j))) /\
       exists m2 FS,
         FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs m2 md /\
         ENT APIf g (hb1 phi (AC.a_size (flen g j))) m2 md /\ addressable m2 (fr + 176) 36 /\
         Frame.munch (f3_Wsh fr) mem m2 /\
         word_mem rsegs m2 (AC.as_tp AC.ASYMS) FS /\ 0 <= FS < 2 ^ 64 /\
         Frame.munch (f3_PW (fr + 176) sp FS) m2 mem' /\ Frame.wmono rsegs m2 mem' /\ ro_same rsegs m2 mem' /\
         stk rsegs mem' (sp - REAC_CTRL_PARSE_K) sp /\
         rw_cells rsegs mem' (fr + 176) [CB 36 (snd (ctrlparse (flen g j) (t_g (g_in g) j)))] /\
         shadow_rw mem' /\ addressable mem' (sp - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
         stk rsegs mem' FS (FS + FS_SIZE) /\ fp_cls mem' FS 1)
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* the run 0x81dd0 -> 0x81dfc *)
    rewrite f3_mkR_of_expand.
    f3_subst_slot Hr2. f3_subst_slot H9. f3_subst_slot Hr19. f3_subst_slot Hs7. f3_subst_slot Hs2.
    eapply LE.evt_cut.
    { eapply f3_st with (fr := fr) (phi := phi); [lia | lia | lia | lia | exact Wsh]. }
    intros ms1 (m2 & a0' & E1 & MU2 & WM2 & ST2 & HSH2).
    subst ms1.
    destruct (f3_fra_sh g fr _ regs mem m2 md HFRA HENT MU2 WM2 HSH2) as (HFRA2 & HENT2).
    (* the call's premises at m2 *)
    assert (KW1 : forall x, 0 <= x < 2 ^ 64 -> Frame.outside (f3_Wsh fr) x -> mbyte rsegs m2 x = mbyte rsegs mem x)
      by (intros x Hx Ho; exact (KindBGlue.mbyte_munch rsegs (f3_Wsh fr) mem m2 x MU2 Hx Ho)).
    assert (HWapp : forall x, app_mem x -> Frame.outside (f3_Wsh fr) x)
      by (intros x Hx; exact (f3_Wsh_app fr x Hfr0 ltac:(lia) Hx)).
    pose proof (fra_stk B APIf ra g fr _ regs m2 md HFRA2) as HFST2.
    assert (HSTKo2 : stk rsegs m2 (fr + 176) (fr + 212))
      by (apply (f2_stk_sub m2 fr (fr + FRAME_BYTES)); [exact HFST2 | lia | lia | lia]).
    destruct (stk_carve rsegs m2 (fr + 176) (fr + 212) 36 HSTKo2 ltac:(cbn; lia)) as (_ & junk & HRWo).
    replace (fr + 212 - Z.of_nat 36) with (fr + 176) in HRWo by (cbn; lia).
    assert (HADDRo : addressable m2 (fr + 176) 36)
      by (apply (f3_addr_o m2 fr ltac:(lia) Hfrm Happ ltac:(lia) HSH2)).
    (* the side-stack package of the call (classes [1], window REAC_CTRL_PARSE_K) *)
    assert (HWc : forall w, In w (reac_ctrl_parse_W (fr + 176) (AC.aspZ regs)) ->
              (g_S g - AF.SLOT_STACK <= fst w /\ snd w <= g_S g) \/ (fr <= fst w /\ snd w <= fr + FRAME_BYTES) \/
              (Sfr fr <= fst w /\ snd w <= Sfr fr + FRAME_SHADOW)).
    { intros w Hw. unfold reac_ctrl_parse_W in Hw.
      replace (fr + 176 =? 0) with false in Hw by (symmetry; apply Z.eqb_neq; lia).
      cbn [In app] in Hw. destruct Hw as [<- | [<- | []]]; cbn [fst snd]; [left | right; left]; lia. }
    assert (HDc : forall d, In d (reac_ctrl_parse_D phi (flen g j) (fr + 176)) ->
              snd d <= AC.GT \/ (fr <= fst d /\ snd d <= fr + FRAME_BYTES) \/
              (fst d < snd d /\ exists p n, In (p, n) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) /\
                 p <= fst d /\ snd d <= p + n)).
    { intros d Hd. unfold reac_ctrl_parse_D in Hd.
      replace (fr + 176 =? 0) with false in Hd by (symmetry; apply Z.eqb_neq; lia).
      apply in_app_iff in Hd. destruct Hd as [Hd|Hd].
      - destruct (flen g j <? 50) eqn:El; cbn [In] in Hd; [destruct Hd|].
        destruct Hd as [<- | []]. right; right. cbn [fst snd]. apply Z.ltb_ge in El.
        split; [lia|]. exists phi, (AC.a_size (flen g j)). split; [exact Hinphi|].
        unfold AC.a_size. lia.
      - cbn [In] in Hd. destruct Hd as [<- | []]. right; left. cbn [fst snd]. lia. }
    destruct (fra_fp B APIf ra g fr _ regs m2 md [1%nat] REAC_CTRL_PARSE_K
                (reac_ctrl_parse_W (fr + 176) (AC.aspZ regs))
                (reac_ctrl_parse_D phi (flen g j) (fr + 176)) HFRA2
                ltac:(intros c Hc; cbn [In] in Hc; destruct Hc as [<- | []]; lia) ltac:(lia) HWc HDc)
      as (FS & HFP & HTLS & HFPdj & HFS1).
    destruct (fra_callee_fp B APIf ra g fr _ regs m2 md REAC_CTRL_PARSE_K [1%nat] FS
                (AC.aspZ regs - REAC_CTRL_PARSE_K) (AC.aspZ regs) _ _ HFRA2 ltac:(lia) HFP HTLS
                ltac:(lia) ltac:(lia)) as (HK1 & HK2 & HK3 & HSTKw & HAPPw & HADw & _ & _).
    rewrite Haspz in HK1, HK2, HK3, HSTKw, HADw, HFP, HTLS.
    pose proof HFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & _ & Htpb & Hpl & _).
    destruct Hpl as (HFSpos & _ & _ & HFSapp & _).
    assert (HFS64 : 0 <= FS < 2 ^ 64).
    { pose proof (HFSapp FS ltac:(unfold FS_SIZE; lia)) as Ha. unfold app_mem in Ha. lia. }
    pose proof (bytes_at_le8_word rsegs m2 _ _ Htpb) as Htp2.
    rewrite MState.unsigned_lit in Htp2 by lia.
    pose proof HFRA2 as (A4 & sp4 & s54 & HRT2 & _ & HRO2 & _).
    assert (HAG2 : forall a, in_globals AF.frame_AG a -> addressable m2 a 1).
    { destruct HFRA2 as (A3 & sp3 & s53 & HRT3 & HAH3 & Hro3 & Hsn3 & Hhalt3 & Hgimg3 & Hr23 & Hspm3 & Haspz3 &
        Hstklo3 & Hr43 & Hr83 & Hr93 & Hr33 & Hr193 & Hr263 & Hfrm3 & Hs53 & HAm3 & HAS3 & Hspa3 & Hfa3 & HA4163 &
        HS43 & HAPP3 & Hspill3 & Hsel3 & Hfr243 & Hloc3 & Hhdr13 & Hhdr23 & Hsh3 & Hwin3 & Hsaved3 & Herrno3 &
        HAG3 & _). exact HAG3. }
    assert (HBCA2 : addressable m2 REAC_CTRL_PARSE_BC 6).
    { unfold REAC_CTRL_PARSE_BC. split; [lia|]. split; [lia|]. split; [lia|].
      intros i Hi.
      assert (Hg : addressable m2 (0x21200 + i) 1).
      { apply HAG2. exists 0x21200, 7. split; [|lia].
        unfold AF.frame_AG. cbn [In]. repeat (first [left; reflexivity | right]). }
      destruct Hg as (_ & _ & _ & Hg). pose proof (Hg 0 ltac:(lia)) as Hg0. rewrite Z.add_0_r in Hg0.
      exact Hg0. }
    destruct (f3_rt_cells _ _ _ HRT2) as (HBY1 & HBY2 & HBY3 & HBY4 & HBY5).
    (* the record's bytes and the block's addressability, kept by the five shadow stores *)
    assert (KP2 : forall x, phi <= x < phi + AC.a_size (flen g j) -> mbyte rsegs m2 x = mbyte rsegs mem x).
    { intros x Hx. apply KW1; [lia|]. apply HWapp. exact (proj1 (Hpall x Hx)). }
    assert (HRD2 : 50 <= flen g j -> bytes_at rsegs m2 phi (t_g (g_in g) j)).
    { intros Hl. apply (f1_bkeep mem m2); [|exact (HPb Hl)]. unfold t_g. rewrite fr50_length.
      intros x Hx. apply KP2. unfold AC.a_size. lia. }
    assert (HAD2 : addressable m2 phi (AC.a_size (flen g j))).
    { apply (f1_addr_keep mem m2 _ _ Hphiad). intros i Hi. apply KW1.
      - pose proof (shadow_of_app (phi + i) (proj1 (Hpall (phi + i) ltac:(lia)))) as Hs.
        pose proof (in_shadow_range _ Hs). lia.
      - unfold f3_Wsh. cbn [Frame.outside]. split; [|exact I]. intros HCx. unfold Sfr in HCx.
        destruct Hphifr as [Hd|Hd].
        + pose proof (f3_sh_lt2 (phi + i) fr ltac:(lia) ltac:(lia) Hfr8). lia.
        + assert (E : shadow_addr (fr + FRAME_BYTES) = shadow_addr fr + FRAME_SHADOW).
          { unfold shadow_addr. replace (fr + FRAME_BYTES) with (fr + FRAME_SHADOW * 8) by lia. rewrite Z.div_add by lia. lia. }
          pose proof (f3_sh_mono (fr + FRAME_BYTES) (phi + i) ltac:(lia)). lia. }
    destruct (f3_place g j phi fr regs mem md HFRA 1 ltac:(lia)) as (_ & Hphisp & _).
    eapply LE.evt_mono.
    { eapply (f3_calln _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 A phi (flen g j) (fr + 176) sp FS
                (t_g (g_in g) j) junk).
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - exact Hspm.
      - lia.
      - lia.
      - lia.
      - exact HSTKw.
      - exact HRO2.
      - unfold t_g. apply fr50_length.
      - apply f3_rd8.
        + unfold q64 in Hq248. apply (f1_bkeep mem m2); [|exact Hq248]. rewrite length_le8.
          intros x Hx. apply KW1; [lia|]. apply HWapp. unfold app_mem. right. lia.
        + apply length_le8.
      - intros Hl. destruct (f3_place g j phi fr regs mem md HFRA 50 ltac:(unfold AC.a_size; lia))
          as (_ & Hp50 & _). rewrite Haspz in Hp50. split; [lia|]. split; [lia|]. left. lia.
      - intros i Hi.
        destruct (Z_lt_ge_dec (flen g j) 50) as [Hlt|Hge].
        + exfalso. unfold cp_rd in Hi. replace (negb (50 <=? flen g j)) with true in Hi
            by (symmetry; apply negb_true_iff, Z.leb_gt; lia). destruct Hi.
        + pose proof (f3_cp_rd_lt _ _ _ Hi) as Hi50.
          destruct (HRD2 ltac:(lia)) as (_ & _ & Hn). apply Hn. unfold t_g. rewrite fr50_length. exact Hi50.
      - clear - HFRAMEb HFRAMEs Hfrm. Z.div_mod_to_equations. lia.
      - exact HRWo.
      - destruct (Hapart REAC_CTRL_PARSE_K ltac:(lia)) as [Hd|Hd]; [left; lia | right; lia].
      - intros Hl. destruct (f3_place g j phi fr regs mem md HFRA 50 ltac:(unfold AC.a_size; lia))
          as (Hf50 & _ & _). destruct Hf50 as [Hd|Hd]; [right; lia | left; lia].
      - exact (AsanRTInv.RT_cells _ _ _ HRT2).
      - exact (AsanRTInv.RT_shadow_rw _ _ _ HRT2).
      - lia.
      - lia.
      - exact HADw.
      - intros Hl.
        pose proof (addressable_sub m2 phi (AC.a_size (flen g j)) 0 50 HAD2 ltac:(lia) ltac:(lia)
                      ltac:(unfold AC.a_size; lia)) as Ha50.
        rewrite Z.add_0_r in Ha50. exact Ha50.
      - exact HADDRo.
      - apply Happ. lia.
      - right. lia.
      - exact HBCA2.
      - exact HBY1.
      - exact HBY2.
      - exact HBY3.
      - exact HBY4.
      - exact HBY5.
      - rewrite HTPu. exact HFP.
      - rewrite HTPu. exact HTLS. }
    { intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & tt3 & tt4 & tt5 & tt6 & m' &
        E & MU3 & WM3 & HRS3 & ST3 & RW3 & SW3 & AD3 & FSS3 & CLS3).
      eexists _, (Z_to_bv 64 0x81dfc), m'. split; [exact E|].
      split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      exists m2, FS.
      split; [exact HFRA2|]. split; [exact HENT2|]. split; [exact HADDRo|]. split; [exact MU2|].
      split; [exact Htp2|]. split; [exact HFS64|].
      split; [exact MU3|]. split; [exact WM3|]. split; [exact HRS3|]. split; [exact ST3|].
      split; [exact RW3|]. split; [exact SW3|]. split; [exact AD3|]. split; [exact FSS3 | exact CLS3]. }
  - (* rebuilding the exit cut *)
    intros R0 pc' mem' regs' md'
      (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er20 & Er21 & Er22 & Er26 & Er23 & Er18 & Er25 & Er10 &
       m2 & FS & HFRA2 & HENT2 & HADo2 & MU2 & Htp2 & HFS & MU3 & WM3 & HRS3 & ST3 & RW3 & SW3 & AD3 & FSS3 & CLS3)
      Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr25 : getr regs' 25 = Z_to_bv 64 (phi + 18)) by (rewrite Hreg; exact Er25).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 (fst (ctrlparse (flen g j) (t_g (g_in g) j))))
      by (rewrite Hreg; exact Er10).
    pose proof MU3 as MU3s.
    rewrite <- Haspz in MU3, ST3, AD3.
    destruct (f3_fra_call g fr _ regs regs' m2 mem' md md' FS _ HFRA2 Htp2 HFS MU3 WM3 HRS3 ST3 AD3 RW3 SW3
                FSS3 CLS3 Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat) as (HFRA' & HENTi).
    pose proof (HENTi HENT2) as HENT'.
    (* the two write sets and what lies outside them *)
    destruct (AC.a_laws_fs_place _ _ _ _ _ LAWS _ _ _ FS HAH
                ltac:(apply (word_mem_frame rsegs m2 mem _ _ Htp2); intros k Hk; symmetry;
                      apply (KindBGlue.mbyte_munch rsegs (f3_Wsh fr) mem m2); [exact MU2 | lia |];
                      apply (f3_Wsh_app fr _ Hfr0 ltac:(lia)); unfold app_mem; left; lia) HFS)
      as (HFSgt & HFSst & HFSal & HFSapp).
    pose proof (HFSfr FS ltac:(apply (word_mem_frame rsegs m2 mem _ _ Htp2); intros k Hk; symmetry;
                      apply (KindBGlue.mbyte_munch rsegs (f3_Wsh fr) mem m2); [exact MU2 | lia |];
                      apply (f3_Wsh_app fr _ Hfr0 ltac:(lia)); unfold app_mem; left; lia) HFS) as HFSlow.
    assert (HFS8 : FS mod 8 = 0) by (clear - HFRAMEb HFRAMEs HFSal; Z.div_mod_to_equations; lia).
    assert (Hsp8 : (sp - 8800) mod 8 = 0) by (clear - HFRAMEb HFRAMEs Hspm; Z.div_mod_to_equations; lia).
    assert (HFSlo : FS + AC.FS_SIZE <= LOWMEM_END \/ HIGHMEM_BEG <= FS).
    { pose proof (HFSapp FS ltac:(lia)) as P1. pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(lia)) as P2.
      unfold app_mem in P1, P2. lia. }
    assert (Ho0 : fr + 176 <> 0) by lia.
    assert (Hoa : fr + 212 <= LOWMEM_END \/ HIGHMEM_BEG <= fr + 176).
    { pose proof (Happ (fr + 176) ltac:(lia)) as P1. pose proof (Happ (fr + 211) ltac:(lia)) as P2.
      unfold app_mem in P1, P2. lia. }
    assert (HFSE : FS + AC.FS_SIZE <= APPMEM_END) by lia.
    assert (HSHO : forall y, 0 <= y < APPMEM_END -> (y < FS + 1085440 \/ FS + 2134016 <= y) ->
              (y < sp - 8800 \/ sp <= y) -> Frame.outside (f3_PW (fr + 176) sp FS) (shadow_addr y)).
    { intros y Hy Hy1 Hy2. apply f3_PW_out_sh; try lia. }
    assert (HAPO : forall x, app_mem x -> ~ (fr + 176 <= x < fr + 212) -> ~ (sp - 8800 <= x < sp) ->
              ~ (FS + 8 <= x < FS + 16) -> ~ (FS + 20480 <= x < FS + 28672) ->
              ~ (FS + 1085440 <= x < FS + 2134016) -> Frame.outside (f3_PW (fr + 176) sp FS) x).
    { intros x Hx N1 N2 N3 N4 N5.
      apply f3_PW_out_app; [lia | exact Hx | lia | lia | lia | lia | lia | lia | lia | lia | lia]. }
    assert (KW1 : forall x, 0 <= x < 2 ^ 64 -> Frame.outside (f3_Wsh fr) x -> mbyte rsegs m2 x = mbyte rsegs mem x)
      by (intros x Hx Ho; exact (KindBGlue.mbyte_munch rsegs (f3_Wsh fr) mem m2 x MU2 Hx Ho)).
    assert (KW2 : forall x, 0 <= x < 2 ^ 64 -> Frame.outside (f3_PW (fr + 176) sp FS) x ->
              mbyte rsegs mem' x = mbyte rsegs m2 x)
      by (intros x Hx Ho; exact (KindBGlue.mbyte_munch rsegs _ m2 mem' x MU3s Hx Ho)).
    assert (HWapp : forall x, app_mem x -> Frame.outside (f3_Wsh fr) x)
      by (intros x Hx; exact (f3_Wsh_app fr x Hfr0 ltac:(lia) Hx)).
    (* an app byte apart from the parse output cells, the window and the side stack, and its shadow when it is
       also apart from the frame's parse cells *)
    assert (KAPP : forall x, app_mem x -> ~ (fr + 176 <= x < fr + 212) -> ~ (sp - 8800 <= x < sp) ->
              (x < FS \/ FS + AC.FS_SIZE <= x) -> mbyte rsegs mem' x = mbyte rsegs mem x).
    { intros x Hx N1 N2 N3. assert (Hxr : 0 <= x < 2 ^ 64) by (unfold app_mem in Hx; lia).
      rewrite (KW2 x Hxr ltac:(apply HAPO; [exact Hx | exact N1 | exact N2 | lia | lia | lia])).
      exact (KW1 x Hxr (HWapp x Hx)). }
    assert (KSH : forall y, app_mem y -> (y < fr + 176 \/ fr + 216 <= y) -> ~ (sp - 8800 <= y < sp) ->
              (y < FS \/ FS + AC.FS_SIZE <= y) ->
              mbyte rsegs mem' (shadow_addr y) = mbyte rsegs mem (shadow_addr y)).
    { intros y Hy N1 N2 N3.
      pose proof (in_shadow_range _ (shadow_of_app y Hy)) as Hsr.
      assert (Hy0 : 0 <= y < APPMEM_END) by (unfold app_mem in Hy; lia).
      rewrite (KW2 (shadow_addr y) ltac:(lia) ltac:(apply HSHO; lia)).
      apply KW1; [lia|]. unfold f3_Wsh. cbn [Frame.outside]. split; [|exact I]. intros HCx. unfold Sfr in HCx.
      destruct N1 as [Hd|Hd].
      - destruct (Z_lt_ge_dec y fr) as [Hy1|Hy1].
        + pose proof (f3_sh_lt2 y fr ltac:(lia) Hy1 Hfr8). lia.
        + assert (E : shadow_addr y < shadow_addr fr + 22).
          { unfold shadow_addr. assert (y / 8 < fr / 8 + 22) by (Z.div_mod_to_equations; lia). lia. }
          lia.
      - assert (E : shadow_addr fr + 27 <= shadow_addr y).
        { unfold shadow_addr. assert (fr / 8 + 27 <= y / 8) by (Z.div_mod_to_equations; lia). lia. }
        lia. }
    assert (HFRwin : forall x, fr <= x < fr + FRAME_BYTES -> ~ (sp - 8800 <= x < sp)).
    { intros x Hx Hw. destruct (Hapart REAC_CTRL_PARSE_K ltac:(lia)) as [Hd|Hd]; lia. }
    (* frame bytes off the parse cells, and their shadow off the parse cells' granules *)
    assert (KFR : forall x, fr <= x < fr + FRAME_BYTES -> ~ (fr + 176 <= x < fr + 212) ->
              mbyte rsegs mem' x = mbyte rsegs mem x).
    { intros x Hx N1. assert (Hxr : 0 <= x < 2 ^ 64) by lia.
      rewrite (KW2 x Hxr ltac:(apply HAPO; [apply Happ; lia | exact N1 | exact (HFRwin x Hx) | lia | lia | lia])).
      exact (KW1 x Hxr (HWapp x (Happ x Hx))). }
    assert (KFSH : forall x, fr <= x < fr + FRAME_BYTES -> (x < fr + 176 \/ fr + 216 <= x) ->
              mbyte rsegs mem' (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
    { intros x Hx N1. pose proof (Happ x Hx) as Hxa.
      pose proof (in_shadow_range _ (shadow_of_app x Hxa)) as Hsr.
      rewrite (KW2 (shadow_addr x) ltac:(lia)
                 ltac:(apply HSHO; [lia | lia | destruct (Hapart REAC_CTRL_PARSE_K ltac:(lia)); lia])).
      apply KW1; [lia|]. unfold f3_Wsh. cbn [Frame.outside]. split; [|exact I]. intros HCx. unfold Sfr in HCx.
      destruct N1 as [Hd|Hd].
      - assert (E : shadow_addr x < shadow_addr fr + 22).
        { unfold shadow_addr. assert (x / 8 < fr / 8 + 22) by (Z.div_mod_to_equations; lia). lia. }
        lia.
      - assert (E : shadow_addr fr + 27 <= shadow_addr x).
        { unfold shadow_addr. assert (fr / 8 + 27 <= x / 8) by (Z.div_mod_to_equations; lia). lia. }
        lia. }
    (* the save area: above sp, apart from every write *)
    assert (KA : forall x, A + 32 <= x < A + 304 -> mbyte rsegs mem' x = mbyte rsegs mem x).
    { intros x Hx. apply KAPP; [unfold app_mem; right; lia | lia | lia | lia]. }
    (* a byte of a live block below stklo, off the side stack *)
    assert (KBLK : forall x, (exists q k, In (q, k) (hb1 phi (AC.a_size (flen g j)) ++ g_H g) /\ q <= x < q + k) ->
              mbyte rsegs mem' x = mbyte rsegs mem x /\
              mbyte rsegs mem' (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
    { intros x (q & k & Hin & Hx).
      destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md q k HAH Hin) as (_ & Hq4 & Hqk & _ & Hall).
      destruct (Hall x Hx) as (Hxa & _ & _ & _ & Hnfs).
      assert (Hnfr : ~ (fr <= x < fr + FRAME_BYTES)).
      { intros Hfx. destruct Hloc as [(_ & _ & Hreal) | (_ & _ & Hfs & _)].
        - pose proof (Hreal x Hfx). lia.
        - exact (Hnfs (Hfs x Hfx)). }
      assert (HnF : x < FS \/ FS + AC.FS_SIZE <= x).
      { destruct (Z_lt_ge_dec x FS) as [H1|H1]; [left; exact H1|].
        destruct (Z_lt_ge_dec x (FS + AC.FS_SIZE)) as [H2|H2]; [|right; lia].
        exfalso. apply Hnfs. exists FS. split; [exact HFS|]. split; [|lia].
        apply (word_mem_frame rsegs m2 mem _ _ Htp2). intros kk Hkk. symmetry.
        apply (KindBGlue.mbyte_munch rsegs (f3_Wsh fr) mem m2); [exact MU2 | lia |].
        apply HWapp. unfold app_mem. left. lia. }
      split.
      - apply KAPP; [exact Hxa | lia | lia | exact HnF].
      - apply KSH; [exact Hxa | lia | lia | exact HnF]. }
    assert (KIMG : forall x, 0 <= x < AC.GT -> mbyte rsegs mem' x = mbyte rsegs mem x /\
              mbyte rsegs mem' (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
    { intros x Hx. split.
      - apply KAPP; [unfold app_mem; left; lia | lia | lia | lia].
      - apply KSH; [unfold app_mem; left; lia | lia | lia | lia]. }
    assert (H9' : rg regs' 9 A) by (unfold rg in *; rewrite Fr9; exact H9).
    assert (HHB' : HB mem' phi (flen g j)).
    { split; [exact Hphinz|]. apply (f1_addr_keep mem mem' _ _ Hphiad). intros i Hi.
      apply (KBLK (phi + i)). exists phi, (AC.a_size (flen g j)). split; [exact Hinphi | lia]. }
    assert (HFLSI' : FLSI g j fr regs' mem').
    { split.
      { apply (flsh_move g j fr regs regs' A mem mem' HFLSH H9 HA ltac:(lia) Fr9).
        - intros x Hx. apply KA. lia.
        - intros x Hx. apply KFSH; lia.
        - intros x Hx. assert (Hn0 : 0 < g_n g) by lia. destruct (HIN) as (HinP & _ & _).
          apply (KBLK x). exists (g_p g), (g_n g). split; [apply in_or_app; right; exact (HinP Hn0) | lia].
        - exact (fra_stk B APIf ra g fr _ regs' mem' md' HFRA'). }
      split; [exact (f1_spill_move regs regs' A 216 _ mem mem' HS216 H9 HA ltac:(lia) ltac:(lia) Fr9
                       ltac:(intros x Hx; apply KA; lia))|].
      split; [exact (f1_spill_move regs regs' A 224 _ mem mem' HS224 H9 HA ltac:(lia) ltac:(lia) Fr9
                       ltac:(intros x Hx; apply KA; lia))|].
      split; [exact (f1_spill_move regs regs' A 248 _ mem mem' HS248 H9 HA ltac:(lia) ltac:(lia) Fr9
                       ltac:(intros x Hx; apply KA; lia))|].
      split.
      - destruct HIN as (HinP & HaddrP & HbytesP).
        split; [exact HinP|]. split.
        + apply (f1_addr_keep mem mem' _ _ HaddrP). intros i Hi. assert (Hn0 : 0 < g_n g) by lia.
          apply (KBLK (g_p g + i)). exists (g_p g), (g_n g).
          split; [apply in_or_app; right; exact (HinP Hn0) | lia].
        + apply (f1_bkeep mem mem'); [|exact HbytesP]. intros x Hx. rewrite <- g_n_len in Hx.
          assert (Hn0 : 0 < g_n g) by lia.
          apply (KBLK x). exists (g_p g), (g_n g). split; [apply in_or_app; right; exact (HinP Hn0) | lia].
      - apply (flc_move fr regs regs' A mem mem' HFLC H9 HA ltac:(lia) Fr9).
        + intros x Hx. apply KA. lia.
        + intros x Hx. apply KFSH; lia. }
    assert (HLK' : LK g fr j regs' mem').
    { destruct HLK as (Hjj & H21 & HOUR). split; [exact Hjj|]. split; [unfold rg in *; rewrite Fr21; exact H21|].
      unfold OURb in *. apply (f1_bkeep mem mem'); [|exact HOUR]. rewrite OUR_length.
      intros x Hx. apply KFR; lia. }
    assert (HC' : b5_C g j phi fr regs' mem').
    { apply (b5c_move g j phi fr regs regs' A mem mem' HC H9 HA ltac:(lia) Fr2 Fr9 Fr18 Fr23).
      - exact KA.
      - intros x Hx. apply KFR; lia.
      - intros x Hx. apply KFSH; lia.
      - intros Hl x Hx. apply (KBLK x). exists phi, (AC.a_size (flen g j)).
        split; [exact Hinphi | unfold AC.a_size; lia].
      - exact KIMG. }
    assert (HREC' : 50 <= flen g j -> bytes_at rsegs mem' phi (t_phi (g_in g) j)).
    { intros Hl. apply (f1_bkeep mem mem'); [|exact (HREC Hl)]. rewrite f2_phi_len.
      intros x Hx. rewrite Z2Nat.id in Hx by lia. apply (KBLK x). exists phi, (AC.a_size (flen g j)).
      split; [exact Hinphi | unfold AC.a_size; lia]. }
    assert (HOUT' : bytes_at rsegs mem' (fr + 176) (snd (ctrlparse (flen g j) (t_g (g_in g) j)))).
    { destruct RW3 as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
    assert (HADo' : addressable mem' (fr + 176) 36).
    { apply (f1_addr_keep m2 mem' _ _ HADo2). intros i Hi.
      pose proof (in_shadow_range _ (shadow_of_app (fr + 176 + i) (Happ (fr + 176 + i) ltac:(lia)))) as Hsr.
      apply KW2; [lia|]. apply HSHO; [lia | lia | destruct (Hapart REAC_CTRL_PARSE_K ltac:(lia)); lia]. }
    rewrite <- SEGS. apply Hexit. cbv beta.
    exists phi, regs', mem', md', fr. split; [reflexivity|].
    split; [exact HFRA'|]. split; [exact HENT'|].
    split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB'|]. split; [exact HFLSI'|].
    split; [exact HLK'|]. split; [exact HC'|].
    (* the 0x81dfc body *)
    split.
    { destruct HFC as (Hs224 & H20 & H18). split; [|split].
      - exact (f1_spill_move regs regs' A 224 _ mem mem' Hs224 H9 HA ltac:(lia) ltac:(lia) Fr9
                 ltac:(intros x Hx; apply KA; lia)).
      - unfold rg in *. rewrite Fr20. exact H20.
      - unfold rg in *. rewrite Fr18. exact H18. }
    split; [unfold rg; rewrite Fr10; reflexivity|].
    split; [unfold rg; exact Fr25|].
    split; [intros Hl; unfold rg in *; rewrite Fr22; exact (H22 Hl)|].
    split; [exact (f3_c7 mem' (fr + 176) (flen g j) (t_g (g_in g) j) RW3)|].
    split.
    { destruct HIDj as (HIDb & Hidok). split; [|exact Hidok]. unfold IDBe in *.
      apply (f1_bkeep mem mem'); [|exact HIDb]. destruct (f1_FS_len (g_in g) j) as (L38 & _). rewrite L38.
      intros x Hx. apply KFR; lia. }
    exact (f3_b5pf g j phi fr regs' mem' md' HFRA' HHB' HFLSI' HC' HREC' HOUT' HADo').
Qed.

End S.
