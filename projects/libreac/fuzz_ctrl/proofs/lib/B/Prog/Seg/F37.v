(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names changed; 2169 of its 2293 lines of code are new or changed and 887 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F30.v, with its module names and numbers changed; 924 of its 1033 lines of code are new or changed and 2184 lines of the source are left out. *)
(* Segment F37 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B): 0x82ca0-0x82d18, the end of one turn
   of the frame loop after the catalogue work (slot-plan-asan-ubsan section 2 row F37, call FREE@0x82d18, twin
   C05). Image A's twin is 0x828d8-0x8293c (no image-A lemma yet).
   rule 24: no function proved.

     0x82ca0  ld s5,240(s1)       -- s5 = [A + 240] = j, the frame index (LK's spill).
     0x82ca4  bne a0,s7,82fa4     -- NOT taken: a0 = t_want j (the catalogue_match result) equals s7 = t_want_m j
                                     (the row the row_of_block scan found, or 0); 0x82fa4 is the abort pair.
     0x82ca8  ld s7,224(s1)       -- s7 = [A + 224] = p + body_j ...
     0x82cac  add s7,s7,s4        --   ... + len_j (s4) = p + c_(j+1).
     0x82cb0  ld a0,232(s1)       -- a0 = [A + 232] = left_j - h_j ...
     0x82cb4  sub s9,a0,s4        --   s9 = left_j - h_j - len_j = left_(j+1).
     0x82cb8 .. 0x82d10  23 x sb s11,off(s3)
                                  -- s3 = S(fr) = (fr >> 3) + 0x7fff8000, the frame's shadow base, s11 = -8; the 23
                                     stores mark the shadow bytes S(fr) + 22 .. S(fr) + 66 0xf8 (the frame's local
                                     variables go out of scope). They lie inside the frame's FRAME_SHADOW (392)
                                     shadow bytes, so no app byte changes.
     0x82d14  mv a0,s2            -- a0 = s2 = Phi, the turn's heap block.
     0x82d18  jal wrapper_free    -- free(Phi) (as_free = 0x534b4, the allocator entry of AC.aa_free); return
                                     point 0x82d1c.

   The range has one failure branch (0x82ca4 to the abort pair 0x82fa4), no branch to 0x82fa0 and no instrumented
   check: the 23 shadow stores are the runtime's out-of-scope marks, not checks. The free is the allocator's own
   contract AC.aa_free (a field of APIf): it removes the block (Phi, len) from the live list, so the exit cut
   carries the empty extra list []. FRA moves across the 23 shadow stores by Tac_slot.sl_fr_meta (AH, the owned
   set and the stack bounds by f37_ah: a_laws_store on the real arm, Tac_fs.a_fs_ok_store_AH on the side arm) and
   ENT by Tac_slot.ent_store; across the free, FRA moves by Tac_slot.sl_mid and ENT by Tac_slot.ent_call, the
   callee precondition being SlotInv.fra_call_pre. The bytes the cuts read are kept across the free by
   AC.a_call_post_frame (f37_keep and its siblings): they are not the allocator's (a_laws_not_owned: the stack at or above stklo,
   the side stack, the live blocks and their shadow; a_laws_client: the client data and the image's shadow;
   frame_facts: the RELRO bytes), and none is in the callee's window, errno, the OOM flag or the freed block.
   FRA's input facts (the input bytes at p and, for n > 0, the block (p, n) live and addressable), which sl_mid
   asks for after the free, are kept the same way: the input block is a live block of the entry heap.
   The free (v1.9 afree_at) also asks for a per-class bound Bc of the call heap and its room inequality: the local
   lemma f37_free, the one application of afree_at, takes them from ENT's per-class conjunct (its 14th) by
   Tac_cls.sl_free_cls, with Bc = Tac_cls.Bc_of BE.

   Entry SlotInv.v's Inv_B82ca0_at (FCUTP; it took this file's former local cut): F35's catalogue facts plus what
   this range reads or hands to F38: the bne operands are equal (t_want j = t_want_m j), the cursor spills
   [A + 224] = p + body_j and [A + 232] = left_j - h_j (FTURN), the spill [A + 272] = k_j, s6 = 1, and the frame
   records and the first-fragment state of turn j + 1 (IFS g fr (S j)). Its live block is the allocator's
   (phi, AC.a_size (flen g j)), the block the free releases.
   Exit SlotInv.v's Inv_B82d1c_at (F38's entry). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Exec Step Tac Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro Tac_fs Tac_cls.
Import ListNotations.
(* Image B's registers, mkst and FPState (the short name YK11 may resolve to lib/Reusable/YK11.v). *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module ULMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL.Mem.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_stack_malloc_c.
Module BYI14 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YI14.
Module BYK0s := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK0s.

(* ===================== bit-vector and memory helpers ===================== *)

Lemma f37_ulit : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 x) = x.
Proof. intros x H. exact (ULMem.wa_unsigned x H). Qed.

Lemma f37_bv_inj : forall a b, Z_to_bv 64 a = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof.
  intros a b E Ha Hb. apply (f_equal (bv_unsigned (n := 64))) in E.
  rewrite (f37_ulit a Ha), (f37_ulit b Hb) in E. exact E.
Qed.

(* The engine's forms of `add` and `sub` on two literals' words. *)
Lemma f37_bv_add : forall a b, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + bv_unsigned (Z_to_bv 64 b)) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma f37_bv_sub : forall a b, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) - bv_unsigned (Z_to_bv 64 b)) = Z_to_bv 64 (a - b).
Proof.
  intros a b. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. reflexivity.
Qed.

(* A spilled word at s1 + off read at the cut's spill base A (Seg/F17.v's f17_spill). *)
Lemma f37_spill : forall regs m off v A, spill regs m off v -> rg regs 9 A ->
  0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 -> q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA H0 H1 Hoff.
  unfold rg in HA, HA'. rewrite HA in HA'.
  pose proof Hq as (Hq0 & Hq1 & _). rewrite LMem.length_le8 in Hq1.
  assert (E : A' = A).
  { apply (f_equal (bv_unsigned (n := 64))) in HA'. rewrite !Z_to_bv_unsigned in HA'. unfold bv_wrap in HA'.
    change (bv_modulus 64) with (2 ^ 64) in HA'.
    rewrite (Z.mod_small A) in HA' by lia. Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.

(* bytes_at moves to a memory that agrees with the old one on the bytes' own range. *)
Lemma f37_ba_eq : forall m m' a bs, LMem.bytes_at rsegs m a bs ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte rsegs m' x = mbyte rsegs m x) ->
  LMem.bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) HK. split; [lia|]. split; [lia|].
  intros i Hi.
  assert (E : LMem.mrd rsegs m' (LMem.wa (a + Z.of_nat i)) = LMem.mrd rsegs m (LMem.wa (a + Z.of_nat i)))
    by exact (HK (a + Z.of_nat i) ltac:(lia)).
  exact (eq_trans E (H i Hi)).
Qed.

(* addressable moves to a memory that keeps the range's shadow bytes. *)
Lemma f37_addr_keep : forall m m' p n, addressable m p n ->
  (forall i, 0 <= i < n -> mbyte rsegs m' (shadow_addr (p + i)) = mbyte rsegs m (shadow_addr (p + i))) ->
  addressable m' p n.
Proof.
  intros m m' p n (H1 & H2 & H3 & H) HK. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  assert (E : LMem.mrd rsegs m' (LMem.wa (shadow_addr (p + i))) = LMem.mrd rsegs m (LMem.wa (shadow_addr (p + i))))
    by exact (HK i Hi).
  exact (eq_trans E Hb).
Qed.

(* stk moves to a memory that keeps the bytes and the writability of the range. *)
Lemma f37_stk_keep : forall m m' lo hi, LFr.stk rsegs m lo hi ->
  (forall x, lo <= x < hi -> mbyte rsegs m' x = mbyte rsegs m x /\
     (writable_at rsegs m x -> writable_at rsegs m' x)) ->
  LFr.stk rsegs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & H) HK. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). destruct (HK a Ha) as (Hm & Hwr). split.
  - exact (Hwr Hw).
  - exists b.
    assert (E : LMem.mrd rsegs m' (LMem.wa a) = LMem.mrd rsegs m (LMem.wa a)) by exact Hm.
    exact (eq_trans E Hb).
Qed.

(* A byte present in a memory is still present after a store: write_to_mem only turns None cells into Some. *)
Lemma f37_pres_write : forall m a bs q,
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= q < 2 ^ 64 ->
  (exists b, mrd rsegs m (wa q) = Some b) ->
  exists b, mrd rsegs (write_to_mem m (wa a) bs) (wa q) = Some b.
Proof.
  intros m a bs q Ha Hl Hq (b & Hb). unfold mrd in *.
  rewrite ULMem.write_to_mem_spec by lia. rewrite ULMem.wa_unsigned by lia.
  destruct (Z.leb_spec0 a q) as [H1|H1]; destruct (Z.ltb_spec0 q (a + Z.of_nat (length bs))) as [H2|H2];
    cbn [andb]; try (exists b; exact Hb).
  destruct (nth_error bs (Z.to_nat (q - a))) as [b0|] eqn:En.
  - exists b0. reflexivity.
  - apply nth_error_None in En. lia.
Qed.

(* Every FakeStack metadata cell lies in [FS, FS + 36864) (Seg/F34.v's f34_fs_meta_range). *)
Lemma f37_fs_meta_range : forall FS q, Tac_fs.fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q [Hq|[Hq|[(c & Hc & Hq)|(c & jj & Hc & Hj & Hq)]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hq. lia.
  - subst q. exact (Tac_fs.a_fs_flag_range FS c jj Hc Hj).
Qed.

(* Every interval of W starts at or above GT, so W misses the runtime's cells (Seg/F16.v's f16_rtdj_GT). *)
Lemma f37_dj_GT : forall (W : list (Z * Z)) a n,
  (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> a + n <= AC.GT -> LFr.disjoint_from W a n.
Proof.
  intros W a n H Hn. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  split.
  - left. pose proof (H lo hi ltac:(left; reflexivity)). lia.
  - apply IH. intros lo' hi' Hin. apply (H lo' hi'). right. exact Hin.
Qed.

Lemma f37_rtdj_GT : forall (W : list (Z * Z)),
  (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> AsanRTInv.rt_disjoint W.
Proof.
  intros W H. unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF,
    RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
    RT_AGLOB, RT_AGLOB_LEN, AC.GT in *.
  repeat split; apply (f37_dj_GT W); solve [ exact H | unfold AC.GT; lia ].
Qed.

(* A shadow byte among the 23 out-of-scope marks is the shadow of a frame byte. *)
Lemma f37_sh_in_fr : forall fr x, fr mod 32 = 0 -> Sfr fr + 22 <= shadow_addr x < Sfr fr + 67 ->
  fr <= x < fr + FRAME_BYTES.
Proof. intros fr x Hfr Hx. rewrite FRAME_BYTES_val. unfold Sfr, shadow_addr in *. Z.div_mod_to_equations. lia. Qed.

Lemma f37_m8 : forall fr, fr mod 32 = 0 -> fr mod 8 = 0.
Proof. intros fr H. Z.div_mod_to_equations. lia. Qed.

Lemma f37_Sfr_GT : forall fr, AC.GT <= fr -> AC.GT + 22 <= Sfr fr.
Proof. intros fr H. unfold Sfr, shadow_addr, ASAN_K, AC.GT in *. Z.div_mod_to_equations. lia. Qed.

Lemma f37_sh_lt : forall a fr, 0 <= a < AC.GT -> AC.GT <= fr -> shadow_addr a < Sfr fr + 22.
Proof. intros a fr Ha Hfr. unfold Sfr, shadow_addr, AC.GT in *. Z.div_mod_to_equations. lia. Qed.

Lemma f37_sh_rng : forall x, 0 <= x < 2 ^ 64 -> 0 <= shadow_addr x < 2 ^ 64.
Proof. intros x Hx. unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. Qed.

Lemma f37_sh_our : forall fr i, fr mod 32 = 0 -> 0 <= i < 6 -> shadow_addr (fr + 2624 + i) = Sfr fr + 328.
Proof. intros fr i Hfr Hi. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* The two frame records [fr + 2688, fr + 2726) and [fragb fr, fragb fr + 72) = [fr + 2768, fr + 2840) have their
   shadow bytes in [S(fr) + 336, S(fr) + 355), above the marked [S(fr) + 22, S(fr) + 67). *)
Lemma f37_sh_rad : forall fr i, fr mod 32 = 0 -> 0 <= i < 152 ->
  Sfr fr + 336 <= shadow_addr (fr + 2688 + i) < Sfr fr + 355.
Proof. intros fr i Hfr Hi. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* The local `first` [fr + 2880, fr + 2920) (FSb, RAD's third range) has its shadow bytes in
   [S(fr) + 360, S(fr) + 365), above the marked [S(fr) + 22, S(fr) + 67). *)
Lemma f37_sh_first : forall fr i, fr mod 32 = 0 -> 0 <= i < 40 ->
  Sfr fr + 360 <= shadow_addr (fr + 2880 + i) < Sfr fr + 365.
Proof. intros fr i Hfr Hi. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* A byte of the frame's FRAME_SHADOW shadow bytes is the shadow of the frame byte 8 (x - K). *)
Lemma f37_sh_pre : forall fr x, fr mod 32 = 0 -> Sfr fr <= x < Sfr fr + FRAME_SHADOW ->
  shadow_addr (8 * (x - ASAN_K)) = x /\ fr <= 8 * (x - ASAN_K) < fr + FRAME_BYTES.
Proof.
  intros fr x Hfr Hx. rewrite FRAME_SHADOW_val in Hx. rewrite FRAME_BYTES_val. split.
  - unfold shadow_addr. replace (8 * (x - ASAN_K)) with ((x - ASAN_K) * 8) by lia.
    rewrite Z.div_mul by lia. lia.
  - unfold Sfr, shadow_addr in Hx. Z.div_mod_to_equations. lia.
Qed.

(* An address range inside one loaded segment is image memory. *)
Lemma f37_img_rng : forall lo hi,
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs
    = true ->
  forall x, lo <= x < hi -> AC.a_in_img x.
Proof.
  intros lo hi H x Hx. apply existsb_exists in H. destruct H as (s & Hs & He).
  apply andb_prop in He as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hs | lia].
Qed.

(* Every registered global lies in a loaded segment (checked by computation). *)
Lemma f37_ag_img : forall a, in_globals AF.frame_AG a -> AC.a_in_img a.
Proof.
  intros a (lo & len & Hil & Hr).
  assert (HB : forallb (fun p => existsb (fun s => (Z.of_N (seg_base s) <=? fst p) &&
                  (fst p + snd p <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in HB. specialize (HB (lo, len) Hil). cbn [fst snd] in HB.
  exact (f37_img_rng lo (lo + len) HB a Hr).
Qed.

(* ===================== the machine run ===================== *)

(* The start register map of sl_run, written with the stepping engine's mkR so the engine reads it. *)
Lemma f37_mkR_of : forall regs, Regs6ss.mkR_of regs =
  mkR (Sem.reg_get regs 1) (Sem.reg_get regs 2) (Sem.reg_get regs 3) (Sem.reg_get regs 4) (Sem.reg_get regs 5)
      (Sem.reg_get regs 6) (Sem.reg_get regs 7) (Sem.reg_get regs 8) (Sem.reg_get regs 9) (Sem.reg_get regs 10)
      (Sem.reg_get regs 11) (Sem.reg_get regs 12) (Sem.reg_get regs 13) (Sem.reg_get regs 14) (Sem.reg_get regs 15)
      (Sem.reg_get regs 16) (Sem.reg_get regs 17) (Sem.reg_get regs 18) (Sem.reg_get regs 19) (Sem.reg_get regs 20)
      (Sem.reg_get regs 21) (Sem.reg_get regs 22) (Sem.reg_get regs 23) (Sem.reg_get regs 24) (Sem.reg_get regs 25)
      (Sem.reg_get regs 26) (Sem.reg_get regs 27) (Sem.reg_get regs 28) (Sem.reg_get regs 29) (Sem.reg_get regs 30)
      (Sem.reg_get regs 31).
Proof. intros regs. reflexivity. Qed.

(* The literal length of a stored byte list. *)
Ltac f37_len :=
  repeat match goal with
  | |- context [@length byte ?bs] =>
      let n := eval vm_compute in (@length byte bs) in change (@length byte bs) with n
  end.

(* One out-of-scope mark `sb s11,off(s3)`: the shadow byte S(fr) + off is writable in every memory the run has
   reached (wr_at of [S(fr) + 22, S(fr) + 67) survives the earlier stores), so the store steps. *)
Ltac f37_sb Sf off HWR :=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let H := fresh "HSo" in
      assert (H : store_ok rsegs mm (wa (Sf + off)) 1 = true)
        by (replace (Sf + off) with (Sf + 22 + (off - 22)) by lia;
            apply (ULMem.wr_at_store_ok rsegs mm (Sf + 22) 45 (off - 22) 1);
            [repeat apply ULMem.wr_at_write; exact HWR | lia | lia])
  end; step.

(* 0x82ca0 -> 0x534b4 (the free entry, through the jal at 0x82d18). Read: the spilled words [A + 240, A + 248),
   [A + 224, A + 232) and [A + 232, A + 240). Written: the 23 shadow bytes of the frame's local variables, all in
   [S(fr) + 22, S(fr) + 67). The failure branch 0x82ca4 `bne a0,s7,82fa4` is not taken: both operands hold W. *)
Lemma f37_evt : forall (regs F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (A Sf W J v224 v232 len phi : Z),
  getr regs 9 = Z_to_bv 64 A -> getr regs 10 = Z_to_bv 64 W -> getr regs 23 = Z_to_bv 64 W ->
  getr regs 18 = Z_to_bv 64 phi -> getr regs 19 = Z_to_bv 64 Sf -> getr regs 20 = Z_to_bv 64 len ->
  getr regs 27 = Z_to_bv 64 (-8) ->
  0 <= Sf -> Sf + FRAME_SHADOW <= 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (A + 240)) 8 = Some (ULMem.le8 (Z_to_bv 64 J)) ->
  ov_read_bytes rsegs m (wa (A + 224)) 8 = Some (ULMem.le8 (Z_to_bv 64 v224)) ->
  ov_read_bytes rsegs m (wa (A + 232)) 8 = Some (ULMem.le8 (Z_to_bv 64 v232)) ->
  wr_at rsegs m (Sf + 22) 45 ->
  evt rsegs (fun ms' => exists R m', ms' = MS R F (Z_to_bv 64 0x534b4) fc None m' (seg_rom rsegs) /\
      getr R 1 = Z_to_bv 64 0x82d1c /\ getr R 10 = Z_to_bv 64 phi /\
      getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
      getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18 /\
      getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 26 = getr regs 26 /\
      getr R 27 = getr regs 27 /\ getr R 22 = getr regs 22 /\
      getr R 23 = Z_to_bv 64 (v224 + len) /\ getr R 25 = Z_to_bv 64 (v232 - len) /\
      getr R 21 = Z_to_bv 64 J /\
      munch [(Sf + 22, Sf + 67)] m m' /\ wmono rsegs m m' /\
      (forall q, 0 <= q < 2 ^ 64 -> (exists b, mrd rsegs m (wa q) = Some b) ->
         exists b, mrd rsegs m' (wa q) = Some b))
    (MS (Regs6ss.mkR_of regs) F (Z_to_bv 64 0x82ca0) fc None m (seg_rom rsegs)).
Proof.
  intros regs F fc m A Sf W J v224 v232 len phi E9 E10 E23 E18 E19 E20 E27 HS0 HS1 L240 L224 L232 HWR.
  pose proof FRAME_SHADOW_val as HFSv.
  rewrite f37_mkR_of.
  assert (R9 : Sem.reg_get regs 9 = Z_to_bv 64 A) by exact E9.
  assert (R10 : Sem.reg_get regs 10 = Z_to_bv 64 W) by exact E10.
  assert (R23 : Sem.reg_get regs 23 = Z_to_bv 64 W) by exact E23.
  assert (R18 : Sem.reg_get regs 18 = Z_to_bv 64 phi) by exact E18.
  assert (R19 : Sem.reg_get regs 19 = Z_to_bv 64 Sf) by exact E19.
  assert (R20 : Sem.reg_get regs 20 = Z_to_bv 64 len) by exact E20.
  assert (R27 : Sem.reg_get regs 27 = Z_to_bv 64 (-8)) by exact E27.
  rewrite R9, R10, R23, R18, R19, R20, R27.
  (* 0x82ca0 ld s5,240(s1) *)
  step.
  (* 0x82ca4 bne a0,s7,82fa4 (both W): not taken *)
  step. if_false.
  (* 0x82ca8 ld s7,224(s1); 0x82cac add s7,s7,s4; 0x82cb0 ld a0,232(s1); 0x82cb4 sub s9,a0,s4 *)
  step. step. step. step.
  (* 0x82cb8 .. 0x82d10: the 23 out-of-scope marks, shadow offsets 22 .. 66 of the frame *)
  f37_sb Sf 59 HWR. f37_sb Sf 60 HWR. f37_sb Sf 66 HWR. f37_sb Sf 50 HWR. f37_sb Sf 56 HWR.
  f37_sb Sf 57 HWR. f37_sb Sf 58 HWR. f37_sb Sf 46 HWR. f37_sb Sf 47 HWR. f37_sb Sf 48 HWR.
  f37_sb Sf 49 HWR. f37_sb Sf 42 HWR. f37_sb Sf 43 HWR. f37_sb Sf 44 HWR. f37_sb Sf 45 HWR.
  f37_sb Sf 26 HWR. f37_sb Sf 32 HWR. f37_sb Sf 34 HWR. f37_sb Sf 38 HWR. f37_sb Sf 22 HWR.
  f37_sb Sf 23 HWR. f37_sb Sf 24 HWR. f37_sb Sf 25 HWR.
  (* 0x82d14 mv a0,s2; 0x82d18 jal wrapper_free *)
  step. step.
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m1 := mm)
  end.
  assert (MU : munch [(Sf + 22, Sf + 67)] m m1).
  { unfold m1.
    do 23 (apply munch_write; [| lia | f37_len; lia | cbn [inside]; left; f37_len; split; lia]).
    apply munch_refl. }
  assert (WM : wmono rsegs m m1) by (unfold m1; do 23 (apply wmono_write); apply wmono_refl).
  assert (HPR : forall q, 0 <= q < 2 ^ 64 -> (exists b, mrd rsegs m (wa q) = Some b) ->
            exists b, mrd rsegs m1 (wa q) = Some b).
  { intros q Hq Hb. unfold m1.
    do 23 (apply f37_pres_write; [lia | f37_len; lia | lia |]). exact Hb. }
  finish.
  all: first [ reflexivity | apply f37_bv_add | apply f37_bv_sub | assumption
             | (rewrite ?E9, ?E10, ?E23, ?E18, ?E19, ?E20, ?E27; reflexivity) ].
Qed.

Section F37.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* ===================== the allocator laws and the call post, as this file reads them ===================== *)
(* The laws with a SlotInv.LawFields lemma (lw_blocks, lw_fs_place, lw_not_owned, lw_client_img_shadow, lw_store)
   are read through it; the others (a_laws_client's client-data conjunct, a_laws_disjoint, a_call_post_frame,
   a_call_post_model) are taken apart once here, by statement. *)

(* a_laws_blocks: a live block ends below stklo; its bytes are app memory, off the image and off the side stack. *)
Lemma f37_blocks : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_img a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin.
  pose proof (lw_blocks (APIf rc) H mem md p n HAH Hin) as HB.
  split; [exact (lwb_end _ _ _ _ _ _ HB)|]. intros a Ha.
  destruct (lwb_byte _ _ _ _ _ _ HB a Ha) as (Hap & _ & Hni & _ & Hnfs).
  split; [exact Hap|]. split; [exact Hni | exact Hnfs].
Qed.

(* a_laws_fs_place: the side stack starts at or above GT, ends below stklo and is app memory. *)
Lemma f37_fs_place : forall H mem md b,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) b -> 0 <= b < 2 ^ 64 ->
  AC.GT <= b /\ b + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, b <= a < b + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md b HAH Hw Hr.
  pose proof (lw_fs_place (APIf rc) H mem md b HAH Hw Hr) as HF.
  split; [exact (lwf_gt _ _ _ _ HF)|]. split; [exact (lwf_end _ _ _ _ HF) | exact (lwf_app _ _ _ _ HF)].
Qed.

(* a_laws_not_owned: the allocator owns no byte of a live block, its slack, the side stack or the real stack, and
   none of their shadow bytes. *)
Lemma f37_not_owned : forall H mem md a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (AC.in_blocks H a \/ AC.in_slack H a \/ AC.a_in_fs AC.ASYMS mem a \/
   AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END) ->
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a /\
  ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md (shadow_addr a).
Proof.
  intros H mem md a HAH Hc.
  pose proof (lw_not_owned (APIf rc) H mem md a HAH Hc) as HN.
  split; [exact (lwn_byte HN) | exact (lwn_shadow HN)].
Qed.

(* a_laws_client: the allocator owns no client data byte and no shadow byte of an image byte. *)
Lemma f37_client : forall H mem md a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (AC.in_blocks AC.a_client a -> ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  (AC.a_in_img a -> ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md (shadow_addr a)).
Proof.
  intros H mem md a HAH. split.
  - decompose [and] (AC.a_laws_client _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md a HAH).
    match goal with Hx : AC.in_blocks AC.a_client a -> ~ _ |- _ => exact Hx end.
  - exact (lw_client_img_shadow (APIf rc) H mem md a HAH).
Qed.

(* a_laws_store, for a store that writes only shadow bytes of the real stack (a_store_ok's fourth arm). *)
Lemma f37_store : forall H mem mem' md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (exists b, a = shadow_addr b /\ AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= b < APPMEM_END) ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH HK HW.
  assert (HK' : forall a, 0 <= a < 2 ^ 64 ->
             ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
             mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply HK; [exact Ha|]. intros (b & Eb & Hb). apply Hns.
    unfold AC.a_store_ok. right. right. right. exists b. split; [exact Eb|]. right. left. exact Hb. }
  pose proof (lw_store (APIf rc) H mem mem' md HAH HK' HW) as HS.
  split; [exact (lws_ah _ _ _ _ _ HS)|]. split; [exact (lws_own _ _ _ _ _ HS)|].
  split; [exact (lws_lo _ _ _ _ _ HS) | exact (lws_hi _ _ _ _ _ HS)].
Qed.

(* a_laws_disjoint: a block of H2 is apart from the block (p, n) in front of it. *)
Lemma f37_disjoint : forall H2 mem md p n q k a,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) ((p, n) :: H2) mem md -> In (q, k) H2 -> q <= a < q + k ->
  ~ (p <= a < p + n).
Proof.
  intros H2 mem md p n q k a HAH Hin Hq Hp.
  destruct (AC.a_laws_disjoint _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) [] H2 mem md p n q k HAH Hin)
    as [D|D]; lia.
Qed.

(* a_call_post_frame: the bytes a callee keeps, with their writability. *)
Lemma f37_cp_frame : forall K H regs mem md touched H' regs' mem' md',
  AC.a_call_post AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc)) K H regs mem md touched H' regs' mem' md' ->
  forall a, 0 <= a < 2 ^ 64 ->
    ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a ->
    ~ AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H' mem' md' a ->
    ~ AC.a_window K regs a -> ~ (AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4) ->
    a <> AC.as_oom AC.ASYMS -> ~ touched a ->
    mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a).
Proof.
  intros K H regs mem md touched H' regs' mem' md' HP.
  exact (AC.a_call_post_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP).
Qed.

(* a_call_post_model: a callee keeps the fd table. *)
Lemma f37_cp_fds : forall K H regs mem md touched H' regs' mem' md',
  AC.a_call_post AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc)) K H regs mem md touched H' regs' mem' md' ->
  m_fds md' = m_fds md.
Proof.
  intros K H regs mem md touched H' regs' mem' md' HP.
  destruct (AC.a_call_post_model _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP) as (lz & mt & vm' & ->).
  reflexivity.
Qed.

(* The free wrapper's contract at this segment's call (Contract.v afree_at, through aa_free at as_free = 0x534b4),
   applied ONCE here, so a new generation of afree_at breaks this lemma and no site. The call heap is the cut's
   block (p, n) in front of the entry heap (H1 = [], H2 = g_H g). Generation N.1's binder Bc and its two class
   premises (the call heap's per-class bytes under Bc, and the room inequality) are Seg/Tac_cls.v's sl_free_cls for
   Bc = Bc_of BE, where BE is the witness of ENT's per-class conjunct: F37 derives no class fact and seg_F37 takes
   no extra premise. *)
Lemma f37_free : forall g hb mem0 md0 regs mem md p n,
  ENT APIf g hb mem0 md0 ->
  AC.a_call_pre AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
    AC.AK_FREE ([] ++ (p, n) :: g_H g) regs mem md ->
  getr regs 10 = Z_to_bv 64 p ->
  SR rsegs (mkCfg (mkst regs (Z_to_bv 64 0x534b4) mem (seg_rom rsegs)) md)
    (fun c' => exists regs' mem' md',
       c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
       AC.a_call_post AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
         (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc))
         (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
         AC.AK_FREE ([] ++ (p, n) :: g_H g) regs mem md (fun a => p <= a < p + n) ([] ++ g_H g) regs' mem' md' /\
       AC.a_errno_kept AC.ASYMS mem mem').
Proof.
  intros g hb mem0 md0 regs mem md p n HENT Hpre Ea0.
  destruct (Tac_cls.sl_free_cls APIf g hb mem0 md0 p n HENT) as (BE & _ & _ & Hcls & Hroom).
  pose proof (@AC.aa_free AC.ASYMS AsanRTInv.RT (APIf rc) fx) as HFREE.
  unfold AC.afree_contract, AC.afree_at in HFREE.
  assert (EFREE : AC.as_free AC.ASYMS = 0x534b4) by reflexivity.
  rewrite EFREE in HFREE.
  exact (HFREE [] (g_H g) regs mem md p n (Tac_cls.Bc_of BE) Hpre Ea0 Hcls Hroom).
Qed.

(* ===================== AH across the 23 out-of-scope marks ===================== *)

(* The write set is the frame shadow bytes [S(fr) + 22, S(fr) + 67): on the real arm the frame lies in
   [stklo, APPMEM_END), so each byte is the shadow of a real-stack byte and a_store_ok (a_laws_store); on the side
   arm the frame lies in the side stack, so each byte is the shadow of a side-stack byte and the metadata is
   untouched (Tac_fs.a_fs_ok_store_AH). Both give the heap invariant, the owned set and the two stack bounds. *)
Lemma f37_ah : forall g fr hb regs mem mem' md,
  FRA B APIf ra g fr hb regs mem md ->
  munch [(Sfr fr + 22, Sfr fr + 67)] mem mem' -> wmono rsegs mem mem' ->
  (forall q, 0 <= q < 2 ^ 64 -> (exists b, mrd rsegs mem (wa q) = Some b) ->
     exists b, mrd rsegs mem' (wa q) = Some b) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  (forall q, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md q <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md q) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros g fr hb regs mem mem' md HFRA MU WM HPR.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  assert (Epre : forall q, Sfr fr + 22 <= q < Sfr fr + 67 ->
            shadow_addr (8 * (q - ASAN_K)) = q /\ fr <= 8 * (q - ASAN_K) < fr + FRAME_BYTES)
    by (intros q Hq; apply (f37_sh_pre fr q Hfrm); lia).
  assert (Hout : forall q, 0 <= q < 2 ^ 64 -> ~ (Sfr fr + 22 <= q < Sfr fr + 67) ->
            mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
  { intros q Hq Hn. apply MU. rewrite f37_ulit by exact Hq. apply out1. lia. }
  assert (Hwr : forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q)
    by (intros q _ Hw; exact (WM (Z_to_bv 64 q) Hw)).
  destruct Hloc as [[Hs50 [Hspfr Hreal]] | [Hs5fr [Hfsb [Hfs Hrec]]]].
  - apply (f37_store (hb ++ g_H g) mem mem' md HAH); [|exact Hwr].
    intros q Hq Hns. apply Hout; [exact Hq|]. intros Hin. apply Hns.
    destruct (Epre q Hin) as (Esh & Erg). exists (8 * (q - ASAN_K)).
    split; [symmetry; exact Esh | exact (Hreal _ Erg)].
  - destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FS & HFSr & HwFS & HFSlo & HFShi).
    pose proof (Hfsb FS HwFS HFSr) as HFSfr.
    destruct (f37_fs_place (hb ++ g_H g) mem md FS HAH HwFS HFSr) as (HGTFS & HFSend & HFSapp).
    assert (HFS64 : FS + AC.FS_SIZE <= 2 ^ 64).
    { pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(unfold AC.FS_SIZE; lia)) as H.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. lia. }
    apply (Tac_fs.a_fs_ok_store_AH AC.ASYMS _ _ _ _ [(Sfr fr + 22, Sfr fr + 67)] (hb ++ g_H g) mem mem' md FS
             LAWS HAH HwFS HFSr HFS64).
    + exact (proj2 (fr_munch_ul _ _ _) MU).
    + exact Hwr.
    + intros q Hq Hb. exact (HPR q Hq Hb).
    + intros q Hm. pose proof (f37_fs_meta_range FS q Hm) as Hr.
      apply (proj1 (fr_outside_lib _ _)). apply out1.
      destruct (Z_lt_le_dec q (Sfr fr + 22)) as [H1|H1]; [left; exact H1|].
      destruct (Z_lt_le_dec q (Sfr fr + 67)) as [H2|H2]; [|right; exact H2].
      exfalso. destruct (Epre q ltac:(lia)) as (Esh & Erg).
      pose proof (shadow_of_app _ (Happ _ Erg)) as Hsq. rewrite Esh in Hsq.
      exact (app_not_shadow q (HFSapp q ltac:(unfold AC.FS_SIZE in *; lia)) Hsq).
    + intros q Hq Hnok Hnfs Hnsh. apply Hout; [exact Hq|]. intros Hin. apply Hnsh.
      destruct (Epre q Hin) as (Esh & Erg). exists (8 * (q - ASAN_K)).
      split; [lia | symmetry; exact Esh].
Qed.

(* ===================== what the free keeps ===================== *)

(* AC.a_call_post_frame for the free of (phi, n): a byte is kept with its writability when it is neither the
   allocator's before nor after (a_laws_not_owned: the stack at or above stklo, the side stack, the live blocks),
   nor in the callee's window [sp - 4096, sp), nor errno, the OOM flag or the freed block. *)
Lemma f37_keep : forall g fr phi n regs mem md regs' mem' md',
  FRA B APIf ra g fr (hb1 phi n) regs mem md ->
  AC.a_call_post AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc)) AC.AK_FREE (hb1 phi n ++ g_H g) regs mem md
    (fun a => phi <= a < phi + n) ([] ++ g_H g) regs' mem' md' ->
  forall a, 0 <= a < 2 ^ 64 ->
  ((AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= a < APPMEM_END /\
      ~ (AC.aspZ regs - AC.AK_FREE <= a < AC.aspZ regs)) \/
   AC.a_in_fs AC.ASYMS mem a \/ AC.in_blocks (g_H g) a) ->
  mbyte rsegs mem' a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem' a).
Proof.
  intros g fr phi n regs mem md regs' mem' md' HFRA HP a Ha Hc.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hwlo & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & _).
  pose proof HP as HAH'; apply AC.a_call_post_ah in HAH'.
  pose proof HP as HSTK; apply AC.a_call_post_stklo in HSTK.
  pose proof (AC.a_call_post_tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP) as HTP.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hhi.
  destruct (f37_blocks _ mem md phi n HAH ltac:(apply in_or_app; left; left; reflexivity)) as (Hpend & Hpby).
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HAK : AC.AK_FREE = 4096) by reflexivity.
  assert (Herr : AC.a_errno AC.ASYMS = 0x5dc5ac) by reflexivity.
  assert (Hoom : AC.as_oom AC.ASYMS = 0x12b920) by reflexivity.
  assert (HGT : AC.GT = 0x5fe000) by reflexivity.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (Hcls : ~ AC.a_window AC.AK_FREE regs a /\ ~ (AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4) /\
                 a <> AC.as_oom AC.ASYMS /\ ~ (phi <= a < phi + n)).
  { destruct Hc as [[Hs Hnw]|[(b & Hbr & Hwb & Hab)|(q & k & Hin & Hr)]].
    - unfold AC.a_window. split; [exact Hnw|]. split; [lia|]. split; lia.
    - destruct (f37_fs_place _ mem md b HAH Hwb Hbr) as (HGTb & Hend & _).
      unfold AC.a_window. split; [lia|]. split; [lia|]. split; [lia|].
      intros Ht. destruct (Hpby a Ht) as (_ & _ & Hnfs). apply Hnfs.
      exists b. split; [exact Hbr|]. split; [exact Hwb | exact Hab].
    - destruct (f37_blocks _ mem md q k HAH ltac:(apply in_or_app; right; exact Hin)) as (Hqend & Hqby).
      destruct (Hqby a Hr) as (_ & Hnimg & _).
      unfold AC.a_window. split; [lia|]. split.
      + intros He. exact (Hnimg (errno_in_img a He)).
      + split; [intros Eo; rewrite Eo in Hnimg; exact (Hnimg oom_in_img)|].
        intros Ht. exact (f37_disjoint (g_H g) mem md phi n q k a HAH Hin Hr Ht). }
  destruct Hcls as (Hnw & Hne & Hno & Hnt).
  pose proof (f37_cp_frame _ _ _ _ _ _ _ _ _ _ HP) as KP.
  apply KP; [exact Ha | | | exact Hnw | exact Hne | exact Hno | exact Hnt].
  - intro Ho. refine (proj1 (f37_not_owned _ mem md a HAH _) Ho).
    destruct Hc as [[Hs _]|[Hf|(q & k & Hin & Hr)]];
      [right; right; right; exact Hs | right; right; left; exact Hf |].
    left. exists q, k. split; [apply in_or_app; right; exact Hin | exact Hr].
  - intro Ho. refine (proj1 (f37_not_owned _ mem' md' a HAH' _) Ho).
    destruct Hc as [[Hs _]|[(b & Hbr & Hwb & Hab)|(q & k & Hin & Hr)]].
    + right; right; right. rewrite HSTK. exact Hs.
    + right; right; left. exists b. split; [exact Hbr|]. split; [|exact Hab].
      intros k Hk. rewrite (HTP (Z.of_nat k) ltac:(lia)). exact (Hwb k Hk).
    + left. exists q, k. split; [exact Hin | exact Hr].
Qed.

(* The shadow byte of such a byte is kept too (a_laws_not_owned's second half); it is not app memory, so it is
   not in the window or the freed block, and it is above errno and the OOM flag. *)
Lemma f37_keep_sh : forall g fr phi n regs mem md regs' mem' md',
  FRA B APIf ra g fr (hb1 phi n) regs mem md ->
  AC.a_call_post AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc)) AC.AK_FREE (hb1 phi n ++ g_H g) regs mem md
    (fun a => phi <= a < phi + n) ([] ++ g_H g) regs' mem' md' ->
  forall b,
  (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md <= b < APPMEM_END \/
   AC.a_in_fs AC.ASYMS mem b \/ AC.in_blocks (g_H g) b) ->
  mbyte rsegs mem' (shadow_addr b) = mbyte rsegs mem (shadow_addr b).
Proof.
  intros g fr phi n regs mem md regs' mem' md' HFRA HP b Hc.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hwlo & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & _).
  pose proof HP as HAH'; apply AC.a_call_post_ah in HAH'.
  pose proof HP as HSTK; apply AC.a_call_post_stklo in HSTK.
  pose proof (AC.a_call_post_tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP) as HTP.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hhi.
  destruct (f37_blocks _ mem md phi n HAH ltac:(apply in_or_app; left; left; reflexivity)) as (Hpend & Hpby).
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HAK : AC.AK_FREE = 4096) by reflexivity.
  assert (Herr : AC.a_errno AC.ASYMS = 0x5dc5ac) by reflexivity.
  assert (Hoom : AC.as_oom AC.ASYMS = 0x12b920) by reflexivity.
  assert (Happ : app_mem b).
  { destruct Hc as [Hs|[(c & Hcr & Hwc & Hbc)|(q & k & Hin & Hr)]].
    - unfold app_mem. right. lia.
    - destruct (f37_fs_place _ mem md c HAH Hwc Hcr) as (_ & _ & Happc).
      apply Happc. exact Hbc.
    - destruct (f37_blocks _ mem md q k HAH ltac:(apply in_or_app; right; exact Hin)) as (_ & Hqby).
      exact (proj1 (Hqby b Hr)). }
  pose proof (shadow_of_app b Happ) as Hsh. pose proof (in_shadow_range _ Hsh) as Hshr.
  pose proof Hsh as Hsh'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh'.
  pose proof (f37_cp_frame _ _ _ _ _ _ _ _ _ _ HP) as KP.
  refine (proj1 (KP (shadow_addr b) ltac:(lia) _ _ _ _ _ _)).
  - intro Ho. refine (proj2 (f37_not_owned _ mem md b HAH _) Ho).
    destruct Hc as [Hs|[Hf|(q & k & Hin & Hr)]];
      [right; right; right; exact Hs | right; right; left; exact Hf |].
    left. exists q, k. split; [apply in_or_app; right; exact Hin | exact Hr].
  - intro Ho. refine (proj2 (f37_not_owned _ mem' md' b HAH' _) Ho).
    destruct Hc as [Hs|[(c & Hcr & Hwc & Hbc)|(q & k & Hin & Hr)]].
    + right; right; right. rewrite HSTK. exact Hs.
    + right; right; left. exists c. split; [exact Hcr|]. split; [|exact Hbc].
      intros k Hk. rewrite (HTP (Z.of_nat k) ltac:(lia)). exact (Hwc k Hk).
    + left. exists q, k. split; [exact Hin | exact Hr].
  - unfold AC.a_window. unfold HIGHMEM_BEG in Hhi. lia.
  - rewrite Herr. lia.
  - rewrite Hoom. lia.
  - intros Ht. cbn beta in Ht. destruct (Hpby _ Ht) as (Hap & _). exact (app_not_shadow _ Hap Hsh).
Qed.

(* An image byte of the client data or of the RELRO range, not errno nor the OOM flag, is kept: the allocator
   owns neither (a_laws_client, frame_facts), and it is below the window and outside every block. *)
Lemma f37_keep_img : forall g fr phi n regs mem md regs' mem' md',
  FRA B APIf ra g fr (hb1 phi n) regs mem md ->
  AC.a_call_post AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc)) AC.AK_FREE (hb1 phi n ++ g_H g) regs mem md
    (fun a => phi <= a < phi + n) ([] ++ g_H g) regs' mem' md' ->
  forall a, AC.a_in_img a -> (AC.in_blocks AC.a_client a \/ in_globals AF.frame_RELRO a) ->
  ~ (AC.a_errno AC.ASYMS <= a < AC.a_errno AC.ASYMS + 4) -> a <> AC.as_oom AC.ASYMS ->
  mbyte rsegs mem' a = mbyte rsegs mem a.
Proof.
  intros g fr phi n regs mem md regs' mem' md' HFRA HP a Himg Hcl Hne Hno.
  pose proof FF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hwlo & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & _).
  pose proof HP as HAH'; apply AC.a_call_post_ah in HAH'.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hhi.
  destruct (f37_blocks _ mem md phi n HAH ltac:(apply in_or_app; left; left; reflexivity)) as (Hpend & Hpby).
  pose proof (img_below_GT a Himg) as Hlo.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HAK : AC.AK_FREE = 4096) by reflexivity.
  assert (HGT : AC.GT = 0x5fe000) by reflexivity.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  pose proof (f37_cp_frame _ _ _ _ _ _ _ _ _ _ HP) as KP.
  refine (proj1 (KP a ltac:(lia) _ _ _ Hne Hno _)).
  - intro Ho. destruct Hcl as [Hc|Hr].
    + exact (proj1 (f37_client _ mem md a HAH) Hc Ho).
    + exact (proj2 (Hown rc _ mem md a Ho) Hr).
  - intro Ho. destruct Hcl as [Hc|Hr].
    + exact (proj1 (f37_client _ mem' md' a HAH') Hc Ho).
    + exact (proj2 (Hown rc _ mem' md' a Ho) Hr).
  - unfold AC.a_window. lia.
  - intros Ht. cbn beta in Ht. destruct (Hpby a Ht) as (_ & Hni & _). exact (Hni Himg).
Qed.

(* The shadow byte of an image byte is kept: the allocator does not own it (a_laws_client). *)
Lemma f37_keep_shimg : forall g fr phi n regs mem md regs' mem' md',
  FRA B APIf ra g fr (hb1 phi n) regs mem md ->
  AC.a_call_post AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc)) AC.AK_FREE (hb1 phi n ++ g_H g) regs mem md
    (fun a => phi <= a < phi + n) ([] ++ g_H g) regs' mem' md' ->
  forall a, AC.a_in_img a -> mbyte rsegs mem' (shadow_addr a) = mbyte rsegs mem (shadow_addr a).
Proof.
  intros g fr phi n regs mem md regs' mem' md' HFRA HP a Himg.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hwlo & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & _).
  pose proof HP as HAH'; apply AC.a_call_post_ah in HAH'.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hhi.
  destruct (f37_blocks _ mem md phi n HAH ltac:(apply in_or_app; left; left; reflexivity)) as (Hpend & Hpby).
  pose proof (img_below_GT a Himg) as Hlo.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HAK : AC.AK_FREE = 4096) by reflexivity.
  assert (Herr : AC.a_errno AC.ASYMS = 0x5dc5ac) by reflexivity.
  assert (Hoom : AC.as_oom AC.ASYMS = 0x12b920) by reflexivity.
  assert (Happ : app_mem a) by (unfold app_mem, LOWMEM_END; unfold AC.GT in Hlo; left; lia).
  pose proof (shadow_of_app a Happ) as Hsh. pose proof (in_shadow_range _ Hsh) as Hshr.
  pose proof Hsh as Hsh'. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh'.
  pose proof (f37_cp_frame _ _ _ _ _ _ _ _ _ _ HP) as KP.
  refine (proj1 (KP (shadow_addr a) ltac:(lia) _ _ _ _ _ _)).
  - exact (proj2 (f37_client _ mem md a HAH) Himg).
  - exact (proj2 (f37_client _ mem' md' a HAH') Himg).
  - unfold AC.a_window. unfold HIGHMEM_BEG in Hhi. lia.
  - rewrite Herr. lia.
  - rewrite Hoom. lia.
  - intros Ht. cbn beta in Ht. destruct (Hpby _ Ht) as (Hap & _). exact (app_not_shadow _ Hap Hsh).
Qed.

(* ===================== the segment lemma ===================== *)

(* S_F37 of forms-asan-ubsan-v190.md, over the official cuts. *)
Lemma seg_F37 : forall j : nat,
  Hat B APIf ra (Inv_B82d1c_at B APIf ra) j ->
  Hat B APIf ra (Inv_B82ca0_at B APIf ra) j.
Proof.
  intros j Hcb8 g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _ & _ & _ & HRimg & _ & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj255 & HHB & _ & _ &
    (H224 & H232 & _ & _) &
    HLK & H272 & _ & H10 & H23 & H18 & H20 & Hs152 & Hs160 & Hphi & Hplen & Hfstk & Hweq & HIFS & H22).
  subst c. rewrite SEGS.
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  pose proof HLK as (_ & H240 & HOUR & HFLI).
  pose proof HFLI as (H27 & _).
  pose proof (Tac_ro.fli_mem _ _ _ _ HFLI) as (Had0 & Hstk0 & HadR0 & HadF0 & HKNT0 & HadS0).
  pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGTfr & Happfr).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hhigh.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HGT : AC.GT = 0x5fe000) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HAK : AC.AK_FREE = 4096) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HwinB : 0 <= g_S g - AF.SLOT_STACK /\ g_S g <= 2 ^ 64)
    by (destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  assert (HAhi : HIGHMEM_BEG + 1048576 - 4096 < A) by lia.
  pose proof (f37_m8 fr Hfrm) as Hfr8.
  assert (Hfrhi : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happfr (fr + FRAME_BYTES - 1) ltac:(lia)) as Ha.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Ha. lia. }
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx. destruct (f37_sh_pre fr x Hfrm Hx) as (Esh & Erg). rewrite <- Esh.
    exact (shadow_of_app _ (Happfr _ Erg)). }
  pose proof (f37_Sfr_GT fr HGTfr) as HSfGT.
  assert (HSfhi : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { pose proof (HshIS (Sfr fr + FRAME_SHADOW - 1) ltac:(lia)) as Hin.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin. lia. }
  (* ---- the spills this range reads, and their 8-byte reads ---- *)
  assert (Q240 : q64 mem (A + 240) (Z.of_nat j)) by (apply (f37_spill regs mem 240 _ A H240 Hr9); lia).
  assert (Q224 : q64 mem (A + 224) (g_p g + t_body (g_in g) j))
    by (apply (f37_spill regs mem 224 _ A H224 Hr9); lia).
  assert (Q232 : q64 mem (A + 232) (t_left (g_in g) j - t_h (g_in g) j))
    by (apply (f37_spill regs mem 232 _ A H232 Hr9); lia).
  assert (RD : forall off v, q64 mem (A + off) v ->
             ov_read_bytes rsegs mem (wa (A + off)) 8 = Some (ULMem.le8 (Z_to_bv 64 v))).
  { intros off v Q.
    pose proof (ULMem.bytes_at_ov_read rsegs mem (A + off) (ULMem.le8 (Z_to_bv 64 v)) 0 8 Q
      ltac:(rewrite ULMem.length_le8; lia)) as HH.
    change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite ULMem.length_le8; lia). exact HH. }
  (* ---- the 45 frame-shadow bytes the marks write are writable ---- *)
  assert (HWR : wr_at rsegs mem (Sfr fr + 22) 45).
  { split; [lia|]. split; [lia|]. intros i Hi.
    exact (proj1 (HSW (Sfr fr + 22 + i) (HshIS (Sfr fr + 22 + i) ltac:(lia)))). }
  assert (H23' : getr regs 23 = Z_to_bv 64 (t_want (g_in g) j)) by (rewrite Hweq; exact H23).
  (* ---- the run 0x82ca0 -> 0x534b4 (sl_run, the lazy bridge of Tac_slot). It reads [A + 224, A + 248) and
     writes the shadow bytes [S(fr) + 22, S(fr) + 67). ---- *)
  apply (sl_run regs (Z_to_bv 64 0x82ca0) mem md
    (fun R0 pc' mem' => pc' = Z_to_bv 64 0x534b4 /\
       getr R0 1 = Z_to_bv 64 0x82d1c /\ getr R0 10 = Z_to_bv 64 phi /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 26 = getr regs 26 /\
       getr R0 27 = getr regs 27 /\ getr R0 22 = getr regs 22 /\
       getr R0 23 = Z_to_bv 64 (g_p g + t_body (g_in g) j + t_len (g_in g) j) /\
       getr R0 25 = Z_to_bv 64 (t_left (g_in g) j - t_h (g_in g) j - t_len (g_in g) j) /\
       getr R0 21 = Z_to_bv 64 (Z.of_nat j) /\
       munch [(Sfr fr + 22, Sfr fr + 67)] mem mem' /\ wmono rsegs mem mem' /\
       (forall q, 0 <= q < 2 ^ 64 -> (exists b, mrd rsegs mem (wa q) = Some b) ->
          exists b, mrd rsegs mem' (wa q) = Some b))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply evt_mono.
    { exact (f37_evt regs fp_regs fp_csr mem A (Sfr fr) (t_want (g_in g) j) (Z.of_nat j)
               (g_p g + t_body (g_in g) j) (t_left (g_in g) j - t_h (g_in g) j) (t_len (g_in g) j) phi
               Hr9 H10 H23' H18 Hr19 H20 H27 ltac:(lia) ltac:(lia)
               (RD 240 _ Q240) (RD 224 _ Q224) (RD 232 _ Q232) HWR). }
    intros ms' (R0 & m' & -> & E1 & E10 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E26 & E27 & E22 & E23 &
                E25 & E21 & MU & WM & HPR).
    exists R0, (Z_to_bv 64 0x534b4), m'.
    split; [reflexivity|]. split; [reflexivity|].
    repeat (split; [assumption|]); assumption.
  - intros R0 pc' mem1 regs1 md1
      (Hpc & E1 & E10 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E26 & E27 & E22 & E23 & E25 & E21 & MU & WM &
       HPR)
      Hreg Hmat.
    subst pc'.
    assert (F1 : getr regs1 1 = Z_to_bv 64 0x82d1c) by (rewrite Hreg; exact E1).
    assert (F10 : getr regs1 10 = Z_to_bv 64 phi) by (rewrite Hreg; exact E10).
    assert (F2 : getr regs1 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (F3 : getr regs1 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (F4 : getr regs1 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (F8 : getr regs1 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (F9 : getr regs1 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (F18 : getr regs1 18 = getr regs 18) by (rewrite Hreg; exact E18).
    assert (F19 : getr regs1 19 = getr regs 19) by (rewrite Hreg; exact E19).
    assert (F20 : getr regs1 20 = getr regs 20) by (rewrite Hreg; exact E20).
    assert (F26 : getr regs1 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (F27 : getr regs1 27 = getr regs 27) by (rewrite Hreg; exact E27).
    assert (F22 : getr regs1 22 = getr regs 22) by (rewrite Hreg; exact E22).
    assert (F23 : getr regs1 23 = Z_to_bv 64 (g_p g + t_body (g_in g) j + t_len (g_in g) j))
      by (rewrite Hreg; exact E23).
    assert (F25 : getr regs1 25 = Z_to_bv 64 (t_left (g_in g) j - t_h (g_in g) j - t_len (g_in g) j))
      by (rewrite Hreg; exact E25).
    assert (F21 : getr regs1 21 = Z_to_bv 64 (Z.of_nat j)) by (rewrite Hreg; exact E21).
    (* ---- what the 23 marks keep: every byte outside [S(fr) + 22, S(fr) + 67) ---- *)
    assert (KW : forall x, 0 <= x < 2 ^ 64 -> ~ (Sfr fr + 22 <= x < Sfr fr + 67) ->
               mbyte rsegs mem1 x = mbyte rsegs mem x).
    { intros x Hx Hn. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
      rewrite f37_ulit by exact Hx. apply out1. lia. }
    assert (KWapp : forall x, app_mem x -> mbyte rsegs mem1 x = mbyte rsegs mem x).
    { intros x Hx. apply KW; [unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hx; lia|].
      intros Hin. exact (app_not_shadow x Hx (HshIS x ltac:(lia))). }
    assert (KWsh : forall x, 0 <= x < 2 ^ 64 -> ~ (fr <= x < fr + FRAME_BYTES) ->
               mbyte rsegs mem1 (shadow_addr x) = mbyte rsegs mem (shadow_addr x)).
    { intros x Hx Hn. apply KW.
      - exact (f37_sh_rng x Hx).
      - intros Hin. apply Hn. exact (f37_sh_in_fr fr x Hfrm Hin). }
    assert (KWwr : forall x, writable_at rsegs mem x -> writable_at rsegs mem1 x)
      by (intros x Hw; exact (WM (Z_to_bv 64 x) Hw)).
    (* ---- FRA and ENT across the marks, then at the materialized model ---- *)
    destruct (f37_ah g fr _ regs mem mem1 md HFRA MU WM HPR) as (HAH1 & Hown1 & HSTK1 & HSTKHI1).
    assert (HRO1 : ro_agree rsegs mem1).
    { apply (sl_ro_keep _ mem mem1 Hro MU). intros x Hx. apply out1. lia. }
    assert (HSH1 : exists sh, bytes_at rsegs mem1 (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
    { assert (ST : stk rsegs mem1 (Sfr fr) (Sfr fr + FRAME_SHADOW)).
      { split; [lia|]. split; [lia|]. intros a Ha.
        destruct (HSW a (HshIS a Ha)) as (Hw & b & Hb).
        split; [exact (WM (wa a) Hw)|].
        exact (HPR a ltac:(lia) (ex_intro _ b Hb)). }
      destruct (stk_bytes rsegs mem1 (Sfr fr) (Sfr fr + FRAME_SHADOW) ST ltac:(lia)) as (sh & Hl & Hb).
      exists sh. split; [exact Hb|]. rewrite Hl.
      replace (Sfr fr + FRAME_SHADOW - Sfr fr) with FRAME_SHADOW by lia. reflexivity. }
    assert (HFRA1a : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs1 mem1 md).
    { apply (sl_fr_meta B APIf ra empty FF g fr _ regs regs1 mem mem1 md [(Sfr fr + 22, Sfr fr + 67)]
               HFRA MU WM HRO1).
      - apply f37_rtdj_GT. intros lo hi Hin. cbn in Hin. destruct Hin as [E|[]]. injection E as <- <-. lia.
      - exact HAH1.
      - exact HSTK1.
      - exact Happfr.
      - exact HGTfr.
      - exact HSH1.
      - intros x Hx H1 H2. apply out1. lia.
      - intros A' HA' HA'r x Hx. assert (EA : A' = A) by (apply (f37_bv_inj A' A); [rewrite <- HA'; exact Hr9 | lia | lia]).
        subst A'. apply out1. lia.
      - intros x Hx. apply out1. lia.
      - intros A' HA' HA'r x Hx. assert (EA : A' = A) by (apply (f37_bv_inj A' A); [rewrite <- HA'; exact Hr9 | lia | lia]).
        subst A'. apply out1. lia.
      - intros x Hx. left. apply out1. lia.
      - intros a Ha. apply (addr1_munch _ mem mem1 a MU); [|exact (HAG a Ha)].
        apply out1. left. exact (f37_sh_lt a fr (img_below_GT a (f37_ag_img a Ha)) HGTfr).
      - exact F2.
      - exact F3.
      - exact F4.
      - exact F8.
      - exact F9.
      - exact F19.
      - exact F26. }
    assert (HFRA1 : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs1 mem1 md1)
      by exact (sl_fra_move B APIf ra g fr _ regs1 regs1 mem1 md md1 HFRA1a
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hmat).
    assert (HENT1a : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem1 md).
    { apply (ent_store B APIf ra g fr _ regs mem mem1 md [(Sfr fr + 22, Sfr fr + 67)] HENT HFRA MU).
      - intros x Hx. destruct (Z_lt_le_dec x (Sfr fr + 22)) as [Hl|Hl]; [left; apply out1; lia|].
        destruct (Z_lt_le_dec x (Sfr fr + 67)) as [Hh|Hh]; [right; right; right; lia | left; apply out1; lia].
      - exact HSTK1.
      - exact HSTKHI1.
      - intros a _ Ho. apply Hown1. exact Ho. }
    pose proof (ent_mat APIf g _ mem1 md md1 HENT1a Hmat) as HENT1.
    (* ---- the free (AC.aa_free at as_free = 0x534b4), from SlotInv.fra_call_pre; its per-class premises from
       ENT's per-class conjunct at the call, through f37_free ---- *)
    assert (Hret : BYK0s.ret_ok (getr regs1 1)) by (rewrite F1; apply BYK0s.ret_ok_even; vm_compute; reflexivity).
    pose proof (fra_call_pre B APIf ra g fr _ regs1 mem1 md1 AC.AK_FREE HFRA1 HENT1 Hret ltac:(lia)) as PRE.
    eapply SR_bind;
      [exact (f37_free g _ mem1 md1 regs1 mem1 md1 phi (AC.a_size (flen g j)) HENT1 PRE F10)|].
    intros c2 (regs2 & mem2 & md2 & Ec2 & HPOST & HERR).
    subst c2. rewrite F1.
    pose proof HPOST as HAH2; apply AC.a_call_post_ah in HAH2.
    pose proof (AC.a_call_post_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPOST) as HREGS.
    pose proof HPOST as HSTK2; apply AC.a_call_post_stklo in HSTK2.
    pose proof (AC.a_call_post_win_writable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPOST) as HWW.
    pose proof (AC.a_call_post_win_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPOST) as HWP.
    pose proof (AC.a_call_post_tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPOST) as HTP2.
    assert (G2 : getr regs2 2 = getr regs1 2) by exact (HREGS 2 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G3 : getr regs2 3 = getr regs1 3) by exact (HREGS 3 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G4 : getr regs2 4 = getr regs1 4) by exact (HREGS 4 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G8 : getr regs2 8 = getr regs1 8) by exact (HREGS 8 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G9 : getr regs2 9 = getr regs1 9) by exact (HREGS 9 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G19 : getr regs2 19 = getr regs1 19) by exact (HREGS 19 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G23 : getr regs2 23 = getr regs1 23) by exact (HREGS 23 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G25 : getr regs2 25 = getr regs1 25) by exact (HREGS 25 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G21 : getr regs2 21 = getr regs1 21) by exact (HREGS 21 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G26 : getr regs2 26 = getr regs1 26) by exact (HREGS 26 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G27 : getr regs2 27 = getr regs1 27) by exact (HREGS 27 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G22 : getr regs2 22 = getr regs1 22) by exact (HREGS 22 ltac:(unfold AC.a_callee_saved; lia)).
    pose proof HFRA1 as (A1 & sp1 & s51 & HRT1 & HAH1' & Hro1 & Hsn1 & Hhalt1 & Hgimg1 & Hr2' & Hspm1 &
      Haspz1 & Hstklo1 & Hr4' & Hr8' & Hr9' & Hr3' & Hr19' & Hr26' & Hfrm1 & Hs51 & HAm1 & HAS1 & Hspa1 & Hfa1 &
      HA4481 & HS41 & HAPP1 & Hspill1 & Hsel1 & Hfr561 & Hloc1 & Hhdr11 & Hhdr21 & Hsh1 & Hwin1 & Hsaved1 &
      Herrno1 & HAG1 & HWA1 & HSHI11 & HSHI21 & HSHI31 & Hhb1 & Hlive1).
    assert (EA1 : A1 = A).
    { apply (f37_bv_inj A1 A); [unfold rg in Hr9', Hr9; rewrite <- Hr9', <- Hr9; exact F9 | |lia].
      destruct Hwin1 as (Hw0 & Hw1 & _). lia. }
    subst A1.
    assert (Esp1 : AC.aspZ regs1 = sp) by (unfold AC.aspZ in *; rewrite F2; exact Haspz).
    pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem1 md1 HAH1') as Hhigh1.
    pose proof (sl_frame_apart_win B APIf ra g fr _ regs1 mem1 md1 HFRA1) as Hfrwin.
    pose proof (f37_keep g fr phi (AC.a_size (flen g j)) regs1 mem1 md1 regs2 mem2 md2 HFRA1 HPOST) as KK.
    pose proof (f37_keep_sh g fr phi (AC.a_size (flen g j)) regs1 mem1 md1 regs2 mem2 md2 HFRA1 HPOST) as KKsh.
    pose proof (f37_keep_img g fr phi (AC.a_size (flen g j)) regs1 mem1 md1 regs2 mem2 md2 HFRA1 HPOST) as KKimg.
    pose proof (f37_keep_shimg g fr phi (AC.a_size (flen g j)) regs1 mem1 md1 regs2 mem2 md2 HFRA1 HPOST)
      as KKshimg.
    (* the stack at and above sp, below sp's window, the frame and the frame's shadow are kept *)
    assert (KEEPhi : forall x, sp <= x < g_S g ->
              mbyte rsegs mem2 x = mbyte rsegs mem1 x /\ (writable_at rsegs mem1 x <-> writable_at rsegs mem2 x)).
    { intros x Hx. apply KK; [lia|]. left. split; [lia|]. rewrite Esp1. lia. }
    assert (KEEPstk : forall x, g_S g - AF.SLOT_STACK <= x < sp - 4096 ->
              mbyte rsegs mem2 x = mbyte rsegs mem1 x /\ (writable_at rsegs mem1 x <-> writable_at rsegs mem2 x)).
    { intros x Hx. apply KK; [lia|]. left. split; [lia|]. rewrite Esp1. lia. }
    assert (KEEPfr : forall x, fr <= x < fr + FRAME_BYTES ->
              mbyte rsegs mem2 x = mbyte rsegs mem1 x /\ (writable_at rsegs mem1 x <-> writable_at rsegs mem2 x)).
    { intros x Hx. apply KK; [lia|].
      destruct Hloc1 as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
      - left. split; [exact (Hreal x Hx)|]. exact (Hfrwin x Hx).
      - right; left. exact (Hfs x Hx). }
    assert (KEEPsh : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> mbyte rsegs mem2 x = mbyte rsegs mem1 x).
    { intros x Hx. destruct (f37_sh_pre fr x Hfrm Hx) as (Esh & Erg).
      rewrite <- Esh. apply KKsh.
      destruct Hloc1 as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
      - left. exact (Hreal _ Erg).
      - right; left. exact (Hfs _ Erg). }
    (* the live blocks of the entry heap are apart from the frame, app memory, and kept *)
    assert (Hbfr : forall x, AC.in_blocks (g_H g) x ->
              ~ (fr <= x < fr + FRAME_BYTES) /\ app_mem x /\ 0 <= x < 2 ^ 64).
    { intros x (q & k & Hin & Hr).
      destruct (f37_blocks _ mem md q k HAH ltac:(apply in_or_app; right; exact Hin)) as (Hqend & Hqby).
      destruct (Hqby x Hr) as (Hap & _ & Hnfs).
      split; [|split; [exact Hap | unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap; lia]].
      intros Hx. destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
      - pose proof (Hreal x Hx). lia.
      - exact (Hnfs (Hfs x Hx)). }
    (* the spill area, across both steps *)
    assert (SPT : forall off v, 0 <= off <= 336 -> spill regs mem off v -> spill regs2 mem2 off v).
    { intros off v Hoff Hsp. exists A. split; [unfold rg in *; rewrite G9, F9; exact Hr9|].
      pose proof (f37_spill regs mem off v A Hsp Hr9 ltac:(lia) ltac:(lia) ltac:(lia)) as Q.
      unfold q64 in *. apply (f37_ba_eq _ _ _ _ Q). rewrite LMem.length_le8. intros x Hx.
      rewrite (proj1 (KEEPhi x ltac:(lia))). apply KWapp. unfold app_mem. right. lia. }
    assert (K2fr : forall x, fr <= x < fr + FRAME_BYTES -> mbyte rsegs mem2 x = mbyte rsegs mem x).
    { intros x Hx. rewrite (proj1 (KEEPfr x Hx)). apply KWapp. apply Happfr. exact Hx. }
    (* the local `first` [fr + 2880, fr + 2920) stays addressable: its shadow bytes are frame shadow bytes
       outside the 23 marks *)
    assert (HadS2 : addressable mem2 (fr + 2880) 40).
    { apply (f37_addr_keep mem mem2 (fr + 2880) 40 HadS0). intros i Hi.
      pose proof (f37_sh_first fr i Hfrm Hi) as Hr.
      rewrite (KEEPsh (shadow_addr (fr + 2880 + i)) ltac:(lia)). apply KW; lia. }
    (* ---- FRA at the return point (Tac_slot.sl_mid) ---- *)
    assert (HFRA2 : FRA B APIf ra g fr [] regs2 mem2 md2).
    { apply (sl_mid B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) [] regs1 mem1 md1 regs2 mem2 md2
               (fun a => phi <= a < phi + AC.a_size (flen g j)) AC.AK_FREE HFRA1 HPOST).
      - cbn [length]. lia.
      - (* sink_none: the sink words are client data *)
        destruct Hsn1 as (Hcse & Hohd & Hfd). destruct Hcse as (Hthrm & Hlockm).
        assert (Hkcl : forall x, 0x5fc8e0 <= x < 0x5fc8f0 \/ 0x5fcd40 <= x < 0x5fcd50 ->
                  mbyte (ms_segs B) mem2 x = mbyte (ms_segs B) mem1 x).
        { intros x Hx. rewrite SEGS. apply KKimg.
          - destruct Hx as [Hx|Hx].
            + apply (f37_img_rng 0x5fc8e0 0x5fc8f0); [vm_compute; reflexivity | exact Hx].
            + apply (f37_img_rng 0x5fcd40 0x5fcd50); [vm_compute; reflexivity | exact Hx].
          - left. unfold AC.in_blocks, AC.a_client. destruct Hx as [Hx|Hx].
            + exists 0x5dc680, 131728. split; [cbn; tauto | lia].
            + exists 0x5fc918, 4320. split; [cbn; tauto | lia].
          - unfold AC.a_errno, AC.as_tp, AC.ASYMS. cbn. lia.
          - unfold AC.as_oom, AC.ASYMS. cbn. lia. }
        split; [|split].
        + split.
          * eapply BYI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply Hkcl. rewrite Hthr in Hx.
            cbn in Hx. left; lia.
          * eapply BYI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply Hkcl. rewrite Hlock in Hx.
            cbn in Hx. right; lia.
        + intros k Hk. rewrite Hkcl; [exact (Hohd k Hk)|]. rewrite Hhead. right; lia.
        + rewrite (f37_cp_fds _ _ _ _ _ _ _ _ _ _ HPOST). exact Hfd.
      - (* G_img_c: the RELRO bytes are not the allocator's *)
        intros a Hin. rewrite <- (Hgimg1 a Hin). rewrite SEGS.
        apply KKimg; [exact (HRimg a Hin) | right; exact Hin | |];
          destruct Hin as (lo & len & Hil & Hr); unfold AF.frame_RELRO in Hil; cbn in Hil;
          destruct Hil as [E|[]]; injection E as <- <-;
          unfold AC.a_errno, AC.as_tp, AC.as_oom, AC.ASYMS; cbn; lia.
      - unfold q64 in *. apply (f37_ba_eq _ _ _ _ Hhdr11). rewrite LMem.length_le8. intros x Hx.
        exact (proj1 (KEEPfr x ltac:(lia))).
      - unfold q64 in *. apply (f37_ba_eq _ _ _ _ Hhdr21). rewrite LMem.length_le8. intros x Hx.
        exact (proj1 (KEEPfr x ltac:(lia))).
      - intros A' HA' HA'r.
        assert (EA : A' = A) by (apply (f37_bv_inj A' A); [rewrite <- HA'; rewrite F9; exact Hr9 | lia | lia]).
        subst A'. unfold q64 in *. apply (f37_ba_eq _ _ _ _ Hspill1). rewrite LMem.length_le8. intros x Hx.
        exact (proj1 (KEEPhi x ltac:(lia))).
      - intros A' HA' HA'r v Hv.
        assert (EA : A' = A) by (apply (f37_bv_inj A' A); [rewrite <- HA'; rewrite F9; exact Hr9 | lia | lia]).
        subst A'. unfold q64 in *. apply (f37_ba_eq _ _ _ _ Hv). rewrite LMem.length_le8. intros x Hx.
        exact (proj1 (KEEPhi x ltac:(lia))).
      - intros A' HA' HA'r.
        assert (EA : A' = A) by (apply (f37_bv_inj A' A); [rewrite <- HA'; rewrite F9; exact Hr9 | lia | lia]).
        subst A'. unfold q64 in *. apply (f37_ba_eq _ _ _ _ Hfr561). rewrite LMem.length_le8. intros x Hx.
        exact (proj1 (KEEPhi x ltac:(lia))).
      - destruct Hsh1 as (sh & Hb & Hl). exists sh. split; [|exact Hl].
        refine (f37_ba_eq _ _ _ _ Hb _). rewrite Hl. change (Z.of_nat (Z.to_nat FRAME_SHADOW)) with FRAME_SHADOW.
        intros x Hx. apply KEEPsh. lia.
      - refine (f37_ba_eq _ _ _ _ Hsaved1 _). intros x Hx.
        unfold saved_bytes in Hx. rewrite !length_app, !LMem.length_le8 in Hx. cbn [length] in Hx.
        exact (proj1 (KEEPhi x ltac:(lia))).
      - split; [lia|]. split; [lia|]. intros a Ha.
        destruct Hwin1 as (_ & _ & Hw).
        destruct (Z_lt_le_dec a (sp - 4096)) as [Hlo'|Hlo'].
        + destruct (Hw a Ha) as (Hw1 & b & Hb). destruct (KEEPstk a ltac:(lia)) as (Hm & Hwr).
          split; [exact (proj1 Hwr Hw1)|]. exists b.
          assert (E : LMem.mrd rsegs mem2 (LMem.wa a) = LMem.mrd rsegs mem1 (LMem.wa a)) by exact Hm.
          exact (eq_trans E Hb).
        + destruct (Z_lt_le_dec a sp) as [Hhi'|Hhi'].
          * split; [exact (HWW a ltac:(unfold AC.a_window; rewrite Esp1; lia))|].
            destruct (HWP a ltac:(unfold AC.a_window; rewrite Esp1; lia)) as (b & Hb). exists b. exact Hb.
          * destruct (Hw a Ha) as (Hw1 & b & Hb). destruct (KEEPhi a ltac:(lia)) as (Hm & Hwr).
            split; [exact (proj1 Hwr Hw1)|]. exists b.
            assert (E : LMem.mrd rsegs mem2 (LMem.wa a) = LMem.mrd rsegs mem1 (LMem.wa a)) by exact Hm.
            exact (eq_trans E Hb).
      - intros a Ha. apply (f37_addr_keep mem1 mem2 a 1 (HAG1 a Ha)). intros i Hi.
        assert (Ei : i = 0) by lia. subst i. rewrite Z.add_0_r. apply KKshimg. exact (f37_ag_img a Ha).
      - intros a H1 H2. apply (f37_addr_keep mem1 mem2 a 1 (HWA1 a H1 H2)). intros i Hi.
        assert (Ei : i = 0) by lia. subst i. rewrite Z.add_0_r. apply KKsh. left. lia.
      - intros (FS & jj & Htp & HFSr & Hj & Hfr & Hflag & Htail).
        destruct (f37_fs_place _ mem1 md1 FS HAH1' Htp HFSr) as (HGTb & Hend & Happ).
        assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
        assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
        assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
        assert (Hfl : SMC.fs_flag FS 6 jj = FS + 36352 + jj) by (unfold SMC.fs_flag; cbn; lia).
        assert (Hfrv : fr = FS + 6328320 + jj * 4096) by (rewrite Hfr; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
        rewrite HM6 in Hj.
        assert (Hin : forall x, FS <= x < FS + AC.FS_SIZE -> AC.a_in_fs AC.ASYMS mem1 x).
        { intros x Hx. exists FS. split; [exact HFSr|]. split; [exact Htp | exact Hx]. }
        assert (Hx64 : forall x, FS <= x < FS + AC.FS_SIZE -> 0 <= x < 2 ^ 64).
        { intros x Hx. pose proof (Happ x Hx) as Hap.
          unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap. lia. }
        exists FS, jj. split.
        { intros k Hk. rewrite (HTP2 (Z.of_nat k) ltac:(lia)). exact (Htp k Hk). }
        split; [exact HFSr|]. split; [rewrite HM6; exact Hj|]. split; [exact Hfr|]. split.
        + apply (f37_ba_eq _ _ _ _ Hflag). cbn [length]. intros x Hx.
          assert (Hxr : FS <= x < FS + AC.FS_SIZE) by lia.
          exact (proj1 (KK x (Hx64 x Hxr) (or_intror (or_introl (Hin x Hxr))))).
        + apply (f37_ba_eq _ _ _ _ Htail). rewrite LMem.length_le8. intros x Hx. rewrite HB6 in Hx.
          assert (Hxr : FS <= x < FS + AC.FS_SIZE) by lia.
          exact (proj1 (KK x (Hx64 x Hxr) (or_intror (or_introl (Hin x Hxr))))).
      - (* FRA's input facts after the free: the input block is a live block of the entry heap, app memory apart
           from the frame (Hbfr); neither the 23 marks nor the free change its bytes or its shadow bytes *)
        apply (f37_ba_eq _ _ _ _ Hinb). intros x Hx.
        assert (Hn : g_n g = Z.of_nat (length (g_in g))) by reflexivity.
        destruct (Hinblk ltac:(lia)) as (HinH & _).
        assert (Hblk : AC.in_blocks (g_H g) x) by (exists (g_p g), (g_n g); split; [exact HinH | lia]).
        destruct (Hbfr _ Hblk) as (_ & Hap & Hr64).
        rewrite (proj1 (KK x Hr64 (or_intror (or_intror Hblk)))). exact (KWapp x Hap).
      - intros Hn. destruct (Hinblk Hn) as (HinH & Hadd).
        apply (f37_addr_keep mem mem2 (g_p g) (g_n g) Hadd). intros i Hi.
        assert (Hblk : AC.in_blocks (g_H g) (g_p g + i)) by (exists (g_p g), (g_n g); split; [exact HinH | lia]).
        destruct (Hbfr _ Hblk) as (Hnf & _ & Hr64).
        rewrite (KKsh _ (or_intror (or_intror Hblk))). exact (KWsh _ Hr64 Hnf).
      - exact G2.
      - exact G3.
      - exact G4.
      - exact G8.
      - exact G9.
      - exact G19.
      - exact G26. }
    (* ---- ENT at the return point (Tac_slot.ent_call) ---- *)
    assert (Hto : forall a, phi <= a < phi + AC.a_size (flen g j) ->
              app_mem a /\ a < g_S g /\ ~ AC.a_in_img a /\ ~ AC.in_blocks (g_H g) a).
    { destruct (f37_blocks _ mem1 md1 phi (AC.a_size (flen g j)) HAH1'
                  ltac:(apply in_or_app; left; left; reflexivity)) as (Hpend & Hpby).
      intros a Ha. destruct (Hpby a Ha) as (Hap & Hni & _).
      split; [exact Hap|]. split; [lia|]. split; [exact Hni|].
      intros (q & k & Hin & Hr).
      exact (f37_disjoint (g_H g) mem1 md1 phi (AC.a_size (flen g j)) q k a HAH1' Hin Hr Ha). }
    pose proof (ent_call B APIf ra g fr _ [] regs1 mem1 md1 regs2 mem2 md2
                  (fun a => phi <= a < phi + AC.a_size (flen g j))
                  AC.AK_FREE HENT1 HFRA1 HPOST ltac:(lia) Hto HERR) as HENT2.
    (* ---- the exit cut, F38's entry ---- *)
    assert (HIexit : Inv_B82d1c_at B APIf ra g j
                       (mkCfg (mkst regs2 (Z_to_bv 64 0x82d1c) mem2 (seg_rom rsegs)) md2)).
    { exists regs2, mem2, md2, fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA2|].
      split; [exact HENT2|].
      split; [exact Hgn|].
      split.
      { apply (Tac_ro.lk_keep g fr j regs regs2 mem mem2 HLK).
        - unfold rg in *. rewrite G27, F27. exact H27.
        - apply (f37_addr_keep mem mem2 (fr + 2624) 6 Had0). intros i Hi.
          rewrite (f37_sh_our fr i Hfrm Hi). rewrite (KEEPsh (Sfr fr + 328) ltac:(lia)). apply KW; [lia | lia].
        - apply (f37_stk_keep mem mem2 fr (fr + FRAME_BYTES) Hstk0). intros x Hx. split.
          + exact (K2fr x Hx).
          + intros Hw. exact (proj1 (proj2 (KEEPfr x Hx)) (KWwr x Hw)).
        - apply (f37_addr_keep mem mem2 (fr + 2688) 38 HadR0). intros i Hi.
          pose proof (f37_sh_rad fr i Hfrm ltac:(lia)) as Hr.
          rewrite (KEEPsh (shadow_addr (fr + 2688 + i)) ltac:(lia)). apply KW; lia.
        - apply (f37_addr_keep mem mem2 (fragb fr) 72 HadF0). intros i Hi.
          pose proof (f37_sh_rad fr (80 + i) Hfrm ltac:(lia)) as Hr.
          replace (fr + 2688 + (80 + i)) with (fragb fr + i) in Hr by (unfold fragb; lia).
          rewrite (KEEPsh (shadow_addr (fragb fr + i)) ltac:(lia)). apply KW; lia.
        - (* the kind-name table (image data in frame_RELRO, below GT): the 23 marks write only the frame's
             shadow; the free keeps the image bytes it does not own and every image byte's shadow byte
             (f37_keep_img, f37_keep_shimg) *)
          assert (HL : length KNC.kind_name_bytes = 112%nat) by reflexivity.
          assert (Kimg : forall x, KNC.KIND_NAME <= x < KNC.KIND_NAME + 112 -> AC.a_in_img x).
          { intros x Hx. unfold KNC.KIND_NAME in Hx.
            apply (f37_img_rng 0x9f580 0x9f5f0); [vm_compute; reflexivity | lia]. }
          destruct HKNT0 as (Hkb & Hka). split.
          + apply (f37_ba_eq _ _ _ _ Hkb). rewrite HL. intros x Hx.
            rewrite (KKimg x (Kimg x ltac:(lia))).
            * apply KWapp. unfold KNC.KIND_NAME in Hx. unfold app_mem, LOWMEM_END. left. lia.
            * right. exists 0x9f168, 9344. unfold KNC.KIND_NAME in Hx.
              split; [unfold AF.frame_RELRO; cbn [In]; left; reflexivity | lia].
            * change (AC.a_errno AC.ASYMS) with 0x5dc5ac. unfold KNC.KIND_NAME in Hx. lia.
            * change (AC.as_oom AC.ASYMS) with 0x12b920. unfold KNC.KIND_NAME in Hx. lia.
          + apply (f37_addr_keep mem mem2 _ 112 Hka). intros i Hi.
            rewrite (KKshimg (KNC.KIND_NAME + i) (Kimg (KNC.KIND_NAME + i) ltac:(lia))).
            apply KWsh; clear - Hi HGTfr; unfold KNC.KIND_NAME, AC.GT in *; lia.
        - exact HadS2.
        - unfold OURb in *. apply (f37_ba_eq _ _ _ _ HOUR).
          assert (Hl : length (OUR (g_in g)) = 6%nat) by (unfold OUR; rewrite length_map, length_seq; reflexivity).
          rewrite Hl. intros x Hx. apply K2fr. lia.
        - exact SPT. }
      split; [apply SPT; [lia | exact H272]|].
      split; [exact I|].
      split; [apply SPT; [lia | exact H224]|].
      split; [unfold rg; rewrite G21; exact F21|].
      split; [unfold rg; rewrite G23; exact F23|].
      split; [unfold rg; rewrite G25; exact F25|].
      split.
      { apply (Tac_ro.ifs_keep g fr (S j) regs regs2 mem mem2 HIFS).
        - intros HbI. apply (f37_ba_eq _ _ _ _ HbI). rewrite Tac_ro.tr_ID_length.
          intros x Hx. apply K2fr. lia.
        - intros HbF. apply (f37_ba_eq _ _ _ _ HbF). rewrite Tac_ro.tr_FG_length.
          intros x Hx. apply K2fr. lia.
        - intros xa xbs Hxa Hxl HbB. apply (f37_ba_eq _ _ _ _ HbB). intros x Hx. apply K2fr. lia.
        - exact HadS2. }
      (* s6 = 1: the range 0x82ca0-0x82d18 writes no s6 and the free keeps it (callee-saved) *)
      unfold rg; rewrite G22, F22; exact H22. }
    pose proof (Hcb8 g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End F37.
