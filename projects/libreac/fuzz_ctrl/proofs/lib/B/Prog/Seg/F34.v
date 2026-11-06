(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1126 of its 1261 lines of code are new or changed and 876 lines of the source are left out. *)
(* Segment F34 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B): 0x82bf4-0x82c20, the body of the
   row_of_block loop at row i (slot-plan-asan-ubsan section 2 row F34, call DECL@0x82c20, twin W02).

     0x82bf4  sb zero,8(s3)     -- s3 = S(fr) = (fr >> 3) + 0x7fff8000 (FRA): the four shadow bytes of the
     0x82bf8  sb zero,9(s3)        32-byte row slot [fr + 64, fr + 96) are set to 0, so the slot is marked
     0x82bfc  sb zero,10(s3)       usable before declaration_of writes it.
     0x82c00  sb zero,11(s3)
     0x82c04  bne a1,a2,82fa0   -- trap row T70: a1 = mulh(i,296) = 0 and a2 = srai(mul(i,296),63) = 0 from the
                                  row head (F33), so i * 296 does not overflow int64 and the branch is not taken.
     0x82c08  add s8,a0,s5      -- s8 = 296 i + T, the row address &cat[i] (T = CAT = 0x9f620).
     0x82c0c  sltu a0,s8,a0     -- the carry of that sum: 0, because 296 i + T < 2^64 (T + 3256 <= 0xa02d8).
     0x82c10  bnez a0,82fa0     -- trap row T71: not taken.
     0x82c14  mv a0,s7          -- a0 = T + 296 i, the row pointer of row i (s7, the row pointer of F33's cut).
     0x82c18  ld s6,152(s1)     -- s6 = [A + 152] = fr + 64, the row slot (spill set 0x815a0).
     0x82c1c  mv a1,s6
     0x82c20  jal declaration_of -> 0x82c24 with a0 = 1 (every catalogue row has decl_ok: declaration_of_rows)
                                   and the 32 bytes at fr + 64 equal to decl_i i.

   Image A's twin is 0x8286c-0x82884: there the row pointer is in s4 and the slot in s9, and image A has no
   overflow check (the two trap rows T70 / T71 are the ubsan build's). Image B keeps the row pointer in s7 and
   reloads the slot from the spill [A + 152]; the checked sum stays in s8, which F36 reads (`bnez s8` at
   0x82c38, trap row T72).

   Entry SlotInv's Inv_B82bf4_at (row i); exit SlotInv's Inv_B82c24_at (F35's entry, W03). Both official cuts
   carry the block as (Phi, AC.a_size len); the row path has len >= 50 (kind 9, t_rowsel), so AC.a_size len = len
   and the proof works with hb1 Phi len. FTURN (the cursor spills [A + 224] / [A + 232] and the Phi bytes), the
   spill [A + 272] and the turn's frame records and local `first` IFS g fr (S j) pass through: the run writes none
   of [A, A + 448), the block [Phi, Phi + len) and [fr + 2688, fr + 2920).
   (v1.9.0: the [A + 248] position of both cuts is `True`, and the entry's s6 = 1 is overwritten by the reload.)
   The call is used through its lib/B contract declaration_of_c.declaration_of_contract (Section Hypothesis
   DECL); the catalogue rows come from declaration_of.declaration_of_rows_holds. The run writes the four frame
   shadow bytes, the callee's stack window [sp - 2256, sp) and the row slot [fr + 64, fr + 96); FRA moves across
   that write set by the local lemma f34_fra_w, then to the materialized model by Tac_slot.sl_fra_move. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcDecl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require declaration_of_c declaration_of.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_ro.
Import ListNotations.
(* The short name YK11 could resolve to lib/Reusable/YK11.v, which the catalogue chain loads; this file's
   registers, mkst and FPState are image B's. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module DECLc := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.declaration_of_c.
Module DECLp := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.declaration_of.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module LPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module RP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcParse.
Module BZB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.BzBridge.

(* ========================= image / model helpers ========================= *)

(* The image bytes of a range, byte by byte (Image.image_bytes reads through Lib.Mem.wa). *)
Lemma f34_img_S : forall A n, Image.image_bytes rsegs A (S n) =
  match seg_rom rsegs (wa A), Image.image_bytes rsegs (A + 1) n with
  | Some b, Some bs => Some (b :: bs)
  | _, _ => None
  end.
Proof. reflexivity. Qed.

Lemma f34_img_nth : forall n A bs k, Image.image_bytes rsegs A n = Some bs -> (k < n)%nat ->
  seg_rom rsegs (Z_to_bv 64 (A + Z.of_nat k)) = nth_error bs k.
Proof.
  induction n as [|n IH]; intros A bs k H Hk; [cbn in Hk; lia|].
  rewrite f34_img_S in H. revert H.
  destruct (Image.image_bytes rsegs (A + 1) n) as [bs'|] eqn:E2;
    destruct (seg_rom rsegs (wa A)) as [b|] eqn:E1; intros H; simpl in H; try discriminate H.
  injection H as Hbs. subst bs. destruct k as [|k].
  - cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact E1.
  - cbn [nth_error]. replace (A + Z.of_nat (S k)) with (A + 1 + Z.of_nat k) by lia.
    apply (IH (A + 1) bs' k E2). lia.
Qed.

(* The catalogue rows: image bytes, decl_ok, length (declaration_of_rows_holds). *)
Lemma f34_row : forall i, (i < 11)%nat ->
  Image.image_bytes rsegs (CAT + CAT_ROW * Z.of_nat i) 296 = Some (rowb (Z.of_nat i)) /\
  decl_ok (rowb (Z.of_nat i)) = true /\ length (rowb (Z.of_nat i)) = 296%nat.
Proof.
  intros i Hi.
  destruct (DECLp.declaration_of_rows_holds i Hi) as (row & Himg & Hok & _).
  assert (E : DECLc.BOX_CATALOGUE + 296 * Z.of_nat i = CAT + CAT_ROW * Z.of_nat i)
    by (unfold CAT, CAT_ROW, DECLc.BOX_CATALOGUE; lia).
  rewrite E in Himg.
  assert (Erow : rowb (Z.of_nat i) = row) by (unfold rowb, img; rewrite Himg; reflexivity).
  rewrite Erow. split; [exact Himg|]. split; [exact Hok|].
  exact (Image.image_bytes_length rsegs 296 _ _ Himg).
Qed.

(* Every row's declaration is 32 bytes (the slot the bcmp of F35 reads). *)
Lemma f34_decl_len : forall i, (i < 11)%nat -> length (decl_i (Z.of_nat i)) = 32%nat.
Proof.
  intros i Hi.
  assert (H : forallb (fun k => Nat.eqb (length (decl_i (Z.of_nat k))) 32) (seq 0 11) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Nat.eqb_eq. exact (H i ltac:(apply in_seq; lia)).
Qed.

(* A non-zero kind needs a frame of at least 50 bytes, and the row path needs kind 9. *)
Lemma f34_k_big : forall inp j, t_k inp j <> 0 -> 50 <= t_len inp j.
Proof.
  intros inp j K. destruct (Z_le_gt_dec 50 (t_len inp j)) as [H|H]; [exact H|].
  exfalso. apply K. unfold t_k. apply RP.ctrlparse_none. intros (HC & _ & _). lia.
Qed.

Lemma f34_rowsel_len : forall inp j, t_rowsel inp j = true -> 50 <= t_len inp j.
Proof.
  intros inp j H. apply f34_k_big. intros K0.
  unfold t_rowsel in H. rewrite K0 in H. cbn in H. discriminate H.
Qed.

(* The catalogue is one registered global and lies in the image's RELRO range. *)
Lemma f34_cat_AG : In (0x9f620, 3256) AF.frame_AG.
Proof. apply (nth_error_In _ 55%nat). vm_compute. reflexivity. Qed.

Lemma f34_cat_RELRO : In (0x9f168, 9344) AF.frame_RELRO.
Proof. unfold AF.frame_RELRO. cbn [In]. left. reflexivity. Qed.

(* Every registered global lies in the image, below 0xa0708. *)
Lemma f34_ag_lo : forall a, in_globals AF.frame_AG a -> 0 <= a < 657928.
Proof.
  intros a (lo & len & Hil & Hr).
  assert (HB : forallb (fun p => andb (0 <=? fst p) (fst p + snd p <? 657928)) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in HB.
  pose proof (HB (lo, len) Hil) as H. cbn [fst snd] in H.
  apply andb_prop in H as (H1 & H2). apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* ========================= branch helpers ========================= *)

(* `bltu x,y` is not taken when y <= x (unsigned); the left operand is compared through its value mod 2^64. *)
Lemma f34_ltu_false : forall x y, 0 <= y < 2 ^ 64 -> y <= x mod 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hy Hxy. unfold bv_ltu. rewrite MState.unsigned_lit_wrap, (MState.unsigned_lit y) by lia.
  apply Z.ltb_ge. lia.
Qed.

(* `sltu rd,x,y` writes 0 under the same premise (the carry of a sum that does not wrap). *)
Lemma f34_sltu_zero : forall x y, 0 <= y < 2 ^ 64 -> y <= x mod 2 ^ 64 ->
  LPE.v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 0.
Proof.
  intros x y Hy Hxy. unfold LPE.v_sltu, LPE.c_ltu. rewrite (f34_ltu_false x y Hy Hxy). reflexivity.
Qed.

(* ========================= memory helpers ========================= *)

Lemma f34_mbyte_mrd : forall m q, mbyte rsegs m q = mrd rsegs m (wa q).
Proof. intros m q. reflexivity. Qed.

Lemma f34_outside_dec : forall W q, {outside W q} + {~ outside W q}.
Proof.
  induction W as [|[lo hi] W IH]; intros q; [left; exact I|].
  destruct (IH q) as [H|H]; [|right; intros (_ & Hc); exact (H Hc)].
  destruct (Z_le_dec lo q) as [H1|H1]; destruct (Z_lt_dec q hi) as [H2|H2].
  - right. intros (Hc & _). apply Hc. split; [exact H1 | exact H2].
  - left. split; [intros (_ & Hc); lia | exact H].
  - left. split; [intros (Hc & _); lia | exact H].
  - left. split; [intros (Hc & _); lia | exact H].
Qed.

Lemma f34_sub_stk : forall m lo hi lo' hi', stk rsegs m lo hi -> lo <= lo' -> hi' <= hi -> lo' <= hi' ->
  stk rsegs m lo' hi'.
Proof.
  intros m lo hi lo' hi' (H0 & H1 & H) Ha Hb Hc.
  split; [lia|]. split; [lia|]. intros a Haa. apply H. lia.
Qed.

(* A spilled word at s1 + off read at the FRA spill base A (the existential base of `spill` is A; both bases
   are compared through Z_to_bv 64, so the byte range of the cell pins the existential one). *)
Lemma f34_spill : forall regs m off v A, spill regs m off v -> rg regs 9 A ->
  0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 -> q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA H0 H1 Hoff.
  unfold rg in HA, HA'. rewrite HA in HA'.
  pose proof Hq as (Hq0 & Hq1 & _). rewrite length_le8 in Hq1.
  assert (E : A' = A).
  { apply (f_equal bv_unsigned) in HA'. rewrite !MState.unsigned_lit_wrap in HA'.
    rewrite (Z.mod_small A) in HA' by lia. Z.div_mod_to_equations. lia. }
  subst A'. exact Hq.
Qed.

(* A 32-byte writable cell carved out of a readable / writable stack range (the callee's output buffer). *)
Lemma f34_rw_of_stk : forall m lo hi, stk rsegs m lo hi -> lo + 32 <= hi ->
  exists ob, length ob = 32%nat /\ rw_cells rsegs m lo [CB 32 ob].
Proof.
  intros m lo hi HST Hle.
  pose proof (f34_sub_stk m lo hi lo (lo + 32) HST ltac:(lia) ltac:(lia) ltac:(lia)) as HS2.
  destruct (stk_bytes rsegs m lo (lo + 32) HS2 ltac:(lia)) as (bs & Hlen & Hb).
  replace (Z.to_nat (lo + 32 - lo)) with 32%nat in Hlen by lia.
  exists bs. split; [exact Hlen|]. split.
  - split; [cbn [cells_wf cell_wf]; split; [exact Hlen | exact I]|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - destruct HST as (H0 & H1 & H).
    split; [lia|]. split; [cbn [cells_size csize]; lia|].
    intros k Hk. cbn [cells_size csize] in Hk. apply (proj1 (H (lo + k) ltac:(lia))).
Qed.

Lemma f34_addr_keep : forall m m' p n, addressable m p n ->
  (forall a, p <= a < p + n -> mrd rsegs m' (wa (shadow_addr a)) = mrd rsegs m (wa (shadow_addr a))) ->
  addressable m' p n.
Proof.
  intros m m' p n (H0 & Hn & Hend & HA) HK. split; [lia|]. split; [lia|]. split; [lia|].
  intros k Hk. destruct (HA k Hk) as (Happ & b & Hb & Hok).
  split; [exact Happ|]. exists b. split; [|exact Hok]. rewrite (HK (p + k) ltac:(lia)). exact Hb.
Qed.

Lemma f34_addr_app : forall m p n k, addressable m p n -> 0 <= k < n -> app_mem (p + k).
Proof. intros m p n k (_ & _ & _ & HA) Hk. exact (proj1 (HA k Hk)). Qed.

Lemma f34_addr_of_bytes : forall m p n, 0 <= p -> 0 <= n -> p + n <= APPMEM_END ->
  (forall a, p <= a < p + n -> addressable m a 1) -> addressable m p n.
Proof.
  intros m p n Hp Hn Hend H. split; [lia|]. split; [lia|]. split; [lia|].
  intros k Hk. destruct (H (p + k) ltac:(lia)) as (_ & _ & _ & HA).
  pose proof (HA 0 ltac:(lia)) as HB. rewrite Z.add_0_r in HB. exact HB.
Qed.

(* Two readings of the same 8-byte cell agree modulo 2^64. *)
Lemma f34_wm_congr : forall (m : word -> option byte) a v1 v2,
  word_mem rsegs m a v1 -> word_mem rsegs m a v2 -> v1 mod 2 ^ 64 = v2 mod 2 ^ 64.
Proof.
  intros m a v1 v2 H1 H2.
  assert (Hb : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2.
    rewrite E1 in E2.
    assert (E2' : Z_to_bv 8 (le_byte v1 8 k) = Z_to_bv 8 (le_byte v2 8 k)) by congruence.
    apply (f_equal (@bv_unsigned 8)) in E2'. rewrite !kb_byte_unsigned in E2'. exact E2'. }
  apply Z.bits_inj'. intros jj Hj.
  destruct (Z.ltb_spec jj 64) as [Hlt|Hge].
  - set (k := Z.to_nat (jj / 8)).
    assert (Hk8 : (k < 8)%nat) by (unfold k; apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      apply Z.div_lt_upper_bound; lia).
    pose proof (Hb k Hk8) as Hbk.
    assert (Hoff : 8 * Z.of_nat k + (jj - 8 * Z.of_nat k) = jj) by lia.
    assert (Hjk : jj - 8 * Z.of_nat k = jj mod 8) by (unfold k; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      rewrite (Z.div_mod jj 8) at 1 by lia; lia).
    assert (Hoff8 : 0 <= jj - 8 * Z.of_nat k < 8) by (rewrite Hjk; apply Z.mod_pos_bound; lia).
    assert (HT : Z.testbit (le_byte v1 8 k) (jj - 8 * Z.of_nat k)
               = Z.testbit (le_byte v2 8 k) (jj - 8 * Z.of_nat k)) by (rewrite Hbk; reflexivity).
    rewrite !le_byte_testbit in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ 8)) in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) in HT by lia.
    rewrite Hoff in HT.
    rewrite !Z.testbit_mod_pow2 by lia.
    rewrite (proj2 (Z.ltb_lt jj 64)) by lia. exact HT.
  - rewrite !Z.testbit_mod_pow2 by lia. rewrite (proj2 (Z.ltb_ge jj 64)) by lia. reflexivity.
Qed.

Lemma f34_word_mem_back : forall W m m' a v, munch W m m' ->
  (forall x, a <= x < a + 8 -> outside W (bv_unsigned (Z_to_bv 64 x))) ->
  word_mem rsegs m' a v -> word_mem rsegs m a v.
Proof.
  intros W m m' a v MU HW H k Hk. rewrite <- (H k Hk). unfold mbyte.
  rewrite (MU (Z_to_bv 64 (a + Z.of_nat k))); [reflexivity|]. apply HW. lia.
Qed.

(* Every FakeStack metadata cell lies in [FS, FS + 36864). *)
Lemma f34_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q [Hq|[Hq|[(c & Hc & Hq)|(c & jj & Hc & Hj & Hq)]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hq. lia.
  - subst q. exact (a_fs_flag_range FS c jj Hc Hj).
Qed.

(* ========================= the machine run ========================= *)

(* 0x82bf4 -> 0x82c24: the four shadow stores at S + 8 .. S + 11 (so that [ost, ost + 32) is addressable), the
   two trap checks (neither taken), the slot reload and declaration_of(r, ost) by its contract. All bounds are
   on plain Z values, so the caller discharges them from the cut without touching the register file.
   Touched memory: the shadow bytes [S + 8, S + 12), the callee window [spv - 2256, spv) and the slot
   [ost, ost + 32). Read: [A + 152, A + 160), the 296 row bytes at T + o and their shadow, the runtime's cells. *)
Lemma f34_evt : DECLc.declaration_of_contract ->
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (S A T o ost spv lo : Z) (row ob : list byte),
    x2 = Z_to_bv 64 spv -> x9 = Z_to_bv 64 A -> x19 = Z_to_bv 64 S ->
    x10 = Z_to_bv 64 o -> x11 = Z_to_bv 64 0 -> x12 = Z_to_bv 64 0 ->
    x21 = Z_to_bv 64 T -> x23 = Z_to_bv 64 (T + o) ->
    2148236288 <= S -> S + 12 <= HIGHMEM_BEG ->
    (forall k, 0 <= k < 4 -> wview rsegs m (wa (S + 8 + k)) <> None) ->
    (forall k, 0 <= k < 4 -> in_shadow (S + 8 + k)) ->
    0 <= ost -> ost + 32 <= APPMEM_END -> (forall k, 0 <= k < 32 -> app_mem (ost + k)) -> app_mem (ost + 32) ->
    (forall k, 0 <= k < 32 -> S + 8 <= shadow_addr (ost + k) < S + 12) ->
    rw_cells rsegs m ost [CB 32 ob] -> length ob = 32%nat ->
    bytes_at rsegs m (A + 152) (le8 (Z_to_bv 64 ost)) -> HIGHMEM_BEG <= A -> A + 160 <= 2 ^ 64 ->
    0 <= o -> 0 <= T -> T + o + 296 <= 656088 -> (T + o) mod 8 = 0 ->
    length row = 296%nat -> decl_ok row = true ->
    bytes_at rsegs m (T + o) row -> addressable m (T + o) 296 ->
    stk rsegs m lo spv -> HIGHMEM_BEG <= lo -> lo + 2256 <= spv -> spv <= APPMEM_END ->
    (ost + 32 <= spv - 2256 \/ spv <= ost) -> RT_HI <= ost ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82c24) x2 x3 x4 t0' t1' t2' x8 x9 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                       x18 (Z_to_bv 64 S) x20 (Z_to_bv 64 T) (Z_to_bv 64 ost) (Z_to_bv 64 (T + o))
                       (Z_to_bv 64 (o + T)) x25 x26 x27 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82c24) fcs None m' (seg_rom rsegs) /\
         munch [(S + 8, S + 12); (spv - 2256, spv); (ost, ost + 32)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ shadow_rw m' /\ stk rsegs m' lo spv /\
         bytes_at rsegs m' ost (decl row) /\ addressable m' ost 32 /\
         (forall q, 0 <= q < 2 ^ 64 ->
            ~ outside [(S + 8, S + 12); (spv - 2256, spv); (ost, ost + 32)] q ->
            exists b, mrd rsegs m' (wa q) = Some b))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82bf4) fcs None m (seg_rom rsegs)).
Proof.
  intros DECL x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m S A T o ost spv lo row ob
    E2 E9 E19 E10 E11 E12 E21 E23 HSlo HShi HWv HSin Ho0 Ho1 Hoapp Hoend Hosh Hob Hoblen
    H152 HAhi HAb Hoz HTz Hrhi Hr8 Hrlen Hok Hrow Hraddr HST Hlo1 Hlo2 Hsp1 Hodj HoRT HMI HAC HSW.
  subst x2 x9 x19 x10 x11 x12 x21 x23.
  assert (EAPP : APPMEM_END = 140737488355328) by reflexivity.
  assert (EHMB : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (ERTH : RT_HI = 697272) by reflexivity.
  assert (ERTL : RT_LO = 657648) by reflexivity.
  assert (EDK : DECLc.DECLARATION_OF_K = 2256) by reflexivity.
  assert (EK : ASAN_K = 2147450880) by reflexivity.
  (* --- the four shadow stores --- *)
  assert (HSok : forall (m' : word -> option byte) k, wmono rsegs m m' -> 0 <= k < 4 ->
            store_ok rsegs m' (wa (S + 8 + k)) 1 = true).
  { intros m' k Hw Hk.
    assert (WR : wr_at rsegs m' (S + 8 + k) 1).
    { split; [lia|]. split; [lia|]. intros kk Hkk. assert (Ei : kk = 0) by lia. subst kk.
      rewrite Z.add_0_r. apply Hw. apply HWv. lia. }
    pose proof (wr_at_store_ok rsegs m' (S + 8 + k) 1 0 1%nat WR ltac:(lia) ltac:(lia)) as HSS.
    rewrite Z.add_0_r in HSS. exact HSS. }
  assert (H8 : store_ok rsegs m (wa (S + 8)) 1 = true).
  { replace (S + 8) with (S + 8 + 0) by lia. apply (HSok m 0); [apply wmono_refl | lia]. }
  step.
  match goal with
  | |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (H9 : store_ok rsegs mm (wa (S + 9)) 1 = true)
        by (replace (S + 9) with (S + 8 + 1) by lia; apply (HSok mm 1);
            [repeat (apply wmono_write); apply wmono_refl | lia])
  end.
  step.
  match goal with
  | |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (H10 : store_ok rsegs mm (wa (S + 10)) 1 = true)
        by (replace (S + 10) with (S + 8 + 2) by lia; apply (HSok mm 2);
            [repeat (apply wmono_write); apply wmono_refl | lia])
  end.
  step.
  match goal with
  | |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (H11 : store_ok rsegs mm (wa (S + 11)) 1 = true)
        by (replace (S + 11) with (S + 8 + 3) by lia; apply (HSok mm 3);
            [repeat (apply wmono_write); apply wmono_refl | lia])
  end.
  step.
  (* --- the memory after the four stores --- *)
  match goal with
  | |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (Em1 : mm = write_to_mem (write_to_mem (write_to_mem (write_to_mem m (wa (S + 8)) [Z_to_bv 8 0])
                       (wa (S + 9)) [Z_to_bv 8 0]) (wa (S + 10)) [Z_to_bv 8 0]) (wa (S + 11)) [Z_to_bv 8 0])
        by (repeat f_equal; try reflexivity; vm_compute; reflexivity);
      rewrite Em1; clear Em1
  end.
  set (m1 := write_to_mem (write_to_mem (write_to_mem (write_to_mem m (wa (S + 8)) [Z_to_bv 8 0])
                 (wa (S + 9)) [Z_to_bv 8 0]) (wa (S + 10)) [Z_to_bv 8 0]) (wa (S + 11)) [Z_to_bv 8 0]) in *.
  assert (MU1 : munch [(S + 8, S + 12)] m m1).
  { unfold m1. apply munch_write; [apply munch_write; [apply munch_write; [apply munch_write;
      [apply munch_refl | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]
      | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]
      | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]
      | lia | cbn [length Z.of_nat]; lia | cbn [inside length Z.of_nat]; left; lia]. }
  assert (WM1 : wmono rsegs m m1)
    by (unfold m1; apply wmono_write, wmono_write, wmono_write, wmono_write, wmono_refl).
  assert (MI1 : mem_inv rsegs m1).
  { unfold m1. apply mem_inv_store; [apply mem_inv_store; [apply mem_inv_store;
      [apply mem_inv_store; [exact HMI|] |] |] |]; cbn [length].
    - replace (S + 8) with (S + 8 + 0) by lia. apply (HSok m 0); [apply wmono_refl | lia].
    - replace (S + 9) with (S + 8 + 1) by lia. apply (HSok _ 1); [apply wmono_write, wmono_refl | lia].
    - replace (S + 10) with (S + 8 + 2) by lia.
      apply (HSok _ 2); [apply wmono_write, wmono_write, wmono_refl | lia].
    - replace (S + 11) with (S + 8 + 3) by lia.
      apply (HSok _ 3); [apply wmono_write, wmono_write, wmono_write, wmono_refl | lia]. }
  assert (Hb8 : forall k, 0 <= k < 4 -> bytes_at rsegs m1 (S + 8 + k) [Z_to_bv 8 0]).
  { intros k Hk. unfold m1.
    assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
    destruct Hk' as [ -> | [ -> | [ -> | -> ]]].
    - rewrite Z.add_0_r.
      apply bytes_at_write_other; [apply bytes_at_write_other; [apply bytes_at_write_other;
        [apply bytes_at_write_same | | |] | | |] | | |]; cbn [length]; lia.
    - replace (S + 8 + 1) with (S + 9) by lia.
      apply bytes_at_write_other; [apply bytes_at_write_other;
        [apply bytes_at_write_same | | |] | | |]; cbn [length]; lia.
    - replace (S + 8 + 2) with (S + 10) by lia.
      apply bytes_at_write_other; [apply bytes_at_write_same | | |]; cbn [length]; lia.
    - replace (S + 8 + 3) with (S + 11) by lia. apply bytes_at_write_same; cbn [length]; lia. }
  assert (Hkeep : forall a bs, bytes_at rsegs m a bs -> (a + Z.of_nat (length bs) <= S + 8 \/ S + 12 <= a) ->
                    bytes_at rsegs m1 a bs).
  { intros a bs Hb Hd. eapply fl_bytes; [exact Hb | exact MU1 |].
    intros x Hx. cbn [outside]. split; [lia | exact I]. }
  assert (Hsh1 : forall a, in_shadow a -> exists b, mrd rsegs m1 (wa a) = Some b).
  { intros a Ha.
    destruct (Z_le_dec (S + 8) a) as [Hl|Hl]; destruct (Z_lt_dec a (S + 12)) as [Hh|Hh].
    - destruct (Hb8 (a - S - 8) ltac:(lia)) as (_ & _ & Hb).
      replace (S + 8 + (a - S - 8)) with a in Hb by lia.
      pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as Hb0. cbn [Z.of_nat] in Hb0.
      rewrite Z.add_0_r in Hb0. exists (Z_to_bv 8 0). exact Hb0.
    - destruct (HSW a Ha) as (_ & b & Hb). exists b. unfold mrd in *. rewrite (MU1 (wa a)); [exact Hb|].
      rewrite wa_unsigned by (pose proof (in_shadow_range a Ha); lia). cbn [outside]. split; [lia | exact I].
    - destruct (HSW a Ha) as (_ & b & Hb). exists b. unfold mrd in *. rewrite (MU1 (wa a)); [exact Hb|].
      rewrite wa_unsigned by (pose proof (in_shadow_range a Ha); lia). cbn [outside]. split; [lia | exact I].
    - destruct (HSW a Ha) as (_ & b & Hb). exists b. unfold mrd in *. rewrite (MU1 (wa a)); [exact Hb|].
      rewrite wa_unsigned by (pose proof (in_shadow_range a Ha); lia). cbn [outside]. split; [lia | exact I]. }
  assert (HSW1 : shadow_rw m1)
    by (intros a Ha; split; [apply WM1; exact (proj1 (HSW a Ha)) | exact (Hsh1 a Ha)]).
  assert (HAC1 : asan_cells m1).
  { apply (asan_cells_kept [(S + 8, S + 12)] m m1 HAC MU1).
    unfold RT_LO, RT_HI. cbn [disjoint_from]. split; [left; lia | exact I]. }
  assert (Hrow1 : bytes_at rsegs m1 (T + o) row) by (apply Hkeep; [exact Hrow | rewrite Hrlen; lia]).
  assert (H152' : bytes_at rsegs m1 (A + 152) (le8 (Z_to_bv 64 ost)))
    by (apply Hkeep; [exact H152 | rewrite length_le8; lia]).
  assert (HL152 : ov_read_bytes rsegs m1 (wa (A + 152)) 8 = Some (le8 (Z_to_bv 64 ost))).
  { pose proof (bytes_at_ov_read rsegs m1 (A + 152) (le8 (Z_to_bv 64 ost)) 0 8 H152'
      ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (Hob1 : rw_cells rsegs m1 ost [CB 32 ob]).
  { destruct Hob as ((Hwf & Hbb) & Hw). split.
    - split; [exact Hwf|]. eapply fl_bytes; [exact Hbb | exact MU1 |].
      intros x Hx. cbn [cells_bytes cbytes] in Hx. rewrite app_nil_r, Hoblen in Hx.
      cbn [outside]. split; [|exact I]. intros Hc.
      apply (app_not_shadow x).
      + replace x with (ost + (x - ost)) by lia. apply Hoapp. cbn [Z.of_nat] in Hx. lia.
      + replace x with (S + 8 + (x - S - 8)) by lia. apply HSin. lia.
    - unfold m1. apply wr_at_write, wr_at_write, wr_at_write, wr_at_write. exact Hw. }
  assert (Hstk1 : stk rsegs m1 lo spv).
  { unfold m1. apply stk_write; [apply stk_write; [apply stk_write; [apply stk_write;
      [exact HST | lia | cbn [length]; lia] | lia | cbn [length]; lia] | lia | cbn [length]; lia]
      | lia | cbn [length]; lia]. }
  assert (Haddr1 : addressable m1 ost 32).
  { split; [lia|]. split; [lia|]. split; [lia|].
    intros k Hk. split; [apply Hoapp; lia|].
    exists (Z_to_bv 8 0). split; [|unfold shadow_ok; left; reflexivity].
    destruct (Hb8 (shadow_addr (ost + k) - S - 8) ltac:(pose proof (Hosh k Hk); lia)) as (_ & _ & Hb).
    replace (S + 8 + (shadow_addr (ost + k) - S - 8)) with (shadow_addr (ost + k)) in Hb
      by (pose proof (Hosh k Hk); lia).
    pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as Hb0. cbn [Z.of_nat] in Hb0.
    rewrite Z.add_0_r in Hb0. exact Hb0. }
  assert (Haddrrow1 : addressable m1 (T + o) 296).
  { apply (f34_addr_keep m m1 (T + o) 296 Hraddr). intros a Ha. unfold mrd.
    rewrite (MU1 (wa (shadow_addr a))); [reflexivity|].
    assert (Happa : app_mem a) by (pose proof (f34_addr_app m (T + o) 296 (a - (T + o)) Hraddr ltac:(lia)) as Hp;
      replace (T + o + (a - (T + o))) with a in Hp by lia; exact Hp).
    rewrite wa_unsigned by (pose proof (in_shadow_range _ (shadow_of_app a Happa)); lia).
    cbn [outside]. split; [|exact I]. intros Hc.
    unfold shadow_addr, ASAN_K in *. revert Ha Hc Hrhi HTz Hoz HSlo. Z.div_mod_to_equations. lia. }
  (* --- 0x82c04 bne a1,a2 (0 = 0): not taken --- *)
  step. if_false.
  (* --- 0x82c08 add s8,a0,s5 ; 0x82c0c sltu a0,s8,a0 : the sum does not wrap --- *)
  step. step.
  rewrite (f34_sltu_zero (o + T) o) by (first [lia | rewrite Z.mod_small by lia; lia]).
  (* --- 0x82c10 bnez a0 (a0 = 0): not taken --- *)
  step. if_false.
  (* --- 0x82c14 mv a0,s7 ; 0x82c18 ld s6,152(s1) ; 0x82c1c mv a1,s6 ; 0x82c20 jal declaration_of --- *)
  step. step. step. step.
  pose proof DECL as HD. unfold DECLc.declaration_of_contract in HD. cbv zeta in HD.
  eapply evt_cut.
  { eapply HD with (lo := lo) (row := row) (ob := ob).
    all: rewrite ?(MState.unsigned_lit (T + o)), ?(MState.unsigned_lit ost), ?(MState.unsigned_lit spv) by lia.
    - exact Hstk1.
    - unfold DECLc.DECLARATION_OF_K in *. lia.
    - exact Hr8.
    - exact Hrlen.
    - exact Hrow1.
    - exact Hob1.
    - right. lia.
    - left. unfold DECLc.DECLARATION_OF_K in *. lia.
    - unfold DECLc.DECLARATION_OF_K in *. destruct Hodj as [HDj|HDj]; [left; lia | right; lia].
    - exact MI1.
    - exact HAC1.
    - exact HSW1.
    - exact Hlo1.
    - exact Hsp1.
    - exact Haddrrow1.
    - exact Haddr1.
    - exact Hoend.
    - right. exact HoRT. }
  intros ms2 Hpost.
  unfold DECLc.declaration_of_post in Hpost.
  destruct Hpost as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                     E2m & MU2 & WM2 & MI2 & ST2 & RW2 & BA2 & AC2 & SW2).
  subst ms2.
  rewrite (MState.unsigned_lit ost) in MU2, RW2 by lia.
  rewrite (MState.unsigned_lit spv) in MU2, ST2 by lia.
  rewrite Hok in RW2.
  replace (ret_pc (Z_to_bv 64 0x82c24)) with (Z_to_bv 64 0x82c24)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  rewrite Hok.
  (* --- the combined write set --- *)
  assert (MUa : munch [(S + 8, S + 12); (spv - 2256, spv); (ost, ost + 32)] m m2).
  { eapply munch_trans.
    - eapply munch_weaken; [|exact MU1]. intros x (Hx & _). cbn [outside]. split; [exact Hx | exact I].
    - eapply munch_weaken; [|exact MU2]. intros x (_ & Hx1 & Hx2 & _). cbn [outside].
      split; [exact Hx1|]. split; [exact Hx2 | exact I]. }
  assert (WMa : wmono rsegs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
  destruct RW2 as (((Hdlen & _) & Hdbb) & _).
  cbn [cells_bytes cbytes] in Hdbb. rewrite app_nil_r in Hdbb.
  assert (HINa : forall q, 0 <= q < 2 ^ 64 ->
            ~ outside [(S + 8, S + 12); (spv - 2256, spv); (ost, ost + 32)] q ->
            exists b, mrd rsegs m2 (wa q) = Some b).
  { intros q Hq Hno.
    assert (Hslot : ost <= q < ost + 32 -> exists b, mrd rsegs m2 (wa q) = Some b).
    { intros Hin. destruct Hdbb as (_ & _ & Hb).
      pose proof (Hb (Z.to_nat (q - ost)) ltac:(rewrite Hdlen; lia)) as Hb0.
      replace (ost + Z.of_nat (Z.to_nat (q - ost))) with q in Hb0 by lia.
      destruct (nth_error (decl row) (Z.to_nat (q - ost))) as [b|] eqn:En;
        [exists b; exact Hb0 | apply nth_error_None in En; rewrite Hdlen in En; lia]. }
    assert (Hshq : S + 8 <= q < S + 12 -> exists b, mrd rsegs m2 (wa q) = Some b).
    { intros Hin. apply (proj2 (SW2 q ltac:(replace q with (S + 8 + (q - S - 8)) by lia; apply HSin; lia))). }
    assert (Hwinq : spv - 2256 <= q < spv -> exists b, mrd rsegs m2 (wa q) = Some b).
    { intros Hin. apply (proj2 (proj2 (proj2 ST2) q ltac:(lia))). }
    destruct (Z_le_dec (S + 8) q) as [L1|L1]; destruct (Z_lt_dec q (S + 12)) as [L2|L2];
    destruct (Z_le_dec (spv - 2256) q) as [L3|L3]; destruct (Z_lt_dec q spv) as [L4|L4];
    destruct (Z_le_dec ost q) as [L5|L5]; destruct (Z_lt_dec q (ost + 32)) as [L6|L6];
    first [ apply Hshq; lia | apply Hwinq; lia | apply Hslot; lia
          | exfalso; apply Hno; cbn [outside]; repeat split; try exact I; lia ]. }
  assert (Haddr2 : addressable m2 ost 32).
  { apply (f34_addr_keep m1 m2 ost 32 Haddr1). intros a Ha. unfold mrd.
    rewrite (MU2 (wa (shadow_addr a))); [reflexivity|].
    assert (Hin : S + 8 <= shadow_addr a < S + 12) by (pose proof (Hosh (a - ost) ltac:(lia)) as Hp;
      replace (ost + (a - ost)) with a in Hp by lia; exact Hp).
    assert (Happa : app_mem a) by (replace a with (ost + (a - ost)) by lia; apply Hoapp; lia).
    assert (Hinsh : in_shadow (shadow_addr a)) by (apply shadow_of_app; exact Happa).
    rewrite wa_unsigned by (pose proof (in_shadow_range _ Hinsh); lia).
    cbn [outside]. split; [|split; [|exact I]].
    - intros Hc. apply (app_not_shadow (shadow_addr a)); [|exact Hinsh].
      unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia.
    - intros Hc. apply (app_not_shadow (shadow_addr a)); [|exact Hinsh].
      replace (shadow_addr a) with (ost + (shadow_addr a - ost)) by lia. apply Hoapp. lia. }
  apply evt_done.
  eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
  split; [reflexivity|].
  split; [exact MUa|]. split; [exact WMa|]. split; [exact MI2|]. split; [exact SW2|].
  split; [exact ST2|]. split; [exact Hdbb|]. split; [exact Haddr2 | exact HINa].
Qed.

(* Every loaded segment of image B ends at or below AC.GT, so no byte at or above AC.GT is read-only. *)
Lemma f34_segs_below_GT : BZB.seg_tops_below rsegs AC.GT = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f34_ro_gt : forall a, AC.GT <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold ro_addr.
  destruct (find_segment rsegs (bv_unsigned (wa a)) 1) as [s|] eqn:E; [|reflexivity].
  destruct (BZB.find_segment_below rsegs AC.GT (bv_unsigned (wa a)) 1 s f34_segs_below_GT E ltac:(lia))
    as [L|L]; [exfalso; rewrite MState.unsigned_lit in L by (unfold AC.GT in *; lia); lia | cbn in L; lia].
Qed.

(* addressable comes back from the normalized memory (the shadow bytes read the same, mrd_rel). *)
Lemma f34_addr_back : forall m m0 p n, mem_rel rsegs m m0 -> addressable m0 p n -> addressable m p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|].
  exists b. rewrite (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

(* f34_evt on the cut's own memory: ro_agree in place of mem_inv (FRA carries ro_agree only). The run is taken
   on the normalized memory (mem_inv_normalize), where the read-side premises hold by the mem_rel transfer
   lemmas of Seg/Tac_ro.v and the slot [ost, ost + 32) stays writable (it lies at or above AC.GT, where no byte
   is read-only, f34_ro_gt); MemNorm.evt_normalize carries the run back to the cut's memory, and the post's
   facts come back across mem_rel / ro_same. *)
Lemma f34_evt_ro : DECLc.declaration_of_contract ->
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fcs : bv 32) (m : word -> option byte)
         (S A T o ost spv lo : Z) (row ob : list byte),
    x2 = Z_to_bv 64 spv -> x9 = Z_to_bv 64 A -> x19 = Z_to_bv 64 S ->
    x10 = Z_to_bv 64 o -> x11 = Z_to_bv 64 0 -> x12 = Z_to_bv 64 0 ->
    x21 = Z_to_bv 64 T -> x23 = Z_to_bv 64 (T + o) ->
    2148236288 <= S -> S + 12 <= HIGHMEM_BEG ->
    (forall k, 0 <= k < 4 -> wview rsegs m (wa (S + 8 + k)) <> None) ->
    (forall k, 0 <= k < 4 -> in_shadow (S + 8 + k)) ->
    0 <= ost -> ost + 32 <= APPMEM_END -> (forall k, 0 <= k < 32 -> app_mem (ost + k)) -> app_mem (ost + 32) ->
    (forall k, 0 <= k < 32 -> S + 8 <= shadow_addr (ost + k) < S + 12) ->
    rw_cells rsegs m ost [CB 32 ob] -> length ob = 32%nat ->
    bytes_at rsegs m (A + 152) (le8 (Z_to_bv 64 ost)) -> HIGHMEM_BEG <= A -> A + 160 <= 2 ^ 64 ->
    0 <= o -> 0 <= T -> T + o + 296 <= 656088 -> (T + o) mod 8 = 0 ->
    length row = 296%nat -> decl_ok row = true ->
    bytes_at rsegs m (T + o) row -> addressable m (T + o) 296 ->
    stk rsegs m lo spv -> HIGHMEM_BEG <= lo -> lo + 2256 <= spv -> spv <= APPMEM_END ->
    (ost + 32 <= spv - 2256 \/ spv <= ost) -> AC.GT <= ost ->
    ro_agree rsegs m -> asan_cells m -> shadow_rw m ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x82c24) x2 x3 x4 t0' t1' t2' x8 x9 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                       x18 (Z_to_bv 64 S) x20 (Z_to_bv 64 T) (Z_to_bv 64 ost) (Z_to_bv 64 (T + o))
                       (Z_to_bv 64 (o + T)) x25 x26 x27 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82c24) fcs None m' (seg_rom rsegs) /\
         munch [(S + 8, S + 12); (spv - 2256, spv); (ost, ost + 32)] m m' /\
         wmono rsegs m m' /\ ro_agree rsegs m' /\ shadow_rw m' /\ stk rsegs m' lo spv /\
         bytes_at rsegs m' ost (decl row) /\ addressable m' ost 32 /\
         (forall q, 0 <= q < 2 ^ 64 ->
            ~ outside [(S + 8, S + 12); (spv - 2256, spv); (ost, ost + 32)] q ->
            exists b, mrd rsegs m' (wa q) = Some b))
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x82bf4) fcs None m (seg_rom rsegs)).
Proof.
  intros DECL x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fcs m S A T o ost spv lo row ob
    E2 E9 E19 E10 E11 E12 E21 E23 HSlo HShi HWv HSin Ho0 Ho1 Hoapp Hoend Hosh Hob Hoblen
    H152 HAhi HAb Hoz HTz Hrhi Hr8 Hrlen Hok Hrow Hraddr HST Hlo1 Hlo2 Hsp1 Hodj HoGT HRO HAC HSW.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  assert (Hlo0 : LOWMEM_END <= lo) by (unfold HIGHMEM_BEG, LOWMEM_END in *; lia).
  assert (Hsp64 : spv <= 2 ^ 64) by (unfold APPMEM_END in *; lia).
  assert (HWv0 : forall k, 0 <= k < 4 -> wview rsegs (normalize rsegs m) (wa (S + 8 + k)) <> None).
  { intros k Hk.
    apply (proj2 (Tac_ro.wview_hi m _ (S + 8 + k) REL ltac:(unfold HIGHMEM_BEG, LOWMEM_END in *; lia))).
    exact (HWv k Hk). }
  assert (Hob0 : rw_cells rsegs (normalize rsegs m) ost [CB 32 ob]).
  { destruct Hob as ((Hwf & Hbb) & Hw). split.
    - split; [exact Hwf | exact (Tac_ro.ba_rel m _ _ _ REL Hbb)].
    - pose proof Hw as (Hw0 & Hw1 & _).
      eapply (wr_at_norm rsegs); [exact REL | exact Hw |].
      intros i Hi. apply f34_ro_gt. lia. }
  pose proof (f34_evt DECL x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
    x24 x25 x26 x27 x28 x29 x30 x31 Fr fcs (normalize rsegs m) S A T o ost spv lo row ob
    E2 E9 E19 E10 E11 E12 E21 E23 HSlo HShi HWv0 HSin Ho0 Ho1 Hoapp Hoend Hosh Hob0 Hoblen
    (Tac_ro.ba_rel m _ _ _ REL H152) HAhi HAb Hoz HTz Hrhi Hr8 Hrlen Hok (Tac_ro.ba_rel m _ _ _ REL Hrow)
    (Tac_ro.addressable_rel m _ _ _ REL Hraddr) (Tac_ro.stk_rel m _ lo _ REL Hlo0 Hsp64 HST) Hlo1 Hlo2 Hsp1
    Hodj ltac:(unfold RT_HI, AC.GT in *; lia) (mem_inv_normalize rsegs m)
    (Tac_ro.asan_cells_rel m _ REL HAC) (Tac_ro.shadow_rw_rel m _ REL HSW)) as HC.
  pose proof (evt_normalize rsegs _ _ _ _ _ _ m (seg_rom rsegs) ltac:(vm_compute; reflexivity) HRO HC) as HN.
  eapply LE.evt_mono; [exact HN|].
  intros ms (s0' & (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
              E & MU & WM & MI' & SW' & ST' & BA' & AD' & IN') & Hrel & Hros).
  subst s0'.
  destruct ms as [regsX frX pcX svcX rvX fcX memX romX].
  destruct Hrel as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmr).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmr, Hros.
  subst regsX frX pcX svcX rvX fcX romX.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', memX.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) memX m0' REL Hmr Hros MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) memX m0' REL Hmr Hros WM)|].
  split; [exact (ro_agree_of_mem_rel rsegs memX m0' Hmr)|].
  split.
  { intros a Ha. pose proof (in_shadow_range a Ha) as Hr.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
    destruct (SW' a Ha) as (Hw & b & Hb). split.
    - apply (proj1 (Tac_ro.wview_hi memX m0' a Hmr ltac:(unfold LOWMEM_END; lia))). exact Hw.
    - exists b. rewrite (mrd_rel rsegs memX m0' (wa a) Hmr). exact Hb. }
  split; [exact (Tac_ro.stk_rel_back memX m0' lo _ Hmr Hlo0 Hsp64 ST')|].
  split; [exact (proj2 (bytes_at_rel rsegs memX m0' _ _ Hmr) BA')|].
  split; [exact (f34_addr_back memX m0' ost 32 Hmr AD')|].
  intros q Hq Hno. destruct (IN' q Hq Hno) as (b & Hb). exists b.
  rewrite (mrd_rel rsegs memX m0' (wa q) Hmr). exact Hb.
Qed.

(* IFS (the two frame records and the local `first` [fr + 2880, fr + 2920)) survives a write W that misses
   [fr + 2688, fr + 2920), given `first`'s addressability on the new memory (FLI's RAD, third range): Tac_ro's
   ifs_munch with the narrower range this segment's W needs (its row slot [fr + 64, fr + 96) is in the frame). The
   records are 38 and 72 bytes (Tac_ro.tr_ID_length / tr_FG_length), so they lie in [fr + 2688, fr + 2840). *)
Lemma f34_IFS_keep : forall g fr j regs regs' m m' W,
  IFS g fr j regs m -> munch W m m' ->
  (forall x, fr + 2688 <= x < fr + 2920 -> outside W x) ->
  addressable m' (fr + 2880) 40 ->
  IFS g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' W H MU HW Hfst.
  apply (Tac_ro.ifs_keep g fr j regs regs' m m' H); [| | | exact Hfst].
  - intros Hb. apply (fl_bytes W m m' _ _ Hb MU). rewrite Tac_ro.tr_ID_length. intros x Hx. apply HW. lia.
  - intros Hb. apply (fl_bytes W m m' _ _ Hb MU). rewrite Tac_ro.tr_FG_length. intros x Hx. apply HW. lia.
  - intros a bs Ha Hab Hb. apply (fl_bytes W m m' a bs Hb MU). intros x Hx. apply HW. lia.
Qed.

(* asan_fs_cells (generated AsanRT.v), the one fact this file reads: the FakeStack pointer cell at RT_TP holds a
   word. Taken apart once here, by statement. *)
Lemma f34_fs_tp : forall sp m md, AsanRTInv.RT sp m md -> exists FS : word, bytes_at rsegs m RT_TP (le8 FS).
Proof.
  intros sp m md HRT. pose proof (AsanRTInv.RT_fs_cells _ _ _ HRT) as Hc. unfold asan_fs_cells in Hc.
  decompose [and ex] Hc.
  match goal with Hx : bytes_at rsegs m RT_TP (le8 ?F) |- _ => exists F; exact Hx end.
Qed.

Section F34.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* declaration_of (0x83114): it copies the row's declaration into the 32-byte slot and returns 1 when the row
   satisfies decl_ok. It checks the 296 row bytes and the 32 slot bytes in the shadow map; both ranges are
   addressable, so its error path is not reached. It writes only [sp - 2256, sp) and the slot. *)
Hypothesis DECL : DECLc.declaration_of_contract.

(* a_laws_blocks, through SlotInv's lw_blocks: a live block ends below stklo, and its bytes are app memory off
   the side stack (lwb_byte's per-byte list taken apart once here). *)
Lemma f34_blocks : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, p <= a < p + n -> app_mem a /\ ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin.
  destruct (lw_blocks (APIf rc) H mem md p n HAH Hin) as [_ _ Hle _ Hall].
  split; [exact Hle|]. intros a Ha. destruct (Hall a Ha) as (Happ & _ & _ & _ & Hnfs).
  split; [exact Happ | exact Hnfs].
Qed.

(* The Lib-evt -> SR bridge (F31's sl_run_lib: the callee contract is a Lib.Exec.evt). The one lazy run of this
   file: 0x82bf4 -> 0x82c24, reading [A + 152, A + 160), the 296 bytes at CAT + 296 i and their shadow bytes,
   the runtime's cells, and writing [S(fr) + 8, S(fr) + 12), [sp - 2256, sp) and [fr + 64, fr + 96). *)
Lemma f34_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  LE.evt rsegs
    (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* ===================== FRA across the segment's write set ===================== *)

(* W = the four frame-shadow bytes S(fr) + 8 .. S(fr) + 11, declaration_of's stack window [sp - 2256, sp) and
   the row slot [fr + 64, fr + 96). RT by RT_meta_write (the frame shadow is rewritten; every shadow byte is
   still readable); AH, stklo and stkhi by a_laws_store (frame on the real stack) or Tac_fs's a_fs_ok_store_AH
   (frame in the side stack); the side arm's frame record FSREC by Tac_slot's fsrec_keep_app_lo (its bytes are
   app memory below stklo outside the frame; W's app bytes are the slot, inside the frame, and the callee window,
   above stklo); the 392 shadow bytes are rebuilt from shadow_rw mem'; the registered globals and the window
   bytes outside the frame keep their shadow bytes (W's shadow bytes are those of the slot, inside the frame);
   every other FRA cell is outside W. ENT moves by Tac_slot's ent_store: W lies in the frame's shadow, the slot
   window below S and the frame. *)
Lemma f34_fra_w : forall g fr hb regs regs' mem mem' md Asp spv,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  getr regs 9 = Z_to_bv 64 Asp -> AC.aspZ regs = spv ->
  fr + FRAME_BYTES <= Asp -> 0 <= Asp < 2 ^ 64 -> AC.GT <= fr ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) ->
  HIGHMEM_BEG + 4096 <= spv -> spv <= Asp -> spv <= APPMEM_END ->
  (fr + FRAME_BYTES <= spv - 2256 \/ spv <= fr) ->
  munch [(Sfr fr + 8, Sfr fr + 12); (spv - 2256, spv); (fr + 64, fr + 96)] mem mem' ->
  wmono rsegs mem mem' -> ro_agree rsegs mem' -> shadow_rw mem' ->
  (forall q, 0 <= q < 2 ^ 64 ->
     ~ outside [(Sfr fr + 8, Sfr fr + 12); (spv - 2256, spv); (fr + 64, fr + 96)] q ->
     exists b, mrd rsegs mem' (wa q) = Some b) ->
  stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md /\ ENT APIf g hb mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md Asp spv HFRA HENT HrA Hasp HfrA HAS' HGT Happ Hsplo HspA HspE Hdw
    MU WM HRO HSW' HIN HWIN E2 E3 E4 E8 E9 E19 E26.
  pose proof HFRA as HFRA0.
  pose proof (fra_in_apart B APIf ra g fr hb regs mem md HFRA) as Hinap.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & Hwout &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  unfold AC.GT in HGT.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (Hsp0 : 0 <= sp) by (unfold AC.aspZ in Haspz; rewrite <- Haspz; apply bv_unsigned_in_range).
  assert (HAb : 0 <= A < 2 ^ 64) by (unfold stk in Hwin; destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (EA : A = Asp).
  { assert (Eq : Z_to_bv 64 A = Z_to_bv 64 Asp) by (unfold rg in Hr9; congruence).
    apply (f_equal (bv_unsigned (n := 64))) in Eq. rewrite !MState.unsigned_lit in Eq by lia. exact Eq. }
  assert (Esp : sp = spv) by (unfold AC.aspZ in Haspz, Hasp; lia).
  clear Haspz. subst A. subst sp.
  assert (Haspz : AC.aspZ regs = spv) by exact Hasp.
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; Z.div_mod_to_equations; lia).
  assert (Efr8 : 8 * (fr / 8) = fr) by (revert Hfr8; Z.div_mod_to_equations; lia).
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  assert (HSlo : ASAN_K + 785408 <= Sfr fr) by (unfold Sfr, shadow_addr, ASAN_K in *; Z.div_mod_to_equations; lia).
  assert (HShi : Sfr fr + 12 <= HIGHMEM_BEG).
  { pose proof (HshIS (Sfr fr + 11) ltac:(lia)) as Hin11.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin11 |- *. lia. }
  assert (Hnsh : forall x, app_mem x -> ~ (Sfr fr + 8 <= x < Sfr fr + 12))
    by (intros x Hx Hin; exact (app_not_shadow x Hx (HshIS x ltac:(lia)))).
  assert (Hfrsh : forall x, fr <= x < fr + FRAME_BYTES -> ~ (Sfr fr + 8 <= x < Sfr fr + 12))
    by (intros x Hx; apply Hnsh; apply Happ; lia).
  assert (Epre : forall q, Sfr fr + 8 <= q < Sfr fr + 12 ->
            shadow_addr (8 * (q - ASAN_K)) = q /\ fr + 64 <= 8 * (q - ASAN_K) < fr + 96).
  { intros q Hq. unfold Sfr, shadow_addr in *. split.
    - replace (8 * (q - ASAN_K)) with ((q - ASAN_K) * 8) by lia. rewrite Z.div_mul by lia. lia.
    - lia. }
  unfold ASAN_K, HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *.
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x Hx0 Hx1.
    assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by lia. cbn [outside]. repeat split; try exact I; lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  assert (HWfr : forall x, fr <= x < fr + 24 -> outside
                   [(Sfr fr + 8, Sfr fr + 12); (spv - 2256, spv); (fr + 64, fr + 96)] x).
  { intros x Hx. cbn [outside]. split; [apply Hfrsh; lia|]. repeat split; try exact I; lia. }
  assert (HWA : forall x, Asp + 40 <= x < Asp + 344 -> outside
                  [(Sfr fr + 8, Sfr fr + 12); (spv - 2256, spv); (fr + 64, fr + 96)] x).
  { intros x Hx. cbn [outside]. repeat split; try exact I; lia. }
  assert (HWsv : forall x, g_S g - 104 <= x < g_S g -> outside
                   [(Sfr fr + 8, Sfr fr + 12); (spv - 2256, spv); (fr + 64, fr + 96)] x).
  { intros x Hx. cbn [outside]. repeat split; try exact I; lia. }
  assert (HRT' : AsanRTInv.RT spv mem' md).
  { eapply (AsanRTInv.RT_meta_write spv spv mem mem' md md); [exact HRT | exact MU | exact WM | | ].
    - unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
        RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
        RT_AGLOB, RT_AGLOB_LEN.
      cbn [disjoint_from]. repeat split; try exact I; left; lia.
    - intros a Ha. destruct (HSW' a Ha) as (_ & b & Hb). exists b. exact Hb. }
  assert (Hwrit : forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q)
    by (intros q Hq Hw; exact (WM (Z_to_bv 64 q) Hw)).
  assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                    (exists b, mbyte rsegs mem' q = Some b)).
  { intros q Hq Hb.
    destruct (f34_outside_dec [(Sfr fr + 8, Sfr fr + 12); (spv - 2256, spv); (fr + 64, fr + 96)] q) as [Ho|Ho].
    - rewrite f34_mbyte_mrd in *. unfold mrd in *. rewrite (MU (wa q)); [exact Hb|].
      rewrite wa_unsigned by lia. exact Ho.
    - rewrite f34_mbyte_mrd. exact (HIN q Hq Ho). }
  assert (AHSTK : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
                  (forall q, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md q <->
                             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md q) /\
                  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                    = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md
                    = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { destruct Hloc as [[Hs50 [Hspfr Hreal]]|[Hs5fr [Hfsb [Hfs _]]]].
    - assert (Hmc : forall q, 0 <= q < 2 ^ 64 ->
                ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
      { intros q Hq Hns. apply MU. rewrite MState.unsigned_lit by lia.
        cbn [outside]. split; [|split; [|split; [|exact I]]].
        - intros Hc. destruct (Epre q Hc) as (Esh & Erg). apply Hns.
          right. right. right. exists (8 * (q - 2147450880)).
          split; [symmetry; exact Esh|]. right. left. apply Hreal. lia.
        - intros Hc. apply Hns. right. left. unfold APPMEM_END. split; lia.
        - intros Hc. apply Hns. right. left. exact (Hreal q ltac:(lia)). }
      destruct (lw_store (APIf rc) (hb ++ g_H g) mem mem' md HAH Hmc Hwrit) as [HAH' Hown' Hstk' Hhi'].
      split; [exact HAH'|]. split; [exact Hown'|]. split; [exact Hstk' | exact Hhi'].
    - destruct (f34_fs_tp _ _ _ HRT) as (FSw & HFSb).
      apply bytes_at_le8_word in HFSb.
      assert (HFSr : 0 <= bv_unsigned FSw < 2 ^ 64) by apply u64_range.
      assert (HFStp : word_mem rsegs mem (AC.as_tp AC.ASYMS) (bv_unsigned FSw)) by exact HFSb.
      pose proof (Hfsb (bv_unsigned FSw) HFStp HFSr) as HFSfr.
      destruct (lw_fs_place (APIf rc) (hb ++ g_H g) mem md (bv_unsigned FSw) HAH HFStp HFSr)
        as [HFGT HFhi _ HFapp].
      assert (HinFS : forall a0, fr <= a0 < fr + FRAME_BYTES ->
                bv_unsigned FSw <= a0 < bv_unsigned FSw + AC.FS_SIZE).
      { intros a0 Ha0. specialize (Hfs a0 ltac:(lia)). destruct Hfs as (b & Hbr & Hwm & Hb1 & Hb2).
        pose proof (f34_wm_congr mem (AC.as_tp AC.ASYMS) b (bv_unsigned FSw) Hwm HFStp) as Hcong.
        rewrite (Z.mod_small b) in Hcong by lia. rewrite (Z.mod_small (bv_unsigned FSw)) in Hcong by lia.
        subst b. split; lia. }
      assert (Hmeta : forall q, fs_meta (bv_unsigned FSw) q ->
                outside [(Sfr fr + 8, Sfr fr + 12); (spv - 2256, spv); (fr + 64, fr + 96)] q).
      { intros q Hq. pose proof (f34_fs_meta_range _ _ Hq) as Hrange.
        assert (Hqapp : app_mem q) by (apply HFapp; unfold AC.FS_SIZE in *; lia).
        cbn [outside]. split; [apply Hnsh; exact Hqapp|].
        repeat split; try exact I; unfold AC.FS_SIZE in *; lia. }
      assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
                ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                ~ (bv_unsigned FSw <= q < bv_unsigned FSw + AC.FS_SIZE) ->
                ~ (exists b, bv_unsigned FSw <= b < bv_unsigned FSw + AC.FS_SIZE /\ q = shadow_addr b) ->
                mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
      { intros q Hq Hns Hnfs Hnsh2. apply MU. rewrite MState.unsigned_lit by lia.
        cbn [outside]. split; [|split; [|split; [|exact I]]].
        - intros Hc. destruct (Epre q Hc) as (Esh & Erg). apply Hnsh2.
          exists (8 * (q - 2147450880)). split; [apply HinFS; lia | symmetry; exact Esh].
        - intros Hc. apply Hns. right. left. unfold APPMEM_END. split; lia.
        - intros Hc. apply Hnfs. apply HinFS. lia. }
      destruct (a_fs_ok_store_AH AC.ASYMS (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
                  (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc))
                  (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
                  [(Sfr fr + 8, Sfr fr + 12); (spv - 2256, spv); (fr + 64, fr + 96)]
                  (hb ++ g_H g) mem mem' md (bv_unsigned FSw) LAWS HAH HFStp HFSr
                  ltac:(unfold AC.FS_SIZE in *; lia) MU Hwrit Hpres Hmeta Hagree) as (HAH' & Hown' & Hstk' & Hhi').
      split; [exact HAH'|]. split; [exact Hown'|]. split; [exact Hstk' | exact Hhi']. }
  destruct AHSTK as (HAH' & Hown' & HSTK & HSTKHI).
  assert (HFRA' : FRA B APIf ra g fr hb regs' mem' md).
  {
  exists Asp, spv, s5.
  split; [exact HRT'|].
  split; [exact HAH'|].
  split; [exact HRO|].
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo;
          [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo;
          [lia | rewrite Hlock in Hx; cbn in Hx; lia].
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold AC.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|].
  split; [exact Hs5|].
  split; [exact HAm|].
  split; [exact HAS|].
  split; [exact Hspa|].
  split; [exact Hfa|].
  split; [exact HA448|].
  split; [exact HS4|].
  split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. apply HWA. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. apply HWA. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr40 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWA. lia. }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split; [|split].
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
        exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
        intros k Hk. rewrite KBlo.
        * exact (Hw k Hk).
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
        * unfold AC.as_tp, AC.ASYMS. cbn. lia.
      + eapply fsrec_keep_app_lo with (W := [(Sfr fr + 8, Sfr fr + 12); (spv - 2256, spv); (fr + 64, fr + 96)]);
          [exact Hrec | exact HAH | exact MU |].
        intros x Hxapp Hxlo Hxfr. cbn [outside].
        split; [apply Hnsh; exact Hxapp|]. split; [lia|]. split; [lia | exact I]. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWfr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWfr. lia. }
  split.
  { assert (HSTKsh : stk rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW)).
    { split; [lia|]. split; [lia|]. intros a Ha. exact (HSW' a (HshIS a Ha)). }
    destruct (stk_bytes rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW) HSTKsh ltac:(lia)) as (sh' & Hl' & Hb').
    exists sh'. split; [exact Hb'|]. rewrite Hl'.
    replace (Sfr fr + FRAME_SHADOW - Sfr fr) with FRAME_SHADOW by lia. reflexivity. }
  split; [exact HWIN|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsv. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn [length] in Hx. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split.
  { intros a Ha. pose proof (f34_ag_lo a Ha) as Hab.
    apply (f34_addr_keep mem mem' a 1 (HAG a Ha)). intros b Hb. unfold mrd.
    rewrite (MU (wa (shadow_addr b))); [reflexivity|].
    assert (Hbapp : app_mem b).
    { pose proof (f34_addr_app mem a 1 (b - a) (HAG a Ha) ltac:(lia)) as Hp.
      replace (a + (b - a)) with b in Hp by lia. exact Hp. }
    assert (Hinsh : in_shadow (shadow_addr b)) by (apply shadow_of_app; exact Hbapp).
    rewrite wa_unsigned by (pose proof (in_shadow_range _ Hinsh); lia).
    cbn [outside]. split; [|split; [|split; [|exact I]]].
    - unfold shadow_addr, Sfr, shadow_addr in *. revert Hab Hb HGT Efr8. Z.div_mod_to_equations. lia.
    - intros Hc. apply (app_not_shadow (shadow_addr b)); [|exact Hinsh].
      unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia.
    - intros Hc. apply (app_not_shadow (shadow_addr b)); [apply Happ; lia|]. exact Hinsh. }
  split.
  { intros a H1 H2. pose proof (Hwout a H1 H2) as Ha1.
    apply (f34_addr_keep mem mem' a 1 Ha1). intros b Hb. unfold mrd.
    rewrite (MU (wa (shadow_addr b))); [reflexivity|].
    assert (Hbapp : app_mem b).
    { pose proof (f34_addr_app mem a 1 (b - a) Ha1 ltac:(lia)) as Hp.
      replace (a + (b - a)) with b in Hp by lia. exact Hp. }
    assert (Hinsh : in_shadow (shadow_addr b)) by (apply shadow_of_app; exact Hbapp).
    rewrite wa_unsigned by (pose proof (in_shadow_range _ Hinsh); lia).
    cbn [outside]. split; [|split; [|split; [|exact I]]].
    - unfold shadow_addr, Sfr, shadow_addr in *. revert Hb H2 Efr8. Z.div_mod_to_equations. lia.
    - intros Hc. apply (app_not_shadow (shadow_addr b)); [|exact Hinsh].
      unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia.
    - intros Hc. apply (app_not_shadow (shadow_addr b)); [apply Happ; lia|]. exact Hinsh. }
  split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|].
  (* the input block: app memory below stklo (so below the callee window, which is above S - 4096) and apart
     from the frame (fra_in_apart); its shadow bytes are outside the frame's shadow (fr mod 32 = 0) *)
  apply (fra_in_keep_sh g mem mem' [(Sfr fr + 8, Sfr fr + 12); (spv - 2256, spv); (fr + 64, fr + 96)]
           Hinb Hinblk MU).
  intros x Hx. destruct (Hinap x Hx) as (Hxa & Hxlo & Hxf & _).
  assert (Hxlo' : x < g_S g - 1048576) by (eapply Z.lt_le_trans; [exact Hxlo | exact Hstklo]).
  assert (Hinsh : in_shadow (shadow_addr x)) by (apply shadow_of_app; exact Hxa).
  split.
  - cbn [outside]. split; [apply Hnsh; exact Hxa|]. split; [lia|]. split; [lia | exact I].
  - cbn [outside]. split; [|split; [|split; [|exact I]]].
    + intros Hb. apply Hxf. rewrite FRAME_BYTES_val. unfold Sfr, shadow_addr in Hb.
      revert Hb Efr8. clear. intros. Z.div_mod_to_equations. lia.
    + intros Hc. apply (app_not_shadow (shadow_addr x)); [|exact Hinsh].
      unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia.
    + intros Hc. apply (app_not_shadow (shadow_addr x)); [apply Happ; lia|]. exact Hinsh. }
  split; [exact HFRA'|].
  eapply ent_store with (W := [(Sfr fr + 8, Sfr fr + 12); (spv - 2256, spv); (fr + 64, fr + 96)])
    (fr := fr) (regs := regs);
    [exact HENT | exact HFRA0 | exact MU | | exact HSTK | exact HSTKHI
    | intros a Hia Ho; exact (proj2 (Hown' a) Ho)].
  intros x Hx. unfold AF.SLOT_STACK.
  destruct (Z_le_dec (Sfr fr + 8) x); destruct (Z_lt_dec x (Sfr fr + 12));
  destruct (Z_le_dec (spv - 2256) x); destruct (Z_lt_dec x spv);
  destruct (Z_le_dec (fr + 64) x); destruct (Z_lt_dec x (fr + 96));
  first [ right; right; right; lia | right; left; lia | right; right; left; lia
        | left; cbn [outside]; repeat split; try exact I; lia ].
Qed.

(* ===================== the segment lemma ===================== *)

(* Entry SlotInv.Inv_B82bf4_at at row i, exit SlotInv.Inv_B82c24_at at row i (forms-asan-ubsan S_F34). *)
Lemma seg_F34 : forall j i : nat, Hat2 B APIf ra (Inv_B82c24_at B APIf ra) j i ->
  Hat2 B APIf ra (Inv_B82bf4_at B APIf ra) j i.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros j i Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HLK & H22e & H24e &
    Hs272 & _ & HRL & HFT & HIFS).
  subst c. rewrite SEGS.
  pose proof HRL as (Hi10 & H23 & H25 & H21 & H10 & H11 & H12 & Hprev & HPT).
  pose proof HPT as (Hsel & H18 & H20 & Hs152 & Hs312 & Hphi & Hplen & Hs160 & Hcnt & Hfstk).
  pose proof HLK as (Hj255 & Hs240 & HOUR & HFLI).
  (* the row path has len >= 50 (kind 9), so the cut's block (Phi, a_size len) is (Phi, len) *)
  assert (Hlen50 : 50 <= flen g j) by (unfold flen; exact (f34_rowsel_len (g_in g) j Hsel)).
  assert (Esz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
  rewrite Esz in HFRA, HENT.
  destruct (fra_app B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (HGT & Hfapp).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel5 & Hfr40 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & Hwout &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (flen g j) ++ g_H g) mem md HAH) as Hstkhi.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW.
  destruct (fra_frame B APIf ra g fr (hb1 phi (flen g j)) regs mem md HFRA) as (Hdisj & _ & _ & _).
  (* ---- bounds ---- *)
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (EAPP : APPMEM_END = 140737488355328) by reflexivity.
  assert (EHMB : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (EGT : AC.GT = 6283264) by reflexivity.
  assert (EKK : ASAN_K = 2147450880) by reflexivity.
  assert (ERTH : RT_HI = 697272) by reflexivity.
  assert (ECAT : CAT = 652832) by reflexivity.
  assert (ECATR : CAT_ROW = 296) by reflexivity.
  assert (HAb : 0 <= A < 2 ^ 64) by (unfold stk in Hwin; destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (Hsp0 : 0 <= sp) by (unfold AC.aspZ in Haspz; rewrite <- Haspz; apply bv_unsigned_in_range).
  assert (Hfrb : fr + FRAME_BYTES <= APPMEM_END).
  { assert (Ha : app_mem (fr + FRAME_BYTES - 1)) by (apply Hfapp; lia).
    unfold app_mem, LOWMEM_END, APPMEM_END, HIGHMEM_BEG in Ha |- *. destruct Ha; lia. }
  assert (Hfr0 : 0 <= fr) by (unfold AC.GT in HGT; lia).
  assert (HspE : sp <= APPMEM_END) by lia.
  assert (Hsphi : HIGHMEM_BEG + 4096 <= sp) by (unfold AF.SLOT_STACK, HIGHMEM_BEG in *; lia).
  assert (Hdw : fr + FRAME_BYTES <= sp - 2256 \/ sp <= fr).
  { destruct (Hdisj 2256 ltac:(unfold FN_STACK, AF.SLOT_STACK; lia)) as [HD|HD];
      [left | right]; rewrite Haspz in HD; lia. }
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; Z.div_mod_to_equations; lia).
  assert (Efr8 : 8 * (fr / 8) = fr) by (revert Hfr8; Z.div_mod_to_equations; lia).
  (* ---- the frame's shadow ---- *)
  assert (HshIS : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + FRAME_BYTES) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Hfapp _ Hin)) as His.
    replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
    unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
  assert (HSlo : 2148236288 <= Sfr fr)
    by (unfold Sfr, shadow_addr, ASAN_K, AC.GT in *; Z.div_mod_to_equations; lia).
  assert (HShi : Sfr fr + 12 <= HIGHMEM_BEG).
  { pose proof (HshIS (Sfr fr + 11) ltac:(lia)) as Hin11.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hin11 |- *. lia. }
  assert (Hshw : forall k, 0 <= k < 4 -> wview rsegs mem (wa (Sfr fr + 8 + k)) <> None)
    by (intros k Hk; exact (proj1 (HSW _ (HshIS (Sfr fr + 8 + k) ltac:(lia))))).
  assert (Hslotsh : forall k, 0 <= k < 32 -> Sfr fr + 8 <= shadow_addr (fr + 64 + k) < Sfr fr + 12).
  { intros k Hk. unfold Sfr, shadow_addr. revert Efr8 Hk. Z.div_mod_to_equations. lia. }
  (* ---- the catalogue row of this turn ---- *)
  destruct (f34_row i ltac:(lia)) as (Himg & Hok & Hrlen).
  assert (Hrb : 0 <= CAT + CAT_ROW * Z.of_nat i /\ CAT + CAT_ROW * Z.of_nat i + 296 <= 656088)
    by (unfold CAT, CAT_ROW; lia).
  assert (Hrow : bytes_at rsegs mem (CAT + CAT_ROW * Z.of_nat i) (rowb (Z.of_nat i))).
  { split; [lia|]. split; [rewrite Hrlen; lia|].
    intros k Hk. rewrite Hrlen in Hk.
    assert (Hin : in_globals AF.frame_RELRO (CAT + CAT_ROW * Z.of_nat i + Z.of_nat k)).
    { exists 0x9f168, 9344. split; [exact f34_cat_RELRO|]. unfold CAT, CAT_ROW in *. lia. }
    pose proof (Hgimg (CAT + CAT_ROW * Z.of_nat i + Z.of_nat k) Hin) as Hg. rewrite SEGS in Hg.
    transitivity (seg_rom rsegs (Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat i + Z.of_nat k))); [exact Hg|].
    exact (f34_img_nth 296 (CAT + CAT_ROW * Z.of_nat i) (rowb (Z.of_nat i)) k Himg ltac:(lia)). }
  assert (Hraddr : addressable mem (CAT + CAT_ROW * Z.of_nat i) 296).
  { apply f34_addr_of_bytes; [lia | lia | unfold APPMEM_END, CAT, CAT_ROW in *; lia |].
    intros a Ha. apply HAG. exists 0x9f620, 3256.
    split; [exact f34_cat_AG|]. unfold CAT, CAT_ROW in *. lia. }
  (* ---- the row slot ---- *)
  assert (Hslotstk : stk rsegs mem (fr + 64) (fr + 96))
    by (apply (f34_sub_stk mem fr (fr + FRAME_BYTES)); [exact Hfstk | lia | lia | lia]).
  destruct (f34_rw_of_stk mem (fr + 64) (fr + 96) Hslotstk ltac:(lia)) as (ob & Hoblen & Hob).
  assert (Q152 : q64 mem (A + 152) (fr + 64))
    by (apply (f34_spill regs mem 152 (fr + 64) A Hs152 Hr9); lia).
  destruct (stk_split rsegs mem (g_S g - AF.SLOT_STACK) sp (g_S g) Hwin ltac:(lia)) as (HSlo2 & HShi2).
  (* ---- the run ---- *)
  apply (f34_run_lib regs (Z_to_bv 64 0x82bf4) mem md
    (fun R0 pc' mem' => pc' = Z_to_bv 64 0x82c24 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 20 = getr regs 20 /\ getr R0 25 = getr regs 25 /\ getr R0 26 = getr regs 26 /\
       getr R0 27 = getr regs 27 /\
       getr R0 19 = Z_to_bv 64 (Sfr fr) /\ getr R0 21 = Z_to_bv 64 CAT /\
       getr R0 22 = Z_to_bv 64 (fr + 64) /\
       getr R0 23 = Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat i) /\
       getr R0 24 = Z_to_bv 64 (CAT_ROW * Z.of_nat i + CAT) /\ getr R0 10 = Z_to_bv 64 1 /\
       munch [(Sfr fr + 8, Sfr fr + 12); (AC.aspZ regs - 2256, AC.aspZ regs); (fr + 64, fr + 96)] mem mem' /\
       wmono rsegs mem mem' /\ ro_agree rsegs mem' /\ shadow_rw mem' /\
       stk rsegs mem' (g_S g - AF.SLOT_STACK) (AC.aspZ regs) /\
       bytes_at rsegs mem' (fr + 64) (decl (rowb (Z.of_nat i))) /\ addressable mem' (fr + 64) 32 /\
       (forall q, 0 <= q < 2 ^ 64 ->
          ~ outside [(Sfr fr + 8, Sfr fr + 12); (AC.aspZ regs - 2256, AC.aspZ regs); (fr + 64, fr + 96)] q ->
          exists b, mrd rsegs mem' (wa q) = Some b))
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold Regs6ss.mkR_of.
    eapply LE.evt_mono.
    { eapply (f34_evt_ro DECL) with (S := Sfr fr) (A := A) (T := CAT) (o := CAT_ROW * Z.of_nat i)
        (ost := fr + 64) (spv := sp) (lo := g_S g - AF.SLOT_STACK) (row := rowb (Z.of_nat i)) (ob := ob).
      - exact Hr2.
      - unfold rg in Hr9. exact Hr9.
      - unfold rg in Hr19. exact Hr19.
      - unfold rg in H10. exact H10.
      - unfold rg in H11. exact H11.
      - unfold rg in H12. exact H12.
      - unfold rg in H21. exact H21.
      - unfold rg in H23. exact H23.
      - exact HSlo.
      - exact HShi.
      - exact Hshw.
      - intros k Hk. apply HshIS. lia.
      - lia.
      - unfold APPMEM_END in *. lia.
      - intros k Hk. apply Hfapp. lia.
      - apply Hfapp. lia.
      - exact Hslotsh.
      - exact Hob.
      - exact Hoblen.
      - unfold q64 in Q152. exact Q152.
      - unfold HIGHMEM_BEG, AF.SLOT_STACK in *. lia.
      - lia.
      - unfold CAT_ROW. lia.
      - unfold CAT. lia.
      - unfold CAT, CAT_ROW in *. lia.
      - unfold CAT, CAT_ROW. Z.div_mod_to_equations. lia.
      - exact Hrlen.
      - exact Hok.
      - exact Hrow.
      - exact Hraddr.
      - exact HSlo2.
      - unfold AF.SLOT_STACK, HIGHMEM_BEG in *. lia.
      - unfold AF.SLOT_STACK in *. lia.
      - exact HspE.
      - destruct Hdw as [HD|HD]; [left; lia | right; lia].
      - lia.
      - exact Hro.
      - exact (AsanRTInv.RT_cells _ _ _ HRT).
      - exact HSW. }
    { intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
                  E2m & MU2 & WM2 & RO2 & SW2 & ST2 & BA2 & AD2 & IN2).
      replace (fr + 64 + 32) with (fr + 96) in MU2, IN2 by lia.
      eexists _, (Z_to_bv 64 0x82c24), m2. split; [exact E2m|].
      do 17 (split; [reflexivity|]).
      split; [rewrite Haspz; exact MU2|]. split; [exact WM2|]. split; [exact RO2|]. split; [exact SW2|].
      split; [rewrite Haspz; exact ST2|]. split; [exact BA2|]. split; [exact AD2|].
      rewrite Haspz. exact IN2. }
  - intros R0 pc' mem' regs' md'
      (Hpc & E2 & E3 & E4 & E8 & E9 & E18 & E20 & E25 & E26 & E27 & E19 & E21 & E22 & E23 & E24 & E10 &
       MU & WM & HroM & SW' & ST' & BA' & AD' & HIN) Hreg Hmat.
    subst pc'.
    assert (F2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (F3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (F4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (F8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (F9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (F18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact E18).
    assert (F20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact E20).
    assert (F25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact E25).
    assert (F26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    assert (F27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact E27).
    assert (F19 : getr regs' 19 = getr regs 19) by (rewrite Hreg, E19; unfold rg in Hr19; symmetry; exact Hr19).
    assert (F21 : getr regs' 21 = Z_to_bv 64 CAT) by (rewrite Hreg; exact E21).
    assert (F22 : getr regs' 22 = Z_to_bv 64 (fr + 64)) by (rewrite Hreg; exact E22).
    assert (F23 : getr regs' 23 = Z_to_bv 64 (CAT + CAT_ROW * Z.of_nat i)) by (rewrite Hreg; exact E23).
    assert (F24 : getr regs' 24 = Z_to_bv 64 (CAT_ROW * Z.of_nat i + CAT)) by (rewrite Hreg; exact E24).
    assert (F10 : getr regs' 10 = Z_to_bv 64 1) by (rewrite Hreg; exact E10).
    assert (Hasp' : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite F2; reflexivity).
    (* the window on the entry-anchored stack: below sp from the callee, above sp untouched or readable *)
    assert (HWIN' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
    { assert (Hhi' : stk rsegs mem' sp (g_S g)).
      { destruct HShi2 as (S0 & S1 & SS). split; [exact S0|]. split; [exact S1|].
        intros a Ha. split.
        - apply WM. exact (proj1 (SS a Ha)).
        - destruct (f34_outside_dec
              [(Sfr fr + 8, Sfr fr + 12); (AC.aspZ regs - 2256, AC.aspZ regs); (fr + 64, fr + 96)] a)
            as [Ho|Ho].
          + destruct (SS a Ha) as (_ & b & Hb). exists b. unfold mrd in *.
            rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
          + apply (HIN a ltac:(lia) Ho). }
      assert (Hlo' : stk rsegs mem' (g_S g - AF.SLOT_STACK) sp) by (rewrite <- Haspz; exact ST').
      exact (Frame.stk_merge rsegs mem' (g_S g - AF.SLOT_STACK) sp (g_S g) Hlo' Hhi' ltac:(lia)). }
    assert (HFE : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md /\
                  ENT APIf g (hb1 phi (flen g j)) mem' md).
    { eapply (f34_fra_w g fr (hb1 phi (flen g j)) regs regs' mem mem' md A sp).
      - exact HFRA.
      - exact HENT.
      - unfold rg in Hr9. exact Hr9.
      - exact Haspz.
      - exact Hfa.
      - lia.
      - exact HGT.
      - exact Hfapp.
      - exact Hsphi.
      - exact Hspa.
      - exact HspE.
      - exact Hdw.
      - rewrite <- Haspz. exact MU.
      - exact WM.
      - exact HroM.
      - exact SW'.
      - rewrite <- Haspz. exact HIN.
      - exact HWIN'.
      - exact F2.
      - exact F3.
      - exact F4.
      - exact F8.
      - exact F9.
      - exact F19.
      - exact F26. }
    destruct HFE as (HFRA' & HENT').
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (flen g j)) regs' mem' md')
      by (apply (sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs' regs' mem' md md' HFRA');
          try reflexivity; exact Hmat).
    assert (HENT'' : ENT APIf g (hb1 phi (flen g j)) mem' md') by (eapply ent_mat; [exact HENT' | exact Hmat]).
    (* the cut's memory facts on mem' *)
    assert (Kout : forall x, fr + 96 <= x < fr + FRAME_BYTES -> outside
              [(Sfr fr + 8, Sfr fr + 12); (AC.aspZ regs - 2256, AC.aspZ regs); (fr + 64, fr + 96)] x).
    { intros x Hx. cbn [outside]. rewrite Haspz.
      split; [intros Hc; apply (app_not_shadow x (Hfapp x ltac:(lia))); apply HshIS; lia|].
      repeat split; try exact I; lia. }
    assert (KA : forall x, A <= x < A + 344 -> outside
              [(Sfr fr + 8, Sfr fr + 12); (AC.aspZ regs - 2256, AC.aspZ regs); (fr + 64, fr + 96)] x).
    { intros x Hx. cbn [outside]. rewrite Haspz. repeat split; try exact I; lia. }
    assert (Hspl : forall off v, 0 <= off <= 336 -> spill regs mem off v -> spill regs' mem' off v).
    { intros off v Hoff Hsp. exists A. split; [unfold rg in *; rewrite F9; exact Hr9|].
      pose proof (f34_spill regs mem off v A Hsp Hr9 ltac:(lia) ltac:(lia) ltac:(lia)) as Hq.
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
      rewrite length_le8. intros x Hx. apply KA. lia. }
    assert (Hfr32 : q64 mem' (fr + 32) 11).
    { unfold q64 in *. eapply fl_bytes; [exact Hcnt | exact MU |].
      rewrite length_le8. intros x Hx. cbn [outside]. rewrite Haspz.
      split; [intros Hc; apply (app_not_shadow x (Hfapp x ltac:(lia))); apply HshIS; lia|].
      repeat split; try exact I; lia. }
    assert (HOUR' : OURb g fr mem').
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |].
      rewrite OUR_length. intros x Hx. apply Kout. lia. }
    assert (Hfstk' : stk rsegs mem' fr (fr + FRAME_BYTES)).
    { destruct Hfstk as (S0 & S1 & SS). split; [exact S0|]. split; [exact S1|].
      intros a Ha. split.
      - apply WM. exact (proj1 (SS a Ha)).
      - destruct (f34_outside_dec
            [(Sfr fr + 8, Sfr fr + 12); (AC.aspZ regs - 2256, AC.aspZ regs); (fr + 64, fr + 96)] a)
          as [Ho|Ho].
        + destruct (SS a Ha) as (_ & b & Hb). exists b. unfold mrd in *.
          rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
        + apply (HIN a ltac:(lia) Ho). }
    (* the heap block: apart from the frame, so its shadow bytes are untouched *)
    assert (Hblk : phi + AC.a_size (flen g j) <= fr \/ fr + FRAME_BYTES <= phi).
    { pose proof (f34_blocks (hb1 phi (flen g j) ++ g_H g) mem md phi (flen g j) HAH
                    ltac:(apply in_or_app; left; unfold hb1; left; reflexivity)) as (Hle & Hby).
      destruct Hloc as [[_ [Hspfr Hreal]]|[_ [_ [Hfs _]]]].
      - left. pose proof (Hreal fr ltac:(lia)) as Hrr. unfold AC.a_size in *. lia.
      - destruct (Z_le_dec (phi + AC.a_size (flen g j)) fr) as [HD|HD]; [left; exact HD|].
        destruct (Z_le_dec (fr + FRAME_BYTES) phi) as [HD2|HD2]; [right; exact HD2|].
        exfalso.
        destruct (Hby (Z.max phi fr) ltac:(unfold AC.a_size in *; lia)) as (_ & Hnfs).
        exact (Hnfs (Hfs (Z.max phi fr) ltac:(unfold AC.a_size in *; lia))). }
    assert (Kaddr : forall p n, addressable mem p n -> (p + n <= fr + 64 \/ fr + 96 <= p) ->
                      addressable mem' p n).
    { intros p n HA Hd. apply (f34_addr_keep mem mem' p n HA).
      intros a Ha.
      assert (Happa : app_mem a).
      { pose proof (f34_addr_app mem p n (a - p) HA ltac:(lia)) as Hap.
        replace (p + (a - p)) with a in Hap by lia. exact Hap. }
      unfold mrd. rewrite (MU (wa (shadow_addr a))); [reflexivity|].
      rewrite wa_unsigned by (pose proof (in_shadow_range _ (shadow_of_app a Happa)); lia).
      cbn [outside]. rewrite Haspz. split; [|split; [|split; [|exact I]]].
      - unfold shadow_addr, Sfr, shadow_addr in *. revert Hd Ha Efr8. Z.div_mod_to_equations. lia.
      - intros Hc. apply (app_not_shadow (shadow_addr a)); [|apply shadow_of_app; exact Happa].
        unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia.
      - intros Hc. apply (app_not_shadow (shadow_addr a)); [apply Hfapp; lia|].
        apply shadow_of_app. exact Happa. }
    (* `first` [fr + 2880, fr + 2920) (FLI's RAD, third range) is above the slot, so it stays addressable *)
    assert (Hfst' : addressable mem' (fr + 2880) 40).
    { pose proof (Tac_ro.fli_mem _ _ _ _ HFLI) as (_ & _ & _ & _ & _ & Ffst).
      apply Kaddr; [exact Ffst | lia]. }
    assert (HHB' : HB mem' phi (flen g j)).
    { destruct HHB as (Hne & Had). split; [exact Hne|]. apply Kaddr; [exact Had | lia]. }
    assert (Hphi' : bytes_at rsegs mem' phi (t_phi (g_in g) j)).
    { pose proof (f34_blocks (hb1 phi (flen g j) ++ g_H g) mem md phi (flen g j) HAH
                    ltac:(apply in_or_app; left; unfold hb1; left; reflexivity)) as (Hle & Hby).
      eapply fl_bytes; [exact Hphi | exact MU |]. intros x Hx.
      assert (Hxapp : app_mem x) by (exact (proj1 (Hby x ltac:(unfold flen in *; lia)))).
      cbn [outside]. rewrite Haspz.
      split; [intros Hc; apply (app_not_shadow x Hxapp); apply HshIS; lia|].
      repeat split; try exact I; unfold AC.a_size, flen in *; lia. }
    (* ---- the exit cut ---- *)
    assert (HIexit : Inv_B82c24_at B APIf ra g j i
                       (mkCfg (mkst regs' (Z_to_bv 64 0x82c24) mem' (seg_rom rsegs)) md')).
    { exists phi, regs', mem', md', fr. rewrite SEGS, Esz. split; [reflexivity|].
      split; [exact HFRA''|].
      split; [exact HENT''|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB'|].
      split; [unfold rg in H18 |- *; rewrite F18; exact H18|].
      split; [unfold flen; unfold rg in H20 |- *; rewrite F20; exact H20|].
      split.
      { destruct HFT as (HF224 & HF232 & _ & _).
        split; [apply Hspl; [lia | exact HF224]|]. split; [apply Hspl; [lia | exact HF232]|].
        split; [exact Hphi' | exact Hplen]. }
      split.
      { pose proof (Tac_ro.fli_mem _ _ _ _ HFLI) as (Fad & _ & Frad & Ffrg & (Fkb & Fka) & _).
        eapply Tac_ro.lk_keep; [exact HLK | | | | | | | exact Hfst' | exact HOUR' | exact Hspl].
        - unfold rg in *. rewrite F27. exact (proj1 HFLI).
        - apply Kaddr; [exact Fad | lia].
        - exact Hfstk'.
        - apply Kaddr; [exact Frad | lia].
        - apply Kaddr; [exact Ffrg | unfold fragb; lia].
        - (* the kind-name table (image data below GT): apart from the frame's shadow, the callee's window and
             the slot *)
          assert (HL : length KNC.kind_name_bytes = 112%nat) by reflexivity.
          unfold KNT. split.
          + eapply fl_bytes; [exact Fkb | exact MU |].
            rewrite HL. intros x Hx. unfold KNC.KIND_NAME in Hx. cbn [outside]. rewrite Haspz.
            split; [intros Hc; apply (app_not_shadow x); [unfold app_mem, LOWMEM_END; left; lia
                                                         | apply HshIS; lia]|].
            repeat split; try exact I; clear - Hx HGT Hsphi; unfold AC.GT, HIGHMEM_BEG in *; lia.
          + apply Kaddr; [exact Fka | left; clear - HGT; unfold KNC.KIND_NAME, AC.GT in *; lia]. }
      split; [exact Hi10|].
      split; [apply Hspl; [lia | exact Hs272]|].
      split; [exact I|].
      split.
      { split; [exact Hi10|].
        split; [unfold rg; exact F23|].
        split; [unfold rg; rewrite F24; f_equal; lia|].
        split; [unfold rg in *; rewrite F25; exact H25|].
        split; [unfold rg; exact F21|].
        split; [unfold rg; exact F22|].
        split; [exact Hprev|].
        split; [exact Hsel|].
        split; [unfold rg in *; rewrite F18; exact H18|].
        split; [unfold rg in *; rewrite F20; exact H20|].
        split; [apply Hspl; [lia | exact Hs152]|].
        split; [apply Hspl; [lia | exact Hs312]|].
        split; [exact Hphi'|]. split; [exact Hplen|].
        split; [apply Hspl; [lia | exact Hs160]|].
        split; [exact Hfr32|].
        exact Hfstk'. }
      split; [unfold rg; exact F10|].
      split; [unfold decl_i; exact BA'|].
      split; [exact AD'|].
      apply (f34_IFS_keep g fr (S j) regs regs' mem mem' _ HIFS MU);
        [intros x Hx; apply Kout; lia | exact Hfst']. }
    pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End F34.
