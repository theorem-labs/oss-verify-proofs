(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 2962 of its 3089 lines of code are new or changed and 884 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F36.v, with its module names, addresses and numbers changed; 796 of its 1156 lines of code are new or changed and 2729 lines of the source are left out. *)
(* Segment F37 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): 0x828d8-0x8293c (plan-asan section 2 row F37,
   call FREE@0x8293c = the free wrapper, by aa_free of the AsanAllocAPI of frame_facts; ubsan twin C05).
   rule 24: no function proved.

   One entry (0x828d8) and one exit (0x82940):
     0x828d8  bne a0,s4,82bf4   -- a0 is the catalogue match's result of F36 (t_want), s4 the expected value
                                  (t_want_m).  The two agree (f37_want_eq, claim C4.12), so the branch to the
                                  abort block 0x82bf4 is not taken.
     0x828dc .. 0x82934         -- 23 one-byte stores `sb s11,o(s3)` with s3 = S(fr), o in [22, 67): the shadow
                                  bytes of the frame words [fr + 176, fr + 536) take the value in s11.  They
                                  change no byte outside [S(fr) + 22, S(fr) + 67).
     0x82938  mv a0,s7          -- the argument: s7 = Phi, the input copy of this turn.
     0x8293c  jal 53378         -- the free wrapper at as_free ASYMS = 0x53378, through aa_free's contract with
                                  ra = 0x82940.  Its premise is a_call_pre at AK_FREE (4096 <= FN_STACK), which
                                  SlotInv's fra_call_pre reads off FRA and ENT, plus a0 = Phi; the block it
                                  takes is the head (Phi, a_size (flen g j)) of the cut's heap list, so the post
                                  heap is the entry heap and the exit cut's list is [].  Generation N.1's two class
                                  premises over the bound Bc come from Seg/Tac_cls.v's sl_free_cls (f37_free).

   Cuts: both are SlotInv.v's official bodies (push 6c, kept through push 14E; v1.9 names and pcs of a Theorem Labs lane's
   bundle on a working branch), so they are F36's exit and F38's
   entry term for term.  The entry Inv_A828d8_at is the frame-loop skeleton (CUTST with the heap list hb1 phi, HB
   and FLSI) with LK, the pass-through bundle FLSX (FLS without the kind register, which the row arm overwrote),
   the two result registers and the hand-on bundle LT.
   The exit Inv_A82940_at carries FLSF (what the free keeps of FLSX: the block's bytes and HB are dropped, the
   block was released) and LT.  The stores and the free write neither the spills (PRO's, FLC's and FLSI's [A+216] /
   [A+224] / [A+248] among them), the harness block of f1_IN, nor the frame records at fr + 2688 / fr + 2768 /
   fr + 2880 that LT = IFS g fr (S j) and FLC name, so FLSI is kept and LT is handed on unchanged.

   v1.9 (libreac v1.9.0): every pc +0xac and the free wrapper 0x53358 -> 0x53378 (b8refit-v190.tsv (a working note, not in this delivery)); the abort
   block 0x82b34 -> 0x82bf4 (+0xc0, not in the map: read off a Theorem Labs lane's v1.9 listing, `828d8: bne a0,s4,82bf4`);
   the frame is FRAME_BYTES = 3136 bytes with FRAME_SHADOW = 392 shadow bytes; PRO gains [A + 32] = fr + 2880 and FLC
   gains [A + 56] / [A + 48] (appended), and FLC's slots are renumbered; FSb takes fr and its positions 3 / 4 are the
   body bytes at fr + 2880 and their 35 addressable bytes; frame_RELRO is the one range (0x9e348, 9344); the image's
   .data / .bss constants move by +0xc0 (errno = as_tp - 164 = 0x5db76c, the out-of-memory flag 0x12aae0, the client
   ranges at 0x5db840 / 0x5fbad8) and the registered globals lie in [0x21140, 0x9f8e8). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm
  AsanLift KindBGlue BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcParse RcIdentModel RcFrag RcMatch
  RcMatchLib RcDecl.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib
  asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs Tac_cls.
Import ListNotations.
(* The plain lib/Prog files also load lib/Reusable/YK11, so the short name YK11 is the plain one here; the slot's
   cuts are stated with the image-A one, which this alias names. *)
Module AYK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Import AYK.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.

(* ===================== pure helpers ===================== *)

(* A one-byte store of a register writes its low byte. *)
Lemma f37_le1_byte : forall v : word, le1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. intros v. unfold le1. cbn [Z_to_le_bytes]. reflexivity. Qed.

Lemma f37_ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (HA & HL & H) Hkj.
  assert (Lf : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Lf; lia|].
  intros i Hi. rewrite Lf in Hi.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  rewrite H by lia. rewrite nth_error_firstn. destruct (Nat.ltb_spec0 i jj) as [_|C]; [|lia].
  rewrite nth_error_skipn. reflexivity.
Qed.

(* n bytes that are all present form a list. *)
Lemma f37_ba_present : forall m n a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> exists b, mrd rsegs m (wa (a + Z.of_nat i)) = Some b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = n.
Proof.
  intros m n. induction n as [|n IH]; intros a Ha Hn H.
  - exists []. split; [|reflexivity]. split; [exact Ha|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi. lia.
  - destruct (H 0%nat ltac:(lia)) as (b0 & Hb0).
    assert (Hrest : forall i, (i < n)%nat -> exists b, mrd rsegs m (wa (a + 1 + Z.of_nat i)) = Some b).
    { intros i Hi. destruct (H (S i) ltac:(lia)) as (b & Hb). exists b.
      replace (a + 1 + Z.of_nat i) with (a + Z.of_nat (S i)) by lia. exact Hb. }
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) Hrest) as (bs & (Ha' & Hl' & Hb') & Hlen).
    exists (b0 :: bs). split; [|cbn [length]; lia].
    split; [exact Ha|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + cbn [nth_error]. exact Hb0.
    + cbn [nth_error]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
      apply Hb'. cbn [length] in Hi. lia.
Qed.

(* A present byte of a list read at its address. *)
Lemma f37_ba_some : forall m a bs i, bytes_at rsegs m a bs -> 0 <= i < Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa (a + i)) = Some b.
Proof.
  intros m a bs i (_ & _ & H) Hi.
  specialize (H (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in H by lia. rewrite H.
  destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [exists b; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

(* bytes_at survives a memory change that keeps each byte of its range. *)
Lemma f37_bkeep : forall (mem mem' : word -> option byte) a bs,
  (forall x, a <= x < a + Z.of_nat (length bs) -> mbyte rsegs mem' x = mbyte rsegs mem x) ->
  bytes_at rsegs mem a bs -> bytes_at rsegs mem' a bs.
Proof.
  intros mem mem' a bs HK (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H i Hi).
  change (mbyte rsegs mem' (a + Z.of_nat i) = mbyte rsegs mem (a + Z.of_nat i)).
  apply HK. lia.
Qed.

Lemma f37_sh_frame_of : forall fr k, 0 <= fr -> fr mod 8 = 0 -> 0 <= k ->
  shadow_addr (fr + 8 * k) = shadow_addr fr + k.
Proof. unfold shadow_addr. intros fr k H0 H8 Hk. Z.div_mod_to_equations. lia. Qed.

Lemma f37_sh_frame : forall fr y k, 0 <= fr -> fr mod 8 = 0 -> 0 <= y -> shadow_addr y = shadow_addr fr + k ->
  fr + 8 * k <= y < fr + 8 * k + 8.
Proof. unfold shadow_addr. intros fr y k H0 H8 Hy E. Z.div_mod_to_equations. lia. Qed.

(* Below an 8-aligned bound, the shadow byte is below the bound's shadow byte. *)
Lemma f37_sh_lt : forall y z, z mod 8 = 0 -> y < z -> shadow_addr y < shadow_addr z.
Proof. intros y z H8 H. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma f37_in_shadow_bnd : forall x, in_shadow x -> LOWMEM_END <= x < HIGHMEM_BEG.
Proof. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG. intros; lia. Qed.

(* addressable survives writes apart from the shadow bytes of its range. *)
Lemma f37_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) MU HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (shadow_of_app (p + i) Hap) as Hs. pose proof (in_shadow_range _ Hs) as Hbd.
  unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. apply HW. exact Hi.
Qed.

(* addressable survives a run that keeps the shadow bytes of its range. *)
Lemma f37_addr_bkeep : forall (m m' : word -> option byte) p n,
  addressable m p n -> (forall i, 0 <= i < n -> mbyte rsegs m' (shadow_addr (p + i)) = mbyte rsegs m (shadow_addr (p + i))) ->
  addressable m' p n.
Proof.
  intros m m' p n (H0 & Hn & He & HA) HK. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  change (mbyte rsegs m' (shadow_addr (p + i)) = Some b). rewrite (HK i Hi). exact Hb.
Qed.

Lemma f37_rg_mod : forall regs r a b, rg regs r a -> rg regs r b -> a mod 2 ^ 64 = b mod 2 ^ 64.
Proof.
  unfold rg. intros regs r a b Ha Hb. rewrite Ha in Hb. apply (f_equal bv_unsigned) in Hb.
  rewrite !Z_to_bv_unsigned in Hb. exact Hb.
Qed.

(* Two in-range values of one register are the same value. *)
Lemma f37_reg_eq : forall (regs : bvmap 5 word) (r : bv 5) a b,
  getr regs r = Z_to_bv 64 a -> getr regs r = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof.
  intros regs r a b Ha Hb Ra Rb.
  assert (E : Z_to_bv 64 a = Z_to_bv 64 b) by congruence.
  apply (f_equal (bv_unsigned (n := 64))) in E. rewrite !unsigned_lit in E by lia. exact E.
Qed.

(* A value of s1 within 416 bytes of the spill base A (both read through rg) is A. *)
Lemma f37_rg_near : forall (regs : bvmap 5 word) (r : bv 5) a b, rg regs r a -> rg regs r b ->
  416 <= a -> a + 416 <= 2 ^ 64 -> -400 <= b -> b + 8 <= 2 ^ 64 -> b = a.
Proof.
  intros regs r a b Ha Hb H1 H2 H3 H4.
  pose proof (f37_rg_mod regs r b a Hb Ha) as E. rewrite (Z.mod_small a) in E by lia.
  pose proof (Z.div_mod b (2 ^ 64) ltac:(lia)) as D. rewrite E in D. lia.
Qed.

(* A readable-and-writable stack window survives a run that keeps every byte of it backed. *)
Lemma f37_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (Hc a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|].
  rewrite wa_unsigned by lia. exact Ho.
Qed.

(* The same, for a run described by kept bytes and kept writability instead of a write set. *)
Lemma f37_stk_keep : forall (m m' : word -> option byte) lo hi, stk rsegs m lo hi ->
  (forall a, lo <= a < hi -> mbyte rsegs m' a = mbyte rsegs m a) ->
  (forall a, lo <= a < hi -> writable_at rsegs m a -> writable_at rsegs m' a) ->
  stk rsegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) HK HW. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (HW a Ha Hw)|].
  exists b. change (mbyte rsegs m' a = Some b). rewrite (HK a Ha). exact Hb.
Qed.

Lemma f37_wm_uniq : forall mem a v1 v2, word_mem rsegs mem a v1 -> word_mem rsegs mem a v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> v1 = v2.
Proof.
  intros mem a v1 v2 H1 H2 R1 R2.
  assert (D : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2. rewrite E1 in E2.
    injection E2 as E2.
    pose proof (kb_byte_unsigned v1 8 k) as K1. pose proof (kb_byte_unsigned v2 8 k) as K2.
    unfold bv_unsigned in K1, K2. rewrite K1, K2 in E2. exact E2. }
  pose proof (kb_le8_digits v1 R1) as G1. pose proof (kb_le8_digits v2 R2) as G2.
  rewrite (D 0%nat ltac:(lia)), (D 1%nat ltac:(lia)), (D 2%nat ltac:(lia)), (D 3%nat ltac:(lia)),
          (D 4%nat ltac:(lia)), (D 5%nat ltac:(lia)), (D 6%nat ltac:(lia)), (D 7%nat ltac:(lia)) in G1.
  lia.
Qed.

(* The side stack's metadata cells lie in its first 36864 bytes. *)
Lemma f37_fs_meta_ge : forall FS q, fs_meta FS q -> FS <= q.
Proof.
  intros FS q H. unfold fs_meta in H.
  destruct H as [H | [H | [[c [Hc Hr]] | [c [jj [Hc [Hj Heq]]]]]]].
  - lia.
  - lia.
  - unfold AC.a_fs_hint in Hr. lia.
  - subst q. pose proof (a_fs_flag_range FS c jj Hc Hj). lia.
Qed.

(* Every segment of the image ends below LOWMEM_END, so a read-only address is below it. *)
Local Definition f37_tops (segs : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) segs.

Local Lemma f37_rsegs_low : f37_tops rsegs LOWMEM_END = true.
Proof. vm_compute. reflexivity. Qed.

Local Lemma f37_find_below : forall segs top x n s,
  f37_tops segs top = true -> find_segment segs x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction segs as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold f37_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

Lemma f37_ro_lo : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < LOWMEM_END.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  destruct (f37_find_below rsegs LOWMEM_END (bv_unsigned a) 1 s f37_rsegs_low E ltac:(lia)) as [L|L];
    [exact L | discriminate L].
Qed.

(* A range of image bytes, found by computation over the image's segments. *)
Lemma f37_img_seg : forall lo hi,
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs
    = true ->
  forall a, lo <= a < hi -> AC.a_in_img a.
Proof.
  intros lo hi H a Ha. apply existsb_exists in H as (s & Hin & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hin | lia].
Qed.

(* errno [0x5db76c, 0x5db770) (as_tp - 164, v1.9 tp 0x5db810) and the runtime's out-of-memory flag 0x12aae0 are image
   bytes. *)
Lemma f37_errno_img : forall a, 0x5db76c <= a < 0x5db770 -> AC.a_in_img a.
Proof. apply f37_img_seg. vm_compute. reflexivity. Qed.

Lemma f37_oom_img : AC.a_in_img 0x12aae0.
Proof. apply (f37_img_seg 0x12aae0 0x12aae1); [vm_compute; reflexivity | lia]. Qed.

(* The registered globals of frame_AG lie in the image's segments and in [0x21140, 0x9f8e8). *)
Lemma f37_ag_img : forall a, in_globals AF.frame_AG a -> AC.a_in_img a.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (Hall : forallb (fun p => existsb (fun s => (Z.of_N (seg_base s) <=? fst p) &&
                   (fst p + snd p <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall _ Hin). apply existsb_exists in Hall as (s & Hs & Hb).
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2.
  exists s. split; [exact Hs | lia].
Qed.

Lemma f37_ag_range : forall a, in_globals AF.frame_AG a -> 0x21140 <= a < 0x9f8e8.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (Hall : forallb (fun p => (0x21140 <=? fst p) && (fst p + snd p <=? 0x9f8e8)) AF.frame_AG = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall _ Hin).
  apply andb_true_iff in Hall as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [fst snd] in H1, H2. lia.
Qed.

Lemma f37_eqb_lit : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

(* A branch arm the facts in context exclude. *)
Ltac f37_bad HC :=
  exfalso;
  first [ congruence
        | discriminate HC
        | (rewrite ?f37_eqb_lit in HC by lia; cbn [negb] in HC;
           first [ (apply Bool.negb_true_iff in HC; apply Z.eqb_neq in HC; lia)
                 | (apply Bool.negb_false_iff in HC; apply Z.eqb_eq in HC; lia)
                 | (apply Z.eqb_eq in HC; lia) | (apply Z.eqb_neq in HC; lia) ])
        | (unfold bv_eqb in HC; rewrite Z.eqb_refl in HC; cbn [negb] in HC; discriminate HC)
        | (vm_compute in HC; discriminate HC) ].
Ltac f37_nt := let H := fresh "HC" in first [ if_cases H; [f37_bad H | clear H] | idtac ].

(* ===================== the model fact the branch reads (C4.12) ===================== *)

Lemma f37_bytes_inj : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma f37_lbytes_inj : forall l1 l2 : list (list byte), map (map bv_unsigned) l1 = map (map bv_unsigned) l2 ->
  l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply f37_bytes_inj; exact H1 | apply IH; exact H2].
Qed.

(* The eleven declaration strings of the match table are the eleven rows of the image's catalogue at 0x9e800. *)
Lemma f37_DECLS : DECLS = map (fun i => decl_i (Z.of_nat i)) (seq 0 11).
Proof. apply f37_lbytes_inj. vm_compute. reflexivity. Qed.

Lemma f37_cm_find_rob : forall blk n k,
  match cm_find blk (map (fun i => decl_i (Z.of_nat i)) (seq k n)) with
  | Some jj => CAT + 296 * Z.of_nat (k + jj) | None => 0 end = rob blk k n.
Proof.
  intros blk n. induction n as [|n IH]; intros k; [reflexivity|].
  cbn [seq map cm_find rob].
  destruct (decide (decl_i (Z.of_nat k) = blk)) as [E|E].
  - rewrite !bool_decide_eq_true_2 by exact E. unfold CAT_ROW. lia.
  - rewrite !bool_decide_eq_false_2 by exact E. rewrite <- (IH (S k)).
    destruct (cm_find blk (map (fun i => decl_i (Z.of_nat i)) (seq (S k) n))) as [jj|]; cbn [option_map];
      [lia | reflexivity].
Qed.

(* C4.12 with struct P5.5: the catalogue match's result is the harness's row_of_block. *)
Lemma f37_want_eq : forall inp j, t_want inp j = t_want_m inp j.
Proof.
  intros inp j. unfold t_want, t_want_m, want, t_rowsel, t_k.
  set (gg := t_g inp j). set (len := t_len inp j).
  destruct (Z.eqb_spec (fst (ctrlparse len gg)) 9) as [K|K].
  - assert (Hh : cp_hdr len gg = true).
    { destruct (cp_hdr len gg) eqn:E; [reflexivity|]. unfold ctrlparse in K. rewrite E in K. cbn in K.
      discriminate K. }
    apply cp_hdr_spec in Hh as (H1 & H2 & H3).
    unfold cm_gate. rewrite K, H2, H3, (proj2 (Z.leb_le 50 len) H1). cbn [Z.eqb Pos.eqb andb].
    destruct (cp_v gg 16 =? 205), (cp_v gg 17 =? 234); cbn [andb]; try reflexivity.
    rewrite f37_DECLS. change (cm_blk gg) with (t_blk inp j).
    exact (f37_cm_find_rob (t_blk inp j) 11 0).
  - unfold cm_gate. rewrite (proj2 (Z.eqb_neq _ _) K). rewrite !andb_false_r. reflexivity.
Qed.

(* ===================== the lengths of the two frame records LT names ===================== *)

(* The identity record at fr + 2688 keeps its 38 bytes and the fragment state at fr + 2768 stays within 72 bytes,
   so the bytes of both lie in the frame [fr, fr + 3136). *)
Lemma f37_upd_N : forall (l bs : list byte) off N, length l = N -> (off + length bs <= N)%nat ->
  length (RcIdentModel.upd l off bs) = N.
Proof.
  intros l bs off N HL H. unfold RcIdentModel.upd.
  rewrite !length_app, length_firstn, length_skipn. lia.
Qed.

Lemma f37_name_len : forall p, (name_len p <= 16)%nat.
Proof. intros p. unfold name_len, NAME_CAP. cbv zeta. lia. Qed.

Lemma f37_ING_len : forall idb a p, length idb = ID_SIZE -> length (snd (ING idb a p)) = ID_SIZE.
Proof.
  intros idb a p H. pose proof (f37_name_len p) as Hw.
  unfold ING, ing_firmware, ing_name, ing_version. cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn [snd]; try exact H;
  repeat (apply f37_upd_N); try exact H;
  unfold ID_SIZE, OFF_FW, OFF_HAS_FW, OFF_NAME, OFF_HAS_NAME, OFF_MAJOR, OFF_MINOR, OFF_PATCH, OFF_RAW,
    OFF_HAS_VER, REAC_VER_LEN, RcIdentModel.le16;
  rewrite ?length_app, ?length_firstn; cbn [length]; lia.
Qed.

Lemma f37_ID_len : forall inp j, length (t_ID inp j) = ID_SIZE.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH]; cbn [fst_at].
  - unfold fs0, ID0. cbn [fs_id]. apply repeat_length.
  - unfold turn, fg_id, rp_id. cbv zeta.
    repeat match goal with |- context [if ?c then _ else _] => destruct c end;
    cbn [fs_id]; repeat (apply f37_ING_len); exact IH.
Qed.

Lemma f37_bat_nn : forall bs i, 0 <= bat bs i.
Proof. intros bs i. unfold bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))). lia. Qed.

Lemma f37_clear_len : forall st, (length st <= 72)%nat -> (length (fg_clear st) <= 72)%nat.
Proof.
  intros st H. unfold fg_clear. rewrite !length_app, length_firstn, length_skipn. cbn [length]. lia.
Qed.

Lemma f37_FG_step : forall len st g, (length st <= 72)%nat -> (length (fg_st len st g) <= 72)%nat.
Proof.
  intros len st g H. unfold fg_st, fcls, fg_class, fg_next.
  destruct (fg_fr len g) eqn:Efr; cbn [negb orb Z.eqb]; [|exact H].
  pose proof (f37_bat_nn g 26) as Hn0. pose proof (f37_bat_nn st 7) as Hl0.
  destruct (bat g 19 =? 1); cbn [negb].
  - assert (Hn : fg_n g <= 22).
    { unfold fg_fr in Efr. apply andb_prop in Efr as (Ea & _). apply andb_prop in Ea as (_ & E22).
      apply Z.leb_le in E22. exact E22. }
    unfold fg_first, fg_body, bsl, fg_n in *. rewrite !length_app, !length_firstn, !length_skipn.
    cbn [length]. lia.
  - destruct (fg_keep st g) eqn:Ek; cbn [negb]; [|apply f37_clear_len; exact H].
    assert (HT : fg_T st g <= 64).
    { unfold fg_keep in Ek. apply andb_prop in Ek as (_ & ET). apply Z.leb_le in ET. exact ET. }
    destruct (fg_close st g); cbn [negb]; apply f37_clear_len;
      unfold fg_join, fg_body, bsl, fg_T, fg_lf, fg_n in *; rewrite !length_app, !length_firstn, !length_skipn;
      lia.
Qed.

Lemma f37_FG_len : forall inp j, (length (t_FG inp j) <= 72)%nat.
Proof.
  intros inp j. unfold t_FG. induction j as [|j IH]; cbn [fst_at].
  - unfold fs0. cbn [fs_fg]. rewrite z72_length. lia.
  - unfold turn. cbv zeta.
    repeat match goal with |- context [if ?c then _ else _] => destruct c end;
    cbn [fs_fg]; apply f37_FG_step; exact IH.
Qed.

(* v1.9 FSb: the first fragment's body is at most the 23 bytes block[9 ..] of a 50-byte record (fs0's is empty),
   so it lies in [fr + 2880, fr + 2903), inside the frame.  (F29's fs_body_len.) *)
Lemma f37_fs_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fst_at fs0 fs_body length]. lia.
  - rewrite fst_at_S. unfold turn. cbv beta zeta.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
    rewrite length_firstn, length_skipn. unfold t_g. rewrite fr50_length. lia.
Qed.

(* ===================== the machine run 0x828d8 -> the free wrapper's entry ===================== *)

(* 0x828d8 bne a0,s4 (not taken, a0 = s4); 0x828dc-0x82934 the 23 frame-shadow stores at S3 + 22 .. S3 + 66;
   0x82938 mv a0,s7; 0x8293c jal 0x53378 (as_free ASYMS) with ra = 0x82940. *)
Lemma f37_evt_body :
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
          x26 x27 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (S3 : Z) (bs : list byte),
    x19 = Z_to_bv 64 S3 -> x10 = x20 ->
    rw_cells rsegs m S3 [CB 67 bs] -> 0 <= S3 -> S3 + 67 <= 2 ^ 64 ->
    LE.evt rsegs
      (fun ms' => exists m', ms' = MS (mkR (Z_to_bv 64 0x82940) x2 x3 x4 x5 x6 x7 x8 x9 x23 x11 x12 x13 x14 x15
                                          x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                     Fr (Z_to_bv 64 0x53378) fc None m' (seg_rom rsegs) /\
         munch [(S3 + 22, S3 + 67)] m m' /\ wmono rsegs m m' /\
         exists cs, rw_cells rsegs m' S3 cs /\ cells_size cs = 67%nat)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
               x27 x28 x29 x30 x31) Fr (Z_to_bv 64 0x828d8) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 Fr fc m S3 bs -> E1020 HRW H0 H1.
  subst x10.
  pose proof (munch_refl [(S3 + 22, S3 + 67)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. f37_nt.
  do 23 (step; rewrite f37_le1_byte; mem_after_store).
  step. step.
  match goal with |- LE.evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : rw_cells rsegs mm S3 ?cs |- _ =>
      apply evt_done; exists mm; split; [reflexivity|];
      split; [assumption|]; split; [assumption|];
      exists cs; split; [exact H | reflexivity]
    end
  end.
Qed.

Section F37.
Context {fx : AYK.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Local Notation STKLO mem md := (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
Local Notation OWNED H mem md := (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md).

(* The Lib-evt -> SR bridge (F29's sl_run_lib). *)
Lemma f37_run_lib : forall regs pc mem md
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

(* The frame's place (plan FP.1/FP.2), as in F29/F36. *)
Lemma f37_fra_loc : forall g fr hb regs mem md, FRA B APIf ra g fr hb regs mem md ->
  exists FS, (exists w : word, bytes_at rsegs mem RT_TP (le8 w) /\ bv_unsigned w = FS) /\
    AC.GT <= FS /\ FS + AC.FS_SIZE <= STKLO mem md /\ (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a) /\
    HIGHMEM_BEG <= STKLO mem md /\
    0 <= fr /\ AC.GT <= fr /\ (forall a, fr <= a < fr + 3136 -> app_mem a) /\
    ((STKLO mem md <= fr /\ fr + 3136 <= APPMEM_END) \/ (FS <= fr /\ fr + 3136 <= FS + AC.FS_SIZE)).
Proof.
  intros g fr hb regs mem md HFRA.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSHv.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGTfr & Hfrapp).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof Hwin as (Hw0 & Hw1 & _).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (RT_fs_cells _ _ _ HRT) as (_ & _ & _ & _ & (FSw & HFSw & HFok) & _).
  pose proof (bv_unsigned_in_range 64 FSw) as HFSr. change (bv_modulus 64) with (2 ^ 64) in HFSr.
  assert (Hwm : word_mem rsegs mem (AC.as_tp AC.ASYMS) (bv_unsigned FSw)).
  { change (AC.as_tp AC.ASYMS) with RT_TP. exact (bytes_at_le8_word rsegs mem RT_TP FSw HFSw). }
  destruct (AC.a_laws_fs_place _ _ _ _ _ LAWS _ mem md (bv_unsigned FSw) HAH Hwm HFSr)
    as (HGT & HFSlo & _ & HFSapp).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hhi.
  pose proof Hhdr1 as Hb1. unfold q64 in Hb1. apply bytes_at_bound in Hb1. rewrite length_le8 in Hb1.
  exists (bv_unsigned FSw).
  split; [exists FSw; split; [exact HFSw | reflexivity]|].
  split; [exact HGT|]. split; [exact HFSlo|]. split; [exact HFSapp|]. split; [exact Hhi|].
  split; [lia|]. split; [exact HGTfr|]. split; [exact Hfrapp|].
  destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
  - pose proof (Hreal fr ltac:(lia)) as R1. pose proof (Hreal (fr + 3135) ltac:(lia)) as R2. left. lia.
  - assert (HFS1 : bv_unsigned FSw + AC.FS_SIZE <= 2 ^ 64) by (unfold AF.SLOT_STACK in *; lia).
    assert (Hin : forall a, fr <= a < fr + 3136 -> bv_unsigned FSw <= a < bv_unsigned FSw + AC.FS_SIZE).
    { intros a Ha. destruct (Hfs a Ha) as (b & Hbr & Hb & Hab).
      change (AC.as_tp AC.ASYMS) with RT_TP in Hb.
      pose proof (f37_wm_uniq mem RT_TP b (bv_unsigned FSw) Hb Hwm Hbr HFSr) as E. lia. }
    pose proof (Hin fr ltac:(lia)) as F1. pose proof (Hin (fr + 3135) ltac:(lia)) as F2.
    right. lia.
Qed.

(* A byte of a live heap block is not a frame byte. *)
Lemma f37_fra_blk : forall g fr hb regs mem md p n a, FRA B APIf ra g fr hb regs mem md ->
  In (p, n) (hb ++ g_H g) -> p <= a < p + n -> fr <= a < fr + 3136 -> False.
Proof.
  intros g fr hb regs mem md p n a HFRA Hin Ha Hfa.
  pose proof FRAME_BYTES_val as HFBv.
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & HfrA & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md p n HAH Hin) as (_ & _ & Hend & _ & Hall).
  destruct (Hall a Ha) as (_ & _ & _ & _ & Hnfs).
  destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
  - pose proof (Hreal a Hfa). lia.
  - exact (Hnfs (Hfs a Hfa)).
Qed.

(* The write set of the frame-shadow stores, and the addresses they miss. *)
Lemma f37_meta_out : forall g fr hb regs mem md o n,
  FRA B APIf ra g fr hb regs mem md -> 0 <= o -> 0 < n -> o + n <= 392 ->
  0 <= fr /\ fr mod 8 = 0 /\ AC.GT <= fr /\ (forall a, fr <= a < fr + 3136 -> app_mem a) /\
  LOWMEM_END <= Sfr fr /\ Sfr fr + 392 <= HIGHMEM_BEG /\
  (forall x, app_mem x -> outside [(Sfr fr + o, Sfr fr + o + n)] x) /\
  (forall x, HIGHMEM_BEG <= x -> outside [(Sfr fr + o, Sfr fr + o + n)] x) /\
  (forall x, x < LOWMEM_END -> outside [(Sfr fr + o, Sfr fr + o + n)] x) /\
  (forall y, 0 <= y -> ~ (fr <= y < fr + 3136) -> outside [(Sfr fr + o, Sfr fr + o + n)] (shadow_addr y)).
Proof.
  intros g fr hb regs mem md o n HFRA Ho Hn Hon.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSHv.
  pose proof (f37_fra_loc g fr hb regs mem md HFRA)
    as (FS & _ & _ & _ & _ & _ & Hfr0 & HGTfr & Hfrapp & _).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; clear; Z.div_mod_to_equations; lia).
  assert (HSh : forall x, Sfr fr <= x < Sfr fr + 392 -> in_shadow x).
  { intros x Hx.
    assert (E : shadow_addr (fr + 8 * (x - Sfr fr)) = x)
      by (rewrite f37_sh_frame_of by (unfold Sfr in *; lia); unfold Sfr in *; lia).
    rewrite <- E. apply shadow_of_app. apply Hfrapp. unfold Sfr in *. lia. }
  pose proof (f37_in_shadow_bnd _ (HSh (Sfr fr) ltac:(lia))) as HB1.
  pose proof (f37_in_shadow_bnd _ (HSh (Sfr fr + 391) ltac:(lia))) as HB2.
  split; [exact Hfr0|]. split; [exact Hfr8|]. split; [exact HGTfr|]. split; [exact Hfrapp|].
  split; [lia|]. split; [lia|].
  split.
  { intros x Hx. cbn [outside]. split; [|exact I]. intros Hin.
    exact (app_not_shadow x Hx (HSh x ltac:(lia))). }
  split; [intros x Hx; cbn [outside]; split; [lia | exact I]|].
  split; [intros x Hx; cbn [outside]; split; [lia | exact I]|].
  intros y Hy0 Hny. cbn [outside]. split; [|exact I]. intros Hin.
  pose proof (f37_sh_frame fr y (shadow_addr y - Sfr fr) Hfr0 Hfr8 Hy0 ltac:(unfold Sfr in *; lia)) as Hz.
  apply Hny. lia.
Qed.

(* The n shadow bytes at S(fr) + o are a writable cell block: they are present (FRA's 392-byte list) and
   writable (the runtime's shadow_rw). *)
Lemma f37_shadow_rw : forall g fr hb regs mem md (o : Z) (n : nat),
  FRA B APIf ra g fr hb regs mem md -> 0 <= o -> (0 < n)%nat -> o + Z.of_nat n <= 392 ->
  exists bs, rw_cells rsegs mem (Sfr fr + o) [CB n bs].
Proof.
  intros g fr hb regs mem md o n HFRA Ho Hn Hon.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSHv.
  destruct (f37_meta_out g fr hb regs mem md o (Z.of_nat n) HFRA Ho ltac:(lia) ltac:(lia))
    as (Hfr0 & Hfr8 & HGTfr & Hfrapp & HB1 & HB2 & _).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    (sh & Hshb & Hshl) & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  assert (HSh : forall x, Sfr fr <= x < Sfr fr + 392 -> in_shadow x).
  { intros x Hx.
    assert (E : shadow_addr (fr + 8 * (x - Sfr fr)) = x)
      by (rewrite f37_sh_frame_of by (unfold Sfr in *; lia); unfold Sfr in *; lia).
    rewrite <- E. apply shadow_of_app. apply Hfrapp. unfold Sfr in *. lia. }
  pose proof (f37_ba_sub mem (Sfr fr) sh (Z.to_nat o) n Hshb ltac:(lia)) as Hsub.
  rewrite Z2Nat.id in Hsub by lia.
  exists (firstn n (skipn (Z.to_nat o) sh)).
  assert (Hwr : wr_at rsegs mem (Sfr fr + o) (Z.of_nat n)).
  { split; [unfold LOWMEM_END in *; lia|]. split; [unfold HIGHMEM_BEG in *; lia|]. intros i Hi.
    exact (proj1 (RT_shadow_rw _ _ _ HRT (Sfr fr + o + i) (HSh (Sfr fr + o + i) ltac:(lia)))). }
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [rewrite length_firstn, length_skipn; lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hsub.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hwr.
Qed.

(* FRA across a run that writes n shadow bytes of the frame, [S(fr) + o, S(fr) + o + n) with o + n <= 392:
   Tac_slot.sl_fr_meta, with the heap invariant from Tac_fs.a_fs_ok_store_AH (each written byte is the shadow of
   a frame byte, which is in the store set of the real-stack arm or the shadow of a side-stack byte on the side
   arm).  The stack bounds and the allocator's byte set do not change either, which ENT reads. *)
Lemma f37_fra_meta : forall g fr hb regs regs' mem mem' md (o n : Z),
  FRA B APIf ra g fr hb regs mem md ->
  0 <= o -> 0 < n -> o + n <= 392 ->
  munch [(Sfr fr + o, Sfr fr + o + n)] mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall x, Sfr fr + o <= x < Sfr fr + o + n -> exists b, mrd rsegs mem' (wa x) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md /\
  STKLO mem' md = STKLO mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall q, OWNED (hb ++ g_H g) mem' md q <-> OWNED (hb ++ g_H g) mem md q).
Proof.
  intros g fr hb regs regs' mem mem' md o n HFRA Ho Hn Hon MU WM HroM HnewP E2 E3 E4 E8 E9 E19 E26.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSHv.
  pose proof (f37_fra_loc g fr hb regs mem md HFRA)
    as (FS & (FSw & HFSw & EFS) & HGTFS & HFSlo & HFSapp & Hhi & Hfr0 & HGTfr & Hfrapp & Hfrloc).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 &
    (sh & Hsh & Hshl) & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof Hwin as (Hw0 & Hw1 & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  assert (HAhi : HIGHMEM_BEG <= A) by (unfold AF.SLOT_STACK in *; lia).
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; clear; Z.div_mod_to_equations; lia).
  set (S3 := Sfr fr) in *.
  assert (HSh : forall x, S3 <= x < S3 + 392 ->
    in_shadow x /\ shadow_addr (fr + 8 * (x - S3)) = x /\ fr <= fr + 8 * (x - S3) < fr + 3136).
  { intros x Hx.
    assert (E : shadow_addr (fr + 8 * (x - S3)) = x)
      by (rewrite f37_sh_frame_of by lia; unfold S3, Sfr; lia).
    split; [rewrite <- E; apply shadow_of_app, Hfrapp; lia | split; [exact E | lia]]. }
  pose proof (f37_in_shadow_bnd _ (proj1 (HSh S3 ltac:(lia)))) as HS3a.
  pose proof (f37_in_shadow_bnd _ (proj1 (HSh (S3 + 391) ltac:(lia)))) as HS3b.
  set (W := [(S3 + o, S3 + o + n)]) in *.
  assert (HWsh : forall x, S3 + o <= x < S3 + o + n -> in_shadow x) by (intros x Hx; apply HSh; lia).
  assert (HWapp : forall x, app_mem x -> outside W x).
  { intros x Hx. cbn [outside]. split; [|exact I]. intros Hin. exact (app_not_shadow x Hx (HWsh x Hin)). }
  assert (HWhi : forall x, HIGHMEM_BEG <= x -> outside W x).
  { intros x Hx. cbn [outside]. split; [|exact I]. intros Hin.
    pose proof (f37_in_shadow_bnd _ (HWsh x Hin)). lia. }
  assert (HWsh2 : forall x, ~ (S3 <= x < S3 + 392) -> outside W x).
  { intros x Hx. cbn [outside]. split; [|exact I]. lia. }
  assert (HpresM : forall x, 0 <= x < 2 ^ 64 -> (exists b, mrd rsegs mem (wa x) = Some b) ->
    exists b, mrd rsegs mem' (wa x) = Some b).
  { intros x Hx Hp. destruct (Z_le_gt_dec (S3 + o) x); [destruct (Z_lt_ge_dec x (S3 + o + n))|].
    - apply HnewP. lia.
    - unfold mrd in *. rewrite MU; [exact Hp|]. rewrite wa_unsigned by lia.
      cbn [outside]. split; [lia | exact I].
    - unfold mrd in *. rewrite MU; [exact Hp|]. rewrite wa_unsigned by lia.
      cbn [outside]. split; [lia | exact I]. }
  assert (Hsh' : exists sh', bytes_at rsegs mem' S3 sh' /\ length sh' = 392%nat).
  { apply f37_ba_present; [unfold LOWMEM_END in *; lia | unfold HIGHMEM_BEG in *; lia |].
    intros i Hi. apply HpresM; [unfold LOWMEM_END, HIGHMEM_BEG in *; lia|].
    apply (f37_ba_some mem S3 sh); [exact Hsh | rewrite Hshl; lia]. }
  assert (Hrtdj : rt_disjoint W).
  { subst W. unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
      RT_AGLOB_LEN.
    unfold LOWMEM_END in HS3a. cbn [disjoint_from]. repeat split; first [left; lia | exact I]. }
  pose proof (bv_unsigned_in_range 64 FSw) as HFSr. change (bv_modulus 64) with (2 ^ 64) in HFSr.
  rewrite EFS in HFSr.
  assert (Hwm : word_mem rsegs mem (AC.as_tp AC.ASYMS) FS).
  { change (AC.as_tp AC.ASYMS) with RT_TP. rewrite <- EFS.
    exact (bytes_at_le8_word rsegs mem RT_TP FSw HFSw). }
  assert (Hfsz : FS + AC.FS_SIZE <= 2 ^ 64) by (unfold AF.SLOT_STACK in *; lia).
  assert (Hmeta : forall q, fs_meta FS q -> outside W q).
  { intros q Hq. apply HWapp. apply HFSapp. split; [exact (f37_fs_meta_ge FS q Hq)|].
    pose proof (fs_meta_below FS q Hq). unfold AC.FS_SIZE. lia. }
  assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
    ~ AC.a_store_ok (hb ++ g_H g) (STKLO mem md) q -> ~ (FS <= q < FS + AC.FS_SIZE) ->
    ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) -> mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
  { intros q Hq Hns Hnf Hnsh. apply MU. rewrite unsigned_lit by lia. cbn [outside]. split; [|exact I].
    intros Hin. destruct (HSh q ltac:(lia)) as (_ & Eq & Hb).
    destruct Hfrloc as [[Hlo Hhi'] | [Hlo Hhi']].
    - apply Hns. unfold AC.a_store_ok. right; right; right. exists (fr + 8 * (q - S3)).
      split; [symmetry; exact Eq|]. right; left. lia.
    - apply Hnsh. exists (fr + 8 * (q - S3)). split; [lia | symmetry; exact Eq]. }
  destruct (a_fs_ok_store_AH AC.ASYMS _ _ _ _ W _ mem mem' md FS LAWS HAH Hwm HFSr Hfsz MU
              (fun q _ Hw => WM _ Hw) (fun q Hq Hp => HpresM q Hq Hp) Hmeta Hagree)
    as (HAH' & HOWN & HSTK & HSTKHI).
  assert (HAG' : forall a, in_globals AF.frame_AG a -> addressable mem' a 1).
  { intros a Hin. pose proof (f37_ag_range a Hin) as Hab.
    apply (f37_addr_keep W mem mem' a 1 (HAG a Hin) MU). intros i Hi.
    assert (Hlt : shadow_addr (a + i) < S3)
      by (unfold S3, Sfr; apply f37_sh_lt; [exact Hfr8 | unfold AC.GT in HGTfr; lia]).
    apply HWsh2. lia. }
  split; [|split; [exact HSTK | split; [exact HSTKHI | exact HOWN]]].
  apply (sl_fr_meta B APIf ra empty FF g fr _ regs regs' mem mem' md W HFRA MU WM HroM Hrtdj HAH' HSTK
           Hfrapp HGTfr Hsh').
  - intros x Hx Hn1 Hn2. exact (HWsh2 x Hn2).
  - intros A1 HA1 HA1r x Hx.
    assert (EA : A1 = A) by (apply (f37_reg_eq regs 9 A1 A HA1 Hr9 HA1r HA64)).
    apply HWhi. lia.
  - intros x Hx. apply HWhi. lia.
  - intros A1 HA1 HA1r x Hx.
    assert (EA : A1 = A) by (apply (f37_reg_eq regs 9 A1 A HA1 Hr9 HA1r HA64)).
    apply HWhi. lia.
  - intros x Hx. left. apply HWhi. unfold AF.SLOT_STACK in *. lia.
  - exact HAG'.
  - exact E2.
  - exact E3.
  - exact E4.
  - exact E8.
  - exact E9.
  - exact E19.
  - exact E26.
Qed.

(* A byte of the real stack above stklo, or a byte of the side stack: the two kinds the free wrapper leaves
   alone outside its own window (F1's f1_loc). *)
Definition f37_loc (mem : word -> option byte) (md : Model) (a : Z) : Prop :=
  STKLO mem md <= a < APPMEM_END \/ (AC.a_in_fs AC.ASYMS mem a /\ AC.GT <= a < STKLO mem md).

(* The free wrapper's contract at this segment's call (Contract.v afree_at, through aa_free), applied ONCE (a Theorem Labs lane's
   instruction of 2026-10-28: until generation N+1 gives afree_at a record with named projections, its positional
   premises are applied in one local lemma, so a new generation breaks this lemma and no site).  The call heap is
   the cut's block (p, n) in front of the entry heap (H1 = [], H2 = g_H g).  Generation N.1's binder Bc and its two
   class premises (the call heap's per-class bytes under Bc, and the room inequality) are Seg/Tac_cls.v's
   sl_free_cls for Bc = Bc_of BE, where BE is ENT #14's own witness (a Theorem Labs lane's design): F37 derives no class fact
   and seg_F37 takes no new premise. *)
Lemma f37_free : forall g hb mem0 md0 regs mem md p n,
  ENT APIf g hb mem0 md0 ->
  AC.a_call_pre AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
    (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
    AC.AK_FREE ([] ++ (p, n) :: g_H g) regs mem md ->
  getr regs 10 = Z_to_bv 64 p ->
  SR rsegs (mkCfg (mkst regs (Z_to_bv 64 (AC.as_free AC.ASYMS)) mem (seg_rom rsegs)) md)
    (fun c' => exists regs' mem' md',
       c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
       AC.a_call_post AC.ASYMS AsanRTInv.RT (AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc))
         (AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc)) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc))
         (AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc))
         AC.AK_FREE ([] ++ (p, n) :: g_H g) regs mem md (fun a => p <= a < p + n) ([] ++ g_H g) regs' mem' md' /\
       AC.a_errno_kept AC.ASYMS mem mem').
Proof.
  intros g hb mem0 md0 regs mem md p n HENT Hpre Ea0.
  destruct (sl_free_cls APIf g hb mem0 md0 p n HENT) as (BE & _ & _ & Hcls & Hroom).
  exact (AC.aa_free AC.ASYMS AsanRTInv.RT (APIf rc) [] (g_H g) regs mem md p n (Bc_of BE) Hpre Ea0 Hcls Hroom).
Qed.

(* ===================== the segment ===================== *)

Lemma seg_F37 : forall j, Hat B APIf ra (Inv_A82940_at B APIf ra) j ->
  Hat B APIf ra (Inv_A828d8_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSHv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI &
                    HLK & HFLSX & H20 & H10 & HLT).
  subst c. pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _ & _ & _ & _ & Hown & _).
  pose proof HFLSX as (_ & H18 & H22 & H23 & H25 & Hrec & Hs152 & Hs280).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  set (n := AC.a_size (flen g j)) in *.
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof Hwin as (Hw0 & Hw1 & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by lia.
  destruct (f37_meta_out g fr (hb1 phi n) regs mem md 22 45 HFRA ltac:(lia) ltac:(lia) ltac:(lia))
    as (Hfr0 & Hfr8 & HGTfr & Hfrapp & HSB1 & HSB2 & HWapp & HWhi & HWlo & HWsh).
  destruct (f37_shadow_rw g fr (hb1 phi n) regs mem md 0 67 HFRA ltac:(lia) ltac:(lia) ltac:(cbn; lia))
    as (bs0 & HRW).
  rewrite Z.add_0_r in HRW.
  (* the branch is not taken: the catalogue match's result is the expected row *)
  assert (E1020 : getr regs 10 = getr regs 20).
  { unfold rg in H10, H20. rewrite H10, H20, f37_want_eq. reflexivity. }
  rewrite SEGS.
  apply (f37_run_lib regs (Z_to_bv 64 0x828d8) mem md
    (fun R0 pc' mem' => pc' = Z_to_bv 64 0x53378 /\
       getr R0 1 = Z_to_bv 64 0x82940 /\ getr R0 10 = getr regs 23 /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 21 = getr regs 21 /\
       getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\
       getr R0 25 = getr regs 25 /\ getr R0 26 = getr regs 26 /\
       munch [(Sfr fr + 22, Sfr fr + 22 + 45)] mem mem' /\ wmono rsegs mem mem' /\
       (exists cs, rw_cells rsegs mem' (Sfr fr) cs /\ cells_size cs = 67%nat))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply (f37_evt_body _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                fp_regs fp_csr mem (Sfr fr) bs0);
        [ unfold rg in Hr19; exact Hr19 | exact E1020 | exact HRW
        | unfold LOWMEM_END in *; lia | unfold HIGHMEM_BEG in *; lia ]. }
    { intros ms' (m' & E & MU & WM & cs & Hcs & Hcsl).
      eexists _, (Z_to_bv 64 0x53378), m'. split; [exact E|].
      split; [reflexivity|].
      do 14 (split; [reflexivity|]).
      split; [replace (Sfr fr + 22 + 45) with (Sfr fr + 67) by lia; exact MU|].
      split; [exact WM|]. exists cs. split; [exact Hcs | exact Hcsl]. }
  - intros R0 pc' mem1 regs1 md1
      (Hpc & E1 & E10 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E21 & E22 & E23 & E25 & E26 &
       MU & WM & cs & Hcs & Hcsl) Hreg Hmat.
    subst pc'.
    assert (F1 : getr regs1 1 = Z_to_bv 64 0x82940) by (rewrite Hreg; exact E1).
    assert (F10 : getr regs1 10 = getr regs 23) by (rewrite Hreg; exact E10).
    assert (F2 : getr regs1 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (F3 : getr regs1 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (F4 : getr regs1 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (F8 : getr regs1 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (F9 : getr regs1 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (F18 : getr regs1 18 = getr regs 18) by (rewrite Hreg; exact E18).
    assert (F19 : getr regs1 19 = getr regs 19) by (rewrite Hreg; exact E19).
    assert (F21 : getr regs1 21 = getr regs 21) by (rewrite Hreg; exact E21).
    assert (F22 : getr regs1 22 = getr regs 22) by (rewrite Hreg; exact E22).
    assert (F23 : getr regs1 23 = getr regs 23) by (rewrite Hreg; exact E23).
    assert (F25 : getr regs1 25 = getr regs 25) by (rewrite Hreg; exact E25).
    assert (F26 : getr regs1 26 = getr regs 26) by (rewrite Hreg; exact E26).
    (* the bytes of the written range are present again *)
    assert (HnewP : forall x, Sfr fr + 22 <= x < Sfr fr + 22 + 45 -> exists b, mrd rsegs mem1 (wa x) = Some b).
    { intros x Hx. destruct Hcs as ((Hwf & Hba) & _).
      pose proof (cells_bytes_length cs Hwf) as Hlen.
      replace x with (Sfr fr + (x - Sfr fr)) by lia.
      apply (f37_ba_some mem1 (Sfr fr) (cells_bytes cs)); [exact Hba | rewrite Hlen, Hcsl; cbn; lia]. }
    assert (Hkeep0 : forall x, 0 <= x < 2 ^ 64 -> ~ (Sfr fr + 22 <= x < Sfr fr + 22 + 45) ->
                       mbyte rsegs mem1 x = mbyte rsegs mem x).
    { intros x Hx Hnx. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
      rewrite MState.unsigned_lit by lia. cbn [outside]. split; [lia | exact I]. }
    assert (HroM : ro_agree rsegs mem1).
    { apply (ro_agree_same rsegs mem mem1 Hro). intros a Ha.
      pose proof (f37_ro_lo a Ha) as Hlo'. apply MU. cbn [outside]. split; [lia | exact I]. }
    destruct (f37_fra_meta g fr (hb1 phi n) regs regs1 mem mem1 md 22 45 HFRA ltac:(lia) ltac:(lia)
                ltac:(lia) MU WM HroM HnewP F2 F3 F4 F8 F9 F19 F26) as (HFRA1 & HSTK1 & HSTKHI1 & HOWN1).
    assert (HFRA2 : FRA B APIf ra g fr (hb1 phi n) regs1 mem1 md1)
      by (apply (sl_fra_move B APIf ra g fr (hb1 phi n) regs1 regs1 mem1 md md1 HFRA1);
          try reflexivity; exact Hmat).
    (* ENT across the stores and the model's lazy materialisation *)
    assert (HENT1 : ENT APIf g (hb1 phi n) mem1 md).
    { apply (ent_store B APIf ra g fr (hb1 phi n) regs mem mem1 md
               [(Sfr fr + 22, Sfr fr + 22 + 45)] HENT HFRA MU).
      - intros x Hx. destruct (Z_le_gt_dec (Sfr fr + 22) x); [destruct (Z_lt_ge_dec x (Sfr fr + 22 + 45))|].
        + right. right. right. unfold Sfr in *. lia.
        + left. cbn [outside]. split; [lia | exact I].
        + left. cbn [outside]. split; [lia | exact I].
      - exact HSTK1.
      - exact HSTKHI1.
      - intros a Hia Hio. exact (proj2 (HOWN1 a) Hio). }
    assert (HENT2 : ENT APIf g (hb1 phi n) mem1 md1) by exact (ent_mat APIf g _ mem1 md md1 HENT1 Hmat).
    (* ---- the free call ---- *)
    assert (Hret : YK0s.ret_ok (getr regs1 1)).
    { rewrite F1. apply YK0s.ret_ok_even. rewrite MState.unsigned_lit by lia. reflexivity. }
    pose proof (fra_call_pre B APIf ra g fr (hb1 phi n) regs1 mem1 md1 AC.AK_FREE HFRA2 HENT2 Hret
                  ltac:(unfold AC.AK_FREE, FN_STACK, AF.SLOT_STACK; lia)) as Hpre.
    assert (Ea0 : getr regs1 10 = Z_to_bv 64 phi) by (rewrite F10; exact H23).
    (* the contract and the carried facts are stated with rsegs; the goal was moved there above.  The class
       premises of the contract come from ENT through f37_free. *)
    eapply SR_bind.
    { refine (f37_free g (hb1 phi n) mem1 md1 regs1 mem1 md1 phi n HENT2 _ Ea0).
      exact Hpre. }
    intros c' (regs2 & mem2 & md2 & Ec' & Hcp & Herrk).
    subst c'. rewrite F1.
    (* ---- what the free keeps ---- *)
    pose proof (sl_frame_apart_win B APIf ra g fr (hb1 phi n) regs1 mem1 md1 HFRA2) as Hapart0.
    pose proof HFRA2 as (A1 & sp1 & s51 & HRT1 & HAH1 & Hro1 & Hsn1 & Hhalt1 & Hgimg1 & Hr21 & Hspm1 & Haspz1a &
      Hstklo1 & Hr41 & Hr81 & Hr91 & Hr31 & Hr191 & Hr261 & Hfrm1 & Hs51 & HAm1 & HAS1 & Hspa1 & Hfa1 &
      HA4161 & HS41 & HAPP1 & Hspill1 & Hsel1 & Hfr241 & Hloc1 & Hhdr11 & Hhdr21 & Hsh1 & Hwin1 & Hsaved1 &
      Herrno1 & HAG1 & HWA1 & HSHI11 & HSHI21 & HSHI31 & Hhb1 & Hlive1).
    pose proof Hwin1 as (Hv0 & Hv1 & _).
    assert (Hr9b : rg regs1 9 A) by (unfold rg in *; rewrite F9; exact Hr9).
    assert (EA1 : A1 = A) by (apply (f37_reg_eq regs1 9 A1 A Hr91 Hr9b); lia).
    subst A1.
    assert (Haspz1 : AC.aspZ regs1 = sp) by (unfold AC.aspZ in *; rewrite F2; exact Haspz).
    assert (Esp1 : sp1 = sp) by (rewrite <- Haspz1a; exact Haspz1).
    subst sp1.
    assert (Eerr : AC.a_errno AC.ASYMS = 0x5db76c) by reflexivity.
    assert (Eoom : AC.as_oom AC.ASYMS = 0x12aae0) by reflexivity.
    assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
    assert (HFSv : AC.FS_SIZE = 11571200) by reflexivity.
    assert (Hsp0 : 0 <= sp < 2 ^ 64) by (rewrite <- Haspz; unfold AC.aspZ; apply u64_range).
    assert (Hstkhi1 : HIGHMEM_BEG <= STKLO mem1 md1)
      by exact (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem1 md1 HAH1).
    assert (HHBv : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
    assert (HAEv : APPMEM_END = 0x800000000000) by reflexivity.
    assert (HLEv : LOWMEM_END = 0x7fff8000) by reflexivity.
    assert (Hsphi : 0x10007fff8000 + 1000000 <= sp) by (unfold AF.SLOT_STACK in *; lia).
    assert (Hapart : forall a, fr <= a < fr + 3136 -> ~ (sp - 4096 <= a < sp))
      by (intros a Ha; rewrite <- Haspz1; exact (Hapart0 a Ha)).
    (* the released block *)
    assert (Hblk_in : In (phi, n) (hb1 phi n ++ g_H g)) by (left; reflexivity).
    destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem1 md1 phi n HAH1 Hblk_in)
      as (_ & Hp4096 & Hpstk & _ & Hball).
    pose proof Hcp as HAH2; apply AC.a_call_post_ah in HAH2.
    pose proof Hcp as Hkept; apply AC.a_call_post_regs in Hkept.
    pose proof Hcp as Hsk2; apply AC.a_call_post_stklo in Hsk2.
    pose proof (AC.a_call_post_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcp) as Hfk.
    pose proof (AC.a_call_post_win_writable _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcp) as Hwinw.
    pose proof (AC.a_call_post_win_present _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hcp) as Hwinp.
    pose proof Hcp as Hmod; apply AC.a_call_post_model in Hmod.
    assert (Htp16 : forall i, 0 <= i < 16 ->
              mbyte rsegs mem2 (AC.as_tp AC.ASYMS + i) = mbyte rsegs mem1 (AC.as_tp AC.ASYMS + i))
      by (eapply AC.a_call_post_tp; exact Hcp).
    rewrite Eerr, Eoom in Hfk.
    assert (G2 : getr regs2 2 = getr regs1 2) by exact (Hkept 2 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G3 : getr regs2 3 = getr regs1 3) by exact (Hkept 3 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G4 : getr regs2 4 = getr regs1 4) by exact (Hkept 4 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G8 : getr regs2 8 = getr regs1 8) by exact (Hkept 8 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G9 : getr regs2 9 = getr regs1 9) by exact (Hkept 9 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G18 : getr regs2 18 = getr regs1 18) by exact (Hkept 18 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G19 : getr regs2 19 = getr regs1 19) by exact (Hkept 19 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G21 : getr regs2 21 = getr regs1 21) by exact (Hkept 21 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G22 : getr regs2 22 = getr regs1 22) by exact (Hkept 22 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G23 : getr regs2 23 = getr regs1 23) by exact (Hkept 23 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G25 : getr regs2 25 = getr regs1 25) by exact (Hkept 25 ltac:(unfold AC.a_callee_saved; lia)).
    assert (G26 : getr regs2 26 = getr regs1 26) by exact (Hkept 26 ltac:(unfold AC.a_callee_saved; lia)).
    (* a kept byte: not the allocator's before or after, off the window, errno, the flag and the block *)
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
        ~ OWNED (hb1 phi n ++ g_H g) mem1 md1 a -> ~ OWNED (g_H g) mem2 md2 a ->
        ~ (sp - 4096 <= a < sp) -> ~ (0x5db76c <= a < 0x5db76c + 4) -> a <> 0x12aae0 ->
        ~ (phi <= a < phi + n) ->
        mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)).
    { intros a Ha Ho1 Ho2 Hw He Hoo Hnt. apply (Hfk a Ha Ho1 Ho2); [| exact He | exact Hoo | exact Hnt].
      unfold AC.a_window, AC.AK_FREE. rewrite Haspz1. exact Hw. }
    assert (FSPOST : forall a, AC.a_in_fs AC.ASYMS mem1 a -> AC.a_in_fs AC.ASYMS mem2 a).
    { intros a (bb & Hbr & Hwm & Hb). exists bb. split; [exact Hbr|]. split; [|exact Hb].
      intros k Hk. rewrite (Htp16 (Z.of_nat k) ltac:(lia)). exact (Hwm k Hk). }
    (* the side stack lies above the image and below stklo *)
    assert (FSC : forall a, AC.a_in_fs AC.ASYMS mem1 a -> AC.GT <= a < STKLO mem1 md1 /\ app_mem a).
    { intros a (bb & Hbr & Hwm & Hb1 & Hb2).
      destruct (AC.a_laws_fs_place _ _ _ _ _ LAWS _ mem1 md1 bb HAH1 Hwm Hbr) as (Hg & Hfsk & _ & Hfa'').
      split; [lia|]. apply Hfa''. lia. }
    (* a located byte and its shadow are not the allocator's, before or after, and not in the block *)
    assert (LOC : forall a, f37_loc mem1 md1 a ->
        0 <= a < 2 ^ 64 /\ AC.GT <= a /\
        ~ OWNED (hb1 phi n ++ g_H g) mem1 md1 a /\ ~ OWNED (hb1 phi n ++ g_H g) mem1 md1 (shadow_addr a) /\
        ~ OWNED (g_H g) mem2 md2 a /\ ~ OWNED (g_H g) mem2 md2 (shadow_addr a) /\
        ~ (phi <= a < phi + n) /\ ~ (phi <= shadow_addr a < phi + n)).
      { intros a Hl.
      assert (Hpl : AC.in_blocks (hb1 phi n ++ g_H g) a \/ AC.in_slack (hb1 phi n ++ g_H g) a \/
                    AC.a_in_fs AC.ASYMS mem1 a \/ STKLO mem1 md1 <= a < APPMEM_END).
      { destruct Hl as [Hs|[Hfs _]]; [right; right; right; exact Hs | right; right; left; exact Hfs]. }
      assert (Hql : AC.in_blocks (g_H g) a \/ AC.in_slack (g_H g) a \/ AC.a_in_fs AC.ASYMS mem2 a \/
                    STKLO mem2 md2 <= a < APPMEM_END).
      { rewrite Hsk2. destruct Hl as [Hs|[Hfs _]];
          [right; right; right; exact Hs | right; right; left; exact (FSPOST a Hfs)]. }
      destruct (AC.a_laws_not_owned _ _ _ _ _ LAWS _ mem1 md1 a HAH1 Hpl) as (N1 & N2).
      destruct (AC.a_laws_not_owned _ _ _ _ _ LAWS _ mem2 md2 a HAH2 Hql) as (N3 & N4).
      assert (Hr : 0 <= a < 2 ^ 64)
        by (destruct Hl as [Hs|[_ Hs]]; unfold APPMEM_END, AC.GT, HIGHMEM_BEG in *; lia).
      assert (Hgt : AC.GT <= a)
        by (destruct Hl as [Hs|[_ Hs]]; unfold AC.GT, HIGHMEM_BEG in *; lia).
      assert (Happ : app_mem a).
      { destruct Hl as [Hs|[Hfs _]]; [unfold app_mem; right; lia | exact (proj2 (FSC a Hfs))]. }
      split; [exact Hr|]. split; [exact Hgt|].
      split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|].
      split.
      - intros Hin. destruct (Hball a Hin) as (_ & _ & _ & _ & Hnfs).
        destruct Hl as [Hs|[Hfs _]]; [lia | exact (Hnfs Hfs)].
      - intros Hin. destruct (Hball _ Hin) as (Hap & _).
        exact (app_not_shadow _ Hap (shadow_of_app a Happ)). }
    assert (KLOC : forall a, f37_loc mem1 md1 a -> ~ (sp - 4096 <= a < sp) ->
        mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)).
    { intros a Hl Hw. destruct (LOC a Hl) as (Hr & Hg & N1 & _ & N3 & _ & Hnt & _).
      apply KEEP; [exact Hr | exact N1 | exact N3 | exact Hw | unfold AC.GT in Hg; lia
                  | unfold AC.GT in Hg; lia | exact Hnt]. }
    assert (KST : forall a, STKLO mem1 md1 <= a < APPMEM_END -> ~ (sp - 4096 <= a < sp) ->
        mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)).
    { intros a Hs Hw. apply KLOC; [left; exact Hs | exact Hw]. }
    assert (KSH : forall a, f37_loc mem1 md1 a -> app_mem a ->
        mbyte rsegs mem2 (shadow_addr a) = mbyte rsegs mem1 (shadow_addr a)).
    { intros a Hl Hap. destruct (LOC a Hl) as (_ & _ & _ & N2 & _ & N4 & _ & Hnt).
      pose proof (shadow_of_app a Hap) as Hsa1. pose proof (in_shadow_range _ Hsa1) as Hsr.
      unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hsa1.
      refine (proj1 (KEEP _ _ N2 N4 _ _ _ Hnt)); unfold HIGHMEM_BEG, AF.SLOT_STACK in *; lia. }
    (* every frame byte is located and application memory *)
    assert (FRAME : forall a, fr <= a < fr + 3136 -> f37_loc mem1 md1 a /\ app_mem a).
    { intros a Ha. destruct Hloc1 as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
      - pose proof (Hreal a Ha) as Hr. split; [left; exact Hr|]. unfold app_mem. right. lia.
      - destruct (FSC a (Hfs a Ha)) as (Ha1 & Ha2).
        split; [right; split; [exact (Hfs a Ha) | exact Ha1] | exact Ha2]. }
    assert (KFR : forall a, fr <= a < fr + 3136 -> mbyte rsegs mem2 a = mbyte rsegs mem1 a).
    { intros a Ha. destruct (FRAME a Ha) as (Hl & _). exact (proj1 (KLOC a Hl (Hapart a Ha))). }
    assert (KFRSH : forall x, Sfr fr <= x < Sfr fr + 392 -> mbyte rsegs mem2 x = mbyte rsegs mem1 x).
    { intros x Hx.
      assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
      { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
      assert (Ex : x = shadow_addr (fr + 8 * (x - Sfr fr))).
      { unfold shadow_addr at 1. rewrite Hdiv. unfold Sfr, shadow_addr. lia. }
      assert (Hin : fr <= fr + 8 * (x - Sfr fr) < fr + 3136) by lia.
      destruct (FRAME _ Hin) as (Hl & Hap). rewrite Ex. exact (KSH _ Hl Hap). }
    assert (KCL : forall a, 0x5db770 <= a < 0x5fe000 -> AC.in_blocks AC.a_client a ->
        mbyte rsegs mem2 a = mbyte rsegs mem1 a).
    { intros a Ha Hcl. refine (proj1 (KEEP a _ _ _ _ _ _ _)); [lia | | | lia | lia | lia |].
      - exact (proj1 (AC.a_laws_client _ _ _ _ _ LAWS _ mem1 md1 a HAH1) Hcl).
      - exact (proj1 (AC.a_laws_client _ _ _ _ _ LAWS _ mem2 md2 a HAH2) Hcl).
      - intros Hin. destruct (Hball a Hin) as (_ & _ & Hni & _). apply Hni.
        apply (f37_img_seg 0x5db770 0x5fe000); [vm_compute; reflexivity | lia]. }
    (* the shadow byte of a registered global (an image byte) is not the allocator's, before or after *)
    assert (KAG : forall a, in_globals AF.frame_AG a ->
        mbyte rsegs mem2 (shadow_addr a) = mbyte rsegs mem1 (shadow_addr a)).
    { intros a Hin. pose proof (f37_ag_img a Hin) as Himg. pose proof (f37_ag_range a Hin) as Hr.
      assert (Hsa : 0x7fff8000 + 16936 <= shadow_addr a <= 0x7fff8000 + 81693).
      { unfold shadow_addr, ASAN_K.
        pose proof (Z.div_le_mono 0x21140 a 8 ltac:(lia) ltac:(lia)) as D1.
        pose proof (Z.div_le_mono a 0x9f8e8 8 ltac:(lia) ltac:(lia)) as D2.
        change (0x21140 / 8) with 16936 in D1. change (0x9f8e8 / 8) with 81693 in D2. lia. }
      refine (proj1 (KEEP _ _ _ _ _ _ _ _)); [lia | | | lia | lia | lia |].
      - exact (proj1 (proj2 (AC.a_laws_client _ _ _ _ _ LAWS _ mem1 md1 a HAH1)) Himg).
      - exact (proj1 (proj2 (AC.a_laws_client _ _ _ _ _ LAWS _ mem2 md2 a HAH2)) Himg).
      - intros Hin2. destruct (Hball _ Hin2) as (Hap & _).
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap. lia. }
    (* FRA moves to the post state with the empty extra list *)
    assert (HFRA3 : FRA B APIf ra g fr [] regs2 mem2 md2).
    { apply (sl_mid B APIf ra g fr (hb1 phi n) [] regs1 mem1 md1 regs2 mem2 md2
               (fun a => phi <= a < phi + n) AC.AK_FREE HFRA2 Hcp).
      - cbn. lia.
      - destruct Hsn1 as ((Hthm & Hlkm) & Hhdm & Hfd).
        split; [split|split].
        + eapply YI14.val_mem_frame; [|exact Hthm]. intros x Hx. rewrite Hthr in Hx. cbn in Hx. rewrite SEGS.
          apply KCL; [lia|]. exists 0x5db840, 131728. split; [|lia].
          unfold AC.a_client; cbn [In]; repeat (first [left; reflexivity | right]).
        + eapply YI14.val_mem_frame; [|exact Hlkm]. intros x Hx. rewrite Hlock in Hx. cbn in Hx. rewrite SEGS.
          apply KCL; [lia|]. exists 0x5fbad8, 4320. split; [|lia].
          unfold AC.a_client; cbn [In]; repeat (first [left; reflexivity | right]).
        + intros k Hk. rewrite <- (Hhdm k Hk). rewrite SEGS, Hhead.
          apply KCL; [lia|]. exists 0x5fbad8, 4320. split; [|lia].
          unfold AC.a_client; cbn [In]; repeat (first [left; reflexivity | right]).
        + destruct Hmod as (lz & mt & vm' & Emd). rewrite Emd.
          change (m_fds (with_vm_backing lz mt (with_vmmaps vm' md1))) with (m_fds md1). exact Hfd.
      - intros a Hin. pose proof (Hgimg1 a Hin) as E. rewrite SEGS in E |- *. rewrite <- E.
        assert (Har : 0x9e348 <= a < 0xa07c8).
        { destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
          destruct Hil as [Ex|[]]; injection Ex as <- <-; lia. }
        refine (proj1 (KEEP a _ _ _ _ _ _ _)); [lia | | | lia | lia | lia |].
        + intros Ho. exact (proj2 (Hown rc _ _ _ _ Ho) Hin).
        + intros Ho. exact (proj2 (Hown rc _ _ _ _ Ho) Hin).
        + intros Hin2. destruct (Hball _ Hin2) as (_ & _ & Hni & _). apply Hni.
          apply (f37_img_seg 0x9e348 0xa07c8); [vm_compute; reflexivity | lia].
      - unfold q64 in *. apply (f37_bkeep mem1 mem2); [|exact Hhdr11].
        rewrite length_le8. intros x Hx. apply KFR. lia.
      - unfold q64 in *. apply (f37_bkeep mem1 mem2); [|exact Hhdr21].
        rewrite length_le8. intros x Hx. apply KFR. lia.
      - intros A0 HA0 HA0r. unfold q64 in *.
        assert (EA0 : A0 = A) by (apply (f37_reg_eq regs1 9 A0 A HA0 Hr9b HA0r HA64)).
        subst A0. apply (f37_bkeep mem1 mem2); [|exact Hspill1].
        rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(lia) ltac:(lia))).
      - intros A0 HA0 HA0r v Hv. unfold q64 in *.
        assert (EA0 : A0 = A) by (apply (f37_reg_eq regs1 9 A0 A HA0 Hr9b HA0r HA64)).
        subst A0. apply (f37_bkeep mem1 mem2); [|exact Hv].
        rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(lia) ltac:(lia))).
      - intros A0 HA0 HA0r. unfold q64 in *.
        assert (EA0 : A0 = A) by (apply (f37_reg_eq regs1 9 A0 A HA0 Hr9b HA0r HA64)).
        subst A0. apply (f37_bkeep mem1 mem2); [|exact Hfr241].
        rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(lia) ltac:(lia))).
      - destruct Hsh1 as (shl & Hshb & Hshl). exists shl. split; [|exact Hshl].
        apply (f37_bkeep mem1 mem2); [|exact Hshb]. rewrite Hshl. intros x Hx. apply KFRSH. lia.
      - apply (f37_bkeep mem1 mem2); [|exact Hsaved1]. intros x Hx.
        unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx.
        exact (proj1 (KST x ltac:(lia) ltac:(lia))).
      - unfold stk in Hwin1 |- *. destruct Hwin1 as (Hu0 & Hu1 & Hu).
        split; [exact Hu0|]. split; [exact Hu1|]. intros a Ha.
        destruct (Hu a Ha) as (Hwv & bb & Hbb).
        destruct (Z_lt_ge_dec a (sp - 4096)) as [Hlt|Hge]; [|destruct (Z_lt_ge_dec a sp) as [Hlt2|Hge2]].
        + destruct (KST a ltac:(lia) ltac:(lia)) as (Em & Ew).
          split; [exact (proj1 Ew Hwv)|]. exists bb. change (mbyte rsegs mem2 a = Some bb).
          rewrite Em. exact Hbb.
        + assert (Hwa : AC.a_window AC.AK_FREE regs1 a)
            by (unfold AC.a_window, AC.AK_FREE; rewrite Haspz1; lia).
          split; [exact (Hwinw a Hwa)|]. exact (Hwinp a Hwa).
        + destruct (KST a ltac:(lia) ltac:(lia)) as (Em & Ew).
          split; [exact (proj1 Ew Hwv)|]. exists bb. change (mbyte rsegs mem2 a = Some bb).
          rewrite Em. exact Hbb.
      - intros a Hin. apply (f37_addr_bkeep mem1 mem2 a 1 (HAG1 a Hin)).
        intros i Hi. replace (a + i) with a by lia. exact (KAG a Hin).
      - intros a Ha Hnf. apply (f37_addr_bkeep mem1 mem2 a 1 (HWA1 a Ha Hnf)).
        intros i Hi. replace (a + i) with a by lia. apply KSH; [left; lia | unfold app_mem; right; lia].
      - (* the side-arm frame record *)
        intros (FS2 & jj & Hwtp & HFSr2 & Hjj & Hfreq & Hflag & Hlast).
        assert (HfsB : SMC.fs_B 6 = 4096) by reflexivity.
        assert (HfsM : SMC.fs_M 6 = 256) by reflexivity.
        assert (Hfrlo : FS2 + 36864 + 6 * 2 ^ 20 <= fr) by (rewrite Hfreq; unfold SMC.fs_frame; lia).
        assert (Hfrhi : fr + SMC.fs_B 6 <= FS2 + AC.FS_SIZE)
          by (rewrite Hfreq; unfold SMC.fs_frame; rewrite HfsB in *; rewrite HfsM in Hjj;
              unfold AC.FS_SIZE; lia).
        assert (Hflr : FS2 <= SMC.fs_flag FS2 6 jj < FS2 + AC.FS_SIZE)
          by (unfold SMC.fs_flag; rewrite HfsM in Hjj; unfold AC.FS_SIZE; lia).
        assert (Hwtp' : word_mem rsegs mem2 (AC.as_tp AC.ASYMS) FS2).
        { intros k Hk. rewrite (Htp16 (Z.of_nat k) ltac:(lia)). exact (Hwtp k Hk). }
        exists FS2, jj.
        split; [exact Hwtp'|]. split; [exact HFSr2|]. split; [exact Hjj|]. split; [exact Hfreq|].
        split.
        + apply (f37_bkeep mem1 mem2); [|exact Hflag]. cbn [length Z.of_nat]. intros x Hx.
          assert (Hxfs : AC.a_in_fs AC.ASYMS mem1 x)
            by (apply (a_fs_in AC.ASYMS mem1 FS2 x Hwtp HFSr2); lia).
          destruct (FSC x Hxfs) as (Hxb & _).
          apply KLOC; [right; split; [exact Hxfs | exact Hxb] | lia].
        + apply (f37_bkeep mem1 mem2); [|exact Hlast]. rewrite length_le8. intros x Hx.
          assert (Hxfs : AC.a_in_fs AC.ASYMS mem1 x)
            by (apply (a_fs_in AC.ASYMS mem1 FS2 x Hwtp HFSr2); lia).
          destruct (FSC x Hxfs) as (Hxb & _).
          apply KLOC; [right; split; [exact Hxfs | exact Hxb] | lia].
      - exact G2.
      - exact G3.
      - exact G4.
      - exact G8.
      - exact G9.
      - exact G19.
      - exact G26. }
    (* ENT moves to the post state *)
    assert (HENT3 : ENT APIf g [] mem2 md2).
    { apply (ent_call B APIf ra g fr (hb1 phi n) [] regs1 mem1 md1 regs2 mem2 md2
               (fun a => phi <= a < phi + n) AC.AK_FREE HENT2 HFRA2 Hcp
               ltac:(unfold AC.AK_FREE, FN_STACK, AF.SLOT_STACK; lia)).
      - intros a Hta. destruct (Hball a Hta) as (Hap & _ & Hnimg & _).
        split; [exact Hap|]. split; [lia|]. split; [exact Hnimg|].
        intros (q0 & k0 & Hin0 & Hr0).
        destruct (AC.a_laws_disjoint _ _ _ _ _ LAWS [] (g_H g) mem1 md1 phi n q0 k0 HAH1 Hin0); lia.
      - exact Herrk. }
    (* ---- the exit cut ---- *)
    rewrite <- SEGS. apply Hexit.
    exists phi, regs2, mem2, md2, fr.
    split; [reflexivity|].
    split; [exact HFRA3|].
    split; [exact HENT3|].
    split; [exact Hgn|].
    assert (KFR0 : forall x, fr <= x < fr + 3136 -> mbyte rsegs mem1 x = mbyte rsegs mem x).
    { intros x Hx. pose proof (Hfrapp x Hx) as Hap. pose proof (HWapp x Hap) as Hout.
      cbn [outside] in Hout.
      apply Hkeep0; [unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap; lia
                    | exact (proj1 Hout)]. }
    split.
    { destruct HLK as (Hj255 & Hreg21 & HOUR). split; [exact Hj255|].
      split; [unfold rg in *; rewrite G21, F21; exact Hreg21|].
      unfold OURb in *. apply (f37_bkeep mem1 mem2).
      - rewrite OUR_length. intros x Hx. apply KFR. lia.
      - apply (f37_bkeep mem mem1); [|exact HOUR].
        rewrite OUR_length. intros x Hx. apply KFR0. lia. }
    (* FLSF *)
    assert (KA : forall off v, spill regs mem off v -> 0 <= off <= 304 -> spill regs2 mem2 off v).
    { intros off v (A0 & HA0 & Hq) Hoff.
      assert (EA0 : A0 = A).
      { pose proof Hq as Hqb. unfold q64 in Hqb. apply bytes_at_bound in Hqb. rewrite length_le8 in Hqb.
        apply (f37_rg_near regs 9 A A0 Hr9 HA0); lia. }
      subst A0. exists A. split; [unfold rg in *; rewrite G9, F9; exact Hr9|].
      unfold q64 in *. apply (f37_bkeep mem1 mem2).
      - rewrite length_le8. intros x Hx. exact (proj1 (KST x ltac:(lia) ltac:(lia))).
      - apply (f37_bkeep mem mem1); [|exact Hq].
        rewrite length_le8. intros x Hx. apply Hkeep0; lia. }
    assert (KFRT : forall x, fr <= x < fr + 3136 -> mbyte rsegs mem2 x = mbyte rsegs mem x)
      by (intros x Hx; rewrite (KFR x Hx); exact (KFR0 x Hx)).
    (* a byte of a live block of the entry heap and its shadow byte are kept by the stores and the free *)
    assert (KBLK : forall a, AC.in_blocks (g_H g) a ->
        mbyte rsegs mem2 a = mbyte rsegs mem a /\
        mbyte rsegs mem2 (shadow_addr a) = mbyte rsegs mem (shadow_addr a)).
    { intros a Hb. pose proof Hb as (p0 & k0 & Hin0 & Hr0).
      assert (Hin1 : In (p0, k0) (hb1 phi n ++ g_H g)) by (apply in_or_app; right; exact Hin0).
      destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem1 md1 p0 k0 HAH1 Hin1) as (_ & _ & Hpk & _ & Hbb).
      destruct (Hbb a Hr0) as (Hap & _ & Hnimg & _ & _).
      assert (Hb1 : AC.in_blocks (hb1 phi n ++ g_H g) a) by (exists p0, k0; split; [exact Hin1 | exact Hr0]).
      destruct (AC.a_laws_not_owned _ _ _ _ _ LAWS _ mem1 md1 a HAH1 (or_introl Hb1)) as (N1 & N2).
      destruct (AC.a_laws_not_owned _ _ _ _ _ LAWS _ mem2 md2 a HAH2 (or_introl Hb)) as (N3 & N4).
      assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap; lia).
      assert (Hne : ~ (0x5db76c <= a < 0x5db76c + 4)) by (intros He; apply Hnimg; apply f37_errno_img; lia).
      assert (Hno : a <> 0x12aae0) by (intros ->; exact (Hnimg f37_oom_img)).
      assert (Hnt : ~ (phi <= a < phi + n)).
      { intros Ht. destruct (AC.a_laws_disjoint _ _ _ _ _ LAWS [] (g_H g) mem1 md1 phi n p0 k0 HAH1 Hin0); lia. }
      assert (Hnf : ~ (fr <= a < fr + 3136))
        by (intros Hf; exact (f37_fra_blk g fr (hb1 phi n) regs mem md p0 k0 a HFRA Hin1 Hr0 Hf)).
      pose proof (shadow_of_app a Hap) as Hsa. pose proof (in_shadow_range _ Hsa) as Hsr.
      assert (Hsnt : ~ (phi <= shadow_addr a < phi + n)).
      { intros Hin. destruct (Hball _ Hin) as (Hap' & _). exact (app_not_shadow _ Hap' Hsa). }
      (* the block lies below stklo, and stklo lies 2^20 below the entry sp, so below the free's window *)
      assert (Hwnd : ~ (sp - 4096 <= a < sp)).
      { assert (Hpk' : p0 + k0 <= STKLO mem1 md1) by exact Hpk.
        assert (Hst' : STKLO mem1 md1 <= g_S g - AF.SLOT_STACK) by exact Hstklo1.
        rewrite HSS in Hst'. lia. }
      split.
      - rewrite (proj1 (KEEP a Ha64 N1 N3 Hwnd Hne Hno Hnt)).
        pose proof (HWapp a Hap) as Hout. cbn [outside] in Hout.
        apply Hkeep0; [exact Ha64 | exact (proj1 Hout)].
      - unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG in Hsa.
        rewrite (proj1 (KEEP (shadow_addr a) ltac:(lia) N2 N4 ltac:(unfold HIGHMEM_BEG, AF.SLOT_STACK in *; lia)
                   ltac:(lia) ltac:(lia) Hsnt)).
        pose proof (HWsh a ltac:(lia) Hnf) as Hout. cbn [outside] in Hout.
        apply Hkeep0; [lia | exact (proj1 Hout)]. }
    (* a frame range in [fr + 2624, fr + 3136) stays addressable: its shadow bytes lie in [S(fr) + 328, S(fr) + 392),
       off the stores' range [S(fr) + 22, S(fr) + 67) and kept by the free (KFRSH) *)
    assert (KADR : forall o k, addressable mem (fr + o) k -> 2624 <= o -> o + k <= 3136 ->
                     addressable mem2 (fr + o) k).
    { intros o k Ha Ho Hk. apply (f37_addr_bkeep mem1 mem2).
      - apply (f37_addr_keep [(Sfr fr + 22, Sfr fr + 22 + 45)] mem mem1 (fr + o) k Ha MU).
        intros i Hi. cbn [outside]. split; [|exact I].
        assert (Hge : Sfr fr + 328 <= shadow_addr (fr + o + i)).
        { unfold Sfr, shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
        lia.
      - intros i Hi. apply KFRSH.
        assert (Hlo2 : Sfr fr + 328 <= shadow_addr (fr + o + i))
          by (unfold Sfr, shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
        assert (Hhi2 : shadow_addr (fr + o + i) < Sfr fr + 392)
          by (unfold Sfr, shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
        lia. }
    assert (HFLSI2 : FLSI g j fr regs2 mem2).
    { (* v1.9: PRO's [A + 200] is [A + 208] and PRO gains [A + 32] = fr + 2880 last (P32); FLC's slots are
         renumbered (208 / 64 / 72 / 80 / 56 / 48 -> 192 / 80 / 88 / 96 / 72 / 64) and FLC gains [A + 56] = fr + 2889
         and [A + 48] = fr + 2890 last. *)
      destruct HFLSI as (((P40 & P120 & P136 & P160 & P168 & P176 & P208 & P248 & Padr & Pbytes & Pin &
                           P184 & P256 & P264 & P272 & P32) & Q128 & Qstk & Q144 & Qadr2) &
                         Q216 & Q224 & Q248 & HIN &
                         (C256 & C184 & C192 & C80 & C88 & C96 & C272 & C264 & Cfrag & C2688 & C72 & C64 &
                          C56 & C48)).
      destruct HIN as (HinH & HaddrIN & HbytesIN).
      (* the harness block's bytes and shadow: a live block of the entry heap (for 0 < n), kept by KBLK *)
      assert (Hlen_in : Z.of_nat (length (g_in g)) = g_n g) by reflexivity.
      assert (KIN : bytes_at rsegs mem (g_p g) (g_in g) -> bytes_at rsegs mem2 (g_p g) (g_in g)).
      { intros Hb. apply (f37_bkeep mem mem2); [|exact Hb].
        intros x Hx. refine (proj1 (KBLK _ _)). exists (g_p g), (g_n g).
        split; [exact (HinH ltac:(lia)) | lia]. }
      assert (KINA : addressable mem (g_p g) (g_n g) -> addressable mem2 (g_p g) (g_n g)).
      { intros Ha. apply (f37_addr_bkeep mem mem2 (g_p g) (g_n g) Ha).
        intros i Hi. refine (proj2 (KBLK _ _)). exists (g_p g), (g_n g).
        split; [exact (HinH ltac:(lia)) | lia]. }
      split.
      { (* FLSH *)
      split.
      { (* PRO *)
      split; [exact (KA 40 _ P40 ltac:(lia))|].
      split; [exact (KA 120 _ P120 ltac:(lia))|].
      split; [exact (KA 136 _ P136 ltac:(lia))|].
      split; [exact (KA 160 _ P160 ltac:(lia))|].
      split; [exact (KA 168 _ P168 ltac:(lia))|].
      split; [exact (KA 176 _ P176 ltac:(lia))|].
      split; [exact (KA 208 _ P208 ltac:(lia))|].
      split; [exact (KA 248 _ P248 ltac:(lia))|].
      split; [exact (KADR 2624 6 Padr ltac:(lia) ltac:(lia))|].
      split; [exact (KIN Pbytes)|].
      split; [intros Hn; destruct (Pin Hn) as (PH & Pa); split; [exact PH | exact (KINA Pa)]|].
      (* push 14D: A4's [A+184] / [A+256] / [A+264] / [A+272] *)
      split; [exact (KA 184 _ P184 ltac:(lia))|].
      split; [exact (KA 256 _ P256 ltac:(lia))|].
      split; [exact (KA 264 _ P264 ltac:(lia))|].
      (* v1.9: A4's [A+32] = fr + 2880 *)
      split; [exact (KA 272 _ P272 ltac:(lia)) | exact (KA 32 _ P32 ltac:(lia))]. }
      split; [exact (KA 128 _ Q128 ltac:(lia))|].
      split.
      { apply (f37_stk_keep mem1 mem2 fr (fr + 3136)).
        + apply (f37_stk_tr [(Sfr fr + 22, Sfr fr + 22 + 45)] mem mem1 fr (fr + 3136) Qstk MU WM).
          intros x Hx. left. apply HWapp. apply Hfrapp. exact Hx.
        + intros x Hx. exact (KFR x Hx).
        + intros x Hx Hw. destruct (FRAME x Hx) as (Hl & _).
          exact (proj1 (proj2 (KLOC x Hl (Hapart x Hx))) Hw). }
      (* push 12A: [A+144] = fr + 2688 and the 17 bytes at fr + 2691 *)
      split; [exact (KA 144 _ Q144 ltac:(lia)) | exact (KADR 2691 17 Qadr2 ltac:(lia) ltac:(lia))]. }
      split; [exact (KA 216 _ Q216 ltac:(lia))|].
      split; [exact (KA 224 _ Q224 ltac:(lia))|].
      split; [exact (KA 248 _ Q248 ltac:(lia))|].
      split.
      { (* f1_IN *)
        split; [exact HinH|]. split; [exact (KINA HaddrIN) | exact (KIN HbytesIN)]. }
      (* FLC (push 14D / 14E): the spills by KA; the two record ranges by KADR (their shadow bytes lie in
         [S(fr) + 336, S(fr) + 355), off the stores' range and kept by the free) *)
      split; [exact (KA 256 _ C256 ltac:(lia))|].
      split; [exact (KA 184 _ C184 ltac:(lia))|].
      split; [exact (KA 192 _ C192 ltac:(lia))|].
      split; [exact (KA 80 _ C80 ltac:(lia))|].
      split; [exact (KA 88 _ C88 ltac:(lia))|].
      split; [exact (KA 96 _ C96 ltac:(lia))|].
      split; [exact (KA 272 _ C272 ltac:(lia))|].
      split; [exact (KA 264 _ C264 ltac:(lia))|].
      split; [exact (KADR 2768 72 Cfrag ltac:(lia) ltac:(lia))|].
      split; [exact (KADR 2688 38 C2688 ltac:(lia) ltac:(lia))|].
      split; [exact (KA 72 _ C72 ltac:(lia))|]. split; [exact (KA 64 _ C64 ltac:(lia))|].
      (* v1.9: P12's [A+56] = fr + 2889 and [A+48] = fr + 2890 *)
      split; [exact (KA 56 _ C56 ltac:(lia)) | exact (KA 48 _ C48 ltac:(lia))]. }
    split.
    { (* FLSF *)
      split; [exact HFLSI2|].
      split; [unfold rg in *; rewrite G18, F18; exact H18|].
      split; [unfold rg in *; rewrite G22, F22; exact H22|].
      split; [unfold rg in *; rewrite G23, F23; exact H23|].
      split; [unfold rg in *; rewrite G25, F25; exact H25|].
      split; [intros H50; destruct (Hrec H50) as (Hp0 & Hp1 & _); split; [exact Hp0 | exact Hp1]|].
      split; [exact (KA 152 _ Hs152 ltac:(lia)) | exact (KA 280 _ Hs280 ltac:(lia))]. }
    (* LT = IFS g fr (S j), handed on: the frame records by KFRT, the first-fragment spills by KA; v1.9 FSb: the
       body bytes at fr + 2880 (at most 23, f37_fs_body_len) by KFRT and their 35 addressable bytes by KADR *)
    { destruct HLT as ((HIDb & HIDok) & (HFGb & HFGok) & (Q104 & Q112 & Qbody & Qad & HFI)).
      split; [split; [|exact HIDok]|].
      - unfold IDBe in *. apply (f37_bkeep mem mem2); [|exact HIDb].
        pose proof (f37_ID_len (g_in g) (S j)) as EL. unfold ID_SIZE in EL.
        intros x Hx. apply KFRT. lia.
      - split; [split; [|exact HFGok]|].
        + unfold FGBe in *. apply (f37_bkeep mem mem2); [|exact HFGb].
          pose proof (f37_FG_len (g_in g) (S j)) as EL.
          intros x Hx. apply KFRT. lia.
        + split; [exact (KA 104 _ Q104 ltac:(lia))|]. split; [exact (KA 112 _ Q112 ltac:(lia))|].
          split.
          * apply (f37_bkeep mem mem2); [|exact Qbody].
            pose proof (f37_fs_body_len (g_in g) (S j)) as EL.
            intros x Hx. apply KFRT. lia.
          * split; [exact (KADR 2880 35 Qad ltac:(lia) ltac:(lia)) | exact HFI]. }
Qed.

End F37.
(* b8refit: applied map b8refit-v190.tsv sha256=7153b913f625df27 kinds=frame,pc,slot. Do not apply it again. *)
