(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1392 of its 1502 lines of code are new or changed and 901 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R14.v, with its module paths, module names, addresses and numbers changed; 541 of its 632 lines of code are new or changed and 1411 lines of the source are left out. *)
(* Segment R20 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): Inv_A818e8 -> Inv_A81924.
   At 0x818e8 the result register a0 of the bcmp wrapper is 0, so `beqz a0,818f0` is taken and 0x818ec (the `j` to
   before_abort) is NOT reached.  0x818f0 sets a0 := -8 and the six 1-byte stores 0x818f4 .. 0x81908 put 0xf8 into
   the frame's own shadow bytes S(fr) + 316, + 317, + 320 .. + 323 (s3 = S(fr)); 0x8190c `j 8191c` then reaches the
   free call, which the shared continuation R15.r_free_cont runs.
   The write set is [S(fr) + 316, S(fr) + 324), a range of the frame's 392 shadow bytes:
   - FRA moves with Tac_slot.sl_fr_meta, whose heap-invariant premise comes from r20_ah (real arm a_laws_store,
     side arm a_laws_fs_store with Tac_fs.a_fs_ok_pres: every side-stack metadata cell is application memory and a
     shadow byte never is);
   - ENT moves with Tac_slot.ent_store (every written byte is one of the frame's own shadow bytes);
   - the frame byte runs (OURb, the id and fragment records), the spills at [A + 32 .. A + 256), the addressable
     id record (38 bytes) and PRO (our[]'s 6 bytes and the input block, its bytes and its addressability) are
     kept, since application memory, the spill base A (at or above HIGHMEM_BEG) and the shadow bytes of
     [fr + 2176, fr + 2214) (= S(fr) + 272 .. + 276), of [fr + 2624, fr + 2630) (= S(fr) + 328) and of the input
     block (a heap block, apart from the frame) are all outside the write set;
   - OUTA (out[]'s 1492 bytes at fr + 544 addressable) is kept by Tac_slot.outa_munch: out[]'s shadow bytes are
     S(fr) + 68 .. + 254, below the write set. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac
  Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
Import ListNotations.
Open Scope Z_scope.

(* ===== The run 0x818e8 .. 0x8191c ===== *)

(* A present, writable byte run gives store_ok for each of its bytes. *)
Lemma r20_stk_store_ok : forall m lo hi a, stk rsegs m lo hi -> lo <= a -> a + 1 <= hi ->
  store_ok rsegs m (wa a) 1%nat = true.
Proof.
  intros m lo hi a (H1 & H2 & H) Hlo Hhi.
  assert (WR : wr_at rsegs m a 1).
  { split; [lia|]. split; [lia|]. intros i Hi. assert (Ei : i = 0) by lia. subst i.
    rewrite Z.add_0_r. exact (proj1 (H a ltac:(lia))). }
  pose proof (wr_at_store_ok rsegs m a 1 0 1%nat WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

(* One shadow store `sb a0,off(s3)`, with the munch / stk / wmono bookkeeping. *)
Ltac r20_sb SHv off STh MUh WMh :=
  let HS := fresh "HSok" in
  (lazymatch goal with
   | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
       assert (HS : store_ok rsegs mm (wa (SHv + off)) 1%nat = true)
         by (apply (r20_stk_store_ok mm (SHv + 316) (SHv + 324) (SHv + off) STh); lia)
   end);
  step;
  (lazymatch goal with
   | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?aa ?bs) _) =>
       apply (munch_write [(SHv + 316, SHv + 324)] _ mm (SHv + off) bs) in MUh;
         [ | lia
           | rewrite length_le1; cbn [Z.of_nat]; lia
           | rewrite length_le1; cbn [inside Z.of_nat]; left; lia ];
       apply (stk_write rsegs mm (SHv + 316) (SHv + 324) (SHv + off) bs) in STh;
         [ | lia | rewrite length_le1; cbn [Z.of_nat]; lia ];
       apply (wmono_write rsegs _ mm aa bs) in WMh
   end);
  clear HS.

(* 0x818e8 beqz a0,818f0 (a0 = 0, taken) ; 0x818f0 li a0,-8 ; the six shadow stores ; 0x8190c j 8191c. *)
Lemma r20_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SHv : Z),
    a0 = Z_to_bv 64 0 -> s3 = Z_to_bv 64 SHv -> 0 <= SHv -> SHv + 324 <= 2 ^ 64 ->
    stk rsegs m (SHv + 316) (SHv + 324) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x8191c) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 24 = s8 /\
         getr R 25 = s9 /\ getr R 26 = s10 /\
         munch [(SHv + 316, SHv + 324)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (SHv + 316) (SHv + 324))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x818e8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m SHv -> -> HS0 HS1 ST.
  pose proof (munch_refl [(SHv + 316, SHv + 324)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. if_true.                           (* 818e8 beqz a0,818f0 *)
  step.                                    (* 818f0 li a0,-8 *)
  r20_sb SHv 322 ST MU WM.                 (* 818f4 sb a0,322(s3) *)
  r20_sb SHv 323 ST MU WM.                 (* 818f8 sb a0,323(s3) *)
  r20_sb SHv 316 ST MU WM.                 (* 818fc sb a0,316(s3) *)
  r20_sb SHv 317 ST MU WM.                 (* 81900 sb a0,317(s3) *)
  r20_sb SHv 320 ST MU WM.                 (* 81904 sb a0,320(s3) *)
  r20_sb SHv 321 ST MU WM.                 (* 81908 sb a0,321(s3) *)
  step.                                    (* 8190c j 8191c *)
  apply evt_done. do 2 eexists. split; [reflexivity|].
  do 12 (split; [reflexivity|]).
  split; [exact MU|]. split; [exact WM | exact ST].
Qed.

(* ===== seg_R20 ===== *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YK1j YN2e.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_rt_b2 Tac_rt2_b2 Tac_fs
  R15.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require B3Rtm.
(* Qualified: R15 requires BzBridge / KindBGlue, which load the image-independent lib/Reusable/YK11; after that a
   bare `Import YK11` is that one, whose getr / mkst / FPState are NOT the ones the cuts are built over. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module AC20 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF20 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

(* The frame's shadow byte at offset k is the shadow of the frame byte at offset 8 k. *)
Lemma r20_shadow_off : forall fr k, 0 <= k -> shadow_addr (fr + k * 8) = Sfr fr + k.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr k Hk. unfold Sfr, shadow_addr. rewrite Z.div_add by lia. lia.
Qed.

(* The A image's loaded segments all end at or below 0x5fe000 (= GT), so every read-only address is below it
   (A/Prog/Seg/R17.v r17_hull / r17_ro_lt / r17_ro_keep). *)
Lemma r20_hull : forall s, In s rsegs -> Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 6283264.
Proof.
  assert (H : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 6283264) rsegs = true)
    by (vm_compute; reflexivity).
  intros s Hin. apply Z.leb_le. rewrite forallb_forall in H. exact (H s Hin).
Qed.

Lemma r20_ro_lt : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < 6283264.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  pose proof (YK1j.find_segment_in rsegs (bv_unsigned a) 1 s E) as Hin.
  pose proof (YK1j.find_segment_range rsegs (bv_unsigned a) 1 s E) as (_ & Hhi).
  pose proof (r20_hull s Hin) as Hb. lia.
Qed.

(* ro_agree is kept by a store whose write set avoids every read-only address. *)
Lemma r20_ro_keep : forall (mem mem' : word -> option byte) (W : list Frame.ivl),
  ro_agree rsegs mem -> Frame.munch W mem mem' ->
  (forall a : word, ro_addr rsegs a = true -> Frame.outside W (bv_unsigned a)) ->
  ro_agree rsegs mem'.
Proof.
  intros mem mem' W HRO MU Hout a Hro. unfold mrd. rewrite (MU a (Hout a Hro)). exact (HRO a Hro).
Qed.


(* Two word_mem values at the same address agree mod 2 ^ 64 (A/Prog/Seg/P2.v p2_wm_congr). *)
Lemma r20_wm_congr : forall (m : word -> option byte) a v1 v2,
  word_mem rsegs m a v1 -> word_mem rsegs m a v2 -> v1 mod 2^64 = v2 mod 2^64.
Proof.
  intros m a v1 v2 H1 H2.
  assert (Hb : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2.
    rewrite E1 in E2.
    assert (E2' : Z_to_bv 8 (le_byte v1 8 k) = Z_to_bv 8 (le_byte v2 8 k)) by congruence.
    apply (f_equal (@bv_unsigned 8)) in E2'. rewrite !KindBGlue.kb_byte_unsigned in E2'. exact E2'. }
  apply Z.bits_inj'. intros j Hj.
  destruct (Z.ltb_spec j 64) as [Hlt|Hge].
  - set (k := Z.to_nat (j / 8)).
    assert (Hk8 : (k < 8)%nat) by (unfold k; apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      apply Z.div_lt_upper_bound; lia).
    pose proof (Hb k Hk8) as Hbk.
    assert (Hoff : 8 * Z.of_nat k + (j - 8 * Z.of_nat k) = j) by lia.
    assert (Hjk : j - 8 * Z.of_nat k = j mod 8) by (unfold k; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      rewrite (Z.div_mod j 8) at 1 by lia; lia).
    assert (Hoff8 : 0 <= j - 8 * Z.of_nat k < 8) by (rewrite Hjk; apply Z.mod_pos_bound; lia).
    assert (HT : Z.testbit (le_byte v1 8 k) (j - 8 * Z.of_nat k)
               = Z.testbit (le_byte v2 8 k) (j - 8 * Z.of_nat k)) by (rewrite Hbk; reflexivity).
    rewrite !le_byte_testbit in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ 8)) in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) in HT by lia.
    rewrite Hoff in HT.
    rewrite !Z.testbit_mod_pow2 by lia.
    rewrite (proj2 (Z.ltb_lt j 64)) by lia. exact HT.
  - rewrite !Z.testbit_mod_pow2 by lia. rewrite (proj2 (Z.ltb_ge j 64)) by lia. reflexivity.
Qed.

(* Every side-stack metadata cell lies in [FS, FS + 36864) (A/Prog/Seg/P2.v p2_fs_meta_range). *)
Lemma r20_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold AC20.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* n present bytes form a byte run. *)
Lemma r20_bytes_of_present : forall (n : nat) (m : word -> option byte) a,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall k, (k < n)%nat -> exists b, mrd rsegs m (wa (a + Z.of_nat k)) = Some b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros m a Ha Hn H.
  - exists []. split; [|reflexivity]. split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi. lia.
  - destruct (H 0%nat ltac:(lia)) as (b & Hb). replace (a + Z.of_nat 0) with a in Hb by lia.
    destruct (IH m (a + 1) ltac:(lia) ltac:(lia)) as (bs & HBs & HL).
    { intros k Hk. replace (a + 1 + Z.of_nat k) with (a + Z.of_nat (S k)) by lia. apply H. lia. }
    exists (b :: bs). split; [|cbn [length]; lia].
    change (b :: bs) with ([b] ++ bs).
    apply (proj2 (bytes_at_app rsegs m a [b] bs)). split.
    + split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
      intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i.
      replace (a + Z.of_nat 0) with a by lia. cbn [nth_error]. exact Hb.
    + cbn [length]. replace (a + Z.of_nat 1) with (a + 1) by lia. exact HBs.
Qed.

(* ADDR-KEEP for a run whose write set misses the shadow bytes of the range. *)
Lemma r20_addr_keep_rng : forall m m' W p n,
  addressable m p n -> Frame.munch W m m' ->
  (forall i, 0 <= i < n -> Frame.outside W (shadow_addr (p + i))) ->
  addressable m' p n.
Proof.
  intros m m' W p n HA MU HO. pose proof HA as (H1 & H2 & H3 & H).
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  pose proof (shadow_of_app (p + i) Ha) as IS. pose proof (in_shadow_range _ IS) as IR.
  unfold mrd in Hb |- *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite Mem.wa_unsigned by lia. exact (HO i Hi).
Qed.

(* One CB cell's rw_cells across a run whose write set W misses the cell's bytes. *)
Lemma r20_rwcb_keep : forall W (m m' : word -> option byte) a n bs,
  Frame.munch W m m' -> Frame.wmono rsegs m m' ->
  (forall x, a <= x < a + Z.of_nat n -> Frame.outside W x) ->
  rw_cells rsegs m a [CB n bs] -> rw_cells rsegs m' a [CB n bs].
Proof.
  intros W m m' a n bs MU WM HO ((Hwf & Hb) & Hw).
  assert (Hlen : length bs = n) by (destruct Hwf as (Hl & _); exact Hl).
  split; [split; [exact Hwf|]|].
  - apply (a_keep W m m' a _ MU); [|exact Hb]. intros x Hx.
    cbn [cells_bytes cbytes] in Hx. rewrite app_nil_r, Hlen in Hx. exact (HO x Hx).
  - destruct Hw as (Hw0 & Hw1 & Hw). split; [exact Hw0|]. split; [exact Hw1|].
    intros i Hi. exact (WM _ (Hw i Hi)).
Qed.

(* Every registered global of frame_AG lies below GT. *)
Definition r20_AGb : bool :=
  forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? 6283264)) AF20.frame_AG.

Lemma r20_AG_lt : forall a, in_globals AF20.frame_AG a -> 0 <= a < 6283264.
Proof.
  intros a (lo & len & Hin & Hr).
  assert (HB : r20_AGb = true) by (vm_compute; reflexivity).
  unfold r20_AGb in HB. rewrite forallb_forall in HB. specialize (HB _ Hin).
  apply andb_true_iff in HB as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [fst snd] in H1, H2. lia.
Qed.

(* Two representatives of register 9 that are both 64-bit values are equal. *)
Lemma r20_A_eq : forall (regs : bvmap 5 word) (A0 Af : Z),
  getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 -> rg regs 9 Af -> 0 <= Af < 2 ^ 64 -> A0 = Af.
Proof.
  intros regs A0 Af H0 HA0 HAf HAfr. unfold rg in HAf. rewrite HAf in H0.
  apply (f_equal (@bv_unsigned 64)) in H0. rewrite !MState.unsigned_lit in H0 by lia. lia.
Qed.

Section R20W.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC20.AsanAllocAPI AC20.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Local Notation API := (APIf rc).

(* The allocator laws whose inner lists this file takes apart (Contract.v, a Theorem Labs lane's v1.9 generation), each restated
   once here, so that a law that gains or moves a conjunct breaks this one proof and no use site (a Theorem Labs lane 15:32Z). *)
Local Notation law_AH := (AC20.aa_AH AC20.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_own := (AC20.aa_owned AC20.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_lo := (AC20.aa_stklo AC20.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_hi := (AC20.aa_stkhi AC20.ASYMS AsanRTInv.RT (APIf rc)).

Lemma r20_law_blocks : forall H mem md p n, law_AH H mem md -> In (p, n) H ->
  p mod 16 = 0 /\ 4096 <= p /\ p + n <= law_lo mem md /\ end_in_app p n /\
  forall a, p <= a < p + n -> app_mem a /\ writable_at rsegs mem a /\ ~ AC20.a_in_img a /\ ~ AC20.a_on_img_page a /\
    ~ AC20.a_in_fs AC20.ASYMS mem a.
Proof. exact (AC20.a_laws_blocks _ _ _ _ _ (AC20.aa_laws AC20.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r20_law_fs_place : forall H mem md b, law_AH H mem md -> word_mem rsegs mem (AC20.as_tp AC20.ASYMS) b -> 0 <= b < 2 ^ 64 ->
  AC20.GT <= b /\ b + AC20.FS_SIZE <= law_lo mem md /\ b mod 4096 = 0 /\ forall a, b <= a < b + AC20.FS_SIZE -> app_mem a.
Proof. exact (AC20.a_laws_fs_place _ _ _ _ _ (AC20.aa_laws AC20.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r20_law_fs_ok : forall H mem md FS, law_AH H mem md -> word_mem rsegs mem (AC20.as_tp AC20.ASYMS) FS ->
  0 <= FS < 2 ^ 64 -> AC20.a_fs_ok mem FS.
Proof.
  intros H mem md FS HAH Hw Hb.
  exact (proj1 (AC20.a_laws_fs_state _ _ _ _ _ (AC20.aa_laws AC20.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw Hb)).
Qed.

Lemma r20_law_store : forall H mem mem' md, law_AH H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC20.a_store_ok H (law_lo mem md) a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  law_AH H mem' md /\ (forall a, law_own H mem' md a <-> law_own H mem md a) /\ law_lo mem' md = law_lo mem md /\
  law_hi mem' md = law_hi mem md.
Proof. exact (AC20.a_laws_store _ _ _ _ _ (AC20.aa_laws AC20.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r20_law_fs_store : forall H mem mem' md FS, law_AH H mem md -> word_mem rsegs mem (AC20.as_tp AC20.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC20.a_store_ok H (law_lo mem md) a -> ~ (FS <= a < FS + AC20.FS_SIZE) ->
     ~ (exists b, FS <= b < FS + AC20.FS_SIZE /\ a = shadow_addr b) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) -> AC20.a_fs_ok mem' FS ->
  law_AH H mem' md /\ (forall a, law_own H mem' md a <-> law_own H mem md a) /\ law_lo mem' md = law_lo mem md /\
  law_hi mem' md = law_hi mem md.
Proof. exact (AC20.a_laws_fs_store _ _ _ _ _ (AC20.aa_laws AC20.ASYMS AsanRTInv.RT (APIf rc))). Qed.

(* The heap invariant, the ownership and the real stack's bounds across a write of a range of the frame's own 392
   shadow bytes: on the real arm every written byte is the shadow of a byte of the real stack (a_store_ok), on the
   side arm it is the shadow of a byte of the side stack, whose metadata cells are application memory and so are
   not shadow bytes (a_laws_fs_store with Tac_fs.a_fs_ok_pres). *)
Lemma r20_ah : forall g fr hb regs mem mem' md (lo hi : Z),
  FRA B APIf ra g fr hb regs mem md ->
  0 <= lo -> lo <= hi -> hi <= FRAME_SHADOW ->
  Frame.munch [(Sfr fr + lo, Sfr fr + hi)] mem mem' ->
  Frame.wmono rsegs mem mem' ->
  (forall q, Sfr fr + lo <= q < Sfr fr + hi -> exists b, mrd rsegs mem' (wa q) = Some b) ->
  AC20.aa_AH AC20.ASYMS AsanRTInv.RT API (hb ++ g_H g) mem' md /\
  (forall a, AC20.aa_owned AC20.ASYMS AsanRTInv.RT API (hb ++ g_H g) mem' md a <->
             AC20.aa_owned AC20.ASYMS AsanRTInv.RT API (hb ++ g_H g) mem md a) /\
  AC20.aa_stklo AC20.ASYMS AsanRTInv.RT API mem' md = AC20.aa_stklo AC20.ASYMS AsanRTInv.RT API mem md /\
  AC20.aa_stkhi AC20.ASYMS AsanRTInv.RT API mem' md = AC20.aa_stkhi AC20.ASYMS AsanRTInv.RT API mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem mem' md lo hi HFRA Hlo Hlh Hhi MU WM HPresW.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  pose proof HFRA as HF0.
  destruct HF0 as (Af & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9f & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAmod & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC20.aa_laws AC20.ASYMS AsanRTInv.RT API) as ALAWS.
  assert (HSS : AF20.SLOT_STACK = 1048576) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HHBv : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (Hfrb : 0 <= fr /\ fr + 8 <= 2 ^ 64).
  { pose proof Hhdr1 as Hx. unfold q64 in Hx. apply bytes_at_bound in Hx. rewrite length_le8 in Hx. lia. }
  assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x).
  { intros x Hx Hwx. exact (WM (Z_to_bv 64 x) Hwx). }
  assert (Hout : forall x, 0 <= x < 2 ^ 64 -> ~ (Sfr fr + lo <= x < Sfr fr + hi) ->
                   mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
  { intros x Hx Hn. apply MU. rewrite MState.unsigned_lit by exact Hx.
    cbn [Frame.outside]. split; [exact Hn | exact I]. }
  assert (Hinsh : forall x, Sfr fr + lo <= x < Sfr fr + hi -> in_shadow x).
  { intros x Hx. replace x with (shadow_addr (fr + (x - Sfr fr) * 8))
      by (rewrite r20_shadow_off by lia; lia).
    apply shadow_of_app. apply Happ. lia. }
  assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
            exists b, mbyte rsegs mem' q = Some b).
  { intros q Hq Hb.
    destruct (Z_lt_le_dec q (Sfr fr + lo)) as [H1|H1].
    - unfold mbyte. rewrite (Hout q Hq ltac:(lia)). exact Hb.
    - destruct (Z_lt_le_dec q (Sfr fr + hi)) as [H2|H2].
      + exact (HPresW q ltac:(lia)).
      + unfold mbyte. rewrite (Hout q Hq ltac:(lia)). exact Hb. }
  destruct Hloc as [[Hs50 [Hspfr Hreal]]|[Hs5fr [HfsbS [Hfs _]]]].
  - (* real arm: the written bytes are shadows of real-stack bytes *)
    assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
              ~ AC20.a_store_ok (hb ++ g_H g) (AC20.aa_stklo AC20.ASYMS AsanRTInv.RT API mem md) x ->
              mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { intros x Hx Hnok.
      destruct (Z_lt_le_dec x (Sfr fr + lo)) as [H1|H1]; [exact (Hout x Hx ltac:(lia))|].
      destruct (Z_lt_le_dec x (Sfr fr + hi)) as [H2|H2]; [|exact (Hout x Hx ltac:(lia))].
      exfalso. apply Hnok. right. right. right. exists (fr + (x - Sfr fr) * 8).
      split; [symmetry; rewrite r20_shadow_off by lia; lia|]. right. left.
      specialize (Hreal (fr + (x - Sfr fr) * 8) ltac:(lia)). lia. }
    destruct (r20_law_store (hb ++ g_H g) mem mem' md HAH Hmc Hwrit)
      as (HAH' & HOWN' & HSTK' & HSTKHI').
    split; [exact HAH'|]. split; [exact HOWN'|]. split; [exact HSTK' | exact HSTKHI'].
  - (* side arm: the written bytes are shadows of side-stack bytes *)
    destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FSb & HFSb0 & HwFSb & HFSbr).
    pose proof (HfsbS FSb HwFSb HFSb0) as HfrGE.
    destruct (r20_law_fs_place (hb ++ g_H g) mem md FSb HAH HwFSb HFSb0)
      as (HGTfs & HFSstk & _ & HFapp).
    assert (HFSsz : AC20.FS_SIZE = 11571200) by reflexivity.
    pose proof (r20_law_fs_ok (hb ++ g_H g) mem md FSb HAH HwFSb HFSb0) as Hfsok.
    (* every frame byte lies in the side stack: the tp word has one value *)
    assert (HinFS : forall a, fr <= a < fr + FRAME_BYTES -> FSb <= a < FSb + AC20.FS_SIZE).
    { intros a Ha. destruct (Hfs a Ha) as (FS2 & HFS20 & HwFS2 & HFS2r).
      assert (E : FS2 = FSb).
      { pose proof (r20_wm_congr mem (AC20.as_tp AC20.ASYMS) FS2 FSb HwFS2 HwFSb) as Hc.
        rewrite !Z.mod_small in Hc by lia. exact Hc. }
      rewrite <- E. exact HFS2r. }
    assert (Hmeta : forall q, fs_meta FSb q -> Frame.outside [(Sfr fr + lo, Sfr fr + hi)] q).
    { intros q Hq. pose proof (r20_fs_meta_range _ _ Hq) as Hqr.
      assert (Hqa : app_mem q) by (apply HFapp; lia).
      cbn [Frame.outside]. split; [|exact I]. intros Hqt.
      exact (app_not_shadow _ Hqa (Hinsh q Hqt)). }
    assert (Hfsok' : AC20.a_fs_ok mem' FSb).
    { apply (a_fs_ok_pres [(Sfr fr + lo, Sfr fr + hi)] mem mem' FSb Hfsok MU Hwrit Hpres Hmeta); lia. }
    assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
              ~ AC20.a_store_ok (hb ++ g_H g) (AC20.aa_stklo AC20.ASYMS AsanRTInv.RT API mem md) x ->
              ~ (FSb <= x < FSb + AC20.FS_SIZE) ->
              ~ (exists bb, FSb <= bb < FSb + AC20.FS_SIZE /\ x = shadow_addr bb) ->
              mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { intros x Hx Hnok HnFS Hnsh.
      destruct (Z_lt_le_dec x (Sfr fr + lo)) as [H1|H1]; [exact (Hout x Hx ltac:(lia))|].
      destruct (Z_lt_le_dec x (Sfr fr + hi)) as [H2|H2]; [|exact (Hout x Hx ltac:(lia))].
      exfalso. apply Hnsh. exists (fr + (x - Sfr fr) * 8).
      split; [apply HinFS; lia | symmetry; rewrite r20_shadow_off by lia; lia]. }
    destruct (r20_law_fs_store (hb ++ g_H g) mem mem' md FSb HAH HwFSb HFSb0
                Hmc Hwrit Hfsok') as (HAH' & HOWN' & HSTK' & HSTKHI').
    split; [exact HAH'|]. split; [exact HOWN'|]. split; [exact HSTK' | exact HSTKHI'].
Qed.

(* FRA across the same write (Tac_slot.sl_fr_meta: the write stays inside the frame's own 392 shadow bytes). *)
Lemma r20_fra : forall g fr hb regs regs' mem mem' md (lo hi : Z),
  FRA B APIf ra g fr hb regs mem md ->
  0 <= lo -> lo <= hi -> hi <= FRAME_SHADOW ->
  Frame.munch [(Sfr fr + lo, Sfr fr + hi)] mem mem' ->
  Frame.wmono rsegs mem mem' ->
  (forall q, Sfr fr + lo <= q < Sfr fr + hi -> exists b, mrd rsegs mem' (wa q) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md lo hi HFRA Hlo Hlh Hhi MU WM HPresW E2 E3 E4 E8 E9 E19 E26.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  destruct (r20_ah g fr hb regs mem mem' md lo hi HFRA Hlo Hlh Hhi MU WM HPresW)
    as (HAH' & _ & HSTK' & _).
  pose proof HFRA as HF0.
  destruct HF0 as (Af & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9f & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAmod & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC20.aa_laws AC20.ASYMS AsanRTInv.RT API) as ALAWS.
  pose proof (AC20.a_laws_stack_high _ _ _ _ _ ALAWS (hb ++ g_H g) mem md HAH) as Hstkhigh.
  assert (HSS : AF20.SLOT_STACK = 1048576) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HGTv : AC20.GT = 0x5fe000) by reflexivity.
  assert (Hfrb : 0 <= fr /\ fr + 8 <= 2 ^ 64).
  { pose proof Hhdr1 as Hx. unfold q64 in Hx. apply bytes_at_bound in Hx. rewrite length_le8 in Hx. lia. }
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; Z.div_mod_to_equations; lia).
  assert (HSfr0 : ASAN_K <= Sfr fr)
    by (unfold Sfr, shadow_addr; pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)); lia).
  assert (HASANK : ASAN_K = 0x7fff8000) by reflexivity.
  assert (Hinsh : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx. replace x with (shadow_addr (fr + (x - Sfr fr) * 8))
      by (rewrite r20_shadow_off by lia; lia).
    apply shadow_of_app. apply Happ. lia. }
  assert (HSfrhi : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { pose proof (Hinsh (Sfr fr + FRAME_SHADOW - 1) ltac:(lia)) as IS.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in IS |- *. lia. }
  assert (HAflo : HIGHMEM_BEG <= Af) by lia.
  assert (HAfhi : Af + 312 <= 2 ^ 64).
  { pose proof Hspill as Hx. unfold q64 in Hx. apply bytes_at_bound in Hx. rewrite length_le8 in Hx. lia. }
  unfold rg in Hr9f.
  (* the written range is inside the frame's shadow, which is below HIGHMEM_BEG and above the image *)
  assert (HWsh : forall x, ~ (Sfr fr <= x < Sfr fr + FRAME_SHADOW) -> Frame.outside [(Sfr fr + lo, Sfr fr + hi)] x).
  { intros x Hx. cbn [Frame.outside]. split; [lia | exact I]. }
  apply (sl_fr_meta B APIf ra empty FF g fr hb regs regs' mem mem' md [(Sfr fr + lo, Sfr fr + hi)] HFRA MU WM).
  - (* ro_agree mem' *)
    apply (r20_ro_keep mem mem' _ Hro MU). intros a Ha. pose proof (r20_ro_lt a Ha) as Har.
    cbn [Frame.outside]. split; [|exact I]. unfold ASAN_K in HSfr0. lia.
  - (* rt_disjoint *)
    unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB,
      RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI,
      RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN. cbn [disjoint_from].
    repeat split; (lia || exact I).
  - exact HAH'.
  - exact HSTK'.
  - exact Happ.
  - exact HGT.
  - (* the new 392 shadow bytes are present *)
    destruct Hsh as (sh0 & Hb0 & HL0).
    pose proof (bytes_at_bound rsegs mem (Sfr fr) sh0 Hb0) as Hb0r. rewrite HL0 in Hb0r.
    apply (r20_bytes_of_present (Z.to_nat FRAME_SHADOW) mem' (Sfr fr)); [lia | lia |].
    intros k Hk.
    pose proof (proj2 (proj2 Hb0) k ltac:(lia)) as Hb0k.
    destruct (nth_error sh0 k) as [bb|] eqn:Ek; [|exfalso; apply nth_error_None in Ek; lia].
    destruct (Z_lt_le_dec (Sfr fr + Z.of_nat k) (Sfr fr + lo)) as [H1|H1].
    + exists bb. unfold mrd, wa in Hb0k |- *.
      rewrite (MU (Z_to_bv 64 (Sfr fr + Z.of_nat k)));
        [exact Hb0k | rewrite MState.unsigned_lit by lia; cbn [Frame.outside]; split; [lia | exact I]].
    + destruct (Z_lt_le_dec (Sfr fr + Z.of_nat k) (Sfr fr + hi)) as [H2|H2].
      * exact (HPresW (Sfr fr + Z.of_nat k) ltac:(lia)).
      * exists bb. unfold mrd, wa in Hb0k |- *.
        rewrite (MU (Z_to_bv 64 (Sfr fr + Z.of_nat k)));
          [exact Hb0k | rewrite MState.unsigned_lit by lia; cbn [Frame.outside]; split; [lia | exact I]].
  - (* W misses everything outside the frame body and the frame shadow *)
    intros x Hx Hnb Hnsh. exact (HWsh x Hnsh).
  - (* the spill [A + 304, A + 312) *)
    intros A0 HA0 HA0r x Hx.
    rewrite (r20_A_eq regs A0 Af HA0 HA0r ltac:(unfold rg; exact Hr9f) ltac:(lia)) in Hx.
    apply HWsh. lia.
  - (* the saved registers [S - 104, S) *)
    intros x Hx. apply HWsh. lia.
  - (* the selector / fr spills [A + 16, A + 32) *)
    intros A0 HA0 HA0r x Hx.
    rewrite (r20_A_eq regs A0 Af HA0 HA0r ltac:(unfold rg; exact Hr9f) ltac:(lia)) in Hx.
    apply HWsh. lia.
  - (* the slot window *)
    intros x Hx. left. apply HWsh. lia.
  - (* the registered globals stay addressable: their shadow bytes are below the frame's *)
    intros a Ha. apply (r20_addr_keep_rng mem mem' _ a 1 (HAG a Ha) MU).
    intros i Hi. replace (a + i) with a by lia.
    pose proof (r20_AG_lt a Ha) as Har. apply HWsh.
    unfold Sfr, shadow_addr. revert HGT Har. unfold AC20.GT. Z.div_mod_to_equations. lia.
  - exact E2.
  - exact E3.
  - exact E4.
  - exact E8.
  - exact E9.
  - exact E19.
  - exact E26.
Qed.

Lemma seg_R20 : forall b : nat,
  Hat B APIf ra (Inv_A81924_at (fx := fx) B APIf ra) b ->
  Hat B APIf ra (Inv_A818e8_at (fx := fx) B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros b Hexit g c HInv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    ((Hgn & Hb6 & HHB & Hr23 & Hour & Hout & Hcur) & Hb0 & HRFb & Ha0 &
     Hs128 & HPRO & Hs104 & Hs96 & Hs64 & Hr21 & Hs112 & Hs144 & Hs208 & HRWid & HRWjk & Hs280 & Hs240 &
     HRWjy & HRWsc & Hs152 & HAid & HRXS)).
  subst c.
  pose proof (proj1 FF) as SEGS.
  pose proof HRFb as (HRB & Hnz & Hr24 & HF).
  pose proof (fra_app B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (HGT & Happ).
  pose proof HFRA as HF0.
  destruct HF0 as (Af & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9f & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAmod & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC20.aa_laws AC20.ASYMS AsanRTInv.RT API) as ALAWS.
  pose proof (AC20.a_laws_stack_high _ _ _ _ _ ALAWS (hb1 phi (rnb g b) ++ g_H g) mem md HAH) as Hstkhigh.
  assert (HSS : AF20.SLOT_STACK = 1048576) by reflexivity.
  assert (HHBv : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HGTv : AC20.GT = 0x5fe000) by reflexivity.
  assert (HASANK : ASAN_K = 0x7fff8000) by reflexivity.
  assert (Hfrb : 0 <= fr /\ fr + 8 <= 2 ^ 64).
  { pose proof Hhdr1 as Hx. unfold q64 in Hx. apply bytes_at_bound in Hx. rewrite length_le8 in Hx. lia. }
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; Z.div_mod_to_equations; lia).
  assert (HSfr0 : ASAN_K <= Sfr fr)
    by (unfold Sfr, shadow_addr; pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)); lia).
  assert (Hinsh : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx. replace x with (shadow_addr (fr + (x - Sfr fr) * 8))
      by (rewrite r20_shadow_off by lia; lia).
    apply shadow_of_app. apply Happ. lia. }
  assert (HSfrhi : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { pose proof (Hinsh (Sfr fr + FRAME_SHADOW - 1) ltac:(lia)) as IS.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in IS |- *. lia. }
  assert (HAflo : HIGHMEM_BEG <= Af) by lia.
  assert (HAfhi : Af + 312 <= 2 ^ 64).
  { pose proof Hspill as Hx. unfold q64 in Hx. apply bytes_at_bound in Hx. rewrite length_le8 in Hx. lia. }
  (* the frame's shadow bytes are present and writable *)
  assert (HSTK0 : stk rsegs mem (Sfr fr + 316) (Sfr fr + 324)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    exact (AsanRTInv.RT_shadow_rw _ _ _ HRT a (Hinsh a ltac:(lia))). }
  unfold rg in Hr19, Hr9f.
  unfold a0v, rg in Ha0.
  rewrite SEGS.
  apply (sl_run_lib regs (Z_to_bv 64 0x818e8) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x8191c /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\
       getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       Frame.munch [(Sfr fr + 316, Sfr fr + 324)] mem mem' /\ Frame.wmono rsegs mem mem' /\
       stk rsegs mem' (Sfr fr + 316) (Sfr fr + 324))
    (Post B APIf ra g)).
  { exact Hhalt. }
  { unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    eapply evt_mono.
    - apply r20_evt with (SHv := Sfr fr); [exact Ha0 | exact Hr19 | lia | lia | exact HSTK0].
    - intros ms' (R & m' & Hms & P2a & P3 & P4 & P8 & P9 & P19 & P21 & P22 & P23 & P24 & P25 & P26 &
                  MUq & WMq & STq).
      exists R, (Z_to_bv 64 0x8191c), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2a|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P19|]. split; [exact P21|]. split; [exact P22|]. split; [exact P23|].
      split; [exact P24|]. split; [exact P25|]. split; [exact P26|].
      split; [exact MUq|]. split; [exact WMq | exact STq]. }
  intros R pc' mem' regs'' md1
    (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K24 & K25 & K26 & MU & WM & STk) Hreg Hmat.
  subst pc'.
  assert (E2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact K2).
  assert (E3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact K3).
  assert (E4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact K4).
  assert (E8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact K8).
  assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
  assert (E19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact K19).
  assert (E21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact K21).
  assert (E22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact K22).
  assert (E23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact K23).
  assert (E24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact K24).
  assert (E25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact K25).
  assert (E26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact K26).
  assert (HPresW : forall q, Sfr fr + 316 <= q < Sfr fr + 324 -> exists bb, mrd rsegs mem' (wa q) = Some bb).
  { intros q Hq. destruct (proj2 (proj2 STk) q Hq) as (_ & Hbq). exact Hbq. }
  (* FRA and ENT after the six shadow stores *)
  assert (HFRAmd : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md)
    by exact (r20_fra g fr (hb1 phi (rnb g b)) regs regs'' mem mem' md 316 324 HFRA ltac:(lia) ltac:(lia)
                ltac:(lia) MU WM HPresW E2 E3 E4 E8 E9 E19 E26).
  assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md1)
    by exact (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs'' regs'' mem' md md1 HFRAmd
                eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hmat).
  destruct (r20_ah g fr (hb1 phi (rnb g b)) regs mem mem' md 316 324 HFRA ltac:(lia) ltac:(lia) ltac:(lia)
              MU WM HPresW) as (HAH' & HOWN' & HSTK' & HSTKHI').
  assert (HENTmd : ENT (fx := fx) APIf g (hb1 phi (rnb g b)) mem' md).
  { eapply ent_store; [exact HENT | exact HFRA | exact MU | | exact HSTK' | exact HSTKHI' |].
    - intros x Hx.
      destruct (Z_lt_le_dec x (Sfr fr + 316)) as [H1|H1];
        [left; cbn [Frame.outside]; split; [lia | exact I]|].
      destruct (Z_lt_le_dec x (Sfr fr + 324)) as [H2|H2];
        [right; right; right; lia | left; cbn [Frame.outside]; split; [lia | exact I]].
    - intros a _ Ho. exact (proj2 (HOWN' a) Ho). }
  assert (HENT'' : ENT (fx := fx) APIf g (hb1 phi (rnb g b)) mem' md1)
    by (eapply ent_mat; [exact HENTmd | exact Hmat]).
  (* the byte runs and spills the exit cut carries: frame bytes and the spill base are outside the write set *)
  assert (Hfout : forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside [(Sfr fr + 316, Sfr fr + 324)] x).
  { intros x Hx. cbn [Frame.outside]. split; [|exact I]. intros Hin.
    exact (app_not_shadow x (Happ x Hx) (Hinsh x ltac:(lia))). }
  assert (Hhout : forall x, HIGHMEM_BEG <= x -> Frame.outside [(Sfr fr + 316, Sfr fr + 324)] x).
  { intros x Hx. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (KSP : forall off w, 0 <= off <= 304 -> spill regs mem off w -> spill regs'' mem' off w).
  { intros off w Hoff (A0 & HA0 & HQ).
    assert (EA : A0 = Af)
      by exact (r15_spill_A regs mem off w A0 Af ltac:(unfold rg; exact Hr9f) HAflo HAfhi Hoff HA0 HQ).
    subst A0. unfold spill. exists Af. split.
    - unfold rg. rewrite E9. exact Hr9f.
    - unfold q64 in *. apply (a_keep [(Sfr fr + 316, Sfr fr + 324)] mem mem' _ _ MU); [|exact HQ].
      rewrite length_le8. intros x Hx. apply Hhout. lia. }
  (* RB of turn (S b): b = 0, so the round-trip state does not move *)
  assert (Hble2 : (b <= 2)%nat) by lia.
  destruct (B3Rtm.a_RS_012 (g_in g) b Hble2) as (EID & EFG).
  destruct (r15_RS_len (g_in g) b) as (LID & LFG).
  assert (HRB'' : RB g fr b (RID (g_in g) (S b)) (RFG (g_in g) (S b)) regs'' mem').
  { rewrite EID, EFG. destruct HRB as (Rb6 & Rcur & Rour & Rr23 & Ridb & Rfgb).
    split; [exact Rb6|].
    split.
    { destruct Rcur as (Rc0 & Rc22 & Rc25). unfold CUR, rg in *.
      split; [exact Rc0|]. split; [rewrite E22; exact Rc22 | rewrite E25; exact Rc25]. }
    split.
    { unfold OURb in *. apply (a_keep [(Sfr fr + 316, Sfr fr + 324)] mem mem' _ _ MU); [|exact Rour].
      rewrite OUR_length. intros x Hx. apply Hfout. lia. }
    split; [unfold rg in *; rewrite E23; exact Rr23|].
    split.
    { unfold IDBr in *. apply (a_keep [(Sfr fr + 316, Sfr fr + 324)] mem mem' _ _ MU); [|exact Ridb].
      rewrite LID. intros x Hx. apply Hfout. lia. }
    { unfold FGBr in *. apply (a_keep [(Sfr fr + 316, Sfr fr + 324)] mem mem' _ _ MU); [|exact Rfgb].
      rewrite LFG. intros x Hx. apply Hfout. lia. } }
  assert (Hr24'' : rg regs'' 24 phi) by (unfold rg in *; rewrite E24; exact Hr24).
  assert (Hr21'' : rg regs'' 21 (fr + 2176)) by (unfold rg in *; rewrite E21; exact Hr21).
  assert (Hs144'' : spill regs'' mem' 144 (fr + 2688)) by exact (KSP 144 _ ltac:(lia) Hs144).
  assert (Hs208'' : spill regs'' mem' 192 (fr + 2768)) by exact (KSP 192 _ ltac:(lia) Hs208).
  (* the frame cells fr + 2688 (38 bytes), fr + 2768 (72), fr + 3040 (1) and fr + 3056 (32): frame bytes, off the
     write set *)
  assert (HRWk : forall a n bs, fr <= a -> a + Z.of_nat n <= fr + FRAME_BYTES ->
            rw_cells rsegs mem a [CB n bs] -> rw_cells rsegs mem' a [CB n bs]).
  { intros ca cn cbs Ha1 Ha2 HRWa. apply (r20_rwcb_keep _ mem mem' _ _ _ MU WM); [|exact HRWa].
    intros x Hx. apply Hfout. lia. }
  assert (HRWid'' : exists idb, rw_cells rsegs mem' (fr + 2688) [CB 38 idb]).
  { destruct HRWid as (idb & HRWi). exists idb. exact (HRWk (fr + 2688) 38%nat idb ltac:(lia) ltac:(lia) HRWi). }
  assert (HRWjk'' : exists junk, rw_cells rsegs mem' (fr + 2768) [CB 72 junk]).
  { destruct HRWjk as (junk & HRWj). exists junk. exact (HRWk (fr + 2768) 72%nat junk ltac:(lia) ltac:(lia) HRWj). }
  assert (Hs280'' : spill regs'' mem' 280 (fr + 3040)) by exact (KSP 280 _ ltac:(lia) Hs280).
  assert (Hs240'' : spill regs'' mem' 240 (fr + 3056)) by exact (KSP 240 _ ltac:(lia) Hs240).
  assert (HRWjy'' : exists jy, rw_cells rsegs mem' (fr + 3040) [CB 1 jy]).
  { destruct HRWjy as (jy & HRWy). exists jy. exact (HRWk (fr + 3040) 1%nat jy ltac:(lia) ltac:(lia) HRWy). }
  assert (HRWsc'' : exists junk, rw_cells rsegs mem' (fr + 3056) [CB 32 junk]).
  { destruct HRWsc as (junk & HRWs). exists junk. exact (HRWk (fr + 3056) 32%nat junk ltac:(lia) ltac:(lia) HRWs). }
  assert (Hs152'' : spill regs'' mem' 152 (Sfr fr + 68)) by exact (KSP 152 _ ltac:(lia) Hs152).
  (* the id record's 38 bytes stay addressable: their shadow bytes are S(fr) + 272 .. + 276 *)
  assert (HAid'' : addressable mem' (fr + 2176) 38).
  { apply (r20_addr_keep_rng mem mem' _ (fr + 2176) 38 HAid MU).
    intros i Hi. cbn [Frame.outside]. split; [|exact I].
    unfold Sfr, shadow_addr. revert Hfr8 Hi. Z.div_mod_to_equations. lia. }
  (* PRO: the spills by KSP; our[]'s 6 bytes stay addressable (their shadow byte is S(fr) + 328); the input block
     is a live block of the entry heap (a_laws_blocks), so application memory (outside the write set, which is
     shadow memory) and apart from the frame (on the real arm the frame is at or above stklo, on the side arm it is
     in the side stack, which no block byte is), so its shadow bytes are not the frame's S(fr) + 316 .. + 323 *)
  assert (INB : In (g_p g, g_n g) (g_H g) -> forall x, g_p g <= x < g_p g + g_n g ->
            app_mem x /\ ~ (fr <= x < fr + FRAME_BYTES)).
  { intros Hin x Hx.
    destruct (r20_law_blocks (hb1 phi (rnb g b) ++ g_H g) mem md (g_p g) (g_n g) HAH
                (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hpend & _ & Hpb).
    destruct (Hpb x Hx) as (Happx & _ & _ & _ & Hnfsx).
    split; [exact Happx|].
    intros Hxf. destruct Hloc as [(H0' & Hspfr & Hreal)|(Hfr0' & HfsbS & Hfs & _)].
    - pose proof (Hreal x Hxf). lia.
    - exact (Hnfsx (Hfs x Hxf)). }
  assert (HPRO'' : PRO g fr regs'' mem').
  { apply (r15_pro_keep g fr regs regs'' mem mem' (fun off v Ho H => KSP off v ltac:(lia) H)); [| | | exact HPRO].
    - intros HAour. apply (r20_addr_keep_rng mem mem' _ (fr + 2624) 6 HAour MU).
      intros i Hi. cbn [Frame.outside]. split; [|exact I].
      unfold Sfr, shadow_addr. revert Hfr8 Hi. Z.div_mod_to_equations. lia.
    - intros Hin HIN. apply (a_keep [(Sfr fr + 316, Sfr fr + 324)] mem mem' _ _ MU); [|exact HIN].
      intros x Hx. rewrite <- g_n_len in Hx. destruct (INB (Hin ltac:(lia)) x Hx) as (Happx & _).
      cbn [Frame.outside]. split; [|exact I]. intros Hxw.
      exact (app_not_shadow x Happx (Hinsh x ltac:(lia))).
    - intros Hin HA. apply (r20_addr_keep_rng mem mem' _ (g_p g) (g_n g) HA MU).
      intros i Hi. cbn [Frame.outside]. split; [|exact I].
      destruct (INB Hin (g_p g + i) ltac:(lia)) as (_ & Hxfr).
      unfold Sfr, shadow_addr. revert Hfr8 Hxfr. Z.div_mod_to_equations. lia. }
  (* out[]'s shadow bytes S(fr) + 68 .. + 254 are below the write set S(fr) + 316 .. + 323 *)
  assert (Hout'' : OUTA fr mem').
  { apply (outa_munch fr mem mem' _ Hout MU).
    intros i Hi. cbn [Frame.outside]. split; [|exact I].
    unfold Sfr, shadow_addr. revert Hfr8 Hi. Z.div_mod_to_equations. lia. }
  (* RXS (push 10): the spills by KSP; the fragment record's shadow bytes S(fr) + 282 .. + 290 are below the write
     set S(fr) + 316 .. + 323 *)
  assert (HRXS'' : RXS g fr regs'' mem').
  { apply (r15_rxs_keep g fr regs regs'' mem mem' (fun off v Ho H => KSP off v ltac:(lia) H)); [|exact HRXS].
    intros HA72. apply (r20_addr_keep_rng mem mem' _ (fr + 2256) 72 HA72 MU).
    intros i Hi. cbn [Frame.outside]. split; [|exact I].
    unfold Sfr, shadow_addr. revert Hfr8 Hi. Z.div_mod_to_equations. lia. }
  rewrite <- SEGS.
  exact (r_free_cont B APIf ra empty FF b Hexit g regs'' mem' md1 fr phi HFRA'' HENT'' Hgn HRB'' Hr24'' Hout''
           (KSP 128 _ ltac:(lia) Hs128) HPRO'' (KSP 104 _ ltac:(lia) Hs104)
           (KSP 96 _ ltac:(lia) Hs96) (KSP 64 _ ltac:(lia) Hs64) Hr21'' (KSP 112 _ ltac:(lia) Hs112) Hs144''
           Hs208'' HRWid'' HRWjk'' Hs280'' Hs240'' HRWjy'' HRWsc'' Hs152'' HAid'' HRXS'').
Qed.

End R20W.
