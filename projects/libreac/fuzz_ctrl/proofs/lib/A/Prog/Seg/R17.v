(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names and numbers changed; 1392 of its 1502 lines of code are new or changed and 901 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/R14.v, with its module paths, module names, addresses and numbers changed; 629 of its 730 lines of code are new or changed and 1401 lines of the source are left out. *)
(* Segment R17 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): [0x8183c, 0x81858], Inv_A8183c -> Inv_A81858
   (turn b = 0).  0x8183c ld a1,112(s1) (= mrow); beq a0,a1,81848 taken (a0 = mrow, the catalogue_match result);
   0x81848 s11 := s8 + 18 (= Phi_r + 18); a0 := s11; a1 := [s1+216] (= fr + 2528); call reac_ports_parse at 0x81854;
   return to 0x81858.  reac_ports_parse writes the two u32 port counts at fr+2528 / fr+2532 (= 4*n_in / 4*n_out of the
   turn-0 port bytes rt_pbs) and q+8, plus its own 16 stack bytes below sp; the result a0 is 0 because the port bytes
   declare a valid record (ports_ok true, B3Rtm.a_rtm_decl).  r17_evt is the Lib-level run of the five instructions
   plus the call by its contract; the push-5b frame-and-shadow transport of FRA across the callee's write set
   W = the stack scratch [sp-16, sp) + the port cells [fr+2528, fr+2540) is B3FrCl.b3_fr_cl (the side arm's FakeStack
   frame record moves because W meets the FakeStack only inside the frame body: the stack scratch is above stklo, the
   FakeStack below it); r17_ah re-derives AH after that store (real arm a_laws_store, side arm a_laws_fs_store);
   seg_R17 is the full segment lemma from the official exit cut Inv_A81858_at to the entry cut Inv_A8183c_at.
   ro_agree of the post memory (needed to rebuild FRA) comes from FRA's ro_agree plus r17_ro_keep (read-only
   addresses are in the image, below 0x5fe000, outside the write set).  FRA carries no mem_inv (push 5b) and
   reac_ports_parse needs none. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YK1j.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ports_parse_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv AsanRTFacts PContract MemNorm AsanLift BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcDecl RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_rt_b2 Tac_rt2_b2 Tac_slot Tac_fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require B3Rtm B3FrCl.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module ACr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module YKa := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.

(* ---- small arithmetic / memory helpers ---- *)

Lemma r17_eqb_refl : forall x : word, bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.

(* A byte at [A0 + 16, A0 + 312) with Z_to_bv 64 A0 = Z_to_bv 64 A lies outside any [lo, hi) with 0 <= lo and
   hi <= A, for every 64-bit representative A0 of A. *)
Lemma r17_wrap_out : forall A A0 lo hi x, Z_to_bv 64 A = Z_to_bv 64 A0 -> 0 <= A -> A + 312 <= 2 ^ 64 ->
  0 <= lo -> hi <= A -> A0 + 16 <= x < A0 + 312 -> ~ (lo <= x < hi).
Proof.
  intros A A0 lo hi x E H0 H1 Hlo Hhi Hx.
  assert (Ew : A mod 2 ^ 64 = A0 mod 2 ^ 64).
  { apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. exact E. }
  rewrite (Z.mod_small A (2 ^ 64)) in Ew by lia.
  pose proof (Z.div_mod A0 (2 ^ 64) ltac:(lia)) as Hdm. rewrite <- Ew in Hdm.
  remember (A0 / 2 ^ 64) as q eqn:Eq. clear Eq.
  change (2 ^ 64) with 18446744073709551616 in *. lia.
Qed.

Lemma r17_bv_mod : forall a a' d, Z_to_bv 64 a = Z_to_bv 64 a' -> Z_to_bv 64 (a + d) = Z_to_bv 64 (a' + d).
Proof.
  intros a a' d H. apply (f_equal bv_unsigned) in H. rewrite !Z_to_bv_unsigned in H.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap in *.
  rewrite (Zplus_mod a d), (Zplus_mod a' d), H. reflexivity.
Qed.

(* bytes_at is invariant under replacing the base address by a congruent (mod 2^64) one. *)
Lemma r17_bytes_cong : forall m a a' bs,
  Z_to_bv 64 a = Z_to_bv 64 a' -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at rsegs m a' bs -> bytes_at rsegs m a bs.
Proof.
  intros m a a' bs Hcong Ha0 Hal (Ha'0 & Ha'l & Hr). split; [exact Ha0|]. split; [exact Hal|].
  intros i Hi.
  assert (Heq : wa (a + Z.of_nat i) = wa (a' + Z.of_nat i)).
  { unfold wa. apply r17_bv_mod. exact Hcong. }
  rewrite Heq. exact (Hr i Hi).
Qed.

(* A q64 spill, read as a single 8-byte read-only cell at the FRA spill base A + off. *)
Lemma r17_spill_ro : forall (regs : bvmap 5 word) m off v A,
  spill regs m off v -> getr regs 9 = Z_to_bv 64 A -> 0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off ->
  ro_cells rsegs m (A + off) [C8 (Z_to_bv 64 v)].
Proof.
  intros regs m off v A (A1 & Hr9' & Hq) Hr9 HA0 HAb Hoff.
  unfold rg in Hr9'. assert (Hcong : Z_to_bv 64 A = Z_to_bv 64 A1) by (rewrite <- Hr9; exact Hr9').
  unfold ro_cells, cells_at. split; [cbn; tauto|].
  cbn [cells_bytes cbytes]. rewrite app_nil_r.
  unfold q64 in Hq.
  eapply r17_bytes_cong; [ apply r17_bv_mod; exact Hcong | lia | rewrite length_le8; lia | exact Hq ].
Qed.

(* A q64 spill transported across a run whose write set W avoids the spill's 8-byte footprint at A + off. *)
Lemma r17_spill_keep : forall (regs regs'' : bvmap 5 word) m m' off v A W,
  spill regs m off v -> getr regs 9 = Z_to_bv 64 A -> getr regs'' 9 = getr regs 9 ->
  0 <= A -> A + off + 8 <= 2 ^ 64 -> 0 <= off ->
  Frame.munch W m m' ->
  (forall x, A + off <= x < A + off + 8 -> Frame.outside W x) ->
  spill regs'' m' off v.
Proof.
  intros regs regs'' m m' off v A W (A1 & Hr9' & Hq) Hr9 K9 HA0 HAb Hoff MU Hout.
  unfold rg in Hr9'. assert (Hcong : Z_to_bv 64 A = Z_to_bv 64 A1) by (rewrite <- Hr9; exact Hr9').
  assert (Hq2 : q64 m (A + off) v).
  { unfold q64 in *. eapply r17_bytes_cong; [ apply r17_bv_mod; exact Hcong | lia | rewrite length_le8; lia | exact Hq ]. }
  exists A. split; [unfold rg; transitivity (getr regs 9); [exact K9 | exact Hr9]|].
  unfold q64 in *. eapply fl_bytes; [exact Hq2 | exact MU |]. rewrite length_le8. exact Hout.
Qed.

(* One CB cell's rw_cells across a run whose write set W misses the cell's bytes. *)
Lemma r17_rwcb_keep : forall W (m m' : word -> option byte) a n bs,
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

(* RXS (push 10) across a run that keeps the spills [A + 0] .. [A + 224) and the fragment record's addressability. *)
Lemma r17_rxs_keep : forall g fr regs regs' (m m' : word -> option byte),
  (forall off v, 0 <= off <= 216 -> spill regs m off v -> spill regs' m' off v) ->
  (addressable m (fr + 2256) 72 -> addressable m' (fr + 2256) 72) ->
  RXS g fr regs m -> RXS g fr regs' m'.
Proof.
  intros g fr regs regs' m m' Hs Ha (H48 & H56 & H88 & H80 & H72 & H16 & H8 & H192 & H216 & HA).
  split; [exact (Hs 48 _ ltac:(lia) H48)|].
  split; [exact (Hs 56 _ ltac:(lia) H56)|].
  split; [exact (Hs 88 _ ltac:(lia) H88)|].
  split; [exact (Hs 80 _ ltac:(lia) H80)|].
  split; [exact (Hs 72 _ ltac:(lia) H72)|].
  split; [exact (Hs 8 _ ltac:(lia) H16)|].
  split; [exact (Hs 0 _ ltac:(lia) H8)|].
  split; [exact (Hs 200 _ ltac:(lia) H192)|].
  split; [exact (Hs 216 _ ltac:(lia) H216) | exact (Ha HA)].
Qed.

(* PRO (push 13B, push 14D) across a run that keeps the spills [A + 32] .. [A + 280), our[]'s 6 bytes addressable
   and the input block: its bytes, and its addressability when it is a live block of the entry heap. *)
Lemma r17_pro_keep : forall g fr regs regs' (m m' : word -> option byte),
  (forall off v, 32 <= off <= 272 -> spill regs m off v -> spill regs' m' off v) ->
  (addressable m (fr + 2624) 6 -> addressable m' (fr + 2624) 6) ->
  ((0 < g_n g -> In (g_p g, g_n g) (g_H g)) ->
     bytes_at rsegs m (g_p g) (g_in g) -> bytes_at rsegs m' (g_p g) (g_in g)) ->
  (In (g_p g, g_n g) (g_H g) -> addressable m (g_p g) (g_n g) -> addressable m' (g_p g) (g_n g)) ->
  PRO g fr regs m -> PRO g fr regs' m'.
Proof.
  intros g fr regs regs' m m' Hs Ha6 Hb Hia
    (H40 & H120 & H136 & H160 & H168 & H176 & H200 & H248 & HA6 & HIN & HG & H184 & H256 & H264 & H272 & H32).
  split; [exact (Hs 40 _ ltac:(lia) H40)|].
  split; [exact (Hs 120 _ ltac:(lia) H120)|].
  split; [exact (Hs 136 _ ltac:(lia) H136)|].
  split; [exact (Hs 160 _ ltac:(lia) H160)|].
  split; [exact (Hs 168 _ ltac:(lia) H168)|].
  split; [exact (Hs 176 _ ltac:(lia) H176)|].
  split; [exact (Hs 208 _ ltac:(lia) H200)|].
  split; [exact (Hs 248 _ ltac:(lia) H248)|].
  split; [exact (Ha6 HA6)|].
  split; [exact (Hb (fun Hn => proj1 (HG Hn)) HIN)|].
  split; [intros Hn; destruct (HG Hn) as (HH & HA); split; [exact HH | exact (Hia HH HA)]|].
  split; [exact (Hs 184 _ ltac:(lia) H184)|].
  split; [exact (Hs 256 _ ltac:(lia) H256)|].
  split; [exact (Hs 264 _ ltac:(lia) H264)|].
  split; [exact (Hs 272 _ ltac:(lia) H272) | exact (Hs 32 _ ltac:(lia) H32)].
Qed.

(* ---- The Lib-level run of [0x8183c, 0x81858) with the reac_ports_parse contract (ports_ok true -> a0 = 0). ---- *)
Lemma r17_evt : reac_ports_parse_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv A phi q mr lo : Z) (bs : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 mr -> s8 = Z_to_bv 64 phi ->
    0 <= phi -> phi + 50 <= 2 ^ 64 -> 0 <= q -> q + 12 <= 2 ^ 64 -> 0 <= spv -> spv < 2 ^ 64 ->
    ro_cells rsegs m (A + 112) [C8 (Z_to_bv 64 mr)] ->
    ro_cells rsegs m (A + 216) [C8 (Z_to_bv 64 q)] ->
    length bs = 20%nat -> bytes_at rsegs m (phi + 18) bs ->
    q mod 4 = 0 -> wr_at rsegs m q 12 ->
    (q + 12 <= phi + 18 \/ phi + 18 + 20 <= q) ->
    (phi + 18 + 20 <= spv - 16 \/ spv <= phi + 18) -> (q + 12 <= spv - 16 \/ spv <= q) ->
    stk rsegs m lo spv -> lo + 16 <= spv ->
    asan_cells m -> shadow_rw m ->
    addressable m (phi + 18) 20 -> addressable m q 12 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       Frame.outside [(spv - 16, spv); (q, q + 12)] x) ->
    RcLeaf.ports_ok (phi + 18) q bs = true ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81858) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = s7 /\ getr R 25 = s9 /\
         getr R 26 = s10 /\
         getr R 24 = Z_to_bv 64 phi /\ getr R 10 = Z_to_bv 64 0 /\ getr R 27 = Z_to_bv 64 (phi + 18) /\
         Frame.munch [(spv - 16, spv); (q, q + 12)] m m' /\ Frame.wmono rsegs m m' /\
         stk rsegs m' lo spv /\
         bytes_at rsegs m' q (le4 (Z_to_bv 64 (4 * RcLeaf.n_in bs))) /\
         bytes_at rsegs m' (q + 4) (le4 (Z_to_bv 64 (4 * RcLeaf.n_out bs))) /\
         bytes_at rsegs m' (q + 8) (le4 (Z_to_bv 64 (16 * RcLeaf.bt bs 7))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8183c) fc None m (seg_rom rsegs)).
Proof.
  intros PP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A phi q mr lo bs -> -> -> -> Hphi0 Hphi50 Hq0 Hqb Hspv0 Hspv
    RO1 RO2 Hlen HB Hqmod HWR Hdisj Hsep1 Hsep2 ST Hlo16 HAC HSW HAp HAq HOutside Hok.
  step.                                 (* 8183c ld a1,112(s1) : a1 := mr *)
  step. if_true_by (r17_eqb_refl (Z_to_bv 64 mr)).    (* 81840 beq a0,a1,81848 taken *)
  step.                                 (* 81848 addi s11,s8,18 *)
  step.                                 (* 8184c mv a0,s11 *)
  clear RO1.
  step.                                 (* 81850 ld a1,216(s1) : a1 := q *)
  step.                                 (* 81854 jal reac_ports_parse *)
  eapply evt_cut.
  { eapply PP with (p := phi + 18) (q := q) (lo := lo) (bs := bs).
    - first [ reflexivity | f_equal; lia ].
    - reflexivity.
    - lia.
    - lia.
    - rewrite MState.unsigned_lit by lia. exact ST.
    - rewrite MState.unsigned_lit by lia. exact Hlo16.
    - intros _ _. split; [exact Hlen | exact HB].
    - intros _ _. rewrite !MState.unsigned_lit by lia.
      split; [exact Hqmod|]. split; [exact HWR|]. split; [exact Hdisj|].
      split; [exact Hsep1 | exact Hsep2].
    - intros _ _. split; [exact HAC|]. split; [exact HSW|]. split; [exact HAp | exact HAq].
    - intros _ _. rewrite !MState.unsigned_lit by lia. exact HOutside. }
  intros ms' PO. unfold reac_ports_parse_post in PO. rewrite Hok in PO.
  destruct PO as (t0' & t1' & t2' & t3' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' &
                  E & WM & MI & STc & HI & HO & H8 & MUc).
  subst ms'.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  do 14 (split; [reflexivity|]).
  rewrite !MState.unsigned_lit in MUc, STc by lia.
  split; [exact MUc|]. split; [exact WM|]. split; [exact STc|].
  split; [exact HI|]. split; [exact HO | exact H8].
Qed.

(* The A image's loaded segments all end at or below 0x5fe000 (= GT), so every read-only address is below it. *)
Lemma r17_hull : forall s, In s rsegs -> Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 6283264.
Proof.
  assert (H : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 6283264) rsegs = true)
    by (vm_compute; reflexivity).
  intros s Hin. apply Z.leb_le. rewrite forallb_forall in H. exact (H s Hin).
Qed.

(* A read-only address lies in the image, hence below 0x5fe000. *)
Lemma r17_ro_lt : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < 6283264.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  pose proof (YK1j.find_segment_in rsegs (bv_unsigned a) 1 s E) as Hin.
  pose proof (YK1j.find_segment_range rsegs (bv_unsigned a) 1 s E) as (_ & Hhi).
  pose proof (r17_hull s Hin) as Hb. lia.
Qed.

(* ro_agree is kept by a store whose write set W avoids every read-only address (all in low image). *)
Lemma r17_ro_keep : forall (mem mem' : word -> option byte) (W : list Frame.ivl),
  ro_agree rsegs mem -> Frame.munch W mem mem' ->
  (forall a : word, ro_addr rsegs a = true -> Frame.outside W (bv_unsigned a)) ->
  ro_agree rsegs mem'.
Proof.
  intros mem mem' W HRO MU Hout a Hro. unfold mrd. rewrite (MU a (Hout a Hro)). exact (HRO a Hro).
Qed.

Section R17W.
Context {fx : YKa.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, ACr.AsanAllocAPI ACr.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis PP : reac_ports_parse_contract.

(* The allocator laws whose inner lists this file takes apart (Contract.v, a Theorem Labs lane's v1.9 generation), each restated
   once here, so that a law that gains or moves a conjunct breaks this one proof and no use site (a Theorem Labs lane 15:32Z). *)
Local Notation law_AH := (ACr.aa_AH ACr.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_own := (ACr.aa_owned ACr.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_lo := (ACr.aa_stklo ACr.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_hi := (ACr.aa_stkhi ACr.ASYMS AsanRTInv.RT (APIf rc)).

Lemma r17_law_blocks : forall H mem md p n, law_AH H mem md -> In (p, n) H ->
  p mod 16 = 0 /\ 4096 <= p /\ p + n <= law_lo mem md /\ end_in_app p n /\
  forall a, p <= a < p + n -> app_mem a /\ writable_at rsegs mem a /\ ~ ACr.a_in_img a /\ ~ ACr.a_on_img_page a /\
    ~ ACr.a_in_fs ACr.ASYMS mem a.
Proof. exact (ACr.a_laws_blocks _ _ _ _ _ (ACr.aa_laws ACr.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r17_law_fs_place : forall H mem md b, law_AH H mem md -> word_mem rsegs mem (ACr.as_tp ACr.ASYMS) b -> 0 <= b < 2 ^ 64 ->
  ACr.GT <= b /\ b + ACr.FS_SIZE <= law_lo mem md /\ b mod 4096 = 0 /\ forall a, b <= a < b + ACr.FS_SIZE -> app_mem a.
Proof. exact (ACr.a_laws_fs_place _ _ _ _ _ (ACr.aa_laws ACr.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r17_law_fs_ok : forall H mem md FS, law_AH H mem md -> word_mem rsegs mem (ACr.as_tp ACr.ASYMS) FS ->
  0 <= FS < 2 ^ 64 -> ACr.a_fs_ok mem FS.
Proof.
  intros H mem md FS HAH Hw Hb.
  exact (proj1 (ACr.a_laws_fs_state _ _ _ _ _ (ACr.aa_laws ACr.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw Hb)).
Qed.

Lemma r17_law_store : forall H mem mem' md, law_AH H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ACr.a_store_ok H (law_lo mem md) a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  law_AH H mem' md /\ (forall a, law_own H mem' md a <-> law_own H mem md a) /\ law_lo mem' md = law_lo mem md /\
  law_hi mem' md = law_hi mem md.
Proof. exact (ACr.a_laws_store _ _ _ _ _ (ACr.aa_laws ACr.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r17_law_fs_store : forall H mem mem' md FS, law_AH H mem md -> word_mem rsegs mem (ACr.as_tp ACr.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ACr.a_store_ok H (law_lo mem md) a -> ~ (FS <= a < FS + ACr.FS_SIZE) ->
     ~ (exists b, FS <= b < FS + ACr.FS_SIZE /\ a = shadow_addr b) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) -> ACr.a_fs_ok mem' FS ->
  law_AH H mem' md /\ (forall a, law_own H mem' md a <-> law_own H mem md a) /\ law_lo mem' md = law_lo mem md /\
  law_hi mem' md = law_hi mem md.
Proof. exact (ACr.a_laws_fs_store _ _ _ _ _ (ACr.aa_laws ACr.ASYMS AsanRTInv.RT (APIf rc))). Qed.

(* AH after the callee store W = [sp-16, sp) U [fr+2528, fr+2540): real arm by a_laws_store, side arm by
   a_laws_fs_store (the port cells lie inside the FakeStack, above its metadata). *)
Lemma r17_ah : forall g fr hb regs mem mem' md,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch [(ACr.aspZ regs - 16, ACr.aspZ regs); (fr + 2528, fr + 2528 + 12)] mem mem' ->
  Frame.wmono rsegs mem mem' -> rd_mono mem mem' ->
  ACr.aa_AH ACr.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
  (forall a, ACr.a_in_img a ->
     ACr.aa_owned ACr.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a ->
     ACr.aa_owned ACr.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a) /\
  ACr.aa_stklo ACr.ASYMS AsanRTInv.RT (APIf rc) mem' md = ACr.aa_stklo ACr.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  ACr.aa_stkhi ACr.ASYMS AsanRTInv.RT (APIf rc) mem' md = ACr.aa_stkhi ACr.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem mem' md HFRA MU WM HRDM.
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hlowin & Hstkwin).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  rewrite Haspz in MU, Hlowin.
  assert (HSS : AFr.SLOT_STACK = 1048576) by reflexivity.
  assert (HFSsz : ACr.FS_SIZE = 11571200) by reflexivity.
  unfold FN_STACK in Hlowin.
  pose proof (ACr.a_laws_stack_high ACr.ASYMS _ _ _ _ (ACr.aa_laws ACr.ASYMS AsanRTInv.RT (APIf rc))
                (hb ++ g_H g) mem md HAH) as Hhigh.
  unfold stk in Hwin. destruct Hwin as (Hwlo & Hwhi & _).
  assert (HWR : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a).
  { intros a _ Ha. exact (WM (Z_to_bv 64 a) Ha). }
  destruct Hloc as [(H0 & Hspfr & Hreal)|(Hfr0 & HfsbS & Hfs & _)].
  - (* real arm: W is wholly in [stklo, APPMEM) *)
    assert (Hunch : forall a, 0 <= a < 2 ^ 64 ->
      ~ ACr.a_store_ok (hb ++ g_H g) (ACr.aa_stklo ACr.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia. cbn [Frame.outside].
      split; [|split; [|exact I]]; intro Hin.
      - apply Hns. unfold ACr.a_store_ok. right; left. split; lia.
      - apply Hns. unfold ACr.a_store_ok. right; left. exact (Hreal a ltac:(lia)). }
    destruct (r17_law_store
                (hb ++ g_H g) mem mem' md HAH Hunch HWR) as (HAH' & HOWN' & HSTK' & HSHI').
    split; [exact HAH'|]. split; [intros a _ Ha; exact (proj2 (HOWN' a) Ha)|].
    split; [exact HSTK' | exact HSHI'].
  - (* side arm: the port cells lie inside the FakeStack *)
    destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FSb & HFSb0 & HwFSb & HFSbr).
    pose proof (HfsbS FSb HwFSb HFSb0) as HfrGE.
    pose proof (r17_law_fs_place
                  (hb ++ g_H g) mem md FSb HAH HwFSb HFSb0) as (HGTfs & HFSstk & _ & _).
    assert (HFSz : FSb + ACr.FS_SIZE <= 2 ^ 64) by lia.
    pose proof (r17_law_fs_ok
                  (hb ++ g_H g) mem md FSb HAH HwFSb HFSb0) as Hfsok.
    assert (HPres : forall q0, 0 <= q0 < 2 ^ 64 -> (exists b, mbyte rsegs mem q0 = Some b) ->
                    (exists b, mbyte rsegs mem' q0 = Some b)).
    { intros q0 Hq0 Hp. apply (HRDM (wa q0)). exact Hp. }
    assert (Hfsok' : ACr.a_fs_ok mem' FSb).
    { apply (a_fs_ok_pres [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] mem mem' FSb Hfsok MU HWR HPres).
      - intros q0 Hmeta. pose proof (fs_meta_below FSb q0 Hmeta) as Hbelow.
        cbn [Frame.outside]. split; [|split; [|exact I]]; intro Hin; lia.
      - lia.
      - exact HFSz. }
    assert (Hunch : forall a, 0 <= a < 2 ^ 64 ->
      ~ ACr.a_store_ok (hb ++ g_H g) (ACr.aa_stklo ACr.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      ~ (FSb <= a < FSb + ACr.FS_SIZE) ->
      ~ (exists bb, FSb <= bb < FSb + ACr.FS_SIZE /\ a = shadow_addr bb) ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns HnFS Hnsh. apply MU. rewrite MState.unsigned_lit by lia. cbn [Frame.outside].
      split; [|split; [|exact I]]; intro Hin.
      - apply Hns. unfold ACr.a_store_ok. right; left. split; lia.
      - apply HnFS. split; lia. }
    destruct (r17_law_fs_store
                (hb ++ g_H g) mem mem' md FSb HAH HwFSb HFSb0 Hunch HWR Hfsok')
      as (HAH' & HOWN' & HSTK' & HSHI').
    split; [exact HAH'|]. split; [intros a _ Ha; exact (proj2 (HOWN' a) Ha)|].
    split; [exact HSTK' | exact HSHI'].
Qed.

Lemma seg_R17 : forall b, Hat B APIf ra (Inv_A81858_at (fx:=fx) B APIf ra) b ->
  Hat B APIf ra (Inv_A8183c_at (fx:=fx) B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros b Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hbody).
  destruct Hbody as ((Hgn & Hb6 & HHB & H23 & HOUR & HOUTA & HCUR & Hsp216) & Hb0 & HRF & Ha0 &
    Hsp112 & Hsp16 & Hsp8 & Hsp192 & HAQ & Hsp128 & HPRO & Hsp104 & Hsp96 & Hsp64 & H21 & Hsp144 & Hsp208 &
    HRWid & HRWjk & Hsp280 & Hsp240 & HRWjy & HRWsc & Hsp152 & HAD38 & HRXS).
  subst c. subst b.
  (* names from FRA *)
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAGf & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (fra_win B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (Hlowin & Hstkwin).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (Hfrpl & Hfr9 & Hfspl & Hfrwr).
  pose proof (fra_app B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as (HGTfr & Hframeapp).
  pose proof (sl_frame_apart_win B APIf ra g fr (hb1 phi (rnb g 0)) regs mem md HFRA) as Hapart.
  rewrite Haspz in Hlowin, Hstkwin, Hapart.
  assert (HSS : AFr.SLOT_STACK = 1048576) by reflexivity.
  unfold FN_STACK in Hlowin, Hstkwin.
  pose proof (ACr.a_laws_stack_high ACr.ASYMS _ _ _ _ (ACr.aa_laws ACr.ASYMS AsanRTInv.RT (APIf rc))
                (hb1 phi (rnb g 0) ++ g_H g) mem md HAH) as Hhigh.
  assert (HSPstrong : HIGHMEM_BEG + 1044480 <= sp) by (unfold HIGHMEM_BEG in *; lia).
  (* RT facts: asan_cells, shadow_rw *)
  destruct HRT as (HAC & HSW & HasO & HCF & HasR & HREAL & HasRest).
  (* round-trip lengths *)
  pose proof HRF as ((Hb6' & HCUR' & HOUR' & H23' & HIDB & HFGB) & Hnz & H24 & HF).
  destruct (a_rtn (g_in g) (Z.of_nat 0) Hnz) as (_ & Hnb & HL).
  change (rt_n (g_in g) (Z.of_nat 0)) with (rnb g 0) in Hnb, HL.
  change (Z.of_nat 0) with 0 in HL, HF.
  (* phi placement *)
  pose proof (a_hb B APIf ra g fr phi (rnb g 0) regs mem md HFRA) as (Hphi0' & Hphi4096 & Hphistk & Hein & Hphibytes).
  (* A in range *)
  assert (HA0 : 0 <= A) by (unfold stk in Hwin; lia).
  assert (HA2 : A + 416 <= g_S g) by exact HA416.
  assert (HSle : g_S g <= 2 ^ 64) by (unfold stk in Hwin; lia).
  assert (HAlt : A + 224 <= 2 ^ 64) by lia.
  assert (HA312 : A + 312 <= 2 ^ 64) by lia.
  assert (HspBig : 17594334539776 <= sp) by (unfold HIGHMEM_BEG in *; lia).
  assert (Hspapp : forall x, sp - 16 <= x < sp -> app_mem x).
  { intros x Hx. unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (Hframe8 : fr mod 8 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  (* phi bounds *)
  assert (Hphi50 : phi + 50 <= 2 ^ 64).
  { assert (Hstkle : ACr.aa_stklo ACr.ASYMS AsanRTInv.RT (APIf rc) mem md <= g_S g - AFr.SLOT_STACK) by exact Hstklo.
    lia. }
  (* the two spilled loads as ro cells *)
  pose proof (r17_spill_ro regs mem 112 (mrow (g_in g)) A Hsp112 Hr9 HA0 ltac:(lia) ltac:(lia)) as RO1.
  pose proof (r17_spill_ro regs mem 216 (fr + 2528) A Hsp216 Hr9 HA0 ltac:(lia) ltac:(lia)) as RO2.
  (* addressable (phi+18) 20 *)
  assert (Hsz : ACr.a_size (rnb g 0) = rnb g 0) by (unfold ACr.a_size; lia).
  destruct HHB as (Hphinz & HAphi). rewrite Hsz in HAphi.
  assert (HAp : addressable mem (phi + 18) 20) by (apply (addressable_sub mem phi (rnb g 0) 18 20 HAphi); lia).
  (* bs = rt_pbs, bytes at phi+18 *)
  assert (Hlen50 : (50 <= length (rt_F (g_in g) 0))%nat) by (rewrite HL; lia).
  assert (EX : rt_pbs (g_in g) = firstn 20 (skipn 18 (rt_F (g_in g) 0))).
  { unfold rt_pbs, RcFrag.bsl, rt_g, fr50.
    change (Z.to_nat 20) with 20%nat. change (Z.to_nat 18) with 18%nat.
    rewrite firstn_app. replace (50 - length (rt_F (g_in g) 0))%nat with 0%nat by lia.
    rewrite firstn_O, app_nil_r, skipn_firstn_comm, firstn_firstn.
    rewrite Nat.min_l by lia. reflexivity. }
  assert (HLS : bytes_at rsegs mem (phi + 18) (firstn 20 (skipn 18 (rt_F (g_in g) 0)))).
  { pose proof HF as HF'. rewrite <- (firstn_skipn 18 (rt_F (g_in g) 0)) in HF'.
    apply bytes_at_app in HF' as [_ HF'].
    rewrite length_firstn, Nat.min_l in HF' by lia.
    rewrite <- (firstn_skipn 20 (skipn 18 (rt_F (g_in g) 0))) in HF'.
    apply bytes_at_app in HF' as [HF' _]. exact HF'. }
  rewrite <- EX in HLS.
  assert (Hpbslen : length (rt_pbs (g_in g)) = 20%nat).
  { rewrite EX, length_firstn, length_skipn. rewrite Nat.min_l by lia. reflexivity. }
  (* ports_ok true *)
  assert (Hok : RcLeaf.ports_ok (phi + 18) (fr + 2528) (rt_pbs (g_in g)) = true).
  { unfold RcLeaf.ports_ok. rewrite (B3Rtm.a_rtm_decl (g_in g)), !andb_true_r.
    apply andb_true_intro. split; apply negb_true_iff; apply Z.eqb_neq; unfold ACr.GT in HGTfr; lia. }
  (* wr_at q 12 *)
  assert (HWRq : wr_at rsegs mem (fr + 2528) 12).
  { unfold ACr.GT in HGTfr. split; [lia|]. split; [lia|]. intros i Hi. apply (Hfrwr (fr + 2528 + i)); lia. }
  (* q window app_mem *)
  pose proof (addressable_app mem (fr + 2528) 12 HAQ) as Happq.
  (* the outside premise *)
  assert (HOutside : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
            Frame.outside [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] x).
  { intros x Hx. cbn [Frame.outside]. split; [|split; [|exact I]]; intro Hin.
    - destruct Hx as [HG|[HC|HSh]].
      + unfold GOT_CELL_K, HIGHMEM_BEG in *; lia.
      + unfold CELL_K, HIGHMEM_BEG in *; lia.
      + unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *; lia.
    - destruct Hx as [HG|[HC|HSh]].
      + unfold GOT_CELL_K, ACr.GT in *; lia.
      + unfold CELL_K, ACr.GT in *; lia.
      + pose proof (Happq x ltac:(lia)) as Happx.
        unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *; lia. }
  (* the heap block [phi, phi+rnb) and the frame [fr, fr+3136) are disjoint: on the real arm the block is below
     stklo <= sp = fr; on the side arm the frame is in the FakeStack and a block byte never is. *)
  assert (Hblkfr : fr + FRAME_BYTES <= phi \/ phi + rnb g 0 <= fr).
  { destruct Hloc as [(H0' & Hspfr & Hreal)|(Hfr0' & HfsbS & Hfs & _)].
    - right. lia.
    - destruct (Z_le_gt_dec (fr + FRAME_BYTES) phi) as [Hle|Hgt]; [left; exact Hle|].
      destruct (Z_le_gt_dec (phi + rnb g 0) fr) as [Hle2|Hgt2]; [right; exact Hle2|].
      exfalso.
      pose proof (r17_law_blocks
                    (hb1 phi (rnb g 0) ++ g_H g) mem md phi (rnb g 0) HAH
                    ltac:(unfold hb1; apply in_or_app; left; apply in_eq)) as (_ & _ & _ & _ & Hbb).
      destruct (Hbb (Z.max phi fr) ltac:(lia)) as (_ & _ & _ & _ & Hnfs).
      exact (Hnfs (Hfs (Z.max phi fr) ltac:(lia))). }
  assert (Hdisj : fr + 2528 + 12 <= phi + 18 \/ phi + 18 + 20 <= fr + 2528)
    by (destruct Hblkfr as [Hc|Hc]; [left; lia | right; lia]).
  assert (Hq4 : (fr + 2528) mod 4 = 0) by (clear - Hfrm; Z.div_mod_to_equations; lia).
  assert (Hsep2 : fr + 2528 + 12 <= sp - 16 \/ sp <= fr + 2528).
  { destruct (Hfrpl 16 ltac:(unfold FN_STACK; lia)) as [Hc|Hc]; rewrite Haspz in Hc; [left; lia | right; lia]. }
  (* run *)
  rewrite SEGS.
  eapply (sl_run_lib regs (Z_to_bv 64 0x8183c) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x81858 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\
       getr R 22 = getr regs 22 /\
       getr R 23 = getr regs 23 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       getr R 24 = Z_to_bv 64 phi /\ getr R 10 = Z_to_bv 64 0 /\ getr R 27 = Z_to_bv 64 (phi + 18) /\
       Frame.munch [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] mem mem' /\ Frame.wmono rsegs mem mem' /\
       stk rsegs mem' (sp - (AFr.SLOT_STACK - 4096)) sp /\
       bytes_at rsegs mem' (fr + 2528) (le4 (Z_to_bv 64 (4 * RcLeaf.n_in (rt_pbs (g_in g))))) /\
       bytes_at rsegs mem' (fr + 2528 + 4) (le4 (Z_to_bv 64 (4 * RcLeaf.n_out (rt_pbs (g_in g))))) /\
       bytes_at rsegs mem' (fr + 2528 + 8) (le4 (Z_to_bv 64 (16 * RcLeaf.bt (rt_pbs (g_in g)) 7))))
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    unfold rg in Ha0, H24.
    eapply evt_mono.
    + apply (r17_evt PP) with (spv := sp) (A := A) (phi := phi) (q := fr + 2528) (mr := mrow (g_in g))
        (lo := sp - (AFr.SLOT_STACK - 4096)) (bs := rt_pbs (g_in g)).
      all: try assumption.
      all: unfold ACr.GT in HGTfr; lia.
    + intros ms' (R & m' & Hms & P2 & P3 & P4 & P8 & P9 & P19 & P21 & P22 & P23 & P25 & P26 & P24 & P10 & P27 &
                  MUq & WMq & STq & HIq & HOq & H8q).
      exists R, (Z_to_bv 64 0x81858), m'. split; [exact Hms|].
      split; [reflexivity|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
      split; [exact P9|]. split; [exact P19|]. split; [exact P21|]. split; [exact P22|].
      split; [exact P23|].
      split; [exact P25|]. split; [exact P26|]. split; [exact P24|]. split; [exact P10|]. split; [exact P27|].
      split; [exact MUq|]. split; [exact WMq|]. split; [exact STq|].
      split; [exact HIq|]. split; [exact HOq | exact H8q].
  - intros R pc' mem' regs'' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K25 & K26 & K24 & K10 & K27 &
       MU & WM & STk & HIc & HOc & H8c) Hreg Hmat.
    subst pc'.
    (* read-monotonicity across the write set *)
    assert (HRDM : rd_mono mem mem').
    { apply (rd_mono_list [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)] mem mem' MU).
      constructor; [|constructor; [|constructor]].
      - cbn [fst snd]. intros y Hy. exact (rd_of_stk mem' (sp - (AFr.SLOT_STACK - 4096)) sp STk y ltac:(lia)).
      - cbn [fst snd]. intros y Hy.
        destruct HIc as (_ & _ & HIcr). destruct HOc as (_ & _ & HOcr). destruct H8c as (_ & _ & H8cr).
        destruct (Z_lt_le_dec y (fr + 2528 + 4)) as [Hy1|Hy1].
        { pose proof (HIcr (Z.to_nat (y - (fr + 2528))) ltac:(rewrite length_le4; lia)) as Hb.
          replace (fr + 2528 + Z.of_nat (Z.to_nat (y - (fr + 2528)))) with y in Hb by lia.
          destruct (nth_error (le4 (Z_to_bv 64 (4 * RcLeaf.n_in (rt_pbs (g_in g)))))
                      (Z.to_nat (y - (fr + 2528)))) as [b|] eqn:E;
            [exists b; rewrite Hb; first [exact E | reflexivity]|].
          apply nth_error_None in E. rewrite length_le4 in E. lia. }
        destruct (Z_lt_le_dec y (fr + 2528 + 8)) as [Hy2|Hy2].
        { pose proof (HOcr (Z.to_nat (y - (fr + 2528 + 4))) ltac:(rewrite length_le4; lia)) as Hb.
          replace (fr + 2528 + 4 + Z.of_nat (Z.to_nat (y - (fr + 2528 + 4)))) with y in Hb by lia.
          destruct (nth_error (le4 (Z_to_bv 64 (4 * RcLeaf.n_out (rt_pbs (g_in g)))))
                      (Z.to_nat (y - (fr + 2528 + 4)))) as [b|] eqn:E;
            [exists b; rewrite Hb; first [exact E | reflexivity]|].
          apply nth_error_None in E. rewrite length_le4 in E. lia. }
        { pose proof (H8cr (Z.to_nat (y - (fr + 2528 + 8))) ltac:(rewrite length_le4; lia)) as Hb.
          replace (fr + 2528 + 8 + Z.of_nat (Z.to_nat (y - (fr + 2528 + 8)))) with y in Hb by lia.
          destruct (nth_error (le4 (Z_to_bv 64 (16 * RcLeaf.bt (rt_pbs (g_in g)) 7)))
                      (Z.to_nat (y - (fr + 2528 + 8)))) as [b|] eqn:E;
            [exists b; rewrite Hb; first [exact E | reflexivity]|].
          apply nth_error_None in E. rewrite length_le4 in E. lia. } }
    (* AH after the store *)
    assert (MUa : Frame.munch [(ACr.aspZ regs - 16, ACr.aspZ regs); (fr + 2528, fr + 2528 + 12)] mem mem').
    { rewrite Haspz. exact MU. }
    pose proof (r17_ah g fr (hb1 phi (rnb g 0)) regs mem mem' md HFRA MUa WM HRDM)
      as (HAH' & HOWN' & HSTK' & HSHI').
    (* the write set is app + rt_disjoint, and misses the FRA-read cells *)
    set (W := [(sp - 16, sp); (fr + 2528, fr + 2528 + 12)]).
    unfold ACr.GT in HGTfr.
    assert (HAW : all_app W).
    { unfold W. cbn [all_app app_ivl]. split; [|split; [|exact I]].
      - intros a Ha. exact (Hspapp a Ha).
      - intros a Ha. exact (Happq a ltac:(lia)). }
    assert (HDJ : rt_disjoint W).
    { unfold W, rt_disjoint; cbn [disjoint_from].
      unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
        RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN in *.
      repeat split; left; lia. }
    assert (HWlo : forall x, 0 <= x < 6283264 -> Frame.outside W x).
    { intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    assert (HWhdr : forall x, fr <= x < fr + 24 -> Frame.outside W x).
    { intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]].
      - intro Hc. apply (Hapart x ltac:(lia)); lia.
      - lia. }
    assert (HWspill : forall A0, getr regs 9 = Z_to_bv 64 A0 -> forall x, A0 + 304 <= x < A0 + 312 -> Frame.outside W x).
    { intros A0 E x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]].
      - apply (r17_wrap_out A A0 (sp - 16) sp x ltac:(rewrite <- Hr9; exact E)); lia.
      - apply (r17_wrap_out A A0 (fr + 2528) (fr + 2528 + 12) x ltac:(rewrite <- Hr9; exact E)); lia. }
    assert (HWsel : forall A0, getr regs 9 = Z_to_bv 64 A0 -> forall x, A0 + 16 <= x < A0 + 32 -> Frame.outside W x).
    { intros A0 E x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]].
      - apply (r17_wrap_out A A0 (sp - 16) sp x ltac:(rewrite <- Hr9; exact E)); lia.
      - apply (r17_wrap_out A A0 (fr + 2528) (fr + 2528 + 12) x ltac:(rewrite <- Hr9; exact E)); lia. }
    assert (HWsaved : forall x, g_S g - 104 <= x < g_S g -> Frame.outside W x).
    { intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    assert (HWsh : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> Frame.outside W x).
    { intros x Hx.
      assert (Hin : in_shadow x).
      { assert (Ex : shadow_addr (fr + 8 * (x - Sfr fr)) = x)
          by (rewrite (sh_add8 fr (x - Sfr fr) Hframe8); unfold Sfr; lia).
        rewrite <- Ex. apply AsanRTFacts.shadow_of_app. apply Hframeapp. unfold Sfr in *. lia. }
      unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; intro Hc.
      - exact (AsanRTFacts.app_not_shadow x (Hspapp x Hc) Hin).
      - exact (AsanRTFacts.app_not_shadow x (Happq x ltac:(lia)) Hin). }
    assert (Hrokeep : ro_agree rsegs mem').
    { apply (r17_ro_keep mem mem' W Hro MU). intros a Hroa.
      pose proof (r17_ro_lt a Hroa) as Hlt. unfold W. cbn [Frame.outside].
      split; [|split; [|exact I]]; lia. }
    assert (HWfs : forall FS x, word_mem rsegs mem (ACr.as_tp ACr.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
      FS <= x < FS + ACr.FS_SIZE -> ~ (fr + 24 <= x < fr + FRAME_BYTES) -> Frame.outside W x).
    { intros FS x Hwtp HFS Hx Hnbody.
      pose proof (r17_law_fs_place
                    (hb1 phi (rnb g 0) ++ g_H g) mem md FS HAH Hwtp HFS) as (_ & HFSstk & _ & _).
      unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    assert (HWcase : forall x, 0 <= x < 2 ^ 64 -> Frame.outside W x \/
      (g_S g - AFr.SLOT_STACK <= x < g_S g) \/ (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
    { intros x Hx.
      destruct (Z_le_gt_dec (sp - 16) x) as [A1|A1]; destruct (Z_lt_ge_dec x sp) as [A2|A2];
        destruct (Z_le_gt_dec (fr + 2528) x) as [B1|B1];
        destruct (Z_lt_ge_dec x (fr + 2528 + 12)) as [B2|B2];
        first [ right; left; lia
              | right; right; left; lia
              | left; unfold W; cbn [Frame.outside]; split; [lia | split; [lia | exact I]] ]. }
    assert (HENT' : ENT APIf g (hb1 phi (rnb g 0)) mem' md).
    { eapply ent_store;
        [ exact HENT | exact HFRA | exact MU | exact HWcase | exact HSTK' | exact HSHI' | exact HOWN' ]. }
    assert (HFRAmd : FRA B APIf ra g fr (hb1 phi (rnb g 0)) regs'' mem' md).
    { apply (B3FrCl.b3_fr_cl B APIf ra empty FF g fr (hb1 phi (rnb g 0)) regs regs'' mem mem' md W HFRA MU WM
        Hrokeep HAW HDJ HAH' HSTK' HWlo HWhdr (fun A0 E _ => HWspill A0 E) (fun A0 E _ => HWsel A0 E)
        HWsaved HWsh HWfs HRDM);
        (rewrite Hreg; assumption). }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (rnb g 0)) regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (rnb g 0)) regs'' regs'' mem' md md' HFRAmd);
        try reflexivity. exact Hmat. }
    (* keep facts across the run *)
    assert (HHB' : HB mem' phi (rnb g 0)).
    { split; [exact Hphinz|]. rewrite Hsz. exact (sl_addr_keep mem mem' W phi (rnb g 0) HAphi MU HAW). }
    assert (Hapart16 : forall x, fr <= x < fr + 2528 \/ fr + 2540 <= x < fr + FRAME_BYTES -> Frame.outside W x).
    { intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]].
      - intro Hc. apply (Hapart x ltac:(lia)); lia.
      - lia. }
    assert (HOUR'' : OURb g fr mem').
    { unfold OURb in *. apply (a_keep W mem mem' (fr + 2624) (OUR (g_in g)) MU).
      - rewrite OUR_length. intros x Hx. apply Hapart16. lia.
      - exact HOUR'. }
    assert (H23'' : rg regs'' 23 (Z.of_nat 0))
      by (unfold rg in *; transitivity (getr R 23); [exact (Hreg _) | transitivity (getr regs 23); [exact K23 | exact H23']]).
    assert (HCUR'' : CUR g 7 regs'').
    { destruct HCUR' as (Hc0 & Hc22 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split;
        [ transitivity (getr R 22); [exact (Hreg _) | transitivity (getr regs 22); [exact K22 | exact Hc22]]
        | transitivity (getr R 25); [exact (Hreg _) | transitivity (getr regs 25); [exact K25 | exact Hc25]] ]. }
    assert (H24'' : rg regs'' 24 phi)
      by (unfold rg in *; transitivity (getr R 24); [exact (Hreg _) | exact K24]).
    assert (HIDB'' : IDBr g fr (RID (g_in g) 0) mem').
    { unfold IDBr in *. apply (a_keep W mem mem' (fr + 2176) (RID (g_in g) 0) MU).
      - assert (LI : length (RID (g_in g) 0) = 38%nat) by reflexivity.
        rewrite LI. intros x Hx. apply Hapart16. lia.
      - exact HIDB. }
    assert (HFGB'' : FGBr g fr (RFG (g_in g) 0) mem').
    { unfold FGBr in *. apply (a_keep W mem mem' (fr + 2256) (RFG (g_in g) 0) MU).
      - assert (LF : length (RFG (g_in g) 0) = 72%nat) by reflexivity.
        rewrite LF. intros x Hx. apply Hapart16. lia.
      - exact HFGB. }
    assert (HF'' : bytes_at rsegs mem' phi (rt_F (g_in g) 0)).
    { apply (a_keep W mem mem' phi (rt_F (g_in g) 0) MU); [|exact HF].
      rewrite HL. intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]].
      - rewrite Z2Nat.id in Hx by lia. unfold rnb in *. lia.
      - rewrite Z2Nat.id in Hx by lia. unfold rnb in *. lia. }
    assert (HRFb'' : RFb g fr 0 (RID (g_in g) 0) (RFG (g_in g) 0) phi regs'' mem').
    { split.
      { split; [exact Hb6'|]. split; [exact HCUR''|]. split; [exact HOUR''|]. split; [exact H23''|].
        split; [exact HIDB'' | exact HFGB'']. }
      split; [exact Hnz|]. split; [exact H24'' | exact HF'']. }
    (* spills kept *)
    assert (Hsp192'' : spill regs'' mem' 200 (decl_slot fr)).
    { apply (r17_spill_keep regs regs'' mem mem' 200 (decl_slot fr) A W Hsp192 Hr9 ltac:(transitivity (getr R 9); [lazymatch goal with |- _ = getr _ ?r => exact (Hreg r) end | exact K9]) HA0 ltac:(lia) ltac:(lia) MU).
      intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    assert (Hsp216'' : spill regs'' mem' 216 (fr + 2528)).
    { apply (r17_spill_keep regs regs'' mem mem' 216 (fr + 2528) A W Hsp216 Hr9 ltac:(transitivity (getr R 9); [lazymatch goal with |- _ = getr _ ?r => exact (Hreg r) end | exact K9]) HA0 ltac:(lia) ltac:(lia) MU).
      intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    assert (Hsp16'' : spill regs'' mem' 8 (mrow (g_in g) + 16)).
    { apply (r17_spill_keep regs regs'' mem mem' 8 (mrow (g_in g) + 16) A W Hsp16 Hr9 ltac:(transitivity (getr R 9); [lazymatch goal with |- _ = getr _ ?r => exact (Hreg r) end | exact K9]) HA0 ltac:(lia) ltac:(lia) MU).
      intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    assert (Hsp8'' : spill regs'' mem' 0 (mrow (g_in g) + 20)).
    { apply (r17_spill_keep regs regs'' mem mem' 0 (mrow (g_in g) + 20) A W Hsp8 Hr9 ltac:(transitivity (getr R 9); [lazymatch goal with |- _ = getr _ ?r => exact (Hreg r) end | exact K9]) HA0 ltac:(lia) ltac:(lia) MU).
      intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    assert (Hsp112'' : spill regs'' mem' 112 (mrow (g_in g))).
    { apply (r17_spill_keep regs regs'' mem mem' 112 (mrow (g_in g)) A W Hsp112 Hr9 ltac:(transitivity (getr R 9); [lazymatch goal with |- _ = getr _ ?r => exact (Hreg r) end | exact K9]) HA0 ltac:(lia) ltac:(lia) MU).
      intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    (* ENT at the exit model *)
    assert (HENT'' : ENT APIf g (hb1 phi (rnb g 0)) mem' md').
    { eapply ent_mat; [exact HENT' | exact Hmat]. }
    (* the R21 facts kept across the call *)
    assert (K9' : getr regs'' 9 = getr regs 9).
    { transitivity (getr R 9); [lazymatch goal with |- _ = getr _ ?r => exact (Hreg r) end | exact K9]. }
    assert (Hsp128'' : spill regs'' mem' 128 (fr + 544)).
    { apply (r17_spill_keep regs regs'' mem mem' 128 (fr + 544) A W Hsp128 Hr9 K9' HA0 ltac:(lia) ltac:(lia) MU).
      intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    (* PRO: the spills are above the port cells and sp; our[]'s and the input block's shadow bytes are kept since W
       is application memory; the input block is a live block of the entry heap, below stklo (so below sp - 16)
       and apart from the frame (on the real arm the frame is at or above stklo, on the side arm it is in the side
       stack, which no block byte is), so outside W *)
    assert (HINk : (0 < g_n g -> In (g_p g, g_n g) (g_H g)) ->
              bytes_at rsegs mem (g_p g) (g_in g) -> bytes_at rsegs mem' (g_p g) (g_in g)).
    { intros Hin HIN. apply (a_keep W mem mem' (g_p g) (g_in g) MU); [|exact HIN].
      intros x Hx. rewrite <- g_n_len in Hx.
      destruct (r17_law_blocks
                  (hb1 phi (rnb g 0) ++ g_H g) mem md (g_p g) (g_n g) HAH
                  (in_or_app _ _ _ (or_intror (Hin ltac:(lia))))) as (_ & _ & Hpend & _ & Hpb).
      destruct (Hpb x Hx) as (_ & _ & _ & _ & Hnfsx).
      assert (Hstkle : ACr.aa_stklo ACr.ASYMS AsanRTInv.RT (APIf rc) mem md <= g_S g - AFr.SLOT_STACK)
        by exact Hstklo.
      assert (Hxfr : ~ (fr <= x < fr + FRAME_BYTES)).
      { intros Hxf. destruct Hloc as [(H0' & Hspfr & Hreal)|(Hfr0' & HfsbS & Hfs & _)].
        - pose proof (Hreal x Hxf). lia.
        - exact (Hnfsx (Hfs x Hxf)). }
      unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    assert (HPRO'' : PRO g fr regs'' mem').
    { apply (r17_pro_keep g fr regs regs'' mem mem'); [| | exact HINk | | exact HPRO].
      - intros xoff xv Hxoff Hxs.
        apply (r17_spill_keep regs regs'' mem mem' xoff xv A W Hxs Hr9 K9' HA0 ltac:(lia) ltac:(lia) MU).
        intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia.
      - intros HA6. exact (sl_addr_keep mem mem' W (fr + 2624) 6 HA6 MU HAW).
      - intros _ HA. exact (sl_addr_keep mem mem' W (g_p g) (g_n g) HA MU HAW). }
    assert (Hsp104'' : spill regs'' mem' 104 0x21140).
    { apply (r17_spill_keep regs regs'' mem mem' 104 0x21140 A W Hsp104 Hr9 K9' HA0 ltac:(lia) ltac:(lia) MU).
      intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    assert (Hsp96'' : spill regs'' mem' 96 0x1234).
    { apply (r17_spill_keep regs regs'' mem mem' 96 0x1234 A W Hsp96 Hr9 K9' HA0 ltac:(lia) ltac:(lia) MU).
      intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    assert (Hsp64'' : spill regs'' mem' 64 0xe38f0000).
    { apply (r17_spill_keep regs regs'' mem mem' 64 0xe38f0000 A W Hsp64 Hr9 K9' HA0 ltac:(lia) ltac:(lia) MU).
      intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    (* out[] stays addressable: W is app memory, so no shadow byte changes *)
    assert (HOUTA'' : OUTA fr mem') by exact (outa_run fr mem mem' W HOUTA MU HAW).
    assert (Hsp144'' : spill regs'' mem' 144 (fr + 2688)).
    { apply (r17_spill_keep regs regs'' mem mem' 144 (fr + 2688) A W Hsp144 Hr9 K9' HA0 ltac:(lia) ltac:(lia) MU).
      intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    assert (Hsp208'' : spill regs'' mem' 192 (fr + 2768)).
    { apply (r17_spill_keep regs regs'' mem mem' 192 (fr + 2768) A W Hsp208 Hr9 K9' HA0 ltac:(lia) ltac:(lia) MU).
      intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    (* the frame cells fr + 2688 (38 bytes), fr + 2768 (72), fr + 3040 (1) and fr + 3056 (32): frame bytes above
       the port cells *)
    assert (HRWk : forall a n bs, fr + 2540 <= a -> a + Z.of_nat n <= fr + FRAME_BYTES ->
              rw_cells rsegs mem a [CB n bs] -> rw_cells rsegs mem' a [CB n bs]).
    { intros ca cn cbs Ha1 Ha2 HRWa. apply (r17_rwcb_keep W mem mem' _ _ _ MU WM); [|exact HRWa].
      intros x Hx. apply Hapart16. lia. }
    assert (HRWid'' : exists idb, rw_cells rsegs mem' (fr + 2688) [CB 38 idb]).
    { destruct HRWid as (idb & HRWi). exists idb. exact (HRWk (fr + 2688) 38%nat idb ltac:(lia) ltac:(lia) HRWi). }
    assert (HRWjk'' : exists junk, rw_cells rsegs mem' (fr + 2768) [CB 72 junk]).
    { destruct HRWjk as (junk & HRWj). exists junk. exact (HRWk (fr + 2768) 72%nat junk ltac:(lia) ltac:(lia) HRWj). }
    assert (Hsp280'' : spill regs'' mem' 280 (fr + 3040)).
    { apply (r17_spill_keep regs regs'' mem mem' 280 (fr + 3040) A W Hsp280 Hr9 K9' HA0 ltac:(lia) ltac:(lia) MU).
      intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    assert (Hsp240'' : spill regs'' mem' 240 (fr + 3056)).
    { apply (r17_spill_keep regs regs'' mem mem' 240 (fr + 3056) A W Hsp240 Hr9 K9' HA0 ltac:(lia) ltac:(lia) MU).
      intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    assert (HRWjy'' : exists jy, rw_cells rsegs mem' (fr + 3040) [CB 1 jy]).
    { destruct HRWjy as (jy & HRWy). exists jy. exact (HRWk (fr + 3040) 1%nat jy ltac:(lia) ltac:(lia) HRWy). }
    assert (HRWsc'' : exists junk, rw_cells rsegs mem' (fr + 3056) [CB 32 junk]).
    { destruct HRWsc as (junk & HRWs). exists junk. exact (HRWk (fr + 3056) 32%nat junk ltac:(lia) ltac:(lia) HRWs). }
    assert (Hsp152'' : spill regs'' mem' 152 (Sfr fr + 68)).
    { apply (r17_spill_keep regs regs'' mem mem' 152 (Sfr fr + 68) A W Hsp152 Hr9 K9' HA0 ltac:(lia) ltac:(lia) MU).
      intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    assert (H21'' : rg regs'' 21 (fr + 2176)).
    { unfold rg in *. transitivity (getr R 21);
        [lazymatch goal with |- _ = getr _ ?r => exact (Hreg r) end|].
      transitivity (getr regs 21); [exact K21 | exact H21]. }
    assert (HAD38'' : addressable mem' (fr + 2176) 38)
      by exact (sl_addr_keep mem mem' W (fr + 2176) 38 HAD38 MU HAW).
    (* RXS (push 10): the spills are above the port cells and sp, and W is application memory, so the fragment
       record's shadow bytes are kept *)
    assert (HRXS'' : RXS g fr regs'' mem').
    { apply (r17_rxs_keep g fr regs regs'' mem mem');
        [| intros HA72; exact (sl_addr_keep mem mem' W (fr + 2256) 72 HA72 MU HAW) | exact HRXS].
      intros xoff xv Hxoff Hxs.
      apply (r17_spill_keep regs regs'' mem mem' xoff xv A W Hxs Hr9 K9' HA0 ltac:(lia) ltac:(lia) MU).
      intros x Hx. unfold W. cbn [Frame.outside]. split; [|split; [|exact I]]; lia. }
    (* rebuild the exit cut *)
    rewrite <- SEGS. apply Hexit. exists phi, regs'', mem', md', fr.
    split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT''|].
    split.
    { split; [exact Hgn|]. split; [exact Hb6|]. split; [exact HHB'|]. split; [exact H23''|].
      split; [exact HOUR''|]. split; [exact HOUTA''|]. split; [exact HCUR'' | exact Hsp192'']. }
    split; [reflexivity|].
    split; [exact HRFb''|].
    split; [unfold rg in *; transitivity (getr R 27); [exact (Hreg _) | exact K27]|].
    split; [unfold a0v, rg in *; transitivity (getr R 10); [exact (Hreg _) | exact K10]|].
    split; [exact HIc|].
    split.
    { replace (fr + 2532) with (fr + 2528 + 4) by lia. exact HOc. }
    split; [exact Hsp216''|].
    split; [exact Hsp16''|].
    split; [exact Hsp8''|].
    split; [exact Hsp112''|].
    split; [exact Hsp128''|].
    split; [exact HPRO''|].
    split; [exact Hsp104''|].
    split; [exact Hsp96''|].
    split; [exact Hsp64''|].
    split; [exact H21''|].
    split; [exact Hsp144''|].
    split; [exact Hsp208''|].
    split; [exact HRWid''|].
    split; [exact HRWjk''|].
    split; [exact Hsp280''|].
    split; [exact Hsp240''|].
    split; [exact HRWjy''|].
    split; [exact HRWsc''|].
    split; [exact Hsp152''|].
    split; [exact HAD38'' | exact HRXS''].
Qed.

End R17W.
