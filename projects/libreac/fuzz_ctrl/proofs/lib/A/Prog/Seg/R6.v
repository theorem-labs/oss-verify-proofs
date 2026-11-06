(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths, module names, addresses and numbers changed; 1684 of its 1797 lines of code are new or changed and 898 lines of the source are left out. *)
(* Segment R6 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): [0x815cc, 0x815e8], turn b of the round trip,
   Inv_A815cc_at b -> Inv_A815ec_at b (both official, push 11F).  rule 24: no function proved (a slot segment).
   The eight instructions load the four build_as argument spills ([A+112] the catalogue row m, [A+168] our[] =
   fr+2624, [A+104] round_trip.box 0x21140, [A+96] 0x1234; a0 = fr+544 = out[] is already loaded at 0x815c8, in R5)
   and a2 = s7 = b, then call reac_ctrl_build_as (BAS@0x815e8, lib/A/Prog/reac_ctrl_build_as_c.v, a Section
   Hypothesis).  r6_evt is the Lib-level run of the eight instructions plus the call by its contract; seg_R6 lifts
   it to the cuts.  The class-0 / class-1 side-stack package of the call (fp [0; 1] + reac_ctrl_build_as_tls) is
   on no cut: Tac_fsfree.fra_fp gives it from FRA.  The write set of the segment is the callee window [sp - 4640, sp),
   the out[] frame [fr+544, fr+544+n_b), the class-0 and class-1 side-stack bytes fp_w [0;1] FS and the shadow of
   the window; ENT crosses it by ent_munch, and every exit fact the entry carries lies outside it. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcPorts RcBox RcSynth RcSynthLib RcLay
  RcFin RcFinLib RcEmit RcEmitLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_stack_malloc_c RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_build_as_c reac_box_model_block_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require reac_ctrl_build_as_c.
Import ListNotations.
Open Scope Z_scope.

Module BA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.
Module PB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.reac_ctrl_build_as_c.
Module RBM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_box_model_block_c.

(* A spilled word is a read-only cell for the load engine (a Theorem Labs lane's r7_q64_ro). *)
Lemma r6_q64_ro : forall (m : word -> option byte) (A v : Z),
  bytes_at rsegs m A (le8 (Z_to_bv 64 v)) -> ro_cells rsegs m A [C8 (Z_to_bv 64 v)].
Proof.
  intros m A v H. split; [split; [exact I | exact I] | cbn [cells_bytes]; rewrite app_nil_r; exact H].
Qed.

(* The control block the emitter writes is 32 bytes (Tac_rt2_b2.a_rtX_len for a general row). *)
Lemma r6_baX_len : forall mdv (mb nb : list byte) bb,
  length mb = 296%nat -> length (PB.ba_X mdv mb nb bb) = 32%nat.
Proof.
  intros mdv mb nb bb Hmb. unfold PB.ba_X, ly_Z.
  assert (HZ : length (if mdv =? 0 then ly_zero else if rc mb bb =? 1 then synth mb bb nb else ly_zero) = 32%nat).
  { destruct (mdv =? 0); [reflexivity|]. destruct (rc mb bb =? 1); [|reflexivity].
    apply rs_synth_len. exact Hmb. }
  destruct (bb <=? 1); [apply rcf_stamp32_len; exact HZ | exact HZ].
Qed.

(* The emitted frame has exactly len bytes (header 18 + block 32 + zero fill + trailer 2). *)
Lemma r6_emfr_len : forall (db sb : list byte) (c16 : Z) (t0 t1 : byte) (blk : list byte) (len : Z),
  length db = 6%nat -> length sb = 6%nat -> length blk = 32%nat -> 52 <= len ->
  Z.of_nat (length (em_fr db sb c16 t0 t1 blk len)) = len.
Proof.
  intros db sb c16 t0 t1 blk len H1 H2 H3 H4.
  unfold em_fr, em_hdr. rewrite !length_app, repeat_length, H1, H2, H3. cbn [length]. lia.
Qed.

(* A byte inside a byte list present in memory is readable. *)
Lemma r6_present : forall (m : word -> option byte) (a : Z) (bs : list byte) (x n : Z),
  bytes_at rsegs m a bs -> Z.of_nat (length bs) = n -> a <= x < a + n ->
  exists bx, mrd rsegs m (wa x) = Some bx.
Proof.
  intros m a bs x n (H0 & H1 & H) Hl Hx.
  assert (Hi : (Z.to_nat (x - a) < length bs)%nat) by lia.
  pose proof (H _ Hi) as Hrd. replace (a + Z.of_nat (Z.to_nat (x - a))) with x in Hrd by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [bx|] eqn:En; [exists bx; exact Hrd|].
  apply nth_error_None in En. lia.
Qed.

(* ---- the run: the four argument loads, a2 = s7, a6 = a7 = 0, and jal reac_ctrl_build_as by its contract ---- *)

Lemma r6_evt : BA.reac_ctrl_build_as_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A spv TPv o mdv bb d FS n len Rv : Z) (Eb : bool) (mb nb db sb junk : list byte),
    n = bm_uw mdv (firstn 8 (skipn 16 mb)) ->
    len = 52 + 36 * n ->
    Eb = PB.ba_E n mb bb ->
    Rv = (if PB.ba_go o mdv bb && Eb then len else 0) ->
    s1 = Z_to_bv 64 A -> sp = Z_to_bv 64 spv -> tp = Z_to_bv 64 TPv -> s7 = Z_to_bv 64 bb ->
    a0 = Z_to_bv 64 o ->
    0 <= A -> A + 176 <= 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= mdv < 2 ^ 64 -> 0 <= bb <= 6 ->
    0 <= d < 2 ^ 64 -> 0 <= TPv < 2 ^ 64 -> 0 <= spv < 2 ^ 64 ->
    bytes_at rsegs m (A + 96) (le8 (Z_to_bv 64 0x1234)) ->
    bytes_at rsegs m (A + 104) (le8 (Z_to_bv 64 0x21140)) ->
    bytes_at rsegs m (A + 112) (le8 (Z_to_bv 64 mdv)) ->
    bytes_at rsegs m (A + 168) (le8 (Z_to_bv 64 d)) ->
    spv mod 16 = 0 ->
    stk rsegs m (spv - BA.REAC_CTRL_BUILD_AS_K) spv ->
    bytes_at rsegs m (BA.BA_FR + 72) PB.ba_tbl ->
    ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv (BA.BA_FR + 72) (BA.BA_FR + 240) ->
    length db = 6%nat -> bytes_at rsegs m d db ->
    ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv d (d + 6) ->
    length sb = 6%nat -> bytes_at rsegs m 0x21140 sb ->
    ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv 0x21140 (0x21140 + 6) ->
    (mdv <> 0 -> mdv mod 8 = 0 /\ mdv + 296 <= 2 ^ 64 /\ length mb = 296%nat /\ bytes_at rsegs m mdv mb /\
                 ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv mdv (mdv + 296)) ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0 ->
       name_ok nb /\ bytes_at rsegs m (rname mb) nb /\
       ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv (rname mb) (rname mb + Z.of_nat (length nb))) ->
    (o <> 0 -> o + 1492 <= 2 ^ 64) ->
    (PB.ba_go o mdv bb && Eb = true ->
       rw_cells rsegs m o [CB (Z.to_nat len) junk] /\
       ly_dj (spv - BA.REAC_CTRL_BUILD_AS_K) spv o (o + len) /\
       ly_dj o (o + len) (BA.BA_FR + 72) (BA.BA_FR + 240) /\ ly_dj o (o + len) mdv (mdv + 296) /\
       (((bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0) ->
          ly_dj o (o + len) (rname mb) (rname mb + Z.of_nat (length nb))) /\
       ly_dj o (o + len) d (d + 6) /\ ly_dj o (o + len) 0x21140 (0x21140 + 6)) ->
    mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
    HIGHMEM_BEG <= spv - BA.REAC_CTRL_BUILD_AS_K -> spv <= APPMEM_END ->
    addressable m (spv - BA.REAC_CTRL_BUILD_AS_K) BA.REAC_CTRL_BUILD_AS_K ->
    addressable m BA.BA_SW 56 -> addressable m (BA.BA_FR + 72) 168 -> addressable m d 6 ->
    addressable m 0x21140 6 ->
    app_mem (d + 6) /\ app_mem (d + 7) -> app_mem (0x21140 + 6) /\ app_mem (0x21140 + 7) ->
    (mdv <> 0 -> addressable m mdv 296) ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0 ->
       addressable m (rname mb) (Z.of_nat (length nb))) ->
    (PB.ba_go o mdv bb && Eb = true ->
       addressable m o len /\ app_mem (o + len) /\ (o + len <= RT_LO \/ RT_HI <= o)) ->
    (bb = 1 -> addressable m RBM.JOIN_0014 32) ->
    (bb = 2 -> addressable m RBM.JOIN_0013 32) ->
    fp [0%nat; 1%nat] m TPv FS (spv - BA.REAC_CTRL_BUILD_AS_K) spv
      [(spv - BA.REAC_CTRL_BUILD_AS_K, spv); (o, o + Rv)]
      [(BA.BA_FR + 72, BA.BA_FR + 240); (mdv, mdv + 296); (d, d + 6); (0x21140, 0x21140 + 6); (o, o + Rv)] ->
    (mdv <> 0 -> (bb = 5 \/ bb = 6) /\ has mb <> 0 /\ rname mb <> 0 ->
       fp_dj [(rname mb, rname mb + Z.of_nat (length nb))] (fp_w [0%nat; 1%nat] FS)) ->
    BA.reac_ctrl_build_as_tls m TPv FS (spv - BA.REAC_CTRL_BUILD_AS_K) spv ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x815ec) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 Rv)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x815ec) fc None m' (seg_rom rsegs)
         /\ munch ([(spv - BA.REAC_CTRL_BUILD_AS_K, spv); (o, o + Rv)] ++ fp_w [0%nat; 1%nat] FS ++
                   [(shadow_addr (spv - BA.REAC_CTRL_BUILD_AS_K), shadow_addr spv)]) m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (spv - BA.REAC_CTRL_BUILD_AS_K) spv
         /\ asan_cells m' /\ shadow_rw m'
         /\ addressable m' (spv - BA.REAC_CTRL_BUILD_AS_K) BA.REAC_CTRL_BUILD_AS_K
         /\ fp [0%nat; 1%nat] m' TPv FS (spv - BA.REAC_CTRL_BUILD_AS_K) spv
              [(spv - BA.REAC_CTRL_BUILD_AS_K, spv); (o, o + Rv)]
              [(BA.BA_FR + 72, BA.BA_FR + 240); (mdv, mdv + 296); (d, d + 6); (0x21140, 0x21140 + 6); (o, o + Rv)]
         /\ (forall x, o <= x < o + Rv -> exists bx, mrd rsegs m' (wa x) = Some bx)
         /\ (PB.ba_go o mdv bb && Eb = true ->
               bytes_at rsegs m' o (em_fr db sb 0x1234 (Z_to_bv 8 205) (Z_to_bv 8 234) (PB.ba_X mdv mb nb bb) len)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x815cc) fc None m (seg_rom rsegs)).
Proof.
  intros BUILD ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A spv TPv o mdv bb d FS n len Rv Eb mb nb db sb junk
    Hn Hlen HEb HRv -> -> -> -> -> HA0 HA1 Ho Hmd Hbb Hd HTP Hspv C96 C104 C112 C168
    H16 ST HBA HBAdj Hdbl HD HDdj Hsbl HS HSdj HM HNM Hobnd HO HMI HAC HSW HHM HAE HAW HSW56 HAWba HAWd HAWs
    HDapp HSapp HMa HNa HOa HJ14 HJ13 HFP HFPN HTLS.
  pose proof (r6_q64_ro m (A + 96) 0x1234 C96) as RW96.
  pose proof (r6_q64_ro m (A + 104) 0x21140 C104) as RW104.
  pose proof (r6_q64_ro m (A + 112) mdv C112) as RW112.
  pose proof (r6_q64_ro m (A + 168) d C168) as RW168.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  subst Rv Eb len n.
  step.                                (* 815cc ld a1,112(s1) *)
  step.                                (* 815d0 mv a2,s7 *)
  step.                                (* 815d4 ld a3,168(s1) *)
  step.                                (* 815d8 ld a4,104(s1) *)
  step.                                (* 815dc ld a5,96(s1) *)
  step.                                (* 815e0 li a6,0 *)
  step.                                (* 815e4 li a7,0 *)
  step.                                (* 815e8 jal 847e4 reac_ctrl_build_as *)
  eapply evt_cut.
  { eapply BUILD with (o := o) (md := mdv) (b := bb) (d := d) (s := 0x21140) (ns := 0)
      (mb := mb) (nb := nb) (db := db) (sb := sb) (junk := junk) (FS := FS).
    all: rewrite ?MState.unsigned_lit by lia.
    all: try assumption.
    all: try reflexivity.
    all: try lia. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  Eq & MU & WM & MI & STp & ACp & SWp & AWp & FPp & _ & HOut).
  subst ms'.
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply MState.unsigned_lit; lia).
  assert (Etp : bv_unsigned (Z_to_bv 64 TPv) = TPv) by (apply MState.unsigned_lit; lia).
  rewrite ?Esp in MU. rewrite ?Esp in STp. rewrite ?Esp in AWp.
  rewrite ?Esp, ?Etp in FPp.
  replace (ret_pc (Z_to_bv 64 0x815ec)) with (Z_to_bv 64 0x815ec)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  apply evt_done.
  do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STp|].
  split; [exact ACp|]. split; [exact SWp|]. split; [exact AWp|]. split; [exact FPp|].
  split.
  { intros x Hx. revert Hx.
    destruct (PB.ba_go o mdv bb && PB.ba_E (bm_uw mdv (firstn 8 (skipn 16 mb))) mb bb) eqn:HE;
      intros Hx; [|lia].
    destruct (HOut eq_refl) as (Hb & Hw & _).
    assert (Hmdne : mdv <> 0).
    { apply andb_true_iff in HE as [Hgo _]. unfold PB.ba_go in Hgo.
      apply andb_true_iff in Hgo as [Hg1 _]. apply andb_true_iff in Hg1 as [_ Hg2].
      apply negb_true_iff, Z.eqb_neq in Hg2. exact Hg2. }
    destruct (HM Hmdne) as (_ & _ & Hmbl & _ & _).
    destruct (em_wok_range _ Hw) as (Hnr & _).
    eapply (r6_present m' o _ x).
    + exact Hb.
    + apply r6_emfr_len; [exact Hdbl | exact Hsbl | exact (r6_baX_len mdv mb nb bb Hmbl) | lia].
    + lia. }
  (* the emitted frame: the count word c16 is [A + 96] = 0x1234, loaded into a5 at 0x815dc *)
  intros HE. destruct (HOut HE) as (Hb & _).
  match type of Hb with bytes_at _ _ _ (em_fr _ _ ?c _ _ _ _) =>
    replace c with 0x1234 in Hb by (vm_compute; reflexivity) end.
  exact Hb.
Qed.

(* The bytes Image.image_bytes returns are the ROM bytes of the segments (Lib's seg_rom / wa, as in Image.v). *)
Lemma r6_imgb_nth : forall n A bs i, Image.image_bytes rsegs A n = Some bs -> (i < n)%nat ->
  seg_rom rsegs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros A bs i H Hi; [lia|].
  cbn [Image.image_bytes] in H.
  destruct (seg_rom rsegs (wa A)) as [b|] eqn:E1, (Image.image_bytes rsegs (A + 1) n) as [bs'|] eqn:E2;
    rewrite ?E1 in H; cbn [Image.image_bytes] in H; try discriminate H.
  injection H as <-. destruct i as [|i].
  - cbn [nth_error]. rewrite Z.add_0_r. exact E1.
  - cbn [nth_error]. replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia.
    apply (IH (A + 1) bs' i E2). lia.
Qed.

(* ===== the cuts ===== *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_fs Tac_b5 RcPro.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcFrag RcReply RcIdentModel.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.

Module ACw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AFw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LImg := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Image.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.
Open Scope Z_scope.

(* ---- the round-trip model's lengths (local copies of Tac_rt2_b2's a_row_len / a_rtn, which this branch lacks) ---- *)

Lemma r6_row_len : forall i, length (rowb i) = 296%nat.
Proof.
  intros i. unfold rowb, img. destruct (LImg.image_bytes rsegs (CAT + CAT_ROW * i) 296) eqn:E.
  - exact (LImg.image_bytes_length rsegs 296 _ _ E).
  - apply repeat_length.
Qed.

(* n_b <> 0: the turn's frame length is in [124, 1492]. *)
Lemma r6_rtn : forall inp b, rt_n inp b <> 0 -> 124 <= rt_n inp b <= 1492.
Proof.
  intros inp b H. unfold rt_n in *. destruct (rt_E inp b) eqn:E; [|congruence]. cbv beta iota.
  unfold rt_E, PB.ba_E in E. apply andb_true_iff in E as [Ew _].
  destruct (em_wok_range _ Ew) as [R _]. lia.
Qed.

(* n_b <> 0 exactly when E(b): then build_as emits the frame rt_F. (E(b) is false for the rows without an
   identity record at b = 5, 6 -- istar in {0, 2, 3} -- where n_b = 0 and out[] is not written.) *)
Lemma r6_E_nz : forall inp b, rt_n inp b <> 0 -> rt_E inp b = true.
Proof. intros inp b H. unfold rt_n in H. destruct (rt_E inp b); [reflexivity | congruence]. Qed.

(* ---- image facts: the catalogue rows, the frame table, the round-trip box, the row names ---- *)

(* The 11 catalogue rows of image A are image bytes (B3Rtm.a_row_img). *)
Lemma r6_row_img : forall i, 0 <= i < 11 -> LImg.image_bytes rsegs (CAT + CAT_ROW * i) 296 = Some (rowb i).
Proof.
  intros i Hi.
  assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]];
    unfold rowb, img; (destruct (LImg.image_bytes _ _ _) eqn:E; [reflexivity | vm_compute in E; discriminate E]).
Qed.

(* CTRL_FRAMES rows 3 .. 9, the 168 bytes the callee reads. *)
Lemma r6_ba_img : LImg.image_bytes rsegs (BA.BA_FR + 72) 168 = Some PB.ba_tbl.
Proof. vm_compute. reflexivity. Qed.

(* round_trip.box: 6 read-only image bytes at 0x21140. *)
Definition r6_sb : list byte := img 0x21140 6.
Lemma r6_sb_ro : LImg.ro_bytes_b rsegs 0x21140 r6_sb = true.
Proof. vm_compute. reflexivity. Qed.
Lemma r6_sb_len : length r6_sb = 6%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma r6_box6 : r6_sb = box6.
Proof. vm_compute. reflexivity. Qed.

(* An address inside one of the registered globals of frame_AG (boolean form; B3Rtm.a_inAG). *)
Definition r6_inAG (a : Z) : bool :=
  existsb (fun p => (fst p <=? a) && (a <? fst p + snd p)) AFw.frame_AG.

Lemma r6_inAG_sound : forall a, r6_inAG a = true -> in_globals AFw.frame_AG a.
Proof.
  intros a H. unfold r6_inAG in H. apply existsb_exists in H. destruct H as ([lo len] & Hin & Hb).
  cbn [fst snd] in Hb. apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists lo, len. split; [exact Hin | lia].
Qed.

Definition r6_AGb (lo len : Z) : bool :=
  existsb (fun p => (fst p =? lo) && (snd p =? len)) AFw.frame_AG.

Lemma r6_AGb_in : forall lo len a, r6_AGb lo len = true -> lo <= a < lo + len -> in_globals AFw.frame_AG a.
Proof.
  intros lo len a H Ha. unfold r6_AGb in H. apply existsb_exists in H. destruct H as ([x y] & Hin & Hb).
  cbn [fst snd] in Hb. apply andb_true_iff in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
  subst x y. exists lo, len. split; [exact Hin | exact Ha].
Qed.

(* Per row: when the model has an identity record and a name pointer, the name is a read-only, registered,
   low-image C string of 1 .. 16 bytes with no inner zero (RcBox.name_ok). *)
Definition r6_namechk (i : Z) : bool :=
  let nm := rname (rowb i) in let nb := img_cstr nm 16 in
  (has (rowb i) =? 0) || (nm =? 0) ||
  ((0 <? nm) && (nm + Z.of_nat (length nb) <=? 6283264) &&
   LImg.ro_bytes_b rsegs nm nb &&
   (1 <=? Z.of_nat (length nb)) && (Z.of_nat (length nb) <=? 16) &&
   forallb (fun k => negb (bv_unsigned (nth k nb (Z_to_bv 8 0)) =? 0)) (seq 0 (pred (length nb))) &&
   ((Nat.eqb (length nb) 16) || (bv_unsigned (nth (pred (length nb)) nb (Z_to_bv 8 0)) =? 0)) &&
   forallb (fun k => r6_inAG (nm + Z.of_nat k)) (seq 0 (length nb))).

Lemma r6_namechk_all : forallb r6_namechk (map Z.of_nat (seq 0 11)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r6_namechk_i : forall i, 0 <= i < 11 -> r6_namechk i = true.
Proof.
  intros i Hi. pose proof r6_namechk_all as H. rewrite forallb_forall in H. apply H.
  apply in_map_iff. exists (Z.to_nat i). split; [lia | apply in_seq; lia].
Qed.

Lemma r6_name_facts : forall i, 0 <= i < 11 -> has (rowb i) <> 0 -> rname (rowb i) <> 0 ->
  name_ok (img_cstr (rname (rowb i)) 16) /\
  0 < rname (rowb i) /\
  rname (rowb i) + Z.of_nat (length (img_cstr (rname (rowb i)) 16)) <= 6283264 /\
  LImg.ro_bytes_b rsegs (rname (rowb i)) (img_cstr (rname (rowb i)) 16) = true /\
  (forall k, (k < length (img_cstr (rname (rowb i)) 16))%nat ->
     in_globals AFw.frame_AG (rname (rowb i) + Z.of_nat k)).
Proof.
  intros i Hi Hh Hn. pose proof (r6_namechk_i i Hi) as H. unfold r6_namechk in H. cbv zeta in H.
  apply orb_true_iff in H. destruct H as [H|H].
  { apply orb_true_iff in H. destruct H as [H|H]; apply Z.eqb_eq in H; [contradiction | contradiction]. }
  rewrite !andb_true_iff in H.
  destruct H as [[[[[[[H1a H1b] H1c] H1d] H1e] H5] H6] H7].
  apply Z.ltb_lt in H1a. apply Z.leb_le in H1b. apply Z.leb_le in H1d. apply Z.leb_le in H1e.
  split; [|split; [lia | split; [lia | split; [exact H1c|]]]].
  - split; [lia|]. split.
    + intros k Hk. rewrite forallb_forall in H5.
      pose proof (H5 k ltac:(apply in_seq; lia)) as Hb. apply negb_true_iff, Z.eqb_neq in Hb. exact Hb.
    + apply orb_true_iff in H6. destruct H6 as [H6|H6].
      * left. apply Nat.eqb_eq. exact H6.
      * right. apply Z.eqb_eq. exact H6.
  - intros k Hk. apply r6_inAG_sound. rewrite forallb_forall in H7.
    apply H7. apply in_seq. lia.
Qed.

(* ---- the call runs on the normalized memory (MemNorm.evt_normalize; the contract needs mem_inv, which no cut
   carries): every premise and every post fact crosses mem_rel.  A1's helpers (a working branch), as iffs. ---- *)

Definition r6_tops (sg : list Segment) (top : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? top) sg.

Lemma r6_rsegs_below : r6_tops rsegs 0x5fe000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r6_fseg_below : forall sg top x n s,
  r6_tops sg top = true -> find_segment sg x n = Some s -> 0 <= n -> x < top \/ n = 0.
Proof.
  induction sg as [|s0 r IH]; intros top x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold r6_tops in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr]. apply Z.leb_le in H0.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [_ E]. apply Z.leb_le in E. lia.
  - exact (IH top x n s Hr H Hn).
Qed.

(* Above the image there is no read-only byte, so normalizing changes nothing there (A1.ro_addr_hi). *)
Lemma r6_ro_hi : forall a, 0x5fe000 <= a < 2 ^ 64 -> ro_addr rsegs (wa a) = false.
Proof.
  intros a Ha. unfold OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.ro_addr.
  match goal with |- context [find_segment ?sg ?x ?n] =>
    destruct (find_segment sg x n) as [s|] eqn:E; [|reflexivity];
    destruct (r6_fseg_below sg 0x5fe000 x n s r6_rsegs_below E ltac:(cbn; lia)) as [L|L];
    [exfalso; rewrite MState.unsigned_lit in L by lia; lia | cbn in L; lia] end.
Qed.

Lemma r6_wv_hi : forall m m0 a, mem_rel rsegs m m0 -> 0x5fe000 <= a < 2 ^ 64 ->
  (wview rsegs m0 (wa a) <> None <-> wview rsegs m (wa a) <> None).
Proof.
  intros m m0 a HR Ha. rewrite (wview_rel_rw rsegs m m0 (wa a) HR (r6_ro_hi a Ha)). split; auto.
Qed.

Lemma r6_stk_iff : forall m m0 lo hi, mem_rel rsegs m m0 -> 0x5fe000 <= lo -> hi <= 2 ^ 64 ->
  (stk rsegs m lo hi <-> stk rsegs m0 lo hi).
Proof.
  intros m m0 lo hi HR Hlo Hhi. split; intros (H0 & H1 & H); (split; [lia|]); (split; [lia|]); intros a Ha;
    destruct (H a Ha) as (Hw & b & Hb); split.
  - apply (proj2 (r6_wv_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
  - apply (proj1 (r6_wv_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r6_shadow_iff : forall m m0, mem_rel rsegs m m0 -> (shadow_rw m <-> shadow_rw m0).
Proof.
  intros m m0 HR. split; intros H a Ha; pose proof (in_shadow_range a Ha) as Hr;
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha;
    destruct (H a Ha) as (Hw & b & Hb); split.
  - apply (proj2 (r6_wv_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite <- (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
  - apply (proj1 (r6_wv_hi m m0 a HR ltac:(lia))). exact Hw.
  - exists b. rewrite (mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma r6_addr_iff : forall m m0 p n, mem_rel rsegs m m0 -> (addressable m p n <-> addressable m0 p n).
Proof.
  intros m m0 p n HR. split; intros (H0 & H1 & H2 & H); (split; [exact H0|]); (split; [exact H1|]);
    (split; [exact H2|]); intros i Hi; destruct (H i Hi) as (Hap & b & Hb & Hok); split; try exact Hap;
    exists b.
  - rewrite <- (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
  - rewrite (mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma r6_fsplace_iff : forall m m0 FS, mem_rel rsegs m m0 -> 0x5fe000 <= FS -> FS + FS_SIZE <= 2 ^ 64 ->
  (fs_place m FS <-> fs_place m0 FS).
Proof.
  intros m m0 FS HR Hlo Hhi. split; intros (P1 & P2 & P3 & P4 & P5);
    (split; [exact P1|]); (split; [exact P2|]); (split; [exact P3|]); (split; [exact P4|]).
  - exact (proj1 (r6_stk_iff m m0 FS (FS + FS_SIZE) HR Hlo Hhi) P5).
  - exact (proj2 (r6_stk_iff m m0 FS (FS + FS_SIZE) HR Hlo Hhi) P5).
Qed.

Lemma r6_ac_iff : forall m m0, mem_rel rsegs m m0 -> (asan_cells m <-> asan_cells m0).
Proof.
  intros m m0 R. unfold asan_cells. split; intros H;
    repeat match goal with H' : _ /\ _ |- _ => destruct H' end;
    repeat match goal with |- _ /\ _ => split end;
    match goal with |- bytes_at _ _ ?a ?bs =>
      first [ exact (proj1 (bytes_at_rel rsegs m m0 a bs R) ltac:(assumption))
            | exact (proj2 (bytes_at_rel rsegs m m0 a bs R) ltac:(assumption)) ] end.
Qed.

Lemma r6_tls_iff : forall m m0 TP DT TS C T DB k, mem_rel rsegs m m0 ->
  (asan_tls_cells m TP DT TS C T DB k <-> asan_tls_cells m0 TP DT TS C T DB k).
Proof.
  intros m m0 TP DT TS C T DB k R.
  assert (BF : forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs)
    by (intros a bs H; exact (proj1 (bytes_at_rel rsegs m m0 a bs R) H)).
  assert (BB : forall a bs, bytes_at rsegs m0 a bs -> bytes_at rsegs m a bs)
    by (intros a bs H; exact (proj2 (bytes_at_rel rsegs m m0 a bs R) H)).
  unfold asan_tls_cells.
  split; intros (H1 & H2 & H3 & H4 & H5 & Hk & H7 & H8 & H9 & H10 & (tb & te & H11) & H12 & H13 & H14 & H15
                 & H16 & H17 & HDB & H19);
    repeat (split;
      [ solve [ first [ assumption
                      | apply BF; assumption
                      | apply BB; assumption
                      | exists tb, te; first [apply BF; assumption | apply BB; assumption] ] ] | ]);
    solve [ first [ assumption
                  | apply BF; assumption
                  | apply BB; assumption
                  | exists tb, te; first [apply BF; assumption | apply BB; assumption] ] ].
Qed.

Lemma r6_cls_iff : forall m m0 FS c, mem_rel rsegs m m0 -> (fp_cls m FS c <-> fp_cls m0 FS c).
Proof.
  intros m m0 FS c R.
  assert (BF : forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m0 a bs)
    by (intros a bs H; exact (proj1 (bytes_at_rel rsegs m m0 a bs R) H)).
  assert (BB : forall a bs, bytes_at rsegs m0 a bs -> bytes_at rsegs m a bs)
    by (intros a bs H; exact (proj2 (bytes_at_rel rsegs m m0 a bs R) H)).
  unfold fp_cls.
  split; intros (Hc & h & flags & H1 & H2 & H3 & H4);
    (split; [exact Hc|]); exists h, flags;
    (split; [first [apply BF; assumption | apply BB; assumption]|]);
    (split; [first [apply BF; assumption | apply BB; assumption]|]);
    (split; [exact H3 | exact H4]).
Qed.

Lemma r6_fp_iff : forall cs m m0 TP FS lo hi W D, mem_rel rsegs m m0 -> 0x5fe000 <= FS -> FS + FS_SIZE <= 2 ^ 64 ->
  (fp cs m TP FS lo hi W D <-> fp cs m0 TP FS lo hi W D).
Proof.
  intros cs m m0 TP FS lo hi W D R Hlo Hhi. unfold fp. split;
    intros (DT & TS & C & T & DB & k & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10);
    exists DT, TS, C, T, DB, k.
  - split; [exact (proj1 (r6_tls_iff m m0 _ _ _ _ _ _ _ R) H1)|].
    split; [exact (proj1 (bytes_at_rel rsegs m m0 _ _ R) H2)|].
    split; [exact (proj1 (r6_fsplace_iff m m0 FS R Hlo Hhi) H3)|].
    split; [exact (proj1 (bytes_at_rel rsegs m m0 _ _ R) H4)|].
    split; [exact (proj1 (bytes_at_rel rsegs m m0 _ _ R) H5)|].
    split; [eapply Forall_impl; [|exact H6]; intros c Hc; exact (proj1 (r6_cls_iff m m0 FS c R) Hc)|].
    split; [exact H7|]. split; [exact H8|]. split; [exact H9 | exact H10].
  - split; [exact (proj2 (r6_tls_iff m m0 _ _ _ _ _ _ _ R) H1)|].
    split; [exact (proj2 (bytes_at_rel rsegs m m0 _ _ R) H2)|].
    split; [exact (proj2 (r6_fsplace_iff m m0 FS R Hlo Hhi) H3)|].
    split; [exact (proj2 (bytes_at_rel rsegs m m0 _ _ R) H4)|].
    split; [exact (proj2 (bytes_at_rel rsegs m m0 _ _ R) H5)|].
    split; [eapply Forall_impl; [|exact H6]; intros c Hc; exact (proj2 (r6_cls_iff m m0 FS c R) Hc)|].
    split; [exact H7|]. split; [exact H8|]. split; [exact H9 | exact H10].
Qed.

(* The build_as tls premise crosses mem_rel (its hypothesis is an asan_tls_cells of the other memory). *)
Lemma r6_btls_iff : forall m m0 TP FS lo hi, mem_rel rsegs m m0 ->
  (BA.reac_ctrl_build_as_tls m TP FS lo hi <-> BA.reac_ctrl_build_as_tls m0 TP FS lo hi).
Proof.
  intros m m0 TP FS lo hi R. unfold BA.reac_ctrl_build_as_tls. split; intros H DT TS C T DB k HT.
  - apply (H DT TS C T DB k). exact (proj2 (r6_tls_iff m m0 TP DT TS C T DB k R) HT).
  - apply (H DT TS C T DB k). exact (proj1 (r6_tls_iff m m0 TP DT TS C T DB k R) HT).
Qed.
(* ---- R3's transport helpers (lib/A/Prog/Seg/R3.v, renamed) ---- *)

Lemma r6_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split; [exact (WM _ Hw)|].
  destruct (Hc a Ha) as [Ho|Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

Lemma r6_wr_stk : forall m lo hi, stk rsegs m lo hi -> wr_at rsegs m lo (hi - lo).
Proof.
  intros m lo hi (H0 & H1 & H). split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (lo + i) ltac:(lia))).
Qed.

Lemma r6_rw_CB : forall m A l, bytes_at rsegs m A l -> wr_at rsegs m A (Z.of_nat (length l)) ->
  rw_cells rsegs m A [CB (length l) l].
Proof.
  intros m A l Hb Hw. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma r6_out_dec : forall W x, outside W x \/ ~ outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; [|right; tauto].
  destruct (Z_lt_le_dec x lo) as [H1|H1]; [left; split; [lia | exact H]|].
  destruct (Z_lt_le_dec x hi) as [H2|H2]; [right; intros (H3 & _); lia | left; split; [lia | exact H]].
Qed.

Lemma r6_addr_keep : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H1 & H2 & H3 & H) MU HO. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  pose proof (in_shadow_range _ (shadow_of_app _ Ha)) as Hr.
  unfold mrd in *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite wa_unsigned by lia. apply HO. exact Hi.
Qed.

(* The instrumented globals of the image lie in [0x21140, 0x9f8e8). *)
Lemma r6_ag_range : forall a, in_globals AFw.frame_AG a -> 0x21140 <= a < 0x9f8e8.
Proof.
  intros a (lo & len & Hin & Hr). unfold AFw.frame_AG in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

(* ---- side-stack geometry: the class-0 and class-1 ranges of fp_w in numbers (F6's f6_fs* lemmas) ---- *)
Lemma r6_fsh0 : forall FS, fs_hint FS 0 = FS.
Proof. intros FS. unfold fs_hint. cbn. lia. Qed.
Lemma r6_fsh1 : forall FS, fs_hint FS 1 = FS + 8.
Proof. intros FS. unfold fs_hint. cbn. lia. Qed.
Lemma r6_fsf0 : forall FS, fs_flag FS 0 0 = FS + 4096.
Proof. intros FS. unfold fs_flag. cbn. lia. Qed.
Lemma r6_fsf1 : forall FS, fs_flag FS 1 0 = FS + 20480.
Proof. intros FS. unfold fs_flag. cbn. lia. Qed.
Lemma r6_fsM0 : fs_M 0 = 16384.
Proof. reflexivity. Qed.
Lemma r6_fsM1 : fs_M 1 = 8192.
Proof. reflexivity. Qed.
Lemma r6_fsfr00 : forall FS, fs_frame FS 0 0 = FS + 36864.
Proof. intros FS. unfold fs_frame, fs_B. cbn. lia. Qed.
Lemma r6_fsfr0M : forall FS, fs_frame FS 0 (fs_M 0) = FS + 1085440.
Proof. intros FS. unfold fs_frame, fs_B, fs_M. cbn. lia. Qed.
Lemma r6_fsfr10 : forall FS, fs_frame FS 1 0 = FS + 1085440.
Proof. intros FS. unfold fs_frame, fs_B. cbn. lia. Qed.
Lemma r6_fsfr1M : forall FS, fs_frame FS 1 (fs_M 1) = FS + 2134016.
Proof. intros FS. unfold fs_frame, fs_B, fs_M. cbn. lia. Qed.

(* A contiguous app range lies wholly in the low or wholly in the high app memory (F6.f6_app_split). *)
Lemma r6_app_split : forall lo hi, lo < hi -> (forall a, lo <= a < hi -> app_mem a) ->
  hi <= LOWMEM_END \/ HIGHMEM_BEG <= lo.
Proof.
  intros lo hi Hlt H. destruct (Z_le_gt_dec hi LOWMEM_END) as [L|L]; [left; exact L|right].
  destruct (Z_le_gt_dec HIGHMEM_BEG lo) as [L2|L2]; [exact L2|exfalso].
  destruct (Z_le_gt_dec lo LOWMEM_END) as [L3|L3].
  - pose proof (H LOWMEM_END ltac:(lia)) as Ha. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
  - pose proof (H lo ltac:(lia)) as Ha. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

(* The shadow bytes of a contiguous app range are in the shadow (F6.f6_shadow_ivl). *)
Lemma r6_shadow_ivl : forall lo hi x, (forall a, lo <= a < hi -> app_mem a) -> lo < hi ->
  lo / 8 + ASAN_K <= x < hi / 8 + ASAN_K -> in_shadow x.
Proof.
  intros lo hi x Happ Hlt Hx.
  assert (Hlo : 0 <= lo)
    by (pose proof (Happ lo ltac:(lia)) as H; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H; lia).
  assert (Hhi : hi <= APPMEM_END)
    by (pose proof (Happ (hi - 1) ltac:(lia)) as H;
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H |- *; lia).
  unfold in_shadow. destruct (r6_app_split lo hi Hlt Happ) as [HL|HH].
  - left. unfold ASAN_K, LOWMEM_END, LOWSHADOW_END in *. Z.div_mod_to_equations. lia.
  - right. unfold ASAN_K, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *. Z.div_mod_to_equations. lia.
Qed.

Lemma r6_mbyte_mrd : forall m a, mbyte rsegs m a = mrd rsegs m (wa a).
Proof. intros m a. reflexivity. Qed.

(* The write set of the segment: the callee window, the out[] frame, the class-0 and class-1 side-stack bytes,
   and the shadow of the window (the contract's munch list). *)
Definition r6_WW (fr spv nb FS : Z) : list ivl :=
  [(spv - BA.REAC_CTRL_BUILD_AS_K, spv); (fr + 544, fr + 544 + nb)] ++ fp_w [0%nat; 1%nat] FS ++
  [(shadow_addr (spv - BA.REAC_CTRL_BUILD_AS_K), shadow_addr spv)].

Lemma r6_out_fpw : forall FS x,
  ~ (FS <= x < FS + 16) -> ~ (FS + 4096 <= x < FS + 28672) -> ~ (FS + 36864 <= x < FS + 2134016) ->
  ~ (shadow_addr (FS + 36864) <= x < shadow_addr (FS + 2134016)) ->
  outside (fp_w [0%nat; 1%nat] FS) x.
Proof.
  intros FS x H1 H2 H3 H4. unfold fp_w, fp_w1. cbn [flat_map app].
  rewrite r6_fsh0, r6_fsh1, r6_fsf0, r6_fsf1, r6_fsfr00, r6_fsfr0M, r6_fsfr10, r6_fsfr1M, r6_fsM0, r6_fsM1.
  assert (Hm1 : shadow_addr (FS + 36864) <= shadow_addr (FS + 1085440))
    by (unfold shadow_addr; Z.div_mod_to_equations; lia).
  assert (Hm2 : shadow_addr (FS + 1085440) <= shadow_addr (FS + 2134016))
    by (unfold shadow_addr; Z.div_mod_to_equations; lia).
  cbn [outside]. repeat split; try exact I; intros HC; lia.
Qed.

Lemma r6_out_WW : forall fr spv nb FS x,
  ~ (spv - BA.REAC_CTRL_BUILD_AS_K <= x < spv) -> ~ (fr + 544 <= x < fr + 544 + nb) ->
  outside (fp_w [0%nat; 1%nat] FS) x ->
  ~ (shadow_addr (spv - BA.REAC_CTRL_BUILD_AS_K) <= x < shadow_addr spv) ->
  outside (r6_WW fr spv nb FS) x.
Proof.
  intros fr spv nb FS x H1 H2 H3 H4. unfold r6_WW.
  apply fl_out_app; [cbn [outside]; tauto|]. apply fl_out_app; [exact H3|]. cbn [outside]. tauto.
Qed.

(* The hint word and the flag bytes of a class other than 0 and 1 miss the class-0 / class-1 ranges
   (F6.f6_hint_other / f6_flag_other). *)
Lemma r6_hint_other : forall FS c, (c <= 10)%nat -> (2 <= c)%nat ->
  FS + 16 <= ACw.a_fs_hint FS c < FS + 88.
Proof.
  intros FS c Hc H2. unfold ACw.a_fs_hint.
  assert (Hz : 2 <= Z.of_nat c <= 10) by lia. lia.
Qed.

Lemma r6_flag_other : forall FS c j, (c <= 10)%nat -> (2 <= c)%nat -> 0 <= j < ACw.a_fs_M c ->
  FS + 28672 <= ACw.a_fs_flag FS c j < FS + 36864.
Proof.
  intros FS c j Hc H2 Hj. unfold ACw.a_fs_flag. unfold ACw.a_fs_M in Hj.
  destruct c as [|[|[|[|[|[|[|[|[|[|[|c]]]]]]]]]]];
    try (exfalso; revert Hc H2; clear; lia);
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hj |- *;
    first [ lia | (vm_compute (2 ^ 15) in *; vm_compute in Hj; lia) ].
Qed.

(* The side-stack state after the call: the class-0 and class-1 hint words, flag bytes and frames come from the
   callee's fp at the return; the other classes' cells are unchanged (F6.f6_fs_ok_post for [0;1]). *)
Lemma r6_fsok : forall (m m' : word -> option byte) (fr spv nb FS TP lo hi : Z) (W D : list ivl),
  ACw.a_fs_ok m FS ->
  munch (r6_WW fr spv nb FS) m m' ->
  fp [0%nat; 1%nat] m' TP FS lo hi W D ->
  (forall x, FS <= x < FS + 36864 ->
     ~ (FS <= x < FS + 16) -> ~ (FS + 4096 <= x < FS + 28672) -> outside (r6_WW fr spv nb FS) x) ->
  0 <= FS -> FS + ACw.FS_SIZE <= 2 ^ 64 ->
  ACw.a_fs_ok m' FS.
Proof.
  intros m m' fr spv nb FS TP lo hi W D (HOK1 & HOK2 & HOK3 & HOK4 & HOK5) MU
    (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFSlo & HAwin & _ & _) HOUT HFS0 HFSb.
  assert (HSZ : ACw.FS_SIZE = FS_SIZE) by reflexivity.
  destruct HP as (HFSp0 & HFSmod & HFSgt & HFSapp & HSTK).
  pose proof (Forall_inv HCL) as (_ & h0 & flags0 & Hh0 & Hfl0 & Hfll0 & Hflb0).
  pose proof (Forall_inv (Forall_inv_tail HCL)) as (_ & h1 & flags1 & Hh1 & Hfl1 & Hfll1 & Hflb1).
  split; [|split; [|split; [|split]]].
  - intros a Ha. destruct HSTK as (_ & _ & HS).
    destruct (HS a ltac:(rewrite HSZ in Ha; unfold FS_SIZE in *; lia)) as [Hw (bb & Hb)].
    split; [exact Hw | exists bb; rewrite r6_mbyte_mrd; exact Hb].
  - pose proof (bytes_at_le8_word rsegs m' (FS + 88) (Z_to_bv 64 20) H88) as HW.
    rewrite MState.unsigned_lit in HW by lia. exact HW.
  - destruct H96 as (_ & _ & H96'). pose proof (H96' 0%nat ltac:(cbn; lia)) as HH.
    cbn [nth_error] in HH. rewrite Z.add_0_r in HH. rewrite r6_mbyte_mrd. exact HH.
  - intros c Hc.
    destruct (Nat.eq_dec c 0) as [->|Hn0].
    { exists (bv_unsigned h0). exact (bytes_at_le8_word rsegs m' (fs_hint FS 0) h0 Hh0). }
    destruct (Nat.eq_dec c 1) as [->|Hn1].
    { exists (bv_unsigned h1). exact (bytes_at_le8_word rsegs m' (fs_hint FS 1) h1 Hh1). }
    destruct (HOK4 c Hc) as (h & Hh). exists h.
    apply (word_mem_frame rsegs m m' _ _ Hh). intros kk Hk.
    pose proof (r6_hint_other FS c Hc ltac:(lia)) as Hr.
    unfold mbyte. rewrite MU; [reflexivity|].
    rewrite MState.unsigned_lit by (rewrite HSZ in HFSb; unfold FS_SIZE in *; lia).
    apply HOUT; lia.
  - intros c j Hc Hj.
    destruct (Nat.eq_dec c 0) as [->|Hn0].
    { destruct Hfl0 as (_ & _ & Hfl0').
      assert (HjN : (Z.to_nat j < length flags0)%nat).
      { rewrite r6_fsM0 in Hfll0. assert (HM : ACw.a_fs_M 0 = 16384) by reflexivity. lia. }
      pose proof (Hfl0' (Z.to_nat j) HjN) as HH.
      destruct (nth_error flags0 (Z.to_nat j)) as [bb|] eqn:E; [|exfalso; apply nth_error_None in E; lia].
      assert (Eaddr : fs_flag FS 0 0 + Z.of_nat (Z.to_nat j) = ACw.a_fs_flag FS 0 j)
        by (unfold fs_flag, ACw.a_fs_flag; cbn; lia).
      rewrite Eaddr in HH. rewrite r6_mbyte_mrd.
      pose proof (proj1 (Forall_forall _ flags0) Hflb0 bb (nth_error_In _ _ E)) as Hb01.
      destruct Hb01 as [->| ->]; [left | right]; exact HH. }
    destruct (Nat.eq_dec c 1) as [->|Hn1].
    { destruct Hfl1 as (_ & _ & Hfl1').
      assert (HjN : (Z.to_nat j < length flags1)%nat).
      { rewrite r6_fsM1 in Hfll1. assert (HM : ACw.a_fs_M 1 = 8192) by reflexivity. lia. }
      pose proof (Hfl1' (Z.to_nat j) HjN) as HH.
      destruct (nth_error flags1 (Z.to_nat j)) as [bb|] eqn:E; [|exfalso; apply nth_error_None in E; lia].
      assert (Eaddr : fs_flag FS 1 0 + Z.of_nat (Z.to_nat j) = ACw.a_fs_flag FS 1 j)
        by (unfold fs_flag, ACw.a_fs_flag; cbn; lia).
      rewrite Eaddr in HH. rewrite r6_mbyte_mrd.
      pose proof (proj1 (Forall_forall _ flags1) Hflb1 bb (nth_error_In _ _ E)) as Hb01.
      destruct Hb01 as [->| ->]; [left | right]; exact HH. }
    pose proof (r6_flag_other FS c j Hc ltac:(lia) Hj) as Hr.
    destruct (HOK5 c j Hc Hj) as [HH|HH]; [left|right];
      (unfold mbyte in *; rewrite MU; [exact HH|];
       rewrite MState.unsigned_lit by (rewrite HSZ in HFSb; unfold FS_SIZE in *; lia);
       apply HOUT; lia).
Qed.

(* The spill base is the A of register 9 (the two agree mod 2^64 and both lie in the frame's window). *)
Lemma r6_spill_at : forall (regs : bvmap 5 word) (mem : word -> option byte) (A off v : Z),
  rg regs 9 A -> 0 <= A -> A + 416 < 2 ^ 64 -> 0 <= off <= 416 -> spill regs mem off v ->
  q64 mem (A + off) v.
Proof.
  intros regs mem A off v Hr HA0 HA1 Hoff (A' & Hr' & Hq).
  pose proof Hq as Hb. unfold q64 in Hb. apply bytes_at_bound in Hb. rewrite length_le8 in Hb.
  pose proof (rg_eq64 regs 9 A' A Hr' Hr) as Hm.
  change (2 ^ 64) with 18446744073709551616 in *.
  assert (A' = A) by (Z.div_mod_to_equations; lia).
  subst A'. exact Hq.
Qed.


(* Addressability of a range inside one registered global, and of a byte-listed range. *)
Lemma r6_addr_glob : forall (m : word -> option byte) (lo len a n : Z),
  (forall x, in_globals AFw.frame_AG x -> addressable m x 1) ->
  r6_AGb lo len = true -> lo <= a -> a + n <= lo + len -> 0 <= n -> 0 <= a -> a + n <= APPMEM_END ->
  addressable m a n.
Proof.
  intros m lo len a n HAG Hb H1 H2 Hn Ha Hae.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (HAG (a + i) (r6_AGb_in lo len (a + i) Hb ltac:(lia))) as (_ & _ & _ & H).
  pose proof (H 0 ltac:(lia)) as Hbb. rewrite Z.add_0_r in Hbb. exact Hbb.
Qed.

Lemma r6_addr_bytes : forall (m : word -> option byte) (a : Z) (k : nat),
  (forall x, in_globals AFw.frame_AG x -> addressable m x 1) ->
  (forall i, (i < k)%nat -> in_globals AFw.frame_AG (a + Z.of_nat i)) ->
  0 <= a -> a + Z.of_nat k <= APPMEM_END -> addressable m a (Z.of_nat k).
Proof.
  intros m a k HAG Hin Ha Hae.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi.
  destruct (HAG (a + i) (ltac:(replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia; apply Hin; lia)))
    as (_ & _ & _ & H).
  pose proof (H 0 ltac:(lia)) as Hbb. rewrite Z.add_0_r in Hbb. exact Hbb.
Qed.

Lemma r6_addr_sub : forall m p n k, addressable m p n -> 0 <= k <= n -> addressable m p k.
Proof.
  intros m p n k (H0 & H1 & H2 & H) Hk.
  split; [lia|]. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
Qed.

(* A low-image range is apart from the class-0 / class-1 side-stack ranges (all of which start at or above GT). *)
Lemma r6_dj_low : forall x y FS, y <= ACw.GT -> ACw.GT <= FS -> fp_dj [(x, y)] (fp_w [0%nat; 1%nat] FS).
Proof.
  intros x y FS Hy HFS. unfold fp_dj. constructor; [|constructor]. apply Forall_forall.
  intros [lo hi] Hin. cbn [fst snd]. unfold ly_dj. left.
  unfold fp_w, fp_w1 in Hin. cbn [flat_map app] in Hin.
  rewrite r6_fsh0, r6_fsh1, r6_fsf0, r6_fsf1, r6_fsfr00, r6_fsfr0M, r6_fsfr10, r6_fsfr1M, r6_fsM0, r6_fsM1 in Hin.
  assert (Hs1 : ACw.GT <= shadow_addr (FS + 36864))
    by (unfold shadow_addr, ASAN_K, ACw.GT in *; Z.div_mod_to_equations; lia).
  assert (Hs2 : ACw.GT <= shadow_addr (FS + 1085440))
    by (unfold shadow_addr, ASAN_K, ACw.GT in *; Z.div_mod_to_equations; lia).
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; unfold ACw.GT in *; lia|]). destruct Hin.
Qed.

(* A byte not outside a write list lies in one of its ranges. *)
Lemma r6_not_out_in : forall W x, ~ outside W x -> exists a b, In (a, b) W /\ a <= x < b.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; [exfalso; apply H; exact I|].
  cbn [outside] in H.
  destruct (Z_le_gt_dec lo x) as [H1|H1]; [destruct (Z_lt_ge_dec x hi) as [H2|H2]|].
  - exists lo, hi. split; [left; reflexivity | lia].
  - destruct (IH x) as (a & b & Hin & Hb); [intros HO; apply H; split; [lia | exact HO]|].
    exists a, b. split; [right; exact Hin | exact Hb].
  - destruct (IH x) as (a & b & Hin & Hb); [intros HO; apply H; split; [lia | exact HO]|].
    exists a, b. split; [right; exact Hin | exact Hb].
Qed.

Lemma r6_addr_byte : forall m p n a, addressable m p n -> p <= a < p + n -> addressable m a 1.
Proof.
  intros m p n a (H0 & H1 & H2 & H) Ha. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + i) with (p + (a - p + i)) by lia. apply H. lia.
Qed.

(* The tp word names one side stack. *)
Lemma r6_wm_uniq : forall m a u v, word_mem rsegs m a u -> word_mem rsegs m a v ->
  0 <= u < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> u = v.
Proof.
  intros m a u v Hu Hv Hur Hvr.
  assert (Hb : forall k, (k < 8)%nat -> le_byte u 8 k = le_byte v 8 k).
  { intros k Hk. pose proof (Hu k Hk) as Eu. pose proof (Hv k Hk) as Ev.
    rewrite Eu in Ev.
    assert (Eb : Z_to_bv 8 (le_byte u 8 k) = Z_to_bv 8 (le_byte v 8 k)) by congruence.
    apply (f_equal bv_unsigned) in Eb. rewrite !kb_byte_unsigned in Eb. exact Eb. }
  rewrite (kb_le8_digits u Hur), (kb_le8_digits v Hvr).
  rewrite (Hb 0%nat), (Hb 1%nat), (Hb 2%nat), (Hb 3%nat), (Hb 4%nat), (Hb 5%nat), (Hb 6%nat), (Hb 7%nat)
    by lia.
  reflexivity.
Qed.

(* The class-0 / class-1 ranges lie in the side stack's first 2134016 bytes or in the shadow of its frames. *)
Lemma r6_fpw_cover : forall FS p, In p (fp_w [0%nat; 1%nat] FS) ->
  (FS <= fst p /\ snd p <= FS + 2134016) \/
  (exists lo hi, FS + 36864 <= lo /\ hi <= FS + 2134016 /\ fst p = shadow_addr lo /\ snd p = shadow_addr hi).
Proof.
  intros FS p Hin. unfold fp_w, fp_w1 in Hin. cbn [flat_map app] in Hin.
  rewrite r6_fsh0, r6_fsh1, r6_fsf0, r6_fsf1, r6_fsfr00, r6_fsfr0M, r6_fsfr10, r6_fsfr1M, r6_fsM0, r6_fsM1 in Hin.
  repeat (destruct Hin as [<-|Hin];
    [cbn [fst snd];
     first [ left; lia
           | right; eexists; eexists; split; [|split; [|split; [reflexivity | reflexivity]]]; lia ] | ]).
  destruct Hin.
Qed.

Lemma r6_dj_of : forall (W : list ivl) a n, (forall p, In p W -> a + n <= fst p) -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n H; [exact I|].
  split; [left; exact (H (lo, hi) (or_introl eq_refl))|].
  apply IH. intros p Hp. apply H. right. exact Hp.
Qed.

Lemma r6_WW_lo : forall fr spv nb FS p, ACw.GT <= FS -> ACw.GT <= fr -> ACw.GT <= spv - BA.REAC_CTRL_BUILD_AS_K ->
  In p (r6_WW fr spv nb FS) -> ACw.GT <= fst p.
Proof.
  intros fr spv nb FS p HFS Hfr Hsp Hin. unfold r6_WW in Hin.
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct Hin as [<-|[<-|[]]]; cbn [fst]; lia.
  - apply in_app_or in Hin. destruct Hin as [Hin|Hin].
    + destruct (r6_fpw_cover FS p Hin) as [(H1 & H2)|(lo5 & hi5 & H1 & H2 & El & Eh)]; [lia|].
      rewrite El. unfold shadow_addr, ASAN_K, ACw.GT in *. Z.div_mod_to_equations. lia.
    + destruct Hin as [<-|[]]; cbn [fst]. unfold shadow_addr, ASAN_K, ACw.GT in *. Z.div_mod_to_equations. lia.
Qed.

(* The write set misses every runtime cell (all of them lie below GT). *)
Lemma r6_rt_dj : forall fr spv nb FS, ACw.GT <= FS -> ACw.GT <= fr -> ACw.GT <= spv - BA.REAC_CTRL_BUILD_AS_K ->
  rt_disjoint (r6_WW fr spv nb FS).
Proof.
  intros fr spv nb FS H1 H2 H3.
  assert (HL : forall p, In p (r6_WW fr spv nb FS) -> 6283264 <= fst p)
    by (intros p Hp; pose proof (r6_WW_lo fr spv nb FS p H1 H2 H3 Hp) as HG; unfold ACw.GT in HG; exact HG).
  unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
    RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB,
    RT_AGLOB_LEN.
  repeat (split; [solve [apply r6_dj_of; intros p Hp; pose proof (HL p Hp); lia] |]);
  solve [apply r6_dj_of; intros p Hp; pose proof (HL p Hp); lia].
Qed.

(* The identity record has 38 bytes and the fragment state 72 at every turn (R21's a_RID_len; Tac_u1's
   u1_fg_st_len / u1_RS_len). *)
Lemma r6_RID_len : forall inp b, length (RID inp b) = 38%nat.
Proof.
  intros inp b. unfold RID. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st].
  destruct (rt_n inp (Z.of_nat b) =? 0); [exact IH|].
  destruct ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)); cbn [fst snd].
  - unfold rp_id. destruct (ir _ _); [apply RcIdentModel.ING_length; exact IH | exact IH].
  - destruct ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)); cbn [fst snd]; [|exact IH].
    unfold fg_id. destruct (fg_rf _ _ _ =? 1); [apply RcIdentModel.ING_length; exact IH | exact IH].
Qed.

Lemma r6_fg_st_len : forall len st g, length st = 72%nat -> length g = 50%nat -> length (fg_st len st g) = 72%nat.
Proof.
  intros len st g Hs Hg. unfold fg_st, fcls, fg_class.
  change ((1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0) || (1 =? 0)) with false. cbv iota.
  destruct (fg_fr len g) eqn:Efr; cbn [negb]; [|exact Hs].
  assert (Hn : 1 <= fg_n g <= 22).
  { unfold fg_fr in Efr. rewrite !andb_true_iff in Efr. destruct Efr as [[[_ H1] H2] _].
    apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
  assert (Hb : forall bs i, 0 <= bat bs i).
  { intros bs i. unfold bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))). lia. }
  assert (Hbody : length (fg_body g) = Z.to_nat (fg_n g)).
  { unfold fg_body, bsl. rewrite length_firstn, length_skipn, Hg. lia. }
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. unfold fg_first. rewrite !length_app, Hbody, length_skipn, Hs. cbn [length].
    unfold bsl. rewrite length_firstn, length_skipn, Hg. lia.
  - destruct (fg_keep st g) eqn:Ek; cbn [negb]; [|cbn [fg_next]; unfold fg_clear;
      rewrite !length_app, length_firstn, length_skipn, Hs; cbn [length]; lia].
    assert (HT : fg_T st g <= 64).
    { unfold fg_keep in Ek. rewrite !andb_true_iff in Ek. destruct Ek as [_ H]. apply Z.leb_le in H. exact H. }
    assert (Hj : length (fg_join st g) = 72%nat).
    { unfold fg_join. unfold fg_T, fg_lf in HT. pose proof (Hb st 7).
      rewrite !length_app, Hbody, length_firstn, length_skipn, Hs. unfold fg_T, fg_lf. lia. }
    destruct (fg_close st g); cbn [negb fg_next]; unfold fg_clear;
      rewrite !length_app, length_firstn, length_skipn, Hj; cbn [length]; lia.
Qed.

Lemma r6_RFG_len : forall inp b, length (RFG inp b) = 72%nat.
Proof.
  intros inp b. unfold RFG. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st].
  destruct (rt_n inp (Z.of_nat b) =? 0); [exact IH|].
  destruct ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)); cbn [fst snd]; [exact IH|].
  destruct ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)); cbn [fst snd]; [|exact IH].
  apply r6_fg_st_len; [exact IH | apply fr50_length].
Qed.

(* ---- ENT and FRA across the call: the shadow bands and the side-arm FakeStack record ---- *)

(* The shadow byte of an image byte (below GT) or of a byte at or above the entry sp S misses the shadow of the
   class-0 / class-1 frames [FS + 36864, FS + 2134016) (whose shadow starts at ASAN_K + 790016 or above, while an
   image byte's is below ASAN_K + 785408) and the shadow of the callee window [lo, hi) (high app memory below S). *)
Lemma r6_band : forall FS lo hi S b,
  6283264 <= FS -> FS + 2134016 <= S -> 17592186044416 + 2147450880 <= lo -> lo <= hi -> hi <= S ->
  (0 <= b < 6283264 \/ S <= b) ->
  ~ (shadow_addr (FS + 36864) <= shadow_addr b < shadow_addr (FS + 2134016)) /\
  ~ (shadow_addr lo <= shadow_addr b < shadow_addr hi).
Proof.
  intros FS lo hi S b H1 H2 H3 H4 H5 Hb.
  assert (M : forall x y, x <= y -> x / 8 <= y / 8) by (intros x y Hxy; apply Z.div_le_mono; lia).
  unfold shadow_addr. destruct Hb as [Hb|Hb].
  - pose proof (M b 6283263 ltac:(lia)) as E1. pose proof (M 6320128 (FS + 36864) ltac:(lia)) as E2.
    pose proof (M 17594333495296 lo ltac:(lia)) as E3.
    change (6283263 / 8) with 785407 in E1. change (6320128 / 8) with 790016 in E2.
    change (17594333495296 / 8) with 2199291686912 in E3. lia.
  - pose proof (M (FS + 2134016) b ltac:(lia)) as E1. pose proof (M hi b ltac:(lia)) as E2. lia.
Qed.

(* An address outside [lo, hi) (both multiples of 8) has its shadow byte outside the shadow of [lo, hi). *)
Lemma r6_sh_out : forall lo hi a, lo mod 8 = 0 -> hi mod 8 = 0 -> ~ (lo <= a < hi) ->
  ~ (shadow_addr lo <= shadow_addr a < shadow_addr hi).
Proof. intros lo hi a Hl Hh Ha. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* FSREC (the side-arm FakeStack frame record) moves across a run that writes nothing in the low image (the tp
   word) and no FakeStack byte outside the frame body and outside the class-0 / class-1 hint, flag and frame
   ranges: the class-6 flag byte lies in [FS + 36352, FS + 36608) and the slot's last word at fr + 4088 with
   fr = fs_frame FS 6 j >= FS + 6328320, both apart from those ranges (R3's r3_fsrec asks for every app byte
   below stklo, which the class-0 / class-1 writes of this call break). *)
Lemma r6_fsrec : forall (mem mem' : word -> option byte) W fr FS,
  FSREC fr mem -> word_mem rsegs mem (ACw.as_tp ACw.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  LF.munch W mem mem' ->
  (forall x, 0 <= x < 6283264 -> LF.outside W x) ->
  (forall x, FS <= x < FS + ACw.FS_SIZE -> ~ (fr <= x < fr + FRAME_BYTES) -> ~ (FS <= x < FS + 16) ->
     ~ (FS + 4096 <= x < FS + 28672) -> ~ (FS + 36864 <= x < FS + 2134016) -> LF.outside W x) ->
  FSREC fr mem'.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros mem mem' W fr FS (FS' & j & Htp & HFSr' & Hj & Hfr & Hflag & Htail) Hwtp HFSr MU HWlo HW.
  assert (E : FS' = FS) by (apply (r6_wm_uniq mem (ACw.as_tp ACw.ASYMS) FS' FS Htp Hwtp); lia).
  subst FS'.
  assert (HFSZ : ACw.FS_SIZE = 11571200) by reflexivity.
  assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
  assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
  assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
  rewrite HM6 in Hj.
  exists FS, j.
  split.
  { intros k Hk.
    assert (Hx : 0 <= ACw.as_tp ACw.ASYMS + Z.of_nat k < 2 ^ 64)
      by (unfold ACw.as_tp, ACw.ASYMS; cbn; lia).
    assert (Hm : mem' (Z_to_bv 64 (ACw.as_tp ACw.ASYMS + Z.of_nat k))
                 = mem (Z_to_bv 64 (ACw.as_tp ACw.ASYMS + Z.of_nat k))).
    { apply MU. rewrite MState.unsigned_lit by lia.
      apply HWlo. unfold ACw.as_tp, ACw.ASYMS. cbn. lia. }
    unfold mbyte. rewrite Hm. exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { eapply fl_bytes; [exact Hflag | exact MU |].
    cbn [length]. intros x Hx. rewrite Hfl in Hx. apply HW; lia. }
  { eapply fl_bytes; [exact Htail | exact MU |].
    rewrite length_le8. intros x Hx. rewrite HB6 in Hx. apply HW; lia. }
Qed.

(* ---- frame cells across the call ---- *)

(* The shadow byte of a frame byte is one of the frame's 392 shadow bytes. *)
Lemma r6_sh_in : forall fr k, fr mod 8 = 0 -> 0 <= k < FRAME_BYTES -> Sfr fr <= shadow_addr (fr + k) < Sfr fr + FRAME_SHADOW.
Proof. pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs. intros fr k H8 Hk. unfold Sfr, shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* A shadow byte x of [lo, hi) is the shadow of 8 * (x - K): that byte lies in [lo - 7, hi), in [lo, hi) when lo
   is 8-aligned. *)
Lemma r6_sh_inv : forall lo hi x, shadow_addr lo <= x < shadow_addr hi ->
  lo - 7 <= 8 * (x - ASAN_K) < hi /\ (lo mod 8 = 0 -> lo <= 8 * (x - ASAN_K)) /\
  shadow_addr (8 * (x - ASAN_K)) = x.
Proof.
  intros lo hi x Hx. unfold shadow_addr in *.
  assert (Hdv : 8 * (x - ASAN_K) / 8 = x - ASAN_K) by (rewrite Z.mul_comm, Z.div_mul; lia).
  rewrite Hdv. split; [|split; [|lia]]; Z.div_mod_to_equations; lia.
Qed.

(* A one-block rw_cells record keeps its bytes and its writability across a run that misses it. *)
Lemma r6_rw_keep : forall W m m' A n bs, rw_cells rsegs m A [CB n bs] -> munch W m m' -> wmono rsegs m m' ->
  (forall x, A <= x < A + Z.of_nat n -> outside W x) -> rw_cells rsegs m' A [CB n bs].
Proof.
  intros W m m' A n bs ((Hwf & Hb) & Hw) MU WM HO.
  cbn [cells_wf cell_wf] in Hwf. destruct Hwf as (Hl & _).
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [exact Hl | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. eapply fl_bytes; [exact Hb | exact MU |]. rewrite Hl. exact HO.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. destruct Hw as (H0 & H1 & H). split; [lia|]. split; [lia|].
    intros i Hi. exact (WM _ (H i Hi)).
Qed.


(* ===== the segment lemma ===== *)
Section R6.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, ACw.AsanAllocAPI ACw.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contract (plan-asan section 4 BAS), a Section Hypothesis as the brief prescribes. *)
Hypothesis BUILD : OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_build_as_c.reac_ctrl_build_as_contract.
Local Notation API := (APIf rc).

(* The callee's write window and out[] (W) and its data ranges (D) at the call: build_as's fp lists. *)
Definition r6_Wc (fr spv nb : Z) : list ivl :=
  [(spv - BA.REAC_CTRL_BUILD_AS_K, spv); (fr + 544, fr + 544 + nb)].
Definition r6_Dc (fr mdv nb : Z) : list ivl :=
  [(BA.BA_FR + 72, BA.BA_FR + 240); (mdv, mdv + 296); (fr + 2624, fr + 2624 + 6); (0x21140, 0x21140 + 6);
   (fr + 544, fr + 544 + nb)].

(* The RELRO bytes of the image are the ROM bytes (FRA's G_img_c). *)
Lemma r6_img_bytes : forall (m : word -> option byte) (A : Z) (n : nat) (bs : list byte),
  ms_segs B = rsegs -> G_img_c B AFw.frame_RELRO m ->
  LImg.image_bytes rsegs A n = Some bs ->
  (forall k, (k < n)%nat -> in_globals AFw.frame_RELRO (A + Z.of_nat k)) ->
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 -> bytes_at rsegs m A bs.
Proof.
  intros m A n bs HS HG Himg Hin HA Hn.
  pose proof (LImg.image_bytes_length rsegs n A bs Himg) as Hl.
  split; [exact HA|]. split; [rewrite Hl; exact Hn|].
  intros i Hi. rewrite Hl in Hi.
  rewrite <- (r6_imgb_nth n A bs i Himg Hi).
  pose proof (HG (A + Z.of_nat i) (Hin i Hi)) as HB. rewrite HS in HB. exact HB.
Qed.

(* FRA across the call (the push-5b FRA, as R3's r3_fra): the write set W avoids the cells FRA reads outside the
   frame (low image, frame header, the spills [A + 16, A + 32) and [A + 304, A + 312), the saved registers) and
   keeps every shadow byte readable (RT_meta_write); the run supplies the new frame-shadow list, its heap
   invariant / stklo, the S-anchored window still backed and still addressable outside the frame, the side-arm
   FakeStack record and the frame_AG globals still addressable.  W holds shadow bytes, the callee window and
   side-stack bytes, so neither Tac_slot.sl_fr_meta nor Tac_slot.sl_fr_cl covers it. *)
Lemma r6_fra : forall g fr hb regs regs' mem mem' md W,
  FRA B APIf ra g fr hb regs mem md ->
  LF.munch W mem mem' -> LF.wmono rsegs mem mem' -> ro_agree rsegs mem' -> rt_disjoint W ->
  ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md ->
  ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem' md = ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md ->
  (forall a, in_shadow a -> exists b, mrd rsegs mem' (wa a) = Some b) ->
  (exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW) ->
  (forall x, 0 <= x < 6283264 -> LF.outside W x) ->
  (forall x, fr <= x < fr + 24 -> LF.outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 16 <= x < bv_unsigned (getr regs 9) + 32 -> LF.outside W x) ->
  (forall x, bv_unsigned (getr regs 9) + 304 <= x < bv_unsigned (getr regs 9) + 312 -> LF.outside W x) ->
  (forall x, g_S g - 104 <= x < g_S g -> LF.outside W x) ->
  (forall x, g_S g - AFw.SLOT_STACK <= x < g_S g -> LF.outside W x \/ exists b, mrd rsegs mem' (wa x) = Some b) ->
  (forall a, in_globals AFw.frame_AG a -> addressable mem' a 1) ->
  (forall a, g_S g - AFw.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) -> addressable mem' a 1) ->
  (FSREC fr mem -> FSREC fr mem') ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs regs' mem mem' md W HFRA MU WM HRO HD HAH' HSTK HshR Hshnew HWlo HWhdr HWsel HWspill
    HWsaved HWwin HAG' HWA' Hrec' E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  destruct HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  assert (HSS : AFw.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64).
  { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
  assert (HbvA : bv_unsigned (getr regs 9) = A).
  { unfold rg in Hr9. rewrite Hr9. apply MState.unsigned_lit. exact HA64. }
  rewrite HbvA in HWsel, HWspill.
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
    rewrite MState.unsigned_lit by lia. exact (HWlo x ltac:(lia)). }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_meta_write sp sp mem mem' md md W HRT MU WM HD HshR)|].
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
    - destruct Hin as (lo & len & Hil & Hr). unfold AFw.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia.
    - destruct Hin as (lo & len & Hil & Hr). unfold AFw.frame_RELRO in Hil. cbn in Hil.
      destruct Hil as [E|[]]; injection E as <- <-; lia. }
  split; [rewrite E2; exact Hr2|].
  split; [exact Hspm|].
  split; [unfold ACw.aspZ in *; rewrite E2; exact Haspz|].
  split; [rewrite HSTK; exact Hstklo|].
  split; [rewrite E4; exact Hr4|].
  split; [unfold rg in *; rewrite E8; exact Hr8|].
  split; [unfold rg in *; rewrite E9; exact Hr9|].
  split; [rewrite E3; exact Hr3|].
  split; [unfold rg in *; rewrite E19; exact Hr19|].
  split; [unfold rg in *; rewrite E26; exact Hr26|].
  split; [exact Hfrm|]. split; [exact Hs5|]. split; [exact HAm|]. split; [exact HAS|]. split; [exact Hspa|].
  split; [exact Hfa|]. split; [exact HA416|]. split; [exact HS4|]. split; [exact HAPP|].
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hspill | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWspill x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hsel | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hfr24 | exact MU |].
    rewrite length_le8. intros x Hx. exact (HWsel x ltac:(lia)). }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hrec]]]].
    - left. split; [exact H0|]. split; [exact Hspfr|].
      intros a Ha. rewrite HSTK. exact (Hreal a Ha).
    - right. split; [exact Hfr0|]. split.
      + intros FS Hw HFSr. apply (Hfsb FS); [| exact HFSr].
        intros k Hk. rewrite <- KBlo.
        * exact (Hw k Hk).
        * unfold ACw.as_tp, ACw.ASYMS. cbn. lia.
        * unfold ACw.as_tp, ACw.ASYMS. cbn. lia.
      + split.
        * intros a Ha. destruct (Hfs a Ha) as (FSb & HFSr & Hw & Hlo & Hhi).
          exists FSb. split; [exact HFSr|]. split; [|split; [exact Hlo | exact Hhi]].
          intros k Hk. rewrite KBlo.
          -- exact (Hw k Hk).
          -- unfold ACw.as_tp, ACw.ASYMS. cbn. lia.
          -- unfold ACw.as_tp, ACw.ASYMS. cbn. lia.
        * exact (Hrec' Hrec). }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr1 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split.
  { unfold q64 in *. eapply fl_bytes; [exact Hhdr2 | exact MU |].
    rewrite length_le8. intros x Hx. apply HWhdr. lia. }
  split; [exact Hshnew|].
  split; [exact (r6_stk_tr W mem mem' _ _ Hwin MU WM HWwin)|].
  split.
  { eapply fl_bytes; [exact Hsaved | exact MU |]. intros x Hx.
    apply HWsaved. unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx. lia. }
  split; [intros a Ha; exact (WM (Z_to_bv 64 a) (Herrno a Ha))|].
  split; [exact HAG'|].
  split; [exact HWA'|].
  split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
  split; [exact Hhb | exact Hlive].
Qed.

Lemma seg_R6 : forall b : nat,
  Hat B APIf ra (Inv_A815ec_at B APIf ra) b -> Hat B APIf ra (Inv_A815cc_at B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros b Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HRS & HOUTA & H128 & HPRO & H104 & H96 &
                    Ha0 & H24 & H64 & H112 & H21 & H152 & H144 & HAWid & H208 & (idb0 & HIDB0) &
                    (fjunk0 & HFGB0) & H280 & H240 & (jy0 & HJY0) & (junk32 & HJ320) & HRXS).
  subst c. unfold a0v in Ha0. unfold OUTA in HOUTA.
  pose proof HRS as (Hb6 & HCUR & HOUR & Hr23 & HID & HFG).
  pose proof HPRO as (_ & _ & _ & _ & H168 & _ & _ & _ & HAWour & _).
  destruct (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hlo & Hstkw).
  destruct (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hplace & HfrA & HfsS & Hfrw).
  pose proof HFRA as HFRA0.
  destruct HFRA0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspl & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA & HSHI1 & HSHI2 &
    HSHI3 & Hhb & Hlive).
  pose proof (ACw.aa_laws ACw.ASYMS AsanRTInv.RT API) as ALAWS.
  pose proof (ACw.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH) as Hhigh.
  assert (HSS : AFw.SLOT_STACK = 1048576) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HKv : BA.REAC_CTRL_BUILD_AS_K = 4640) by reflexivity.
  assert (HFSv : FS_SIZE = 11571200) by reflexivity.
  assert (HFSv2 : ACw.FS_SIZE = 11571200) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 17592186044416 + 2147450880) by reflexivity.
  assert (HLMv : LOWMEM_END = 2147450880) by reflexivity.
  assert (HGTv : ACw.GT = 6283264) by reflexivity.
  assert (HGTv2 : ASAN_GT = 6283264) by reflexivity.
  assert (HKK : ASAN_K = 2147450880) by reflexivity.
  assert (HTPv : ACw.as_tp ACw.ASYMS = 0x5db810) by reflexivity.
  assert (HTPr : 0 <= ACw.as_tp ACw.ASYMS < 2 ^ 64) by lia.
  rewrite Haspz in Hlo, Hstkw, Hplace.
  assert (HA64 : 0 <= A < 2 ^ 64) by (destruct Hwin as (Hw0 & Hw1 & _); unfold AFw.SLOT_STACK in *; lia).
  assert (HbvA : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; exact HA64).
  rewrite HbvA in HfrA.
  (* the callee window is addressable: FRA's window clause, the frame being apart from it (fra_frame) *)
  assert (HAWwin : addressable mem (sp - BA.REAC_CTRL_BUILD_AS_K) BA.REAC_CTRL_BUILD_AS_K).
  { split; [lia|]. split; [lia|]. split; [lia|]. intros i Hi.
    pose proof (HWA (sp - BA.REAC_CTRL_BUILD_AS_K + i) ltac:(lia)
                  ltac:(destruct (Hplace BA.REAC_CTRL_BUILD_AS_K ltac:(lia)) as [Hd|Hd]; lia)) as Had.
    destruct Had as (_ & _ & _ & Hb). pose proof (Hb 0 ltac:(lia)) as Hb0.
    rewrite Z.add_0_r in Hb0. exact Hb0. }
  (* the frame is application memory above GT *)
  assert (Happ : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a /\ ACw.GT <= a).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - pose proof (Hreal a Ha). unfold app_mem, ACw.GT, HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *. lia.
    - destruct (Hfs a Ha) as (FSb & HFSrb & Hwb & Hlo2 & Hhi2).
      destruct (ACw.a_laws_fs_place _ _ _ _ _ ALAWS ([] ++ g_H g) mem md FSb HAH Hwb HFSrb)
        as (HGTb & _ & _ & HFapp).
      split; [apply HFapp; lia | lia]. }
  assert (Happ' : forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) by (intros a Ha; exact (proj1 (Happ a Ha))).
  assert (HGT : ACw.GT <= fr) by exact (proj2 (Happ fr ltac:(lia))).
  assert (Hfre : 0 <= fr /\ fr + FRAME_BYTES <= APPMEM_END).
  { destruct (Happ fr ltac:(lia)) as (H1 & _). destruct (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as (H2 & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (HLH : fr + FRAME_BYTES <= LOWMEM_END \/ HIGHMEM_BEG <= fr).
  { destruct (Happ fr ltac:(lia)) as (H1 & _). destruct (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as (H2 & _).
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; clear; intros; Z.div_mod_to_equations; lia).
  assert (HSfr : Sfr fr = fr / 8 + ASAN_K) by reflexivity.
  (* the frame bytes are readable and writable *)
  assert (Hfrd : forall a, fr <= a < fr + FRAME_BYTES -> exists bb, mrd rsegs mem (wa a) = Some bb).
  { intros a Ha. destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
    - destruct Hwin as (_ & _ & Hw). exact (proj2 (Hw a ltac:(unfold AFw.SLOT_STACK in *; lia))).
    - destruct (Hfs a Ha) as (FSb & HFSrb & Hwb & Hlo2 & Hhi2).
      destruct (ACw.a_laws_fs_state _ _ _ _ _ ALAWS ([] ++ g_H g) mem md FSb HAH Hwb HFSrb) as (Hok & _).
      destruct Hok as (Hok1 & _). destruct (Hok1 a ltac:(unfold ACw.FS_SIZE in *; lia)) as (_ & bb & Hb).
      exists bb. exact Hb. }
  assert (Hfstk : stk rsegs mem fr (fr + FRAME_BYTES)).
  { split; [lia|]. split; [lia|]. intros a Ha. split; [exact (Hfrw a Ha) | exact (Hfrd a Ha)]. }
  (* the spill words at the base A *)
  assert (HAr0 : 0 <= A) by lia.
  assert (HAr1 : A + 416 < 2 ^ 64) by (unfold APPMEM_END in HAPP; lia).
  pose proof (r6_spill_at regs mem A 128 (fr + 544) Hr9 HAr0 HAr1 ltac:(lia) H128) as Q128.
  pose proof (r6_spill_at regs mem A 112 (mrow (g_in g)) Hr9 HAr0 HAr1 ltac:(lia) H112) as Q112.
  pose proof (r6_spill_at regs mem A 168 (fr + 2624) Hr9 HAr0 HAr1 ltac:(lia) H168) as Q168.
  pose proof (r6_spill_at regs mem A 104 0x21140 Hr9 HAr0 HAr1 ltac:(lia) H104) as Q104.
  pose proof (r6_spill_at regs mem A 96 0x1234 Hr9 HAr0 HAr1 ltac:(lia) H96) as Q96.
  pose proof (r6_spill_at regs mem A 64 0xe38f0000 Hr9 HAr0 HAr1 ltac:(lia) H64) as Q64.
  pose proof (r6_spill_at regs mem A 152 (Sfr fr + 68) Hr9 HAr0 HAr1 ltac:(lia) H152) as Q152.
  pose proof (r6_spill_at regs mem A 144 (fr + 2688) Hr9 HAr0 HAr1 ltac:(lia) H144) as Q144.
  pose proof (r6_spill_at regs mem A 192 (fr + 2768) Hr9 HAr0 HAr1 ltac:(lia) H208) as Q208.
  pose proof (r6_spill_at regs mem A 280 (fr + 3040) Hr9 HAr0 HAr1 ltac:(lia) H280) as Q280.
  pose proof (r6_spill_at regs mem A 240 (fr + 3056) Hr9 HAr0 HAr1 ltac:(lia) H240) as Q240.
  (* the model row and the turn's length *)
  assert (Histar : 0 <= istar (g_in g) < 11) by (unfold istar, CAT_N; apply Z.mod_pos_bound; lia).
  assert (Hmr : 0x9e800 <= mrow (g_in g) /\ mrow (g_in g) + 296 <= 0x9e800 + 3256)
    by (unfold mrow, CAT, CAT_ROW in *; lia).
  assert (Hmd8 : mrow (g_in g) mod 8 = 0)
    by (unfold mrow, CAT, CAT_ROW; revert Histar; clear; intros; Z.div_mod_to_equations; lia).
  assert (Hmbl : length (rt_mb (g_in g)) = 296%nat) by (unfold rt_mb; apply r6_row_len).
  assert (Hnb : 0 <= rnb g b <= 1492).
  { destruct (Z.eq_dec (rnb g b) 0) as [E0|E0]; [unfold rnb in *; lia|].
    pose proof (r6_rtn (g_in g) (Z.of_nat b) E0) as R2. unfold rnb in *. lia. }
  assert (Hgo : PB.ba_go (fr + 544) (mrow (g_in g)) (Z.of_nat b) = true).
  { unfold PB.ba_go.
    rewrite (proj2 (Z.eqb_neq (fr + 544) 0) ltac:(unfold ACw.GT in *; lia)),
            (proj2 (Z.eqb_neq (mrow (g_in g)) 0) ltac:(lia)),
            (proj2 (Z.leb_le (Z.of_nat b) 6) ltac:(lia)).
    reflexivity. }
  assert (HRveq : rnb g b = (if PB.ba_go (fr + 544) (mrow (g_in g)) (Z.of_nat b) &&
                               rt_E (g_in g) (Z.of_nat b)
                             then 52 + 36 * rt_uw (g_in g) else 0)).
  { rewrite Hgo. cbn [andb]. unfold rnb, rt_n. reflexivity. }
  (* the side stack: the class-0 / class-1 package of the call, from FRA (Tac_fsfree.fra_fp, cs = [0; 1]) *)
  assert (HWin : forall w, In w (r6_Wc fr sp (rnb g b)) ->
            (g_S g - AFw.SLOT_STACK <= fst w /\ snd w <= g_S g) \/ (fr <= fst w /\ snd w <= fr + FRAME_BYTES) \/
            (Sfr fr <= fst w /\ snd w <= Sfr fr + FRAME_SHADOW)).
  { intros w Hw. unfold r6_Wc in Hw. destruct Hw as [<- | [<- | []]]; cbn [fst snd]; [left | right; left]; lia. }
  assert (HDin : forall d, In d (r6_Dc fr (mrow (g_in g)) (rnb g b)) ->
            snd d <= ACw.GT \/ (fr <= fst d /\ snd d <= fr + FRAME_BYTES) \/
            (fst d < snd d /\ exists p n, In (p, n) ([] ++ g_H g) /\ p <= fst d /\ snd d <= p + n)).
  { intros d Hd. unfold r6_Dc in Hd. destruct Hd as [<- | [<- | [<- | [<- | [<- | []]]]]]; cbn [fst snd];
      [left; unfold BA.BA_FR; lia | left; lia | right; left; lia | left; lia | right; left; lia]. }
  destruct (fra_fp B APIf ra g fr [] regs mem md [0%nat; 1%nat] BA.REAC_CTRL_BUILD_AS_K
              (r6_Wc fr sp (rnb g b)) (r6_Dc fr (mrow (g_in g)) (rnb g b)) HFRA
              ltac:(intros cc Hcc; destruct Hcc as [<- | [<- | []]]; lia) ltac:(lia) HWin HDin)
    as (FS & HFP & HTLS0 & HDJF & _).
  rewrite Haspz in HFP, HTLS0.
  assert (HTLS : BA.reac_ctrl_build_as_tls mem (ACw.as_tp ACw.ASYMS) FS (sp - BA.REAC_CTRL_BUILD_AS_K) sp)
    by (unfold BA.reac_ctrl_build_as_tls; exact HTLS0).
  pose proof HFP as HFP0.
  destruct HFP0 as (DT & TS & Cc & Tt & DB & kk & HTLSc & HTPw & HFSplace & H88 & H96b & HCLS & HFSlo2 & HAwin2 &
                    _ & _).
  destruct HFSplace as (HFS0 & HFSmod & HFSgt & HFSapp & HFSstk).
  assert (HFSr : 0 <= FS < 2 ^ 64) by (unfold FS_SIZE in *; lia).
  assert (HGTFS : ACw.GT <= FS) by lia.
  assert (HfrFPW : forall x, fr <= x < fr + FRAME_BYTES -> outside (fp_w [0%nat; 1%nat] FS) x).
  { intros x Hx. apply (fl_dj_out_r _ _ fr (fr + FRAME_BYTES) x HDJF); [left; reflexivity | exact Hx]. }
  assert (HshFPW : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> outside (fp_w [0%nat; 1%nat] FS) x).
  { intros x Hx. apply (fl_dj_out_r _ _ (Sfr fr) (Sfr fr + FRAME_SHADOW) x HDJF); [right; left; reflexivity | exact Hx]. }
  pose proof (mem_rel_normalize rsegs mem Hro) as REL.
  (* ---- the call's premises at the normalized memory ---- *)
  assert (NMI : mem_inv rsegs (normalize rsegs mem)) by apply mem_inv_normalize.
  assert (NAC : asan_cells (normalize rsegs mem))
    by (apply (proj1 (r6_ac_iff mem _ REL)); exact (AsanRTInv.RT_cells _ _ _ HRT)).
  assert (NSW : shadow_rw (normalize rsegs mem))
    by (apply (proj1 (r6_shadow_iff mem _ REL)); exact (AsanRTInv.RT_shadow_rw _ _ _ HRT)).
  assert (NST : stk rsegs (normalize rsegs mem) (sp - BA.REAC_CTRL_BUILD_AS_K) sp).
  { apply (proj1 (r6_stk_iff mem (normalize rsegs mem) (sp - BA.REAC_CTRL_BUILD_AS_K) sp REL
                 ltac:(lia) ltac:(lia))).
    destruct (stk_split rsegs mem (sp - FN_STACK) (sp - BA.REAC_CTRL_BUILD_AS_K) sp Hstkw ltac:(lia)) as (_ & Hw2).
    exact Hw2. }
  assert (N96 : bytes_at rsegs (normalize rsegs mem) (A + 96) (le8 (Z_to_bv 64 0x1234)))
    by (apply (bytes_at_normalize rsegs mem _ _ Hro); exact Q96).
  assert (N104 : bytes_at rsegs (normalize rsegs mem) (A + 104) (le8 (Z_to_bv 64 0x21140)))
    by (apply (bytes_at_normalize rsegs mem _ _ Hro); exact Q104).
  assert (N112 : bytes_at rsegs (normalize rsegs mem) (A + 112) (le8 (Z_to_bv 64 (mrow (g_in g)))))
    by (apply (bytes_at_normalize rsegs mem _ _ Hro); exact Q112).
  assert (N168 : bytes_at rsegs (normalize rsegs mem) (A + 168) (le8 (Z_to_bv 64 (fr + 2624))))
    by (apply (bytes_at_normalize rsegs mem _ _ Hro); exact Q168).
  assert (NBA : bytes_at rsegs (normalize rsegs mem) (BA.BA_FR + 72) PB.ba_tbl).
  { apply (bytes_at_normalize rsegs mem _ _ Hro).
    apply (r6_img_bytes mem (BA.BA_FR + 72) 168 PB.ba_tbl SEGS Hgimg r6_ba_img).
    - intros k Hk. exists 0x9e348, 9344. split; [left; reflexivity | unfold BA.BA_FR; lia].
    - unfold BA.BA_FR; lia.
    - unfold BA.BA_FR; cbn; lia. }
  assert (NROW : bytes_at rsegs (normalize rsegs mem) (mrow (g_in g)) (rt_mb (g_in g))).
  { apply (bytes_at_normalize rsegs mem _ _ Hro).
    apply (r6_img_bytes mem (mrow (g_in g)) 296 (rt_mb (g_in g)) SEGS Hgimg
             (r6_row_img (istar (g_in g)) Histar)).
    - intros k Hk. exists 0x9e348, 9344. split; [left; reflexivity | lia].
    - lia.
    - cbn; lia. }
  assert (NSB : bytes_at rsegs (normalize rsegs mem) 0x21140 r6_sb).
  { apply (ro_bytes_at rsegs); [apply mem_inv_normalize | lia | rewrite r6_sb_len; cbn; lia |].
    exact (LImg.ro_bytes_b_sound rsegs _ _ r6_sb_ro). }
  assert (NOUR : bytes_at rsegs (normalize rsegs mem) (fr + 2624) (OUR (g_in g)))
    by (apply (bytes_at_normalize rsegs mem _ _ Hro); exact HOUR).
  assert (NDBL : length (OUR (g_in g)) = 6%nat) by apply OUR_length.
  assert (LD1 : ly_dj (sp - BA.REAC_CTRL_BUILD_AS_K) sp (BA.BA_FR + 72) (BA.BA_FR + 240))
    by (unfold ly_dj, BA.BA_FR; right; lia).
  assert (LD2 : ly_dj (sp - BA.REAC_CTRL_BUILD_AS_K) sp (fr + 2624) (fr + 2624 + 6)).
  { destruct (Hplace BA.REAC_CTRL_BUILD_AS_K ltac:(lia)) as [Hd|Hd]; unfold ly_dj; [right|left]; lia. }
  assert (LD3 : ly_dj (sp - BA.REAC_CTRL_BUILD_AS_K) sp 0x21140 (0x21140 + 6)) by (unfold ly_dj; right; lia).
  assert (LD4 : ly_dj (sp - BA.REAC_CTRL_BUILD_AS_K) sp (mrow (g_in g)) (mrow (g_in g) + 296))
    by (unfold ly_dj; right; lia).
  assert (NMD : mrow (g_in g) <> 0 ->
            mrow (g_in g) mod 8 = 0 /\ mrow (g_in g) + 296 <= 2 ^ 64 /\ length (rt_mb (g_in g)) = 296%nat /\
            bytes_at rsegs (normalize rsegs mem) (mrow (g_in g)) (rt_mb (g_in g)) /\
            ly_dj (sp - BA.REAC_CTRL_BUILD_AS_K) sp (mrow (g_in g)) (mrow (g_in g) + 296)).
  { intros _. split; [exact Hmd8|]. split; [lia|]. split; [exact Hmbl|]. split; [exact NROW | exact LD4]. }
  assert (NNM : mrow (g_in g) <> 0 ->
            (Z.of_nat b = 5 \/ Z.of_nat b = 6) /\ has (rt_mb (g_in g)) <> 0 /\ rname (rt_mb (g_in g)) <> 0 ->
            name_ok (rt_nb (g_in g)) /\
            bytes_at rsegs (normalize rsegs mem) (rname (rt_mb (g_in g))) (rt_nb (g_in g)) /\
            ly_dj (sp - BA.REAC_CTRL_BUILD_AS_K) sp (rname (rt_mb (g_in g)))
                  (rname (rt_mb (g_in g)) + Z.of_nat (length (rt_nb (g_in g))))).
  { intros _ (_ & Hh & Hn).
    destruct (r6_name_facts (istar (g_in g)) Histar Hh Hn) as (HOK & HP1 & HP2 & HRO2 & _).
    unfold rt_nb, rt_mb in *.
    split; [exact HOK|]. split.
    - apply (ro_bytes_at rsegs); [apply mem_inv_normalize | lia | lia |].
      exact (LImg.ro_bytes_b_sound rsegs _ _ HRO2).
    - unfold ly_dj. right. lia. }
  assert (NOB2 : fr + 544 <> 0 -> fr + 544 + 1492 <= 2 ^ 64) by (intros _; lia).
  assert (HObE : exists junk,
            PB.ba_go (fr + 544) (mrow (g_in g)) (Z.of_nat b) && rt_E (g_in g) (Z.of_nat b) = true ->
            rw_cells rsegs (normalize rsegs mem) (fr + 544)
              [CB (Z.to_nat (52 + 36 * rt_uw (g_in g))) junk]).
  { destruct (PB.ba_go (fr + 544) (mrow (g_in g)) (Z.of_nat b) && rt_E (g_in g) (Z.of_nat b)) eqn:HE.
    - assert (HE2 : rt_E (g_in g) (Z.of_nat b) = true) by (apply andb_true_iff in HE; tauto).
      assert (Hlen : 52 + 36 * rt_uw (g_in g) = rnb g b)
        by (unfold rnb, rt_n; rewrite HE2; reflexivity).
      destruct (stk_split rsegs mem fr (fr + 544) (fr + FRAME_BYTES) Hfstk ltac:(lia)) as (_ & Hf2).
      destruct (stk_split rsegs mem (fr + 544) (fr + 544 + rnb g b) (fr + FRAME_BYTES) Hf2 ltac:(lia)) as (Hos & _).
      destruct (stk_bytes rsegs mem (fr + 544) (fr + 544 + rnb g b) Hos ltac:(lia)) as (junk & Hjl & Hjb).
      exists junk. intros _. rewrite Hlen.
      replace (Z.to_nat (rnb g b)) with (length junk) by lia.
      apply r6_rw_CB.
      + apply (bytes_at_normalize rsegs mem _ _ Hro). exact Hjb.
      + apply (wr_at_norm rsegs mem _ _ _ REL).
        * replace (Z.of_nat (length junk)) with (fr + 544 + rnb g b - (fr + 544)) by lia.
          exact (r6_wr_stk mem (fr + 544) (fr + 544 + rnb g b) Hos).
        * intros i Hi. apply r6_ro_hi. unfold ACw.GT in *. lia.
    - exists []. intros Hf. discriminate Hf. }
  destruct HObE as (junk & NOBE).
  assert (NOBX : PB.ba_go (fr + 544) (mrow (g_in g)) (Z.of_nat b) && rt_E (g_in g) (Z.of_nat b) = true ->
            rw_cells rsegs (normalize rsegs mem) (fr + 544)
              [CB (Z.to_nat (52 + 36 * rt_uw (g_in g))) junk] /\
            ly_dj (sp - BA.REAC_CTRL_BUILD_AS_K) sp (fr + 544) (fr + 544 + (52 + 36 * rt_uw (g_in g))) /\
            ly_dj (fr + 544) (fr + 544 + (52 + 36 * rt_uw (g_in g))) (BA.BA_FR + 72) (BA.BA_FR + 240) /\
            ly_dj (fr + 544) (fr + 544 + (52 + 36 * rt_uw (g_in g))) (mrow (g_in g)) (mrow (g_in g) + 296) /\
            (((Z.of_nat b = 5 \/ Z.of_nat b = 6) /\ has (rt_mb (g_in g)) <> 0 /\ rname (rt_mb (g_in g)) <> 0) ->
               ly_dj (fr + 544) (fr + 544 + (52 + 36 * rt_uw (g_in g))) (rname (rt_mb (g_in g)))
                 (rname (rt_mb (g_in g)) + Z.of_nat (length (rt_nb (g_in g))))) /\
            ly_dj (fr + 544) (fr + 544 + (52 + 36 * rt_uw (g_in g))) (fr + 2624) (fr + 2624 + 6) /\
            ly_dj (fr + 544) (fr + 544 + (52 + 36 * rt_uw (g_in g))) 0x21140 (0x21140 + 6)).
  { intros HE. assert (HE2 : rt_E (g_in g) (Z.of_nat b) = true) by (apply andb_true_iff in HE; tauto).
      assert (Hlen : 52 + 36 * rt_uw (g_in g) = rnb g b)
        by (unfold rnb, rt_n; rewrite HE2; reflexivity).
    split; [exact (NOBE HE)|]. rewrite Hlen.
    split; [destruct (Hplace BA.REAC_CTRL_BUILD_AS_K ltac:(lia)) as [Hd|Hd]; unfold ly_dj; [right|left]; lia|].
    split; [unfold ly_dj, BA.BA_FR, ACw.GT in *; right; lia|].
    split; [unfold ly_dj, ACw.GT in *; right; lia|].
    split.
    - intros (_ & Hh & Hn). destruct (r6_name_facts (istar (g_in g)) Histar Hh Hn) as (_ & HP1 & HP2 & _ & _).
      unfold rt_nb, rt_mb in *. unfold ly_dj, ACw.GT in *. right. lia.
    - split; [unfold ly_dj; left; lia | unfold ly_dj, ACw.GT in *; right; lia]. }
  assert (NAW : addressable (normalize rsegs mem) (sp - BA.REAC_CTRL_BUILD_AS_K) BA.REAC_CTRL_BUILD_AS_K)
    by (apply (proj1 (r6_addr_iff mem _ _ _ REL)); exact HAWwin).
  assert (NAWsw : addressable (normalize rsegs mem) BA.BA_SW 56).
  { apply (proj1 (r6_addr_iff mem _ _ _ REL)).
    apply (r6_addr_glob mem 0x21980 56 BA.BA_SW 56 HAG ltac:(vm_compute; reflexivity));
      unfold BA.BA_SW, APPMEM_END; lia. }
  assert (NAWba : addressable (normalize rsegs mem) (BA.BA_FR + 72) 168).
  { apply (proj1 (r6_addr_iff mem _ _ _ REL)).
    apply (r6_addr_glob mem 0x9f7e0 264 (BA.BA_FR + 72) 168 HAG ltac:(vm_compute; reflexivity));
      unfold BA.BA_FR, APPMEM_END; lia. }
  assert (NAWd : addressable (normalize rsegs mem) (fr + 2624) 6)
    by (apply (proj1 (r6_addr_iff mem _ _ _ REL)); exact HAWour).
  assert (NAWs : addressable (normalize rsegs mem) 0x21140 6).
  { apply (proj1 (r6_addr_iff mem _ _ _ REL)).
    apply (r6_addr_glob mem 0x21140 6 0x21140 6 HAG ltac:(vm_compute; reflexivity)); unfold APPMEM_END; lia. }
  assert (NAWmd : mrow (g_in g) <> 0 -> addressable (normalize rsegs mem) (mrow (g_in g)) 296).
  { intros _. apply (proj1 (r6_addr_iff mem _ _ _ REL)).
    apply (r6_addr_glob mem 0x9e800 3256 (mrow (g_in g)) 296 HAG ltac:(vm_compute; reflexivity));
      unfold APPMEM_END; lia. }
  assert (NAWnm : mrow (g_in g) <> 0 ->
            (Z.of_nat b = 5 \/ Z.of_nat b = 6) /\ has (rt_mb (g_in g)) <> 0 /\ rname (rt_mb (g_in g)) <> 0 ->
            addressable (normalize rsegs mem) (rname (rt_mb (g_in g)))
              (Z.of_nat (length (rt_nb (g_in g))))).
  { intros _ (_ & Hh & Hn). apply (proj1 (r6_addr_iff mem _ _ _ REL)).
    destruct (r6_name_facts (istar (g_in g)) Histar Hh Hn) as (_ & HP1 & HP2 & _ & HIN).
    unfold rt_nb, rt_mb in *.
    apply (r6_addr_bytes mem (rname (rowb (istar (g_in g)))) (length (img_cstr (rname (rowb (istar (g_in g)))) 16))
             HAG HIN); unfold APPMEM_END; lia. }
  assert (NAWo : PB.ba_go (fr + 544) (mrow (g_in g)) (Z.of_nat b) && rt_E (g_in g) (Z.of_nat b) = true ->
            addressable (normalize rsegs mem) (fr + 544) (52 + 36 * rt_uw (g_in g)) /\
            app_mem (fr + 544 + (52 + 36 * rt_uw (g_in g))) /\
            (fr + 544 + (52 + 36 * rt_uw (g_in g)) <= RT_LO \/ RT_HI <= fr + 544)).
  { intros HE. assert (HE2 : rt_E (g_in g) (Z.of_nat b) = true) by (apply andb_true_iff in HE; tauto).
      assert (Hlen : 52 + 36 * rt_uw (g_in g) = rnb g b)
        by (unfold rnb, rt_n; rewrite HE2; reflexivity).
    rewrite Hlen. split.
    - apply (proj1 (r6_addr_iff mem _ _ _ REL)).
      exact (r6_addr_sub mem (fr + 544) 1492 (rnb g b) HOUTA ltac:(lia)).
    - split; [apply Happ'; lia|]. right. unfold RT_HI, ACw.GT in *. lia. }
  assert (NJ14 : Z.of_nat b = 1 -> addressable (normalize rsegs mem) RBM.JOIN_0014 32).
  { intros _. apply (proj1 (r6_addr_iff mem _ _ _ REL)).
    apply (r6_addr_glob mem 0x21a60 32 RBM.JOIN_0014 32 HAG ltac:(vm_compute; reflexivity));
      unfold RBM.JOIN_0014, APPMEM_END; lia. }
  assert (NJ13 : Z.of_nat b = 2 -> addressable (normalize rsegs mem) RBM.JOIN_0013 32).
  { intros _. apply (proj1 (r6_addr_iff mem _ _ _ REL)).
    apply (r6_addr_glob mem 0x21a20 32 RBM.JOIN_0013 32 HAG ltac:(vm_compute; reflexivity));
      unfold RBM.JOIN_0013, APPMEM_END; lia. }
  assert (NAPPd : app_mem (fr + 2624 + 6) /\ app_mem (fr + 2624 + 7)) by (split; apply Happ'; lia).
  assert (NAPPs : app_mem (0x21140 + 6) /\ app_mem (0x21140 + 7))
    by (unfold app_mem, LOWMEM_END; split; left; lia).
  assert (NFPc : fp [0%nat; 1%nat] (normalize rsegs mem) (ACw.as_tp ACw.ASYMS) FS
                   (sp - BA.REAC_CTRL_BUILD_AS_K) sp
                   [(sp - BA.REAC_CTRL_BUILD_AS_K, sp); (fr + 544, fr + 544 + rnb g b)]
                   [(BA.BA_FR + 72, BA.BA_FR + 240); (mrow (g_in g), mrow (g_in g) + 296);
                    (fr + 2624, fr + 2624 + 6); (0x21140, 0x21140 + 6); (fr + 544, fr + 544 + rnb g b)])
    by (apply (proj1 (r6_fp_iff [0%nat; 1%nat] mem (normalize rsegs mem) (ACw.as_tp ACw.ASYMS) FS
                   (sp - BA.REAC_CTRL_BUILD_AS_K) sp _ _ REL ltac:(lia) ltac:(lia))); exact HFP).
  assert (NTLS : BA.reac_ctrl_build_as_tls (normalize rsegs mem) (ACw.as_tp ACw.ASYMS) FS
                   (sp - BA.REAC_CTRL_BUILD_AS_K) sp)
    by (apply (proj1 (r6_btls_iff mem _ _ _ _ _ REL)); exact HTLS).
  assert (NFPN : mrow (g_in g) <> 0 ->
            (Z.of_nat b = 5 \/ Z.of_nat b = 6) /\ has (rt_mb (g_in g)) <> 0 /\ rname (rt_mb (g_in g)) <> 0 ->
            fp_dj [(rname (rt_mb (g_in g)), rname (rt_mb (g_in g)) + Z.of_nat (length (rt_nb (g_in g))))]
                  (fp_w [0%nat; 1%nat] FS)).
  { intros _ (_ & Hh & Hn). destruct (r6_name_facts (istar (g_in g)) Histar Hh Hn) as (_ & HP1 & HP2 & _ & _).
    unfold rt_nb, rt_mb in *.
    apply r6_dj_low; [unfold ACw.GT; lia | exact HGTFS]. }
  assert (NHM : HIGHMEM_BEG <= sp - BA.REAC_CTRL_BUILD_AS_K) by lia.
  assert (NAE : sp <= APPMEM_END) by lia.
  assert (NSPr : 0 <= sp < 2 ^ 64) by lia.
  assert (NOr : 0 <= fr + 544 < 2 ^ 64) by lia.
  assert (NMDr : 0 <= mrow (g_in g) < 2 ^ 64) by lia.
  assert (NBBr : 0 <= Z.of_nat b <= 6) by lia.
  assert (NDr : 0 <= fr + 2624 < 2 ^ 64) by lia.
  assert (NAr : A + 176 <= 2 ^ 64) by lia.
  (* ---- the run ---- *)
  rewrite SEGS.
  eapply (sl_run_lib regs (Z_to_bv 64 0x815cc) mem md
    (fun R pc' mem' =>
       pc' = Z_to_bv 64 0x815ec /\
       getr R 1 = Z_to_bv 64 0x815ec /\ getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\
       getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\
       getr R 10 = Z_to_bv 64 (rnb g b) /\ getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\
       getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\
       getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
       munch (r6_WW fr sp (rnb g b) FS) mem mem' /\ wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       stk rsegs mem' (sp - BA.REAC_CTRL_BUILD_AS_K) sp /\ asan_cells mem' /\ shadow_rw mem' /\
       addressable mem' (sp - BA.REAC_CTRL_BUILD_AS_K) BA.REAC_CTRL_BUILD_AS_K /\
       ACw.a_fs_ok mem' FS /\
       (forall x, fr + 544 <= x < fr + 544 + rnb g b -> exists bx, mrd rsegs mem' (wa x) = Some bx) /\
       (rt_E (g_in g) (Z.of_nat b) = true -> bytes_at rsegs mem' (fr + 544) (rt_F (g_in g) (Z.of_nat b))))
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    eapply evt_mono.
    + eapply (evt_normalize rsegs _ _ fp_regs _ fp_csr None mem (seg_rom rsegs)
               ltac:(vm_compute; reflexivity) Hro).
      apply (r6_evt BUILD) with (A := A) (spv := sp) (TPv := ACw.as_tp ACw.ASYMS) (o := fr + 544)
        (mdv := mrow (g_in g)) (bb := Z.of_nat b) (d := fr + 2624) (FS := FS)
        (n := rt_uw (g_in g)) (len := 52 + 36 * rt_uw (g_in g)) (Rv := rnb g b)
        (Eb := rt_E (g_in g) (Z.of_nat b)) (mb := rt_mb (g_in g)) (nb := rt_nb (g_in g))
        (db := OUR (g_in g)) (sb := r6_sb) (junk := junk).
      all: try assumption.
      all: try reflexivity.
      all: try lia.
    + intros ms (s0 & HQ & HREL & HROs).
      destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                      Es0 & MUn & WMn & MIn & STn & ACn & SWn & AWn & FPn & OUTn & OUTFn).
      subst s0.
      destruct HREL as (Hrg & Hrf & Hpcv & Hsv & Hrv & Hfcs & Hrom & HMR).
      destruct ms as [R1 F1 pc1 svc1 rv1 fc1 mr rom1].
      cbn in Hrg, Hrf, Hpcv, Hsv, Hrv, Hfcs, Hrom, HMR, HROs.
      subst R1 F1 pc1 svc1 rv1 fc1 rom1.
      eexists. exists (Z_to_bv 64 0x815ec), mr.
      split; [reflexivity|].
      assert (MUr : munch (r6_WW fr sp (rnb g b) FS) mem mr)
        by (apply (munch_rel rsegs _ mem (normalize rsegs mem) mr m0' REL HMR HROs); exact MUn).
      assert (WMr : wmono rsegs mem mr)
        by (apply (wmono_rel rsegs mem (normalize rsegs mem) mr m0' REL HMR HROs); exact WMn).
      assert (ROr : ro_agree rsegs mr) by exact (ro_agree_same rsegs mem mr Hro HROs).
      assert (STr : stk rsegs mr (sp - BA.REAC_CTRL_BUILD_AS_K) sp)
        by (apply (proj2 (r6_stk_iff mr m0' (sp - BA.REAC_CTRL_BUILD_AS_K) sp HMR ltac:(lia) ltac:(lia))); exact STn).
      assert (ACr : asan_cells mr) by (apply (proj2 (r6_ac_iff mr m0' HMR)); exact ACn).
      assert (SWr : shadow_rw mr) by (apply (proj2 (r6_shadow_iff mr m0' HMR)); exact SWn).
      assert (AWr : addressable mr (sp - BA.REAC_CTRL_BUILD_AS_K) BA.REAC_CTRL_BUILD_AS_K)
        by (apply (proj2 (r6_addr_iff mr m0' _ _ HMR)); exact AWn).
      assert (FPr : fp [0%nat; 1%nat] mr (ACw.as_tp ACw.ASYMS) FS (sp - BA.REAC_CTRL_BUILD_AS_K) sp
                      [(sp - BA.REAC_CTRL_BUILD_AS_K, sp); (fr + 544, fr + 544 + rnb g b)]
                      [(BA.BA_FR + 72, BA.BA_FR + 240); (mrow (g_in g), mrow (g_in g) + 296);
                       (fr + 2624, fr + 2624 + 6); (0x21140, 0x21140 + 6); (fr + 544, fr + 544 + rnb g b)])
        by (apply (proj2 (r6_fp_iff [0%nat; 1%nat] mr m0' (ACw.as_tp ACw.ASYMS) FS
                     (sp - BA.REAC_CTRL_BUILD_AS_K) sp _ _ HMR ltac:(lia) ltac:(lia))); exact FPn).
      assert (Hwtp0 : word_mem rsegs mem (ACw.as_tp ACw.ASYMS) FS).
      { pose proof (bytes_at_le8_word rsegs mem (ACw.as_tp ACw.ASYMS) (Z_to_bv 64 FS) HTPw) as HW.
        rewrite MState.unsigned_lit in HW by lia. exact HW. }
      assert (HFSok : ACw.a_fs_ok mem FS)
        by exact (proj1 (ACw.a_laws_fs_state _ _ _ _ _ ALAWS ([] ++ g_H g) mem md FS HAH Hwtp0 HFSr)).
      assert (FSOKr : ACw.a_fs_ok mr FS).
      { apply (r6_fsok mem mr fr sp (rnb g b) FS (ACw.as_tp ACw.ASYMS) (sp - BA.REAC_CTRL_BUILD_AS_K) sp
                 _ _ HFSok MUr FPr); [| lia | lia].
        intros x Hx G1 G2. apply r6_out_WW.
        - lia.
        - destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
          + pose proof (HfsS FS Hwtp0 HFSr) as Hfrb. lia.
          + pose proof (HfsS FS Hwtp0 HFSr) as Hfrb. lia.
        - apply r6_out_fpw; [lia | lia | lia |].
          intros HC. apply (app_not_shadow x (HFSapp x ltac:(unfold FS_SIZE; lia))).
          apply (r6_shadow_ivl (FS + 36864) (FS + 2134016) x);
            [intros a Ha; apply HFSapp; unfold FS_SIZE; lia | lia | unfold shadow_addr in HC; lia].
        - intros HC. apply (app_not_shadow x (HFSapp x ltac:(unfold FS_SIZE; lia))).
          apply (r6_shadow_ivl (sp - BA.REAC_CTRL_BUILD_AS_K) sp x);
            [exact HAwin2 | lia | unfold shadow_addr in HC; lia]. }
      assert (PRESr : forall x, fr + 544 <= x < fr + 544 + rnb g b ->
                exists bx, mrd rsegs mr (wa x) = Some bx).
      { intros x Hx. destruct (OUTn x Hx) as (bx & Hb). exists bx. rewrite (mrd_rel rsegs mr m0' (wa x) HMR). exact Hb. }
      (* out[] = rt_F of turn b: build_as's emitted frame (db = our[] = OUR, sb = round_trip.box = box6, the count
         word 0x1234 = CNT16, the block rt_X and the length rt_n) *)
      assert (OUTFr : rt_E (g_in g) (Z.of_nat b) = true ->
                bytes_at rsegs mr (fr + 544) (rt_F (g_in g) (Z.of_nat b))).
      { intros HE2.
        assert (HEt : PB.ba_go (fr + 544) (mrow (g_in g)) (Z.of_nat b) && rt_E (g_in g) (Z.of_nat b) = true)
          by (rewrite Hgo, HE2; reflexivity).
        pose proof (OUTFn HEt) as Hb.
        apply (proj2 (bytes_at_rel rsegs mr m0' _ _ HMR)).
        unfold rt_F. rewrite <- r6_box6. unfold CNT16.
        replace (rt_n (g_in g) (Z.of_nat b)) with (52 + 36 * rt_uw (g_in g))
          by (unfold rt_n; rewrite HE2; reflexivity).
        exact Hb. }
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact MUr|]. split; [exact WMr|]. split; [exact ROr|]. split; [exact STr|].
      split; [exact ACr|]. split; [exact SWr|]. split; [exact AWr|]. split; [exact FSOKr|].
      split; [exact PRESr | exact OUTFr].
  (* ---- the exit cut ---- *)
  - intros R pc' mem' regs'' md' HK Hreg Hmat.
    destruct HK as (Hpc & E1 & E2 & E3 & E4 & E8 & E9 & E10 & E19 & E21 & E22 & E23 & E24 & E25 & E26 &
                    MU & WM & ROm & STm & ACm & SWm & AWm & FSOK & PRES & OUTF).
    subst pc'.
    assert (K1 : getr regs'' 1 = Z_to_bv 64 0x815ec) by (rewrite Hreg; exact E1).
    assert (K2 : getr regs'' 2 = getr regs 2) by (rewrite Hreg; exact E2).
    assert (K3 : getr regs'' 3 = getr regs 3) by (rewrite Hreg; exact E3).
    assert (K4 : getr regs'' 4 = getr regs 4) by (rewrite Hreg; exact E4).
    assert (K8 : getr regs'' 8 = getr regs 8) by (rewrite Hreg; exact E8).
    assert (K9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact E9).
    assert (K10 : getr regs'' 10 = Z_to_bv 64 (rnb g b)) by (rewrite Hreg; exact E10).
    assert (K19 : getr regs'' 19 = getr regs 19) by (rewrite Hreg; exact E19).
    assert (K21 : getr regs'' 21 = getr regs 21) by (rewrite Hreg; exact E21).
    assert (K22 : getr regs'' 22 = getr regs 22) by (rewrite Hreg; exact E22).
    assert (K23 : getr regs'' 23 = getr regs 23) by (rewrite Hreg; exact E23).
    assert (K24 : getr regs'' 24 = getr regs 24) by (rewrite Hreg; exact E24).
    assert (K25 : getr regs'' 25 = getr regs 25) by (rewrite Hreg; exact E25).
    assert (K26 : getr regs'' 26 = getr regs 26) by (rewrite Hreg; exact E26).
    (* which bytes the segment leaves alone *)
    assert (Hshx : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> LOWMEM_END <= x < HIGHMEM_BEG).
    { intros x Hx. rewrite HSfr in Hx. unfold ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *.
      Z.div_mod_to_equations. lia. }
    assert (HoutHI : forall x, sp <= x -> x < 2 ^ 64 -> ~ (fr + 544 <= x < fr + 544 + rnb g b) ->
              outside (r6_WW fr sp (rnb g b) FS) x).
    { intros x Hx Hx2 Hnx. apply r6_out_WW; [lia | exact Hnx | |].
      - apply r6_out_fpw; [lia | lia | lia |].
        intros HC. assert (HI : in_shadow x).
        { apply (r6_shadow_ivl (FS + 36864) (FS + 2134016) x);
            [intros a Ha; apply HFSapp; unfold FS_SIZE; lia | lia | unfold shadow_addr in HC; lia]. }
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in HI. lia.
      - intros HC. assert (HI : in_shadow x).
        { apply (r6_shadow_ivl (sp - BA.REAC_CTRL_BUILD_AS_K) sp x);
            [exact HAwin2 | lia | unfold shadow_addr in HC; lia]. }
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in HI. lia. }
    assert (HoutLO : forall x, 0 <= x < ACw.GT -> outside (r6_WW fr sp (rnb g b) FS) x).
    { intros x Hx. apply r6_out_WW; [lia | lia | |].
      - apply r6_out_fpw; [lia | lia | lia |].
        intros HC. unfold shadow_addr, ASAN_K, ACw.GT in *. Z.div_mod_to_equations. lia.
      - intros HC. unfold shadow_addr, ASAN_K, ACw.GT in *. Z.div_mod_to_equations. lia. }
    assert (HoutFR : forall x, fr <= x < fr + FRAME_BYTES -> ~ (fr + 544 <= x < fr + 544 + rnb g b) ->
              outside (r6_WW fr sp (rnb g b) FS) x).
    { intros x Hx Hnx. apply r6_out_WW; [| exact Hnx | exact (HfrFPW x Hx) |].
      - destruct (Hplace BA.REAC_CTRL_BUILD_AS_K ltac:(lia)) as [Hd|Hd]; lia.
      - intros HC. apply (app_not_shadow x (Happ' x Hx)).
        apply (r6_shadow_ivl (sp - BA.REAC_CTRL_BUILD_AS_K) sp x);
          [exact HAwin2 | lia | unfold shadow_addr in HC; lia]. }
    assert (HoutSH : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> outside (r6_WW fr sp (rnb g b) FS) x).
    { intros x Hx. pose proof (Hshx x Hx) as Hxr. apply r6_out_WW; [| | exact (HshFPW x Hx) |].
      - lia.
      - destruct HLH as [HL|HL]; rewrite HSfr in Hx; unfold ASAN_K, LOWMEM_END, HIGHMEM_BEG in *;
          intros HC; Z.div_mod_to_equations; lia.
      - intros HC. rewrite HSfr in Hx. unfold shadow_addr, ASAN_K in *.
        destruct (Hplace BA.REAC_CTRL_BUILD_AS_K ltac:(lia)) as [Hd|Hd]; Z.div_mod_to_equations; lia. }
    (* the heap invariant across the call *)
    assert (Hwtp : word_mem rsegs mem (ACw.as_tp ACw.ASYMS) FS).
    { pose proof (bytes_at_le8_word rsegs mem (ACw.as_tp ACw.ASYMS) (Z_to_bv 64 FS) HTPw) as HW.
      rewrite MState.unsigned_lit in HW by lia. exact HW. }
    assert (Hwrit : forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q)
      by (intros q _ Hq; exact (WM (Z_to_bv 64 q) Hq)).
    destruct (ACw.a_laws_fs_place _ _ _ _ _ ALAWS ([] ++ g_H g) mem md FS HAH Hwtp HFSr)
      as (_ & HFSstklo & _).
    assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
              ~ ACw.a_store_ok (g_H g) (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT API mem md) q ->
              ~ (FS <= q < FS + ACw.FS_SIZE) ->
              ~ (exists bb, FS <= bb < FS + ACw.FS_SIZE /\ q = shadow_addr bb) ->
              mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
    { intros q Hq Hns Hnfs Hnsh.
      destruct (r6_out_dec (r6_WW fr sp (rnb g b) FS) q) as [Ho|Hno].
      - apply MU. rewrite MState.unsigned_lit by lia. exact Ho.
      - exfalso. destruct (r6_not_out_in _ _ Hno) as (u & v & Hin & Hv).
        unfold r6_WW in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
        + destruct Hin as [E|[E|[]]]; injection E as <- <-.
          * apply Hns. right; left. unfold APPMEM_END in *. lia.
          * destruct Hloc as [[_ [Hspfr Hreal]] | [_ [_ [Hfs _]]]].
            -- apply Hns. right; left. pose proof (Hreal q ltac:(lia)) as Hreal2. unfold APPMEM_END in *. lia.
            -- apply Hnfs. destruct (Hfs q ltac:(lia)) as (FSb & HFSrb & Hwb & Hlo3 & Hhi3).
               assert (EFS : FSb = FS)
                 by (apply (r6_wm_uniq mem (ACw.as_tp ACw.ASYMS) FSb FS Hwb Hwtp); lia).
               subst FSb. unfold ACw.FS_SIZE, FS_SIZE in *. lia.
        + apply in_app_or in Hin. destruct Hin as [Hin|Hin].
          * destruct (r6_fpw_cover FS (u, v) Hin) as [(Hlo4 & Hhi4)|(lo5 & hi5 & Hl5 & Hh5 & El & Eh)];
              cbn [fst snd] in *.
            -- apply Hnfs. unfold ACw.FS_SIZE, FS_SIZE in *. lia.
            -- apply Hnsh. exists (8 * (q - ASAN_K)).
               assert (Hdv : 8 * (q - ASAN_K) / 8 = q - ASAN_K) by (rewrite Z.mul_comm, Z.div_mul; lia).
               subst u v. unfold ACw.FS_SIZE, FS_SIZE in *.
               split; [unfold shadow_addr in *; Z.div_mod_to_equations; lia
                      | unfold shadow_addr; rewrite Hdv; lia].
          * destruct Hin as [E|[]]. injection E as <- <-.
            apply Hns. right; right; right. exists (8 * (q - ASAN_K)).
            assert (Hdv : 8 * (q - ASAN_K) / 8 = q - ASAN_K) by (rewrite Z.mul_comm, Z.div_mul; lia).
            split; [unfold shadow_addr; rewrite Hdv; lia|].
            right; left. unfold shadow_addr, APPMEM_END in *. Z.div_mod_to_equations. lia. }
    destruct (ACw.a_laws_fs_store _ _ _ _ _ ALAWS (g_H g) mem mem' md FS HAH Hwtp HFSr Hagree Hwrit FSOK)
      as (HAH' & HOWN' & HSTKeq & HSTKhi).
    (* FRA at the new memory and model *)
    assert (Hshnew : exists sh', bytes_at rsegs mem' (Sfr fr) sh' /\ length sh' = Z.to_nat FRAME_SHADOW).
    { assert (Hst : stk rsegs mem' (Sfr fr) (Sfr fr + FRAME_SHADOW)).
      { split; [rewrite HSfr; unfold ASAN_K; lia|]. split; [rewrite HSfr in Hshx |- *; unfold ASAN_K in *; lia|].
        intros a Ha. apply SWm. unfold in_shadow.
        pose proof (Hshx a Ha) as Har.
        unfold LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
      destruct (stk_bytes rsegs mem' _ _ Hst ltac:(lia)) as (bs & Hl & Hb).
      exists bs. split; [exact Hb|]. rewrite Hl. lia. }
    (* the shadow byte of a registered global is outside the write set *)
    assert (HoutGL : forall a, 0x21140 <= a < 0x9f8e8 -> outside (r6_WW fr sp (rnb g b) FS) (shadow_addr a)).
    { intros a Ha.
      assert (Hsa : 2147450880 + 16936 <= shadow_addr a <= 2147450880 + 81693)
        by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
      assert (Hin_sh : in_shadow (shadow_addr a))
        by (apply shadow_of_app; unfold app_mem, LOWMEM_END; left; lia).
      assert (HnFS : forall lo hi, FS <= lo -> hi <= FS + FS_SIZE -> ~ (lo <= shadow_addr a < hi)).
      { intros lo hi H1 H2 HC.
        exact (app_not_shadow (shadow_addr a) (HFSapp (shadow_addr a) ltac:(lia)) Hin_sh). }
      assert (Hs2 : 2147450880 + 790016 <= shadow_addr (FS + 36864))
        by (unfold shadow_addr, ASAN_K, ACw.GT in *; Z.div_mod_to_equations; lia).
      assert (Hs3 : 2147450880 + 2199023255552 <= shadow_addr (sp - BA.REAC_CTRL_BUILD_AS_K))
        by (unfold shadow_addr, ASAN_K in *; Z.div_mod_to_equations; lia).
      apply r6_out_WW.
      - lia.
      - destruct HLH as [HL|HL]; lia.
      - apply r6_out_fpw.
        + exact (HnFS FS (FS + 16) ltac:(lia) ltac:(unfold FS_SIZE; lia)).
        + exact (HnFS (FS + 4096) (FS + 28672) ltac:(lia) ltac:(unfold FS_SIZE; lia)).
        + exact (HnFS (FS + 36864) (FS + 2134016) ltac:(lia) ltac:(unfold FS_SIZE; lia)).
        + lia.
      - lia. }
    assert (HAG' : forall a, in_globals AFw.frame_AG a -> addressable mem' a 1).
    { intros a Ha. pose proof (r6_ag_range a Ha) as Har.
      apply (r6_addr_keep (r6_WW fr sp (rnb g b) FS) mem mem' a 1 (HAG a Ha) MU).
      intros i Hi. replace (a + i) with a by lia. apply HoutGL. lia. }
    (* the slot window outside the frame stays addressable: inside the callee window by the callee's post,
       elsewhere because its shadow bytes are outside the write set *)
    assert (Hsp8 : (sp - BA.REAC_CTRL_BUILD_AS_K) mod 8 = 0 /\ sp mod 8 = 0)
      by (rewrite HKv; split; revert Hspm; clear; intros; Z.div_mod_to_equations; lia).
    assert (HWA' : forall a, g_S g - AFw.SLOT_STACK <= a < g_S g -> ~ (fr <= a < fr + FRAME_BYTES) ->
                     addressable mem' a 1).
    { intros a H1 H2.
      destruct (Z_le_gt_dec (sp - BA.REAC_CTRL_BUILD_AS_K) a) as [L1|L1];
        [destruct (Z_lt_ge_dec a sp) as [L2|L2]|].
      1: exact (r6_addr_byte mem' (sp - BA.REAC_CTRL_BUILD_AS_K) BA.REAC_CTRL_BUILD_AS_K a AWm ltac:(lia)).
      all: apply (r6_addr_keep (r6_WW fr sp (rnb g b) FS) mem mem' a 1 (HWA a H1 H2) MU);
           intros i Hi; replace (a + i) with a by lia.
      all: assert (Happa : app_mem a) by (unfold app_mem; right; lia);
           pose proof (shadow_of_app a Happa) as Hsa.
      all: apply r6_out_WW;
        [ intros HC; exact (app_not_shadow (shadow_addr a) (HAwin2 _ HC) Hsa)
        | intros HC; exact (app_not_shadow (shadow_addr a) (Happ' (shadow_addr a) ltac:(lia)) Hsa)
        | apply r6_out_fpw;
          [ intros HC; exact (app_not_shadow (shadow_addr a) (HFSapp (shadow_addr a) ltac:(lia)) Hsa)
          | intros HC; exact (app_not_shadow (shadow_addr a) (HFSapp (shadow_addr a) ltac:(lia)) Hsa)
          | intros HC; exact (app_not_shadow (shadow_addr a) (HFSapp (shadow_addr a) ltac:(lia)) Hsa)
          | unfold shadow_addr; intros HC;
            assert (M : (FS + 2134016) / 8 <= a / 8) by (apply Z.div_le_mono; lia); lia ]
        | apply (r6_sh_out _ _ a (proj1 Hsp8) (proj2 Hsp8)); lia ]. }
    (* the side-arm FakeStack record: its class-6 cells are apart from the class-0 / class-1 ranges *)
    assert (HREC' : FSREC fr mem -> FSREC fr mem').
    { intros Hrec0.
      apply (r6_fsrec mem mem' (r6_WW fr sp (rnb g b) FS) fr FS Hrec0 Hwtp HFSr MU).
      - intros x Hx. apply HoutLO. unfold ACw.GT. lia.
      - intros x Hx Hnfr Hn0 Hn1 Hn2.
        assert (Happx : app_mem x) by (apply HFSapp; lia).
        apply r6_out_WW.
        + lia.
        + lia.
        + apply r6_out_fpw; [exact Hn0 | exact Hn1 | exact Hn2 |].
          intros HC. apply (app_not_shadow x Happx).
          apply (r6_shadow_ivl (FS + 36864) (FS + 2134016) x);
            [intros a Ha; apply HFSapp; lia | lia | unfold shadow_addr in HC; lia].
        + intros HC. apply (app_not_shadow x Happx).
          apply (r6_shadow_ivl (sp - BA.REAC_CTRL_BUILD_AS_K) sp x);
            [exact HAwin2 | lia | unfold shadow_addr in HC; lia]. }
    (* ENT across the call (ent_munch): no address ENT keeps -- an entry block's byte, an image byte, a byte of
       [S, APPMEM_END) or the shadow byte of one of the last two -- is in the write set *)
    assert (HoutENT : forall x, ent_kept g x -> outside (r6_WW fr sp (rnb g b) FS) x).
    { intros x Hk. destruct Hk as [Hblkk | [Hik | [Habk | [(b0 & Hor & ->) | Hblks]]]].
      - (* an entry block byte: app memory below stklo, not a side-stack byte *)
        destruct Hblkk as (q & k & i & Hin & Hni & Hi & ->).
        destruct (ACw.a_laws_blocks _ _ _ _ _ ALAWS ([] ++ g_H g) mem md q k HAH
                    (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hend & _ & Hall).
        destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
        assert (HnFS : ~ (FS <= q + i < FS + ACw.FS_SIZE)).
        { intros HF. apply Hnfs. exists FS. split; [exact HFSr | split; [exact Hwtp | exact HF]]. }
        apply r6_out_WW.
        + lia.
        + intros Ho. destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
          * pose proof (Hreal (q + i) ltac:(lia)) as X. lia.
          * destruct (Hfs (q + i) ltac:(lia)) as (FSb & HFSrb & Hwb & Hlo3 & Hhi3).
            apply Hnfs. exists FSb. split; [exact HFSrb | split; [exact Hwb | lia]].
        + apply r6_out_fpw; [lia | lia | lia |].
          intros HC. apply (app_not_shadow (q + i) Happq).
          apply (r6_shadow_ivl (FS + 36864) (FS + 2134016) (q + i));
            [intros a Ha; apply HFSapp; lia | lia | unfold shadow_addr in HC; lia].
        + intros HC. apply (app_not_shadow (q + i) Happq).
          apply (r6_shadow_ivl (sp - BA.REAC_CTRL_BUILD_AS_K) sp (q + i));
            [exact HAwin2 | lia | unfold shadow_addr in HC; lia].
      - (* an image byte: below GT *)
        exact (HoutLO x (img_below_GT x Hik)).
      - (* a byte of [S, APPMEM_END): at or above sp, above the frame *)
        apply HoutHI; lia.
      - (* the shadow byte of an image byte or of a byte of [S, APPMEM_END): a shadow byte is no app byte, and
           the shadow bands of the class-0 / class-1 frames and of the callee window miss it (r6_band) *)
        assert (Hb0 : 0 <= b0 < 6283264 \/ g_S g <= b0 < APPMEM_END).
        { destruct Hor as [Hi|Hr]; [left; pose proof (img_below_GT b0 Hi) as X; unfold ACw.GT in X; lia
                                   | right; exact Hr]. }
        assert (Happb : app_mem b0) by (unfold app_mem; lia).
        pose proof (shadow_of_app b0 Happb) as Hsb.
        pose proof (r6_band FS (sp - BA.REAC_CTRL_BUILD_AS_K) sp (g_S g) b0 ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(lia) ltac:(lia) ltac:(lia)) as (Hbd1 & Hbd2).
        apply r6_out_WW.
        + intros HC. exact (app_not_shadow (shadow_addr b0) (HAwin2 _ HC) Hsb).
        + intros HC. exact (app_not_shadow (shadow_addr b0) (Happ' (shadow_addr b0) ltac:(lia)) Hsb).
        + apply r6_out_fpw; [| | | exact Hbd1];
            intros HC; exact (app_not_shadow (shadow_addr b0) (HFSapp (shadow_addr b0) ltac:(lia)) Hsb).
        + exact Hbd2.
      - (* frame batch 2 item 9: the shadow byte of an entry block byte (app memory below stklo, off the side
           stack): a shadow byte is no app byte, and the two shadow bands have 8-aligned ends (r6_sh_out) *)
        destruct Hblks as (q & k & i & Hin & _ & Hi & ->).
        destruct (ACw.a_laws_blocks _ _ _ _ _ ALAWS ([] ++ g_H g) mem md q k HAH
                    (in_or_app _ _ _ (or_intror Hin))) as (_ & _ & Hend & _ & Hall).
        destruct (Hall (q + i) ltac:(lia)) as (Happq & _ & _ & _ & Hnfs).
        assert (HnFS : ~ (FS <= q + i < FS + ACw.FS_SIZE)).
        { intros HF. apply Hnfs. exists FS. split; [exact HFSr | split; [exact Hwtp | exact HF]]. }
        pose proof (shadow_of_app (q + i) Happq) as Hsq.
        assert (HFS8 : (FS + 36864) mod 8 = 0 /\ (FS + 2134016) mod 8 = 0)
          by (revert HFSmod; clear; intros; split; Z.div_mod_to_equations; lia).
        apply r6_out_WW.
        + intros HC. exact (app_not_shadow (shadow_addr (q + i)) (HAwin2 _ HC) Hsq).
        + intros HC. exact (app_not_shadow (shadow_addr (q + i)) (Happ' (shadow_addr (q + i)) ltac:(lia)) Hsq).
        + apply r6_out_fpw;
            [ intros HC; exact (app_not_shadow (shadow_addr (q + i)) (HFSapp (shadow_addr (q + i)) ltac:(lia)) Hsq)
            | intros HC; exact (app_not_shadow (shadow_addr (q + i)) (HFSapp (shadow_addr (q + i)) ltac:(lia)) Hsq)
            | intros HC; exact (app_not_shadow (shadow_addr (q + i)) (HFSapp (shadow_addr (q + i)) ltac:(lia)) Hsq)
            | apply (r6_sh_out _ _ (q + i) (proj1 HFS8) (proj2 HFS8)); lia ].
        + apply (r6_sh_out _ _ (q + i) (proj1 Hsp8) (proj2 Hsp8)). lia. }
    assert (HFRA' : FRA B APIf ra g fr [] regs'' mem' md).
    { apply (r6_fra g fr [] regs regs'' mem mem' md (r6_WW fr sp (rnb g b) FS) HFRA MU WM ROm
               (r6_rt_dj fr sp (rnb g b) FS HGTFS HGT ltac:(lia)) HAH' HSTKeq
               (fun a Ha => proj2 (SWm a Ha)) Hshnew).
      - intros x Hx. apply HoutLO. unfold ACw.GT. lia.
      - intros x Hx. apply HoutFR; lia.
      - intros x Hx. rewrite HbvA in Hx. apply HoutHI; lia.
      - intros x Hx. rewrite HbvA in Hx. apply HoutHI; lia.
      - intros x Hx. apply HoutHI; lia.
      - intros x Hx. destruct (Z_le_gt_dec sp x) as [L|L].
        + destruct (Z_le_gt_dec (fr + 544) x) as [L1|L1];
            [destruct (Z_lt_ge_dec x (fr + 544 + rnb g b)) as [L2|L2]|].
          * right. destruct (PRES x ltac:(lia)) as (bx & Hb). exists bx. exact Hb.
          * left. apply HoutHI; [lia | unfold AFw.SLOT_STACK, APPMEM_END in *; lia | lia].
          * left. apply HoutHI; [lia | unfold AFw.SLOT_STACK, APPMEM_END in *; lia | lia].
        + destruct (Z_le_gt_dec (sp - BA.REAC_CTRL_BUILD_AS_K) x) as [L3|L3].
          * right. destruct STm as (_ & _ & Hs).
            destruct (Hs x ltac:(lia)) as (_ & bx & Hb). exists bx. exact Hb.
          * left. apply r6_out_WW.
            -- lia.
            -- destruct Hloc as [[_ [Hspfr _]] | [_ [_ [Hfs _]]]].
               ++ lia.
               ++ destruct (Hfs (fr + FRAME_BYTES - 1) ltac:(lia)) as (FSb & HFSrb & Hwb & Hlo3 & Hhi3).
                  assert (EFS : FSb = FS)
                    by (apply (r6_wm_uniq mem (ACw.as_tp ACw.ASYMS) FSb FS Hwb Hwtp); lia).
                  subst FSb. unfold ACw.FS_SIZE, FS_SIZE, AFw.SLOT_STACK in *. lia.
            -- apply r6_out_fpw;
                 [unfold FS_SIZE in *; lia | unfold FS_SIZE in *; lia | unfold FS_SIZE in *; lia |].
               intros HC. assert (HI : in_shadow x).
               { apply (r6_shadow_ivl (FS + 36864) (FS + 2134016) x);
                   [intros a Ha; apply HFSapp; unfold FS_SIZE; lia | lia | unfold shadow_addr in HC; lia]. }
               unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in HI.
               unfold AFw.SLOT_STACK in *. lia.
            -- intros HC. assert (HI : in_shadow x).
               { apply (r6_shadow_ivl (sp - BA.REAC_CTRL_BUILD_AS_K) sp x);
                   [exact HAwin2 | lia | unfold shadow_addr in HC; lia]. }
               unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in HI.
               unfold AFw.SLOT_STACK in *. lia.
      - exact HAG'.
      - exact HWA'.
      - exact HREC'.
      - exact K2.
      - exact K3.
      - exact K4.
      - exact K8.
      - exact K9.
      - exact K19.
      - exact K26. }
    assert (HFRA2 : FRA B APIf ra g fr [] regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr [] regs'' regs'' mem' md md' HFRA'); try reflexivity. exact Hmat. }
    (* ENT at the new memory (ent_munch, the model unchanged), then across the model step (ent_mat) *)
    assert (HENT2 : ENT APIf g [] mem' md').
    { apply (ent_mat APIf g [] mem' md md'); [|exact Hmat].
      apply (ent_munch APIf g [] mem mem' md (r6_WW fr sp (rnb g b) FS) HENT HAH MU HoutENT HSTKeq HSTKhi).
      intros a _ Hown. exact (proj2 (HOWN' a) Hown). }
    (* the facts the entry carries and the exit names: spills at A + off (at or above sp, above the frame),
       frame cells past out[] and addressable frame ranges (their shadow is S(fr) .. S(fr) + 391) *)
    assert (SPL : forall off v, 0 <= off <= 416 -> q64 mem (A + off) v -> spill regs'' mem' off v).
    { intros off v Hoff Hq. exists A. split; [unfold rg in *; rewrite K9; exact Hr9|].
      unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
      rewrite length_le8. intros x Hx. apply HoutHI; lia. }
    assert (RWK : forall k n bs, 2036 <= k -> k + Z.of_nat n <= FRAME_BYTES ->
              rw_cells rsegs mem (fr + k) [CB n bs] -> rw_cells rsegs mem' (fr + k) [CB n bs]).
    { intros k n bs Hk Hn Hc. apply (r6_rw_keep _ mem mem' (fr + k) n bs Hc MU WM).
      intros x Hx. apply HoutFR; lia. }
    assert (ADK : forall k n, 0 <= k -> k + n <= FRAME_BYTES -> addressable mem (fr + k) n -> addressable mem' (fr + k) n).
    { intros k n Hk Hn Ha. apply (r6_addr_keep _ mem mem' (fr + k) n Ha MU).
      intros i Hi. replace (fr + k + i) with (fr + (k + i)) by lia.
      apply HoutSH. apply r6_sh_in; [exact Hfr8 | lia]. }
    (* PRO across the call (RcPro.rc_pro_keep): every byte of the write set is at or above stklo (the callee
       window; out[] on the real arm), on the side stack (out[] on the side arm; the class-0 / class-1 bytes), or
       the shadow of such a byte (the class-0 / class-1 frames' shadow; the window's shadow, 8-aligned) *)
    assert (HAWAY : forall x, ~ outside (r6_WW fr sp (rnb g b) FS) x -> rc_away APIf mem md x).
    { intros x Hno. unfold rc_away. destruct (r6_not_out_in _ _ Hno) as (u & v & Hin & Hv).
      unfold r6_WW in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
      - destruct Hin as [E|[E|[]]]; injection E as <- <-.
        + left. lia.
        + destruct Hloc as [[_ [_ Hreal]] | [_ [_ [Hfs _]]]].
          * left. pose proof (Hreal x ltac:(lia)). lia.
          * right; left. exact (Hfs x ltac:(lia)).
      - apply in_app_or in Hin. destruct Hin as [Hin|Hin].
        + destruct (r6_fpw_cover FS (u, v) Hin) as [(Hlo4 & Hhi4)|(lo5 & hi5 & Hl5 & Hh5 & El & Eh)];
            cbn [fst snd] in *.
          * right; left. exists FS. split; [exact HFSr|]. split; [exact Hwtp | unfold ACw.FS_SIZE; lia].
          * right; right. exists (8 * (x - ASAN_K)). subst u v.
            destruct (r6_sh_inv lo5 hi5 x Hv) as (Hy & _ & Esh).
            split; [apply HFSapp; lia|]. split; [symmetry; exact Esh|].
            right. exists FS. split; [exact HFSr|]. split; [exact Hwtp | lia].
        + destruct Hin as [E|[]]. injection E as <- <-.
          right; right. exists (8 * (x - ASAN_K)).
          destruct (r6_sh_inv _ _ x Hv) as (Hy & Hy8 & Esh).
          pose proof (Hy8 (proj1 Hsp8)) as Hy8'.
          split; [unfold app_mem; right; lia|]. split; [symmetry; exact Esh|].
          left. split; [lia | rewrite Z.mul_comm; apply Z.mod_mul; lia]. }
    assert (HPRO' : PRO g fr regs'' mem').
    { apply (rc_pro_keep B APIf ra g fr [] regs regs'' mem mem' md (r6_WW fr sp (rnb g b) FS) A HFRA HPRO MU
               Hr9 HAr0 ltac:(lia) K9).
      - intros x Hx. apply HoutHI; lia.
      - intros i Hi. replace (fr + 2624 + i) with (fr + (2624 + i)) by lia.
        apply HoutSH. apply r6_sh_in; [exact Hfr8 | lia].
      - exact HAWAY. }
    (* the exit cut *)
    rewrite <- SEGS. apply Hexit.
    exists regs'', mem', md', fr, A.
    split; [reflexivity|].
    split; [exact HFRA2|].
    split; [exact HENT2|].
    split; [exact Hgn|].
    split; [exact Hb6|].
    split; [unfold ACw.ANMAX; lia|].
    split; [unfold ACw.a_size; lia|].
    split; [exact HA64|].
    split; [unfold rg; rewrite K9; exact Hr9|].
    split; [unfold rg; rewrite K24; exact H24|].
    split; [unfold a0v, rg; exact K10|].
    split.
    { unfold q64 in *. eapply fl_bytes; [exact Q64 | exact MU |].
      rewrite length_le8. intros x Hx. apply HoutHI; lia. }
    split; [exact (SPL 128 (fr + 544) ltac:(lia) Q128)|].
    split.
    { unfold IDBr in *. eapply fl_bytes; [exact HID | exact MU |].
      rewrite (r6_RID_len (g_in g) b). intros x Hx. apply HoutFR; lia. }
    split.
    { unfold FGBr in *. eapply fl_bytes; [exact HFG | exact MU |].
      rewrite (r6_RFG_len (g_in g) b). intros x Hx. apply HoutFR; lia. }
    split; [intros Hnz; exact (OUTF (r6_E_nz (g_in g) (Z.of_nat b) Hnz))|].
    split; [unfold rg; rewrite K23; exact Hr23|].
    split.
    { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |].
      rewrite OUR_length. intros x Hx. apply HoutFR; lia. }
    split; [unfold OUTA; exact (ADK 544 1492 ltac:(lia) ltac:(lia) HOUTA)|].
    split.
    { destruct HCUR as (Hc0 & Hc22 & Hc25). unfold CUR, rg in *.
      split; [exact Hc0|]. split; [rewrite K22; exact Hc22 | rewrite K25; exact Hc25]. }
    split; [exact (SPL 112 (mrow (g_in g)) ltac:(lia) Q112)|].
    split; [exact HPRO'|].
    split; [exact (SPL 104 0x21140 ltac:(lia) Q104)|].
    split; [exact (SPL 96 0x1234 ltac:(lia) Q96)|].
    split; [exact (SPL 144 (fr + 2688) ltac:(lia) Q144)|].
    split; [exact (SPL 192 (fr + 2768) ltac:(lia) Q208)|].
    split; [exists idb0; exact (RWK 2688 38%nat idb0 ltac:(lia) ltac:(lia) HIDB0)|].
    split; [exists fjunk0; exact (RWK 2768 72%nat fjunk0 ltac:(lia) ltac:(lia) HFGB0)|].
    split; [exact (SPL 280 (fr + 3040) ltac:(lia) Q280)|].
    split; [exact (SPL 240 (fr + 3056) ltac:(lia) Q240)|].
    split; [exists jy0; exact (RWK 3040 1%nat jy0 ltac:(lia) ltac:(lia) HJY0)|].
    split; [exists junk32; exact (RWK 3056 32%nat junk32 ltac:(lia) ltac:(lia) HJ320)|].
    split; [exact (SPL 152 (Sfr fr + 68) ltac:(lia) Q152)|].
    split; [unfold rg in *; rewrite K21; exact H21|].
    split; [exact (ADK 2176 38 ltac:(lia) ltac:(lia) HAWid)|].
    (* RXS: nine spills at A + 0 .. A + 224 and the fragment record's 72 bytes addressable *)
    destruct HRXS as (X48 & X56 & X88 & X80 & X72 & X16 & X8 & X192 & X216 & XA).
    split; [exact (SPL 48 _ ltac:(lia) (r6_spill_at regs mem A 48 _ Hr9 HAr0 HAr1 ltac:(lia) X48))|].
    split; [exact (SPL 56 _ ltac:(lia) (r6_spill_at regs mem A 56 _ Hr9 HAr0 HAr1 ltac:(lia) X56))|].
    split; [exact (SPL 88 _ ltac:(lia) (r6_spill_at regs mem A 88 _ Hr9 HAr0 HAr1 ltac:(lia) X88))|].
    split; [exact (SPL 80 _ ltac:(lia) (r6_spill_at regs mem A 80 _ Hr9 HAr0 HAr1 ltac:(lia) X80))|].
    split; [exact (SPL 72 _ ltac:(lia) (r6_spill_at regs mem A 72 _ Hr9 HAr0 HAr1 ltac:(lia) X72))|].
    split; [exact (SPL 8 _ ltac:(lia) (r6_spill_at regs mem A 8 _ Hr9 HAr0 HAr1 ltac:(lia) X16))|].
    split; [exact (SPL 0 _ ltac:(lia) (r6_spill_at regs mem A 0 _ Hr9 HAr0 HAr1 ltac:(lia) X8))|].
    split; [exact (SPL 200 _ ltac:(lia) (r6_spill_at regs mem A 200 _ Hr9 HAr0 HAr1 ltac:(lia) X192))|].
    split; [exact (SPL 216 _ ltac:(lia) (r6_spill_at regs mem A 216 _ Hr9 HAr0 HAr1 ltac:(lia) X216))|].
    exact (ADK 2256 72 ltac:(lia) ltac:(lia) XA).
Qed.

End R6.
