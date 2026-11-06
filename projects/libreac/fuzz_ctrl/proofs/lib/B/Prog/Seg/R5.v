(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 2488 of its 3291 lines of code are new or changed and 2298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_catalogue_match.v, with its module paths and module names changed; 2419 of its 2557 lines of code are new or changed and 3153 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/Tac_slot.v; 615 of its 747 lines of code are new or changed and 2425 lines of the source are left out. *)
(* Demonstrator segment for fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B, libreac v1.9.0): a register-only
   block of the R5 segment (plan-asan-ubsan.md 3.3, R5 = Inv_B8169c "b=0 constants"). The block 0x816bc..0x816d4
   computes the round_trip.box address (BOXA = 0x21140) with auipc / lui / li / addi -- seven register-only
   instructions, no memory write, no branch, no call (v1.9.0: 0x816c8 `li s5,36`, 0x816cc `li s11,32`, 0x816d0
   `li s8,-8`; the patched block set s2 = 32 and s11 = -8). None of the touched registers (a0/a1/a2/s5/s11/s8) is
   an FRA register (sp 2, gp 3, tp 4, s0 8, s1 9, s3 19, s10 26), so FRA is preserved across the run
   (sl_fra_move). This is the image-B twin of the lib/A Tac_slot seg_A5 pattern, stated in the Section form of the
   asan seg brief. *)
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
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.

Section Demo.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* Two FRA cut points inside the R5 segment: the entry of the round_trip.box address computation (0x816bc) and its
   exit, the store sd a0,256(s1) (0x816d8). FRA alone (no extra register/memory content). The names keep the
   patched pcs (0x81658 / 0x81674) until the cut-rename step. *)
(* v1.9 pc 0x816bc *)
Definition Inv_B816bc (g : ghost) (c : config) : Prop := CUTST B APIf ra g 0x816bc [] (fun _ _ _ => True) c.
(* v1.9 pc 0x816d8 *)
Definition Inv_B816d8 (g : ghost) (c : config) : Prop := CUTST B APIf ra g 0x816d8 [] (fun _ _ _ => True) c.

Lemma seg_R5_box : Hcut B APIf ra Inv_B816d8 -> Hcut B APIf ra Inv_B816bc.
Proof.
  intros Hbc g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & _). subst c.
  rewrite SEGS.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hrest).
  apply (sl_run regs (Z_to_bv 64 0x816bc) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x816d8 /\ mem' = mem /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = getr regs 26)
    (Post B APIf ra g)).
  - exact Hhalt.
  - do 7 step. finish.
    all: simp_regs; try reflexivity;
      try (apply kb_getr_eqv; apply Regs6ss.mkR_of_eqv).
  - intros R pc' mem' regs'' md' (Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR26) Hreg Hmat.
    subst pc' mem'.
    rewrite <- SEGS.
    apply Hbc.
    exists regs'', mem, md', fr.
    split; [reflexivity|].
    split.
    { apply (sl_fra_move B APIf ra g fr [] regs regs'' mem md md' HFRA);
        [ rewrite Hreg; exact HR2 | rewrite Hreg; exact HR3 | rewrite Hreg; exact HR4
        | rewrite Hreg; exact HR8 | rewrite Hreg; exact HR9 | rewrite Hreg; exact HR19
        | rewrite Hreg; exact HR26 | exact Hmat ]. }
    (* the memory is unchanged, so ENT moves with the model step alone (push 5c, ent_mat) *)
    split; [| exact I].
    eapply ent_mat; [exact HENT | exact Hmat].
Qed.

End Demo.

(* ==== The full R5 segment (libreac v1.9.0): [0x8169c, 0x816e8], 20 instructions, no call, no instrumented check,
   no trap; cut Inv_B8169c (v1.9 pc 0x8169c) -> cut Inv_B816ec_at g 0 (v1.9 pc 0x816ec).  Re-fit of the v1.8 proof
   (a working branch c439fa41c5b) onto the v1.9.0 bytes and a Theorem Labs lane's v1.9 cut bundle; the cut names are still the
   v1.8 names.  rule 24: no function proved (a slot segment).
   0x8169c li s6,0 (b = 0); the spills 0x816a4 sd a0,32(s1) (a0 = s2 & 7), 0x816ac sd a0,24(s1) (a0 = s2 + 16),
   0x816b0 sd s2,272(s1) (the catalogue box), 0x816b8 sd s2,16(s1) (s2 + 20); the constants 0x816c8 li s5,36,
   0x816cc li s11,32, 0x816d0 li s8,-8; 0x816d8 sd a0,256(s1) (a0 = round_trip.box 0x21140 by auipc / addi),
   0x816e0 sd a0,248(s1) (a0 = 0x1234 by lui / addiw), 0x816e8 sd a2,128(s1) (a2 = 0xe38f0000 by lui / slli).
   v1.9.0 against the patched image: the spills move [A+48] -> [A+32], [A+40] -> [A+24], [A+288] -> [A+272],
   [A+32] -> [A+16], [A+272] -> [A+256], [A+256] -> [A+248]; the constant 32 is set in s11 (0x816cc li s11,32,
   register 27), not s2, and s8 is set to -8 (0x816d0 li s8,-8, new; the patched image set s11).  CUR is s7 / s9
   (registers 23 / 25), which the run does not write.
   The run writes exactly the 56 spill bytes W = [A + 16, A + 40) u [A + 128, A + 136) u [A + 248, A + 256) u
   [A + 256, A + 264) u [A + 272, A + 280) (A = s1), all inside the S-anchored window, above the frame and below the
   fr spill [A + 336, A + 344), and apart from the fr reload / selector spills [A + 40, A + 56).

   The exit is the R6 head Inv_B816ec_at g 0 (RS, RBE, s5 = 36, R6X, the row-name clause, s11 = 32).  The run
   creates the spills [A + 128], [A + 256], [A + 248], [A + 272] = s2 = mrow, [A + 32] = mrow & 7 = 0 (mrow = CAT +
   296 * k is a multiple of 8), [A + 24] = mrow + 16, [A + 16] = mrow + 20, s5 = 36, s6 = 0 and (adopt 10 of a working branch)
   s11 = 32; FRA gives the image bytes of RBE / R6X (the CTRL_FRAMES rows at BA_FR + 72 and the catalogue row at
   mrow are RELRO bytes, G_img_c; round_trip.box at BOXA is in the read-only LOAD segment, ro_agree); the official
   entry Inv_B8169c gives the rest of RBE, which the run only carries: the spills [A + 312], [A + 264], [A + 56],
   [A + 184], [A + 144], [A + 8], [A + 96], [A + 120], [A + 240], [A + 232], [A + 224], [A + 176], [A + 208],
   [A + 64], A4's frame-loop pointer spills (PRA), [A + 152], [A + 112] and [A + 160] (outside W), out[] / our[] /
   the identity record / the fragment record addressable (W is app memory, sl_addr_keep) and the row-name clause
   (image bytes below GT, outside W); R6X g 0 is r6x_of_rbe.  FRA's input facts are kept by fra_in_keep (the input
   block is below stklo <= S - SLOT_STACK < A + 16).  No side-stack package: the R6 call site rebuilds build_as's
   from FRA (fra_fp). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Image.
Module LImg := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Image.

(* The spill bytes the run writes. *)
Definition r5_W (A : Z) : list (Z * Z) :=
  [(A + 16, A + 40); (A + 128, A + 136); (A + 248, A + 256); (A + 256, A + 264); (A + 272, A + 280)].

Lemma r5_out : forall A x,
  x < A + 16 \/ (A + 40 <= x < A + 128) \/ (A + 136 <= x < A + 248) \/ (A + 264 <= x < A + 272) \/
  A + 280 <= x ->
  Frame.outside (r5_W A) x.
Proof. intros A x H. unfold r5_W. cbn [Frame.outside]. repeat (split; [lia|]). exact I. Qed.

Lemma r5_not_out : forall A x, ~ Frame.outside (r5_W A) x ->
  (A + 16 <= x < A + 40) \/ (A + 128 <= x < A + 136) \/ (A + 248 <= x < A + 256) \/
  (A + 256 <= x < A + 264) \/ (A + 272 <= x < A + 280).
Proof. intros A x H. unfold r5_W in H. cbn [Frame.outside] in H. lia. Qed.

(* The register file of the slot cuts, in the engine's concrete form. *)
Lemma r5_mkR_of : forall regs,
  Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* One cell of a block of cells, read as a byte block at its own offset. *)
Lemma r5_cell_bytes : forall m A cs k c bs,
  rw_cells rsegs m A cs -> cell_at cs k = Some c -> cbytes c = bs ->
  bytes_at rsegs m (A + Z.of_nat k) bs.
Proof.
  intros m A cs k c bs [[Hwf Hb] _] Hat <-.
  destruct (cell_at_split cs k c c Hat) as (pre & post & -> & Hsz & _).
  apply cells_wf_app in Hwf. destruct Hwf as [Hwfp Hwfc]. cbn in Hwfc. destruct Hwfc as [Hwfc Hwfs].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb].
  rewrite (cells_bytes_length pre Hwfp), Hsz in Hb.
  cbn [cells_bytes] in Hb. apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

(* The first cell of a block, an 8-byte word, read as the word's bytes. *)
Lemma r5_cell0 : forall m A cs v w,
  rw_cells rsegs m A cs -> cell_at cs 0 = Some (C8 v) -> v = w -> bytes_at rsegs m A (le8 w).
Proof.
  intros m A cs v w H Hc <-.
  pose proof (r5_cell_bytes m A cs 0 (C8 v) (le8 v) H Hc eq_refl) as Hb.
  change (Z.of_nat 0) with 0 in Hb. rewrite Z.add_0_r in Hb. exact Hb.
Qed.

(* Every byte of a byte block is present. *)
Lemma r5_pres : forall m a bs x,
  bytes_at rsegs m a bs -> a <= x < a + Z.of_nat (length bs) ->
  exists b, mbyte rsegs m x = Some b.
Proof.
  intros m a bs x Hb Hx. destruct Hb as (H0 & H1 & H).
  assert (Hi : (Z.to_nat (x - a) < length bs)%nat) by lia.
  pose proof (H (Z.to_nat (x - a)) Hi) as E.
  rewrite Z2Nat.id in E by lia. replace (a + (x - a)) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:Eb.
  - exists b. unfold mbyte. unfold mrd, wa in E. exact E.
  - apply nth_error_None in Eb. lia.
Qed.

(* A read through a cell the run did not change. *)
Lemma r5_mrd_eq : forall m m' (a : word) b, m' a = m a -> mrd rsegs m a = Some b -> mrd rsegs m' a = Some b.
Proof. intros m m' a b E H. unfold mrd in *. rewrite E. exact H. Qed.

(* Every byte of the image lies below 6283264 (GT, the end of its writable data rounded up to a page). *)
Lemma r5_img_low : forall s, In s rsegs -> Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 6283264.
Proof.
  intros s Hin.
  assert (Hb : forallb (fun s => Z.leb (Z.of_N (seg_base s) + Z.of_N (seg_size s)) 6283264) rsegs = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb. apply Z.leb_le. exact (Hb s Hin).
Qed.

(* A read-only address of the image is one of those bytes. *)
Lemma r5_ro_low : forall a, ro_addr rsegs a = true -> bv_unsigned a < 6283264.
Proof.
  intros a Ha. unfold ro_addr in Ha.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:Es; [|discriminate].
  destruct (KindBGlue.kb_find_segment rsegs (bv_unsigned a) 1 s Es) as (Hin & H1 & H2).
  pose proof (r5_img_low s Hin). lia.
Qed.

(* A slice [a, a + n) of the S-anchored window is one writable block of n bytes. *)
Lemma r5_carve : forall m lo hi a (n : nat),
  Frame.stk rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists junk, rw_cells rsegs m a [CB n junk].
Proof.
  intros m lo hi a n H H1 H2.
  destruct (Frame.stk_split rsegs m lo a hi H ltac:(lia)) as (_ & S1).
  destruct (Frame.stk_split rsegs m a (a + Z.of_nat n) hi S1 ltac:(lia)) as (S2 & _).
  destruct (Frame.stk_carve rsegs m a (a + Z.of_nat n) n S2 ltac:(lia)) as (_ & junk & HJ).
  replace (a + Z.of_nat n - Z.of_nat n) with a in HJ by lia.
  exists junk. exact HJ.
Qed.

(* A spill conjunct names the spill base A of register 9 (its word lies in [A, A + 448)). *)
Lemma r5_spill_A : forall (regs : bvmap 5 word) m off v A A1,
  rg regs 9 A1 -> q64 m (A1 + off) v -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 ->
  A1 = A.
Proof.
  intros regs m off v A A1 H1 Hq H2 HA0 HAe Hoff.
  unfold q64 in Hq. apply bytes_at_bound in Hq. rewrite length_le8 in Hq. change (Z.of_nat 8) with 8 in Hq.
  pose proof (rg_eq64 regs 9 A1 A H1 H2) as Hm. change (2 ^ 64) with 18446744073709551616 in *.
  Z.div_mod_to_equations. lia.
Qed.

(* PRA (adopt 9 of a working branch: A4's frame-loop pointer spills; v1.9: eleven conjuncts, [A+168] = fr + 2880 twice) is
   carried by any map that carries each of its spills. *)
Lemma r5_pra : forall fr (regs regs' : bvmap 5 word) m m',
  (forall off v, In off [136; 280; 168; 192; 200; 216; 104; 288; 296; 304] ->
     spill regs m off v -> spill regs' m' off v) ->
  PRA fr regs m -> PRA fr regs' m'.
Proof.
  intros fr regs regs' m m' K (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11). unfold PRA.
  split; [apply K; [cbn [In]; lia | exact H1]|]. split; [apply K; [cbn [In]; lia | exact H2]|].
  split; [apply K; [cbn [In]; lia | exact H3]|]. split; [apply K; [cbn [In]; lia | exact H4]|].
  split; [apply K; [cbn [In]; lia | exact H5]|]. split; [apply K; [cbn [In]; lia | exact H6]|].
  split; [apply K; [cbn [In]; lia | exact H7]|]. split; [apply K; [cbn [In]; lia | exact H8]|].
  split; [apply K; [cbn [In]; lia | exact H9]|]. split; [apply K; [cbn [In]; lia | exact H10]|].
  apply K; [cbn [In]; lia | exact H11].
Qed.

(* mrow & 7 = 0 for a multiple of 8. *)
Lemma r5_land7 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

(* A spill word of the run, read off the first spill block C (from s1 + 16) at byte offset k. *)
Local Ltac r5_val :=
  cbn [cbytes];
  first [ reflexivity
        | f_equal; first [ reflexivity
                         | apply bv_eq; rewrite ?Z_to_bv_unsigned; unfold bv_wrap; cbn; lia ] ].

(* The run of the segment. s1 (reg 9) = A; the five spill blocks are the whole write set. *)
Lemma r5_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (j1 j2 j3 j4 j5 : list byte),
    bv_unsigned s2 mod 8 = 0 ->
    rw_cells rsegs m (bv_unsigned s1 + 16) [CB 24 j1] ->
    rw_cells rsegs m (bv_unsigned s1 + 128) [CB 8 j2] ->
    rw_cells rsegs m (bv_unsigned s1 + 248) [CB 8 j3] ->
    rw_cells rsegs m (bv_unsigned s1 + 256) [CB 8 j4] ->
    rw_cells rsegs m (bv_unsigned s1 + 272) [CB 8 j5] ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' s2' s5' s6' s8' s11' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2' s3 s4 s5' s6' s7 s8' s9 s10 s11'
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x816ec) fc None m' (seg_rom rsegs) /\
         s5' = Z_to_bv 64 36 /\ s6' = Z_to_bv 64 0 /\ s11' = Z_to_bv 64 32 /\
         munch (r5_W (bv_unsigned s1)) m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (bv_unsigned s1 + 16) (le8 (Z_to_bv 64 (bv_unsigned s2 + 20))) /\
         bytes_at rsegs m' (bv_unsigned s1 + 24) (le8 (Z_to_bv 64 (bv_unsigned s2 + 16))) /\
         bytes_at rsegs m' (bv_unsigned s1 + 32) (le8 (Z_to_bv 64 0)) /\
         bytes_at rsegs m' (bv_unsigned s1 + 128) (le8 (Z_to_bv 64 0xe38f0000)) /\
         bytes_at rsegs m' (bv_unsigned s1 + 248) (le8 (Z_to_bv 64 0x1234)) /\
         bytes_at rsegs m' (bv_unsigned s1 + 256) (le8 (Z_to_bv 64 0x21140)) /\
         bytes_at rsegs m' (bv_unsigned s1 + 272) (le8 (Z_to_bv 64 (bv_unsigned s2))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x8169c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m j1 j2 j3 j4 j5 H8 C1 C2 C3 C4 C5.
  assert (Hl7 : forall X, X = 7 -> Z.land (bv_unsigned s2) X = 0) by (intros X ->; exact (r5_land7 _ H8)).
  pose proof (munch_refl [(bv_unsigned s1 + 16, bv_unsigned s1 + 40); (bv_unsigned s1 + 128, bv_unsigned s1 + 136);
                          (bv_unsigned s1 + 248, bv_unsigned s1 + 256); (bv_unsigned s1 + 256, bv_unsigned s1 + 264);
                          (bv_unsigned s1 + 272, bv_unsigned s1 + 280)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 s1) as R1. change (bv_modulus 64) with (2^64) in R1.
  pose proof (rw_cells_bound _ _ _ _ C1) as HB1. cbn [cells_size csize Nat.add] in HB1.
  pose proof (rw_cells_bound _ _ _ _ C2) as HB2. cbn [cells_size csize Nat.add] in HB2.
  pose proof (rw_cells_bound _ _ _ _ C3) as HB3. cbn [cells_size csize Nat.add] in HB3.
  pose proof (rw_cells_bound _ _ _ _ C4) as HB4. cbn [cells_size csize Nat.add] in HB4.
  pose proof (rw_cells_bound _ _ _ _ C5) as HB5. cbn [cells_size csize Nat.add] in HB5.
  do 20 step.
  apply evt_done. cbn beta.
  eexists _, _, _, _, _, _, _, _, _.
  split; [reflexivity|].
  split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
  split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
  split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity]|].
  split; [exact MU|]. split; [exact WM|].
  split.
  { replace (bv_unsigned s1 + 16) with (bv_unsigned s1 + 16 + Z.of_nat 0) by (change (Z.of_nat 0) with 0%Z; lia).
    apply (r5_cell_bytes _ _ _ 0 _ _ C1 ltac:(cells_cbv; reflexivity)). r5_val. }
  split.
  { replace (bv_unsigned s1 + 24) with (bv_unsigned s1 + 16 + Z.of_nat 8) by (change (Z.of_nat 8) with 8%Z; lia).
    apply (r5_cell_bytes _ _ _ 8 _ _ C1 ltac:(cells_cbv; reflexivity)). r5_val. }
  split.
  { replace (bv_unsigned s1 + 32) with (bv_unsigned s1 + 16 + Z.of_nat 16) by (change (Z.of_nat 16) with 16%Z; lia).
    apply (r5_cell_bytes _ _ _ 16 _ _ C1 ltac:(cells_cbv; reflexivity)).
    cbn [cbytes]. f_equal. f_equal. apply Hl7. vm_compute. reflexivity. }
  split; [eapply r5_cell0; [exact C2 | cells_cbv; reflexivity |
            first [reflexivity | apply bv_eq; vm_compute; reflexivity]]|].
  split; [eapply r5_cell0; [exact C3 | cells_cbv; reflexivity |
            first [reflexivity | apply bv_eq; vm_compute; reflexivity]]|].
  split; [eapply r5_cell0; [exact C4 | cells_cbv; reflexivity |
            first [reflexivity | apply bv_eq; vm_compute; reflexivity]]|].
  eapply r5_cell0; [exact C5 | cells_cbv; reflexivity |].
  first [reflexivity | symmetry; apply MState.Z_to_bv_bv_unsigned].
Qed.

(* ---- image bytes: the bytes image_bytes reads are the segments' bytes ---- *)
Lemma r5_image_nth : forall n A bs, LImg.image_bytes rsegs A n = Some bs ->
  forall i, (i < n)%nat -> seg_rom rsegs (wa (A + Z.of_nat i)) = nth_error bs i.
Proof.
  induction n as [|n IH]; intros A bs H i Hi; [lia|].
  assert (Hs : LImg.image_bytes rsegs A (S n) =
               match seg_rom rsegs (wa A), LImg.image_bytes rsegs (A + 1) n with
               | Some b, Some bs => Some (b :: bs)
               | _, _ => None
               end) by reflexivity.
  rewrite Hs in H. clear Hs.
  destruct (seg_rom rsegs (wa A)) as [b|] eqn:Eb;
    destruct (LImg.image_bytes rsegs (A + 1) n) as [bs'|] eqn:E;
    cbv beta iota in H; try discriminate H.
  injection H as <-. destruct i as [|i].
  - cbn [nth_error]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact Eb.
  - cbn [nth_error]. replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia.
    apply IH; [exact E | lia].
Qed.

(* Read-only image bytes are in every memory that agrees with the read-only segments. *)
Lemma r5_ro_bytes : forall mem A n bs,
  ro_agree rsegs mem ->
  (forall i, (i < n)%nat -> ro_addr rsegs (wa (A + Z.of_nat i)) = true) ->
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  LImg.image_bytes rsegs A n = Some bs -> bytes_at rsegs mem A bs.
Proof.
  intros mem A n bs HRO Hro HA0 HAn Him.
  pose proof (LImg.image_bytes_length rsegs n A bs Him) as Hlen.
  split; [exact HA0|]. split; [rewrite Hlen; exact HAn|].
  intros i Hi. rewrite Hlen in Hi.
  transitivity (seg_rom rsegs (wa (A + Z.of_nat i))).
  - exact (HRO _ (Hro i Hi)).
  - exact (r5_image_nth n A bs Him i Hi).
Qed.

Lemma r5_img_eq : forall A n Y,
  match LImg.image_bytes rsegs A n with
  | Some bs => if list_eq_dec (@bv_eq_dec 8) bs Y then true else false
  | None => false
  end = true -> LImg.image_bytes rsegs A n = Some Y.
Proof.
  intros A n Y H. destruct (LImg.image_bytes rsegs A n) as [bs|]; [|discriminate].
  destruct (list_eq_dec (@bv_eq_dec 8) bs Y) as [->|]; [reflexivity | discriminate].
Qed.

(* The CTRL_FRAMES rows 3 .. 9 (RELRO) and round_trip.box (read-only data) of the image. *)
Lemma r5_tbl_img : LImg.image_bytes rsegs (BAC.BA_FR + 72) 168 = Some BAP.ba_tbl.
Proof. apply r5_img_eq. vm_compute. reflexivity. Qed.

Lemma r5_box_img : LImg.image_bytes rsegs BOXA 6 = Some box6.
Proof. apply r5_img_eq. vm_compute. reflexivity. Qed.

(* Every catalogue row (11 rows of 296 bytes from CAT, in RELRO) is image data, by computation; the exit's
   catalogue row rt_mb = rowb (istar in) is then the image's bytes at mrow. *)
Lemma r5_rows_img : forallb (fun i => match LImg.image_bytes rsegs (CAT + CAT_ROW * i) 296 with
                                      | Some _ => true | None => false end)
                      [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma r5_box_ro : forall i, (i < 6)%nat -> ro_addr rsegs (wa (BOXA + Z.of_nat i)) = true.
Proof. intros i Hi. do 6 (destruct i as [|i]; [vm_compute; reflexivity|]). lia. Qed.

Section Seg.
Context {fx : YK11.FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The inner lists of the allocator laws this file reads, taken apart once each, by statement where the law allows
   (a Theorem Labs lane 15:32Z: append-only at every level; a new generation touches these lemmas, not every site). *)
Lemma r5_fsp : forall H mem md FS,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  word_mem rsegs mem (AC.as_tp AC.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  AC.GT <= FS /\ FS + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, FS <= a < FS + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md FS HAH Hw HFS.
  pose proof (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw HFS)
    as P.
  decompose [and] P. split; [assumption | split; assumption].
Qed.

Lemma r5_store : forall H mem mem' md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH Hmc Hwrit.
  pose proof (AC.a_laws_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md HAH Hmc Hwrit)
    as P.
  decompose [and] P. split; [assumption | split; [assumption | split; assumption]].
Qed.

(* RELRO image bytes are in every memory FRA's image agreement (G_img_c) holds for. *)
Lemma r5_img_bytes : forall mem A n bs,
  G_img_c B AF.frame_RELRO mem ->
  (forall i, 0 <= i < Z.of_nat n -> in_globals AF.frame_RELRO (A + i)) ->
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  LImg.image_bytes rsegs A n = Some bs -> bytes_at rsegs mem A bs.
Proof.
  intros mem A n bs HG Hin HA0 HAn Him.
  pose proof (proj1 FF) as SEGS.
  pose proof (LImg.image_bytes_length rsegs n A bs Him) as Hlen.
  split; [exact HA0|]. split; [rewrite Hlen; exact HAn|].
  intros i Hi. rewrite Hlen in Hi.
  pose proof (HG (A + Z.of_nat i) (Hin (Z.of_nat i) ltac:(lia))) as Hg. rewrite SEGS in Hg.
  rewrite <- (r5_image_nth n A bs Him i Hi). exact Hg.
Qed.

(* FRA survives a run whose writes are the five R5 spill blocks r5_W A: app bytes of the real stack in
   [stklo, APPMEM_END) (a_store_ok, so AH / stklo by a_laws_store; RT by RT_store), above the image, the runtime
   cells and the shadow map, above the frame (fr + 3136 <= A), below the fr spill [A + 336, A + 344) and the saved
   caller registers [S - 104, S), and apart from the spills [A + 40, A + 56); FSREC by fsrec_munch_lo (nothing is
   written below stklo); the input facts by fra_in_keep (the input block is below stklo <= S - SLOT_STACK < A). *)
Lemma r5_fra : forall g fr hb regs regs' mem mem' md A0,
  FRA B APIf ra g fr hb regs mem md -> rg regs 9 A0 -> 0 <= A0 < 2 ^ 64 ->
  Frame.munch (r5_W A0) mem mem' -> Frame.wmono rsegs mem mem' ->
  (forall x, ~ Frame.outside (r5_W A0) x -> exists b, mbyte rsegs mem' x = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md A0 HF Hr90 HA0 MU WM HPres E2 E3 E4 E8 E9 E19 E26.
  pose proof FF as (SEGS & _ & _ & _ & Hhead & Hlock & Hthr & _).
  pose proof (fra_in_apart B APIf ra g fr hb regs mem md HF) as HINAP.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                (hb ++ g_H g) mem md HAH) as Hhm.
  assert (HAhm : HIGHMEM_BEG <= A) by lia.
  assert (HA64 : 0 <= A < 2 ^ 64) by (unfold HIGHMEM_BEG in HAhm; unfold APPMEM_END in HAPP; lia).
  assert (HAeq : A0 = A).
  { unfold rg in Hr9, Hr90. rewrite Hr9 in Hr90.
    pose proof (f_equal (@bv_unsigned 64) Hr90) as Hq.
    rewrite !MState.unsigned_lit in Hq by lia. lia. }
  subst A0.
  assert (Hfrapp : forall a, fr <= a < fr + 3136 -> app_mem a).
  { pose proof Hloc as Hl2. destruct Hl2 as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
    - intros a Ha. unfold app_mem. right. pose proof (Hreal a Ha). lia.
    - intros a Ha. destruct (Hfs a Ha) as (b & Hb64 & Hwm & Hlo & Hhi).
      destruct (r5_fsp (hb ++ g_H g) mem md b HAH Hwm Hb64) as (_ & _ & Happ).
      apply Happ. lia. }
  assert (HAW : all_app (r5_W A)).
  { unfold r5_W. cbn [all_app].
    repeat split; try exact I; intros a Ha; unfold app_mem; right;
      unfold HIGHMEM_BEG, APPMEM_END in *; lia. }
  assert (HD : rt_disjoint (r5_W A)).
  { unfold HIGHMEM_BEG in HAhm. unfold r5_W.
    unfold rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF,
      RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM,
      RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
    cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.disjoint_from Frame.disjoint_from].
    repeat split; first [ exact I | left; lia ]. }
  assert (Hagree : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by exact Ha.
    destruct (KindBGlue.kb_outside_dec (r5_W A) a) as [Ho|Ho]; [exact Ho|exfalso].
    pose proof (r5_not_out A a Ho) as Hin.
    apply Hns. unfold AC.a_store_ok. right; left. unfold APPMEM_END in *. lia. }
  assert (Hwr : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
  destruct (r5_store (hb ++ g_H g) mem mem' md HAH Hagree Hwr) as (HAH' & _ & HSTK & _).
  assert (KBlo : forall (sg : list Segment) x, 0 <= x -> x < 6283264 -> mbyte sg mem' x = mbyte sg mem x).
  { intros sg x H0 H1. assert (Hm : mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
    { apply MU. rewrite MState.unsigned_lit by (unfold HIGHMEM_BEG in HAhm; lia).
      apply r5_out. unfold HIGHMEM_BEG in HAhm. lia. }
    unfold mbyte. rewrite Hm. reflexivity. }
  exists A, sp, s5.
  split; [exact (AsanRTInv.RT_store sp sp mem mem' md md (r5_W A) HRT MU WM HAW HD)|].
  split; [exact HAH'|].
  split.
  { apply (ro_agree_same rsegs mem mem' Hro). intros a Ha. pose proof (r5_ro_low a Ha) as Hb.
    pose proof (bv_unsigned_in_range 64 a) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    apply MU. apply r5_out. unfold HIGHMEM_BEG in HAhm. lia. }
  split.
  { destruct Hsn as (Hcse & Hohd & Hfd). split; [|split; [|exact Hfd]].
    - destruct Hcse as (Hthrm & Hlockm). split.
      + eapply YI14.val_mem_frame; [|exact Hthrm]. intros x Hx. apply KBlo; [lia | rewrite Hthr in Hx; cbn in Hx; lia].
      + eapply YI14.val_mem_frame; [|exact Hlockm]. intros x Hx. apply KBlo; [lia | rewrite Hlock in Hx; cbn in Hx; lia].
    - intros k Hk. rewrite KBlo; [exact (Hohd k Hk) | rewrite Hhead; lia | rewrite Hhead; lia]. }
  split; [exact Hhalt|].
  split.
  { intros a Hin. rewrite KBlo.
    - exact (Hgimg a Hin).
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [Ei|Hil]; [injection Ei as <- <-; lia|]); destruct Hil.
    - destruct Hin as (lo & len & Hil & Hr). unfold AF.frame_RELRO in Hil. cbn in Hil.
      repeat (destruct Hil as [Ei|Hil]; [injection Ei as <- <-; lia|]); destruct Hil. }
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
  { unfold q64 in *. apply (fl_bytes (r5_W A) mem mem' _ _ Hspill MU).
    rewrite length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply r5_out. lia. }
  split.
  { unfold q64 in *. apply (fl_bytes (r5_W A) mem mem' _ _ Hsel MU).
    rewrite length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply r5_out. lia. }
  split.
  { unfold q64 in *. apply (fl_bytes (r5_W A) mem mem' _ _ Hfr56 MU).
    rewrite length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply r5_out. lia. }
  split.
  { destruct Hloc as [[H0 [Hspfr Hreal]]|[Hfr0 [Hfsb [Hfs Hfsrec]]]].
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
      + eapply fsrec_munch_lo with (W := r5_W A); [exact Hfsrec | exact HAH | exact MU |].
        intros x Hx _. apply r5_out. left. lia. }
  split.
  { unfold q64 in *. apply (fl_bytes (r5_W A) mem mem' _ _ Hhdr1 MU).
    rewrite length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply r5_out. lia. }
  split.
  { unfold q64 in *. apply (fl_bytes (r5_W A) mem mem' _ _ Hhdr2 MU).
    rewrite length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply r5_out. lia. }
  split.
  { destruct Hsh as (sh & Hbytes & Hlen). exists sh. split; [|exact Hlen].
    apply (fl_bytes (r5_W A) mem mem' _ _ Hbytes MU). rewrite Hlen. intros x Hx. apply r5_out. left.
    rewrite HFSv in Hx. change (Z.of_nat (Z.to_nat 392)) with 392 in Hx.
    assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
    { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (Hinfr : fr <= fr + 8 * (x - Sfr fr) < fr + 3136) by lia.
    pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Hfrapp _ Hinfr)) as His.
    unfold shadow_addr in His. rewrite Hdiv in His. unfold Sfr, shadow_addr in *.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
  split.
  { destruct Hwin as (Hw0 & Hw1 & Hwv). split; [exact Hw0|]. split; [exact Hw1|].
    intros x Hx. destruct (Hwv x Hx) as (Hwx & b & Hb). split; [exact (WM (wa x) Hwx)|].
    destruct (KindBGlue.kb_outside_dec (r5_W A) x) as [Ho|Ho].
    - exists b. apply (r5_mrd_eq mem mem' (wa x) b); [|exact Hb].
      apply MU. rewrite Mem.wa_unsigned by lia. exact Ho.
    - destruct (HPres x Ho) as (b' & Hb'). exists b'. exact Hb'. }
  split.
  { apply (fl_bytes (r5_W A) mem mem' _ _ Hsaved MU). intros x Hx.
    unfold saved_bytes in Hx. rewrite !length_app, !length_le8 in Hx. cbn in Hx.
    apply r5_out. lia. }
  split.
  { intros a Ha. exact (WM (Z_to_bv 64 a) (Herrno a Ha)). }
  split; [intros a Hin; exact (sl_addr_keep mem mem' (r5_W A) a 1 (HAG a Hin) MU HAW)|].
  split; [intros a Ha1 Ha2; exact (sl_addr_keep mem mem' (r5_W A) a 1 (HWA a Ha1 Ha2) MU HAW)|].
  split; [exact HSHI1|]. split; [exact HSHI2|]. split; [exact HSHI3|].
  split; [exact Hhb|]. split; [exact Hlive|].
  assert (Hin16 : forall x, g_p g <= x < g_p g + g_n g -> x < A + 16).
  { intros x Hx. destruct (HINAP x Hx) as (_ & Hxlo & _). lia. }
  exact (fra_in_keep g mem mem' (r5_W A) Hinb Hinblk MU HAW (fun x Hx => r5_out A x (or_introl (Hin16 x Hx)))).
Qed.

(* R5: the 20 instructions 0x8169c .. 0x816e8 into the round-trip head 0x816ec at b = 0 (Inv_B816ec_at g 0). The
   run keeps s7 / s9 (CUR), the FRA registers and every frame byte (OUR, the turn-0 identity and fragment records),
   sets s6 = 0, s5 = 36 and s11 = 32, and writes the five spill blocks; the carried spills of the official entry
   Inv_B8169c lie outside them.  ENT moves by ent_store (every written byte is in the slot window). *)
Lemma seg_R5 : Hat B APIf ra (Inv_B816ec_at B APIf ra) 0%nat -> Hcut B APIf ra (Inv_B8169c B APIf ra).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hn26 & HCUR & HOUR & HID & HFG & Hs312 & Hs264 &
                    Hs56 & Hs184 & Hs144 & Hs8 & Hr18 & Had2624 & Had544 & Hs96 & Hs120 & Hs240 & Hs232 &
                    Hs224 & Hs176 & Hs208 & Hs64 & HPRA & Hs152 & Hs112 & Had2176 & Had2256 & Hname & Hs160).
  unfold OUTA in Had544.
  subst c.
  rewrite SEGS.
  pose proof HFRA as HF0.
  destruct HF0 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & _ & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc))
                ([] ++ g_H g) mem md HAH) as Hhm.
  assert (HAhm : HIGHMEM_BEG <= A) by lia.
  assert (HA64 : 0 <= A < 2 ^ 64) by (unfold HIGHMEM_BEG in HAhm; unfold APPMEM_END in HAPP; lia).
  assert (E9 : bv_unsigned (getr regs 9) = A)
    by (unfold rg in Hr9; rewrite Hr9; apply MState.unsigned_lit; lia).
  (* the carried spills name the spill base A of register 9 *)
  destruct Hs312 as (A1 & HA1 & Hq312).
  assert (HA1e : A1 = A)
    by (apply (r5_spill_A regs mem 312 (fr + 544) A A1 HA1 Hq312 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A1.
  destruct Hs264 as (A2 & HA2 & Hq264).
  assert (HA2e : A2 = A)
    by (apply (r5_spill_A regs mem 264 (fr + 2624) A A2 HA2 Hq264 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A2.
  destruct Hs56 as (A3 & HA3 & Hq56).
  assert (HA3e : A3 = A)
    by (apply (r5_spill_A regs mem 56 (fr + 3040) A A3 HA3 Hq56 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A3.
  destruct Hs184 as (A4 & HA4 & Hq184).
  assert (HA4e : A4 = A)
    by (apply (r5_spill_A regs mem 184 (fr + 2368) A A4 HA4 Hq184 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A4.
  destruct Hs144 as (A5 & HA5 & Hq144).
  assert (HA5e : A5 = A)
    by (apply (r5_spill_A regs mem 144 (fr + 2176) A A5 HA5 Hq144 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A5.
  destruct Hs8 as (A6 & HA6 & Hq8).
  assert (HA6e : A6 = A)
    by (apply (r5_spill_A regs mem 8 (Sfr fr + 68) A A6 HA6 Hq8 Hr9); unfold APPMEM_END in HAPP; lia).
  subst A6.
  (* the A4 spills the run carries name the same spill base *)
  assert (KSp : forall off v, 0 <= off <= 440 -> spill regs mem off v -> q64 mem (A + off) v).
  { intros off v Hoff (A' & HA' & Hq).
    assert (HAe : A' = A)
      by (apply (r5_spill_A regs mem off v A A' HA' Hq Hr9); unfold APPMEM_END in HAPP; lia).
    subst A'. exact Hq. }
  pose proof (KSp 96 _ ltac:(lia) Hs96) as Hq96. pose proof (KSp 120 _ ltac:(lia) Hs120) as Hq120.
  pose proof (KSp 240 _ ltac:(lia) Hs240) as Hq240. pose proof (KSp 232 _ ltac:(lia) Hs232) as Hq232.
  pose proof (KSp 224 _ ltac:(lia) Hs224) as Hq224. pose proof (KSp 176 _ ltac:(lia) Hs176) as Hq176.
  pose proof (KSp 208 _ ltac:(lia) Hs208) as Hq208. pose proof (KSp 64 _ ltac:(lia) Hs64) as Hq64.
  pose proof (KSp 152 _ ltac:(lia) Hs152) as Hq152. pose proof (KSp 112 _ ltac:(lia) Hs112) as Hq112.
  pose proof (KSp 160 _ ltac:(lia) Hs160) as Hq160.
  (* s2 = mrow, a multiple of 8 (CAT = 0x9f620, CAT_ROW = 296) *)
  assert (Hist : 0 <= istar (g_in g) < 11) by (unfold istar, CAT_N; apply Z.mod_pos_bound; lia).
  assert (Hmrow : bv_unsigned (getr regs 18) = mrow (g_in g)).
  { unfold rg in Hr18. rewrite Hr18. apply MState.unsigned_lit. unfold mrow, CAT, CAT_ROW. lia. }
  assert (H8 : bv_unsigned (getr regs 18) mod 8 = 0).
  { rewrite Hmrow. unfold mrow, CAT, CAT_ROW. clear -Hist. Z.div_mod_to_equations. lia. }
  (* the five writable blocks the run stores into, carved from the S-anchored window *)
  destruct (r5_carve mem (g_S g - AF.SLOT_STACK) (g_S g) (A + 16) 24 Hwin
              ltac:(lia) ltac:(change (Z.of_nat 24) with 24; lia)) as (j1 & C1).
  destruct (r5_carve mem (g_S g - AF.SLOT_STACK) (g_S g) (A + 128) 8 Hwin
              ltac:(lia) ltac:(change (Z.of_nat 8) with 8; lia)) as (j2 & C2).
  destruct (r5_carve mem (g_S g - AF.SLOT_STACK) (g_S g) (A + 248) 8 Hwin
              ltac:(lia) ltac:(change (Z.of_nat 8) with 8; lia)) as (j3 & C3).
  destruct (r5_carve mem (g_S g - AF.SLOT_STACK) (g_S g) (A + 256) 8 Hwin
              ltac:(lia) ltac:(change (Z.of_nat 8) with 8; lia)) as (j4 & C4).
  destruct (r5_carve mem (g_S g - AF.SLOT_STACK) (g_S g) (A + 272) 8 Hwin
              ltac:(lia) ltac:(change (Z.of_nat 8) with 8; lia)) as (j5 & C5).
  assert (HAW : all_app (r5_W A)).
  { unfold r5_W. cbn [all_app].
    repeat split; try exact I; intros a Ha; unfold app_mem; right;
      unfold HIGHMEM_BEG, APPMEM_END in *; lia. }
  (* the run *)
  apply (sl_run regs (Z_to_bv 64 0x8169c) mem md
    (fun R pc' mm =>
       pc' = Z_to_bv 64 0x816ec /\
       Frame.munch (r5_W A) mem mm /\ Frame.wmono rsegs mem mm /\
       q64 mm (A + 16) (bv_unsigned (getr regs 18) + 20) /\ q64 mm (A + 24) (bv_unsigned (getr regs 18) + 16) /\
       q64 mm (A + 32) 0 /\
       q64 mm (A + 128) 0xe38f0000 /\ q64 mm (A + 248) 0x1234 /\ q64 mm (A + 256) 0x21140 /\
       q64 mm (A + 272) (bv_unsigned (getr regs 18)) /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = getr regs 26 /\ getr R 23 = getr regs 23 /\ getr R 25 = getr regs 25 /\
       getr R 21 = Z_to_bv 64 36 /\ getr R 22 = Z_to_bv 64 0 /\ getr R 27 = Z_to_bv 64 32)
    (Post B APIf ra g)).
  - exact Hhalt.
  - rewrite r5_mkR_of.
    eapply evt_mono.
    + apply r5_evt with (j1 := j1) (j2 := j2) (j3 := j3) (j4 := j4) (j5 := j5); try rewrite E9; assumption.
    + intros ms' HP.
      destruct HP as (a0' & a1' & a2' & s2' & s5' & s6' & s8' & s11' & m' & Hms & E5 & E6 & E11 & MU & WM &
        Hq16 & Hq24 & Hq32 & Hq128 & Hq248 & Hq256 & Hq272).
      subst s5' s6' s11'.
      rewrite E9 in MU, Hq16, Hq24, Hq32, Hq128, Hq248, Hq256, Hq272.
      do 3 eexists. split; [exact Hms|].
      split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|].
      split; [exact Hq16|]. split; [exact Hq24|]. split; [exact Hq32|].
      split; [exact Hq128|]. split; [exact Hq248|]. split; [exact Hq256|]. split; [exact Hq272|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; reflexivity.
  - intros R pc' mm regs'' md' HK Hreg Hmat.
    destruct HK as (Hpc & MU & WM & Hq16 & Hq24 & Hq32 & Hq128 & Hq248 & Hq256 & Hq272 &
      G2 & G3 & G4 & G8 & G9 & G19 & G26 & G23 & G25 & G21 & G22 & G27).
    subst pc'.
    unfold q64 in Hq16, Hq24, Hq32, Hq128, Hq248, Hq256, Hq272.
    assert (HPres : forall x, ~ Frame.outside (r5_W A) x -> exists b, mbyte rsegs mm x = Some b).
    { intros x Ho. destruct (r5_not_out A x Ho) as [Hx|[Hx|[Hx|[Hx|Hx]]]].
      - destruct (Z_lt_le_dec x (A + 24)) as [H1|H1];
          [|destruct (Z_lt_le_dec x (A + 32)) as [H2|H2]].
        + apply (r5_pres mm (A + 16) _ x Hq16). rewrite length_le8. change (Z.of_nat 8) with 8. lia.
        + apply (r5_pres mm (A + 24) _ x Hq24). rewrite length_le8. change (Z.of_nat 8) with 8. lia.
        + apply (r5_pres mm (A + 32) _ x Hq32). rewrite length_le8. change (Z.of_nat 8) with 8. lia.
      - apply (r5_pres mm (A + 128) _ x Hq128). rewrite length_le8. change (Z.of_nat 8) with 8. lia.
      - apply (r5_pres mm (A + 248) _ x Hq248). rewrite length_le8. change (Z.of_nat 8) with 8. lia.
      - apply (r5_pres mm (A + 256) _ x Hq256). rewrite length_le8. change (Z.of_nat 8) with 8. lia.
      - apply (r5_pres mm (A + 272) _ x Hq272). rewrite length_le8. change (Z.of_nat 8) with 8. lia. }
    assert (HF1 : FRA B APIf ra g fr [] regs'' mm md).
    { apply (r5_fra g fr [] regs regs'' mem mm md A HFRA Hr9 HA64 MU WM HPres);
        rewrite Hreg; assumption. }
    assert (HF2 : FRA B APIf ra g fr [] regs'' mm md')
      by exact (sl_fra_move B APIf ra g fr [] regs'' regs'' mm md md' HF1
                  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Hmat).
    assert (HA9 : rg regs'' 9 A) by (unfold rg in *; rewrite Hreg, G9; exact Hr9).
    (* ENT: every written byte is a_store_ok and in the slot window, so a_laws_store keeps stklo / stkhi /
       ownership and ent_store moves ENT; ent_mat takes the model step *)
    assert (Hagree : forall a, 0 <= a < 2 ^ 64 ->
        ~ AC.a_store_ok ([] ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
        mm (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by exact Ha.
      destruct (KindBGlue.kb_outside_dec (r5_W A) a) as [Ho|Ho]; [exact Ho|exfalso].
      pose proof (r5_not_out A a Ho) as Hin.
      apply Hns. unfold AC.a_store_ok. right; left. unfold APPMEM_END in *. lia. }
    assert (Hwr : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mm a)
      by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
    destruct (r5_store ([] ++ g_H g) mem mm md HAH Hagree Hwr) as (_ & HOWN' & HSTK' & HHI').
    assert (HWcases : forall x, 0 <= x < 2 ^ 64 ->
              Frame.outside (r5_W A) x \/ (g_S g - AF.SLOT_STACK <= x < g_S g) \/ (fr <= x < fr + 3136) \/
              (Sfr fr <= x < Sfr fr + 392)).
    { intros x Hx. destruct (KindBGlue.kb_outside_dec (r5_W A) x) as [Ho|Ho]; [left; exact Ho|].
      right; left. pose proof (r5_not_out A x Ho). lia. }
    assert (HOWNk : forall a, AC.a_in_img a ->
              AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mem md a ->
              AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) ([] ++ g_H g) mm md a)
      by (intros a _ Ho; exact (proj2 (HOWN' a) Ho)).
    assert (HENT' : ENT APIf g [] mm md).
    { eapply ent_store with (W := r5_W A); try exact FF; try exact HENT; try exact HFRA; try exact MU;
        try exact HWcases; try exact HSTK'; try exact HHI'; try exact HOWNk. }
    assert (HENT'' : ENT APIf g [] mm md') by (eapply ent_mat; [exact HENT' | exact Hmat]).
    (* the run's memory facts the exit reads *)
    pose proof HF1 as (A' & sp' & s5' & _ & _ & Hro1 & _ & _ & Hgimg1 & _).
    rewrite <- SEGS. apply Hexit. exists regs'', mm, md', fr.
    split; [reflexivity|]. split; [exact HF2|]. split; [exact HENT''|]. cbv beta.
    split; [exact Hn26|].
    split.
    { unfold RS, RB. split; [lia|].
      destruct HCUR as (Hc & H23 & H25).
      split; [split; [exact Hc|]; unfold rg in *; rewrite !Hreg, G23, G25; split; [exact H23 | exact H25]|].
      split.
      { unfold OURb in *. apply (fl_bytes (r5_W A) mem mm _ _ HOUR MU).
        rewrite OUR_length. intros x Hx. change (Z.of_nat 6) with 6 in Hx. apply r5_out. lia. }
      split; [unfold rg; rewrite Hreg, G22; reflexivity|].
      split.
      { unfold IDBr in *. apply (fl_bytes (r5_W A) mem mm _ _ HID MU).
        assert (LID : length (RID (g_in g) 0) = 38%nat) by reflexivity.
        rewrite LID. intros x Hx. change (Z.of_nat 38) with 38 in Hx. apply r5_out. lia. }
      { unfold FGBr in *. apply (fl_bytes (r5_W A) mem mm _ _ HFG MU).
        assert (LFG : length (RFG (g_in g) 0) = 72%nat) by reflexivity.
        rewrite LFG. intros x Hx. change (Z.of_nat 72) with 72 in Hx. apply r5_out. lia. } }
    (* the spills the run carries: their words are outside the five written blocks *)
    assert (KR : forall off v, q64 mem (A + off) v ->
              off + 8 <= 16 \/ (40 <= off /\ off + 8 <= 128) \/ (136 <= off /\ off + 8 <= 248) \/
              (264 <= off /\ off + 8 <= 272) \/ 280 <= off ->
              spill regs'' mm off v).
    { intros off v Hq Hoff. exists A. split; [exact HA9|]. unfold q64 in *.
      apply (fl_bytes (r5_W A) mem mm _ _ Hq MU).
      rewrite length_le8. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply r5_out. lia. }
    (* the row-name clause: image bytes below GT < A, outside the written blocks *)
    assert (HNM : RS6.has (rt_mb (g_in g)) <> 0 /\ RS6.rname (rt_mb (g_in g)) <> 0 ->
              RBx.name_ok (rt_nb (g_in g)) /\ bytes_at rsegs mm (RS6.rname (rt_mb (g_in g))) (rt_nb (g_in g)) /\
              addressable mm (RS6.rname (rt_mb (g_in g))) (Z.of_nat (length (rt_nb (g_in g)))) /\
              0 < RS6.rname (rt_mb (g_in g)) /\
              RS6.rname (rt_mb (g_in g)) + Z.of_nat (length (rt_nb (g_in g))) <= AC.GT).
    { intros Hh. destruct (Hname Hh) as (Hok & Hb & Had & Hpos & Hgt).
      split; [exact Hok|].
      split.
      { apply (fl_bytes (r5_W A) mem mm _ _ Hb MU). intros x Hx. apply r5_out. left.
        pose proof HAhm as HAh'. unfold HIGHMEM_BEG in HAh'. unfold AC.GT in Hgt. lia. }
      split; [exact (sl_addr_keep mem mm (r5_W A) _ _ Had MU HAW)|].
      split; [exact Hpos | exact Hgt]. }
    (* RBE: the run's spills ([A + 128], [A + 272] = mrow, [A + 256], [A + 248], [A + 32] = 0, [A + 24] =
       mrow + 16, [A + 16] = mrow + 20), the carried spills, out[] / the identity record / our[] addressable, the
       row-name clause, and the image bytes (CTRL_FRAMES rows and the catalogue row are RELRO, G_img_c; the box
       is read-only, ro_agree) *)
    assert (HRBE : RBE g fr regs'' mm).
    { unfold RBE.
      split; [exists A; split; [exact HA9 | exact Hq128]|].
      split; [exact (KR 312 _ Hq312 ltac:(lia))|].
      split; [exists A; split; [exact HA9|]; unfold q64; rewrite <- Hmrow; exact Hq272|].
      split; [exact (KR 264 _ Hq264 ltac:(lia))|].
      split; [exists A; split; [exact HA9 | exact Hq256]|].
      split; [exists A; split; [exact HA9 | exact Hq248]|].
      split; [exact (KR 56 _ Hq56 ltac:(lia))|].
      split; [exact (KR 184 _ Hq184 ltac:(lia))|].
      split; [exact (KR 144 _ Hq144 ltac:(lia))|].
      split; [exact (KR 8 _ Hq8 ltac:(lia))|].
      split; [exists A; split; [exact HA9 | exact Hq32]|].
      split; [exists A; split; [exact HA9|]; unfold q64; rewrite <- Hmrow; exact Hq24|].
      split; [exists A; split; [exact HA9|]; unfold q64; rewrite <- Hmrow; exact Hq16|].
      split; [exact (KR 96 _ Hq96 ltac:(lia))|].
      split; [exact (KR 120 _ Hq120 ltac:(lia))|].
      split; [exact (KR 240 _ Hq240 ltac:(lia))|].
      split; [exact (KR 232 _ Hq232 ltac:(lia))|].
      split; [exact (KR 224 _ Hq224 ltac:(lia))|].
      split; [exact (KR 176 _ Hq176 ltac:(lia))|].
      split; [exact (KR 208 _ Hq208 ltac:(lia))|].
      split; [exact (KR 64 _ Hq64 ltac:(lia))|].
      split; [unfold OUTA; exact (sl_addr_keep mem mm (r5_W A) (fr + 544) 1492 Had544 MU HAW)|].
      split; [exact (sl_addr_keep mem mm (r5_W A) (fr + 2176) 38 Had2176 MU HAW)|].
      split; [exact HNM|].
      split; [exact (sl_addr_keep mem mm (r5_W A) (fr + 2624) 6 Had2624 MU HAW)|].
      split.
      { apply (r5_img_bytes mm (BAC.BA_FR + 72) 168 BAP.ba_tbl Hgimg1);
          [| unfold BAC.BA_FR; lia | unfold BAC.BA_FR; lia | exact r5_tbl_img].
        intros i Hi. exists 0x9f168, 9344.
        split; [unfold AF.frame_RELRO; cbn [In]; left; reflexivity | unfold BAC.BA_FR; lia]. }
      split.
      { apply (r5_ro_bytes mm BOXA 6 box6 Hro1 r5_box_ro); [unfold BOXA; lia | unfold BOXA; lia | exact r5_box_img]. }
      split.
      { assert (Hin11 : In (istar (g_in g)) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]) by (cbn [In]; lia).
        pose proof (proj1 (forallb_forall _ _) r5_rows_img _ Hin11) as Hrw. cbv beta in Hrw.
        destruct (LImg.image_bytes rsegs (CAT + CAT_ROW * istar (g_in g)) 296) as [row|] eqn:Hrow;
          [|discriminate Hrw].
        assert (Emb : rt_mb (g_in g) = row) by (unfold rt_mb, rowb, img; rewrite Hrow; reflexivity).
        rewrite Emb.
        apply (r5_img_bytes mm (mrow (g_in g)) 296 row Hgimg1);
          [| unfold mrow, CAT, CAT_ROW; lia | unfold mrow, CAT, CAT_ROW; lia | unfold mrow; exact Hrow].
        intros i Hi. exists 0x9f168, 9344.
        split; [unfold AF.frame_RELRO; cbn [In]; left; reflexivity | unfold mrow, CAT, CAT_ROW; lia]. }
      (* adopt 9 of a working branch: PRA, [A + 152] = fr + 64 and [A + 112] = fr + 2256, carried (outside W) *)
      split.
      { apply (r5_pra fr regs regs'' mem mm); [|exact HPRA].
        intros off v Hin Hs. cbn [In] in Hin.
        apply (KR off v); [apply KSp; [clear -Hin; lia | exact Hs] | clear -Hin; lia]. }
      split; [exact (KR 152 _ Hq152 ltac:(lia))|]. split; [exact (KR 112 _ Hq112 ltac:(lia))|].
      (* adopt 10 of a working branch: the fragment record's 72 bytes, addressable (W is app memory) *)
      split; [exact (sl_addr_keep mem mm (r5_W A) (fr + 2256) 72 Had2256 MU HAW)|].
      (* [A + 160] = fr + 32 (v1.9.0's A4 store, appended last to RBE), carried (outside W) *)
      exact (KR 160 _ Hq160 ltac:(lia)). }
    split; [exact HRBE|].
    split; [unfold rg; rewrite Hreg; exact G21|].
    (* R6X g 0 from RBE; the row-name clause *)
    split; [exact (r6x_of_rbe g 0%nat fr regs'' mm HRBE)|].
    split; [exact HNM|].
    (* adopt 10 of a working branch: s11 = 32 (0x816cc li s11,32) *)
    unfold rg; rewrite Hreg; exact G27.
Qed.

End Seg.
