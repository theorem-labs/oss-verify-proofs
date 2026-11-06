(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v; 186 of its 223 lines of code are new or changed and 359 lines of the source are left out. *)
(* Segment F27 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, patched image A), 0x82604-0x82658: the head of the
   inlined check_ports after the second reac_ports_unknown call. Entry cut Inv_A82604_at (s9 = r = t_rp,
   s4 = unk = t_unk, a0 = the second count = t_unk), exit cuts Inv_A8265c_at (r = 0) and Inv_A82750_at (r <> 0).
     0x82604  bne  a0,s4,82bf4   -- not taken: both counts are t_unk.
     0x82608  seqz a0,s9 ; 0x8260c slti a1,s4,0 ; 0x82610 li a2,-7
     0x82614  beq  a0,a1,82bf4   -- not taken: t_rp = 0 exactly when 0 <= t_unk (ports fact C5.3).
     0x82618  ld   t2,136(s1)    -- t2 = [A+136] = fr + 128 (the ports words).
     0x8261c  beqz s9,82640
   r <> 0 (t_rp = t_unk = -1): 0x82620-0x82638 load the three ports words (lw, no instrumented check) and compare
   them with -7; each `bne _,a2,82bf4` is not taken because PORTS keeps the three words at -7 (C5.4); s9 = [A+176]
   = fr + 64; `j 82750` reaches the exit Inv_A82750_at.
   r = 0 (0 <= t_unk <= 48): 0x82640-0x82658 set a6 = a3 = a1 = a2 = 0, a4 = a0 = s6 + 8 = phi + 26, a5 = 12 and
   reach the exit Inv_A8265c_at (port-slot loop head).
   No call, no store, no instrumented check: memory is unchanged, so FRA moves by sl_fra_move, the entry relation
   ENT by ent_mat, FLSI by b7_flsi_regs and B7K by b7_B7K_regs. The ports facts are the plain twin's (a Theorem Labs lane
   lib/Prog/Seg/Tac_b7.v, b7_ prefix kept). The exit 0x82750's FLS and LT come from B7K (push 12: s2 = len_j, the record
   at phi, the [A+152] spill, LT) by b7_a826a4. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL Require Import Exec Step Tac Cells Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.AW Require Import SmLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcPorts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot B7Cuts.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module ULMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Mem.
Module ULPE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.PropExec.

(* ---- Ports facts C5.3 / C5.4 (plain twin Tac_b7.v; block = phi + 18, pbs = its first 20 bytes) ---- *)

(* C5.3: reac_ports_parse and reac_ports_unknown accept the same blocks. *)
Lemma b7_decl_same : forall bs, RcLeaf.decl bs = RcPorts.pu_decl bs.
Proof. intros bs. reflexivity. Qed.

Lemma b7_nunk_nonneg : forall bs k, 0 <= RcPorts.pu_nunk bs k.
Proof. intros bs k. induction k as [|k IH]; cbn [RcPorts.pu_nunk]; [lia|]. destruct (4 <=? _); lia. Qed.

Lemma b7_nunk_le : forall bs k, RcPorts.pu_nunk bs k <= Z.of_nat k.
Proof. intros bs k. induction k as [|k IH]; cbn [RcPorts.pu_nunk]; [lia|]. destruct (4 <=? _); lia. Qed.

Lemma b7_unk_rp0 : forall inp j, t_rp inp j = 0 -> 0 <= t_unk inp j <= 48 /\ RcPorts.pu_decl (t_pbs inp j) = true.
Proof.
  intros inp j H. unfold t_rp, t_unk in *. rewrite <- b7_decl_same.
  destruct (RcLeaf.decl (t_pbs inp j)); [|discriminate H].
  pose proof (b7_nunk_nonneg (t_pbs inp j) 12). pose proof (b7_nunk_le (t_pbs inp j) 12).
  change (Z.of_nat 12) with 12 in *. split; [lia | reflexivity].
Qed.

Lemma b7_unk_rpm : forall inp j, t_rp inp j <> 0 -> t_rp inp j = -1 /\ t_unk inp j = -1.
Proof.
  intros inp j H. unfold t_rp, t_unk in *.
  change (RcPorts.pu_decl (t_pbs inp j)) with (RcLeaf.decl (t_pbs inp j)).
  destruct (RcLeaf.decl (t_pbs inp j)); [exfalso; apply H; reflexivity | split; reflexivity].
Qed.

(* ---- Stepping helpers (asan engine) ---- *)

(* A carried `bytes_at` fact in the `ov_read_bytes _ _ _ n = Some bs` form the UL load step consumes. *)
Lemma f27_rd4 : forall m a bs, bytes_at rsegs m a bs -> length bs = 4%nat ->
  ov_read_bytes rsegs m (ULMem.wa a) 4 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (ULMem.bytes_at_ov_read rsegs m a bs 0 4 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.
Lemma f27_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (ULMem.wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (ULMem.bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.

(* Two spill bases equal as 64-bit values give the same word address at every offset. *)
Lemma f27_wa_shift : forall x y d, Z_to_bv 64 x = Z_to_bv 64 y -> ULMem.wa (x + d) = ULMem.wa (y + d).
Proof.
  intros x y d E. unfold ULMem.wa. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E.
  assert (E' : x mod 2 ^ 64 = y mod 2 ^ 64) by exact E.
  apply bv_eq. rewrite !Z_to_bv_unsigned.
  change ((x + d) mod 2 ^ 64 = (y + d) mod 2 ^ 64).
  rewrite Zplus_mod, E', <- Zplus_mod. reflexivity.
Qed.

(* slti a1,s4,0 with s4 = t_unk >= 0 gives 0. *)
Lemma f27_slti0 : forall u, 0 <= u < 2 ^ 63 -> ULPE.v_slti (Z_to_bv 64 u) 0 = Z_to_bv 64 0.
Proof.
  intros u Hu. unfold ULPE.v_slti, ULPE.zsig.
  assert (E : bv_unsigned (Z_to_bv 64 u) = u) by (apply MState.unsigned_lit; lia).
  rewrite (ULPE.bv_signed_small (Z_to_bv 64 u)) by (rewrite E; lia). rewrite E.
  destruct (Z.ltb_spec u 0); [lia | reflexivity].
Qed.

(* mkR_of regs is definitionally the explicit 31-slot register map; exposing it lets `step` read a slot rewritten to
   a concrete value. *)
Lemma f27_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  Frame.mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

(* Rewrite a register slot `getr regs r` to its carried value, from H : rg regs r v. *)
Ltac f27_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

(* Replace the condition of the branch at the head of the goal by its value v: closed conditions by computation
   (f27_brc), others by the proof pf of `c = v` (f27_br). *)
Ltac f27_brc v :=
  lazymatch goal with
  | |- context [if ?c then _ else _] => replace c with v by (vm_compute; reflexivity); cbv_concl_iota
  end.
Ltac f27_br v pf :=
  lazymatch goal with
  | |- context [if ?c then _ else _] => replace c with v by (symmetry; pf); cbv_concl_iota
  end.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_F27 : forall j : nat, Hat B APIf ra (Inv_A8265c_at B APIf ra) j ->
  Hat B APIf ra (Inv_A82750_at B APIf ra) j -> Hat B APIf ra (Inv_A82604_at B APIf ra) j.
Proof.
  intros j H0 H1 g c HInv.
  pose proof (proj1 FF) as SEGS.
  unfold Inv_A82604_at, B7CUT in HInv.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HFLSI & HK &
    Hs9 & Hs4 & Ha0 & HPO & HFI & Had1 & Had2). subst c.
  rewrite SEGS.
  pose proof (b7_asize_flen g j phi fr regs mem HK) as Hasz.
  rewrite Hasz in HFRA, HENT.
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & _).
  pose proof HK as (HLK & H23 & H22 & Hphi0 & Hphi50 & Hflen & Hblk & Hs280 & H24 & H18 & H152 & Hg & Hph & Hlen &
    HLT & HS136 & HS120 & HS176).
  destruct HS136 as (A1 & H91 & Hq136).
  destruct HS176 as (A3 & H93 & Hq176).
  pose proof (f27_rd8 mem _ _ Hq136 ltac:(apply length_le8)) as RD136.
  pose proof (f27_rd8 mem _ _ Hq176 ltac:(apply length_le8)) as RD176.
  assert (EW : ULMem.wa (A3 + 176) = ULMem.wa (A1 + 176)).
  { apply f27_wa_shift. unfold rg in H91, H93. rewrite <- H91, <- H93. reflexivity. }
  rewrite EW in RD176. clear EW.
  destruct (Z.eq_dec (t_rp (g_in g) j) 0) as [Er|Er].
  - (* r = 0: the loop registers are set; exit at 0x8265c. *)
    destruct (b7_unk_rp0 _ _ Er) as (Hu & _).
    assert (Hu63 : 0 <= t_unk (g_in g) j < 2 ^ 63) by lia.
    apply (sl_run regs (Z_to_bv 64 0x82604) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x8265c /\ mem' = mem /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
         getr R 26 = getr regs 26 /\ getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\
         getr R 22 = getr regs 22 /\ getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\
         getr R 18 = getr regs 18 /\
         getr R 7 = Z_to_bv 64 (fr + 128) /\ getr R 10 = Z_to_bv 64 (phi + 26) /\
         getr R 14 = Z_to_bv 64 (phi + 26) /\ getr R 15 = Z_to_bv 64 12 /\
         getr R 11 = Z_to_bv 64 0 /\ getr R 12 = Z_to_bv 64 0 /\ getr R 13 = Z_to_bv 64 0 /\
         getr R 16 = Z_to_bv 64 0)
      (Post B APIf ra g)).
    + exact Hhalt.
    + rewrite f27_mkR_of_expand.
      rewrite Er in Hs9.
      f27_slot Hs9. f27_slot Hs4. f27_slot Ha0. f27_slot H91. f27_slot H22.
      (* 0x82604 bne a0,s4: both counts are t_unk, not taken *)
      step. f27_br false ltac:(rewrite bv_eqb_refl; reflexivity).
      (* 0x82608 seqz a0,s9 ; 0x8260c slti a1,s4,0 ; 0x82610 li a2,-7 *)
      step. step. step.
      (* 0x82614 beq a0,a1: seqz r = 1, slti unk = 0, not taken *)
      step. f27_br false ltac:(rewrite (f27_slti0 (t_unk (g_in g) j) Hu63); vm_compute; reflexivity).
      (* 0x82618 ld t2,136(s1) = fr + 128 ; 0x8261c beqz s9: r = 0, taken to 0x82640 *)
      step. step. f27_brc true.
      (* 0x82640-0x82658: li a6,0 ; li a3,0 ; li a1,0 ; li a2,0 ; addi a4,s6,8 ; li a5,12 ; mv a0,a4 *)
      step. step. step. step. step. step. step.
      finish. all: simp_regs; try reflexivity; try (f_equal; lia).
    + intros R pc' mem' regs'' md'
        (Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR26 & HR20 & HR21 & HR22 & HR23 & HR24 & HR18 &
         HR7 & HR10 & HR14 & HR15 & HR11 & HR12 & HR13 & HR16) Hreg Hmat.
      subst pc' mem'. rewrite <- SEGS. apply H0.
      unfold Inv_A8265c_at, B7CUT.
      exists phi, regs'', mem, md', fr.
      rewrite ?Hasz.
      cbv beta.
      split; [reflexivity|].
      split.
      { apply (sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs regs'' mem md md' HFRA);
          [ rewrite Hreg; exact HR2 | rewrite Hreg; exact HR3 | rewrite Hreg; exact HR4
          | rewrite Hreg; exact HR8 | rewrite Hreg; exact HR9 | rewrite Hreg; exact HR19
          | rewrite Hreg; exact HR26 | exact Hmat ]. }
      split; [exact (ent_mat APIf g (hb1 phi (flen g j)) mem md md' HENT Hmat)|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
      split; [apply (b7_flsi_regs g j fr regs regs'' mem HFLSI); rewrite Hreg; exact HR9|].
      split; [apply (b7_B7K_regs g j phi fr regs regs'' mem HK); rewrite Hreg; assumption|].
      split; [exact Er|].
      split; [lia|].
      split; [unfold rg; rewrite Hreg, HR20; exact Hs4|].
      split; [unfold rg; rewrite Hreg; exact HR7|].
      split; [exact HPO|].
      split; [exact HFI|].
      split; [unfold rg; rewrite Hreg; exact HR10|].
      split; [unfold rg; rewrite Hreg; exact HR14|].
      split; [unfold rg; rewrite Hreg; exact HR15|].
      split; [unfold rg; rewrite Hreg; exact HR11|].
      split; [unfold rg; rewrite Hreg; exact HR12|].
      split; [unfold rg; rewrite Hreg; exact HR13|].
      unfold rg; rewrite Hreg; exact HR16.
  - (* r <> 0: r = unk = -1, the three ports words are -7; exit at 0x82750. *)
    destruct (b7_unk_rpm _ _ Er) as (Er' & Eu).
    destruct (proj2 HPO Er) as (P0 & P4 & P8).
    pose proof (f27_rd4 mem _ _ P0 ltac:(apply length_le4)) as RD0.
    pose proof (f27_rd4 mem _ _ P4 ltac:(apply length_le4)) as RD4.
    pose proof (f27_rd4 mem _ _ P8 ltac:(apply length_le4)) as RD8.
    apply (sl_run regs (Z_to_bv 64 0x82604) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x82750 /\ mem' = mem /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
         getr R 26 = getr regs 26 /\ getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22 /\
         getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 18 = getr regs 18 /\
         getr R 25 = Z_to_bv 64 (fr + 64))
      (Post B APIf ra g)).
    + exact Hhalt.
    + rewrite f27_mkR_of_expand.
      rewrite Er' in Hs9. rewrite Eu in Hs4, Ha0.
      f27_slot Hs9. f27_slot Hs4. f27_slot Ha0. f27_slot H91.
      (* 0x82604 bne a0,s4: both -1, not taken *)
      step. f27_brc false.
      (* seqz a0,s9 = 0 ; slti a1,s4,0 = 1 ; li a2,-7 ; 0x82614 beq a0,a1 not taken *)
      step. step. step. step. f27_brc false.
      (* 0x82618 ld t2,136(s1) = fr + 128 ; 0x8261c beqz s9 (= -1) not taken *)
      step. step. f27_brc false.
      (* 0x82620 lw a0,0(t2) = -7 ; 0x82624 ld s9,176(s1) = fr + 64 ; 0x82628 bne a0,a2 not taken *)
      step. step. step. f27_brc false.
      (* 0x8262c lw a0,4(t2) = -7 ; 0x82630 bne a0,a2 not taken *)
      step. step. f27_brc false.
      (* 0x82634 lw a0,8(t2) = -7 ; 0x82638 bne a0,a2 not taken *)
      step. step. f27_brc false.
      (* 0x8263c j 82750 *)
      step.
      finish. all: simp_regs; try reflexivity; try (f_equal; lia).
    + intros R pc' mem' regs'' md'
        (Hpc & Hmem & HR2 & HR3 & HR4 & HR8 & HR9 & HR19 & HR26 & HR21 & HR22 & HR23 & HR24 & HR18 & HR25)
        Hreg Hmat.
      subst pc' mem'. rewrite <- SEGS. apply H1.
      unfold Inv_A82750_at.
      exists phi, regs'', mem, md', fr.
      rewrite ?Hasz.
      cbv beta.
      split; [reflexivity|].
      split.
      { apply (sl_fra_move B APIf ra g fr (hb1 phi (flen g j)) regs regs'' mem md md' HFRA);
          [ rewrite Hreg; exact HR2 | rewrite Hreg; exact HR3 | rewrite Hreg; exact HR4
          | rewrite Hreg; exact HR8 | rewrite Hreg; exact HR9 | rewrite Hreg; exact HR19
          | rewrite Hreg; exact HR26 | exact Hmat ]. }
      split; [exact (ent_mat APIf g (hb1 phi (flen g j)) mem md md' HENT Hmat)|].
      split; [exact Hgn|]. split; [exact Hj|]. split; [exact HHB|].
      assert (HFLSI' : FLSI g j fr regs'' mem)
        by (apply (b7_flsi_regs g j fr regs regs'' mem HFLSI); rewrite Hreg; exact HR9).
      split; [exact HFLSI'|].
      apply (b7_a826a4 g j phi fr regs'' mem HFLSI').
      * apply (b7_B7K_regs g j phi fr regs regs'' mem HK); rewrite Hreg; assumption.
      * unfold rg; rewrite Hreg; exact HR25.
Qed.

End S.
