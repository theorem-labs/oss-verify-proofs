(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v; 952 of its 1022 lines of code are new or changed and 1069 lines of the source are left out. *)
(* UciCcCmp: Lemma cc_cmp : cc_cmp_stmt of lib/A/Prog/UciCcCut.v, the five field comparisons of
   check_clamp, the offsets +0x124 .. +0x240 of the audited listing lib/A/Prog/UciPList.v.
   The piece writes no memory and calls nothing: it reads the caller's record (s3) and the leaf's
   clamped copy (s5) field by field, each read behind a shadow check, and aborts at +0x318 when a field
   of the copy differs from `hold` of the caller's field (fuzz_uci.c check_clamp, lines 135-173).
   The walk runs the PA engine (lib/A/Prog/PaRun.v, PaShadow.v, UciPPaLib.v) over four cuts, at +0x150,
   +0x194, +0x1d4 and +0x208, so a field costs three paths instead of multiplying them:
     +0x124 .. +0x14c  amin = hold (in.adapt_min_ms, 1, 1000), into a1;
     +0x150 .. +0x190  prefill_ms, then the local's adapt_min_ms against a1;
     +0x194 .. +0x1d0  adapt_max_ms, held to [amin, 1000];
     +0x1d4 .. +0x204  adapt_margin, held to [0, margin_max];
     +0x208 .. +0x240  servo_clamp_ppm, held to [0, 50000].
   The two records are two read-only regions of the symbolic state (atoms 33 .. 37 the caller's five
   fields, 38 .. 42 the clamped five, atom 11 the one value a cut carries); the five shadow checks are
   decided by the token engine from the statement's range_addressable premise (lib/Reusable/YCbn.v
   shent_ok, with the shadow entry of the caller's twenty bytes); each value branch is split by hand and
   its abort arm refuted by the clamp_* theorems of lib/Spec/UciModel.v. The run keeps no journal: the
   piece changes no memory, so the regions are read-only and lib/Reusable/YA0o.v frame_of_read_only
   gives the memory back unchanged. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YG0s YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import
UciPSyms UciPList UciPAddr UciPPa UciPImg UciPPaLib UciPCJ.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require AE2k AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import Cells Step Frame ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import UciCg UciCcKit UciCcLeafb.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import check_clamp_cg UciCcCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic state of the five comparisons                          *)
(* ------------------------------------------------------------------ *)

Definition cmp_u32 (z : Z) : Z := z mod 2 ^ 32.
Definition cmp_fields (q : rp_hot) : list Z :=
  [prefill_ms q; adapt_min_ms q; adapt_max_ms q; adapt_margin q; servo_clamp_ppm q].
Definition cmp_extra (p : rp_hot) (mm : Z) : list word :=
  w64 SHADOW_OFF :: map (fun z => w64 (cmp_u32 z)) (cmp_fields p ++ cmp_fields (rp_hot_clamp_m p mm)).

Definition cmp_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition cmp_Bx : sv := SOff 24 0.
Definition cmp_SH : list shent := [mkSHE 19 0 20].
Definition cmp_ch4 (o : Z) (k : nat) : YP09.chunk := YP09.mkChunk o (CVal 4 (SOff k 0)).
Definition cmp_pin_rg : YP09.region :=
  YP09.mkRegion (Some 19%nat) 0 20 0 0 [cmp_ch4 0 33; cmp_ch4 4 34; cmp_ch4 8 35; cmp_ch4 12 36; cmp_ch4 16 37].
Definition cmp_loc_rg : YP09.region :=
  YP09.mkRegion (Some 21%nat) 0 20 0 0 [cmp_ch4 0 38; cmp_ch4 4 39; cmp_ch4 8 40; cmp_ch4 12 41; cmp_ch4 16 42].
Definition cmp_regions : smem := [cmp_pin_rg; cmp_loc_rg].
Definition cmp_atoms : list (nat * afact) :=
  [(19%nat, mkAF (2 ^ 46) (2 ^ 47 - 20) 0); (21%nat, mkAF 4096 (2 ^ 47) 0);
   (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (38%nat, mkAF 1 1000 0); (39%nat, mkAF 1 1000 0); (40%nat, mkAF 1 1000 0);
   (41%nat, mkAF 0 2147483647 0); (42%nat, mkAF 0 50000 0)].
Definition cmp_G : facts := mkFacts cmp_atoms [] [].
Definition cmp_G1 : facts := mkFacts ((11%nat, mkAF 1 1000 0) :: cmp_atoms) [] [].
Definition cmp_ss (pc : Z) (G : facts) : sstate := mkSS pc sr_atoms cmp_regions None G.
(* the offsets of the piece, from the listing's base *)
Definition CMP_AT (k : Z) : Z := AF_check_clamp + k.

(* ------------------------------------------------------------------ *)
(* bytes                                                               *)
(* ------------------------------------------------------------------ *)

Lemma cmp_le_byte_range : forall z w k, 0 <= le_byte z w k < 256.
Proof. intros z w k. unfold le_byte. apply Z.mod_pos_bound. lia. Qed.

Lemma cmp_le4_byte : forall x k, (k < 4)%nat ->
  option_map (fun b : byte => bv_unsigned b) (nth_error (LMem.le4 (LMem.wa x)) k)
  = Some (le_byte (cmp_u32 x) 4 k).
Proof.
  intros x k Hk. unfold LMem.le4, word_to_le_bytes.
  apply ucc_leafb_le_byte; [exact Hk|].
  rewrite (ucc_leafb_wa_mod x 4 ltac:(lia)).
  change (8 * Z.of_nat 4) with 32. unfold cmp_u32.
  symmetry. apply (ucc_leafb_mod_pow2_mod x 32 32). lia.
Qed.

Lemma cmp_byte_eq : forall (m : word -> option byte) a x k, (k < 4)%nat ->
  mbyte tfibsegs m a = nth_error (LMem.le4 (LMem.wa x)) k ->
  mbyte tfibsegs m a = Some (Z_to_bv 8 (le_byte (cmp_u32 x) 4 k)).
Proof.
  intros m a x k Hk Hm. rewrite Hm.
  apply (ucc_leafb_opt_byte_eq _ _ (le_byte (cmp_u32 x) 4 k)); [apply cmp_le4_byte; exact Hk|].
  cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. apply cmp_le_byte_range.
Qed.

(* One four-byte field of a record of cells, as the engine reads it. *)
Lemma cmp_bytes_val : forall (m : word -> option byte) (A : Z) (bs : list byte) (o : Z) (x : Z),
  LMem.bytes_at rsegs m A bs ->
  (forall k, (k < 4)%nat -> nth_error bs (Z.to_nat o + k)%nat = nth_error (LMem.le4 (LMem.wa x)) k) ->
  0 <= o -> (Z.to_nat o + 4 <= length bs)%nat ->
  val_mem tfibsegs m (A + o) 4 (cmp_u32 x).
Proof.
  intros m A bs o x Hb Hnth Ho Hlen k Hk.
  destruct Hb as (HA0 & HAt & Hb).
  specialize (Hb (Z.to_nat o + k)%nat ltac:(lia)).
  rewrite (Hnth k Hk) in Hb.
  replace (A + Z.of_nat (Z.to_nat o + k)) with (A + o + Z.of_nat k) in Hb by lia.
  apply (cmp_byte_eq m (A + o + Z.of_nat k) x k Hk).
  exact Hb.
Qed.

Lemma cmp_hot_val : forall (m : word -> option byte) (A : Z) (q : rp_hot) (o x : Z),
  cells_at rsegs m A (PHC.hot_cells q) ->
  In (o, x) [(0, prefill_ms q); (4, adapt_min_ms q); (8, adapt_max_ms q);
             (12, adapt_margin q); (16, servo_clamp_ppm q)] ->
  val_mem tfibsegs m (A + o) 4 (cmp_u32 x).
Proof.
  intros m A q o x [Hwf Hb] Hin.
  assert (HL : length (cells_bytes (PHC.hot_cells q)) = 20%nat) by reflexivity.
  cbn [In] in Hin.
  destruct Hin as [E | [E | [E | [E | [E | []]]]]]; injection E as <- <-;
  (apply (cmp_bytes_val m A (cells_bytes (PHC.hot_cells q)) _ _ Hb);
   [ intros k Hk; destruct k as [|[|[|[|k]]]];
     [reflexivity | reflexivity | reflexivity | reflexivity | lia]
   | lia
   | rewrite HL; lia ]).
Qed.

(* ------------------------------------------------------------------ *)
(* the walk                                                            *)
(* ------------------------------------------------------------------ *)

Section cmp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ uci_listing PI_uci).
Local Abbreviation BASE := (@pa_val _ uci_listing PI_uci A_TEXT).

Definition cmp_E (regs : bvmap 5 word) (p : rp_hot) (mm : Z) : env :=
  Eimg (PI := PI_uci) (Ereg regs (cmp_extra p mm)).

Lemma cmp_ew_reg : forall regs p mm n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (cmp_E regs p mm) n = YK11.getr regs r.
Proof. intros regs p mm n r Hn. unfold cmp_E. apply ucc_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma cmp_ew_ex : forall regs p mm j, (j < 11)%nat ->
  ew (cmp_E regs p mm) (32 + j) = nth j (cmp_extra p mm) (Z_to_bv 64 0).
Proof.
  intros regs p mm j Hj. unfold cmp_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  apply ew_Ereg_extra.
Qed.

Lemma cmp_env_img : forall regs p mm, img_env VAL A_LIM (cmp_E regs p mm).
Proof. intros regs p mm. unfold cmp_E. apply Eimg_env. Qed.

Lemma cmp_agree0 : forall regs p mm, env_agree 32 (Ereg regs (cmp_extra p mm)) (cmp_E regs p mm).
Proof.
  intros regs p mm. split; [intros n Hn; unfold cmp_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

Lemma cmp_agree_extK : forall b (E E' : env) K ws, (b <= K)%nat ->
  env_agree b E E' -> env_agree b E (extK E' K ws).
Proof.
  intros b E E' K ws HK [H1 H2]. split.
  - intros n Hn. rewrite (proj1 (env_agree_extK E' K ws) n ltac:(lia)). exact (H1 n Hn).
  - rewrite (proj2 (env_agree_extK E' K ws)). exact H2.
Qed.

Lemma cmp_u32_id : forall z, 0 <= z < 2 ^ 32 -> cmp_u32 z = z.
Proof. intros z Hz. unfold cmp_u32. apply Z.mod_small. lia. Qed.

Lemma cmp_hold_range : forall x lo hi, lo <= hi -> lo <= hold_m x lo hi <= hi.
Proof. intros x lo hi H. unfold hold_m. destruct (Z.ltb_spec x lo); destruct (Z.ltb_spec hi x); lia. Qed.

(* one four-byte chunk of a record region *)
Lemma cmp_chunk : forall (E : env) (m : word -> option byte) (n k : nat) (b o x : Z),
  bv_unsigned (ew E n) = b -> ew E k = w64 (cmp_u32 x) -> val_mem segs m (b + o) 4 (cmp_u32 x) ->
  YP09.chunk_ok segs E m b (cmp_ch4 o k).
Proof.
  intros E m n k b o x Hn Hk Hv. unfold cmp_ch4.
  pose proof (Z.mod_pos_bound x (2 ^ 32) ltac:(lia)) as Hr. fold (cmp_u32 x) in Hr.
  apply (chunk_ok_val segs E m b o 4%N (SOff k 0) (cmp_u32 x)).
  - cbn [sv_denot]. rewrite Hk, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - change (8 * Z.of_N 4) with 32. lia.
  - change (Z.of_N 4) with 4. lia.
  - change (N.to_nat 4) with 4%nat. exact Hv.
Qed.

Lemma cmp_entry : forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte)
    (p : rp_hot) (pin F mm pc : Z) (G : facts),
  YK11.getr regs 19 = w64 pin -> YK11.getr regs 21 = Z_to_bv 64 (F + 32) ->
  2 ^ 46 <= pin -> pin + 20 <= 2 ^ 47 -> 4096 <= F -> F + 128 <= alloc_ceiling -> F + 128 <= pin ->
  cells_at rsegs (mrestrict (w_H W) mem) pin (PHC.hot_cells p) ->
  cells_at rsegs (mrestrict (w_H W) mem) (F + 32) (PHC.hot_cells (rp_hot_clamp_m p mm)) ->
  facts_ok (cmp_E regs p mm) G ->
  st_ok_pi segs VAL (cmp_E regs p mm) (cmp_ss pc G)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem p pin F mm pc G R19 R21 Hp1 Hp2 HF1 HF2 HFp Hcp Hcl HG.
  pose proof asan_consts as (C1 & _).
  rewrite restrict_mkst_fx. unfold cmp_ss, cmp_regions.
  assert (U19 : bv_unsigned (ew (cmp_E regs p mm) 19) = pin)
    by (rewrite (cmp_ew_reg regs p mm 19 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
  assert (U21 : bv_unsigned (ew (cmp_E regs p mm) 21) = F + 32)
    by (rewrite (cmp_ew_reg regs p mm 21 21%bv eq_refl), R21; apply unsigned_lit_small; lia).
  assert (VB19 : base_val (cmp_E regs p mm) (Some 19%nat) = pin)
    by (cbn [base_val]; exact U19).
  assert (VB21 : base_val (cmp_E regs p mm) (Some 21%nat) = F + 32)
    by (cbn [base_val]; exact U21).
  apply (@pa_entry_st_ok_full fx rc uci_listing PI_uci).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
    unfold cmp_pin_rg, cmp_loc_rg, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      [ apply (cmp_chunk _ _ 19 33 pin 0 (prefill_ms p))
      | apply (cmp_chunk _ _ 19 34 pin 4 (adapt_min_ms p))
      | apply (cmp_chunk _ _ 19 35 pin 8 (adapt_max_ms p))
      | apply (cmp_chunk _ _ 19 36 pin 12 (adapt_margin p))
      | apply (cmp_chunk _ _ 19 37 pin 16 (servo_clamp_ppm p)) ];
      solve [ exact U19
            | exact (cmp_ew_ex regs p mm 1%nat ltac:(lia)) | exact (cmp_ew_ex regs p mm 2%nat ltac:(lia))
            | exact (cmp_ew_ex regs p mm 3%nat ltac:(lia)) | exact (cmp_ew_ex regs p mm 4%nat ltac:(lia))
            | exact (cmp_ew_ex regs p mm 5%nat ltac:(lia))
            | apply (cmp_hot_val _ pin p); [exact Hcp | cbn [In]; tauto] ].
    + rewrite U21. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      [ apply (cmp_chunk _ _ 21 38 (F + 32) 0 (prefill_ms (rp_hot_clamp_m p mm)))
      | apply (cmp_chunk _ _ 21 39 (F + 32) 4 (adapt_min_ms (rp_hot_clamp_m p mm)))
      | apply (cmp_chunk _ _ 21 40 (F + 32) 8 (adapt_max_ms (rp_hot_clamp_m p mm)))
      | apply (cmp_chunk _ _ 21 41 (F + 32) 12 (adapt_margin (rp_hot_clamp_m p mm)))
      | apply (cmp_chunk _ _ 21 42 (F + 32) 16 (servo_clamp_ppm (rp_hot_clamp_m p mm))) ];
      solve [ exact U21
            | exact (cmp_ew_ex regs p mm 6%nat ltac:(lia)) | exact (cmp_ew_ex regs p mm 7%nat ltac:(lia))
            | exact (cmp_ew_ex regs p mm 8%nat ltac:(lia)) | exact (cmp_ew_ex regs p mm 9%nat ltac:(lia))
            | exact (cmp_ew_ex regs p mm 10%nat ltac:(lia))
            | apply (cmp_hot_val _ (F + 32) (rp_hot_clamp_m p mm)); [exact Hcl | cbn [In]; tauto] ].
  - apply pairwise_disjoint_of_extents.
    unfold cmp_pin_rg, cmp_loc_rg, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite VB19, VB21.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - exact HG.
Qed.

Lemma cmp_shok : forall (W : world segs) regs (mem : word -> option byte) p mm pin,
  YK11.getr regs 24 = w64 SHADOW_OFF -> YK11.getr regs 19 = w64 pin ->
  2 ^ 46 <= pin -> pin + 20 <= 2 ^ 47 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF pin 20 ->
  sh_ok segs cmp_Bx cmp_SH (cmp_E regs p mm) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem p mm pin R24 R19 Hp1 Hp2 HRA.
  apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range segs (w_H W) mem (cmp_E regs p mm) cmp_Bx 19%nat pin 20 pin 0 20).
  - exact HRA.
  - unfold cmp_Bx. apply (U_atom _ 24 SHADOW_OFF); [rewrite (cmp_ew_reg regs p mm 24 24%bv eq_refl); exact R24 | unfold SHADOW_OFF; lia].
  - apply (U_atom _ 19 pin); [rewrite (cmp_ew_reg regs p mm 19 19%bv eq_refl); exact R19 | lia].
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* One run of the engine over a piece that writes no memory and calls nothing. *)
Lemma cmp_run : forall (W : world segs) (E : env) (ss : sstate) (ms : machine_state) (md : Model)
    (K : nat) (stop : Z) (st' : shst) (r : ptrun_status usym) (Q : world segs -> config -> Prop),
  (A_LIM <= K)%nat ->
  img_env VAL A_LIM E ->
  st_ok_pi segs VAL E ss (restrict (w_H W) ms) ->
  sh_ok segs cmp_Bx cmp_SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K cmp_Bx cmp_Bspan cmp_SH (ss_facts ss) (ss_mem ss) = true ->
  sym_run_toN_pi_tok uci_tpi uci_tw K cmp_Bx cmp_Bspan cmp_SH FUEL stop ss = (st', r) ->
  match r with PTS_call _ => False | PTS_ecall => False | _ => True end ->
  Forall (ob_holds segs cmp_Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  rs_read_only (ss_mem ss) = true ->
  (forall ws ms' mat,
     length ws = sh_j st' ->
     img_env VAL A_LIM (extK E K ws) ->
     st_ok_pi segs VAL (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
     sh_ok segs cmp_Bx cmp_SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
     ms_mem ms' = ms_mem ms ->
     SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr segs W (mkCfg ms md) Q.
Proof.
  intros W E ss ms md K stop st' r Q HK HE HS HSH Hchk Hrun Hnc Hobl Hro HKQ.
  assert (Hrun' : sym_run_toN_pi_tok (ptree_of_list uci_listing) (tw_of 0 uci_listing)
                    K cmp_Bx cmp_Bspan cmp_SH FUEL stop ss = (st', r))
    by (rewrite (@pl_tw_eq uci_listing PL_uci); exact Hrun).
  destruct (sym_run_to_pi_tok_sound usym _ _ VAL _ uci_listing
     (pa_fetch_ok (PI := PI_uci)) (@pa_cert _ uci_listing PI_uci) (@pa_B_ok _ uci_listing PI_uci)
     A_LIM A_LIM_text (@pl_lim uci_listing PL_uci) (@pl_len uci_listing PL_uci)
     K cmp_Bx cmp_Bspan cmp_SH HK FUEL stop E ss (restrict (w_H W) ms) st' r HE HS HSH Hchk Hrun' Hobl)
   as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
  apply (SRr_msteps segs (@pa_wx _ uci_listing PI_uci) W ms msr' md Q Hms).
  intros model' Hsame Hcl.
  rewrite (same_but_materialized_wvb md model' Hsame).
  pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
  pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
  assert (Hmem : ms_mem (unrestrict (w_H W) (ms_mem ms) msr') = ms_mem ms).
  { eapply frame_of_read_only; [exact Hro|].
    cbn [unrestrict ms_mem]. apply frame_of_unrestrict.
    cbn [restrict ms_mem] in Hfr. exact Hfr. }
  apply (HKQ ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
  - rewrite Hrr. destruct r as [ | | s | why]; cbn [ptok_post] in HP;
    [exact HP | destruct HP | destruct Hnc | exact HP].
  - rewrite Hmm. exact Hsh'.
  - exact Hmem.
Qed.
(* ------------------------------------------------------------------ *)
(* the environment's slots, and the facts they satisfy                 *)
(* ------------------------------------------------------------------ *)

Definition cmp_ews (E : env) (p : rp_hot) (mm pin F : Z) : Prop :=
  ew E 19 = w64 pin /\ ew E 20 = w64 mm /\ ew E 21 = w64 (F + 32) /\ ew E 24 = w64 SHADOW_OFF /\
  ew E 32 = w64 SHADOW_OFF /\
  ew E 33 = w64 (cmp_u32 (prefill_ms p)) /\ ew E 34 = w64 (cmp_u32 (adapt_min_ms p)) /\
  ew E 35 = w64 (cmp_u32 (adapt_max_ms p)) /\ ew E 36 = w64 (cmp_u32 (adapt_margin p)) /\
  ew E 37 = w64 (cmp_u32 (servo_clamp_ppm p)) /\
  ew E 38 = w64 (cmp_u32 (prefill_ms (rp_hot_clamp_m p mm))) /\
  ew E 39 = w64 (cmp_u32 (adapt_min_ms (rp_hot_clamp_m p mm))) /\
  ew E 40 = w64 (cmp_u32 (adapt_max_ms (rp_hot_clamp_m p mm))) /\
  ew E 41 = w64 (cmp_u32 (adapt_margin (rp_hot_clamp_m p mm))) /\
  ew E 42 = w64 (cmp_u32 (servo_clamp_ppm (rp_hot_clamp_m p mm))).

Lemma cmp_ews_E : forall regs p mm pin F,
  YK11.getr regs 19 = w64 pin -> YK11.getr regs 20 = w64 mm ->
  YK11.getr regs 21 = w64 (F + 32) -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  cmp_ews (cmp_E regs p mm) p mm pin F.
Proof.
  intros regs p mm pin F R19 R20 R21 R24. unfold cmp_ews.
  split; [rewrite (cmp_ew_reg regs p mm 19 19%bv eq_refl); exact R19|].
  split; [rewrite (cmp_ew_reg regs p mm 20 20%bv eq_refl); exact R20|].
  split; [rewrite (cmp_ew_reg regs p mm 21 21%bv eq_refl); exact R21|].
  split; [rewrite (cmp_ew_reg regs p mm 24 24%bv eq_refl); exact R24|].
  split; [exact (cmp_ew_ex regs p mm 0%nat ltac:(lia))|].
  split; [exact (cmp_ew_ex regs p mm 1%nat ltac:(lia))|].
  split; [exact (cmp_ew_ex regs p mm 2%nat ltac:(lia))|].
  split; [exact (cmp_ew_ex regs p mm 3%nat ltac:(lia))|].
  split; [exact (cmp_ew_ex regs p mm 4%nat ltac:(lia))|].
  split; [exact (cmp_ew_ex regs p mm 5%nat ltac:(lia))|].
  split; [exact (cmp_ew_ex regs p mm 6%nat ltac:(lia))|].
  split; [exact (cmp_ew_ex regs p mm 7%nat ltac:(lia))|].
  split; [exact (cmp_ew_ex regs p mm 8%nat ltac:(lia))|].
  split; [exact (cmp_ew_ex regs p mm 9%nat ltac:(lia))|].
  exact (cmp_ew_ex regs p mm 10%nat ltac:(lia)).
Qed.

Lemma cmp_ews_extK : forall E p mm pin F K ws, (43 <= K)%nat ->
  cmp_ews E p mm pin F -> cmp_ews (extK E K ws) p mm pin F.
Proof.
  intros E p mm pin F K ws HK HE.
  assert (Hag : forall n, (n < 43)%nat -> ew (extK E K ws) n = ew E n)
    by (intros n Hn; apply (proj1 (env_agree_extK E K ws)); lia).
  unfold cmp_ews in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; rewrite Hag by lia; assumption.
Qed.

Lemma cmp_clamp_ranges : forall p mm, 0 <= mm <= INT_MAX ->
  1 <= prefill_ms (rp_hot_clamp_m p mm) <= 1000 /\
  1 <= adapt_min_ms (rp_hot_clamp_m p mm) <= 1000 /\
  1 <= adapt_max_ms (rp_hot_clamp_m p mm) <= 1000 /\
  0 <= adapt_margin (rp_hot_clamp_m p mm) <= mm /\
  0 <= servo_clamp_ppm (rp_hot_clamp_m p mm) <= 50000.
Proof.
  intros p mm Hmm.
  pose proof (cmp_hold_range (adapt_min_ms p) 1 1000 ltac:(lia)) as Hmn.
  split; [rewrite clamp_prefill; apply cmp_hold_range; lia|].
  split; [rewrite clamp_adapt_min; apply cmp_hold_range; lia|].
  split; [rewrite clamp_adapt_max;
          pose proof (cmp_hold_range (adapt_max_ms p) (hold_m (adapt_min_ms p) 1 1000) 1000 ltac:(lia)); lia|].
  split; [rewrite clamp_margin by lia; apply cmp_hold_range; lia|].
  rewrite clamp_servo. apply cmp_hold_range. lia.
Qed.

Lemma cmp_u_of_ew : forall (E : env) n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E n) = v.
Proof. intros E n v H Hv. rewrite H. unfold w64. apply unsigned_lit_small. lia. Qed.

Lemma cmp_facts_of : forall (E : env) p mm pin F amin (G : facts),
  cmp_ews E p mm pin F -> 2 ^ 46 <= pin -> pin + 20 <= 2 ^ 47 ->
  4096 <= F -> F + 128 <= alloc_ceiling -> 0 <= mm <= INT_MAX ->
  f_conds G = [] -> f_alias G = [] ->
  (f_atoms G = cmp_atoms \/ (f_atoms G = (11%nat, mkAF 1 1000 0) :: cmp_atoms /\ ew E 11 = w64 amin /\ 1 <= amin <= 1000)) ->
  facts_ok E G.
Proof.
  intros E p mm pin F amin G HEW Hp1 Hp2 HF1 HF2 Hmm Hcd Hal Hat.
  pose proof asan_consts as (C1 & _).
  destruct (cmp_clamp_ranges p mm Hmm) as (Q38 & Q39 & Q40 & Q41 & Q42).
  unfold cmp_ews in HEW.
  destruct HEW as (E19 & E20 & E21 & E24 & E32 & _ & _ & _ & _ & _ & E38 & E39 & E40 & E41 & E42).
  assert (U19 : bv_unsigned (ew E 19) = pin) by (apply (cmp_u_of_ew E 19); [exact E19 | lia]).
  assert (U21 : bv_unsigned (ew E 21) = F + 32) by (apply (cmp_u_of_ew E 21); [exact E21 | lia]).
  assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF)
    by (apply (cmp_u_of_ew E 24); [exact E24 | unfold SHADOW_OFF; lia]).
  assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF)
    by (apply (cmp_u_of_ew E 32); [exact E32 | unfold SHADOW_OFF; lia]).
  assert (U38 : bv_unsigned (ew E 38) = prefill_ms (rp_hot_clamp_m p mm))
    by (apply (cmp_u_of_ew E 38); [rewrite E38, cmp_u32_id by lia; reflexivity | lia]).
  assert (U39 : bv_unsigned (ew E 39) = adapt_min_ms (rp_hot_clamp_m p mm))
    by (apply (cmp_u_of_ew E 39); [rewrite E39, cmp_u32_id by lia; reflexivity | lia]).
  assert (U40 : bv_unsigned (ew E 40) = adapt_max_ms (rp_hot_clamp_m p mm))
    by (apply (cmp_u_of_ew E 40); [rewrite E40, cmp_u32_id by lia; reflexivity | lia]).
  assert (U41 : bv_unsigned (ew E 41) = adapt_margin (rp_hot_clamp_m p mm))
    by (apply (cmp_u_of_ew E 41); [rewrite E41, cmp_u32_id by (unfold INT_MAX in *; lia); reflexivity
                                  | unfold INT_MAX in *; lia]).
  assert (U42 : bv_unsigned (ew E 42) = servo_clamp_ppm (rp_hot_clamp_m p mm))
    by (apply (cmp_u_of_ew E 42); [rewrite E42, cmp_u32_id by lia; reflexivity | lia]).
  unfold facts_ok. rewrite Hcd, Hal.
  destruct Hat as [Hat | (Hat & E11 & Ha)]; rewrite Hat.
  - unfold cmp_atoms. cbn [atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U21, U24, U32, U38, U39, U40, U41, U42.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF, INT_MAX in *; lia.
  - assert (U11 : bv_unsigned (ew E 11) = amin) by (apply (cmp_u_of_ew E 11); [exact E11 | lia]).
    unfold cmp_atoms. cbn [atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U11, U19, U21, U24, U32, U38, U39, U40, U41, U42.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF, INT_MAX in *; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* denotations and branch conditions                                   *)
(* ------------------------------------------------------------------ *)

Lemma cmp_signed_lit : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite signed_lit, zcanon_wrap, (bv_swrap_wrap 64). apply swrap64_id. unfold half64. lia.
Qed.

Lemma cmp_u_den : forall (E : env) a x, sv_denot E a = w64 x -> U E a = zcanon x.
Proof.
  intros E a x H. unfold U. rewrite H. unfold w64. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus, zcanon, M64. change (2 ^ Z.of_N 64) with (2 ^ 64). reflexivity.
Qed.

Lemma cmp_den_atom : forall (E : env) n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n 0) = w64 v.
Proof.
  intros E n v H Hv. cbn [sv_denot]. rewrite H, Z.add_0_r. unfold w64.
  rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma cmp_den_slot : forall (E : env) n x, ew E n = w64 (cmp_u32 x) -> 0 <= x < 2 ^ 32 ->
  sv_denot E (SOff n 0) = w64 x.
Proof.
  intros E n x H Hx. rewrite (cmp_u32_id x) in H by lia. apply (cmp_den_atom E n x H). lia.
Qed.

Lemma cmp_den_lit : forall (E : env) z, sv_denot E (SLit z) = w64 z.
Proof. intros E z. reflexivity. Qed.

Lemma cmp_den_sext : forall (E : env) n x, ew E n = w64 (cmp_u32 x) -> INT_MIN <= x <= INT_MAX ->
  sv_denot E (SExt true 32 (SOff n 0)) = w64 x.
Proof.
  intros E n x Hn Hx. unfold INT_MIN, INT_MAX in Hx.
  pose proof (Z.mod_pos_bound x (2 ^ 32) ltac:(lia)) as Hr. fold (cmp_u32 x) in Hr.
  assert (Ua : U E (SOff n 0) = cmp_u32 x) by (apply (U_atom E n); [exact Hn | lia]).
  rewrite denot_lit_U, U_SExt, Ua. change (Z.of_N 32) with 32.
  replace (cmp_u32 x mod 2 ^ 32) with (x mod 2 ^ 32)
    by (unfold cmp_u32; rewrite (ucc_leafb_mod_pow2_mod x 32 32) by lia; reflexivity).
  rewrite (swrap32_congr (x mod 2 ^ 32) x)
    by (rewrite Zminus_mod_idemp_l, Z.sub_diag; reflexivity).
  rewrite swrap32_id by lia.
  unfold w64. apply Z_to_bv64_canon.
Qed.

Lemma cmp_den_add0 : forall (E : env) a x, sv_denot E a = w64 x -> - 2 ^ 63 <= x < 2 ^ 63 ->
  sv_denot E (SAlu ALU_ADD a (SLit 0)) = w64 x.
Proof.
  intros E a x H Hx. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
  rewrite (cmp_u_den E a x H), U_SLit, (zcanon_id 0) by (unfold M64; lia).
  rewrite Z.add_0_r, !Z_to_bv64_canon. reflexivity.
Qed.

Lemma cmp_bt_lt : forall (E : env) a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  - 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (x <? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite Ha, Hb. cbn [branch_taken].
  rewrite bv_lts_signed. unfold w64. rewrite !cmp_signed_lit by lia. reflexivity.
Qed.

Lemma cmp_bt_ge : forall (E : env) a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  - 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (x <? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite Ha, Hb. cbn [branch_taken].
  rewrite bv_lts_signed. unfold w64. rewrite !cmp_signed_lit by lia. reflexivity.
Qed.

Lemma cmp_modeq : forall x y, - 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
  (x mod 2 ^ 64 =? y mod 2 ^ 64) = (x =? y).
Proof.
  intros x y Hx Hy. destruct (Z.eqb_spec x y) as [->|Hne]; [rewrite Z.eqb_refl; reflexivity|].
  apply Z.eqb_neq. intros H.
  assert (Hd : (x - y) mod 2 ^ 64 = 0)
    by (rewrite Zminus_mod, H, Z.sub_diag; reflexivity).
  apply Z.mod_divide in Hd; [|lia]. destruct Hd as [k Hk]. nia.
Qed.

Lemma cmp_bt_eq : forall (E : env) a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  - 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
  branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = (x =? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite branch_eq_U.
  rewrite (cmp_u_den E a x Ha), (cmp_u_den E b y Hb). unfold zcanon, M64.
  apply cmp_modeq; lia.
Qed.

Lemma cmp_bt_ne : forall (E : env) a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  - 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
  branch_taken BC_NE (sv_denot E a) (sv_denot E b) = negb (x =? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite branch_ne_U.
  rewrite (cmp_u_den E a x Ha), (cmp_u_den E b y Hb). unfold zcanon, M64.
  rewrite cmp_modeq by lia. reflexivity.
Qed.

(* `slti a2, a0, 0` and `slt a2, zero, a0`: the sign mask of an int *)
Lemma cmp_u_slt_r0 : forall (E : env) a x, sv_denot E a = w64 x -> - 2 ^ 63 <= x < 2 ^ 63 ->
  U E (SAlu ALU_SLT a (SLit 0)) = (if x <? 0 then 1 else 0).
Proof.
  intros E a x H Hx. rewrite U_SAlu. cbn [zalu_raw].
  replace (bv_swrap 64 (U E a)) with x.
  2:{ rewrite (cmp_u_den E a x H), zcanon_wrap, (bv_swrap_wrap 64). symmetry. apply swrap64_id.
      unfold half64. lia. }
  replace (bv_swrap 64 (U E (SLit 0))) with 0 by reflexivity.
  destruct (x <? 0); apply zcanon_id; unfold M64; lia.
Qed.

Lemma cmp_u_slt_l0 : forall (E : env) a x, sv_denot E a = w64 x -> - 2 ^ 63 <= x < 2 ^ 63 ->
  U E (SAlu ALU_SLT (SLit 0) a) = (if 0 <? x then 1 else 0).
Proof.
  intros E a x H Hx. rewrite U_SAlu. cbn [zalu_raw].
  replace (bv_swrap 64 (U E a)) with x.
  2:{ rewrite (cmp_u_den E a x H), zcanon_wrap, (bv_swrap_wrap 64). symmetry. apply swrap64_id.
      unfold half64. lia. }
  replace (bv_swrap 64 (U E (SLit 0))) with 0 by reflexivity.
  destruct (0 <? x); apply zcanon_id; unfold M64; lia.
Qed.

Lemma cmp_land_ones : forall v, 0 <= v < 2 ^ 64 -> Z.land (2 ^ 64 - 1) v = v.
Proof.
  intros v Hv. rewrite Z.land_comm. change (2 ^ 64 - 1) with (Z.ones 64).
  rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(* `addi a2,a2,-1 ; and a0,a2,X` after `slti a2,a0,0`: X when the int is >= 0, else 0 *)
Lemma cmp_den_mask_ge0 : forall (E : env) a c x v,
  sv_denot E a = w64 x -> - 2 ^ 63 <= x < 2 ^ 63 -> sv_denot E c = w64 v -> 0 <= v < 2 ^ 63 ->
  sv_denot E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLT a (SLit 0)) (SLit (-1))) c)
  = w64 (if x <? 0 then 0 else v).
Proof.
  intros E a c x v Ha Hx Hc Hv.
  assert (Hadd : U E (SAlu ALU_ADD (SAlu ALU_SLT a (SLit 0)) (SLit (-1)))
                 = (if x <? 0 then 0 else 2 ^ 64 - 1)).
  { rewrite U_SAlu. cbn [zalu_raw]. rewrite (cmp_u_slt_r0 E a x Ha Hx), U_SLit.
    destruct (x <? 0); vm_compute; reflexivity. }
  assert (Hcv : U E c = v) by (rewrite (cmp_u_den E c v Hc); apply zcanon_id; unfold M64; lia).
  rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite Hadd, Hcv.
  destruct (x <? 0).
  - rewrite Z.land_0_l, (zcanon_id 0) by (unfold M64; lia). reflexivity.
  - rewrite cmp_land_ones by lia. rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.

(* the same, when the kept value is the int itself *)
Lemma cmp_den_mask_ge0_self : forall (E : env) a x,
  sv_denot E a = w64 x -> - 2 ^ 63 <= x < 2 ^ 63 ->
  sv_denot E (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_SLT a (SLit 0)) (SLit (-1))) a)
  = w64 (if x <? 0 then 0 else x).
Proof.
  intros E a x Ha Hx.
  assert (Hadd : U E (SAlu ALU_ADD (SAlu ALU_SLT a (SLit 0)) (SLit (-1)))
                 = (if x <? 0 then 0 else 2 ^ 64 - 1)).
  { rewrite U_SAlu. cbn [zalu_raw]. rewrite (cmp_u_slt_r0 E a x Ha Hx), U_SLit.
    destruct (x <? 0); vm_compute; reflexivity. }
  rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite Hadd, (cmp_u_den E a x Ha).
  pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)) as Hm.
  destruct (x <? 0).
  - rewrite Z.land_0_l, (zcanon_id 0) by (unfold M64; lia). reflexivity.
  - rewrite cmp_land_ones by (unfold zcanon, M64; lia).
    rewrite !Z_to_bv64_canon. reflexivity.
Qed.

(* `slt a2,zero,a0 ; sub a2,zero,a2 ; and a0,a2,a0`: the int when it is > 0, else 0 *)
Lemma cmp_den_mask_pos : forall (E : env) a x,
  sv_denot E a = w64 x -> - 2 ^ 63 <= x < 2 ^ 63 ->
  sv_denot E (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) a)) a)
  = w64 (if 0 <? x then x else 0).
Proof.
  intros E a x Ha Hx.
  assert (Hsub : U E (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLT (SLit 0) a))
                 = (if 0 <? x then 2 ^ 64 - 1 else 0)).
  { rewrite U_SAlu. cbn [zalu_raw]. rewrite (cmp_u_slt_l0 E a x Ha Hx), U_SLit.
    destruct (0 <? x); vm_compute; reflexivity. }
  rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite Hsub, (cmp_u_den E a x Ha).
  pose proof (Z.mod_pos_bound x (2 ^ 64) ltac:(lia)) as Hm.
  destruct (0 <? x).
  - rewrite cmp_land_ones by (unfold zcanon, M64; lia).
    rewrite !Z_to_bv64_canon. reflexivity.
  - rewrite Z.land_0_l, (zcanon_id 0) by (unfold M64; lia). reflexivity.
Qed.
(* ------------------------------------------------------------------ *)
(* the five fields                                                     *)
(* ------------------------------------------------------------------ *)

Definition cmp_pre (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte)
    (p : rp_hot) (pin F mm : Z) : Prop :=
  YK11.getr regs 19 = w64 pin /\ YK11.getr regs 20 = w64 mm /\
  YK11.getr regs 21 = w64 (F + 32) /\ YK11.getr regs 24 = w64 SHADOW_OFF /\
  2 ^ 46 <= pin /\ pin + 20 <= 2 ^ 47 /\ 4096 <= F /\ F + 128 <= alloc_ceiling /\ F + 128 <= pin /\
  PHC.hot_int p /\ 0 <= mm <= INT_MAX /\
  cells_at rsegs (mrestrict (w_H W) mem) pin (PHC.hot_cells p) /\
  cells_at rsegs (mrestrict (w_H W) mem) (F + 32) (PHC.hot_cells (rp_hot_clamp_m p mm)) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF pin 20.

Lemma cmp_pre_keep : forall W regs regs' mem p pin F mm,
  cmp_pre W regs mem p pin F mm -> aregs_preserved regs regs' -> cmp_pre W regs' mem p pin F mm.
Proof.
  intros W regs regs' mem p pin F mm HP HR.
  destruct HP as (R19 & R20 & R21 & R24 & HP). unfold cmp_pre.
  split; [transitivity (YK11.getr regs 19); [exact (HR 19 ltac:(unfold acallee_saved; lia)) | exact R19]|].
  split; [transitivity (YK11.getr regs 20); [exact (HR 20 ltac:(unfold acallee_saved; lia)) | exact R20]|].
  split; [transitivity (YK11.getr regs 21); [exact (HR 21 ltac:(unfold acallee_saved; lia)) | exact R21]|].
  split; [transitivity (YK11.getr regs 24); [exact (HR 24 ltac:(unfold acallee_saved; lia)) | exact R24]|].
  exact HP.
Qed.

(* the value of a register of the machine state HS describes *)
Ltac cmp_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

(* the slot values of the current environment *)
Ltac cmp_ew :=
  repeat match goal with H : ew _ _ = _ |- _ => clear H end;
  match goal with HEW : cmp_ews _ _ _ _ _ |- _ =>
    let H := fresh "HX" in pose proof HEW as H;
    destruct H as (Ew19 & Ew20 & Ew21 & Ew24 & Ew32 & Ew33 & Ew34 & Ew35 & Ew36 & Ew37
                   & Ew38 & Ew39 & Ew40 & Ew41 & Ew42)
  end.

(* the one value a merge carries: a1, the held adapt_min_ms *)
Definition cmp_e11 (E : env) (v : Z) : Prop := ew E 11 = w64 v.

Lemma cmp_e11_E : forall regs p mm v, YK11.getr regs 11 = w64 v -> cmp_e11 (cmp_E regs p mm) v.
Proof. intros regs p mm v H. unfold cmp_e11. rewrite (cmp_ew_reg regs p mm 11 11%bv eq_refl). exact H. Qed.

Lemma cmp_e11_extK : forall E v K ws, (12 <= K)%nat -> cmp_e11 E v -> cmp_e11 (extK E K ws) v.
Proof.
  intros E v K ws HK H. unfold cmp_e11 in *.
  rewrite (proj1 (env_agree_extK E K ws) 11%nat ltac:(lia)). exact H.
Qed.

(* one run of the engine, up to the merge pc or to the next undecided branch *)
Ltac cmp_step stop :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) |- SRr _ _ (mkCfg _ ?md) ?Q =>
    let K := eval vm_compute in (run_K A_LIM cmp_Bx cmp_SH ss) in
    let rr := eval vm_compute in (sym_run_toN_pi_tok uci_tpi uci_tw K cmp_Bx cmp_Bspan cmp_SH FUEL stop ss) in
    lazymatch rr with
    | (?st', ?res) =>
      lazymatch goal with
      | HSH : sh_ok _ _ _ E _, HEI : img_env _ _ E |- _ =>
        apply (cmp_run W E ss ms md K stop st' res Q ltac:(unfold A_LIM; lia) HEI HS HSH
                 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) I
                 ltac:(apply Forall_nil) ltac:(vm_compute; reflexivity));
        clear HS HSH HEI;
        let ws := fresh "ws" in let msn := fresh "ms" in let mat := fresh "mat" in
        let Hlen := fresh "Hlen" in let Hm := fresh "Hmem" in
        intros ws msn mat Hlen HEI HS HSH Hm;
        rewrite ?wvb_collapse;
        match goal with HEW : cmp_ews ?Eo ?pp ?mv ?pv ?Fv |- _ =>
          apply (cmp_ews_extK Eo pp mv pv Fv K ws ltac:(lia)) in HEW end;
        match goal with HAE : env_agree 32 ?X ?Eo |- _ =>
          apply (cmp_agree_extK 32 X Eo K ws ltac:(lia)) in HAE end;
        try (match goal with H11 : cmp_e11 ?Eo ?v |- _ =>
          apply (cmp_e11_extK Eo v K ws ltac:(lia)) in H11 end)
      end
    end
  end.

(* the two arms of an undecided branch *)
Ltac cmp_branch :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) |- SRr _ _ (mkCfg _ ?md) ?Q =>
    let K := eval vm_compute in (run_K A_LIM cmp_Bx cmp_SH ss) in
    let why := psym_why_tok uci_tpi uci_tw K cmp_Bx cmp_Bspan cmp_SH (start K cmp_Bx cmp_Bspan cmp_SH ss) in
    lazymatch why with
    | SR_branch ?c ?a ?b =>
      apply (paj_branch (PI := PI_uci) W E ss ms md Q c a b HS); clear HS;
      let Hc := fresh "Hc" in intros Hc HS
    end
  end.

(* the machine state at the merge: its shape and its memory *)
Ltac cmp_shape :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ => pmkst HS end;
  repeat match goal with H : ms_mem ?a = ms_mem ?b |- _ => rewrite H end;
  cbn [ms_mem YK11.mkst].

Ltac cmp_kept regs HPR :=
  lazymatch goal with
  | HS : st_ok_pi ?sg ?vl ?Ex ?ssx (restrict (w_H ?W) ?msx), HAE : env_agree 32 (Ereg regs ?ex) ?Ex |- _ =>
    assert (HPR : aregs_preserved regs (ms_regs msx))
      by (apply (aregs_preserved_of_st_ok segs (w_H W) Ex (abs_ss vl ssx) msx regs ex HS HAE);
          vm_compute; reflexivity)
  end.

Lemma cmp_seg1 : forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (p : rp_hot) (pin F mm : Z) (Q : world segs -> config -> Prop),
  cmp_pre W regs mem p pin F mm ->
  (forall regs' mat, aregs_preserved regs regs' ->
     YK11.getr regs' 11 = w64 (hold_m (adapt_min_ms p) 1 1000) ->
     SRr segs W (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 (BASE + CMP_AT 0x150)) mem (YK11.seg_rom segs))
       (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr segs W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CMP_AT 0x124)) mem (YK11.seg_rom segs)) md) Q.
Proof.
  intros W regs mem md p pin F mm Q HPRE HKQ.
  pose proof HPRE as HP0.
  destruct HP0 as (R19 & R20 & R21 & R24 & Hp1 & Hp2 & HF1 & HF2 & HFp & Hint & Hmm & Hcp & Hcl & HRA).
  pose proof Hint as (Ipf & Imn & Imx & Img & Isv).
  pose proof (cmp_ews_E regs p mm pin F R19 R20 R21 R24) as HEW.
  pose proof (cmp_agree0 regs p mm) as HAE.
  pose proof (cmp_env_img regs p mm) as HEI.
  pose proof (cmp_shok W regs mem p mm pin R24 R19 Hp1 Hp2 HRA) as HSH.
  pose proof (cmp_entry W regs mem p pin F mm (CMP_AT 0x124) cmp_G R19 R21 Hp1 Hp2 HF1 HF2 HFp Hcp Hcl
     (cmp_facts_of (cmp_E regs p mm) p mm pin F 0 cmp_G HEW Hp1 Hp2 HF1 HF2 Hmm eq_refl eq_refl
        (or_introl eq_refl))) as HS.
  cmp_step (CMP_AT 0x150). cmp_branch.
  - (* adapt_min_ms p < 1000 *)
    cmp_ew.
    rewrite (cmp_bt_lt _ _ _ (adapt_min_ms p) 1000 (cmp_den_sext _ 34 _ Ew34 Imn) (cmp_den_lit _ 1000))
      in Hc by (unfold INT_MIN, INT_MAX in *; lia).
    apply Z.ltb_lt in Hc.
    cmp_step (CMP_AT 0x150). cmp_branch.
    + (* 0 < adapt_min_ms p: a1 is the field *)
      cmp_ew.
      rewrite (cmp_bt_lt _ _ _ 0 (adapt_min_ms p) (cmp_den_lit _ 0) (cmp_den_sext _ 34 _ Ew34 Imn))
        in Hc0 by (unfold INT_MIN, INT_MAX in *; lia).
      apply Z.ltb_lt in Hc0.
      cmp_step (CMP_AT 0x150).
      cmp_ew.
      cmp_reg HS (11%bv : bv 5) (w64 (hold_m (adapt_min_ms p) 1 1000)) R11
        ltac:(rewrite (cmp_den_sext _ 34 _ Ew34 Imn); unfold hold_m;
              rewrite (proj2 (Z.ltb_ge (adapt_min_ms p) 1) ltac:(lia)),
                      (proj2 (Z.ltb_ge 1000 (adapt_min_ms p)) ltac:(lia)); reflexivity).
      cmp_kept regs HPR. cmp_shape. apply (HKQ _ _ HPR R11).
    + (* adapt_min_ms p <= 0: a1 is 1 *)
      cmp_ew.
      rewrite (cmp_bt_lt _ _ _ 0 (adapt_min_ms p) (cmp_den_lit _ 0) (cmp_den_sext _ 34 _ Ew34 Imn))
        in Hc0 by (unfold INT_MIN, INT_MAX in *; lia).
      apply Z.ltb_ge in Hc0.
      cmp_step (CMP_AT 0x150).
      cmp_reg HS (11%bv : bv 5) (w64 (hold_m (adapt_min_ms p) 1 1000)) R11
        ltac:(unfold hold_m; rewrite (proj2 (Z.ltb_lt (adapt_min_ms p) 1) ltac:(lia)); reflexivity).
      cmp_kept regs HPR. cmp_shape. apply (HKQ _ _ HPR R11).
  - (* 1000 <= adapt_min_ms p: a1 is 1000 *)
    cmp_ew.
    rewrite (cmp_bt_lt _ _ _ (adapt_min_ms p) 1000 (cmp_den_sext _ 34 _ Ew34 Imn) (cmp_den_lit _ 1000))
      in Hc by (unfold INT_MIN, INT_MAX in *; lia).
    apply Z.ltb_ge in Hc.
    cmp_step (CMP_AT 0x150).
    assert (Hv : hold_m (adapt_min_ms p) 1 1000 = 1000)
      by (unfold hold_m; repeat match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b) end; lia).
    cmp_reg HS (11%bv : bv 5) (w64 (hold_m (adapt_min_ms p) 1 1000)) R11
      ltac:(rewrite Hv; reflexivity).
    cmp_kept regs HPR. cmp_shape. apply (HKQ _ _ HPR R11).
Qed.
Lemma cmp_seg2 : forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (p : rp_hot) (pin F mm amin : Z) (Q : world segs -> config -> Prop),
  cmp_pre W regs mem p pin F mm ->
  amin = hold_m (adapt_min_ms p) 1 1000 ->
  YK11.getr regs 11 = w64 amin ->
  (forall regs' mat, aregs_preserved regs regs' -> YK11.getr regs' 11 = w64 amin ->
     SRr segs W (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 (BASE + CMP_AT 0x194)) mem (YK11.seg_rom segs))
       (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr segs W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CMP_AT 0x150)) mem (YK11.seg_rom segs)) md) Q.
Proof.
  intros W regs mem md p pin F mm amin Q HPRE Hamin R11 HKQ.
  pose proof HPRE as HP0.
  destruct HP0 as (R19 & R20 & R21 & R24 & Hp1 & Hp2 & HF1 & HF2 & HFp & Hint & Hmm & Hcp & Hcl & HRA).
  pose proof Hint as (Ipf & Imn & Imx & Img & Isv).
  pose proof (cmp_hold_range (adapt_min_ms p) 1 1000 ltac:(lia)) as Hmin.
  rewrite <- Hamin in Hmin.
  destruct (cmp_clamp_ranges p mm Hmm) as (Q38 & Q39 & Q40 & Q41 & Q42).
  pose proof (cmp_ews_E regs p mm pin F R19 R20 R21 R24) as HEW.
  pose proof (cmp_e11_E regs p mm amin R11) as HE11.
  pose proof (cmp_agree0 regs p mm) as HAE.
  pose proof (cmp_env_img regs p mm) as HEI.
  pose proof (cmp_shok W regs mem p mm pin R24 R19 Hp1 Hp2 HRA) as HSH.
  pose proof (cmp_entry W regs mem p pin F mm (CMP_AT 0x150) cmp_G1 R19 R21 Hp1 Hp2 HF1 HF2 HFp Hcp Hcl
     (cmp_facts_of (cmp_E regs p mm) p mm pin F amin cmp_G1 HEW Hp1 Hp2 HF1 HF2 Hmm eq_refl eq_refl
        (or_intror (conj eq_refl (conj HE11 Hmin))))) as HS.
  cmp_step (CMP_AT 0x194). cmp_branch.
  - (* 1000 <= prefill_ms p *)
    cmp_ew.
    rewrite (cmp_bt_ge _ _ _ (prefill_ms p) 1000 (cmp_den_sext _ 33 _ Ew33 Ipf) (cmp_den_lit _ 1000))
      in Hc by (unfold INT_MIN, INT_MAX in *; lia).
    apply negb_true_iff, Z.ltb_ge in Hc.
    assert (Hpf : prefill_ms (rp_hot_clamp_m p mm) = 1000)
      by (rewrite clamp_prefill; unfold hold_m;
          repeat match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b) end; lia).
    cmp_step (CMP_AT 0x194). cmp_branch.
    + (* the local's prefill is 1000 *)
      cmp_step (CMP_AT 0x194). cmp_branch.
      * (* the local's adapt_min differs from a1: unreachable *)
        exfalso. cmp_ew.
        rewrite (cmp_bt_ne _ _ _ (adapt_min_ms (rp_hot_clamp_m p mm)) amin
                   (cmp_den_slot _ 39 _ Ew39 ltac:(lia)) (cmp_den_atom _ 11 _ HE11 ltac:(lia)))
          in Hc1 by lia.
        apply negb_true_iff, Z.eqb_neq in Hc1. rewrite clamp_adapt_min in Hc1. lia.
      * cmp_step (CMP_AT 0x194).
        cmp_reg HS (11%bv : bv 5) (w64 amin) R11'
          ltac:(exact (cmp_den_atom _ 11 _ HE11 ltac:(lia))).
        cmp_kept regs HPR. cmp_shape. apply (HKQ _ _ HPR R11').
    + (* the local's prefill differs from 1000: unreachable *)
      exfalso. cmp_ew.
      rewrite (cmp_bt_eq _ _ _ (prefill_ms (rp_hot_clamp_m p mm)) 1000
                 (cmp_den_slot _ 38 _ Ew38 ltac:(lia)) (cmp_den_lit _ 1000)) in Hc0 by lia.
      apply Z.eqb_neq in Hc0. lia.
  - (* prefill_ms p < 1000 *)
    cmp_ew.
    rewrite (cmp_bt_ge _ _ _ (prefill_ms p) 1000 (cmp_den_sext _ 33 _ Ew33 Ipf) (cmp_den_lit _ 1000))
      in Hc by (unfold INT_MIN, INT_MAX in *; lia).
    apply negb_false_iff, Z.ltb_lt in Hc.
    cmp_step (CMP_AT 0x194). cmp_branch.
    + (* prefill_ms p <= 0 *)
      cmp_ew.
      rewrite (cmp_bt_ge _ _ _ 0 (prefill_ms p) (cmp_den_lit _ 0) (cmp_den_sext _ 33 _ Ew33 Ipf))
        in Hc0 by (unfold INT_MIN, INT_MAX in *; lia).
      apply negb_true_iff, Z.ltb_ge in Hc0.
      assert (Hpf : prefill_ms (rp_hot_clamp_m p mm) = 1)
        by (rewrite clamp_prefill; unfold hold_m;
            repeat match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b) end; lia).
      cmp_step (CMP_AT 0x194). cmp_branch.
      * (* the local's prefill differs from 1: unreachable *)
        exfalso. cmp_ew.
        rewrite (cmp_bt_ne _ _ _ (prefill_ms (rp_hot_clamp_m p mm)) 1
                   (cmp_den_slot _ 38 _ Ew38 ltac:(lia)) (cmp_den_lit _ 1)) in Hc1 by lia.
        apply negb_true_iff, Z.eqb_neq in Hc1. lia.
      * cmp_step (CMP_AT 0x194). cmp_branch.
        -- exfalso. cmp_ew.
           rewrite (cmp_bt_ne _ _ _ (adapt_min_ms (rp_hot_clamp_m p mm)) amin
                      (cmp_den_slot _ 39 _ Ew39 ltac:(lia)) (cmp_den_atom _ 11 _ HE11 ltac:(lia)))
             in Hc2 by lia.
           apply negb_true_iff, Z.eqb_neq in Hc2. rewrite clamp_adapt_min in Hc2. lia.
        -- cmp_step (CMP_AT 0x194).
           cmp_reg HS (11%bv : bv 5) (w64 amin) R11'
             ltac:(exact (cmp_den_atom _ 11 _ HE11 ltac:(lia))).
           cmp_kept regs HPR. cmp_shape. apply (HKQ _ _ HPR R11').
    + (* 0 < prefill_ms p < 1000 *)
      cmp_ew.
      rewrite (cmp_bt_ge _ _ _ 0 (prefill_ms p) (cmp_den_lit _ 0) (cmp_den_sext _ 33 _ Ew33 Ipf))
        in Hc0 by (unfold INT_MIN, INT_MAX in *; lia).
      apply negb_false_iff, Z.ltb_lt in Hc0.
      assert (Hpf : prefill_ms (rp_hot_clamp_m p mm) = prefill_ms p)
        by (rewrite clamp_prefill; unfold hold_m;
            repeat match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b) end; lia).
      cmp_step (CMP_AT 0x194). cmp_branch.
      * (* the local's prefill is the field's *)
        cmp_step (CMP_AT 0x194). cmp_branch.
        -- exfalso. cmp_ew.
           rewrite (cmp_bt_ne _ _ _ (adapt_min_ms (rp_hot_clamp_m p mm)) amin
                      (cmp_den_slot _ 39 _ Ew39 ltac:(lia)) (cmp_den_atom _ 11 _ HE11 ltac:(lia)))
             in Hc2 by lia.
           apply negb_true_iff, Z.eqb_neq in Hc2. rewrite clamp_adapt_min in Hc2. lia.
        -- cmp_step (CMP_AT 0x194).
           cmp_reg HS (11%bv : bv 5) (w64 amin) R11'
             ltac:(exact (cmp_den_atom _ 11 _ HE11 ltac:(lia))).
           cmp_kept regs HPR. cmp_shape. apply (HKQ _ _ HPR R11').
      * (* the local's prefill differs from the field's: unreachable *)
        exfalso. cmp_ew.
        rewrite (cmp_bt_eq _ _ _ (prefill_ms (rp_hot_clamp_m p mm)) (prefill_ms p)
                   (cmp_den_slot _ 38 _ Ew38 ltac:(lia)) (cmp_den_sext _ 33 _ Ew33 Ipf))
          in Hc1 by (unfold INT_MIN, INT_MAX in *; lia).
        apply Z.eqb_neq in Hc1. lia.
Qed.
Lemma cmp_seg3 : forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (p : rp_hot) (pin F mm amin : Z) (Q : world segs -> config -> Prop),
  cmp_pre W regs mem p pin F mm ->
  amin = hold_m (adapt_min_ms p) 1 1000 ->
  YK11.getr regs 11 = w64 amin ->
  (forall regs' mat, aregs_preserved regs regs' ->
     SRr segs W (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 (BASE + CMP_AT 0x1d4)) mem (YK11.seg_rom segs))
       (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr segs W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CMP_AT 0x194)) mem (YK11.seg_rom segs)) md) Q.
Proof.
  intros W regs mem md p pin F mm amin Q HPRE Hamin R11 HKQ.
  pose proof HPRE as HP0.
  destruct HP0 as (R19 & R20 & R21 & R24 & Hp1 & Hp2 & HF1 & HF2 & HFp & Hint & Hmm & Hcp & Hcl & HRA).
  pose proof Hint as (Ipf & Imn & Imx & Img & Isv).
  pose proof (cmp_hold_range (adapt_min_ms p) 1 1000 ltac:(lia)) as Hmin.
  rewrite <- Hamin in Hmin.
  destruct (cmp_clamp_ranges p mm Hmm) as (Q38 & Q39 & Q40 & Q41 & Q42).
  assert (Hmx : adapt_max_ms (rp_hot_clamp_m p mm) = hold_m (adapt_max_ms p) amin 1000)
    by (rewrite clamp_adapt_max, <- Hamin; reflexivity).
  pose proof (cmp_ews_E regs p mm pin F R19 R20 R21 R24) as HEW.
  pose proof (cmp_e11_E regs p mm amin R11) as HE11.
  pose proof (cmp_agree0 regs p mm) as HAE.
  pose proof (cmp_env_img regs p mm) as HEI.
  pose proof (cmp_shok W regs mem p mm pin R24 R19 Hp1 Hp2 HRA) as HSH.
  pose proof (cmp_entry W regs mem p pin F mm (CMP_AT 0x194) cmp_G1 R19 R21 Hp1 Hp2 HF1 HF2 HFp Hcp Hcl
     (cmp_facts_of (cmp_E regs p mm) p mm pin F amin cmp_G1 HEW Hp1 Hp2 HF1 HF2 Hmm eq_refl eq_refl
        (or_intror (conj eq_refl (conj HE11 Hmin))))) as HS.
  cmp_step (CMP_AT 0x1d4). cmp_branch.
  - (* 1000 <= adapt_max_ms p *)
    cmp_ew.
    rewrite (cmp_bt_ge _ _ _ (adapt_max_ms p) 1000 (cmp_den_sext _ 35 _ Ew35 Imx) (cmp_den_lit _ 1000))
      in Hc by (unfold INT_MIN, INT_MAX in *; lia).
    apply negb_true_iff, Z.ltb_ge in Hc.
    cmp_step (CMP_AT 0x1d4). cmp_branch.
    + (* adapt_max_ms p < a1: impossible, a1 is at most 1000 *)
      exfalso. cmp_ew.
      rewrite (cmp_bt_lt _ _ _ (adapt_max_ms p) amin (cmp_den_sext _ 35 _ Ew35 Imx)
                 (cmp_den_atom _ 11 _ HE11 ltac:(lia))) in Hc0 by (unfold INT_MIN, INT_MAX in *; lia).
      apply Z.ltb_lt in Hc0. lia.
    + cmp_ew.
      rewrite (cmp_bt_lt _ _ _ (adapt_max_ms p) amin (cmp_den_sext _ 35 _ Ew35 Imx)
                 (cmp_den_atom _ 11 _ HE11 ltac:(lia))) in Hc0 by (unfold INT_MIN, INT_MAX in *; lia).
      apply Z.ltb_ge in Hc0.
      assert (Hv : adapt_max_ms (rp_hot_clamp_m p mm) = 1000)
        by (rewrite Hmx; unfold hold_m;
            repeat match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b) end; lia).
      cmp_step (CMP_AT 0x1d4). cmp_branch.
      * exfalso. cmp_ew.
        rewrite (cmp_bt_ne _ _ _ (adapt_max_ms (rp_hot_clamp_m p mm)) 1000
                   (cmp_den_slot _ 40 _ Ew40 ltac:(lia)) (cmp_den_lit _ 1000)) in Hc1 by lia.
        apply negb_true_iff, Z.eqb_neq in Hc1. lia.
      * cmp_step (CMP_AT 0x1d4). cmp_kept regs HPR. cmp_shape. apply (HKQ _ _ HPR).
  - (* adapt_max_ms p < 1000 *)
    cmp_ew.
    rewrite (cmp_bt_ge _ _ _ (adapt_max_ms p) 1000 (cmp_den_sext _ 35 _ Ew35 Imx) (cmp_den_lit _ 1000))
      in Hc by (unfold INT_MIN, INT_MAX in *; lia).
    apply negb_false_iff, Z.ltb_lt in Hc.
    cmp_step (CMP_AT 0x1d4). cmp_branch.
    + (* a1 <= adapt_max_ms p *)
      cmp_ew.
      rewrite (cmp_bt_ge _ _ _ (adapt_max_ms p) amin (cmp_den_sext _ 35 _ Ew35 Imx)
                 (cmp_den_atom _ 11 _ HE11 ltac:(lia))) in Hc0 by (unfold INT_MIN, INT_MAX in *; lia).
      apply negb_true_iff, Z.ltb_ge in Hc0.
      assert (Hv : adapt_max_ms (rp_hot_clamp_m p mm) = adapt_max_ms p)
        by (rewrite Hmx; unfold hold_m;
            repeat match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b) end; lia).
      cmp_step (CMP_AT 0x1d4). cmp_branch.
      * exfalso. cmp_ew.
        rewrite (cmp_bt_ne _ _ _ (adapt_max_ms (rp_hot_clamp_m p mm)) (adapt_max_ms p)
                   (cmp_den_slot _ 40 _ Ew40 ltac:(lia))
                   (cmp_den_add0 _ _ (adapt_max_ms p) (cmp_den_sext _ 35 _ Ew35 Imx)
                      ltac:(unfold INT_MIN, INT_MAX in *; lia)))
          in Hc1 by (unfold INT_MIN, INT_MAX in *; lia).
        apply negb_true_iff, Z.eqb_neq in Hc1. lia.
      * cmp_step (CMP_AT 0x1d4). cmp_kept regs HPR. cmp_shape. apply (HKQ _ _ HPR).
    + (* adapt_max_ms p < a1 *)
      cmp_ew.
      rewrite (cmp_bt_ge _ _ _ (adapt_max_ms p) amin (cmp_den_sext _ 35 _ Ew35 Imx)
                 (cmp_den_atom _ 11 _ HE11 ltac:(lia))) in Hc0 by (unfold INT_MIN, INT_MAX in *; lia).
      apply negb_false_iff, Z.ltb_lt in Hc0.
      assert (Hv : adapt_max_ms (rp_hot_clamp_m p mm) = amin)
        by (rewrite Hmx; unfold hold_m;
            repeat match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b) end; lia).
      cmp_step (CMP_AT 0x1d4). cmp_branch.
      * cmp_step (CMP_AT 0x1d4). cmp_kept regs HPR. cmp_shape. apply (HKQ _ _ HPR).
      * exfalso. cmp_ew.
        rewrite (cmp_bt_eq _ _ _ (adapt_max_ms (rp_hot_clamp_m p mm)) amin
                   (cmp_den_slot _ 40 _ Ew40 ltac:(lia)) (cmp_den_atom _ 11 _ HE11 ltac:(lia)))
          in Hc1 by lia.
        apply Z.eqb_neq in Hc1. lia.
Qed.

Lemma cmp_seg4 : forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (p : rp_hot) (pin F mm : Z) (Q : world segs -> config -> Prop),
  cmp_pre W regs mem p pin F mm ->
  (forall regs' mat, aregs_preserved regs regs' ->
     SRr segs W (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 (BASE + CMP_AT 0x208)) mem (YK11.seg_rom segs))
       (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr segs W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CMP_AT 0x1d4)) mem (YK11.seg_rom segs)) md) Q.
Proof.
  intros W regs mem md p pin F mm Q HPRE HKQ.
  pose proof HPRE as HP0.
  destruct HP0 as (R19 & R20 & R21 & R24 & Hp1 & Hp2 & HF1 & HF2 & HFp & Hint & Hmm & Hcp & Hcl & HRA).
  pose proof Hint as (Ipf & Imn & Imx & Img & Isv).
  destruct (cmp_clamp_ranges p mm Hmm) as (Q38 & Q39 & Q40 & Q41 & Q42).
  assert (Hmg : adapt_margin (rp_hot_clamp_m p mm) = hold_m (adapt_margin p) 0 mm)
    by (rewrite clamp_margin by lia; reflexivity).
  pose proof (cmp_ews_E regs p mm pin F R19 R20 R21 R24) as HEW.
  pose proof (cmp_agree0 regs p mm) as HAE.
  pose proof (cmp_env_img regs p mm) as HEI.
  pose proof (cmp_shok W regs mem p mm pin R24 R19 Hp1 Hp2 HRA) as HSH.
  pose proof (cmp_entry W regs mem p pin F mm (CMP_AT 0x1d4) cmp_G R19 R21 Hp1 Hp2 HF1 HF2 HFp Hcp Hcl
     (cmp_facts_of (cmp_E regs p mm) p mm pin F 0 cmp_G HEW Hp1 Hp2 HF1 HF2 Hmm eq_refl eq_refl
        (or_introl eq_refl))) as HS.
  cmp_step (CMP_AT 0x208). cmp_branch.
  - (* adapt_margin p < margin_max *)
    cmp_ew.
    rewrite (cmp_bt_lt _ _ _ (adapt_margin p) mm (cmp_den_sext _ 36 _ Ew36 Img)
               (cmp_den_atom _ 20 _ Ew20 ltac:(unfold INT_MAX in *; lia)))
      in Hc by (unfold INT_MIN, INT_MAX in *; lia).
    apply Z.ltb_lt in Hc.
    cmp_step (CMP_AT 0x208). cmp_branch.
    + exfalso. cmp_ew.
      rewrite (cmp_bt_ne _ _ _ (adapt_margin (rp_hot_clamp_m p mm))
                 (if adapt_margin p <? 0 then 0 else adapt_margin p)
                 (cmp_den_slot _ 41 _ Ew41 ltac:(unfold INT_MAX in *; lia))
                 (cmp_den_mask_ge0_self _ _ (adapt_margin p) (cmp_den_sext _ 36 _ Ew36 Img)
                    ltac:(unfold INT_MIN, INT_MAX in *; lia)))
        in Hc0 by (destruct (adapt_margin p <? 0); unfold INT_MIN, INT_MAX in *; lia).
      apply negb_true_iff, Z.eqb_neq in Hc0. rewrite Hmg in Hc0. unfold hold_m in Hc0.
      repeat match goal with H : context [?a <? ?b] |- _ => destruct (Z.ltb_spec a b) end; lia.
    + cmp_step (CMP_AT 0x208). cmp_kept regs HPR. cmp_shape. apply (HKQ _ _ HPR).
  - (* margin_max <= adapt_margin p *)
    cmp_ew.
    rewrite (cmp_bt_lt _ _ _ (adapt_margin p) mm (cmp_den_sext _ 36 _ Ew36 Img)
               (cmp_den_atom _ 20 _ Ew20 ltac:(unfold INT_MAX in *; lia)))
      in Hc by (unfold INT_MIN, INT_MAX in *; lia).
    apply Z.ltb_ge in Hc.
    cmp_step (CMP_AT 0x208). cmp_branch.
    + exfalso. cmp_ew.
      rewrite (cmp_bt_ne _ _ _ (adapt_margin (rp_hot_clamp_m p mm))
                 (if adapt_margin p <? 0 then 0 else mm)
                 (cmp_den_slot _ 41 _ Ew41 ltac:(unfold INT_MAX in *; lia))
                 (cmp_den_mask_ge0 _ _ _ (adapt_margin p) mm (cmp_den_sext _ 36 _ Ew36 Img)
                    ltac:(unfold INT_MIN, INT_MAX in *; lia)
                    (cmp_den_atom _ 20 _ Ew20 ltac:(unfold INT_MAX in *; lia))
                    ltac:(unfold INT_MAX in *; lia)))
        in Hc0 by (destruct (adapt_margin p <? 0); unfold INT_MIN, INT_MAX in *; lia).
      apply negb_true_iff, Z.eqb_neq in Hc0. rewrite Hmg in Hc0. unfold hold_m in Hc0.
      repeat match goal with H : context [?a <? ?b] |- _ => destruct (Z.ltb_spec a b) end; lia.
    + cmp_step (CMP_AT 0x208). cmp_kept regs HPR. cmp_shape. apply (HKQ _ _ HPR).
Qed.

Lemma cmp_seg5 : forall (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (p : rp_hot) (pin F mm : Z) (Q : world segs -> config -> Prop),
  cmp_pre W regs mem p pin F mm ->
  (forall regs' mat, aregs_preserved regs regs' ->
     SRr segs W (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 (BASE + CMP_AT 0x244)) mem (YK11.seg_rom segs))
       (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr segs W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + CMP_AT 0x208)) mem (YK11.seg_rom segs)) md) Q.
Proof.
  intros W regs mem md p pin F mm Q HPRE HKQ.
  pose proof HPRE as HP0.
  destruct HP0 as (R19 & R20 & R21 & R24 & Hp1 & Hp2 & HF1 & HF2 & HFp & Hint & Hmm & Hcp & Hcl & HRA).
  pose proof Hint as (Ipf & Imn & Imx & Img & Isv).
  destruct (cmp_clamp_ranges p mm Hmm) as (Q38 & Q39 & Q40 & Q41 & Q42).
  assert (Hsv : servo_clamp_ppm (rp_hot_clamp_m p mm) = hold_m (servo_clamp_ppm p) 0 50000)
    by (rewrite clamp_servo; reflexivity).
  pose proof (cmp_ews_E regs p mm pin F R19 R20 R21 R24) as HEW.
  pose proof (cmp_agree0 regs p mm) as HAE.
  pose proof (cmp_env_img regs p mm) as HEI.
  pose proof (cmp_shok W regs mem p mm pin R24 R19 Hp1 Hp2 HRA) as HSH.
  pose proof (cmp_entry W regs mem p pin F mm (CMP_AT 0x208) cmp_G R19 R21 Hp1 Hp2 HF1 HF2 HFp Hcp Hcl
     (cmp_facts_of (cmp_E regs p mm) p mm pin F 0 cmp_G HEW Hp1 Hp2 HF1 HF2 Hmm eq_refl eq_refl
        (or_introl eq_refl))) as HS.
  cmp_step (CMP_AT 0x244). cmp_branch.
  - (* servo_clamp_ppm p < 50000 *)
    cmp_ew.
    rewrite (cmp_bt_lt _ _ _ (servo_clamp_ppm p) 50000 (cmp_den_sext _ 37 _ Ew37 Isv)
               (cmp_den_lit _ 50000)) in Hc by (unfold INT_MIN, INT_MAX in *; lia).
    apply Z.ltb_lt in Hc.
    cmp_step (CMP_AT 0x244). cmp_branch.
    + exfalso. cmp_ew.
      rewrite (cmp_bt_ne _ _ _ (servo_clamp_ppm (rp_hot_clamp_m p mm))
                 (if 0 <? servo_clamp_ppm p then servo_clamp_ppm p else 0)
                 (cmp_den_slot _ 42 _ Ew42 ltac:(lia))
                 (cmp_den_mask_pos _ _ (servo_clamp_ppm p) (cmp_den_sext _ 37 _ Ew37 Isv)
                    ltac:(unfold INT_MIN, INT_MAX in *; lia)))
        in Hc0 by (destruct (0 <? servo_clamp_ppm p); unfold INT_MIN, INT_MAX in *; lia).
      apply negb_true_iff, Z.eqb_neq in Hc0. rewrite Hsv in Hc0. unfold hold_m in Hc0.
      repeat match goal with H : context [?a <? ?b] |- _ => destruct (Z.ltb_spec a b) end; lia.
    + cmp_step (CMP_AT 0x244). cmp_kept regs HPR. cmp_shape. apply (HKQ _ _ HPR).
  - (* 50000 <= servo_clamp_ppm p *)
    cmp_ew.
    rewrite (cmp_bt_lt _ _ _ (servo_clamp_ppm p) 50000 (cmp_den_sext _ 37 _ Ew37 Isv)
               (cmp_den_lit _ 50000)) in Hc by (unfold INT_MIN, INT_MAX in *; lia).
    apply Z.ltb_ge in Hc.
    cmp_step (CMP_AT 0x244). cmp_branch.
    + exfalso. cmp_ew.
      rewrite (cmp_bt_ne _ _ _ (servo_clamp_ppm (rp_hot_clamp_m p mm)) 50000
                 (cmp_den_slot _ 42 _ Ew42 ltac:(lia)) (cmp_den_lit _ 50000)) in Hc0 by lia.
      apply negb_true_iff, Z.eqb_neq in Hc0. rewrite Hsv in Hc0. unfold hold_m in Hc0.
      repeat match goal with H : context [?a <? ?b] |- _ => destruct (Z.ltb_spec a b) end; lia.
    + cmp_step (CMP_AT 0x244). cmp_kept regs HPR. cmp_shape. apply (HKQ _ _ HPR).
Qed.

(* ------------------------------------------------------------------ *)
(* the cut                                                             *)
(* ------------------------------------------------------------------ *)

Variable B : asyms.

Lemma cc_cmp : @cc_cmp_stmt fx rc B.
Proof.
  unfold cc_cmp_stmt.
  intros W regs mem md Q lyc Sc memc mdc S2 sp0r pos pin F mm p
    HJ R19 R20 R21 R24 Hp1 Hp2 HF1 HF2 HFp Hint Hmm Hcp Hcl HRA HKQ.
  assert (HP0 : cmp_pre W regs mem p pin F mm).
  { unfold cmp_pre. repeat match goal with |- _ /\ _ => split end; try assumption; lia. }
  apply (cmp_seg1 W regs mem md p pin F mm Q HP0).
  intros regs1 mat1 HR1 Ha1. rewrite ?wvb_collapse.
  pose proof (cmp_pre_keep W regs regs1 mem p pin F mm HP0 HR1) as HP1.
  apply (cmp_seg2 W regs1 mem _ p pin F mm _ Q HP1 eq_refl Ha1).
  intros regs2 mat2 HR2 Ha2. rewrite ?wvb_collapse.
  pose proof (cmp_pre_keep W regs1 regs2 mem p pin F mm HP1 HR2) as HP2.
  apply (cmp_seg3 W regs2 mem _ p pin F mm _ Q HP2 eq_refl Ha2).
  intros regs3 mat3 HR3. rewrite ?wvb_collapse.
  pose proof (cmp_pre_keep W regs2 regs3 mem p pin F mm HP2 HR3) as HP3.
  apply (cmp_seg4 W regs3 mem _ p pin F mm Q HP3).
  intros regs4 mat4 HR4. rewrite ?wvb_collapse.
  pose proof (cmp_pre_keep W regs3 regs4 mem p pin F mm HP3 HR4) as HP4.
  apply (cmp_seg5 W regs4 mem _ p pin F mm Q HP4).
  intros regs5 mat5 HR5. rewrite ?wvb_collapse.
  apply (HKQ regs5 mat5).
  eapply aregs_preserved_trans; [|exact HR5].
  eapply aregs_preserved_trans; [|exact HR4].
  eapply aregs_preserved_trans; [|exact HR3].
  eapply aregs_preserved_trans; [exact HR1 | exact HR2].
Qed.

End cmp.
