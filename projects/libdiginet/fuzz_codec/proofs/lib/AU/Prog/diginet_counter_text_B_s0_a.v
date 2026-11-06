(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:138-139
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh5.v:99 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-117
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:367-369 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8w.v:289-290 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:156-159. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec_A.v, with its module paths and module names changed; 327 of its 365 lines of code are new or changed and 967 lines of the source are left out. *)
(* Segment S0 of diginet_counter_text's walk in image B (fuzz_codec.asan-ubsan 0x869e4), part a: the two states S0
   passes through (ct_s0_r1 at 0x86a5c, after the class-1 frame request; ct_s0_r2 at 0x86b1c, after __asan_memset)
   and the first part, entry -> the request -> its return.
   0x869e4 .. 0x86a58: the real frame 192 (`sd zero,0(sp)` at sp - 192, the 13 saves at sp - 8 .. sp - 104),
   s0 = entry sp, sp = s1 = 32 * ((sp - 192) / 32) = sp1, s3 = dt, 56(s1) = sg (stored before the request, so it is
   carried across it as the saves are), the shadow offset into s10 through the .got slot 0x9e430 and its cell, the
   cell 0x9e488 (it holds 1, so beqz a2 at 0x86a50 is not taken), s6 = q, a0 = 128, jal 0x3d3c0, then
   CPgWalkFrameU.cpg_stack_malloc_keep_io.
   The realigned sp is not an offset of the entry sp, so the store `sd a1,56(s1)` at 0x86a30 has no address the
   engine can place: the walk runs to 0x86a30, pins s1 to the atom 33 that holds sp1 (its value is
   32 * ((sp - 192) / 32), by cw_denot_and_m32), and runs on. The slot 56(s1) is then a region of atom 33; the save
   area [sp - 104, sp) and the zero word at sp - 192 are two regions of atom 2, disjoint from it because
   sp - 208 <= sp1 <= sp - 192. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgEncU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU diginet_counter_text_B_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- small arithmetic and memory facts ---------------------------------------------------------------------- *)
Lemma ct_count_le : forall cid l, count_cid cid l <= Z.of_nat (length l).
Proof. intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|]. destruct (c =? cid); lia. Qed.
Lemma ct_kept_of_frame : forall E rs H (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros E rs H m m' HF a Ha Hn. apply (aview_eq_of tfibsegs). apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma ct_regv : forall (x : word), x = Z_to_bv 64 (bv_unsigned x) /\ 0 <= bv_unsigned x < 2 ^ (8 * Z.of_N 8).
Proof.
intros x. split; [symmetry; apply Z_to_bv_bv_unsigned|].
pose proof (bv_unsigned_in_range _ x) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.
Ltac ct_in := cbn [In]; repeat first [left; reflexivity | right].

(* the zero word the prologue writes at sp - 192, and the slot 56(s1) of the realigned sp (atom 33) *)
Definition ct_zero_region : YP09.region := YP09.mkRegion (Some 2%nat) (-192) (-184) (-192) (-184) [].
Definition ct_sg_region : YP09.region := YP09.mkRegion (Some 33%nat) 56 64 56 64 [].

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.

(* ---- the states S0 passes through ----------------------------------------------------------------------------- *)
(* the thirteen saves of the prologue, as ct_common states them *)
Definition ct_saves (g : ct_ctx) (mem2 : word -> option byte) : Prop :=
  val_mem tfibsegs (rd (cg_W g) mem2) (cg_sp g - 8) 8 (raZ (cg_regs g)) /\
  val_mem tfibsegs (rd (cg_W g) mem2) (cg_sp g - 16) 8 (bv_unsigned (getr (cg_regs g) 8)) /\
  val_mem tfibsegs (rd (cg_W g) mem2) (cg_sp g - 24) 8 (bv_unsigned (getr (cg_regs g) 9)) /\
  val_mem tfibsegs (rd (cg_W g) mem2) (cg_sp g - 32) 8 (bv_unsigned (getr (cg_regs g) 18)) /\
  val_mem tfibsegs (rd (cg_W g) mem2) (cg_sp g - 40) 8 (bv_unsigned (getr (cg_regs g) 19)) /\
  val_mem tfibsegs (rd (cg_W g) mem2) (cg_sp g - 48) 8 (bv_unsigned (getr (cg_regs g) 20)) /\
  val_mem tfibsegs (rd (cg_W g) mem2) (cg_sp g - 56) 8 (bv_unsigned (getr (cg_regs g) 21)) /\
  val_mem tfibsegs (rd (cg_W g) mem2) (cg_sp g - 64) 8 (bv_unsigned (getr (cg_regs g) 22)) /\
  val_mem tfibsegs (rd (cg_W g) mem2) (cg_sp g - 72) 8 (bv_unsigned (getr (cg_regs g) 23)) /\
  val_mem tfibsegs (rd (cg_W g) mem2) (cg_sp g - 80) 8 (bv_unsigned (getr (cg_regs g) 24)) /\
  val_mem tfibsegs (rd (cg_W g) mem2) (cg_sp g - 88) 8 (bv_unsigned (getr (cg_regs g) 25)) /\
  val_mem tfibsegs (rd (cg_W g) mem2) (cg_sp g - 96) 8 (bv_unsigned (getr (cg_regs g) 26)) /\
  val_mem tfibsegs (rd (cg_W g) mem2) (cg_sp g - 104) 8 (bv_unsigned (getr (cg_regs g) 27)).
(* what S0 carries from the request on: the caller's journal with the frame, what the call kept, the write set as
   at entry, the frame new, the model's input, the flag word, the slot 56(s1) = sg, the saves *)
Definition ct_s0_j (g : ct_ctx) (pos : Z) (S2 : astate) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  ajournal tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_W0 g) (cg_mem0 g) (cg_md0 g)
    ((1, pos) :: cg_own g) (cg_lyc g) S2 (cg_W g) mem2 md2 (cg_k g) /\
  tcj_kept tfibsegs B TB_counter_text (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) (cg_W g) mem2 (cg_sp g) (ct_wr g) /\
  (forall a, ct_wr g a -> aview tfibsegs (w_H (cg_W g)) mem2 a = aview tfibsegs (w_H (cg_W g)) (cg_memc g) a) /\
  ablocks B (cg_lyc g) S2 = ablocks B (cg_lyc g) (cg_Sc g) /\ frames S2 = (1, pos) :: frames (cg_Sc g) /\
  ~ In (1, pos) (frames (cg_Sc g)) /\ (exists f, S2 = set_fs f (cg_Sc g)) /\ same_io (cg_mdc g) md2 /\
  rdword (aview tfibsegs (w_H (cg_W g)) mem2) (cg_F g pos + 120) = Some (cg_FL g pos) /\
  val_mem tfibsegs (rd (cg_W g) mem2) (cg_sp1 g + 56) 8 (cg_sg g) /\
  ct_saves g mem2.
(* 0x86a5c, the request's return: a0 = F, the frame's shadow zero *)
Definition ct_s0_r1 (g : ct_ctx) : world tfibsegs -> config -> Prop :=
  fun W2 c2 => W2 = cg_W g /\ exists S2 regs2 mem2 md2 pos,
    c2 = mkCfg (mkst regs2 (Z_to_bv 64 0x86a5c) mem2 (seg_rom tfibsegs)) md2 /\
    ct_s0_j g pos S2 mem2 md2 /\
    zero_shadow (aview tfibsegs (w_H (cg_W g)) mem2) SHADOW_OFF (cg_F g pos) 128 /\
    getr regs2 10 = w64 (cg_F g pos) /\
    getr regs2 2 = w64 (cg_sp1 g) /\ getr regs2 9 = w64 (cg_sp1 g) /\ getr regs2 8 = w64 (cg_sp g) /\
    getr regs2 3 = getr (cg_regs g) 3 /\ getr regs2 4 = getr (cg_regs g) 4 /\
    getr regs2 19 = w64 (cg_dt g) /\ getr regs2 22 = w64 (cg_q g) /\ getr regs2 26 = w64 SB.
(* 0x86b1c, __asan_memset's return: the frame's shadow as CT_FRAME_SHADOW, dot[0..8) zero, 48(s1) = F + 64 *)
Definition ct_s0_r2 (g : ct_ctx) : world tfibsegs -> config -> Prop :=
  fun W2 c2 => W2 = cg_W g /\ exists S2 regs2 mem2 md2 pos,
    c2 = mkCfg (mkst regs2 (Z_to_bv 64 0x86b1c) mem2 (seg_rom tfibsegs)) md2 /\
    ct_s0_j g pos S2 mem2 md2 /\
    garr8 tfibsegs (rd (cg_W g) mem2) (SB + cg_F g pos / 8) CT_FRAME_SHADOW /\
    (forall i, 0 <= i < 8 -> val_mem tfibsegs (rd (cg_W g) mem2) (cg_F g pos + 64 + 4 * i) 4 0) /\
    val_mem tfibsegs (rd (cg_W g) mem2) (cg_sp1 g + 48) 8 (cg_F g pos + 64) /\
    getr regs2 2 = w64 (cg_sp1 g) /\ getr regs2 9 = w64 (cg_sp1 g) /\ getr regs2 8 = w64 (cg_sp g) /\
    getr regs2 3 = getr (cg_regs g) 3 /\ getr regs2 4 = getr (cg_regs g) 4 /\
    getr regs2 18 = w64 (cg_F g pos) /\ getr regs2 20 = w64 (cg_F g pos) /\
    getr regs2 19 = w64 (cg_dt g) /\ getr regs2 22 = w64 (cg_q g) /\
    getr regs2 24 = w64 (SB + cg_F g pos / 8) /\ getr regs2 26 = w64 SB.

(* A byte of the write set lies in a heap block or a frame of the call state, off the call's window. *)
Lemma ct_wr_where : forall g, ct_pre B g -> forall a, ct_wr g a ->
  ((exists b m, In (b, m) (ablocks B (cg_lyc g) (cg_Sc g)) /\ b <= a < b + req_size m) \/
   (exists cid pos, In (cid, pos) (frames (cg_Sc g)) /\ in_zr a (frame_rng (cg_lyc g) (cid, pos)))) /\
  ~ (cg_sp g - TB_counter_text <= a < cg_sp g).
Proof.
intros g Hpre a Ha.
destruct Hpre as (_ & _ & _ & _ & Hsg & _ & _ & _ & Hdt & _).
destruct Hsg as (_ & _ & Tsg & _ & _ & _ & _ & Wsg). destruct Hdt as (_ & _ & Tdt & _ & _ & _ & _ & Wdt).
unfold coff_win in Wsg, Wdt. unfold ct_wr in Ha.
destruct Ha as [Ha | Ha]; [split; [exact (Tsg a Ha) | lia] | split; [exact (Tdt a Ha) | lia]].
Qed.

Section w.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM1 : astack_malloc_realizes tfibsegs B 1.
Hypothesis SMP : stack_malloc_progressP B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.

(* entry -> the class-1 frame request -> its return at 0x86a5c *)
Lemma ct_s0_p1 : forall g, ct_pre B g ->
  SRr tfibsegs (cg_W g) (cfg_at tfibsegs B_CT (cg_regs g) (cg_memc g) (cg_mdc g)) (ct_s0_r1 g).
Proof.
intros [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj] Hpre.
pose proof (ct_wr_where _ Hpre) as HWR.
unfold ct_pre in Hpre.
cbn [cg_STK cg_sp0 cg_FP cg_ly cg_S cg_W0 cg_mem0 cg_md0 cg_own cg_lyc cg_Sc cg_W cg_memc cg_mdc cg_k cg_regs
  cg_q cg_sg cg_dt cg_tb cg_sj cg_dj] in Hpre, HWR |- *.
unfold ct_s0_r1, ct_s0_j, ct_saves, cg_sp, cg_sp1, cg_F, cg_FL, ct_wr in *.
cbn [cg_STK cg_sp0 cg_FP cg_ly cg_S cg_W0 cg_mem0 cg_md0 cg_own cg_lyc cg_Sc cg_W cg_memc cg_mdc cg_k cg_regs
  cg_q cg_sg cg_dt cg_tb cg_sj cg_dj] in HWR |- *.
destruct Hpre as (HE & H10 & Hstr & H11 & Hsg & Hsj & Hsjl & H12 & Hdt & Hdj & Hd1 & Hd2 & Hd3 & Hfr8).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_counter_text HE
  ltac:(unfold TB_counter_text, ESTACK; lia)) as (Hceil & H47 & H46 & Hal & Hpres).
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & _ & Hwlo & Hwhi & Hev & Hlive).
pose proof HJ as (HAR & _).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (TT : TB_counter_text = 4320) by reflexivity. rewrite TT in *.
pose proof (cw_kept0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (spZ regs) 4320
  (fun a => sg <= a < sg + 8 \/ dt <= a < dt + 1) HJ Hwlo Hwhi) as HK.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBguar, HBuar in Kguar. rewrite HBuar in Kuar.
pose proof Hsg as (Hsg0 & Hsg63 & _). pose proof Hdt as (Hdt0 & Hdt63 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
(* the realigned sp *)
set (sp1 := 32 * ((spZ regs - 192) / 32)) in *.
destruct (sp1_facts (spZ regs - 192) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192) by lia. clear Hsp1r.
(* the entry state: the save area [sp - 104, sp), the .got slot and the shadow cell, the zero word at sp - 192,
   the slot 56(s1) of atom 33 = sp1, the use-after-return cell (it holds 1) *)
pose proof (cw_entry B TL LAWS B_CT 104 [sp1] [ct_sg_region; ct_zero_region; uar_got_region; uar_cell_region]
  [(33%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] lyc Sc W regs memc mdc HAR
  ltac:(lia) ltac:(lia) Hal ltac:(intros a Ha; apply Hpres; lia) ltac:(vm_compute; reflexivity)) as HS.
set (E := Ereg regs (cw_extra [sp1])) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 sp1) by (subst E; exact (cw_ew_x regs [sp1] 0)).
assert (U33 : bv_unsigned (ew E 33) = sp1) by (rewrite E33; apply unsigned_lit_small; lia).
specialize (HS ltac:(repeat (apply Forall_cons; [|]); try apply Forall_nil;
  unfold ct_sg_region, ct_zero_region, uar_got_region, uar_cell_region, region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  unfold A_GOT_uar, A_uar_glob;
  first
  [ rewrite U33; (split; [lia|]); (split; [lia|]); (split; [intros o Ho; apply (apresent_writable tfibsegs);
      apply Hpres; lia |]); apply Forall_nil
  | rewrite Usp; (split; [lia|]); (split; [lia|]); (split; [intros o Ho; apply (apresent_writable tfibsegs);
      apply Hpres; lia |]); apply Forall_nil
  | (split; [lia|]); (split; [lia|]); (split; [intros o Ho; lia|]);
    apply Forall_cons; try apply Forall_nil;
    first
    [ apply (chunk_ok_val tfibsegs E _ 0 0x9e488 8 (SLit 0xa6dc0) 0xa6dc0); [reflexivity | zside | zside |];
      rewrite Z.add_0_l; exact (val_mem_of_rdword tfibsegs (w_H W) memc _ _ Kguar)
    | apply (chunk_ok_val tfibsegs E _ 0 0xa6dc0 4 (SLit 1) 1); [reflexivity | zside | zside |];
      rewrite Z.add_0_l; exact (val_mem_of_rd32 tfibsegs (w_H W) memc _ _ Kuar) ] ])).
specialize (HS ltac:(apply pairwise_disjoint_of_extents;
  unfold cw_regs, stack_region, got_region, bcell_region, ct_sg_region, ct_zero_region, uar_got_region,
    uar_cell_region, extent_of_region;
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi]; cbn [base_val]; rewrite Usp, U33;
  unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia)).
specialize (HS ltac:(cbn [atoms_ok]; split; [|exact I]; unfold afact_ok; cbn [af_lo af_hi af_al2];
  rewrite U33; change (2 ^ 5) with 32; split; [lia|]; split; [exact Hsp1al | lia])).
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (B2 := Usp).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E2v : ew E 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (D33 : sv_denot E (SOff 33 0) = Z_to_bv 64 sp1)
  by (cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity).
(* `andi sp,sp,-32` and the `mv s1,sp` that copies it *)
assert (Dand : sv_denot E (SAlu ALU_AND (SOff 2 (-192)) (SLit (-32))) = Z_to_bv 64 sp1)
  by exact (cw_denot_and_m32 E 2 (spZ regs) (-192) E2v ltac:(lia) ltac:(lia) ltac:(unfold spZ in *; lia)).
assert (Dadd : sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-192)) (SLit (-32))) (SLit 0)) = Z_to_bv 64 sp1).
{ change (sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-192)) (SLit (-32))) (SLit 0)))
    with (alu64 ALU_ADD (sv_denot E (SAlu ALU_AND (SOff 2 (-192)) (SLit (-32)))) (sv_denot E (SLit 0))).
  rewrite Dand. cbn [sv_denot]. rewrite YI08.alu64_add_lit, Z.add_0_r. reflexivity. }
clearbody E.
unfold cfg_at. change (w64 B_CT) with (Z_to_bv 64 0x869e4).
(* 0x869e4 .. 0x86a2c: the prologue, stopped before `sd a1,56(s1)` *)
cw_run_to ltac:(cw_awr_anchor 33%nat Usp U33 (spZ regs) sp1 sp0) 0x86a30.
lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2), HG : mem_grows _ _ |- _ =>
  assert (KX1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 192 <= a < spZ regs) ->
    aview tfibsegs H m2 a = aview tfibsegs H m1 a);
  [ intros a Ha Hx; apply (ct_kept_of_frame Ef rs H m1 m2 HFr a Ha); intros (r & Hr & Hb); apply Hx;
    lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
    repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
      rewrite ?B2, ?U33 in Hb; lia | ]);
    destruct Hr
  | ];
  assert (KP1 : forall a, apresent H m1 a -> apresent H m2 a) by (intros a Hp; exact (apresent_grows _ _ _ a HG Hp));
  clear HFr HG
end.
clear_frames.
rename ms into msA.
(* s1 holds sp1: pin it to atom 33, so the store `sd a1,56(s1)` lands in that atom's region *)
rreg_by HS (9%bv : bv 5) (Z_to_bv 64 sp1) Dadd R9a.
assert (R9b : getr (ms_regs msA) (9%bv : bv 5) = sv_denot E (SOff 33 0)) by (rewrite R9a, D33; reflexivity).
pose proof (st_ok_set_reg tfibsegs E _ _ (9%bv : bv 5) (SOff 33 0) HS ltac:(intros Hx; discriminate Hx) R9b) as HS1.
clear HS R9a R9b. rename HS1 into HS. norm_ss HS.
(* 0x86a30 .. jal 0x3d3c0 at 0x86a58: 56(s1) := sg, s10 := SB, the cell 0x9e488 is 1 so beqz a2 is not taken *)
cw_run_to ltac:(cw_awr_anchor 33%nat Usp U33 (spZ regs) sp1 sp0) 0x3d3c0.
lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2), HG : mem_grows _ _ |- _ =>
  assert (KX2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 192 <= a < spZ regs) ->
    aview tfibsegs H m2 a = aview tfibsegs H m1 a);
  [ intros a Ha Hx; apply (ct_kept_of_frame Ef rs H m1 m2 HFr a Ha); intros (r & Hr & Hb); apply Hx;
    lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
    repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
      rewrite ?B2, ?U33 in Hb; lia | ]);
    destruct Hr
  | ];
  assert (KP2 : forall a, apresent H m1 a -> apresent H m2 a) by (intros a Hp; exact (apresent_grows _ _ _ a HG Hp));
  clear HFr HG
end.
clear_frames.
assert (KX : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 192 <= a < spZ regs) ->
  aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) memc a)
  by (intros a Ha Hx; rewrite (KX2 a Ha Hx); exact (KX1 a Ha Hx)).
assert (KP : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Hp; apply KP2; apply KP1; exact Hp).
clear KX1 KX2 KP1 KP2.
assert (HK1 : tcj_kept tfibsegs B 4320 lyc Sc W memc W (ms_mem ms) (spZ regs)
  (fun a => sg <= a < sg + 8 \/ dt <= a < dt + 1)).
{ apply (cw_kept_step B LAWS 4320 lyc Sc W memc mdc W memc (ms_mem ms) (spZ regs) _
    (fun a => spZ regs - 192 <= a < spZ regs) ltac:(lia) HAR HK KX); [|exact KP].
  intros a Ha. cbv beta in Ha. left. lia. }
clear HK.
(* the registers and the memory at the request *)
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1) Dand R2.
rreg_by HS (9%bv : bv 5) (Z_to_bv 64 sp1) D33 R9.
rreg HS (1%bv : bv 5) R1. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4. rreg HS (8%bv : bv 5) R8.
rreg HS (19%bv : bv 5) R19. rreg HS (22%bv : bv 5) R22. rreg HS (26%bv : bv 5) R26.
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as RG0.
pose proof (st_ok_region_nth E _ _ 3 _ HS eq_refl) as RG3.
cbn [ms_mem restrict] in RG0, RG3.
assert (VS : forall (i : nat) (r : bv 5) od, Z.of_nat i = bv_unsigned r ->
   In (YP09.mkChunk od (CVal 8 (SOff i 0)))
     [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
      YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
      YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
      YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
      YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
      YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
      YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
   val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + od) 8 (bv_unsigned (getr regs r))).
{ intros i r od Hir Hc. rewrite <- Usp.
  lazymatch type of RG0 with region_ok _ _ _ ?rg =>
    let rg' := eval vm_compute in rg in change rg with rg' in RG0 end.
  eapply (cw_fld E _ 2 _ _ _ _ _ _ od 8%N i (bv_unsigned (getr regs r)) RG0 eq_refl);
  [ cbn [In] in Hc; repeat (destruct Hc as [Hc | Hc]; [rewrite <- Hc; ct_in |]); destruct Hc
  | rewrite (EE i r Hir); exact (proj1 (ct_regv _)) | exact (proj2 (ct_regv _)) | lia ]. }
pose proof (VS 1%nat 1%bv (-8) eq_refl ltac:(ct_in)) as V1.
pose proof (VS 8%nat 8%bv (-16) eq_refl ltac:(ct_in)) as V8.
pose proof (VS 9%nat 9%bv (-24) eq_refl ltac:(ct_in)) as V9.
pose proof (VS 18%nat 18%bv (-32) eq_refl ltac:(ct_in)) as V18.
pose proof (VS 19%nat 19%bv (-40) eq_refl ltac:(ct_in)) as V19.
pose proof (VS 20%nat 20%bv (-48) eq_refl ltac:(ct_in)) as V20.
pose proof (VS 21%nat 21%bv (-56) eq_refl ltac:(ct_in)) as V21.
pose proof (VS 22%nat 22%bv (-64) eq_refl ltac:(ct_in)) as V22.
pose proof (VS 23%nat 23%bv (-72) eq_refl ltac:(ct_in)) as V23.
pose proof (VS 24%nat 24%bv (-80) eq_refl ltac:(ct_in)) as V24.
pose proof (VS 25%nat 25%bv (-88) eq_refl ltac:(ct_in)) as V25.
pose proof (VS 26%nat 26%bv (-96) eq_refl ltac:(ct_in)) as V26.
pose proof (VS 27%nat 27%bv (-104) eq_refl ltac:(ct_in)) as V27.
clear VS RG0.
(* the slot 56(s1): the sg the prologue stored there *)
assert (VSG : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp1 + 56) 8 sg).
{ rewrite <- U33.
  lazymatch type of RG3 with region_ok _ _ _ ?rg =>
    let rg' := eval vm_compute in rg in change rg with rg' in RG3 end.
  replace sg with (bv_unsigned (getr regs 11))
    by (rewrite H11; unfold w64; apply unsigned_lit_small; lia).
  eapply (cw_fld E _ 33 _ _ _ _ _ _ 56 8%N 11%nat (bv_unsigned (getr regs 11)) RG3 eq_refl);
  [ ct_in | rewrite (EE 11%nat 11%bv eq_refl); exact (proj1 (ct_regv _)) | exact (proj2 (ct_regv _)) | lia ]. }
clear RG3.
(* 0x3d3c0: the class-1 frame request *)
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 250816 with (pc_stack_malloc (as_code B) 1) by (rewrite HBcode; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (cpg_stack_malloc_keep_io tfibsegs B LAWS Hsegs errno_low ML SMP 1 ASM1 ltac:(lia) W (ms_regs msX) (ms_mem msX)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ HJ) end.
  - unfold spZ at 1. rewrite R2. rewrite unsigned_lit_small by lia. lia.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hsp0al. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - vm_compute. reflexivity.
  - change (fs_frames 1) with 8192. pose proof (ct_count_le 1 (frames Sc)). lia. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag
  & HKa & HSf & HKr & Hio).
replace (sp0 + (sp1 - sp0) - ESTACK) with (sp1 - 4096) in HKa by (unfold ESTACK; lia).
replace (sp0 + (sp1 - sp0)) with sp1 in HKa by lia.
assert (CS : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r)) by exact HP2.
assert (KA : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - 4096 <= a < sp1) ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) (ms_mem ms) a) by exact (proj1 HKa).
assert (KV : forall a n v, sp1 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
   val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) a n v ->
   val_mem tfibsegs (mrestrict (w_H W) mem2) a n v).
{ intros a n v H1 H2 Hv. apply (cw_val_mem_kept (w_H W) (w_H W) (ms_mem ms) mem2 a n v); [|exact Hv].
  intros x Hx. apply KA; [lia | lia]. }
assert (KS : forall od vv, -104 <= od <= -8 ->
   val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + od) 8 vv ->
   val_mem tfibsegs (mrestrict (w_H W) mem2) (spZ regs - - od) 8 vv).
{ intros od vv Hod Hvv. replace (spZ regs - - od) with (spZ regs + od) by lia.
  apply KV; [lia | cbn; lia | exact Hvv]. }
apply SRr_ret. split; [reflexivity|].
exists S2, regs2, mem2, md2, pos.
split; [reflexivity|].
split; [split; [exact HJ2|]|].
{ split.
  { apply (cw_kept_call B 4320 lyc Sc W memc W (ms_mem ms) mem2 (spZ regs) (sp1 - 4096) sp1 _
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HK1 HKa). }
  split.
  { intros a Ha. destruct (HWR a Ha) as ([(b & m & Hin & Hr) | (cid & p & Hin & Hr)] & Hw).
    - pose proof HKa as (_ & A2 & _).
      replace a with (b + (a - b)) by lia.
      rewrite (A2 b m (a - b) Hin ltac:(lia) (fun H => H)). replace (b + (a - b)) with a by lia.
      apply KX; [destruct Ha; lia | lia].
    - pose proof HKa as (_ & _ & _ & A4 & _).
      rewrite (A4 cid p a Hin (or_introl Hr) (fun H => H)).
      apply KX; [destruct Ha; lia | lia]. }
  split; [exact Eab|]. split; [exact Hfrs2|]. split; [exact Hnin|]. split; [exact HSf|].
  split; [eapply same_io_trans; [apply cw_same_io_wvb | exact Hio]|].
  split.
  { change (fs_frame_bytes 1) with 128 in Hflag.
    replace (frame_addr lyc 1 pos + 128 - 8) with (frame_addr lyc 1 pos + 120) in Hflag by lia. exact Hflag. }
  split; [exact (KV (sp1 + 56) 8%nat sg ltac:(lia) ltac:(cbn; lia) VSG)|].
  split; [exact (KS (-8) _ ltac:(lia) V1)|].
  split; [exact (KS (-16) _ ltac:(lia) V8)|].
  split; [exact (KS (-24) _ ltac:(lia) V9)|].
  split; [exact (KS (-32) _ ltac:(lia) V18)|].
  split; [exact (KS (-40) _ ltac:(lia) V19)|].
  split; [exact (KS (-48) _ ltac:(lia) V20)|].
  split; [exact (KS (-56) _ ltac:(lia) V21)|].
  split; [exact (KS (-64) _ ltac:(lia) V22)|].
  split; [exact (KS (-72) _ ltac:(lia) V23)|].
  split; [exact (KS (-80) _ ltac:(lia) V24)|].
  split; [exact (KS (-88) _ ltac:(lia) V25)|].
  split; [exact (KS (-96) _ ltac:(lia) V26)|].
  exact (KS (-104) _ ltac:(lia) V27). }
split; [change (fs_frame_bytes 1) with 128 in Hz; exact Hz|].
split; [exact Ha0|].
assert (P2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (CS 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3 = getr (ms_regs ms) 3) by exact (CS 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4 = getr (ms_regs ms) 4) by exact (CS 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr (ms_regs ms) 8) by exact (CS 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9 = getr (ms_regs ms) 9) by exact (CS 9 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs2 19 = getr (ms_regs ms) 19) by exact (CS 19 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs2 22 = getr (ms_regs ms) 22) by exact (CS 22 ltac:(unfold acallee_saved; lia)).
assert (P26 : getr regs2 26 = getr (ms_regs ms) 26) by exact (CS 26 ltac:(unfold acallee_saved; lia)).
split; [rewrite P2; exact R2|].
split; [rewrite P9; exact R9|].
split; [rewrite P8, R8, E2v; reflexivity|].
split; [rewrite P3, R3; exact (EE 3%nat 3%bv eq_refl)|].
split; [rewrite P4, R4; exact (EE 4%nat 4%bv eq_refl)|].
split; [rewrite P19, R19, (EE 12%nat 12%bv eq_refl); exact H12|].
split; [rewrite P22, R22, (EE 10%nat 10%bv eq_refl); exact H10|].
rewrite P26, R26. exact E32.
Qed.
End w.
End s.
