(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:155-159
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbl.v:141-145 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:140-148, 156-160 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-370
   [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used
   under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_A.v, with its module paths and module names changed; 380 of its 427 lines of code are new or changed and 761 lines of the source are left out. *)
(* Segment S0 of owed_counter_text's walk in image B (fuzz_codec.asan-ubsan 0x84474), part a: the two states S0 passes
   through (oc_s0_r1 at 0x844ec, after the class-1 frame request; oc_s0_r2 at 0x845b8, after __asan_memset) and the
   first part, entry -> the request -> its return.
   0x84474 .. 0x844b8: the real frame 192 (`sd zero,0(sp)`, 13 saves), s0 = entry sp, sp = s1 = 32 * ((sp - 192) / 32);
   one run to 0x844bc, then sp1 into atom 70 (the store 48(s1) needs a base the engine names). 0x844bc .. 0x844e8:
   s2 = dt, 48(s1) := sg, the shadow offset into s7 through the .got slot 0x9e430 and its cell, the cell 0x9e488 (it
   holds 1, so beqz a2 at 0x844e0 is not taken), s4 = q, a0 = 128, jal 0x3d3c0: one run to the request, then
   CPgWalkFrameU.cpg_stack_malloc_keep_io. The form is lib/A/Prog/diginet_counter_text_A_s0_a.v's. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU owed_counter_text_B_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- small arithmetic and memory facts ---------------------------------------------------------------------- *)
Lemma oc_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma oc_count_le : forall cid l, count_cid cid l <= Z.of_nat (length l).
Proof. intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|]. destruct (c =? cid); lia. Qed.
Lemma oc_kept_of_frame : forall E rs H (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros E rs H m m' HF a Ha Hn. apply (aview_eq_of tfibsegs). apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.
(* a field of a region whose chunk is an atom with a known value *)
Lemma oc_fld : forall E m n bse cs lo hi wlo whi od (w : N) i v,
  region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = bse ->
  In (YP09.mkChunk od (CVal w (SOff i 0))) cs -> ew E i = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
  Z.of_N w <= 8 ->
  val_mem tfibsegs m (bse + od) (N.to_nat w) v.
Proof.
intros E m n bse cs lo hi wlo whi od w i v Hr Hb Hc Hi Hv Hw.
eapply (field_of_region E m n bse cs lo hi wlo whi od w (SOff i 0) v Hr Hb Hc); [|exact Hv | exact Hw].
cbn [sv_denot]. rewrite Hi, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma oc_regv : forall (x : word), x = Z_to_bv 64 (bv_unsigned x) /\ 0 <= bv_unsigned x < 2 ^ (8 * Z.of_N 8).
Proof.
intros x. split; [symmetry; apply Z_to_bv_bv_unsigned|].
pose proof (bv_unsigned_in_range _ x) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.
Ltac oc_in := cbn [In]; repeat first [left; reflexivity | right].
(* the index of the region based at atom n in a state *)
Ltac oc_ridx HS n :=
  lazymatch type of HS with st_ok _ _ ?ss _ => let rs := eval vm_compute in (ss_mem ss) in idx_of_base rs n end.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.

(* ---- the states S0 passes through ----------------------------------------------------------------------------- *)
(* the thirteen saves of the prologue, as oc_common states them *)
Definition oc_saves (g : oc_ctx) (mem2 : word -> option byte) : Prop :=
  val_mem tfibsegs (rd (og_W g) mem2) (og_sp g - 8) 8 (raZ (og_regs g)) /\
  val_mem tfibsegs (rd (og_W g) mem2) (og_sp g - 16) 8 (bv_unsigned (getr (og_regs g) 8)) /\
  val_mem tfibsegs (rd (og_W g) mem2) (og_sp g - 24) 8 (bv_unsigned (getr (og_regs g) 9)) /\
  val_mem tfibsegs (rd (og_W g) mem2) (og_sp g - 32) 8 (bv_unsigned (getr (og_regs g) 18)) /\
  val_mem tfibsegs (rd (og_W g) mem2) (og_sp g - 40) 8 (bv_unsigned (getr (og_regs g) 19)) /\
  val_mem tfibsegs (rd (og_W g) mem2) (og_sp g - 48) 8 (bv_unsigned (getr (og_regs g) 20)) /\
  val_mem tfibsegs (rd (og_W g) mem2) (og_sp g - 56) 8 (bv_unsigned (getr (og_regs g) 21)) /\
  val_mem tfibsegs (rd (og_W g) mem2) (og_sp g - 64) 8 (bv_unsigned (getr (og_regs g) 22)) /\
  val_mem tfibsegs (rd (og_W g) mem2) (og_sp g - 72) 8 (bv_unsigned (getr (og_regs g) 23)) /\
  val_mem tfibsegs (rd (og_W g) mem2) (og_sp g - 80) 8 (bv_unsigned (getr (og_regs g) 24)) /\
  val_mem tfibsegs (rd (og_W g) mem2) (og_sp g - 88) 8 (bv_unsigned (getr (og_regs g) 25)) /\
  val_mem tfibsegs (rd (og_W g) mem2) (og_sp g - 96) 8 (bv_unsigned (getr (og_regs g) 26)) /\
  val_mem tfibsegs (rd (og_W g) mem2) (og_sp g - 104) 8 (bv_unsigned (getr (og_regs g) 27)).
(* what S0 carries from the request on: the caller's journal with the frame, what the call kept, the write set as
   at entry, the frame new, the model's input, the flag word, the saves, the spill of sg at 48(s1) *)
Definition oc_s0_j (g : oc_ctx) (pos : Z) (S2 : astate) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  ajournal tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    ((1, pos) :: og_own g) (og_lyc g) S2 (og_W g) mem2 md2 (og_k g) /\
  tcj_kept tfibsegs B TB_owed_counter_text (og_lyc g) (og_Sc g) (og_W g) (og_memc g) (og_W g) mem2 (og_sp g) (oc_wr g) /\
  (forall a, oc_wr g a -> aview tfibsegs (w_H (og_W g)) mem2 a = aview tfibsegs (w_H (og_W g)) (og_memc g) a) /\
  ablocks B (og_lyc g) S2 = ablocks B (og_lyc g) (og_Sc g) /\ frames S2 = (1, pos) :: frames (og_Sc g) /\
  ~ In (1, pos) (frames (og_Sc g)) /\ (exists f, S2 = set_fs f (og_Sc g)) /\ same_io (og_mdc g) md2 /\
  rdword (aview tfibsegs (w_H (og_W g)) mem2) (og_F g pos + 120) = Some (og_FL g pos) /\
  oc_saves g mem2 /\
  val_mem tfibsegs (rd (og_W g) mem2) (og_sp1 g + 48) 8 (og_sg g).
(* 0x844ec, the request's return: a0 = F, the frame's shadow zero *)
Definition oc_s0_r1 (g : oc_ctx) : world tfibsegs -> config -> Prop :=
  fun W2 c2 => W2 = og_W g /\ exists S2 regs2 mem2 md2 pos,
    c2 = mkCfg (mkst regs2 (Z_to_bv 64 0x844ec) mem2 (seg_rom tfibsegs)) md2 /\
    oc_s0_j g pos S2 mem2 md2 /\
    zero_shadow (aview tfibsegs (w_H (og_W g)) mem2) SHADOW_OFF (og_F g pos) 128 /\
    getr regs2 10 = w64 (og_F g pos) /\
    getr regs2 2 = w64 (og_sp1 g) /\ getr regs2 9 = w64 (og_sp1 g) /\ getr regs2 8 = w64 (og_sp g) /\
    getr regs2 3 = getr (og_regs g) 3 /\ getr regs2 4 = getr (og_regs g) 4 /\
    getr regs2 18 = w64 (og_dt g) /\ getr regs2 20 = w64 (og_q g) /\ getr regs2 23 = w64 SB.
(* 0x845b8, __asan_memset's return: the frame's shadow as OC_FRAME_SHADOW, dot[0..8) zero, the spills of the frame
   and of dt *)
Definition oc_s0_r2 (g : oc_ctx) : world tfibsegs -> config -> Prop :=
  fun W2 c2 => W2 = og_W g /\ exists S2 regs2 mem2 md2 pos,
    c2 = mkCfg (mkst regs2 (Z_to_bv 64 0x845b8) mem2 (seg_rom tfibsegs)) md2 /\
    oc_s0_j g pos S2 mem2 md2 /\
    garr8 tfibsegs (rd (og_W g) mem2) (SB + og_F g pos / 8) OC_FRAME_SHADOW /\
    (forall i, 0 <= i < 8 -> val_mem tfibsegs (rd (og_W g) mem2) (og_F g pos + 64 + 4 * i) 4 0) /\
    val_mem tfibsegs (rd (og_W g) mem2) (og_sp1 g + 24) 8 (og_F g pos) /\
    val_mem tfibsegs (rd (og_W g) mem2) (og_sp1 g + 32) 8 (og_F g pos) /\
    val_mem tfibsegs (rd (og_W g) mem2) (og_sp1 g + 40) 8 (og_dt g) /\
    val_mem tfibsegs (rd (og_W g) mem2) (og_sp1 g + 80) 8 (og_F g pos) /\
    getr regs2 2 = w64 (og_sp1 g) /\ getr regs2 9 = w64 (og_sp1 g) /\ getr regs2 8 = w64 (og_sp g) /\
    getr regs2 3 = getr (og_regs g) 3 /\ getr regs2 4 = getr (og_regs g) 4 /\
    getr regs2 20 = w64 (og_q g) /\ getr regs2 21 = w64 (og_F g pos + 64) /\ getr regs2 22 = w64 (og_F g pos + 32) /\
    getr regs2 23 = w64 SB /\ getr regs2 26 = w64 (SB + og_F g pos / 8).

(* A byte of the write set lies in a heap block, a frame of the call state or the caller's machine stack, off the
   call's window. *)
Lemma oc_wr_win : forall g, oc_pre B g -> forall a, oc_wr g a -> ~ (og_sp g - TB_owed_counter_text <= a < og_sp g).
Proof.
intros g Hpre a Ha.
destruct Hpre as (_ & _ & _ & _ & Hsg & _ & _ & _ & Hdt & _).
destruct Hsg as (_ & _ & _ & _ & _ & _ & _ & Wsg).
assert (Wdt : coff_win (og_sp g) TB_owed_counter_text (og_dt g) 1)
  by (destruct Hdt as [((_ & _ & _ & _ & _ & _ & _ & W) & _) | (_ & _ & _ & _ & _ & _ & _ & _ & W)]; exact W).
unfold coff_win in Wsg, Wdt. unfold oc_wr in Ha. destruct Ha as [Ha | Ha]; lia.
Qed.

(* Where a byte of the write set lies: a heap block or a frame of the call state, or (dt) the caller's machine
   stack, which lies above the allocator ceiling. *)
Lemma oc_wr_where : forall g, oc_pre B g -> forall a, oc_wr g a ->
  (exists b m, In (b, m) (ablocks B (og_lyc g) (og_Sc g)) /\ b <= a < b + req_size m) \/
  (exists cid pos, In (cid, pos) (frames (og_Sc g)) /\ in_zr a (frame_rng (og_lyc g) (cid, pos))) \/
  (alloc_ceiling <= a < 2 ^ 47).
Proof.
intros g Hpre a Ha.
destruct Hpre as ((HJ & _) & _ & _ & _ & Hsg & _ & _ & _ & Hdt & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hstk as (_ & _ & Hsceil & _ & _ & HS47 & _).
destruct Ha as [Ha | Ha].
- destruct Hsg as (_ & _ & Htd & _). destruct (Htd a Ha) as [H | H]; [left; exact H | right; left; exact H].
- destruct Hdt as [((_ & _ & Htd & _) & _) | (_ & _ & Hlo & Hhi & _)].
  + destruct (Htd a Ha) as [H | H]; [left; exact H | right; left; exact H].
  + right; right. lia.
Qed.

Section w.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM1 : astack_malloc_realizes tfibsegs B 1.
Hypothesis SMP : stack_malloc_progressP B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.

(* entry -> the class-1 frame request -> its return at 0x844ec *)
Lemma oc_s0_p1 : forall g, oc_pre B g ->
  SRr tfibsegs (og_W g) (cfg_at tfibsegs B_OCT (og_regs g) (og_memc g) (og_mdc g)) (oc_s0_r1 g).
Proof.
intros [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj] Hpre.
pose proof Hpre as Hpre0.
pose proof (oc_wr_win _ Hpre) as HWR.
unfold oc_pre in Hpre.
cbn [og_STK og_sp0 og_FP og_ly og_S og_W0 og_mem0 og_md0 og_own og_lyc og_Sc og_W og_memc og_mdc og_k og_regs
  og_q og_sg og_dt og_tb og_sj og_dj] in Hpre, HWR |- *.
unfold oc_s0_r1, oc_s0_j, oc_saves, og_sp, og_sp1, og_F, og_FL, oc_wr in *.
cbn [og_STK og_sp0 og_FP og_ly og_S og_W0 og_mem0 og_md0 og_own og_lyc og_Sc og_W og_memc og_mdc og_k og_regs
  og_q og_sg og_dt og_tb og_sj og_dj] in HWR |- *.
destruct Hpre as (HE & H10 & Hstr & H11 & Hsg & Hsj & Hsjl & H12 & Hdt & Hdj & Hd1 & Hd2 & Hd3 & Hfr8).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_owed_counter_text HE
  ltac:(unfold TB_owed_counter_text, ESTACK; lia)) as (Hceil & H47 & H46 & Hal & Hpres).
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & _ & Hwlo & Hwhi & Hev & Hlive).
pose proof HJ as (HAR & _).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (TT : TB_owed_counter_text = 4320) by reflexivity. rewrite TT in *.
pose proof (cw_kept0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (spZ regs) 4320
  (fun a => sg <= a < sg + 8 \/ dt <= a < dt + 1) HJ Hwlo Hwhi) as HK.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBguar, HBuar in Kguar. rewrite HBuar in Kuar.
pose proof (cw_entry B TL LAWS B_OCT 224 [] [uar_got_region; uar_cell_region] [] lyc Sc W regs memc mdc HAR
  ltac:(lia) ltac:(lia) Hal ltac:(intros a Ha; apply Hpres; lia) ltac:(vm_compute; reflexivity)) as HS.
remember (Ereg regs (cw_extra [])) as E eqn:HE0 in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
specialize (HS ltac:(apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  unfold region_ok, uar_got_region, uar_cell_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  unfold A_GOT_uar, A_uar_glob; (split; [lia|]); (split; [lia|]); (split; [intros o Ho; lia|]);
  apply Forall_cons; try apply Forall_nil;
  first
  [ apply (chunk_ok_val tfibsegs E _ 0 0x9e488 8 (SLit 0xa6dc0) 0xa6dc0); [reflexivity | zside | zside |];
    rewrite Z.add_0_l; exact (val_mem_of_rdword tfibsegs (w_H W) memc _ _ Kguar)
  | apply (chunk_ok_val tfibsegs E _ 0 0xa6dc0 4 (SLit 1) 1); [reflexivity | zside | zside |];
    rewrite Z.add_0_l; exact (val_mem_of_rd32 tfibsegs (w_H W) memc _ _ Kuar) ])).
specialize (HS ltac:(apply pairwise_disjoint_of_extents;
  unfold cw_regs, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, extent_of_region;
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi]; cbn [base_val]; rewrite Usp;
  unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia)).
specialize (HS I).
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (B2 := Usp).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E2v : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
unfold cfg_at. change (w64 B_OCT) with (Z_to_bv 64 0x84474).
(* what S0's runs change: bytes of the save area [sp - 224, sp) only *)
set (Xs := fun a => spZ regs - 224 <= a < spZ regs).
(* 0x84474 .. 0x844b8: one run, stopped at 0x844bc *)
cw_run_to cw_awr_stk 0x844bc.
lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2), HG : mem_grows _ _ |- _ =>
  assert (KX : forall a, 0 <= a < 2 ^ 64 -> ~ Xs a -> aview tfibsegs H m2 a = aview tfibsegs H m1 a);
  [ intros a Ha Hx; apply (oc_kept_of_frame Ef rs H m1 m2 HFr a Ha); intros (r & Hr & Hb); apply Hx; unfold Xs;
    lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
    repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; revert Hb; evalE AG; intros Hb; lia | ]);
    destruct Hr
  | ];
  assert (KP : forall a, apresent H m1 a -> apresent H m2 a) by (intros a Hp; exact (apresent_grows _ _ _ a HG Hp));
  clear HFr HG
end.
clear_frames.
assert (HK1 : tcj_kept tfibsegs B 4320 lyc Sc W memc W (ms_mem ms) (spZ regs) (fun a => sg <= a < sg + 8 \/ dt <= a < dt + 1)).
{ apply (cw_kept_step B LAWS 4320 lyc Sc W memc mdc W memc (ms_mem ms) (spZ regs) _ Xs ltac:(lia) HAR HK KX); [|exact KP].
  intros a Ha. unfold Xs in Ha. left. lia. }
assert (Hdtb : 0 < dt /\ dt + 1 <= 2 ^ 63) by (destruct Hdt as [((Hx0 & Hx1 & _) & _) | (Hx0 & Hx1 & _)]; lia).
pose proof Hsg as (Hsg0 & Hsg63 & _).
assert (KW1 : forall a, (sg <= a < sg + 8 \/ dt <= a < dt + 1) ->
  aview tfibsegs (w_H W) (ms_mem ms) a = aview tfibsegs (w_H W) memc a)
  by (intros a Ha; pose proof (HWR a Ha) as Hw; apply KX; [destruct Ha; lia | unfold Xs; lia]).
clear HK KX KP.
(* sp1 into atom 70 *)
set (sp1 := 32 * ((spZ regs - 192) / 32)).
destruct (sp1_facts (spZ regs - 192) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 208 <= sp1 <= spZ regs - 192) by lia. clear Hsp1r.
assert (Dand : sv_denot E (SAlu ALU_AND (SOff 2 (-192)) (SLit (-32))) = Z_to_bv 64 sp1)
  by exact (oc_denot_and_m32 E 2 (spZ regs) (-192) E2v ltac:(lia) ltac:(lia) ltac:(unfold spZ in *; lia)).
assert (Dadd : sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-192)) (SLit (-32))) (SLit 0)) = Z_to_bv 64 sp1).
{ change (sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-192)) (SLit (-32))) (SLit 0)))
    with (alu64 ALU_ADD (sv_denot E (SAlu ALU_AND (SOff 2 (-192)) (SLit (-32)))) (sv_denot E (SLit 0))).
  rewrite Dand. cbn [sv_denot]. rewrite YI08.alu64_add_lit, Z.add_0_r. reflexivity. }
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1) Dand R2.
rreg_by HS (9%bv : bv 5) (Z_to_bv 64 sp1) Dadd R9.
clear Dand Dadd.
pose proof (st_ok_agree tfibsegs 70 E (havoc E 70 [Z_to_bv 64 sp1]) _ _ HS
  (env_agree_havoc_ge 70 70 E E _ ltac:(lia) (env_agree_refl 70 E)) ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (E70 : ew Ev 70 = Z_to_bv 64 sp1) by (rewrite HEv; exact (ew_havoc_new _ 70 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (2%bv : bv 5) (SOff 70 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E70, Z.add_0_r, R2; rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_set_reg_fp tfibsegs Ev ssx msx (9%bv : bv 5) (SOff 70 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E70, Z.add_0_r, R9; rewrite unsigned_lit_small by lia; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS. clear R2 R9.
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_add_fact tfibsegs Ev ssx msx 70%nat (mkAF (2 ^ 46) (2 ^ 47) 5) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E70, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3;
  clear HS; rename HS3 into HS end.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let rs' := eval vm_compute in (trim_stack rs (-104) 0) in
  pose proof (st_ok_submem tfibsegs Ex ssx (restrict (w_H W) msX) rs' HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  pose proof (ast_ok_add_region tfibsegs Ev _ _ (YP09.mkRegion (Some 70%nat) 48 56 48 56 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
          rewrite E70, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
          intros o Ho; apply (apresent_writable tfibsegs); apply HJpres; lia)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob; repeat split; lia)) as HS3;
  clear HS; rename HS3 into HS end.
norm_ss HS.
reshok HS.
(* 0x844bc .. jal 0x3d3c0 at 0x844e8: one run, stopped at the request *)
lazymatch type of HS with st_ok _ ?Ev _ _ =>
  assert (U70 : bv_unsigned (ew Ev 70) = sp1) by (rewrite E70; apply unsigned_lit_small; lia);
  assert (U2 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
cw_run_to ltac:(idtac;
  lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?s0 ?fp ?b0 ?bc ?lyv ?ownv =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk s0 fp b0 bc lyv ownv) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [azlit_tac|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0)); [reflexivity | rewrite U2; lia | cbn; lia | cbn; lia |]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 70%nat (sp1 - sp0)); [reflexivity | rewrite U70; lia | cbn; lia | cbn; lia |] ])
  0x3d3c0.
lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2), HG : mem_grows _ _ |- _ =>
  assert (KX : forall a, 0 <= a < 2 ^ 64 -> ~ Xs a -> aview tfibsegs H m2 a = aview tfibsegs H m1 a);
  [ intros a Ha Hx; apply (oc_kept_of_frame Ef rs H m1 m2 HFr a Ha); intros (r & Hr & Hb); apply Hx; unfold Xs;
    lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
    repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; revert Hb; evalE AG; intros Hb; lia | ]);
    destruct Hr
  | ];
  assert (KP : forall a, apresent H m1 a -> apresent H m2 a) by (intros a Hp; exact (apresent_grows _ _ _ a HG Hp));
  clear HFr HG
end.
clear_frames.
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => is_var m; rename m into msB end.
assert (HK2 : tcj_kept tfibsegs B 4320 lyc Sc W memc W (ms_mem msB) (spZ regs) (fun a => sg <= a < sg + 8 \/ dt <= a < dt + 1)).
{ apply (cw_kept_step B LAWS 4320 lyc Sc W memc mdc W (ms_mem ms) (ms_mem msB) (spZ regs) _ Xs ltac:(lia) HAR HK1 KX); [|exact KP].
  intros a Ha; unfold Xs in Ha; left; lia. }
(* the write set kept by the two runs *)
assert (KW2 : forall a, (sg <= a < sg + 8 \/ dt <= a < dt + 1) ->
  aview tfibsegs (w_H W) (ms_mem msB) a = aview tfibsegs (w_H W) memc a).
{ intros a Ha. pose proof (HWR a Ha) as Hw. rewrite <- (KW1 a Ha). apply KX; [destruct Ha; lia | unfold Xs; lia]. }
clear HK1 KW1 KX KP.
(* the registers and the saves at the request *)
rreg HS (1%bv : bv 5) R1. rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4.
rreg HS (8%bv : bv 5) R8. rreg HS (9%bv : bv 5) R9. rreg HS (18%bv : bv 5) R18. rreg HS (20%bv : bv 5) R20.
rreg HS (23%bv : bv 5) R23.
let i2 := oc_ridx HS 2%nat in pose proof (st_ok_region_nth _ _ _ i2 _ HS eq_refl) as RG0.
let i70 := oc_ridx HS 70%nat in pose proof (st_ok_region_nth _ _ _ i70 _ HS eq_refl) as RG70.
cbn [ms_mem restrict] in RG0, RG70.
lazymatch type of RG0 with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RG0 end.
lazymatch type of RG70 with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RG70 end.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (VS : forall (i : nat) (r : bv 5) od, Z.of_nat i = bv_unsigned r ->
   In (YP09.mkChunk od (CVal 8 (SOff i 0)))
     [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
      YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
      YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
      YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
      YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
      YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
      YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
   val_mem tfibsegs (mrestrict (w_H W) (ms_mem msB)) (spZ regs + od) 8 (bv_unsigned (getr regs r))) end.
{ intros i r od Hir Hc. rewrite <- U2.
  eapply (oc_fld _ _ 2 _ _ _ _ _ _ od 8%N i (bv_unsigned (getr regs r)) RG0 eq_refl);
  [ cbn [In] in Hc; repeat (destruct Hc as [Hc | Hc]; [rewrite <- Hc; oc_in |]); destruct Hc
  | rewrite (AG i) by (pose proof (bv_unsigned_in_range _ r) as Hbr; change (bv_modulus 5) with 32 in Hbr; lia); rewrite (EE i r Hir); exact (proj1 (oc_regv _)) | exact (proj2 (oc_regv _)) | lia ]. }
pose proof (VS 1%nat 1%bv (-8) eq_refl ltac:(oc_in)) as V1.
pose proof (VS 8%nat 8%bv (-16) eq_refl ltac:(oc_in)) as V8.
pose proof (VS 9%nat 9%bv (-24) eq_refl ltac:(oc_in)) as V9.
pose proof (VS 18%nat 18%bv (-32) eq_refl ltac:(oc_in)) as V18.
pose proof (VS 19%nat 19%bv (-40) eq_refl ltac:(oc_in)) as V19.
pose proof (VS 20%nat 20%bv (-48) eq_refl ltac:(oc_in)) as V20.
pose proof (VS 21%nat 21%bv (-56) eq_refl ltac:(oc_in)) as V21.
pose proof (VS 22%nat 22%bv (-64) eq_refl ltac:(oc_in)) as V22.
pose proof (VS 23%nat 23%bv (-72) eq_refl ltac:(oc_in)) as V23.
pose proof (VS 24%nat 24%bv (-80) eq_refl ltac:(oc_in)) as V24.
pose proof (VS 25%nat 25%bv (-88) eq_refl ltac:(oc_in)) as V25.
pose proof (VS 26%nat 26%bv (-96) eq_refl ltac:(oc_in)) as V26.
pose proof (VS 27%nat 27%bv (-104) eq_refl ltac:(oc_in)) as V27.
clear VS RG0.
assert (VSG : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msB)) (sp1 + 48) 8 sg).
{ eapply (oc_fld _ _ 70 _ _ _ _ _ _ 48 8%N 11%nat sg RG70 U70);
  [ oc_in | rewrite (AG 11%nat) by lia; rewrite (EE 11%nat 11%bv eq_refl); exact H11
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia ]. }
clear RG70.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
(* 0x3d3c0: the class-1 frame request *)
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 250816 with (pc_stack_malloc (as_code B) 1) by (rewrite HBcode; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (cpg_stack_malloc_keep_io tfibsegs B LAWS Hsegs errno_low ML SMP 1 ASM1 ltac:(lia) W (ms_regs msX) (ms_mem msX)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ HJ) end.
  - unfold spZ at 1. rewrite R2. evalE AG; lia.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hsp0al. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite R3. evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp.
  - rewrite R4. evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp.
  - exact R1.
  - vm_compute. reflexivity.
  - change (fs_frames 1) with 8192. pose proof (oc_count_le 1 (frames Sc)). lia. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag
  & HKa & HSf & HKr & Hio).
replace (sp0 + (sp1 - sp0) - ESTACK) with (sp1 - 4096) in HKa by (unfold ESTACK; lia).
replace (sp0 + (sp1 - sp0)) with sp1 in HKa by lia.
assert (CS : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs msB) (Z_to_bv 5 r)) by exact HP2.
assert (KA : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - 4096 <= a < sp1) ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) (ms_mem msB) a) by exact (proj1 HKa).
assert (KS : forall a vv, sp1 <= a -> a + 8 <= spZ regs ->
   val_mem tfibsegs (mrestrict (w_H W) (ms_mem msB)) a 8 vv ->
   val_mem tfibsegs (mrestrict (w_H W) mem2) a 8 vv).
{ intros a vv H1 H2 Hvv.
  apply (cw_val_mem_kept (w_H W) (w_H W) (ms_mem msB) mem2 a 8 vv); [|exact Hvv].
  intros x Hx. apply KA; [cbn in Hx; lia | lia]. }
apply SRr_ret. split; [reflexivity|].
exists S2, regs2, mem2, md2, pos.
split; [reflexivity|].
split; [split; [exact HJ2|]|].
{ split.
  { apply (cw_kept_call B 4320 lyc Sc W memc W (ms_mem msB) mem2 (spZ regs) (sp1 - 4096) sp1 _
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HK2 HKa). }
  split.
  { intros a Ha. rewrite <- (KW2 a Ha). pose proof (HWR a Ha) as Hw.
    destruct (oc_wr_where _ Hpre0 a Ha) as [(b & m & Hin & Hr) | [(cid & p & Hin & Hr) | Hst]].
    - pose proof HKa as (_ & A2 & _).
      replace a with (b + (a - b)) by lia.
      rewrite (A2 b m (a - b) Hin ltac:(lia) (fun H => H)). reflexivity.
    - pose proof HKa as (_ & _ & _ & A4 & _).
      exact (A4 cid p a Hin (or_introl Hr) (fun H => H)).
    - apply KA; [cbn in Hst; lia | lia]. }
  split; [exact Eab|]. split; [exact Hfrs2|]. split; [exact Hnin|]. split; [exact HSf|].
  split; [eapply same_io_trans; [apply cw_same_io_wvb | exact Hio]|].
  split.
  { change (fs_frame_bytes 1) with 128 in Hflag.
    replace (frame_addr lyc 1 pos + 128 - 8) with (frame_addr lyc 1 pos + 120) in Hflag by lia. exact Hflag. }
  split.
  { split; [apply KS; [lia | lia | replace (spZ regs - 8) with (spZ regs + -8) by lia; exact V1]|].
    split; [apply KS; [lia | lia | replace (spZ regs - 16) with (spZ regs + -16) by lia; exact V8]|].
    split; [apply KS; [lia | lia | replace (spZ regs - 24) with (spZ regs + -24) by lia; exact V9]|].
    split; [apply KS; [lia | lia | replace (spZ regs - 32) with (spZ regs + -32) by lia; exact V18]|].
    split; [apply KS; [lia | lia | replace (spZ regs - 40) with (spZ regs + -40) by lia; exact V19]|].
    split; [apply KS; [lia | lia | replace (spZ regs - 48) with (spZ regs + -48) by lia; exact V20]|].
    split; [apply KS; [lia | lia | replace (spZ regs - 56) with (spZ regs + -56) by lia; exact V21]|].
    split; [apply KS; [lia | lia | replace (spZ regs - 64) with (spZ regs + -64) by lia; exact V22]|].
    split; [apply KS; [lia | lia | replace (spZ regs - 72) with (spZ regs + -72) by lia; exact V23]|].
    split; [apply KS; [lia | lia | replace (spZ regs - 80) with (spZ regs + -80) by lia; exact V24]|].
    split; [apply KS; [lia | lia | replace (spZ regs - 88) with (spZ regs + -88) by lia; exact V25]|].
    split; [apply KS; [lia | lia | replace (spZ regs - 96) with (spZ regs + -96) by lia; exact V26]|].
    apply KS; [lia | lia | replace (spZ regs - 104) with (spZ regs + -104) by lia; exact V27]. }
  fold sp1. apply (KS (sp1 + 48) sg); [lia | lia | exact VSG]. }
split; [change (fs_frame_bytes 1) with 128 in Hz; exact Hz|].
split; [exact Ha0|].
assert (P2 : getr regs2 2 = getr (ms_regs msB) 2) by exact (CS 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3 = getr (ms_regs msB) 3) by exact (CS 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4 = getr (ms_regs msB) 4) by exact (CS 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr (ms_regs msB) 8) by exact (CS 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9 = getr (ms_regs msB) 9) by exact (CS 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs2 18 = getr (ms_regs msB) 18) by exact (CS 18 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20 = getr (ms_regs msB) 20) by exact (CS 20 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs2 23 = getr (ms_regs msB) 23) by exact (CS 23 ltac:(unfold acallee_saved; lia)).
split; [rewrite P2, R2; evalE AG; reflexivity|].
split; [rewrite P9, R9; evalE AG; reflexivity|].
split; [rewrite P8, R8; evalE AG; rewrite E2v; reflexivity|].
split; [rewrite P3, R3; evalE AG; exact (EE 3%nat 3%bv eq_refl)|].
split; [rewrite P4, R4; evalE AG; exact (EE 4%nat 4%bv eq_refl)|].
split; [rewrite P18, R18; evalE AG; rewrite (EE 12%nat 12%bv eq_refl); exact H12|].
split; [rewrite P20, R20; evalE AG; rewrite (EE 10%nat 10%bv eq_refl); exact H10|].
rewrite P23, R23. evalE AG; exact E32.
Qed.
End w.
End s.
