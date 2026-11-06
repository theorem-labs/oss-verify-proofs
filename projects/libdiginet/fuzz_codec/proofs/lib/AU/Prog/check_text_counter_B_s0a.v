(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:138-139
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh5.v:99 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-117
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:367-369 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8w.v:289-290 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:156-159. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec_A.v, with its module paths and module names changed; 231 of its 263 lines of code are new or changed and 973 lines of the source are left out. *)
(* Segment S0 of check_text_counter's walk in image B (fuzz_codec.asan-ubsan 0x841c4), part a: the state S0 passes
   through at the class-0 frame request's return (cc_s0_r1 at 0x8423c) and the walk to it.
   0x841c4 .. 0x84238: the real frame 160 (`sd zero,0(sp)`, 13 saves), s0 = entry sp, sp = s1 = 32 * ((sp - 160) / 32),
   s4 = dt, s3 = sg, the use-after-return cell through the .got slot 0x9e488 (it holds 1, so beqz a2 at 0x84230 is not
   taken), the shadow offset into s8 through the .got slot 0x9e430 and its cell, s5 = q, a0 = 64, jal 0x3d24c: one run
   to the request, then CPgWalkFrameU.cpg_stack_malloc_keep_io. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU check_text_scribble_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_s0a.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_counter_B_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variables SEG7TBL GLYPHA : Z.
Variable ROSTRS : list (Z * Z).

(* ---- the state S0 passes through ------------------------------------------------------------------------------ *)
(* the thirteen saves of the prologue, as cc_common states them *)
Definition cc_saves (g : cc_ctx) (mem2 : word -> option byte) : Prop :=
  val_mem tfibsegs (rd (cc_W g) mem2) (cc_sp g - 8) 8 (raZ (cc_regs g)) /\
  val_mem tfibsegs (rd (cc_W g) mem2) (cc_sp g - 16) 8 (bv_unsigned (getr (cc_regs g) 8)) /\
  val_mem tfibsegs (rd (cc_W g) mem2) (cc_sp g - 24) 8 (bv_unsigned (getr (cc_regs g) 9)) /\
  val_mem tfibsegs (rd (cc_W g) mem2) (cc_sp g - 32) 8 (bv_unsigned (getr (cc_regs g) 18)) /\
  val_mem tfibsegs (rd (cc_W g) mem2) (cc_sp g - 40) 8 (bv_unsigned (getr (cc_regs g) 19)) /\
  val_mem tfibsegs (rd (cc_W g) mem2) (cc_sp g - 48) 8 (bv_unsigned (getr (cc_regs g) 20)) /\
  val_mem tfibsegs (rd (cc_W g) mem2) (cc_sp g - 56) 8 (bv_unsigned (getr (cc_regs g) 21)) /\
  val_mem tfibsegs (rd (cc_W g) mem2) (cc_sp g - 64) 8 (bv_unsigned (getr (cc_regs g) 22)) /\
  val_mem tfibsegs (rd (cc_W g) mem2) (cc_sp g - 72) 8 (bv_unsigned (getr (cc_regs g) 23)) /\
  val_mem tfibsegs (rd (cc_W g) mem2) (cc_sp g - 80) 8 (bv_unsigned (getr (cc_regs g) 24)) /\
  val_mem tfibsegs (rd (cc_W g) mem2) (cc_sp g - 88) 8 (bv_unsigned (getr (cc_regs g) 25)) /\
  val_mem tfibsegs (rd (cc_W g) mem2) (cc_sp g - 96) 8 (bv_unsigned (getr (cc_regs g) 26)) /\
  val_mem tfibsegs (rd (cc_W g) mem2) (cc_sp g - 104) 8 (bv_unsigned (getr (cc_regs g) 27)).
(* what S0 carries from the request on: the caller's journal with the frame, what the call kept, the frame new, the
   model's input, the flag word, the saves *)
Definition cc_s0_j (g : cc_ctx) (pos : Z) (S2 : astate) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  ajournal tfibsegs B (cc_STK g) (cc_sp0 g) (cc_FP g) (cc_ly g) (cc_S g) (cc_W0 g) (cc_mem0 g) (cc_md0 g)
    ((0, pos) :: cc_own g) (cc_lyc g) S2 (cc_W g) mem2 md2 (cc_k g) /\
  tcj_kept tfibsegs B TB_check_text_counter (cc_lyc g) (cc_Sc g) (cc_W g) (cc_memc g) (cc_W g) mem2 (cc_sp g) (cc_wr g) /\
  ablocks B (cc_lyc g) S2 = ablocks B (cc_lyc g) (cc_Sc g) /\ frames S2 = (0, pos) :: frames (cc_Sc g) /\
  ~ In (0, pos) (frames (cc_Sc g)) /\ (exists f, S2 = set_fs f (cc_Sc g)) /\ same_io (cc_mdc g) md2 /\
  rdword (aview tfibsegs (w_H (cc_W g)) mem2) (cc_F g pos + 56) = Some (cc_FL g pos) /\
  cc_saves g mem2.
(* 0x8423c, the request's return: a0 = F, the frame's shadow zero *)
Definition cc_s0_r1 (g : cc_ctx) : world tfibsegs -> config -> Prop :=
  fun W2 c2 => W2 = cc_W g /\ exists S2 regs2 mem2 md2 pos,
    c2 = mkCfg (mkst regs2 (Z_to_bv 64 0x8423c) mem2 (seg_rom tfibsegs)) md2 /\
    cc_s0_j g pos S2 mem2 md2 /\
    zero_shadow (aview tfibsegs (w_H (cc_W g)) mem2) SHADOW_OFF (cc_F g pos) 64 /\
    getr regs2 10 = w64 (cc_F g pos) /\
    getr regs2 2 = w64 (cc_sp1 g) /\ getr regs2 9 = w64 (cc_sp1 g) /\ getr regs2 8 = w64 (cc_sp g) /\
    getr regs2 3 = getr (cc_regs g) 3 /\ getr regs2 4 = getr (cc_regs g) 4 /\
    getr regs2 19 = w64 (cc_sg g) /\ getr regs2 20 = w64 (cc_dt g) /\ getr regs2 21 = w64 (cc_q g) /\
    getr regs2 24 = w64 SB.

Section w.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM0 : astack_malloc_realizes tfibsegs B 0.
Hypothesis SMP : stack_malloc_progressP B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.

(* entry -> the class-0 frame request -> its return at 0x8423c *)
Lemma cc_s0_p1 : forall g, cc_pre B SEG7TBL GLYPHA ROSTRS g ->
  SRr tfibsegs (cc_W g) (cfg_at tfibsegs B_CTC (cc_regs g) (cc_memc g) (cc_mdc g)) (cc_s0_r1 g).
Proof.
intros [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj] Hpre.
unfold cc_pre in Hpre.
unfold cc_s0_r1, cc_s0_j, cc_saves, cc_sp, cc_sp1, cc_F, cc_FL, cc_wr, cc_len in *.
cbn [cc_STK cc_sp0 cc_FP cc_ly cc_S cc_W0 cc_mem0 cc_md0 cc_own cc_lyc cc_Sc cc_W cc_memc cc_mdc cc_k cc_regs
  cc_q cc_sg cc_dt cc_tb cc_sj cc_dj] in Hpre |- *.
destruct Hpre as (HE & H10 & Hstr & Hoq & Hosg & Hodt & H11 & Hsg & Hsj & Hsjl & H12 & Hdt & Hdj & Hd1 & Hd2 & Hd3 &
  Himg & Hagr & Hfr6).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TB_check_text_counter HE
  ltac:(unfold TB_check_text_counter, ESTACK; lia)) as (Hceil & H47 & H46 & Hal & Hpres).
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & _ & Hwlo & Hwhi & Hev & Hlive).
pose proof HJ as (HAR & _).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (TT : TB_check_text_counter = 8384) by reflexivity. rewrite TT in *.
pose proof (cw_kept0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (spZ regs) 8384
  (fun a => sg <= a < sg + 24 \/ dt <= a < dt + 1) HJ Hwlo Hwhi) as HK.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBguar, HBuar in Kguar. rewrite HBuar in Kuar.
pose proof (cw_entry B TL LAWS B_CTC 160 [] [uar_got_region; uar_cell_region] [] lyc Sc W regs memc mdc HAR
  ltac:(lia) ltac:(lia) Hal ltac:(intros a Ha; apply Hpres; lia) ltac:(vm_compute; reflexivity)) as HS.
set (E := Ereg regs (cw_extra [])) in HS.
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
clearbody E.
unfold cfg_at. change (w64 B_CTC) with (Z_to_bv 64 0x841c4).
(* 0x841c4 .. jal 0x3d24c at 0x84238: one run, stopped at the request *)
cw_run_to cw_awr_stk 0x3d24c.
(* what the run kept: only the save area [sp - 160, sp) changed *)
lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2), HG : mem_grows _ _ |- _ =>
  assert (KX : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 160 <= a < spZ regs) -> aview tfibsegs H m2 a = aview tfibsegs H m1 a);
  [ intros a Ha Hx; apply (bs_kept_of_frame Ef rs H m1 m2 HFr a Ha); intros (r & Hr & Hb); apply Hx;
    lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
    repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?B2 in Hb; lia | ]);
    destruct Hr
  | ];
  assert (KP : forall a, apresent H m1 a -> apresent H m2 a) by (intros a Hp; exact (apresent_grows _ _ _ a HG Hp));
  clear HFr HG
end.
clear_frames.
assert (HK1 : tcj_kept tfibsegs B 8384 lyc Sc W memc W (ms_mem ms) (spZ regs) (fun a => sg <= a < sg + 24 \/ dt <= a < dt + 1)).
{ apply (cw_kept_step B LAWS 8384 lyc Sc W memc mdc W memc (ms_mem ms) (spZ regs) _
    (fun a => spZ regs - 160 <= a < spZ regs) ltac:(lia) HAR HK KX); [|exact KP].
  intros a Ha. cbv beta in Ha. left. lia. }
clear HK.
(* the registers and the saves at the request *)
set (sp1 := 32 * ((spZ regs - 160) / 32)).
destruct (sp1_facts (spZ regs - 160) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160) by lia. clear Hsp1r.
assert (Dand : sv_denot E (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32))) = Z_to_bv 64 sp1)
  by exact (bs_denot_and_m32 E 2 (spZ regs) (-160) E2v ltac:(lia) ltac:(lia) ltac:(unfold spZ in *; lia)).
assert (Dadd : sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32))) (SLit 0)) = Z_to_bv 64 sp1).
{ change (sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32))) (SLit 0)))
    with (alu64 ALU_ADD (sv_denot E (SAlu ALU_AND (SOff 2 (-160)) (SLit (-32)))) (sv_denot E (SLit 0))).
  rewrite Dand. cbn [sv_denot]. rewrite YI08.alu64_add_lit, Z.add_0_r. reflexivity. }
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1) Dand R2.
rreg_by HS (9%bv : bv 5) (Z_to_bv 64 sp1) Dadd R9.
rreg HS (1%bv : bv 5) R1. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4. rreg HS (8%bv : bv 5) R8.
rreg HS (19%bv : bv 5) R19. rreg HS (20%bv : bv 5) R20. rreg HS (21%bv : bv 5) R21. rreg HS (24%bv : bv 5) R24.
clear Dand Dadd.
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as RG0.
cbn [ms_mem restrict] in RG0.
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
  eapply (bs_fld E _ 2 _ _ _ _ _ _ od 8%N i (bv_unsigned (getr regs r)) RG0 eq_refl);
  [ cbn [In] in Hc; repeat (destruct Hc as [Hc | Hc]; [rewrite <- Hc; bs_in |]); destruct Hc
  | rewrite (EE i r Hir); exact (proj1 (bs_regv _)) | exact (proj2 (bs_regv _)) | lia ]. }
pose proof (VS 1%nat 1%bv (-8) eq_refl ltac:(bs_in)) as V1.
pose proof (VS 8%nat 8%bv (-16) eq_refl ltac:(bs_in)) as V8.
pose proof (VS 9%nat 9%bv (-24) eq_refl ltac:(bs_in)) as V9.
pose proof (VS 18%nat 18%bv (-32) eq_refl ltac:(bs_in)) as V18.
pose proof (VS 19%nat 19%bv (-40) eq_refl ltac:(bs_in)) as V19.
pose proof (VS 20%nat 20%bv (-48) eq_refl ltac:(bs_in)) as V20.
pose proof (VS 21%nat 21%bv (-56) eq_refl ltac:(bs_in)) as V21.
pose proof (VS 22%nat 22%bv (-64) eq_refl ltac:(bs_in)) as V22.
pose proof (VS 23%nat 23%bv (-72) eq_refl ltac:(bs_in)) as V23.
pose proof (VS 24%nat 24%bv (-80) eq_refl ltac:(bs_in)) as V24.
pose proof (VS 25%nat 25%bv (-88) eq_refl ltac:(bs_in)) as V25.
pose proof (VS 26%nat 26%bv (-96) eq_refl ltac:(bs_in)) as V26.
pose proof (VS 27%nat 27%bv (-104) eq_refl ltac:(bs_in)) as V27.
clear VS RG0.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hsp0al & _) & _).
(* 0x3d24c: the class-0 frame request *)
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 250444 with (pc_stack_malloc (as_code B) 0) by (rewrite HBcode; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (cpg_stack_malloc_keep_io tfibsegs B LAWS Hsegs errno_low ML SMP 0 ASM0 ltac:(lia) W (ms_regs msX) (ms_mem msX)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (sp1 - sp0) _ HJ) end.
  - unfold spZ at 1. rewrite R2. rewrite unsigned_lit_small by lia. lia.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hsp0al. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - vm_compute. reflexivity.
  - change (fs_frames 0) with 16384. pose proof (bs_count_le 0 (frames Sc)). lia. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag
  & HKa & HSf & HKr & Hio).
replace (sp0 + (sp1 - sp0) - ESTACK) with (sp1 - 4096) in HKa by (unfold ESTACK; lia).
replace (sp0 + (sp1 - sp0)) with sp1 in HKa by lia.
assert (CS : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r)) by exact HP2.
assert (KA : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - 4096 <= a < sp1) ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) (ms_mem ms) a) by exact (proj1 HKa).
assert (KS : forall od vv, -104 <= od <= -8 ->
   val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + od) 8 vv ->
   val_mem tfibsegs (mrestrict (w_H W) mem2) (spZ regs - - od) 8 vv).
{ intros od vv Hod Hvv. replace (spZ regs - - od) with (spZ regs + od) by lia.
  apply (cw_val_mem_kept (w_H W) (w_H W) (ms_mem ms) mem2 (spZ regs + od) 8 vv); [|exact Hvv].
  intros x Hx. apply KA; [cbn in Hx; lia | lia]. }
apply SRr_ret. split; [reflexivity|].
exists S2, regs2, mem2, md2, pos.
split; [reflexivity|].
split; [split; [exact HJ2|]|].
{ split.
  { apply (cw_kept_call B 8384 lyc Sc W memc W (ms_mem ms) mem2 (spZ regs) (sp1 - 4096) sp1 _
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HK1 HKa). }
  split; [exact Eab|]. split; [exact Hfrs2|]. split; [exact Hnin|]. split; [exact HSf|].
  split; [eapply same_io_trans; [apply cw_same_io_wvb | exact Hio]|].
  split.
  { change (fs_frame_bytes 0) with 64 in Hflag.
    replace (frame_addr lyc 0 pos + 64 - 8) with (frame_addr lyc 0 pos + 56) in Hflag by lia. exact Hflag. }
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
split; [change (fs_frame_bytes 0) with 64 in Hz; exact Hz|].
split; [exact Ha0|].
assert (P2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (CS 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3 = getr (ms_regs ms) 3) by exact (CS 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4 = getr (ms_regs ms) 4) by exact (CS 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr (ms_regs ms) 8) by exact (CS 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9 = getr (ms_regs ms) 9) by exact (CS 9 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs2 19 = getr (ms_regs ms) 19) by exact (CS 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20 = getr (ms_regs ms) 20) by exact (CS 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs2 21 = getr (ms_regs ms) 21) by exact (CS 21 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs2 24 = getr (ms_regs ms) 24) by exact (CS 24 ltac:(unfold acallee_saved; lia)).
split; [rewrite P2; exact R2|].
split; [rewrite P9; exact R9|].
split; [rewrite P8, R8, E2v; reflexivity|].
split; [rewrite P3, R3; exact (EE 3%nat 3%bv eq_refl)|].
split; [rewrite P4, R4; exact (EE 4%nat 4%bv eq_refl)|].
split; [rewrite P19, R19, (EE 11%nat 11%bv eq_refl); exact H11|].
split; [rewrite P20, R20, (EE 12%nat 12%bv eq_refl); exact H12|].
split; [rewrite P21, R21, (EE 10%nat 10%bv eq_refl); exact H10|].
rewrite P24, R24; exact E32.
Qed.
End w.
End s.
