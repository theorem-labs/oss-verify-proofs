(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:155-159
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbl.v:141-145 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:140-148, 156-160 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-370
   [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used
   under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_A.v, with its module paths and module names changed; 212 of its 260 lines of code are new or changed and 760 lines of the source are left out. *)
(* Segment ENTRY of the image-A walk of LLVMFuzzerTestOneInput (fuzz_codec.asan 0x8084c), part a: from the contract's
   pre-condition at the entry to the return of the class-3 frame request at 0x808c0 (ae_r1).
   0x8084c .. 0x808bc: the real frame 288 (`sd zero,0(sp)` and the thirteen saves at sp0 - 104 .. sp0 - 8), s0 = sp0,
   sp = s1 = sp1 = 32 * ((sp0 - 288) / 32) (0x8088c `andi sp,sp,-32`), s8 = n, s9 = p, the shadow offset into s4 through
   the .got slot 0x9db10 and its cell, the use-after-return cell through the .got slot 0x9db68 (it holds 1, so `beqz a2`
   at 0x808b4 is not taken), a0 = 448, jal 0x3d400: one run from the entry state (the journal of ajournal_init), then
   the class-3 frame request through CPgWalkFrame.cpg_stack_malloc_keep_io (count_cid 3 [] = 0 < fs_frames 3). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YO09 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalk CPgWalkKept CPgWalkFrame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- small arithmetic and memory facts ---------------------------------------------------------------------- *)
(* `andi x, y, -32` of an offset of an atom (the realignment of sp) *)
Lemma ae_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
(* a field of a region whose chunk is an atom with a known value *)
Lemma ae_fld : forall E m n bse cs lo hi wlo whi od (w : N) i v,
  region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = bse ->
  In (YP09.mkChunk od (CVal w (SOff i 0))) cs -> ew E i = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
  Z.of_N w <= 8 ->
  val_mem tfibsegs m (bse + od) (N.to_nat w) v.
Proof.
intros E m n bse cs lo hi wlo whi od w i v Hr Hb Hc Hi Hv Hw.
eapply (field_of_region E m n bse cs lo hi wlo whi od w (SOff i 0) v Hr Hb Hc); [|exact Hv | exact Hw].
cbn [sv_denot]. rewrite Hi, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma ae_regv : forall (x : word), x = Z_to_bv 64 (bv_unsigned x) /\ 0 <= bv_unsigned x < 2 ^ (8 * Z.of_N 8).
Proof.
intros x. split; [symmetry; apply Z_to_bv_bv_unsigned|].
pose proof (bv_unsigned_in_range _ x) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.
Ltac ae_in := cbn [In]; repeat first [left; reflexivity | right].

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* the realigned sp of the machine frame *)
Definition ae_sp1 (g : ectx) : Z := 32 * ((e_sp0 g - 288) / 32).
(* the thirteen saved words of the prologue, as mcommon states them *)
Definition ae_saves (g : ectx) (W : world tfibsegs) (mem2 : word -> option byte) : Prop :=
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 8) 8 (raZ (e_regs g)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 16) 8 (bv_unsigned (getr (e_regs g) 8)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 24) 8 (bv_unsigned (getr (e_regs g) 9)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 32) 8 (bv_unsigned (getr (e_regs g) 18)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 40) 8 (bv_unsigned (getr (e_regs g) 19)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 48) 8 (bv_unsigned (getr (e_regs g) 20)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 56) 8 (bv_unsigned (getr (e_regs g) 21)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 64) 8 (bv_unsigned (getr (e_regs g) 22)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 72) 8 (bv_unsigned (getr (e_regs g) 23)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 80) 8 (bv_unsigned (getr (e_regs g) 24)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 88) 8 (bv_unsigned (getr (e_regs g) 25)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 96) 8 (bv_unsigned (getr (e_regs g) 26)) /\
  val_mem tfibsegs (rd W mem2) (e_sp0 g - 104) 8 (bv_unsigned (getr (e_regs g) 27)).

Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.

(* 0x808c0, the request's return: the journal from the entry with the new frame (3, pos) as own, the frame's shadow
   zero, the flag address at F + 504, a0 = F, the registers the rest of the segment reads, the saves *)
Definition ae_r1 (g : ectx) : world tfibsegs -> config -> Prop :=
  fun W2 c2 => W2 = e_W g /\ exists S2 regs2 mem2 md2 pos,
    c2 = mkCfg (mkst regs2 (Z_to_bv 64 0x808c0) mem2 (seg_rom tfibsegs)) md2 /\
    ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
      (e_ly g) S2 (e_W g) mem2 md2 0 /\
    frames S2 = [(3, pos)] /\ (exists f, S2 = set_fs f (e_S g)) /\ blocks_bytes S2 = blocks_bytes (e_S g) /\
    zero_shadow (aview tfibsegs (w_H (e_W g)) mem2) SHADOW_OFF (FA g pos) 512 /\
    rdword (aview tfibsegs (w_H (e_W g)) mem2) (FA g pos + 504) = Some (flag_addr (e_ly g) 3 pos) /\
    getr regs2 10 = w64 (FA g pos) /\
    getr regs2 2 = w64 (ae_sp1 g) /\ getr regs2 9 = w64 (ae_sp1 g) /\ getr regs2 8 = w64 (e_sp0 g) /\
    getr regs2 3 = w64 (as_gp B) /\ getr regs2 4 = w64 (as_tp B) /\ getr regs2 20 = w64 SHADOW_OFF /\
    getr regs2 24 = w64 (e_n g) /\ getr regs2 25 = w64 (e_p g) /\
    ae_saves g (e_W g) mem2.

Section h.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM3 : astack_malloc_realizes tfibsegs B 3.
Hypothesis SMP : stack_malloc_progressP B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.

(* entry -> the class-3 frame request -> its return at 0x808c0 *)
Lemma ae_p1 : forall g, e_pre B MT K XM_LIB g ->
  SRr tfibsegs (e_W g) (cfg_at tfibsegs A_LLVMF (e_regs g) (e_mem g) (e_md g)) (ae_r1 g).
Proof.
intros g Hpre. destruct g as [ly S W mem md regs p n pl M].
unfold ae_r1, ae_saves, ae_sp1, FA, e_sp0. cbn [e_ly e_S e_W e_mem e_md e_regs e_p e_n e_pl e_M].
unfold e_pre, codec_lib_pre_x in Hpre. cbn [e_ly e_S e_W e_mem e_md e_regs e_p e_n e_pl e_M] in Hpre.
destruct Hpre as (HFN & Hra & Ha0 & Ha1 & Hpn & _ & _ & Hfr0 & _ & _ & _).
pose proof HFN as (HAR & Hraok & Hra4 & Hgp & Htp & Hstk & Hpres & _ & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof (ajournal_init tfibsegs B LLVMF_STK [] ly S W regs mem md [] HFN) as HJ.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : LLVMF_STK = 32768) by reflexivity.
assert (Hpres' : forall a, spZ regs - 288 <= a < spZ regs -> apresent (w_H W) mem a)
  by (intros a Ha; apply Hpres; lia).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBguar, HBuar in Kguar. rewrite HBuar in Kuar.
pose proof (cw_entry B TL LAWS A_LLVMF 288 [] [uar_got_region; uar_cell_region] [] ly S W regs mem md HAR
  ltac:(lia) ltac:(lia) Hal16 Hpres' ltac:(vm_compute; reflexivity)) as HS.
set (E := Ereg regs (cw_extra [])) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
specialize (HS ltac:(apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
  unfold region_ok, uar_got_region, uar_cell_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  unfold A_GOT_uar, A_uar_glob; (split; [lia|]); (split; [lia|]); (split; [intros o Ho; lia|]);
  apply Forall_cons; try apply Forall_nil;
  first
  [ apply (chunk_ok_val tfibsegs E _ 0 0x9db68 8 (SLit 0xa6480) 0xa6480); [reflexivity | zside | zside |];
    rewrite Z.add_0_l; exact (val_mem_of_rdword tfibsegs (w_H W) mem _ _ Kguar)
  | apply (chunk_ok_val tfibsegs E _ 0 0xa6480 4 (SLit 1) 1); [reflexivity | zside | zside |];
    rewrite Z.add_0_l; exact (val_mem_of_rd32 tfibsegs (w_H W) mem _ _ Kuar) ])).
specialize (HS ltac:(apply pairwise_disjoint_of_extents;
  unfold cw_regs, stack_region, got_region, bcell_region, uar_got_region, uar_cell_region, extent_of_region;
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi]; cbn [base_val]; rewrite Usp;
  unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia)).
specialize (HS I).
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) mem)) by constructor.
assert (B2 := Usp).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E2v : ew E 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
clearbody E.
unfold cfg_at. change (w64 A_LLVMF) with (Z_to_bv 64 0x8084c).
(* 0x8084c .. jal 0x3d400 at 0x808bc: one run, stopped at the request *)
cw_run_to cw_awr_stk 0x3d400.
clear_frames.
(* the registers and the saves at the request *)
set (sp1 := 32 * ((spZ regs - 288) / 32)).
destruct (sp1_facts (spZ regs - 288) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by lia. clear Hsp1r.
assert (Dand : sv_denot E (SAlu ALU_AND (SOff 2 (-288)) (SLit (-32))) = Z_to_bv 64 sp1)
  by exact (ae_denot_and_m32 E 2 (spZ regs) (-288) E2v ltac:(lia) ltac:(lia) ltac:(unfold spZ in *; lia)).
assert (Dadd : sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-288)) (SLit (-32))) (SLit 0)) = Z_to_bv 64 sp1).
{ change (sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-288)) (SLit (-32))) (SLit 0)))
    with (alu64 ALU_ADD (sv_denot E (SAlu ALU_AND (SOff 2 (-288)) (SLit (-32)))) (sv_denot E (SLit 0))).
  rewrite Dand. cbn [sv_denot]. rewrite YI08.alu64_add_lit, Z.add_0_r. reflexivity. }
rreg_by HS (2%bv : bv 5) (Z_to_bv 64 sp1) Dand R2.
rreg_by HS (9%bv : bv 5) (Z_to_bv 64 sp1) Dadd R9.
rreg HS (1%bv : bv 5) R1. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4. rreg HS (8%bv : bv 5) R8.
rreg HS (20%bv : bv 5) R20. rreg HS (24%bv : bv 5) R24. rreg HS (25%bv : bv 5) R25.
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
  eapply (ae_fld E _ 2 _ _ _ _ _ _ od 8%N i (bv_unsigned (getr regs r)) RG0 eq_refl);
  [ cbn [In] in Hc; repeat (destruct Hc as [Hc | Hc]; [rewrite <- Hc; ae_in |]); destruct Hc
  | rewrite (EE i r Hir); exact (proj1 (ae_regv _)) | exact (proj2 (ae_regv _)) | lia ]. }
pose proof (VS 1%nat 1%bv (-8) eq_refl ltac:(ae_in)) as V1.
pose proof (VS 8%nat 8%bv (-16) eq_refl ltac:(ae_in)) as V8.
pose proof (VS 9%nat 9%bv (-24) eq_refl ltac:(ae_in)) as V9.
pose proof (VS 18%nat 18%bv (-32) eq_refl ltac:(ae_in)) as V18.
pose proof (VS 19%nat 19%bv (-40) eq_refl ltac:(ae_in)) as V19.
pose proof (VS 20%nat 20%bv (-48) eq_refl ltac:(ae_in)) as V20.
pose proof (VS 21%nat 21%bv (-56) eq_refl ltac:(ae_in)) as V21.
pose proof (VS 22%nat 22%bv (-64) eq_refl ltac:(ae_in)) as V22.
pose proof (VS 23%nat 23%bv (-72) eq_refl ltac:(ae_in)) as V23.
pose proof (VS 24%nat 24%bv (-80) eq_refl ltac:(ae_in)) as V24.
pose proof (VS 25%nat 25%bv (-88) eq_refl ltac:(ae_in)) as V25.
pose proof (VS 26%nat 26%bv (-96) eq_refl ltac:(ae_in)) as V26.
pose proof (VS 27%nat 27%bv (-104) eq_refl ltac:(ae_in)) as V27.
clear VS RG0.
(* 0x3d400: the class-3 frame request *)
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace 250880 with (pc_stack_malloc (as_code B) 3) by (rewrite HBcode; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (cpg_stack_malloc_keep_io tfibsegs B LAWS Hsegs errno_low ML SMP 3 ASM3 ltac:(lia) W (ms_regs msX) (ms_mem msX)
    _ _ _ _ _ _ _ _ _ _ _ _ _ (sp1 - spZ regs) _ HJ) end.
  - unfold spZ at 1. rewrite R2. rewrite unsigned_lit_small by lia. lia.
  - rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - vm_compute. reflexivity.
  - rewrite Hfr0. apply Z.ltb_lt. vm_compute. reflexivity. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0' & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz
  & Hflag & HKa & HSf & HKr & Hio).
replace (spZ regs + (sp1 - spZ regs) - ESTACK) with (sp1 - 4096) in HKa by (unfold ESTACK; lia).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in HKa by lia.
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
split; [exact HJ2|].
split; [rewrite Hfrs2, Hfr0; reflexivity|].
split; [exact HSf|].
split; [exact Hbb2|].
split; [change (fs_frame_bytes 3) with 512 in Hz; exact Hz|].
split; [change (fs_frame_bytes 3) with 512 in Hflag; replace (frame_addr ly 3 pos + 512 - 8) with (frame_addr ly 3 pos + 504) in Hflag by lia; exact Hflag|].
split; [exact Ha0'|].
assert (P2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (CS 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs2 3 = getr (ms_regs ms) 3) by exact (CS 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs2 4 = getr (ms_regs ms) 4) by exact (CS 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs2 8 = getr (ms_regs ms) 8) by exact (CS 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs2 9 = getr (ms_regs ms) 9) by exact (CS 9 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs2 20 = getr (ms_regs ms) 20) by exact (CS 20 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs2 24 = getr (ms_regs ms) 24) by exact (CS 24 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs2 25 = getr (ms_regs ms) 25) by exact (CS 25 ltac:(unfold acallee_saved; lia)).
split; [rewrite P2; exact R2|].
split; [rewrite P9; exact R9|].
split; [rewrite P8, R8, E2v; reflexivity|].
split; [rewrite P3, R3; exact (EE 3%nat 3%bv eq_refl) || (rewrite (EE 3%nat 3%bv eq_refl); exact Hgp)|].
split; [rewrite P4, R4; exact (EE 4%nat 4%bv eq_refl) || (rewrite (EE 4%nat 4%bv eq_refl); exact Htp)|].
split; [rewrite P20, R20, E32; reflexivity|].
split; [rewrite P24, R24, (EE 11%nat 11%bv eq_refl); exact Ha1|].
split; [rewrite P25, R25, (EE 10%nat 10%bv eq_refl); exact Ha0|].
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
exact (KS (-104) _ ltac:(lia) V27).
Qed.
End h.
End b.
End a.
