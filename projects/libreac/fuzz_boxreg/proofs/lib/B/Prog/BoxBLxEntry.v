(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img's image range set to libreac/fuzz_boxreg's own (Reusable/YImgTop.v IMG_LO, IMG_TOP). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YCbq.v, with its module paths and module names changed; 447 of its 579 lines of code are new or changed and 2830 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/B/Prog/BoxBLxExit.v, with its module names changed; 1010 of its 1070 lines of code are new or changed and 519 lines of the source are left out. *)
(* The entry phase of the B walk of fuzz_boxreg's LLVMFuzzerTestOneInput (fuzz_boxreg.asan-ubsan 0x7ffac): from the
   function's first slot under lx_base to the loop head 0x80258 (BoxBLxDefs.v LP_J) of turn 0.

   The walk: the prologue saves ra, s0, s1, s2 .. s11 below sp0 and realigns sp to sp1 (andi sp,sp,-0x20); the
   GOT-loaded use-after-return flag is 1 (AR's const law), so __asan_stack_malloc_3 (0x8001c) gives the frame F
   (its fallback on the machine stack is not taken: F <> 0); the frame header and the 52 shadow bytes LSH_entry are
   written; n >> 26 = 0 (lx_base: n < 2 ^ 26); the slots 0x10 / 0x18 / 0x80 hold F, 0x88 / 0x90 the input cursor;
   malloc (0x120) (0x8017c, amalloc04_rule) gives the registry r (NULL refuted by 4096 <= r); fuzz_u8 reads the
   first input byte when n > 0 (UBSan's pointer test refuted by p >= 4096, ASan's shadow check of p by the block's
   shadow); reac_boxreg_init (r, the sign-extended byte) (0x801e4); the byte - 1 clamp test gives the fabric;
   check (r, fabric) (0x80210); the loop's slots are set up, and the run stops at 0x80258, where LI_J of turn 0 holds.
   This file walks from the entry to the call of check (cut D, BoxBLxEntryDefs.v ss_D / le_D_stmt): lx_entry_of
   from the entry to the call of reac_boxreg_init (cut C, ss_C), le_from_C from there; BoxBLxEntryD.v (le_D) walks
   the call of check to its return (cut K, ss_K) and BoxBLxEntryK.v (le_K) the loop's set-up to LI_J.

   The symbolic state uses the seat layout of BoxBLxSeat.v from the first slot: atom 2 is sp1 and atom 8 is sp0
   (the entry registers 2 and 8 are named by the overrides of le_sr0), 33 .. 45 the caller's saved words, 32
   SHADOW_OFF; 46 / 47 (the frame and its flag address) and 22 (its shadow base) are bound after
   __asan_stack_malloc_3 returns; 48 is the use-after-return flag cell. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase YC4b BoxRo PaStep.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBReacBoxregInit BoxBCheck.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import SnprintfDefB.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxEntryDefs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require BoxBLxEntryD BoxBLxEntryK.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregInit reac_boxreg_init_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the entry state ---- *)
(* The entry registers in the seat's atoms: ra and s0, s1, s2 .. s11 are the caller's saved words 33 .. 45, sp is
   sp0 (atom 8); every other register is its own atom. *)
Definition LE_OV0 : list (bv 5 * sv) :=
  [((1%bv : bv 5), SOff 33 0); ((2%bv : bv 5), SOff 8 0); ((8%bv : bv 5), SOff 34 0); ((9%bv : bv 5), SOff 35 0);
   ((18%bv : bv 5), SOff 36 0); ((19%bv : bv 5), SOff 37 0); ((20%bv : bv 5), SOff 38 0);
   ((21%bv : bv 5), SOff 39 0); ((22%bv : bv 5), SOff 40 0); ((23%bv : bv 5), SOff 41 0);
   ((24%bv : bv 5), SOff 42 0); ((25%bv : bv 5), SOff 43 0); ((26%bv : bv 5), SOff 44 0);
   ((27%bv : bv 5), SOff 45 0)].
Definition le_sr0 : list sv := Eval vm_compute in lx_sr LE_OV0.
(* The saved words' window and the word `sd zero, 0(sp)` writes (both below sp0), the use-after-return flag's GOT
   word (object 0) and cell (atom 48), the shadow base's GOT word (object 1) and cell (object 12). *)
Definition le_regions0 : smem :=
  [YP09.mkRegion (Some 8%nat) (-104) 0 (-104) 0 []; YP09.mkRegion (Some 8%nat) (-256) (-248) (-256) (-248) [];
   uar_got_regionP 48; uar_cell_regionP 48; got_regionP; bcell_regionP 32].
(* sp1 (atom 2) is the value of `andi sp,sp,-0x20`: the alias makes the engine name it. *)
Definition le_facts0 : facts :=
  mkFacts [(2%nat, mkAF 0x7fff7f800000 (2 ^ 47) 5); (8%nat, mkAF 0x7fff7f808000 (2 ^ 47) 4);
           (11%nat, mkAF 0 (2 ^ 26 - 1) 0); (32%nat, mkAF SBR SBR 0)] []
          [(SAlu ALU_AND (SOff 8 (-256)) (SLit (-32)), SOff 2 0)].
Definition ss_le0 : sstate := mkSS 0 le_sr0 le_regions0 None le_facts0.

Lemma le_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
  intros x Hx.
  assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
  rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
  rewrite Z.land_ones, Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.

Lemma le_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
  intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
  change (zcanon (-32)) with (2 ^ 64 - 32). rewrite le_land_m32 by lia. apply zcanon_id. rewrite M64_val.
  split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
  pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.


Ltac le_norm HS :=
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : lx_hyps B MT.

(* The entry environment: the seat's (BoxBLxSeat.v lx_env) over the entry registers with sp1 at atom 2 and sp0 at
   atom 8, the frame atoms 46 / 47 not yet bound (the frame of position 0), and the flag cell at atom 48. *)
Definition le_regsE (cx : lxcx) : bvmap 5 word :=
  regupd (regupd (lc_regs cx) 2%bv (w64 (lsp1 cx))) 8%bv (w64 (lsp0 cx)).
Definition le_E0 (cx : lxcx) : env := lx_env cx 0 (le_regsE cx) [w64 (as_uar_cell B)].

Lemma le_getr_regsE : forall cx (r : bv 5), r <> 2%bv -> r <> 8%bv -> getr (le_regsE cx) r = getr (lc_regs cx) r.
Proof.
  intros cx r H2 H8. unfold getr, le_regsE. destruct (bv_eqb r 0); [reflexivity|].
  rewrite !regupd_other by assumption. reflexivity.
Qed.

Lemma le_E0_reg : forall cx n (r : bv 5), Z.of_nat n = bv_unsigned r -> r <> 2%bv -> r <> 8%bv ->
  ew (le_E0 cx) n = getr (lc_regs cx) r.
Proof.
  intros cx n r Hn H2 H8. unfold le_E0. rewrite (lx_env_reg cx 0 _ _ n r Hn). exact (le_getr_regsE cx r H2 H8).
Qed.

Lemma le_E0_2 : forall cx, ew (le_E0 cx) 2 = w64 (lsp1 cx).
Proof.
  intros cx. unfold le_E0. rewrite (lx_env_reg cx 0 _ _ 2 (2%bv : bv 5)) by reflexivity.
  unfold getr, le_regsE. cbn [bv_eqb]. rewrite regupd_other by discriminate. apply regupd_same.
Qed.

Lemma le_E0_8 : forall cx, ew (le_E0 cx) 8 = w64 (lsp0 cx).
Proof.
  intros cx. unfold le_E0. rewrite (lx_env_reg cx 0 _ _ 8 (8%bv : bv 5)) by reflexivity.
  unfold getr, le_regsE. cbn [bv_eqb]. apply regupd_same.
Qed.

Lemma le_E0_x : forall cx i, (i < 16)%nat -> ew (le_E0 cx) (32 + i) = nth i (lx_xatoms cx 0) (w64 0).
Proof. intros cx i Hi. unfold le_E0. exact (lx_env_x cx 0 _ _ i Hi). Qed.

Lemma le_E0_48 : forall cx, ew (le_E0 cx) 48 = w64 (as_uar_cell B).
Proof. intros cx. unfold le_E0. exact (lx_env_ex cx 0 _ _ 0 ltac:(lia)). Qed.

Lemma le_E0_img : forall cx, img_env VAL A_LIM (le_E0 cx).
Proof. intros cx. unfold le_E0. apply lx_env_img. Qed.

(* The entry registers are the overrides' atoms. *)
Lemma le_regs_ok0 : forall cx, regs_ok (le_E0 cx) le_sr0 (lc_regs cx).
Proof.
  intros cx r. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [ lazymatch goal with |- getr _ ?rr = sv_denot _ (sr_get le_sr0 ?rr) =>
        let e := eval vm_compute in (sr_get le_sr0 rr) in change (sr_get le_sr0 rr) with e end;
      first
      [ reflexivity
      | lazymatch goal with |- getr _ ?rr = sv_denot _ (SOff ?k 0) =>
          rewrite lx_sv_SOff0, (le_E0_reg cx k rr) by first [reflexivity | discriminate]; reflexivity end
      | rewrite lx_sv_SOff0, le_E0_8; unfold lsp0, spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | rewrite lx_sv_SOff0;
        lazymatch goal with |- _ = ew _ ?k =>
          let i := eval vm_compute in (k - 32)%nat in
          replace k with (32 + i)%nat by reflexivity; rewrite (le_E0_x cx i) by lia; reflexivity end ]
    |]).
  destruct Hin.
Qed.

(* The entry state: the seat's atoms over the entry registers, the saved words' window, the GOT words and cells. *)
Lemma le_entry_st : forall cx, lx_base B MT cx ->
  st_ok_pi SEGS VAL (le_E0 cx) ss_le0
    (restrict (w_H (lc_W cx)) (mkst (lc_regs cx) (Z_to_bv 64 (BASE + 0)) (lc_mem cx) (seg_rom SEGS))).
Proof.
  intros cx HB. pose proof (le_sp_facts B MT cx HB) as (Hal16 & Hsp0lo & Hsp0hi & Hsp1 & Hal32).
  destruct HB as (HPRE & H10 & H11 & Hn & _).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  pose proof (lh_laws B MT HY) as LAWS. pose proof (lh_tl B MT HY) as TL. pose proof (lh_tlf B MT HY) as TLF.
  destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & Kuar & Kgot & Kguar).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
  rewrite (palf_got_uar B TLF) in Kguar.
  pose proof (palf_uar_img B TLF) as Huimg. pose proof (palf_uar_al B TLF) as Hual.
  pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
  pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
  pose proof (pa_obj_img 0 ltac:(lia)) as Hgot0R.
  assert (E8 : ew (le_E0 cx) 8 = w64 (lsp0 cx)) by apply le_E0_8.
  assert (E2 : ew (le_E0 cx) 2 = w64 (lsp1 cx)) by apply le_E0_2.
  assert (E32 : ew (le_E0 cx) 32 = w64 SHADOW_OFF) by exact (le_E0_x cx 0 ltac:(lia)).
  assert (E48 : ew (le_E0 cx) 48 = w64 (as_uar_cell B)) by apply le_E0_48.
  assert (E11 : ew (le_E0 cx) 11 = w64 (lc_n cx))
    by (rewrite (le_E0_reg cx 11 (11%bv : bv 5)) by first [reflexivity | discriminate]; exact H11).
  set (E := le_E0 cx) in *.
  assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
    by (subst E; unfold le_E0, lx_env; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
    by (subst E; unfold le_E0, lx_env; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Eo12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
    by (subst E; unfold le_E0, lx_env; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> YP09.base_val E (Some n) = v).
  { intros n v Hv Hr. cbn [YP09.base_val]. rewrite Hv. apply unsigned_lit_small. exact Hr. }
  assert (Ub8 : YP09.base_val E (Some 8%nat) = lsp0 cx) by (apply VB; [exact E8 | lia]).
  assert (Ubo0 : YP09.base_val E (Some (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply VB; [exact Eo0 | lia]).
  assert (Ubo1 : YP09.base_val E (Some (A_OBJ 1)) = VAL (A_OBJ 1)) by (apply VB; [exact Eo1 | lia]).
  assert (Ubo12 : YP09.base_val E (Some (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply VB; [exact Eo12 | lia]).
  assert (Ub48 : YP09.base_val E (Some 48%nat) = as_uar_cell B) by (apply VB; [exact E48 | lia]).
  assert (Hsp : spZ (lc_regs cx) = lsp0 cx) by reflexivity.
  rewrite restrict_mkst_fx. unfold ss_le0. apply pa_entry_st_ok_full.
  - exact (le_regs_ok0 cx).
  - vm_compute. reflexivity.
  - unfold le_regions0, uar_got_regionP, uar_cell_regionP, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
      rewrite ?Ub8, ?Ubo0, ?Ubo1, ?Ubo12, ?Ub48.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite Hsp. unfold LX_STK. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite Hsp. unfold LX_STK. lia.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff 48 0) (as_uar_cell B));
        [rewrite lx_sv_SOff0, E48; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (lc_W cx)) (lc_mem cx) _ _ Kguar).
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H (lc_W cx)) (lc_mem cx) _ _ Kuar).
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [cbn [sv_denot]; rewrite Eo12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (lc_W cx)) (lc_mem cx) _ _ Kgot).
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SHADOW_OFF);
        [rewrite lx_sv_SOff0, E32; reflexivity | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H (lc_W cx)) (lc_mem cx) _ _ Kcell).
  - apply pairwise_disjoint_of_extents.
    unfold le_regions0, uar_got_regionP, uar_cell_regionP, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite Ub8, Ubo0, Ubo1, Ubo12, Ub48.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hsep Huimg HcellR HgotR Hgot0R Hsp0lo C1. clear. intros. repeat split; lia.
  - split; [|split; [exact I|]].
    + cbn [le_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E2, E8, E11, E32. unfold w64.
      rewrite (unsigned_lit_small (lsp1 cx)) by lia. rewrite (unsigned_lit_small (lsp0 cx)) by lia.
      rewrite (unsigned_lit_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
      assert (Hn26 : 0 <= lc_n cx < 2 ^ 26) by (unfold lc_n in *; lia).
      rewrite (unsigned_lit_small (lc_n cx)) by lia.
      change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite Z.pow_0_r, !Z.mod_1_r.
      unfold SBR, SHADOW_OFF. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
    + cbn [le_facts0 f_alias alias_ok]. split; [|exact I].
      rewrite (le_and_m32 E 8 (lsp0 cx) (-256) E8) by lia. rewrite lx_sv_SOff0, E2. reflexivity.
Qed.

(* A symbolic state with its memory regions and facts replaced. *)
Lemma le_restate : forall E pc sr rs G rs' G' ms,
  st_ok_pi SEGS VAL E (mkSS pc sr rs None G) ms ->
  YP09.regions_wf rs' = true -> Forall (YP09.region_ok SEGS E (ms_mem ms)) rs' -> YP09.pairwise_disjoint E rs' ->
  facts_ok E G' -> st_ok_pi SEGS VAL E (mkSS pc sr rs' None G') ms.
Proof.
  intros E pc sr rs G rs' G' ms HS Hwf Hok Hpd HG.
  unfold st_ok_pi, abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
  destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _ & _).
  unfold st_ok. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
  repeat (split; [assumption|]). split; [|exact HG].
  split; [exact Hwf|]. split; [exact Hok | exact Hpd].
Qed.

(* A region read through fewer chunks and no window. *)
Lemma le_region_sub : forall E m n lo hi wlo whi cs cs',
  YP09.region_ok SEGS E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> (forall c, In c cs' -> In c cs) ->
  YP09.region_ok SEGS E m (YP09.mkRegion (Some n) lo hi 0 0 cs').
Proof.
  intros E m n lo hi wlo whi cs cs' (H1 & H2 & _ & H4) Hi.
  unfold YP09.region_ok in *. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
  split; [exact H1|]. split; [exact H2|]. split; [intros o Ho; lia|].
  rewrite Forall_forall in H4 |- *. intros c Hc. exact (H4 c (Hi c Hc)).
Qed.

Lemma le_U_srl26 : forall E x, U E (SAlu ALU_SRL x (SLit 26)) = U E x / 2 ^ 26.
Proof.
  intros E x. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 26) 63) with 26.
  rewrite Z.shiftr_div_pow2 by lia. apply zcanon_id. rewrite M64_val.
  pose proof (U_range E x) as Hx. rewrite M64_val in Hx.
  split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ (U E x)); [apply Z.div_le_upper_bound; lia | lia].
Qed.

(* A region appended after a state's regions. *)
Lemma le_add_region_end : forall E pc sr rs G r ms,
  st_ok_pi SEGS VAL E (mkSS pc sr rs None G) ms ->
  YP09.regions_wf (rs ++ [r]) = true -> YP09.region_ok SEGS E (ms_mem ms) r ->
  Forall (fun x => YP09.all_disjoint E x [r]) rs ->
  st_ok_pi SEGS VAL E (mkSS pc sr (rs ++ [r]) None G) ms.
Proof.
  intros E pc sr rs G r ms HS Hwf Hr Hd.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hok & Hpd) & HG).
  cbn [abs_ss setpc ss_mem ss_facts] in Hok, Hpd, HG.
  apply (le_restate E pc sr rs G (rs ++ [r]) G ms HS Hwf); [| | exact HG].
  - apply Forall_app. split; [exact Hok | apply Forall_cons; [exact Hr | apply Forall_nil]].
  - apply lx_pwd_app; [exact Hpd | split; exact I | exact Hd].
Qed.

(* A byte of a block of the entry state, at a later state of the journal. *)
Lemma le_val_mem_kept : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k p n i v,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
  val_mem SEGS (mrestrict (w_H W) mem) (p + i) 1 v -> val_mem SEGS (mrestrict (w_H W') mem') (p + i) 1 v.
Proof.
  intros STK sp0 ly S W mem md own ly' S' W' mem' md' k p n i v HJ H1 H2 Hi Hv.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  apply (val_mem_moved SEGS (w_H W) (w_H W') mem mem' (p + i) (p + i) 1 v); [|exact Hv].
  intros q Hq. replace (p + i + q) with (p + (i + q)) by lia.
  apply (F2 p n (i + q) H1 H2); [lia | apply inFP_nil].
Qed.

(* A block the last malloc added is no block of before. *)
Lemma le_new_block : forall ly S (W : world SEGS) mem md l res n,
  AR SEGS B ly S W mem md -> ablocks B ly S = l ++ [(res, n)] -> 0 < req_size n -> ~ In (res, n) l.
Proof.
  intros ly S W mem md l res n HAR E Hq Hin. apply in_split in Hin as (l1 & l2 & El).
  pose proof (sep_blocks_pos SEGS B (lh_laws B MT HY) ly S W mem md (res, n) (res, n) l1 l2 [] HAR) as Hd.
  rewrite E, El, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.



(* A symbolic state at a callee's entry, restated: equal registers, other regions, other facts. *)
Lemma le_normalize : forall E pc sr sr' rs rs' G G' ms,
  st_ok SEGS E (mkSST pc sr [] rs None G) ms ->
  (forall r, sv_denot E (sr_get sr' r) = sv_denot E (sr_get sr r)) ->
  YP09.regions_wf rs' = true -> Forall (YP09.region_ok SEGS E (ms_mem ms)) rs' -> YP09.pairwise_disjoint E rs' ->
  facts_ok E G' -> st_ok SEGS E (mkSST pc sr' [] rs' None G') ms.
Proof.
  intros E pc sr sr' rs rs' G G' ms HS Hsr Hwf Hok Hpd HG.
  destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _ & _).
  unfold st_ok. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
  repeat (split; [assumption|]). split; [intros r; rewrite (H7 r); symmetry; apply Hsr|].
  split; [|exact HG]. split; [exact Hwf|]. split; [exact Hok | exact Hpd].
Qed.

(* Fresh atoms at a callee's entry. *)
Lemma le_st_ok_havoc : forall k E ss pc ws ms,
  st_ok SEGS E (setpc ss pc) ms -> ss_atoms_p (pband k (k + length ws)) ss = true ->
  st_ok SEGS (havoc E k ws) (setpc ss pc) ms.
Proof.
  intros k E ss pc ws ms HS Hat.
  assert (HSpi : st_ok_pi SEGS VAL E (setpc ss (pc - BASE)) ms)
    by (unfold st_ok_pi, abs_ss; cbn [ss_pc setpc]; replace (BASE + (pc - BASE)) with pc by lia; exact HS).
  pose proof (st_ok_pi_havoc_hi k E _ ms ws HSpi ltac:(destruct ss; exact Hat)) as H.
  unfold st_ok_pi, abs_ss in H. cbn [ss_pc setpc] in H. replace (BASE + (pc - BASE)) with pc in H by lia. exact H.
Qed.

Lemma le_chunk_eq : forall E m base off w e e',
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal w e)) -> sv_denot E e = sv_denot E e' ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal w e')).
Proof.
  intros E m base off w e e' H He i Hi. destruct (H i Hi) as (b & H1 & H2). exists b.
  cbn [cbyte YP09.c_val YP09.c_off] in *. rewrite <- He. split; assumption.
Qed.

(* The spill region with the input cursor's two slots named by other expressions of the same values. *)
Lemma le_spill_swap : forall E m e1 e2 e1' e2' c3 c4 c5,
  YP09.region_ok SEGS E m (YP09.mkRegion (Some 2%nat) 0 152 0 152
    [YP09.mkChunk 136 (CVal 8 e1); YP09.mkChunk 144 (CVal 8 e2); c3; c4; c5]) ->
  sv_denot E e1 = sv_denot E e1' -> sv_denot E e2 = sv_denot E e2' ->
  YP09.region_ok SEGS E m (YP09.mkRegion (Some 2%nat) 0 152 0 152
    [YP09.mkChunk 136 (CVal 8 e1'); YP09.mkChunk 144 (CVal 8 e2'); c3; c4; c5]).
Proof.
  intros E m e1 e2 e1' e2' c3 c4 c5 (H1 & H2 & H3 & H4) He1 He2.
  unfold YP09.region_ok in *. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  inversion H4 as [|x1 l1 Hc1 T1]; subst. inversion T1 as [|x2 l2 Hc2 T2]; subst.
  constructor; [exact (le_chunk_eq _ _ _ _ _ _ _ Hc1 He1)|].
  constructor; [exact (le_chunk_eq _ _ _ _ _ _ _ Hc2 He2) | exact T2].
Qed.

Lemma le_spill_swap' : forall E m e1 e2 e1' e2' c3 c4 c5,
  YP09.region_ok SEGS E m (YP09.mkRegion (Some 2%nat) 0 152 0 152
    [YP09.mkChunk 144 (CVal 8 e2); YP09.mkChunk 136 (CVal 8 e1); c3; c4; c5]) ->
  sv_denot E e1 = sv_denot E e1' -> sv_denot E e2 = sv_denot E e2' ->
  YP09.region_ok SEGS E m (YP09.mkRegion (Some 2%nat) 0 152 0 152
    [YP09.mkChunk 136 (CVal 8 e1'); YP09.mkChunk 144 (CVal 8 e2'); c3; c4; c5]).
Proof.
  intros E m e1 e2 e1' e2' c3 c4 c5 (H1 & H2 & H3 & H4) He1 He2.
  unfold YP09.region_ok in *. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  inversion H4 as [|x1 l1 Hc1 T1]; subst. inversion T1 as [|x2 l2 Hc2 T2]; subst.
  constructor; [exact (le_chunk_eq _ _ _ _ _ _ _ Hc2 He1)|].
  constructor; [exact (le_chunk_eq _ _ _ _ _ _ _ Hc1 He2) | exact T2].
Qed.

Lemma le_sext8_0 : forall E, ew E 96 = w64 0 ->
  sv_denot E (le_sext8 96) = Z_to_bv 64 0 /\ sv_denot E (SAlu ALU_ADD (le_sext8 96) (SLit 0)) = Z_to_bv 64 0.
Proof. intros E H. cbn [sv_denot le_sext8]. rewrite H. split; vm_compute; reflexivity. Qed.

(* The registry's bytes across a run that writes only inside its regions' windows. *)
Lemma le_lreg_frame : forall E rs (W : world SEGS) ms ms' r bs,
  frame_of E rs (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  0 <= r -> r + LX_REG < 2 ^ 64 ->
  (forall a, r <= a < r + LX_REG -> ~ YP09.in_wrange E rs a) -> lreg W ms r bs -> lreg W ms' r bs.
Proof.
  intros E rs W ms ms' r bs Hfr H0 H1 Hw HL i Hi. unfold lview in *. rewrite <- (HL i Hi).
  apply aview_eq_of. apply Hfr. rewrite unsigned_lit_small by lia. apply Hw. lia.
Qed.

(* No window of the seat's four regions meets the registry (a heap block away from the frame). *)
Lemma le_reg_nowin : forall cx fp E r cs0 cs1 cs2 cs3 wlo whi a,
  YP09.base_val E (Some LA_SP0) = lsp0 cx -> YP09.base_val E (Some LA_SP) = lsp1 cx ->
  YP09.base_val E (Some LA_F) = lF cx fp -> YP09.base_val E (Some LA_FSH) = lSH cx fp ->
  r + LX_REG <= lsp1 cx -> (r + LX_REG <= lF cx fp \/ lF cx fp + 512 <= r) -> whi <= wlo ->
  r <= a < r + LX_REG ->
  ~ YP09.in_wrange E [YP09.mkRegion (Some LA_SP0) (-104) 0 0 0 cs0; YP09.mkRegion (Some LA_SP) 0 LX_SPILL 0 LX_SPILL cs1;
     YP09.mkRegion (Some LA_F) 0 512 0 512 cs2; YP09.mkRegion (Some LA_FSH) 0 64 wlo whi cs3] a.
Proof.
  intros cx fp E r cs0 cs1 cs2 cs3 wlo whi a U8 U2 U46 U22 Hs Hf Hw Ha (rg & Hin & Hr).
  cbn [In] in Hin. unfold LX_SPILL in *.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; rewrite ?U8, ?U2, ?U46, ?U22 in Hr; lia |]).
  destruct Hin.
Qed.

(* From the call of reac_boxreg_init (cut C) to the call of check (cut D). *)
Lemma le_from_C : le_D_stmt B MT -> forall POST cx fp (E : env) (W : world SEGS) ms md ly S r b pos,
  lx_from B MT POST (LI_J B MT 0) -> lx_base B MT cx ->
  st_ok SEGS E (setpc ss_C (SIGMA BB_reac_boxreg_init)) (restrict (w_H W) ms) ->
  img_env VAL A_LIM E -> lx_E cx fp E ->
  ew E 84 = w64 r -> ew E 96 = w64 b -> 0 <= b < 256 ->
  ew E 97 = w64 (lc_p cx + Z.of_nat pos) -> ew E 98 = w64 (lc_n cx - Z.of_nat pos) ->
  (pos <= length (lc_pl cx))%nat ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(LX_CID, fp)]
    ly S W (ms_mem ms) md 1 ->
  frames S = [(LX_CID, fp)] -> mo_le MT (lc_S cx) S (LX_A1 MT) ->
  ablocks B ly S = ablocks B (lc_ly cx) (lc_S cx) ++ [(r, LX_REG)] ->
  SRr SEGS W (mkCfg ms md) (POST cx).
Proof.
  intros HD POST cx fp E W ms md ly S r b pos HFROM HB HS HEI HE E84 E96 Hb E97 E98 Hpos HJ HFR Hmle Hbl.
  pose proof (le_sp_facts B MT cx HB) as (Hal16 & Hsp0lo & Hsp0hi & Hsp1 & Hal32).
  pose proof HB as (HPRE & H10 & H11 & Hn & Hgarr & Hfr0 & Hnev & Hlive & Hro & Hmok & Hneed & Htr).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  pose proof (lh_laws B MT HY) as LAWS. pose proof (lh_tl B MT HY) as TL.
  pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
  pose proof (lx_F_facts B MT LAWS cx fp W ms ly S md 1 HB HJ HFR) as (HF0 & HFc & HFia & HFo & HF64 & HSHeq).
  pose proof (lx_frame_addr_eq B MT LAWS cx fp W ms ly S md 1 HB HJ) as Hfa. change LX_CID with 3 in Hfa.
  pose proof HJ as (HAR1 & _ & _ & _ & _ & _ & _ & _ & HJF1 & _ & _ & _ & _ & HJpres & _).
  assert (Hrin : In (r, LX_REG) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR1 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & Hrpres & _ & _).
  change (req_size LX_REG) with 288 in *.
  assert (Hrnew : ~ In (r, LX_REG) (ablocks B (lc_ly cx) (lc_S cx)))
    by (apply (le_new_block _ _ _ _ _ _ _ _ HAR1 Hbl); vm_compute; reflexivity).
  assert (HdrF : r + 288 <= lF cx fp \/ lF cx fp + 512 <= r).
  { pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ r LX_REG 3 fp HAR1 Hrin ltac:(rewrite HFR; left; reflexivity))
      as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hfa in Hd. change (req_size LX_REG) with 288 in Hd.
    change (fs_frame_bytes 3) with 512 in Hd. lia. }
  pose proof (lx_extents B MT LAWS cx fp W ms ly S md 1 HB HJ HFR E HE) as (U8 & U2 & U46 & U22).
  pose proof (paj_run B LAWS) as RUN. pose proof (paj_branch (PI := PI)) as BR.
  (* reac_boxreg_init (r, the sign-extended byte) (0x801e4) *)
  pose proof (le_saved_at B MT cx fp E _ _ W ms HB HE HS eq_refl) as HSV.
  pose proof (le_chain B MT cx fp ly S W ms md 1 HB HJ HSV) as Hach.
  pmkst HS.
  prreg HS (10%bv : bv 5) Ia0. prreg HS (2%bv : bv 5) I2. prreg HS (3%bv : bv 5) I3. prreg HS (4%bv : bv 5) I4.
  prreg HS (1%bv : bv 5) I1. prreg HS (8%bv : bv 5) I8.
  pose proof (st_ok_restrict_reg SEGS (w_H W) E _ ms (11%bv : bv 5) HS) as Ia1.
  lazymatch type of Ia1 with _ = sv_denot _ (sr_get ?l ?q) => let e := eval vm_compute in (sr_get l q) in change (sr_get l q) with e in Ia1 end.

  rewrite pa_sigma_reac_boxreg_init.
  set (cI := bv_unsigned (getr (ms_regs ms) 11)).
  assert (HcI : getr (ms_regs ms) 11 = w64 cI) by (unfold cI, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
  pose proof HE as (EW2 & EW8 & EW3 & EW4 & EW22 & EW32 & EWSV & EW46 & EW47).
  unfold LA_SP, LA_SP0, LA_FSH, LA_SB, LA_F, LA_FL in EW2, EW8, EW22, EW32, EW46, EW47.
  assert (HspI : spZ (ms_regs ms) = lsp1 cx).
  { unfold spZ. rewrite I2, EW2. unfold w64. apply unsigned_lit_small. lia. }
  assert (H16 : (lsp1 cx - lsp0 cx) mod 16 = 0).
  { assert (H16' : lsp1 cx mod 16 = 0)
      by (unfold lsp1; replace (32 * ((lsp0 cx - 256) / 32)) with ((2 * ((lsp0 cx - 256) / 32)) * 16) by lia;
          apply Z_mod_mult).
    rewrite Zminus_mod, H16', Hal16. reflexivity. }
  assert (Ha0I : getr (ms_regs ms) 10 = w64 r) by (rewrite Ia0; exact E84).
  eapply SRr_bind.
  { eapply (cl_callS B LAWS W (ms_regs ms) (ms_mem ms) _ LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx)
      (lc_md cx) [(3, fp)] ly S md 1 REAC_BOXREG_INIT_STKB [(r, r + REG_SIZEB)] 0 (lsp1 cx - lsp0 cx) (getr (ms_regs ms) 1) (lch cx) _ HJ).
    - rewrite HspI. lia.
    - exact H16.
    - lia.
    - unfold REAC_BOXREG_INIT_STKB. change ESTACK with 4096. lia.
    - unfold REAC_BOXREG_INIT_STKB, LX_STK. change ESTACK with 4096. lia.
    - rewrite I3, EW3. exact Hgp.
    - rewrite I4, EW4. exact Htp.
    - reflexivity.
    - rewrite I1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite I1, unsigned_lit_small by (pose proof pa_B_ok; lia). pose proof pa_base_lo. lia.
    - replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) by lia.
      unfold s0Z. rewrite I8, EW8. unfold w64. rewrite unsigned_lit_small by lia. exact Hach.
    - intros HPREc. exact (lh_init B MT HY ly S W (ms_regs ms) (ms_mem ms) md (lch cx) r cI HPREc Ha0I HcI Hrin).
    - intros a (x & [<- | []] & Hx). cbn [fst snd] in Hx. right. exists r, LX_REG.
      split; [exact Hrin|]. split; [exact Hrnew|]. change (req_size LX_REG) with 288. unfold REG_SIZEB in Hx. lia. }
  cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HJc & HP5 & (-> & -> & -> & Hperm5 & Hinit)).

  rewrite I1.
  replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) in HJc by lia.
  change (1 + 0) with 1 in HJ5.
  assert (Hd1 : lF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
  assert (Hd0 : 0 <= lF cx fp / 8) by (apply Z.div_pos; lia).
  pose proof Hria as Hria'. change (req_size LX_REG) with 288 in Hria'.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hria'.
  assert (Hkeep5 : lx_keep cx fp W [] (ms_mem ms) mem5).
  { eapply (lx_keep_call_fp B MT LAWS cx fp W ms ly S md 1 HB HJ HFR [] [(r, r + REG_SIZEB)] REAC_BOXREG_INIT_STKB
      _ _ mem5 md5 0); [lia | | apply Forall_nil | | exact HJc].
    - intros q m Hq. rewrite Hbl. apply in_or_app. left. exact Hq.
    - intros a Ha (x & [<- | []] & Hx). cbn [fst snd] in Hx. unfold REG_SIZEB in Hx.
      destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
      + lia.
      + destruct Hn as [[Hn0 _] | ((Hnpos & Hn26) & Hpin)]; [lia|].
        assert (Hpin' : In (lc_p cx, lc_n cx) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; left; exact Hpin).
        assert (Hne : (lc_p cx, lc_n cx) <> (r, LX_REG)) by (intros Heq; rewrite Heq in Hpin; exact (Hrnew Hpin)).
        pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR1 Hpin' Hrin Hne) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size LX_REG) with 288 in Hd.
        pose proof (req_size_pos (lc_n cx) ltac:(lia)) as (_ & Hrq).
        assert (Hrqn : req_size (lc_n cx) = lc_n cx) by (unfold req_size; destruct (Z.eqb_spec (lc_n cx) 0); lia).
        rewrite Hrqn in Hd. lia.
      + change (fs_frame_bytes LX_CID) with 512 in Ha. lia.
      + change (fs_frame_bytes LX_CID / 8) with 64 in Ha. rewrite HSHeq in Ha. unfold SHADOW_OFF in Ha. lia.
      + inversion Ha. }
  pose proof HJ5 as (HAR5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ5pres & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 3 fp HAR5 ltac:(rewrite HFR; left; reflexivity)) as (_ & _ & HF5pres & _).
  rewrite Hfa in HF5pres. change (fs_frame_bytes 3) with 512 in HF5pres.
  jafter_call_keep_pi HS 112%nat regs5 (mrestrict (w_H W) mem5) HP5 [0; 1; 2; 3]%nat HS2.

  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    apply (le_kept4 cx fp E); [exact U8 | exact U2 | exact U46 | exact U22 | lia | lia | |].
    - intros a Ha. apply Hkeep5. unfold lx_keep_at. change (fs_frame_bytes LX_CID) with 512.
      destruct Ha as [Ha|[Ha|Ha]]; [left; lia | right; right; left; lia | right; right; right; left; change (512 / 8) with 64; lia].
    - intros a [Ha | [Ha | Ha]]; [apply HJ5pres; unfold LX_STK, LX_SPILL in *; lia | apply HF5pres; lia | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  set (ms5 := mkst regs5 (Z_to_bv 64 (BASE + 572)) mem5 (seg_rom SEGS)) in *.
  remember (havoc E 112 (map (getr regs5) CLOB)) as E6 eqn:HEq6.
  assert (EA6 : forall n, (n < 112)%nat -> ew E6 n = ew E n) by (intros n Hnn; rewrite HEq6; apply ew_havoc_old; exact Hnn).
  assert (HE6 : lx_E cx fp E6) by (apply (lx_E_agree cx fp E E6 HE); intros n Hnn; apply EA6; unfold LA_EX in Hnn; lia).
  assert (HEI6 : img_env VAL A_LIM E6)
    by (rewrite HEq6; apply img_env_havoc; [exact HEI | unfold A_TEXT; rewrite length_map; cbn [length CLOB]; lia]).
  le_norm HS.

  pose proof (lx_extents B MT LAWS cx fp W ms5 ly S md5 1 HB HJ5 HFR E6 HE6) as (V8 & V2 & V46 & V22).
  pose proof HE6 as (FW2 & FW8 & FW3 & FW4 & FW22 & FW32 & FWSV & FW46 & FW47).
  assert (UB32 : U E6 (SOff LA_SB 0) = SHADOW_OFF) by (apply U_atom; [exact FW32 | unfold SHADOW_OFF; lia]).
  assert (UB46 : U E6 (SOff LA_F 0) = lF cx fp) by (apply U_atom; [exact FW46 | lia]).
  assert (SHOK : sh_ok SEGS CBR [mkSHE LA_F 512 0] E6 (mrestrict (w_H W) (ms_mem ms5))).
  { unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
    exact (lx_shent_rev E6 _ (lF cx fp) 512 LA_F UB32 UB46 HFia ltac:(lia)). }
  (* the byte - 1 clamp test *)
  paj_run_tok RUN HS HJ5 SHOK BspanR.
  { cbn [ss_mem]. apply (le_awr B MT cx fp E6); [exact HB | exact V2 | exact V46 | exact V22 | exact Hfa | lia | lia | apply awr_ok_nil]. }
  rename HFr into HFr6. clear HF HG. repeat rewrite wvb_collapse in HJ5.

  assert (U96 : ew E6 96 = w64 b) by (rewrite EA6 by lia; exact E96).
  psrr_branch_tok RUN BR HS SHOK BspanR.
  all: rewrite branch_ltu_U, (le_mask_U E6 96 b U96 Hb), U_lit in Hc by lia.
  all: paj_run_tok RUN HS HJ5 SHOK BspanR;
    [ cbn [ss_mem add_cond]; apply (le_awr B MT cx fp E6); [exact HB | exact V2 | exact V46 | exact V22 | exact Hfa | lia | lia | apply awr_ok_nil] |].
  all: rename HFr into HFr7; clear HF HG; repeat rewrite wvb_collapse in HJ5.

  all: pose proof (le_byte_facts b Hb) as (BF1 & BF2 & BF3 & BF4).
  all: assert (HcIv : cI = le_sx b mod 2 ^ 64) by (unfold cI; rewrite Ia1; change (U E (SAlu ALU_ADD (le_sext8 96) (SLit 0)) = le_sx b mod 2 ^ 64);
         rewrite U_SAlu, U_SLit; cbn [zalu_raw]; rewrite (le_sext8_U E 96 b E96 Hb); change (zcanon 0) with 0; rewrite Z.add_0_r;
         apply zcanon_id; rewrite M64_val; apply Z.mod_pos_bound; lia).
  all: set (fab := reac_boxreg_init_c.clamp40 (le_sx b)) in *.
  all: assert (HL5 : lreg W ms5 r (reac_boxreg_init_c.init_bytes fab))
         by (intros i Hi; unfold lview; subst ms5; cbn [ms_mem mkst];
             rewrite (Hinit i ltac:(unfold REG_SIZEB; unfold LX_REG in Hi; lia)), HcIv, BF1; reflexivity).
  Show 1.

  all: assert (HL1 : lreg W ms1 r (reac_boxreg_init_c.init_bytes fab)).
  all: [> apply (le_lreg_frame E6 _ W ms0 ms1 r _ HFr7); [lia | unfold LX_REG; lia | | ];
          [ intros a Ha; eapply (le_reg_nowin cx fp E6 r); [exact V8 | exact V2 | exact V46 | exact V22 | unfold LX_REG; lia | unfold LX_REG; lia | lia | exact Ha]
          | apply (le_lreg_frame E6 _ W ms5 ms0 r _ HFr6); [lia | unfold LX_REG; lia | | exact HL5];
            intros a Ha; eapply (le_reg_nowin cx fp E6 r); [exact V8 | exact V2 | exact V46 | exact V22 | unfold LX_REG; lia | unfold LX_REG; lia | lia | exact Ha] ]
       | idtac
       | apply (le_lreg_frame E6 _ W ms0 ms1 r _ HFr7); [lia | unfold LX_REG; lia | | ];
          [ intros a Ha; eapply (le_reg_nowin cx fp E6 r); [exact V8 | exact V2 | exact V46 | exact V22 | unfold LX_REG; lia | unfold LX_REG; lia | lia | exact Ha]
          | apply (le_lreg_frame E6 _ W ms5 ms0 r _ HFr6); [lia | unfold LX_REG; lia | | exact HL5];
            intros a Ha; eapply (le_reg_nowin cx fp E6 r); [exact V8 | exact V2 | exact V46 | exact V22 | unfold LX_REG; lia | unfold LX_REG; lia | lia | exact Ha] ]
       | idtac ].

  all: lazymatch type of HS with st_ok _ ?Ex _ _ =>
         assert (EAc : forall n, (n < 512)%nat -> ew Ex n = ew E6 n)
           by (intros n Hnn; repeat rewrite ew_ewset_other by lia; reflexivity);
         assert (HEIc : img_env VAL A_LIM Ex) by (first [assumption | rewrite <- HEq6 in *; assumption]);
         pose proof (le_st_ok_havoc 99 Ex _ _ [w64 fab] _ HS ltac:(vm_compute; reflexivity)) as HS';
         remember (havoc Ex 99 [w64 fab]) as Ed eqn:HEqd;
         assert (EAd : forall n, (n < 99)%nat -> ew Ed n = ew E6 n)
           by (intros n Hnn; rewrite HEqd, ew_havoc_old by lia; apply EAc; lia);
         assert (Ed99 : ew Ed 99 = w64 fab) by (rewrite HEqd; exact (ew_havoc_new Ex 99 [w64 fab] 0 (w64 0) ltac:(cbn; lia)));
         assert (HEId : img_env VAL A_LIM Ed) by (rewrite HEqd; apply img_env_havoc; [exact HEIc | unfold A_TEXT; cbn; lia])
       end.
  all: clear HS; rename HS' into HS.
  all: assert (HEd : lx_E cx fp Ed) by (apply (lx_E_agree cx fp E6 Ed HE6); intros n Hnn; apply EAd; unfold LA_EX in Hnn; lia).
  all: assert (Ed96 : ew Ed 96 = w64 b) by (rewrite EAd by lia; exact U96).
  all: assert (H99 : sv_denot Ed (SOff 99 0) = w64 fab) by (rewrite lx_sv_SOff0; exact Ed99).
  all: cbn [setpc] in HS.

  - assert (Hfb : fab = b) by (rewrite BF2, Hc; reflexivity).
    assert (Hsx : le_sx b = b) by (apply BF3; exact Hc).
    assert (HS1 : sv_denot Ed (le_sext8 96) = w64 fab).
    { rewrite denot_lit_U, (le_sext8_U Ed 96 b Ed96 Hb), Hsx, Hfb, Z.mod_small by lia. reflexivity. }
    assert (HS2 : sv_denot Ed (SAlu ALU_ADD (le_sext8 96) (SLit 0)) = w64 fab).
    { rewrite denot_lit_U, U_SAlu, U_SLit. cbn [zalu_raw]. rewrite (le_sext8_U Ed 96 b Ed96 Hb).
      change (zcanon 0) with 0. rewrite Z.add_0_r, zcanon_id by (rewrite M64_val; apply Z.mod_pos_bound; lia).
      rewrite Hsx, Hfb, Z.mod_small by lia. reflexivity. }
    lazymatch goal with HS : st_ok _ ?Ed _ _ |- _ =>
      pose proof (le_normalize Ed _ _ le_regs_D _ [lx_saved_region; le_spill_D; le_frame_C; le_shadow_C] _ le_facts_D _ HS) as HSD;
      lazymatch type of HSD with ?A -> _ => assert (HRG : A) end;
      [ intros rr; pose proof (all_regs_in rr) as Hin; cbv [all_regs In] in Hin;
        repeat (destruct Hin as [<- | Hin];
          [ lazymatch goal with |- sv_denot _ (sr_get ?l1 ?q) = sv_denot _ (sr_get ?l2 ?q) =>
              let e1 := eval vm_compute in (sr_get l1 q) in let e2 := eval vm_compute in (sr_get l2 q) in
              change (sv_denot Ed e1 = sv_denot Ed e2) end;
            first [ reflexivity | (rewrite H99; symmetry; first [exact HS1 | exact HS2]) ]
          |]);
        destruct Hin
      | specialize (HSD HRG); clear HRG;
        pose proof HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hok & Hpd) & (HGa & _ & HGl));
        specialize (HSD ltac:(vm_compute; reflexivity) Hok Hpd);
        assert (HFa99 : afact_ok Ed 99 (mkAF 1 40 0))
          by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Ed99; unfold w64; rewrite unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia);
        specialize (HSD (conj (conj HFa99 HGa) (conj I HGl)));
        apply (HD POST cx fp Ed W ms1 _ ly S r b fab pos); [|exact HSD];
        unfold le_cut;
        split; [exact HFROM|]; split; [exact HB|]; split; [exact HEId|]; split; [exact HEd|];
        split; [rewrite EAd, EA6 by lia; exact E84|];
        split; [exact Ed96|]; split; [exact Hb|]; split; [exact Ed99|]; split; [reflexivity|];
        split; [rewrite EAd, EA6 by lia; exact E97|]; split; [rewrite EAd, EA6 by lia; exact E98|]; split; [exact Hpos|];
        split; [exact HJ5|]; split; [exact HFR|]; split; [exact Hmle|]; split; [exact Hbl|]; exact HL1 ]
      end.

  - assert (Hfb : fab = 40) by (rewrite BF2, Hc; reflexivity).
    assert (HS1 : sv_denot Ed (SLit 40) = w64 fab) by (rewrite Hfb; reflexivity).
    assert (HS2 : sv_denot Ed (SLit 40) = w64 fab) by exact HS1.
    lazymatch goal with HS : st_ok _ ?Ed _ _ |- _ =>
      pose proof (le_normalize Ed _ _ le_regs_D _ [lx_saved_region; le_spill_D; le_frame_C; le_shadow_C] _ le_facts_D _ HS) as HSD;
      lazymatch type of HSD with ?A -> _ => assert (HRG : A) end;
      [ intros rr; pose proof (all_regs_in rr) as Hin; cbv [all_regs In] in Hin;
        repeat (destruct Hin as [<- | Hin];
          [ lazymatch goal with |- sv_denot _ (sr_get ?l1 ?q) = sv_denot _ (sr_get ?l2 ?q) =>
              let e1 := eval vm_compute in (sr_get l1 q) in let e2 := eval vm_compute in (sr_get l2 q) in
              change (sv_denot Ed e1 = sv_denot Ed e2) end;
            first [ reflexivity | (rewrite H99; symmetry; first [exact HS1 | exact HS2]) ]
          |]);
        destruct Hin
      | specialize (HSD HRG); clear HRG;
        pose proof HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hok & Hpd) & (HGa & _ & HGl));
        specialize (HSD ltac:(vm_compute; reflexivity) Hok Hpd);
        assert (HFa99 : afact_ok Ed 99 (mkAF 1 40 0))
          by (unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Ed99; unfold w64; rewrite unsigned_lit_small by lia;
              rewrite Z.pow_0_r, Z.mod_1_r; lia);
        specialize (HSD (conj (conj HFa99 HGa) (conj I HGl)));
        apply (HD POST cx fp Ed W ms1 _ ly S r b fab pos); [|exact HSD];
        unfold le_cut;
        split; [exact HFROM|]; split; [exact HB|]; split; [exact HEId|]; split; [exact HEd|];
        split; [rewrite EAd, EA6 by lia; exact E84|];
        split; [exact Ed96|]; split; [exact Hb|]; split; [exact Ed99|]; split; [reflexivity|];
        split; [rewrite EAd, EA6 by lia; exact E97|]; split; [rewrite EAd, EA6 by lia; exact E98|]; split; [exact Hpos|];
        split; [exact HJ5|]; split; [exact HFR|]; split; [exact Hmle|]; split; [exact Hbl|]; exact HL1 ]
      end.
Qed.


(* The phase from the function's entry, given cut D. *)
Theorem lx_entry_of : le_D_stmt B MT -> forall POST, lx_from B MT POST (LI_J B MT 0) -> lx_start B MT POST.
Proof.
  intros HD POST HFROM cx HB.
  pose proof (le_entry_st cx HB) as HS.
  pose proof (le_sp_facts B MT cx HB) as (Hal16 & Hsp0lo & Hsp0hi & Hsp1 & Hal32).
  pose proof HB as (HPRE & H10 & H11 & Hn & Hgarr & Hfr0 & Hnev & Hlive & Hro & Hmok & Hneed & Htr).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  pose proof (lh_laws B MT HY) as LAWS. pose proof (lh_tl B MT HY) as TL. pose proof (lh_tlf B MT HY) as TLF.
  pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
  pose proof (ajournal_init SEGS B LX_STK [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_regs cx) (lc_mem cx) (lc_md cx) [] HPRE) as HJ.
  change (spZ (lc_regs cx)) with (lsp0 cx) in HJ.
  assert (SHOK : sh_ok SEGS CBR [] (le_E0 cx) (mrestrict (w_H (lc_W cx)) (lc_mem cx))) by (unfold sh_ok; apply Forall_nil).
  assert (HEI : img_env VAL A_LIM (le_E0 cx)) by apply le_E0_img.
  assert (Usp0 : bv_unsigned (ew (le_E0 cx) 8) = lsp0 cx) by (rewrite le_E0_8; apply unsigned_lit_small; lia).
  pose proof (paj_run B LAWS) as RUN.
  unfold LP_entry. change (w64 (BASE + 0)) with (Z_to_bv 64 (BASE + 0)).
  (* the prologue, the GOT loads, up to the call of __asan_stack_malloc_3 *)
  paj_run_tok RUN HS HJ SHOK BspanR; [awr_ok_tac; exact Usp0 |].
  clear HF HFr HG.
  (* __asan_stack_malloc_3 (0x8001c): the frame F of class 3 *)
  pmkst HS.
  prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
  rewrite (palf_sm3 B TLF).
  eapply SRr_bind.
  { eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs (pal_env B TL) (lh_ml B MT HY) (lh_smp B MT HY) 3 (lh_asm3 B MT HY)
      ltac:(lia) (lc_W cx) _ _ LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) []
      (lc_ly cx) (lc_S cx) _ 0 (lsp1 cx - lsp0 cx) _ HJ).
    - unfold spZ at 1. rewrite R2, le_E0_2. unfold w64. rewrite unsigned_lit_small by lia. lia.
    - assert (H16 : lsp1 cx mod 16 = 0)
        by (unfold lsp1; replace (32 * ((lsp0 cx - 256) / 32)) with ((2 * ((lsp0 cx - 256) / 32)) * 16) by lia;
            apply Z_mod_mult).
      rewrite Zminus_mod, H16, Hal16. reflexivity.
    - lia.
    - unfold LX_STK. change ESTACK with 4096. lia.
    - rewrite R3. rewrite (le_E0_reg cx 3 (3%bv : bv 5)) by first [reflexivity | discriminate]. exact Hgp.
    - rewrite R4. rewrite (le_E0_reg cx 4 (4%bv : bv 5)) by first [reflexivity | discriminate]. exact Htp.
    - exact R1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Hfr0. vm_compute. reflexivity. }
  cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fp & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2
    & Hbb2 & Hz & Hflag & HK & HJs & (fS & ES2)).
  rewrite Hfr0 in Hfrs2.
  replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) in HK, HJs by lia.
  pose proof HK as (HK1 & _).
  pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
  (* back at 0x80020: the saved words' window is above the callee's stack *)
  jafter_call_keep_pi HS 64%nat regs2 (mrestrict (w_H (lc_W cx)) mem2) HP2 [0%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.base_val]; rewrite Usp0; intros a Ha.
    - apply (mbyte_of_aview SEGS). apply HK1; [lia | change ESTACK with 4096; lia].
    - intros _. apply (apresent_writable SEGS). apply HJpres. unfold LX_STK; lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  clear R1 R2 R3 R4 HJ HK HJs SHOK.
  set (ms3 := mkst regs2 (Z_to_bv 64 (BASE + 116)) mem2 (seg_rom SEGS)) in *.
  assert (Hmm3 : ms_mem ms3 = mem2) by reflexivity.
  assert (Hrg3 : ms_regs ms3 = regs2) by reflexivity.
  change (frame_addr (lc_ly cx) 3 fp) with (lF cx fp) in *.
  change (flag_addr (lc_ly cx) 3 fp) with (lFL cx fp) in *.
  (* bind F, FL (atoms 46, 47) and the frame's shadow base (atom 22); a0 is F *)
  pose proof (st_ok_pi_havoc_hi 46 _ _ _ [w64 (lF cx fp); w64 (lFL cx fp)] HS ltac:(vm_compute; reflexivity)) as HS'.
  clear HS. rename HS' into HS.
  pose proof (st_ok_pi_havoc_hi 22 _ _ _ [w64 (lSH cx fp)] HS ltac:(vm_compute; reflexivity)) as HS'.
  clear HS. rename HS' into HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E3 eqn:HE3 end.
  assert (EA : forall n, (n < 22)%nat -> ew E3 n = ew (le_E0 cx) n).
  { intros n Hnn. subst E3. rewrite !ew_havoc_old by lia. reflexivity. }
  assert (EB : forall n, (23 <= n < 46)%nat -> ew E3 n = ew (le_E0 cx) n).
  { intros n Hnn. subst E3. rewrite ew_havoc_above by (cbn [length]; lia). rewrite !ew_havoc_old by lia. reflexivity. }
  assert (E3_22 : ew E3 22 = w64 (lSH cx fp)).
  { subst E3. exact (ew_havoc_new _ 22 [w64 (lSH cx fp)] 0 (w64 0) ltac:(cbn; lia)). }
  assert (E3_46 : ew E3 46 = w64 (lF cx fp)).
  { subst E3. rewrite ew_havoc_above by (cbn [length]; lia).
    exact (ew_havoc_new _ 46 [w64 (lF cx fp); w64 (lFL cx fp)] 0 (w64 0) ltac:(cbn; lia)). }
  assert (E3_47 : ew E3 47 = w64 (lFL cx fp)).
  { subst E3. rewrite ew_havoc_above by (cbn [length]; lia).
    exact (ew_havoc_new _ 46 [w64 (lF cx fp); w64 (lFL cx fp)] 1 (w64 0) ltac:(cbn; lia)). }
  assert (HEI3 : img_env VAL A_LIM E3).
  { subst E3. apply img_env_havoc; [|unfold A_TEXT; cbn [length]; lia].
    apply img_env_havoc; [|unfold A_TEXT; cbn [length]; lia].
    apply img_env_havoc; [exact HEI | unfold A_TEXT; rewrite length_map; cbn [length CLOB]; lia]. }
  assert (HE : lx_E cx fp E3).
  { unfold lx_E. split; [rewrite EA by (unfold LA_SP; lia); apply le_E0_2|].
    split; [rewrite EA by (unfold LA_SP0; lia); apply le_E0_8|].
    split; [rewrite EA by lia; apply (le_E0_reg cx 3 (3%bv : bv 5)); first [reflexivity | discriminate]|].
    split; [rewrite EA by lia; apply (le_E0_reg cx 4 (4%bv : bv 5)); first [reflexivity | discriminate]|].
    split; [exact E3_22|].
    split; [rewrite EB by (unfold LA_SB; lia); exact (le_E0_x cx 0 ltac:(lia))|].
    split; [|split; [exact E3_46 | exact E3_47]].
    intros j Hj. rewrite EB by (unfold LA_SAV; lia). unfold LA_SAV.
    replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite (le_E0_x cx (S j)) by lia.
    unfold lx_xatoms. cbn [app nth]. rewrite app_nth1 by (rewrite length_map; cbn [length lx_sregs map]; lia).
    reflexivity. }
  (* a0 holds F: name it by atom 46 *)
  pose proof (ast_ok_pi_set_reg_fp E3 _ _ (10%bv : bv 5) (SOff 46 0) HS eq_refl
    ltac:(cbn [ms_regs restrict]; rewrite lx_sv_SOff0, E3_46; subst ms3; cbn [ms_regs mkst]; rewrite Ha0; reflexivity))
    as HS'.
  clear HS. rename HS' into HS.
  le_norm HS.
  (* the seat's regions: the saved words (read-only from here), the spill slots, the frame, its shadow (zero) *)
  pose proof (lx_sp_facts B MT cx HB) as SPF.
  pose proof (lx_F_facts B MT LAWS cx fp (lc_W cx) ms3 (lc_ly cx) S2 md2 0 HB HJ2 Hfrs2)
    as (HF0 & HFc & HFia & HFo & HF64 & HSHeq).
  pose proof (lx_extents B MT LAWS cx fp (lc_W cx) ms3 (lc_ly cx) S2 md2 0 HB HJ2 Hfrs2 E3 HE)
    as (U8 & U2 & U46 & U22).
  assert (HSH0 : lshadow cx fp (lc_W cx) ms3 (repeat 0 64)).
  { intros i Hi. rewrite repeat_length in Hi. rewrite nth_repeat. unfold lview. rewrite Hmm3.
    unfold zero_shadow in Hz. change (fs_frame_bytes 3 / 8) with 64 in Hz.
    specialize (Hz (Z.of_nat i) ltac:(lia)). unfold shadow_of_addr in Hz. exact Hz. }
  assert (HSR0 : YP09.region_ok SEGS E3 (ms_mem (restrict (w_H (lc_W cx)) ms3)) lx_saved_region).
  { pose proof (st_ok_pi_region_nth E3 _ _ 0 _ HS eq_refl) as HR0.
    unfold lx_saved_region. eapply le_region_sub; [exact HR0|].
    intros c Hc. cbn [lx_saved_chunks In] in Hc. cbn [In].
    repeat (destruct Hc as [<- | Hc]; [repeat (first [left; reflexivity | right]) |]). destruct Hc. }
  set (G1 := mkFacts ((11%nat, mkAF 0 (2 ^ 26 - 1) 0) :: LX_AF) []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 46 0) (SLit 3)) (SOff 32 0), SOff 22 0)]).
  pose proof (le_restate E3 _ _ _ _ (lx_regions (repeat 0 64) [] [] 0 512 0 64 []) G1 _ HS) as HS'.
  specialize (HS' ltac:(vm_compute; reflexivity)).
  specialize (HS' ltac:(unfold lx_regions, lx_regions0; cbn [app];
    repeat apply Forall_cons; try apply Forall_nil;
    [ exact HSR0
    | exact (lx_region_spill B MT cx fp (lc_W cx) ms3 (lc_ly cx) S2 md2 0 HB HJ2 E3 [] HE (Forall_nil _))
    | exact (lx_region_frame B MT LAWS cx fp (lc_W cx) ms3 (lc_ly cx) S2 md2 0 HB HJ2 Hfrs2 E3 0 512 [] HE ltac:(lia) ltac:(vm_compute; intros; discriminate) Hflag (Forall_nil _))
    | exact (lx_region_shadow B MT LAWS cx fp (lc_W cx) ms3 (lc_ly cx) S2 md2 0 HB HJ2 Hfrs2 E3 (repeat 0 64) 0 64 HE
               ltac:(lia) ltac:(lia) HSH0) ])).
  specialize (HS' ltac:(unfold lx_regions; rewrite app_nil_r;
    exact (lx_disj B MT LAWS cx fp (lc_W cx) ms3 (lc_ly cx) S2 md2 0 HB HJ2 Hfrs2 E3 _ _ _ _ _ _ _ HE))).
  specialize (HS' ltac:(split; [cbn [G1 f_atoms atoms_ok]; split;
      [ unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EA by lia;
        rewrite (le_E0_reg cx 11 (11%bv : bv 5)) by first [reflexivity | discriminate]; rewrite H11; unfold w64;
        assert (Hn26 : 0 <= lc_n cx < 2 ^ 26) by (unfold lc_n in *; lia);
        rewrite unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia
      | exact (lx_af_ok B MT LAWS cx fp (lc_W cx) ms3 (lc_ly cx) S2 md2 0 HB HJ2 Hfrs2 E3 HE) ]
    | split; [exact I|]; cbn [G1 f_alias alias_ok]; split; [|exact I];
      pose proof HE as (_ & _ & _ & _ & _ & H32 & _);
      apply (shadow_decl_ok E3 46 32 22 (lF cx fp) SHADOW_OFF E3_46 ltac:(lia) H32);
      rewrite E3_22, HSHeq; reflexivity ])).
  clear HS. rename HS' into HS. clear HSR0.
  (* the frame header, the 52 shadow bytes, the slot 0x80, up to `bnez (n >> 26)` (0x80164) *)
  pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
  paj_run_sh RUNP HS HJ2.
  { cbn [ss_mem]. unfold lx_regions, lx_regions0, lx_saved_region, lx_spill_region, lx_frame_region, fframe_region,
      lx_shadow_region, fshadow_region. cbn [app]. change (fs_frame_bytes LX_CID) with 512. change (512 / 8) with 64.
    apply (le_awr B MT cx fp E3); [exact HB | exact U2 | exact U46 | exact U22 | reflexivity | lia | lia | apply awr_ok_nil]. }
  clear HF HFr HG.
  assert (U11 : U E3 (SOff 11 0) = lc_n cx).
  { apply U_atom; [|unfold lc_n in *; lia]. rewrite EA by lia.
    rewrite (le_E0_reg cx 11 (11%bv : bv 5)) by first [reflexivity | discriminate]. exact H11. }
  assert (SHOK : sh_ok SEGS CBR [] E3 (mrestrict (w_H (lc_W cx)) (ms_mem ms0))) by (unfold sh_ok; apply Forall_nil).
  pose proof (paj_branch (PI := PI)) as BR.
  psrr_branch_tok RUN BR HS SHOK BspanR.
  { (* n >> 26 <> 0: lx_base has n < 2 ^ 26 *)
    exfalso. rewrite branch_ne_U, le_U_srl26, U11, U_lit in Hc by lia.
    assert (Hn26 : 0 <= lc_n cx < 2 ^ 26) by (unfold lc_n in *; lia).
    rewrite Z.div_small in Hc by lia. discriminate Hc. }
  clear Hc.
  (* the shadow bytes are written: their window closes (the token runner checks the shadow span) *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
    pose proof (ast_ok_pi_set_region Ex ssx msx 3 _ (set_window (nth 3 (ss_mem ssx) lx_saved_region) 0 0) HS eq_refl
      eq_refl ltac:(vm_compute; reflexivity)
      (region_ok_rewindow SEGS Ex _ _ 0 0 (st_ok_pi_region_nth Ex ssx msx 3 _ HS eq_refl) ltac:(intros o Ho; lia)))
      as HS' end.
  clear HS. rename HS' into HS. le_norm HS.
  (* the slots 0x18 / 0x10 / 0x88 / 0x90, up to malloc (0x120) (0x8017c); the frame's window is a reversed shadow
     entry for the token runner (BoxBLxSeat.v lx_shent_rev) *)
  pose proof HE as (_ & _ & _ & _ & _ & H32E & _).
  assert (UB32 : U E3 (SOff LA_SB 0) = SHADOW_OFF) by (apply U_atom; [exact H32E | unfold SHADOW_OFF; lia]).
  assert (UB46 : U E3 (SOff LA_F 0) = lF cx fp) by (apply U_atom; [exact E3_46 | lia]).
  assert (SHOK2 : sh_ok SEGS CBR [mkSHE LA_F 512 0] E3 (mrestrict (w_H (lc_W cx)) (ms_mem ms0))).
  { unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
    exact (lx_shent_rev E3 _ (lF cx fp) 512 LA_F UB32 UB46 HFia ltac:(lia)). }
  clear SHOK.
  paj_run_tok RUN HS HJ2 SHOK2 BspanR.
  { cbn [ss_mem].
    apply (le_awr B MT cx fp E3); [exact HB | exact U2 | exact U46 | exact U22 | reflexivity | lia | lia | apply awr_ok_nil]. }
  clear HF HFr HG. repeat rewrite wvb_collapse in HJ2.
  (* malloc (0x120) (0x8017c): the registry r *)
  assert (HSV1 : lsaved cx (lc_W cx) ms1).
  { lazymatch type of HS with st_ok _ _ (setpc ?ssx ?pcx) ?msx =>
      assert (HSpi : st_ok_pi SEGS VAL E3 (setpc ssx (pcx - BASE)) msx)
        by (unfold st_ok_pi, abs_ss; cbn [ss_pc setpc]; replace (BASE + (pcx - BASE)) with pcx by lia; exact HS) end.
    exact (lx_saved_of_ss B MT cx fp (lc_W cx) ms1 HB E3 _ HE HSpi eq_refl). }
  pmkst HS.
  prreg HS (10%bv : bv 5) Ra0. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  prreg HS (1%bv : bv 5) R1. prreg HS (8%bv : bv 5) R8.
  rewrite (pal_malloc B TL).
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & HJ2F1 & _).
  assert (Hach : achain (lc_ly cx) (aview SEGS (w_H (lc_W cx)) (ms_mem ms1)) (lsp1 cx) (lsp0 cx) (lch cx)).
  { pose proof Hstk as (_ & _ & _ & _ & _ & H47 & _ & Htop & Htop2).
    pose proof HSV1 as (Hsv8 & Hsvj).
    assert (Hal8 : lsp0 cx mod 8 = 0).
    { pose proof (Z.div_mod (lsp0 cx) 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
      replace (16 * (lsp0 cx / 16)) with ((2 * (lsp0 cx / 16)) * 8) by lia. apply Z_mod_mult. }
    apply (lx_achain cx _ (lsp1 cx) Hch); [lia | lia | exact Hal8 | exact Hra4 | | exact Hsv8 | | lia].
    - intros a Ha. apply HJ2F1; [lia | lia].
    - pose proof (Hsvj 0 ltac:(lia)) as H16. replace (lsp0 cx - 16 - 8 * 0) with (lsp0 cx - 16) in H16 by lia.
      exact H16. }
  assert (HraT : raZ (ms_regs ms1) = BASE + 0x1d4).
  { unfold raZ. rewrite R1. apply unsigned_lit_small. pose proof pa_B_ok. lia. }
  assert (HspT : spZ (ms_regs ms1) = lsp1 cx).
  { unfold spZ. rewrite R2, EA, le_E0_2 by lia. unfold w64. apply unsigned_lit_small. lia. }
  pose proof (lh_mtl B MT HY) as MLAW. pose proof (lh_mtfl B MT HY) as MLAWF.
  assert (HA0 : 0 <= mo_free MT /\ 0 <= mo_malloc MT 48 /\ 0 <= mo_malloc MT LX_REG).
  { split; [apply (mo_free_nonneg MT MLAW)|]. split; apply (mo_malloc_nonneg MT MLAW); unfold LX_REG; lia. }
  eapply SRr_bind.
  { eapply (amalloc04_sub SEGS B LAWS Hsegs MT (lh_malloc B MT HY) (lc_W cx) _ _ LX_STK (lsp0 cx) [] (lc_ly cx)
      (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx) [(3, fp)] (lc_ly cx) S2 _ 0 288 (lsp1 cx - lsp0 cx) _ (lch cx) HJ2).
    - rewrite Ra0. reflexivity.
    - unfold MALLOC_MAX. lia.
    - rewrite Hbb2. unfold LX_LIVE in Hlive. unfold LIVE_MAX in *. lia.
    - rewrite HspT. lia.
    - assert (H16 : lsp1 cx mod 16 = 0)
        by (unfold lsp1; replace (32 * ((lsp0 cx - 256) / 32)) with ((2 * ((lsp0 cx - 256) / 32)) * 16) by lia;
            apply Z_mod_mult).
      rewrite Zminus_mod, H16, Hal16. reflexivity.
    - lia.
    - unfold LX_STK, ASTACK. lia.
    - rewrite R3, EA by lia. rewrite (le_E0_reg cx 3 (3%bv : bv 5)) by first [reflexivity | discriminate]. exact Hgp.
    - rewrite R4, EA by lia. rewrite (le_E0_reg cx 4 (4%bv : bv 5)) by first [reflexivity | discriminate]. exact Htp.
    - exact R1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Hnev2. unfold LX_EV in Hnev. unfold EV_MAX in *. lia.
    - apply (achain_chain_pre (lc_ly cx) _ (lsp1 cx) (lsp0 cx) (lch cx) _ Hach).
      + rewrite HspT. lia.
      + unfold s0Z. rewrite R8, EA, le_E0_8 by lia. unfold w64. apply unsigned_lit_small. lia.
      + rewrite HraT. pose proof pa_base_lo. lia.
    - apply Htr. left. split; [reflexivity|]. rewrite HraT. replace (BASE + 0x1d4 - BASE) with 0x1d4 by lia.
      left. reflexivity.
    - rewrite ES2. apply (mo_ok_set_fs MT MLAWF). apply (mo_ok_le MT MLAW _ _ (lc_T cx) Hmok).
      unfold LX_NEED, LX_A1, LX_AI in Hneed. change 288 with LX_REG. lia. }
  cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & r & -> & HJ4 & HP4 & Hr10 & Hfrs4 & Hr4096 & Hbl4 & HK4
    & Hmle4 & HJm).
  replace (lsp0 cx + (lsp1 cx - lsp0 cx)) with (lsp1 cx) in HK4, HJm by lia.
  change (0 + 1) with 1 in HJ4. rewrite Hfrs2 in Hfrs4.
  pose proof HJ4 as (HAR4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ4pres & _).
  assert (Hrin4 : In (r, 288) (ablocks B ly4 S4)) by (rewrite Hbl4; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r 288 HAR4 Hrin4) as (Hr16 & _ & Hrceil & Hria & Hrpres & _ & _).
  change (req_size 288) with 288 in *.
  set (ms4 := mkst regs4 (Z_to_bv 64 (BASE + 468)) mem4 (seg_rom SEGS)) in *.
  assert (Hfa4 : frame_addr ly4 3 fp = lF cx fp)
    by exact (lx_frame_addr_eq B MT LAWS cx fp W4 ms4 ly4 S4 md4 1 HB HJ4).
  assert (HdrF : r + 288 <= lF cx fp \/ lF cx fp + 512 <= r).
  { pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ r 288 3 fp HAR4 Hrin4 ltac:(rewrite Hfrs4; left; reflexivity))
      as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hfa4 in Hd. change (req_size 288) with 288 in Hd.
    change (fs_frame_bytes 3) with 512 in Hd. lia. }
  destruct (al_frames _ _ LAWS _ _ _ _ _ 3 fp HAR4 ltac:(rewrite Hfrs4; left; reflexivity)) as (_ & _ & HF4pres & _).
  rewrite Hfa4 in HF4pres. change (fs_frame_bytes 3) with 512 in HF4pres.
  pose proof HK4 as (HK41 & _ & _ & HK44 & _).
  (* back at 0x80180: the seat's four regions are kept *)
  jafter_call_keep_pi HS 80%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1; 2; 3]%nat HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    apply (le_kept4 cx fp E3); [exact U8 | exact U2 | exact U46 | exact U22 | lia | lia | |].
    - intros a [Ha | [Ha | Ha]].
      + apply HK41; [lia | unfold ASTACK; lia].
      + apply (HK44 3 fp a ltac:(rewrite Hfrs2; left; reflexivity)); [left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 3) with 512; exact Ha | lia].
      + apply (HK44 3 fp a ltac:(rewrite Hfrs2; left; reflexivity)); [right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 3 / 8) with 64; exact Ha |].
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hria. rewrite HSHeq in Ha.
        assert (Hd1 : lF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
        unfold SHADOW_OFF in Ha. lia.
    - intros a [Ha | [Ha | Ha]]; [apply HJ4pres; unfold LX_STK, LX_SPILL in *; lia | apply HF4pres; lia | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. fold ms4 in HS.
  remember (havoc E3 80 (map (getr regs4) CLOB)) as E4 eqn:HEq4.
  assert (EA4 : forall n, (n < 80)%nat -> ew E4 n = ew E3 n) by (intros n Hnn; rewrite HEq4; apply ew_havoc_old; exact Hnn).
  assert (HE4 : lx_E cx fp E4) by (apply (lx_E_agree cx fp E3 E4 HE); intros n Hnn; apply EA4; unfold LA_EX in Hnn; lia).
  assert (HEI4 : img_env VAL A_LIM E4)
    by (rewrite HEq4; apply img_env_havoc; [exact HEI3 | unfold A_TEXT; rewrite length_map; cbn [length CLOB]; lia]).
  assert (E4_84 : ew E4 84 = w64 r).
  { rewrite HEq4. rewrite (ew_havoc_new E3 80 _ 4 (w64 0)) by (rewrite length_map; cbn; lia).
    cbn [CLOB map nth]. exact Hr10. }
  pose proof (lx_extents B MT LAWS cx fp W4 ms4 ly4 S4 md4 1 HB HJ4 Hfrs4 E4 HE4) as (U8' & U2' & U46' & U22').
  clear U8 U2 U46 U22. rename U8' into U8, U2' into U2, U46' into U46, U22' into U22.
  (* r: a heap block, 16-aligned, at least 4096 *)
  pose proof (st_ok_pi_add_fact E4 _ _ 84 (mkAF 4096 140737479966720 4) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E4_84; unfold w64; rewrite unsigned_lit_small by lia;
          change (2 ^ 4) with 16; lia)) as HS'.
  clear HS. rename HS' into HS. le_norm HS.
  pose proof HE4 as (_ & _ & _ & _ & _ & H32E4 & _).
  assert (UB32' : U E4 (SOff LA_SB 0) = SHADOW_OFF) by (apply U_atom; [exact H32E4 | unfold SHADOW_OFF; lia]).
  assert (UB46' : U E4 (SOff LA_F 0) = lF cx fp) by (apply U_atom; [rewrite EA4 by (unfold LA_F; lia); exact E3_46 | lia]).
  assert (SHOK : sh_ok SEGS CBR [mkSHE LA_F 512 0] E4 (mrestrict (w_H W4) (ms_mem ms4))).
  { unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
    exact (lx_shent_rev E4 _ (lF cx fp) 512 LA_F UB32' UB46' HFia ltac:(lia)). }
  clear SHOK2.
  (* `beqz a0` (NULL) is decided by r's fact; the run stops at `beqz n` (0x8018c) *)
  paj_run_tok RUN HS HJ4 SHOK BspanR.
  { cbn [ss_mem].
    apply (le_awr B MT cx fp E4); [exact HB | exact U2 | exact U46 | exact U22 | exact Hfa4 | lia | lia | apply awr_ok_nil]. }
  clear HF HFr HG. repeat rewrite wvb_collapse in HJ4.
  assert (Hblk4 : forall q m, In (q, m) (ablocks B (lc_ly cx) (lc_S cx)) -> In (q, m) (ablocks B ly4 S4)).
  { intros q m Hq. rewrite Hbl4, Eab. apply in_or_app. left. exact Hq. }
  (* fuzz_u8: n = 0 gives 0; else the first input byte *)
  psrr_branch_tok RUN BR HS SHOK BspanR.
  2:{ (* n <> 0: the input block, its first byte (atom 96) and the shadow entry of its first byte *)
    rewrite branch_eq_U, U_lit, (U_atom E4 11 (lc_n cx)) in Hc by first [lia | rewrite EA4, EA by lia;
      rewrite (le_E0_reg cx 11 (11%bv : bv 5)) by first [reflexivity | discriminate]; exact H11 | unfold lc_n in *; lia].
    apply Z.eqb_neq in Hc.
    destruct Hn as [[Hn0 _] | ((Hnpos & Hn26) & Hpin)]; [exfalso; exact (Hc Hn0)|].
    assert (Hpin4 : In (lc_p cx, lc_n cx) (ablocks B ly4 S4)) by exact (Hblk4 _ _ Hpin).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (Hpin)) as (Hp16 & Hp4096 & Hpceil & Hpia & _ & _ & _).
    pose proof (req_size_pos (lc_n cx) ltac:(lia)) as (_ & Hrq).
    assert (Hpl : (0 < length (lc_pl cx))%nat) by (unfold lc_n in Hnpos; lia).
    set (b0 := nth 0 (map (fun b : byte => bv_unsigned b) (lc_pl cx)) 0) in *.
    destruct (Hgarr 0%nat ltac:(rewrite length_map; exact Hpl)) as (Hb0 & Hb0r). fold b0 in Hb0, Hb0r.
    assert (Hb04 : val_mem SEGS (mrestrict (w_H W4) (ms_mem ms2)) (lc_p cx + 0) 1 b0).
    { apply (le_val_mem_kept _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4 Hpin Hpin4); [lia | exact Hb0]. }
    pose proof (st_ok_pi_havoc_hi 96 _ _ _ [w64 b0] HS ltac:(vm_compute; reflexivity)) as HS'.
    clear HS. rename HS' into HS.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E5 eqn:HEq5 end.
    assert (EA5 : forall n, (n < 96)%nat -> ew E5 n = ew E4 n) by (intros n Hnn; rewrite HEq5; apply ew_havoc_old; exact Hnn).
    assert (E5_96 : ew E5 96 = w64 b0) by (rewrite HEq5; exact (ew_havoc_new E4 96 [w64 b0] 0 (w64 0) ltac:(cbn; lia))).
    assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HEq5; apply img_env_havoc; [exact HEI4 | unfold A_TEXT; cbn; lia]).
    assert (E5_10 : ew E5 10 = w64 (lc_p cx)).
    { rewrite EA5, EA4, EA by lia. rewrite (le_E0_reg cx 10 (10%bv : bv 5)) by first [reflexivity | discriminate].
      exact H10. }
    pose proof (st_ok_pi_add_fact E5 _ _ 10 (mkAF 4096 140737479966720 4) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E5_10; unfold w64; rewrite unsigned_lit_small by lia;
            change (2 ^ 4) with 16; lia)) as HS'.
    clear HS. rename HS' into HS.
    pose proof (st_ok_pi_add_fact E5 _ _ 96 (mkAF 0 255 0) HS
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E5_96; unfold w64; rewrite unsigned_lit_small by lia;
            rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS'.
    clear HS. rename HS' into HS. le_norm HS.
    assert (HE5 : lx_E cx fp E5)
      by (apply (lx_E_agree cx fp E4 E5 HE4); intros n Hnn; apply EA5; unfold LA_EX in Hnn; lia).
    pose proof HJ4 as (HAR4' & _).
    pose proof (lx_extents B MT LAWS cx fp W4 ms2 ly4 S4 _ 1 HB HJ4 Hfrs4 E5 HE5) as (V8 & V2 & V46 & V22).
    assert (Vp : YP09.base_val E5 (Some 10%nat) = lc_p cx) by (cbn [YP09.base_val]; rewrite E5_10; apply unsigned_lit_small; lia).
    assert (HdpF : lc_p cx + lc_n cx <= lF cx fp \/ lF cx fp + 512 <= lc_p cx).
    { pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ 3 fp HAR4' Hpin4 ltac:(rewrite Hfrs4; left; reflexivity))
        as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hfa4 in Hd. change (fs_frame_bytes 3) with 512 in Hd.
      lia. }
    lazymatch type of HS with st_ok_pi _ _ _ (mkSST ?pcx ?srx [] ?rsx None ?Gx) ?msx =>
      pose proof (le_add_region_end E5 pcx srx rsx Gx
        (YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 96 0))]) msx HS
        ltac:(vm_compute; reflexivity)) as HS' end.
    specialize (HS' ltac:(unfold YP09.region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]; rewrite Vp;
      split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
      apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_val SEGS E5 _ (lc_p cx) 0 1 (SOff 96 0) b0);
        [rewrite lx_sv_SOff0, E5_96; reflexivity | cbn; lia | cbn; lia | exact Hb04])).
    assert (Hd1 : lF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia).
    assert (Hd0 : 0 <= lF cx fp / 8) by (apply Z.div_pos; lia).
    assert (Hrqn : req_size (lc_n cx) = lc_n cx) by (unfold req_size; destruct (Z.eqb_spec (lc_n cx) 0); lia).
    rewrite Hrqn in Hpceil, Hpia.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpia.
    unfold LA_SP0, LA_SP, LA_F, LA_FSH in V8, V2, V46, V22.
    specialize (HS' ltac:(
      repeat apply Forall_cons; try apply Forall_nil;
      (split; [|exact I];
       unfold YP09.extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi];
       rewrite ?V8; rewrite ?V2; rewrite ?V46; rewrite ?V22; rewrite Vp; rewrite ?HSHeq; unfold SHADOW_OFF; lia))).
    clear HS. rename HS' into HS. le_norm HS.
    pose proof HE5 as (_ & _ & _ & _ & _ & H32E5 & _).
    assert (UB32'' : U E5 (SOff LA_SB 0) = SHADOW_OFF) by (apply U_atom; [exact H32E5 | unfold SHADOW_OFF; lia]).
    assert (UB46'' : U E5 (SOff LA_F 0) = lF cx fp) by (apply U_atom; [rewrite EA5, EA4 by (unfold LA_F; lia); exact E3_46 | lia]).
    assert (Up10 : U E5 (SOff 10 0) = lc_p cx) by (apply U_atom; [exact E5_10 | lia]).
    assert (SHOK5 : sh_ok SEGS CBR [mkSHE LA_F 512 0; mkSHE 10 0 1] E5 (mrestrict (w_H W4) (ms_mem ms2))).
    { unfold sh_ok. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      - exact (lx_shent_rev E5 _ (lF cx fp) 512 LA_F UB32'' UB46'' HFia ltac:(lia)).
      - exact (lx_shent_block B LAWS _ _ _ _ _ E5 (lc_p cx) (lc_p cx) (lc_n cx) 0 1 10 HAR4' Hpin4 UB32'' Up10
                 ltac:(lia) ltac:(lia) ltac:(lia)). }
    clear SHOK.
    (* `bgeu 1, p + 1` (UBSan) and the shadow check of p are decided; lbu s3; up to reac_boxreg_init *)
    paj_run_tok RUN HS HJ4 SHOK5 BspanR.
    { cbn [ss_mem].
      apply (le_awr B MT cx fp E5); [exact HB | exact V2 | exact V46 | exact V22 | exact Hfa4 | lia | lia |].
      apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
    clear HF HFr HG. repeat rewrite wvb_collapse in HJ4.
    (* the cut at reac_boxreg_init: the input cursor at p + 1 / n - 1 (atoms 97 / 98) *)
    lazymatch type of HS with st_ok _ ?Ex _ _ => remember Ex as Ec eqn:HEqc end.
    assert (EAc : forall n, (n < 512)%nat -> ew Ec n = ew E5 n)
      by (intros n Hnn; rewrite HEqc; rewrite !ew_ewset_other by lia; reflexivity).
    assert (HEIc : img_env VAL A_LIM Ec) by (first [assumption | rewrite HEqc; assumption]).
    pose proof (le_st_ok_havoc 97 Ec _ _ [w64 (lc_p cx + 1); w64 (lc_n cx - 1)] _ HS ltac:(vm_compute; reflexivity)) as HS'.
    clear HS. rename HS' into HS.
    remember (havoc Ec 97 [w64 (lc_p cx + 1); w64 (lc_n cx - 1)]) as Ed eqn:HEqd.
    assert (EAd : forall n, (n < 97)%nat -> ew Ed n = ew E5 n) by (intros n Hnn; rewrite HEqd, ew_havoc_old by lia; apply EAc; lia).
    assert (Ed97 : ew Ed 97 = w64 (lc_p cx + 1))
      by (rewrite HEqd; exact (ew_havoc_new Ec 97 [w64 (lc_p cx + 1); w64 (lc_n cx - 1)] 0 (w64 0) ltac:(cbn; lia))).
    assert (Ed98 : ew Ed 98 = w64 (lc_n cx - 1))
      by (rewrite HEqd; exact (ew_havoc_new Ec 97 [w64 (lc_p cx + 1); w64 (lc_n cx - 1)] 1 (w64 0) ltac:(cbn; lia))).
    assert (HEId : img_env VAL A_LIM Ed) by (rewrite HEqd; apply img_env_havoc; [exact HEIc | unfold A_TEXT; cbn; lia]).
    assert (HEd : lx_E cx fp Ed) by (apply (lx_E_agree cx fp E5 Ed HE5); intros n Hnn; apply EAd; unfold LA_EX in Hnn; lia).
    cbn [setpc] in HS.
    pose proof (le_normalize Ed _ _ le_regs_C _ [lx_saved_region; le_spill_C; le_frame_C; le_shadow_C] _ le_facts_C _ HS) as HSC.
    specialize (HSC ltac:(intros rr; reflexivity)).
    specialize (HSC ltac:(vm_compute; reflexivity)).
    assert (Ed10 : ew Ed 10 = w64 (lc_p cx)) by (rewrite EAd by lia; exact E5_10).
    assert (Ed11 : ew Ed 11 = w64 (lc_n cx)).
    { rewrite EAd, EA5, EA4, EA by lia. rewrite (le_E0_reg cx 11 (11%bv : bv 5)) by first [reflexivity | discriminate].
      exact H11. }
    assert (He1 : sv_denot Ed (SOff 10 1) = sv_denot Ed (SOff 97 0)).
    { rewrite lx_sv_SOff0, Ed97. cbn [sv_denot]. rewrite Ed10. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    assert (He2 : sv_denot Ed (SOff 11 (-1)) = sv_denot Ed (SOff 98 0)).
    { rewrite lx_sv_SOff0, Ed98. cbn [sv_denot]. rewrite Ed11. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    specialize (HSC ltac:(
      repeat apply Forall_cons; try apply Forall_nil;
      [ exact (st_ok_region_nth Ed _ _ 0 _ HS eq_refl)
      | exact (le_spill_swap Ed _ _ _ _ _ _ _ _ (st_ok_region_nth Ed _ _ 1 _ HS eq_refl) He1 He2)
      | exact (st_ok_region_nth Ed _ _ 2 _ HS eq_refl)
      | exact (st_ok_region_nth Ed _ _ 3 _ HS eq_refl) ])).
    pose proof (lx_disj B MT LAWS cx fp W4 ms0 ly4 S4 _ 1 HB HJ4 Hfrs4 Ed (repeat 0 64) [] [] 0 512 0 0 HEd) as Hpd0.
    specialize (HSC ltac:(apply pairwise_disjoint_of_extents; exact (zpairwise_of_pairwise _ _ Hpd0))).
    pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & (HGa & _ & HGl)).
    assert (HFC : facts_ok Ed le_facts_C).
    { split; [|split; [exact I | exact HGl]].
      eapply atoms_ok_incl; [|exact HGa].
      intros x Hx. cbn [le_facts_C f_atoms] in Hx. unfold LX_AF in Hx. cbn [In] in Hx |- *.
      repeat (destruct Hx as [<- | Hx]; [repeat (first [left; reflexivity | right]) |]). destruct Hx. }
    specialize (HSC HFC). clear HS HGa HGl HFC. rename HSC into HS.
    (* to the rest of the walk *)
    apply (le_from_C HD POST cx fp Ed W4 ms0 _ ly4 S4 r b0 1 HFROM HB HS HEId HEd).
    - rewrite EAd, EA5 by lia. exact E4_84.
    - rewrite EAd by lia. exact E5_96.
    - lia.
    - exact Ed97.
    - exact Ed98.
    - lia.
    - exact HJ4.
    - exact Hfrs4.
    - unfold LX_A1, LX_REG. replace (mo_malloc MT 288) with (0 + mo_malloc MT 288) by lia.
      apply (mle_station MT _ S2 _ 0 _ MLAW); [|exact Hmle4].
      rewrite ES2. apply (mo_le_set_fs_r MT MLAWF). exact (mle_start MT _ MLAW).
    - rewrite Hbl4, Eab. reflexivity. }
  (* n = 0: s3 = 0; up to reac_boxreg_init *)
  paj_run_tok RUN HS HJ4 SHOK BspanR.
  { cbn [ss_mem].
    apply (le_awr B MT cx fp E4); [exact HB | exact U2 | exact U46 | exact U22 | exact Hfa4 | lia | lia | apply awr_ok_nil]. }
  clear HF HFr HG. repeat rewrite wvb_collapse in HJ4.
  (* the cut at reac_boxreg_init: the byte 0 (atom 96), the input cursor at p / n (atoms 97 / 98), a2 (atom 513) *)
  pose proof (le_st_ok_havoc 96 E4 _ _ [w64 0] _ HS ltac:(vm_compute; reflexivity)) as HS'.
  clear HS. rename HS' into HS.
  pose proof (le_st_ok_havoc 97 _ _ _ [w64 (lc_p cx); w64 (lc_n cx)] _ HS ltac:(vm_compute; reflexivity)) as HS'.
  clear HS. rename HS' into HS.
  pose proof (le_st_ok_havoc 513 _ _ _ [ew E4 86] _ HS ltac:(vm_compute; reflexivity)) as HS'.
  clear HS. rename HS' into HS.
  lazymatch type of HS with st_ok _ ?Ex _ _ => remember Ex as Ed eqn:HEqd end.
  assert (EAd : forall n, (n < 96)%nat -> ew Ed n = ew E4 n) by (intros n Hnn; rewrite HEqd, !ew_havoc_old by lia; reflexivity).
  assert (Ed96 : ew Ed 96 = w64 0).
  { rewrite HEqd, ew_havoc_old by lia. rewrite ew_havoc_old by lia.
    exact (ew_havoc_new E4 96 [w64 0] 0 (w64 0) ltac:(cbn; lia)). }
  assert (Ed97 : ew Ed 97 = w64 (lc_p cx)).
  { rewrite HEqd, ew_havoc_old by lia. exact (ew_havoc_new _ 97 [w64 (lc_p cx); w64 (lc_n cx)] 0 (w64 0) ltac:(cbn; lia)). }
  assert (Ed98 : ew Ed 98 = w64 (lc_n cx)).
  { rewrite HEqd, ew_havoc_old by lia. exact (ew_havoc_new _ 97 [w64 (lc_p cx); w64 (lc_n cx)] 1 (w64 0) ltac:(cbn; lia)). }
  assert (Ed513 : ew Ed 513 = ew E4 86).
  { rewrite HEqd. exact (ew_havoc_new _ 513 [ew E4 86] 0 (w64 0) ltac:(cbn; lia)). }
  assert (HEId : img_env VAL A_LIM Ed).
  { rewrite HEqd. apply img_env_havoc_hi; [|unfold A_LIM; lia].
    apply img_env_havoc; [|unfold A_TEXT; cbn; lia]. apply img_env_havoc; [exact HEI4 | unfold A_TEXT; cbn; lia]. }
  assert (HEd : lx_E cx fp Ed) by (apply (lx_E_agree cx fp E4 Ed HE4); intros n Hnn; apply EAd; unfold LA_EX in Hnn; lia).
  cbn [setpc] in HS.
  pose proof (le_normalize Ed _ _ le_regs_C _ [lx_saved_region; le_spill_C; le_frame_C; le_shadow_C] _ le_facts_C _ HS) as HSC.
  destruct (le_sext8_0 Ed Ed96) as (Hsx1 & Hsx2).
  lazymatch type of HSC with ?A -> _ => assert (HRG : A) end.
  { intros rr. pose proof (all_regs_in rr) as Hin. cbv [all_regs In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [ lazymatch goal with |- sv_denot _ (sr_get ?l1 ?q) = sv_denot _ (sr_get ?l2 ?q) =>
          let e1 := eval vm_compute in (sr_get l1 q) in let e2 := eval vm_compute in (sr_get l2 q) in
          change (sv_denot Ed e1 = sv_denot Ed e2) end;
        first
        [ reflexivity
        | (transitivity (Z_to_bv 64 0); [first [exact Hsx1 | exact Hsx2 | (rewrite lx_sv_SOff0; exact Ed96)] | reflexivity])
        | (rewrite !lx_sv_SOff0, Ed513; symmetry; apply EAd; lia) ]
      |]).
    destruct Hin. }
  specialize (HSC HRG). clear HRG.
  specialize (HSC ltac:(vm_compute; reflexivity)).
  assert (He1 : sv_denot Ed (SOff 10 0) = sv_denot Ed (SOff 97 0)).
  { rewrite !lx_sv_SOff0, Ed97, EAd, EA4, EA by lia.
    rewrite (le_E0_reg cx 10 (10%bv : bv 5)) by first [reflexivity | discriminate]. exact H10. }
  assert (He2 : sv_denot Ed (SOff 11 0) = sv_denot Ed (SOff 98 0)).
  { rewrite !lx_sv_SOff0, Ed98, EAd, EA4, EA by lia.
    rewrite (le_E0_reg cx 11 (11%bv : bv 5)) by first [reflexivity | discriminate]. exact H11. }
  specialize (HSC ltac:(
    repeat apply Forall_cons; try apply Forall_nil;
    [ exact (st_ok_region_nth Ed _ _ 0 _ HS eq_refl)
    | exact (le_spill_swap' Ed _ _ _ _ _ _ _ _ (st_ok_region_nth Ed _ _ 1 _ HS eq_refl) He1 He2)
    | exact (st_ok_region_nth Ed _ _ 2 _ HS eq_refl)
    | exact (st_ok_region_nth Ed _ _ 3 _ HS eq_refl) ])).
  pose proof (lx_disj B MT LAWS cx fp W4 ms0 ly4 S4 _ 1 HB HJ4 Hfrs4 Ed (repeat 0 64) [] [] 0 512 0 0 HEd) as Hpd0.
  specialize (HSC ltac:(apply pairwise_disjoint_of_extents; exact (zpairwise_of_pairwise _ _ Hpd0))).
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & (HGa & _ & HGl)).
  assert (HFa84 : atoms_ok Ed ((84%nat, mkAF 4096 140737479966720 4) :: LX_AF)).
  { eapply atoms_ok_incl; [|exact HGa].
    intros x Hx. unfold LX_AF in Hx. cbn [In] in Hx |- *.
    repeat (destruct Hx as [<- | Hx]; [repeat (first [left; reflexivity | right]) |]). destruct Hx. }
  assert (HFa96 : afact_ok Ed 96 (mkAF 0 255 0)).
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ed96. unfold w64. rewrite unsigned_lit_small by lia.
    rewrite Z.pow_0_r, Z.mod_1_r. lia. }
  specialize (HSC (conj (conj HFa96 HFa84) (conj I HGl))). clear HS HGa HGl HFa84 HFa96. rename HSC into HS.
  (* to the rest of the walk *)
  apply (le_from_C HD POST cx fp Ed W4 ms0 _ ly4 S4 r 0 0 HFROM HB HS HEId HEd).
  - rewrite EAd by lia. exact E4_84.
  - exact Ed96.
  - lia.
  - rewrite Z.add_0_r. exact Ed97.
  - rewrite Z.sub_0_r. exact Ed98.
  - lia.
  - exact HJ4.
  - exact Hfrs4.
  - unfold LX_A1, LX_REG. replace (mo_malloc MT 288) with (0 + mo_malloc MT 288) by lia.
    apply (mle_station MT _ S2 _ 0 _ MLAW); [|exact Hmle4].
    rewrite ES2. apply (mo_le_set_fs_r MT MLAWF). exact (mle_start MT _ MLAW).
  - rewrite Hbl4, Eab. reflexivity.
Qed.

(* The entry phase: cut D from BoxBLxEntryD.v le_D, which closes on cut K by BoxBLxEntryK.v le_K. *)
Theorem lx_entry : forall POST, lx_from B MT POST (LI_J B MT 0) -> lx_start B MT POST.
Proof. exact (lx_entry_of (BoxBLxEntryD.le_D B MT HY (BoxBLxEntryK.le_K B MT HY))). Qed.

End a.
