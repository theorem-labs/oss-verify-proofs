(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:132-134;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:140-147, 156-161;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACev.v:181-184; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACjv.v:45-48, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* reac_box_name (fuzz_identity.asan-ubsan 0x82d74, AF_reac_box_name = 0x2600), segment "entry" of the program
   walk: from the first slot to the cut point C1 (0x83000, +0x28c, back from memset #1) and, for the argument checks
   that refuse, to the frame release R (0x834ac, +0x738). Lemma rbn_seg_entry; lib/B/Prog/reac_box_name.v chains it.
   The cut states are those of lib/B/Prog/reac_box_name_inv.v (rbn_pre, rbn_C1, rbn_R).
   The segment is cut at three inner points (offsets from 0x82d74), stated below as rbe_X1 / rbe_X2a / rbe_X2:
     X1  0x82f10 +0x19c  the class-3 frame taken, its header (magic, the two description words) and its 36 shadow
                         bytes written, s4 = -1; the argument checks next;
     X2a 0x82f68 +0x1f4  the arguments accepted (0x82f10 .. 0x82f64), a4 = display;
     X2  0x82fc8 +0x254  in / out stored, s9 = the stem (said, the table entry for f in 1 .. 3, or "REAC").
   Pieces: rbe_e1 (entry -> X1: the prologue, sp realigned to 32 (andi, a fresh atom for s1), the use-after-return
   flag cell holds 1 (AR_const_law with PALibF) so the real-stack fallback 0x82e10 .. 0x82e38 is not reached,
   __asan_stack_malloc_3(288) through aj_stack_malloc_atS with ASM3, the frame / shadow regions and the alias of
   the frame's shadow address, the stores of 0x82e3c .. 0x82f08), rbe_e2a (X1 -> R for every refusal, with
   bn_args_ok false there, or X2a), rbe_e2b (X2a -> X2: the ASan checks of said and of the table word go through
   the token engine), rbe_e2c (X2 -> C1: the window stores, w4's scope byte, memset(s1 + 200, 0, 16) through
   aj_intrin_atS with AMEMSET). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YI08 YI09 YI0s YI0t YI0m YI0n YP0g.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBProgSig IdentBCJ IdentBFrame YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import sb_ch sb_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import reac_box_name_sbm reac_box_name_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_name_c sb_dec_c box_name_lemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* #[local]: this flag must not leak to files that Require this one. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section h.
Variable B : asyms.
Variable G : list (Z * Z).
Section walk.
Context {RO : ro_below_ofl SEGS (@pa_relro_lo _ identb_listing PI) (@pa_relro_hi _ identb_listing PI)}.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis GM : globs_marked SEGS B G.
Hypothesis IV : img_shadow_vis SEGS B.
Hypothesis PSIG : identb_prog_sig_ok.
Hypothesis HSC : tsb_ch_spec B.
Hypothesis HSB : tsb_dec_spec B.
Hypothesis ASM3 : astack_malloc_realizes SEGS B 3.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA IB___asan_memset).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
(* ---- The cut states inside the entry segment (offsets from 0x82d74). ---- *)
(* The memory part every inner cut state holds: the pre-condition, the caller's journal with the class-3 frame
   (3, x_fpos c) owned and the layout of the entry (x_ly c), the heap blocks of the entry, the saved registers,
   name_len at s1 + 56 (0x82dc4), the frame at s1 + 80 (0x82e3c), the frame's flag pointer at F + 504, the four
   scope shadow bytes as 0x82e8c .. 0x82ef8 left them (0xf8), and the heap bytes of the entry unchanged. *)
Definition rbe_mem (c : rbx) (Sc : astate) (mem : word -> option byte) (md : Model) : Prop :=
  rbn_pre B G c /\
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] (x_ly c) Sc (x_W c) mem md 0 /\
  ablocks B (x_ly c) Sc = ablocks B (x_ly c) (x_S c) /\
  rbn_saved c mem /\
  val_mem SEGS (x_mem_at c mem) (x_s1 c + 56) 8 (x_name_len c) /\
  val_mem SEGS (x_mem_at c mem) (x_s1 c + 80) 8 (x_F c) /\
  rdword (aview SEGS (w_H (x_W c)) mem) (x_F c + 504) = Some (flag_addr (x_ly c) 3 (x_fpos c)) /\
  rbn_scope c mem 0xf8 0xf8 0xf8 0xf8 /\
  rbn_bufkept B c mem.
(* The registers every inner cut state holds: sp = s1, gp, tp, s0 = sp0, s1, s2 = FS, s3 = s7 = F, s6 = the shadow
   base, a5 = display_len (0x82e14), s5 = token, s8 = name, s10 = token_len. *)
Definition rbe_regs (c : rbx) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (x_s1 c) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 8 = w64 (x_sp0 c) /\ getr regs 9 = w64 (x_s1 c) /\ getr regs 18 = w64 (x_FS c) /\
  getr regs 19 = w64 (x_F c) /\ getr regs 23 = w64 (x_F c) /\ getr regs 22 = w64 SHADOW_OFF /\
  getr regs 15 = w64 (x_display_len c) /\ getr regs 21 = w64 (x_token c) /\
  getr regs 24 = w64 (x_name c) /\ getr regs 26 = w64 (x_token_len c).
(* X1, 0x82f10 (+0x19c): frame taken, header and shadow written, s4 = -1; the argument checks are next. *)
Definition rbe_X1 (c : rbx) (Sc : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  rbe_mem c Sc mem md /\ rbe_regs c regs /\
  getr regs 12 = w64 (x_i c) /\ getr regs 13 = w64 (x_o c) /\ getr regs 20 = w64 (-1) /\
  getr regs 25 = w64 (x_said c) /\ getr regs 27 = w64 (x_f c).
(* X2a, 0x82f68 (+0x1f4): the arguments accepted (0x82f10 .. 0x82f64); a4 = display (0x82f28). *)
Definition rbe_X2a (c : rbx) (Sc : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  rbe_X1 c Sc regs mem md /\
  reac_box_name_c.bn_args_ok (x_name c) (x_name_len c) (x_token c) (x_token_len c) (x_display c)
    (x_display_len c) (x_i c) (x_o c) = true /\
  getr regs 14 = w64 (x_display c).
(* X2, 0x82fc8 (+0x254): in / out stored (0x82f68), s9 = the stem st (rbn_stem, stated for the entry memory). *)
Definition rbe_X2 (c : rbx) (Sc : astate) (st : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  : Prop :=
  rbe_mem c Sc mem md /\ rbe_regs c regs /\
  reac_box_name_c.bn_args_ok (x_name c) (x_name_len c) (x_token c) (x_token_len c) (x_display c)
    (x_display_len c) (x_i c) (x_o c) = true /\
  getr regs 14 = w64 (x_display c) /\ getr regs 25 = w64 st /\
  val_mem SEGS (x_mem_at c mem) (x_s1 c + 40) 8 (x_i c mod 2 ^ 64) /\
  val_mem SEGS (x_mem_at c mem) (x_s1 c + 48) 8 (x_o c mod 2 ^ 64) /\
  rbn_stem B G c (x_mem c) st.
(* ---- YOUR LEMMAS BELOW (helpers prefixed with your lane's prefix) ---- *)
(* ==== Piece E1: entry (0x82d74) -> X1 (0x82f10). ==== *)
Definition rbe1_args_region : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 34 0)); YP09.mkChunk 8 (CVal 8 (SOff 35 0))].
Definition rbe1_ss0 : sstate := mkSS AF_reac_box_name sr_atoms
  [stack_region 320; rbe1_args_region; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33] None
  (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (33%nat, mkAF 65536 6266880 2)] [] []).
Definition rbe1_extra (uar display display_len : Z) : list word :=
  map (Z_to_bv 64) [SHADOW_OFF; uar; display; display_len].
Ltac rbe1_nss HS := lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss3 ?d =>
  let v := eval vm_compute in ss3 in change (st_ok_pi a b c v d) in HS end.
(* The symbolic state at the first slot. *)
Lemma rbe1_entry : forall c, rbn_pre B G c ->
  st_ok_pi SEGS VAL (Eimg (Ereg (x_regs c) (rbe1_extra (as_uar_cell B) (x_display c) (x_display_len c)))) rbe1_ss0
    (restrict (w_H (x_W c)) (mkst (x_regs c) (Z_to_bv 64 (BASE + AF_reac_box_name)) (x_mem c) (seg_rom SEGS))).
Proof.
intros c Hpre.
destruct c as [ly S W regs mem md ch f said i o name name_len token token_len display display_len sd fpos].
cbn [x_ly x_S x_W x_regs x_mem x_md x_ch x_f x_said x_i x_o x_name x_name_len x_token x_token_len x_display
  x_display_len x_sd x_fpos x_sp0 x_mem_at] in *.
pose proof Hpre as (HAFN & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  Vdisp & Rdisp & Vdl & Rdl & _).
cbn [x_ly x_S x_W x_regs x_mem x_md x_ch x_f x_said x_i x_o x_name x_name_len x_token x_token_len x_display
  x_display_len x_sd x_fpos x_sp0 x_mem_at] in Vdisp, Rdisp, Vdl, Rdl, HAFN.
pose proof HAFN as (HAR & _ & _ & _ & _ & Hstk & Hpres & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (Hes : ESTACK = 4096) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 31 ltac:(lia)) as Hob31.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (rbe1_extra (as_uar_cell B) display display_len))).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (rbe1_extra (as_uar_cell B) display display_len)) k)
  by (intros k Hk; subst E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 display) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 display_len) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Eo0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Eo31 : ew E (A_OBJ 31) = Z_to_bv 64 (VAL (A_OBJ 31))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Uu : bv_unsigned (ew E 33) = as_uar_cell B) by (rewrite E33; apply unsigned_lit_small; lia).
assert (Uo0 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite Eo0; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 0)); lia).
assert (Uo1 : bv_unsigned (ew E (A_OBJ 1)) = VAL (A_OBJ 1)) by (rewrite Eo1; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 1)); lia).
assert (Uo31 : bv_unsigned (ew E (A_OBJ 31)) = VAL (A_OBJ 31)) by (rewrite Eo31; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 31)); lia).
unfold rbe1_ss0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok, stack_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros k Hk. apply (apresent_writable SEGS). apply Hpres. lia.
  + unfold region_ok, rbe1_args_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. split; [lia|]. split; [lia|]. split; [intros k Hk; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ (spZ regs) 0 8 _ display);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Vdisp.
    * apply (chunk_ok_val SEGS E _ (spZ regs) 8 8 _ display_len);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vdl].
  + unfold region_ok, got_regionP. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Uo1. split; [lia|]. split; [lia|]. split; [intros k Hk; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 31) 0) (VAL (A_OBJ 31)));
    [cbn [sv_denot]; rewrite Eo31, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + unfold region_ok, bcell_regionP. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Uo31. split; [lia|]. split; [lia|]. split; [intros k Hk; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 31)) 0 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + unfold region_ok, uar_got_regionP. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Uo0. split; [lia|]. split; [lia|]. split; [intros k Hk; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff 33 0) (as_uar_cell B));
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
  + unfold region_ok, uar_cell_regionP. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Uu. split; [lia|]. split; [lia|]. split; [intros k Hk; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold stack_region, rbe1_args_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite Usp, Uo0, Uo1, Uo31, Uu.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  clear - Hsep Hob0 Hob1 Hob31 Huar C1 Hceil Hslo Hstk0 Hshi H47 Hes.
  repeat split; lia.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I]. split; [|split; [|exact I]].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp. change (2 ^ 4) with 16.
    split; [lia|]. split; [exact Hal16 | lia].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Uu. change (2 ^ 2) with 4.
    split; [lia|]. split; [exact Huar4 | lia].
Qed.
(* sp after 0x82db4 andi sp,sp,-32 (the 32-byte realignment). *)
Lemma rbe1_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma rbe1_denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite rbe1_land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
Lemma rbe1_sp1_facts : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
(* The windows of a region list: every write of a run lies in one of them. *)
Local Ltac rbe1_win :=
  let bb0 := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros bb0 wlo whi x Hin Hr;
  vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [ injection Hin as <- <- <-; cbn [base_val] in Hr;
      repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H in Hr end;
      first [lia | (left; lia) | (right; left; lia) | (right; right; lia)]
    | ]);
  try destruct Hin.
Local Ltac rbe1_awr :=
  lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end.
(* A saved register out of the sp0 region (chunks at sp0 - 8 .. sp0 - 104). *)
Local Ltac rbe1_save :=
  lazymatch goal with
  | HR : region_ok _ ?Ex ?m (YP09.mkRegion (Some 2%nat) (-104) 0 _ _ ?cs),
    U : bv_unsigned (ew ?Ex 2%nat) = ?sp,
    AG : forall n0, (n0 < 60)%nat -> ew ?Ex n0 = ew ?E0 n0,
    EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew ?E0 k = getr ?rg r
    |- val_mem _ ?m (?sp - ?k) 8 (bv_unsigned (getr ?rg ?r)) =>
    replace (sp - k) with (sp + - k) by lia;
    eapply (field_of_region Ex m 2%nat sp cs _ _ _ _ (- k) 8%N _ _ HR U);
    [ repeat first [left; reflexivity | right]
    | cbn [sv_denot]; rewrite Z.add_0_r;
      lazymatch goal with |- Z_to_bv 64 (bv_unsigned (ew _ ?n)) = _ => rewrite (AG n ltac:(lia)), (EE n r eq_refl) end;
      reflexivity
    | exact (bv_unsigned_in_range 64 (getr rg r))
    | lia ]
  end.
(* A byte of the frame's shadow out of the shadow region (a 1-byte chunk holding 0xf8). *)
Local Ltac rbe1_shb HR0 U529 :=
  apply (aview_of_val_mem1 SEGS); [| lia];
  lazymatch goal with |- val_mem _ _ (?b + ?j) _ _ =>
    let V := fresh "V" in
    pose proof (field_of_region_any _ _ 529%nat b _ _ _ _ _ j 1%N _ HR0 U529
      ltac:(repeat first [left; reflexivity | right]) ltac:(lia)) as V;
    cbn [sv_denot] in V; exact V end.
Lemma rbe_e1 : forall c, rbn_pre B G c ->
  SRr SEGS (x_W c) (cfg_at SEGS (BASE + AF_reac_box_name) (x_regs c) (x_mem c) (x_md c))
    (fun W' c' => W' = x_W c /\ exists fpos Sc regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x19c)) mem' (seg_rom SEGS)) md' /\
       rbe_X1 (x_setpos c fpos) Sc regs' mem' md').
Proof.
intros c Hpre.
pose proof (rbe1_entry c Hpre) as HS.
destruct c as [ly S W regs mem md ch f said i o name name_len token token_len display display_len sd fpos0].
cbn [x_ly x_S x_W x_regs x_mem x_md x_ch x_f x_said x_i x_o x_name x_name_len x_token x_token_len x_display
  x_display_len x_sd x_fpos x_sp0 x_mem_at x_FP] in *.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_identb)) as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : 336 + 2 * ESTACK = 8528) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof Hpre as (HAFN & HROD & H10 & Hf & H11 & Hsaid & H12 & Hi & H13 & Ho & H14 & Hname & H15 & Hnl &
  H16 & Htok & H17 & Htl & HP16 & Vdisp & Rdisp & Vdl & Rdl & HIMG & HARGS & Hfr7 & Hnev & Hbb).
unfold x_sp0, x_mem_at, x_FP in HAFN, HROD, H10, Hf, H11, Hsaid, H12, Hi, H13, Ho, H14, Hname,
  H15, Hnl, H16, Htok, H17, Htl, HP16, Vdisp, Rdisp, Vdl, Rdl, HIMG, HARGS, Hfr7, Hnev, Hbb.
cbn [x_ly x_S x_W x_regs x_mem x_md x_ch x_f x_said x_i x_o x_name x_name_len x_token x_token_len x_display
  x_display_len x_sd x_fpos] in HAFN, HROD, H10, Hf, H11, Hsaid, H12, Hi, H13, Ho, H14, Hname,
  H15, Hnl, H16, Htok, H17, Htl, HP16, Vdisp, Rdisp, Vdl, Rdl, HIMG, HARGS, Hfr7, Hnev, Hbb.
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (ajournal_init SEGS B (336 + 2 * ESTACK) (rbn_fp name name_len token token_len display display_len)
  ly S W regs mem md ch HAFN) as HJc.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 31 ltac:(lia)) as Hob31.
pose proof (palf_uar_img B TLF) as Huar.
remember (Eimg (Ereg regs (rbe1_extra (as_uar_cell B) display display_len))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
  by (intros k0 r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (E35 : ew E 35 = Z_to_bv 64 display_len) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 3)).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO31 : ew E (A_OBJ 31) = Z_to_bv 64 (VAL (A_OBJ 31))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Uu : bv_unsigned (ew E 33) = as_uar_cell B) by (rewrite E33; apply unsigned_lit_small; lia).
assert (Uo0 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite EO0; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 0)); lia).
assert (Uo1 : bv_unsigned (ew E (A_OBJ 1)) = VAL (A_OBJ 1)) by (rewrite EO1; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 1)); lia).
assert (Uo31 : bv_unsigned (ew E (A_OBJ 31)) = VAL (A_OBJ 31)) by (rewrite EO31; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 31)); lia).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_reac_box_name)) with (Z_to_bv 64 (BASE + AF_reac_box_name)).
(* run 1: the prologue, 0x82d74 .. 0x82db8 (after the andi). *)
paj_run_to_sh RUNTOP HS HJc 0x2644.
{ rbe1_awr. repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
    [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo]; clear - HSTK; lia | cbn [YP09.r_whi]; lia |] ]. }
assert (KB1 : forall b m k, In (b, m) (ablocks B ly S) -> 0 <= k < req_size m ->
  aview SEGS (w_H W) (ms_mem ms) (b + k) = aview SEGS (w_H W) mem (b + k)).
{ intros b m k Hin Hk. destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & Hb4 & Hbc & _).
  apply (kept_of_frame E (ss_mem rbe1_ss0) (w_H W) mem (ms_mem ms) (fun a => alloc_ceiling <= a) HFr).
  - rbe1_win.
  - lia.
  - lia. }
clear HF HG HFr.
(* 0x82db4 andi sp,sp,-32: s1 = 32 * ((sp0 - 320) / 32), a fresh atom 60, 32-aligned. *)
set (s1v := 32 * ((spZ regs + -320) / 32)).
destruct (rbe1_sp1_facts (spZ regs + -320) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp0al; reflexivity))
  as (Hs1r & Hs1al & Hs1al16).
fold s1v in Hs1r, Hs1al, Hs1al16.
assert (Hs1 : spZ regs - 336 <= s1v <= spZ regs - 320) by lia. clear Hs1r.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_pi_restrict_reg (w_H W) Ev ssx msx (2%bv : bv 5) HS) as R2;
  change (sr_get (ss_regs ssx) (2%bv : bv 5)) with (SAlu ALU_AND (SOff 2 (-320)) (SLit (-32))) in R2;
  rewrite (rbe1_denot_and_m32 Ev 2 (spZ regs) (-320) ltac:(rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia) ltac:(lia) ltac:(lia)) in R2;
  fold s1v in R2;
  pose proof (st_ok_pi_havoc_hi 60 Ev ssx (restrict (w_H W) msx) [Z_to_bv 64 s1v] HS ltac:(vm_compute; reflexivity)) as HS3
end.
clear HS. rename HS3 into HS.
set (E1 := havoc E 60 [Z_to_bv 64 s1v]) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc; [exact HEI | cbv; lia]).
assert (AG1 : forall n0, (n0 < 60)%nat -> ew E1 n0 = ew E n0) by (intros n0 Hn0; apply ew_havoc_old; exact Hn0).
assert (AG1' : forall n0, (61 <= n0)%nat -> ew E1 n0 = ew E n0) by (intros n0 Hn0; apply ew_havoc_above; cbn; lia).
assert (E60 : ew E1 60 = Z_to_bv 64 s1v) by exact (ew_havoc_new E 60 [Z_to_bv 64 s1v] 0 (Z_to_bv 64 0) ltac:(cbn; lia)).
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp E1 ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, R2; rewrite unsigned_lit_small by lia; reflexivity)) as HS3
end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact E1 ssx msx 60%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E60, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3
end.
clear HS. rename HS3 into HS. rbe1_nss HS.
assert (B60 : bv_unsigned (ew E1 60) = s1v) by (rewrite E60; apply unsigned_lit_small; lia).
assert (B2 : bv_unsigned (ew E1 2) = spZ regs) by (rewrite (AG1 2%nat ltac:(lia)); exact Usp).
assert (Bu : bv_unsigned (ew E1 33) = as_uar_cell B) by (rewrite (AG1 33%nat ltac:(lia)); exact Uu).
assert (Bo0 : bv_unsigned (ew E1 241) = VAL (A_OBJ 0)) by (rewrite (AG1' 241%nat ltac:(lia)); exact Uo0).
assert (Bo1 : bv_unsigned (ew E1 242) = VAL (A_OBJ 1)) by (rewrite (AG1' 242%nat ltac:(lia)); exact Uo1).
assert (Bo31 : bv_unsigned (ew E1 272) = VAL (A_OBJ 31)) by (rewrite (AG1' 272%nat ltac:(lia)); exact Uo31).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  let rs := eval cbn [ss_mem] in (ss_mem ssx) in
  lazymatch rs with ?r0 :: ?rest =>
  pose proof (st_ok_pi_submem E1 ssx (restrict (w_H W) msx) (trim_lo r0 (-104) :: rest) HS
    ltac:(cbn [ss_mem]; apply submem_keep; [apply subregion_trim_lo | apply submem_refl]) ltac:(vm_compute; reflexivity)) as HS3 end
end.
clear HS. rename HS3 into HS. rbe1_nss HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
  assert (HD : all_disjoint E1 (YP09.mkRegion (Some 60%nat) 56 88 56 88 []) (ss_mem ssx)) end.
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi extent_of_region base_val fst snd].
  rewrite ?B60, ?B2, ?Bu, ?Bo0, ?Bo1, ?Bo31.
  clear - Hs1 Hob0 Hob1 Hob31 Huar C1 Hceil Hslo Hstk0 Hshi H47 Hes. repeat split; lia. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  pose proof (st_ok_pi_add_region E1 ssx (restrict (w_H W) msx) (YP09.mkRegion (Some 60%nat) 56 88 56 88 []) HS eq_refl
    ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst base_val]; rewrite B60;
          split; [lia|]; split; [lia|]; split; [|constructor];
          intros o0 Ho0; apply (apresent_writable SEGS); apply Hpres1; lia) HD) as HS3
end.
clear HS HD. rename HS3 into HS. rbe1_nss HS.
(* run 2: 0x82db8 .. the call of __asan_stack_malloc_3 at 0x82dfc. *)
set (ms1 := ms) in *. clearbody ms1. clear ms.
paj_run_shc RUNP RUNC HS HJc.
{ rbe1_awr. repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
    [reflexivity | rewrite B2; lia | cbn [YP09.r_wlo]; clear - HSTK; lia | cbn [YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (s1v - spZ regs));
    [reflexivity | rewrite B60; lia | cbn [YP09.r_wlo]; clear - Hs1 HSTK; lia | cbn [YP09.r_whi]; clear - Hs1; lia |] ]. }
assert (KB2 : forall b m k, In (b, m) (ablocks B ly S) -> 0 <= k < req_size m ->
  aview SEGS (w_H W) (ms_mem ms) (b + k) = aview SEGS (w_H W) mem (b + k)).
{ intros b m k Hin Hk. destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & Hb4 & Hbc & _).
  rewrite <- (KB1 b m k Hin Hk).
  lazymatch type of HFr with frame_of ?Ex ?rsx _ _ =>
    apply (kept_of_frame Ex rsx (w_H W) (ms_mem ms1) (ms_mem ms) (fun a => alloc_ceiling <= a) HFr) end.
  - rbe1_win.
  - lia.
  - lia. }
clear HF HG HFr KB1.
(* the call of __asan_stack_malloc_3 at 0x82dfc (class 3, 512 bytes; returns to 0x82e00). *)
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
rewrite E60 in Rsp. rewrite (AG1 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl), Hgp in Rgp.
rewrite (AG1 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl), Htp in Rtp.
pmkst HS. rewrite (palf_sm3 B TLF).
pose proof (count_cid_le_length 3 (frames S)) as Hcnt.
assert (HFF : 8 <= fs_frames 3) by (vm_compute; discriminate).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msX) _) _) _ =>
  eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs (pal_env B TL) ML SMP 3 ASM3 ltac:(lia) W (ms_regs msX) (ms_mem msX)
    (336 + 2 * ESTACK) (spZ regs) (rbn_fp name name_len token token_len display display_len) ly S W mem md [] ly S _ 0
    (s1v - spZ regs) _ HJc) end.
  - unfold spZ at 1. rewrite Rsp, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hs1al16, Hsp0al. reflexivity.
  - lia.
  - rewrite Hes. lia.
  - exact Rgp.
  - exact Rtp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - lia. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJ1 & (fS2 & ES2)).
assert (KB3 : forall b m k, In (b, m) (ablocks B ly S) -> 0 <= k < req_size m ->
  aview SEGS (w_H W) mem2 (b + k) = aview SEGS (w_H W) mem (b + k)).
{ intros b m k Hin Hk. rewrite <- (KB2 b m k Hin Hk). exact (proj1 (proj2 HK) b m k Hin Hk (fun H => H)). }
clear KB2.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
let K := run_K_hi HS in jafter_call_keep_hi HS K regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2.
lazymatch type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite B60; intros a Ha.
    + apply (mbyte_of_aview SEGS); apply (proj1 HK); lia.
    + intros _; apply (apresent_writable SEGS); apply HJpres2; lia.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite B2; intros a Ha.
    + apply (mbyte_of_aview SEGS). apply (proj1 HK); lia.
    + intros _. apply (apresent_writable SEGS). apply HJpres2. lia.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite B2; intros a Ha.
    + apply (mbyte_of_aview SEGS). apply (proj1 HK); lia.
    + lia. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
(* The class-3 frame the call returned, and its shadow. *)
assert (Hfin2 : In (3, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (proj1 HJ2) as HAR2.
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 fpos HAR2 Hfin2) as (HFal & [HFa0 HFapp] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 fpos HAR2 Hfin2) as (HF4096 & HFceil & HFhigh).
destruct (frame_al64 SEGS B ly S2 W mem2 md2 3 fpos HAR2 Hfin2) as (HF64 & _ & _).
destruct (FFL ly S2 W mem2 md2 3 fpos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng & HFLnum).
change (fs_frame_bytes 3) with 512 in *.
set (F := frame_addr ly 3 fpos) in *. set (FL := flag_addr ly 3 fpos) in *.
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HF8 : F / 8 = 8 * (F / 64)) by (rewrite HFq at 1; replace (64 * (F / 64)) with (8 * (F / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 + 64 <= 17592186044416) by (rewrite HF8; lia).
set (E2v := havoc E1 512 (map (getr regs2) CLOB)) in HS.
assert (HEI2 : img_env VAL A_LIM E2v) by (apply img_env_havoc_hi; [exact HEI1 | cbv; lia]).
assert (AG2 : forall n0, (n0 < 512)%nat -> ew E2v n0 = ew E1 n0) by (intros n0 Hn0; apply ew_havoc_old; exact Hn0).
assert (E516 : ew E2v 516 = Z_to_bv 64 F).
{ transitivity (getr regs2 (10%bv : bv 5));
  [exact (ew_havoc_new E1 512 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0) ltac:(cbv; lia)) | rewrite Ha0; reflexivity]. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_havoc_hi 528 E2v ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3
end.
clear HS. rename HS3 into HS.
set (E3v := havoc E2v 528 [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)]) in HS.
assert (HEI3 : img_env VAL A_LIM E3v) by (apply img_env_havoc_hi; [exact HEI2 | cbv; lia]).
assert (AG3 : forall n0, (n0 < 528)%nat -> ew E3v n0 = ew E2v n0) by (intros n0 Hn0; apply ew_havoc_old; exact Hn0).
assert (E528 : ew E3v 528 = Z_to_bv 64 FL)
  by exact (ew_havoc_new E2v 528 [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)).
assert (E529 : ew E3v 529 = Z_to_bv 64 (SHADOW_OFF + F / 8))
  by exact (ew_havoc_new E2v 528 [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)).
assert (E32' : ew E3v 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (AG3 32%nat ltac:(lia)), (AG2 32%nat ltac:(lia)), (AG1 32%nat ltac:(lia)); exact E32).
assert (E516' : ew E3v 516 = Z_to_bv 64 F) by (rewrite (AG3 516%nat ltac:(lia)); exact E516).
assert (RF3 : bv_unsigned (ew E3v 516) = F) by (rewrite E516'; apply unsigned_lit_small; lia).
lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_add_fact E3v ssv msv 516 (HPTR 6) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite RF3; change (2 ^ 6) with 64; lia)) as HS3 end.
clear HS. rename HS3 into HS. rbe1_nss HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_add_fact E3v ssv msv 528 (HPTR 0) HS
    ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E528;
          rewrite (unsigned_lit_small FL) by (clear - HFLnum C1; lia);
          rewrite Z.pow_0_r, Z.mod_1_r; clear - HFLnum C1; lia)) as HS3 end.
clear HS. rename HS3 into HS. rbe1_nss HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_add_fact E3v ssv msv 529 (mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 17592186044416) 3) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SHADOW_OFF; lia); change (2 ^ 3) with 8; unfold SHADOW_OFF;
          split; [lia|]; split; [rewrite HF8; replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by lia; apply Z_mod_mult | lia])) as HS3 end.
clear HS. rename HS3 into HS. rbe1_nss HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssv ?msv =>
  pose proof (st_ok_pi_add_alias E3v ssv msv _ _ HS (shadow_decl_ok E3v 516 32 529 F SHADOW_OFF
    ltac:(rewrite <- RF3; symmetry; apply Z_to_bv_bv_unsigned) ltac:(lia) E32' E529)) as HS3 end.
clear HS. rename HS3 into HS. rbe1_nss HS.
assert (B516 : base_val E3v (Some 516%nat) = F) by (cbn [base_val]; exact RF3).
assert (B529 : base_val E3v (Some 529%nat) = SHADOW_OFF + F / 8)
  by (cbn [base_val]; rewrite E529; apply unsigned_lit_small; unfold SHADOW_OFF; clear - HF8lo HF8hi; lia).
assert (B2' : base_val E3v (Some 2%nat) = spZ regs)
  by (cbn [base_val]; rewrite (AG3 2%nat ltac:(lia)), (AG2 2%nat ltac:(lia)); exact B2).
assert (B60' : base_val E3v (Some 60%nat) = s1v)
  by (cbn [base_val]; rewrite (AG3 60%nat ltac:(lia)), (AG2 60%nat ltac:(lia)); exact B60).
lazymatch type of HS with st_ok_pi _ _ _ ?ssv _ =>
  assert (HDF : all_disjoint E3v (fframe_region 516 528 3 []) (ss_mem ssv)) end.
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint, extent_of_region, fframe_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi fst snd].
  rewrite B516, B2', B60'. change (fs_frame_bytes 3) with 512.
  clear - HF4096 HFceil Hs1 Hslo Hceil Hstk0 HSTK C1 Hshi H47.
  repeat split; lia. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssv (restrict _ ?msv) =>
  pose proof (st_ok_pi_add_region E3v ssv (restrict (w_H W) msv) (fframe_region 516 528 3 []) HS eq_refl
    ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst app];
          rewrite B516; change (fs_frame_bytes 3) with 512;
          split; [clear - HF4096; lia|]; split; [clear - HFceil C1; lia|]; split;
          [ intros o0 Ho0; apply (apresent_writable SEGS); exact (proj1 (HFpres (F + o0) ltac:(clear - Ho0; lia)))
          | apply Forall_cons; [|apply Forall_nil];
            apply (chunk_ok_val SEGS E3v _ F 504 8 _ FL);
            [cbn [sv_denot]; rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
            | clear - HFLnum C1; zside | zside
            | replace (F + 504) with (F + 512 - 8) by (clear; lia); exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ]) HDF) as HS3
end.
clear HS HDF. rename HS3 into HS. rbe1_nss HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ssv _ =>
  assert (HDS : all_disjoint E3v (fshadow_region 529 3 0 64 []) (ss_mem ssv)) end.
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint, extent_of_region, fframe_region, fshadow_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi fst snd].
  rewrite B529, B516, B2', B60'. change (fs_frame_bytes 3 / 8) with 64. change (fs_frame_bytes 3) with 512.
  clear - HF4096 HFceil HF8lo HF8hi HFapp HFq HF8 Hs1 Hslo Hceil Hstk0 HSTK C1 Hshi H47.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as [HFa | [HFa HFa2]].
  all: unfold SHADOW_OFF; repeat split; first [exact I | left; lia | right; lia]. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssv (restrict _ ?msv) =>
  pose proof (st_ok_pi_add_region E3v ssv (restrict (w_H W) msv) (fshadow_region 529 3 0 64 []) HS eq_refl
    ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict mkst];
          rewrite B529; change (fs_frame_bytes 3 / 8) with 64;
          split; [clear - HF8lo; unfold SHADOW_OFF; lia|]; split; [clear - HF8hi; unfold SHADOW_OFF; lia|]; split;
          [ intros o0 Ho0; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres;
            exact (proj1 (HFSpres o0 ltac:(change (512 / 8) with 64; clear - Ho0; lia)))
          | apply Forall_nil ]) HDS) as HS3
end.
clear HS HDS. rename HS3 into HS. rbe1_nss HS.
(* run 3: 0x82e00 .. 0x82f10 (the frame header, the frame's shadow, s4 = -1). *)
assert (SHF : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
assert (HIF1 : forall a, F <= a < F + 512 -> in_frames ly [(3, fpos)] a).
{ intros a Ha. exists 3, fpos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  change (fs_frame_bytes 3) with 512. fold F. lia. }
assert (HIF2 : forall a, SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 64 -> in_frames ly [(3, fpos)] a).
{ intros a Ha. exists 3, fpos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
  change (fs_frame_bytes 3 / 8) with 64. fold F. rewrite SHF. lia. }
set (ms2 := mkst (ms_regs ms) (Z_to_bv 64 (BASE + 9868)) mem2 (seg_rom SEGS)) in *.
paj_run_to_sh RUNTOP HS HJ2 0x279c.
{ rbe1_awr. repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat 0);
    [reflexivity | cbn [base_val] in B2'; rewrite B2'; lia | cbn [YP09.r_wlo]; clear - HSTK; lia | cbn [YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (s1v - spZ regs));
    [reflexivity | cbn [base_val] in B60'; rewrite B60'; lia | cbn [YP09.r_wlo]; clear - Hs1 HSTK; lia | cbn [YP09.r_whi]; clear - Hs1; lia |]
  | eapply awr_ok_cons_gen;
    [reflexivity | first [exact RF3 | exact B529]
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right;
      first [apply HIF1; clear - Ha; lia | apply HIF2; clear - Ha; lia]
    | ] ]. }
(* ---- X1: read the cut state out of the symbolic state. ---- *)
cbn [ms_mem mkst] in HF, HFr, HG.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => rename msx into msF end.
assert (AGr : forall n0, (n0 < 60)%nat -> ew E3v n0 = ew E n0)
  by (intros n0 Hn0; rewrite (AG3 n0 ltac:(lia)), (AG2 n0 ltac:(lia)), (AG1 n0 Hn0); reflexivity).
assert (U529 : bv_unsigned (ew E3v 529) = SHADOW_OFF + F / 8) by exact B529.
assert (U60 : bv_unsigned (ew E3v 60) = s1v) by exact B60'.
assert (U2 : bv_unsigned (ew E3v 2) = spZ regs) by exact B2'.
assert (KB4 : forall b m k, In (b, m) (ablocks B ly S) -> 0 <= k < req_size m ->
  aview SEGS (w_H W) (ms_mem msF) (b + k) = aview SEGS (w_H W) mem (b + k)).
{ intros b m k Hin Hk. destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & Hb4 & Hbc & Hbapp & _).
  assert (Hin2 : In (b, m) (ablocks B ly S2)) by (rewrite Eab; exact Hin).
  pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 b m 3 fpos HAR2 Hin2 Hfin2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 3) with 512 in Hd. fold F in Hd.
  rewrite <- (KB3 b m k Hin Hk).
  lazymatch type of HFr with frame_of ?Ex ?rsx _ _ =>
    apply (kept_of_frame Ex rsx (w_H W) mem2 (ms_mem msF)
      (fun a => alloc_ceiling <= a \/ (F <= a < F + 512) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 64)) HFr) end.
  - rbe1_win.
  - lia.
  - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. unfold SHADOW_OFF in *.
    clear - Hk Hbc Hd Hbapp HF8lo HF8hi C1. lia. }
clear KB3 HF HG.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (15%bv : bv 5) Q15.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
assert (E60' : ew E3v 60 = Z_to_bv 64 s1v) by (rewrite (AG3 60%nat ltac:(lia)), (AG2 60%nat ltac:(lia)); exact E60).
rewrite E60' in Q2, Q9.
rewrite (AGr 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl), Hgp in Q3.
rewrite (AGr 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl), Htp in Q4.
rewrite (AGr 2%nat ltac:(lia)), (EE 2%nat 2%bv eq_refl) in Q8.
rewrite (AGr 12%nat ltac:(lia)), (EE 12%nat 12%bv eq_refl), H12 in Q12.
rewrite (AGr 13%nat ltac:(lia)), (EE 13%nat 13%bv eq_refl), H13 in Q13.
rewrite (AGr 35%nat ltac:(lia)), E35 in Q15.
rewrite E529 in Q18. rewrite E516' in Q19, Q23.
rewrite (AGr 16%nat ltac:(lia)), (EE 16%nat 16%bv eq_refl), H16 in Q21.
rewrite E32' in Q22.
rewrite (AGr 14%nat ltac:(lia)), (EE 14%nat 14%bv eq_refl), H14 in Q24.
rewrite (AGr 11%nat ltac:(lia)), (EE 11%nat 11%bv eq_refl), H11 in Q25.
rewrite (AGr 17%nat ltac:(lia)), (EE 17%nat 17%bv eq_refl), H17 in Q26.
rewrite (AGr 10%nat ltac:(lia)), (EE 10%nat 10%bv eq_refl), H10 in Q27.
pose proof (st_ok_pi_region_nth E3v _ (restrict (w_H W) msF) 0%nat _ HS eq_refl) as HR0. cbn [restrict ms_mem] in HR0.
pose proof (st_ok_pi_region_nth E3v _ (restrict (w_H W) msF) 1%nat _ HS eq_refl) as HR1. cbn [restrict ms_mem] in HR1.
pose proof (st_ok_pi_region_nth E3v _ (restrict (w_H W) msF) 2%nat _ HS eq_refl) as HR2. cbn [restrict ms_mem] in HR2.
pose proof (st_ok_pi_region_nth E3v _ (restrict (w_H W) msF) 3%nat _ HS eq_refl) as HR3. cbn [restrict ms_mem] in HR3.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
exists fpos, S2. do 3 eexists.
split.
{ replace (BASE + AF_reac_box_name + 0x19c) with (BASE + 10140) by (unfold AF_reac_box_name; lia). reflexivity. }
unfold rbe_X1, rbe_mem, rbe_regs.
unfold x_setpos, x_s1, x_F, x_FS, x_sp0, x_FP.
cbn [x_ly x_S x_W x_regs x_mem x_md x_ch x_f x_said x_i x_o x_name x_name_len x_token x_token_len x_display
  x_display_len x_sd x_fpos].
replace (spZ regs - 320) with (spZ regs + -320) by lia. fold s1v. fold F.
split.
{ split; [exact Hpre|].
split; [exact HJ2|].
split; [exact Eab|].
split.
{ unfold rbn_saved, rbn_saved_regs, x_mem_at, x_sp0.
  cbn [x_ly x_S x_W x_regs x_mem x_md x_ch x_f x_said x_i x_o x_name x_name_len x_token x_token_len x_display
    x_display_len x_sd x_fpos fst snd].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; rbe1_save. }
split.
{ unfold x_mem_at. cbn [x_W].
  eapply (field_of_region E3v _ 60%nat s1v _ _ _ _ _ 56 8%N _ name_len HR2 U60);
  [ repeat first [left; reflexivity | right]
  | cbn [sv_denot]; rewrite Z.add_0_r, (AGr 15%nat ltac:(lia)), (EE 15%nat 15%bv eq_refl), H15, unsigned_lit_small by lia; reflexivity
  | cbn [Z.of_N]; lia | lia ]. }
split.
{ unfold x_mem_at. cbn [x_W].
  eapply (field_of_region E3v _ 60%nat s1v _ _ _ _ _ 80 8%N _ F HR2 U60);
  [ repeat first [left; reflexivity | right]
  | cbn [sv_denot]; rewrite Z.add_0_r, E516', unsigned_lit_small by lia; reflexivity
  | cbn [Z.of_N]; lia | lia ]. }
split.
{ apply rdword_of_val_mem; [| clear - HFLnum C1; lia].
  eapply (field_of_region E3v _ 516%nat F _ _ _ _ _ 504 8%N _ FL HR1 RF3);
  [ repeat first [left; reflexivity | right]
  | cbn [sv_denot]; rewrite Z.add_0_r, E528, unsigned_lit_small by (clear - HFLnum C1; lia); reflexivity
  | cbn [Z.of_N]; clear - HFLnum C1; lia | lia ]. }
split.
{ unfold rbn_scope, x_FS, x_F. cbn [x_W x_ly x_fpos]. fold F. cbv zeta.
  split; [rbe1_shb HR0 U529|].
  split; [intros j Hj; assert (j = 8 \/ j = 9 \/ j = 10) as [-> | [-> | ->]] by lia; rbe1_shb HR0 U529|].
  split; [intros j Hj; assert (j = 16 \/ j = 17 \/ j = 18) as [-> | [-> | ->]] by lia; rbe1_shb HR0 U529|].
  intros j Hj; assert (j = 24 \/ j = 25 \/ j = 26 \/ j = 27 \/ j = 28 \/ j = 29) as [-> | [-> | [-> | [-> | [-> | ->]]]]] by lia;
  rbe1_shb HR0 U529. }
{ unfold rbn_bufkept, x_mem_at, x_FP. cbn [x_W x_ly x_S x_mem].
  intros a _ (q & N & Hq & Hqa).
  destruct (al_blocks _ _ LAWS ly S W mem md q N HAR Hq) as (_ & _ & _ & _ & _ & _ & HN).
  pose proof (req_size_pos N ltac:(lia)) as [_ HNr].
  replace a with (q + (a - q)) by lia. apply (KB4 q N); [exact Hq | lia]. } }
split.
{ unfold w64. repeat split; first [exact Q2 | exact Q3 | exact Q4 | exact Q9 | exact Q18 | exact Q19 | exact Q23 | exact Q22
    | exact Q15 | exact Q21 | exact Q24 | exact Q26
    | rewrite Q8; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity]. }
unfold w64. repeat split; first [exact Q12 | exact Q13 | exact Q25 | exact Q27 | rewrite Q20; apply bv_eq; reflexivity].
Qed.
(* ---- X1 (0x82f10, +0x19c) through the argument checks (0x82f10 .. 0x82f64): every branch to 0x834ac
   (+0x738) refuses (rbn_R with s4 = -1), the passing paths reach 0x82f68 (+0x1f4, rbe_X2a). ---- *)
(* The symbolic state at X1: display at s0 (atom 32, read at 0x82f28) and name_len at s1 + 56 (atom 33, read at
   0x82f18), both read-only. No store happens before 0x82f68; no region covers its store sd a2,40(s1), so the run
   stops there. *)
Definition rbe2a_rd : YP09.region := YP09.mkRegion (Some 8%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition rbe2a_rn : YP09.region := YP09.mkRegion (Some 9%nat) 56 64 0 0 [YP09.mkChunk 56 (CVal 8 (SOff 33 0))].
Definition rbe2a_ss : sstate := mkSS 0x279c sr_atoms [rbe2a_rd; rbe2a_rn] None (mkFacts [] [] []).
(* The registers the checks leave unchanged (they write a0, a1, a4 only): those rbn_R / rbe_X2a state. *)
Definition rbe2a_kR : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 23%bv].
Definition rbe2a_kX : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 13%bv; 15%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv;
   26%bv; 27%bv].
Local Ltac rbe2a_inl := repeat (first [left; reflexivity | right]).
(* x mod m (m a positive literal) as the remainder of a Euclidean division, for lia. *)
Local Ltac rbe2a_euc1 x m :=
  let q := fresh "q" in let r := fresh "r" in let Hq := fresh "Hq" in let Hr := fresh "Hr" in
  pose proof (Z.div_mod x m ltac:(lia)) as Hq; pose proof (Z.mod_pos_bound x m ltac:(lia)) as Hr;
  set (r := x mod m) in *; set (q := x / m) in *; clearbody r q.
Local Ltac rbe2a_euc :=
  repeat match goal with
  | |- context [?x mod ?m] => rbe2a_euc1 x m
  | H : context [?x mod ?m] |- _ => rbe2a_euc1 x m
  end.
(* beqz on an atom with value v. *)
Lemma rbe2a_Uz : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 64 < v < 2 ^ 64 ->
  (U E (SOff n 0) =? U E (SLit 0)) = (v =? 0).
Proof.
intros E n v Hn Hv.
rewrite U_SOff, Hn, Z.add_0_r, U_SLit, Z_to_bv_unsigned.
unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (2 ^ 64) with 18446744073709551616 in *.
rbe2a_euc.
repeat match goal with |- context [?a =? ?b] => destruct (Z.eqb_spec a b) end;
first [reflexivity | exfalso; lia].
Qed.
(* addiw a0,x,-41; li a1,-39; bltu a0,a1 (0x82f34 / 0x82f54): taken unless 2 <= x <= 40 (x a 32-bit int). *)
Lemma rbe2a_Ultu : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 31 <= v < 2 ^ 31 ->
  (U E (SAluw ALU_ADD (SOff n 0) (SLit (-41))) <? U E (SLit 18446744073709551577)) =
  negb ((2 <=? v) && (v <=? 40)).
Proof.
intros E n v Hn Hv.
rewrite (U_of_S E (SAluw ALU_ADD (SOff n 0) (SLit (-41)))), S_SAluw. cbn [zalu_raw].
rewrite U_SOff, Hn, Z.add_0_r, !U_SLit, Z_to_bv_unsigned.
unfold bv_swrap, zcanon, M64. change (bv_half_modulus 32) with (2 ^ 31). unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32).
change (2 ^ 31) with 2147483648 in *. change (2 ^ 32) with 4294967296 in *.
change (2 ^ 64) with 18446744073709551616 in *.
rbe2a_euc.
repeat match goal with
| |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
| |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
end; cbn [andb negb]; first [reflexivity | exfalso; lia].
Qed.
(* andi a0,x,1; bnez a0 (0x82f40 / 0x82f60): taken when x is odd. *)
Lemma rbe2a_Uand : forall E n v, ew E n = Z_to_bv 64 v -> - 2 ^ 31 <= v < 2 ^ 31 ->
  (U E (SAlu ALU_AND (SOff n 0) (SLit 1)) =? U E (SLit 0)) = Z.even v.
Proof.
intros E n v Hn Hv.
rewrite U_and_lit by lia. rewrite U_SOff, Hn, Z.add_0_r, U_SLit, Z_to_bv_unsigned.
replace (Z.land (zcanon (bv_wrap 64 v)) 1) with (zcanon (bv_wrap 64 v) mod 2)
  by (symmetry; exact (Z.land_ones (zcanon (bv_wrap 64 v)) 1 ltac:(lia))).
unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (2 ^ 31) with 2147483648 in *. change (2 ^ 64) with 18446744073709551616 in *.
destruct (Z.even v) eqn:Ev.
- apply Z.even_spec in Ev. destruct Ev as (k & Hk). rbe2a_euc.
  repeat match goal with |- context [?a =? ?b] => destruct (Z.eqb_spec a b) end;
  first [reflexivity | exfalso; lia].
- assert (Od : Z.odd v = true) by (rewrite <- Z.negb_even, Ev; reflexivity).
  apply Z.odd_spec in Od. destruct Od as (k & Hk). rbe2a_euc.
  repeat match goal with |- context [?a =? ?b] => destruct (Z.eqb_spec a b) end;
  first [reflexivity | exfalso; lia].
Qed.
(* rbe_mem holds for a memory with the same bytes and the caller's journal at it. *)
Lemma rbe2a_mem : forall c Sc mem md mem' md', rbe_mem c Sc mem md ->
  (forall a, aview SEGS (w_H (x_W c)) mem' a = aview SEGS (w_H (x_W c)) mem a) ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] (x_ly c) Sc (x_W c) mem' md' 0 ->
  rbe_mem c Sc mem' md'.
Proof.
intros c Sc mem md mem' md' (Hpre & _ & Hbl & Hsav & Hnl & HFv & Hflag & Hsc & Hbk) KEEP HJ.
assert (KV : forall a n v, val_mem SEGS (x_mem_at c mem) a n v -> val_mem SEGS (x_mem_at c mem') a n v).
{ intros a n v Hv. unfold x_mem_at in *.
  apply (val_mem_kept SEGS (w_H (x_W c)) (w_H (x_W c)) mem mem'); [|exact Hv].
  intros k _. apply KEEP. }
unfold rbe_mem. split; [exact Hpre|]. split; [exact HJ|]. split; [exact Hbl|].
split; [unfold rbn_saved in *; refine (Forall_impl _ _ Hsav); intros p Hp; apply KV; exact Hp|].
split; [apply KV; exact Hnl|]. split; [apply KV; exact HFv|].
split.
{ rewrite (rdword_ext (aview SEGS (w_H (x_W c)) mem) (aview SEGS (w_H (x_W c)) mem')); [exact Hflag|].
  intros k _. apply KEEP. }
split.
- unfold rbn_scope in *. cbv zeta in Hsc |- *. destruct Hsc as (S1 & S2 & S3 & S4).
  split; [rewrite KEEP; exact S1|].
  split; [intros j Hj; rewrite KEEP; exact (S2 j Hj)|].
  split; intros j Hj; rewrite KEEP; [exact (S3 j Hj) | exact (S4 j Hj)].
- unfold rbn_bufkept in *. intros a H1 H2. rewrite KEEP. exact (Hbk a H1 H2).
Qed.
(* A refusal at 0x834ac: the arguments are refused (bn_args_ok false, so bn_accept is false and s4 = -1 is the
   result); the memory as at X1. *)
Lemma rbe2a_R : forall c Sc regs mem md regs' mem' md', rbe_X1 c Sc regs mem md ->
  (forall a, aview SEGS (w_H (x_W c)) mem' a = aview SEGS (w_H (x_W c)) mem a) ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] (x_ly c) Sc (x_W c) mem' md' 0 ->
  (forall r, In r rbe2a_kR -> getr regs' r = getr regs r) ->
  reac_box_name_c.bn_args_ok (x_name c) (x_name_len c) (x_token c) (x_token_len c) (x_display c)
    (x_display_len c) (x_i c) (x_o c) = false ->
  rbn_R B G c (x_ly c) Sc mem' md' regs'.
Proof.
intros c Sc regs mem md regs' mem' md' (HM & HR & _ & _ & H20 & _ & _) KEEP HJ HK Hno.
destruct (rbe2a_mem c Sc mem md mem' md' HM KEEP HJ) as (Hpre & _ & Hbl & Hsav & _ & _ & Hflag & _ & Hbk).
destruct HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & _).
assert (Hacc : reac_box_name_c.bn_accept (x_f c) (x_sd c) (x_i c) (x_o c) (x_name c) (x_name_len c) (x_token c)
  (x_token_len c) (x_display c) (x_display_len c) = false)
  by (unfold reac_box_name_c.bn_accept; rewrite Hno; reflexivity).
unfold rbn_R, rbn_core. cbv zeta. rewrite Hacc.
rewrite !HK by (unfold rbe2a_kR; cbn [In]; rbe2a_inl).
split; [|split; [exact H20 | exact Hbk]].
split; [exact Hpre|]. split; [exact HJ|]. split; [rewrite Hbl; apply Permutation_refl|].
repeat match goal with |- _ /\ _ => split end; assumption.
Qed.
(* A pass to 0x82f68: the arguments accepted; a4 = display. *)
Lemma rbe2a_X2a : forall c Sc regs mem md regs' mem' md', rbe_X1 c Sc regs mem md ->
  (forall a, aview SEGS (w_H (x_W c)) mem' a = aview SEGS (w_H (x_W c)) mem a) ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] (x_ly c) Sc (x_W c) mem' md' 0 ->
  (forall r, In r rbe2a_kX -> getr regs' r = getr regs r) ->
  reac_box_name_c.bn_args_ok (x_name c) (x_name_len c) (x_token c) (x_token_len c) (x_display c)
    (x_display_len c) (x_i c) (x_o c) = true ->
  getr regs' 14 = w64 (x_display c) ->
  rbe_X2a c Sc regs' mem' md'.
Proof.
intros c Sc regs mem md regs' mem' md' (HM & HR & H12 & H13 & H20 & H25 & H27) KEEP HJ HK Hok H14.
pose proof (rbe2a_mem c Sc mem md mem' md' HM KEEP HJ) as HM'.
unfold rbe_X2a. split; [|split; [exact Hok | exact H14]].
destruct HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & R22 & R15 & R21 & R24 & R26).
unfold rbe_X1, rbe_regs.
rewrite !HK by (unfold rbe2a_kX; cbn [In]; rbe2a_inl).
split; [exact HM'|].
repeat match goal with |- _ /\ _ => split end; assumption.
Qed.
(* ---- The driver: run to 0x834ac; split each branch the engine cannot decide; a refusal reaches 0x834ac
   (offset 11576 = 0x2600 + 0x738), a pass stops at the store at 0x82f68 (10228 = 0x2600 + 0x1f4). ---- *)
Local Ltac rbe2a_awr :=
  lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx);
    repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; apply Z.le_refl|]); apply awr_ok_nil
  end.
Local Ltac rbe2a_kstep :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1),
    HK0 : forall a, aview ?sg _ _ a = aview _ _ ?mm a |- _ =>
    let K2 := fresh "K" in
    assert (K2 : forall a, aview sg H m1 a = aview sg H mm a)
      by (let a := fresh "a" in intros a;
          refine (eq_trans (aview_eq_of SEGS H m0 m1 a _) (HK0 a));
          rewrite (frame_of_read_only Ex rs (mrestrict H m0) (mrestrict H m1) ltac:(vm_compute; reflexivity) HFr);
          reflexivity);
    clear HK0; rename K2 into KEEP
  end;
  repeat match goal with
  | Hx : frame_of _ _ _ _ |- _ => clear Hx
  | Hx : mem_grows _ _ |- _ => clear Hx
  end.
Local Ltac rbe2a_cond :=
  lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
    rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U in Hc;
    repeat match goal with
    | UZ : (U ?E0 ?a =? U ?E0 ?b) = ?rhs |- _ =>
      lazymatch rhs with true => fail | false => fail | _ => idtac end;
      lazymatch type of Hc with context [U E0 a =? U E0 b] => rewrite UZ in Hc end
    | UZ : (U ?E0 ?a <? U ?E0 ?b) = ?rhs |- _ =>
      lazymatch rhs with true => fail | false => fail | _ => idtac end;
      lazymatch type of Hc with context [U E0 a <? U E0 b] => rewrite UZ in Hc end
    end;
    rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in Hc
  end.
Local Ltac rbe2a_bool :=
  unfold reac_box_name_c.bn_args_ok, bn_ok;
  repeat match goal with
  | H : ?l = true |- context [?l] => rewrite H
  | H : ?l = false |- context [?l] => rewrite H
  end;
  repeat (progress (cbn [negb andb orb];
    rewrite ?Bool.andb_false_r, ?Bool.andb_true_r, ?Bool.orb_false_r, ?Bool.orb_true_r));
  reflexivity.
Local Ltac rbe2a_go :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    paj_run_to_sh RUNTOP HS HJ 0x2d38; [ rbe2a_awr | rbe2a_kstep; rbe2a_leaf ]
  end
with rbe2a_leaf :=
  lazymatch goal with HS : st_ok_pi _ _ _ ?ss _ |- _ =>
    let pc := eval vm_compute in (ss_pc ss) in
    lazymatch pc with
    | 11576 => idtac
    | 10228 => idtac
    | _ => psrr_branch_pi RUNP BR HS; rbe2a_cond; rbe2a_go
    end
  end.
Lemma rbe_e2a : forall c Sc regs mem md, rbe_X1 c Sc regs mem md ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_name + 0x19c)) mem (seg_rom SEGS)) md)
    (fun W' c' => W' = x_W c /\ exists Sc' regs' mem' md',
       (c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x738)) mem' (seg_rom SEGS)) md' /\
        rbn_R B G c (x_ly c) Sc' mem' md' regs') \/
       (c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x1f4)) mem' (seg_rom SEGS)) md' /\
        rbe_X2a c Sc' regs' mem' md')).
Proof.
intros c Sc regs mem md HX.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HX as (HM & HR & H12 & H13 & _ & _ & _).
pose proof HM as (Hpre & HJ & _ & _ & Hnl & _ & _ & _ & _).
pose proof HR as (_ & _ & _ & R8 & R9 & _ & _ & _ & _ & R15 & R21 & R24 & R26).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & Ri & _ & Ro & _ & Rname & _ & Rnl & _ & Rtok & _ & Rtl & _ &
  Vd0 & Rdisp & _ & Rdl & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & K1 & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hs1 : x_sp0 c - 352 < x_s1 c <= x_sp0 c - 320).
{ unfold x_s1. pose proof (Z.div_mod (x_sp0 c - 320) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (x_sp0 c - 320) 32 ltac:(lia)) as D2. lia. }
(* display (at sp0, above the call's stack window) as at entry *)
assert (Vd : val_mem SEGS (mrestrict (w_H (x_W c)) mem) (x_sp0 c) 8 (x_display c)).
{ apply (val_mem_kept SEGS (w_H (x_W c)) (w_H (x_W c)) (x_mem c) mem); [|exact Vd0].
  intros k Hk. change (Z.of_nat 8) with 8 in Hk. apply K1; lia. }
remember (Eimg (Ereg regs [Z_to_bv 64 (x_display c); Z_to_bv 64 (x_name_len c)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 (x_display c); Z_to_bv 64 (x_name_len c)]) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER : regs_ok E sr_atoms regs) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (E32 : ew E 32 = Z_to_bv 64 (x_display c))
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (x_name_len c))
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E8 : ew E 8 = Z_to_bv 64 (x_sp0 c)) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 (x_s1 c)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E12 : ew E 12 = Z_to_bv 64 (x_i c)) by (rewrite (EE 12%nat 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 (x_o c)) by (rewrite (EE 13%nat 13%bv eq_refl); exact H13).
assert (E15 : ew E 15 = Z_to_bv 64 (x_display_len c)) by (rewrite (EE 15%nat 15%bv eq_refl); exact R15).
assert (E21 : ew E 21 = Z_to_bv 64 (x_token c)) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E24 : ew E 24 = Z_to_bv 64 (x_name c)) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (E26 : ew E 26 = Z_to_bv 64 (x_token_len c)) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
clear HE EE.
assert (U8 : bv_unsigned (ew E 8) = x_sp0 c) by (rewrite E8; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = x_s1 c) by (rewrite E9; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E rbe2a_ss
  (restrict (w_H (x_W c)) (mkst regs (Z_to_bv 64 (BASE + 0x279c)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rbe2a_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok, rbe2a_rd.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (x_sp0 c) 0 8 _ (x_display c));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Vd.
    + unfold region_ok, rbe2a_rn.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (x_s1 c) 56 8 _ (x_name_len c));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Hnl].
  - apply pairwise_disjoint_of_extents.
    unfold rbe2a_rd, rbe2a_rn, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
(* the branch conditions in terms of the arguments (after the last lia of this proof) *)
pose proof (rbe2a_Uz E 15 (x_display_len c) E15 ltac:(lia)) as UZ15.
pose proof (rbe2a_Uz E 26 (x_token_len c) E26 ltac:(lia)) as UZ26.
pose proof (rbe2a_Uz E 33 (x_name_len c) E33 ltac:(lia)) as UZ33.
pose proof (rbe2a_Uz E 24 (x_name c) E24 ltac:(lia)) as UZ24.
pose proof (rbe2a_Uz E 21 (x_token c) E21 ltac:(lia)) as UZ21.
pose proof (rbe2a_Uz E 32 (x_display c) E32 ltac:(lia)) as UZ32.
pose proof (rbe2a_Uz E 12 (x_i c) E12 ltac:(lia)) as UZ12.
pose proof (rbe2a_Uz E 13 (x_o c) E13 ltac:(lia)) as UZ13.
pose proof (rbe2a_Ultu E 12 (x_i c) E12 Ri) as UL12.
pose proof (rbe2a_Ultu E 13 (x_o c) E13 Ro) as UL13.
pose proof (rbe2a_Uand E 12 (x_i c) E12 Ri) as UA12.
pose proof (rbe2a_Uand E 13 (x_o c) E13 Ro) as UA13.
assert (EPC : BASE + AF_reac_box_name + 0x19c = BASE + 0x279c) by (rewrite <- Z.add_assoc; reflexivity).
assert (EPCR : BASE + AF_reac_box_name + 0x738 = BASE + 11576) by (rewrite <- Z.add_assoc; reflexivity).
assert (EPCP : BASE + AF_reac_box_name + 0x1f4 = BASE + 10228) by (rewrite <- Z.add_assoc; reflexivity).
rewrite EPC.
assert (KEEP : forall a, aview SEGS (w_H (x_W c)) mem a = aview SEGS (w_H (x_W c)) mem a) by (intros; reflexivity).
clear E8 E9 U8 U9 Vd Vd0 K1 Hstk ER EPC.
rbe2a_go.
(* the leaves: refusals at 0x834ac, passes at 0x82f68 *)
all: lazymatch goal with HS : st_ok_pi _ _ _ ?ss _ |- _ =>
  let pc := eval vm_compute in (ss_pc ss) in
  lazymatch pc with
  | 11576 =>
    pmkst HS;
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md2) _ =>
      apply SRr_ret; split; [reflexivity|];
      exists Sc, rg, mm, md2; left; split; [rewrite EPCR; reflexivity|];
      apply (rbe2a_R c Sc regs mem md rg mm md2 HX KEEP HJ);
      [ let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
        exact (regs_kept_of_st_ok_pi _ _ _ regs _ rbe2a_kR HS HAE ltac:(vm_compute; reflexivity) r Hr)
      | rbe2a_bool ]
    end
  | 10228 =>
    let R14 := fresh "R14" in prreg HS (14%bv : bv 5) R14;
    pmkst HS;
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?md2) _ =>
      apply SRr_ret; split; [reflexivity|];
      exists Sc, rg, mm, md2; right; split; [rewrite EPCP; reflexivity|];
      apply (rbe2a_X2a c Sc regs mem md rg mm md2 HX KEEP HJ);
      [ let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
        exact (regs_kept_of_st_ok_pi _ _ _ regs _ rbe2a_kX HS HAE ltac:(vm_compute; reflexivity) r Hr)
      | rbe2a_bool
      | rewrite R14, E32; reflexivity ]
    end
  end
end.
Qed.
(* ---- rbe_e2b: X2a (0x82f68, +0x1f4) -> X2 (0x82fc8, +0x254), listing lines 127-150. ----
   The walk stores in / out at s1 + 40 / s1 + 48 (the machine-stack window, awr_byte case 1), then picks the stem:
   said when it is non-NULL and its first byte is non-zero (the ASan 1-byte shadow check of said is discharged by the
   token engine with the shadow entry of said), else the table entry f - 1 for f in 1 .. 3 (8-byte shadow check
   discharged by the shadow entry of the table, in_zs at the current AR), else "REAC" (object 19).
   The symbolic state: the window [s1 + 40, s1 + 56) (atom 9 = s1, the only writable region), the table (object 22,
   its words atoms 33, 34, 35) and, when said <> 0, said's first byte (atom 25 = said; SLit 0, or atom 32 with a fact
   1 .. 255). s6 (atom 22) is the shadow base. k = 0: said = 0 (s9 pinned to 0); k = 1: said <> 0, sd = [];
   k = 2: said <> 0, sd <> []. *)
Definition rbe2b_Bx : sv := SOff 22 0.
Definition rbe2b_win : YP09.region := YP09.mkRegion (Some 9%nat) 40 56 40 56 [].
Definition rbe2b_tbl : YP09.region := YP09.mkRegion (Some (A_OBJ 22)) 0 24 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0))].
Definition rbe2b_sdr (v : sv) : YP09.region := YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 v)].
Definition rbe2b_fb : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF SB SB 0); (A_OBJ 22, mkAF IMG_LO (IMG_TOP - 24) 3)].
Definition rbe2b_regions (k : nat) : smem :=
  match k with
  | O => [rbe2b_win; rbe2b_tbl]
  | 1%nat => [rbe2b_win; rbe2b_tbl; rbe2b_sdr (SLit 0)]
  | _ => [rbe2b_win; rbe2b_tbl; rbe2b_sdr (SOff 32 0)]
  end.
Definition rbe2b_facts (k : nat) : facts :=
  match k with
  | O => mkFacts rbe2b_fb [] []
  | 1%nat => mkFacts (rbe2b_fb ++ [(25%nat, mkAF 4096 (2 ^ 47 - 1) 0)]) [] []
  | _ => mkFacts (rbe2b_fb ++ [(25%nat, mkAF 4096 (2 ^ 47 - 1) 0); (32%nat, mkAF 1 255 0)]) [] []
  end.
Definition rbe2b_SH (k : nat) : list shent :=
  match k with O => [mkSHE (A_OBJ 22) 0 24] | _ => [mkSHE (A_OBJ 22) 0 24; mkSHE 25 0 1] end.
Definition rbe2b_ss (k : nat) : sstate :=
  mkSS (AF_reac_box_name + 0x1f4) sr_atoms (rbe2b_regions k) None (rbe2b_facts k).
Definition rbe2b_extra (c0 t1 t2 t3 : Z) : list word := map (Z_to_bv 64) [c0; t1; t2; t3].
Definition rbe2b_E (regs : bvmap 5 word) (c0 t1 t2 t3 : Z) : env := Eimg (Ereg regs (rbe2b_extra c0 t1 t2 t3)).
(* The bytes the walk may write (the window), and the registers it keeps. *)
Definition rbe2b_z (s1 a : Z) : Prop := s1 + 40 <= a < s1 + 56.
Definition rbe2b_kregs : list (bv 5) := [2; 3; 4; 8; 9; 14; 15; 18; 19; 21; 22; 23; 24; 26]%bv.
Lemma rbe2b_s1 : forall c, x_sp0 c - 352 < x_s1 c <= x_sp0 c - 320 /\ x_s1 c mod 32 = 0.
Proof.
intros c. unfold x_s1.
pose proof (Z.div_mod (x_sp0 c - 320) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (x_sp0 c - 320) 32 ltac:(lia)) as M.
split; [lia|]. rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.
Lemma rbe2b_bv_mod : forall t, Z_to_bv 64 t = Z_to_bv 64 (t mod 2 ^ 64).
Proof.
intros t. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.
(* Every write token lies in a heap block of the entry (rbn_bufs). *)
Lemma rbe2b_fp_blk : forall c,
  rbn_bufs B (x_ly c) (x_S c) (x_name c) (x_name_len c) (x_token c) (x_token_len c) (x_display c) (x_display_len c) ->
  forall x, inFP (x_FP c) x -> exists q N, In (q, N) (ablocks B (x_ly c) (x_S c)) /\ q <= x < q + N.
Proof.
intros c (B1 & B2 & B3 & _) x HF. unfold x_FP in HF. apply rbn_fp_in in HF.
destruct HF as [(_ & Hx) | [(_ & Hx) | (_ & Hx)]].
- destruct B1 as (q & N & Hin & H1 & H2). exists q, N. split; [exact Hin | lia].
- destruct B2 as (q & N & Hin & H1 & H2). exists q, N. split; [exact Hin | lia].
- destruct B3 as (q & N & Hin & H1 & H2). exists q, N. split; [exact Hin | lia].
Qed.
(* An image word the journal keeps (rbn_fixed, sink closed) reads at the current memory as at entry. *)
Lemma rbe2b_img_now : forall c Sc mem md a n,
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] (x_ly c) Sc (x_W c) mem md 0 ->
  ~ YI16.sink_open_fp (x_FP c) -> rbn_fixed B a n ->
  forall b v, a <= b -> b + 8 <= a + n ->
  val_mem SEGS (x_mem_at c (x_mem c)) b 8 v -> val_mem SEGS (x_mem_at c mem) b 8 v.
Proof.
intros c Sc mem md a n HJ Hcl Hfix b v Hb1 Hb2 Hv.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G3 & _).
unfold x_mem_at in *. eapply val_mem_kept; [|exact Hv].
intros k Hk. change (Z.of_nat 8) with 8 in Hk.
destruct (Hfix (b + k) ltac:(lia)) as (Hi & Hns & He).
exact (G3 (b + k) Hi Hns He (fp_spares_closed _ _ Hcl)).
Qed.
(* said <> 0: its first byte and its shadow at the current memory (frame of the entry, kept by the journal; the
   write tokens lie in heap blocks, apart from the frame and from the shadow band). *)
Lemma rbe2b_said_now : forall c Sc mem md,
  rbe_mem c Sc mem md ->
  reac_box_name_c.bn_args_ok (x_name c) (x_name_len c) (x_token c) (x_token_len c) (x_display c)
    (x_display_len c) (x_i c) (x_o c) = true ->
  x_said c <> 0 ->
  4096 <= x_said c /\ x_said c + 1 <= alloc_ceiling /\ (x_said c + 1 <= IMG_LO \/ IMG_TOP <= x_said c) /\
  (x_said c + 1 <= kLowShadowBeg \/ kHighMemBeg <= x_said c) /\
  range_addressable (aview SEGS (w_H (x_W c)) mem) SHADOW_OFF (x_said c) 1 /\
  val_mem SEGS (x_mem_at c mem) (x_said c) 1 (nth 0 (x_sd c ++ [0]) 0) /\
  Forall (fun x => 0 < x < 256) (x_sd c).
Proof.
intros c Sc mem md HM Hok Hs.
destruct HM as (Hpre & HJ & _).
pose proof Hpre as (Hafn & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & Hargs & _).
destruct (Hargs Hok) as [[[Hs0 _] | (_ & Hcs & cid & pos & Hin & Hlo & Hhi)] Hbufs]; [contradiction|].
pose proof Hcs as (HF & Hlen & Hpos & Hamr & Hgarr & Hra & Hhv & Htail).
pose proof (proj1 Hafn) as HAR0.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR0 Hin) as (Hf0 & Hfc & Hfapp).
pose proof (frm_off_imgP B _ _ _ _ _ cid pos HAR0 Hin) as Himg.
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR0 Hin) as (Hal32 & _).
pose proof (frame_facts B _ _ _ cid pos (proj1 HAR0) Hin) as (Hcid & _).
assert (HnF : forall x, frame_addr (x_ly c) cid pos <= x < frame_addr (x_ly c) cid pos + fs_frame_bytes cid ->
  ~ inFP (x_FP c) x).
{ intros x Hx HFx. destruct (rbe2b_fp_blk c Hbufs x HFx) as (q & N & HqN & Hq).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ q N cid pos HAR0 HqN Hin) as Hd.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR0 HqN) as (_ & _ & _ & _ & _ & _ & HN).
  pose proof (req_size_pos N ltac:(lia)) as [_ Hr].
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (HFPs : forall x, inFP (x_FP c) x -> x < kLowShadowBeg \/ kHighShadowEnd <= x).
{ intros x HFx. destruct (rbe2b_fp_blk c Hbufs x HFx) as (q & N & HqN & Hq).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR0 HqN) as (_ & _ & _ & Happ & _ & _ & HN).
  pose proof (req_size_pos N ltac:(lia)) as [_ Hr].
  unfold in_app, kLowShadowBeg, kHighMemBeg, kHighShadowEnd in *. lia. }
assert (Hl0 : 0 <= Z.of_nat (length (x_sd c))) by lia.
split; [lia|]. split; [lia|]. split; [lia|].
split; [unfold in_app, kLowShadowBeg, kHighMemBeg in *; lia|].
split.
{ apply (range_addressable_entry_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos (x_said c) 1 HJ Hin
    ltac:(lia) ltac:(lia) ltac:(lia) (mod32_mod8 _ Hal32) HFPs HAR0).
  apply (range_addressable_sub _ _ _ _ _ _ Hra); lia. }
split; [|exact HF].
destruct (garr8_nthZ SEGS _ _ _ 0 Hgarr ltac:(lia) ltac:(rewrite length_app; cbn [length Z.to_nat]; lia))
  as [Hb0 _].
rewrite Z.add_0_r in Hb0. change (Z.to_nat 0) with 0%nat in Hb0.
unfold x_mem_at.
apply (val_mem_entry_frame SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos (x_said c) 1 _ HJ Hin ltac:(lia) ltac:(lia)).
- intros x Hx. apply HnF. lia.
- exact Hb0.
Qed.
(* The not-taken side of the bounds test at 0x82f94 for an f outside 1 .. 3: 2 <u (f - 1 as an int). *)
Lemma rbe2b_bltu_kill : forall E f, ew E 27 = Z_to_bv 64 f -> - 2 ^ 31 <= f < 2 ^ 31 -> ~ (1 <= f <= 3) ->
  branch_taken BC_LTU (sv_denot E (SLit 2)) (sv_denot E (SAluw ALU_ADD (SOff 27 0) (SLit (-1)))) = false -> False.
Proof.
intros E f H Hf Hn. rewrite branch_ltu_U, U_SLit, U_of_S, S_SAluw, U_SOff, U_SLit, H, Z.add_0_r, Z_to_bv_unsigned.
cbn [zalu_raw].
assert (A1 : zcanon (bv_wrap 64 f) mod 2 ^ 32 = f mod 2 ^ 32).
{ unfold zcanon, bv_wrap, M64. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia.
  Z.div_mod_to_equations; lia. }
replace (zcanon (-1) mod 2 ^ 32) with (2 ^ 32 - 1) by reflexivity.
replace (zcanon 2) with 2 by reflexivity.
rewrite A1. unfold bv_swrap, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
intros Hc. apply Z.ltb_ge in Hc. revert Hc.
destruct (Z_lt_le_dec f 1); Z.div_mod_to_equations; lia.
Qed.
(* The stem facts (rbn_stem at the entry memory) for the three ways the walk picks it. *)
Lemma rbe2b_stem_sd : forall c,
  rbn_said (x_ly c) (x_S c) (x_W c) (x_mem c) (x_said c) (x_sd c) -> x_sd c <> [] ->
  rbn_stem B G c (x_mem c) (x_said c).
Proof.
intros c [(_ & Hsd) | (_ & Hcs & cid & pos & H1 & H2 & H3)] Hne; [contradiction|].
left. split; [exact Hne|]. split; [reflexivity|]. split; [exact Hcs|]. exists cid, pos. auto.
Qed.
Lemma rbe2b_stem_tab : forall c k u, x_sd c = [] -> x_f c = k ->
  rbn_imgstr B G (x_W c) (x_mem c) u (bn_STEM k) -> rbn_stem B G c (x_mem c) u.
Proof.
intros c k u Hsd Hf HI. right. split; [exact Hsd|]. unfold x_stem. rewrite Hsd, Hf. exact HI.
Qed.
Lemma rbe2b_stem_reac : forall c, x_sd c = [] -> ~ (1 <= x_f c <= 3) ->
  rbn_imgstr B G (x_W c) (x_mem c) (VAL (A_OBJ 19)) (bn_STEM 0) -> rbn_stem B G c (x_mem c) (VAL (A_OBJ 19)).
Proof.
intros c Hsd Hn HI. right. split; [exact Hsd|]. unfold x_stem. rewrite Hsd. cbn [bn_stem].
replace (bn_STEM (x_f c)) with (bn_STEM 0); [exact HI|].
unfold bn_STEM. destruct (Z.eqb_spec (x_f c) 1); [lia|]. destruct (Z.eqb_spec (x_f c) 2); [lia|].
destruct (Z.eqb_spec (x_f c) 3); [lia|]. reflexivity.
Qed.
(* The symbolic state at 0x82f68 and its shadow entries. *)
Lemma rbe2b_entry : forall c Sc regs mem md (k : nat) (c0 t1 t2 t3 : Z),
  rbe_X2a c Sc regs mem md ->
  0 <= c0 < 256 -> 0 <= t1 < 2 ^ 64 -> 0 <= t2 < 2 ^ 64 -> 0 <= t3 < 2 ^ 64 ->
  val_mem SEGS (x_mem_at c mem) (VAL (A_OBJ 22)) 8 t1 ->
  val_mem SEGS (x_mem_at c mem) (VAL (A_OBJ 22) + 8) 8 t2 ->
  val_mem SEGS (x_mem_at c mem) (VAL (A_OBJ 22) + 16) 8 t3 ->
  IMG_LO + 64 <= VAL (A_OBJ 22) -> VAL (A_OBJ 22) + 24 + 64 <= IMG_TOP -> VAL (A_OBJ 22) mod 8 = 0 ->
  range_addressable (aview SEGS (w_H (x_W c)) mem) SHADOW_OFF (VAL (A_OBJ 22)) 24 ->
  (k <> O ->
     4096 <= x_said c /\ x_said c + 1 <= alloc_ceiling /\ (x_said c + 1 <= IMG_LO \/ IMG_TOP <= x_said c) /\
     (x_said c + 1 <= kLowShadowBeg \/ kHighMemBeg <= x_said c) /\
     range_addressable (aview SEGS (w_H (x_W c)) mem) SHADOW_OFF (x_said c) 1 /\
     val_mem SEGS (x_mem_at c mem) (x_said c) 1 c0) ->
  (k = 1%nat -> c0 = 0) -> ((2 <= k)%nat -> 1 <= c0 <= 255) ->
  st_ok_pi SEGS VAL (rbe2b_E regs c0 t1 t2 t3) (rbe2b_ss k)
    (restrict (w_H (x_W c)) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x1f4))) mem (seg_rom SEGS))) /\
  sh_ok SEGS rbe2b_Bx (rbe2b_SH k) (rbe2b_E regs c0 t1 t2 t3) (mrestrict (w_H (x_W c)) mem).
Proof.
intros c Sc regs mem md k c0 t1 t2 t3 HX Rc0 R1 R2 R3 V1 V2 V3 Tlo Thi T8 HRT HSD HK1 HK2.
pose proof HX as ((HM & HR & H12 & H13 & H20 & H25 & H27) & Hok & H14).
pose proof HM as (Hpre & HJ & _).
pose proof HR as (_ & _ & _ & _ & R9 & _ & _ & _ & R22 & _ & _ & _ & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HSTK : 336 + 2 * ESTACK = 8528) by reflexivity.
pose proof (rbe2b_s1 c) as ([Hs1a Hs1b] & Hs1c).
pose proof (pa_val_range (A_OBJ 22)) as RgT.
assert (Hs1r : 2 ^ 46 <= x_s1 c /\ x_s1 c + 56 <= 2 ^ 47) by (clear - Hs1a Hs1b Hceil Hslo Hshi H47 HSTK C1; lia).
assert (Hs1ac : alloc_ceiling + 8000 <= x_s1 c) by (clear - Hs1a Hceil Hslo HSTK; lia).
rewrite restrict_mkst_fx.
set (E := rbe2b_E regs c0 t1 t2 t3).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold rbe2b_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rbe2b_extra c0 t1 t2 t3)) n)
  by (intros n Hn; subst E; unfold rbe2b_E; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 (x_s1 c))
  by (rewrite EL by (unfold A_TEXT; clear; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E22 : ew E 22 = Z_to_bv 64 SB)
  by (rewrite EL by (unfold A_TEXT; clear; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact R22).
assert (E25 : ew E 25 = Z_to_bv 64 (x_said c))
  by (rewrite EL by (unfold A_TEXT; clear; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E32 : ew E 32 = Z_to_bv 64 c0) by (rewrite EL by (unfold A_TEXT; clear; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 t1) by (rewrite EL by (unfold A_TEXT; clear; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 t2) by (rewrite EL by (unfold A_TEXT; clear; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 t3) by (rewrite EL by (unfold A_TEXT; clear; lia); exact (ew_Ereg_extra regs _ 3)).
assert (ET : ew E (A_OBJ 22) = Z_to_bv 64 (VAL (A_OBJ 22)))
  by (subst E; unfold rbe2b_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; clear; lia).
assert (U9 : bv_unsigned (ew E 9) = x_s1 c) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = SB) by (rewrite E22; apply unsigned_lit_small; unfold SB; lia).
assert (UT : bv_unsigned (ew E (A_OBJ 22)) = VAL (A_OBJ 22)) by (rewrite ET; apply unsigned_lit_small; lia).
assert (UBx : U E rbe2b_Bx = SHADOW_OFF) by (unfold rbe2b_Bx; rewrite (U_atom E 22 SB E22) by (unfold SB; lia); reflexivity).
assert (UTa : U E (SOff (A_OBJ 22) 0) = VAL (A_OBJ 22)) by (exact (U_atom E (A_OBJ 22) _ ET RgT)).
assert (RO_win : region_ok SEGS E (mrestrict (w_H (x_W c)) mem) rbe2b_win).
{ unfold region_ok, rbe2b_win.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. clear - Ho Hs1a Hs1b HSTK. lia. }
assert (RO_tbl : region_ok SEGS E (mrestrict (w_H (x_W c)) mem) rbe2b_tbl).
{ unfold region_ok, rbe2b_tbl.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite UT. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 22)) 0 8 (SOff 33 0) t1);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact V1.
  - apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 22)) 8 8 (SOff 34 0) t2);
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V2].
  - apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 22)) 16 8 (SOff 35 0) t3);
    [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V3]. }
assert (A9 : afact_ok E 9 (mkAF (2 ^ 46) (2 ^ 47) 5)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32. lia. }
assert (A22 : afact_ok E 22 (mkAF SB SB 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U22, Z.pow_0_r, Z.mod_1_r. lia. }
assert (AT : afact_ok E (A_OBJ 22) (mkAF IMG_LO (IMG_TOP - 24) 3)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite UT. change (2 ^ 3) with 8. lia. }
assert (SH_tbl : shent_ok SEGS rbe2b_Bx E (mrestrict (w_H (x_W c)) mem) (mkSHE (A_OBJ 22) 0 24)).
{ apply (shent_ok_of_range SEGS (w_H (x_W c)) mem E rbe2b_Bx (A_OBJ 22) (VAL (A_OBJ 22)) 24 (VAL (A_OBJ 22)) 0 24
    HRT UBx UTa); [lia | lia |].
  intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia. }
destruct k as [|[|k]].
- (* said = 0 *)
  split.
  + unfold rbe2b_ss, rbe2b_regions, rbe2b_facts, rbe2b_fb. apply pa_entry_st_ok_full.
    * subst E. unfold rbe2b_E. apply regs_ok_Eimg_Ereg.
    * vm_compute. reflexivity.
    * repeat apply Forall_cons; try apply Forall_nil; assumption.
    * apply pairwise_disjoint_of_extents. unfold rbe2b_win, rbe2b_tbl, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, UT.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - Hs1r Thi. repeat split; lia.
    * unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok app].
      split; [|split; exact I].
      repeat match goal with |- _ /\ _ => split end; first [exact A9 | exact A22 | exact AT | exact I].
  + unfold sh_ok, rbe2b_SH. repeat apply Forall_cons; try apply Forall_nil; assumption.
- (* said <> 0, sd = [] *)
  destruct (HSD ltac:(discriminate)) as (S1 & S2 & S3 & S4 & S5 & S6).
  pose proof (HK1 eq_refl) as ->.
  assert (U25 : bv_unsigned (ew E 25) = x_said c) by (rewrite E25; apply unsigned_lit_small; lia).
  assert (U25a : U E (SOff 25 0) = x_said c) by (exact (U_atom E 25 _ E25 ltac:(lia))).
  assert (RO_sd : region_ok SEGS E (mrestrict (w_H (x_W c)) mem) (rbe2b_sdr (SLit 0))).
  { unfold region_ok, rbe2b_sdr.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U25. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (x_said c) 0 1 (SLit 0) 0); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact S6. }
  assert (A25 : afact_ok E 25 (mkAF 4096 (2 ^ 47 - 1) 0)).
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U25, Z.pow_0_r, Z.mod_1_r. lia. }
  assert (SH_sd : shent_ok SEGS rbe2b_Bx E (mrestrict (w_H (x_W c)) mem) (mkSHE 25 0 1)).
  { apply (shent_ok_of_range SEGS (w_H (x_W c)) mem E rbe2b_Bx 25 (x_said c) 1 (x_said c) 0 1 S5 UBx U25a);
    [lia | lia |].
    intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. unfold kLowShadowBeg, kHighMemBeg in S4. lia. }
  split.
  + unfold rbe2b_ss, rbe2b_regions, rbe2b_facts, rbe2b_fb. apply pa_entry_st_ok_full.
    * subst E. unfold rbe2b_E. apply regs_ok_Eimg_Ereg.
    * vm_compute. reflexivity.
    * repeat apply Forall_cons; try apply Forall_nil; assumption.
    * apply pairwise_disjoint_of_extents. unfold rbe2b_win, rbe2b_tbl, rbe2b_sdr, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, UT, U25.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - Hs1r Hs1ac Thi Tlo S1 S2 S3 C1. repeat split; lia.
    * unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok app].
      split; [|split; exact I].
      repeat match goal with |- _ /\ _ => split end; first [exact A9 | exact A22 | exact AT | exact A25 | exact I].
  + unfold sh_ok, rbe2b_SH. repeat apply Forall_cons; try apply Forall_nil; assumption.
- (* said <> 0, sd = c0 :: _ *)
  destruct (HSD ltac:(discriminate)) as (S1 & S2 & S3 & S4 & S5 & S6).
  pose proof (HK2 ltac:(lia)) as Hc0.
  assert (U25 : bv_unsigned (ew E 25) = x_said c) by (rewrite E25; apply unsigned_lit_small; lia).
  assert (U25a : U E (SOff 25 0) = x_said c) by (exact (U_atom E 25 _ E25 ltac:(lia))).
  assert (U32 : bv_unsigned (ew E 32) = c0) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (RO_sd : region_ok SEGS E (mrestrict (w_H (x_W c)) mem) (rbe2b_sdr (SOff 32 0))).
  { unfold region_ok, rbe2b_sdr.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U25. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (x_said c) 0 1 (SOff 32 0) c0);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact S6. }
  assert (A25 : afact_ok E 25 (mkAF 4096 (2 ^ 47 - 1) 0)).
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U25, Z.pow_0_r, Z.mod_1_r. lia. }
  assert (A32 : afact_ok E 32 (mkAF 1 255 0)).
  { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32, Z.pow_0_r, Z.mod_1_r. lia. }
  assert (SH_sd : shent_ok SEGS rbe2b_Bx E (mrestrict (w_H (x_W c)) mem) (mkSHE 25 0 1)).
  { apply (shent_ok_of_range SEGS (w_H (x_W c)) mem E rbe2b_Bx 25 (x_said c) 1 (x_said c) 0 1 S5 UBx U25a);
    [lia | lia |].
    intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. unfold kLowShadowBeg, kHighMemBeg in S4. lia. }
  split.
  + unfold rbe2b_ss, rbe2b_regions, rbe2b_facts, rbe2b_fb. apply pa_entry_st_ok_full.
    * subst E. unfold rbe2b_E. apply regs_ok_Eimg_Ereg.
    * vm_compute. reflexivity.
    * repeat apply Forall_cons; try apply Forall_nil; assumption.
    * apply pairwise_disjoint_of_extents. unfold rbe2b_win, rbe2b_tbl, rbe2b_sdr, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, UT, U25.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - Hs1r Hs1ac Thi Tlo S1 S2 S3 C1. repeat split; lia.
    * unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok app].
      split; [|split; exact I].
      repeat match goal with |- _ /\ _ => split end;
      first [exact A9 | exact A22 | exact AT | exact A25 | exact A32 | exact I].
  + unfold sh_ok, rbe2b_SH. repeat apply Forall_cons; try apply Forall_nil; assumption.
Qed.
(* The state at 0x82fc8 from the end of a run: the memory facts of X2 carried over the window writes, the kept
   registers, s9 = st, in / out from the final window region, and the stem. *)
Lemma rbe2b_post : forall c Sc regs mem md st regs' mem' md' E cs,
  rbe_X2a c Sc regs mem md ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] (x_ly c) Sc (x_W c) mem' md' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ rbe2b_z (x_s1 c) a ->
     aview SEGS (w_H (x_W c)) mem' a = aview SEGS (w_H (x_W c)) mem a) ->
  (forall r, In r rbe2b_kregs -> getr regs' r = getr regs r) ->
  getr regs' 25 = w64 st ->
  region_ok SEGS E (mrestrict (w_H (x_W c)) mem') (YP09.mkRegion (Some 9%nat) 40 56 40 56 cs) ->
  bv_unsigned (ew E 9) = x_s1 c -> ew E 12 = w64 (x_i c) -> ew E 13 = w64 (x_o c) ->
  In (YP09.mkChunk 40 (CVal 8 (SOff 12 0))) cs -> In (YP09.mkChunk 48 (CVal 8 (SOff 13 0))) cs ->
  rbn_stem B G c (x_mem c) st ->
  rbe_X2 c Sc st regs' mem' md'.
Proof.
intros c Sc regs mem md st regs' mem' md' E cs HX HJ' KEEP HKR H25' HR0 U9 E12 E13 C40 C48 HST.
destruct HX as ((HM & HR & H12 & H13 & H20 & H25 & H27) & Hok & H14).
destruct HM as (Hpre & HJ & Hblk & Hsv & Hnl & HF80 & Hflag & Hsc & Hbk).
pose proof (rbe2b_s1 c) as ([Hs1a Hs1b] & _).
pose proof HJ' as (HAR' & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (HSTK : 336 + 2 * ESTACK = 8528) by reflexivity.
assert (KLO : forall a, 0 <= a < x_s1 c + 40 ->
  aview SEGS (w_H (x_W c)) mem' a = aview SEGS (w_H (x_W c)) mem a).
{ intros a Ha. apply KEEP; [clear - Ha Hs1a Hs1b Hslo Hshi H47 HSTK; lia | unfold rbe2b_z; clear - Ha; lia]. }
assert (KHI : forall a, x_s1 c + 56 <= a < 2 ^ 64 ->
  aview SEGS (w_H (x_W c)) mem' a = aview SEGS (w_H (x_W c)) mem a).
{ intros a Ha. apply KEEP; [clear - Ha Hs1a Hs1b Hceil Hslo HSTK C1; lia | unfold rbe2b_z; clear - Ha; lia]. }
assert (HinF : In (3, x_fpos c) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 (x_fpos c) HAR' HinF) as (HF0 & HFc & _).
change (frame_addr (x_ly c) 3 (x_fpos c)) with (x_F c) in HF0, HFc.
assert (HFB : fs_frame_bytes 3 = 512) by reflexivity.
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as MF.
split.
{ split; [exact Hpre|]. split; [exact HJ'|]. split; [exact Hblk|].
  split.
  { unfold rbn_saved in *. apply Forall_forall. intros p Hp.
    pose proof (proj1 (Forall_forall _ _) Hsv p Hp) as Hv.
    assert (Hfp : 8 <= fst p <= 104)
      by (unfold rbn_saved_regs in Hp; repeat (destruct Hp as [<- | Hp]; [cbn [fst]; lia|]); destruct Hp).
    unfold x_mem_at in *. eapply val_mem_kept; [|exact Hv]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    apply KHI. clear - Hk Hfp Hs1b Hshi H47. lia. }
  split.
  { unfold x_mem_at in *. eapply val_mem_kept; [|exact Hnl]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    apply KHI. clear - Hk Hs1b Hshi H47. lia. }
  split.
  { unfold x_mem_at in *. eapply val_mem_kept; [|exact HF80]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    apply KHI. clear - Hk Hs1b Hshi H47. lia. }
  split.
  { rewrite <- Hflag. apply rdword_ext. intros k Hk. apply KLO.
    clear - Hk HF0 HFc HFB Hceil Hslo HSTK Hs1a. lia. }
  split.
  { unfold rbn_scope in *. cbv zeta in *. destruct Hsc as (S1 & S2 & S3 & S4).
    assert (HFS : forall j, 0 <= j < 64 -> 0 <= x_FS c + j < x_s1 c + 40)
      by (intros j Hj; unfold x_FS, SHADOW_OFF; clear - Hj DF MF HF0 HFc HFB Hceil Hslo HSTK Hs1a C1; lia).
    split; [rewrite KLO by (apply HFS; clear; lia); exact S1|].
    split; [intros j Hj; rewrite KLO by (apply HFS; clear - Hj; lia); exact (S2 j Hj)|].
    split; [intros j Hj; rewrite KLO by (apply HFS; clear - Hj; lia); exact (S3 j Hj)|].
    intros j Hj; rewrite KLO by (apply HFS; clear - Hj; lia); exact (S4 j Hj). }
  { unfold rbn_bufkept in *. intros a HFa Hb. rewrite <- (Hbk a HFa Hb). apply KLO.
    destruct Hb as (q & N & Hin & Hq).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q N (proj1 (proj1 Hpre)) Hin) as (_ & H4096 & Hqc & _ & _ & _ & HN).
    pose proof (req_size_pos N ltac:(lia)) as [_ Hr].
    clear - Hq H4096 Hqc Hr Hceil Hslo HSTK Hs1a. lia. } }
split.
{ unfold rbe_regs in *.
  rewrite !HKR by (unfold rbe2b_kregs; repeat first [left; reflexivity | right]).
  exact HR. }
split; [exact Hok|].
split; [rewrite HKR by (unfold rbe2b_kregs; repeat first [left; reflexivity | right]); exact H14|].
split; [exact H25'|].
split.
{ apply (field_of_region E _ 9 (x_s1 c) cs 40 56 40 56 40 8 (SOff 12 0) (x_i c mod 2 ^ 64) HR0 U9 C40).
  - cbn [sv_denot]. rewrite E12. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply rbe2b_bv_mod.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
  - cbn. lia. }
split.
{ apply (field_of_region E _ 9 (x_s1 c) cs 40 56 40 56 48 8 (SOff 13 0) (x_o c mod 2 ^ 64) HR0 U9 C48).
  - cbn [sv_denot]. rewrite E13. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply rbe2b_bv_mod.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
  - cbn. lia. }
exact HST.
Qed.
(* The environment's atoms the walk's post reads. *)
Lemma rbe2b_envf : forall c Sc regs mem md (c0 t1 t2 t3 : Z), rbe_X2a c Sc regs mem md ->
  img_env VAL A_LIM (rbe2b_E regs c0 t1 t2 t3) /\
  env_agree 32 (Ereg regs (rbe2b_extra c0 t1 t2 t3)) (rbe2b_E regs c0 t1 t2 t3) /\
  bv_unsigned (ew (rbe2b_E regs c0 t1 t2 t3) 9) = x_s1 c /\
  ew (rbe2b_E regs c0 t1 t2 t3) 12 = w64 (x_i c) /\ ew (rbe2b_E regs c0 t1 t2 t3) 13 = w64 (x_o c) /\
  ew (rbe2b_E regs c0 t1 t2 t3) 25 = w64 (x_said c) /\ ew (rbe2b_E regs c0 t1 t2 t3) 27 = Z_to_bv 64 (x_f c) /\
  ew (rbe2b_E regs c0 t1 t2 t3) 33 = Z_to_bv 64 t1 /\ ew (rbe2b_E regs c0 t1 t2 t3) 34 = Z_to_bv 64 t2 /\
  ew (rbe2b_E regs c0 t1 t2 t3) 35 = Z_to_bv 64 t3 /\
  ew (rbe2b_E regs c0 t1 t2 t3) 260%nat = Z_to_bv 64 (VAL (A_OBJ 19)).
Proof.
intros c Sc regs mem md c0 t1 t2 t3 HX.
pose proof HX as ((HM & HR & H12 & H13 & H20 & H25 & H27) & Hok & H14).
pose proof HM as (Hpre & HJ & _).
pose proof HR as (_ & _ & _ & _ & R9 & _ & _ & _ & _ & _ & _ & _ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
pose proof (rbe2b_s1 c) as ([Hs1a Hs1b] & _).
assert (HSTK : 336 + 2 * ESTACK = 8528) by reflexivity.
assert (Hs1r : 0 <= x_s1 c < 2 ^ 64) by (clear - Hs1a Hs1b Hceil Hslo Hshi H47 HSTK C1; lia).
set (E := rbe2b_E regs c0 t1 t2 t3).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (rbe2b_extra c0 t1 t2 t3)) n)
  by (intros n Hn; subst E; unfold rbe2b_E; apply Eimg_low; exact Hn).
split; [subst E; unfold rbe2b_E; apply Eimg_env|].
split; [split; [intros n Hn; apply EL; unfold A_TEXT; clear - Hn; lia | subst E; reflexivity]|].
split.
{ rewrite EL by (unfold A_TEXT; clear; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9.
  apply unsigned_lit_small. exact Hs1r. }
split; [rewrite EL by (unfold A_TEXT; clear; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12|].
split; [rewrite EL by (unfold A_TEXT; clear; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13|].
split; [rewrite EL by (unfold A_TEXT; clear; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25|].
split; [rewrite EL by (unfold A_TEXT; clear; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27|].
split; [rewrite EL by (unfold A_TEXT; clear; lia); exact (ew_Ereg_extra regs _ 1)|].
split; [rewrite EL by (unfold A_TEXT; clear; lia); exact (ew_Ereg_extra regs _ 2)|].
split; [rewrite EL by (unfold A_TEXT; clear; lia); exact (ew_Ereg_extra regs _ 3)|].
subst E. unfold rbe2b_E. exact (Eimg_img _ 260%nat ltac:(unfold A_TEXT, A_LIM; clear; lia)).
Qed.
(* ---- The walk's tactics. ---- *)
Local Ltac rbe2b_awr :=
  lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx);
    lazymatch goal with U9 : bv_unsigned (ew _ 9%nat) = ?S1, HWIN : - _ <= ?S1 - _ + 40 /\ _ |- _ =>
    repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; clear; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (S1 - spx));
      [ reflexivity
      | cbn [ew ewset Nat.eqb]; rewrite U9; ring
      | cbn [YP09.r_wlo]; clear - HWIN; lia
      | cbn [YP09.r_whi]; clear - HWIN; lia
      | ] ]
    end
  end.
Local Ltac rbe2b_win :=
  let bb0 := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros bb0 wlo whi x Hin Hr;
  vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [ injection Hin as <- <- <-; cbn [base_val ew ewset Nat.eqb] in Hr;
      try (lazymatch goal with U9 : bv_unsigned (ew _ 9%nat) = _ |- _ => rewrite U9 in Hr end);
      unfold rbe2b_z; clear - Hr; lia
    | ]);
  try destruct Hin.
Local Ltac rbe2b_keep :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1),
    KEEP : forall a, _ -> ~ rbe2b_z ?S1 a -> aview ?sg ?H ?m0 a = aview _ _ ?mem a |- _ =>
    let K2 := fresh "KEEP" in
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ rbe2b_z S1 a -> aview sg H m1 a = aview sg H mem a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in
      intros a Ha Hz;
      refine (eq_trans (kept_of_frame Ex rs H m0 m1 (rbe2b_z S1) HFr _ a Ha Hz) (KEEP a Ha Hz)); rbe2b_win
    | clear KEEP; repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end ]
  end.
Local Ltac rbe2b_agree :=
  lazymatch goal with HAE : env_agree 32 ?E1 ?E0 |- env_agree 32 ?E1 ?Ex =>
    split;
    [ let nn := fresh "nn" in let Hnn := fresh "Hnn" in intros nn Hnn;
      repeat (rewrite ew_ewset_other by (clear - Hnn; lia)); exact (proj1 HAE nn Hnn)
    | exact (proj2 HAE) ]
  end.
Local Ltac rbe2b_fin :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?W) ?msx), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    KEEP : forall a, _ -> ~ rbe2b_z _ a -> _,
    HX : rbe_X2a ?c ?Sc ?regs ?mem ?md, HAE : env_agree 32 (Ereg ?regs ?extra) _ |- _ =>
    let R25 := fresh "R25" in prreg HS (25%bv : bv 5) R25;
    repeat match goal with Ei : ew _ _ = _ |- _ => rewrite Ei in R25 end;
    let HR0 := fresh "HR0" in
    pose proof (st_ok_pi_region_nth Ex _ (restrict (w_H W) msx) 0%nat _ HS eq_refl) as HR0;
    cbn [restrict ms_mem] in HR0;
    pmkst HS;
    apply SRr_ret; split; [reflexivity|];
    eexists; exists Sc, (ms_regs msx), (ms_mem msx); eexists;
    split; [rewrite <- (Z.add_assoc BASE AF_reac_box_name 0x254); reflexivity|];
    eapply (rbe2b_post c Sc regs mem md _ (ms_regs msx) (ms_mem msx) _ Ex _ HX HJ KEEP);
    [ let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
      exact (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H W) msx) regs extra rbe2b_kregs HS
               ltac:(rbe2b_agree) ltac:(vm_compute; reflexivity) r Hr)
    | exact R25
    | exact HR0
    | cbn [ew ewset Nat.eqb]; assumption
    | cbn [ew ewset Nat.eqb]; assumption
    | cbn [ew ewset Nat.eqb]; assumption
    | repeat first [left; reflexivity | right]
    | repeat first [left; reflexivity | right]
    | assumption ]
  end.
Local Ltac rbe2b_dead :=
  lazymatch goal with
  | Hc : branch_taken BC_LTU _ _ = false, HN : ~ (1 <= ?f <= 3), Hfr : - 2 ^ 31 <= ?f < 2 ^ 31,
    E27 : ew _ 27%nat = Z_to_bv 64 ?f |- _ =>
    exfalso; refine (rbe2b_bltu_kill _ _ _ Hfr HN Hc); cbn [ew ewset Nat.eqb]; exact E27
  end.
Local Ltac rbe2b_go :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 10324; [rbe2b_awr | ];
    rbe2b_keep;
    lazymatch goal with
    | HS' : st_ok_pi _ _ _ ?ss _, SHOK' : sh_ok _ ?Bx ?SH _ _ |- _ =>
      let pc := eval vm_compute in (ss_pc ss) in
      lazymatch pc with
      | 10324 => rbe2b_fin
      | _ =>
        let K := eval vm_compute in (run_K A_LIM Bx SH ss) in
        let why := lazymatch paj_tables RUN with (?tpi, ?tw) =>
          psym_why_tok tpi tw K Bx Bspan SH (start K Bx Bspan SH ss) end in
        lazymatch why with
        | SR_branch _ _ _ =>
          psrr_branch_tok RUN BR HS' SHOK' Bspan;
          [ first [ solve [rbe2b_dead] | rbe2b_go ] | first [ solve [rbe2b_dead] | rbe2b_go ] ]
        | _ => fail 100 "rbe2b_go: the run stopped at" pc why
        end
      end
    end
  end.
Local Ltac rbe2b_pin r v P :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss0 ?ms0 |- _ =>
    let HP := fresh "HP" in
    pose proof (st_ok_pi_pin_reg' Ex ss0 ms0 r v HS P eq_refl) as HP;
    clear HS; rename HP into HS;
    lazymatch type of HS with st_ok_pi _ _ _ ?ss1 _ => let ss2 := eval vm_compute in ss1 in change ss1 with ss2 in HS end
  end.
(* f in 1 .. 3 (s11 pinned: the table entry f - 1) or not (the bounds test sends the walk to "REAC"). *)
Local Ltac rbe2b_fsplit c regs u1 u2 u3 I1 I2 I3 IR Hsd H27 Hfr :=
  let FC := fresh "FC" in let Hf1 := fresh "Hf1" in let HN := fresh "HN" in
  let ST := fresh "ST" in let P27 := fresh "P27" in
  assert (FC : x_f c = 1 \/ x_f c = 2 \/ x_f c = 3 \/ ~ (1 <= x_f c <= 3)) by (clear - Hfr; lia);
  destruct FC as [Hf1 | [Hf1 | [Hf1 | HN]]];
  [ assert (ST : rbn_stem B G c (x_mem c) u1) by exact (rbe2b_stem_tab c 1 u1 Hsd Hf1 I1);
    assert (P27 : getr regs 27%bv = Z_to_bv 64 1) by (rewrite H27, Hf1; reflexivity);
    rbe2b_pin (27%bv : bv 5) 1 P27; rbe2b_go
  | assert (ST : rbn_stem B G c (x_mem c) u2) by exact (rbe2b_stem_tab c 2 u2 Hsd Hf1 I2);
    assert (P27 : getr regs 27%bv = Z_to_bv 64 2) by (rewrite H27, Hf1; reflexivity);
    rbe2b_pin (27%bv : bv 5) 2 P27; rbe2b_go
  | assert (ST : rbn_stem B G c (x_mem c) u3) by exact (rbe2b_stem_tab c 3 u3 Hsd Hf1 I3);
    assert (P27 : getr regs 27%bv = Z_to_bv 64 3) by (rewrite H27, Hf1; reflexivity);
    rbe2b_pin (27%bv : bv 5) 3 P27; rbe2b_go
  | assert (ST : rbn_stem B G c (x_mem c) (VAL (A_OBJ 19))) by exact (rbe2b_stem_reac c Hsd HN IR);
    rbe2b_go ].
Lemma rbe_e2b : forall c Sc regs mem md, rbe_X2a c Sc regs mem md ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_name + 0x1f4)) mem (seg_rom SEGS)) md)
    (fun W' c' => W' = x_W c /\ exists st Sc' regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x254)) mem' (seg_rom SEGS)) md' /\
       rbe_X2 c Sc' st regs' mem' md').
Proof.
intros c Sc regs mem md HX.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HX as ((HM & HR & H12 & H13 & H20 & H25 & H27) & Hok & H14).
pose proof HM as (Hpre & HJ & _).
pose proof HR as (_ & _ & _ & _ & R9 & _ & _ & _ & R22 & _ & _ & _ & _).
pose proof Hpre as (Hafn & _ & _ & Hfr & _ & Hsdr & _ & Hir & _ & Hor & _ & Hnmr & _ & _ & _ & Htkr & _ & _ & _ & _ &
  Hdr & _ & _ & Himg & Hargs & _).
destruct (Hargs Hok) as [Hsaid Hbufs].
pose proof Himg as (Ht8 & Htlo & Hthi & Hzs & Htfix & (u1 & u2 & u3 & V1 & V2 & V3 & I1 & I2 & I3) & IR & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
pose proof (rbe2b_s1 c) as ([Hs1a Hs1b] & _).
assert (HSTK : 336 + 2 * ESTACK = 8528) by reflexivity.
assert (Hs1r : 0 <= x_s1 c < 2 ^ 64) by (clear - Hs1a Hs1b Hceil Hslo Hshi H47 HSTK C1; lia).
assert (HWIN : - (336 + 2 * ESTACK) <= x_s1 c - x_sp0 c + 40 /\ x_s1 c - x_sp0 c + 56 <= 0)
  by (clear - Hs1a Hs1b HSTK; lia).
assert (Hcl : ~ YI16.sink_open_fp (x_FP c))
  by (exact (rbn_fp_closed _ _ _ _ _ _ (proj1 Hnmr) (proj1 Htkr) (proj1 Hdr))).
assert (W1 : val_mem SEGS (x_mem_at c mem) (VAL (A_OBJ 22)) 8 u1)
  by (exact (rbe2b_img_now c Sc mem md _ 24 HJ Hcl Htfix (VAL (A_OBJ 22)) u1 ltac:(clear; lia) ltac:(clear; lia) V1)).
assert (W2 : val_mem SEGS (x_mem_at c mem) (VAL (A_OBJ 22) + 8) 8 u2)
  by (exact (rbe2b_img_now c Sc mem md _ 24 HJ Hcl Htfix (VAL (A_OBJ 22) + 8) u2 ltac:(clear; lia) ltac:(clear; lia) V2)).
assert (W3 : val_mem SEGS (x_mem_at c mem) (VAL (A_OBJ 22) + 16) 8 u3)
  by (exact (rbe2b_img_now c Sc mem md _ 24 HJ Hcl Htfix (VAL (A_OBJ 22) + 16) u3 ltac:(clear; lia) ltac:(clear; lia) V3)).
pose proof (ro_usable SEGS B LAWS _ _ _ _ _ _ _ HAR Hzs) as HRT.
pose proof I1 as (I1lo & I1hi & _). pose proof I2 as (I2lo & I2hi & _). pose proof I3 as (I3lo & I3hi & _).
assert (Ru1 : 0 <= u1 < 2 ^ 64) by (clear - I1lo I1hi; lia).
assert (Ru2 : 0 <= u2 < 2 ^ 64) by (clear - I2lo I2hi; lia).
assert (Ru3 : 0 <= u3 < 2 ^ 64) by (clear - I3lo I3hi; lia).
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ rbe2b_z (x_s1 c) a ->
  aview SEGS (w_H (x_W c)) mem a = aview SEGS (w_H (x_W c)) mem a) by (intros; reflexivity).
rewrite <- (Z.add_assoc BASE AF_reac_box_name 0x1f4).
pose proof Hsaid as Hsaid'.
destruct Hsaid as [(Hs0 & Hsd) | (Hsn & _)].
- (* said = 0: s9 pinned to 0, the stem is the table entry or "REAC" *)
  destruct (rbe2b_entry c Sc regs mem md 0 0 u1 u2 u3 HX ltac:(clear; lia) Ru1 Ru2 Ru3 W1 W2 W3 Htlo
    ltac:(clear - Hthi; lia) Ht8 HRT ltac:(intros Hk; exfalso; exact (Hk eq_refl))
    ltac:(intros; reflexivity) ltac:(intros Hk; exfalso; clear - Hk; lia)) as [HS SHOK].
  destruct (rbe2b_envf c Sc regs mem md 0 u1 u2 u3 HX) as (HEI & HAE & U9 & E12 & E13 & E25 & E27 & E33 & E34 & E35 & E260).
  remember (rbe2b_E regs 0 u1 u2 u3) as E eqn:HE. clear HE.
  assert (P25 : getr regs 25%bv = Z_to_bv 64 0) by (rewrite H25, Hs0; reflexivity).
  rbe2b_pin (25%bv : bv 5) 0 P25.
  rbe2b_fsplit c regs u1 u2 u3 I1 I2 I3 IR Hsd H27 Hfr.
- destruct (rbe2b_said_now c Sc mem md HM Hok Hsn) as (Sa1 & Sa2 & Sa3 & Sa4 & Sa5 & Sa6 & Sa7).
  destruct (x_sd c) as [|c0 sd'] eqn:Hsd; rewrite ?Hsd in Sa6, Sa7.
  + (* said <> 0, sd = []: said[0] = 0, the stem is the table entry or "REAC" *)
    destruct (rbe2b_entry c Sc regs mem md 1 0 u1 u2 u3 HX ltac:(clear; lia) Ru1 Ru2 Ru3 W1 W2 W3 Htlo
      ltac:(clear - Hthi; lia) Ht8 HRT (fun _ => conj Sa1 (conj Sa2 (conj Sa3 (conj Sa4 (conj Sa5 Sa6)))))
      ltac:(intros; reflexivity) ltac:(intros Hk; exfalso; clear - Hk; lia)) as [HS SHOK].
    destruct (rbe2b_envf c Sc regs mem md 0 u1 u2 u3 HX) as (HEI & HAE & U9 & E12 & E13 & E25 & E27 & E33 & E34 & E35 & E260).
  remember (rbe2b_E regs 0 u1 u2 u3) as E eqn:HE. clear HE.
    rbe2b_fsplit c regs u1 u2 u3 I1 I2 I3 IR Hsd H27 Hfr.
  + (* said <> 0, sd = c0 :: _: the stem is said *)
    apply Forall_inv in Sa7.
    assert (ST : rbn_stem B G c (x_mem c) (x_said c)) by (apply rbe2b_stem_sd; rewrite Hsd; [exact Hsaid' | discriminate]).
    destruct (rbe2b_entry c Sc regs mem md 2 c0 u1 u2 u3 HX ltac:(clear - Sa7; lia) Ru1 Ru2 Ru3 W1 W2 W3 Htlo
      ltac:(clear - Hthi; lia) Ht8 HRT (fun _ => conj Sa1 (conj Sa2 (conj Sa3 (conj Sa4 (conj Sa5 Sa6)))))
      ltac:(intros Hk; discriminate Hk) ltac:(intros _; clear - Sa7; lia)) as [HS SHOK].
    destruct (rbe2b_envf c Sc regs mem md c0 u1 u2 u3 HX) as (HEI & HAE & U9 & E12 & E13 & E25 & E27 & E33 & E34 & E35 & E260).
    remember (rbe2b_E regs c0 u1 u2 u3) as E eqn:HE. clear HE.
    rbe2b_go.
Qed.
(* ---- X2 (0x82fc8, +0x254) -> C1 (0x83000, +0x28c, back from memset(s1 + 200, 0, 16)). ---- *)
(* s1 = sp0 - 320 rounded down to 32: 16-aligned below sp0 by 320 or 336. *)
Lemma rbe2c_s1 : forall c, x_sp0 c mod 16 = 0 ->
  x_sp0 c - 336 <= x_s1 c <= x_sp0 c - 320 /\ x_s1 c mod 32 = 0 /\ (x_s1 c - x_sp0 c) mod 16 = 0.
Proof.
intros c H16. unfold x_s1.
pose proof (Z.div_mod (x_sp0 c - 320) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (x_sp0 c - 320) 32 ltac:(lia)) as M.
pose proof (Z.div_mod (x_sp0 c) 16 ltac:(lia)) as D16. rewrite H16, Z.add_0_r in D16.
set (q := (x_sp0 c - 320) / 32) in *. set (r := (x_sp0 c - 320) mod 32) in *. set (t := x_sp0 c / 16) in *.
split; [lia|]. split.
- rewrite Z.mul_comm. apply Z_mod_mult.
- replace (32 * q - x_sp0 c) with ((2 * q - t) * 16) by lia. apply Z_mod_mult.
Qed.
(* A range of the machine stack: its shadow is zero (AR_zshadow_law, the stack range is page aligned), so it is
   addressable and its shadow hull is readable. *)
Lemma rbe2c_stk_shadow : forall (rd : Z -> option Z) lo hi x n,
  zero_shadow rd SHADOW_OFF lo (hi - lo) -> lo mod 4096 = 0 -> hi mod 4096 = 0 -> 0 <= lo ->
  lo <= x -> x + n <= hi -> x mod 8 = 0 -> n mod 8 = 0 -> 0 < n ->
  range_addressable rd SHADOW_OFF x n /\ shadow_hull_vis rd x n.
Proof.
intros rd lo hi x n Hz Hlo Hhi Hlo0 Hx Hxn Hx8 Hn8 Hn.
pose proof (Z.div_mod lo 4096 ltac:(lia)) as Dl. rewrite Hlo, Z.add_0_r in Dl.
pose proof (Z.div_mod hi 4096 ltac:(lia)) as Dh. rewrite Hhi, Z.add_0_r in Dh.
assert (Hl8 : lo mod 8 = 0) by (replace lo with ((512 * (lo / 4096)) * 8) by lia; apply Z_mod_mult).
assert (Hh8 : hi mod 8 = 0) by (replace hi with ((512 * (hi / 4096)) * 8) by lia; apply Z_mod_mult).
assert (Hl64 : lo mod 64 = 0) by (replace lo with ((64 * (lo / 4096)) * 64) by lia; apply Z_mod_mult).
assert (Hh64 : hi mod 64 = 0) by (replace hi with ((64 * (hi / 4096)) * 64) by lia; apply Z_mod_mult).
assert (Hhl8 : (hi - lo) mod 8 = 0) by (replace (hi - lo) with ((512 * (hi / 4096) - 512 * (lo / 4096)) * 8) by lia; apply Z_mod_mult).
split.
- eapply range_addressable_sub; [apply zero_shadow_range; [exact Hl8 | exact Hhl8 | exact Hz] | lia | lia].
- intros s Hs. destruct (hull_inside lo hi x n s Hl64 Hh64 Hlo0 Hx Hxn ltac:(lia) Hs) as (g & Hg8 & Hg & ->).
  pose proof (Z.div_mod g 8 ltac:(lia)) as Dg. rewrite Hg8, Z.add_0_r in Dg.
  pose proof (Z.div_mod lo 8 ltac:(lia)) as Dl8. rewrite Hl8, Z.add_0_r in Dl8.
  pose proof (Z.div_mod hi 8 ltac:(lia)) as Dh8. rewrite Hh8, Z.add_0_r in Dh8.
  assert (Ei : (g - lo) / 8 = g / 8 - lo / 8).
  { replace (g - lo) with ((g / 8 - lo / 8) * 8) by (clear - Dg Dl8; lia). apply Z.div_mul. lia. }
  assert (Eh : (hi - lo) / 8 = hi / 8 - lo / 8).
  { replace (hi - lo) with ((hi / 8 - lo / 8) * 8) by (clear - Dh8 Dl8; lia). apply Z.div_mul. lia. }
  unfold zero_shadow in Hz. specialize (Hz ((g - lo) / 8) ltac:(rewrite Ei, Eh; clear - Dg Dl8 Dh8 Hg; lia)).
  unfold shadow_of_addr in Hz. unfold shadow_addr.
  replace (SHADOW_OFF + g / 8) with (SHADOW_OFF + lo / 8 + (g - lo) / 8) by (rewrite Ei; clear; lia).
  rewrite Hz. discriminate.
Qed.
(* The shadow byte of an address of an 8-aligned range lies in the range's shadow. *)
Lemma rbe2c_fsh : forall F b x, F mod 8 = 0 -> b mod 8 = 0 -> F <= x < F + b ->
  shadow_addr F <= shadow_addr x < shadow_addr F + b / 8.
Proof.
intros F b x HF Hb Hx. unfold shadow_addr.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF, Z.add_0_r in DF.
pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite Hb, Z.add_0_r in Db.
assert (F / 8 <= x / 8) by (apply Z.div_le_mono; lia).
assert (x / 8 < F / 8 + b / 8) by (apply Z.div_lt_upper_bound; lia).
lia.
Qed.
Lemma rbe2c_zero4 : forall H (m : word -> option byte) a,
  (forall i, 0 <= i < 4 -> aview SEGS H m (a + i) = Some 0) -> val_mem SEGS (mrestrict H m) a 4 0.
Proof.
intros H m a Hz j Hj. specialize (Hz (Z.of_nat j) ltac:(lia)). unfold aview in Hz. revert Hz.
destruct (mbyte SEGS (mrestrict H m) (a + Z.of_nat j)) as [b|] eqn:Hb; cbn [option_map]; intros Hz; [|discriminate Hz].
injection Hz as Hz. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by (vm_compute; discriminate)). lia.
Qed.
(* The stem string through the caller's journal: said lies in a frame of the entry state (frame bytes and frame
   shadow are kept, the buffers are in heap blocks), an image stem in kept image bytes (the write tokens are
   closed, rbn_fp_closed). *)
Lemma rbe2c_stem : forall c st own lyc Sc mem' md' k,
  rbn_pre B G c ->
  reac_box_name_c.bn_args_ok (x_name c) (x_name_len c) (x_token c) (x_token_len c) (x_display c)
    (x_display_len c) (x_i c) (x_o c) = true ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    own lyc Sc (x_W c) mem' md' k ->
  rbn_stem B G c (x_mem c) st -> rbn_stem B G c mem' st.
Proof.
intros c st own lyc Sc mem' md' k Hpre HOK HJ HST.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & F4 & _).
destruct Hpre as (Hafn & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hname & _ & _ & _ & Htok & _ & _ & _ & _ & Hdisp & _ & _ & _ & Hargs & _).
destruct Hafn as (HAR0 & _).
destruct (Hargs HOK) as (_ & Bn & Bt & Bd & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFPb : forall x, inFP (x_FP c) x ->
  exists q N, In (q, N) (ablocks B (x_ly c) (x_S c)) /\ q <= x < q + req_size N).
{ intros x Hx. apply rbn_fp_in in Hx.
  destruct Hx as [(_ & Hx) | [(_ & Hx) | (_ & Hx)]];
  [destruct Bn as (q & N & Hq & H1 & H2) | destruct Bt as (q & N & Hq & H1 & H2) | destruct Bd as (q & N & Hq & H1 & H2)];
  exists q, N; split; try exact Hq;
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR0 Hq) as (_ & _ & _ & _ & _ & _ & HN);
  pose proof (req_size_pos N ltac:(lia)) as (_ & HrN); lia. }
assert (HFPapp : forall x, inFP (x_FP c) x -> x < kLowShadowBeg \/ kHighShadowEnd <= x).
{ intros x Hx. destruct (HFPb x Hx) as (q & N & Hq & Hr).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR0 Hq) as (_ & _ & _ & Happ & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold kLowShadowBeg. lia. }
destruct HST as [(Hne & Hst & Hcs & cid & pos & Hin & Hlo & Hhi) | (Hnil & Himg)].
- left. split; [exact Hne|]. split; [exact Hst|].
  split; [| exists cid, pos; split; [exact Hin | split; [exact Hlo | exact Hhi]]].
  destruct (frame_al64 SEGS B _ _ _ _ _ cid pos HAR0 Hin) as (Hal & Hbal & Hb64).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR0 Hin) as (Hf0 & Hfc & _).
  assert (KF : forall x,
     (frame_addr (x_ly c) cid pos <= x < frame_addr (x_ly c) cid pos + fs_frame_bytes cid) \/
     (shadow_addr (frame_addr (x_ly c) cid pos) <= x <
        shadow_addr (frame_addr (x_ly c) cid pos) + fs_frame_bytes cid / 8) ->
     aview SEGS (w_H (x_W c)) mem' x = aview SEGS (w_H (x_W c)) (x_mem c) x).
  { intros x Hx. apply (F4 cid pos x Hin).
    - unfold in_zr, frame_rng. cbn [fst snd]. exact Hx.
    - intros HF. destruct Hx as [Hx | Hx].
      + destruct (HFPb x HF) as (q & N & Hq & Hr).
        pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ q N cid pos HAR0 Hq Hin) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
      + pose proof (HFPapp x HF) as Hxa.
        pose proof (shadow_addr_bounds (frame_addr (x_ly c) cid pos) ltac:(lia)) as S1.
        pose proof (shadow_range_end (frame_addr (x_ly c) cid pos) (fs_frame_bytes cid) ltac:(lia)) as S2.
        pose proof (shadow_addr_bounds (frame_addr (x_ly c) cid pos + fs_frame_bytes cid) ltac:(lia)) as S3.
        unfold kLowShadowBeg in Hxa. lia. }
  remember (frame_addr (x_ly c) cid pos) as f eqn:Ef. remember (fs_frame_bytes cid) as bs eqn:Eb.
  assert (Hal8 : f mod 8 = 0).
  { pose proof (Z.div_mod f 64 ltac:(lia)). replace f with ((8 * (f / 64)) * 8) by lia. apply Z_mod_mult. }
  assert (Hb8 : bs mod 8 = 0).
  { pose proof (Z.div_mod bs 64 ltac:(lia)). replace bs with ((8 * (bs / 64)) * 8) by lia. apply Z_mod_mult. }
  destruct Hcs as (Hfa & Hlen & Hpos & Hamr & Hg & Hra & Hhull & Htail).
  unfold rbn_cstr.
  split; [exact Hfa|]. split; [exact Hlen|]. split; [exact Hpos|]. split; [exact Hamr|].
  split.
  { apply (garr8_frame SEGS _ _ _ _ Hg). intros a Ha. apply (mbyte_of_aview SEGS). apply KF. left.
    rewrite length_app in Ha. cbn [length] in Ha. lia. }
  split.
  { intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    rewrite KF; [exact Hs|]. right. change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x).
    apply (rbe2c_fsh f bs x Hal8 Hb8). lia. }
  split.
  { intros s Hs. rewrite KF; [exact (Hhull s Hs)|]. right.
    assert (Hfb64 : (f + bs) mod 64 = 0) by (rewrite Z.add_mod, Hal, Hbal by lia; reflexivity).
    destruct (hull_inside f (f + bs) st (Z.of_nat (length (x_sd c)) + 1) s Hal Hfb64 ltac:(lia) Hlo ltac:(lia) ltac:(lia) Hs)
      as (g & Hg8 & Hgr & ->).
    apply (rbe2c_fsh f bs g Hal8 Hb8). lia. }
  { intros x Hx. rewrite KF; [exact (Htail x Hx)|]. left.
    pose proof (Z.mod_pos_bound (st + Z.of_nat (length (x_sd c))) 8 ltac:(lia)). lia. }
- right. split; [exact Hnil|].
  destruct Himg as (I1 & I2 & I3 & Ig & Iglob & Ifix & Itail).
  unfold rbn_imgstr. split; [exact I1|]. split; [exact I2|]. split; [exact I3|].
  split; [|split; [exact Iglob | split; [exact Ifix | exact Itail]]].
  apply (garr8_frame SEGS _ _ _ _ Ig). intros a Ha. apply (mbyte_of_aview SEGS).
  rewrite length_app in Ha. cbn [length] in Ha.
  destruct (Ifix a ltac:(lia)) as (Hi & Hno & Her).
  apply (F3 a Hi Hno Her). apply fp_spares_closed. apply rbn_fp_closed; lia.
Qed.
(* The state C1 from the facts of the run 0x82fc8 .. 0x82ffc (KR: only the stored bytes changed; the stored
   values) and of memset(s1 + 200, 0, 16) (KM, Heff), with the registers after the call. *)
Lemma rbe2c_post : forall c Sc st regs mem md msm mem2 md2 regs2,
  rbe_X2 c Sc st regs mem md ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] (x_ly c) Sc (x_W c) mem2 md2 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 c <= a < x_s1 c + 40) -> ~ (x_s1 c + 184 <= a < x_s1 c + 200) ->
     a <> x_FS c + 4 -> aview SEGS (w_H (x_W c)) msm a = aview SEGS (w_H (x_W c)) mem a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 c + 200 <= a < x_s1 c + 200 + 16) ->
     ~ (x_sp0 c + (x_s1 c - x_sp0 c) - ESTACK <= a < x_sp0 c + (x_s1 c - x_sp0 c)) ->
     aview SEGS (w_H (x_W c)) mem2 a = aview SEGS (w_H (x_W c)) msm a) ->
  (forall i, 0 <= i < 16 -> aview SEGS (w_H (x_W c)) mem2 (x_s1 c + 200 + i) = Some (0 mod 256)) ->
  val_mem SEGS (x_mem_at c msm) (x_s1 c + 0) 8 (x_display c) ->
  val_mem SEGS (x_mem_at c msm) (x_s1 c + 8) 8 (x_name c) ->
  val_mem SEGS (x_mem_at c msm) (x_s1 c + 16) 8 (x_token c) ->
  val_mem SEGS (x_mem_at c msm) (x_s1 c + 24) 8 (x_token_len c) ->
  val_mem SEGS (x_mem_at c msm) (x_s1 c + 32) 8 (x_display_len c) ->
  val_mem SEGS (x_mem_at c msm) (x_s1 c + 184) 8 (x_W4 c) ->
  val_mem SEGS (x_mem_at c msm) (x_s1 c + 192) 8 5 ->
  aview SEGS (w_H (x_W c)) msm (x_FS c + 4) = Some 5 ->
  getr regs2 2 = w64 (x_s1 c) -> getr regs2 3 = w64 (as_gp B) -> getr regs2 4 = w64 (as_tp B) ->
  getr regs2 8 = w64 (x_sp0 c) -> getr regs2 9 = w64 (x_s1 c) -> getr regs2 18 = w64 (x_FS c) ->
  getr regs2 19 = w64 (x_F c) -> getr regs2 23 = w64 (x_F c) -> getr regs2 22 = w64 SHADOW_OFF ->
  getr regs2 20 = w64 (x_W4 c) -> getr regs2 21 = w64 5 -> getr regs2 24 = w64 (x_name c) ->
  getr regs2 25 = w64 st -> getr regs2 26 = w64 (x_token_len c) ->
  rbn_C1 B G c st (x_ly c) Sc mem2 md2 regs2.
Proof.
intros c Sc st regs mem md msm mem2 md2 regs2 HX HJ2 KR KM Heff V0 V8 V16 V24 V32 V184 V192 VFS
  Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q23 Q22 Q20 Q21 Q24 Q25 Q26.
destruct HX as (HM & _ & HOK & _ & _ & H40 & H48 & HSTEM).
destruct HM as (Hpre & HJ & HBL & HSV & H56 & H80 & HFL & HSCO & HBK).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & HST & _).
pose proof HST as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (rbe2c_s1 c Hsp0al) as (Hs1 & _ & _).
assert (Hin3 : In (3, x_fpos c) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hin3) as (HF0 & HFc & HFapp).
change (frame_addr (x_ly c) 3 (x_fpos c)) with (x_F c) in HF0, HFc, HFapp.
assert (Hfb : fs_frame_bytes 3 = 512) by reflexivity. rewrite Hfb in HFc, HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as MF.
assert (HFS : x_FS c = SHADOW_OFF + x_F c / 8) by reflexivity.
assert (HSBv : SHADOW_OFF = 2147450880) by reflexivity.
assert (HZ : 2147450880 <= x_FS c /\ x_FS c + 64 <= x_s1 c - 4096 /\ x_F c + 512 <= x_s1 c - 4096 /\ 4096 <= x_F c /\
  (x_F c + 512 <= 2147450880 \/ x_FS c + 64 <= x_F c) /\ x_s1 c + 320 <= x_sp0 c /\ x_sp0 c <= 2 ^ 47 /\
  0 <= x_s1 c - 4096 /\ alloc_ceiling + 4096 <= x_s1 c /\ x_FS c + 64 <= 0x10007fff8000)
  by (clear - HFapp DF MF HFS HSBv C1 Hceil Hslo Hshi H47 Hs1 HFc HF0 Hes; lia).
clear DF MF HFapp.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 c - 4096 <= a < x_s1 c + 40) ->
  ~ (x_s1 c + 184 <= a < x_s1 c + 216) -> a <> x_FS c + 4 ->
  aview SEGS (w_H (x_W c)) mem2 a = aview SEGS (w_H (x_W c)) mem a).
{ intros a Ha H1 H2 H3. rewrite (KM a Ha ltac:(clear - H2; lia) ltac:(clear - H1 Hes; lia)).
  apply KR; [exact Ha | clear - H1; lia | clear - H2; lia | exact H3]. }
assert (KM' : forall a, x_s1 c <= a < x_s1 c + 200 -> 
  aview SEGS (w_H (x_W c)) mem2 a = aview SEGS (w_H (x_W c)) msm a).
{ intros a Ha. apply KM; clear - Ha HZ Hes; lia. }
unfold x_mem_at in *.
unfold rbn_C1, rbn_live, rbn_core.
split.
{ split.
  { split; [exact Hpre|]. split; [exact HJ2|]. split; [rewrite HBL; apply Permutation_refl|].
    split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q8|]. split; [exact Q9|].
    split; [exact Q18|]. split; [exact Q19|]. split; [exact Q23|].
    split.
    { unfold rbn_saved in *. apply Forall_forall. intros p Hp. pose proof (proj1 (Forall_forall _ _) HSV p Hp) as Hv.
      assert (Hoff : 8 <= fst p <= 104)
        by (unfold rbn_saved_regs in Hp; repeat (destruct Hp as [<- | Hp]; [cbn [fst]; lia|]); destruct Hp).
      unfold x_mem_at in Hv. eapply val_mem_kept; [|exact Hv]. intros k Hk. cbn in Hk.
      apply KEEP; clear - Hk Hoff HZ; lia. }
    erewrite rdword_ext; [exact HFL|]. intros k Hk. apply KEEP; clear - Hk HZ HSBv HFS; lia. }
  split; [exact HOK|].
  split.
  { intros a HaF Hab. rewrite <- (HBK a HaF Hab). destruct Hab as (q & N & Hq & Hr).
    rewrite <- HBL in Hq. destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR Hq) as (_ & H4096 & Hce & Happ & _ & _ & HN).
    pose proof (req_size_pos N ltac:(lia)) as (_ & HrN).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
    apply KEEP; clear - Hr H4096 Hce Happ HN HrN HZ HSBv HFS C1 C2 C3; lia. }
  split.
  { unfold rbn_slots. cbv zeta. unfold x_mem_at in *. rewrite Z.add_0_r in V0.
    split. { eapply val_mem_kept; [|exact V0]. intros k Hk. cbn in Hk. apply KM'. lia. }
    split. { eapply val_mem_kept; [|exact V8]. intros k Hk. cbn in Hk. apply KM'. lia. }
    split. { eapply val_mem_kept; [|exact V16]. intros k Hk. cbn in Hk. apply KM'. lia. }
    split. { eapply val_mem_kept; [|exact V24]. intros k Hk. cbn in Hk. apply KM'. lia. }
    split. { eapply val_mem_kept; [|exact V32]. intros k Hk. cbn in Hk. apply KM'. lia. }
    split. { eapply val_mem_kept; [|exact H40]. intros k Hk. cbn in Hk. apply KEEP; clear - Hk HZ; lia. }
    split. { eapply val_mem_kept; [|exact H48]. intros k Hk. cbn in Hk. apply KEEP; clear - Hk HZ; lia. }
    split. { eapply val_mem_kept; [|exact H56]. intros k Hk. cbn in Hk. apply KEEP; clear - Hk HZ; lia. }
    { eapply val_mem_kept; [|exact H80]. intros k Hk. cbn in Hk. apply KEEP; clear - Hk HZ; lia. } }
  exact Q22. }
split; [exact (rbe2c_stem c st [(3, x_fpos c)] (x_ly c) Sc mem2 md2 0 Hpre HOK HJ2 HSTEM)|].
split; [exact Q20|]. split; [exact Q21|]. split; [exact Q24|]. split; [exact Q25|]. split; [exact Q26|].
split.
{ unfold rbn_scope in *. cbv zeta in *. destruct HSCO as (S4 & S8 & S16 & S24).
  split; [rewrite (KM (x_FS c + 4) ltac:(clear - HZ; lia) ltac:(clear - HZ; lia) ltac:(clear - HZ Hes; lia)); exact VFS|].
  split; [intros j Hj; rewrite (KEEP (x_FS c + j) ltac:(clear - Hj HZ; lia) ltac:(clear - Hj HZ; lia)
            ltac:(clear - Hj HZ; lia) ltac:(clear - Hj; lia)); exact (S8 j Hj)|].
  split; [intros j Hj; rewrite (KEEP (x_FS c + j) ltac:(clear - Hj HZ; lia) ltac:(clear - Hj HZ; lia)
            ltac:(clear - Hj HZ; lia) ltac:(clear - Hj; lia)); exact (S16 j Hj)|].
  intros j Hj; rewrite (KEEP (x_FS c + j) ltac:(clear - Hj HZ; lia) ltac:(clear - Hj HZ; lia)
            ltac:(clear - Hj HZ; lia) ltac:(clear - Hj; lia)); exact (S24 j Hj). }
unfold rbn_sb, x_wb. cbv zeta. unfold x_mem_at in *.
split. { eapply val_mem_kept; [|exact V184]. intros k Hk. cbn in Hk. apply KM'. lia. }
split. { replace (x_s1 c + 184 + 8) with (x_s1 c + 192) by lia.
         eapply val_mem_kept; [|exact V192]. intros k Hk. cbn in Hk. apply KM'. lia. }
split. { cbn [length Z.of_nat]. replace (x_s1 c + 184 + 16) with (x_s1 c + 200) by lia.
         apply val_mem_zero8. intros i Hi. rewrite (Heff i ltac:(lia)). reflexivity. }
split. { replace (x_s1 c + 184 + 24) with (x_s1 c + 200 + 8) by lia. apply rbe2c_zero4. intros i Hi.
         replace (x_s1 c + 200 + 8 + i) with (x_s1 c + 200 + (8 + i)) by lia.
         rewrite (Heff (8 + i) ltac:(lia)). reflexivity. }
split; [left; reflexivity|]. split; [cbn; lia|]. split; [constructor|]. apply garr8_nil.
Qed.
Definition rbe2c_rw1 : YP09.region := YP09.mkRegion (Some 9%nat) 0 40 0 40 [].
Definition rbe2c_rw2 : YP09.region := YP09.mkRegion (Some 9%nat) 184 200 184 200 [].
Definition rbe2c_rfs : YP09.region := YP09.mkRegion (Some 18%nat) 4 5 4 5 [].
Definition rbe2c_ss : sstate :=
  mkSS (AF_reac_box_name + 0x254) sr_atoms [rbe2c_rw1; rbe2c_rw2; rbe2c_rfs] None (mkFacts [] [] []).
Lemma rbe_e2c : forall c Sc st regs mem md, rbe_X2 c Sc st regs mem md ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_name + 0x254)) mem (seg_rom SEGS)) md)
    (fun W' c' => W' = x_W c /\ exists Sc' regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x28c)) mem' (seg_rom SEGS)) md' /\
       rbn_C1 B G c st (x_ly c) Sc' mem' md' regs').
Proof.
intros c Sc st regs mem md HX.
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HX as (HM & HR & HOK & G14 & G25 & H40 & H48 & HSTEM).
pose proof HM as (Hpre & HJ & HBL & HSV & H56 & H80 & HFL & HSCO & HBK).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & R22 & R15 & R21 & R24 & R26).
pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hname & _ & _ & _ & Htok & _ & Htl & _ & _ & Hdisp & _ & Hdl & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & HST & _).
pose proof HST as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
destruct (rbe2c_s1 c Hsp0al) as (Hs1 & Hs1al & Hs1o).
assert (Hin3 : In (3, x_fpos c) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hin3) as (HF0 & HFc & HFapp).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & _ & _ & Hsh).
change (frame_addr (x_ly c) 3 (x_fpos c)) with (x_F c) in HF0, HFc, HFapp, Hsh.
assert (Hfb : fs_frame_bytes 3 = 512) by reflexivity. rewrite Hfb in HFc, HFapp, Hsh.
change (shadow_addr (x_F c)) with (x_FS c) in Hsh.
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as MF.
assert (HFS : x_FS c = SHADOW_OFF + x_F c / 8) by reflexivity.
assert (HSBv : SHADOW_OFF = 2147450880) by reflexivity.
assert (HZ : 2147450880 <= x_FS c /\ x_FS c + 64 <= x_s1 c - 4096 /\ x_s1 c + 320 <= x_sp0 c /\
   x_sp0 c - (336 + 2 * ESTACK) <= x_s1 c /\ 2 ^ 46 <= x_s1 c /\ x_sp0 c <= 2 ^ 47 /\ kHighMemBeg <= x_s1 c /\
   ly_stk_lo (x_ly c) + 8192 <= x_s1 c /\ x_sp0 c <= ly_stk_hi (x_ly c) /\ 0 <= ly_stk_lo (x_ly c))
  by (clear - DF MF HFS HSBv C1 C3 Hceil Hslo Hshi H47 Hs1 HFc HF0 Hes; lia).
clear DF MF.
assert (Hs1_8 : (x_s1 c + 200) mod 8 = 0).
{ pose proof (Z.div_mod (x_s1 c) 32 ltac:(lia)) as D. rewrite Hs1al, Z.add_0_r in D.
  replace (x_s1 c + 200) with ((4 * (x_s1 c / 32) + 25) * 8) by (clear - D; lia). apply Z_mod_mult. }
(* the environment: atom r = register r *)
remember (Eimg (Ereg regs (@nil word))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER : regs_ok E sr_atoms regs) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (E2 : ew E 2 = Z_to_bv 64 (x_s1 c)) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact R3).
assert (E4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact R4).
assert (E8 : ew E 8 = Z_to_bv 64 (x_sp0 c)) by (rewrite (EE 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 (x_s1 c)) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E14 : ew E 14 = Z_to_bv 64 (x_display c)) by (rewrite (EE 14%nat 14%bv eq_refl); exact G14).
assert (E15 : ew E 15 = Z_to_bv 64 (x_display_len c)) by (rewrite (EE 15%nat 15%bv eq_refl); exact R15).
assert (E18 : ew E 18 = Z_to_bv 64 (x_FS c)) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 (x_F c)) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E21 : ew E 21 = Z_to_bv 64 (x_token c)) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E23 : ew E 23 = Z_to_bv 64 (x_F c)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = Z_to_bv 64 (x_name c)) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = Z_to_bv 64 st) by (rewrite (EE 25%nat 25%bv eq_refl); exact G25).
assert (E26 : ew E 26 = Z_to_bv 64 (x_token_len c)) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
clear HE EE.
assert (Hb9 : bv_unsigned (ew E 9) = x_s1 c) by (rewrite E9; apply unsigned_lit_small; clear - HZ; lia).
assert (Hb18 : bv_unsigned (ew E 18) = x_FS c) by (rewrite E18; apply unsigned_lit_small; clear - HZ; lia).
assert (HS : st_ok_pi SEGS VAL E rbe2c_ss
  (restrict (w_H (x_W c)) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x254))) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rbe2c_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - unfold rbe2c_rw1, rbe2c_rw2, rbe2c_rfs.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?Hb9, ?Hb18.
    + split; [clear - HZ; lia|]. split; [clear - HZ; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. clear - Ho HZ; lia.
    + split; [clear - HZ; lia|]. split; [clear - HZ; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. clear - Ho HZ; lia.
    + split; [clear - HZ; lia|]. split; [clear - HZ; lia|]. split; [|constructor].
      intros o Ho. replace o with 4 by (clear - Ho; lia). apply (apresent_writable SEGS).
      exact (proj1 (Hsh 4 ltac:(split; [clear; lia | reflexivity]))).
  - unfold rbe2c_rw1, rbe2c_rw2, rbe2c_rfs.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?Hb9, ?Hb18.
    repeat split; try exact I; clear - HZ; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
rewrite <- (Z.add_assoc BASE AF_reac_box_name 0x254).
paj_run_shc RUNP RUNC HS HJ.
{ unfold rbe2c_ss. cbn [ss_mem].
  apply (awr_ok_cons_gen E rbe2c_rw1 _ _ _ _ _ _ _ _ 9%nat (x_s1 c) eq_refl Hb9).
  { intros a Ha. unfold rbe2c_rw1 in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. clear - Ha HZ Hes; lia. }
  apply (awr_ok_cons_gen E rbe2c_rw2 _ _ _ _ _ _ _ _ 9%nat (x_s1 c) eq_refl Hb9).
  { intros a Ha. unfold rbe2c_rw2 in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. clear - Ha HZ Hes; lia. }
  apply (awr_ok_cons_gen E rbe2c_rfs _ _ _ _ _ _ _ _ 18%nat (x_FS c) eq_refl Hb18).
  { intros a Ha. unfold rbe2c_rfs in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right.
    exists 3, (x_fpos c). split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    change (shadow_addr (frame_addr (x_ly c) 3 (x_fpos c))) with (x_FS c). rewrite Hfb.
    change (512 / 8) with 64. clear - Ha; lia. }
  apply awr_ok_nil. }
(* at the call of memset (0x82ffc) *)
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (8%bv : bv 5) Rs0. prreg HS (9%bv : bv 5) Rs1. prreg HS (18%bv : bv 5) Rs2. prreg HS (19%bv : bv 5) Rs3.
prreg HS (20%bv : bv 5) Rs4. prreg HS (21%bv : bv 5) Rs5. prreg HS (22%bv : bv 5) Rs6. prreg HS (23%bv : bv 5) Rs7.
prreg HS (24%bv : bv 5) Rs8. prreg HS (25%bv : bv 5) Rs9. prreg HS (26%bv : bv 5) Rs10.
pose proof (st_ok_region_nth E _ _ 0%nat _ HS eq_refl) as RG0.
pose proof (st_ok_region_nth E _ _ 1%nat _ HS eq_refl) as RG1.
pose proof (st_ok_region_nth E _ _ 2%nat _ HS eq_refl) as RG2.
cbn [ms_mem restrict] in RG0, RG1, RG2.
assert (V0 : val_mem SEGS (x_mem_at c (ms_mem ms)) (x_s1 c + 0) 8 (x_display c)).
{ eapply (field_of_region E _ 9%nat (x_s1 c) _ _ _ _ _ 0 8%N (SOff 14 0) (x_display c) RG0 Hb9).
  - repeat (first [left; reflexivity | right]).
  - cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E14.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). clear - Hdisp; lia.
  - clear; lia. }
assert (V8 : val_mem SEGS (x_mem_at c (ms_mem ms)) (x_s1 c + 8) 8 (x_name c)).
{ eapply (field_of_region E _ 9%nat (x_s1 c) _ _ _ _ _ 8 8%N (SOff 24 0) (x_name c) RG0 Hb9).
  - repeat (first [left; reflexivity | right]).
  - cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E24.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). clear - Hname; lia.
  - clear; lia. }
assert (V16 : val_mem SEGS (x_mem_at c (ms_mem ms)) (x_s1 c + 16) 8 (x_token c)).
{ eapply (field_of_region E _ 9%nat (x_s1 c) _ _ _ _ _ 16 8%N (SOff 21 0) (x_token c) RG0 Hb9).
  - repeat (first [left; reflexivity | right]).
  - cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E21.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). clear - Htok; lia.
  - clear; lia. }
assert (V24 : val_mem SEGS (x_mem_at c (ms_mem ms)) (x_s1 c + 24) 8 (x_token_len c)).
{ eapply (field_of_region E _ 9%nat (x_s1 c) _ _ _ _ _ 24 8%N (SOff 26 0) (x_token_len c) RG0 Hb9).
  - repeat (first [left; reflexivity | right]).
  - cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E26.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). clear - Htl; lia.
  - clear; lia. }
assert (V32 : val_mem SEGS (x_mem_at c (ms_mem ms)) (x_s1 c + 32) 8 (x_display_len c)).
{ eapply (field_of_region E _ 9%nat (x_s1 c) _ _ _ _ _ 32 8%N (SOff 15 0) (x_display_len c) RG0 Hb9).
  - repeat (first [left; reflexivity | right]).
  - cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E15.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). clear - Hdl; lia.
  - clear; lia. }
assert (V184 : val_mem SEGS (x_mem_at c (ms_mem ms)) (x_s1 c + 184) 8 (x_W4 c)).
{ eapply (field_of_region E _ 9%nat (x_s1 c) _ _ _ _ _ 184 8%N (SOff 19 32) (x_W4 c) RG1 Hb9).
  - repeat (first [left; reflexivity | right]).
  - cbn [sv_denot]. rewrite E19, unsigned_lit_small by (clear - HF0 HFc C1; lia). reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold x_W4. clear - HF0 HFc C1; lia.
  - clear; lia. }
assert (V192 : val_mem SEGS (x_mem_at c (ms_mem ms)) (x_s1 c + 192) 8 5).
{ eapply (field_of_region E _ 9%nat (x_s1 c) _ _ _ _ _ 192 8%N (SLit 5) 5 RG1 Hb9).
  - repeat (first [left; reflexivity | right]).
  - reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). clear; lia.
  - clear; lia. }
assert (VFS1 : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem ms)) (x_FS c + 4) 1 5).
{ eapply (field_of_region E _ 18%nat (x_FS c) _ _ _ _ _ 4 1%N (SLit 5) 5 RG2 Hb18).
  - left; reflexivity.
  - reflexivity.
  - change (2 ^ (8 * Z.of_N 1)) with 256. clear; lia.
  - clear; lia. }
assert (VFS : aview SEGS (w_H (x_W c)) (ms_mem ms) (x_FS c + 4) = Some 5)
  by (apply (aview_of_val_mem1 SEGS); [exact VFS1 | clear; lia]).
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 c <= a < x_s1 c + 40) -> ~ (x_s1 c + 184 <= a < x_s1 c + 200) ->
  a <> x_FS c + 4 -> aview SEGS (w_H (x_W c)) (ms_mem ms) a = aview SEGS (w_H (x_W c)) mem a).
{ intros a Ha H1 H2 H3.
  apply (kept_of_frame E (ss_mem rbe2c_ss) (w_H (x_W c)) mem (ms_mem ms)
    (fun x => (x_s1 c <= x < x_s1 c + 40) \/ (x_s1 c + 184 <= x < x_s1 c + 200) \/ x = x_FS c + 4) HFr).
  - intros bb wlo whi aa Hin Hr. unfold rbe2c_ss, rbe2c_rw1, rbe2c_rw2, rbe2c_rfs in Hin.
    cbn [ss_mem windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
    destruct Hin as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <- <-; cbn [base_val] in Hr;
    rewrite ?Hb9, ?Hb18 in Hr; clear - Hr; lia.
  - exact Ha.
  - clear - H1 H2 H3. tauto. }
assert (HSTK : range_addressable (aview SEGS (w_H (x_W c)) (ms_mem ms)) SHADOW_OFF (x_s1 c + 200) 16 /\
               shadow_hull_vis (aview SEGS (w_H (x_W c)) (ms_mem ms)) (x_s1 c + 200) 16).
{ pose proof HJ as (HAR1 & _).
  pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR1))) as (_ & _ & _ & _ & Hpal & Hpah & _).
  pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo (x_ly c), ly_stk_hi (x_ly c) - ly_stk_lo (x_ly c))
    HAR1 ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
  apply (rbe2c_stk_shadow _ _ _ _ _ Hz Hpal Hpah); [clear - HZ; lia | clear - HZ; lia | clear - HZ; lia
    | exact Hs1_8 | reflexivity | clear; lia]. }
pmkst HS.
eapply SRr_mono.
{ eapply (aj_intrin_atS SEGS B LAWS Hsegs OSet (SIGMA IB___asan_memset) AMEMSET (x_W c) (ms_regs ms) (ms_mem ms)
    (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)] (x_ly c) Sc _ 0
    (x_s1 c + 200) 0 16 (x_s1 c - x_sp0 c) (Z_to_bv 64 (BASE + AF_reac_box_name + 0x28c)) HJ).
  - rewrite Ra0, Hb9. reflexivity.
  - rewrite Ra1. reflexivity.
  - rewrite Ra2. reflexivity.
  - clear; lia.
  - clear - HZ; lia.
  - clear - HZ; lia.
  - unfold spZ. rewrite Rsp, E2, unsigned_lit_small by (clear - HZ; lia). clear; lia.
  - exact Hs1o.
  - clear - HZ; lia.
  - clear - Hs1 Hes; lia.
  - rewrite Rgp. exact E3.
  - rewrite Rtp. exact E4.
  - rewrite Rra. f_equal. rewrite <- Z.add_assoc. reflexivity.
  - rewrite <- Z.add_assoc. apply ret_ok_codeptr_v; [unfold AF_reac_box_name; clear; lia | reflexivity].
  - intros a Ha. split; [left; clear - Ha HZ Hes; lia | clear - Ha HZ Hes; lia].
  - unfold amem_range. right. clear - HZ C3 C4; lia.
  - exact (proj1 HSTK).
  - intros _. exact (proj2 HSTK).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & _ & Heff & Hfr2 & _ & _).
split; [reflexivity|]. exists Sc, regs2, mem2, md2. split; [reflexivity|].
apply (rbe2c_post c Sc st regs mem md (ms_mem ms) mem2 md2 regs2 HX HJ2 KR Hfr2 Heff V0 V8 V16 V24 V32 V184 V192 VFS).
- transitivity (getr (ms_regs ms) 2%bv); [exact (HP 2 ltac:(unfold acallee_saved; clear; lia)) | rewrite Rsp; exact E2].
- transitivity (getr (ms_regs ms) 3%bv); [exact (HP 3 ltac:(unfold acallee_saved; clear; lia)) | rewrite Rgp; exact E3].
- transitivity (getr (ms_regs ms) 4%bv); [exact (HP 4 ltac:(unfold acallee_saved; clear; lia)) | rewrite Rtp; exact E4].
- transitivity (getr (ms_regs ms) 8%bv); [exact (HP 8 ltac:(unfold acallee_saved; clear; lia)) | rewrite Rs0; exact E8].
- transitivity (getr (ms_regs ms) 9%bv); [exact (HP 9 ltac:(unfold acallee_saved; clear; lia)) | rewrite Rs1; exact E9].
- transitivity (getr (ms_regs ms) 18%bv); [exact (HP 18 ltac:(unfold acallee_saved; clear; lia)) | rewrite Rs2; exact E18].
- transitivity (getr (ms_regs ms) 19%bv); [exact (HP 19 ltac:(unfold acallee_saved; clear; lia)) | rewrite Rs3; exact E19].
- transitivity (getr (ms_regs ms) 23%bv); [exact (HP 23 ltac:(unfold acallee_saved; clear; lia)) | rewrite Rs7; exact E23].
- transitivity (getr (ms_regs ms) 22%bv); [exact (HP 22 ltac:(unfold acallee_saved; clear; lia)) | rewrite Rs6; exact E22].
- transitivity (getr (ms_regs ms) 20%bv); [exact (HP 20 ltac:(unfold acallee_saved; clear; lia)) | rewrite Rs4].
  rewrite E19, unsigned_lit_small by (clear - HF0 HFc C1; lia). reflexivity.
- transitivity (getr (ms_regs ms) 21%bv); [exact (HP 21 ltac:(unfold acallee_saved; clear; lia)) | rewrite Rs5; reflexivity].
- transitivity (getr (ms_regs ms) 24%bv); [exact (HP 24 ltac:(unfold acallee_saved; clear; lia)) | rewrite Rs8; exact E24].
- transitivity (getr (ms_regs ms) 25%bv); [exact (HP 25 ltac:(unfold acallee_saved; clear; lia)) | rewrite Rs9; exact E25].
- transitivity (getr (ms_regs ms) 26%bv); [exact (HP 26 ltac:(unfold acallee_saved; clear; lia)) | rewrite Rs10; exact E26].
Qed.
Lemma rbn_seg_entry : forall c, rbn_pre B G c ->
  SRr SEGS (x_W c) (cfg_at SEGS (BASE + AF_reac_box_name) (x_regs c) (x_mem c) (x_md c))
    (fun W' c' => W' = x_W c /\ exists fpos st lyc Sc regs' mem' md',
       (c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x28c)) mem' (seg_rom SEGS)) md' /\
        rbn_C1 B G (x_setpos c fpos) st lyc Sc mem' md' regs') \/
       (c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x738)) mem' (seg_rom SEGS)) md' /\
        rbn_R B G (x_setpos c fpos) lyc Sc mem' md' regs')).
Proof.
intros c Hpre.
eapply SRr_bind; [exact (rbe_e1 c Hpre)|].
intros W1 c1 _ (-> & fpos & Sc1 & regs1 & mem1 & md1 & -> & HX1).
eapply SRr_bind; [exact (rbe_e2a (x_setpos c fpos) Sc1 regs1 mem1 md1 HX1)|].
intros W2 c2 _ (-> & Sc2 & regs2 & mem2 & md2 & [(-> & HR) | (-> & HX2a)]).
- apply SRr_ret. split; [reflexivity|]. exists fpos, 0, (x_ly c), Sc2, regs2, mem2, md2. right. split; [reflexivity | exact HR].
- eapply SRr_bind; [exact (rbe_e2b (x_setpos c fpos) Sc2 regs2 mem2 md2 HX2a)|].
  intros W3 c3 _ (-> & st & Sc3 & regs3 & mem3 & md3 & -> & HX2).
  eapply SRr_mono; [exact (rbe_e2c (x_setpos c fpos) Sc3 st regs3 mem3 md3 HX2)|].
  intros W4 c4 _ (-> & Sc4 & regs4 & mem4 & md4 & -> & HC1).
  split; [reflexivity|]. exists fpos, st, (x_ly c), Sc4, regs4, mem4, md4. left. split; [reflexivity | exact HC1].
Qed.

End walk.
End h.
End f.
End d.
