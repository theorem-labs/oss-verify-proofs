(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 DecTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCState BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0 CmpFsKit0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCFactsFs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCFactsBs BzCLemmasMs CmpCutMS CmpMsKit CmpMsKit2 S0_cmp_fsZ.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs6.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas8.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Strategy 1000 [find_orig fallbackSort blockSort mainSort].
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section BSP.
  Variables (cx : cctx) (g : eg) (e : est).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) (sv : word).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis IMG : cctx_img S0C cx.
  Hypothesis NB : (1 <= e_nblock e <= NBLOCKMAX + 9)%Z.
  Hypothesis STK : (lo + BS_STACK <= bv_unsigned sp)%Z. Hypothesis LO : (CEIL <= lo)%Z. Hypothesis AL : (bv_unsigned sp mod 16 = 0)%Z.
  Notation usp := (bv_unsigned sp). Notation p := (bv_unsigned sp - 5008)%Z.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation FT := (c_FT cx). Notation n := (e_nblock e).
  Notation W5 := [(E + 48, E + 52); (A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 4 * 65537); (usp - 8192, usp)]%Z.
  Notation POST := (blockSort_post2 s0segs cx g e ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (blockSort_W cx usp) m).

  Ltac prep :=
    let IA1 := ident:(IA1) in let IA2 := ident:(IA2) in let IFT := ident:(IFT) in pose proof CX as CX'; unfold cctx_ok in CX'; cbv zeta in CX';
    cps_destruct CX' as (RE & RE' & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LJ & _);
    pose proof SEP as SEP'; unfold cctx_sep, apart in SEP'; cbv zeta in SEP';
    cps_destruct SEP' as (SE1 & SE2 & SEF & _ & _ & AP12 & AP1F & _ & _ & AP2F & _);
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof IMG as IMG'; unfold cctx_img, img_apart, IMG_LO3, IMG_HI3 in IMG'; cbn [ci_hi S0C] in IMG';
    cps_destruct IMG' as (IE & IA1 & IA2 & IFT & _);
    bz_ceil; bz_params; unfold FTAB_WORDS, ESTATE_SIZE, BS_STACK, CEIL in *;
    (destruct IA1 as [IA1|IA1]; [exfalso; lia|]); (destruct IA2 as [IA2|IA2]; [exfalso; lia|]); (destruct IFT as [IFT|IFT]; [exfalso; lia|]).
  Local Ltac nt := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => notrap | _ => idtac end.

  (* [comment removed for export] *)
  Lemma S0_forig : forall (Q : machine_state -> Prop) (cnt : nat) (i : Z) (a1f : zarr)
      (x0 x4 x5 x6 x7 x8 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word) (m1 : word -> option byte),
    Z.of_nat cnt = (n - i)%Z -> (0 <= i < n)%Z -> zbok a1f ->
    (exists k, i <= k < n /\ rd32 a1f k = 0)%Z ->
    u8arr s0segs m1 A1 (zb8 a1f ARR1_SIZE) ->
    (forall (k : Z) (y15 : word), (i <= k < n)%Z -> rd32 a1f k = 0%Z -> find_orig (Z.to_nat (n - i)) a1f i = k ->
      evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                            (Z_to_bv 64 (n - k)) (Z_to_bv 64 k) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (A1 + 4 * k)) (Z_to_bv 64 (A1 + 4 * k)) y15 x16
                            (Z_to_bv 64 A1) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                       F (Z_to_bv 64 0x22194) fc None m1 (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                          (Z_to_bv 64 (n - i)) (Z_to_bv 64 i) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (A1 + 4 * i)) (Z_to_bv 64 (A1 + 4 * i)) x15 x16
                          (Z_to_bv 64 A1) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x2215c) fc None m1 (seg_rom s0segs)).
  Proof.
    intros Q. induction cnt as [|cnt IH]; [intros; exfalso; lia|].
    intros i a1f x0 x4 x5 x6 x7 x8 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 m1 Hcnt Hi OK1 EX AR1 K.
    prep. pose proof (zb8_length a1f ARR1_SIZE ltac:(lia)) as L1. pose proof (zbok_rd32 a1f i OK1) as Bw.
    replace (Z.to_nat (n - i)) with (S (Z.to_nat (n - (i + 1)))) in K by lia. cbn [find_orig] in K.
    wstep. flags. wstep. nt. wstep. nt. wstep. nt.
    (* [comment removed for export] *)
    pose proof (zb8_read4 s0segs m1 A1 a1f ARR1_SIZE i _ AR1 ltac:(lia) ltac:(lia) OK1 ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD.
    wstep; if_cases Kb; zify_cond_z Kb.
    - (* [comment removed for export] *)
      assert (Z0 : rd32 a1f i = 0%Z) by (first [lia | apply (proj1 (sx32_zero_iff _ Bw)) in Kb; lia]).
      rewrite Z0, Z.eqb_refl in K.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K i _ ltac:(lia) Z0 eq_refl) end; [st_eq].
    - assert (Zn : rd32 a1f i <> 0%Z) by (first [lia | intros Z0; apply Kb; apply (proj2 (sx32_zero_iff _ Bw)); exact Z0]).
      replace (rd32 a1f i =? 0)%Z with false in K by (symmetry; apply Z.eqb_neq; exact Zn).
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep.
      wstep; if_cases Kc; zify_cond_z Kc.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          enter_with (IH (i + 1)%Z a1f x0 x4 x5 x6 x7 x8 _ x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 mm) end;
          [st_eq| lia| lia| exact OK1| | exact AR1| ].
        { cps_destruct EX as (k & Hk & Zk). exists k. split; [| exact Zk]. destruct (Z.eq_dec k i); [subst k; exfalso; exact (Zn Zk)| lia]. }
        intros k y15 Hk Zk FO. enter_with (K k y15 ltac:(lia) Zk FO); [st_eq].
      + exfalso. cps_destruct EX as (k & Hk & Zk). destruct (Z.eq_dec k i); [subst k; exact (Zn Zk)| lia].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_bs_find : forall (a1f a2f ftf : zarr)
      (x0 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word) (m1 : word -> option byte),
    zbok a1f -> (exists k, 0 <= k < n /\ rd32 a1f k = 0)%Z ->
    fst (fst (fst (blockSort e znew))) = est_sorted e a1f a2f ftf ->
    rw_cells s0segs m1 E (EHEAD1 cx g e) -> rw_cells s0segs m1 (E + 640) (EHEAD2 cx g e) ->
    u8arr s0segs m1 A1 (zb8 a1f ARR1_SIZE) -> u8arr s0segs m1 A2 (zb8 a2f ARR2_SIZE) -> u32arr s0segs m1 FT (zw32 ftf FTAB_WORDS) ->
    rw_cells s0segs m1 (p + 4904) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk s0segs m1 lo (p + 4904) -> mem_inv s0segs m1 -> munch W5 m m1 -> wmono s0segs m m1 ->
    evt s0segs POST (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 (Z_to_bv 64 E) x9 x10 x11 x12 x13 x14 x15 x16
                              (Z_to_bv 64 A1) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                         F (Z_to_bv 64 0x22130) fc None m1 (seg_rom s0segs)).
  Proof.
    intros a1f a2f ftf
           x0 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 m1
           OK1 EX EE EH1 EH2 AR1 AR2 FTB SAV ST MI MU WM.
    prep. unfold EHEAD1 in EH1.
    pose proof (zb8_length a1f ARR1_SIZE ltac:(lia)) as L1.
    pose proof CX as CXa; unfold cctx_ok in CXa; cbv zeta in CXa; cps_destruct CXa as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A1M & _).
    (* [comment removed for export] *)
    wstep.
    wstep. wstep.
    wstep; if_cases Kz; [apply blez_taken in Kz; [exfalso; lia| lia] | clear Kz].
    assert (A1L : Z.land A1 3 = 0%Z) by (change 3%Z with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2)%Z with 4%Z; Z.div_mod_to_equations; lia).
    wstep. wstep. flags. wstep. rewrite ?A1L. flags. wstep. flags. wstep. flags. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (S0_forig POST (Z.to_nat n) 0%Z a1f x0 x4 x5 x6 x7 _ x15 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 mm) end;
      [st_eq| lia| lia| exact OK1| exact EX| exact AR1|].
    intros k y15 Hk Zk FO. replace (n - 0)%Z with n in FO by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep. do 13 wstep. wstep.
    replace (Z_to_bv 64 (p + 5008)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
    wstep.
    (* [comment removed for export] *)
    pose proof (stk_of_rw_cells s0segs _ _ _ SAV) as K7. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in K7. stk_add ST K7.
    lazymatch type of ST with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in ST by lia end.
    (* [comment removed for export] *)
    apply evt_done. unfold blockSort_post2. cbv zeta. rewrite EE. unfold est_sorted, EHEAD1, EHEAD2, amem.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack g_aie g_sort g_mtf g_bs g_zbits].
    rewrite FO. unfold EHEAD2 in EH2. unfold blockSort_W, FTAB_WORDS, BS_STACK.
    do 16 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact EH1|]. split; [exact EH2|]. split; [exact AR1|]. split; [exact AR2| exact FTB].
  Time Qed.

  (* [comment removed for export] *)
  Notation FBW := [(A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 4 * 65537); (p - 3072, p)]%Z.
  Lemma S0_bs_fbcall : forall (Q : machine_state -> Prop) (a1 a2 ft : zarr)
      (x0 x4 x5 x6 x7 x8 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word) (m1 : word -> option byte),
    zbok a1 -> zbok a2 -> (forall i, 0 <= zget ft i < 4294967296)%Z -> fs_facts a1 a2 ft n ->
    rw_cells s0segs m1 E (EHEAD1 cx g e) ->
    u8arr s0segs m1 A1 (zb8 a1 ARR1_SIZE) -> u8arr s0segs m1 A2 (zb8 a2 ARR2_SIZE) -> u32arr s0segs m1 FT (zw32 ft FTAB_WORDS) ->
    cimg_mem S0C m1 sv -> mem_inv s0segs m1 -> stk s0segs m1 lo p -> munch W5 m m1 -> wmono s0segs m m1 ->
    (forall (m2 : word -> option byte) (t0 t1 t2 a0 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      let r := fallbackSort a1 a2 ft znew znew znew znew n in
      rw_cells s0segs m2 E (EHEAD1 cx g e) ->
      u8arr s0segs m2 A1 (zb8 (fr_fm r) ARR1_SIZE) -> u8arr s0segs m2 A2 (zb8 (fr_ec r) ARR2_SIZE) -> u32arr s0segs m2 FT (zw32 (fr_bh r) FTAB_WORDS) ->
      cimg_mem S0C m2 sv -> mem_inv s0segs m2 -> stk s0segs m2 lo p -> munch W5 m m2 -> wmono s0segs m m2 ->
      munch FBW m1 m2 -> wmono s0segs m1 m2 ->
      evt s0segs Q (MS (mkR (Z_to_bv 64 0x20414) (Z_to_bv 64 p) gp tp t0 t1 t2 x7 x8
                            a0 a1' a2' a3 a4 a5 a6 a7
                            x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x20414) fc None m2 (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 x7 x8
                          (Z_to_bv 64 A1) (Z_to_bv 64 A2) (Z_to_bv 64 FT) (Z_to_bv 64 n) (Z_to_bv 64 0) x14 x15 x16
                          x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x20410) fc None m1 (seg_rom s0segs)).
  Proof.
    intros Q a1 a2 ft x0 x4 x5 x6 x7 x8 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 m1
           OK1 OK2 FTW FSF EH1 AR1 AR2 FTB CM MI ST MU WM K.
    prep. unfold EHEAD1 in EH1.
    cps_destruct CM as (CM1 & CM2 & CM3 & CM4). cbn [ci_segs ci_got ci_stderrp ci_crc ci_crcx S0C] in CM1, CM2, CM3, CM4.
    (* [comment removed for export] *)
    wstep.
    pose proof S0_fallbackSort as FS. unfold fallbackSort_spec in FS. cbv zeta in FS. cbn [ci_segs ci_fallbackSort S0C] in FS.
    eapply evt_cut.
    { eapply (FS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 cx (est_sorted e a1 a2 ft) n lo sv);
        cbn [e_arr1 e_arr2 e_ftab est_sorted];
        [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact AR1| exact AR2| exact FTB
        | split; [exact CM1| split; [exact CM2| split; [exact CM3| exact CM4]]]
        | exact MI| | | exact LO| | exact CX| exact SEP| exact IMG| exact OK1| exact OK2| exact FTW| bz_params; lia| exact FSF].
      - rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by lia. exact ST.
      - rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, FS_FRAME. rewrite Z.mod_small by lia. lia.
      - rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite (Z.mod_small (bv_unsigned sp - 5008)) by lia. Z.div_mod_to_equations. lia. }
    clear FS. intros ms' PO. unfold fallbackSort_post in PO. cbv zeta in PO. cbn [e_arr1 e_arr2 e_ftab est_sorted] in PO.
    cps_destruct PO as (t0' & t1' & t2' & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3' & t4' & t5' & t6' & m2 & -> & MUc & WMc & MI2 & ST2 & AR1' & AR2' & FTB').
    unfold fallbackSort_W, FTAB_WORDS, FS_FRAME in MUc.
    rewrite Z_to_bv_unsigned in MUc, ST2. unfold bv_wrap, bv_modulus in MUc, ST2. rewrite Z.mod_small in MUc, ST2 by lia.
    clear AR1 AR2 FTB MI ST. transport_after_call s0segs m1 m2 MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x20414)) with (Z_to_bv 64 0x20414) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    eapply K; [exact EH1| exact AR1'| exact AR2'| exact FTB'| | exact MI2| exact ST2| exact MU| exact WM| exact MUc| exact WMc].
    split; [exact CM1| split; [exact CM2| split; [exact CM3| exact CM4]]].
  Time Qed.
End BSP.

End ACeilS1.
