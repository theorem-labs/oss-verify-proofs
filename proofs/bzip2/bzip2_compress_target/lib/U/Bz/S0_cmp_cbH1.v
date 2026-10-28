(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 DecTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpLaws. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCutCB. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpMsKit CmpMsKit2 CmpFsKit0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpArith BzSepTac BzCLemmas1 BzLemmasMtf BzLemmasT. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs6 BzCFactsBs6 CmpCutMS CmpHmKit.
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
Strategy 1000 [blockSort compressBlock cb_e0 cb_sorted].
(* [comment removed for export] *)
Ltac qlia := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | zify_prune; Zify.zify; xlia zchecker ].
Ltac addr_eq_tac ::= symmetry; first [ apply wa_of_Z_to_bv; qlia | apply wa_of_var; qlia | unfold wa; f_equal; qlia ].
Ltac cbn_est_in H :=
  cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
       e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
       e_len e_code e_rfreq e_len_pack est_set_bw bw_buff bw_live bw_numZ bw_zb] in H.
Ltac cbn_est :=
  cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
       e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
       e_len e_code e_rfreq e_len_pack est_set_bw bw_buff bw_live bw_numZ bw_zb].


(* [comment removed for export] *)
Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section CrcArith.
  Open Scope Z_scope.
  Lemma low32_lxor_ones64 : forall a, Z.lxor a 18446744073709551615 mod M32 = Z.lxor (a mod M32) 4294967295.
  Proof. intros a. rewrite low32_lxor. reflexivity. Qed.
  Lemma crc_final_mod : forall c, 0 <= c < 4294967296 -> crc_final c mod M32 = crc_final c.
  Proof. intros c Hc. apply low32_small. pose proof (BzCLemmas1.crc_final_range c Hc). lia. Qed.
  (* [comment removed for export] *)
  Lemma low32_final : forall c, 0 <= c < 4294967296 ->
    bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (sx32 (Z_to_bv 64 c))) 18446744073709551615)) mod M32 = crc_final c mod M32.
  Proof.
    intros c Hc. rewrite low32_lit, low32_lxor_ones64, low32_sx32, low32_lit, (low32_small c) by lia.
    rewrite crc_final_mod by lia. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma low32_combine : forall c bc, 0 <= c < 4294967296 -> 0 <= bc < 4294967296 ->
    bv_unsigned (Z_to_bv 64
      (Z.lxor (Z.lor (Z.land (bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 c)) * 2)) 18446744073709551615)
                     (bv_unsigned (sx32 (Z_to_bv 64 c)) mod 4294967296 / 2147483648))
              (Z.lxor (bv_unsigned (sx32 (Z_to_bv 64 bc))) 18446744073709551615))) mod M32
    = Z.lxor (Z.lor ((Z.shiftl c 1) mod 4294967296) (Z.shiftr c 31)) (crc_final bc) mod M32.
  Proof.
    intros c bc Hc Hb. rewrite low32_lit, low32_lxor, low32_lxor_ones64.
    rewrite (low32_sx32 (Z_to_bv 64 bc)), (low32_lit bc), (low32_small bc) by lia. fold (crc_final bc).
    rewrite low32_lor. change 18446744073709551615 with (Z.ones 64) at 1. rewrite Z.land_ones by lia.
    change (2 ^ 64) with 18446744073709551616. rewrite mod64_mod32, swrap32_mod32, low32_mul.
    rewrite (low32_sx32 (Z_to_bv 64 c)), (low32_lit c), (low32_small c) by lia.
    rewrite (low32_small (c / 2147483648)). 2:{ split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. change (2 ^ 31) with 2147483648.
    symmetry. apply low32_small. change 4294967296 with (2 ^ 32) at 3.
    apply BzLemmasMtf.lxor_lt_pow2.
    - apply BzLemmasT.lor_lt_pow2.
      + pose proof (Z.mod_pos_bound (c * 2) 4294967296 ltac:(lia)). change (2 ^ 32) with 4294967296. lia.
      + split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2147483648 * 2 ^ 32) with (2 ^ 63). lia.
    - change (2 ^ 32) with 4294967296. apply BzCLemmas1.crc_final_range. exact Hb.
  Qed.
End CrcArith.

Section CBH.
  Variables (cx : cctx) (g : eg) (e : est).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) (sv : word) (is_last : bool).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis IMG : cctx_img S0C cx.
  Hypothesis CE : cb_entry g e.
  Hypothesis STK : (lo + CB_STACK <= bv_unsigned sp)%Z. Hypothesis LO : (CEIL <= lo)%Z. Hypothesis AL : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis S0_blockSort : blockSort_spec2 bsX S0C.
  Local Ltac nt := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => notrap | _ => idtac end.
  Notation usp := (bv_unsigned sp). Notation p := (bv_unsigned sp - 384)%Z.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation FT := (c_FT cx). Notation J := (c_J cx). Notation n := (e_nblock e).
  Notation CBW := [(E, E + 55768); (A1, A1 + ARR1_SIZE); (A2, A2 + ARR2_SIZE); (FT, FT + 4 * 65537); (usp - 16384, usp)]%Z.
  (* [comment removed for export] *)
  Definition erest (m1 : word -> option byte) : Prop :=
    u8arr s0segs m1 (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) /\
    u8arr s0segs m1 (E + 384) (ovb (e_unseqToSeq e) (jseg J 384 256) 256) /\
    u32arr s0segs m1 (E + 672) (ovw (e_mtfFreq e) (jseg J 672 1032) 258) /\
    u8arr s0segs m1 (E + 1704) (ovb (e_selector e) (jseg J 1704 18002) 18002) /\
    u8arr s0segs m1 (E + 19706) (ovb (e_selectorMtf e) (jseg J 19706 18002) 18002) /\
    u8arr s0segs m1 (E + 37708) (ovb (e_len e) (jseg J 37708 1548) 1548) /\
    u32arr s0segs m1 (E + 39256) (ovw (e_code e) (jseg J 39256 6192) 1548) /\
    u32arr s0segs m1 (E + 45448) (ovw (e_rfreq e) (jseg J 45448 6192) 1548) /\
    u32arr s0segs m1 (E + 51640) (ovw (e_len_pack e) (jseg J 51640 4128) 1032).
  Definition g1 : eg := EG (g_aie g) true (g_mtf g) (g_bs g) (g_zbits g).

  (* [comment removed for export] *)
  Lemma numz_step : forall (Q : machine_state -> Prop) (m1 : word -> option byte)
      (x0 x4 x5 x6 x8 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word),
    (0 < n)%Z ->
    rw_cells s0segs m1 E (EHEAD1 cx g (cb_e0 e)) -> mem_inv s0segs m1 -> munch [(E + 116, E + 120)]%Z m1 m1 -> wmono s0segs m1 m1 ->
    (forall m2 (x11 : word), rw_cells s0segs m2 E (EHEAD1 cx g (cb_e0 e)) -> mem_inv s0segs m2 -> munch [(E + 116, E + 120)]%Z m1 m2 -> wmono s0segs m1 m2 ->
      evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 (Z_to_bv 64 E) x8 (Z_to_bv 64 2) x10 x11 x12 x13 x14 x15 x16
                            x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                       F (Z_to_bv 64 0x163cc) fc None m2 (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x0 (Z_to_bv 64 p) gp tp x4 x5 x6 (Z_to_bv 64 E) x8 (Z_to_bv 64 2) x10 (sx32 (Z_to_bv 64 (e_blockNo e))) x12 x13 x14 x15 x16
                          x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30)
                     F (Z_to_bv 64 0x163c4) fc None m1 (seg_rom s0segs)).
  Proof.
    intros Q m1 x0 x4 x5 x6 x8 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 POS EH1 MI MU WM K.
    pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'.
    cps_destruct CX' as (RE & RE' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ME16 & _).
    bz_ceil; bz_params; unfold ESTATE_SIZE, CEIL in *.
    pose proof (cb_entry_facts g e CE) as (EOK & _). cps_pose EOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BN).
    unfold EHEAD1, cb_e0 in EH1. cbn_est_in EH1.
    wstep; if_cases Kb; zify_cond_z Kb.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _) end; [st_eq| unfold EHEAD1, cb_e0; cbn_est; exact EH1| exact MI| exact MU| exact WM].
    - wstep; lit_store.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _) end; [st_eq| unfold EHEAD1, cb_e0; cbn_est; exact EH1| exact MI| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  Lemma S0_cb_H1 : forall (Q : machine_state -> Prop) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (0 < n)%Z ->
    emem cx s0segs g e m -> amem cx s0segs e m -> cimg_mem S0C m sv -> mem_inv s0segs m -> stk s0segs m lo usp ->
    (forall (sp' : word) (m' : word -> option byte) (J280 : list byte) (y0 y4 y5 y6 y9 y10 y11 y12 y13 y14 y15 y16 y27 y28 y29 y30 : word),
      bv_unsigned sp' = (usp - 384)%Z ->
      rw_cells s0segs m' E (EHEAD1 cx g1 (cbE1 e)) -> rw_cells s0segs m' (E + 640) (EHEAD2 cx g1 (cbE1 e)) -> amem cx s0segs (cbE1 e) m' ->
      erest m' -> cimg_mem S0C m' sv -> mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp') ->
      u8arr s0segs m' (bv_unsigned sp') J280 -> Z.of_nat (length J280) = 280%Z ->
      rw_cells s0segs m' (bv_unsigned sp' + 280) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      munch CBW m m' -> wmono s0segs m m' ->
      evt s0segs Q (MS (mkR y0 sp' gp tp y4 y5 y6 (Z_to_bv 64 E) (Z_to_bv 64 (if is_last then 1 else 0)) y9 y10 y11 y12 y13 y14 y15 y16
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x163dc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) (Z_to_bv 64 (if is_last then 1 else 0)) a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x16344) fc None m (seg_rom s0segs)).
  Proof.
    intros Q t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 POS EM AM CM MI ST K.
    pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'.
    cps_destruct CX' as (RE & RE' & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & _ & _ & _ & _ & ME16 & _ & _ & _ & _ & _ & LJ & _).
    pose proof SEP as SEP'. unfold cctx_sep, apart in SEP'. cbv zeta in SEP'.
    cps_destruct SEP' as (SE1 & SE2 & SEF & _ & _ & AP12 & AP1F & _ & _ & AP2F & _).
    pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3, IMG_HI3 in IMG'. cbn [ci_hi S0C] in IMG'. cps_destruct IMG' as (IE & IA1 & IA2 & IFT & _).
    bz_ceil; bz_params; unfold FTAB_WORDS, ESTATE_SIZE, CB_STACK, CEIL in *.
    destruct IA1 as [IA1|IA1]; [exfalso; lia|]. destruct IA2 as [IA2|IA2]; [exfalso; lia|]. destruct IFT as [IFT|IFT]; [exfalso; lia|].
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    destruct (mod16_linq _ AL) as [qsp ALQ]. clear AL.
    cps_pose (cb_entry_facts g e CE) as (EOK & NBR & _ & _ & SOP & NZ0 & BN1 & ALT). bz_params.
    cps_pose EOK as (A1OK & A2OK & FTW & _ & _ & _ & _ & _ & _ & _ & BC & CC & _).
    pose proof CM as CM'. cps_destruct CM' as (CM1 & CM2 & CM3 & CM4). cbn [ci_segs ci_got ci_stderrp ci_crc ci_crcx S0C] in CM1, CM2, CM3, CM4.
    open_emem EM. cbn_est_in EH1. cbn_est_in EH2. rewrite NZ0 in EH1.
    open_amem AM. unfold FTAB_WORDS in AR1, AR2, FTB.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (munch_refl CBW m) as MU. pose proof (wmono_refl s0segs m) as WM.
    (* [comment removed for export] *)
    carve_frame 384%nat ST.
    pose proof (u8arr_of_rw_cells s0segs _ _ _ _ FR) as FRu.
    assert (LJK : Z.of_nat (length junk) = 384%Z) by (pose proof (proj1 (proj1 (proj1 FR))) as W; cbn in W; lia).
    clear FR.
    u8take FRu FRONTu 280%Z (bv_unsigned sp + -104)%Z. rename FRu into SAVu.
    name_bytes SAVu jsav 104%Z. name_bytes FRONTu jfr 280%Z. clear LJK junk.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SAVu) as SAV. clear SAVu. replace (length jsav) with 104%nat in SAV by lia.
    replace (bv_unsigned sp + -104)%Z with (bv_unsigned sp - 384 + 280)%Z in SAV by lia.
    replace (bv_unsigned sp + -384)%Z with (bv_unsigned sp - 384)%Z in ST, FRONTu by lia.
    wstep. replace (Z_to_bv 64 (bv_unsigned sp + -384)) with (Z_to_bv 64 (bv_unsigned sp - 384)) by (f_equal; lia).
    do 13 wstep.
    (* [comment removed for export] *)
    wstep. nt. wstep. wstep. wstep. nt. wstep. wstep.
    wstep; if_cases Kz; [apply blez_taken in Kz; [exfalso; lia| lia] | clear Kz].
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    wstep. wstep.
    reword_C4 EH2 2%nat (crc_final (e_blockCRC e)). { apply low32_final. exact BC. }
    reword_C4 EH2 3%nat (Z.lxor (Z.lor ((Z.shiftl (e_combinedCRC e) 1) mod 4294967296) (Z.shiftr (e_combinedCRC e) 31)) (crc_final (e_blockCRC e))).
    { apply low32_combine; [exact CC| exact BC]. }
    assert (EH2f : rw_cells s0segs _ (E + 640) (EHEAD2 cx g (cb_e0 e))) by (unfold EHEAD2, cb_e0; cbn_est; exact EH2). clear EH2.
    (* [comment removed for export] *)
    assert (EH1f : rw_cells s0segs _ E (EHEAD1 cx g (cb_e0 e))) by (unfold EHEAD1, cb_e0; cbn_est; exact EH1). clear EH1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    eapply (numz_step Q m1); [exact POS| exact EH1f| exact MI| apply munch_refl| apply wmono_refl|].
    clear EH1f MI. intros m2 x11' EH1 MI MU2 WM2. transport_after_call s0segs m1 m2 MU2 WM2. clear MU2 WM2.
    (* [comment removed for export] *)
    pose proof EH2f as EH2r. unfold EHEAD2, cb_e0 in EH2r. cbn_est_in EH2r.
    wstep. clear EH2r. wstep; try if_false. wstep. wstep.
    pose proof (cbE0_ok g e CE POS) as [EOK0 NB0]. change (cbE0 e) with (cb_e0 e) in EOK0, NB0. cbn [e_nblock cb_e0] in NB0.
    pose proof S0_blockSort as BS. unfold blockSort_spec2 in BS. cbv zeta in BS. cbn [ci_segs ci_blockSort S0C] in BS.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
    eapply evt_cut.
    { eapply (BS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 cx g (cb_e0 e) lo sv);
        rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?(Z.mod_small (bv_unsigned sp - 384)) by lia;
        [reflexivity| exact EH1| exact EH2f| | | exact MI| exact ST| unfold BS_STACK; lia| exact LO| Z.div_mod_to_equations; lia
        | exact CX| exact SEP| exact IMG| exact EOK0| cbn [e_nblock cb_e0]; bz_params; lia| ].
      - unfold cb_e0. apply amem_introF; cbn_est; [exact AR1| exact AR2| exact FTB].
      - split; [exact CM1| split; [exact CM2| split; [exact CM3| exact CM4]]].
      - apply bsX_intro; [exact EOK0| cbn [e_nblock cb_e0]; bz_params; lia]. }
    clear BS EH1 EH2f AR1 AR2 FTB MI ST.
    intros ms' PO. unfold blockSort_post2 in PO. cbv zeta in PO.
    cps_destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m4 & -> & MUc & WMc & MI & ST & EH1 & EH2 & AM).
    unfold blockSort_W, FTAB_WORDS, BS_STACK in MUc.
    rewrite Z_to_bv_unsigned in MUc, ST. unfold bv_wrap, bv_modulus in MUc, ST. rewrite (Z.mod_small (bv_unsigned sp - 384)) in MUc, ST by lia.
    transport_after_call s0segs m3 m4 MUc WMc. clear MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x163dc)) with (Z_to_bv 64 0x163dc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    change (fst (fst (fst (blockSort (cb_e0 e) znew)))) with (cbE1 e) in EH1, EH2, AM.
    change (EG (g_aie g) true (g_mtf g) (g_bs g) (g_zbits g)) with g1 in EH1, EH2.
    (* [comment removed for export] *)
    eapply (K (Z_to_bv 64 (bv_unsigned sp - 384))); rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?(Z.mod_small (bv_unsigned sp - 384)) by lia;
      [reflexivity| exact EH1| exact EH2| exact AM| | | exact MI| exact ST| exact FRONTu| exact Ljfr| exact SAV| exact MU| exact WM].
    - unfold erest. repeat (split; [assumption|]). assumption.
    - split; [exact CM1| split; [exact CM2| split; [exact CM3| exact CM4]]].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_cb_H1z : forall (Q : machine_state -> Prop) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    n = 0%Z ->
    emem cx s0segs g e m -> amem cx s0segs e m -> cimg_mem S0C m sv -> mem_inv s0segs m -> stk s0segs m lo usp ->
    (forall (sp' : word) (m' : word -> option byte) (J280 : list byte) (y4 y5 y6 y9 y10 y11 y12 y13 y14 y15 y16 y27 y28 y29 y30 : word),
      bv_unsigned sp' = (usp - 384)%Z ->
      rw_cells s0segs m' E (EHEAD1 cx g e) -> rw_cells s0segs m' (E + 640) (EHEAD2 cx g e) -> amem cx s0segs e m' ->
      erest m' -> cimg_mem S0C m' sv -> mem_inv s0segs m' -> stk s0segs m' lo (bv_unsigned sp') ->
      u8arr s0segs m' (bv_unsigned sp') J280 -> Z.of_nat (length J280) = 280%Z ->
      rw_cells s0segs m' (bv_unsigned sp' + 280) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      munch CBW m m' -> wmono s0segs m m' ->
      evt s0segs Q (MS (mkR ra sp' gp tp y4 y5 y6 (Z_to_bv 64 E) (Z_to_bv 64 (if is_last then 1 else 0)) y9 y10 y11 y12 y13 y14 y15 y16
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y27 y28 y29 y30)
                       F (Z_to_bv 64 0x163dc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) (Z_to_bv 64 (if is_last then 1 else 0)) a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x16344) fc None m (seg_rom s0segs)).
  Proof.
    intros Q t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Z0 EM AM CM MI ST K.
    pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'.
    cps_destruct CX' as (RE & RE' & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & _ & _ & _ & _ & ME16 & _ & _ & _ & _ & _ & LJ & _).
    bz_ceil; bz_params; unfold FTAB_WORDS, ESTATE_SIZE, CB_STACK, CEIL in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof CM as CM'. cps_destruct CM' as (CM1 & CM2 & CM3 & CM4). cbn [ci_segs ci_got ci_stderrp ci_crc ci_crcx S0C] in CM1, CM2, CM3, CM4.
    open_emem EM. cbn_est_in EH1. cbn_est_in EH2.
    open_amem AM. unfold FTAB_WORDS in AR1, AR2, FTB.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (munch_refl CBW m) as MU. pose proof (wmono_refl s0segs m) as WM.
    carve_frame 384%nat ST.
    pose proof (u8arr_of_rw_cells s0segs _ _ _ _ FR) as FRu.
    assert (LJK : Z.of_nat (length junk) = 384%Z) by (pose proof (proj1 (proj1 (proj1 FR))) as W; cbn in W; lia).
    clear FR.
    u8take FRu FRONTu 280%Z (bv_unsigned sp + -104)%Z. rename FRu into SAVu.
    name_bytes SAVu jsav 104%Z. name_bytes FRONTu jfr 280%Z. clear LJK junk.
    pose proof (rw_cells_of_u8arr s0segs _ _ _ SAVu) as SAV. clear SAVu. replace (length jsav) with 104%nat in SAV by lia.
    replace (bv_unsigned sp + -104)%Z with (bv_unsigned sp - 384 + 280)%Z in SAV by lia.
    replace (bv_unsigned sp + -384)%Z with (bv_unsigned sp - 384)%Z in ST, FRONTu by lia.
    wstep. replace (Z_to_bv 64 (bv_unsigned sp + -384)) with (Z_to_bv 64 (bv_unsigned sp - 384)) by (f_equal; lia).
    do 13 wstep.
    (* [comment removed for export] *)
    wstep. nt. wstep. wstep. wstep. nt. wstep. wstep.
    wstep; if_cases Kz; [clear Kz | apply blez_not_taken in Kz; [exfalso; lia| lia]].
    eapply (K (Z_to_bv 64 (bv_unsigned sp - 384))); rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite ?(Z.mod_small (bv_unsigned sp - 384)) by lia;
      [reflexivity| unfold EHEAD1; cbn_est; exact EH1| unfold EHEAD2; cbn_est; exact EH2| | | | exact MI| exact ST| exact FRONTu| exact Ljfr| exact SAV| exact MU| exact WM].
    - apply amem_intro; [exact AR1| exact AR2| exact FTB].
    - unfold erest. repeat (split; [assumption|]). assumption.
    - split; [exact CM1| split; [exact CM2| split; [exact CM3| exact CM4]]].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
End CBH.

End ACeilS1.
