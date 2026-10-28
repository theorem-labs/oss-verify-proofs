From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_FseDecomp.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseRdKit FseRdKit2 HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_fdw_kit
  RF_huf_y4_kit_reload.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Definition PFSE_DSYMF : Z := 0x20ca0.
Definition PFSE_DSYM : Z := 0x20d28.

Definition fse_dsym_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (DS BD DT S lo : Z) (jp : list byte) (o s' : Z) (d' : bitD) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : fmem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(DS, DS + 16); (BD, BD + 40)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' DS [C8 (Z_to_bv 64 s'); C8 (Z_to_bv 64 (DT + 4))]
    /\ rw_cells usegs m' BD (bitdz_cells S d' jp).

Definition fse_dsym_stmt_at (ENTRY : Z) (fast : bool) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (DS BD DT S lo : Z) (dt : dtable) (s : Z) (d : bitD)
         (jp : list byte) (o s' : Z) (d' : bitD),
  rw_cells usegs m DS [C8 (Z_to_bv 64 s); C8 (Z_to_bv 64 (DT + 4))] ->
  rw_cells usegs m BD (bitdz_cells S d jp) ->
  bytes_at usegs m (DT + 4) (concat (map fse_cell_bytes (dt_cells dt))) ->
  1 <= dt_tableLog dt <= 12 -> zlen (dt_cells dt) = 2^(dt_tableLog dt) ->
  Forall (fun c => 0 <= dc_symbol c < 256 /\ 0 <= dc_nbBits c <= dt_tableLog dt /\ 0 <= dc_newState c
                   /\ dc_newState c + 2^(dc_nbBits c) <= 2^(dt_tableLog dt)) (dt_cells dt) ->
  decode_sym dt fast s d = Ok (o, s', d') ->
  0 <= bd_bits d <= 2^30 -> 0 <= bd_cont d < 2^64 ->
  0 < DS -> DS mod 8 = 0 -> 0 < BD -> BD mod 8 = 0 -> 0 < DT -> DT + 4 + 4 * 2^(dt_tableLog dt) <= 2^64 -> 8 <= S ->
  (DS + 16 <= BD \/ BD + 40 <= DS) ->
  (DS + 16 <= DT + 4 \/ DT + 4 + 4 * 2^(dt_tableLog dt) <= DS) ->
  (BD + 40 <= DT + 4 \/ DT + 4 + 4 * 2^(dt_tableLog dt) <= BD) ->
  stk usegs m lo (bv_unsigned sp) -> (DS + 16 <= lo \/ bv_unsigned sp <= DS) -> (BD + 40 <= lo \/ bv_unsigned sp <= BD) ->
  mem_inv usegs m ->
  evt usegs (fse_dsym_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DS BD DT S lo jp o s' d' m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DS) (Z_to_bv 64 BD) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).

Definition fse_dsymf_stmt : Prop := fse_dsym_stmt_at PFSE_DSYMF true.
Definition fse_dsym_stmt : Prop := fse_dsym_stmt_at PFSE_DSYM false.

Lemma dsym_inv : forall dt fast s d o s' d',
  decode_sym dt fast s d = Ok (o, s', d') ->
  exists c lb, 0 <= s < zlen (dt_cells dt) /\ nth_error (dt_cells dt) (Z.to_nat s) = Some c /\
    o = dc_symbol c /\ s' = dc_newState c + lb /\ d' = skip_bits d (dc_nbBits c) /\
    (if fast then lb = look_bits_fast d (dc_nbBits c) else look_bits d (dc_nbBits c) = Ok lb).
Proof.
  intros dt fast s d o s' d' H. unfold decode_sym, HufPure_FseDecomp.cell in H.
  destruct ((0 <=? s) && (s <? FseNCount.Zlength (dt_cells dt))) eqn:B; [|discriminate].
  apply andb_true_iff in B. destruct B as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
  unfold FseNCount.Zlength in B2. cbn [bind] in H.
  assert (NE : nth_error (dt_cells dt) (Z.to_nat s) = Some (nth (Z.to_nat s) (dt_cells dt) (mkDC 0 0 0)))
    by (apply nth_error_nth'; lia).
  set (c := nth (Z.to_nat s) (dt_cells dt) (mkDC 0 0 0)) in *. clearbody c.
  destruct fast.
  - cbn [bind] in H. unfold read_bits_fast in H. injection H as <- <- <-.
    exists c, (look_bits_fast d (dc_nbBits c)). repeat split; lia || assumption || reflexivity.
  - unfold read_bits in H. destruct (look_bits d (dc_nbBits c)) as [v| | |] eqn:L; cbn [bind] in H; try discriminate.
    injection H as <- <- <-. exists c, v. repeat split; lia || assumption || reflexivity.
Qed.

Ltac fd_step uim stop := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 uim) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 stop) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep end).

Ltac fd_clr := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H | H : bytes_at _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H | H : wmono _ _ _ |- _ => clear H | H : mem_inv _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H | H : ov_read_bytes _ _ _ _ = _ |- _ => clear H
  | H : _ \/ _ |- _ => clear H | H : decode_sym _ _ _ _ = _ |- _ => clear H | H : Forall _ _ |- _ => clear H end.

Ltac fd_brk := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
  let U := fresh "U" in if_cases U; zify_cond U; land7; nrm U end.

Ltac fd_ref SH := try (exfalso; fd_clr; rewrite ?SH in *; lia).

Lemma fd_zx16 : forall x, 0 <= x < 2^16 -> bv_unsigned (zx16 (Z_to_bv 64 x)) = x.
Proof.
  intros x X. unfold zx16. rewrite (unsigned_lit x) by lia. rewrite (Z.mod_small x) by lia. apply unsigned_lit; lia.
Qed.

Lemma fd_zx32 : forall x, 0 <= x < 2^32 -> bv_unsigned (zx32 (Z_to_bv 64 x)) = x.
Proof.
  intros x X. unfold zx32. rewrite (unsigned_lit x) by lia. rewrite (Z.mod_small x) by lia. apply unsigned_lit; lia.
Qed.

Lemma fd_sx32 : forall x, 0 <= x < 2^31 -> bv_unsigned (sx32 (Z_to_bv 64 x)) = x.
Proof.
  intros x X. unfold sx32. rewrite (unsigned_lit x) by lia. rewrite (FseWalkKit.swrap32_small x) by lia.
  apply unsigned_lit; lia.
Qed.

Ltac fd_zx := repeat match goal with
  | H : context [bv_unsigned (zx16 (Z_to_bv 64 ?x))] |- _ => rewrite (fd_zx16 x) in H by lia
  | |- context [bv_unsigned (zx16 (Z_to_bv 64 ?x))] => rewrite (fd_zx16 x) by lia
  | H : context [bv_unsigned (zx32 (Z_to_bv 64 ?x))] |- _ => rewrite (fd_zx32 x) in H by lia
  | |- context [bv_unsigned (zx32 (Z_to_bv 64 ?x))] => rewrite (fd_zx32 x) by lia
  | H : context [bv_unsigned (sx32 (Z_to_bv 64 ?x))] |- _ => rewrite (fd_sx32 x) in H by lia
  | |- context [bv_unsigned (sx32 (Z_to_bv 64 ?x))] => rewrite (fd_sx32 x) by lia end.

Lemma fd_nb : forall sy nb, 0 <= sy < 256 -> 0 <= nb < 256 ->
  ((sy + 256 * nb) ≪ 16 mod 18446744073709551616) ≫ 24 = nb.
Proof.
  intros sy nb A B. rewrite Z.shiftl_mul_pow2 by lia. change (2^16) with 65536.
  rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^24) with 16777216.
  symmetry. apply (Z.div_unique _ _ nb (sy * 65536)); lia.
Qed.

Lemma fd_sh : forall nb, 0 <= nb <= 32 ->
  (bv_swrap 32 (0 - nb) mod 18446744073709551616) mod 64 = (u32 (64 - nb)) mod 64.
Proof.
  intros nb N. rewrite (FseWalkKit.swrap32_small (0 - nb)) by lia.
  unfold u32. rewrite (Z.mod_small (64 - nb)) by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma fd_land : forall sy nb, 0 <= sy < 256 -> 0 <= nb -> Z.land (sy + 256 * nb) 255 = sy.
Proof.
  intros sy nb A B. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2^8) with 256.
  replace (sy + 256 * nb) with (sy + nb * 256) by ring. rewrite Z.mod_add by lia. apply Z.mod_small; lia.
Qed.

Theorem fse_dsymf_proof : fse_dsymf_stmt.
Proof.
  unfold fse_dsymf_stmt, fse_dsym_stmt_at, PFSE_DSYMF.
  intros until d'. intros HDS HBD TB TL TLN COK DSY B30 BCR R1 R2 R3 R4 R5 R6 R7 DJ1 DJ2 DJ3 STK SP1 SP2 MI.
  destruct (dsym_inv _ _ _ _ _ _ _ DSY) as (c & lb & SR & NE & -> & -> & -> & LB). cbv iota in LB. subst lb.
  rewrite TLN in SR.
  pose proof (proj1 (Forall_forall _ _) COK c (nth_error_In _ _ NE)) as CK. cbv beta in CK.
  destruct CK as (CS & CN & CN0 & CNS).
  set (tl := dt_tableLog dt) in *. set (cells := dt_cells dt) in *.
  assert (P2 : 2 <= 2^tl <= 4096) by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia
                                            | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
  pose proof (Z.pow_pos_nonneg 2 (dc_nbBits c) ltac:(lia) ltac:(lia)) as PN.
  assert (SH4 : s ≪ 2 = 4 * s) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  pose proof (cell_rd_ns usegs m (DT + 4) cells s c (Z_to_bv 64 (s ≪ 2 + (DT + 4))) TB NE ltac:(lia)
                ltac:(unfold wa; f_equal; rewrite SH4; lia)) as RNS.
  pose proof (cell_rd_off usegs m (DT + 4) cells s c 2 2%nat TB NE ltac:(lia) ltac:(lia) ltac:(lia)) as RSN.
  change (Z.to_nat 2) with 2%nat in RSN. unfold fse_cell_bytes, le2 in RSN. cbn [firstn skipn app Z_to_le_bytes] in RSN.
  rewrite <- (le2_two_bytes (dc_symbol c) (dc_nbBits c)) in RSN by lia.
  replace (DT + 4 + (4 * s + 2)) with (s ≪ 2 + (DT + 4) + 2) in RSN by (rewrite SH4; lia). unfold wa in RSN.
  unfold bitdz_cells in HBD.
  pose proof (munch_refl [(DS, DS + 16); (BD, BD + 40)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  repeat (fd_step 0x20d24 0; fd_brk; fd_ref SH4).
  all: fd_step 0x20d24 0.
  all: fd_ref SH4.
  all: fd_zx.
  all: rewrite ?(fd_nb (dc_symbol c) (dc_nbBits c)) in * by lia.
  all: rewrite ?(fd_sh (dc_nbBits c)) in * by lia.
  all: rewrite ?(fd_land (dc_symbol c) (dc_nbBits c)) by lia.
  all: apply evt_done; unfold fse_dsym_post, bitdz_cells; cbn [skip_bits bd_cont bd_bits bd_ptr bd_zero].
  all: repeat (lazymatch goal with |- ex _ => eexists end).
  all: split; [reflexivity|].
  all: split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|].
  all: split.
  all: lazymatch goal with
    | H : rw_cells usegs ?mm _ [C8 (Z_to_bv 64 ?w); C8 ?x] |- rw_cells usegs ?mm _ [C8 (Z_to_bv 64 ?v); C8 ?x] =>
        replace v with w; [exact H|];
        unfold look_bits_fast, u64; replace (u32 (bd_bits d)) with (bd_bits d) by (unfold u32; rewrite Z.mod_small; lia);
        etransitivity; [apply Z.add_comm|]; reflexivity
    | H : rw_cells usegs ?mm _ (C8 ?x :: C4 (Z_to_bv 64 ?w) :: ?y) |- rw_cells usegs ?mm _ (C8 ?x :: C4 (Z_to_bv 64 ?v) :: ?y) =>
        replace v with w; [exact H|]; unfold u32; rewrite Z.mod_small by lia; reflexivity
  end.
Qed.

Lemma fd_w : forall sy nb ns, 0 <= sy < 256 -> 0 <= nb < 256 -> 0 <= ns < 65536 ->
  Z.lor (((sy + 256 * nb) ≪ 16) mod 18446744073709551616) ns = ns + 65536 * sy + 16777216 * nb.
Proof.
  intros sy nb ns A B C. rewrite Z.shiftl_mul_pow2 by lia. change (2^16) with 65536.
  rewrite Z.mod_small by lia. replace ((sy + 256 * nb) * 65536) with ((sy + 256 * nb) * 2^16) by reflexivity.
  rewrite lor_shift_add by lia. lia.
Qed.

Lemma fd_nbd : forall sy nb, 0 <= sy < 256 -> 0 <= nb < 256 ->
  (((sy + 256 * nb) ≪ 16) mod 18446744073709551616) / 2^24 = nb.
Proof.
  intros sy nb A B. rewrite <- Z.shiftr_div_pow2 by lia. apply fd_nb; lia.
Qed.

Lemma fd_x4 : forall x, 0 <= x < 2^60 -> (x ≪ 2) mod 18446744073709551616 = 4 * x.
Proof.
  intros x X. rewrite Z.shiftl_mul_pow2 by lia. change (2^2) with 4. rewrite Z.mod_small by lia. lia.
Qed.

Lemma fd_sym : forall sy nb ns, 0 <= sy < 256 -> 0 <= nb < 256 -> 0 <= ns < 65536 ->
  (((ns + 65536 * sy + 16777216 * nb) ≪ 40) mod 18446744073709551616) ≫ 56 = sy.
Proof.
  intros sy nb ns A B C. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace ((ns + 65536 * sy + 16777216 * nb) * 2^40 mod 18446744073709551616) with ((ns + 65536 * sy) * 2^40)
    by (apply (Z.mod_unique _ _ nb); lia).
  symmetry. apply (Z.div_unique _ _ sy (ns * 2^40)); lia.
Qed.

Lemma fd_lo16 : forall sy nb ns, 0 <= sy < 256 -> 0 <= nb < 256 -> 0 <= ns < 65536 ->
  (ns + 65536 * sy + 16777216 * nb) mod 65536 = ns.
Proof.
  intros sy nb ns A B C. symmetry. apply (Z.mod_unique _ _ (sy + 256 * nb)); lia.
Qed.

Ltac fd_ref2 SH := try (exfalso; fd_clr; fd_zx; rewrite ?SH in *; rewrite ?fd_w in * by lia;
  rewrite ?fd_nbd in * by lia; rewrite ?fd_x4 in * by lia; lia).

Theorem fse_dsym_proof : fse_dsym_stmt.
Proof.
  unfold fse_dsym_stmt, fse_dsym_stmt_at, PFSE_DSYM.
  intros until d'. intros HDS HBD TB TL TLN COK DSY B30 BCR R1 R2 R3 R4 R5 R6 R7 DJ1 DJ2 DJ3 STK SP1 SP2 MI.
  destruct (dsym_inv _ _ _ _ _ _ _ DSY) as (c & lb & SR & NE & -> & -> & -> & LB). cbv iota in LB.
  rewrite TLN in SR.
  pose proof (proj1 (Forall_forall _ _) COK c (nth_error_In _ _ NE)) as CK. cbv beta in CK.
  destruct CK as (CS & CN & CN0 & CNS).
  set (tl := dt_tableLog dt) in *. set (cells := dt_cells dt) in *.
  assert (P2 : 2 <= 2^tl <= 4096) by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia
                                            | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
  pose proof (Z.pow_pos_nonneg 2 (dc_nbBits c) ltac:(lia) ltac:(lia)) as PN.
  rewrite lookbits_mach in LB by lia. injection LB as <-.
  assert (SH4 : s ≪ 2 = 4 * s) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  pose proof (cell_rd_ns usegs m (DT + 4) cells s c (Z_to_bv 64 (s ≪ 2 + (DT + 4))) TB NE ltac:(lia)
                ltac:(unfold wa; f_equal; rewrite SH4; lia)) as RNS.
  pose proof (cell_rd_off usegs m (DT + 4) cells s c 2 2%nat TB NE ltac:(lia) ltac:(lia) ltac:(lia)) as RSN.
  change (Z.to_nat 2) with 2%nat in RSN. unfold fse_cell_bytes, le2 in RSN. cbn [firstn skipn app Z_to_le_bytes] in RSN.
  rewrite <- (le2_two_bytes (dc_symbol c) (dc_nbBits c)) in RSN by lia.
  replace (DT + 4 + (4 * s + 2)) with (s ≪ 2 + (DT + 4) + 2) in RSN by (rewrite SH4; lia). unfold wa in RSN.
  pose proof (mask_rd m (dc_nbBits c) MI ltac:(lia)) as MK.
  replace (4 * dc_nbBits c)
    with (((((bv_unsigned (zx16 (Z_to_bv 64 (dc_symbol c + 256 * dc_nbBits c)))) ≪ 16) mod 18446744073709551616) ≫ 24) ≪ 2)
    in MK by (rewrite fd_zx16 by lia; rewrite fd_nb by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
  unfold BIT_MASK_TAB in MK.
  unfold bitdz_cells in HBD.
  pose proof (munch_refl [(DS, DS + 16); (BD, BD + 40)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  repeat (fd_step 0x20de0 0; fd_brk; fd_ref2 SH4).
  all: fd_step 0x20de0 0.
  all: fd_ref2 SH4.
  all: fd_zx.
  all: rewrite ?(fd_w (dc_symbol c) (dc_nbBits c) (dc_newState c)) in * by lia.
  all: rewrite ?(fd_sym (dc_symbol c) (dc_nbBits c) (dc_newState c)) in * by lia.
  all: rewrite ?(fd_lo16 (dc_symbol c) (dc_nbBits c) (dc_newState c)) in * by lia.
  all: rewrite ?(fd_nb (dc_symbol c) (dc_nbBits c)) in * by lia.
  all: rewrite ?Z.mod_mod in * by lia.
  all: apply evt_done; unfold fse_dsym_post, bitdz_cells; cbn [skip_bits bd_cont bd_bits bd_ptr bd_zero].
  all: repeat (lazymatch goal with |- ex _ => eexists end).
  all: split; [reflexivity|].
  all: split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|].
  all: split.
  all: lazymatch goal with
    | H : rw_cells usegs ?mm _ [C8 (Z_to_bv 64 ?w); C8 ?x] |- rw_cells usegs ?mm _ [C8 (Z_to_bv 64 ?v); C8 ?x] =>
        replace v with w; [exact H|]; rewrite (Z.mod_small (bd_bits d + dc_nbBits c)) by lia;
        etransitivity; [apply Z.add_comm|]; reflexivity
    | H : rw_cells usegs ?mm _ (C8 ?x :: C4 (Z_to_bv 64 ?w) :: ?y) |- rw_cells usegs ?mm _ (C8 ?x :: C4 (Z_to_bv 64 ?v) :: ?y) =>
        replace v with w; [exact H|]; unfold u32; rewrite Z.mod_small by lia; reflexivity
  end.
Qed.
