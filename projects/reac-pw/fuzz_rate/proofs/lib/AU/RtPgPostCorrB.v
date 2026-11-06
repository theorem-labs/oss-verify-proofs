(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 764 of its 806 lines of code are new or changed and 284 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPostCorr.v at da027552bb80; restated for
   reac-pw/fuzz_rate's image A: role's cut pcs become rate's (R 0x82808, RT 0x82888), its registers rate's
   (s2 = K is atom 18, s7 = &pp->len atom 23, s6 its shadow address atom 22, s11 = pp atom 27), the shadow-base
   atom of the token engine is W10Bx = SOff 18 0, the rm_ / rl_ vocabulary becomes rtm_ / rt_, lib/A/RtPgSteps.v's
   helpers (rts_wx, rts_segs_low, same_io_wvb, rts_region_nth, rts_chunks, regs_kept_of_st_ok) stand in for role's
   RPgW7bBase and RPgCfgChanges, and the input byte at the cut comes from the lane kit's w10_input_now. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgPostCorr.v at 8af9cea6f917; restated for
   image B (fuzz_rate.asan-ubsan) over lib/AU's RtPgMemB / RtPgSegB / RtPgStepsB / RtPgPostKB under the prefix
   wb10c_: image B's loop (R 0x82960, RT 0x829fc), its registers (t2 = &pp->len atom 7, s4 = K atom 20, a6 = 1
   atom 16, the loaded length in a7), pp, ~pp and the shadow address of &pp->len read from the real-frame cells
   R+0x168 / R+0x108 / R+0x170 (two read-only regions of s1 = R, atom 9; pp and ~pp are the extra atoms 36 / 37),
   and its three UBSan trap branches (0x82980, 0x829ac, 0x829b4), which the engine decides itself from closed-numeral
   atom ranges and one cond fact; the cuts' value lists carry R+0x108 and a6, and the input lies apart from the two
   cell ranges. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): one turn of the corruption loop of
   LLVMFuzzerTestOneInput (0x8076c), pod.h:445-446 with fuzz.h:39-42. Proves no function (kind: segment lemma).
   THE CODE (the cut R = 0x82960 is the loop head; a3 = kk, a2 = cnt - kk, a4 = off, a0 the cursor, a5 what is
   left of the input, a6 = 1)
     0x82960 ld a1,0x170(s1) / lbu a1,0(a1) / bnez a1 -> 0x834c4   the shadow byte of &pp->len (R+0x170 holds
                                                                   (pp + 0x4000 >> 3) + K)
     0x8296c ld a7,0(t2) / add a1,a4,a3                 len, off + kk
     0x82974 bgeu a1,a7 -> 0x829fc                      off + kk >= len: the corruption ends (RT)
     0x82978 beqz a5 -> 0x829a4                         no input left: the byte is 0 (0x829a4 li a7,0)
     0x8297c addi t0,a0,1 / bgeu a6,t0 -> 0x83098       UBSan: the cursor + 1 does not wrap (a6 = 1)
     0x82984 .. 0x82990                                 the check of the 1-byte read at a0 (second test 0x829f0)
     0x82994 lbu a7,0(a0) / addi a5,a5,-1 / mv a0,t0 / j 0x829a8
     0x829a8 srli t0,a1,14 / bnez t0 -> 0x83098         UBSan: off + kk < 16384
     0x829b0 ld t0,0x108(s1) / bltu t0,a1 -> 0x83098    UBSan: ~pp is not below off + kk (pp + off + kk < 2^64)
     0x829b8 ld t0,0x168(s1) / add a1,t0,a1             pp + off + kk
     0x829c0 .. 0x829cc                                 the check of the 1-byte store at a1 (second test 0x829e4)
     0x829d0 sb a7,0(a1) / addi a2,a2,-1 / addi a3,a3,1
     0x829dc bnez a2 -> 0x82960                         the next turn (R with kk + 1)
     0x829e0 j 0x829fc                                  the count is done (RT)
   The engine meets the two computed addresses through the facts' aliases: off + kk is atom 33 and pp + off + kk
   atom 34, so the store lands in a region of its own; each access's shadow bytes are a shadow entry of the engine
   (the length word and the store target inside the first block, the input byte inside the input), so no check
   reaches its error path. The engine decides the three trap branches itself: 0x82980 and 0x829b4 from the atom
   ranges (the cursor in [1, 2^47 - 2] against a6 in [1, 1]; ~pp in [2^63, 2^64 - 1] against off + kk in
   [8, 5440]), 0x829ac from the cond fact (off + kk) >> 14 = 0 (wb10c_shr14), since its decision procedure settles
   an equality only through the state's conds.
   wb10_corr: RtPgSegB's rsb_piece_W10_corr_stmt, R kk -> R (kk + 1) or RT. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgSegB RtPgStepsB RtPgPostKB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.

(* ---- the input byte at the cursor ---- *)
Lemma wb10c_nth_skipn : forall (rest : list byte) j x r1, skipn j rest = x :: r1 ->
  nth j (rsb_u8s rest) 0 = bv_unsigned x.
Proof.
unfold rsb_u8s. induction rest as [|y rest IH]; intros [|j] x r1 H; cbn in H |- *; try discriminate.
- injection H as -> ->. reflexivity.
- exact (IH j x r1 H).
Qed.

(* the sum of two atoms, as the engine writes `add` *)
Lemma wb10c_den_add : forall E n1 n2 v1 v2, ew E n1 = Z_to_bv 64 v1 -> 0 <= v1 < 2 ^ 62 ->
  ew E n2 = Z_to_bv 64 v2 -> 0 <= v2 < 2 ^ 62 ->
  sv_denot E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0)) = Z_to_bv 64 (v1 + v2).
Proof.
intros E n1 n2 v1 v2 H1 B1 H2 B2. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, (U_atom E n1 v1 H1 ltac:(lia)), (U_atom E n2 v2 H2 ltac:(lia)). cbn [zalu_raw].
apply zcanon_id. unfold M64. lia.
Qed.

(* the shadow entry of one input byte *)
Lemma wb10c_shent_in : forall E m n src left c, amem_range src left -> U E WB10Bx = SHADOW_OFF ->
  U E (SOff n 0) = c -> src <= c -> c + 1 <= src + left ->
  range_addressable (rd_of rsegs m) SHADOW_OFF c 1 ->
  shent_ok rsegs WB10Bx E m (mkSHE n 0 1).
Proof.
intros E m n src left c Ham HB Hc H1 H2 Hra. split; cbn [she_m she_lo she_hi].
- rewrite HB, Hc. eapply range_addressable_sub; [exact Hra | lia | lia].
- unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite HB. rewrite Hc in Ha.
  change (Z.min 0 1) with 0 in Ha. change (Z.max 0 1) with 1 in Ha.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia.
Qed.

(* a nonempty suffix: its head is the next byte of the prefix *)
Lemma wb10c_skipn_cons : forall (l : list byte) k y l', skipn k l = y :: l' ->
  firstn (S k) l = firstn k l ++ [y] /\ skipn (S k) l = l'.
Proof.
induction l as [|z l IH]; intros [|k] y l' H; cbn in H |- *; try discriminate.
- injection H as -> ->. split; reflexivity.
- destruct (IH k y l' H) as [H1 H2]. split; [rewrite H1; reflexivity | exact H2].
Qed.

Lemma wb10c_le1 : forall y : byte, Z_to_le_bytes 1 (bv_unsigned y) = [y].
Proof. intros y. cbn [Z_to_le_bytes]. rewrite wb10_byte_self. reflexivity. Qed.

(* the 64-bit complement as the cell R+0x108 holds it, as an unsigned value *)
Lemma wb10c_lnot_mod : forall p, 0 <= p < 2 ^ 64 -> Z.lnot p mod 2 ^ 64 = 2 ^ 64 - 1 - p.
Proof.
intros p Hp. replace (Z.lnot p) with ((2 ^ 64 - 1 - p) + (-1) * 2 ^ 64) by (unfold Z.lnot; lia).
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* the UBSan test of 0x829ac (`srli t0,a1,14; bnez t0`, pod.h:446) as a cond fact of the state: the engine settles an
   equality only through f_conds (YP0m decide_eq has no rule for a range of one value), so the state carries
   (off + kk) >> 14 = 0, and the engine then decides the trap branch not taken by itself *)
Lemma wb10c_shr14 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 16384 ->
  acond_ok E (mkAC BC_EQ (SAlu ALU_SRL (SOff n 0) (SLit 14)) (SLit 0)).
Proof.
intros E n v Hn Hv. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_eq_U, U_SAlu, !U_SLit, (U_atom E n v Hn ltac:(lia)). cbn [zalu_raw].
change (Z.land (zcanon 14) 63) with 14. rewrite Z.shiftr_div_pow2 by lia.
rewrite Z.div_small by (change (2 ^ 14) with 16384; lia). apply Z.eqb_refl.
Qed.

(* two real-frame ranges of the build's write set (rate_himg_B's hi_w1): the input lies outside them, so the two
   read-only cell regions of the loop's state are apart from the input byte's *)
Lemma wb10c_not_w1 : forall e a, ~ rt_inw e (hi_w1 rate_himg_B) a ->
  ~ (q_R e + 0x58 <= a < q_R e + 0x148) /\ ~ (q_R e + 0x150 <= a < q_R e + 0x180).
Proof.
intros e a H. split; intros Ha; apply H; unfold rt_inw; cbn [hi_w1 rate_himg_B].
- do 3 apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rt_xv]. lia.
- do 4 apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd rt_xv]. lia.
Qed.

(* a one-byte field of a region of a run's end state *)
Lemma wb10c_field1 : forall {fx : YK11.FPState} E ss ms (H : word -> bool) i n lo hi wlo whi cs b e v,
  st_ok rsegs E ss (restrict H ms) ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk 0 (CVal 1 e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 256 ->
  val_mem rsegs (mrestrict H (ms_mem ms)) b 1 v.
Proof.
intros fx E ss ms H i n lo hi wlo whi cs b e v HS Hi Hn Hc He Hv.
pose proof (rtsb_region_nth E ss ms i _ H HS Hi) as Hr.
pose proof (rtsb_chunks E (mrestrict H (ms_mem ms)) n b cs lo hi wlo whi Hr Hn _ Hc) as Hck.
replace b with (b + 0) by lia.
exact (val_of_chunk_ok rsegs E (mrestrict H (ms_mem ms)) b 0 1%N e v Hck He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

(* the block after the store of the corruption's byte kk *)
Lemma wb10c_img_next : forall {fx : YK11.FPState} {rc : YM05.RunCeil}
  (cx : rsb_scx rsegs) W2 mem2 mem3 sh ps off bs kk (y : byte),
  rsb_wf sh ps -> 8 <= off -> (kk < length bs)%nat -> off + Z.of_nat (length bs) <= rsb_plen sh ps ->
  rsb_pp_at rsegs cx W2 mem2 (rsb_img_corr sh ps off bs (Z.of_nat kk)) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (q_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  (forall a, q_pp (x_e cx) <= a < q_pp (x_e cx) + PP_SIZE -> a <> q_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  firstn (S kk) bs = firstn kk bs ++ [y] ->
  rsb_pp_at rsegs cx W2 mem3 (rsb_img_corr sh ps off bs (Z.of_nat (S kk))).
Proof.
intros fx rc cx W2 mem2 mem3 sh ps off bs kk y Hwf Hoff Hk Hob Hpp Hv HK Hfs.
destruct (wb10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & _).
unfold rsb_plen in Hob.
unfold rsb_pp_at, rsb_img_corr in *. rewrite Nat2Z.id in *. rewrite Hfs.
assert (Hl : length (firstn kk bs) = kk) by (rewrite length_firstn; lia).
rewrite <- (wb10_img_step sh ps off (firstn kk bs) y ltac:(lia) ltac:(rewrite Hl; lia)).
rewrite Hl. rewrite <- (wb10c_le1 y).
set (IMG := pp_image (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) (firstn kk bs))
  (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))
  (ents (PodRec sh ps None)) false) in *.
assert (HLl : Z.of_nat (length IMG) = PP_SIZE).
{ apply length_pp_image; [| exact HW3 | exact HW4].
  rewrite length_overwrite; [rewrite HW2; unfold POD_BUF_MAX; lia | rewrite Hl; lia]. }
unfold PP_SIZE in HLl.
apply (rtmb_bytes_store rsegs (w_H W2) mem2 (w_H W2) mem3 (q_pp (x_e cx)) _ (Z.to_nat off + kk) 1 (bv_unsigned y) Hpp).
- replace (q_pp (x_e cx) + Z.of_nat (Z.to_nat off + kk)) with (q_pp (x_e cx) + off + Z.of_nat kk) by lia. exact Hv.
- lia.
- intros z Hz Hn. apply HK; [unfold PP_SIZE; lia | lia].
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* What one turn of the loop leaves, read off the turn's end: the journal clauses, the post cuts' values (with the
   R list's cell R+0x108 and a6), the frame's shadow and the block with one more corruption byte. *)
Lemma wb10c_turn_common : forall (cx : rsb_scx rsegs) rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    sh ps off bs cnt r r' (y : byte),
  rsb_pre rsegs B cx ->
  rsb_cut_R rsegs B MT cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall n : Z, In n [2; 3; 4; 8; 9; 19; 20; 7; 24; 16] ->
     getr regs3 (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> q_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (q_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  skipn kk bs = y :: fst (fuzz_u8s (length bs - S kk) r') ->
  rsb_core rsegs B MT cx (rsb_E1 rsegs cx) ly2 S2 W2 regs3 mem3 md3 /\
  rsb_at_cx rsegs cx W2 mem3 regs3 (rsb_L_post rsegs cx) /\
  rt_at rsegs (w_H W2) mem3 regs3 (x_e cx) (LCell XR 0x108) (Z.lnot (q_pp (x_e cx))) /\
  getr regs3 (Z_to_bv 5 16) = w64 1 /\
  rsb_fsh_at rsegs cx W2 mem3 rsb_P0 /\
  rsb_pp_at rsegs cx W2 mem3 (rsb_img_corr sh ps off bs (Z.of_nat (S kk))) /\
  (kk < length bs)%nat /\ skipn (S kk) bs = fst (fuzz_u8s (length bs - S kk) r').
Proof.
intros cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y HP HR HJ3 Hio3 Hregs HK Hv Hsk.
destruct HR as (HC & HL & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Htie & Hcw & Hkk & Hkb & Hskip).
destruct (wb10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (wb10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
destruct (wb10_R_bounds B cx HP) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7 & RB8).
destruct (wb10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & _).
pose proof Hcw as (Hoff & Hob & Hb7 & Hcnt & Hbmin). unfold rsb_plen in Hob, Hbmin.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hkl : (kk < length bs)%nat).
{ destruct (Nat.lt_ge_cases kk (length bs)) as [H|H]; [exact H|]. rewrite skipn_all2 in Hsk by exact H. discriminate. }
destruct (wb10c_skipn_cons bs kk y _ Hsk) as [Hfs Hss].
assert (Hnp : forall a, q_R (x_e cx) - T_SEG_STK <= a -> a <> q_pp (x_e cx) + off + Z.of_nat kk).
{ intros a Ha. unfold T_SEG_STK, ASTACK in *. lia. }
assert (Hcell : forall o i, 0 <= o < 0x220 -> 0 <= i < 8 ->
  aview rsegs (w_H W2) mem3 (q_R (x_e cx) + o + i) = aview rsegs (w_H W2) mem2 (q_R (x_e cx) + o + i)).
{ intros o i Ho Hi. apply HK; [unfold T_SEG_STK, ASTACK in *; lia | apply Hnp; unfold T_SEG_STK, ASTACK; lia]. }
pose proof HL as HLx. unfold rsb_at_cx, rsb_at in HLx. apply Forall_app in HLx. destruct HLx as [HLp HLt].
apply Forall_cons_iff in HLt as [H108 HLt].
do 5 (apply Forall_cons_iff in HLt as [_ HLt]).
apply Forall_cons_iff in HLt as [H16 _].
cbn [fst snd] in H108. cbn [fst snd rt_at] in H16.
split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Hkl | exact Hss]]]]]]].
- apply (wb10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    (fun a => a = q_pp (x_e cx) + off + Z.of_nat kk) HC HJ3).
  + intros rr Hr. apply Hregs. destruct Hr as [->|[->| ->]]; cbn; tauto.
  + exact Hio3.
  + intros a Ha Hn. exact (HK a Ha Hn).
  + intros a ->. right. unfold PP_SIZE. lia.
- apply (rtmb_atl_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 (x_e cx) _ HLp).
  intros f Hf. unfold rsb_L_post, rsb_Hc in Hf. cbv zeta in Hf. cbn [app] in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst rtmb_keeps rt_xv];
    first [ (apply Hregs; cbn; tauto) | (intros i Hi; apply Hcell; lia) ] |]).
  destruct Hf.
- apply (rtmb_at_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 (x_e cx) _ _ H108).
  cbn [rtmb_keeps rt_xv]. intros i Hi. apply Hcell; lia.
- rewrite (Hregs 16 ltac:(cbn; tauto)). exact H16.
- apply (rtmb_fsh_kept rsegs (w_H W2) mem2 (w_H W2) mem3 (q_F (x_e cx)) rsb_P0 Hfsh).
  intros i Hi. change (Z.of_nat (length rsb_P0)) with 88 in Hi.
  pose proof (Z.div_pos (q_F (x_e cx)) 8 ltac:(lia)). assert (q_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  pose proof (wb10_shadow_not_pp (q_pp (x_e cx)) (q_F (x_e cx)) i Happ HF3 ltac:(lia)) as Hs.
  apply HK; [unfold shadow_addr, SHADOW_OFF; lia | unfold PP_SIZE in Hs; lia].
- apply (wb10c_img_next cx W2 mem2 mem3 sh ps off bs kk y Hwf Hoff Hkl Hob Hpp Hv); [| exact Hfs].
  intros a Ha Hn. apply HK; [unfold PP_SIZE in Ha; lia | exact Hn].
Qed.

Lemma wb10c_finish_R : forall (cx : rsb_scx rsegs) rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    sh ps off bs cnt r r' (y : byte),
  rsb_pre rsegs B cx ->
  rsb_cut_R rsegs B MT cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall n : Z, In n [2; 3; 4; 8; 9; 19; 20; 7; 24; 16] ->
     getr regs3 (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> q_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (q_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  skipn kk bs = y :: fst (fuzz_u8s (length bs - S kk) r') ->
  rsb_suffix rest r' ->
  getr regs3 (Z_to_bv 5 13) = w64 (Z.of_nat (S kk)) ->
  getr regs3 (Z_to_bv 5 12) = w64 (cnt - Z.of_nat (S kk)) ->
  getr regs3 (Z_to_bv 5 14) = w64 off ->
  getr regs3 (Z_to_bv 5 10) = w64 (rsb_cur rsegs cx rest r') ->
  getr regs3 (Z_to_bv 5 15) = w64 (Z.of_nat (length r')) ->
  Z.of_nat (S kk) < cnt ->
  rsb_cut_R rsegs B MT cx sh ps rest r' off bs cnt (Z.of_nat (S kk)) ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y HP HR HJ3 Hio3 Hregs HK Hv Hsk Hsuf'
  R13 R12 R14 R10 R15 Hlt.
destruct (wb10c_turn_common cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y
  HP HR HJ3 Hio3 Hregs HK Hv Hsk) as (Hcore & HLp & H108 & H16 & Hfsh & Hpp & Hkl & Hss).
destruct HR as (_ & _ & _ & _ & Hin & _ & Hwf & Hlen & Htie & Hcw & _ & _ & _).
split; [exact Hcore|]. split.
{ unfold rsb_at_cx, rsb_at in *. apply Forall_app. split; [exact HLp|].
  apply Forall_cons; [exact H108|].
  repeat (apply Forall_cons; [cbn [fst snd rt_at]; assumption |]). apply Forall_nil. }
split; [exact Hfsh|]. split; [exact Hpp|]. split; [exact Hin|]. split; [exact Hsuf'|]. split; [exact Hwf|].
split; [exact Hlen|]. split; [exact Htie|]. split; [exact Hcw|]. split; [lia|]. split; [lia|].
rewrite Nat2Z.id. exact Hss.
Qed.

Lemma wb10c_finish_RT : forall (cx : rsb_scx rsegs) rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    sh ps off bs cnt r r' (y : byte),
  rsb_pre rsegs B cx ->
  rsb_cut_R rsegs B MT cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall n : Z, In n [2; 3; 4; 8; 9; 19; 20; 7; 24; 16] ->
     getr regs3 (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> q_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (q_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  skipn kk bs = y :: fst (fuzz_u8s (length bs - S kk) r') ->
  rsb_suffix rest r' ->
  length bs = S kk ->
  rsb_cut_RT rsegs B MT cx sh ps off bs rest r' ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y HP HR HJ3 Hio3 Hregs HK Hv Hsk Hsuf'
  Hbl.
destruct (wb10c_turn_common cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y
  HP HR HJ3 Hio3 Hregs HK Hv Hsk) as (Hcore & HLp & _ & _ & Hfsh & Hpp & Hkl & Hss).
destruct HR as (_ & _ & _ & _ & Hin & _ & Hwf & Hlen & Htie & Hcw & _ & _ & _).
destruct Hcw as (Hoff & Hob & Hb7 & _).
split; [exact Hcore|]. split; [exact HLp|]. split; [exact Hfsh|]. split; [rewrite Hbl; exact Hpp|].
split; [exact Hin|]. split; [exact Hsuf'|]. split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Htie|].
split; [exact Hoff|]. split; [exact Hob | exact Hb7].
Qed.

Theorem wb10_corr : rsb_piece_W10_corr_stmt rsegs B MT.
Proof.
unfold rsb_piece_W10_corr_stmt. intros cx POST rest kk Hst HR1 HRT.
unfold rsb_from_R. intros ly2 S2 W2 regs2 mem2 md2 sh ps r off bs cnt HR.
destruct Hst as (HP & Hfsh0 & _ & _).
pose proof HR as HRc.
destruct HR as (HC & HL & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Htie & Hcw & Hkk & Hkb & Hskip).
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (wb10_ctx B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR16 & HRS & HSTK & Hceil & H47 & HAR).
destruct (wb10_F_ctx B cx HP) as (HF1 & HF2 & HF3).
destruct (wb10_R_bounds B cx HP) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7 & RB8).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (wb10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
destruct Hcw as (Hoff & Hob & Hb7 & Hcnt & Hbmin).
unfold rsb_plen in Hob, Hbmin.
pose proof Hin as (Hleft & _ & _ & _ & Hamr & Hsrc0 & Hsrc63 & Hindisj).
destruct Hsuf as (j & Hj & Hrj).
set (pp := q_pp (x_e cx)) in *.
set (Lp := Z.of_nat (length (pc_buf (PbCut sh ps None)))) in *.
set (enc := pod_encode (PodRec sh ps None)) in *.
rewrite Nat2Z.id in Hskip.
assert (Hbl : length (overwrite enc (Z.to_nat off) (firstn kk bs)) = length (pc_buf (PbCut sh ps None))).
{ rewrite length_overwrite; [exact HW2|]. rewrite length_firstn. lia. }
assert (HLv : val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 Lp).
{ unfold rsb_pp_at, rsb_img_corr in Hpp. rewrite Nat2Z.id in Hpp.
  pose proof (rtmb_pp_len rsegs (overwrite enc (Z.to_nat off) (firstn kk bs)) _ _ _ _ _
    ltac:(rewrite Hbl; unfold POD_BUF_MAX; lia) HW3 HW4 (w_H W2) mem2 pp Hpp) as X.
  rewrite Hbl in X. exact X. }
pose proof HL as HL0.
unfold rsb_at_cx, rsb_at, rsb_L_post, rsb_Hc in HL. cbv zeta in HL. cbn [app] in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (P8 & P9 & P19 & P20 & P7 & P24 & C8 & C10 & C50 & C60 & Cf8 & C120 & C138 & C168 & C170 &
  H48 & H30 & H38 & H40 & H18 & H148 & C108 & P13 & P12 & P14 & P10 & P15 & P16 & _).
cbn [fst snd rt_at] in P8, P9, P19, P20, P7, P24, P13, P12, P14, P10, P15, P16.
cbn [fst snd rt_at rt_xv] in C108, C168, C170.
pose proof HC as (HJ & _).
change (q_pp (x_e cx)) with pp in P7, C168, C170.
set (cur := rsb_cur rsegs cx rest r) in P10.
assert (Hcur : cur = q_src (x_e cx) + Z.of_nat j).
{ subst cur. unfold rsb_cur. rewrite Hrj, length_skipn. lia. }
assert (Hrl : Z.of_nat (length r) = Z.of_nat (length rest) - Z.of_nat j) by (rewrite Hrj, length_skipn; lia).
assert (HK47 : q_src (x_e cx) + q_left (x_e cx) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
set (src := q_src (x_e cx)) in Hcur, HK47, Hamr, Hsrc0, Hsrc63, Hindisj.
set (kz := Z.of_nat kk) in P13, P12, Hkk, Hkb, Hpp.
(* the three real-frame cells the loop reads, as unsigned values *)
assert (Hpp47 : 0 <= pp + 0x4000 < 2 ^ 47) by lia.
assert (Hsa : 0 <= shadow_addr (pp + 0x4000) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (pp + 0x4000) 8 ltac:(lia)).
  assert ((pp + 0x4000) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia). lia. }
rewrite (Z.mod_small (shadow_addr (pp + 0x4000))) in C170 by exact Hsa.
rewrite (Z.mod_small pp) in C168 by lia.
rewrite (wb10c_lnot_mod pp ltac:(lia)) in C108.
remember (Ereg regs2 [Z_to_bv 64 Lp; Z_to_bv 64 (off + kz); Z_to_bv 64 (pp + off + kz);
  Z_to_bv 64 (match r with x :: _ => bv_unsigned x | [] => 0 end); Z_to_bv 64 pp;
  Z_to_bv 64 (2 ^ 64 - 1 - pp)]) as E eqn:HE.
assert (E7 : ew E 7 = Z_to_bv 64 (pp + 0x4000)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 7 (Z_to_bv 5 7) eq_refl); exact P7).
assert (E9 : ew E 9 = Z_to_bv 64 (q_R (x_e cx))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl); exact P9).
assert (E10 : ew E 10 = Z_to_bv 64 cur) by (subst E; rewrite (ew_Ereg_nat regs2 _ 10 (Z_to_bv 5 10) eq_refl); exact P10).
assert (E12 : ew E 12 = Z_to_bv 64 (cnt - kz)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 12 (Z_to_bv 5 12) eq_refl); exact P12).
assert (E13 : ew E 13 = Z_to_bv 64 kz) by (subst E; rewrite (ew_Ereg_nat regs2 _ 13 (Z_to_bv 5 13) eq_refl); exact P13).
assert (E14 : ew E 14 = Z_to_bv 64 off) by (subst E; rewrite (ew_Ereg_nat regs2 _ 14 (Z_to_bv 5 14) eq_refl); exact P14).
assert (E15 : ew E 15 = Z_to_bv 64 (Z.of_nat (length r))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 15 (Z_to_bv 5 15) eq_refl); exact P15).
assert (E16 : ew E 16 = Z_to_bv 64 1) by (subst E; rewrite (ew_Ereg_nat regs2 _ 16 (Z_to_bv 5 16) eq_refl); exact P16).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs2 _ 20 (Z_to_bv 5 20) eq_refl); exact P20).
assert (E32 : ew E 32 = Z_to_bv 64 Lp) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (off + kz)) by (subst E; exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (pp + off + kz)) by (subst E; exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (match r with x :: _ => bv_unsigned x | [] => 0 end))
  by (subst E; exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 pp) by (subst E; exact (ew_Ereg_extra regs2 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (2 ^ 64 - 1 - pp)) by (subst E; exact (ew_Ereg_extra regs2 _ 5)).
assert (HB : U E WB10Bx = SHADOW_OFF) by exact (wb10_U_atom E 20 SHADOW_OFF E20 ltac:(unfold SHADOW_OFF; lia)).
assert (HoffL : off + kz <= Lp) by lia.
pose proof HL0 as HLpost. unfold rsb_at_cx, rsb_at in HLpost. apply Forall_app in HLpost. destruct HLpost as [HLpost _].
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 Lp; Z_to_bv 64 (off + kz); Z_to_bv 64 (pp + off + kz);
  Z_to_bv 64 (match r with x :: _ => bv_unsigned x | [] => 0 end); Z_to_bv 64 pp;
  Z_to_bv 64 (2 ^ 64 - 1 - pp)]) E)
  by (rewrite HE; split; [intros; reflexivity | reflexivity]).
assert (Himgl : forall k, (k <= length bs)%nat -> Z.of_nat (length (rsb_img_corr sh ps off bs (Z.of_nat k))) = PP_SIZE).
{ intros k Hk. unfold rsb_img_corr. fold enc. apply length_pp_image; [| exact HW3 | exact HW4].
  rewrite length_overwrite; [rewrite HW2; unfold POD_BUF_MAX; lia|]. rewrite length_firstn. lia. }
(* the regions every state of the turn starts with: the length word (t2), the two real-frame cell ranges (s1) *)
assert (HRL : region_ok rsegs E (mrestrict (w_H W2) mem2)
  (YP09.mkRegion (Some 7%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))])).
{ apply (rtmb_ro_region rsegs E (w_H W2) mem2 7 (pp + 0x4000)).
  - rewrite E7. rewrite unsigned_lit_small by lia. reflexivity.
  - lia. - lia.
  - constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ (pp + 0x4000) 0 8 (SOff 32 0) Lp).
    + exact (wb10_den_atom _ 32 Lp E32). + cbn. lia. + cbn. lia. + rewrite Z.add_0_r. exact HLv. }
assert (HRA : region_ok rsegs E (mrestrict (w_H W2) mem2)
  (YP09.mkRegion (Some 9%nat) 0x108 0x110 0 0 [YP09.mkChunk 0x108 (CVal 8 (SOff 37 0))])).
{ apply (rtmb_ro_region rsegs E (w_H W2) mem2 9 (q_R (x_e cx))).
  - rewrite E9. rewrite unsigned_lit_small by lia. reflexivity.
  - lia. - lia.
  - constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ (q_R (x_e cx)) 0x108 8 (SOff 37 0) (2 ^ 64 - 1 - pp)).
    + exact (wb10_den_atom _ 37 _ E37). + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia. + cbn. lia.
    + exact C108. }
assert (HRB : region_ok rsegs E (mrestrict (w_H W2) mem2)
  (YP09.mkRegion (Some 9%nat) 0x168 0x178 0 0
    [YP09.mkChunk 0x168 (CVal 8 (SOff 36 0));
     YP09.mkChunk 0x170 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 7 0) (SLit 3)) (SOff 20 0)))])).
{ apply (rtmb_ro_region rsegs E (w_H W2) mem2 9 (q_R (x_e cx))).
  - rewrite E9. rewrite unsigned_lit_small by lia. reflexivity.
  - lia. - lia.
  - constructor; [|constructor; [|constructor]].
    + apply (chunk_ok_val rsegs _ _ (q_R (x_e cx)) 0x168 8 (SOff 36 0) pp).
      * exact (wb10_den_atom _ 36 _ E36). * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia. * cbn. lia.
      * exact C168.
    + apply (chunk_ok_val rsegs _ _ (q_R (x_e cx)) 0x170 8 _ (shadow_addr (pp + 0x4000))).
      * exact (wb10_den_sh E 7 20 (pp + 0x4000) E7 Hpp47 E20).
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia. * cbn. lia.
      * exact C170. }
destruct (Z_le_gt_dec Lp (off + kz)) as [Hge|Hlt].
{ (* off + kk reaches the length: the corruption ends with the bytes written so far *)
  assert (Hkbs : kz = Z.of_nat (length bs)) by lia.
  assert (HS : st_ok rsegs E (mkSS 0x82960 sr_atoms
    [YP09.mkRegion (Some 7%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
     YP09.mkRegion (Some 9%nat) 0x168 0x178 0 0
       [YP09.mkChunk 0x168 (CVal 8 (SOff 36 0));
        YP09.mkChunk 0x170 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 7 0) (SLit 3)) (SOff 20 0)))]] None
    (mkFacts [(7%nat, mkAF 4096 WB10_HI 4); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0);
              (33%nat, mkAF 8 5447 0); (12%nat, mkAF 1 7 0); (13%nat, mkAF 0 6 0); (14%nat, mkAF 8 5440 0)]
       [mkAC BC_GEU (SOff 33 0) (SOff 32 0)]
       [(SAlu ALU_ADD (SOff 13 0) (SOff 14 0), SOff 33 0)]))
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x82960) mem2 (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [exact HRL | constructor; [exact HRB | constructor]].
    - apply pairwise_disjoint_of_extents.
      cbn [map zpairwise_disjoint zall_disjoint]. unfold YA0q.extent_of_region, zdisj.
      cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi fst snd].
      rewrite E7, E9, !unsigned_lit_small by lia.
      unfold T_SEG_STK, ASTACK in *. repeat split; lia.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok].
      refine (conj _ (conj (conj _ I) (conj _ I))).
      + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E7, E20, E32, E33, E12, E13, E14.
        rewrite !unsigned_lit_small by (unfold SHADOW_OFF, WB10_HI; lia).
        repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, WB10_HI; lia);
        try (rewrite Z.pow_0_r; apply Z.mod_1_r).
        change (2 ^ 4) with 16. rewrite Z.add_mod by lia. rewrite Hal. reflexivity.
      + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, (wb10_U_atom _ 33 _ E33 ltac:(lia)), (wb10_U_atom _ 32 _ E32 ltac:(lia)).
        apply negb_true_iff, Z.ltb_ge. lia.
      + rewrite (wb10c_den_add _ 13 14 kz off E13 ltac:(lia) E14 ltac:(lia)), (wb10_den_atom _ 33 _ E33). f_equal. lia. }
  assert (SHOK : sh_ok rsegs WB10Bx [mkSHE 7 0 8] E (mrestrict (w_H W2) mem2)).
  { constructor; [|constructor].
    apply (wb10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 7 0 8 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (wb10_U_atom E 7 _ E7 ltac:(lia)); lia. }
  unfold cfg_at. change (w64 RSB_R) with (Z_to_bv 64 0x82960).
  aj_run_to_tok wb10_tbl_ok HS HJ SHOK WB10Bspan 0x829fc.
  { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  assert (HK : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha. apply (wb10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
    destruct Hr as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; lia. }
  pose proof (regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 11; Z_to_bv 5 17] HS HAE ltac:(vm_compute; reflexivity)) as RK.
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps off bs r).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
  - apply (wb10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun _ => False) HC HJ).
    + intros rr Hr. apply RK; [destruct Hr as [->|[->| ->]]; vm_compute; discriminate |].
      apply wb10_notin. destruct Hr as [->|[->| ->]]; vm_compute; reflexivity.
    + apply same_io_wvb.
    + intros a Ha _. exact (HK a Ha).
    + intros a [].
  - apply (rtmb_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _ HLpost).
    intros f Hf. unfold rsb_L_post, rsb_Hc in Hf. cbv zeta in Hf. cbn [app] in Hf.
    repeat (destruct Hf as [<-|Hf]; [cbn [fst rtmb_keeps rt_xv];
      first [ (apply RK; [vm_compute; discriminate | apply wb10_notin; vm_compute; reflexivity])
            | (intros i Hi; apply HK; lia) ] |]).
    destruct Hf.
  - apply (rtmb_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (q_F (x_e cx)) rsb_P0 Hfsh).
    intros i Hi. apply HK. change (Z.of_nat (length rsb_P0)) with 88 in Hi.
    pose proof (Z.div_pos (q_F (x_e cx)) 8 ltac:(lia)). assert (q_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
    unfold shadow_addr, SHADOW_OFF. lia.
  - rewrite <- Hkbs. apply (rtmb_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) pp _ Hpp).
    assert (X : Z.of_nat (length (rsb_img_corr sh ps off bs kz)) = PP_SIZE) by exact (Himgl kk ltac:(lia)).
    intros y Hy. rewrite X in Hy. apply HK. unfold PP_SIZE in Hy. lia.
  - exact Hin.
  - exists j. split; [exact Hj | exact Hrj].
  - exact Hwf.
  - exact Hlen.
  - exact Htie.
  - exact Hoff.
  - unfold rsb_plen. exact Hob.
  - exact Hb7. }
(* the store's region inside the first block *)
assert (HRS34 : region_ok rsegs E (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some 34%nat) 0 1 0 1 [])).
{ apply (rtmb_rw_region rsegs _ (w_H W2) mem2 34 (pp + off + kz)).
  - rewrite E34. rewrite unsigned_lit_small by lia. reflexivity.
  - lia. - lia.
  - intros o Ho. apply Hpres. lia.
  - constructor. }
destruct r as [|x r1].
{ (* no input left: the byte is 0 *)
  cbv beta iota in E35, HE, HAE.
  assert (Hkl : (kk < length bs)%nat) by (unfold kz in *; lia).
  assert (Hsk : skipn kk bs = Z_to_bv 8 0 :: fst (fuzz_u8s (length bs - S kk) [])).
  { rewrite Hskip. replace (length bs - kk)%nat with (S (length bs - S kk)) by lia. apply wb10_fuzz_u8s_nil. }
  assert (Hsuf' : rsb_suffix rest []) by (exists j; split; [exact Hj | exact Hrj]).
  assert (Hy0 : bv_unsigned (Z_to_bv 8 0 : byte) = 0) by reflexivity.
  change (Z.of_nat (length (@nil byte))) with 0 in E15.
assert (HS : st_ok rsegs E (mkSS 0x82960 sr_atoms
  [YP09.mkRegion (Some 34%nat) 0 1 0 1 [];
   YP09.mkRegion (Some 7%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some 9%nat) 0x108 0x110 0 0 [YP09.mkChunk 0x108 (CVal 8 (SOff 37 0))];
   YP09.mkRegion (Some 9%nat) 0x168 0x178 0 0
     [YP09.mkChunk 0x168 (CVal 8 (SOff 36 0));
      YP09.mkChunk 0x170 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 7 0) (SLit 3)) (SOff 20 0)))]] None
  (mkFacts [(7%nat, mkAF 4096 WB10_HI 4); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0);
            (33%nat, mkAF 8 5440 0); (34%nat, mkAF 4096 WB10_HI 0);
            (37%nat, mkAF 9223372036854775808 18446744073709551615 0);
            (15%nat, mkAF 0 0 0); (12%nat, mkAF 1 7 0);
            (13%nat, mkAF 0 6 0); (14%nat, mkAF 8 5440 0)]
     [mkAC BC_LTU (SOff 33 0) (SOff 32 0); mkAC BC_EQ (SOff 15 0) (SLit 0);
      mkAC BC_EQ (SAlu ALU_SRL (SOff 33 0) (SLit 14)) (SLit 0)]
     [(SAlu ALU_ADD (SOff 13 0) (SOff 14 0), SOff 33 0); (SAlu ALU_ADD (SOff 36 0) (SOff 33 0), SOff 34 0)]))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x82960) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [exact HRS34 | constructor; [exact HRL | constructor; [exact HRA | constructor; [exact HRB | constructor]]]].
  - apply pairwise_disjoint_of_extents.
    cbn [map zpairwise_disjoint zall_disjoint]. unfold YA0q.extent_of_region, zdisj.
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi fst snd].
    rewrite E34, E7, E9, !unsigned_lit_small by lia.
    unfold T_SEG_STK, ASTACK in *. repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok].
    refine (conj _ (conj (conj _ (conj _ (conj _ I))) (conj _ (conj _ I)))).
    + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E7, E20, E32, E33, E34, E37, E15, E12, E13, E14.
      rewrite !unsigned_lit_small by (unfold SHADOW_OFF, WB10_HI; lia).
      repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, WB10_HI; lia);
      try (rewrite Z.pow_0_r; apply Z.mod_1_r).
      change (2 ^ 4) with 16. rewrite Z.add_mod by lia. rewrite Hal. reflexivity.
    + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, (wb10_U_atom _ 33 _ E33 ltac:(lia)), (wb10_U_atom _ 32 _ E32 ltac:(lia)).
      apply Z.ltb_lt. lia.
    + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, (wb10_U_atom _ 15 0 E15 ltac:(lia)), U_lit by lia.
      reflexivity.
    + exact (wb10c_shr14 _ 33 (off + kz) E33 ltac:(lia)).
    + rewrite (wb10c_den_add _ 13 14 kz off E13 ltac:(lia) E14 ltac:(lia)), (wb10_den_atom _ 33 _ E33). f_equal. lia.
    + rewrite (wb10c_den_add _ 36 33 pp (off + kz) E36 ltac:(lia) E33 ltac:(lia)), (wb10_den_atom _ 34 _ E34). f_equal. lia. }
(* the shadow entries: the store target and the length word inside the first block *)
assert (SHOK : sh_ok rsegs WB10Bx [mkSHE 34 0 1; mkSHE 7 0 8] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor; [|constructor]].
  - apply (wb10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 34 0 1 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (wb10_U_atom E 34 _ E34 ltac:(lia)); lia.
  - apply (wb10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 7 0 8 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (wb10_U_atom E 7 _ E7 ltac:(lia)); lia. }
unfold cfg_at. change (w64 RSB_R) with (Z_to_bv 64 0x82960).
aj_run_to_tok wb10_tbl_ok HS HJ SHOK WB10Bspan 0x829fc.
{ cbn [ss_mem].
  eapply (wb10_awr_cons_pp E _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
    [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
  { rewrite E34. apply unsigned_lit_small. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_nil. }
rename ms into msA. rename HF into HFa. rename HFr into HFra. rename HG into HGa.
srr_branch_tok wb10_tbl_ok HS SHOK WB10Bspan.
- (* a2 - 1 <> 0: the next turn *)
  aj_run_to_tok wb10_tbl_ok HS HJ SHOK WB10Bspan 0x82960.
  { cbn [ss_mem add_cond].
    eapply (wb10_awr_cons_pp _ _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
      [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
    { rewrite ?ew_ewset_other by lia. rewrite E34. apply unsigned_lit_small. lia. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_nil. }
  rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 12 (cnt - kz) (-1)) in Hc;
    [| rewrite !ew_ewset_other by lia; exact E12 | lia | lia].
  rewrite U_lit in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (HKAB : forall a, 0 <= a < 2 ^ 64 -> a <> pp + off + kz ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. transitivity (aview rsegs (w_H W2) (ms_mem msA) a).
    - apply (wb10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem add_cond] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia|lia|lia].
      rewrite !ew_ewset_other in Hrb by lia. rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia.
    - apply (wb10_frame_kept _ _ _ _ _ HFra a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia|lia|lia].
      rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia. }
  assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned (Z_to_bv 8 0 : byte))).
  { rewrite Hy0.
    apply (wb10c_field1 _ _ ms (w_H W2) 0%nat 34%nat 0 1 0 1 _ (pp + off + kz) (SLit 0) 0 HS eq_refl);
      [ rewrite !ew_ewset_other by lia; rewrite E34; apply unsigned_lit_small; lia
      | left; reflexivity | reflexivity | lia ]. }
  pose proof (regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 5; Z_to_bv 5 6; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 17]
    HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
  assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 20; 7; 24; 16] ->
    getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn];
      [apply RK; [vm_compute; discriminate | apply wb10_notin; vm_compute; reflexivity] |]).
    destruct Hn. }
  assert (R13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 (Z.of_nat (S kk))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 13) HS). wb10_sr_eval.
    rewrite (wb10_den_off _ 13 kz 1) by (rewrite !ew_ewset_other by lia; exact E13).
    f_equal. unfold kz. lia. }
  assert (R12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (cnt - Z.of_nat (S kk))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 12) HS). wb10_sr_eval.
    rewrite (wb10_den_off _ 12 (cnt - kz) (-1)) by (rewrite !ew_ewset_other by lia; exact E12).
    f_equal. unfold kz. lia. }
  assert (R14 : getr (ms_regs ms) (Z_to_bv 5 14) = w64 off).
  { rewrite RK; [exact P14 | vm_compute; discriminate | apply wb10_notin; vm_compute; reflexivity]. }
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (rsb_cur rsegs cx rest [])).
  { rewrite RK; [exact P10 | vm_compute; discriminate | apply wb10_notin; vm_compute; reflexivity]. }
  assert (R15 : getr (ms_regs ms) (Z_to_bv 5 15) = w64 (Z.of_nat (length (@nil byte)))).
  { rewrite RK; [exact P15 | vm_compute; discriminate | apply wb10_notin; vm_compute; reflexivity]. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HR1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps [] off bs cnt).
  apply (wb10c_finish_R cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt [] [] (Z_to_bv 8 0)
    HP HRc HJ ltac:(eapply same_io_trans; apply same_io_wvb) Hregs HKAB Hv Hsk Hsuf' R13 R12 R14 R10 R15).
  unfold kz in *. lia.
- (* a2 - 1 = 0: the count is done *)
  aj_run_to_tok wb10_tbl_ok HS HJ SHOK WB10Bspan 0x829fc.
  { cbn [ss_mem add_cond].
    eapply (wb10_awr_cons_pp _ _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
      [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
    { rewrite ?ew_ewset_other by lia. rewrite E34. apply unsigned_lit_small. lia. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_nil. }
  rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 12 (cnt - kz) (-1)) in Hc;
    [| rewrite !ew_ewset_other by lia; exact E12 | lia | lia].
  rewrite U_lit in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (HKAB : forall a, 0 <= a < 2 ^ 64 -> a <> pp + off + kz ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. transitivity (aview rsegs (w_H W2) (ms_mem msA) a).
    - apply (wb10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem add_cond] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia|lia|lia].
      rewrite !ew_ewset_other in Hrb by lia. rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia.
    - apply (wb10_frame_kept _ _ _ _ _ HFra a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb; [|lia|lia|lia].
      rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia. }
  assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned (Z_to_bv 8 0 : byte))).
  { rewrite Hy0.
    apply (wb10c_field1 _ _ ms (w_H W2) 0%nat 34%nat 0 1 0 1 _ (pp + off + kz) (SLit 0) 0 HS eq_refl);
      [ rewrite !ew_ewset_other by lia; rewrite E34; apply unsigned_lit_small; lia
      | left; reflexivity | reflexivity | lia ]. }
  pose proof (regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 5; Z_to_bv 5 6; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 17]
    HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
  assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 20; 7; 24; 16] ->
    getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn];
      [apply RK; [vm_compute; discriminate | apply wb10_notin; vm_compute; reflexivity] |]).
    destruct Hn. }
  assert (Hbs : length bs = S kk) by (unfold kz in *; lia).
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps off bs []).
  exact (wb10c_finish_RT cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt [] [] (Z_to_bv 8 0)
    HP HRc HJ ltac:(eapply same_io_trans; apply same_io_wvb) Hregs HKAB Hv Hsk Hsuf' Hbs).
}
cbv beta iota in E35, HE, HAE.
assert (Hjr : (j < length rest)%nat) by (cbn [length] in Hrl; lia).
assert (Hkl : (kk < length bs)%nat) by (unfold kz in *; lia).
assert (Hsk : skipn kk bs = x :: fst (fuzz_u8s (length bs - S kk) r1)).
{ rewrite Hskip. replace (length bs - kk)%nat with (S (length bs - S kk)) by lia. apply wb10_fuzz_u8s_cons. }
assert (Hsuf' : rsb_suffix rest r1).
{ exists (S j). split; [lia | symmetry; exact (proj2 (wb10c_skipn_cons rest j x r1 (eq_sym Hrj)))]. }
destruct (wb10_input_now B MT cx rest ly2 S2 W2 regs2 mem2 md2 (Z.of_nat j) HP Hin Hfsh0 HC Hfsh ltac:(lia))
  as (Hbyte & Hra).
assert (Hx : val_mem rsegs (mrestrict (w_H W2) mem2) cur 1 (bv_unsigned x)).
{ rewrite Nat2Z.id in Hbyte. rewrite (wb10c_nth_skipn rest j x r1 (eq_sym Hrj)) in Hbyte.
  rewrite Hcur. exact Hbyte. }
pose proof (bv_unsigned_in_range _ x) as Hxr. unfold bv_modulus in Hxr. change (Z.of_N 8) with 8 in Hxr.
destruct (Hindisj cur ltac:(lia)) as (Hns & Hnw & Hnp). unfold PP_SIZE in Hnp.
destruct (wb10c_not_w1 (x_e cx) cur Hnw) as [Hw1 Hw2].
assert (HS : st_ok rsegs E (mkSS 0x82960 sr_atoms
  [YP09.mkRegion (Some 34%nat) 0 1 0 1 [];
   YP09.mkRegion (Some 7%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))];
   YP09.mkRegion (Some 9%nat) 0x108 0x110 0 0 [YP09.mkChunk 0x108 (CVal 8 (SOff 37 0))];
   YP09.mkRegion (Some 9%nat) 0x168 0x178 0 0
     [YP09.mkChunk 0x168 (CVal 8 (SOff 36 0));
      YP09.mkChunk 0x170 (CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 7 0) (SLit 3)) (SOff 20 0)))]] None
  (mkFacts [(7%nat, mkAF 4096 WB10_HI 4); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0);
            (33%nat, mkAF 8 5440 0); (34%nat, mkAF 4096 WB10_HI 0); (35%nat, mkAF 0 255 0);
            (37%nat, mkAF 9223372036854775808 18446744073709551615 0);
            (10%nat, mkAF 1 (2 ^ 47 - 2) 0); (15%nat, mkAF 1 (2 ^ 47) 0); (16%nat, mkAF 1 1 0);
            (12%nat, mkAF 1 7 0); (13%nat, mkAF 0 6 0); (14%nat, mkAF 8 5440 0)]
     [mkAC BC_LTU (SOff 33 0) (SOff 32 0); mkAC BC_EQ (SAlu ALU_SRL (SOff 33 0) (SLit 14)) (SLit 0)]
     [(SAlu ALU_ADD (SOff 13 0) (SOff 14 0), SOff 33 0); (SAlu ALU_ADD (SOff 36 0) (SOff 33 0), SOff 34 0)]))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 0x82960) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [exact HRS34 | constructor; [exact HRL | constructor; [| constructor; [exact HRA | constructor; [exact HRB | constructor]]]]].
    apply (rtmb_ro_region rsegs _ (w_H W2) mem2 10 cur).
    + rewrite E10. rewrite unsigned_lit_small by lia. reflexivity.
    + lia. + lia.
    + constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ cur 0 1 (SOff 35 0) (bv_unsigned x)).
      * exact (wb10_den_atom _ 35 _ E35). * cbn. lia. * cbn. lia. * rewrite Z.add_0_r. exact Hx.
  - apply pairwise_disjoint_of_extents.
    cbn [map zpairwise_disjoint zall_disjoint]. unfold YA0q.extent_of_region, zdisj.
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi fst snd].
    rewrite E34, E7, E10, E9, !unsigned_lit_small by lia.
    unfold T_SEG_STK, ASTACK in *. repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok].
    refine (conj _ (conj (conj _ (conj _ I)) (conj _ (conj _ I)))).
    + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E7, E20, E32, E33, E34, E35, E37, E10, E15, E16, E12, E13, E14.
      rewrite !unsigned_lit_small by (unfold SHADOW_OFF, WB10_HI; lia).
      repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, WB10_HI; lia);
      try (rewrite Z.pow_0_r; apply Z.mod_1_r).
      change (2 ^ 4) with 16. rewrite Z.add_mod by lia. rewrite Hal. reflexivity.
    + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, (wb10_U_atom _ 33 _ E33 ltac:(lia)), (wb10_U_atom _ 32 _ E32 ltac:(lia)).
      apply Z.ltb_lt. lia.
    + exact (wb10c_shr14 _ 33 (off + kz) E33 ltac:(lia)).
    + rewrite (wb10c_den_add _ 13 14 kz off E13 ltac:(lia) E14 ltac:(lia)), (wb10_den_atom _ 33 _ E33). f_equal. lia.
    + rewrite (wb10c_den_add _ 36 33 pp (off + kz) E36 ltac:(lia) E33 ltac:(lia)), (wb10_den_atom _ 34 _ E34). f_equal. lia. }
(* the shadow entries: the store target and the length word inside the first block, the input byte *)
assert (SHOK : sh_ok rsegs WB10Bx [mkSHE 34 0 1; mkSHE 7 0 8; mkSHE 10 0 1] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (wb10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 34 0 1 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (wb10_U_atom E 34 _ E34 ltac:(lia)); lia.
  - apply (wb10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 7 0 8 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact HB | | | lia];
    rewrite (wb10_U_atom E 7 _ E7 ltac:(lia)); lia.
  - apply (wb10c_shent_in E _ 10 src (q_left (x_e cx)) cur Hamr HB (wb10_U_atom E 10 _ E10 ltac:(lia)));
    [lia | lia | rewrite Hcur; exact Hra]. }
unfold cfg_at. change (w64 RSB_R) with (Z_to_bv 64 0x82960).
aj_run_to_tok wb10_tbl_ok HS HJ SHOK WB10Bspan 0x829fc.
{ cbn [ss_mem].
  eapply (wb10_awr_cons_pp E _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
    [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
  { rewrite E34. apply unsigned_lit_small. lia. }
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename ms into msA. rename HF into HFa. rename HFr into HFra. rename HG into HGa.
srr_branch_tok wb10_tbl_ok HS SHOK WB10Bspan.
- (* a2 - 1 <> 0: the next turn *)
  aj_run_to_tok wb10_tbl_ok HS HJ SHOK WB10Bspan 0x82960.
  { cbn [ss_mem add_cond].
    eapply (wb10_awr_cons_pp _ _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
      [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
    { rewrite ?ew_ewset_other by lia. rewrite E34. apply unsigned_lit_small. lia. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 12 (cnt - kz) (-1)) in Hc;
    [| rewrite !ew_ewset_other by lia; exact E12 | lia | lia].
  rewrite U_lit in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (HKAB : forall a, 0 <= a < 2 ^ 64 -> a <> pp + off + kz ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. transitivity (aview rsegs (w_H W2) (ms_mem msA) a).
    - apply (wb10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem add_cond] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb;
        [|lia|lia|lia|lia].
      rewrite !ew_ewset_other in Hrb by lia. rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia.
    - apply (wb10_frame_kept _ _ _ _ _ HFra a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb;
        [|lia|lia|lia|lia].
      rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia. }
  assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned x)).
  { apply (wb10c_field1 _ _ ms (w_H W2) 0%nat 34%nat 0 1 0 1 _ (pp + off + kz) (SOff 35 0) (bv_unsigned x) HS eq_refl);
      [ rewrite !ew_ewset_other by lia; rewrite E34; apply unsigned_lit_small; lia
      | left; reflexivity
      | apply (wb10_den_atom _ 35); rewrite !ew_ewset_other by lia; exact E35
      | lia ]. }
  pose proof (regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 5; Z_to_bv 5 6; Z_to_bv 5 10; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 15;
     Z_to_bv 5 17] HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
  assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 20; 7; 24; 16] ->
    getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn];
      [apply RK; [vm_compute; discriminate | apply wb10_notin; vm_compute; reflexivity] |]).
    destruct Hn. }
  assert (R13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 (Z.of_nat (S kk))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 13) HS). wb10_sr_eval.
    rewrite (wb10_den_off _ 13 kz 1) by (rewrite !ew_ewset_other by lia; exact E13).
    f_equal. unfold kz. lia. }
  assert (R12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (cnt - Z.of_nat (S kk))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 12) HS). wb10_sr_eval.
    rewrite (wb10_den_off _ 12 (cnt - kz) (-1)) by (rewrite !ew_ewset_other by lia; exact E12).
    f_equal. unfold kz. lia. }
  assert (R14 : getr (ms_regs ms) (Z_to_bv 5 14) = w64 off).
  { rewrite RK; [exact P14 | vm_compute; discriminate | apply wb10_notin; vm_compute; reflexivity]. }
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (rsb_cur rsegs cx rest r1)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 10) HS). wb10_sr_eval.
    rewrite (wb10_den_off _ 10 cur 1) by (rewrite !ew_ewset_other by lia; exact E10).
    f_equal. unfold cur, rsb_cur. cbn [length]. lia. }
  assert (R15 : getr (ms_regs ms) (Z_to_bv 5 15) = w64 (Z.of_nat (length r1))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 15) HS). wb10_sr_eval.
    rewrite (wb10_den_off _ 15 (Z.of_nat (length (x :: r1))) (-1)) by (rewrite !ew_ewset_other by lia; exact E15).
    f_equal. cbn [length]. lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HR1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps r1 off bs cnt).
  apply (wb10c_finish_R cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt (x :: r1) r1 x
    HP HRc HJ ltac:(eapply same_io_trans; apply same_io_wvb) Hregs HKAB Hv Hsk Hsuf' R13 R12 R14 R10 R15).
  unfold kz in *. lia.
- (* a2 - 1 = 0: the count is done *)
  aj_run_to_tok wb10_tbl_ok HS HJ SHOK WB10Bspan 0x829fc.
  { cbn [ss_mem add_cond].
    eapply (wb10_awr_cons_pp _ _ _ _ _ _ _ _ _ _ 34%nat (pp + off + kz) pp);
      [reflexivity | | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia |].
    { rewrite ?ew_ewset_other by lia. rewrite E34. apply unsigned_lit_small. lia. }
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 12 (cnt - kz) (-1)) in Hc;
    [| rewrite !ew_ewset_other by lia; exact E12 | lia | lia].
  rewrite U_lit in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (HKAB : forall a, 0 <= a < 2 ^ 64 -> a <> pp + off + kz ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. transitivity (aview rsegs (w_H W2) (ms_mem msA) a).
    - apply (wb10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem add_cond] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb;
        [|lia|lia|lia|lia].
      rewrite !ew_ewset_other in Hrb by lia. rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia.
    - apply (wb10_frame_kept _ _ _ _ _ HFra a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrb;
        [|lia|lia|lia|lia].
      rewrite E34, unsigned_lit_small in Hrb by lia. apply Hn. lia. }
  assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned x)).
  { apply (wb10c_field1 _ _ ms (w_H W2) 0%nat 34%nat 0 1 0 1 _ (pp + off + kz) (SOff 35 0) (bv_unsigned x) HS eq_refl);
      [ rewrite !ew_ewset_other by lia; rewrite E34; apply unsigned_lit_small; lia
      | left; reflexivity
      | apply (wb10_den_atom _ 35); rewrite !ew_ewset_other by lia; exact E35
      | lia ]. }
  pose proof (regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 5; Z_to_bv 5 6; Z_to_bv 5 10; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 15;
     Z_to_bv 5 17] HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
  assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 20; 7; 24; 16] ->
    getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn];
      [apply RK; [vm_compute; discriminate | apply wb10_notin; vm_compute; reflexivity] |]).
    destruct Hn. }
  assert (Hbs : length bs = S kk) by (unfold kz in *; lia).
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps off bs r1).
  exact (wb10c_finish_RT cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt (x :: r1) r1 x
    HP HRc HJ ltac:(eapply same_io_trans; apply same_io_wvb) Hregs HKAB Hv Hsk Hsuf' Hbs).
Qed.
End c.

Print Assumptions wb10_corr.
