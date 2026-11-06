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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgPostCorrB.v, with its module paths, module names and numbers changed; 554 of its 826 lines of code are new or changed and 534 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPostCorr.v at 01f4363fe7d, for image B of
   reac-pw/fuzz_headamp: w10_ -> hw10_, rs_ -> hsu_ (the cut states of lib/AU/HPgSeg.v), rm_ -> hm_, rs_u8s ->
   hd_zbytes; the engine runs walk image B's own code (the shadow address of pp->len reloaded from R+0x150, len read
   through t2 pinned to pp + 0x4000, ~pp read from R+0xf0, the turn's three UBSan tests decided by the engine: two
   from the atoms' ranges, the shift test from a condition fact), the input byte's shadow entry is the kit's
   hw10_shent_in, the first block is one shadow entry, and the cut R carries a6 = 1 and the cell R+0xf0. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): one turn of the corruption loop of
   LLVMFuzzerTestOneInput (0x80c40), pod.h:445-446 with fuzz.h:39-42. Proves no function (kind: segment lemma).
   THE CODE (the cut R = 0x82e2c is the loop head; a3 = kk, a2 = cnt - kk, a4 = off, a6 = 1, a0 the cursor, a5 what
   is left of the input; s1 = R, s2 = pp, t2 = pp + 0x4000, s11 = K)
     0x82e2c ld a1,0x150(s1) / lbu a1,0(a1)              the shadow byte of &pp->len (R+0x150 holds its address)
     0x82e34 beqz a1 -> 0x82e3c, else j 0x83dac           the report
     0x82e3c ld a7,0(t2) / add a1,a4,a3                   len, off + kk
     0x82e44 bgeu a1,a7 -> 0x82ec8                        off + kk >= len: the corruption ends (RT)
     0x82e48 beqz a5 -> 0x82e74                           no input left: the byte is 0 (0x82e74 li a7,0)
     0x82e4c addi t0,a0,1 / bgeu a6,t0 -> 0x83a14        the UBSan test of the cursor (the trap `unimp`)
     0x82e54 .. 0x82e60                                   the check of the 1-byte read at a0 (second test 0x82ebc)
     0x82e64 lbu a7,0(a0) / addi a5,a5,-1 / mv a0,t0 / j 0x82e78
     0x82e78 srli t0,a1,14 / bnez t0 -> 0x83a14           the UBSan test off + kk < 2^14
     0x82e80 ld t0,0xf0(s1) / bltu t0,a1 -> 0x83a14       the UBSan test off + kk <= ~pp (R+0xf0 holds ~pp)
     0x82e88 add a1,s2,a1                                 pp + off + kk
     0x82e8c .. 0x82e98                                   the check of the 1-byte store at a1 (second test 0x82eb0)
     0x82e9c sb a7,0(a1) / addi a2,a2,-1 / addi a3,a3,1
     0x82ea8 bnez a2 -> 0x82e2c                           the next turn (R with kk + 1)
     0x82eac j 0x82ec8                                    the count is done (RT)
   The engine meets the two computed addresses through the facts' aliases: off + kk is atom 33 and
   pp + off + kk atom 34, so the store lands in a region of its own; ~pp is atom 36. The atoms' ranges decide the
   UBSan tests `bgeu a6,t0` (a6 = 1 < cursor + 1) and `bltu t0,a1` (off + kk <= ~pp); YP0m.decide_eq decides a
   difference from disjoint ranges but no equality from ranges, so the facts carry (off + kk) >> 14 = 0 for `bnez t0`
   (hw10c_U_srl14). Each access's shadow bytes are a shadow entry of the engine (the length word and the store
   target inside the first block, the input byte inside the input), so no check reaches its second test or its
   report.
   hw10_corr: the statement hsu_piece_W10_corr_stmt (lib/AU/HPgSeg.v), R kk -> R (kk + 1) or RT. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgW10Kit HPgW10Req.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.

(* R's two cells the turn reads: R+0xf0 (~pp, the bound of the UBSan test of pp + off + kk) and R+0x150 (pp->len's
   shadow address) *)
Definition hw10c_rR : YP09.region := YP09.mkRegion (Some 9%nat) 0xf0 0x158 0 0
  [YP09.mkChunk 0xf0 (CVal 8 (SOff 36 0)); YP09.mkChunk 0x150 (CVal 8 (hw10_sh 18 0x4000))].

(* ---- the input byte at the cursor ---- *)
Lemma hw10c_nth_skipn : forall (rest : list byte) j x r1, skipn j rest = x :: r1 -> nth j (hd_zbytes rest) 0 = bv_unsigned x.
Proof.
unfold hd_zbytes. induction rest as [|y rest IH]; intros [|j] x r1 H; cbn in H |- *; try discriminate.
- injection H as -> ->. reflexivity.
- exact (IH j x r1 H).
Qed.

(* the sum of two atoms, as the engine writes `add` *)
Lemma hw10c_den_add : forall E n1 n2 v1 v2, ew E n1 = Z_to_bv 64 v1 -> 0 <= v1 < 2 ^ 62 ->
  ew E n2 = Z_to_bv 64 v2 -> 0 <= v2 < 2 ^ 62 ->
  sv_denot E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0)) = Z_to_bv 64 (v1 + v2).
Proof.
intros E n1 n2 v1 v2 H1 B1 H2 B2. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, (U_atom E n1 v1 H1 ltac:(lia)), (U_atom E n2 v2 H2 ltac:(lia)). cbn [zalu_raw].
apply zcanon_id. unfold M64. lia.
Qed.

(* the UBSan test `srli t0,a1,14 / bnez t0` on off + kk: the shift is 0 *)
Lemma hw10c_U_srl14 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 14 ->
  U E (SAlu ALU_SRL (SOff n 0) (SLit 14)) = 0.
Proof.
intros E n v H Hv. rewrite U_SAlu, U_SLit, (U_atom E n v H ltac:(lia)). cbn [zalu_raw].
change (Z.land (zcanon 14) 63) with 14. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

(* an atom's value at a run's environment, from its value at the entry one *)
Lemma hw10c_ew : forall k E E' (n : nat) v, env_agree k E E' -> (n < k)%nat -> ew E n = Z_to_bv 64 v ->
  ew E' n = Z_to_bv 64 v.
Proof. intros k E E' n v [H _] Hn Hv. rewrite (H n Hn). exact Hv. Qed.

(* a nonempty suffix: its head is the next byte of the prefix *)
Lemma hw10c_skipn_cons : forall (l : list byte) k y l', skipn k l = y :: l' ->
  firstn (S k) l = firstn k l ++ [y] /\ skipn (S k) l = l'.
Proof.
induction l as [|z l IH]; intros [|k] y l' H; cbn in H |- *; try discriminate.
- injection H as -> ->. split; reflexivity.
- destruct (IH k y l' H) as [H1 H2]. split; [rewrite H1; reflexivity | exact H2].
Qed.

Lemma hw10c_le1 : forall y : byte, Z_to_le_bytes 1 (bv_unsigned y) = [y].
Proof. intros y. cbn [Z_to_le_bytes]. rewrite hw10_byte_self. reflexivity. Qed.

(* the block after the store of the corruption's byte kk *)
Lemma hw10c_img_next : forall (cx : hsu_scx rsegs) W2 mem2 mem3 sh ps off bs kk (y : byte),
  hsu_wf sh ps -> 8 <= off -> (kk < length bs)%nat -> off + Z.of_nat (length bs) <= hsu_plen sh ps ->
  hsu_pp_at rsegs cx W2 mem2 (hsu_img_corr sh ps off bs (Z.of_nat kk)) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  (forall a, e_pp (x_e cx) <= a < e_pp (x_e cx) + PP_SIZE -> a <> e_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  firstn (S kk) bs = firstn kk bs ++ [y] ->
  hsu_pp_at rsegs cx W2 mem3 (hsu_img_corr sh ps off bs (Z.of_nat (S kk))).
Proof.
intros cx W2 mem2 mem3 sh ps off bs kk y Hwf Hoff Hk Hob Hpp Hv HK Hfs.
destruct (hw10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & _).
unfold hsu_plen in Hob.
unfold hsu_pp_at, hsu_img_corr in *. rewrite Nat2Z.id in *. rewrite Hfs.
assert (Hl : length (firstn kk bs) = kk) by (rewrite length_firstn; lia).
rewrite <- (hw10_img_step sh ps off (firstn kk bs) y ltac:(lia) ltac:(rewrite Hl; lia)).
rewrite Hl. rewrite <- (hw10c_le1 y).
set (IMG := pp_image (overwrite (pod_encode (PodRec sh ps None)) (Z.to_nat off) (firstn kk bs))
  (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None)) (params_struct (PodRec sh ps None))
  (ents (PodRec sh ps None)) false) in *.
assert (HLl : Z.of_nat (length IMG) = PP_SIZE).
{ apply length_pp_image; [| exact HW3 | exact HW4].
  rewrite length_overwrite; [rewrite HW2; unfold POD_BUF_MAX; lia | rewrite Hl; lia]. }
unfold PP_SIZE in HLl.
apply (hm_bytes_store rsegs (w_H W2) mem2 (w_H W2) mem3 (e_pp (x_e cx)) _ (Z.to_nat off + kk) 1 (bv_unsigned y) Hpp).
- replace (e_pp (x_e cx) + Z.of_nat (Z.to_nat off + kk)) with (e_pp (x_e cx) + off + Z.of_nat kk) by lia. exact Hv.
- lia.
- intros z Hz Hn. apply HK; [unfold PP_SIZE; lia | lia].
Qed.

(* ---- the engine runs' environments ---- *)
(* the run's environment E' agrees with the entry one E on the atoms below k *)
Ltac hw10c_agree k E HAE0 name :=
  lazymatch goal with HS' : st_ok _ ?E' _ (restrict _ _) |- _ =>
    assert (name : env_agree k E E') by env_agree_chain HAE0 end.
(* the value of atom n at a run's environment, in the goal or in a hypothesis *)
Ltac hw10c_at k E HAE0 n En :=
  lazymatch goal with
  | |- context [ew ?Ex n] =>
    let H := fresh "HAx" in assert (H : env_agree k E Ex) by env_agree_chain HAE0;
    rewrite (hw10c_ew _ _ _ n _ H ltac:(lia) En); clear H
  end.
Ltac hw10c_at_in k E HAE0 n En Hy :=
  lazymatch type of Hy with
  | context [ew ?Ex n] =>
    let H := fresh "HAx" in assert (H : env_agree k E Ex) by env_agree_chain HAE0;
    rewrite (hw10c_ew _ _ _ n _ H ltac:(lia) En) in Hy; clear H
  end.
(* the write right of a run whose first region is the store target pp + off + kk (atom 34) *)
Ltac hw10c_awr k E HAE0 E34 b p Hinp Hfresh :=
  cbn [ss_mem add_cond];
  eapply (hw10_awr_cons_pp _ _ _ _ _ _ _ _ _ _ 34%nat b p);
  [ reflexivity
  | hw10c_at k E HAE0 34%nat E34; apply unsigned_lit_small; lia
  | exact Hinp | exact Hfresh | cbn; lia | cbn; unfold PP_SIZE; lia | awr_ok_tac ].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* What one turn of the loop leaves, read off the turn's end: the journal clauses, the post cuts' values, the cell
   R+0xf0, the frame's shadow and the block with one more corruption byte. *)
Lemma hw10c_turn_common : forall (cx : hsu_scx rsegs) rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    sh ps off bs cnt r r' (y : byte),
  hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) ->
  hsu_cut_R rsegs B MT headamp_himg_B cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall n : Z, In n [2; 3; 4; 8; 9; 19; 27; 7; 18; 24] ->
     getr regs3 (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> e_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  skipn kk bs = y :: fst (fuzz_u8s (length bs - S kk) r') ->
  hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly2 S2 W2 regs3 mem3 md3 /\
  hsu_at_cx rsegs cx W2 mem3 regs3 (hsu_L_post rsegs cx) /\
  hd_at rsegs (w_H W2) mem3 regs3 (x_e cx) (LCell XR 0xf0) (- e_pp (x_e cx) - 1) /\
  hsu_fsh_at rsegs cx W2 mem3 (hsu_P0 headamp_himg_B) /\
  hsu_pp_at rsegs cx W2 mem3 (hsu_img_corr sh ps off bs (Z.of_nat (S kk))) /\
  (kk < length bs)%nat /\ skipn (S kk) bs = fst (fuzz_u8s (length bs - S kk) r').
Proof.
intros cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y HP HR HJ3 Hio3 Hregs HK Hv Hsk.
destruct HR as (HC & HL & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Htie & Hcw & Hkk & Hkb & Hskip).
destruct (hw10_ctx B MT cx _ ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR32 & HRS & HSTK & Hceil & H47 & HAR).
destruct (hw10_F_ctx B cx _ HP) as (HF1 & HF2 & HF3).
destruct (hw10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & _).
pose proof Hcw as (Hoff & Hob & Hb7 & Hcnt & Hbmin). unfold hsu_plen in Hob, Hbmin.
destruct (hw10_pre_geom B cx _ HP) as (_ & X1 & X2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hkl : (kk < length bs)%nat).
{ destruct (Nat.lt_ge_cases kk (length bs)) as [H|H]; [exact H|]. rewrite skipn_all2 in Hsk by exact H. discriminate. }
destruct (hw10c_skipn_cons bs kk y _ Hsk) as [Hfs Hss].
assert (Hnp : forall a, e_R (x_e cx) - T_SEG_STK <= a -> a <> e_pp (x_e cx) + off + Z.of_nat kk).
{ intros a Ha. unfold T_SEG_STK, ASTACK in *. lia. }
assert (Hcell : forall o i, 0 <= o < 0x220 -> 0 <= i < 8 ->
  aview rsegs (w_H W2) mem3 (e_R (x_e cx) + o + i) = aview rsegs (w_H W2) mem2 (e_R (x_e cx) + o + i)).
{ intros o i Ho Hi. apply HK; [unfold T_SEG_STK, ASTACK in *; lia | apply Hnp; unfold T_SEG_STK, ASTACK; lia]. }
split; [|split; [|split; [|split; [|split; [|split; [exact Hkl | exact Hss]]]]]].
- apply (hw10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 (fun a => a = e_pp (x_e cx) + off + Z.of_nat kk) HC HJ3).
  + intros rr Hr. apply Hregs. destruct Hr as [->|[->| ->]]; cbn; tauto.
  + exact Hio3.
  + intros a Ha Hn. exact (HK a Ha Hn).
  + intros a ->. right. unfold PP_SIZE. lia.
- pose proof HL as HLp. unfold hsu_at_cx, hsu_at in HLp. apply Forall_app in HLp. destruct HLp as [HLp _].
  apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 (x_e cx) _ HLp).
  intros f Hf. unfold hsu_L_post in Hf. cbv zeta in Hf.
  repeat (destruct Hf as [<-|Hf]; [cbn [fst hm_keeps hd_xv];
    first [ (apply Hregs; cbn; tauto) | (intros i Hi; apply Hcell; lia) ] |]).
  destruct Hf.
- pose proof HL as HLf. unfold hsu_at_cx, hsu_at in HLf. apply Forall_app in HLf. destruct HLf as [_ HLf].
  rewrite !Forall_cons_iff in HLf. destruct HLf as (_ & _ & _ & _ & _ & _ & Hf0 & _).
  cbn [fst snd] in Hf0.
  apply (hm_at_kept rsegs (w_H W2) mem2 (w_H W2) mem3 regs2 regs3 (x_e cx) _ _ Hf0).
  cbn [hm_keeps hd_xv]. intros i Hi. apply Hcell; lia.
- apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) mem3 (e_F (x_e cx)) (hsu_P0 headamp_himg_B) Hfsh).
  intros i Hi. change (length (hsu_P0 headamp_himg_B)) with 116%nat in Hi.
  pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia)). assert (e_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
  pose proof (hw10_shadow_not_pp (e_pp (x_e cx)) (e_F (x_e cx)) i Happ HF3 ltac:(lia)) as Hs.
  apply HK; [unfold shadow_addr, SHADOW_OFF; lia | unfold PP_SIZE in Hs; lia].
- apply (hw10c_img_next cx W2 mem2 mem3 sh ps off bs kk y Hwf Hoff Hkl Hob Hpp Hv); [| exact Hfs].
  intros a Ha Hn. apply HK; [unfold PP_SIZE in Ha; lia | exact Hn].
Qed.

Lemma hw10c_finish_R : forall (cx : hsu_scx rsegs) rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    sh ps off bs cnt r r' (y : byte),
  hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) ->
  hsu_cut_R rsegs B MT headamp_himg_B cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall n : Z, In n [2; 3; 4; 8; 9; 19; 27; 7; 18; 24] ->
     getr regs3 (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> e_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  skipn kk bs = y :: fst (fuzz_u8s (length bs - S kk) r') ->
  hsu_suffix rest r' ->
  getr regs3 (Z_to_bv 5 13) = w64 (Z.of_nat (S kk)) ->
  getr regs3 (Z_to_bv 5 12) = w64 (cnt - Z.of_nat (S kk)) ->
  getr regs3 (Z_to_bv 5 14) = w64 off ->
  getr regs3 (Z_to_bv 5 16) = w64 1 ->
  getr regs3 (Z_to_bv 5 10) = w64 (hsu_cur rsegs cx rest r') ->
  getr regs3 (Z_to_bv 5 15) = w64 (Z.of_nat (length r')) ->
  Z.of_nat (S kk) < cnt ->
  hsu_cut_R rsegs B MT headamp_himg_B cx sh ps rest r' off bs cnt (Z.of_nat (S kk)) ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y HP HR HJ3 Hio3 Hregs HK Hv Hsk Hsuf'
  R13 R12 R14 R16 R10 R15 Hlt.
destruct (hw10c_turn_common cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y
  HP HR HJ3 Hio3 Hregs HK Hv Hsk) as (Hcore & HLp & Hf0 & Hfsh & Hpp & Hkl & Hss).
destruct HR as (_ & _ & _ & _ & Hin & _ & Hwf & Hlen & Htie & Hcw & _ & _ & _).
split; [exact Hcore|]. split.
{ unfold hsu_at_cx, hsu_at in *. apply Forall_app. split; [exact HLp|].
  repeat (apply Forall_cons; [cbn [fst snd]; first [exact Hf0 | (cbn [hd_at]; assumption)] |]). apply Forall_nil. }
split; [exact Hfsh|]. split; [exact Hpp|]. split; [exact Hin|]. split; [exact Hsuf'|]. split; [exact Hwf|].
split; [exact Hlen|]. split; [exact Htie|]. split; [exact Hcw|]. split; [lia|]. split; [lia|].
rewrite Nat2Z.id. exact Hss.
Qed.

Lemma hw10c_finish_RT : forall (cx : hsu_scx rsegs) rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3
    sh ps off bs cnt r r' (y : byte),
  hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) ->
  hsu_cut_R rsegs B MT headamp_himg_B cx sh ps rest r off bs cnt (Z.of_nat kk) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall n : Z, In n [2; 3; 4; 8; 9; 19; 27; 7; 18; 24] ->
     getr regs3 (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> e_pp (x_e cx) + off + Z.of_nat kk ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  val_mem rsegs (mrestrict (w_H W2) mem3) (e_pp (x_e cx) + off + Z.of_nat kk) 1 (bv_unsigned y) ->
  skipn kk bs = y :: fst (fuzz_u8s (length bs - S kk) r') ->
  hsu_suffix rest r' ->
  length bs = S kk ->
  hsu_cut_RT rsegs B MT headamp_himg_B cx sh ps off bs rest r' ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y HP HR HJ3 Hio3 Hregs HK Hv Hsk Hsuf'
  Hbl.
destruct (hw10c_turn_common cx rest kk ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 sh ps off bs cnt r r' y
  HP HR HJ3 Hio3 Hregs HK Hv Hsk) as (Hcore & HLp & _ & Hfsh & Hpp & Hkl & Hss).
destruct HR as (_ & _ & _ & _ & Hin & _ & Hwf & Hlen & Htie & Hcw & _ & _ & _).
destruct Hcw as (Hoff & Hob & Hb7 & _).
split; [exact Hcore|]. split; [exact HLp|]. split; [exact Hfsh|]. split; [rewrite Hbl; exact Hpp|].
split; [exact Hin|]. split; [exact Hsuf'|]. split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Htie|].
split; [exact Hoff|]. split; [exact Hob | exact Hb7].
Qed.

Theorem hw10_corr : hsu_piece_W10_corr_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof.
unfold hsu_piece_W10_corr_stmt. intros cx POST rest kk Hst HR1 HRT.
unfold hsu_from_R. intros ly2 S2 W2 regs2 mem2 md2 sh ps r off bs cnt HR.
destruct Hst as (HP & _ & _ & _).
pose proof HR as HRc.
destruct HR as (HC & HL & Hfsh & Hpp & Hin & Hsuf & Hwf & Hlen & Htie & Hcw & Hkk & Hkb & Hskip).
pose proof hw10_wx as Hwx. pose proof hw10_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
destruct (hw10_ctx B MT cx _ ly2 S2 W2 regs2 mem2 md2 HP HC)
  as (Hinp & Hfresh & Hal & Hlo & Hhi & Happ & Hpres & H2 & HR32 & HRS & HSTK & Hceil & H47 & HAR).
destruct (hw10_F_ctx B cx _ HP) as (HF1 & HF2 & HF3).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (hw10_wf_facts sh ps Hwf) as (HW1 & HW2 & HW3 & HW4 & HW5).
destruct Hcw as (Hoff & Hob & Hb7 & Hcnt & Hbmin).
unfold hsu_plen in Hob, Hbmin.
destruct (hw10_in_now B MT cx rest (hsu_P0 headamp_himg_B) ly2 S2 W2 regs2 mem2 md2 HP Hin HC Hfsh eq_refl)
  as (Hbytes & Hra & _).
pose proof Hin as (Hleft & _ & _ & _ & Hamr & Hsrc0 & Hsrc63 & Hindisj).
destruct Hsuf as (j & Hj & Hrj).
assert (HR0 : 0 <= e_R (x_e cx) /\ e_R (x_e cx) + 0x220 <= 2 ^ 47).
{ destruct (hw10_pre_geom B cx _ HP) as (_ & X1 & X2 & _). unfold T_SEG_STK, ASTACK in *. lia. }
set (pp := e_pp (x_e cx)) in *.
set (Lp := Z.of_nat (length (pc_buf (PbCut sh ps None)))) in *.
set (enc := pod_encode (PodRec sh ps None)) in *.
rewrite Nat2Z.id in Hskip.
assert (Hbl : length (overwrite enc (Z.to_nat off) (firstn kk bs)) = length (pc_buf (PbCut sh ps None))).
{ rewrite length_overwrite; [exact HW2|]. rewrite length_firstn. lia. }
assert (HLv : val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 Lp).
{ unfold hsu_pp_at, hsu_img_corr in Hpp. rewrite Nat2Z.id in Hpp.
  pose proof (hm_pp_len rsegs (overwrite enc (Z.to_nat off) (firstn kk bs)) _ _ _ _ _
    ltac:(rewrite Hbl; unfold POD_BUF_MAX; lia) HW3 HW4 (w_H W2) mem2 pp Hpp) as X.
  rewrite Hbl in X. exact X. }
pose proof HL as HL0.
unfold hsu_at_cx, hsu_at, hsu_L_post in HL. cbv zeta in HL. cbn [app] in HL.
rewrite !Forall_cons_iff in HL.
destruct HL as (P8 & P9 & P19 & P27 & P7 & P18 & P24 & Q08 & Q18 & Q20 & Q38 & Q48 & Qe0 & Q108 & Q120 & Q148 & Q150 &
  P13 & P12 & P14 & P16 & P10 & P15 & Qf0 & _).
cbn [fst snd hd_at hd_xv] in P8, P9, P19, P27, P7, P18, P24, Q150, P13, P12, P14, P16, P10, P15, Qf0.
pose proof HC as (HJ & _).
change (e_pp (x_e cx)) with pp in P7, P18, P24, Q150, Qf0.
assert (Hsh : 0 <= shadow_addr (pp + 0x4000) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (pp + 0x4000) 8 ltac:(lia) ltac:(lia)).
  assert ((pp + 0x4000) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia). lia. }
unfold Layout.OFF_LEN in Q150. rewrite Z.mod_small in Q150 by lia.
assert (Hneg : (- pp - 1) mod 2 ^ 64 = 2 ^ 64 - pp - 1).
{ replace (- pp - 1) with ((2 ^ 64 - pp - 1) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
rewrite Hneg in Qf0.
set (cur := hsu_cur rsegs cx rest r) in P10.
assert (Hcur : cur = e_src (x_e cx) + Z.of_nat j).
{ subst cur. unfold hsu_cur. rewrite Hrj, length_skipn. lia. }
assert (Hrl : Z.of_nat (length r) = Z.of_nat (length rest) - Z.of_nat j) by (rewrite Hrj, length_skipn; lia).
assert (HK47 : e_src (x_e cx) + e_left (x_e cx) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
set (src := e_src (x_e cx)) in Hcur, HK47, Hamr, Hsrc0, Hsrc63, Hra, Hbytes, Hindisj.
set (kz := Z.of_nat kk) in P13, P12, Hkk, Hkb, Hpp.
remember (Ereg regs2 [Z_to_bv 64 Lp; Z_to_bv 64 (off + kz); Z_to_bv 64 (pp + off + kz);
  Z_to_bv 64 (match r with x :: _ => bv_unsigned x | [] => 0 end); Z_to_bv 64 (2 ^ 64 - pp - 1)]) as E eqn:HE.
assert (E9 : ew E 9 = Z_to_bv 64 (e_R (x_e cx))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl); exact P9).
assert (E10 : ew E 10 = Z_to_bv 64 cur) by (subst E; rewrite (ew_Ereg_nat regs2 _ 10 (Z_to_bv 5 10) eq_refl); exact P10).
assert (E12 : ew E 12 = Z_to_bv 64 (cnt - kz)) by (subst E; rewrite (ew_Ereg_nat regs2 _ 12 (Z_to_bv 5 12) eq_refl); exact P12).
assert (E13 : ew E 13 = Z_to_bv 64 kz) by (subst E; rewrite (ew_Ereg_nat regs2 _ 13 (Z_to_bv 5 13) eq_refl); exact P13).
assert (E14 : ew E 14 = Z_to_bv 64 off) by (subst E; rewrite (ew_Ereg_nat regs2 _ 14 (Z_to_bv 5 14) eq_refl); exact P14).
assert (E15 : ew E 15 = Z_to_bv 64 (Z.of_nat (length r))) by (subst E; rewrite (ew_Ereg_nat regs2 _ 15 (Z_to_bv 5 15) eq_refl); exact P15).
assert (E16 : ew E 16 = Z_to_bv 64 1) by (subst E; rewrite (ew_Ereg_nat regs2 _ 16 (Z_to_bv 5 16) eq_refl); exact P16).
assert (E18 : ew E 18 = Z_to_bv 64 pp) by (subst E; rewrite (ew_Ereg_nat regs2 _ 18 (Z_to_bv 5 18) eq_refl); exact P18).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl); exact P27).
assert (E32 : ew E 32 = Z_to_bv 64 Lp) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (off + kz)) by (subst E; exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (pp + off + kz)) by (subst E; exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (match r with x :: _ => bv_unsigned x | [] => 0 end))
  by (subst E; exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (2 ^ 64 - pp - 1)) by (subst E; exact (ew_Ereg_extra regs2 _ 4)).
assert (Hpp47 : 0 <= pp + 0x4000 < 2 ^ 47) by lia.
assert (HoffL : off + kz <= Lp) by lia.
pose proof HL0 as HLpost. unfold hsu_at_cx, hsu_at in HLpost. apply Forall_app in HLpost. destruct HLpost as [HLpost _].
assert (HAE : env_agree 32 (Ereg regs2 [Z_to_bv 64 Lp; Z_to_bv 64 (off + kz); Z_to_bv 64 (pp + off + kz);
  Z_to_bv 64 (match r with x :: _ => bv_unsigned x | [] => 0 end); Z_to_bv 64 (2 ^ 64 - pp - 1)]) E)
  by (rewrite HE; split; [intros; reflexivity | reflexivity]).
assert (HAE0 : env_agree 37 E E) by apply env_agree_refl.
assert (Himgl : forall k, (k <= length bs)%nat -> Z.of_nat (length (hsu_img_corr sh ps off bs (Z.of_nat k))) = PP_SIZE).
{ intros k Hk. unfold hsu_img_corr. fold enc. apply length_pp_image; [| exact HW3 | exact HW4].
  rewrite length_overwrite; [rewrite HW2; unfold POD_BUF_MAX; lia|]. rewrite length_firstn. lia. }
destruct (Z_le_gt_dec Lp (off + kz)) as [Hge|Hlt].
{ (* off + kk reaches the length: the corruption ends with the bytes written so far *)
  assert (Hkbs : kz = Z.of_nat (length bs)) by lia.
  assert (HS : st_ok rsegs E (mkSS HW10_R hw10_sr_post [hw10_r150; hw10_rlen] None
    (mkFacts [(18%nat, mkAF 4096 HW10_PPHI 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0);
              (33%nat, mkAF 8 5447 0); (12%nat, mkAF 1 7 0); (13%nat, mkAF 0 6 0); (14%nat, mkAF 8 5440 0)]
       [mkAC BC_GEU (SOff 33 0) (SOff 32 0)]
       [(SAlu ALU_ADD (SOff 13 0) (SOff 14 0), SOff 33 0)]))
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 HW10_R) mem2 (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
    - unfold hw10_sr_post. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | |] | |].
      + intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X.
      + rewrite (hw10_den_off _ 18 _ 0x4000 E18). exact P7.
      + intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X.
      + rewrite (hw10_den_off _ 18 _ 0x4d18 E18). exact P24.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor]].
      + apply (hm_ro_region rsegs _ (w_H W2) mem2 9 (e_R (x_e cx))); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
        constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ (e_R (x_e cx)) 0x150 8 _ (shadow_addr (pp + 0x4000))).
        * apply (hw10_den_sh _ 18 pp 0x4000 E18); [lia | lia | exact E27].
        * cbn. lia.
        * cbn. lia.
        * exact Q150.
      + apply (hm_ro_region rsegs _ (w_H W2) mem2 18 pp); [rewrite E18; apply unsigned_lit_small; lia | lia | lia |].
        constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ pp 0x4000 8 (SOff 32 0) Lp).
        * exact (hw10_den_atom _ 32 Lp E32). * cbn. lia. * cbn. lia. * exact HLv.
    - apply pairwise_disjoint_of_extents.
      cbn [map zpairwise_disjoint zall_disjoint]. unfold YA0q.extent_of_region, zdisj.
      cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi fst snd hw10_r150 hw10_rlen].
      rewrite E9, E18, !unsigned_lit_small by lia.
      unfold T_SEG_STK, ASTACK in *. repeat split; lia.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok].
      refine (conj _ (conj (conj _ I) (conj _ I))).
      + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E18, E27, E32, E33, E12, E13, E14.
        rewrite !unsigned_lit_small by (unfold SHADOW_OFF, HW10_PPHI; lia).
        repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, HW10_PPHI; lia);
        try (rewrite Z.pow_0_r; apply Z.mod_1_r).
        change (2 ^ 4) with 16. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal; [|lia]. exact Hal.
      + unfold acond_ok. cbn [ac_c ac_a ac_b].
        rewrite branch_geu_U, (hw10_U_atom _ 33 _ E33 ltac:(lia)), (hw10_U_atom _ 32 _ E32 ltac:(lia)).
        apply negb_true_iff, Z.ltb_ge. lia.
      + rewrite (hw10c_den_add _ 13 14 kz off E13 ltac:(lia) E14 ltac:(lia)), (hw10_den_atom _ 33 _ E33). f_equal. lia. }
  (* the first block's bytes are one shadow entry of the engine: they are marked usable *)
  assert (SHOK : sh_ok rsegs hw10_Bx [mkSHE 18 0 0x4d20] E (mrestrict (w_H W2) mem2)).
  { constructor; [|constructor].
    apply (hw10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 18 0 0x4d20 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact (hw10_UB E E27) | | | lia];
    rewrite (hw10_U_atom E 18 _ E18 ltac:(lia)); lia. }
  unfold cfg_at. change (w64 (bi_R headamp_bld_B)) with (Z_to_bv 64 HW10_R).
  aj_run_to_tok hw10_tbl_ok HS HJ SHOK hw10_Bspan HW10_RT.
  all: try solve [awr_ok_tac].
  hw10c_agree 34%nat E (env_agree_refl 34 E) HAEf.
  assert (HK : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha. apply (hw10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
    destruct Hr as [<-|[<-|[]]]; cbn in Hrb; lia. }
  pose proof (HPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 7; Z_to_bv 5 11; Z_to_bv 5 17; Z_to_bv 5 24] HS ltac:(env_agree_chain HAE)
    ltac:(vm_compute; reflexivity)) as RK.
  assert (RK7 : getr (ms_regs ms) (Z_to_bv 5 7) = getr regs2 (Z_to_bv 5 7)).
  { apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 7) 34 (SOff 18 0x4000) _ HS HAEf); [vm_compute; reflexivity | reflexivity |].
    rewrite (hw10_den_off _ 18 _ 0x4000 E18). symmetry. exact P7. }
  assert (RK24 : getr (ms_regs ms) (Z_to_bv 5 24) = getr regs2 (Z_to_bv 5 24)).
  { apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 24) 34 (SOff 18 0x4d18) _ HS HAEf); [vm_compute; reflexivity | reflexivity |].
    rewrite (hw10_den_off _ 18 _ 0x4d18 E18). symmetry. exact P24. }
  assert (Hcell : forall o i, 0 <= o < 0x220 -> 0 <= i < 8 ->
    aview rsegs (w_H W2) (ms_mem ms) (e_R (x_e cx) + o + i) = aview rsegs (w_H W2) mem2 (e_R (x_e cx) + o + i)).
  { intros o i Ho Hi. apply HK. lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps off bs r).
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
  - apply (hw10_core_run B MT cx ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ (fun _ => False) HC HJ).
    + intros rr Hr. apply RK; [destruct Hr as [->|[->| ->]]; vm_compute; discriminate |].
      apply hw10_notin. destruct Hr as [->|[->| ->]]; vm_compute; reflexivity.
    + apply HPgSteps.same_io_wvb.
    + intros a Ha _. exact (HK a Ha).
    + intros a [].
  - apply (hm_atl_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) regs2 (ms_regs ms) (x_e cx) _ HLpost).
    intros f Hf. unfold hsu_L_post in Hf. cbv zeta in Hf.
    repeat (destruct Hf as [<-|Hf]; [cbn [fst hm_keeps hd_xv];
      first [ exact RK7 | exact RK24
            | (apply RK; [vm_compute; discriminate | apply hw10_notin; vm_compute; reflexivity])
            | (intros i Hi; apply Hcell; lia) ] |]).
    destruct Hf.
  - apply (hm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) (e_F (x_e cx)) (hsu_P0 headamp_himg_B) Hfsh).
    intros i Hi. apply HK. change (length (hsu_P0 headamp_himg_B)) with 116%nat in Hi.
    pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia)). assert (e_F (x_e cx) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
    unfold shadow_addr, SHADOW_OFF. lia.
  - rewrite <- Hkbs. apply (hm_bytes_kept rsegs (w_H W2) mem2 (w_H W2) (ms_mem ms) pp _ Hpp).
    assert (X : Z.of_nat (length (hsu_img_corr sh ps off bs kz)) = PP_SIZE) by exact (Himgl kk ltac:(lia)).
    intros y Hy. try rewrite length_map in Hy. rewrite X in Hy. apply HK. unfold PP_SIZE in Hy. lia.
  - exact Hin.
  - exists j. split; [exact Hj | exact Hrj].
  - exact Hwf.
  - exact Hlen.
  - exact Htie.
  - exact Hoff.
  - unfold hsu_plen. exact Hob.
  - exact Hb7. }
destruct r as [|x r1].
{ (* no input left: the byte is 0 *)
  cbv beta iota in E35, HE, HAE.
  assert (Hkl : (kk < length bs)%nat) by (unfold kz in *; lia).
  assert (Hsk : skipn kk bs = Z_to_bv 8 0 :: fst (fuzz_u8s (length bs - S kk) [])).
  { rewrite Hskip. replace (length bs - kk)%nat with (S (length bs - S kk)) by lia. apply hw10_fuzz_u8s_nil. }
  assert (Hsuf' : hsu_suffix rest []) by (exists j; split; [exact Hj | exact Hrj]).
  assert (Hy0 : bv_unsigned (Z_to_bv 8 0 : byte) = 0) by reflexivity.
  change (Z.of_nat (length (@nil byte))) with 0 in E15.
  assert (HS : st_ok rsegs E (mkSS HW10_R hw10_sr_post
    [YP09.mkRegion (Some 34%nat) 0 1 0 1 []; hw10_rlen; hw10c_rR] None
    (mkFacts [(18%nat, mkAF 4096 HW10_PPHI 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0);
              (33%nat, mkAF 8 5440 0); (34%nat, mkAF 4096 HW10_HI 0);
              (36%nat, mkAF (2 ^ 64 - 1 - HW10_PPHI) (2 ^ 64 - 4097) 0);
              (15%nat, mkAF 0 0 0); (16%nat, mkAF 1 1 0); (12%nat, mkAF 1 7 0);
              (13%nat, mkAF 0 6 0); (14%nat, mkAF 8 5440 0)]
       [mkAC BC_LTU (SOff 33 0) (SOff 32 0); mkAC BC_EQ (SOff 15 0) (SLit 0);
        mkAC BC_EQ (SAlu ALU_SRL (SOff 33 0) (SLit 14)) (SLit 0)]
       [(SAlu ALU_ADD (SOff 13 0) (SOff 14 0), SOff 33 0); (SAlu ALU_ADD (SOff 18 0) (SOff 33 0), SOff 34 0)]))
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 HW10_R) mem2 (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
    - unfold hw10_sr_post. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | |] | |].
      + intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X.
      + rewrite (hw10_den_off _ 18 _ 0x4000 E18). exact P7.
      + intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X.
      + rewrite (hw10_den_off _ 18 _ 0x4d18 E18). exact P24.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor; [|constructor]]].
      + apply (hm_rw_region rsegs _ (w_H W2) mem2 34 (pp + off + kz)).
        * rewrite E34. rewrite unsigned_lit_small by lia. reflexivity.
        * lia. * lia.
        * intros o Ho. apply Hpres. lia.
        * constructor.
      + apply (hm_ro_region rsegs _ (w_H W2) mem2 18 pp); [rewrite E18; apply unsigned_lit_small; lia | lia | lia |].
        constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ pp 0x4000 8 (SOff 32 0) Lp).
        * exact (hw10_den_atom _ 32 Lp E32). * cbn. lia. * cbn. lia. * exact HLv.
      + apply (hm_ro_region rsegs _ (w_H W2) mem2 9 (e_R (x_e cx))); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
        constructor; [|constructor; [|constructor]].
        * apply (chunk_ok_val rsegs _ _ (e_R (x_e cx)) 0xf0 8 (SOff 36 0) (2 ^ 64 - pp - 1)).
          -- exact (hw10_den_atom _ 36 _ E36). -- cbn. lia. -- cbn. lia. -- exact Qf0.
        * apply (chunk_ok_val rsegs _ _ (e_R (x_e cx)) 0x150 8 _ (shadow_addr (pp + 0x4000))).
          -- apply (hw10_den_sh _ 18 pp 0x4000 E18); [lia | lia | exact E27].
          -- cbn. lia. -- cbn. lia. -- exact Q150.
    - apply pairwise_disjoint_of_extents.
      cbn [map zpairwise_disjoint zall_disjoint]. unfold YA0q.extent_of_region, zdisj.
      cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi fst snd hw10_rlen hw10c_rR].
      rewrite E34, E18, E9, !unsigned_lit_small by lia.
      unfold T_SEG_STK, ASTACK in *. repeat split; lia.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok].
      refine (conj _ (conj (conj _ (conj _ (conj _ I))) (conj _ (conj _ I)))).
      + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E18, E27, E32, E33, E34, E36, E15, E16, E12, E13, E14.
        rewrite !unsigned_lit_small by (unfold SHADOW_OFF, HW10_PPHI; lia).
        repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, HW10_PPHI, HW10_HI; lia);
        try (rewrite Z.pow_0_r; apply Z.mod_1_r).
        change (2 ^ 4) with 16. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal; [|lia]. exact Hal.
      + unfold acond_ok. cbn [ac_c ac_a ac_b].
        rewrite branch_ltu_U, (hw10_U_atom _ 33 _ E33 ltac:(lia)), (hw10_U_atom _ 32 _ E32 ltac:(lia)).
        apply Z.ltb_lt. lia.
      + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, (hw10_U_atom _ 15 0 E15 ltac:(lia)), U_lit by lia.
        reflexivity.
      + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, U_lit by lia.
        rewrite (hw10c_U_srl14 _ 33 (off + kz) E33 ltac:(lia)). reflexivity.
      + rewrite (hw10c_den_add _ 13 14 kz off E13 ltac:(lia) E14 ltac:(lia)), (hw10_den_atom _ 33 _ E33). f_equal. lia.
      + rewrite (hw10c_den_add _ 18 33 pp (off + kz) E18 ltac:(lia) E33 ltac:(lia)), (hw10_den_atom _ 34 _ E34). f_equal. lia. }
  (* the shadow entries: the first block (the length word and the store target) *)
  assert (SHOK : sh_ok rsegs hw10_Bx [mkSHE 18 0 0x4d20; mkSHE 34 0 1] E (mrestrict (w_H W2) mem2)).
  { constructor; [|constructor; [|constructor]].
    - apply (hw10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 18 0 0x4d20 HAR Hinp);
      change (req_size PP_SIZE) with 19744; [exact Happ | exact (hw10_UB E E27) | | | lia];
      rewrite (hw10_U_atom E 18 _ E18 ltac:(lia)); lia.
    - apply (hw10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 34 0 1 HAR Hinp);
      change (req_size PP_SIZE) with 19744; [exact Happ | exact (hw10_UB E E27) | | | lia];
      rewrite (hw10_U_atom E 34 _ E34 ltac:(lia)); lia. }
  unfold cfg_at. change (w64 (bi_R headamp_bld_B)) with (Z_to_bv 64 HW10_R).
  aj_run_to_tok hw10_tbl_ok HS HJ SHOK hw10_Bspan HW10_RT.
  all: try solve [hw10c_awr 37%nat E HAE0 E34 (pp + off + kz) pp Hinp Hfresh].
  rename ms into msA. rename HF into HFa. rename HFr into HFra. rename HG into HGa.
  srr_branch_tok hw10_tbl_ok HS SHOK hw10_Bspan.
  - (* a2 - 1 <> 0: the next turn *)
    hw10c_agree 37%nat E HAE0 HAEb.
    rewrite branch_ne_U in Hc.
    rewrite (U_atom_off _ 12 (cnt - kz) (-1)) in Hc;
      [| exact (hw10c_ew _ _ _ 12 _ HAEb ltac:(lia) E12) | lia | lia].
    rewrite U_lit in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc.
    aj_run_to_tok hw10_tbl_ok HS HJ SHOK hw10_Bspan HW10_R.
    all: try solve [hw10c_awr 37%nat E HAE0 E34 (pp + off + kz) pp Hinp Hfresh].
    hw10c_agree 37%nat E HAE0 HAEf.
    assert (HKAB : forall a, 0 <= a < 2 ^ 64 -> a <> pp + off + kz ->
      aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
    { intros a Ha Hn. transitivity (aview rsegs (w_H W2) (ms_mem msA) a).
      - apply (hw10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem add_cond] in Hr.
        destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hw10_rlen hw10c_rR] in Hrb;
          [|lia|lia].
        hw10c_at_in 37%nat E HAE0 34%nat E34 Hrb. rewrite unsigned_lit_small in Hrb by lia. apply Hn. lia.
      - apply (hw10_frame_kept _ _ _ _ _ HFra a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
        destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hw10_rlen hw10c_rR] in Hrb;
          [|lia|lia].
        hw10c_at_in 37%nat E HAE0 34%nat E34 Hrb. rewrite unsigned_lit_small in Hrb by lia. apply Hn. lia. }
    assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned (Z_to_bv 8 0 : byte))).
    { rewrite Hy0. pose proof (HPgSteps.st_ok_region_at _ _ _ 0 _ HS eq_refl) as HRg.
      replace (pp + off + kz) with (pp + off + kz + 0) by lia.
      apply (hw10_field _ _ 34 (pp + off + kz) _ 0 1 0 1 0 1 (SLit 0) 0 HRg);
        [ rewrite (hw10c_ew _ _ _ 34 _ HAEf ltac:(lia) E34); apply unsigned_lit_small; lia
        | left; reflexivity
        | reflexivity
        | cbn; lia | cbn; lia ]. }
    pose proof (HPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2)
      [Z_to_bv 5 5; Z_to_bv 5 6; Z_to_bv 5 7; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 17; Z_to_bv 5 24] HS
      ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
    assert (RK7 : getr (ms_regs ms) (Z_to_bv 5 7) = getr regs2 (Z_to_bv 5 7)).
    { apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 7) 37 (SOff 18 0x4000) _ HS HAEf); [vm_compute; reflexivity | reflexivity |].
      rewrite (hw10_den_off _ 18 _ 0x4000 E18). symmetry. exact P7. }
    assert (RK24 : getr (ms_regs ms) (Z_to_bv 5 24) = getr regs2 (Z_to_bv 5 24)).
    { apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 24) 37 (SOff 18 0x4d18) _ HS HAEf); [vm_compute; reflexivity | reflexivity |].
      rewrite (hw10_den_off _ 18 _ 0x4d18 E18). symmetry. exact P24. }
    assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 27; 7; 18; 24] ->
      getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
    { intros n Hn. cbn [In] in Hn.
      repeat (destruct Hn as [<-|Hn];
        [first [exact RK7 | exact RK24 | (apply RK; [vm_compute; discriminate | apply hw10_notin; vm_compute; reflexivity])] |]).
      destruct Hn. }
    assert (R13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 (Z.of_nat (S kk))).
    { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 13) HS). hw10_sr_eval.
      rewrite (hw10_den_off _ 13 kz 1 (hw10c_ew _ _ _ 13 _ HAEf ltac:(lia) E13)).
      f_equal. unfold kz. lia. }
    assert (R12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (cnt - Z.of_nat (S kk))).
    { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 12) HS). hw10_sr_eval.
      rewrite (hw10_den_off _ 12 (cnt - kz) (-1) (hw10c_ew _ _ _ 12 _ HAEf ltac:(lia) E12)).
      f_equal. unfold kz. lia. }
    assert (R14 : getr (ms_regs ms) (Z_to_bv 5 14) = w64 off).
    { rewrite RK; [exact P14 | vm_compute; discriminate | apply hw10_notin; vm_compute; reflexivity]. }
    assert (R16 : getr (ms_regs ms) (Z_to_bv 5 16) = w64 1).
    { rewrite RK; [exact P16 | vm_compute; discriminate | apply hw10_notin; vm_compute; reflexivity]. }
    assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (hsu_cur rsegs cx rest [])).
    { rewrite RK; [exact P10 | vm_compute; discriminate | apply hw10_notin; vm_compute; reflexivity]. }
    assert (R15 : getr (ms_regs ms) (Z_to_bv 5 15) = w64 (Z.of_nat (length (@nil byte)))).
    { rewrite RK; [exact P15 | vm_compute; discriminate | apply hw10_notin; vm_compute; reflexivity]. }
    rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
    apply (HR1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps [] off bs cnt).
    apply (hw10c_finish_R cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt [] []
      (Z_to_bv 8 0) HP HRc HJ ltac:(eapply same_io_trans; apply HPgSteps.same_io_wvb) Hregs HKAB Hv Hsk Hsuf'
      R13 R12 R14 R16 R10 R15).
    unfold kz in *. lia.
  - (* a2 - 1 = 0: the count is done *)
    hw10c_agree 37%nat E HAE0 HAEb.
    rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 12 (cnt - kz) (-1)) in Hc;
      [| exact (hw10c_ew _ _ _ 12 _ HAEb ltac:(lia) E12) | lia | lia].
    rewrite U_lit in Hc by lia.
    apply negb_false_iff, Z.eqb_eq in Hc.
    aj_run_to_tok hw10_tbl_ok HS HJ SHOK hw10_Bspan HW10_RT.
    all: try solve [hw10c_awr 37%nat E HAE0 E34 (pp + off + kz) pp Hinp Hfresh].
    hw10c_agree 37%nat E HAE0 HAEf.
    assert (HKAB : forall a, 0 <= a < 2 ^ 64 -> a <> pp + off + kz ->
      aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
    { intros a Ha Hn. transitivity (aview rsegs (w_H W2) (ms_mem msA) a).
      - apply (hw10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem add_cond] in Hr.
        destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hw10_rlen hw10c_rR] in Hrb;
          [|lia|lia].
        hw10c_at_in 37%nat E HAE0 34%nat E34 Hrb. rewrite unsigned_lit_small in Hrb by lia. apply Hn. lia.
      - apply (hw10_frame_kept _ _ _ _ _ HFra a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
        destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hw10_rlen hw10c_rR] in Hrb;
          [|lia|lia].
        hw10c_at_in 37%nat E HAE0 34%nat E34 Hrb. rewrite unsigned_lit_small in Hrb by lia. apply Hn. lia. }
    assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned (Z_to_bv 8 0 : byte))).
    { rewrite Hy0. pose proof (HPgSteps.st_ok_region_at _ _ _ 0 _ HS eq_refl) as HRg.
      replace (pp + off + kz) with (pp + off + kz + 0) by lia.
      apply (hw10_field _ _ 34 (pp + off + kz) _ 0 1 0 1 0 1 (SLit 0) 0 HRg);
        [ rewrite (hw10c_ew _ _ _ 34 _ HAEf ltac:(lia) E34); apply unsigned_lit_small; lia
        | left; reflexivity
        | reflexivity
        | cbn; lia | cbn; lia ]. }
    pose proof (HPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2)
      [Z_to_bv 5 5; Z_to_bv 5 6; Z_to_bv 5 7; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 17; Z_to_bv 5 24] HS
      ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
    assert (RK7 : getr (ms_regs ms) (Z_to_bv 5 7) = getr regs2 (Z_to_bv 5 7)).
    { apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 7) 37 (SOff 18 0x4000) _ HS HAEf); [vm_compute; reflexivity | reflexivity |].
      rewrite (hw10_den_off _ 18 _ 0x4000 E18). symmetry. exact P7. }
    assert (RK24 : getr (ms_regs ms) (Z_to_bv 5 24) = getr regs2 (Z_to_bv 5 24)).
    { apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 24) 37 (SOff 18 0x4d18) _ HS HAEf); [vm_compute; reflexivity | reflexivity |].
      rewrite (hw10_den_off _ 18 _ 0x4d18 E18). symmetry. exact P24. }
    assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 27; 7; 18; 24] ->
      getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
    { intros n Hn. cbn [In] in Hn.
      repeat (destruct Hn as [<-|Hn];
        [first [exact RK7 | exact RK24 | (apply RK; [vm_compute; discriminate | apply hw10_notin; vm_compute; reflexivity])] |]).
      destruct Hn. }
    assert (Hbs : length bs = S kk) by (unfold kz in *; lia).
    rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
    apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps off bs []).
    exact (hw10c_finish_RT cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt [] []
      (Z_to_bv 8 0) HP HRc HJ ltac:(eapply same_io_trans; apply HPgSteps.same_io_wvb) Hregs HKAB Hv Hsk Hsuf' Hbs). }
(* the cursor's byte x is read and stored *)
cbv beta iota in E35, HE, HAE.
assert (Hjr : (j < length rest)%nat) by (cbn [length] in Hrl; lia).
assert (Hkl : (kk < length bs)%nat) by (unfold kz in *; lia).
assert (Hsk : skipn kk bs = x :: fst (fuzz_u8s (length bs - S kk) r1)).
{ rewrite Hskip. replace (length bs - kk)%nat with (S (length bs - S kk)) by lia. apply hw10_fuzz_u8s_cons. }
assert (Hsuf' : hsu_suffix rest r1).
{ exists (S j). split; [lia | symmetry; exact (proj2 (hw10c_skipn_cons rest j x r1 (eq_sym Hrj)))]. }
assert (Hx : val_mem rsegs (mrestrict (w_H W2) mem2) cur 1 (bv_unsigned x)).
{ destruct (garr8_nthZ rsegs _ _ _ (Z.of_nat j) Hbytes ltac:(lia) ltac:(unfold hd_zbytes; rewrite length_map; lia)) as [V _].
  rewrite Nat2Z.id, (hw10c_nth_skipn rest j x r1 (eq_sym Hrj)) in V. rewrite Hcur. exact V. }
pose proof (bv_unsigned_in_range _ x) as Hxr. unfold bv_modulus in Hxr. change (Z.of_N 8) with 8 in Hxr.
destruct (Hindisj cur ltac:(lia)) as (_ & HnW & Hnp). unfold PP_SIZE in Hnp.
assert (HcurR : ~ (e_R (x_e cx) <= cur < e_R (x_e cx) + 0x198)).
{ intros X. apply HnW. unfold hd_inw. cbn [hi_w1 headamp_himg_B].
  apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [fst snd hd_xv]. lia. }
assert (HS : st_ok rsegs E (mkSS HW10_R hw10_sr_post
  [YP09.mkRegion (Some 34%nat) 0 1 0 1 []; hw10_rlen; hw10c_rR;
   YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))]] None
  (mkFacts [(18%nat, mkAF 4096 HW10_PPHI 4); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 8 5440 0);
            (33%nat, mkAF 8 5440 0); (34%nat, mkAF 4096 HW10_HI 0); (35%nat, mkAF 0 255 0);
            (36%nat, mkAF (2 ^ 64 - 1 - HW10_PPHI) (2 ^ 64 - 4097) 0);
            (10%nat, mkAF 1 (2 ^ 47 - 2) 0); (15%nat, mkAF 1 (2 ^ 47) 0); (16%nat, mkAF 1 1 0);
            (12%nat, mkAF 1 7 0); (13%nat, mkAF 0 6 0); (14%nat, mkAF 8 5440 0)]
     [mkAC BC_LTU (SOff 33 0) (SOff 32 0); mkAC BC_EQ (SAlu ALU_SRL (SOff 33 0) (SLit 14)) (SLit 0)]
     [(SAlu ALU_ADD (SOff 13 0) (SOff 14 0), SOff 33 0); (SAlu ALU_ADD (SOff 18 0) (SOff 33 0), SOff 34 0)]))
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 HW10_R) mem2 (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. subst E. apply (entry_st_ok_full rsegs).
  - unfold hw10_sr_post. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | |] | |].
    + intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X.
    + rewrite (hw10_den_off _ 18 _ 0x4000 E18). exact P7.
    + intros X; apply (f_equal (@bv_unsigned 5)) in X; vm_compute in X; discriminate X.
    + rewrite (hw10_den_off _ 18 _ 0x4d18 E18). exact P24.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + apply (hm_rw_region rsegs _ (w_H W2) mem2 34 (pp + off + kz)).
      * rewrite E34. rewrite unsigned_lit_small by lia. reflexivity.
      * lia. * lia.
      * intros o Ho. apply Hpres. lia.
      * constructor.
    + apply (hm_ro_region rsegs _ (w_H W2) mem2 18 pp); [rewrite E18; apply unsigned_lit_small; lia | lia | lia |].
      constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ pp 0x4000 8 (SOff 32 0) Lp).
      * exact (hw10_den_atom _ 32 Lp E32). * cbn. lia. * cbn. lia. * exact HLv.
    + apply (hm_ro_region rsegs _ (w_H W2) mem2 9 (e_R (x_e cx))); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val rsegs _ _ (e_R (x_e cx)) 0xf0 8 (SOff 36 0) (2 ^ 64 - pp - 1)).
        -- exact (hw10_den_atom _ 36 _ E36). -- cbn. lia. -- cbn. lia. -- exact Qf0.
      * apply (chunk_ok_val rsegs _ _ (e_R (x_e cx)) 0x150 8 _ (shadow_addr (pp + 0x4000))).
        -- apply (hw10_den_sh _ 18 pp 0x4000 E18); [lia | lia | exact E27].
        -- cbn. lia. -- cbn. lia. -- exact Q150.
    + apply (hm_ro_region rsegs _ (w_H W2) mem2 10 cur).
      * rewrite E10. rewrite unsigned_lit_small by lia. reflexivity.
      * lia. * lia.
      * constructor; [|constructor]. apply (chunk_ok_val rsegs _ _ cur 0 1 (SOff 35 0) (bv_unsigned x)).
        -- exact (hw10_den_atom _ 35 _ E35). -- cbn. lia. -- cbn. lia. -- rewrite Z.add_0_r. exact Hx.
  - apply pairwise_disjoint_of_extents.
    cbn [map zpairwise_disjoint zall_disjoint]. unfold YA0q.extent_of_region, zdisj.
    cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi fst snd hw10_rlen hw10c_rR].
    rewrite E34, E18, E9, E10, !unsigned_lit_small by lia.
    unfold T_SEG_STK, ASTACK in *. repeat split; lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias conds_ok alias_ok].
    refine (conj _ (conj (conj _ (conj _ I)) (conj _ (conj _ I)))).
    + cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E18, E27, E32, E33, E34, E35, E36, E10, E15, E16, E12, E13, E14.
      rewrite !unsigned_lit_small by (unfold SHADOW_OFF, HW10_PPHI; lia).
      repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF, HW10_PPHI, HW10_HI; lia);
      try (rewrite Z.pow_0_r; apply Z.mod_1_r).
      change (2 ^ 4) with 16. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal; [|lia]. exact Hal.
    + unfold acond_ok. cbn [ac_c ac_a ac_b].
      rewrite branch_ltu_U, (hw10_U_atom _ 33 _ E33 ltac:(lia)), (hw10_U_atom _ 32 _ E32 ltac:(lia)).
      apply Z.ltb_lt. lia.
    + unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, U_lit by lia.
      rewrite (hw10c_U_srl14 _ 33 (off + kz) E33 ltac:(lia)). reflexivity.
    + rewrite (hw10c_den_add _ 13 14 kz off E13 ltac:(lia) E14 ltac:(lia)), (hw10_den_atom _ 33 _ E33). f_equal. lia.
    + rewrite (hw10c_den_add _ 18 33 pp (off + kz) E18 ltac:(lia) E33 ltac:(lia)), (hw10_den_atom _ 34 _ E34). f_equal. lia. }
(* the shadow entries: the first block (the length word and the store target), the input byte *)
assert (SHOK : sh_ok rsegs hw10_Bx [mkSHE 18 0 0x4d20; mkSHE 34 0 1; mkSHE 10 0 1] E (mrestrict (w_H W2) mem2)).
{ constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (hw10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 18 0 0x4d20 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact (hw10_UB E E27) | | | lia];
    rewrite (hw10_U_atom E 18 _ E18 ltac:(lia)); lia.
  - apply (hw10_shent_blk B ly2 S2 W2 mem2 md2 E pp PP_SIZE 34 0 1 HAR Hinp);
    change (req_size PP_SIZE) with 19744; [exact Happ | exact (hw10_UB E E27) | | | lia];
    rewrite (hw10_U_atom E 34 _ E34 ltac:(lia)); lia.
  - apply (hw10_shent_in E _ 10 src (e_left (x_e cx)) cur 1 Hamr (hw10_UB E E27) (hw10_U_atom E 10 _ E10 ltac:(lia)));
      [lia | lia | lia | exact Hra]. }
unfold cfg_at. change (w64 (bi_R headamp_bld_B)) with (Z_to_bv 64 HW10_R).
aj_run_to_tok hw10_tbl_ok HS HJ SHOK hw10_Bspan HW10_RT.
all: try solve [hw10c_awr 37%nat E HAE0 E34 (pp + off + kz) pp Hinp Hfresh].
rename ms into msA. rename HF into HFa. rename HFr into HFra. rename HG into HGa.
srr_branch_tok hw10_tbl_ok HS SHOK hw10_Bspan.
- (* a2 - 1 <> 0: the next turn *)
  hw10c_agree 37%nat E HAE0 HAEb.
  rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 12 (cnt - kz) (-1)) in Hc;
    [| exact (hw10c_ew _ _ _ 12 _ HAEb ltac:(lia) E12) | lia | lia].
  rewrite U_lit in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  aj_run_to_tok hw10_tbl_ok HS HJ SHOK hw10_Bspan HW10_R.
  all: try solve [hw10c_awr 37%nat E HAE0 E34 (pp + off + kz) pp Hinp Hfresh].
  hw10c_agree 37%nat E HAE0 HAEf.
  assert (HKAB : forall a, 0 <= a < 2 ^ 64 -> a <> pp + off + kz ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. transitivity (aview rsegs (w_H W2) (ms_mem msA) a).
    - apply (hw10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem add_cond] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hw10_rlen hw10c_rR] in Hrb;
        [|lia|lia|lia].
      hw10c_at_in 37%nat E HAE0 34%nat E34 Hrb. rewrite unsigned_lit_small in Hrb by lia. apply Hn. lia.
    - apply (hw10_frame_kept _ _ _ _ _ HFra a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hw10_rlen hw10c_rR] in Hrb;
        [|lia|lia|lia].
      hw10c_at_in 37%nat E HAE0 34%nat E34 Hrb. rewrite unsigned_lit_small in Hrb by lia. apply Hn. lia. }
  assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned x)).
  { pose proof (HPgSteps.st_ok_region_at _ _ _ 0 _ HS eq_refl) as HRg.
    replace (pp + off + kz) with (pp + off + kz + 0) by lia.
    apply (hw10_field _ _ 34 (pp + off + kz) _ 0 1 0 1 0 1 (SOff 35 0) (bv_unsigned x) HRg);
      [ rewrite (hw10c_ew _ _ _ 34 _ HAEf ltac:(lia) E34); apply unsigned_lit_small; lia
      | left; reflexivity
      | exact (hw10_den_atom _ 35 _ (hw10c_ew _ _ _ 35 _ HAEf ltac:(lia) E35))
      | cbn; lia | cbn; lia ]. }
  pose proof (HPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 5; Z_to_bv 5 6; Z_to_bv 5 7; Z_to_bv 5 10; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 15;
     Z_to_bv 5 17; Z_to_bv 5 24] HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
  assert (RK7 : getr (ms_regs ms) (Z_to_bv 5 7) = getr regs2 (Z_to_bv 5 7)).
  { apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 7) 37 (SOff 18 0x4000) _ HS HAEf); [vm_compute; reflexivity | reflexivity |].
    rewrite (hw10_den_off _ 18 _ 0x4000 E18). symmetry. exact P7. }
  assert (RK24 : getr (ms_regs ms) (Z_to_bv 5 24) = getr regs2 (Z_to_bv 5 24)).
  { apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 24) 37 (SOff 18 0x4d18) _ HS HAEf); [vm_compute; reflexivity | reflexivity |].
    rewrite (hw10_den_off _ 18 _ 0x4d18 E18). symmetry. exact P24. }
  assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 27; 7; 18; 24] ->
    getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn];
      [first [exact RK7 | exact RK24 | (apply RK; [vm_compute; discriminate | apply hw10_notin; vm_compute; reflexivity])] |]).
    destruct Hn. }
  assert (R13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 (Z.of_nat (S kk))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 13) HS). hw10_sr_eval.
    rewrite (hw10_den_off _ 13 kz 1 (hw10c_ew _ _ _ 13 _ HAEf ltac:(lia) E13)).
    f_equal. unfold kz. lia. }
  assert (R12 : getr (ms_regs ms) (Z_to_bv 5 12) = w64 (cnt - Z.of_nat (S kk))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 12) HS). hw10_sr_eval.
    rewrite (hw10_den_off _ 12 (cnt - kz) (-1) (hw10c_ew _ _ _ 12 _ HAEf ltac:(lia) E12)).
    f_equal. unfold kz. lia. }
  assert (R14 : getr (ms_regs ms) (Z_to_bv 5 14) = w64 off).
  { rewrite RK; [exact P14 | vm_compute; discriminate | apply hw10_notin; vm_compute; reflexivity]. }
  assert (R16 : getr (ms_regs ms) (Z_to_bv 5 16) = w64 1).
  { rewrite RK; [exact P16 | vm_compute; discriminate | apply hw10_notin; vm_compute; reflexivity]. }
  assert (R10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (hsu_cur rsegs cx rest r1)).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 10) HS). hw10_sr_eval.
    rewrite (hw10_den_off _ 10 cur 1 (hw10c_ew _ _ _ 10 _ HAEf ltac:(lia) E10)).
    f_equal. unfold cur, hsu_cur. cbn [length]. lia. }
  assert (R15 : getr (ms_regs ms) (Z_to_bv 5 15) = w64 (Z.of_nat (length r1))).
  { rewrite (st_ok_restrict_reg rsegs (w_H W2) _ _ ms (Z_to_bv 5 15) HS). hw10_sr_eval.
    rewrite (hw10_den_off _ 15 (Z.of_nat (length (x :: r1))) (-1) (hw10c_ew _ _ _ 15 _ HAEf ltac:(lia) E15)).
    f_equal. cbn [length]. lia. }
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HR1 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps r1 off bs cnt).
  apply (hw10c_finish_R cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt (x :: r1) r1 x
    HP HRc HJ ltac:(eapply same_io_trans; apply HPgSteps.same_io_wvb) Hregs HKAB Hv Hsk Hsuf' R13 R12 R14 R16 R10 R15).
  unfold kz in *. lia.
- (* a2 - 1 = 0: the count is done *)
  hw10c_agree 37%nat E HAE0 HAEb.
  rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 12 (cnt - kz) (-1)) in Hc;
    [| exact (hw10c_ew _ _ _ 12 _ HAEb ltac:(lia) E12) | lia | lia].
  rewrite U_lit in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc.
  aj_run_to_tok hw10_tbl_ok HS HJ SHOK hw10_Bspan HW10_RT.
  all: try solve [hw10c_awr 37%nat E HAE0 E34 (pp + off + kz) pp Hinp Hfresh].
  hw10c_agree 37%nat E HAE0 HAEf.
  assert (HKAB : forall a, 0 <= a < 2 ^ 64 -> a <> pp + off + kz ->
    aview rsegs (w_H W2) (ms_mem ms) a = aview rsegs (w_H W2) mem2 a).
  { intros a Ha Hn. transitivity (aview rsegs (w_H W2) (ms_mem msA) a).
    - apply (hw10_frame_kept _ _ _ _ _ HFr a Ha). intros (rg & Hr & Hrb). cbn [ss_mem add_cond] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hw10_rlen hw10c_rR] in Hrb;
        [|lia|lia|lia].
      hw10c_at_in 37%nat E HAE0 34%nat E34 Hrb. rewrite unsigned_lit_small in Hrb by lia. apply Hn. lia.
    - apply (hw10_frame_kept _ _ _ _ _ HFra a Ha). intros (rg & Hr & Hrb). cbn [ss_mem] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hw10_rlen hw10c_rR] in Hrb;
        [|lia|lia|lia].
      hw10c_at_in 37%nat E HAE0 34%nat E34 Hrb. rewrite unsigned_lit_small in Hrb by lia. apply Hn. lia. }
  assert (Hv : val_mem rsegs (mrestrict (w_H W2) (ms_mem ms)) (pp + off + kz) 1 (bv_unsigned x)).
  { pose proof (HPgSteps.st_ok_region_at _ _ _ 0 _ HS eq_refl) as HRg.
    replace (pp + off + kz) with (pp + off + kz + 0) by lia.
    apply (hw10_field _ _ 34 (pp + off + kz) _ 0 1 0 1 0 1 (SOff 35 0) (bv_unsigned x) HRg);
      [ rewrite (hw10c_ew _ _ _ 34 _ HAEf ltac:(lia) E34); apply unsigned_lit_small; lia
      | left; reflexivity
      | exact (hw10_den_atom _ 35 _ (hw10c_ew _ _ _ 35 _ HAEf ltac:(lia) E35))
      | cbn; lia | cbn; lia ]. }
  pose proof (HPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs2 _ (w_H W2)
    [Z_to_bv 5 5; Z_to_bv 5 6; Z_to_bv 5 7; Z_to_bv 5 10; Z_to_bv 5 11; Z_to_bv 5 12; Z_to_bv 5 13; Z_to_bv 5 15;
     Z_to_bv 5 17; Z_to_bv 5 24] HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as RK.
  assert (RK7 : getr (ms_regs ms) (Z_to_bv 5 7) = getr regs2 (Z_to_bv 5 7)).
  { apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 7) 37 (SOff 18 0x4000) _ HS HAEf); [vm_compute; reflexivity | reflexivity |].
    rewrite (hw10_den_off _ 18 _ 0x4000 E18). symmetry. exact P7. }
  assert (RK24 : getr (ms_regs ms) (Z_to_bv 5 24) = getr regs2 (Z_to_bv 5 24)).
  { apply (hw10_reg E _ _ ms (w_H W2) (Z_to_bv 5 24) 37 (SOff 18 0x4d18) _ HS HAEf); [vm_compute; reflexivity | reflexivity |].
    rewrite (hw10_den_off _ 18 _ 0x4d18 E18). symmetry. exact P24. }
  assert (Hregs : forall n : Z, In n [2; 3; 4; 8; 9; 19; 27; 7; 18; 24] ->
    getr (ms_regs ms) (Z_to_bv 5 n) = getr regs2 (Z_to_bv 5 n)).
  { intros n Hn. cbn [In] in Hn.
    repeat (destruct Hn as [<-|Hn];
      [first [exact RK7 | exact RK24 | (apply RK; [vm_compute; discriminate | apply hw10_notin; vm_compute; reflexivity])] |]).
    destruct Hn. }
  assert (Hbs : length bs = S kk) by (unfold kz in *; lia).
  rewrite (st_ok_restrict_mkst rsegs (w_H W2) _ _ ms HS eq_refl). cbn [ss_pc].
  apply (HRT ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ sh ps off bs r1).
  exact (hw10c_finish_RT cx rest kk ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) _ sh ps off bs cnt (x :: r1) r1 x
    HP HRc HJ ltac:(eapply same_io_trans; apply HPgSteps.same_io_wvb) Hregs HKAB Hv Hsk Hsuf' Hbs).
Qed.
End c.
Print Assumptions hw10_corr.
