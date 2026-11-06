(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8c.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AE2d.v, proofs/cgif/cgif_file_fuzzer/lib/UI2d.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on image B (fuzz_grant.asan-ubsan, bin fde52226dc48, 0x8363c = BASE + 0x2c00, 367 slots), ported from lib/A/Prog/CtrlBuildGrantSweep.v at a working branch 5aae1e8a0ce (its Require closure: 196 files, 0 Admitted / admit / Axiom / Parameter), with the steps of the class-6 side-stack frame adapted from lib/A/Prog/CtrlStampHeadamp.v at the same commit (whose own cgif sources are proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, ACam.v, ACbf.v, ACf6.v, AChd.v); every address, constant and byte is image B's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/CtrlBuildGrantSweep.v, with its module paths and module names changed; 458 of its 493 lines of code are new or changed and 3975 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3FieldMDA.v; 423 of its 512 lines of code are new or changed and 404 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC45.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1h YC1i YC81 YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoArm3 DiscoArm3FieldCut DiscoArm3FieldPFKit DiscoArm3FieldPFXKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require DiscoArm3FieldModel ReacDiscoTableAge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c reac_disco_table_json_c disco_json_text disco_json_reader_model slot_ser_defs slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition pfd_CNT : nat := 563%nat.
Definition pfd_srx (b : Z) (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0
  | 2%nat => SOff AT_A 0
  | 8%nat => SOff AT_STK 0
  | 9%nat => SOff AT_A 0
  | 10%nat => SLit b
  | 18%nat => SLit WS_MASK
  | 19%nat => SOff 32 0
  | 20%nat => SLit 32
  | 21%nat => SOff AT_SH 0
  | 22%nat => SLit (2 ^ 64 - 1)
  | _ => SOff (AT_X + r) 0
  end.
Definition pfd_sr (b : Z) : list sv := map (pfd_srx b) (seq 0 32).
Definition pfd_acs : list YP09.chunk := [].
Definition pfd_fcs : list YP09.chunk := [YP09.mkChunk 2544 (CVal 4 (SOff pfd_CNT 0))].
Definition pfd_fa : list (nat * afact) :=
  [(pfd_CNT, mkAF 1 8 0); (554%nat, mkAF 0 7 0); (556%nat, mkAF 1 8 0)].
Definition pfd_G (cnd : branch_cond) : facts := d_facts pfd_fa [mkAC cnd (SOff 556 0) (SOff pfd_CNT 0)].
Definition pfd_rs : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 0 (dslot_chunks ++ pfd_acs);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ pfd_fcs);
   fshadow_region AT_SH DFRAME_CLASS 216 219 (dsh_chunks dsh_mac);
   got_regionP; bcell_regionP 32].
Definition pfd_keep (sr : list sv) : Prop :=
  sr_get sr 2 = SOff AT_A 0 /\ sr_get sr 3 = SOff 534 0 /\ sr_get sr 4 = SOff 535 0 /\
  sr_get sr 8 = SOff AT_STK 0 /\ sr_get sr 9 = SOff AT_A 0 /\ sr_get sr 18 = SLit WS_MASK /\
  sr_get sr 19 = SOff 32 0 /\ sr_get sr 20 = SLit 32 /\ sr_get sr 24 = SOff 555 0 /\
  sr_get sr 27 = SOff AT_SH 0.

Lemma pfd_subregion : forall b lo hi wlo whi wlo' whi' cs,
  whi' <= wlo' \/ (wlo <= wlo' /\ whi' <= whi) ->
  subregion (YP09.mkRegion b lo hi wlo' whi' cs) (YP09.mkRegion b lo hi wlo whi cs).
Proof.
  intros b lo hi wlo whi wlo' whi' cs Hw. unfold subregion.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hw|]. intros c Hc. exact Hc.
Qed.
Lemma pfd_subrefl : forall r, subregion r r.
Proof. intros [b lo hi wlo whi cs]. apply pfd_subregion. lia. Qed.
Lemma pfd_submem : submem pfd_rs (d_kregions dsh_mac pfd_acs pfd_fcs ++ []).
Proof.
  unfold pfd_rs, d_kregions, fshadow_region. rewrite app_nil_r.
  apply submem_keep; [apply pfd_subrefl|].
  apply submem_keep; [apply pfd_subregion; lia|].
  apply submem_keep; [apply pfd_subregion; lia|].
  apply submem_keep; [apply pfd_subregion; unfold DFRAME_SH; lia|].
  apply submem_keep; [apply pfd_subrefl|].
  apply submem_keep; [apply pfd_subrefl|].
  apply submem_nil.
Qed.
Lemma pfd_wf : regions_wf pfd_rs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pfd_kwf : regions_wf (d_kregions dsh_mac pfd_acs pfd_fcs ++ []) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pfd_inw : forall E a, in_wrange E pfd_rs a ->
  base_val E (Some AT_SH) + 216 <= a < base_val E (Some AT_SH) + 219.
Proof.
  intros E a (r & Hin & Hr). unfold pfd_rs in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
    unfold got_regionP, bcell_regionP, fshadow_region in Hr;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia.
Qed.
Lemma pfd_lts : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. rewrite bv_lts_signed.
  assert (Ux : bv_unsigned (Z_to_bv 64 x) = x) by (apply unsigned_lit_small; lia).
  assert (Uy : bv_unsigned (Z_to_bv 64 y) = y) by (apply unsigned_lit_small; lia).
  rewrite (bv_signed_small (Z_to_bv 64 x)) by lia. rewrite (bv_signed_small (Z_to_bv 64 y)) by lia.
  rewrite Ux, Uy. reflexivity.
Qed.
Lemma pfd_lt_true : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> x < y ->
  branch_taken BC_LT (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof.
  intros x y Hx Hy Hxy. cbn [branch_taken]. rewrite pfd_lts by assumption. apply Z.ltb_lt. exact Hxy.
Qed.
Lemma pfd_ge_true : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 -> y <= x ->
  branch_taken BC_GE (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
Proof.
  intros x y Hx Hy Hxy. change BC_GE with (neg_bc BC_LT). rewrite branch_taken_neg. cbn [branch_taken].
  rewrite pfd_lts by assumption. apply negb_true_iff, Z.ltb_ge. exact Hxy.
Qed.
Lemma pfd_soff : forall E n z b, bv_unsigned (ew E n) = b -> sv_denot E (SOff n z) = Z_to_bv 64 (b + z).
Proof. intros E n z b Hb. cbn [sv_denot]. rewrite Hb. reflexivity. Qed.
Lemma pfd_soffv : forall E n z v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n z) = Z_to_bv 64 (v + z).
Proof. intros E n z v H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hv. reflexivity. Qed.

Lemma pfd_slot24_len : forall buf vpad t, length vpad = 4%nat -> length (slot_ser_defs.slot24 buf vpad t) = 24%nat.
Proof.
  intros buf vpad t Hv. unfold slot_ser_defs.slot24. destruct (_ =? 0); [apply repeat_length|].
  rewrite !length_app, Hv. reflexivity.
Qed.
Lemma pfd_objs_len : forall buf vpad (os : list disco_json_reader_model.jobj), length vpad = 4%nat ->
  Forall (fun o => length o = 6%nat) os ->
  length (slot_ser_defs.objs_bytes buf vpad os) = (144 * length os)%nat.
Proof.
  intros buf vpad os Hv Ho. unfold slot_ser_defs.objs_bytes.
  assert (Hc : forall l, length (concat (map (slot_ser_defs.slot24 buf vpad) l)) = (24 * length l)%nat).
  { induction l as [|t l IHl]; [reflexivity|]. cbn [map concat length].
    rewrite length_app, IHl, pfd_slot24_len by exact Hv. lia. }
  induction Ho as [|o os' Hol Ho IH]; [reflexivity|].
  cbn [map concat length]. rewrite length_app, IH. unfold slot_ser_defs.obj_bytes. rewrite Hc, Hol. lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma pfd_env_reg : forall cx E regs ex (r : bv 5) a, a = (AT_X + Z.to_nat (bv_unsigned r))%nat ->
  ew (d_env cx E (a3f_vals regs ++ ex)) a = getr regs r.
Proof.
  intros cx E regs ex r a ->.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite d_env_x by (unfold a3f_vals; rewrite length_app, length_map, length_seq; lia).
  unfold a3f_vals. rewrite app_nth1 by (rewrite length_map, length_seq; lia).
  rewrite (nth_indep _ _ ((fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))) 0%nat))
    by (rewrite length_map, length_seq; lia).
  pose proof (map_nth (fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))) (seq 0 32) 0%nat
    (Z.to_nat (bv_unsigned r))) as Hm.
  cbv beta in Hm |- *. rewrite Hm, seq_nth by lia. cbn [Nat.add]. rewrite Z2Nat.id by lia.
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma pfd_atom : forall cx E regs ex (r : bv 5) a, a = (AT_X + Z.to_nat (bv_unsigned r))%nat ->
  sv_denot (d_env cx E (a3f_vals regs ++ ex)) (SOff a 0) = getr regs r.
Proof.
  intros cx E regs ex r a Ha. cbn [sv_denot].
  rewrite (pfd_env_reg cx E regs ex r a Ha), Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

Lemma pfd_reg : forall (fq : YK11.FPState) E ss ms (H : word -> bool) (r : bv 5) e v,
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> sv_denot E e = v ->
  getr (ms_regs ms) r = v.
Proof.
  intros fq E ss ms H r e v HS He Hv. rewrite (st_ok_pi_restrict_reg _ _ _ _ r HS), He. exact Hv.
Qed.

Section h.
Variable B : asyms.

Lemma pfd_regs_ok : forall cx E regs ex b, d_E cx E -> d_rLs B cx 0 regs ->
  getr regs 10 = w64 b -> getr regs 21 = w64 (shadow_addr (d_FB cx)) -> getr regs 22 = w64 (2 ^ 64 - 1) ->
  regs_ok (d_env cx E (a3f_vals regs ++ ex)) (pfd_sr b) regs.
Proof.
  intros cx E regs ex b HE HL H10 H21 H22.
  pose proof (d_E_env cx E (a3f_vals regs ++ ex) HE) as HE'.
  destruct HE' as (HER & H32 & _ & HA60 & _ & HSH). unfold AT_A in HA60. unfold AT_SH in HSH.
  destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20).
  assert (Hsp2 : getr regs 2 = w64 (d_A cx)).
  { unfold w64. replace (d_A cx) with (spZ regs) by lia. unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
  all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
         let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  all: cbn [sv_denot].
  all: first
    [ rewrite getr_zero; reflexivity
    | exact H10
    | exact H18
    | exact H20
    | exact H22
    | rewrite HSH, Z.add_0_r, Z_to_bv_bv_unsigned; exact H21
    | rewrite H32, Z.add_0_r, Z_to_bv_bv_unsigned; exact H19
    | rewrite (HER 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, H8; unfold w64, d_S, spZ;
      rewrite Z_to_bv_bv_unsigned; reflexivity
    | rewrite HA60, Z.add_0_r, Z_to_bv_bv_unsigned; first [ exact H9 | exact Hsp2 ]
    | match goal with |- getr ?rg ?x = Z_to_bv 64 (bv_unsigned (ew ?Ex ?a) + 0) =>
        rewrite (pfd_env_reg cx E regs ex x a eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end ].
Qed.

Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis DBRT : d_body_rt_stmt B.

Theorem a3f_pfd : pfD_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf count os vpad p j W c Hs.
unfold pf_c3, a3f_stg, d_at in Hs.
destruct Hs as (Hfrom & fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM0 & HBASE & HJ & HFR & Hk & Hnev & HMO &
  Hacc & Hi & Hn & Hnow & HRL & R24 & ((R21 & R22 & R23 & R25 & R26) & R10) &
  (HSP1 & HTAB & HBUF & HJR & HVP & HOO & (HSL & Hj & H408 & HUSED)) & HSP0 & HBODY).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20).
pose proof HSL as (Hp & H368 & H360).
pose proof HTAB as ((removed & HAM & HAP) & HGT).
pose proof HAP as (HLT1 & _ & _ & _ & _ & _ & HTOK1 & _).
destruct (DiscoArm3FieldModel.a3f_count_y T1 now count os HLT1 HTOK1 Hnow HJR) as (Ec & Hc08 & Los & Lo6 & _).
assert (LO : Z.of_nat (length (slot_ser_defs.objs_bytes buf vpad os)) <= 1296).
{ rewrite (pfd_objs_len buf vpad os HVP Lo6), Los. lia. }
pose proof HBODY as (TT & GG & LL & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & V184 & V120 & V136 & V376 & V280 & V232 & V264).
pose proof HE as (EE & E32 & HEI0 & E60 & EF & ESH).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GSHpres & GSTKpres & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_lt as Hceil0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo. clear GS16 GF32.
assert (HSHr : kLowMemEnd <= shadow_addr (d_FB cx) /\ shadow_addr (d_FB cx) + 512 <= kHighShadowEnd).
{ pose proof (YCbq.shadow_addr_bounds (d_FB cx) ltac:(lia)) as Q1.
  pose proof (YCbq.shadow_addr_bounds (d_FB cx + 4096) ltac:(lia)) as Q2.
  pose proof (YCbq.shadow_range_end (d_FB cx) 4096 ltac:(lia)) as Q3. change (4096 / 8) with 512 in Q3. lia. }
pose proof HBLK as (HPerm0 & _).
assert (Hinb : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinb) as (Hb16 & Hb4096 & Hbceil & HbApp & _).
pose proof (req_size_pos (Z.max (slot_ser_defs.ser_cap op) 1) ltac:(lia)) as (_ & Hrq).
pose proof HBUF as (Hr2 & HGB).
assert (Lb : Z.of_nat (length (a3_text T1 now ++ [0])) = a3_r T1 now + 1)
  by (unfold a3_r; rewrite length_app; cbn [length]; lia).
assert (LU : length (a3f_used p) = 32%nat) by (unfold a3f_used; reflexivity).
assert (HhA : in_app h (req_size HUNT_SIZE)).
{ assert (Hin : In (h, HUNT_SIZE) (ablocks B ly3 S3)).
  { apply (Permutation_in _ (Permutation_sym HPerm0)). apply in_or_app. right. left. reflexivity. }
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin))))). }
assert (HpA : 0 < c_n cx -> in_app (c_p cx) (req_size (c_n cx))).
{ intros Hc. pose proof HBASE as ((HPRE & _ & _ & _ & Hpn & _) & _). pose proof HPRE as (HAR0 & _).
  destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
  exact (proj1 (proj2 (proj2 (proj2 (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin))))). }
assert (Hro : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> 0 <= a < kLowMemEnd).
{ intros a [(s & Hs & _ & Hsa) | Hr]; apply pa_segs_low; [exists s; split; [exact Hs | exact Hsa] | exact (pa_relro_img a Hr)]. }
assert (NFS : forall x, (d_FB cx <= x < d_FB cx + 4096) \/ (d_S cx - 32768 <= x < d_S cx) \/
  (buf <= x < buf + req_size (Z.max (slot_ser_defs.ser_cap op) 1)) -> 0 <= x < 2 ^ 64 /\ ~ d_fsh cx x).
{ intros x Hx. unfold d_fsh. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. zlia. }
set (vals := a3f_vals regs ++ [Z_to_bv 64 count]).
assert (Lv : length vals = 33%nat)
  by (unfold vals, a3f_vals; rewrite length_app, length_map, length_seq; reflexivity).
pose proof (d_E_env cx E vals HE) as HE'.
pose proof HE' as (EE' & E32' & HEI & E60' & EF' & ESH').
assert (U60 : bv_unsigned (ew (d_env cx E vals) 60) = d_A cx).
{ change 60%nat with AT_A. rewrite E60'. unfold w64. apply unsigned_lit_small. lia. }
assert (U516 : bv_unsigned (ew (d_env cx E vals) 516) = d_FB cx).
{ change 516%nat with AT_F. rewrite EF'. unfold w64. apply unsigned_lit_small. lia. }
assert (U529 : bv_unsigned (ew (d_env cx E vals) 529) = shadow_addr (d_FB cx)).
{ change 529%nat with AT_SH. rewrite ESH'. unfold w64. apply unsigned_lit_small.
  unfold shadow_addr, SHADOW_OFF in *. lia. }
assert (U2 : bv_unsigned (ew (d_env cx E vals) 2) = d_S cx)
  by (rewrite (EE' 2%nat 2%bv eq_refl); reflexivity).
assert (U32 : bv_unsigned (ew (d_env cx E vals) 32) = SHADOW_OFF).
{ rewrite E32'. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
assert (E554 : ew (d_env cx E vals) 554 = Z_to_bv 64 (j - 1))
  by exact (eq_trans (pfd_env_reg cx E regs [Z_to_bv 64 count] (23%bv : bv 5) 554%nat eq_refl) R23).
assert (E556 : ew (d_env cx E vals) 556 = Z_to_bv 64 j)
  by exact (eq_trans (pfd_env_reg cx E regs [Z_to_bv 64 count] (25%bv : bv 5) 556%nat eq_refl) R25).
assert (E557 : ew (d_env cx E vals) 557 = Z_to_bv 64 (d_obj cx OT + 48 * (j - 1) + 2))
  by exact (eq_trans (pfd_env_reg cx E regs [Z_to_bv 64 count] (26%bv : bv 5) 557%nat eq_refl) R26).
assert (E563 : ew (d_env cx E vals) pfd_CNT = Z_to_bv 64 count)
  by (unfold pfd_CNT; exact (d_env_x cx E vals 32 ltac:(rewrite Lv; lia))).
assert (U563 : bv_unsigned (ew (d_env cx E vals) pfd_CNT) = count)
  by (rewrite E563; apply unsigned_lit_small; lia).
assert (HVC : val_mem SEGS (rd W mem3) (d_obj cx OT + 384) 4 count).
{ rewrite Ec. rewrite <- (ReacDiscoTableAge.ta_n_val T1 HLT1 (proj1 HTOK1)).
  apply (ReacDiscoTableAge.ta_vm_of_ga (rd W mem3) (d_obj cx OT) T1 384 4 HGT ltac:(lia)).
  rewrite HLT1. cbn [Z.of_nat]. lia. }
assert (SEAT : forall (b : Z) (cnd : branch_cond), getr regs 10 = w64 b ->
  branch_taken cnd (Z_to_bv 64 j) (Z_to_bv 64 count) = true ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) (mkSS PFR2_OFF (pfd_sr b) pfd_rs None (pfd_G cnd))
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + PFR2_OFF)) mem3 (YK11.seg_rom SEGS)))).
{ intros b cnd R10b Hcnd.
  assert (Hregs : regs_ok (d_env cx E vals) (pfd_sr b) regs).
  { unfold vals. apply (pfd_regs_ok cx E regs [Z_to_bv 64 count] b HE HRL R10b R21 R22). }
  assert (HGf : facts_ok (d_env cx E vals) (pfd_G cnd)).
  { apply (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals pfd_fa [mkAC cnd (SOff 556 0) (SOff pfd_CNT 0)] HCTX HE).
    - cbn [atoms_ok pfd_fa]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E563, E554, E556. rewrite !unsigned_lit_small by lia.
      rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; lia.
    - cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b sv_denot].
      rewrite E556, E563. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r. exact Hcnd. }
  assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx)) pfd_acs)
    by (unfold pfd_acs; apply Forall_nil).
  assert (Hfcs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_FB cx)) pfd_fcs).
  { apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (d_FB cx) 2544 4%N (SOff pfd_CNT 0) count).
    - cbn [sv_denot]. rewrite U563, Z.add_0_r. reflexivity.
    - cbn. lia.
    - cbn. lia.
    - replace (d_FB cx + 2544) with (d_obj cx OT + 384) by (unfold d_obj, dobj_off; lia). exact HVC. }
  pose proof (DSEAT LAWS PAL fq cx dsh_mac ly3 S3 W regs mem3 md3 k E PFR2_OFF (pfd_sr b) vals pfd_acs pfd_fcs []
    (pfd_G cnd) HCTX HE HREG HFLAG Hregs HGf Hacs Hfcs (Forall_nil _) I (Forall_nil _) pfd_kwf) as HS0.
  exact (st_ok_pi_submem _ _ _ pfd_rs HS0 pfd_submem pfd_wf). }
assert (HAWR : awr_ok (d_env cx E vals) pfd_rs LLVMF_STK (d_S cx) [] (ablocks B (c_ly cx) (c_S cx))
  (ablocks B ly3 S3) ly3 [(DFRAME_CLASS, c_fpos cx)]).
{ unfold pfd_rs.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 529%nat (shadow_addr (d_FB cx)));
    [reflexivity | exact U529 | |].
  { unfold fshadow_region. cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right.
    exists DFRAME_CLASS, (c_fpos cx). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia. }
  apply awr_ok_cons_ro; [unfold got_regionP; cbn; lia|].
  apply awr_ok_cons_ro; [unfold bcell_regionP; cbn; lia|].
  apply awr_ok_nil. }
assert (POST : forall (pc' : Z) (R' : bvmap 5 word -> Prop) (Y' : world SEGS -> (word -> option byte) -> Prop)
  (ss' : sstate) (ms : machine_state) (mat : list word),
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) ss' (restrict (w_H W) ms) ->
  ss_pc ss' = pc' -> ss_resv ss' = None -> d_land_chk dsh_ser2 (ss_mem ss') = true -> pfd_keep (ss_regs ss') ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) k ->
  frame_of (d_env cx E vals) pfd_rs (rd W mem3) (rd W (ms_mem ms)) ->
  mem_grows (rd W mem3) (rd W (ms_mem ms)) ->
  R' (ms_regs ms) ->
  (a3f_slots cx p count W (ms_mem ms) /\
   val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 408) 8 (d_obj cx OO + 144 * p) /\
   garr8 SEGS (rd W (ms_mem ms)) (d_obj cx OUSED) (a3f_used p) -> Y' W (ms_mem ms)) ->
  a3f_st B MT XM_LIB RLO RHI tfib_K cx h i n now op W0 c0 T0 T1 buf count os vpad pc' dsh_ser2 R' Y' W
    (mkCfg ms (with_vm_backing (m_vm_lazy md3) mat md3))).
{ intros pc' R' Y' ss' ms mat HS1 Hpc Hrv Hchk Hkp HJ1 HFr1 HG1 HR' HY'.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ d_fsh cx a ->
    rd W (ms_mem ms) (Z_to_bv 64 a) = rd W mem3 (Z_to_bv 64 a)).
  { intros a Ha Hns. apply HFr1. rewrite unsigned_lit_small by lia. intros Hw. apply pfd_inw in Hw.
    change (base_val (d_env cx E vals) (Some AT_SH)) with (bv_unsigned (ew (d_env cx E vals) 529)) in Hw.
    rewrite U529 in Hw. unfold d_fsh in Hns. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Hns. lia. }
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ d_fsh cx a ->
    mbyte SEGS (rd W (ms_mem ms)) a = mbyte SEGS (rd W mem3) a).
  { intros a Ha Hns. unfold mbyte. rewrite (KM a Ha Hns). reflexivity. }
  assert (KV : forall a (nn : nat) v,
    (forall x, a <= x < a + Z.of_nat nn -> 0 <= x < 2 ^ 64 /\ ~ d_fsh cx x) ->
    val_mem SEGS (rd W mem3) a nn v -> val_mem SEGS (rd W (ms_mem ms)) a nn v).
  { intros a nn v Hx Hv. apply (val_mem_frame SEGS (rd W mem3)); [|exact Hv].
    intros x Hxx. destruct (Hx x Hxx) as (X1 & X2). exact (KB x X1 X2). }
  assert (KG : forall a l,
    (forall x, a <= x < a + Z.of_nat (length l) -> 0 <= x < 2 ^ 64 /\ ~ d_fsh cx x) ->
    garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W (ms_mem ms)) a l).
  { intros a l Hx Hg. apply (garr8_frame SEGS (rd W mem3)); [exact Hg|].
    intros x Hxx. destruct (Hx x Hxx) as (X1 & X2). exact (KB x X1 X2). }
  assert (KS : forall off v, 0 <= off -> off + 8 <= 472 ->
    val_mem SEGS (rd W mem3) (d_A cx + off) 8 v -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + off) 8 v).
  { intros off v Ho Ho2 Hv. apply KV; [|exact Hv]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    apply NFS. right. left. lia. }
  assert (KF : forall a l, d_FB cx <= a -> a + Z.of_nat (length l) <= d_FB cx + 4096 ->
    garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W (ms_mem ms)) a l).
  { intros a l H1 H2 Hg. apply KG; [|exact Hg]. intros x Hx. apply NFS. left. lia. }
  assert (Q : forall r : bv 5, getr (ms_regs ms) r = sv_denot (d_env cx E vals) (sr_get (ss_regs ss') r))
    by (intros r; exact (st_ok_pi_restrict_reg _ _ _ _ r HS1)).
  destruct Hkp as (K2 & K3 & K4 & K8 & K9 & K18 & K19 & K20 & K24 & K27).
  assert (Q3 : getr (ms_regs ms) 3 = getr regs 3)
    by (rewrite Q, K3; exact (pfd_atom cx E regs [Z_to_bv 64 count] (3%bv : bv 5) 534%nat eq_refl)).
  assert (Q4 : getr (ms_regs ms) 4 = getr regs 4)
    by (rewrite Q, K4; exact (pfd_atom cx E regs [Z_to_bv 64 count] (4%bv : bv 5) 535%nat eq_refl)).
  assert (Q24 : getr (ms_regs ms) 24 = getr regs 24)
    by (rewrite Q, K24; exact (pfd_atom cx E regs [Z_to_bv 64 count] (24%bv : bv 5) 555%nat eq_refl)).
  assert (Q2 : getr (ms_regs ms) 2 = w64 (d_A cx)).
  { rewrite Q, K2. change AT_A with 60%nat. rewrite (pfd_soff _ _ _ _ U60). unfold w64. f_equal. lia. }
  assert (Q8 : getr (ms_regs ms) 8 = w64 (d_S cx)).
  { rewrite Q, K8. change AT_STK with 2%nat. rewrite (pfd_soff _ _ _ _ U2). unfold w64. f_equal. lia. }
  assert (Q9 : getr (ms_regs ms) 9 = w64 (d_A cx)).
  { rewrite Q, K9. change AT_A with 60%nat. rewrite (pfd_soff _ _ _ _ U60). unfold w64. f_equal. lia. }
  assert (Q18 : getr (ms_regs ms) 18 = w64 WS_MASK) by (rewrite Q, K18; reflexivity).
  assert (Q19 : getr (ms_regs ms) 19 = w64 SHADOW_OFF).
  { rewrite Q, K19. rewrite (pfd_soff _ _ _ _ U32). unfold w64. rewrite Z.add_0_r. reflexivity. }
  assert (Q20 : getr (ms_regs ms) 20 = w64 32) by (rewrite Q, K20; reflexivity).
  assert (Q27 : getr (ms_regs ms) 27 = w64 (shadow_addr (d_FB cx))).
  { rewrite Q, K27. change AT_SH with 529%nat. rewrite (pfd_soff _ _ _ _ U529). unfold w64. f_equal. lia. }
  assert (HHS1 : d_hslots cx h W (ms_mem ms)).
  { apply (d_hslots_kept cx h W W mem3 (ms_mem ms));
      [intros a Ha; apply (aview_eq_of SEGS); apply KM; [lia | apply NFS; right; left; lia]
      | exact (d_hslots_of_frame cx h dsh_mac W mem3 HFRM)]. }
  assert (HCTX1 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) k)
    by exact (conj HBASE (conj HJ1 HFR)).
  pose proof (d_land_hs B MT XM_LIB RLO RHI tfib_K DLAND LAWS FFL fq cx h dsh_ser2 ly3 S3 W
    (with_vm_backing (m_vm_lazy md3) mat md3) k (d_env cx E vals) ss' ms HCTX1 HE' (d_env_fl cx E vals) HS1 Hchk HHS1)
    as (HFRM1 & HSHD1).
  assert (HBODY1 : d_body B cx h n (a3_xb buf op) dsh_ser2 ly3 S3 W (ms_mem ms)).
  { apply (DBRT cx h n n (a3_xb buf op) dsh_mac dsh_ser2 ly3 S3 W mem3 (ms_mem ms) (d_A cx) (d_A cx)
      (fun a => d_fsh cx a) HBODY).
    - unfold LLVMF_STK. lia.
    - lia.
    - intros a Ha. right. intros Hr.
      unfold d_fsh in Ha. change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha.
      unfold d_rdset, d_objr, d_obj, dobj_off, dobj_size in Hr.
      change (req_size HUNT_SIZE) with 480 in HhA. unfold HUNT_SIZE in Hr.
      destruct Hr as [Hr | [Hr | [Hr | [Hr | [Hr | [(Hc & Hr) | [Hr | Hr]]]]]]].
      + zlia.
      + zlia.
      + zlia.
      + zlia.
      + zlia.
      + specialize (HpA Hc). unfold req_size in HpA. destruct (Z.eqb_spec (c_n cx) 0); [lia|]. zlia.
      + specialize (Hro a (proj1 Hr)). zlia.
      + unfold FF_canary in Hr. zlia.
    - intros a Ha Hna. apply (aview_eq_of SEGS). apply KM; [exact Ha | exact Hna].
    - intros a _ Ha. eapply apresent_grows; [exact HG1 | exact Ha].
    - exact HFRM1.
    - exact HSHD1.
    - lia. }
  assert (KY : a3f_slots cx p count W (ms_mem ms) /\
    val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 408) 8 (d_obj cx OO + 144 * p) /\
    garr8 SEGS (rd W (ms_mem ms)) (d_obj cx OUSED) (a3f_used p)).
  { split; [split; [exact Hp|]; split|split].
    - apply KS; [lia | lia | exact H368].
    - apply KS; [lia | lia | exact H360].
    - apply KS; [lia | lia | exact H408].
    - apply KF; [unfold d_obj, dobj_off; lia | | exact HUSED].
      rewrite LU. change (Z.of_nat 32) with 32. unfold d_obj, dobj_off. lia. }
  pose proof HSP1 as ((H208 & H320) & H192 & H200).
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS1 Hrv). rewrite Hpc.
  unfold a3f_st. split; [exact Hfrom|].
  unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md3) mat md3), k, acc.
  split; [reflexivity|].
  split; [exact HFRM0|].
  split; [exact HBASE|]. split; [exact HJ1|]. split; [exact HFR|]. split; [exact Hk|].
  split; [exact Hnev|]. split; [exact HMO|]. split; [exact Hacc|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split.
  { unfold d_rL. split; [unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia|].
    split; [rewrite Q3; exact Rgp|]. split; [rewrite Q4; exact Rtp|]. split; [exact Q8|].
    split; [exact Q9|]. split; [exact Q19|]. split; [exact Q18|]. split; [exact Q20 | exact Q27]. }
  split.
  { cbv beta. split; [rewrite Q24; exact R24|]. exact HR'. }
  split.
  { cbv beta.
    split; [split; [split|split]|].
    - apply KS; [lia | lia | exact H208].
    - apply KS; [lia | lia | exact H320].
    - apply KS; [lia | lia | exact H192].
    - apply KS; [lia | lia | exact H200].
    - split; [split; [exact (proj1 HTAB)|]|].
      + apply KF; [unfold d_obj, dobj_off; lia | | exact HGT].
        rewrite length_map, HLT1. change (Z.of_nat 400) with 400. unfold d_obj, dobj_off. lia.
      + split; [split; [exact Hr2|]|].
        * apply KG; [|exact HGB]. intros x Hx. rewrite Lb in Hx. apply NFS. right. right. lia.
        * split; [exact HJR|]. split; [exact HVP|]. split.
          -- apply KF; [unfold d_obj, dobj_off; lia | | exact HOO].
             rewrite length_map. unfold d_obj, dobj_off. lia.
          -- exact (HY' KY). }
  split.
  { split.
    - apply KS; [lia | lia | exact H208].
    - apply KS; [lia | lia | exact H320]. }
  exact HBODY1. }
pose proof (SRr_run_to_pi_AJ (fx := fq) (PI := PI) B LAWS) as RUNTOP.
destruct (Z.eqb_spec (j - 1) p) as [Ejp | Njp].
- assert (R10' : getr regs 10 = w64 1)
    by (rewrite R10; first [reflexivity | rewrite Ejp, Z.eqb_refl; reflexivity]).
  destruct (Z_lt_le_dec j count) as [Hjc | Hjc];
    [ pose proof (SEAT 1 BC_LT R10' (pfd_lt_true j count ltac:(lia) ltac:(lia) Hjc)) as HS
    | pose proof (SEAT 1 BC_GE R10' (pfd_ge_true j count ltac:(lia) ltac:(lia) Hjc)) as HS ];
    (unfold cfg_at, w64;
     paj_run_to_shc RUNTOP HS HJ PFX_OFF;
     [ exact HAWR
     | apply SRr_ret; right; unfold f_pfx;
       lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
         refine (POST PFX_OFF _ _ s ms mat HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
           ltac:(unfold pfd_keep; repeat split; vm_compute; reflexivity) HJ HFr HG _ _) end;
       [ cbv beta; apply (pfd_reg fq _ _ _ _ 22 (SOff 554 0) _ HS ltac:(vm_compute; reflexivity));
         rewrite (pfd_soffv _ _ _ _ E554 ltac:(lia)); unfold w64; f_equal; lia
       | intros (Sl & V408 & VU); cbv beta; split; [exact Sl|]; split; [exact V408 | exact VU] ] ]).
- assert (R10' : getr regs 10 = w64 0)
    by (rewrite R10; first [reflexivity | rewrite (proj2 (Z.eqb_neq _ _) Njp); reflexivity]).
  assert (Hjp : j <= p) by lia.
  pose proof (SEAT 0 BC_LT R10' (pfd_lt_true j count ltac:(lia) ltac:(lia) ltac:(lia))) as HS.
  unfold cfg_at, w64.
  paj_run_to_shc RUNTOP HS HJ PF_OFF.
  + exact HAWR.
  + apply SRr_ret. left. split; [exact Hjp|]. unfold f_pf.
    lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
      refine (POST PF_OFF _ _ s ms mat HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
        ltac:(unfold pfd_keep; repeat split; vm_compute; reflexivity) HJ HFr HG _ _) end.
    * cbv beta. split; [|split; [|split]].
      -- apply (pfd_reg fq _ _ _ _ 22 (SLit (2 ^ 64 - 1)) _ HS ltac:(vm_compute; reflexivity)). reflexivity.
      -- apply (pfd_reg fq _ _ _ _ 23 (SOff 554 1) _ HS ltac:(vm_compute; reflexivity)).
         rewrite (pfd_soffv _ _ _ _ E554 ltac:(lia)). unfold w64. f_equal; lia.
      -- apply (pfd_reg fq _ _ _ _ 25 (SOff 556 1) _ HS ltac:(vm_compute; reflexivity)).
         rewrite (pfd_soffv _ _ _ _ E556 ltac:(lia)). unfold w64. f_equal; lia.
      -- apply (pfd_reg fq _ _ _ _ 26 (SOff 557 48) _ HS ltac:(vm_compute; reflexivity)).
         rewrite (pfd_soffv _ _ _ _ E557 ltac:(unfold d_obj, dobj_off; lia)). unfold w64. f_equal; lia.
    * intros (Sl & V408 & VU). cbv beta. split; [exact Sl|]. split; [lia|]. split; [exact V408 | exact VU].
Qed.

End h.
End f.
End d.
