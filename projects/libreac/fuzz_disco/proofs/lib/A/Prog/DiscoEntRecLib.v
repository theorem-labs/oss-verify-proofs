(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 322 of its 355 lines of code are new or changed and 36 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame YC81.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC4b YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition rec_sr : list sv :=
  [SLit 0; SOff 531 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 532 0; SOff 533 0; SOff 534 0;
   SOff 2 0; SOff 60 0; SOff 535 0; SOff 536 0; SOff 537 0; SOff 538 0; SOff 516 2160; SOff 539 0;
   SOff 540 0; SOff 541 0; SOff 32 0; SOff 542 0; SLit WS_MASK; SOff 543 0; SOff 516 2992; SOff 544 0;
   SOff 545 0; SLit 32; SOff 516 2128; SOff 546 0; SOff 547 0; SOff 548 0; SOff 549 0; SOff 550 0].
Definition rec_inchunks : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 1 (SOff 551 0)); YP09.mkChunk 1 (CVal 1 (SOff 552 0))].
Definition rec_in_r (m : nat) : YP09.region := YP09.mkRegion (Some 540%nat) 0 (Z.of_nat m) 0 0 (firstn m rec_inchunks).
Definition rec_ext (m : nat) : smem := match m with O => [] | _ => [rec_in_r m] end.
Definition rec_rs (m : nat) : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 392 400 (dslot_chunks ++ []);
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 (dfhdr_chunks ++ []);
   fshadow_region AT_SH DFRAME_CLASS 0 0 (dsh_chunks dsh_loop);
   got_regionP; bcell_regionP 32] ++ rec_ext m.
Definition rec_fa : list (nat * afact) := [(551%nat, mkAF 0 255 0); (552%nat, mkAF 0 255 0)].
Definition rec_ss (m : nat) : sstate := mkSS REC_OFF rec_sr (rec_rs m) None (d_facts rec_fa []).

Lemma rl_swrap8 : forall b, 0 <= b < 256 -> bv_swrap 8 b = if b <? 128 then b else b - 256.
Proof.
intros b Hb. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 8) with 256. change (256 / 2) with 128.
destruct (Z.ltb_spec b 128).
- rewrite Z.mod_small by lia. lia.
- replace (b + 128) with ((b - 128) + 1 * 256) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma rl_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma rl_lor_add : forall a b, 0 <= a -> 0 <= b < 256 -> Z.lor (a * 256) b = a * 256 + b.
Proof.
intros a b Ha Hb.
assert (H0 : Z.land (a * 256) b = 0).
{ apply Z.bits_inj'. intros m Hm. rewrite Z.land_spec, Z.bits_0.
  change 256 with (2 ^ 8). rewrite <- Z.shiftl_mul_pow2 by lia.
  destruct (Z.lt_ge_cases m 8) as [Hl|Hg].
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - destruct (Z.eq_dec b 0) as [->|Hb0]; [rewrite Z.bits_0; apply andb_false_r|].
    rewrite (Z.bits_above_log2 b m); [apply andb_false_r | lia |].
    apply Z.log2_lt_pow2; [lia|]. change (2 ^ 8) with 256 in *. assert (2 ^ 8 <= 2 ^ m) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 8) with 256 in *. lia. }
rewrite <- Z.lxor_lor by exact H0. rewrite <- Z.add_nocarry_lxor by exact H0. reflexivity.
Qed.

Section u.
Variable E : env.
Lemma rl_U_sext8 : forall k b, ew E k = Z_to_bv 64 b -> 0 <= b < 256 ->
  U E (SExt true 8 (SOff k 0)) = if b <? 128 then b else b + (2 ^ 64 - 256).
Proof.
intros k b Hk Hb. rewrite U_SExt, (U_atom E k b Hk) by lia. change (2 ^ Z.of_N 8) with 256.
rewrite (Z.mod_small b 256) by lia. rewrite rl_swrap8 by lia. unfold zcanon, M64.
destruct (Z.ltb_spec b 128).
- apply Z.mod_small. lia.
- replace (b - 256) with ((b + (2 ^ 64 - 256)) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma rl_S_sext8 : forall k b, ew E k = Z_to_bv 64 b -> 0 <= b < 256 ->
  Sg E (SExt true 8 (SOff k 0)) = if b <? 128 then b else b - 256.
Proof.
intros k b Hk Hb. rewrite S_of_U, (rl_U_sext8 k b Hk Hb).
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 / 2) with (2 ^ 63).
destruct (Z.ltb_spec b 128).
- rewrite Z.mod_small by lia. lia.
- replace (b + (2 ^ 64 - 256) + 2 ^ 63) with ((b - 256 + 2 ^ 63) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma rl_br_ge : forall a b, branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (Sg E a <? Sg E b).
Proof. intros a b. reflexivity. Qed.
Lemma rl_S_and7 : forall k c v, ew E k = Z_to_bv 64 v -> 0 <= v -> 0 <= c -> v + c < 2 ^ 64 ->
  Sg E (SAlu ALU_AND (SOff k c) (SLit 7)) = (v + c) mod 8.
Proof.
intros k c v Hk Hv Hc Hvc. rewrite S_of_U. rewrite U_and_lit by lia. rewrite (U_atom_off E k v c Hk) by lia. rewrite rl_land7.
pose proof (Z.mod_pos_bound (v + c) 8 ltac:(lia)). apply swrap64_id. unfold half64. lia.
Qed.
Lemma rl_beq_cell : forall v s, ew E v = Z_to_bv 64 s -> 0 <= s < 8 ->
  branch_taken BC_EQ (sv_denot E (SExt true 8 (SOff v 0))) (sv_denot E (SLit 0)) = (s =? 0).
Proof.
intros v s Hv Hs. rewrite branch_eq_U, (rl_U_sext8 v s Hv) by lia. rewrite U_lit by lia.
destruct (Z.ltb_spec s 128); [reflexivity | lia].
Qed.
Lemma rl_bge_cell : forall k c x v s, ew E k = Z_to_bv 64 x -> 0 <= x -> 0 <= c -> x + c < 2 ^ 64 ->
  ew E v = Z_to_bv 64 s -> 0 <= s < 8 ->
  branch_taken BC_GE (sv_denot E (SAlu ALU_AND (SOff k c) (SLit 7))) (sv_denot E (SExt true 8 (SOff v 0)))
  = negb ((x + c) mod 8 <? s).
Proof.
intros k c x v s Hk Hx Hc Hxc Hv Hs. rewrite rl_br_ge, (rl_S_and7 k c x Hk Hx Hc Hxc), (rl_S_sext8 v s Hv) by lia.
destruct (Z.ltb_spec s 128); [reflexivity | lia].
Qed.
Lemma rl_beq_atom : forall q v w, ew E q = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff q 0)) (sv_denot E (SLit w)) = (v =? w).
Proof. intros q v w Hq Hv Hw. rewrite branch_eq_U, (U_atom E q v Hq) by lia. rewrite U_lit by lia. reflexivity. Qed.
Lemma rl_bne_atom : forall q v w, ew E q = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff q 0)) (sv_denot E (SLit w)) = negb (v =? w).
Proof. intros q v w Hq Hv Hw. rewrite branch_ne_U, (U_atom E q v Hq) by lia. rewrite U_lit by lia. reflexivity. Qed.
End u.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Definition rb (cx : dcx) (n j : Z) : Z := nth (Z.to_nat (c_n cx - n + j)) (map (fun b : byte => bv_unsigned b) (c_pl cx)) 0.
Definition rec_vals (cx : dcx) (i n now op : Z) (regs : bvmap 5 word) : list word :=
  [getr regs 1; getr regs 5; w64 i; w64 n; getr regs 10; w64 now; getr regs 12; getr regs 13; getr regs 15;
   w64 (d_cur cx n); w64 (if op <? 128 then op else op - 256); w64 (op mod 4); getr regs 21; getr regs 23;
   getr regs 24; w64 op; getr regs 28; getr regs 29; getr regs 30; getr regs 31; w64 (rb cx n 0); w64 (rb cx n 1)].

Lemma rb_range : forall cx n j, 0 <= rb cx n j < 256.
Proof.
intros cx n j. unfold rb. set (l := map (fun b : byte => bv_unsigned b) (c_pl cx)). set (k := Z.to_nat (c_n cx - n + j)).
destruct (Nat.lt_ge_cases k (length l)) as [Hk|Hk].
- assert (In (nth k l 0) l) by (apply nth_In; exact Hk). subst l. apply in_map_iff in H as (b & <- & _). apply u8_range.
- rewrite nth_overflow by exact Hk. lia.
Qed.
Lemma rec_ev : forall cx E i n now op regs (j q : nat), (j < 22)%nat -> q = (531 + j)%nat ->
  ew (d_env cx E (rec_vals cx i n now op regs)) q = nth j (rec_vals cx i n now op regs) (Z_to_bv 64 0).
Proof.
intros cx E i n now op regs j q Hj ->.
replace (531 + j)%nat with (AT_X + j)%nat by (unfold AT_X; lia).
apply d_env_x. unfold rec_vals. cbn [length]. lia.
Qed.
Lemma rl_val_mem_keep : forall (H : word -> bool) (m m' : word -> option byte) a (w : nat) v,
  val_mem SEGS (mrestrict H m) a w v -> (forall j, 0 <= j < Z.of_nat w -> aview SEGS H m' (a + j) = aview SEGS H m (a + j)) ->
  val_mem SEGS (mrestrict H m') a w v.
Proof.
intros H m m' a w v Hv Hk k Hkk. rewrite (mbyte_of_aview SEGS H H m m' (a + Z.of_nat k)); [apply Hv; exact Hkk|]. apply Hk. lia.
Qed.
Lemma rl_garr8_keep : forall (H : word -> bool) (m m' : word -> option byte) a l,
  garr8 SEGS (mrestrict H m) a l -> (forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS H m' (a + j) = aview SEGS H m (a + j)) ->
  garr8 SEGS (mrestrict H m') a l.
Proof.
intros H m m' a l G Hk j Hj. destruct (G j Hj) as (G1 & G2). split; [|exact G2].
apply (rl_val_mem_keep H m m' (a + Z.of_nat j) 1 _ G1). intros jj Hjj. replace (a + Z.of_nat j + jj) with (a + (Z.of_nat j + jj)) by lia.
apply Hk. lia.
Qed.
Lemma rl_meq_frame : forall E rs (H : word -> bool) (m0 m1 m2 : word -> option byte) lo hi,
  frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> lo <= a < hi) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m1 a = aview SEGS H m0 a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m2 a = aview SEGS H m0 a.
Proof.
intros E rs H m0 m1 m2 lo hi HF Hw HM a Ha Hn.
rewrite (kept_of_frame (segs := SEGS) E rs H m1 m2 (fun a => lo <= a < hi) HF Hw a Ha Hn). exact (HM a Ha Hn).
Qed.
Lemma rl_pres_grow : forall (H : word -> bool) (m0 m1 m2 : word -> option byte),
  mem_grows (mrestrict H m1) (mrestrict H m2) ->
  (forall a, apresent H m0 a -> apresent H m1 a) -> forall a, apresent H m0 a -> apresent H m2 a.
Proof.
intros H m0 m1 m2 HG HP a Ha. destruct (HP a Ha) as (Hh & b & Hb). split; [exact Hh|].
specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh in HG. rewrite Hb in HG.
destruct (m2 (Z_to_bv 64 a)) as [b'|] eqn:E2; [exists b'; reflexivity|]. exfalso. apply HG; [discriminate | reflexivity].
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.

Lemma rl_d_E_agree : forall cx E E', d_E cx E -> (forall k, (k < 530)%nat -> ew E' k = ew E k) -> d_E cx E'.
Proof.
intros cx E E' (EE & E32 & HEI & E60 & E516 & E529) AG.
split; [intros n r Hn; rewrite AG; [apply EE; exact Hn | pose proof (u5_range r); lia]|].
split; [rewrite AG by lia; exact E32|].
split; [intros a Ha; rewrite AG by (unfold A_LIM in Ha; lia); apply HEI; exact Ha|].
split; [rewrite AG by (unfold AT_A; lia); exact E60|].
split; [rewrite AG by (unfold AT_F; lia); exact E516|].
rewrite AG by (unfold AT_SH; lia); exact E529.
Qed.
Lemma rl_d_at_mono : forall cx pc kmax accmax (P P' : bvmap 5 word -> alayout -> astate -> world SEGS -> (word -> option byte) -> Model -> Prop) W c,
  d_at B MT XM_LIB RLO RHI tfib_K cx pc kmax accmax P W c ->
  (forall regs ly S W' mem md, P regs ly S W' mem md -> P' regs ly S W' mem md) ->
  d_at B MT XM_LIB RLO RHI tfib_K cx pc kmax accmax P' W c.
Proof.
intros cx pc kmax accmax P P' W c (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & Hfrm & HB & HJ & HF & Hk & Hev & Hmo & Hacc & HP) HPP.
exists fq, ly3, S3, regs, mem3, md3, k, acc. repeat (split; [assumption|]). apply HPP. exact HP.
Qed.
Lemma rl_A_range : forall cx, 608 <= d_S cx -> d_S cx - 608 < d_A cx <= d_S cx - 576 /\ d_A cx mod 32 = 0.
Proof.
intros cx HS. unfold d_A. pose proof (Z.div_mod (d_S cx - MFRAME) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (d_S cx - MFRAME) 32 ltac:(lia)) as M. unfold MFRAME in *.
split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.

Lemma rec_seat : forall (fq : YK11.FPState) (cx : dcx) (i n now op : Z) ly3 S3 (W3 : world SEGS) (regs : bvmap 5 word) mem3 md3 k
  (E : env) (m : nat),
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 mem3 md3 k ->
  d_E cx E -> Forall (region_ok SEGS E (rd W3 mem3)) (d_regions cx dsh_loop) ->
  rdword (aview SEGS (w_H W3) mem3) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) = Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  d_rD B cx i n now op regs ->
  (m <= 2)%nat -> Z.of_nat m <= n -> 0 <= i < 2 ^ 64 -> 0 <= now < 2 ^ 64 -> 0 <= op < 256 -> 0 <= n ->
  ((0 < m)%nat -> In (c_p cx, c_n cx) (ablocks B ly3 S3) /\ n <= c_n cx - 7 /\ c_n cx < 2 ^ 26 /\
     garr8 SEGS (rd W3 mem3) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
     off_img (c_p cx) (c_n cx) /\ Z.of_nat (length (c_pl cx)) = c_n cx) ->
  0 <= d_cur cx n < 2 ^ 64 ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E (rec_vals cx i n now op regs)) (rec_ss m)
    (restrict (w_H W3) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + REC_OFF)) mem3 (YK11.seg_rom SEGS))).
Proof.
intros fq cx i n now op ly3 S3 W3 regs mem3 md3 k E m HC HE HRG HFL HR Hm Hmn Ri Rnow Rop Rn Hin Rcur.
set (vals := rec_vals cx i n now op regs).
pose proof HC as (HB & HJ & HFR).
pose proof HB as ((HPRE & _) & _). pose proof HPRE as (HAR0 & _ & _ & Hgp0 & Htp0 & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (HAR & HLY & _).
pose proof HE as (EE & E32 & HEI & E60 & E516 & E529). unfold AT_A, AT_F, AT_SH in E60, E516, E529.
pose proof HR as ((Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25) & H6 & H7 & H11 & H14 & H16 & H17 & H19 & H22 & H26 & H27).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 HLY) as (_ & EFA3 & _).
assert (Hfin : In (DFRAME_CLASS, c_fpos cx) (frames S3)) by (rewrite HFR; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR Hfin) as (HF0 & HFc & HFapp).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hfin) as (HF32 & _).
rewrite EFA3 in HF0, HFc, HFapp, HF32. fold (d_FB cx) in HF0, HFc, HFapp, HF32.
assert (Hfb : fs_frame_bytes DFRAME_CLASS = 4096) by reflexivity. rewrite Hfb in *.
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold YG0f.ASAN_CEIL in CR.
assert (HS608 : 608 <= d_S cx) by (unfold d_S, LLVMF_STK in *; lia).
destruct (rl_A_range cx HS608) as [HAr HA32].
assert (HSr : 0 <= d_S cx <= 2 ^ 47) by (unfold d_S, LLVMF_STK in *; lia).
assert (HSlo : alloc_ceiling + 32768 <= d_S cx) by (unfold d_S, LLVMF_STK in *; lia).
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as Ho1. pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as Ho66.
assert (EL : forall q, (q < 530)%nat -> ew (d_env cx E vals) q = ew E q) by (intros q Hq; unfold d_env; apply ew_havoc_old; exact Hq).
assert (EV : forall q j, q = (531 + j)%nat -> (j < 22)%nat -> ew (d_env cx E vals) q = nth j vals (Z_to_bv 64 0)).
{ intros q j -> Hj. unfold d_env. replace (531 + j)%nat with (AT_FL + S j)%nat by (unfold AT_FL; lia).
  rewrite (ew_havoc_new E AT_FL _ (S j) (Z_to_bv 64 0)) by (cbn [length]; unfold vals, rec_vals; cbn [length]; lia). reflexivity. }
assert (Ecur : ew (d_env cx E vals) 540 = Z_to_bv 64 (d_cur cx n)) by exact (EV 540%nat 9%nat eq_refl ltac:(lia)).
assert (Uf : forall q v, ew E q = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E q) = v)
  by (intros q v Hq Hv; rewrite Hq; apply unsigned_lit_small; exact Hv).
assert (UFB : bv_unsigned (ew E 516) = d_FB cx) by (apply Uf; [exact E516 | lia]).
pose proof (pa_val_range (A_OBJ 1)) as RV1. pose proof (pa_val_range (A_OBJ 66)) as RV66.
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (apply img_env_atomP; [exact HEI | unfold A_OBJ, A_TEXT, A_LIM; lia]).
assert (EO66 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (apply img_env_atomP; [exact HEI | unfold A_OBJ, A_TEXT, A_LIM; lia]).
assert (E2 : ew E 2 = Z_to_bv 64 (d_S cx)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_loop ly3 S3 W3 regs mem3 md3 k E REC_OFF rec_sr vals [] [] (rec_ext m)
  (d_facts rec_fa []) HC HE HRG HFL) as HSEAT.
assert (Hm3 : m = 0%nat \/ m = 1%nat \/ m = 2%nat) by lia.
assert (HREGS : regs_ok (d_env cx E vals) rec_sr regs).
{ apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat (destruct Hr as [ <- | Hr ];
    [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
        let v := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with v end;
      lazymatch goal with
      | |- _ = sv_denot _ (SLit 0) => rewrite getr_zero; reflexivity
      | |- _ = sv_denot _ (SLit _) => cbn [sv_denot]; first [ exact H20 | exact H25 ]
      | |- _ = sv_denot _ (SOff 516 _) => cbn [sv_denot]; rewrite EL by lia; rewrite UFB;
          first [ rewrite H14 | rewrite H22 | rewrite H26 ]; unfold w64, d_obj, dobj_off; reflexivity
      | |- _ = sv_denot _ (SOff ?q 0) => rewrite sv_denot_SOff0;
          lazymatch eval vm_compute in (Nat.ltb q 530) with
          | true => rewrite EL by lia;
              first [ rewrite E60; first [ exact H9 | unfold w64; rewrite <- Hsp; unfold YG0d.spZ; symmetry; apply Z_to_bv_bv_unsigned ]
                    | rewrite E32; exact H18
                    | rewrite E2; exact H8
                    | rewrite (EE 3%nat 3%bv eq_refl), Hgp0; exact Hgp
                    | rewrite (EE 4%nat 4%bv eq_refl), Htp0; exact Htp ]
          | false => let j := eval vm_compute in (q - 531)%nat in
              rewrite (EV q j eq_refl ltac:(lia)); unfold vals, rec_vals; cbn [nth];
              first [ reflexivity | assumption ]
          end
      end
    | ]).
  destruct Hr. }
assert (HFACTS : facts_ok (d_env cx E vals) (d_facts rec_fa [])).
{ apply (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W3 mem3 md3 k E vals rec_fa [] HC HE); [|exact I].
  assert (AB : forall j q, (j < 2)%nat -> q = (551 + j)%nat -> afact_ok (d_env cx E vals) q (mkAF 0 255 0)).
  { intros j q Hj ->. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (EV (551 + j)%nat (20 + j)%nat ltac:(lia) ltac:(lia)).
    pose proof (rb_range cx n 0). pose proof (rb_range cx n 1).
    assert (Hj2 : j = 0%nat \/ j = 1%nat) by lia.
    destruct Hj2 as [ -> | -> ]; unfold vals, rec_vals; cbn [nth Nat.add]; unfold w64;
    rewrite unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia. }
  cbn [atoms_ok rec_fa]. split; [exact (AB 0%nat _ ltac:(lia) eq_refl)|]. split; [exact (AB 1%nat _ ltac:(lia) eq_refl) | exact I]. }
assert (HSUB : submem (rec_rs m) (d_kregions dsh_loop [] [] ++ rec_ext m)).
{ unfold rec_rs, d_kregions. cbn [app].
  apply submem_keep; [unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|]; intros c Hc; exact Hc|].
  apply submem_keep; [unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|]; intros c Hc; exact Hc|].
  apply submem_keep; [unfold subregion; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|]; intros c Hc; exact Hc|].
  apply submem_keep; [unfold subregion, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    split; [reflexivity|]; split; [lia|]; split; [lia|]; split; [lia|]; intros c Hc; exact Hc|].
  apply submem_keep; [apply subregion_refl|]. apply submem_keep; [apply subregion_refl|].
  apply submem_refl. }
destruct Hm3 as [Hm0 | Hm12].
- subst m.
  assert (HWF : regions_wf (d_kregions dsh_loop [] [] ++ rec_ext 0) = true) by (vm_compute; reflexivity).
  specialize (HSEAT HREGS HFACTS (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) HWF).
  exact (st_ok_pi_submem _ _ _ (rec_rs 0) HSEAT HSUB ltac:(vm_compute; reflexivity)).
- destruct (Hin ltac:(lia)) as (HinB & Hn7 & HN26 & HG & HOI & Hlen).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR HinB Hfin) as HBF.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HinB) as (Hp16 & Hp4k & Hpc & Hpapp & _).
  rewrite EFA3 in HBF. fold (d_FB cx) in HBF.
  assert (Hrq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  rewrite Hrq in Hpc, Hpapp, HBF. rewrite Hfb in HBF.
  assert (HEXT : Forall (region_ok SEGS (d_env cx E vals) (rd W3 mem3)) (rec_ext m)).
  { assert (CK : forall j, (j < 2)%nat -> Z.of_nat j < Z.of_nat m ->
      YP09.chunk_ok SEGS (d_env cx E vals) (rd W3 mem3) (d_cur cx n) (YP09.mkChunk (Z.of_nat j) (CVal 1 (SOff (551 + j) 0)))).
    { intros j Hj Hjm. apply (chunk_ok_val SEGS _ _ _ _ 1 _ (rb cx n (Z.of_nat j))).
      - rewrite sv_denot_SOff0, (EV (551 + j)%nat (20 + j)%nat ltac:(lia) ltac:(lia)).
        assert (Hj2 : j = 0%nat \/ j = 1%nat) by lia. destruct Hj2 as [ -> | -> ]; reflexivity.
      - pose proof (rb_range cx n (Z.of_nat j)). change (2 ^ (8 * Z.of_N 1)) with 256. lia.
      - cbn. lia.
      - change (N.to_nat 1) with 1%nat. unfold rb.
        assert (Hidx : (Z.to_nat (c_n cx - n + Z.of_nat j) < length (map (fun b : byte => bv_unsigned b) (c_pl cx)))%nat).
        { rewrite length_map. lia. }
        destruct (HG _ Hidx) as [Hv _]. unfold d_cur. rewrite Z2Nat.id in Hv by lia.
        replace (c_p cx + (c_n cx - n) + Z.of_nat j) with (c_p cx + (c_n cx - n + Z.of_nat j)) by lia. exact Hv. }
    destruct Hm12 as [ -> | -> ]; cbn [rec_ext]; apply Forall_cons; try apply Forall_nil;
    unfold region_ok, rec_in_r; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite Ecur; rewrite unsigned_lit_small by lia;
    (split; [lia|]); (split; [unfold d_cur in *; lia|]); (split; [intros o Ho; cbn in Ho; lia|]);
    cbn [firstn rec_inchunks]; repeat apply Forall_cons; try apply Forall_nil;
    first [ exact (CK 0%nat ltac:(lia) ltac:(lia)) | exact (CK 1%nat ltac:(lia) ltac:(lia)) ]. }
  assert (HPD : pairwise_disjoint (d_env cx E vals) (rec_ext m)) by (destruct Hm12 as [ -> | -> ]; cbn; tauto).
  assert (HAD : Forall (fun r => all_disjoint (d_env cx E vals) r (d_kregions dsh_loop [] [])) (rec_ext m)).
  { destruct Hm12 as [ -> | -> ]; cbn [rec_ext];
    apply Forall_cons; try apply Forall_nil; apply all_disjoint_of_extents; unfold extent_of_region, rec_in_r, d_kregions, fshadow_region,
      got_regionP, bcell_regionP; cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint]; unfold zdisj; cbn [fst snd];
    unfold AT_STK, AT_A, AT_F, AT_SH;
    rewrite Ecur, !EL by (unfold A_OBJ; lia); rewrite E2, E60, E516, E529, EO1, EO66; unfold w64;
    rewrite !unsigned_lit_small by (unfold d_cur, shadow_addr, SHADOW_OFF in *; unfold IMG_LO, IMG_TOP in *;
      pose proof (Z.div_pos (d_FB cx) 8 ltac:(lia)); pose proof (Z.div_le_upper_bound (d_FB cx) 8 (d_FB cx) ltac:(lia) ltac:(lia)); lia);
    change (fs_frame_bytes DFRAME_CLASS) with 4096; change (4096 / 8) with 512;
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, d_cur, shadow_addr, SHADOW_OFF, off_img, zdisjoint in *;
    unfold IMG_LO, IMG_TOP in *; cbn [fst snd] in HBF;
    pose proof (Z.div_mod (d_FB cx) 8 ltac:(lia)) as DF; pose proof (Z.mod_pos_bound (d_FB cx) 8 ltac:(lia));
    cbn [Z.of_nat]; repeat split; lia. }
  assert (HWF : regions_wf (d_kregions dsh_loop [] [] ++ rec_ext m) = true)
    by (destruct Hm12 as [ -> | -> ]; vm_compute; reflexivity).
  specialize (HSEAT HREGS HFACTS (Forall_nil _) (Forall_nil _) HEXT HPD HAD HWF).
  exact (st_ok_pi_submem _ _ _ (rec_rs m) HSEAT HSUB ltac:(destruct Hm12 as [ -> | -> ]; vm_compute; reflexivity)).
Qed.

End h.
End f.
End d.
