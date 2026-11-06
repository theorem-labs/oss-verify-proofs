(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 1029 of its 1060 lines of code are new or changed and 38 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody DiscoEntObsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c slot_observe slot_known.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition o2_sr (ai : Z) : list sv :=
  map (fun r => match r with 10%nat => SLit ai | 27%nat => SOff AT_F 2160 | _ => sr_x r end) (seq 0 32).
Definition o2_acs : list YP09.chunk :=
  map (fun kv => YP09.mkChunk (fst kv) (CVal 8 (SOff (snd kv) 0)))
  [(408, 563%nat); (344, 564%nat); (232, 565%nat); (216, 566%nat); (152, 567%nat); (248, 568%nat);
   (336, 569%nat); (368, 570%nat); (280, 571%nat)].
Definition o2_tcs : list YP09.chunk :=
  [YP09.mkChunk 2544 (CVal 4 (SOff 572 0)); YP09.mkChunk 2548 (CVal 4 (SOff 573 0)); YP09.mkChunk 2552 (CVal 4 (SOff 574 0))].
Definition o2_ecs (ai : Z) : list YP09.chunk :=
  if ai <? 0 then [] else
  map (fun kv => YP09.mkChunk (2160 + 48 * ai + fst (fst kv)) (CVal (snd (fst kv)) (SOff (snd kv) 0)))
  [(8, 4%N, 575%nat); (12, 1%N, 576%nat); (13, 1%N, 577%nat); (14, 1%N, 578%nat); (15, 1%N, 579%nat);
   (16, 1%N, 580%nat); (20, 4%N, 581%nat); (24, 4%N, 582%nat); (32, 8%N, 583%nat)].

Lemma o2_u_rng : forall (T : list byte) p (n : nat), 0 <= u_at T p n < 2 ^ (8 * Z.of_nat n).
Proof.
intros T p n. unfold u_at. pose proof (YK11.bytes_le_to_Z_nonneg (sub T p n)) as H0.
pose proof (YK11.bytes_le_to_Z_bound (sub T p n)) as H1.
assert (L : (length (sub T p n) <= n)%nat) by (unfold sub; rewrite length_firstn; lia).
split; [exact H0|]. eapply Z.lt_le_trans; [exact H1|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma o2_w64_u64 : forall v, Z_to_bv 64 (u64 v) = Z_to_bv 64 v.
Proof. intros v. unfold u64. exact (Z_to_bv64_canon v). Qed.
Lemma o2_u64_rng : forall v, 0 <= u64 v < 2 ^ 64.
Proof. intros v. unfold u64. apply Z.mod_pos_bound. lia. Qed.
Lemma o2_u64_small : forall v, 0 <= v < 2 ^ 64 -> u64 v = v.
Proof. intros v Hv. unfold u64. apply Z.mod_small. exact Hv. Qed.
Lemma o2_ble_cons : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (YK11.bytes_le_to_Z_nonneg bs) as Hr.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite <- Z.lxor_lor.
- rewrite Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
- apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
  + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
  + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.
Lemma o2_nth_le_byte : forall bs k (b : byte),
  nth_error bs k = Some b -> bv_unsigned b = (bytes_le_to_Z bs / 2 ^ (8 * Z.of_nat k)) mod 256.
Proof.
induction bs as [|b0 bs IHbs]; intros k b H; [destruct k; discriminate H|].
rewrite o2_ble_cons. pose proof (u8_range b0) as Hb0. pose proof (YK11.bytes_le_to_Z_nonneg bs) as Hr.
destruct k as [|k].
- cbn in H. injection H as <-. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. lia.
- cbn [nth_error] in H. rewrite (IHbs k b H).
  replace (8 * Z.of_nat (Datatypes.S k)) with (8 + 8 * Z.of_nat k) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  rewrite <- Z.div_div by lia. f_equal. f_equal. lia.
Qed.

Section u.
Variable E : env.
Lemma o2_dn_atom : forall a v, ew E a = Z_to_bv 64 v -> sv_denot E (SOff a 0) = Z_to_bv 64 v.
Proof. intros a v H. rewrite sv_denot_SOff0. exact H. Qed.
Lemma o2_dn_sx32 : forall a u, ew E a = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff a 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros a u H Hu. rewrite denot_lit_U, U_SExt, (U_atom E a u H) by lia. cbv iota.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small u) by lia. exact (Z_to_bv64_canon _).
Qed.
Lemma o2_dn_zx8 : forall a u, ew E a = Z_to_bv 64 u -> 0 <= u < 256 ->
  sv_denot E (SExt false 8 (SOff a 0)) = Z_to_bv 64 u.
Proof.
intros a u H Hu. rewrite denot_lit_U, U_SExt, (U_atom E a u H) by lia. cbv iota.
change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small u) by lia. exact (Z_to_bv64_canon _).
Qed.
Lemma o2_dn_own : forall a w, ew E a = Z_to_bv 64 (u64 w) ->
  sv_denot E (SAlu ALU_SRL (SAlu ALU_SLL (SOff a 0) (SLit 60)) (SLit 63)) = Z_to_bv 64 ((u64 w / 8) mod 2).
Proof.
intros a w H. pose proof (o2_u64_rng w) as R.
rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SLit, U_SLit, (U_atom E a (u64 w) H R).
change (Z.land (zcanon 60) 63) with 60. change (Z.land (zcanon 63) 63) with 63.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. f_equal. unfold zcanon, M64.
set (x := u64 w) in *. clearbody x.
change (2 ^ 60) with 1152921504606846976 in *. change (2 ^ 63) with 9223372036854775808 in *.
change (2 ^ 64) with 18446744073709551616 in *. lia.
Qed.
Lemma o2_dn_sx32u : forall a (T : list byte) p, ew E a = Z_to_bv 64 (u_at T p 4) ->
  sv_denot E (SExt true 32 (SOff a 0)) = Z_to_bv 64 (bv_swrap 32 (u_at T p 4)).
Proof.
intros a T p H. apply (o2_dn_sx32 a _ H). pose proof (o2_u_rng T p 4) as R.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R. exact R.
Qed.
Lemma o2_dn_zx8u : forall a (T : list byte) p, ew E a = Z_to_bv 64 (u_at T p 1) ->
  sv_denot E (SExt false 8 (SOff a 0)) = Z_to_bv 64 (u_at T p 1).
Proof.
intros a T p H. apply (o2_dn_zx8 a _ H). pose proof (o2_u_rng T p 1) as R.
change (2 ^ (8 * Z.of_nat 1)) with 256 in R. exact R.
Qed.
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
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma o2_vm_u64 : forall m a v, val_mem SEGS m a 8 v <-> val_mem SEGS m a 8 (u64 v).
Proof.
intros m a v. unfold val_mem, u64.
split; intros H k Hk; rewrite (H k Hk); first [unfold YO0f.le_byte | unfold YG0f.le_byte];
change (8 * Z.of_nat 8) with 64; rewrite ?Zmod_mod; reflexivity.
Qed.
Lemma o2_garr8_nth : forall (m : word -> option byte) base (L : list byte) j b,
  garr8 SEGS m base (map (fun b : byte => bv_unsigned b) L) -> nth_error L j = Some b ->
  mbyte SEGS m (base + Z.of_nat j) = Some b.
Proof.
intros m base L j b G Hj.
assert (Hl : (j < length L)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
rewrite (garr8_mbyte SEGS m base _ j G) by (rewrite length_map; exact Hl).
f_equal. rewrite (nth_error_nth _ j 0 (map_nth_error (fun b : byte => bv_unsigned b) j L Hj)). apply Z_to_bv_bv_unsigned.
Qed.
Lemma o2_u_val : forall (m : word -> option byte) t (T : list byte) p (n : nat),
  length T = 400%nat -> garr8 SEGS m t (map (fun b : byte => bv_unsigned b) T) ->
  0 <= p -> p + Z.of_nat n <= 400 ->
  val_mem SEGS m (t + p) n (u_at T p n).
Proof.
intros m t T p n LT GT Hp Hpn k Hk.
assert (Hlen : length (sub T p n) = n) by (unfold sub; rewrite length_firstn, length_skipn, LT; lia).
pose proof (o2_u_rng T p n) as Hb.
destruct (nth_error T (Z.to_nat p + k)) as [b|] eqn:Hb2; [|apply nth_error_None in Hb2; lia].
replace (t + p + Z.of_nat k) with (t + Z.of_nat (Z.to_nat p + k)) by lia.
rewrite (o2_garr8_nth m t T _ b GT Hb2). f_equal.
rewrite le_byte_small by first [exact Hk | exact Hb].
assert (Hs : nth_error (sub T p n) k = Some b).
{ unfold sub. rewrite nth_error_firstn. destruct (Nat.ltb_spec k n); [|lia]. rewrite nth_error_skipn. exact Hb2. }
pose proof (o2_nth_le_byte _ _ _ Hs) as Hv.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.shiftr_div_pow2 by lia. unfold u_at. rewrite <- Hv. first [reflexivity | symmetry; apply Z.mod_small; apply (u8_range b)].
Qed.
Lemma o2_vm_keep : forall (W W' : world SEGS) (m m' : word -> option byte) a n v,
  (forall j, (j < n)%nat -> aview SEGS (w_H W') m' (a + Z.of_nat j) = aview SEGS (w_H W) m (a + Z.of_nat j)) ->
  val_mem SEGS (rd W m) a n v -> val_mem SEGS (rd W' m') a n v.
Proof. intros W W' m m' a n v Hk H j Hj. rewrite (mbyte_of_aview SEGS _ _ _ _ _ (Hk j Hj)). exact (H j Hj). Qed.
Lemma o2_garr8_keep : forall (W W' : world SEGS) (m m' : word -> option byte) a l,
  (forall j, (j < length l)%nat -> aview SEGS (w_H W') m' (a + Z.of_nat j) = aview SEGS (w_H W) m (a + Z.of_nat j)) ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W' m') a l.
Proof.
intros W W' m m' a l Hk H j Hj. destruct (H j Hj) as [H1 H2]. split; [|exact H2].
apply (o2_vm_keep W W' m m' _ 1 _); [|exact H1].
intros k Hk'. replace (a + Z.of_nat j + Z.of_nat k) with (a + Z.of_nat j) by lia. exact (Hk j Hj).
Qed.
Lemma o2_pres_grow : forall (H : word -> bool) (m1 m2 : word -> option byte),
  mem_grows (mrestrict H m1) (mrestrict H m2) -> forall a, apresent H m1 a -> apresent H m2 a.
Proof.
intros H m1 m2 HG a (Hh & b & Hb). split; [exact Hh|].
specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite Hh in HG. rewrite Hb in HG.
destruct (m2 (Z_to_bv 64 a)) as [b'|] eqn:E2; [exists b'; reflexivity|]. exfalso. apply HG; [discriminate | reflexivity].
Qed.
Lemma o2_atom : forall cx E (regs : bvmap 5 word) X j, (j < length X)%nat ->
  ew (d_env cx E (obs_vals regs ++ X)) (563 + j) = nth j X (Z_to_bv 64 0).
Proof.
intros cx E regs X j Hj.
assert (L : length (obs_vals regs) = 32%nat) by (unfold obs_vals; rewrite length_map, length_seq; reflexivity).
replace (563 + j)%nat with (AT_X + (32 + j))%nat by (unfold AT_X; lia).
rewrite d_env_x by (rewrite length_app; lia).
rewrite app_nth2 by lia. rewrite L. f_equal. lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MT_TRIV : MT = ameter_triv.
#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).
#[local] Notation oc := (oc B).

Definition o2_x (cx : dcx) (h i now nb fr len w : Z) (T : list byte) (ai : Z) : list word :=
  [w64 (u64 w); w64 (u64 now); w64 (u64 i); w64 (u64 h); w64 (u64 (h + 440)); w64 (u64 (d_cur cx nb)); w64 (u64 len);
   w64 (u64 nb); w64 (u64 fr);
   w64 (u_at T 384 4); w64 (u_at T 388 4); w64 (u_at T 392 4);
   w64 (u_at T (48 * ai + 8) 4); w64 (u_at T (48 * ai + 12) 1); w64 (u_at T (48 * ai + 13) 1);
   w64 (u_at T (48 * ai + 14) 1); w64 (u_at T (48 * ai + 15) 1); w64 (u_at T (48 * ai + 16) 1);
   w64 (u_at T (48 * ai + 20) 4); w64 (u_at T (48 * ai + 24) 4); w64 (u_at T (48 * ai + 32) 8)].

Lemma o2_regs_ok : forall cx E (regs : bvmap 5 word) ai X, d_E cx E -> d_rL B cx regs -> 0 <= d_A cx < 2 ^ 64 ->
  getr regs 10 = w64 ai -> getr regs 27 = w64 (d_obj cx OT) ->
  regs_ok (d_env cx E (obs_vals regs ++ X)) (o2_sr ai) regs.
Proof.
intros cx E regs ai X HE HL HA R10 R27.
destruct HE as (HER & H32 & _ & HA60 & HF516 & _).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60. change AT_F with 516%nat in HF516.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
all: cbn [sv_denot].
all: first
  [ rewrite getr_zero; reflexivity
  | exact R10
  | rewrite R27; unfold d_env; rewrite ew_havoc_old by (cbv; lia); rewrite HF516; unfold w64; rewrite w64_add_w;
    unfold d_obj, dobj_off; reflexivity
  | rewrite Z.add_0_r; unfold d_env; rewrite ew_havoc_old by (cbv; lia);
    first [ rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18 ]
  | rewrite Z.add_0_r; unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth obs_vals map seq Nat.add AT_X AT_FL app];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; reflexivity ].
Qed.

Lemma o2_seat : forall (fq : YK11.FPState) cx h i n now op nb fr len Sg T ai w (regs : bvmap 5 word) ly3 S3 W mem3 md3 k E,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k ->
  d_E cx E -> Forall (region_ok SEGS E (rd W mem3)) (d_regions cx dsh_rec) ->
  rdword (aview SEGS (w_H W) mem3) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) = Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  oc cx h i n now op nb fr len Sg T regs ly3 S3 W mem3 ->
  getr regs 10 = w64 ai -> getr regs 27 = w64 (d_obj cx OT) -> -1 <= ai < 8 ->
  val_mem SEGS (rd W mem3) (d_A cx + 408) 8 w ->
  val_mem SEGS (rd W mem3) (d_A cx + 216) 8 h -> val_mem SEGS (rd W mem3) (d_A cx + 152) 8 (h + 440) ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E (obs_vals regs ++ o2_x cx h i now nb fr len w T ai))
    (ss_d (OBS_OFF + 16) (o2_sr ai) dsh_rec o2_acs (o2_tcs ++ o2_ecs ai) [] (d_facts [] []))
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + (OBS_OFF + 16))) mem3 (YK11.seg_rom SEGS))).
Proof.
intros fq cx h i n now op nb fr len Sg T ai w regs ly3 S3 W mem3 md3 k E HC HE HRG HFL HOC R10 R27 Hai H408 H216 H152.
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & (H232 & H344) & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof HC as (_ & HJ & _).
destruct (ob_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). ceil.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
assert (XA : forall j, (j < 21)%nat -> ew (d_env cx E (obs_vals regs ++ o2_x cx h i now nb fr len w T ai)) (563 + j) =
  nth j (o2_x cx h i now nb fr len w T ai) (Z_to_bv 64 0)) by (intros j Hj; apply o2_atom; cbn; lia).
apply (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E (OBS_OFF + 16) (o2_sr ai)
  (obs_vals regs ++ o2_x cx h i now nb fr len w T ai) o2_acs (o2_tcs ++ o2_ecs ai) [] (d_facts [] []) HC HE HRG HFL).
- exact (o2_regs_ok cx E regs ai _ HE HrL HAr2 R10 R27).
- exact (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E _ [] [] HC HE I I).
- unfold o2_acs. cbn [map fst snd].
  repeat apply Forall_cons; try apply Forall_nil;
  match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?q 0))) =>
    let j := eval vm_compute in (q - 563)%nat in
    let v := eval cbn [nth o2_x] in (nth j (o2_x cx h i now nb fr len w T ai) (Z_to_bv 64 0)) in
    lazymatch v with w64 (u64 ?z) =>
      apply (chunk_ok_val SEGS _ _ _ o 8 _ (u64 z));
      [ rewrite sv_denot_SOff0; exact (XA j ltac:(lia)) | apply o2_u64_rng | cbn; lia
      | apply (proj1 (o2_vm_u64 _ _ z)); assumption ]
    end
  end.
- apply Forall_app. split.
  + unfold o2_tcs. repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 4 (SOff ?q 0))) =>
      let j := eval vm_compute in (q - 563)%nat in
      let v := eval cbn [nth o2_x] in (nth j (o2_x cx h i now nb fr len w T ai) (Z_to_bv 64 0)) in
      lazymatch v with w64 (u_at T ?p 4) =>
        apply (chunk_ok_val SEGS _ _ _ o 4 _ (u_at T p 4));
        [ rewrite sv_denot_SOff0; exact (XA j ltac:(lia)) | exact (o2_u_rng T p 4) | cbn; lia
        | replace (d_FB cx + o) with (d_obj cx OT + p) by (unfold d_obj, dobj_off; lia);
          exact (o2_u_val _ _ T p 4 HTl HT ltac:(lia) ltac:(lia)) ]
      end
    end.
  + unfold o2_ecs. destruct (Z.ltb_spec ai 0) as [Hneg|Hpos]; [apply Forall_nil|].
    cbn [map fst snd].
    repeat apply Forall_cons; try apply Forall_nil;
    match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal ?wd (SOff ?q 0))) =>
      let j := eval vm_compute in (q - 563)%nat in
      let v := eval cbn [nth o2_x] in (nth j (o2_x cx h i now nb fr len w T ai) (Z_to_bv 64 0)) in
      lazymatch v with w64 (u_at T ?p ?nn) =>
        apply (chunk_ok_val SEGS _ _ _ o wd _ (u_at T p nn));
        [ rewrite sv_denot_SOff0; exact (XA j ltac:(lia)) | exact (o2_u_rng T p nn) | cbn; lia
        | replace (d_FB cx + o) with (d_obj cx OT + p) by (unfold d_obj, dobj_off; lia);
          exact (o2_u_val _ _ T p nn HTl HT ltac:(lia) ltac:(lia)) ]
      end
    end.
- apply Forall_nil.
- exact I.
- apply Forall_nil.
- assert (Hc : ai = -1 \/ ai = 0 \/ ai = 1 \/ ai = 2 \/ ai = 3 \/ ai = 4 \/ ai = 5 \/ ai = 6 \/ ai = 7) by lia.
  repeat (destruct Hc as [-> | Hc]; [vm_compute; reflexivity|]). subst ai. vm_compute; reflexivity.
Qed.

Lemma o2_oc_keep : forall cx h i n now op nb fr len Sg T (regs regs' : bvmap 5 word) ly3 S3 W mem3 mem' md k,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem' md k ->
  oc cx h i n now op nb fr len Sg T regs ly3 S3 W mem3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem3 a) ->
  (forall a, apresent (w_H W) mem3 a -> apresent (w_H W) mem' a) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr regs' r = getr regs r) ->
  d_frame cx h dsh_rec W mem' -> d_shadow cx dsh_rec W mem' ->
  val_mem SEGS (rd W mem') (d_A cx + 232) 8 i -> val_mem SEGS (rd W mem') (d_A cx + 344) 8 now ->
  val_mem SEGS (rd W mem') (d_A cx + 248) 8 (d_cur cx nb) -> val_mem SEGS (rd W mem') (d_A cx + 336) 8 len ->
  val_mem SEGS (rd W mem') (d_A cx + 368) 8 nb -> val_mem SEGS (rd W mem') (d_A cx + 280) 8 fr ->
  oc cx h i n now op nb fr len Sg T regs' ly3 S3 W mem'.
Proof.
intros cx h i n now op nb fr len Sg T regs regs' ly3 S3 W mem3 mem' md k HC HOC MEQ MPR RG HF' HSh' V232 V344 V248 V336 V368 V280.
destruct HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & _ & _ & _ & HBL & _).
pose proof HC as (_ & HJ & _).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem' md k HC) as (_ & HSlo & _ & HF4 & HFc & _ & _ & _ & _ & _ & _ & HAR & _).
destruct (ob_A_range B cx ly3 S3 W mem' md k HJ) as (HSr & _ & HAr & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). ceil.
assert (FAR : forall a, 0 <= a < d_S cx - LLVMF_STK -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem3 a).
{ intros a Ha. apply MEQ; unfold LLVMF_STK in *; lia. }
refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj _ (conj (conj V232 V344) (conj _ (conj HSgl (conj _ (conj HSf
  (conj V248 (conj V336 (conj V368 (conj V280 (conj Hlen (conj Hnb (conj HTl (conj _ (conj HTok _)))))))))))))))))))).
- destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25). unfold d_rL, spZ in *.
  rewrite (RG 2%bv ltac:(cbv; tauto)), (RG 3%bv ltac:(cbv; tauto)), (RG 4%bv ltac:(cbv; tauto)), (RG 8%bv ltac:(cbv; tauto)),
    (RG 9%bv ltac:(cbv; tauto)), (RG 18%bv ltac:(cbv; tauto)), (RG 20%bv ltac:(cbv; tauto)), (RG 25%bv ltac:(cbv; tauto)).
  repeat split; assumption.
- destruct Hfrm as (F1 & F2 & Fn & F3). split; [exact F1|]. split; [exact F2|]. split; [exact Fn|].
  apply (o2_garr8_keep W W mem3 mem' fr); [|exact F3].
  intros j Hj. rewrite length_map, length_firstn in Hj.
  destruct (Z.eq_dec len 0) as [L0|L0]; [subst len; cbn in Hj; lia|].
  assert (Hfr0 : fr <> 0) by (intros E0; apply L0; exact (F2 E0)).
  assert (Hin : In (fr, len) (ablocks B ly3 S3)).
  { destruct HBL as (Hperm & _). apply (Permutation_in _ (Permutation_sym Hperm)). unfold dxb.
    rewrite (proj2 (Z.eqb_neq fr 0) Hfr0). left. reflexivity. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4k & Hpc & _).
  assert (Hrq : req_size len = len) by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
  rewrite Hrq in Hpc. apply FAR. unfold LLVMF_STK in *. lia.
- apply (o2_garr8_keep W W mem3 mem' _); [|exact HSg].
  intros j Hj. rewrite length_map, HSgl in Hj. apply FAR. unfold d_obj, dobj_off, LLVMF_STK in *. lia.
- apply (o2_garr8_keep W W mem3 mem' _); [|exact HT].
  intros j Hj. rewrite length_map, HTl in Hj. apply FAR. unfold d_obj, dobj_off, LLVMF_STK in *. lia.
- apply (d_body_rt B cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 mem' (d_A cx) (d_A cx + 472)
    (fun a => d_A cx <= a < d_A cx + 472) Hbody).
  + unfold LLVMF_STK in *. lia.
  + lia.
  + intros a Ha. left. exact Ha.
  + intros a Ha HnR. exact (MEQ a Ha HnR).
  + intros a _ Ha. exact (MPR a Ha).
  + exact HF'.
  + exact HSh'.
  + lia.
Qed.

Lemma o2_land : forall (fq : YK11.FPState) cx h i n now op nb fr len Sg T kmax accmax ly3 S3 W mem3 md4 k acc E ss ms
   (regs : bvmap 5 word) pc (X : bvmap 5 word -> world SEGS -> (word -> option byte) -> Prop),
  d_base B MT XM_LIB RLO RHI tfib_K cx -> lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md4 k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= kmax -> st_nev S3 <= st_nev (c_S cx) + kmax -> mo_le MT (c_S cx) S3 acc -> acc <= accmax ->
  d_E cx E -> ew E AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  d_land_chk dsh_rec (ss_mem ss) = true ->
  oc cx h i n now op nb fr len Sg T regs ly3 S3 W mem3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a) ->
  (forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms) a) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr (ms_regs ms) r = getr regs r) ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 216) 8 h -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 152) 8 (h + 440) ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 232) 8 i -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 344) 8 now ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 248) 8 (d_cur cx nb) -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 336) 8 len ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 368) 8 nb -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 280) 8 fr ->
  X (ms_regs ms) W (ms_mem ms) ->
  DAT cx pc kmax accmax (fun regs' ly' S' W' mem' md' => oc cx h i n now op nb fr len Sg T regs' ly' S' W' mem' /\ X regs' W' mem')
    W (mkCfg ms md4).
Proof.
intros fq cx h i n now op nb fr len Sg T kmax accmax ly3 S3 W mem3 md4 k acc E ss ms regs pc X
  HB Hfz HJ HFR Hk Hev Hmo Hacc HE HFL HS Hrv Hpc Hchk HOC MEQ MPR RG V216 V152 V232 V344 V248 V336 V368 V280 HX.
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md4 k) by (split; [exact HB | split; [exact HJ | exact HFR]]).
destruct (d_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx h dsh_rec ly3 S3 W md4 k E ss ms HC HE HFL HS Hchk V216 V152)
  as [HF' HSh'].
pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md4, k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|].
split; [exact Hfz|]. split; [exact HB|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hev|].
split; [exact Hmo|]. split; [exact Hacc|].
split; [|exact HX].
exact (o2_oc_keep cx h i n now op nb fr len Sg T regs (ms_regs ms) ly3 S3 W mem3 (ms_mem ms) md4 k HC HOC MEQ MPR RG HF' HSh'
  V232 V344 V248 V336 V368 V280).
Qed.

Definition o2_X3 (cx : dcx) (T : list byte) (ai ow now : Z) (regs : bvmap 5 word) (W : world SEGS) (m : word -> option byte) : Prop :=
  getr regs 26 = w64 (d_obj cx OOUR) /\ ob_sp22 cx T ai W m /\ val_mem SEGS (rd W m) (d_A cx + 408) 8 ow /\
  getr regs 1 = w64 (BASE + 0x1804) /\ getr regs 10 = w64 (d_obj cx OT) /\ getr regs 11 = w64 (d_obj cx OS) /\
  getr regs 12 = w64 ow /\ getr regs 13 = w64 now /\ getr regs 19 = w64 (n_of T) /\ getr regs 24 = w64 (ov_of T) /\
  getr regs 23 = w64 (s32_at T 392) /\ getr regs 22 = w64 ai /\ getr regs 27 = w64 (d_obj cx OT).
#[local] Notation ob_c2 := (ob_c2 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c3 := (ob_c3 B MT XM_LIB RLO RHI tfib_K).
Lemma o2_c3_of : forall cx h i n now op nb fr len Sg kmax accmax T ai ow W c,
  find_res T (s_mac Sg) ai -> (ow = 0 \/ ow = 1) ->
  DAT cx AF_reac_disco_table_observe kmax accmax
    (fun regs ly S W' m md => oc cx h i n now op nb fr len Sg T regs ly S W' m /\ o2_X3 cx T ai ow now regs W' m) W c ->
  ob_c3 cx h i n now op nb fr len Sg kmax accmax W c.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax T ai ow W c HFR How
  (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & Hz & HB & HJ & HF & Hk & Hev & Hmo & Hacc & HOC & X).
exists fq, ly3, S3, regs, mem3, md3, k, acc. repeat (split; [assumption|]).
destruct X as (X26 & XSP & X408 & X1 & X10 & X11 & X12 & X13 & X19 & X24 & X23 & X22 & X27).
exists T, ai, ow. repeat (split; [assumption|]). assumption.
Qed.

Ltac o2_dn0 :=
  lazymatch goal with
  | |- sv_denot _ (SLit _) = _ => cbn [sv_denot]; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity
  | |- sv_denot ?Ex (SOff 240 ?kk) = _ =>
      lazymatch goal with HE : img_env _ _ Ex |- _ => exact (codeptr_val Ex kk HE) end
  | |- sv_denot _ (SOff 516 _) = _ =>
      cbn [sv_denot]; lazymatch goal with H : ew _ 516 = _ |- _ => rewrite H end; unfold w64; rewrite w64_add_w; reflexivity
  | |- sv_denot _ (SOff ?q 0) = _ =>
      rewrite sv_denot_SOff0; lazymatch goal with H : ew _ q = _ |- _ => rewrite H end; unfold w64; rewrite ?o2_w64_u64; reflexivity
  | |- sv_denot _ (SExt true 32 (SOff ?q 0)) = _ =>
      lazymatch goal with H : ew _ q = _ |- _ => rewrite (o2_dn_sx32u _ _ _ _ H) end; reflexivity
  | |- sv_denot _ (SExt false 8 (SOff ?q 0)) = _ =>
      lazymatch goal with H : ew _ q = _ |- _ => rewrite (o2_dn_zx8u _ _ _ _ H) end; reflexivity
  | |- sv_denot _ (SAlu ALU_SRL (SAlu ALU_SLL (SOff ?q 0) (SLit 60)) (SLit 63)) = _ =>
      lazymatch goal with H : ew _ q = _ |- _ => rewrite (o2_dn_own _ _ _ H) end; reflexivity
  end.
Ltac o2_fld RA UA :=
  eapply (DiscoACjr.field_of_region _ _ 60 _ _ _ _ _ _ _ 8 _ _ RA);
  [ exact UA | cbn [In]; repeat (first [left; reflexivity | right]) | rewrite o2_w64_u64; o2_dn0 | apply o2_u64_rng | cbn; lia ].
Ltac o2_reg HSpi :=
  lazymatch goal with |- getr (ms_regs ?msx) ?r = _ =>
    rewrite (st_ok_pi_restrict_reg _ _ _ msx r HSpi);
    lazymatch type of HSpi with st_ok_pi _ _ _ ?ssx _ =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e end;
    unfold w64; o2_dn0 end.
Ltac o2_awr UA :=
  cbn [ss_mem];
  repeat (first [ apply awr_ok_cons_ro; [cbn; lia|]
                | eapply awr_ok_cons_gen; [reflexivity | exact UA | intros a Ha; left; cbn [YP09.r_wlo YP09.r_whi] in Ha;
                    unfold LLVMF_STK; lia | ] ]);
  apply awr_ok_nil.
Ltac o2_hwin UA :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros b wlo whi a Hin Ha; vm_compute in Hin;
  repeat (destruct Hin as [Hin|Hin];
    [ injection Hin; intros; subst; cbn [base_val] in Ha; first [ lia | rewrite UA in Ha; lia ] | ]);
  destruct Hin.

Ltac o2_post23 UA HSpi :=
  lazymatch goal with HS : st_ok _ _ _ _ |- _ =>
    rewrite (pa_sigma_reac_disco_table_observe (PI := PI)) in HS;
    lazymatch type of HS with st_ok _ ?Ex (setpc ?ssx _) ?msx =>
      assert (HSpi : st_ok_pi SEGS VAL Ex (setpc ssx AF_reac_disco_table_observe) msx) by exact HS end;
    clear HS end.

Theorem ob_s23 : ob_seg23 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfz & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc & T & ai & w &
  HOC & R26 & R27 & R10 & HFR & H408).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & (H232 & H344) & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (ob_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). ceil.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
assert (Hai : -1 <= ai < 8) by (destruct HTok as (HT1 & _); unfold tbl_T1 in HT1; destruct HFR as [[-> _] | (Hr & _)]; lia).
pose proof (o2_seat fq cx h i n now op nb fr len Sg T ai w regs ly3 S3 W mem3 md3 k E HC HdE Hregs Hflag HOC R10 R27 Hai
  H408 Hh216 Hh152) as HS.
assert (XA : forall j, (j < 21)%nat -> ew (d_env cx E (obs_vals regs ++ o2_x cx h i now nb fr len w T ai)) (563 + j) =
  nth j (o2_x cx h i now nb fr len w T ai) (Z_to_bv 64 0)) by (intros j Hj; apply o2_atom; cbn; lia).
pose proof (XA 0%nat ltac:(lia)) as AX563. pose proof (XA 1%nat ltac:(lia)) as AX564. pose proof (XA 2%nat ltac:(lia)) as AX565.
pose proof (XA 3%nat ltac:(lia)) as AX566. pose proof (XA 4%nat ltac:(lia)) as AX567. pose proof (XA 5%nat ltac:(lia)) as AX568.
pose proof (XA 6%nat ltac:(lia)) as AX569. pose proof (XA 7%nat ltac:(lia)) as AX570. pose proof (XA 8%nat ltac:(lia)) as AX571.
pose proof (XA 9%nat ltac:(lia)) as AX572. pose proof (XA 10%nat ltac:(lia)) as AX573. pose proof (XA 11%nat ltac:(lia)) as AX574.
pose proof (XA 12%nat ltac:(lia)) as AX575. pose proof (XA 13%nat ltac:(lia)) as AX576. pose proof (XA 14%nat ltac:(lia)) as AX577.
pose proof (XA 15%nat ltac:(lia)) as AX578. pose proof (XA 16%nat ltac:(lia)) as AX579. pose proof (XA 17%nat ltac:(lia)) as AX580.
pose proof (XA 18%nat ltac:(lia)) as AX581. pose proof (XA 19%nat ltac:(lia)) as AX582. pose proof (XA 20%nat ltac:(lia)) as AX583.
cbn [nth o2_x Nat.add] in AX563, AX564, AX565, AX566, AX567, AX568, AX569, AX570, AX571, AX572, AX573, AX574, AX575, AX576,
  AX577, AX578, AX579, AX580, AX581, AX582, AX583.
clear XA.
pose proof (o2_regs_ok cx E regs ai (o2_x cx h i now nb fr len w T ai) HdE HrL HAr2 R10 R27) as A1.
pose proof (d_E_env cx E (obs_vals regs ++ o2_x cx h i now nb fr len w T ai) HdE) as HdE'.
pose proof (d_env_fl cx E (obs_vals regs ++ o2_x cx h i now nb fr len w T ai)) as HFL'.
assert (HEI : img_env VAL A_LIM (d_env cx E (obs_vals regs ++ o2_x cx h i now nb fr len w T ai))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (obs_vals regs ++ o2_x cx h i now nb fr len w T ai)) (rd W mem3)) by constructor.
set (Ev := d_env cx E (obs_vals regs ++ o2_x cx h i now nb fr len w T ai)) in *. clearbody Ev.
pose proof HdE' as (_ & _ & _ & E60 & E516 & _). change AT_A with 60%nat in E60. change AT_F with 516%nat in E516.
assert (UA : bv_unsigned (ew Ev 60) = d_A cx) by (rewrite E60; apply unsigned_lit_small; lia).
pose (RUN := paj_run (fx := fq) B LAWS).
set (ow := (u64 w / 8) mod 2).
assert (How : ow = 0 \/ ow = 1) by (pose proof (Z.mod_pos_bound (u64 w / 8) 2 ltac:(lia)); unfold ow; lia).
unfold cfg_at. change (w64 (BASE + (OBS_OFF + 16))) with (Z_to_bv 64 (BASE + (OBS_OFF + 16))).
assert (Hc : ai = -1 \/ ai = 0 \/ ai = 1 \/ ai = 2 \/ ai = 3 \/ ai = 4 \/ ai = 5 \/ ai = 6 \/ ai = 7) by lia.
clear Hai.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]].
all: (unfold ss_d in HS; ro_base HS 516%nat; ro_base HS 529%nat;
  paj_run_tok RUN HS HJ SHOK OBspan; [o2_awr UA|];
  o2_post23 UA HSpi;
  set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *;
  assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) ->
    aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a)
    by (apply (kept_of_frame (segs := SEGS) _ _ (w_H W) mem3 (ms_mem ms) (fun a => d_A cx <= a < d_A cx + 472) HFr); o2_hwin UA);
  pose proof (o2_pres_grow (w_H W) mem3 (ms_mem ms) HG) as MPR;
  assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr (ms_regs ms) r = getr regs r)
    by (let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr;
        rewrite (st_ok_pi_restrict_reg _ _ _ ms r HSpi), (A1 r);
        cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr);
  assert (G26 : getr (ms_regs ms) 26 = getr regs 26)
    by (rewrite (st_ok_pi_restrict_reg _ _ _ ms 26%bv HSpi), (A1 26%bv); f_equal; vm_compute; reflexivity);
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HSpi eq_refl) as RA; cbn [ms_mem restrict] in RA;
  assert (V216 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 216) 8 (u64 h)) by (o2_fld RA UA);
  assert (V152 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 152) 8 (u64 (h + 440))) by (o2_fld RA UA);
  assert (V232 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 232) 8 (u64 i)) by (o2_fld RA UA);
  assert (V344 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 344) 8 (u64 now)) by (o2_fld RA UA);
  assert (V248 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 248) 8 (u64 (d_cur cx nb))) by (o2_fld RA UA);
  assert (V336 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 336) 8 (u64 len)) by (o2_fld RA UA);
  assert (V368 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 368) 8 (u64 nb)) by (o2_fld RA UA);
  assert (V280 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 280) 8 (u64 fr)) by (o2_fld RA UA);
  apply SRr_ret;
  apply (o2_c3_of cx h i n now op nb fr len Sg kmax accmax T _ ow W _ HFR How);
  apply (o2_land fq cx h i n now op nb fr len Sg T kmax accmax ly3 S3 W mem3 md4 k acc Ev _ ms regs _ _ Hbase Hfz HJ Hfrs Hk Hnev
    Hmo Hacc HdE' HFL' HSpi eq_refl eq_refl ltac:(vm_compute; reflexivity) HOC MEQ MPR RG
    (proj2 (o2_vm_u64 _ _ _) V216) (proj2 (o2_vm_u64 _ _ _) V152) (proj2 (o2_vm_u64 _ _ _) V232) (proj2 (o2_vm_u64 _ _ _) V344)
    (proj2 (o2_vm_u64 _ _ _) V248) (proj2 (o2_vm_u64 _ _ _) V336) (proj2 (o2_vm_u64 _ _ _) V368) (proj2 (o2_vm_u64 _ _ _) V280));
  unfold o2_X3, ob_sp22;
  repeat match goal with |- _ /\ _ => split end;
  first [ rewrite G26; exact R26 | o2_reg HSpi | o2_fld RA UA | apply (proj2 (o2_vm_u64 _ _ _)); o2_fld RA UA ]).

Qed.

Lemma o2_obT_pt : forall cx now Sg T T' ai ow ret (W : world SEGS) (m m' : word -> option byte),
  (forall x, rd W m' x = rd W m x) -> obT cx now Sg T T' ai ow ret W m -> obT cx now Sg T T' ai ow ret W m'.
Proof.
intros cx now Sg T T' ai ow ret W m m' Hpt (LT & TO & FR & HOW & SP & V408 & OM).
destruct SP as (S88 & S80 & S392 & S136 & S128 & S120 & S112 & S104 & S224 & S96 & S72).
refine (conj LT (conj TO (conj FR (conj HOW (conj _ (conj (val_mem_pt _ _ _ _ _ Hpt V408) OM)))))).
refine (conj (val_mem_pt _ _ _ _ _ Hpt S88) (conj (val_mem_pt _ _ _ _ _ Hpt S80) (conj (val_mem_pt _ _ _ _ _ Hpt S392)
  (conj (val_mem_pt _ _ _ _ _ Hpt S136) (conj (val_mem_pt _ _ _ _ _ Hpt S128) (conj (val_mem_pt _ _ _ _ _ Hpt S120)
  (conj (val_mem_pt _ _ _ _ _ Hpt S112) (conj (val_mem_pt _ _ _ _ _ Hpt S104) (conj (val_mem_pt _ _ _ _ _ Hpt S224)
  (conj (val_mem_pt _ _ _ _ _ Hpt S96) (val_mem_pt _ _ _ _ _ Hpt S72))))))))))).
Qed.

Definition o2_X5 (cx : dcx) (now : Z) (Sg T T' : list byte) (ai ow ret : Z) (regs : bvmap 5 word) (W : world SEGS)
  (m : word -> option byte) : Prop :=
  getr regs 26 = w64 (d_obj cx OOUR) /\ obT cx now Sg T T' ai ow ret W m /\ ob_rT T ai regs /\
  getr regs 1 = w64 (BASE + 0x181c) /\ getr regs 10 = w64 (d_obj cx OT) /\ getr regs 21 = w64 ret /\
  getr regs 24 = w64 (ov_of T) /\ getr regs 23 = w64 (s32_at T 392) /\ getr regs 27 = w64 (d_obj cx OT).
#[local] Notation ob_c4 := (ob_c4 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c5 := (ob_c5 B MT XM_LIB RLO RHI tfib_K).
Lemma o2_c5_of : forall cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W c,
  DAT cx AF_check_table kmax accmax
    (fun regs ly S W' m md => oc cx h i n now op nb fr len Sg T' regs ly S W' m /\ o2_X5 cx now Sg T T' ai ow ret regs W' m) W c ->
  ob_c5 cx h i n now op nb fr len Sg kmax accmax W c.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W c
  (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & Hz & HB & HJ & HF & Hk & Hev & Hmo & Hacc & HOC & X).
exists fq, ly3, S3, regs, mem3, md3, k, acc. repeat (split; [assumption|]).
destruct X as (X26 & XT & XR & X1 & X10 & X21 & X24 & X23 & X27).
exists T, T', ai, ow, ret. repeat (split; [assumption|]). assumption.
Qed.

Theorem ob_s45 : ob_seg45 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfz & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ai & ow & ret & HOC & R26 & HOT & HRT & R10 & R24 & R23 & R27).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & (H232 & H344) & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (ob_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). ceil.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
pose proof HOT as (LT & TOK & HFR & HOW & HSP & H408 & HOM).
assert (Hret : ret = 0 \/ ret = 1) by exact (slot_observe.obs_ret T Sg ow now T' ret LT HSgl (proj1 TOK) HOM).
pose proof (regs_ok_obs B cx E regs HdE HrL HAr2) as A1.
assert (E541 : ew (d_env cx E (obs_vals regs)) 541 = w64 ret).
{ change 541%nat with (AT_X + 10)%nat. rewrite d_env_x by (unfold obs_vals; rewrite length_map, length_seq; lia).
  unfold obs_vals. cbn [nth map seq]. rewrite <- R10. f_equal; apply bv_eq; reflexivity. }
assert (HFA : facts_ok (d_env cx E (obs_vals regs)) (d_facts [(541%nat, mkAF 0 1 0)] [])).
{ apply (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E _ _ [] HC HdE); [|exact I].
  cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E541.
  unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E 0x1804 obs_sr (obs_vals regs)
  [] [] [] (d_facts [(541%nat, mkAF 0 1 0)] []) HC HdE Hregs Hflag A1 HFA (Forall_nil _) (Forall_nil _)
  (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
pose proof (d_E_env cx E (obs_vals regs) HdE) as HdE'.
pose proof (d_env_fl cx E (obs_vals regs)) as HFL'.
assert (HEI : img_env VAL A_LIM (d_env cx E (obs_vals regs))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (obs_vals regs)) (rd W mem3)) by constructor.
set (Ev := d_env cx E (obs_vals regs)) in *. clearbody Ev.
unfold ss_d in HS. ro_base HS 516%nat. ro_base HS 529%nat. ro_base HS 60%nat.
pose (RUN := paj_run (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + 0x1804)) with (Z_to_bv 64 (BASE + 0x1804)).
paj_run_tok RUN HS HJ SHOK OBspan.
{ cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
assert (Hpt := frame_of_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
assert (Hptr := frame_of_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
rewrite (pa_sigma_check_table (PI := PI)) in HS.
lazymatch type of HS with st_ok _ ?Ex (setpc ?ssx _) ?msx =>
  assert (HSpi : st_ok_pi SEGS VAL Ex (setpc ssx AF_check_table) msx) by exact HS end.
clear HS.
set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a)
  by (intros a _ _; apply aview_eq_of; apply Hptr).
assert (MPR : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a [Hh [b Hb]]; split; [exact Hh|]; exists b; rewrite Hpt; exact Hb).
assert (GU : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. rewrite (st_ok_pi_restrict_reg _ _ _ ms r HSpi), (A1 r).
  cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr (ms_regs ms) r = getr regs r)
  by (intros r Hr; apply GU; cbv [In] in Hr |- *; tauto).
assert (G10 : getr (ms_regs ms) 10 = getr regs 27)
  by (rewrite (st_ok_pi_restrict_reg _ _ _ ms 10%bv HSpi), (A1 27%bv); f_equal; vm_compute; reflexivity).
assert (G21 : getr (ms_regs ms) 21 = getr regs 10)
  by (rewrite (st_ok_pi_restrict_reg _ _ _ ms 21%bv HSpi), (A1 10%bv); f_equal; vm_compute; reflexivity).
assert (G1 : getr (ms_regs ms) 1 = w64 (BASE + 0x181c)) by o2_reg HSpi.
apply SRr_ret.
apply (o2_c5_of cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W _).
apply (o2_land fq cx h i n now op nb fr len Sg T' kmax accmax ly3 S3 W mem3 md4 k acc Ev _ ms regs _ _ Hbase Hfz HJ Hfrs Hk Hnev
  Hmo Hacc HdE' HFL' HSpi eq_refl eq_refl ltac:(vm_compute; reflexivity) HOC MEQ MPR RG
  (val_mem_pt _ _ _ _ _ Hptr Hh216) (val_mem_pt _ _ _ _ _ Hptr Hh152) (val_mem_pt _ _ _ _ _ Hptr H232)
  (val_mem_pt _ _ _ _ _ Hptr H344) (val_mem_pt _ _ _ _ _ Hptr H248) (val_mem_pt _ _ _ _ _ Hptr H336)
  (val_mem_pt _ _ _ _ _ Hptr H368) (val_mem_pt _ _ _ _ _ Hptr H280)).
destruct HRT as (R19 & R22).
refine (conj _ (conj (o2_obT_pt cx now Sg T T' ai ow ret W mem3 (ms_mem ms) Hptr HOT) (conj (conj _ _)
  (conj G1 (conj _ (conj _ (conj _ (conj _ _)))))))).
- rewrite GU by (cbv; tauto). exact R26.
- rewrite GU by (cbv; tauto). exact R19.
- rewrite GU by (cbv; tauto). exact R22.
- rewrite G10. exact R27.
- rewrite G21. exact R10.
- rewrite GU by (cbv; tauto). exact R24.
- rewrite GU by (cbv; tauto). exact R23.
- rewrite GU by (cbv; tauto). exact R27.
Qed.

Definition o6_seqc : acond :=
  mkAC BC_EQ (SExt true 32 (SOff 563 0))
    (SAluw ALU_ADD (SAlu ALU_ADD (SOff 552 0) (SOff 554 0))
       (SAlu ALU_AND (SAlu ALU_AND (SAlu ALU_SLT (SOff 553 0) (SLit 0)) (SAlu ALU_SLTU (SOff 555 0) (SLit 1)))
          (SAlu ALU_XOR (SAlu ALU_SLT (SOff 550 0) (SLit 8)) (SLit (-1))))).
Lemma o6_sw : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> bv_swrap 64 (zcanon (zcanon x)) = x.
Proof.
intros x Hx. rewrite (zcanon_wrap (zcanon x)), swrap_wrap', zcanon_wrap, swrap_wrap'. apply swrap64_id. unfold half64. lia.
Qed.
Lemma o6_z0 : forall x, - 2 ^ 63 <= x < 2 ^ 63 -> (zcanon (zcanon x) <? zcanon 1) = (x =? 0).
Proof.
intros x Hx. unfold zcanon, M64. rewrite Zmod_mod. change (1 mod 2 ^ 64) with 1.
destruct (Z.eqb_spec x 0) as [->|Hn]; [reflexivity|]. apply Z.ltb_ge.
destruct (Z.ltb_spec x 0) as [Hl|Hl].
- replace (x mod 2 ^ 64) with (x + 2 ^ 64).
  + lia.
  + apply (Z.mod_unique x (2 ^ 64) (-1)); lia.
- rewrite Z.mod_small by lia. lia.
Qed.
Lemma o6_flag : forall E (ai ov nn : Z),
  ew E 553 = Z_to_bv 64 ai -> - 2 ^ 63 <= ai < 2 ^ 63 ->
  ew E 555 = Z_to_bv 64 ov -> - 2 ^ 63 <= ov < 2 ^ 63 ->
  ew E 550 = Z_to_bv 64 nn -> - 2 ^ 63 <= nn < 2 ^ 63 ->
  U E (SAlu ALU_AND (SAlu ALU_AND (SAlu ALU_SLT (SOff 553 0) (SLit 0)) (SAlu ALU_SLTU (SOff 555 0) (SLit 1)))
        (SAlu ALU_XOR (SAlu ALU_SLT (SOff 550 0) (SLit 8)) (SLit (-1)))) =
  Z.b2z ((ai <? 0) && (ov =? 0) && negb (nn <? 8)).
Proof.
intros E ai ov nn Ha Ra Ho Ro Hn Rn.
rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, !U_SOff, Ha, Ho, Hn, !unsigned_lit, !Z.add_0_r.
rewrite (o6_sw ai Ra), (o6_sw nn Rn), (o6_z0 ov Ro).
change (bv_swrap 64 (zcanon 0)) with 0. change (bv_swrap 64 (zcanon 8)) with 8.
destruct (ai <? 0), (ov =? 0), (nn <? 8); vm_compute; reflexivity.
Qed.
Lemma o6_m64 : forall x, zcanon x mod 2 ^ 32 = x mod 2 ^ 32.
Proof.
intros x. unfold zcanon, M64. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32).
rewrite (Z.div_mod x (2 ^ 32 * 2 ^ 32)) at 2 by lia.
replace (2 ^ 32 * 2 ^ 32 * (x / (2 ^ 32 * 2 ^ 32)) + x mod (2 ^ 32 * 2 ^ 32))
  with (x mod (2 ^ 32 * 2 ^ 32) + (2 ^ 32 * (x / (2 ^ 32 * 2 ^ 32))) * 2 ^ 32) by ring.
rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma o6_arith : forall s ret f, 0 <= s < 2 ^ 32 ->
  ((s + ret + f) mod 2 ^ 32 - ((ret + bv_swrap 32 s) mod 2 ^ 32 + f mod 2 ^ 32)) mod 2 ^ 32 = 0.
Proof.
intros s ret f Hs.
assert (Hw : exists b, bv_swrap 32 s = s - 2 ^ 32 * b).
{ unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
  change (2 ^ 32 / 2) with (2 ^ 31).
  destruct (Z.ltb_spec s (2 ^ 31)).
  - exists 0. rewrite Z.mod_small by lia. lia.
  - exists 1. replace (s + 2 ^ 31) with ((s - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add, Z.mod_small by lia. lia. }
destruct Hw as [b ->].
replace (ret + (s - 2 ^ 32 * b)) with (ret + s + (- b) * 2 ^ 32) by ring.
rewrite Z_mod_plus_full.
rewrite Zminus_mod, Zmod_mod, <- Zplus_mod.
replace (ret + s + f) with (s + ret + f) by ring.
rewrite Z.sub_diag. reflexivity.
Qed.
Lemma o6_seq : forall E (u ret s ai ov nn : Z),
  ew E 563 = Z_to_bv 64 u -> 0 <= u < 2 ^ (8 * Z.of_nat 4) ->
  ew E 552 = Z_to_bv 64 ret -> 0 <= ret <= 1 ->
  ew E 554 = Z_to_bv 64 (bv_swrap 32 s) -> 0 <= s < 2 ^ (8 * Z.of_nat 4) ->
  ew E 553 = Z_to_bv 64 ai -> - 2 ^ 63 <= ai < 2 ^ 63 ->
  ew E 555 = Z_to_bv 64 ov -> - 2 ^ 63 <= ov < 2 ^ 63 ->
  ew E 550 = Z_to_bv 64 nn -> - 2 ^ 63 <= nn < 2 ^ 63 ->
  u = (s + ret + Z.b2z ((ai <? 0) && (ov =? 0) && negb (nn <? 8))) mod 2 ^ 32 ->
  acond_ok E o6_seqc.
Proof.
intros E u ret s ai ov nn Hu Ru Hr Rr Hs Rs Ha Ra Ho Ro Hn Rn Heq.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Ru, Rs.
unfold acond_ok, o6_seqc. cbn [ac_c ac_a ac_b].
rewrite branch_eq_U. apply Z.eqb_eq.
rewrite (U_of_S E (SAluw _ _ _)), S_SAluw. cbn [zalu_raw].
rewrite (o6_flag E ai ov nn Ha Ra Ho Ro Hn Rn).
rewrite U_SExt, (U_atom E 563 u Hu) by lia. cbv iota.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hr, Hs, !unsigned_lit, !Z.add_0_r.
set (f := Z.b2z ((ai <? 0) && (ov =? 0) && negb (nn <? 8))) in *.
clearbody f. subst u.
change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite (o6_m64 (zcanon (zcanon ret) + zcanon (zcanon (bv_swrap 32 s)))).
rewrite (Zplus_mod (zcanon (zcanon ret)) (zcanon (zcanon (bv_swrap 32 s))) (2 ^ 32)).
rewrite (o6_m64 (zcanon ret)), (o6_m64 ret), (o6_m64 (zcanon (bv_swrap 32 s))), (o6_m64 (bv_swrap 32 s)).
rewrite <- (Zplus_mod ret (bv_swrap 32 s) (2 ^ 32)).
rewrite (Zmod_mod (s + ret + f) (2 ^ 32)).
rewrite zcanon_wrap. f_equal.
apply (swrapN_congr 32). change (2 ^ Z.of_N 32) with (2 ^ 32).
apply o6_arith. exact Rs.
Qed.
Lemma o6_blt : forall E a v, ew E a = Z_to_bv 64 v -> - 2 ^ 63 <= v < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SOff a 0)) (sv_denot E (SLit 0)) = (v <? 0).
Proof.
intros E a v H Hv. change (branch_taken BC_LT (sv_denot E (SOff a 0)) (sv_denot E (SLit 0))) with (Sg E (SOff a 0) <? Sg E (SLit 0)).
rewrite S_SOff, S_SLit, H, unsigned_lit, Z.add_0_r, zcanon_wrap, swrap_wrap', swrap64_id by (unfold half64; lia). reflexivity.
Qed.

Definition o6_sr : list sv := map (fun r => match r with 27%nat => SOff AT_F 2160 | _ => sr_x r end) (seq 0 32).
Definition o6_acs : list YP09.chunk :=
  map (fun kv => YP09.mkChunk (fst kv) (CVal 8 (SOff (snd kv) 0)))
  [(368, 564%nat); (336, 565%nat); (280, 566%nat); (392, 567%nat); (248, 568%nat)].
Definition o6_fcs : list YP09.chunk := [YP09.mkChunk 2552 (CVal 4 (SOff 563 0))].
Definition o6_x (cx : dcx) (nb fr len : Z) (T T' : list byte) (ai : Z) : list word :=
  [w64 (u_at T' 392 4); w64 (u64 nb); w64 (u64 len); w64 (u64 fr); w64 (u64 (oldv ai (role_of_e T ai))); w64 (u64 (d_cur cx nb))].
#[local] Notation ob_c6 := (ob_c6 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c7 := (ob_c7 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c9 := (ob_c9 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation ob_c10 := (ob_c10 B MT XM_LIB RLO RHI tfib_K).

Lemma o6_regs_ok : forall cx E (regs : bvmap 5 word) X, d_E cx E -> d_rL B cx regs -> 0 <= d_A cx < 2 ^ 64 ->
  getr regs 27 = w64 (d_obj cx OT) -> regs_ok (d_env cx E (obs_vals regs ++ X)) o6_sr regs.
Proof.
intros cx E regs X HE HL HA R27.
destruct HE as (HER & H32 & _ & HA60 & HF516 & _).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60. change AT_F with 516%nat in HF516.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
all: cbn [sv_denot].
all: first
  [ rewrite getr_zero; reflexivity
  | rewrite R27; unfold d_env; rewrite ew_havoc_old by (cbv; lia); rewrite HF516; unfold w64; rewrite w64_add_w;
    unfold d_obj, dobj_off; reflexivity
  | rewrite Z.add_0_r; unfold d_env; rewrite ew_havoc_old by (cbv; lia);
    first [ rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18 ]
  | rewrite Z.add_0_r; unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth obs_vals map seq Nat.add AT_X AT_FL app];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; reflexivity ].
Qed.

Lemma o2_regatom : forall cx E (regs : bvmap 5 word) X (j : nat), (j < 32)%nat ->
  ew (d_env cx E (obs_vals regs ++ X)) (531 + j) = getr regs (Z_to_bv 5 (Z.of_nat j)).
Proof.
intros cx E regs X j Hj.
assert (L : length (obs_vals regs) = 32%nat) by (unfold obs_vals; rewrite length_map, length_seq; reflexivity).
replace (531 + j)%nat with (AT_X + j)%nat by (unfold AT_X; lia).
rewrite d_env_x by (rewrite length_app; lia).
rewrite app_nth1 by lia. unfold obs_vals.
rewrite (nth_indep _ _ ((fun r : nat => getr regs (Z_to_bv 5 (Z.of_nat r))) 0%nat)) by (rewrite length_map, length_seq; lia).
rewrite (map_nth (fun r : nat => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32) 0%nat j).
rewrite seq_nth by lia. reflexivity.
Qed.

Lemma o6_seat : forall (fq : YK11.FPState) cx h i n now op nb fr len Sg T T' ai ow ret (regs : bvmap 5 word) ly3 S3 W mem3 md3 k E cs,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k ->
  d_E cx E -> Forall (region_ok SEGS E (rd W mem3)) (d_regions cx dsh_rec) ->
  rdword (aview SEGS (w_H W) mem3) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) = Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  oc cx h i n now op nb fr len Sg T' regs ly3 S3 W mem3 -> obT cx now Sg T T' ai ow ret W mem3 ->
  getr regs 27 = w64 (d_obj cx OT) ->
  conds_ok (d_env cx E (obs_vals regs ++ o6_x cx nb fr len T T' ai)) cs ->
  st_ok_pi (fx := fq) SEGS VAL (d_env cx E (obs_vals regs ++ o6_x cx nb fr len T T' ai))
    (ss_d 0x181c o6_sr dsh_rec o6_acs o6_fcs [] (d_facts [] cs))
    (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + 0x181c)) mem3 (YK11.seg_rom SEGS))).
Proof.
intros fq cx h i n now op nb fr len Sg T T' ai ow ret regs ly3 S3 W mem3 md3 k E cs HC HE HRG HFL HOC HOT R27 HCS.
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & (H232 & H344) & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof HOT as (LT & TOK & HFR & HOW & (S88 & S80 & S392 & _) & H408 & HOM).
pose proof (proj2 (o2_vm_u64 _ _ _) S392) as S392'.
pose proof HC as (_ & HJ & _).
destruct (ob_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). ceil.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
assert (XA : forall j, (j < 6)%nat -> ew (d_env cx E (obs_vals regs ++ o6_x cx nb fr len T T' ai)) (563 + j) =
  nth j (o6_x cx nb fr len T T' ai) (Z_to_bv 64 0)) by (intros j Hj; apply o2_atom; cbn; lia).
apply (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E 0x181c o6_sr
  (obs_vals regs ++ o6_x cx nb fr len T T' ai) o6_acs o6_fcs [] (d_facts [] cs) HC HE HRG HFL).
- exact (o6_regs_ok cx E regs _ HE HrL HAr2 R27).
- exact (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E _ [] cs HC HE I HCS).
- unfold o6_acs. cbn [map fst snd].
  repeat apply Forall_cons; try apply Forall_nil;
  match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?q 0))) =>
    let j := eval vm_compute in (q - 563)%nat in
    let v := eval cbn [nth o6_x] in (nth j (o6_x cx nb fr len T T' ai) (Z_to_bv 64 0)) in
    lazymatch v with w64 (u64 ?z) =>
      apply (chunk_ok_val SEGS _ _ _ o 8 _ (u64 z));
      [ rewrite sv_denot_SOff0; exact (XA j ltac:(lia)) | apply o2_u64_rng | cbn; lia
      | apply (proj1 (o2_vm_u64 _ _ z)); assumption ]
    end
  end.
- unfold o6_fcs. apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ _ 2552 4 _ (u_at T' 392 4));
  [ rewrite sv_denot_SOff0; exact (XA 0%nat ltac:(lia)) | exact (o2_u_rng T' 392 4) | cbn; lia
  | replace (d_FB cx + 2552) with (d_obj cx OT + 392) by (unfold d_obj, dobj_off; lia);
    exact (o2_u_val _ _ T' 392 4 HTl HT ltac:(lia) ltac:(lia)) ].
- apply Forall_nil.
- exact I.
- apply Forall_nil.
- vm_compute; reflexivity.
Qed.

Definition o2_X7 (cx : dcx) (now : Z) (Sg T T' : list byte) (ai ow ret nb fr len : Z) (regs : bvmap 5 word) (W : world SEGS)
  (m : word -> option byte) : Prop :=
  getr regs 26 = w64 (d_obj cx OOUR) /\ obT cx now Sg T T' ai ow ret W m /\ ob_rT T ai regs /\ ob_rX nb fr len ret regs /\
  0 <= ai /\ role_of_e T ai = 1 /\
  getr regs 1 = w64 (BASE + 0x1874) /\ getr regs 10 = w64 (d_obj cx OT) /\ getr regs 11 = w64 (d_obj cx OS).
Definition o2_X9 (cx : dcx) (now : Z) (Sg T T' : list byte) (ai ow ret nb fr len : Z) (regs : bvmap 5 word) (W : world SEGS)
  (m : word -> option byte) : Prop :=
  getr regs 26 = w64 (d_obj cx OOUR) /\ obT cx now Sg T T' ai ow ret W m /\ ob_rT T ai regs /\ ob_rX nb fr len ret regs /\
  0 <= ai /\ getr regs 13 = w64 (d_obj cx OT).
Definition o2_X10 (cx : dcx) (now : Z) (Sg T T' : list byte) (ai ow ret nb fr len : Z) (regs : bvmap 5 word) (W : world SEGS)
  (m : word -> option byte) : Prop :=
  getr regs 26 = w64 (d_obj cx OOUR) /\ obT cx now Sg T T' ai ow ret W m /\ ob_rT T ai regs /\ ob_rX nb fr len ret regs /\
  ai < 0 /\ getr regs 13 = w64 (d_obj cx OT) /\ getr regs 14 = w64 (d_cur cx nb).
Lemma o2_c7_of : forall cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W c,
  DAT cx AF_find_entry kmax accmax
    (fun regs ly S W' m md => oc cx h i n now op nb fr len Sg T' regs ly S W' m /\ o2_X7 cx now Sg T T' ai ow ret nb fr len regs W' m)
    W c ->
  ob_c7 cx h i n now op nb fr len Sg kmax accmax W c.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W c
  (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & Hz & HB & HJ & HF & Hk & Hev & Hmo & Hacc & HOC & X).
exists fq, ly3, S3, regs, mem3, md3, k, acc. repeat (split; [assumption|]).
destruct X as (X26 & XT & XR & XX & X0 & XR1 & X1 & X10 & X11).
exists T, T', ai, ow, ret. repeat (split; [assumption|]). assumption.
Qed.
Lemma o2_c9_of : forall cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W c,
  DAT cx 0x18b8 kmax accmax
    (fun regs ly S W' m md => oc cx h i n now op nb fr len Sg T' regs ly S W' m /\ o2_X9 cx now Sg T T' ai ow ret nb fr len regs W' m)
    W c ->
  ob_c9 cx h i n now op nb fr len Sg kmax accmax W c.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W c
  (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & Hz & HB & HJ & HF & Hk & Hev & Hmo & Hacc & HOC & X).
exists fq, ly3, S3, regs, mem3, md3, k, acc. repeat (split; [assumption|]).
destruct X as (X26 & XT & XR & XX & X0 & X13).
exists T, T', ai, ow, ret. repeat (split; [assumption|]). assumption.
Qed.
Lemma o2_c10_of : forall cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W c,
  DAT cx 0x1b78 kmax accmax
    (fun regs ly S W' m md => oc cx h i n now op nb fr len Sg T' regs ly S W' m /\ o2_X10 cx now Sg T T' ai ow ret nb fr len regs W' m)
    W c ->
  ob_c10 cx h i n now op nb fr len Sg kmax accmax W c.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W c
  (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & Hc & Hz & HB & HJ & HF & Hk & Hev & Hmo & Hacc & HOC & X).
exists fq, ly3, S3, regs, mem3, md3, k, acc. repeat (split; [assumption|]).
destruct X as (X26 & XT & XR & XX & X0 & X13 & X14).
exists T, T', ai, ow, ret. repeat (split; [assumption|]). assumption.
Qed.

Theorem ob_s67 : ob_seg67 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfz & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ai & ow & ret & HOC & R26 & HOT & HRT & R21 & R24 & R23 & R27).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & (H232 & H344) & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (ob_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). ceil.
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
pose proof HOT as (LT & TOK & HFR & HOW & HSP & H408 & HOM).
pose proof TOK as (HT1 & HT2 & _).
destruct HRT as (R19 & R22).
destruct (slot_observe.seq_target T Sg ow now T' ret ai LT HSgl HT1 HFR HOM) as (Hr0 & Hrf & EST).
assert (Hai : -1 <= ai < 8) by (unfold tbl_T1 in HT1; destruct HFR as [[-> _] | (Hr & _)]; lia).
assert (Hn8 : 0 <= n_of T <= 8) by exact HT1.
assert (Hov : - 2 ^ 31 <= ov_of T < 2 ^ 31) by (unfold ov_of, s32_at; apply swrap32_range).
assert (Hret : 0 <= ret <= 1) by (destruct (_ && _); cbn in Hrf; lia).
set (X := o6_x cx nb fr len T T' ai).
set (Ev := d_env cx E (obs_vals regs ++ X)).
assert (E550 : ew Ev 550 = w64 (n_of T))
  by (unfold Ev; change 550%nat with (531 + 19)%nat; rewrite (o2_regatom cx E regs X 19 ltac:(lia)), <- R19; f_equal; apply bv_eq; reflexivity).
assert (E552 : ew Ev 552 = w64 ret)
  by (unfold Ev; change 552%nat with (531 + 21)%nat; rewrite (o2_regatom cx E regs X 21 ltac:(lia)), <- R21; f_equal; apply bv_eq; reflexivity).
assert (E553 : ew Ev 553 = w64 ai)
  by (unfold Ev; change 553%nat with (531 + 22)%nat; rewrite (o2_regatom cx E regs X 22 ltac:(lia)), <- R22; f_equal; apply bv_eq; reflexivity).
assert (E554 : ew Ev 554 = w64 (s32_at T 392))
  by (unfold Ev; change 554%nat with (531 + 23)%nat; rewrite (o2_regatom cx E regs X 23 ltac:(lia)), <- R23; f_equal; apply bv_eq; reflexivity).
assert (E555 : ew Ev 555 = w64 (ov_of T))
  by (unfold Ev; change 555%nat with (531 + 24)%nat; rewrite (o2_regatom cx E regs X 24 ltac:(lia)), <- R24; f_equal; apply bv_eq; reflexivity).
assert (XA : forall j, (j < 6)%nat -> ew Ev (563 + j) = nth j X (Z_to_bv 64 0)) by (intros j Hj; apply o2_atom; cbn; lia).
pose proof (XA 0%nat ltac:(lia)) as AX563. pose proof (XA 1%nat ltac:(lia)) as AX564. pose proof (XA 2%nat ltac:(lia)) as AX565.
pose proof (XA 3%nat ltac:(lia)) as AX566. pose proof (XA 4%nat ltac:(lia)) as AX567. pose proof (XA 5%nat ltac:(lia)) as AX568.
unfold X in AX563, AX564, AX565, AX566, AX567, AX568.
cbn [nth o6_x Nat.add] in AX563, AX564, AX565, AX566, AX567, AX568.
clear XA.
assert (CSEQ : acond_ok Ev o6_seqc).
{ apply (o6_seq Ev (u_at T' 392 4) ret (u_at T 392 4) ai (ov_of T) (n_of T) AX563 (o2_u_rng T' 392 4) E552 Hret E554
    (o2_u_rng T 392 4) E553 ltac:(lia) E555 ltac:(lia) E550 ltac:(lia)).
  exact EST. }
pose proof (o6_regs_ok cx E regs X HdE HrL HAr2 R27) as A1.
pose proof (d_E_env cx E (obs_vals regs ++ X) HdE) as HdE'.
pose proof (d_env_fl cx E (obs_vals regs ++ X)) as HFL'.
fold Ev in A1, HdE', HFL'.
assert (HEI : img_env VAL A_LIM Ev).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold Ev, d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] Ev (rd W mem3)) by constructor.
pose proof HdE' as (_ & _ & _ & E60 & E516 & _). change AT_A with 60%nat in E60. change AT_F with 516%nat in E516.
pose (RUNTO := paj_run_to (fx := fq) B LAWS).
unfold cfg_at. change (w64 (BASE + 0x181c)) with (Z_to_bv 64 (BASE + 0x181c)).
destruct (Z.ltb_spec ai 0) as [Hneg|Hpos].
- assert (CA : acond_ok Ev (mkAC BC_LT (SOff 553 0) (SLit 0))).
  { unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite (o6_blt Ev 553 ai E553 ltac:(lia)). apply Z.ltb_lt. exact Hneg. }
  pose proof (o6_seat fq cx h i n now op nb fr len Sg T T' ai ow ret regs ly3 S3 W mem3 md3 k E
    [o6_seqc; mkAC BC_LT (SOff 553 0) (SLit 0)] HC HdE Hregs Hflag HOC HOT R27 (conj CSEQ (conj CA I))) as HS.
  fold X Ev in HS. clearbody Ev.
  unfold ss_d in HS. ro_base HS 516%nat. ro_base HS 529%nat. ro_base HS 60%nat.
  paj_run_to_tok RUNTO HS HJ SHOK OBspan 0x1b78.
  { cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  assert (Hpt := frame_of_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
  assert (Hptr := frame_of_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
  clear HF HFr HG.
  set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
  assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a)
    by (intros a _ _; apply aview_eq_of; apply Hptr).
  assert (MPR : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms) a)
    by (intros a [Hh [b Hb]]; split; [exact Hh|]; exists b; rewrite Hpt; exact Hb).
  assert (GU : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26]%bv -> getr (ms_regs ms) r = getr regs r).
  { intros r Hr. rewrite (st_ok_pi_restrict_reg _ _ _ ms r HS), (A1 r).
    cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
  assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr (ms_regs ms) r = getr regs r)
    by (intros r Hr; apply GU; cbv [In] in Hr |- *; tauto).
  apply SRr_ret. right. right.
  apply (o2_c10_of cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W _).
  apply (o2_land fq cx h i n now op nb fr len Sg T' kmax accmax ly3 S3 W mem3 md4 k acc Ev _ ms regs _ _ Hbase Hfz HJ Hfrs Hk Hnev
    Hmo Hacc HdE' HFL' HS eq_refl eq_refl ltac:(vm_compute; reflexivity) HOC MEQ MPR RG
    (val_mem_pt _ _ _ _ _ Hptr Hh216) (val_mem_pt _ _ _ _ _ Hptr Hh152) (val_mem_pt _ _ _ _ _ Hptr H232)
    (val_mem_pt _ _ _ _ _ Hptr H344) (val_mem_pt _ _ _ _ _ Hptr H248) (val_mem_pt _ _ _ _ _ Hptr H336)
    (val_mem_pt _ _ _ _ _ Hptr H368) (val_mem_pt _ _ _ _ _ Hptr H280)).
  unfold o2_X10, ob_rT, ob_rX.
  refine (conj _ (conj (o2_obT_pt cx now Sg T T' ai ow ret W mem3 (ms_mem ms) Hptr HOT) (conj (conj _ _)
    (conj (conj _ (conj _ (conj _ _))) (conj Hneg (conj _ _)))))).
  all: first [ rewrite GU by (cbv; tauto); assumption | o2_reg HS ].
- assert (CA : acond_ok Ev (mkAC BC_GE (SOff 553 0) (SLit 0))).
  { unfold acond_ok. cbn [ac_c ac_a ac_b].
    change (branch_taken BC_GE (sv_denot Ev (SOff 553 0)) (sv_denot Ev (SLit 0)))
      with (negb (branch_taken BC_LT (sv_denot Ev (SOff 553 0)) (sv_denot Ev (SLit 0)))).
    rewrite (o6_blt Ev 553 ai E553 ltac:(lia)). apply negb_true_iff, Z.ltb_ge. exact Hpos. }
  assert (Hrr : - 2 ^ 31 <= role_of_e T ai < 2 ^ 31) by (unfold role_of_e, s32_at; apply swrap32_range).
  assert (U567 : U Ev (SOff 567 0) = u64 (role_of_e T ai)).
  { rewrite (U_atom Ev 567 _ AX567 (o2_u64_rng _)). unfold oldv. rewrite (proj2 (Z.ltb_ge ai 0) Hpos). reflexivity. }
  destruct (Z.eq_dec (role_of_e T ai) 1) as [Hr1|Hr1].
  + assert (HCR : acond_ok Ev (mkAC BC_EQ (SOff 567 0) (SLit 1))).
    { unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, U567, U_lit by lia. rewrite Hr1. reflexivity. }
    pose proof (o6_seat fq cx h i n now op nb fr len Sg T T' ai ow ret regs ly3 S3 W mem3 md3 k E
      [o6_seqc; mkAC BC_GE (SOff 553 0) (SLit 0); mkAC BC_EQ (SOff 567 0) (SLit 1)] HC HdE Hregs Hflag HOC HOT R27
      (conj CSEQ (conj CA (conj HCR I)))) as HS.
    fold X Ev in HS. clearbody Ev.
    unfold ss_d in HS. ro_base HS 516%nat. ro_base HS 529%nat. ro_base HS 60%nat.
    paj_run_to_tok RUNTO HS HJ SHOK OBspan 0x18b8.
    { cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    assert (Hpt := frame_of_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
    assert (Hptr := frame_of_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
    clear HF HFr HG.
    rewrite (pa_sigma_find_entry (PI := PI)) in HS.
    lazymatch type of HS with st_ok _ ?Ex (setpc ?ssx _) ?msx =>
      assert (HSpi : st_ok_pi SEGS VAL Ex (setpc ssx AF_find_entry) msx) by exact HS end.
    clear HS.
    set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
    assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a)
      by (intros a _ _; apply aview_eq_of; apply Hptr).
    assert (MPR : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms) a)
      by (intros a [Hh [b Hb]]; split; [exact Hh|]; exists b; rewrite Hpt; exact Hb).
    assert (GU : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26]%bv -> getr (ms_regs ms) r = getr regs r).
    { intros r Hr. rewrite (st_ok_pi_restrict_reg _ _ _ ms r HSpi), (A1 r).
      cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
    assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr (ms_regs ms) r = getr regs r)
      by (intros r Hr; apply GU; cbv [In] in Hr |- *; tauto).
    apply SRr_ret. left.
    apply (o2_c7_of cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W _).
    apply (o2_land fq cx h i n now op nb fr len Sg T' kmax accmax ly3 S3 W mem3 md4 k acc Ev _ ms regs _ _ Hbase Hfz HJ Hfrs Hk Hnev
      Hmo Hacc HdE' HFL' HSpi eq_refl eq_refl ltac:(vm_compute; reflexivity) HOC MEQ MPR RG
      (val_mem_pt _ _ _ _ _ Hptr Hh216) (val_mem_pt _ _ _ _ _ Hptr Hh152) (val_mem_pt _ _ _ _ _ Hptr H232)
      (val_mem_pt _ _ _ _ _ Hptr H344) (val_mem_pt _ _ _ _ _ Hptr H248) (val_mem_pt _ _ _ _ _ Hptr H336)
      (val_mem_pt _ _ _ _ _ Hptr H368) (val_mem_pt _ _ _ _ _ Hptr H280)).
    unfold o2_X7, ob_rT, ob_rX.
    refine (conj _ (conj (o2_obT_pt cx now Sg T T' ai ow ret W mem3 (ms_mem ms) Hptr HOT) (conj (conj _ _)
      (conj (conj _ (conj _ (conj _ _))) (conj Hpos (conj Hr1 (conj _ (conj _ _)))))))).
    all: first [ rewrite GU by (cbv; tauto); assumption | o2_reg HSpi ].
  + assert (HCR : acond_ok Ev (mkAC BC_NE (SOff 567 0) (SLit 1))).
    { unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U, U567, U_lit by lia.
      apply negb_true_iff, Z.eqb_neq. unfold u64. intros Hm. apply Hr1.
      destruct (Z.ltb_spec (role_of_e T ai) 0) as [Hl|Hl].
      - exfalso. rewrite <- (Z.mod_unique (role_of_e T ai) (2 ^ 64) (-1) (role_of_e T ai + 2 ^ 64)) in Hm by lia. lia.
      - rewrite Z.mod_small in Hm by lia. exact Hm. }
    pose proof (o6_seat fq cx h i n now op nb fr len Sg T T' ai ow ret regs ly3 S3 W mem3 md3 k E
      [o6_seqc; mkAC BC_GE (SOff 553 0) (SLit 0); mkAC BC_NE (SOff 567 0) (SLit 1)] HC HdE Hregs Hflag HOC HOT R27
      (conj CSEQ (conj CA (conj HCR I)))) as HS.
    fold X Ev in HS. clearbody Ev.
    unfold ss_d in HS. ro_base HS 516%nat. ro_base HS 529%nat. ro_base HS 60%nat.
    paj_run_to_tok RUNTO HS HJ SHOK OBspan 0x18b8.
    { cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
    assert (Hpt := frame_of_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
    assert (Hptr := frame_of_ro_pt _ _ _ _ HFr ltac:(vm_compute; reflexivity)).
    clear HF HFr HG.
    set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
    assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx <= a < d_A cx + 472) -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a)
      by (intros a _ _; apply aview_eq_of; apply Hptr).
    assert (MPR : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms) a)
      by (intros a [Hh [b Hb]]; split; [exact Hh|]; exists b; rewrite Hpt; exact Hb).
    assert (GU : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 25; 26]%bv -> getr (ms_regs ms) r = getr regs r).
    { intros r Hr. rewrite (st_ok_pi_restrict_reg _ _ _ ms r HS), (A1 r).
      cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
    assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr (ms_regs ms) r = getr regs r)
      by (intros r Hr; apply GU; cbv [In] in Hr |- *; tauto).
    apply SRr_ret. right. left.
    apply (o2_c9_of cx h i n now op nb fr len Sg kmax accmax T T' ai ow ret W _).
    apply (o2_land fq cx h i n now op nb fr len Sg T' kmax accmax ly3 S3 W mem3 md4 k acc Ev _ ms regs _ _ Hbase Hfz HJ Hfrs Hk Hnev
      Hmo Hacc HdE' HFL' HS eq_refl eq_refl ltac:(vm_compute; reflexivity) HOC MEQ MPR RG
      (val_mem_pt _ _ _ _ _ Hptr Hh216) (val_mem_pt _ _ _ _ _ Hptr Hh152) (val_mem_pt _ _ _ _ _ Hptr H232)
      (val_mem_pt _ _ _ _ _ Hptr H344) (val_mem_pt _ _ _ _ _ Hptr H248) (val_mem_pt _ _ _ _ _ Hptr H336)
      (val_mem_pt _ _ _ _ _ Hptr H368) (val_mem_pt _ _ _ _ _ Hptr H280)).
    unfold o2_X9, ob_rT, ob_rX.
    refine (conj _ (conj (o2_obT_pt cx now Sg T T' ai ow ret W mem3 (ms_mem ms) Hptr HOT) (conj (conj _ _)
      (conj (conj _ (conj _ (conj _ _))) (conj Hpos _))))).
    all: first [ rewrite GU by (cbv; tauto); assumption | o2_reg HS ].
Qed.

End h.
End f.
End d.
