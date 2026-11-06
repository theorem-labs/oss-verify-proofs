(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 977 of its 1008 lines of code are new or changed and 38 lines of the source are left out. *)
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
YC1g YC1h YC81 YC4b YC45 YC85 YC88 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody DiscoEntObsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c slot_observe slot_known.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YA0j YI67.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require FindEntry.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma zc_small : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z Hz. unfold zcanon, M64. apply Z.mod_small. lia. Qed.
Lemma UA0 : forall E n v, ew E n = Z_to_bv 64 v -> U E (SOff n 0) = zcanon v.
Proof. intros E n v H. rewrite U_SOff, H, Z.add_0_r, unsigned_lit. unfold zcanon. apply Zmod_mod. Qed.
Lemma UA32 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> U E (SExt true 32 (SOff n 0)) = zcanon (bv_swrap 32 v).
Proof.
intros E n v H Hv. rewrite U_SExt, (UA0 E n v H), (zc_small v) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite (Z.mod_small v) by lia. reflexivity.
Qed.
Lemma UA8 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> U E (SExt false 8 (SOff n 0)) = v.
Proof.
intros E n v H Hv. rewrite U_SExt, (UA0 E n v H), (zc_small v) by lia. change (2 ^ Z.of_N 8) with 256.
rewrite (Z.mod_small v) by lia. apply zc_small. lia.
Qed.
Lemma Uadd0 : forall E x, U E (SAlu ALU_ADD x (SLit 0)) = U E x.
Proof.
intros E x. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (zcanon 0) with 0. rewrite Z.add_0_r.
apply zc_small. pose proof (U_range E x). unfold M64 in *. lia.
Qed.
Lemma sw32_case : forall a, 0 <= a < 2 ^ 32 -> bv_swrap 32 a = if a <? 2 ^ 31 then a else a - 2 ^ 32.
Proof.
intros a Ha. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ (Z.of_N 32 - 1)) with 2147483648. change (2 ^ 31) with 2147483648.
change (2 ^ 32) with 4294967296 in *.
destruct (Z.ltb_spec a 2147483648); lia.
Qed.
Lemma zc_sw : forall a, 0 <= a < 2 ^ 32 -> zcanon (bv_swrap 32 a) = if a <? 2 ^ 31 then a else a + (2 ^ 64 - 2 ^ 32).
Proof.
intros a Ha. rewrite sw32_case by exact Ha. unfold zcanon, M64. destruct (Z.ltb_spec a (2 ^ 31)); lia.
Qed.
Lemma zltu_sw : forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 ->
  (zcanon (bv_swrap 32 a) <? zcanon (bv_swrap 32 b)) = (a <? b).
Proof.
intros a b Ha Hb. rewrite !zc_sw by assumption.
destruct (Z.ltb_spec a (2 ^ 31)), (Z.ltb_spec b (2 ^ 31)); apply Bool.eq_iff_eq_true; rewrite !Z.ltb_lt; lia.
Qed.
Lemma fu_uat : forall (L : list byte) k n, CtrlParsed.fu L k n = u_at L (Z.of_nat k) n.
Proof. intros L k n. unfold CtrlParsed.fu, CtrlParsed.fld, u_at, sub. rewrite Nat2Z.id. reflexivity. Qed.
Lemma uat1_fb : forall (L : list byte) k, (k < length L)%nat -> u_at L (Z.of_nat k) 1 = CtrlParsed.fb L k.
Proof.
intros L k Hk. unfold u_at, sub, CtrlParsed.fb. rewrite Nat2Z.id.
destruct (nth_split L (CtrlParsed.zb 0) Hk) as (l1 & l2 & EL & Hl1). rewrite EL at 1.
rewrite <- Hl1, skipn_app, skipn_all, Nat.sub_diag. cbn [skipn app firstn bytes_le_to_Z].
rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
Qed.
Lemma s32_sw : forall v, 0 <= v < 2 ^ 32 -> CtrlParsed.s32 v = bv_swrap 32 v.
Proof. intros v Hv. unfold CtrlParsed.s32. rewrite sw32_case by exact Hv. reflexivity. Qed.
Lemma sight_S12 : forall Sg, disco_classify_c.sighting_ok Sg -> sighting_S1 Sg /\ sighting_S2 Sg.
Proof.
intros Sg (L & Hr & Hh).
assert (U8 : 0 <= u_at Sg 8 4 < 2 ^ 32).
{ unfold u_at. pose proof (bytes_le_to_Z_bound (sub Sg 8 4)) as B1. pose proof (bytes_le_to_Z_nonneg (sub Sg 8 4)).
  assert (length (sub Sg 8 4) = 4%nat) by (unfold sub; rewrite length_firstn, length_skipn; lia). rewrite H0 in B1. lia. }
assert (E8 : CtrlParsed.fu Sg 8 4 = u_at Sg 8 4) by (rewrite fu_uat; reflexivity).
rewrite E8, s32_sw in Hr by exact U8.
assert (E12 : CtrlParsed.fb Sg 12 = u_at Sg 12 1) by (rewrite <- (uat1_fb Sg 12) by lia; reflexivity).
assert (E13 : CtrlParsed.fb Sg 13 = u_at Sg 13 1) by (rewrite <- (uat1_fb Sg 13) by lia; reflexivity).
assert (E14 : CtrlParsed.fb Sg 14 = u_at Sg 14 1) by (rewrite <- (uat1_fb Sg 14) by lia; reflexivity).
rewrite E12, E13, E14 in Hh.
split.
- unfold sighting_S1, s_role, s32_at. lia.
- unfold sighting_S2, s_hd, s_din, s_dout. lia.
Qed.

Lemma u_at_range : forall (L : list byte) k n, (Z.to_nat k + n <= length L)%nat -> 0 <= u_at L k n < 2 ^ (8 * Z.of_nat n).
Proof.
intros L k n Hl. assert (Hsub : length (sub L k n) = n) by (unfold sub; rewrite length_firstn, length_skipn; lia).
pose proof (bytes_le_to_Z_bound (sub L k n)) as Hb1. pose proof (bytes_le_to_Z_nonneg (sub L k n)) as Hb0. rewrite Hsub in Hb1.
unfold u_at. lia.
Qed.
Lemma u_at_r1 : forall (L : list byte) k, (Z.to_nat k + 1 <= length L)%nat -> 0 <= u_at L k 1 < 256.
Proof. intros L k H. pose proof (u_at_range L k 1 H). change (2 ^ (8 * Z.of_nat 1)) with 256 in *. lia. Qed.
Lemma u_at_r4 : forall (L : list byte) k, (Z.to_nat k + 4 <= length L)%nat -> 0 <= u_at L k 4 < 2 ^ 32.
Proof. intros L k H. pose proof (u_at_range L k 4 H). change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in *. lia. Qed.
Lemma obs_fields : forall T G ow now T' ret r,
  length T = 400%nat -> length G = 24%nat -> 0 <= r < n_of T -> n_of T <= 8 -> 0 <= now -> 0 <= ow <= 1 ->
  tbl_T2 T -> tbl_T4 T -> sighting_S1 G -> sighting_S2 G ->
  find_res T (s_mac G) r -> reac_disco_table_observe_c.observe_model T G ow now T' ret ->
  length T' = 400%nat /\
  (forall j, 0 <= j < 8 -> mac_of T' j = mac_of T j) /\
  u_at T' 384 4 = u_at T 384 4 /\
  bv_swrap 32 (u_at T' (48 * r + 8) 4) = slot_known.want_role (s_role G) (role_of_e T r) /\
  u_at T' (48 * r + 12) 1 = (if s_hd G =? 0 then hd_of T r else 1) /\
  u_at T' (48 * r + 13) 1 = (if s_hd G =? 0 then din_of T r else s_din G) /\
  u_at T' (48 * r + 14) 1 = (if s_hd G =? 0 then dout_of T r else s_dout G) /\
  u_at T' (48 * r + 15) 1 = (if s_fam G =? 0 then reac_disco_table_observe_c.fam_of T r else s_fam G) /\
  u_at T' (48 * r + 16) 1 = (if s_slots G =? 0 then reac_disco_table_observe_c.slots_of T r else s_slots G) /\
  bv_swrap 32 (u_at T' (48 * r + 20) 4) =
    bv_swrap 32 (if reac_disco_table_observe_c.ch_of T r <? s_ch G then s_ch G else reac_disco_table_observe_c.ch_of T r) /\
  bv_swrap 32 (u_at T' (48 * r + 24) 4) = (if ow =? 0 then owned_of T r else 1) /\
  u_at T' (48 * r + 32) 8 = u_at T (48 * r + 32) 8 /\
  u_at T' (48 * r + 40) 8 = now mod 2 ^ 64 /\
  ret = (if slot_observe.c_any T G ow r then 1 else 0).
Proof.
intros T G ow now T' ret r LT LG Hr Hn8 Hn How T2 T4 S1 S2 FR OM.
pose proof (slot_observe.known_arm T G ow now T' ret r FR ltac:(lia) OM) as EK.
destruct (slot_observe.ok_facts T G ow now r T' ret LT LG ltac:(lia) EK)
  as (LT' & EM & E384 & E8 & E12 & E13 & E14 & E15 & E16 & E20 & E24 & E32 & E40 & E392 & Eret).
destruct (T4 r Hr) as (Hhd & _ & Hown).
unfold u_at. rewrite E384, E8, E12, E13, E14, E15, E16, E20, E24, E32, E40.
split; [exact LT'|]. split; [exact EM|]. split; [reflexivity|].
split; [exact (slot_known.role_field T G r S1 (T2 r Hr))|].
split; [exact (slot_known.hd_field T G r S2 Hhd)|].
split; [exact (slot_known.din_field T G r S2)|].
split; [exact (slot_known.dout_field T G r S2)|].
split; [exact (slot_known.fam_field T G r)|].
split; [exact (slot_known.slots_field T G r)|].
split; [exact (slot_known.ch_field T G r)|].
split; [exact (slot_known.own_field T ow r How Hown)|].
split; [reflexivity|].
split; [apply bytes_le_Z_to_le; exact Hn|].
exact Eret.
Qed.




Lemma zc_mod : forall x, zcanon (x mod 2 ^ 64) = zcanon x.
Proof. intros x. unfold zcanon, M64. apply Zmod_mod. Qed.
Definition sr9_x (r : nat) : sv := match r with 13%nat => SOff AT_F 2160 | _ => sr_x r end.
Definition sr9 : list sv := map sr9_x (seq 0 32).
Definition xa (j : nat) : sv := SOff (AT_X + 32 + j) 0.
Definition acs9 : list YP09.chunk :=
  [YP09.mkChunk 392 (CVal 8 (xa 0)); YP09.mkChunk 136 (CVal 8 (xa 1)); YP09.mkChunk 128 (CVal 8 (xa 2));
   YP09.mkChunk 120 (CVal 8 (xa 3)); YP09.mkChunk 112 (CVal 8 (xa 4)); YP09.mkChunk 104 (CVal 8 (xa 5));
   YP09.mkChunk 224 (CVal 8 (xa 6)); YP09.mkChunk 96 (CVal 8 (xa 7)); YP09.mkChunk 72 (CVal 8 (xa 8));
   YP09.mkChunk 88 (CVal 8 (xa 9)); YP09.mkChunk 80 (CVal 8 (xa 10)); YP09.mkChunk 408 (CVal 8 (xa 11));
   YP09.mkChunk 368 (CVal 8 (xa 12)); YP09.mkChunk 344 (CVal 8 (xa 13)); YP09.mkChunk 248 (CVal 8 (xa 14));
   YP09.mkChunk 336 (CVal 8 (xa 15)); YP09.mkChunk 280 (CVal 8 (xa 16)); YP09.mkChunk 232 (CVal 8 (xa 17));
   YP09.mkChunk 216 (CVal 8 (xa 18)); YP09.mkChunk 152 (CVal 8 (xa 19))].
Definition fcs9 : list YP09.chunk :=
  [YP09.mkChunk 3000 (CVal 4 (xa 20)); YP09.mkChunk 3004 (CVal 1 (xa 21)); YP09.mkChunk 3005 (CVal 1 (xa 22));
   YP09.mkChunk 3006 (CVal 1 (xa 23)); YP09.mkChunk 3007 (CVal 1 (xa 24)); YP09.mkChunk 3008 (CVal 1 (xa 25));
   YP09.mkChunk 3012 (CVal 4 (xa 26)); YP09.mkChunk 2544 (CVal 4 (xa 27))].
Fixpoint sr_forget (sr : list sv) (rs : list (bv 5)) (k : nat) : list sv :=
  match rs with [] => sr | r :: rs' => sr_forget (sr_set sr r (SOff k 0)) rs' (S k) end.
Definition ss_join (ss : sstate) (rs : list (bv 5)) (k : nat) (ai ci li : list nat) : sstate :=
  mkSS (ss_pc ss) (sr_forget (ss_regs ss) rs k) (ss_mem ss) (ss_resv ss)
    (mkFacts (pick (f_atoms (ss_facts ss)) ai) (pick (f_conds (ss_facts ss)) ci) (pick (f_alias (ss_facts ss)) li)).



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

Lemma ew_dx : forall cx E (regs : bvmap 5 word) (xv : list word) j, (j < length xv)%nat ->
  ew (d_env cx E (obs_vals regs ++ xv)) (AT_X + 32 + j) = nth j xv (Z_to_bv 64 0).
Proof.
intros cx E regs xv j Hj. unfold d_env, havoc. cbn [ew].
replace (AT_X + 32 + j <? AT_FL)%nat with false by (symmetry; apply Nat.ltb_ge; unfold AT_X, AT_FL; lia).
replace (AT_X + 32 + j - AT_FL)%nat with (S (32 + j)) by (unfold AT_X, AT_FL; lia). cbn [nth].
assert (L : length (obs_vals regs) = 32%nat) by (unfold obs_vals; rewrite length_map, length_seq; reflexivity).
rewrite app_nth2 by lia. rewrite L. replace (32 + j - 32)%nat with j by lia. apply nth_indep. exact Hj.
Qed.
Lemma ew_dr : forall cx E (regs : bvmap 5 word) (xv : list word) (r : nat), (r < 32)%nat ->
  ew (d_env cx E (obs_vals regs ++ xv)) (AT_X + r) = getr regs (Z_to_bv 5 (Z.of_nat r)).
Proof.
intros cx E regs xv r Hr. unfold d_env, havoc. cbn [ew].
replace (AT_X + r <? AT_FL)%nat with false by (symmetry; apply Nat.ltb_ge; unfold AT_X, AT_FL; lia).
replace (AT_X + r - AT_FL)%nat with (S r) by (unfold AT_X, AT_FL; lia). cbn [nth].
assert (L : length (obs_vals regs) = 32%nat) by (unfold obs_vals; rewrite length_map, length_seq; reflexivity).
rewrite app_nth1 by lia. unfold obs_vals.
rewrite (nth_indep _ _ (getr regs (Z_to_bv 5 (Z.of_nat 0)))) by (rewrite length_map, length_seq; exact Hr).
rewrite (map_nth (fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0)))). rewrite seq_nth by exact Hr. reflexivity.
Qed.

Lemma st_ok_pi_fregs : forall {fq : YK11.FPState} E pc sr fr fr' mem resv G ms,
  st_ok_pi (fx := fq) SEGS VAL E (mkSST pc sr fr mem resv G) ms -> st_ok_pi (fx := fq) SEGS VAL E (mkSST pc sr fr' mem resv G) ms.
Proof. intros fq E pc sr fr fr' mem resv G ms H. exact H. Qed.
Lemma w64_eqm : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). exact H. Qed.
Lemma val_mem_mod : forall (m : word -> option byte) a n v,
  val_mem SEGS m a n (v mod 2 ^ (8 * Z.of_nat n)) -> val_mem SEGS m a n v.
Proof. intros m a n v H k Hk. rewrite (H k Hk). unfold YO0f.le_byte. rewrite Zmod_mod. reflexivity. Qed.
Lemma st_ok_repc : forall {fq : YK11.FPState} E ss ms p H,
  ss_resv ss = None -> st_ok (fx := fq) SEGS E ss (restrict H ms) ->
  st_ok (fx := fq) SEGS E (setpc ss p) (restrict H (YK11.mkst (ms_regs ms) (Z_to_bv 64 p) (ms_mem ms) (YK11.seg_rom SEGS))).
Proof.
intros fq E ss ms p H Hr HS. unfold st_ok in *. destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
destruct ss as [pc0 sr fr0 mem0 resv G]. cbn [setpc ss_resv ss_regs ss_mem ss_facts ss_pc] in *. subst resv.
cbn [restrict YK11.mkst ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem] in *.
do 6 (split; [first [reflexivity | assumption]|]). exact (conj H7 (conj H8 H9)).
Qed.
Lemma chunk_vm : forall {fq : YK11.FPState} E ss ms i rg p off e a v,
  st_ok (fx := fq) SEGS E ss ms -> nth_error (ss_mem ss) i = Some rg -> YP09.r_base rg = Some p ->
  In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks rg) -> bv_unsigned (ew E p) = a ->
  sv_denot E e = Z_to_bv 64 v -> val_mem SEGS (ms_mem ms) (a + off) 8 v.
Proof.
intros fq E ss ms i rg p off e a v HS Hi Hb Hin Ha He. apply val_mem_mod.
apply (YI67.st_chunk_val SEGS E ss ms i rg p off 8 e a (v mod 2 ^ (8 * Z.of_nat 8)) HS Hi Hb Hin Ha).
- rewrite He. apply w64_eqm. change (8 * Z.of_nat 8) with 64. rewrite Zmod_mod. reflexivity.
- change (8 * Z.of_N 8) with 64. change (8 * Z.of_nat 8) with 64. apply Z.mod_pos_bound. lia.
- lia.
Qed.
Lemma sr_forget_ok : forall {fq : YK11.FPState} rs E pc sr mem resv G ms k,
  st_ok_pi (fx := fq) SEGS VAL E (mkSS pc sr mem resv G) ms -> forallb (fun r : bv 5 => negb (bv_eqb r 0)) rs = true ->
  (forall j, (j < length rs)%nat -> sv_denot E (SOff (k + j) 0) = getr (ms_regs ms) (nth j rs 0%bv)) ->
  st_ok_pi (fx := fq) SEGS VAL E (mkSS pc (sr_forget sr rs k) mem resv G) ms.
Proof.
intros fq rs. induction rs as [|r rs IH]; intros E pc sr mem resv G ms k HS Hnz Hv; [exact HS|].
cbn [forallb] in Hnz. apply andb_prop in Hnz as [Hr Hnz]. cbn [sr_forget].
apply IH; [| exact Hnz |].
- pose proof (ast_ok_pi_set_reg_fp (fx := fq) E (mkSS pc sr mem resv G) ms r (SOff k 0) HS
    ltac:(destruct (bv_eqb r 0); [discriminate | reflexivity]) ltac:(rewrite <- (Nat.add_0_r k); exact (Hv 0%nat ltac:(cbn; lia)))) as H.
  exact H.
- intros j Hj. replace (S k + j)%nat with (k + S j)%nat by lia. exact (Hv (S j) ltac:(cbn; lia)).
Qed.
Lemma st_ok_pi_join : forall {fq : YK11.FPState} E ss ms rs k ai ci li,
  st_ok_pi (fx := fq) SEGS VAL E ss ms ->
  ss_atoms_p (pband k A_TEXT) (set_facts ss (mkFacts (pick (f_atoms (ss_facts ss)) ai) (pick (f_conds (ss_facts ss)) ci) (pick (f_alias (ss_facts ss)) li))) = true ->
  (k + length rs <= A_TEXT)%nat -> forallb (fun r : bv 5 => negb (bv_eqb r 0)) rs = true ->
  st_ok_pi (fx := fq) SEGS VAL (havoc E k (map (getr (ms_regs ms)) rs)) (ss_join ss rs k ai ci li) ms.
Proof.
intros fq E ss ms rs k ai ci li HS Hat Hk Hnz.
pose proof (st_ok_pi_pick_facts E ss ms ai ci li HS) as H1.
pose proof (st_ok_pi_havoc k E _ ms (map (getr (ms_regs ms)) rs) H1 Hat ltac:(rewrite length_map; exact Hk)) as H2.
destruct ss as [pc sr fr mem resv G]. unfold set_facts in H2. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in H2 |- *.
apply (st_ok_pi_fregs _ _ _ fr nil) in H2.
unfold ss_join. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
apply sr_forget_ok; [exact H2 | exact Hnz |].
intros j Hj. cbn [sv_denot]. rewrite Z.add_0_r, (ew_havoc_new E k _ j (getr (ms_regs ms) 0%bv)) by (rewrite length_map; exact Hj).
rewrite Z_to_bv_bv_unsigned. apply map_nth.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Lemma garr8_u : forall (m : word -> option byte) p (L : list byte) k n, 0 <= k -> (Z.to_nat k + n <= length L)%nat ->
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) L) -> val_mem SEGS m (p + k) n (u_at L k n).
Proof.
intros m p L k n Hk Hl G j Hj.
assert (Hsub : length (sub L k n) = n) by (unfold sub; rewrite length_firstn, length_skipn; lia).
destruct (nth_error L (Z.to_nat k + j)) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
replace (p + k + Z.of_nat j) with (p + Z.of_nat (Z.to_nat k + j)) by lia.
rewrite (garr8_mbyte SEGS m p _ (Z.to_nat k + j) G) by (rewrite length_map; lia).
f_equal. rewrite (nth_error_nth (map (fun b0 : byte => bv_unsigned b0) L) _ 0 (map_nth_error _ _ _ Hb)).
assert (Hs : nth_error (sub L k n) j = Some b).
{ unfold sub. rewrite nth_error_firstn. destruct (Nat.ltb_spec j n); [|lia]. rewrite nth_error_skipn. exact Hb. }
pose proof (YA0j.nth_error_le_byte _ _ _ Hs) as Hv.
pose proof (bytes_le_to_Z_bound (sub L k n)) as Hb1. pose proof (bytes_le_to_Z_nonneg (sub L k n)) as Hb0. rewrite Hsub in Hb1.
unfold u_at. rewrite le_byte_small by (split; [exact Hb0 | exact Hb1] || lia).
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.shiftr_div_pow2 by lia. rewrite Hv. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma chunk_okW : forall E (m : word -> option byte) base off (w : N) a v,
  ew E a = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem SEGS m (base + off) (N.to_nat w) v ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal w (SOff a 0))).
Proof.
intros E m base off w a v Ha Hv Hw H. apply (chunk_ok_val SEGS E m base off w (SOff a 0) v); [| exact Hv | exact Hw | exact H].
cbn [sv_denot]. rewrite Ha, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma chunk_ok8 : forall E (m : word -> option byte) base off a v,
  ew E a = Z_to_bv 64 v -> val_mem SEGS m (base + off) 8 v ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 8 (SOff a 0))).
Proof.
intros E m base off a v Ha H. apply (chunk_okW E m base off 8 a (v mod 2 ^ 64)).
- rewrite Ha. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Zmod_mod. reflexivity.
- change (8 * Z.of_N 8) with 64. apply Z.mod_pos_bound. lia.
- lia.
- intros j Hj. rewrite (H j Hj). f_equal. f_equal. unfold YO0f.le_byte. change (8 * Z.of_nat (N.to_nat 8)) with 64. change (8 * Z.of_nat 8) with 64. rewrite Zmod_mod. reflexivity.
Qed.
Lemma regs_ok9 : forall cx E regs xv, d_E cx E -> d_rL B cx regs -> getr regs 13 = w64 (d_obj cx OT) ->
  0 <= d_A cx < 2 ^ 64 -> 0 <= d_FB cx -> d_FB cx + 4096 <= 2 ^ 64 ->
  regs_ok (d_env cx E (obs_vals regs ++ xv)) sr9 regs.
Proof.
intros cx E regs xv HE HL H13 HA HF0 HF1.
destruct HE as (HER & H32 & _ & HA60 & HF516 & _).
destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
apply regs_ok_by_cases. intros r Hr.
cbv [all_regs In] in Hr.
assert (H2 : getr regs 2 = Z_to_bv 64 (d_A cx)) by (rewrite <- Hsp; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HS2 : ew E 2 = Z_to_bv 64 (d_S cx)).
{ rewrite (HER 2%nat 2%bv eq_refl). unfold d_S, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
change AT_A with 60%nat in HA60. change AT_F with 516%nat in HF516.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
all: try (match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot];
  first
  [ rewrite getr_zero; reflexivity
  | unfold d_env; rewrite ew_havoc_old by (cbv; lia); rewrite HF516, w64_add_w; rewrite H13; unfold d_obj, w64; reflexivity
  | rewrite Z.add_0_r; unfold d_env; rewrite ew_havoc_old by (cbv; lia);
    first [ rewrite HA60, Z_to_bv_bv_unsigned; first [exact H2 | exact H9]
          | rewrite HS2, Z_to_bv_bv_unsigned; exact H8
          | rewrite H32; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18 ]
  | rewrite Z.add_0_r; unfold d_env, havoc; cbn [ew Nat.ltb Nat.leb Nat.sub nth obs_vals map seq Nat.add AT_X AT_FL app];
    match goal with |- getr ?rg _ = Z_to_bv 64 (bv_unsigned (getr ?rg ?x)) =>
      let y := eval vm_compute in x in change x with y end;
    rewrite Z_to_bv_bv_unsigned; reflexivity ]).
Qed.

Definition obwin (cx : dcx) (a : Z) : Prop := d_A cx - 8192 <= a < d_A cx + 472.
Definition envJ (Es : env) (vs : list Z) (E : env) : Prop :=
  img_env VAL A_LIM E /\ (forall a, (a < 64 \/ 240 <= a < 640)%nat -> ew E a = ew Es a) /\
  (forall j, (j < length vs)%nat -> ew E (64 + j) = Z_to_bv 64 (nth j vs 0)).
Definition obM (cx : dcx) (W0 : world SEGS) (ly3 : alayout) (S3 : astate) (mem3 : word -> option byte) (kj : Z)
  (ms : machine_state) (md : Model) : Prop :=
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W0 (ms_mem ms) md kj /\
  d_kept (obwin cx) W0 mem3 W0 (ms_mem ms) /\
  (forall a, apresent (w_H W0) mem3 a -> apresent (w_H W0) (ms_mem ms) a).
Definition obJ (fq : YK11.FPState) (cx : dcx) (W0 : world SEGS) (ly3 : alayout) (S3 : astate) (mem3 : word -> option byte)
  (kj : Z) (Es : env) (vs : list Z) (ssJ : sstate) : world SEGS -> config -> Prop :=
  fun W' c' => W' = W0 /\ exists (E' : env) (ms' : machine_state) (md' : Model),
    c' = mkCfg ms' md' /\ st_ok_pi (fx := fq) SEGS VAL E' ssJ (restrict (w_H W0) ms') /\ envJ Es vs E' /\
    obM cx W0 ly3 S3 mem3 kj ms' md'.
Lemma envJ_init : forall Es, img_env VAL A_LIM Es -> envJ Es [] Es.
Proof. intros Es H. split; [exact H|]. split; [intros; reflexivity | intros j Hj; cbn in Hj; lia]. Qed.
Lemma envJ_step : forall Es vs E1 ws vs', envJ Es vs E1 -> (64 + length vs + length ws <= A_TEXT)%nat ->
  ws = map (Z_to_bv 64) vs' -> envJ Es (vs ++ vs') (havoc E1 (64 + length vs) ws).
Proof.
intros Es vs E1 ws vs' (HI & AG & JV) Hk Hws. split; [apply img_env_havoc; [exact HI | exact Hk]|]. split.
- intros a Ha. destruct Ha as [Ha|Ha].
  + rewrite ew_havoc_old by lia. apply AG. lia.
  + rewrite ew_havoc_above by (unfold A_TEXT in Hk; lia). apply AG. lia.
- intros j Hj. rewrite length_app in Hj. destruct (Nat.lt_ge_cases j (length vs)) as [Hl|Hl].
  + rewrite ew_havoc_old by lia. rewrite app_nth1 by exact Hl. exact (JV j Hl).
  + assert (Lw : length ws = length vs') by (subst ws; rewrite length_map; reflexivity).
    replace (64 + j)%nat with (64 + length vs + (j - length vs))%nat by lia.
    rewrite (ew_havoc_new E1 _ ws (j - length vs) (Z_to_bv 64 0)) by lia.
    rewrite app_nth2 by exact Hl. subst ws. apply map_nth.
Qed.
Lemma apresent_grow : forall H (m m' : word -> option byte) a, mem_grows (mrestrict H m) (mrestrict H m') ->
  apresent H m a -> apresent H m' a.
Proof.
intros H m m' a G (Hh & b & Hb). split; [exact Hh|].
specialize (G (Z_to_bv 64 a)). unfold mrestrict in G. rewrite Hh in G.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|]. exfalso. apply G; [rewrite Hb; discriminate | reflexivity].
Qed.
Lemma obM_run : forall cx W0 ly3 S3 mem3 kj ms md ms' md' E rs,
  obM cx W0 ly3 S3 mem3 kj ms md ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W0 (ms_mem ms') md' kj ->
  frame_of E rs (mrestrict (w_H W0) (ms_mem ms)) (mrestrict (w_H W0) (ms_mem ms')) ->
  mem_grows (mrestrict (w_H W0) (ms_mem ms)) (mrestrict (w_H W0) (ms_mem ms')) ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> obwin cx a) ->
  obM cx W0 ly3 S3 mem3 kj ms' md'.
Proof.
intros cx W0 ly3 S3 mem3 kj ms md ms' md' E rs (HJ & HK & HP) HJ' HF HG Hw.
split; [exact HJ'|]. split.
- intros a Ha Hn. rewrite (kept_of_frame (segs := SEGS) E rs (w_H W0) (ms_mem ms) (ms_mem ms') (obwin cx) HF Hw a Ha Hn).
  exact (HK a Ha Hn).
- intros a Ha. exact (apresent_grow _ _ _ a HG (HP a Ha)).
Qed.



Lemma mod_add3 : forall x y z, (x mod 2 ^ 64 + y mod 2 ^ 64 + z) mod 2 ^ 64 = (x + y + z) mod 2 ^ 64.
Proof. intros. rewrite <- Zplus_mod_idemp_l. rewrite <- Zplus_mod. rewrite Zplus_mod_idemp_l. reflexivity. Qed.
Lemma s6_val : forall E fb a, ew E 516 = Z_to_bv 64 fb -> ew E 572 = Z_to_bv 64 (u64 (16 * a)) -> ew E 573 = Z_to_bv 64 (u64 (64 * a)) ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 516 2160) (SMd M_MUL (SOff 572 0) (SLit 18446744073709551615))) (SOff 573 0)) =
  Z_to_bv 64 (fb + 2160 + 48 * a).
Proof.
intros E fb a H516 H572 H573. rewrite denot_lit_U. apply w64_eqm.
rewrite !U_SAlu, U_SMd, !U_SOff, U_SLit. cbn [zalu_raw zmd_raw]. rewrite H516, H572, H573, !unsigned_lit.
unfold zcanon, M64, u64. rewrite !Z.add_0_r.
rewrite ?Zmod_mod, ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r, ?Zmult_mod_idemp_l, ?Zmult_mod_idemp_r, ?Zmod_mod.
rewrite mod_add3.
replace (fb + 2160 + 16 * a * 18446744073709551615 + 64 * a) with (fb + 2160 + 48 * a + (16 * a) * 2 ^ 64) by lia.
apply Z_mod_plus_full.
Qed.
Lemma val_mem_keep : forall (W W' : world SEGS) (m m' : word -> option byte) a n v,
  (forall j, (j < n)%nat -> aview SEGS (w_H W') m' (a + Z.of_nat j) = aview SEGS (w_H W) m (a + Z.of_nat j)) ->
  val_mem SEGS (rd W m) a n v -> val_mem SEGS (rd W' m') a n v.
Proof. intros W W' m m' a n v Hk H j Hj. rewrite (mbyte_of_aview SEGS _ _ _ _ _ (Hk j Hj)). exact (H j Hj). Qed.
Lemma garr8_keep : forall (W W' : world SEGS) (m m' : word -> option byte) a l,
  (forall j, (j < length l)%nat -> aview SEGS (w_H W') m' (a + Z.of_nat j) = aview SEGS (w_H W) m (a + Z.of_nat j)) ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W' m') a l.
Proof.
intros W W' m m' a l Hk H j Hj. destruct (H j Hj) as [H1 H2]. split; [|exact H2].
apply (val_mem_keep W W' m m' _ 1 _); [|exact H1].
intros k Hk'. replace (a + Z.of_nat j + Z.of_nat k) with (a + Z.of_nat j) by lia. exact (Hk j Hj).
Qed.

Lemma d_E_envJ : forall cx E vals vs E', d_E cx E -> envJ (d_env cx E vals) vs E' -> d_E cx E'.
Proof.
intros cx E vals vs E' HE (HI & AG & _).
pose proof (d_E_env cx E vals HE) as (EE & E32 & _ & E60 & EF & ESH).
refine (conj _ (conj _ (conj HI (conj _ (conj _ _))))).
- intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite (AG n ltac:(lia)). exact (EE n r Hn).
- rewrite (AG 32%nat ltac:(lia)). exact E32.
- change AT_A with 60%nat in *. rewrite (AG 60%nat ltac:(lia)). exact E60.
- change AT_F with 516%nat in *. rewrite (AG 516%nat ltac:(lia)). exact EF.
- change AT_SH with 529%nat in *. rewrite (AG 529%nat ltac:(lia)). exact ESH.
Qed.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let DSEAT := d_seat B MT XM_LIB RLO RHI tfib_K.
Let DFACTS := d_facts_ok B MT XM_LIB RLO RHI tfib_K.
Let DLAND := d_land B MT XM_LIB RLO RHI tfib_K.
Let DBRT := d_body_rt B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Lemma region_ok_keep : forall E (W W' : world SEGS) (m m' : word -> option byte) r,
  region_ok SEGS E (rd W m) r ->
  (forall c i, In c (YP09.r_chunks r) -> 0 <= i < YP09.c_len c ->
     aview SEGS (w_H W') m' (base_val E (YP09.r_base r) + YP09.c_off c + i) =
     aview SEGS (w_H W) m (base_val E (YP09.r_base r) + YP09.c_off c + i)) ->
  (forall o, YP09.r_wlo r <= o < YP09.r_whi r -> apresent (w_H W') m' (base_val E (YP09.r_base r) + o)) ->
  region_ok SEGS E (rd W' m') r.
Proof.
intros E W W' m m' r (H1 & H2 & H3 & H4) Hc Hp. unfold region_ok.
split; [exact H1|]. split; [exact H2|]. split.
- intros o Ho. apply (apresent_writable SEGS). apply Hp. exact Ho.
- rewrite Forall_forall in *. intros c Hin i Hi. destruct (H4 c Hin i Hi) as (b & Hb & Hm).
  exists b. split; [exact Hb|]. rewrite (mbyte_of_aview SEGS _ _ _ _ _ (Hc c i Hin Hi)). exact Hm.
Qed.
Lemma rdword_keep : forall (rd rd' : reader) a, (forall j, 0 <= j < 8 -> rd' (a + j) = rd (a + j)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. unfold rdword.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma d_shadow_keep : forall cx shf (W W' : world SEGS) (m m' : word -> option byte),
  d_shadow cx shf W m ->
  (forall k, 0 <= k < DFRAME_SH -> aview SEGS (w_H W') m' (shadow_addr (d_FB cx) + k) = aview SEGS (w_H W) m (shadow_addr (d_FB cx) + k)) ->
  d_shadow cx shf W' m'.
Proof. intros cx shf W W' m m' H Hk k Hkk. rewrite (Hk k Hkk). exact (H k Hkk). Qed.

Lemma d_frame_keep : forall cx h shf (W W' : world SEGS) (m m' : word -> option byte) ly3 S3 md3 k,
  d_frame cx h shf W m -> d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W' m' md3 k ->
  (forall a, (d_A cx <= a < d_S cx \/ d_FB cx <= a < d_FB cx + 24 \/ d_FB cx + 4088 <= a < d_FB cx + 4096 \/
              shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512) ->
     aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  d_frame cx h shf W' m'.
Proof.
intros cx h shf W W' m m' ly3 S3 md3 k (E & HE & Hregs & Hflag & H216 & H152) Hctx Hkeep.
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W' m' md3 k Hctx)
  as (HS16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr & HA32). unfold MFRAME in HAr.
pose proof HE as (HER & H32 & HI & HA & HF & HSH).
assert (B2 : bv_unsigned (ew E AT_STK) = d_S cx) by (change AT_STK with 2%nat; rewrite (HER 2%nat 2%bv eq_refl); reflexivity).
assert (BA : bv_unsigned (ew E AT_A) = d_A cx) by (rewrite HA; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
assert (BF : bv_unsigned (ew E AT_F) = d_FB cx) by (rewrite HF; apply unsigned_lit_small; lia).
assert (BSH : bv_unsigned (ew E AT_SH) = shadow_addr (d_FB cx)).
{ rewrite HSH; apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. split; [|apply Z.lt_le_trans with (2147450880 + 2 ^ 47 / 8 + 1); [|lia]]; 
  pose proof (Z.div_pos (d_FB cx) 8 ltac:(lia) ltac:(lia)); [lia|]. assert (d_FB cx / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). lia. }
change (fs_frame_bytes DFRAME_CLASS) with 4096 in *.
exists E. split; [exact HE|]. split; [|split; [|split]].
- unfold d_regions in *. rewrite !Forall_cons_iff in Hregs. destruct Hregs as (R1 & R2 & R3 & R4 & _).
  repeat (apply Forall_cons); [| | | | apply Forall_nil].
  + apply (region_ok_keep E W W' m m' _ R1).
    * intros c i Hin Hi. cbn [YP09.r_chunks YP09.r_base base_val] in *. rewrite B2.
      unfold dsave_chunks in Hin. apply in_map_iff in Hin as (j & <- & Hj). apply in_seq in Hj.
      cbn [length dsave_regs] in Hj. cbn [YP09.c_off YP09.c_len YP09.c_val cv_len Z.of_N] in *.
      apply Hkeep. left. lia.
    * cbn. intros o Ho. lia.
  + apply (region_ok_keep E W W' m m' _ R2).
    * intros c i Hin Hi. cbn [YP09.r_chunks YP09.r_base base_val] in *. rewrite BA.
      unfold dslot_chunks in Hin. apply in_map_iff in Hin as (kv & <- & Hkv).
      assert (Hkv' : 0 <= fst kv <= 416) by (cbn [In] in Hkv; repeat destruct Hkv as [<-|Hkv]; cbn; lia).
      cbn [YP09.c_off YP09.c_len YP09.c_val cv_len Z.of_N] in *. apply Hkeep. left. lia.
    * cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val]. rewrite BA. intros o Ho. apply HStk. unfold LLVMF_STK. lia.
  + apply (region_ok_keep E W W' m m' _ R3).
    * intros c i Hin Hi. cbn [YP09.r_chunks YP09.r_base base_val] in *. rewrite BF.
      cbn [In] in Hin. repeat destruct Hin as [<-|Hin]; [..|destruct Hin]; cbn [YP09.c_off YP09.c_len YP09.c_val cv_len Z.of_N] in *;
      apply Hkeep; right; left; lia.
    * cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val]. rewrite BF. intros o Ho. apply HFp. unfold DFRAME_SIZE in Ho. lia.
  + apply (region_ok_keep E W W' m m' _ R4).
    * intros c i Hin Hi. cbn [YP09.r_chunks YP09.r_base base_val fshadow_region] in *. rewrite BSH.
      unfold dsh_chunks in Hin. apply in_map_iff in Hin as (j & <- & Hj). apply in_seq in Hj.
      cbn [YP09.c_off YP09.c_len YP09.c_val cv_len Z.of_N] in *. unfold DFRAME_SH in Hj.
      apply Hkeep. right; right; right. lia.
    * cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val fshadow_region]. rewrite BSH. intros o Ho. apply HSp. unfold DFRAME_SH in Ho. lia.
- rewrite (rdword_keep (aview SEGS (w_H W) m) (aview SEGS (w_H W') m')); [exact Hflag|].
  intros j Hj. apply Hkeep. right; right; left. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
- apply (val_mem_keep W W' m m' _ 8 _); [|exact H216]. intros j Hj. apply Hkeep. left. lia.
- apply (val_mem_keep W W' m m' _ 8 _); [|exact H152]. intros j Hj. apply Hkeep. left. lia.
Qed.

Lemma dsh_rec_t : forall k, 270 <= k < 320 -> dsh_rec k = 0.
Proof.
intros k Hk. assert (Hj : exists j, (j < 50)%nat /\ k = 270 + Z.of_nat j) by (exists (Z.to_nat (k - 270)); lia).
destruct Hj as (j & Hj & ->). do 50 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma dsh_rec_s : forall k, 374 <= k < 377 -> dsh_rec k = 0.
Proof.
intros k Hk. assert (Hj : exists j, (j < 3)%nat /\ k = 374 + Z.of_nat j) by (exists (Z.to_nat (k - 374)); lia).
destruct Hj as (j & Hj & ->). do 3 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma shadow_addr_off : forall F o, F mod 8 = 0 -> shadow_addr (F + o) = shadow_addr F + o / 8.
Proof.
intros F o HF. unfold shadow_addr. pose proof (Z.div_mod F 8 ltac:(lia)) as D.
replace (F + o) with (o + F / 8 * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.
Lemma ra_frame : forall cx shf (W : world SEGS) (m : word -> option byte) lo len,
  d_shadow cx shf W m -> d_FB cx mod 8 = 0 -> 0 <= lo -> 0 <= len -> lo + len <= 3072 ->
  (forall k, lo / 8 <= k < (lo + len + 7) / 8 -> shf k = 0) ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (d_FB cx + lo) len.
Proof.
intros cx shf W m lo len Hsh HF8 Hlo Hlen Hhi Hz x Hx. exists 0. split; [|left; reflexivity].
assert (Hq : shadow_of_addr SHADOW_OFF x = shadow_addr (d_FB cx) + (x - d_FB cx) / 8).
{ rewrite <- shadow_addr_off by exact HF8. replace (d_FB cx + (x - d_FB cx)) with x by lia. reflexivity. }
rewrite Hq. rewrite (Hsh ((x - d_FB cx) / 8)).
- rewrite Hz; [reflexivity|]. split; [apply Z.div_le_mono; lia|].
  apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.mod_pos_bound (lo + len + 7) 8 ltac:(lia)).
  pose proof (Z.div_mod (lo + len + 7) 8 ltac:(lia)). lia.
- unfold DFRAME_SH. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.
Lemma hull_frame : forall cx shf (W : world SEGS) (m : word -> option byte) lo len,
  d_shadow cx shf W m -> d_FB cx mod 8 = 0 -> 64 <= lo -> 0 < len -> lo + len <= 3016 ->
  shadow_hull_vis (aview SEGS (w_H W) m) (d_FB cx + lo) len.
Proof.
intros cx shf W m lo len Hsh HF8 Hlo Hlen Hhi s Hs.
assert (E1 : shadow_addr (d_FB cx + lo) = shadow_addr (d_FB cx) + lo / 8) by (apply shadow_addr_off; exact HF8).
assert (E2 : shadow_addr (d_FB cx + lo + len - 1) = shadow_addr (d_FB cx) + (lo + len - 1) / 8).
{ replace (d_FB cx + lo + len - 1) with (d_FB cx + (lo + len - 1)) by lia. apply shadow_addr_off; exact HF8. }
rewrite E1, E2 in Hs.
pose proof (Z.div_mod (shadow_addr (d_FB cx) + lo / 8) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (shadow_addr (d_FB cx) + lo / 8) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (shadow_addr (d_FB cx) + (lo + len - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (shadow_addr (d_FB cx) + (lo + len - 1) / 8) 8 ltac:(lia)) as M2.
assert (Lb : 8 <= lo / 8) by (apply Z.div_le_lower_bound; lia).
assert (Ub : (lo + len - 1) / 8 < 377) by (apply Z.div_lt_upper_bound; lia).
replace s with (shadow_addr (d_FB cx) + (s - shadow_addr (d_FB cx))) by lia.
rewrite (Hsh (s - shadow_addr (d_FB cx))); [discriminate|]. unfold DFRAME_SH. lia.
Qed.

Lemma d_rL_pres : forall cx regs regs', aregs_preserved regs regs' -> d_rL B cx regs -> d_rL B cx regs'.
Proof.
intros cx regs regs' HP (H2 & H3 & H4 & H8 & H9 & H18 & H20 & H25). unfold d_rL.
split; [unfold spZ in *; rewrite <- H2; f_equal; exact (HP 2 ltac:(unfold acallee_saved; lia))|].
split; [transitivity (getr regs 3%bv); [exact (HP 3 ltac:(unfold acallee_saved; lia)) | exact H3]|].
split; [transitivity (getr regs 4%bv); [exact (HP 4 ltac:(unfold acallee_saved; lia)) | exact H4]|].
split; [transitivity (getr regs 8%bv); [exact (HP 8 ltac:(unfold acallee_saved; lia)) | exact H8]|].
split; [transitivity (getr regs 9%bv); [exact (HP 9 ltac:(unfold acallee_saved; lia)) | exact H9]|].
split; [transitivity (getr regs 18%bv); [exact (HP 18 ltac:(unfold acallee_saved; lia)) | exact H18]|].
split; [transitivity (getr regs 20%bv); [exact (HP 20 ltac:(unfold acallee_saved; lia)) | exact H20]|].
transitivity (getr regs 25%bv); [exact (HP 25 ltac:(unfold acallee_saved; lia)) | exact H25].
Qed.

#[local] Notation ob_c9 := (ob_c9 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation r27_in := (r27_in B MT XM_LIB RLO RHI tfib_K).

Theorem ob_s9a : ob_seg9a B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len Sg kmax accmax W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hf0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ai & ow & ret & HOC & H26 & HobT & HrT & HrX & Hai & H13).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof HobT as (HTl0 & HTok0 & Hfind & How & Hsp22 & H408 & HOM).
pose proof Hsp22 as (H88 & H80 & H392 & H136 & H128 & H120 & H112 & H104 & H224 & H96 & H72).
pose proof Hsp0 as (H232 & H344).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoff & Hgeo & Hcanb & Hstk & Hawr).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
destruct (ob_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HctxD)
  as (_ & _ & _ & HF4 & HFc & HFia & HFo & HF32 & HFp & HSp & HStk & HAR & Hfin & Efa & Efl).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
set (xz := [u64 (oldv ai (role_of_e T ai)); u64 (oldv ai (hd_of T ai)); u64 (oldv ai (din_of T ai));
  u64 (oldv ai (dout_of T ai)); u64 (oldv ai (reac_disco_table_observe_c.fam_of T ai));
  u64 (oldv ai (reac_disco_table_observe_c.slots_of T ai)); u64 (oldv ai (s32_at T (48 * ai + 20)));
  u64 (oldv ai (owned_of T ai)); u64 (oldv ai (u_at T (48 * ai + 32) 8)); u64 (16 * ai); u64 (64 * ai);
  ow; nb; now; d_cur cx nb; len; fr; i; h; h + 440;
  u_at Sg 8 4; u_at Sg 12 1; u_at Sg 13 1; u_at Sg 14 1; u_at Sg 15 1; u_at Sg 16 1; u_at Sg 20 4; u_at T' 384 4]).
set (xv := map (Z_to_bv 64) xz).
set (Es := d_env cx E (obs_vals regs ++ xv)).
assert (XV : forall j, (j < 28)%nat -> ew Es (AT_X + 32 + j) = Z_to_bv 64 (nth j xz 0)).
{ intros j Hj. unfold Es. rewrite ew_dx by (unfold xv; rewrite length_map; cbn; lia). unfold xv.
  apply map_nth. }
assert (A563 : ew Es 563 = Z_to_bv 64 (u64 (oldv ai (role_of_e T ai)))) by exact (XV 0%nat ltac:(lia)).
assert (A564 : ew Es 564 = Z_to_bv 64 (u64 (oldv ai (hd_of T ai)))) by exact (XV 1%nat ltac:(lia)).
assert (A565 : ew Es 565 = Z_to_bv 64 (u64 (oldv ai (din_of T ai)))) by exact (XV 2%nat ltac:(lia)).
assert (A566 : ew Es 566 = Z_to_bv 64 (u64 (oldv ai (dout_of T ai)))) by exact (XV 3%nat ltac:(lia)).
assert (A567 : ew Es 567 = Z_to_bv 64 (u64 (oldv ai (reac_disco_table_observe_c.fam_of T ai)))) by exact (XV 4%nat ltac:(lia)).
assert (A568 : ew Es 568 = Z_to_bv 64 (u64 (oldv ai (reac_disco_table_observe_c.slots_of T ai)))) by exact (XV 5%nat ltac:(lia)).
assert (A569 : ew Es 569 = Z_to_bv 64 (u64 (oldv ai (s32_at T (48 * ai + 20))))) by exact (XV 6%nat ltac:(lia)).
assert (A570 : ew Es 570 = Z_to_bv 64 (u64 (oldv ai (owned_of T ai)))) by exact (XV 7%nat ltac:(lia)).
assert (A571 : ew Es 571 = Z_to_bv 64 (u64 (oldv ai (u_at T (48 * ai + 32) 8)))) by exact (XV 8%nat ltac:(lia)).
assert (A572 : ew Es 572 = Z_to_bv 64 (u64 (16 * ai))) by exact (XV 9%nat ltac:(lia)).
assert (A573 : ew Es 573 = Z_to_bv 64 (u64 (64 * ai))) by exact (XV 10%nat ltac:(lia)).
assert (A574 : ew Es 574 = Z_to_bv 64 (ow)) by exact (XV 11%nat ltac:(lia)).
assert (A575 : ew Es 575 = Z_to_bv 64 (nb)) by exact (XV 12%nat ltac:(lia)).
assert (A576 : ew Es 576 = Z_to_bv 64 (now)) by exact (XV 13%nat ltac:(lia)).
assert (A577 : ew Es 577 = Z_to_bv 64 (d_cur cx nb)) by exact (XV 14%nat ltac:(lia)).
assert (A578 : ew Es 578 = Z_to_bv 64 (len)) by exact (XV 15%nat ltac:(lia)).
assert (A579 : ew Es 579 = Z_to_bv 64 (fr)) by exact (XV 16%nat ltac:(lia)).
assert (A580 : ew Es 580 = Z_to_bv 64 (i)) by exact (XV 17%nat ltac:(lia)).
assert (A581 : ew Es 581 = Z_to_bv 64 (h)) by exact (XV 18%nat ltac:(lia)).
assert (A582 : ew Es 582 = Z_to_bv 64 (h + 440)) by exact (XV 19%nat ltac:(lia)).
assert (A583 : ew Es 583 = Z_to_bv 64 (u_at Sg 8 4)) by exact (XV 20%nat ltac:(lia)).
assert (A584 : ew Es 584 = Z_to_bv 64 (u_at Sg 12 1)) by exact (XV 21%nat ltac:(lia)).
assert (A585 : ew Es 585 = Z_to_bv 64 (u_at Sg 13 1)) by exact (XV 22%nat ltac:(lia)).
assert (A586 : ew Es 586 = Z_to_bv 64 (u_at Sg 14 1)) by exact (XV 23%nat ltac:(lia)).
assert (A587 : ew Es 587 = Z_to_bv 64 (u_at Sg 15 1)) by exact (XV 24%nat ltac:(lia)).
assert (A588 : ew Es 588 = Z_to_bv 64 (u_at Sg 16 1)) by exact (XV 25%nat ltac:(lia)).
assert (A589 : ew Es 589 = Z_to_bv 64 (u_at Sg 20 4)) by exact (XV 26%nat ltac:(lia)).
assert (A590 : ew Es 590 = Z_to_bv 64 (u_at T' 384 4)) by exact (XV 27%nat ltac:(lia)).
assert (A550 : ew Es 550 = Z_to_bv 64 (n_of T)).
{ unfold Es. change 550%nat with (AT_X + 19)%nat. rewrite (ew_dr cx E regs xv 19 ltac:(lia)). exact (proj1 HrT). }
assert (A552 : ew Es 552 = Z_to_bv 64 ret).
{ unfold Es. change 552%nat with (AT_X + 21)%nat. rewrite (ew_dr cx E regs xv 21 ltac:(lia)). exact (proj1 HrX). }
assert (Hain : 0 <= ai < n_of T) by (destruct Hfind as [[Exx _]|(Hrx & _)]; lia).
pose proof HTok0 as (Ht1 & Ht2 & Ht3 & Ht4).
assert (HSS : sighting_S1 Sg /\ sighting_S2 Sg) by (apply sight_S12; pose proof HSf as (_ & _ & _ & _ & _ & Hok & _); exact Hok).
destruct HSS as (HS1g & HS2g).
pose proof (Ht2 ai Hain) as Hrole. destruct (Ht4 ai Hain) as (Hhd & _ & Hown).
pose proof (obs_fields T Sg ow now T' ret ai HTl0 HSgl Hain ltac:(unfold tbl_T1 in Ht1; lia) ltac:(lia) ltac:(lia) Ht2 Ht4 HS1g HS2g Hfind HOM)
  as (HFlen & HFmac & HFn & HFrole & HFhd & HFdin & HFdout & HFfam & HFslots & HFch & HFown & HFfs & HFlast & HFret).
assert (Hai8 : ai < 8) by (unfold tbl_T1 in Ht1; lia).
assert (Ea0 : (ai <? 0) = false) by (apply Z.ltb_ge; lia).
Ltac efact HEJ n :=
  lazymatch type of HEJ with envJ ?Es ?vs ?E =>
  lazymatch goal with
  | _ : ew E n = Z_to_bv 64 _ |- _ => idtac
  | Ha : ew Es n = Z_to_bv 64 ?v |- _ =>
      let H := fresh "V" in assert (H : ew E n = Z_to_bv 64 v) by (rewrite (proj1 (proj2 HEJ) n ltac:(lia)); exact Ha)
  | _ => let j := eval vm_compute in (n - 64)%nat in
      let v := eval cbn [nth app] in (nth j vs 0) in
      let H := fresh "V" in assert (H : ew E n = Z_to_bv 64 v) by exact (proj2 (proj2 HEJ) j ltac:(cbn; lia))
  end end.
Ltac rng9 := first [ apply u_at_r4 | apply u_at_r1 | idtac ];
  repeat match goal with H : length ?L = _ |- context [length ?L] => rewrite H end; cbn; lia.
Ltac Uat9 HEJ :=
  repeat first
  [ rewrite Uadd0
  | match goal with |- context [U ?E (SExt true 32 (SOff ?n 0))] => efact HEJ n;
      match goal with H : ew E n = Z_to_bv 64 ?v |- _ => rewrite (UA32 E n v H) by rng9 end end
  | match goal with |- context [U ?E (SExt false 8 (SOff ?n 0))] => efact HEJ n;
      match goal with H : ew E n = Z_to_bv 64 ?v |- _ => rewrite (UA8 E n v H) by rng9 end end
  | match goal with |- context [U ?E (SOff ?n 0)] => efact HEJ n;
      match goal with H : ew E n = Z_to_bv 64 ?v |- _ => rewrite (UA0 E n v H) end end
  | rewrite U_SLit
  | rewrite U_SAlu ].
Ltac jv9 :=
  match goal with HS1 : st_ok_pi _ _ ?E1 ?ss1 (restrict (w_H ?W) ?ms1) |- map _ _ = map _ _ =>
  lazymatch E1 with havoc _ 64 _ => fail | havoc _ 65 _ => fail | havoc _ 66 _ => fail | havoc _ 69 _ => fail
    | havoc _ 70 _ => fail | havoc _ 71 _ => fail | havoc _ 72 _ => fail | _ => idtac end;
  cbn [map];
  repeat match goal with |- cons _ _ = cons _ _ => apply f_equal2 end;
  try reflexivity;
  match goal with |- getr _ ?r = _ =>
    cbn [ms_regs restrict];
    rewrite (st_ok_pi_restrict_reg (w_H W) E1 ss1 ms1 r HS1);
    let e := eval vm_compute in (sr_get (ss_regs ss1) r) in change (sr_get (ss_regs ss1) r) with e;
    rewrite denot_lit_U; apply w64_eqm
  end end.
Ltac hc9 HEJ :=
  lazymatch goal with Hc : branch_taken _ _ _ = _ |- _ =>
    rewrite ?branch_ne_U, ?branch_eq_U, ?branch_ltu_U in Hc; revert Hc; Uat9 HEJ; intros Hc end.
assert (RG : regs_ok Es sr9 regs) by (apply (regs_ok9 cx E regs xv HdE HrL H13 HAr2); lia).
assert (OTe : d_obj cx OT = d_FB cx + 2160) by reflexivity.
assert (OSe : d_obj cx OS = d_FB cx + 2992) by reflexivity.
assert (CA : Forall (YP09.chunk_ok SEGS Es (rd W mem3) (d_A cx)) acs9).
{ let l := eval vm_compute in acs9 in change acs9 with l.
  repeat apply Forall_cons; try apply Forall_nil;
  match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal _ (SOff ?a _))) =>
    match goal with Hv : val_mem _ _ (d_A cx + off) _ ?v |- _ =>
      apply (chunk_ok8 _ _ _ _ _ v); [| exact Hv];
      let j := eval vm_compute in (a - (AT_X + 32))%nat in
      exact (XV j ltac:(lia)) end end. }
assert (CF : Forall (YP09.chunk_ok SEGS Es (rd W mem3) (d_FB cx)) fcs9).
{ let l := eval vm_compute in fcs9 in change fcs9 with l.
  repeat apply Forall_cons; try apply Forall_nil;
  match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal ?w (SOff ?a 0))) =>
    let j := eval vm_compute in (a - (AT_X + 32))%nat in
    let v := eval cbn [nth xz] in (nth j xz 0) in
    apply (chunk_okW _ _ _ _ w a v); [exact (XV j ltac:(lia)) | | lia |];
    [ apply u_at_range; first [rewrite HSgl | rewrite HTl]; lia
    | first [ replace (d_FB cx + off) with (d_obj cx OS + (off - 2992)) by (rewrite OSe; lia); apply garr8_u; [lia | rewrite HSgl; cbn; lia | exact HSg]
            | replace (d_FB cx + off) with (d_obj cx OT + (off - 2160)) by (rewrite OTe; lia); apply garr8_u; [lia | rewrite HTl; cbn; lia | exact HT] ] ]
  end. }
pose proof (DSEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E 0x18b8 sr9 (obs_vals regs ++ xv) acs9 fcs9 [] (d_facts [] [])
  HctxD HdE Hregs Hflag RG
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (obs_vals regs ++ xv) [] [] HctxD HdE I I)
  CA CF (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
fold Es in HS.
unfold ss_d in HS.
ro_base HS 516%nat. ro_base HS 529%nat.
assert (HEI : img_env VAL A_LIM Es).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold Es, d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] Es (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS).
pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
unfold cfg_at. change (w64 (BASE + 0x18b8)) with (Z_to_bv 64 (BASE + 0x18b8)).
assert (A60 : forall vs Ec, envJ Es vs Ec -> bv_unsigned (ew Ec 60) = d_A cx).
{ intros vs Ec (_ & AG & _). rewrite (AG 60%nat ltac:(lia)). unfold Es. rewrite d_env_old by (cbv; lia).
  destruct HdE as (_ & _ & _ & HA60 & _). change AT_A with 60%nat in HA60. rewrite HA60. apply unsigned_lit_small. lia. }
assert (HM : obM cx W ly3 S3 mem3 k (mkst regs (Z_to_bv 64 (BASE + 0x18b8)) mem3 (seg_rom SEGS)) md3).
{ split; [exact HJ|]. split; [intros a _ _; reflexivity | intros a Ha; exact Ha]. }
assert (HEJ : envJ Es [] Es) by (apply envJ_init; exact HEI).
Ltac awr9 A60 HEJ :=
  lazymatch type of A60 with forall _ _, _ -> _ = d_A ?cx =>
  cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|];
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx)); [reflexivity | rewrite (A60 _ _ HEJ); lia | cbn; unfold LLVMF_STK; lia | cbn; lia |];
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil end.
Ltac win9 A60 HEJ :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros b wlo whi a Hin Ha; vm_compute in Hin;
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <-; cbn [base_val] in Ha; rewrite ?(A60 _ _ HEJ) in Ha; unfold obwin; lia|]);
  destruct Hin.
Ltac run9 RUN A60 :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _, HEJ : envJ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK OBspan; [awr9 A60 HEJ|] end.
Ltac runto9 RUNTO A60 pc :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _, HEJ : envJ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK OBspan pc; [awr9 A60 HEJ|] end.
Ltac upd9 A60 :=
  lazymatch goal with HM : obM _ _ _ _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _), HG : mem_grows _ _, HEJ : envJ _ _ _ |- _ =>
  let HM2 := fresh "HM" in
  pose proof (obM_run _ _ _ _ _ _ _ _ _ _ _ _ HM HJ HFr HG ltac:(win9 A60 HEJ)) as HM2; clear HM HFr HG; rename HM2 into HM
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
run9 RUN A60. upd9 A60.
Ltac join9 fq RUN RUNTO BR A60 pcJ rs vs' :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss (restrict (w_H ?W) ?ms), SHOK : sh_ok _ ?Bx ?SH _ _, HEJ : envJ ?Es ?vs _,
    HM : obM ?cx _ ?ly3 ?S3 ?mem3 ?kj _ _ |- SRr _ _ (mkCfg ?ms ?md) _ =>
  let kk := eval vm_compute in (64 + length vs)%nat in
  let na := eval vm_compute in (length (f_atoms (ss_facts ss))) in
  let nc := eval vm_compute in (length (f_conds (ss_facts ss))) in
  let nl := eval vm_compute in (length (f_alias (ss_facts ss))) in
  eapply (SRr_bind SEGS W (mkCfg ms md) (obJ fq cx W ly3 S3 mem3 kj Es (vs ++ vs') _)); [
  psrr_branch_tok RUN BR HS SHOK OBspan;
  runto9 RUNTO A60 pcJ;
  lazymatch goal with HS1 : st_ok_pi _ _ ?E1 ?ss1 (restrict _ ?ms1) |- SRr _ _ (mkCfg ?ms1 ?md1) _ =>
    let HJn := fresh "HJn" in
    pose proof (st_ok_pi_join E1 ss1 _ rs kk (seq 0 na) (seq 1 nc) (seq 0 nl) HS1 ltac:(vm_compute; reflexivity) ltac:(unfold A_TEXT; cbn; lia) eq_refl) as HJn;
    let s := eval vm_compute in (ss_join ss1 rs kk (seq 0 na) (seq 1 nc) (seq 0 nl)) in
    change (ss_join ss1 rs kk (seq 0 na) (seq 1 nc) (seq 0 nl)) with s in HJn;
    upd9 A60;
    apply SRr_ret; unfold obJ; split; [reflexivity|]; do 3 eexists; split; [reflexivity|];
    split; [exact HJn|];
    split; [apply (envJ_step _ _ _ _ vs' HEJ); [unfold A_TEXT; cbn; lia|] | assumption]
  end
  | let W' := fresh "W" in let c' := fresh "c" in let HJJ := fresh "HJJ" in
    intros W' c' _ HJJ;
    let E2 := fresh "E" in let ms2 := fresh "ms" in let md2 := fresh "md" in
    let HS2 := fresh "HS" in let HEJ2 := fresh "HEJ" in let HM2 := fresh "HM" in
    destruct HJJ as (-> & E2 & ms2 & md2 & -> & HS2 & HEJ2 & HM2);
    lazymatch goal with HJo : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => clear HJo end;
    clear HS HEJ HM SHOK; rename HS2 into HS; rename HEJ2 into HEJ; rename HM2 into HM;
    pose proof (proj1 HM) as HJ; let HEI2 := fresh "HEI" in pose proof (proj1 HEJ) as HEI2;
    assert (SHOK : sh_ok SEGS (SOff 32 0) [] E2 (mrestrict (w_H W) (ms_mem ms2))) by constructor ] end.
join9 fq RUN RUNTO BR A60 6364 [(11%bv : bv 5)] [if (role_of_e T ai =? 1) && (s_role Sg =? 2) then 1 else s_role Sg].
1-2: (jv9; hc9 HEJ; try change (bv_swrap 32 (u_at Sg 8 4)) with (s_role Sg) in Hc |- *; try change (u_at Sg 12 1) with (s_hd Sg) in Hc |- *; try change (u_at Sg 13 1) with (s_din Sg) in Hc |- *; try change (u_at Sg 14 1) with (s_dout Sg) in Hc |- *; try change (u_at Sg 15 1) with (s_fam Sg) in Hc |- *; try change (u_at Sg 16 1) with (s_slots Sg) in Hc |- *; try change (u_at Sg 20 4) with (s_ch Sg) in Hc |- *; unfold u64, oldv in Hc |- *; rewrite ?Ea0 in Hc; rewrite ?Ea0; cbn [zalu_raw] in Hc |- *; change (zcanon 0) with 0 in Hc; pose proof HS1g as HSq; pose proof Hrole as HRo; unfold sighting_S1 in HSq; destruct HSq as [Er|[Er|Er]]; rewrite ?Er in Hc; rewrite ?Er; destruct HRo as [Eo|[Eo|Eo]]; rewrite ?Eo in Hc; rewrite ?Eo; unfold slot_known.want_role; vm_compute in Hc; first [discriminate Hc | vm_compute; reflexivity]).
run9 RUN A60. upd9 A60.
join9 fq RUN RUNTO BR A60 6376 [(15%bv : bv 5)] [slot_known.want_role (s_role Sg) (role_of_e T ai)].
1-2: (jv9; hc9 HEJ; try change (bv_swrap 32 (u_at Sg 8 4)) with (s_role Sg) in Hc |- *; try change (u_at Sg 12 1) with (s_hd Sg) in Hc |- *; try change (u_at Sg 13 1) with (s_din Sg) in Hc |- *; try change (u_at Sg 14 1) with (s_dout Sg) in Hc |- *; try change (u_at Sg 15 1) with (s_fam Sg) in Hc |- *; try change (u_at Sg 16 1) with (s_slots Sg) in Hc |- *; try change (u_at Sg 20 4) with (s_ch Sg) in Hc |- *; unfold u64, oldv in Hc |- *; rewrite ?Ea0 in Hc; rewrite ?Ea0; cbn [zalu_raw] in Hc |- *; change (zcanon 0) with 0 in Hc; pose proof HS1g as HSq; pose proof Hrole as HRo; unfold sighting_S1 in HSq; destruct HSq as [Er|[Er|Er]]; rewrite ?Er in Hc; rewrite ?Er; destruct HRo as [Eo|[Eo|Eo]]; rewrite ?Eo in Hc; rewrite ?Eo; unfold slot_known.want_role; vm_compute in Hc; first [discriminate Hc | vm_compute; reflexivity]).
run9 RUN A60. upd9 A60.
join9 fq RUN RUNTO BR A60 6408 [(24%bv : bv 5); (27%bv : bv 5); (26%bv : bv 5)]
  [if s_hd Sg =? 0 then din_of T ai else s_din Sg; if s_hd Sg =? 0 then dout_of T ai else s_dout Sg;
   if s_hd Sg =? 0 then hd_of T ai else 1].
1-2: (jv9; hc9 HEJ; try change (bv_swrap 32 (u_at Sg 8 4)) with (s_role Sg) in Hc |- *; try change (u_at Sg 12 1) with (s_hd Sg) in Hc |- *; try change (u_at Sg 13 1) with (s_din Sg) in Hc |- *; try change (u_at Sg 14 1) with (s_dout Sg) in Hc |- *; try change (u_at Sg 15 1) with (s_fam Sg) in Hc |- *; try change (u_at Sg 16 1) with (s_slots Sg) in Hc |- *; try change (u_at Sg 20 4) with (s_ch Sg) in Hc |- *; unfold u64, oldv in Hc |- *; rewrite ?Ea0 in Hc; rewrite ?Ea0; cbn [zalu_raw] in Hc |- *; change (zcanon 0) with 0 in Hc; try (unfold s32_at in Hc |- *; rewrite ?zc_mod in Hc; rewrite zltu_sw in Hc by (first [apply u_at_r4; rewrite HTl0; lia | unfold s_ch; apply u_at_r4; rewrite HSgl; cbn; lia]); change (u_at T (48 * ai + 20) 4) with (reac_disco_table_observe_c.ch_of T ai) in Hc |- *); first [apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc | apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc]; repeat match goal with |- context [if (?a =? ?b) then _ else _] => destruct (Z.eqb_spec a b) as [Hq|Hq] | |- context [if (?a <? ?b) then _ else _] => destruct (Z.ltb_spec a b) as [Hq|Hq] end; unfold zcanon, M64 in Hc |- *; try (rewrite (Z.mod_small ow) in Hc by (destruct How as [->| ->]; lia)); rewrite ?Zmod_mod; first [reflexivity | exfalso; clear - Hc Hq; lia]).
run9 RUN A60. upd9 A60.
join9 fq RUN RUNTO BR A60 6424 [(6%bv : bv 5)] [if s_slots Sg =? 0 then reac_disco_table_observe_c.slots_of T ai else s_slots Sg].
1-2: (jv9; hc9 HEJ; try change (bv_swrap 32 (u_at Sg 8 4)) with (s_role Sg) in Hc |- *; try change (u_at Sg 12 1) with (s_hd Sg) in Hc |- *; try change (u_at Sg 13 1) with (s_din Sg) in Hc |- *; try change (u_at Sg 14 1) with (s_dout Sg) in Hc |- *; try change (u_at Sg 15 1) with (s_fam Sg) in Hc |- *; try change (u_at Sg 16 1) with (s_slots Sg) in Hc |- *; try change (u_at Sg 20 4) with (s_ch Sg) in Hc |- *; unfold u64, oldv in Hc |- *; rewrite ?Ea0 in Hc; rewrite ?Ea0; cbn [zalu_raw] in Hc |- *; change (zcanon 0) with 0 in Hc; try (unfold s32_at in Hc |- *; rewrite ?zc_mod in Hc; rewrite zltu_sw in Hc by (first [apply u_at_r4; rewrite HTl0; lia | unfold s_ch; apply u_at_r4; rewrite HSgl; cbn; lia]); change (u_at T (48 * ai + 20) 4) with (reac_disco_table_observe_c.ch_of T ai) in Hc |- *); first [apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc | apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc]; repeat match goal with |- context [if (?a =? ?b) then _ else _] => destruct (Z.eqb_spec a b) as [Hq|Hq] | |- context [if (?a <? ?b) then _ else _] => destruct (Z.ltb_spec a b) as [Hq|Hq] end; unfold zcanon, M64 in Hc |- *; try (rewrite (Z.mod_small ow) in Hc by (destruct How as [->| ->]; lia)); rewrite ?Zmod_mod; first [reflexivity | exfalso; clear - Hc Hq; lia]).
run9 RUN A60. upd9 A60.
join9 fq RUN RUNTO BR A60 6440 [(7%bv : bv 5)] [if s_fam Sg =? 0 then reac_disco_table_observe_c.fam_of T ai else s_fam Sg].
1-2: (jv9; hc9 HEJ; try change (bv_swrap 32 (u_at Sg 8 4)) with (s_role Sg) in Hc |- *; try change (u_at Sg 12 1) with (s_hd Sg) in Hc |- *; try change (u_at Sg 13 1) with (s_din Sg) in Hc |- *; try change (u_at Sg 14 1) with (s_dout Sg) in Hc |- *; try change (u_at Sg 15 1) with (s_fam Sg) in Hc |- *; try change (u_at Sg 16 1) with (s_slots Sg) in Hc |- *; try change (u_at Sg 20 4) with (s_ch Sg) in Hc |- *; unfold u64, oldv in Hc |- *; rewrite ?Ea0 in Hc; rewrite ?Ea0; cbn [zalu_raw] in Hc |- *; change (zcanon 0) with 0 in Hc; try (unfold s32_at in Hc |- *; rewrite ?zc_mod in Hc; rewrite zltu_sw in Hc by (first [apply u_at_r4; rewrite HTl0; lia | unfold s_ch; apply u_at_r4; rewrite HSgl; cbn; lia]); change (u_at T (48 * ai + 20) 4) with (reac_disco_table_observe_c.ch_of T ai) in Hc |- *); first [apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc | apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc]; repeat match goal with |- context [if (?a =? ?b) then _ else _] => destruct (Z.eqb_spec a b) as [Hq|Hq] | |- context [if (?a <? ?b) then _ else _] => destruct (Z.ltb_spec a b) as [Hq|Hq] end; unfold zcanon, M64 in Hc |- *; try (rewrite (Z.mod_small ow) in Hc by (destruct How as [->| ->]; lia)); rewrite ?Zmod_mod; first [reflexivity | exfalso; clear - Hc Hq; lia]).
run9 RUN A60. upd9 A60.
join9 fq RUN RUNTO BR A60 6464 [(12%bv : bv 5)]
  [bv_swrap 32 (if reac_disco_table_observe_c.ch_of T ai <? s_ch Sg then s_ch Sg else reac_disco_table_observe_c.ch_of T ai)].
1-2: (jv9; hc9 HEJ; try change (bv_swrap 32 (u_at Sg 8 4)) with (s_role Sg) in Hc |- *; try change (u_at Sg 12 1) with (s_hd Sg) in Hc |- *; try change (u_at Sg 13 1) with (s_din Sg) in Hc |- *; try change (u_at Sg 14 1) with (s_dout Sg) in Hc |- *; try change (u_at Sg 15 1) with (s_fam Sg) in Hc |- *; try change (u_at Sg 16 1) with (s_slots Sg) in Hc |- *; try change (u_at Sg 20 4) with (s_ch Sg) in Hc |- *; unfold u64, oldv in Hc |- *; rewrite ?Ea0 in Hc; rewrite ?Ea0; cbn [zalu_raw] in Hc |- *; change (zcanon 0) with 0 in Hc; try (unfold s32_at in Hc |- *; rewrite ?zc_mod in Hc; rewrite zltu_sw in Hc by (first [apply u_at_r4; rewrite HTl0; lia | unfold s_ch; apply u_at_r4; rewrite HSgl; cbn; lia]); change (u_at T (48 * ai + 20) 4) with (reac_disco_table_observe_c.ch_of T ai) in Hc |- *); first [apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc | apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc]; repeat match goal with |- context [if (?a =? ?b) then _ else _] => destruct (Z.eqb_spec a b) as [Hq|Hq] | |- context [if (?a <? ?b) then _ else _] => destruct (Z.ltb_spec a b) as [Hq|Hq] end; unfold zcanon, M64 in Hc |- *; try (rewrite (Z.mod_small ow) in Hc by (destruct How as [->| ->]; lia)); rewrite ?Zmod_mod; first [reflexivity | exfalso; clear - Hc Hq; lia]).
run9 RUN A60. upd9 A60.
join9 fq RUN RUNTO BR A60 6484 [(14%bv : bv 5)] [if ow =? 0 then owned_of T ai else 1].
1-2: (jv9; hc9 HEJ; try change (bv_swrap 32 (u_at Sg 8 4)) with (s_role Sg) in Hc |- *; try change (u_at Sg 12 1) with (s_hd Sg) in Hc |- *; try change (u_at Sg 13 1) with (s_din Sg) in Hc |- *; try change (u_at Sg 14 1) with (s_dout Sg) in Hc |- *; try change (u_at Sg 15 1) with (s_fam Sg) in Hc |- *; try change (u_at Sg 16 1) with (s_slots Sg) in Hc |- *; try change (u_at Sg 20 4) with (s_ch Sg) in Hc |- *; unfold u64, oldv in Hc |- *; rewrite ?Ea0 in Hc; rewrite ?Ea0; cbn [zalu_raw] in Hc |- *; change (zcanon 0) with 0 in Hc; try (unfold s32_at in Hc |- *; rewrite ?zc_mod in Hc; rewrite zltu_sw in Hc by (first [apply u_at_r4; rewrite HTl0; lia | unfold s_ch; apply u_at_r4; rewrite HSgl; cbn; lia]); change (u_at T (48 * ai + 20) 4) with (reac_disco_table_observe_c.ch_of T ai) in Hc |- *); first [apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc | apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc]; repeat match goal with |- context [if (?a =? ?b) then _ else _] => destruct (Z.eqb_spec a b) as [Hq|Hq] | |- context [if (?a <? ?b) then _ else _] => destruct (Z.ltb_spec a b) as [Hq|Hq] end; unfold zcanon, M64 in Hc |- *; try (rewrite (Z.mod_small ow) in Hc by (destruct How as [->| ->]; lia)); rewrite ?Zmod_mod; first [reflexivity | exfalso; clear - Hc Hq; lia]).
run9 RUN A60. upd9 A60.
lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ => psrr_branch_tok RUN BR HS SHOK OBspan end.
{ exfalso; lazymatch goal with Hc : branch_taken BC_NE _ _ = true |- _ => rewrite branch_ne_U in Hc; revert Hc; Uat9 HEJ; intros Hc; rewrite HFn in Hc; change (bv_swrap 32 (u_at T 384 4)) with (n_of T) in Hc; rewrite Z.eqb_refl in Hc; discriminate Hc end. }
run9 RUN A60. upd9 A60.
lazymatch goal with HS : st_ok _ ?Ec (setpc ?ssc _) (restrict (w_H W) ?msX) |- _ => rename HS into HSc end.
pose proof HEJ as (HIc & AGc & JVc).
pose proof alloc_ceiling_val as Hac.
assert (FB8 : d_FB cx mod 8 = 0) by lia.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in *.
unfold LLVMF_STK in HSr.
Ltac creg HSc r :=
  lazymatch type of HSc with st_ok _ ?E ?ss (restrict ?H ?m) =>
    rewrite (st_ok_restrict_reg SEGS H E ss m r HSc);
    let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
  end.
lazymatch goal with HSc : st_ok _ ?Ec ?ss (restrict (w_H W) ?msX), HEJ : envJ _ _ ?Ec, HM : obM _ _ _ _ _ _ ?msX ?mdX |- _ =>
  assert (E516 : ew Ec 516 = Z_to_bv 64 (d_FB cx)) by (rewrite (AGc 516%nat ltac:(lia)); unfold Es, d_env; rewrite ew_havoc_old by (cbv; lia); destruct HdE as (_ & _ & _ & _ & HF & _); exact HF);
  assert (B516 : bv_unsigned (ew Ec 516) = d_FB cx) by (rewrite E516; apply unsigned_lit_small; lia);
  assert (B60 : bv_unsigned (ew Ec 60) = d_A cx) by exact (A60 _ _ HEJ);
  assert (E572 : ew Ec 572 = Z_to_bv 64 (u64 (16 * ai))) by (rewrite (AGc 572%nat ltac:(lia)); exact A572);
  assert (E573 : ew Ec 573 = Z_to_bv 64 (u64 (64 * ai))) by (rewrite (AGc 573%nat ltac:(lia)); exact A573);
  assert (V65 : ew Ec 65 = Z_to_bv 64 (slot_known.want_role (s_role Sg) (role_of_e T ai))) by exact (JVc 1%nat ltac:(cbn; lia));
  assert (V66 : ew Ec 66 = Z_to_bv 64 (if s_hd Sg =? 0 then din_of T ai else s_din Sg)) by exact (JVc 2%nat ltac:(cbn; lia));
  assert (V67 : ew Ec 67 = Z_to_bv 64 (if s_hd Sg =? 0 then dout_of T ai else s_dout Sg)) by exact (JVc 3%nat ltac:(cbn; lia));
  assert (V68 : ew Ec 68 = Z_to_bv 64 (if s_hd Sg =? 0 then hd_of T ai else 1)) by exact (JVc 4%nat ltac:(cbn; lia));
  assert (V69 : ew Ec 69 = Z_to_bv 64 (if s_slots Sg =? 0 then reac_disco_table_observe_c.slots_of T ai else s_slots Sg)) by exact (JVc 5%nat ltac:(cbn; lia));
  assert (V70 : ew Ec 70 = Z_to_bv 64 (if s_fam Sg =? 0 then reac_disco_table_observe_c.fam_of T ai else s_fam Sg)) by exact (JVc 6%nat ltac:(cbn; lia));
  assert (V71 : ew Ec 71 = Z_to_bv 64 (bv_swrap 32 (if reac_disco_table_observe_c.ch_of T ai <? s_ch Sg then s_ch Sg else reac_disco_table_observe_c.ch_of T ai))) by exact (JVc 7%nat ltac:(cbn; lia));
  assert (V72 : ew Ec 72 = Z_to_bv 64 (if ow =? 0 then owned_of T ai else 1)) by exact (JVc 8%nat ltac:(cbn; lia))
end.
lazymatch goal with HSc : st_ok _ ?Ec ?ss (restrict (w_H W) ?msX), HEJ : envJ _ _ ?Ec, HM : obM _ _ _ _ _ _ ?msX ?mdX |- _ =>
  assert (RG22 : getr (ms_regs msX) 22 = w64 (d_obj cx OT + 48 * ai))
    by (creg HSc (22%bv : bv 5); rewrite (s6_val _ (d_FB cx) ai E516 E572 E573); unfold w64; rewrite OTe; f_equal; lia);
  assert (RG10 : getr (ms_regs msX) 10 = w64 (d_obj cx OT + 48 * ai))
    by (creg HSc (10%bv : bv 5); rewrite (s6_val _ (d_FB cx) ai E516 E572 E573); unfold w64; rewrite OTe; f_equal; lia);
  assert (RG11 : getr (ms_regs msX) 11 = w64 (d_obj cx OS))
    by (creg HSc (11%bv : bv 5); cbn [sv_denot]; rewrite E516, w64_add_w; unfold w64; rewrite OSe; reflexivity);
  assert (RG12 : getr (ms_regs msX) 12 = w64 6) by (creg HSc (12%bv : bv 5); reflexivity);
  assert (RG1 : getr (ms_regs msX) 1 = Z_to_bv 64 (BASE + 6544)) by (creg HSc (1%bv : bv 5); exact (codeptr_val _ 6544 HIc));
  assert (RSP : spZ (ms_regs msX) = d_A cx) by (unfold spZ; creg HSc (2%bv : bv 5); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact B60)
end.
Ltac rval HSc AGc r :=
  creg HSc r; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
Ltac rkeep HSc AGc RG r :=
  creg HSc r; rewrite (RG r);
  match goal with |- context [sr_get ?s2 r] => let v2 := eval vm_compute in (sr_get s2 r) in change (sr_get s2 r) with v2 end;
  cbn [sv_denot]; rewrite AGc by lia; reflexivity.
lazymatch goal with HSc : st_ok _ ?Ec ?ss (restrict (w_H W) ?msX), HEJ : envJ _ _ ?Ec, HM : obM _ _ _ _ _ _ ?msX ?mdX |- _ =>
  assert (RG19 : getr (ms_regs msX) 19 = ew Ec 65) by (rval HSc AGc (19%bv : bv 5); reflexivity);
  assert (RG21 : getr (ms_regs msX) 21 = ew Ec 69) by (rval HSc AGc (21%bv : bv 5); reflexivity);
  assert (RG23 : getr (ms_regs msX) 23 = ew Ec 70) by (rval HSc AGc (23%bv : bv 5); reflexivity);
  assert (RG24 : getr (ms_regs msX) 24 = ew Ec 66) by (rval HSc AGc (24%bv : bv 5); reflexivity);
  assert (RG26 : getr (ms_regs msX) 26 = ew Ec 68) by (rval HSc AGc (26%bv : bv 5); reflexivity);
  assert (RG27 : getr (ms_regs msX) 27 = ew Ec 67) by (rval HSc AGc (27%bv : bv 5); reflexivity);
  assert (K2 : getr (ms_regs msX) 2 = getr regs 2) by (rkeep HSc AGc RG (2%bv : bv 5));
  assert (K3 : getr (ms_regs msX) 3 = getr regs 3) by (rkeep HSc AGc RG (3%bv : bv 5));
  assert (K4 : getr (ms_regs msX) 4 = getr regs 4) by (rkeep HSc AGc RG (4%bv : bv 5));
  assert (K8 : getr (ms_regs msX) 8 = getr regs 8) by (rkeep HSc AGc RG (8%bv : bv 5));
  assert (K9 : getr (ms_regs msX) 9 = getr regs 9) by (rkeep HSc AGc RG (9%bv : bv 5));
  assert (K18 : getr (ms_regs msX) 18 = getr regs 18) by (rkeep HSc AGc RG (18%bv : bv 5));
  assert (K20 : getr (ms_regs msX) 20 = getr regs 20) by (rkeep HSc AGc RG (20%bv : bv 5));
  assert (K25 : getr (ms_regs msX) 25 = getr regs 25) by (rkeep HSc AGc RG (25%bv : bv 5));
  assert (HrLX : d_rL B cx (ms_regs msX))
    by (pose proof HrL as (Xsp & Xgp & Xtp & X8 & X9 & X18 & X20 & X25); unfold d_rL, spZ in *;
        rewrite K2, K3, K4, K8, K9, K18, K20, K25; repeat split; assumption)
end.
Ltac cvm HSc B60 AGc :=
  lazymatch type of HSc with st_ok _ ?E ?ss ?ms =>
  lazymatch goal with |- val_mem _ _ (d_A ?cx + ?off) 8 ?v =>
    let r := eval vm_compute in (nth 1 (ss_mem ss) got_regionP) in
    let c := eval vm_compute in (find (fun ch => Z.eqb (YP09.c_off ch) off) (YP09.r_chunks r)) in
    lazymatch c with Some (YP09.mkChunk _ (CVal 8 ?e)) =>
      apply (chunk_vm E ss ms 1 r 60%nat off e (d_A cx) v HSc);
      [ vm_compute; reflexivity | reflexivity | cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]) | exact B60
      | try (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; first [assumption | rewrite AGc by lia; assumption]) ]
    end end end.
lazymatch goal with HSc : st_ok _ ?Ec ?ss (restrict (w_H W) ?msX), HEJ : envJ _ _ ?Ec, HM : obM _ _ _ _ _ _ ?msX ?mdX |- _ =>
  assert (M392 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 392) 8 (u64 (oldv ai (role_of_e T ai)))) by (cvm HSc B60 AGc);
  assert (M136 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 136) 8 (u64 (oldv ai (hd_of T ai)))) by (cvm HSc B60 AGc);
  assert (M128 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 128) 8 (u64 (oldv ai (din_of T ai)))) by (cvm HSc B60 AGc);
  assert (M120 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 120) 8 (u64 (oldv ai (dout_of T ai)))) by (cvm HSc B60 AGc);
  assert (M112 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 112) 8 (u64 (oldv ai (reac_disco_table_observe_c.fam_of T ai)))) by (cvm HSc B60 AGc);
  assert (M104 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 104) 8 (u64 (oldv ai (reac_disco_table_observe_c.slots_of T ai)))) by (cvm HSc B60 AGc);
  assert (M224 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 224) 8 (u64 (oldv ai (s32_at T (48 * ai + 20))))) by (cvm HSc B60 AGc);
  assert (M96 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 96) 8 (u64 (oldv ai (owned_of T ai)))) by (cvm HSc B60 AGc);
  assert (M72 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 72) 8 (u64 (oldv ai (u_at T (48 * ai + 32) 8)))) by (cvm HSc B60 AGc);
  assert (M88 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 88) 8 (if ow =? 0 then owned_of T ai else 1)) by (cvm HSc B60 AGc);
  assert (M408 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 408) 8 ret) by (cvm HSc B60 AGc);
  assert (MA64 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 64) 8
    (bv_swrap 32 (if reac_disco_table_observe_c.ch_of T ai <? s_ch Sg then s_ch Sg else reac_disco_table_observe_c.ch_of T ai))) by (cvm HSc B60 AGc);
  assert (MA56 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 56) 8 (bv_swrap 32 (s_ch Sg)))
    by (cvm HSc B60 AGc; rewrite denot_lit_U, (UA32 Ec 589 (u_at Sg 20 4) ltac:(rewrite AGc by lia; exact A589) ltac:(apply u_at_r4; rewrite HSgl; cbn; lia));
        apply w64_eqm; unfold zcanon, M64; rewrite Zmod_mod; reflexivity);
  assert (M368 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 368) 8 nb) by (cvm HSc B60 AGc);
  assert (M344 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 344) 8 now) by (cvm HSc B60 AGc);
  assert (M248 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 248) 8 (d_cur cx nb)) by (cvm HSc B60 AGc);
  assert (M336 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 336) 8 len) by (cvm HSc B60 AGc);
  assert (M280 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 280) 8 fr) by (cvm HSc B60 AGc);
  assert (M232 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 232) 8 i) by (cvm HSc B60 AGc);
  assert (M216 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 216) 8 h) by (cvm HSc B60 AGc);
  assert (M152 : val_mem SEGS (rd W (ms_mem msX)) (d_A cx + 152) 8 (h + 440)) by (cvm HSc B60 AGc)
end.
lazymatch goal with HSc : st_ok _ ?Ec ?ss (restrict (w_H W) ?msX), HEJ : envJ _ _ ?Ec, HM : obM _ _ _ _ _ _ ?msX ?mdX |- _ =>
  pose proof (st_ok_repc Ec ss msX (BASE + 6544) (w_H W) eq_refl HSc) as HSrp;
  lazymatch type of HSrp with st_ok _ _ (setpc ?s0 _) (restrict _ ?msL) =>
    assert (HSpi : st_ok_pi SEGS VAL Ec (setpc s0 6544) (restrict (w_H W) msL)) by exact HSrp;
  assert (HctxT : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem msX) mdX k) by (split; [exact Hbase | split; [exact (proj1 HM) | exact Hfrs]]);
  assert (EFL : ew Ec AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)))
    by (change AT_FL with 530%nat; rewrite (AGc 530%nat ltac:(lia)); exact (d_env_fl cx E _));
  destruct (DLAND LAWS FFL fq cx h dsh_rec ly3 S3 W mdX k Ec _ msL HctxT (d_E_envJ cx E _ _ Ec HdE HEJ) EFL HSpi
    ltac:(vm_compute; reflexivity) M216 M152) as [HframeT HshadowT]; clear HSrp HSpi end
end.
lazymatch goal with HSc : st_ok _ ?Ec ?ss (restrict (w_H W) ?msX), HEJ : envJ _ _ ?Ec, HM : obM _ _ _ _ _ _ ?msX ?mdX |- _ =>
  pmkst HSc;
  eapply SRr_bind; [ eapply (aj_bcmp_at (fx := fq) SEGS B LAWS pa_segs_low (SIGMA DS___interceptor_trampoline_bcmp) (ABCMP fq) W
    (ms_regs msX) (ms_mem msX) LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)]
    ly3 S3 _ k (d_obj cx OT + 48 * ai) (d_obj cx OS) 6 (d_A cx - d_S cx) (Z_to_bv 64 (BASE + 6544)) (proj1 HM)) | ];
  [ exact RG10 | exact RG11 | exact RG12 | lia
  | rewrite OTe; lia | rewrite OTe; lia | rewrite OSe; lia | rewrite OSe; lia
  | rewrite RSP; lia | lia | lia | unfold ESTACK, LLVMF_STK; lia
  | rewrite K3; exact (proj1 (proj2 HrL)) | rewrite K4; exact (proj1 (proj2 (proj2 HrL)))
  | exact RG1 | apply ret_ok_codeptr_v; [lia | reflexivity]
  | let a := fresh in let Ha := fresh in intros a Ha; split;
    [ rewrite (proj1 (proj2 HM) a ltac:(rewrite OTe in Ha; lia) ltac:(unfold obwin; rewrite OTe in Ha; lia));
      apply (FindEntry.fe_aview_some (w_H W) mem3 (d_obj cx OT) T' a HT); rewrite HTl; cbn; lia
    | rewrite RSP; rewrite OTe in Ha; unfold ESTACK; lia ]
  | let a := fresh in let Ha := fresh in intros a Ha; split;
    [ rewrite (proj1 (proj2 HM) a ltac:(rewrite OSe in Ha; lia) ltac:(unfold obwin; rewrite OSe in Ha; lia));
      apply (FindEntry.fe_aview_some (w_H W) mem3 (d_obj cx OS) Sg a HSg); rewrite HSgl; cbn; lia
    | rewrite RSP; rewrite OSe in Ha; unfold ESTACK; lia ]
  | let a := fresh in let Ha := fresh in intros a Ha; rewrite OTe in Ha; unfold ESTACK; lia
  | let a := fresh in let Ha := fresh in intros a Ha; rewrite OSe in Ha; unfold ESTACK; lia
  | apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg in HFia; rewrite OTe; lia | rewrite OTe; lia]
  | apply amem_range_high; [lia | unfold in_app, kLowShadowBeg, kHighMemBeg in HFia; rewrite OSe; lia | rewrite OSe; lia]
  | replace (d_obj cx OT + 48 * ai) with (d_FB cx + (2160 + 48 * ai)) by (rewrite OTe; lia);
    exact (ra_frame cx dsh_rec W (ms_mem msX) (2160 + 48 * ai) 6 HshadowT FB8 ltac:(lia) ltac:(lia) ltac:(lia)
      (fun kk Hkk => dsh_rec_t kk ltac:(lia)))
  | intros _; replace (d_obj cx OT + 48 * ai) with (d_FB cx + (2160 + 48 * ai)) by (rewrite OTe; lia);
    exact (hull_frame cx dsh_rec W (ms_mem msX) (2160 + 48 * ai) 6 HshadowT FB8 ltac:(lia) ltac:(lia) ltac:(lia))
  | replace (d_obj cx OS) with (d_FB cx + 2992) by (rewrite OSe; lia);
    exact (ra_frame cx dsh_rec W (ms_mem msX) 2992 6 HshadowT FB8 ltac:(lia) ltac:(lia) ltac:(lia)
      (fun kk Hkk => dsh_rec_s kk ltac:(lia)))
  | intros _; replace (d_obj cx OS) with (d_FB cx + 2992) by (rewrite OSe; lia);
    exact (hull_frame cx dsh_rec W (ms_mem msX) 2992 6 HshadowT FB8 ltac:(lia) ltac:(lia) ltac:(lia))
  | idtac ]
end.
lazymatch goal with HSc : st_ok _ ?Ec ?ss (restrict (w_H W) ?msX), HEJ : envJ _ _ ?Ec, HM : obM _ _ _ _ _ _ ?msX ?mdX |- _ =>
  cbv beta; intros W2 c2 _ HPP;
  destruct HPP as (-> & regsB & memB & mdB & vB & -> & HJB & HPB & HvB & Hcmp & HfrB & HpresB);
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx - 8192 <= a < d_A cx) ->
     aview SEGS (w_H W) memB a = aview SEGS (w_H W) (ms_mem msX) a)
    by (intros a Hxa Hxn; apply HfrB; [exact Hxa | unfold ESTACK; lia]);
  pose proof (proj1 (proj2 HM)) as KX;
  assert (KM : d_kept (obwin cx) W mem3 W memB)
    by (intros a Hxa Hxn; rewrite (KB a Hxa ltac:(unfold obwin in Hxn; lia)); exact (KX a Hxa Hxn));
  assert (KA : forall a nn v, d_A cx <= a -> a + Z.of_nat nn <= d_A cx + 472 ->
     val_mem SEGS (rd W (ms_mem msX)) a nn v -> val_mem SEGS (rd W memB) a nn v)
    by (intros a nn v Hy1 Hy2 Hyv; apply (val_mem_keep W W (ms_mem msX) memB a nn v); [intros j Hj; apply KB; lia | exact Hyv]);
  assert (KF : forall a l, garr8 SEGS (rd W mem3) a l -> d_FB cx <= a -> a + Z.of_nat (length l) <= d_FB cx + 4096 ->
     garr8 SEGS (rd W memB) a l)
    by (intros a l Hyg Hy1 Hy2; apply (garr8_keep W W mem3 memB a l); [intros j Hj; apply KM; [lia | unfold obwin; lia] | exact Hyg]);
  assert (HctxB : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W memB mdB k) by (split; [exact Hbase | split; [exact HJB | exact Hfrs]]);
  assert (HframeB : d_frame cx h dsh_rec W memB)
    by (apply (d_frame_keep cx h dsh_rec W W (ms_mem msX) memB ly3 S3 mdB k HframeT HctxB);
        intros a Hxa; apply KB; unfold shadow_addr, SHADOW_OFF in *; lia);
  assert (HshadowB : d_shadow cx dsh_rec W memB)
    by (apply (d_shadow_keep cx dsh_rec W W (ms_mem msX) memB HshadowT); intros kk Hkk; apply KB; unfold shadow_addr, SHADOW_OFF, DFRAME_SH in *; lia);
  assert (Hbody4 : d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W memB)
    by (apply (DBRT cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 memB (d_A cx - 8192) (d_A cx + 472) (obwin cx) Hbody);
        [ unfold LLVMF_STK; lia | lia | intros a Hxa; left; exact Hxa | exact KM
        | intros a _ Hp; apply HpresB; exact (proj2 (proj2 HM) a Hp) | exact HframeB | exact HshadowB | lia ]);
  assert (LS6 : length (s_mac Sg) = 6%nat) by (change (length (firstn 6 Sg) = 6%nat); rewrite length_firstn, HSgl; reflexivity);
  assert (GS6 : garr8 SEGS (rd W mem3) (d_obj cx OS) (map bv_unsigned (s_mac Sg)))
    by (change (garr8 SEGS (mrestrict (w_H W) mem3) (d_obj cx OS) (map bv_unsigned (firstn 6 Sg))); rewrite <- firstn_map;
        replace (d_obj cx OS) with (d_obj cx OS + Z.of_nat 0) by lia; exact (garr8_sub_x SEGS _ _ _ 0 6 HSg ltac:(rewrite length_map; lia)));
  assert (MACEQ : forall i0, 0 <= i0 < 6 ->
     aview SEGS (w_H W) mem3 (d_obj cx OT + 48 * ai + i0) = aview SEGS (w_H W) mem3 (d_obj cx OS + i0))
    by (apply (proj2 (FindEntry.fe_mac (w_H W) mem3 (d_obj cx OT) (d_obj cx OS) T' (s_mac Sg) ai HTl LS6 ltac:(lia) HT GS6));
        rewrite (HFmac ai ltac:(lia)); destruct Hfind as [[Ex _]|(_ & Hm & _)]; [lia | exact Hm]);
  apply SRr_ret; unfold ob_c11, d_at;
  exists fq, ly3, S3, regsB, memB, mdB, k, acc;
  split; [unfold cfg_at, w64; reflexivity|];
  split; [exact Hf0|]; split; [exact Hbase|]; split; [exact HJB|]; split; [exact Hfrs|]; split; [exact Hk|];
  split; [exact Hnev|]; split; [exact Hmo|]; split; [exact Hacc|];
  exists T, T', ai, ow, ret;
  split;
  [ unfold oc;
    refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj _ (conj _ (conj _ (conj HSgl (conj _ (conj HSf
      (conj _ (conj _ (conj _ (conj _ (conj Hlen (conj Hnb (conj HTl (conj _ (conj HTok Hbody4))))))))))))))))))));
    [ exact (d_rL_pres cx (ms_regs msX) regsB HPB HrLX)
    | split; (apply (KA _ 8%nat _); [lia | cbn; lia | assumption])
    | destruct Hfrm as (Ff1 & F2 & Ffn & F3); split; [exact Ff1|]; split; [exact F2|]; split; [exact Ffn|];
      destruct (Z.eq_dec fr 0) as [Efr0|Efr0];
      [ rewrite (F2 Efr0); exact (garr8_nil SEGS _ _)
      | assert (Hin : In (fr, len) (ablocks B ly3 S3))
          by (destruct Hblocks as (Hperm & _); apply (Permutation_in _ (Permutation_sym Hperm)); unfold dxb;
              rewrite (proj2 (Z.eqb_neq fr 0) Efr0); left; reflexivity);
        destruct (al_blocks _ _ LAWS ly3 S3 W mem3 md3 fr len HAR Hin) as (_ & Hfr4 & Hfrc & _);
        assert (Hrq : len <= req_size len) by (unfold req_size; destruct (Z.eqb_spec len 0); lia);
        assert (HL : Z.of_nat (length (map (fun b : byte => bv_unsigned b) (firstn (Z.to_nat len) (rest_of (c_pl cx) nb)))) <= len)
          by (rewrite length_map, length_firstn; lia);
        apply (garr8_keep W W mem3 memB fr _); [intros j Hj; apply KM; [lia | unfold obwin; lia] | exact F3] ]
    | apply (KF _ _ HSg); rewrite ?length_map, ?HSgl, OSe; cbn; lia
    | apply (KA _ 8%nat _); [lia | cbn; lia | assumption]
    | apply (KA _ 8%nat _); [lia | cbn; lia | assumption]
    | apply (KA _ 8%nat _); [lia | cbn; lia | assumption]
    | apply (KA _ 8%nat _); [lia | cbn; lia | assumption]
    | apply (KF _ _ HT); rewrite ?length_map, ?HTl, OTe; cbn; lia ]
  | split; [exact HTl0|]; split; [exact HTok0|]; split; [exact Hfind|]; split; [exact Hain|]; split; [exact How|];
    split; [exact HOM|]; split;
    [ unfold ob_sp24; repeat split; (apply (KA _ 8%nat _); [lia | cbn; lia | assumption])
    | unfold ob_r24;
      split; [rewrite HvB; apply (proj2 Hcmp); intros i0 Hi0;
              rewrite (KX (d_obj cx OT + 48 * ai + i0)) by (rewrite OTe; unfold obwin; lia);
              rewrite (KX (d_obj cx OS + i0)) by (rewrite OSe; unfold obwin; lia); exact (MACEQ i0 Hi0)|];
      split; [transitivity (getr (ms_regs msX) 19%bv); [exact (HPB 19 ltac:(unfold acallee_saved; lia)) | rewrite RG19, V65; unfold slot_known.want_role, w64; reflexivity]|];
      split; [transitivity (getr (ms_regs msX) 21%bv); [exact (HPB 21 ltac:(unfold acallee_saved; lia)) | rewrite RG21, V69; reflexivity]|];
      split; [transitivity (getr (ms_regs msX) 22%bv); [exact (HPB 22 ltac:(unfold acallee_saved; lia)) | exact RG22]|];
      split; [transitivity (getr (ms_regs msX) 23%bv); [exact (HPB 23 ltac:(unfold acallee_saved; lia)) | rewrite RG23, V70; reflexivity]|];
      split; [transitivity (getr (ms_regs msX) 24%bv); [exact (HPB 24 ltac:(unfold acallee_saved; lia)) | rewrite RG24, V66; reflexivity]|];
      split; [transitivity (getr (ms_regs msX) 26%bv); [exact (HPB 26 ltac:(unfold acallee_saved; lia)) | rewrite RG26, V68; reflexivity]|];
      transitivity (getr (ms_regs msX) 27%bv); [exact (HPB 27 ltac:(unfold acallee_saved; lia)) | rewrite RG27, V67; reflexivity] ] ]
end.
Qed.
End h.
End f.
End d.
