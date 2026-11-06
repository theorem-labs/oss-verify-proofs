(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 211 of its 238 lines of code are new or changed and 1251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3AgeShort.v; 721 of its 767 lines of code are new or changed and 192 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop YE00 YC5d.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame YC81.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC45.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoArm3 DiscoArm3AgeSt DiscoArm3AgeKit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv disco_table_c reac_disco_table_age_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require
reac_disco_table_json_c slot_ser_defs slot_ser_pure disco_json_lemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition res_ro (r : YP09.region) : YP09.region :=
  YP09.mkRegion (YP09.r_base r) (YP09.r_lo r) (YP09.r_hi r) 0 0 (YP09.r_chunks r).

Lemma res_submem : forall rs, submem (map res_ro rs) rs.
Proof.
  induction rs as [|r rs IH]; cbn [map]; [constructor|].
  apply submem_keep; [|exact IH].
  unfold subregion, res_ro. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. intros c Hc. exact Hc.
Qed.

Lemma res_nowin : forall rs, forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) (map res_ro rs) = true.
Proof. induction rs as [|r rs IH]; [reflexivity|]. cbn [map forallb]. rewrite IH. reflexivity. Qed.

Lemma res_cap : forall op, 2 <= a3_cap op <= 1280.
Proof.
  intros op. unfold a3_cap, slot_ser_defs.ser_cap, slot_ser_defs.ser_k.
  replace (Z.land (Z.shiftr op 2) 31) with (Z.shiftr op 2 mod 32)
    by (symmetry; exact (Z.land_ones (Z.shiftr op 2) 5 ltac:(lia))).
  pose proof (Z.mod_pos_bound (Z.shiftr op 2) 32 ltac:(lia)) as Hb.
  destruct (Z.eqb_spec (Z.shiftr op 2 mod 32) 0); lia.
Qed.

Lemma res_text : forall T now, length T = 400%nat -> disco_table_c.table_ok T -> 0 <= now < 2 ^ 64 ->
  ~ In 0 (a3_text T now) /\ nth 0 (a3_text T now) 0 = 91 /\
  nth (length (a3_text T now) - 1) (a3_text T now) 0 = 93 /\ 2 <= a3_r T now <= 969.
Proof.
  intros T now HL HT Hn. destruct (slot_ser_pure.ser_tj_ok T HL HT) as (H1 & H2).
  unfold a3_r, a3_text, reac_disco_table_json_c.tj_text.
  destruct (disco_json_lemmas.F1_1_text_shape _ _ now slot_ser_pure.ser_tok_ok H1 H2 Hn) as (A & B & C & D).
  pose proof (disco_json_lemmas.C7_text_bound _ _ now slot_ser_pure.ser_tok_ok H1 H2 Hn) as E.
  split; [exact A|]. split; [exact B|]. split; [exact C|]. lia.
Qed.

Lemma res_leb : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
  intros v Hv. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
  rewrite (Z.mod_small v 256) by exact Hv. rewrite (Z.mod_small v 256) by exact Hv. reflexivity.
Qed.

Lemma res_rd1 : forall segs (m : word -> option byte) a s,
  option_map (fun b : byte => bv_unsigned b) (mbyte segs m a) = Some s -> val_mem segs m a 1 s /\ 0 <= s < 256.
Proof.
  intros segs m a s H. destruct (mbyte segs m a) as [b|] eqn:Hb; [|discriminate H].
  cbn [option_map] in H. injection H as <-.
  pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  split; [|exact Hr].
  intros kk Hk. assert (kk = 0%nat) by lia. subst kk. rewrite Z.add_0_r, Hb. f_equal.
  rewrite res_leb by exact Hr.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_small by exact Hr. reflexivity.
Qed.

Lemma res_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  base_val E (Some n) = v /\ sv_denot E (SOff n 0) = Z_to_bv 64 v /\ U E (SOff n 0) = v.
Proof.
  intros E n v H Hv. split; [|split].
  - cbn [base_val]. rewrite H. apply unsigned_lit_small. exact Hv.
  - cbn [sv_denot]. rewrite H, unsigned_lit_small, Z.add_0_r by exact Hv. reflexivity.
  - apply U_atom; assumption.
Qed.

Lemma res_lt : forall E a b, 0 <= U E a < 2 ^ 63 -> 0 <= U E b < 2 ^ 63 -> U E a < U E b ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = true.
Proof.
  intros E a b Ha Hb Hab. cbn [branch_taken]. rewrite bv_lts_signed. unfold U in *.
  rewrite !signed_of_small by (unfold half64; lia). apply Z.ltb_lt. exact Hab.
Qed.

Lemma res_sdecl : forall E (p b s : nat) (pv c Bv : Z),
  ew E p = Z_to_bv 64 pv -> 0 <= pv < 2 ^ 64 -> 0 <= pv + c < 2 ^ 64 ->
  ew E b = Z_to_bv 64 Bv -> 0 <= Bv < 2 ^ 64 -> ew E s = Z_to_bv 64 (Bv + (pv + c) / 8) ->
  0 <= Bv + (pv + c) / 8 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff p c) (SLit 3)) (SOff b 0)) = sv_denot E (SOff s 0).
Proof.
  intros E p b s pv c Bv Hp Hpv Hpc Hb HB Hs Hsv. apply U_inj.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, !U_SOff, Hp, Hb, Hs, !Z.add_0_r.
  rewrite !unsigned_lit_small by lia.
  rewrite (zcanon_id (pv + c)) by (unfold M64; lia). rewrite (zcanon_id Bv) by (unfold M64; lia).
  rewrite (zcanon_id (Bv + (pv + c) / 8)) by (unfold M64; lia).
  pose proof (Z.div_pos (pv + c) 8 ltac:(lia) ltac:(lia)).
  rewrite Z.add_comm. apply zcanon_id. unfold M64. lia.
Qed.

Definition res_xr : smem :=
  [YP09.mkRegion (Some 563%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
   YP09.mkRegion (Some 564%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 565 0))]].
Definition res_fa : list (nat * afact) :=
  [(541%nat, mkAF 2 1279 0); (550%nat, mkAF 3 1280 0); (565%nat, mkAF 0 7 0)].
Definition res_cs (s : Z) : list acond :=
  mkAC BC_LTU (SOff 541 0) (SOff 550 0) ::
  (if s =? 0 then [mkAC BC_EQ (SOff 565 0) (SLit 0)]
   else [mkAC BC_NE (SOff 565 0) (SLit 0); mkAC BC_LT (SAlu ALU_AND (SOff 563 0) (SLit 7)) (SOff 565 0)]).
Definition res_fx : list (nat * afact) := [(550%nat, mkAF 2 1279 0)].
Definition res_cx : list acond := [mkAC BC_EQ (SOff 541 0) (SLit 18446744073709551615)].

Definition brk_x1 : smem :=
  [YP09.mkRegion (Some 557%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 91))];
   YP09.mkRegion (Some 550%nat) (-1) 0 0 0 [YP09.mkChunk (-1) (CVal 1 (SLit 93))];
   YP09.mkRegion (Some 563%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 564 0))]].
Definition brk_f1 : list (nat * afact) := [(564%nat, mkAF 0 7 0)].
Definition brk_c1 (s : Z) : list acond :=
  mkAC BC_EQ (SOff 541 0) (SOff 553 0) ::
  (if s =? 0 then [mkAC BC_EQ (SOff 564 0) (SLit 0)]
   else [mkAC BC_NE (SOff 564 0) (SLit 0); mkAC BC_LT (SAlu ALU_AND (SOff 557 0) (SLit 7)) (SOff 564 0);
         mkAC BC_LT (SAlu ALU_AND (SOff 550 (-1)) (SLit 7)) (SOff 564 0)]).
Definition brk_x2 : smem :=
  [YP09.mkRegion (Some 557%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 91))];
   YP09.mkRegion (Some 550%nat) (-1) 0 0 0 [YP09.mkChunk (-1) (CVal 1 (SLit 93))];
   YP09.mkRegion (Some 563%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
   YP09.mkRegion (Some 564%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 565 0))]].
Definition brk_f2 : list (nat * afact) := [(565%nat, mkAF 0 7 0)].
Definition brk_c2 (s : Z) : list acond :=
  mkAC BC_EQ (SOff 541 0) (SOff 553 0) ::
  (if s =? 0 then [mkAC BC_EQ (SOff 565 0) (SLit 0)]
   else [mkAC BC_NE (SOff 565 0) (SLit 0); mkAC BC_LT (SAlu ALU_AND (SOff 550 (-1)) (SLit 7)) (SOff 565 0)]).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma res_drL : forall B cx (regs regs' : bvmap 5 word),
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 20 = getr regs 20 -> getr regs' 25 = getr regs 25 -> d_rL B cx regs -> d_rL B cx regs'.
Proof.
  intros B cx regs regs' E2 E3 E4 E8 E9 E18 E20 E25 HL. unfold d_rL, spZ in *.
  rewrite E2, E3, E4, E8, E9, E18, E20, E25. exact HL.
Qed.

Lemma res_regeq : forall (fq : YK11.FPState) E ss ms ss' ms' (H H' : word -> bool) (r r' : bv 5),
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict H ms) -> st_ok_pi (fx := fq) SEGS VAL E ss' (restrict H' ms') ->
  sr_get (ss_regs ss') r' = sr_get (ss_regs ss) r -> getr (ms_regs ms') r' = getr (ms_regs ms) r.
Proof.
  intros fq E ss ms ss' ms' H H' r r' HS HS' Hr.
  rewrite (st_ok_pi_restrict_reg H' E ss' ms' r' HS'), (st_ok_pi_restrict_reg H E ss ms r HS), Hr. reflexivity.
Qed.

Lemma res_regv : forall (fq : YK11.FPState) E ss ms (H : word -> bool) (r : bv 5) n v,
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 ->
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> getr (ms_regs ms) r = Z_to_bv 64 v.
Proof.
  intros fq E ss ms H r n v HS Hr Hn Hv. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hr.
  exact (proj1 (proj2 (res_atom E n v Hn Hv))).
Qed.

Lemma res_rok : forall E m (n : nat) lo p v e, base_val E (Some n) = p -> 0 <= p + lo -> p + lo + 1 <= 2 ^ 64 ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 256 -> val_mem SEGS m (p + lo) 1 v ->
  region_ok SEGS E m (YP09.mkRegion (Some n) lo (lo + 1) 0 0 [YP09.mkChunk lo (CVal 1 e)]).
Proof.
  intros E m n lo p v e Hp H0 H1 He Hv Hm. unfold region_ok. cbv zeta.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite Hp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E m p lo 1%N e v); [exact He | cbn; lia | cbn; lia | exact Hm].
Qed.

Lemma res_vm : forall (W : world SEGS) m m' a len v,
  (forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  0 <= a -> a + Z.of_nat len <= 2 ^ 64 -> val_mem SEGS (rd W m) a len v -> val_mem SEGS (rd W m') a len v.
Proof.
  intros W m m' a len v HK Ha Hl Hv.
  apply (a3_val_mem_keep W m m' 0 0 a len v); [intros x Hx _; exact (HK x Hx) | exact Ha | exact Hl | intros; lia | exact Hv].
Qed.

Lemma res_g8 : forall (W : world SEGS) m m' a l,
  (forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 -> garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W m') a l.
Proof.
  intros W m m' a l HK Ha Hl Hg.
  apply (a3_garr8_keep W m m' 0 0 a l); [intros x Hx _; exact (HK x Hx) | exact Ha | exact Hl | intros; lia | exact Hg].
Qed.

Lemma res_sp0 : forall cx i now (W : world SEGS) m m', 0 <= d_A cx -> d_A cx + 472 <= 2 ^ 64 ->
  (forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  d_sp0 cx i now W m -> d_sp0 cx i now W m'.
Proof.
  intros cx i now W m m' H0 H1 HK (A & B').
  split; (apply (res_vm W m m'); [exact HK | lia | cbn; lia | assumption]).
Qed.

Lemma res_sp1 : forall cx i n now (W : world SEGS) m m', 0 <= d_A cx -> d_A cx + 472 <= 2 ^ 64 ->
  (forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  d_sp1 cx i n now W m -> d_sp1 cx i n now W m'.
Proof.
  intros cx i n now W m m' H0 H1 HK (A & B' & C).
  split; [exact (res_sp0 cx i now W m m' H0 H1 HK A)|].
  split; (apply (res_vm W m m'); [exact HK | lia | cbn; lia | assumption]).
Qed.

Lemma res_tab : forall cx now T0 T1 (W : world SEGS) m m', 0 <= d_FB cx -> d_FB cx + 4096 <= 2 ^ 64 ->
  (forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  a3_tab cx now T0 T1 W m -> a3_tab cx now T0 T1 W m'.
Proof.
  intros cx now T0 T1 W m m' H0 H1 HK (A & G). split; [exact A|].
  pose proof A as (rem & _ & HL & _). unfold d_obj, dobj_off.
  apply (res_g8 W m m'); [exact HK | lia | rewrite length_map, HL; cbn; lia | exact G].
Qed.

Lemma res_buf : forall op T1 now buf (W : world SEGS) m m', 0 <= buf -> buf + a3_cap op <= 2 ^ 64 ->
  (forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  a3_buf op T1 now buf W m -> a3_buf op T1 now buf W m'.
Proof.
  intros op T1 now buf W m m' H0 H1 HK (Hr & G). split; [exact Hr|].
  apply (res_g8 W m m'); [exact HK | lia | | exact G].
  rewrite length_app. cbn [length]. unfold a3_r, a3_cap in *. lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBRT : d_body_rt_stmt B.

Lemma res_kx : forall cx ly3 S3 W mem3 md3 k E vals r a b,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k -> d_E cx E ->
  extent_of_region (d_env cx E vals) r = (a, b) ->
  ((4096 <= a /\ a <= b /\ b <= alloc_ceiling /\ in_app a (b - a) /\ off_img a (b - a) /\
    (b <= d_FB cx \/ d_FB cx + 4096 <= a)) \/
   (exists p, a = SHADOW_OFF + p / 8 /\ b = a + 1 /\ 4096 <= p /\ p + 1 <= alloc_ceiling /\
    (p + 1 <= d_FB cx \/ d_FB cx + 4096 <= p))) ->
  all_disjoint (d_env cx E vals) r (d_kregions dsh_loop [] []).
Proof.
  intros cx ly3 S3 W mem3 md3 k E vals r a b HC HE Hext Hz.
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
    as (Hal16 & HSlo & HShi & HFB0 & HFc & HFia & HFo & HFal & _).
  pose proof asan_consts as (Hac & _).
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
  destruct (d_E_env cx E vals HE) as (EE & E32 & HEI & E60 & EF & ESH).
  set (E' := d_env cx E vals) in *.
  pose proof (pa_obj_img 1 ltac:(vm_compute; lia)) as HO1. pose proof (pa_obj_img 66 ltac:(vm_compute; lia)) as HO66.
  pose proof (pa_val_range (A_OBJ 1)) as HV1. pose proof (pa_val_range (A_OBJ 66)) as HV66.
  assert (Hd0 : 0 <= d_FB cx / 8) by (apply Z.div_pos; lia).
  assert (U2 : base_val E' (Some AT_STK) = d_S cx).
  { cbn [base_val]. unfold AT_STK. rewrite (EE 2%nat 2%bv eq_refl). reflexivity. }
  assert (U60 : base_val E' (Some AT_A) = d_A cx).
  { cbn [base_val]. rewrite E60. apply unsigned_lit_small. unfold MFRAME, LLVMF_STK in *. lia. }
  assert (U516 : base_val E' (Some AT_F) = d_FB cx).
  { cbn [base_val]. rewrite EF. apply unsigned_lit_small. lia. }
  assert (U529 : base_val E' (Some AT_SH) = shadow_addr (d_FB cx)).
  { cbn [base_val]. rewrite ESH. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF.
    assert (d_FB cx / 8 <= d_FB cx) by (apply Z.div_le_upper_bound; lia). lia. }
  assert (EA : forall n, (A_TEXT <= n < A_LIM)%nat -> base_val E' (Some n) = VAL n).
  { intros n Hn. cbn [base_val]. rewrite (img_env_atomP E' n HEI Hn). apply unsigned_lit_small. apply pa_val_range. }
  assert (UG1 : base_val E' (Some (A_OBJ 1)) = VAL (A_OBJ 1)) by (apply EA; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (UG66 : base_val E' (Some (A_OBJ 66)) = VAL (A_OBJ 66)) by (apply EA; unfold A_OBJ, A_TEXT, A_LIM; lia).
  apply all_disjoint_of_extents. rewrite Hext.
  unfold d_kregions, fshadow_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U2, U60, U516, U529, UG1, UG66.
  change (fs_frame_bytes DFRAME_CLASS) with 4096. change (4096 / 8) with 512.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold shadow_addr, in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, MFRAME, LLVMF_STK,
    IMG_LO, IMG_TOP in *.
  destruct Hz as [Hz | (p & -> & -> & Hz)]; repeat split; lia.
Qed.

Ltac res_awr := let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; exfalso; exact (a3_nowin _ _ a (res_nowin _) Ha).

Ltac res_run_to HS HJ HEI stop :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_run_toN_pi disco_tpi 200%N stop ss) in
    lazymatch r with
    | (?ss', ?st) =>
      eapply (SRr_run_to_pi_AJ B LAWS W 200%N stop E ss ss' st ms);
      [ exact HEI | exact HS | vm_compute; reflexivity | exact I | exact HJ | res_awr | ]
    end
  end.

Ltac res_run_call HS HJ HEI :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_runN_pi disco_tpi 200%N ss) in
    lazymatch r with
    | (?ss', PRS_call ?s) =>
      eapply (SRr_run_pi_AJ_call B LAWS W 200%N E ss ss' s ms);
      [ exact HEI | exact HS | vm_compute; reflexivity | exact HJ | res_awr | cbn [setpc] ]
    end
  end.

Ltac res_same HS0 HSf r := apply (res_regeq _ _ _ _ _ _ _ _ r r HS0 HSf); vm_compute; reflexivity.

Ltac res_drl HS0 HSf HrL :=
  eapply res_drL; [res_same HS0 HSf (2%bv : bv 5) | res_same HS0 HSf (3%bv : bv 5) | res_same HS0 HSf (4%bv : bv 5) | res_same HS0 HSf (8%bv : bv 5)
    | res_same HS0 HSf (9%bv : bv 5) | res_same HS0 HSf (18%bv : bv 5) | res_same HS0 HSf (20%bv : bv 5) | res_same HS0 HSf (25%bv : bv 5) | exact HrL].

Ltac res_val HSf r n En :=
  eapply (res_regv _ _ _ _ _ r n _ HSf); [vm_compute; reflexivity | exact En | lia].

Theorem e_res : e_res_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros cx h i n now op W0 c0 T0 T1 buf r W c (HF0 & HA).
  unfold a3_st, d_at in HA.
  destruct HA as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & HB & HJ & HFR & Hk & Hnev & Hmo & Hacc &
    Hi & Hn & Hnow & HrL & (R10 & R19 & R26) & (Hbuf & Hsp1 & Htab & Hjres & Htxt) & Hsp0 & Hbody).
  assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HB (conj HJ HFR)).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
    as (Hal16 & HSlo & HShi & HFB0 & HFc & HFia & HFo & HFal & _ & _ & _ & HAR & Hfin & Efa & Efl).
  pose proof asan_consts as (Hac & _).
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
  pose proof (res_cap op) as Hcap.
  assert (Hcapd : a3_cap op = slot_ser_defs.ser_cap op) by reflexivity.
  pose proof Htab as ((rem & _ & Hagp) & _).
  pose proof Hagp as (HL1 & _ & _ & _ & _ & _ & HTok & _).
  destruct (res_text T1 now HL1 HTok Hnow) as (Hno0 & Hfst & Hlst & Hrb).
  pose proof Hbody as (TT & GG & LL & HH & _ & _ & _ & (Hperm & _) & _).
  assert (Hin : In (buf, Z.max (a3_cap op) 1) (ablocks B ly3 S3)).
  { eapply Permutation_in; [symmetry; exact Hperm|]. apply in_or_app. left. left. reflexivity. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbia & _).
  pose proof (blk_off_imgP B _ _ _ _ _ _ _ HAR Hin) as Hbimg.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hin Hfin) as Hbfr. rewrite Efa in Hbfr.
  assert (Hreq : req_size (Z.max (a3_cap op) 1) = a3_cap op)
    by (unfold req_size; destruct (Z.eqb_spec (Z.max (a3_cap op) 1) 0); lia).
  rewrite Hreq in Hbceil, Hbia, Hbimg, Hbfr.
  unfold zdisjoint in Hbfr. cbn [fst snd] in Hbfr. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hbfr.
  unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbia, Hbimg.
  assert (HKA : 0 <= d_A cx /\ d_A cx + 472 <= 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
  unfold cfg_at.
  destruct Hjres as [(-> & Hcj) | (Hr & Hc3 & Hrc)].
  - assert (Hc1280 : a3_cap op <= 1279) by lia.
    assert (HX : forall E, d_E cx E ->
      atoms_ok (d_env cx E (a3_vals regs [])) res_fx /\ conds_ok (d_env cx E (a3_vals regs [])) res_cx /\
      Forall (YP09.chunk_ok SEGS (d_env cx E (a3_vals regs [])) (rd W mem3) (d_A cx)) [] /\
      Forall (YP09.chunk_ok SEGS (d_env cx E (a3_vals regs [])) (rd W mem3) (d_FB cx)) [] /\
      Forall (region_ok SEGS (d_env cx E (a3_vals regs [])) (rd W mem3)) [] /\
      pairwise_disjoint (d_env cx E (a3_vals regs [])) [] /\
      Forall (fun r => all_disjoint (d_env cx E (a3_vals regs [])) r (d_kregions dsh_loop [] [])) []).
    { intros E HE. split; [|split; [|repeat split; constructor]].
      - cbn [atoms_ok res_fx]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite (a3_env_reg cx E regs [] 19%bv 550 eq_refl), R19. unfold w64.
        rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
      - cbn [conds_ok res_cx]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
        rewrite branch_eq_U, U_SOff, (a3_env_reg cx E regs [] 10%bv 541 eq_refl), R10. vm_compute. reflexivity. }
    destruct (a3_seat B MT XM_LIB RLO RHI tfib_K LAWS TL DSEAT DFACTS fq cx P_TJ_RA h n (a3_xb buf op) dsh_loop
      ly3 S3 W regs mem3 md3 k [] [] [] [] res_fx res_cx HC HrL Hbody HX ltac:(vm_compute; reflexivity))
      as (E & HE & HS0).
    pose proof (a3_env_img cx E (a3_vals regs []) HE) as HEI.
    pose proof (st_ok_pi_submem _ _ _ _ HS0 (res_submem _) ltac:(vm_compute; reflexivity)) as HS1.
    clear HS0.
    res_run_to HS1 HJ HEI R14X_OFF.
    intros ms' mat HSf HJ' HF HFr HG. cbn [ms_mem YK11.mkst] in HF, HFr, HG, HJ'.
    assert (HK0 : forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms') x = aview SEGS (w_H W) mem3 x).
    { intros x Hx. apply (a3_kept_frame _ _ (w_H W) mem3 (ms_mem ms') 0 0 HFr); [res_awr | exact Hx | lia]. }
    apply SRr_ret. right. split; [exact HF0|].
    apply (a3_land_rt B MT XM_LIB RLO RHI tfib_K LAWS FFL DLAND DBRT fq cx R14X_OFF (EV_HEAD i + 1) h i n n now
      (a3_xb buf op) (fun regs => getr regs 26 = w64 buf) (fun W m => d_sp1 cx i n now W m /\ a3_tab cx now T0 T1 W m)
      W ly3 S3 mem3 _ k acc _ _ ms' (d_S cx) (d_S cx) Hfrm0 HB HJ' HFR Hk Hnev Hmo Hacc Hi ltac:(lia) Hnow Hbody HSf
      eq_refl eq_refl (d_E_env cx E _ HE) (d_env_fl cx E _) ltac:(vm_compute; reflexivity)
      ltac:(unfold LLVMF_STK; lia) ltac:(lia) ltac:(intros x Hx _; exact (HK0 x Hx))
      ltac:(intros; eapply (a3_present_grows _ _ _ HG); eassumption) ltac:(intros; lia)).
    + res_drl HS1 HSf HrL.
    + cbn beta. rewrite <- R26. res_same HS1 HSf (26%bv : bv 5).
    + cbn beta. split.
      * exact (res_sp1 cx i n now W mem3 (ms_mem ms') (proj1 HKA) (proj2 HKA) HK0 Hsp1).
      * exact (res_tab cx now T0 T1 W mem3 (ms_mem ms') ltac:(lia) ltac:(lia) HK0 Htab).
    + exact (res_sp0 cx i now W mem3 (ms_mem ms') (proj1 HKA) (proj2 HKA) HK0 Hsp0).
  - pose proof (Htxt Hr) as Hg.
    assert (Hlen : Z.of_nat (length (a3_text T1 now)) = r) by (rewrite Hr; reflexivity).
    assert (Hz : val_mem SEGS (rd W mem3) (buf + r) 1 0).
    { destruct (Hg (length (a3_text T1 now)) ltac:(rewrite length_app; cbn [length]; lia)) as (Hv & _).
      rewrite app_nth2, Nat.sub_diag in Hv by lia. cbn [nth] in Hv. rewrite Hlen in Hv. exact Hv. }
    pose proof (obl_of_block SEGS B LAWS ly3 S3 W mem3 md3 (mkEnv (fun _ => Z_to_bv 64 0) (fun _ => []))
      (SLit SHADOW_OFF) (buf + r) 1 buf (Z.max (a3_cap op) 1) HAR Hin ltac:(vm_compute; reflexivity)
      ltac:(lia) ltac:(rewrite Hreq; lia)) as Hra.
    destruct (Hra (buf + r) ltac:(lia)) as (s & Hs & Hsok).
    clear Hra. unfold shadow_of_addr in Hs. change (U _ (SLit SHADOW_OFF)) with SHADOW_OFF in Hs.
    unfold rd_of in Hs. destruct (res_rd1 _ _ _ _ Hs) as (Hsv & Hsr). clear Hs.
    assert (Hs7 : 0 <= s <= 7) by (unfold saddr_ok in Hsok; lia).
    assert (Hbr : buf + r + 1 <= alloc_ceiling) by lia.
    set (ex := [w64 (buf + r); w64 (SHADOW_OFF + (buf + r) / 8); w64 s]).
    assert (HEX : forall E, d_E cx E ->
      ew (d_env cx E (a3_vals regs ex)) 541 = Z_to_bv 64 r /\ ew (d_env cx E (a3_vals regs ex)) 550 = Z_to_bv 64 (a3_cap op) /\
      ew (d_env cx E (a3_vals regs ex)) 557 = Z_to_bv 64 buf /\
      ew (d_env cx E (a3_vals regs ex)) 563 = Z_to_bv 64 (buf + r) /\
      ew (d_env cx E (a3_vals regs ex)) 564 = Z_to_bv 64 (SHADOW_OFF + (buf + r) / 8) /\
      ew (d_env cx E (a3_vals regs ex)) 565 = Z_to_bv 64 s /\
      ew (d_env cx E (a3_vals regs ex)) 32 = Z_to_bv 64 SHADOW_OFF).
    { intros E HE. split; [rewrite (a3_env_reg cx E regs ex 10%bv 541 eq_refl); exact R10|].
      split; [rewrite (a3_env_reg cx E regs ex 19%bv 550 eq_refl); exact R19|].
      split; [rewrite (a3_env_reg cx E regs ex 26%bv 557 eq_refl); exact R26|].
      split; [exact (d_env_x cx E (a3_vals regs ex) 32 ltac:(vm_compute; lia))|].
      split; [exact (d_env_x cx E (a3_vals regs ex) 33 ltac:(vm_compute; lia))|].
      split; [exact (d_env_x cx E (a3_vals regs ex) 34 ltac:(vm_compute; lia))|].
      rewrite d_env_old by (unfold AT_FL; lia). destruct HE as (_ & E32 & _). exact E32. }
    assert (HX : forall E, d_E cx E ->
      atoms_ok (d_env cx E (a3_vals regs ex)) res_fa /\ conds_ok (d_env cx E (a3_vals regs ex)) (res_cs s) /\
      Forall (YP09.chunk_ok SEGS (d_env cx E (a3_vals regs ex)) (rd W mem3) (d_A cx)) [] /\
      Forall (YP09.chunk_ok SEGS (d_env cx E (a3_vals regs ex)) (rd W mem3) (d_FB cx)) [] /\
      Forall (region_ok SEGS (d_env cx E (a3_vals regs ex)) (rd W mem3)) res_xr /\
      pairwise_disjoint (d_env cx E (a3_vals regs ex)) res_xr /\
      Forall (fun r => all_disjoint (d_env cx E (a3_vals regs ex)) r (d_kregions dsh_loop [] [])) res_xr).
    { intros E HE. destruct (HEX E HE) as (E541 & E550 & E557 & E563 & E564 & E565 & E32).
      set (E' := d_env cx E (a3_vals regs ex)) in *.
      destruct (res_atom E' 541 r E541 ltac:(lia)) as (_ & _ & U541).
      destruct (res_atom E' 550 (a3_cap op) E550 ltac:(lia)) as (_ & _ & U550).
      destruct (res_atom E' 563 (buf + r) E563 ltac:(lia)) as (B563 & _ & U563).
      destruct (res_atom E' 564 (SHADOW_OFF + (buf + r) / 8) E564
        ltac:(unfold SHADOW_OFF; lia))
        as (B564 & _ & U564).
      destruct (res_atom E' 565 s E565 ltac:(lia)) as (_ & D565 & U565).
      split; [|split; [|split; [constructor|split; [constructor|]]]].
      - cbn [atoms_ok res_fa]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E541, E550, E565. rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
        repeat split; lia.
      - unfold res_cs. destruct (Z.eqb_spec s 0) as [Hs0|Hs0]; cbn [conds_ok]; unfold acond_ok; cbn [ac_c ac_a ac_b].
        + split; [rewrite branch_ltu_U, U541, U550; apply Z.ltb_lt; lia|].
          split; [|exact I]. rewrite branch_eq_U, U565, U_SLit. apply Z.eqb_eq. rewrite Hs0. reflexivity.
        + split; [rewrite branch_ltu_U, U541, U550; apply Z.ltb_lt; lia|].
          split; [rewrite branch_ne_U, U565, U_SLit; apply negb_true_iff, Z.eqb_neq; exact Hs0|].
          split; [|exact I].
          assert (UA : U E' (SAlu ALU_AND (SOff 563 0) (SLit 7)) = (buf + r) mod 8).
          { rewrite U_and_lit, U563 by lia. exact (Z.land_ones (buf + r) 3 ltac:(lia)). }
          apply res_lt; rewrite ?UA, ?U565; [pose proof (Z.mod_pos_bound (buf + r) 8 ltac:(lia)); lia | lia |].
          unfold saddr_ok in Hsok. lia.
      - split; [|split].
        + constructor; [|constructor; [|constructor]].
          * apply (res_rok E' (rd W mem3) 563 0 (buf + r) 0 (SLit 0)); [exact B563 | lia | lia | reflexivity | lia |].
            rewrite Z.add_0_r. exact Hz.
          * apply (res_rok E' (rd W mem3) 564 0 (SHADOW_OFF + (buf + r) / 8) s (SOff 565 0));
              [exact B564 | | | exact D565 | lia | rewrite Z.add_0_r; exact Hsv];
              unfold SHADOW_OFF; pose proof (Z.div_pos (buf + r) 8 ltac:(lia) ltac:(lia));
              pose proof (Z.div_le_upper_bound (buf + r) 8 (buf + r) ltac:(lia) ltac:(lia)); lia.
        + apply pairwise_disjoint_of_extents. unfold res_xr, extent_of_region.
          cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B563, B564.
          cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
          unfold SHADOW_OFF. repeat split; lia.
        + constructor; [|constructor; [|constructor]].
          * apply (res_kx cx ly3 S3 W mem3 md3 k E (a3_vals regs ex) _ (buf + r) (buf + r + 1) HC HE).
            -- unfold extent_of_region. fold E'. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B563. f_equal; lia.
            -- left. unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. repeat split; lia.
          * apply (res_kx cx ly3 S3 W mem3 md3 k E (a3_vals regs ex) _ (SHADOW_OFF + (buf + r) / 8)
              (SHADOW_OFF + (buf + r) / 8 + 1) HC HE).
            -- unfold extent_of_region. fold E'. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B564. f_equal; lia.
            -- right. exists (buf + r). repeat split; lia. }
    destruct (a3_seat B MT XM_LIB RLO RHI tfib_K LAWS TL DSEAT DFACTS fq cx P_TJ_RA h n (a3_xb buf op) dsh_loop
      ly3 S3 W regs mem3 md3 k ex [] [] res_xr res_fa (res_cs s) HC HrL Hbody HX ltac:(vm_compute; reflexivity))
      as (E & HE & HS0).
    destruct (HEX E HE) as (E541 & E550 & E557 & E563 & E564 & E565 & E32).
    pose proof (a3_env_img cx E (a3_vals regs ex) HE) as HEI.
    set (E' := d_env cx E (a3_vals regs ex)) in *.
    destruct (res_atom E' 541 r E541 ltac:(lia)) as (_ & _ & U541).
    destruct (res_atom E' 557 buf E557 ltac:(lia)) as (_ & _ & U557).
    destruct (res_atom E' 563 (buf + r) E563 ltac:(lia)) as (_ & _ & U563).
    pose proof (st_ok_pi_add_alias _ _ _ (SAlu ALU_ADD (SOff 557 0) (SOff 541 0)) (SOff 563 0) HS0
      ltac:(apply U_inj; rewrite U_SAlu; cbn [zalu_raw]; rewrite U557, U541, U563; apply zcanon_id; unfold M64; lia))
      as HS1. clear HS0.
    pose proof (st_ok_pi_add_alias _ _ _ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 563 0) (SLit 3)) (SOff 32 0)) (SOff 564 0) HS1
      (shadow_decl_ok E' 563 32 564 (buf + r) SHADOW_OFF E563 ltac:(lia) E32 E564)) as HS2. clear HS1.
    pose proof (st_ok_pi_submem _ _ _ _ HS2 (res_submem _) ltac:(vm_compute; reflexivity)) as HS3. clear HS2.
    unfold res_cs in HS3.
    destruct (Z.eqb_spec s 0) as [Hs0|Hs0].
    all: res_run_call HS3 HJ HEI.
    all: intros ms' mat HSf HJ' HF HFr HG; cbn [ms_mem YK11.mkst] in HF, HFr, HG, HJ'.
    all: pose proof (a3_pcall_pi fq E' _ _ _ HSf) as HSp; clear HSf.
    all: assert (HK0 : forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms') x = aview SEGS (w_H W) mem3 x)
      by (intros x Hx; apply (a3_kept_frame _ _ (w_H W) mem3 (ms_mem ms') 0 0 HFr); [res_awr | exact Hx | lia]).
    all: apply SRr_ret; left; split; [exact HF0|].
    all: apply (a3_land_rt B MT XM_LIB RLO RHI tfib_K LAWS FFL DLAND DBRT fq cx
      (SIGMA DS___interceptor_trampoline_strlen - BASE) (EV_HEAD i + 1) h i n n now (a3_xb buf op)
      (fun regs => getr regs 1 = w64 (BASE + P_SL_RA) /\ getr regs 10 = w64 buf /\
         getr regs 19 = w64 (buf + a3_r T1 now) /\ getr regs 22 = w64 (a3_r T1 now) /\ getr regs 26 = w64 buf)
      (fun W m => 4096 <= buf /\ d_sp1 cx i n now W m /\ a3_tab cx now T0 T1 W m /\ a3_buf op T1 now buf W m)
      W ly3 S3 mem3 _ k acc _ _ ms' (d_S cx) (d_S cx) Hfrm0 HB HJ' HFR Hk Hnev Hmo Hacc Hi ltac:(lia) Hnow Hbody HSp
      eq_refl eq_refl (d_E_env cx E _ HE) (d_env_fl cx E _) ltac:(vm_compute; reflexivity)
      ltac:(unfold LLVMF_STK; lia) ltac:(lia) ltac:(intros x Hx _; exact (HK0 x Hx))
      ltac:(intros; eapply (a3_present_grows _ _ _ HG); eassumption) ltac:(intros; lia));
      [ res_drl HS3 HSp HrL
      | cbn beta; rewrite <- Hr; unfold w64;
        split; [rewrite (st_ok_pi_restrict_reg _ _ _ _ 1%bv HSp);
          replace (sr_get (ss_regs _) 1%bv) with (SOff A_TEXT 2844) by (vm_compute; reflexivity);
          exact (codeptr_val E' 2844 HEI)|];
        split; [res_val HSp (10%bv : bv 5) 557%nat E557|];
        split; [res_val HSp (19%bv : bv 5) 563%nat E563|];
        split; [res_val HSp (22%bv : bv 5) 541%nat E541|];
        res_val HSp (26%bv : bv 5) 557%nat E557
      | cbn beta; split; [exact Hbuf|];
        split; [exact (res_sp1 cx i n now W mem3 (ms_mem ms') (proj1 HKA) (proj2 HKA) HK0 Hsp1)|];
        split; [exact (res_tab cx now T0 T1 W mem3 (ms_mem ms') ltac:(lia) ltac:(lia) HK0 Htab)|];
        apply (res_buf op T1 now buf W mem3 (ms_mem ms') ltac:(lia) ltac:(lia) HK0);
        split; [clear - Hr Hrb Hrc; unfold a3_cap in Hrc; lia | exact Hg]
      | exact (res_sp0 cx i now W mem3 (ms_mem ms') (proj1 HKA) (proj2 HKA) HK0 Hsp0) ].
Qed.

Theorem e_brk : e_brk_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros cx h i n now op W0 c0 T0 T1 buf W c (HF0 & HA).
  unfold a3_st, d_at in HA.
  destruct HA as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm0 & HB & HJ & HFR & Hk & Hnev & Hmo & Hacc &
    Hi & Hn & Hnow & HrL & (R10 & R19 & R22 & R26) & (Hbuf & Hsp1 & Htab & Habuf) & Hsp0 & Hbody).
  assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HB (conj HJ HFR)).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS _ _ _ _ _ _ _ HC)
    as (Hal16 & HSlo & HShi & HFB0 & HFc & HFia & HFo & HFal & _ & _ & _ & HAR & Hfin & Efa & Efl).
  pose proof asan_consts as (Hac & _).
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
  pose proof (res_cap op) as Hcap.
  assert (Hcapd : a3_cap op = slot_ser_defs.ser_cap op) by reflexivity.
  pose proof Htab as ((rem & _ & Hagp) & _).
  pose proof Hagp as (HL1 & _ & _ & _ & _ & _ & HTok & _).
  destruct (res_text T1 now HL1 HTok Hnow) as (Hno0 & Hfst & Hlst & Hrb).
  pose proof Hbody as (TT & GG & LL & HH & _ & _ & _ & (Hperm & _) & _).
  assert (Hin : In (buf, Z.max (a3_cap op) 1) (ablocks B ly3 S3)).
  { eapply Permutation_in; [symmetry; exact Hperm|]. apply in_or_app. left. left. reflexivity. }
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (Hb16 & Hb4096 & Hbceil & Hbia & _).
  pose proof (blk_off_imgP B _ _ _ _ _ _ _ HAR Hin) as Hbimg.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hin Hfin) as Hbfr. rewrite Efa in Hbfr.
  assert (Hreq : req_size (Z.max (a3_cap op) 1) = a3_cap op)
    by (unfold req_size; destruct (Z.eqb_spec (Z.max (a3_cap op) 1) 0); lia).
  rewrite Hreq in Hbceil, Hbia, Hbimg, Hbfr.
  unfold zdisjoint in Hbfr. cbn [fst snd] in Hbfr. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hbfr.
  unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbia, Hbimg.
  assert (HKA : 0 <= d_A cx /\ d_A cx + 472 <= 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
  unfold cfg_at.
  pose proof Habuf as (Hrr & Hg).
  set (r := a3_r T1 now) in *.
  assert (Hlen : Z.of_nat (length (a3_text T1 now)) = r) by reflexivity.
  assert (Hv0 : val_mem SEGS (rd W mem3) (buf + 0) 1 91).
  { destruct (Hg 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as (Hv & _).
    rewrite app_nth1 in Hv by lia. rewrite Hfst in Hv. exact Hv. }
  assert (Hv1 : val_mem SEGS (rd W mem3) (buf + r + -1) 1 93).
  { destruct (Hg (length (a3_text T1 now) - 1)%nat ltac:(rewrite length_app; cbn [length]; lia)) as (Hv & _).
    rewrite app_nth1 in Hv by lia. rewrite Hlst in Hv.
    replace (buf + Z.of_nat (length (a3_text T1 now) - 1)) with (buf + r + -1) in Hv by lia. exact Hv. }
  pose proof (obl_of_block SEGS B LAWS ly3 S3 W mem3 md3 (mkEnv (fun _ => Z_to_bv 64 0) (fun _ => []))
    (SLit SHADOW_OFF) (buf + r - 1) 1 buf (Z.max (a3_cap op) 1) HAR Hin ltac:(vm_compute; reflexivity)
    ltac:(lia) ltac:(rewrite Hreq; lia)) as Hra.
  destruct (Hra (buf + r - 1) ltac:(lia)) as (s & Hs & Hsok).
  clear Hra. unfold shadow_of_addr in Hs. change (U _ (SLit SHADOW_OFF)) with SHADOW_OFF in Hs.
  unfold rd_of in Hs. destruct (res_rd1 _ _ _ _ Hs) as (Hsv & Hsr). clear Hs.
  assert (Hs7 : 0 <= s <= 7) by (unfold saddr_ok in Hsok; lia).
  destruct (Z_le_gt_dec r 8) as [Hr8 | Hr8].
  - assert (Hdv : (buf + r - 1) / 8 = buf / 8) by lia.
    rewrite Hdv in Hsv.
    set (ex := [w64 (SHADOW_OFF + buf / 8); w64 s]).
    assert (HEX : forall E, d_E cx E ->
      ew (d_env cx E (a3_vals regs ex)) 541 = Z_to_bv 64 r /\ ew (d_env cx E (a3_vals regs ex)) 550 = Z_to_bv 64 (buf + r) /\
      ew (d_env cx E (a3_vals regs ex)) 553 = Z_to_bv 64 r /\ ew (d_env cx E (a3_vals regs ex)) 557 = Z_to_bv 64 buf /\
      ew (d_env cx E (a3_vals regs ex)) 563 = Z_to_bv 64 (SHADOW_OFF + buf / 8) /\
      ew (d_env cx E (a3_vals regs ex)) 564 = Z_to_bv 64 s /\
      ew (d_env cx E (a3_vals regs ex)) 32 = Z_to_bv 64 SHADOW_OFF).
    { intros E HE. split; [rewrite (a3_env_reg cx E regs ex 10%bv 541 eq_refl); exact R10|].
      split; [rewrite (a3_env_reg cx E regs ex 19%bv 550 eq_refl); exact R19|].
      split; [rewrite (a3_env_reg cx E regs ex 22%bv 553 eq_refl); exact R22|].
      split; [rewrite (a3_env_reg cx E regs ex 26%bv 557 eq_refl); exact R26|].
      split; [exact (d_env_x cx E (a3_vals regs ex) 32 ltac:(vm_compute; lia))|].
      split; [exact (d_env_x cx E (a3_vals regs ex) 33 ltac:(vm_compute; lia))|].
      rewrite d_env_old by (unfold AT_FL; lia). destruct HE as (_ & E32 & _). exact E32. }
    assert (HX : forall E, d_E cx E ->
      atoms_ok (d_env cx E (a3_vals regs ex)) brk_f1 /\ conds_ok (d_env cx E (a3_vals regs ex)) (brk_c1 s) /\
      Forall (YP09.chunk_ok SEGS (d_env cx E (a3_vals regs ex)) (rd W mem3) (d_A cx)) [] /\
      Forall (YP09.chunk_ok SEGS (d_env cx E (a3_vals regs ex)) (rd W mem3) (d_FB cx)) [] /\
      Forall (region_ok SEGS (d_env cx E (a3_vals regs ex)) (rd W mem3)) brk_x1 /\
      pairwise_disjoint (d_env cx E (a3_vals regs ex)) brk_x1 /\
      Forall (fun r => all_disjoint (d_env cx E (a3_vals regs ex)) r (d_kregions dsh_loop [] [])) brk_x1).
    { intros E HE. destruct (HEX E HE) as (E541 & E550 & E553 & E557 & E563 & E564 & E32).
      set (E' := d_env cx E (a3_vals regs ex)) in *.
      destruct (res_atom E' 541 r E541 ltac:(lia)) as (_ & _ & U541).
      destruct (res_atom E' 550 (buf + r) E550 ltac:(lia)) as (B550 & _ & U550).
      destruct (res_atom E' 553 r E553 ltac:(lia)) as (_ & _ & U553).
      destruct (res_atom E' 557 buf E557 ltac:(lia)) as (B557 & _ & U557).
      destruct (res_atom E' 563 (SHADOW_OFF + buf / 8) E563 ltac:(unfold SHADOW_OFF; lia)) as (B563 & _ & U563).
      destruct (res_atom E' 564 s E564 ltac:(lia)) as (_ & D564 & U564).
      assert (U550m : U E' (SOff 550 (-1)) = buf + r - 1).
      { rewrite U_SOff, E550, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
      split; [|split; [|split; [constructor|split; [constructor|]]]].
      - cbn [atoms_ok brk_f1]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E564. rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
        repeat split; lia.
      - unfold brk_c1. destruct (Z.eqb_spec s 0) as [Hs0|Hs0]; cbn [conds_ok]; unfold acond_ok; cbn [ac_c ac_a ac_b].
        + split; [rewrite branch_eq_U, U541, U553; apply Z.eqb_refl|].
          split; [|exact I]. rewrite branch_eq_U, U564, U_SLit. apply Z.eqb_eq. rewrite Hs0. reflexivity.
        + split; [rewrite branch_eq_U, U541, U553; apply Z.eqb_refl|].
          split; [rewrite branch_ne_U, U564, U_SLit; apply negb_true_iff, Z.eqb_neq; exact Hs0|].
          split.
          * assert (UA : U E' (SAlu ALU_AND (SOff 557 0) (SLit 7)) = buf mod 8).
            { rewrite U_and_lit, U557 by lia. exact (Z.land_ones buf 3 ltac:(lia)). }
            apply res_lt; rewrite ?UA, ?U564; lia.
          * split; [|exact I].
            assert (UA : U E' (SAlu ALU_AND (SOff 550 (-1)) (SLit 7)) = (buf + r - 1) mod 8).
            { rewrite U_and_lit, U550m by lia. exact (Z.land_ones (buf + r - 1) 3 ltac:(lia)). }
            apply res_lt; rewrite ?UA, ?U564; [pose proof (Z.mod_pos_bound (buf + r - 1) 8 ltac:(lia)); lia | lia |].
            unfold saddr_ok in Hsok. lia.
      - split; [|split].
        + constructor; [|constructor; [|constructor; [|constructor]]].
          * apply (res_rok E' (rd W mem3) 557 0 buf 91 (SLit 91)); [exact B557 | lia | lia | reflexivity | lia | exact Hv0].
          * apply (res_rok E' (rd W mem3) 550 (-1) (buf + r) 93 (SLit 93)); [exact B550 | lia | lia | reflexivity | lia | exact Hv1].
          * apply (res_rok E' (rd W mem3) 563 0 (SHADOW_OFF + buf / 8) s (SOff 564 0));
              [exact B563 | unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia | exact D564 | lia | rewrite Z.add_0_r; exact Hsv].
        + apply pairwise_disjoint_of_extents. unfold brk_x1, extent_of_region.
          cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B557, B550, B563.
          cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
          unfold SHADOW_OFF. repeat split; lia.
        + constructor; [|constructor; [|constructor; [|constructor]]].
          * apply (res_kx cx ly3 S3 W mem3 md3 k E (a3_vals regs ex) _ buf (buf + 1) HC HE).
            -- unfold extent_of_region. fold E'. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B557. f_equal; lia.
            -- left. unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. repeat split; lia.
          * apply (res_kx cx ly3 S3 W mem3 md3 k E (a3_vals regs ex) _ (buf + r - 1) (buf + r) HC HE).
            -- unfold extent_of_region. fold E'. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B550. f_equal; lia.
            -- left. unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. repeat split; lia.
          * apply (res_kx cx ly3 S3 W mem3 md3 k E (a3_vals regs ex) _ (SHADOW_OFF + buf / 8)
              (SHADOW_OFF + buf / 8 + 1) HC HE).
            -- unfold extent_of_region. fold E'. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B563. f_equal; lia.
            -- right. exists buf. repeat split; lia. }
    destruct (a3_seat B MT XM_LIB RLO RHI tfib_K LAWS TL DSEAT DFACTS fq cx P_SL_RA h n (a3_xb buf op) dsh_loop
      ly3 S3 W regs mem3 md3 k ex [] [] brk_x1 brk_f1 (brk_c1 s) HC HrL Hbody HX ltac:(vm_compute; reflexivity))
      as (E & HE & HS0).
    destruct (HEX E HE) as (E541 & E550 & E553 & E557 & E563 & E564 & E32).
    pose proof (a3_env_img cx E (a3_vals regs ex) HE) as HEI.
    set (E' := d_env cx E (a3_vals regs ex)) in *.
    pose proof (st_ok_pi_add_alias _ _ _ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 557 0) (SLit 3)) (SOff 32 0)) (SOff 563 0) HS0
      (shadow_decl_ok E' 557 32 563 buf SHADOW_OFF E557 ltac:(lia) E32 E563)) as HS1. clear HS0.
    pose proof (st_ok_pi_add_alias _ _ _ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 550 (-1)) (SLit 3)) (SOff 32 0)) (SOff 563 0) HS1
      (res_sdecl E' 550 32 563 (buf + r) (-1) SHADOW_OFF E550 ltac:(lia) ltac:(lia) E32 ltac:(unfold SHADOW_OFF; lia)
        ltac:(rewrite E563; do 2 f_equal; lia) ltac:(unfold SHADOW_OFF; lia))) as HS2. clear HS1.
    pose proof (st_ok_pi_submem _ _ _ _ HS2 (res_submem _) ltac:(vm_compute; reflexivity)) as HS3. clear HS2.
    unfold brk_c1 in HS3.
    destruct (Z.eqb_spec s 0) as [Hs0|Hs0].
    all: res_run_to HS3 HJ HEI R10_OFF.
    all: intros ms' mat HSf HJ' HF HFr HG; cbn [ms_mem YK11.mkst] in HF, HFr, HG, HJ'.
    all: assert (HK0 : forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms') x = aview SEGS (w_H W) mem3 x)
      by (intros x Hx; apply (a3_kept_frame _ _ (w_H W) mem3 (ms_mem ms') 0 0 HFr); [res_awr | exact Hx | lia]).
    all: apply SRr_ret; split; [exact HF0|].
    all: apply (a3_land_rt B MT XM_LIB RLO RHI tfib_K LAWS FFL DLAND DBRT fq cx R10_OFF (EV_HEAD i + 1) h i n n now
      (a3_xb buf op)
      (fun regs => getr regs 22 = w64 (a3_r T1 now) /\ getr regs 26 = w64 buf)
      (fun W m => d_sp1 cx i n now W m /\ a3_tab cx now T0 T1 W m /\ a3_buf op T1 now buf W m)
      W ly3 S3 mem3 _ k acc _ _ ms' (d_S cx) (d_S cx) Hfrm0 HB HJ' HFR Hk Hnev Hmo Hacc Hi ltac:(lia) Hnow Hbody HSf
      eq_refl eq_refl (d_E_env cx E _ HE) (d_env_fl cx E _) ltac:(vm_compute; reflexivity)
      ltac:(unfold LLVMF_STK; lia) ltac:(lia) ltac:(intros x Hx _; exact (HK0 x Hx))
      ltac:(intros; eapply (a3_present_grows _ _ _ HG); eassumption) ltac:(intros; lia));
      [ res_drl HS3 HSf HrL
      | cbn beta; unfold w64; split; [res_val HSf (22%bv : bv 5) 553%nat E553 | res_val HSf (26%bv : bv 5) 557%nat E557]
      | cbn beta; split; [exact (res_sp1 cx i n now W mem3 (ms_mem ms') (proj1 HKA) (proj2 HKA) HK0 Hsp1)|];
        split; [exact (res_tab cx now T0 T1 W mem3 (ms_mem ms') ltac:(lia) ltac:(lia) HK0 Htab)|];
        exact (res_buf op T1 now buf W mem3 (ms_mem ms') ltac:(lia) ltac:(lia) HK0 Habuf)
      | exact (res_sp0 cx i now W mem3 (ms_mem ms') (proj1 HKA) (proj2 HKA) HK0 Hsp0) ].
  - assert (Hdv : buf / 8 + 1 <= (buf + r - 1) / 8) by lia.
    pose proof (obl_of_block SEGS B LAWS ly3 S3 W mem3 md3 (mkEnv (fun _ => Z_to_bv 64 0) (fun _ => []))
      (SLit SHADOW_OFF) buf 8 buf (Z.max (a3_cap op) 1) HAR Hin ltac:(vm_compute; reflexivity)
      ltac:(lia) ltac:(rewrite Hreq; lia)) as Hra.
    destruct (Hra (buf + 7) ltac:(lia)) as (s0 & Hs0' & Hsok0).
    clear Hra. unfold shadow_of_addr in Hs0'. change (U _ (SLit SHADOW_OFF)) with SHADOW_OFF in Hs0'.
    unfold rd_of in Hs0'. destruct (res_rd1 _ _ _ _ Hs0') as (Hsv0 & _). clear Hs0'.
    assert (Hz0 : s0 = 0) by (unfold saddr_ok in Hsok0; lia). subst s0.
    replace ((buf + 7) / 8) with (buf / 8) in Hsv0 by lia.
    set (ex := [w64 (SHADOW_OFF + buf / 8); w64 (SHADOW_OFF + (buf + r - 1) / 8); w64 s]).
    assert (HEX : forall E, d_E cx E ->
      ew (d_env cx E (a3_vals regs ex)) 541 = Z_to_bv 64 r /\ ew (d_env cx E (a3_vals regs ex)) 550 = Z_to_bv 64 (buf + r) /\
      ew (d_env cx E (a3_vals regs ex)) 553 = Z_to_bv 64 r /\ ew (d_env cx E (a3_vals regs ex)) 557 = Z_to_bv 64 buf /\
      ew (d_env cx E (a3_vals regs ex)) 563 = Z_to_bv 64 (SHADOW_OFF + buf / 8) /\
      ew (d_env cx E (a3_vals regs ex)) 564 = Z_to_bv 64 (SHADOW_OFF + (buf + r - 1) / 8) /\
      ew (d_env cx E (a3_vals regs ex)) 565 = Z_to_bv 64 s /\
      ew (d_env cx E (a3_vals regs ex)) 32 = Z_to_bv 64 SHADOW_OFF).
    { intros E HE. split; [rewrite (a3_env_reg cx E regs ex 10%bv 541 eq_refl); exact R10|].
      split; [rewrite (a3_env_reg cx E regs ex 19%bv 550 eq_refl); exact R19|].
      split; [rewrite (a3_env_reg cx E regs ex 22%bv 553 eq_refl); exact R22|].
      split; [rewrite (a3_env_reg cx E regs ex 26%bv 557 eq_refl); exact R26|].
      split; [exact (d_env_x cx E (a3_vals regs ex) 32 ltac:(vm_compute; lia))|].
      split; [exact (d_env_x cx E (a3_vals regs ex) 33 ltac:(vm_compute; lia))|].
      split; [exact (d_env_x cx E (a3_vals regs ex) 34 ltac:(vm_compute; lia))|].
      rewrite d_env_old by (unfold AT_FL; lia). destruct HE as (_ & E32 & _). exact E32. }
    assert (HX : forall E, d_E cx E ->
      atoms_ok (d_env cx E (a3_vals regs ex)) brk_f2 /\ conds_ok (d_env cx E (a3_vals regs ex)) (brk_c2 s) /\
      Forall (YP09.chunk_ok SEGS (d_env cx E (a3_vals regs ex)) (rd W mem3) (d_A cx)) [] /\
      Forall (YP09.chunk_ok SEGS (d_env cx E (a3_vals regs ex)) (rd W mem3) (d_FB cx)) [] /\
      Forall (region_ok SEGS (d_env cx E (a3_vals regs ex)) (rd W mem3)) brk_x2 /\
      pairwise_disjoint (d_env cx E (a3_vals regs ex)) brk_x2 /\
      Forall (fun r => all_disjoint (d_env cx E (a3_vals regs ex)) r (d_kregions dsh_loop [] [])) brk_x2).
    { intros E HE. destruct (HEX E HE) as (E541 & E550 & E553 & E557 & E563 & E564 & E565 & E32).
      set (E' := d_env cx E (a3_vals regs ex)) in *.
      destruct (res_atom E' 541 r E541 ltac:(lia)) as (_ & _ & U541).
      destruct (res_atom E' 550 (buf + r) E550 ltac:(lia)) as (B550 & _ & U550).
      destruct (res_atom E' 553 r E553 ltac:(lia)) as (_ & _ & U553).
      destruct (res_atom E' 557 buf E557 ltac:(lia)) as (B557 & _ & U557).
      destruct (res_atom E' 563 (SHADOW_OFF + buf / 8) E563 ltac:(unfold SHADOW_OFF; lia)) as (B563 & _ & U563).
      destruct (res_atom E' 564 (SHADOW_OFF + (buf + r - 1) / 8) E564 ltac:(unfold SHADOW_OFF; lia)) as (B564 & _ & U564).
      destruct (res_atom E' 565 s E565 ltac:(lia)) as (_ & D565 & U565).
      assert (U550m : U E' (SOff 550 (-1)) = buf + r - 1).
      { rewrite U_SOff, E550, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
      split; [|split; [|split; [constructor|split; [constructor|]]]].
      - cbn [atoms_ok brk_f2]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite E565. rewrite !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
        repeat split; lia.
      - unfold brk_c2. destruct (Z.eqb_spec s 0) as [Hs0|Hs0]; cbn [conds_ok]; unfold acond_ok; cbn [ac_c ac_a ac_b].
        + split; [rewrite branch_eq_U, U541, U553; apply Z.eqb_refl|].
          split; [|exact I]. rewrite branch_eq_U, U565, U_SLit. apply Z.eqb_eq. rewrite Hs0. reflexivity.
        + split; [rewrite branch_eq_U, U541, U553; apply Z.eqb_refl|].
          split; [rewrite branch_ne_U, U565, U_SLit; apply negb_true_iff, Z.eqb_neq; exact Hs0|].
          split; [|exact I].
          assert (UA : U E' (SAlu ALU_AND (SOff 550 (-1)) (SLit 7)) = (buf + r - 1) mod 8).
          { rewrite U_and_lit, U550m by lia. exact (Z.land_ones (buf + r - 1) 3 ltac:(lia)). }
          apply res_lt; rewrite ?UA, ?U565; [pose proof (Z.mod_pos_bound (buf + r - 1) 8 ltac:(lia)); lia | lia |].
          unfold saddr_ok in Hsok. lia.
      - split; [|split].
        + constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
          * apply (res_rok E' (rd W mem3) 557 0 buf 91 (SLit 91)); [exact B557 | lia | lia | reflexivity | lia | exact Hv0].
          * apply (res_rok E' (rd W mem3) 550 (-1) (buf + r) 93 (SLit 93)); [exact B550 | lia | lia | reflexivity | lia | exact Hv1].
          * apply (res_rok E' (rd W mem3) 563 0 (SHADOW_OFF + buf / 8) 0 (SLit 0));
              [exact B563 | unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia | reflexivity | lia | rewrite Z.add_0_r; exact Hsv0].
          * apply (res_rok E' (rd W mem3) 564 0 (SHADOW_OFF + (buf + r - 1) / 8) s (SOff 565 0));
              [exact B564 | unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia | exact D565 | lia | rewrite Z.add_0_r; exact Hsv].
        + apply pairwise_disjoint_of_extents. unfold brk_x2, extent_of_region.
          cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B557, B550, B563, B564.
          cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
          unfold SHADOW_OFF. repeat split; lia.
        + constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
          * apply (res_kx cx ly3 S3 W mem3 md3 k E (a3_vals regs ex) _ buf (buf + 1) HC HE).
            -- unfold extent_of_region. fold E'. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B557. f_equal; lia.
            -- left. unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. repeat split; lia.
          * apply (res_kx cx ly3 S3 W mem3 md3 k E (a3_vals regs ex) _ (buf + r - 1) (buf + r) HC HE).
            -- unfold extent_of_region. fold E'. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B550. f_equal; lia.
            -- left. unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. repeat split; lia.
          * apply (res_kx cx ly3 S3 W mem3 md3 k E (a3_vals regs ex) _ (SHADOW_OFF + buf / 8)
              (SHADOW_OFF + buf / 8 + 1) HC HE).
            -- unfold extent_of_region. fold E'. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B563. f_equal; lia.
            -- right. exists buf. repeat split; lia.
          * apply (res_kx cx ly3 S3 W mem3 md3 k E (a3_vals regs ex) _ (SHADOW_OFF + (buf + r - 1) / 8)
              (SHADOW_OFF + (buf + r - 1) / 8 + 1) HC HE).
            -- unfold extent_of_region. fold E'. cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B564. f_equal; lia.
            -- right. exists (buf + r - 1). repeat split; lia. }
    destruct (a3_seat B MT XM_LIB RLO RHI tfib_K LAWS TL DSEAT DFACTS fq cx P_SL_RA h n (a3_xb buf op) dsh_loop
      ly3 S3 W regs mem3 md3 k ex [] [] brk_x2 brk_f2 (brk_c2 s) HC HrL Hbody HX ltac:(vm_compute; reflexivity))
      as (E & HE & HS0).
    destruct (HEX E HE) as (E541 & E550 & E553 & E557 & E563 & E564 & E565 & E32).
    pose proof (a3_env_img cx E (a3_vals regs ex) HE) as HEI.
    set (E' := d_env cx E (a3_vals regs ex)) in *.
    pose proof (st_ok_pi_add_alias _ _ _ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 557 0) (SLit 3)) (SOff 32 0)) (SOff 563 0) HS0
      (shadow_decl_ok E' 557 32 563 buf SHADOW_OFF E557 ltac:(lia) E32 E563)) as HS1. clear HS0.
    pose proof (st_ok_pi_add_alias _ _ _ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 550 (-1)) (SLit 3)) (SOff 32 0)) (SOff 564 0) HS1
      (res_sdecl E' 550 32 564 (buf + r) (-1) SHADOW_OFF E550 ltac:(lia) ltac:(lia) E32 ltac:(unfold SHADOW_OFF; lia)
        ltac:(rewrite E564; do 2 f_equal; lia) ltac:(unfold SHADOW_OFF; lia))) as HS2. clear HS1.
    pose proof (st_ok_pi_submem _ _ _ _ HS2 (res_submem _) ltac:(vm_compute; reflexivity)) as HS3. clear HS2.
    unfold brk_c2 in HS3.
    destruct (Z.eqb_spec s 0) as [Hs0|Hs0].
    all: res_run_to HS3 HJ HEI R10_OFF.
    all: intros ms' mat HSf HJ' HF HFr HG; cbn [ms_mem YK11.mkst] in HF, HFr, HG, HJ'.
    all: assert (HK0 : forall x, 0 <= x < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms') x = aview SEGS (w_H W) mem3 x)
      by (intros x Hx; apply (a3_kept_frame _ _ (w_H W) mem3 (ms_mem ms') 0 0 HFr); [res_awr | exact Hx | lia]).
    all: apply SRr_ret; split; [exact HF0|].
    all: apply (a3_land_rt B MT XM_LIB RLO RHI tfib_K LAWS FFL DLAND DBRT fq cx R10_OFF (EV_HEAD i + 1) h i n n now
      (a3_xb buf op)
      (fun regs => getr regs 22 = w64 (a3_r T1 now) /\ getr regs 26 = w64 buf)
      (fun W m => d_sp1 cx i n now W m /\ a3_tab cx now T0 T1 W m /\ a3_buf op T1 now buf W m)
      W ly3 S3 mem3 _ k acc _ _ ms' (d_S cx) (d_S cx) Hfrm0 HB HJ' HFR Hk Hnev Hmo Hacc Hi ltac:(lia) Hnow Hbody HSf
      eq_refl eq_refl (d_E_env cx E _ HE) (d_env_fl cx E _) ltac:(vm_compute; reflexivity)
      ltac:(unfold LLVMF_STK; lia) ltac:(lia) ltac:(intros x Hx _; exact (HK0 x Hx))
      ltac:(intros; eapply (a3_present_grows _ _ _ HG); eassumption) ltac:(intros; lia));
      [ res_drl HS3 HSf HrL
      | cbn beta; unfold w64; split; [res_val HSf (22%bv : bv 5) 553%nat E553 | res_val HSf (26%bv : bv 5) 557%nat E557]
      | cbn beta; split; [exact (res_sp1 cx i n now W mem3 (ms_mem ms') (proj1 HKA) (proj2 HKA) HK0 Hsp1)|];
        split; [exact (res_tab cx now T0 T1 W mem3 (ms_mem ms') ltac:(lia) ltac:(lia) HK0 Htab)|];
        exact (res_buf op T1 now buf W mem3 (ms_mem ms') ltac:(lia) ltac:(lia) HK0 Habuf)
      | exact (res_sp0 cx i now W mem3 (ms_mem ms') (proj1 HKA) (proj2 HKA) HK0 Hsp0) ].
Qed.

End h.
End f.
End d.
