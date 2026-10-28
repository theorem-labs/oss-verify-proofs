(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AE2l AF0m AF0x AE2y AE3i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE04 YE00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ff_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_run_toN tfibsegs tbl_ff FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_ff tbl_ff_ok AF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma ff_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_runN tfibsegs tbl_ff FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_ff tbl_ff_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Definition cells_hold (m : word -> option byte) (l : list (Z * Z * list (Z * N * Z))) : Prop :=
Forall (fun r => 0 <= fst (fst r) /\ fst (fst r) + snd (fst r) <= 2 ^ 47 /\
Forall (fun c => val_mem tfibsegs m (fst (fst r) + fst (fst c)) (N.to_nat (snd (fst c))) (snd c) /\
0 <= snd c < 2 ^ (8 * Z.of_N (snd (fst c))) /\ Z.of_N (snd (fst c)) <= 8) (snd r)) l.
Lemma cells_region_ok : forall m E l, cells_hold m l -> Forall (region_ok tfibsegs E m) (map ro_region l).
Proof.
intros m E l Hl. apply Forall_map. apply Forall_forall. intros [[base sz] cs] Hin.
pose proof (proj1 (Forall_forall _ _) Hl _ Hin) as (H0 & Hhi & Hcs). cbn [fst snd] in H0, Hhi, Hcs.
unfold ro_region, region_ok. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_map. apply Forall_forall. intros [[off n] v] Hc. pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as (Hv & Hr & Hn). cbn [fst snd] in Hv, Hr, Hn.
unfold ro_chunk. cbn [fst snd]. eapply (chunk_ok_val tfibsegs E _ 0 (base + off) n (SLit v) v); [| exact Hr | exact Hn | rewrite Z.add_0_l; exact Hv].
cbn [sv_denot]. reflexivity.
Qed.
Lemma cells_hold_frame : forall (m m' : word -> option byte) l,
(forall a, Exists (fun r => fst (fst r) <= a < fst (fst r) + snd (fst r)) l -> mbyte tfibsegs m' a = mbyte tfibsegs m a) ->
Forall (fun r => Forall (fun c => 0 <= fst (fst c) /\ fst (fst c) + Z.of_N (snd (fst c)) <= snd (fst r)) (snd r)) l ->
cells_hold m l -> cells_hold m' l.
Proof.
intros m m' l Hfr Hin Hl. unfold cells_hold in *. apply Forall_forall. intros r Hr.
pose proof (proj1 (Forall_forall _ _) Hl r Hr) as (H0 & Hhi & Hcs). pose proof (proj1 (Forall_forall _ _) Hin r Hr) as Hcin.
split; [exact H0|]. split; [exact Hhi|]. apply Forall_forall. intros c Hc.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as (Hv & Hrg & Hn). pose proof (proj1 (Forall_forall _ _) Hcin c Hc) as [Hc0 Hc1].
split; [| exact (conj Hrg Hn)]. intros k Hk. rewrite Hfr; [exact (Hv k Hk)|].
apply Exists_exists. exists r. split; [exact Hr|]. pose proof (N_nat_Z (snd (fst c))). lia.
Qed.
Definition hashT (pf : nat) : sv := SMd M_MUL (SOff pf 0) (SLit 1025).
Definition hashH (pf : nat) : sv := SAlu ALU_XOR (SAlu ALU_SRL (hashT pf) (SLit 6)) (hashT pf).
Definition hashQ (pf : nat) : sv := SAlu ALU_SRL (SMd M_MULHU (hashH pf) (SLit AHM_MAGIC)) (SLit 14).
Definition hashI (pf : nat) : sv := SAlu ALU_SUB (hashH pf) (SMd M_MUL (hashQ pf) (SLit 31051)).
Definition hashX (pf : nat) : sv := SAlu ALU_SUB (SAlu ALU_SLL (hashI pf) (SLit 7)) (SAlu ALU_SLL (hashI pf) (SLit 3)).
Definition hashS4 (pm pf : nat) : sv := SAlu ALU_ADD (SOff pm 0) (hashX pf).
Lemma U_hashS4 : forall E (pm pf : nat) M f,
ew E pm = Z_to_bv 64 M -> ew E pf = Z_to_bv 64 f -> 0 <= M -> M + AMETA_SIZE <= 2 ^ 64 -> 0 <= f < 2 ^ 64 ->
U E (hashS4 pm pf) = M + 120 * ahm_idx f.
Proof.
intros E pm pf M f HM Hf RM RM2 Rf.
rewrite (U_zev E) by reflexivity. cbn [zev svpure hashS4 hashX hashI hashQ hashH hashT].
unfold rho_of. rewrite HM, Hf, !unsigned_lit_small by (unfold AMETA_SIZE in *; lia). rewrite !Z.add_0_r.
cbn [zmd_raw zalu_raw]. unfold zcanon, M64.
change (Z.land (1025 mod 2 ^ 64) 63) with 1. change (1025 mod 2 ^ 64) with 1025. change (Z.land (6 mod 2 ^ 64) 63) with 6.
change (Z.land (14 mod 2 ^ 64) 63) with 14. change (Z.land (7 mod 2 ^ 64) 63) with 7. change (Z.land (3 mod 2 ^ 64) 63) with 3.
change (31051 mod 2 ^ 64) with 31051. change (AHM_MAGIC mod 2 ^ 64) with AHM_MAGIC. change (Z.of_N 64) with 64.
rewrite !Z.shiftr_div_pow2, !Z.shiftl_mul_pow2 by lia.
rewrite (Z.mod_small f) by lia.
pose proof (ahm_offset_eval f Rf) as EV. cbv zeta in EV.
replace ((f * 1025) mod 2 ^ 64) with (((f * 2 ^ 10) mod 2 ^ 64 + f) mod 2 ^ 64)
by (rewrite Z.add_mod_idemp_l by lia; f_equal; lia).
set (t := ((f * 2 ^ 10) mod 2 ^ 64 + f) mod 2 ^ 64) in *.
rewrite Z.lxor_comm. rewrite EV.
pose proof (ahm_idx_range f). unfold AMETA_SIZE in *. rewrite (Z.mod_small M) by lia. apply Z.mod_small. lia.
Qed.
Definition bucketR (n : nat) : YP09.region :=
YP09.mkRegion (Some n) 0 120 0 8
[YP09.mkChunk 0 (CVal 8 (SLit 0)); YP09.mkChunk 16 (CVal 8 (SLit 0)); YP09.mkChunk 24 (CVal 8 (SLit 0));
YP09.mkChunk 56 (CVal 8 (SLit 0)); YP09.mkChunk 88 (CVal 8 (SLit 0))].
Lemma bucketR_ok : forall E (m : word -> option byte) n b,
bv_unsigned (ew E n) = b -> 0 <= b -> b + 120 <= 2 ^ 64 ->
(forall a, b <= a < b + 120 -> mbyte tfibsegs m a = Some (Z_to_bv 8 0)) ->
(forall o, 0 <= o < 8 -> writable_at tfibsegs m (b + o)) ->
region_ok tfibsegs E m (bucketR n).
Proof.
intros E m n b Hn Hb0 Hb1 Hz Hw. unfold bucketR, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hn.
split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hw; lia|].
assert (Z8 : forall off, 0 <= off -> off + 8 <= 120 -> YP09.chunk_ok tfibsegs E m b (YP09.mkChunk off (CVal 8 (SLit 0)))).
{ intros off H0 H1. eapply (chunk_ok_val tfibsegs E m b off 8 (SLit 0) 0); [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia |].
intros k Hk. rewrite Hz by lia. f_equal. unfold YO0f.le_byte. rewrite Z.shiftr_0_l. reflexivity. }
repeat (apply Forall_cons; [apply Z8; lia|]). apply Forall_nil.
Qed.
Lemma in_wrange_two_b : forall E rs a n1 lo1 hi1 v1 n2 lo2 hi2 v2,
forallb (fun t => win_eqb t (Some n1, lo1, hi1) || win_eqb t (Some n2, lo2, hi2) || (snd t <=? snd (fst t))) (windows rs) = true ->
bv_unsigned (ew E n1) = v1 -> bv_unsigned (ew E n2) = v2 ->
in_wrange E rs a -> (v1 + lo1 <= a < v1 + hi1) \/ (v2 + lo2 <= a < v2 + hi2).
Proof.
intros E rs a n1 lo1 hi1 v1 n2 lo2 hi2 v2 Hb H1 H2 Hin.
destruct (in_wrange_windows E rs a Hin) as (b & lo & hi & Ht & Hr).
rewrite forallb_forall in Hb. specialize (Hb _ Ht). apply orb_prop in Hb as [Hb|Hb]; [apply orb_prop in Hb as [Hb|Hb]|].
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. rewrite H1 in Hr. left. exact Hr.
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. rewrite H2 in Hr. right. exact Hr.
- cbn [fst snd] in Hb. apply Z.leb_le in Hb. lia.
Qed.
Definition img_piece (a n : Z) : YP09.region := YP09.mkRegion None a (a + n) a a [YP09.mkChunk a (CImg n)].
Lemma img_piece_ok : forall (m : word -> option byte) E a0 n0 a n,
ro_img m -> In (YP09.mkChunk a0 (CImg n0)) img_ro_chunks -> a0 <= a -> 0 <= n -> a + n <= a0 + n0 ->
region_ok tfibsegs E m (img_piece a n).
Proof.
intros m E a0 n0 a n Hro Hin Hlo Hn Hhi.
pose proof (Hro E) as (B0 & B1 & _ & HCS). unfold img_ro_region in B0, B1, HCS. cbn [YP09.r_chunks YP09.r_base YP09.r_lo YP09.r_hi base_val] in B0, B1, HCS.
pose proof (proj1 (Forall_forall _ _) HCS _ Hin) as HC.
pose proof (proj1 (Forall_forall _ _) img_ro_chunks_inside _ Hin) as (I0 & I1 & _). cbn [YP09.c_off c_len cv_len YP09.c_val] in I0, I1.
unfold img_piece, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold IMG_RO_LO, IMG_RO_HI in *.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
intros i Hi. cbn [YP09.c_off YP09.c_val c_len cv_len] in Hi |- *.
specialize (HC (a - a0 + i)). cbn [YP09.c_off YP09.c_val c_len cv_len] in HC.
destruct (HC ltac:(lia)) as (bb & Hc & Hm). exists bb. rewrite !Z.add_0_l in *. cbn [cbyte] in Hc |- *.
replace (a + i) with (a0 + (a - a0 + i)) by lia. exact (conj Hc Hm).
Qed.
End d.
