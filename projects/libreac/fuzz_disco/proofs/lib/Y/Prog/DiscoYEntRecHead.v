(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 365 of its 397 lines of code are new or changed and 37 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntLatch.v, with its module paths and numbers changed; 429 of its 512 lines of code are new or changed and 314 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YC45 YC81 YC85 YC1g YC1h YC4b.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoYEntRecCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma yr_rdb_range : forall R j, 0 <= rdb R j < 256.
Proof.
intros R j. unfold rdb. pose proof (bv_unsigned_in_range 8 (nth j R (Z_to_bv 8 0))) as Hr.
change (bv_modulus 8) with 256 in Hr. exact Hr.
Qed.

Lemma yr_rdb_over : forall R j, (length R <= j)%nat -> rdb R j = 0.
Proof. intros R j Hj. unfold rdb. rewrite nth_overflow by exact Hj. reflexivity. Qed.

Lemma yr_rest_len : forall (pl : list byte) n, 0 <= n <= Z.of_nat (length pl) ->
  length (rest_of pl n) = Z.to_nat n.
Proof. intros pl n Hn. unfold rest_of. rewrite length_skipn. lia. Qed.

Lemma yr_rest0 : forall pl : list byte, rest_of pl 0 = [].
Proof. intros pl. unfold rest_of. cbn [Z.to_nat]. rewrite Nat.sub_0_r. apply skipn_all. Qed.

Lemma yr_U_off : forall E (q : nat) x c, ew E q = w64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  U E (SOff q c) = x + c.
Proof.
intros E q x c Hq Hx Hxc. rewrite U_SOff, Hq. unfold w64. rewrite unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.

Lemma yr_and7 : forall E (q : nat) x c, ew E q = w64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  U E (SAlu ALU_AND (SOff q c) (SLit 7)) = (x + c) mod 8.
Proof.
intros E q x c Hq Hx Hxc. rewrite (U_and_lit E _ 7 ltac:(lia)), (yr_U_off E q x c Hq Hx Hxc).
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma yr_u8 : forall E (q : nat) v, ew E q = w64 v -> 0 <= v < 256 -> U E (SExt false 8 (SOff q 0)) = v.
Proof.
intros E q v Hq Hv. rewrite U_SExt. change (2 ^ Z.of_N 8) with 256.
rewrite (yr_U_off E q v 0 Hq ltac:(lia) ltac:(lia)), Z.add_0_r, (Z.mod_small v 256) by lia.
apply zcanon_id. unfold M64. lia.
Qed.

Lemma yr_s8 : forall E (q : nat) v, ew E q = w64 v -> 0 <= v < 128 -> U E (SExt true 8 (SOff q 0)) = v.
Proof.
intros E q v Hq Hv. rewrite U_SExt. change (2 ^ Z.of_N 8) with 256.
rewrite (yr_U_off E q v 0 Hq ltac:(lia) ltac:(lia)), Z.add_0_r, (Z.mod_small v 256) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
rewrite (Z.mod_small (v + 128) 256) by lia. replace (v + 128 - 128) with v by lia.
apply zcanon_id. unfold M64. lia.
Qed.

Lemma yr_u8_denot : forall E (q : nat) v, ew E q = w64 v -> 0 <= v < 256 ->
  sv_denot E (SExt false 8 (SOff q 0)) = w64 v.
Proof. intros E q v Hq Hv. rewrite denot_lit_U, (yr_u8 E q v Hq Hv). reflexivity. Qed.

Lemma yr_sll8 : forall E (q : nat) v, ew E q = w64 v -> 0 <= v < 256 ->
  sv_denot E (SAlu ALU_SLL (SExt false 8 (SOff q 0)) (SLit 8)) = w64 (256 * v).
Proof.
intros E q v Hq Hv. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. unfold w64. f_equal.
rewrite (yr_u8 E q v Hq Hv), U_SLit.
change (Z.land (zcanon 8) 63) with 8. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (zcanon_id (v * 256)) by (unfold M64; lia). lia.
Qed.

Lemma yr_s8_ne : forall E (q : nat) v, ew E q = w64 v -> 0 <= v < 256 ->
  branch_taken BC_EQ (sv_denot E (SExt true 8 (SOff q 0))) (sv_denot E (SLit 0)) = false -> v <> 0.
Proof.
intros E q v Hq Hv Hb Hv0. subst v.
rewrite branch_eq_U, (U_lit E 0 ltac:(lia)), U_SExt in Hb.
rewrite (yr_U_off E q 0 0 Hq ltac:(lia) ltac:(lia)) in Hb.
vm_compute in Hb. discriminate Hb.
Qed.

Lemma yr_bge : forall E a b x y, U E a = x -> U E b = y -> 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (x <? y).
Proof.
intros E a b x y Ha Hb Hx Hy. unfold U in Ha, Hb. cbn [branch_taken]. unfold bv_lts, bv_signed.
rewrite Ha, Hb.
assert (Hs : forall z, 0 <= z < 2 ^ 63 -> bv_swrap 64 z = z).
{ intros z Hz. unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63).
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia. }
rewrite !Hs by lia. reflexivity.
Qed.

Ltac yr_awr := repeat (apply awr_ok_cons_ro; [apply Z.leb_le; vm_compute; reflexivity|]); apply awr_ok_nil.

Ltac yr_drop HS :=
  let HS2 := fresh "HSd" in
  pose proof (st_ok_pi_submem _ _ _ [] HS (submem_nil _) eq_refl) as HS2;
  clear HS; rename HS2 into HS; norm_ss HS.

Ltac yr_meq :=
  lazymatch goal with HF : frame_of _ _ (ms_mem ?m0) (ms_mem _) |- _ =>
    let M := fresh "Mq" in
    pose proof (y_frame_eq _ _ _ _ HF ltac:(vm_compute; reflexivity)) as M; cbn [ms_mem mkst] in M;
    clear HF;
    lazymatch goal with
    | MEQ : forall x, ms_mem m0 x = _ |- _ =>
        let MN := fresh "Mn" in pose proof (fun x => eq_trans (M x) (MEQ x)) as MN; clear M MEQ;
        rename MN into MEQ
    end
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma yr_vm_ext : forall (W3 : world SEGS) (m m' : word -> option byte) a q v,
  (forall x, m' x = m x) -> val_mem SEGS (rd W3 m) a q v -> val_mem SEGS (rd W3 m') a q v.
Proof. intros W3 m m' a q v HM Hv j Hj. rewrite (y_mbyte_ext SEGS (w_H W3) m m' HM). exact (Hv j Hj). Qed.

Lemma yr_in_val : forall cx n (W3 : world SEGS) mem3 (j : nat),
  d_input cx n W3 mem3 -> Z.of_nat (length (c_pl cx)) = c_n cx -> Z.of_nat j < n ->
  aview SEGS (w_H W3) mem3 (d_cur cx n + Z.of_nat j) = Some (rdb (rest_of (c_pl cx) n) j).
Proof.
intros cx n W3 mem3 j (Hn & HG & _) Hlen Hj.
assert (Hnc : n <= c_n cx) by lia.
assert (Hidx : (Z.to_nat (c_n cx - n) + j < length (c_pl cx))%nat) by lia.
destruct (HG (Z.to_nat (c_n cx - n) + j)%nat ltac:(rewrite length_map; exact Hidx)) as (Hv & Hr).
assert (Heq : nth (Z.to_nat (c_n cx - n) + j) (map (fun b : byte => bv_unsigned b) (c_pl cx)) 0 =
              rdb (rest_of (c_pl cx) n) j).
{ unfold rdb, rest_of. rewrite nth_skipn.
  rewrite (nth_indep (map (fun b : byte => bv_unsigned b) (c_pl cx)) 0 (bv_unsigned (Z_to_bv 8 0)))
    by (rewrite length_map; exact Hidx).
  rewrite (map_nth (fun b : byte => bv_unsigned b)). f_equal. f_equal. lia. }
apply aview_of_val_mem1.
- replace (d_cur cx n + Z.of_nat j) with (c_p cx + Z.of_nat (Z.to_nat (c_n cx - n) + j))
    by (unfold d_cur; lia).
  rewrite <- Heq. exact Hv.
- rewrite <- Heq. exact Hr.
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Section g.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis TL : PALib B.
Hypothesis SEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis FACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis BRT : d_body_rt_stmt B.

Lemma yr_blk : forall cx h n ly3 S3 (W3 : world SEGS) mem3,
  d_base B MT XM_LIB RLO RHI tfib_K cx -> d_body B cx h n [] dsh_loop ly3 S3 W3 mem3 -> 1 <= n ->
  8 <= c_n cx /\ n <= c_n cx - 7 /\ 4096 <= c_p cx /\ c_p cx mod 8 = 0 /\
  c_p cx + c_n cx <= alloc_ceiling /\ Z.of_nat (length (c_pl cx)) = c_n cx /\
  In (c_p cx, c_n cx) (ablocks B ly3 S3).
Proof.
intros cx h n ly3 S3 W3 mem3 HB HBD Hn.
pose proof HB as ((HPRE & _ & _ & _ & HINdisj & _) & _).
pose proof HPRE as (HAR0 & _).
pose proof HBD as (_ & _ & _ & _ & _ & _ & _ & (HPERM & _) & ((Rn0 & Rn1) & _) & _ & _ &
  (_ & _ & _ & _ & _ & Hlen & _) & _).
assert (Hcn : 8 <= c_n cx) by lia.
destruct HINdisj as [(Hc0 & _) | (_ & Hin)]; [lia|].
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hin) as (H16 & H4096 & Hc & _).
assert (Hrq : req_size (c_n cx) = c_n cx)
  by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); [lia | reflexivity]).
rewrite Hrq in Hc.
split; [lia|]. split; [lia|]. split; [lia|]. split; [clear - H16; lia|]. split; [lia|].
split; [exact Hlen|].
apply (Permutation_in _ (Permutation_sym HPERM)). cbn [app]. right. exact Hin.
Qed.

Lemma yr_land : forall (fq : YK11.FPState) (cx : dcx) (h i n now op : Z) ly3 S3 (W3 : world SEGS) mem3 md' k acc
  (E : env) (ss : sstate) (ms : machine_state),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W3 (ms_mem ms) md' k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD i -> st_nev S3 <= st_nev (c_S cx) + EV_HEAD i ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 -> 0 <= op < 256 -> op mod 4 <> 3 ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W3) ms) -> ss_resv ss = None -> ss_pc ss = JOIN_OFF ->
  d_body B cx h n [] dsh_loop ly3 S3 W3 mem3 ->
  (forall x, ms_mem ms x = mem3 x) ->
  d_sp0 cx i now W3 mem3 -> d_spOP cx op W3 mem3 ->
  d_rL B cx (ms_regs ms) /\ getr (ms_regs ms) 22 = w64 1 /\ getr (ms_regs ms) 21 = w64 i /\
  getr (ms_regs ms) 26 = w64 now /\ getr (ms_regs ms) 23 = w64 (op mod 4) /\
  getr (ms_regs ms) 11 = w64 (rdb (rest_of (c_pl cx) n) 0) /\
  getr (ms_regs ms) 12 = w64 (256 * rdb (rest_of (c_pl cx) n) 1) /\
  getr (ms_regs ms) 24 = w64 (rec_rem n) /\ getr (ms_regs ms) 25 = w64 (d_cur cx (rec_rem n)) ->
  yr_join B MT XM_LIB RLO RHI tfib_K cx h i n now op W3 (mkCfg ms md').
Proof.
intros fq cx h i n now op ly3 S3 W3 mem3 md' k acc E ss ms HFQ HB HJ HFR Hk Hev Hmo Hacc Ri Rn Rnow Rop Ropm
  HS Hrv Hpc HBD MEQ HSP HOP (HL & Zr22 & Zr21 & Zr26 & Zr23 & Zr11 & Zr12 & Zr24 & Zr25).
pose proof (st_ok_pi_restrict_mkst (w_H W3) E ss ms HS Hrv) as Hms.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, acc.
split; [unfold cfg_at; rewrite Hms at 1; rewrite Hpc; reflexivity|].
split; [exact HFQ|].
split; [exact HB|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|]. split; [exact Hev|].
split; [exact Hmo|]. split; [exact Hacc|].
split; [exact Ri|]. split; [exact Rn|]. split; [exact Rnow|]. split; [exact Rop|]. split; [exact Ropm|].
split; [exact HL|]. split; [exact Zr22|]. split; [exact Zr21|]. split; [exact Zr26|]. split; [exact Zr23|].
split; [exact Zr11|]. split; [exact Zr12|]. split; [exact Zr24|]. split; [exact Zr25|].
split; [destruct HSP as (V1 & V2);
        exact (conj (yr_vm_ext W3 mem3 (ms_mem ms) _ _ _ MEQ V1) (yr_vm_ext W3 mem3 (ms_mem ms) _ _ _ MEQ V2))|].
split; [destruct HOP as (V1 & V2);
        exact (conj (yr_vm_ext W3 mem3 (ms_mem ms) _ _ _ MEQ V1) (yr_vm_ext W3 mem3 (ms_mem ms) _ _ _ MEQ V2))|].
exact (y_body_ext B BRT cx h n [] dsh_loop ly3 S3 W3 mem3 (ms_mem ms) MEQ HBD).
Qed.

Theorem yr_pb_head : yr_head_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
unfold yr_head_stmt. intros cx h i n now op W c Hpre.
destruct Hpre as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFQ & HB & HJ & HFR & Hk & Hev & Hmo & Hacc &
  Ri & Rn & Rnow & Rop & Ropm & HR & HSP & HOP & HBD).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact HB | split; [exact HJ | exact HFR]]).
pose proof asan_consts as (C1 & _).
pose proof HB as ((HPRE & _ & _ & _ & HINdisj & _) & _).
pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
change (spZ (c_regs cx)) with (d_S cx) in Hslo, Hshi.
pose proof HBD as (T & G & Lk & H & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFF & HGEO & HCAN & HSTK & HWR).
pose proof HFRM as (E & HE & HRG & HFL & _).
pose proof HE as (EE & E32 & HEI & E60 & E516 & E529).
unfold AT_A, AT_F, AT_SH in E60, E516, E529.
pose proof HR as ((Hsp & Hgp & Htp & H8 & H9 & H19 & H18 & H20 & H27) & H22 & H21 & H14 & H26 & H25 & H16 & H23).
assert (Rcn : c_n cx < 2 ^ 26) by (clear - HINdisj; destruct HINdisj as [(-> & _) | (Hr & _)]; lia).
pose proof HINP as (Rnm & _ & _).
assert (Rn64 : 0 <= n < 2 ^ 64) by (clear - Rn Rnm Rcn; lia).
pose proof (y_A_range (d_S cx) ltac:(clear - C1 Hceil Hslo; unfold MFRAME, LLVMF_STK in *; lia)) as HAr.
change (32 * ((d_S cx - MFRAME) / 32)) with (d_A cx) in HAr.
assert (RA : 0 <= d_A cx < 2 ^ 64) by (clear - C1 Hceil Hslo Hshi H47 HAr; unfold MFRAME, LLVMF_STK in *; lia).
pose proof (y_E_env cx E (yr_vals cx h i n now op regs) HE) as HEd.
pose proof HEd as (_ & _ & HEI' & _).
set (Ed := d_env cx E (yr_vals cx h i n now op regs)) in *.
assert (AO : forall q, (q < AT_FL)%nat -> ew Ed q = ew E q) by (intros q Hq; apply y_env_old; exact Hq).
assert (AX : forall j, (j < 34)%nat -> ew Ed (AT_X + j) = nth j (yr_vals cx h i n now op regs) (Z_to_bv 64 0))
  by (intros j Hj; apply y_env_x; cbn [length yr_vals]; lia).
assert (D60 : sv_denot Ed (SOff 60 0) = w64 (d_A cx))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); exact E60).
assert (D2 : sv_denot Ed (SOff 2 0) = w64 (d_S cx))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
      unfold w64, d_S, spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (D3 : sv_denot Ed (SOff 3 0) = w64 (as_gp B))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); rewrite (EE 3%nat 3%bv eq_refl); exact Hgp0).
assert (D4 : sv_denot Ed (SOff 4 0) = w64 (as_tp B))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); rewrite (EE 4%nat 4%bv eq_refl); exact Htp0).
assert (D32 : sv_denot Ed (SOff 32 0) = w64 SHADOW_OFF)
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); exact E32).
assert (D529 : sv_denot Ed (SOff 529 0) = w64 (shadow_addr (d_FB cx)))
  by (rewrite sv_denot_SOff0, AO by (unfold AT_FL; lia); exact E529).
assert (DX : forall j q, q = (AT_X + j)%nat -> (j < 34)%nat ->
  sv_denot Ed (SOff q 0) = nth j (yr_vals cx h i n now op regs) (Z_to_bv 64 0))
  by (intros j q -> Hj; rewrite sv_denot_SOff0; exact (AX j Hj)).
assert (HROK : regs_ok Ed yr_sr regs).
{ apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
  repeat (destruct Hz as [<-|Hz];
    [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
        let v := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with v end;
      lazymatch goal with
      | |- _ = sv_denot _ (SLit 0) => rewrite getr_zero; reflexivity
      | |- _ = sv_denot _ (SLit _) => cbn [sv_denot]; first [ exact H18 | exact H20 | exact H22 ]
      | |- _ = sv_denot _ (SOff 60 0) => rewrite D60;
          first [ exact H9 | unfold w64; rewrite <- Hsp; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned ]
      | |- _ = sv_denot _ (SOff 2 0) => rewrite D2; exact H8
      | |- _ = sv_denot _ (SOff 3 0) => rewrite D3; exact Hgp
      | |- _ = sv_denot _ (SOff 4 0) => rewrite D4; exact Htp
      | |- _ = sv_denot _ (SOff 32 0) => rewrite D32; exact H19
      | |- _ = sv_denot _ (SOff 529 0) => rewrite D529; exact H27
      | |- _ = sv_denot _ (SOff ?q 0) =>
          let j := eval vm_compute in (q - 531)%nat in
          rewrite (DX j q eq_refl ltac:(lia)); cbn [nth yr_vals]; first [reflexivity | assumption]
      end
    | ]).
  destruct Hz. }
assert (HFACTS : facts_ok Ed (d_facts [] []))
  by exact (FACTS LAWS cx ly3 S3 W mem3 md3 k E (yr_vals cx h i n now op regs) [] [] HC HE I I).
pose proof (SEAT LAWS TL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E REC_OFF yr_sr
  (yr_vals cx h i n now op regs) [] [] [] (d_facts [] []) HC HE HRG HFL HROK HFACTS (Forall_nil _)
  (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
unfold ss_d in HS0. fold Ed in HS0.
pose proof (st_ok_pi_submem _ _ _ [] HS0 (submem_nil _) eq_refl) as HS.
clear HS0 HROK HFACTS HRG HFL HFRM HE HEd EE HEI HSHD HOBJ HIMG HOFF HCAN HSTK HWR HPRE.
norm_ss HS.
destruct (y_geom B LAWS MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k HC) as
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GAR & _).
pose proof (SRr_run_to_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNTO.
pose proof (SRr_run_pi_AJ (fx := fq) (PL := PL_both3_0) (PI := PI) B LAWS) as RUNP.
pose (BR := paj_branch (fx := fq) (PI := PI)).
unfold cfg_at. change (w64 (BASE + REC_OFF)) with (Z_to_bv 64 (BASE + REC_OFF)).
assert (MEQ : forall x, ms_mem (mkst regs (Z_to_bv 64 (BASE + REC_OFF)) mem3 (seg_rom SEGS)) x = mem3 x)
  by reflexivity.
assert (A531 : ew Ed 531 = w64 n) by exact (AX 0%nat ltac:(lia)).
assert (A534 : ew Ed 534 = w64 (d_cur cx n)) by exact (AX 3%nat ltac:(lia)).
assert (A559 : ew Ed 559 = w64 (y_dsh_cell_addr (d_cur cx n))) by exact (AX 28%nat ltac:(lia)).
assert (A560 : ew Ed 560 = w64 (y_dsh_cell (c_p cx) (c_n cx) (d_cur cx n))) by exact (AX 29%nat ltac:(lia)).
assert (A561 : ew Ed 561 = w64 (rdb (rest_of (c_pl cx) n) 0)) by exact (AX 30%nat ltac:(lia)).
assert (A562 : ew Ed 562 = w64 (y_dsh_cell_addr (d_cur cx n + 1))) by exact (AX 31%nat ltac:(lia)).
assert (A563 : ew Ed 563 = w64 (y_dsh_cell (c_p cx) (c_n cx) (d_cur cx n + 1))) by exact (AX 32%nat ltac:(lia)).
assert (A564 : ew Ed 564 = w64 (rdb (rest_of (c_pl cx) n) 1)) by exact (AX 33%nat ltac:(lia)).
assert (A32 : ew Ed 32 = w64 SHADOW_OFF) by (rewrite AO by (unfold AT_FL; lia); exact E32).
pose proof (yr_rdb_range (rest_of (c_pl cx) n) 0) as Rb0.
pose proof (yr_rdb_range (rest_of (c_pl cx) n) 1) as Rb1.
let yr_dr HS :=
  (yr_rg HS (2%bv : bv 5) Zr2; yr_rg HS (3%bv : bv 5) Zr3; yr_rg HS (4%bv : bv 5) Zr4;
   yr_rg HS (8%bv : bv 5) Zr8; yr_rg HS (9%bv : bv 5) Zr9; yr_rg HS (19%bv : bv 5) Zr19;
   yr_rg HS (18%bv : bv 5) Zr18; yr_rg HS (20%bv : bv 5) Zr20; yr_rg HS (27%bv : bv 5) Zr27;
   yr_rg HS (22%bv : bv 5) Zr22; yr_rg HS (21%bv : bv 5) Zr21; yr_rg HS (26%bv : bv 5) Zr26;
   yr_rg HS (23%bv : bv 5) Zr23; yr_rg HS (11%bv : bv 5) Zr11; yr_rg HS (12%bv : bv 5) Zr12;
   yr_rg HS (24%bv : bv 5) Zr24; yr_rg HS (25%bv : bv 5) Zr25;
   split; [unfold d_rL;
     split; [unfold spZ; rewrite Zr2, D60; unfold w64; apply unsigned_lit_small; exact RA|];
     split; [rewrite Zr3; exact D3|]; split; [rewrite Zr4; exact D4|]; split; [rewrite Zr8; exact D2|];
     split; [rewrite Zr9; exact D60|]; split; [rewrite Zr19; exact D32|]; split; [rewrite Zr18; reflexivity|];
     split; [rewrite Zr20; reflexivity|]; rewrite Zr27; exact D529 |];
   split; [rewrite Zr22; reflexivity|];
   split; [rewrite Zr21, (DX 1%nat 532%nat eq_refl ltac:(lia)); reflexivity|];
   split; [rewrite Zr26, (DX 2%nat 533%nat eq_refl ltac:(lia)); reflexivity|];
   split; [rewrite Zr23, (DX 6%nat 537%nat eq_refl ltac:(lia)); reflexivity|];
   split; [rewrite Zr11 | split; [rewrite Zr12 | split; [rewrite Zr24 | rewrite Zr25]]]) in
let yr_landt HS :=
  (apply SRr_ret;
   apply (yr_land fq cx h i n now op ly3 S3 W mem3 _ k acc Ed _ _ HFQ HB HJ HFR Hk Hev Hmo Hacc Ri Rn Rnow Rop Ropm
     HS eq_refl eq_refl HBD MEQ HSP HOP);
   yr_dr HS) in
let yr_bseat HS rdst q v y s o Hq Hv Hreg Hbase :=
  (lazymatch type of HS with
   | st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?Wx) ?msx) =>
       pose proof (y_byte_seat _ Ex ssx msx Wx rdst q v y s o HS eq_refl Hreg Hq
         ltac:(clear - Rcur Rcu RS0 RS1 C1 Rc0 Rc1 Rb0 Rb1; lia) ltac:(lia)
         ltac:(clear - Rcur Rcu RS0 RS1 C1 Rc0 Rc1 Rb0 Rb1; lia) Hv
         ltac:(clear - Rcur Rcu RS0 RS1 C1 Rc0 Rc1 Rb0 Rb1; lia)
         ltac:(rewrite (y_aview_ext SEGS (w_H Wx) mem3 (ms_mem msx) MEQ); exact Hbase) I) as HSb;
       clear HS; rename HSb into HS; norm_ss HS
   end) in
let yr_k40 HS :=
  (yr_drop HS;
   yr_rg HS (10%bv : bv 5) Zg10; symmetry in Zg10;
   yr_bseat HS (10%bv : bv 5) 534%nat 564%nat (d_cur cx n) (rdb (rest_of (c_pl cx) n) 1) 1 A534 A564 Zg10 Hin1;
   paj_run_to_sh RUNTO HS HJ JOIN_OFF;
   [ yr_awr
   | yr_meq; yr_landt HS;
     [ rewrite (yr_u8_denot Ed 561%nat (rdb (rest_of (c_pl cx) n) 0) A561 Rb0); reflexivity
     | rewrite (yr_sll8 Ed 564%nat (rdb (rest_of (c_pl cx) n) 1) A564 Rb1); reflexivity
     | rewrite denot_lit_U, (yr_U_off Ed 531%nat n (-2) A531 Rn64 ltac:(clear - Hn2 Rn64; lia));
       unfold w64; f_equal; unfold rec_rem, rec_take; clear - Hn2; lia
     | rewrite denot_lit_U, (yr_U_off Ed 534%nat (d_cur cx n) 2 A534 Rcu ltac:(clear - Rcur2 C1 Rcu; lia));
       unfold w64; f_equal; unfold d_cur, rec_rem, rec_take; clear - Hn2; lia ] ]) in
let yr_k50 HS :=
  (yr_drop HS;
   yr_rg HS (25%bv : bv 5) Zg25; symmetry in Zg25;
   yr_bseat HS (25%bv : bv 5) 534%nat 561%nat (d_cur cx n) (rdb (rest_of (c_pl cx) n) 0) 0 A534 A561 Zg25 Hin0;
   paj_run_to_sh RUNTO HS HJ 0xa54;
   [ yr_awr
   | yr_meq;
     psrr_branch_pi RUNP BR HS;
     [ assert (Hn2 : 2 <= n)
         by (rewrite branch_ne_U, (U_atom Ed 531%nat n A531 Rn64), (U_lit Ed 1 ltac:(lia)) in Hc;
             apply negb_true_iff, Z.eqb_neq in Hc; clear - Hc Hn1; lia);
       clear Hc;
       assert (Rcur2 : d_cur cx n + 2 <= alloc_ceiling) by (unfold d_cur; clear - Hnc Hpc Hn2; lia);
       assert (Rin1 : c_p cx <= d_cur cx n + 1 < c_p cx + c_n cx)
         by (unfold d_cur; clear - Hn2 Hnc Hcn8; lia);
       assert (Hsh1 : aview SEGS (w_H W) mem3 (y_dsh_cell_addr (d_cur cx n + 1) + 0) =
                      Some (y_dsh_cell (c_p cx) (c_n cx) (d_cur cx n + 1)))
         by (rewrite Z.add_0_r;
             exact (y_dsh_cell_val B LAWS ly3 S3 W mem3 md3 (c_p cx) (c_n cx) (d_cur cx n + 1) GAR HinB Rin1));
       assert (Hin1 : aview SEGS (w_H W) mem3 (d_cur cx n + 1) = Some (rdb (rest_of (c_pl cx) n) 1))
         by exact (yr_in_val cx n W mem3 1%nat HINP Hplen ltac:(clear - Hn2; lia));
       paj_run_to_sh RUNTO HS HJ 0xd2c;
       [ yr_awr
       | yr_meq; psrr_branch_pi RUNP BR HS;
         [ clear Hc;
           paj_run_to_sh RUNTO HS HJ 0xd34;
           [ yr_awr
           | yr_meq; yr_drop HS;
             yr_rg HS (12%bv : bv 5) Zg12;
             rewrite (y_dsh_cell_denot Ed 534 562 1 (d_cur cx n) A534 ltac:(clear - Rcu; lia)
               ltac:(lia) ltac:(clear - Rcur C1; lia) A32 A562) in Zg12;
             symmetry in Zg12;
             yr_bseat HS (12%bv : bv 5) 562%nat 563%nat (y_dsh_cell_addr (d_cur cx n + 1))
               (y_dsh_cell (c_p cx) (c_n cx) (d_cur cx n + 1)) 0 A562 A563 Zg12 Hsh1;
             paj_run_to_sh RUNTO HS HJ 0xd40;
             [ yr_awr
             | yr_meq; psrr_branch_pi RUNP BR HS;
               [ clear Hc; yr_k40 HS
               | assert (Hsnz1 : y_dsh_cell (c_p cx) (c_n cx) (d_cur cx n + 1) <> 0)
                   by exact (yr_s8_ne Ed 563%nat (y_dsh_cell (c_p cx) (c_n cx) (d_cur cx n + 1)) A563
                     ltac:(clear - Rc1; lia) Hc);
                 clear Hc;
                 paj_run_to_sh RUNTO HS HJ 0xd40;
                 [ yr_awr
                 | yr_meq; psrr_branch_pi RUNP BR HS;
                   [ exfalso;
                     rewrite (yr_bge Ed (SAlu ALU_AND (SOff 534 1) (SLit 7)) (SExt true 8 (SOff 563 0))
                       ((d_cur cx n + 1) mod 8) (y_dsh_cell (c_p cx) (c_n cx) (d_cur cx n + 1))
                       (yr_and7 Ed 534%nat (d_cur cx n) 1 A534 Rcu ltac:(clear - Rcur C1; lia))
                       (yr_s8 Ed 563%nat (y_dsh_cell (c_p cx) (c_n cx) (d_cur cx n + 1)) A563
                          ltac:(clear - Rc1; lia))
                       ltac:(clear - Rcur C1 Rcu;
                             pose proof (Z.mod_pos_bound (d_cur cx n + 1) 8 ltac:(lia)); lia)
                       ltac:(clear - Rc1; lia)) in Hc;
                     apply negb_true_iff, Z.ltb_ge in Hc;
                     pose proof (y_dsh_cell_lt (c_p cx) (c_n cx) (d_cur cx n + 1) Hp8
                       ltac:(clear - Hcn8; lia) Rin1 Hsnz1) as Hlt1;
                     clear - Hc Hlt1; lia
                   | clear Hc;
                     paj_run_to_sh RUNTO HS HJ 0xd40; [ yr_awr | yr_meq; yr_k40 HS ] ] ] ] ] ]
         | exfalso;
           rewrite branch_ltu_U, (U_lit Ed 1 ltac:(lia)),
             (yr_U_off Ed 534%nat (d_cur cx n) 2 A534 Rcu ltac:(clear - Rcur2 C1 Rcu; lia)) in Hc;
           apply Z.ltb_ge in Hc; clear - Hc Rcur; lia ] ]
     | assert (Hne1 : n = 1)
         by (rewrite branch_ne_U, (U_atom Ed 531%nat n A531 Rn64), (U_lit Ed 1 ltac:(lia)) in Hc;
             apply negb_false_iff, Z.eqb_eq in Hc; exact Hc);
       clear Hc;
       paj_run_to_sh RUNTO HS HJ JOIN_OFF;
       [ yr_awr
       | yr_meq; yr_landt HS;
         [ rewrite (yr_u8_denot Ed 561%nat (rdb (rest_of (c_pl cx) n) 0) A561 Rb0); reflexivity
         | rewrite (yr_rdb_over (rest_of (c_pl cx) n) 1
             ltac:(rewrite (yr_rest_len (c_pl cx) n ltac:(clear - Hplen Hnc Hcn8 Rn; lia));
                   clear - Hne1; lia)); reflexivity
         | rewrite Hne1; reflexivity
         | rewrite denot_lit_U, (yr_U_off Ed 534%nat (d_cur cx n) 1 A534 Rcu ltac:(clear - Rcur C1; lia));
           unfold w64; f_equal; unfold d_cur, rec_rem, rec_take; clear - Hne1; lia ] ] ] ]) in
psrr_branch_pi RUNP BR HS;
[ assert (Hn0 : n = 0)
    by (rewrite branch_eq_U, (U_atom Ed 531%nat n A531 Rn64), (U_lit Ed 0 ltac:(lia)) in Hc;
        apply Z.eqb_eq in Hc; exact Hc);
  clear Hc;
  paj_run_to_sh RUNTO HS HJ JOIN_OFF;
  [ yr_awr
  | yr_meq; yr_landt HS;
    [ rewrite Hn0, yr_rest0, (yr_rdb_over [] 0 ltac:(cbn [length]; lia)); reflexivity
    | rewrite Hn0, yr_rest0, (yr_rdb_over [] 1 ltac:(cbn [length]; lia)); reflexivity
    | rewrite Hn0; reflexivity
    | rewrite (DX 3%nat 534%nat eq_refl ltac:(lia)), Hn0; reflexivity ] ]
| assert (Hn1 : 1 <= n)
    by (rewrite branch_eq_U, (U_atom Ed 531%nat n A531 Rn64), (U_lit Ed 0 ltac:(lia)) in Hc;
        apply Z.eqb_neq in Hc; clear - Hc Rn; lia);
  clear Hc;
  destruct (yr_blk cx h n ly3 S3 W mem3 HB HBD Hn1) as (Hcn8 & Hnc & Hp4096 & Hp8 & Hpc & Hplen & HinB);
  assert (Rcur : 4103 <= d_cur cx n /\ d_cur cx n + 1 <= alloc_ceiling)
    by (unfold d_cur; clear - Hnc Hp4096 Hpc Hn1; lia);
  assert (Rcu : 0 <= d_cur cx n < 2 ^ 64) by (clear - Rcur C1; lia);
  assert (RS0 : 0 <= y_dsh_cell_addr (d_cur cx n) < 2 ^ 64)
    by (unfold y_dsh_cell_addr; apply y_shaddr_range; exact Rcu);
  assert (RS1 : 0 <= y_dsh_cell_addr (d_cur cx n + 1) < 2 ^ 64)
    by (unfold y_dsh_cell_addr; apply y_shaddr_range; clear - Rcur C1; lia);
  pose proof (y_dsh_cell_range (c_p cx) (c_n cx) (d_cur cx n)) as Rc0;
  pose proof (y_dsh_cell_range (c_p cx) (c_n cx) (d_cur cx n + 1)) as Rc1;
  assert (Rin0 : c_p cx <= d_cur cx n < c_p cx + c_n cx) by (unfold d_cur; clear - Hn1 Hnc Hcn8; lia);
  assert (Hsh0 : aview SEGS (w_H W) mem3 (y_dsh_cell_addr (d_cur cx n) + 0) =
                 Some (y_dsh_cell (c_p cx) (c_n cx) (d_cur cx n)))
    by (rewrite Z.add_0_r;
        exact (y_dsh_cell_val B LAWS ly3 S3 W mem3 md3 (c_p cx) (c_n cx) (d_cur cx n) GAR HinB Rin0));
  assert (Hin0 : aview SEGS (w_H W) mem3 (d_cur cx n + 0) = Some (rdb (rest_of (c_pl cx) n) 0))
    by exact (yr_in_val cx n W mem3 0%nat HINP Hplen ltac:(clear - Hn1; lia));
  paj_run_to_sh RUNTO HS HJ 0xa44;
  [ yr_awr
  | yr_meq;
    psrr_branch_pi RUNP BR HS;
    [ clear Hc;
      paj_run_to_sh RUNTO HS HJ 0xa44;
      [ yr_awr
      | yr_meq;
      yr_rg HS (11%bv : bv 5) Zg11;
      rewrite (y_dsh_cell_denot Ed 534 559 0 (d_cur cx n) A534 ltac:(clear - Rcu; lia) ltac:(lia)
        ltac:(clear - Rcur C1; lia) A32 ltac:(rewrite Z.add_0_r; exact A559)) in Zg11;
      symmetry in Zg11;
      yr_bseat HS (11%bv : bv 5) 559%nat 560%nat (y_dsh_cell_addr (d_cur cx n))
        (y_dsh_cell (c_p cx) (c_n cx) (d_cur cx n)) 0 A559 A560 Zg11 Hsh0;
      paj_run_to_sh RUNTO HS HJ 0xa50;
      [ yr_awr
      | yr_meq; psrr_branch_pi RUNP BR HS;
        [ clear Hc; yr_k50 HS
        | assert (Hsnz0 : y_dsh_cell (c_p cx) (c_n cx) (d_cur cx n) <> 0)
            by exact (yr_s8_ne Ed 560%nat (y_dsh_cell (c_p cx) (c_n cx) (d_cur cx n)) A560
              ltac:(clear - Rc0; lia) Hc);
          clear Hc;
          assert (HU7 : U Ed (SAlu ALU_AND (SOff 534 0) (SLit 7)) = d_cur cx n mod 8)
            by (rewrite (yr_and7 Ed 534%nat (d_cur cx n) 0 A534 Rcu ltac:(clear - Rcu; lia)); f_equal; lia);
          paj_run_to_sh RUNTO HS HJ 0xa50;
          [ yr_awr
          | yr_meq; psrr_branch_pi RUNP BR HS;
            [ exfalso;
              rewrite (yr_bge Ed (SAlu ALU_AND (SOff 534 0) (SLit 7)) (SExt true 8 (SOff 560 0))
                (d_cur cx n mod 8) (y_dsh_cell (c_p cx) (c_n cx) (d_cur cx n)) HU7
                (yr_s8 Ed 560%nat (y_dsh_cell (c_p cx) (c_n cx) (d_cur cx n)) A560 ltac:(clear - Rc0; lia))
                ltac:(clear - Rcu; pose proof (Z.mod_pos_bound (d_cur cx n) 8 ltac:(lia)); lia)
                ltac:(clear - Rc0; lia)) in Hc;
              apply negb_true_iff, Z.ltb_ge in Hc;
              pose proof (y_dsh_cell_lt (c_p cx) (c_n cx) (d_cur cx n) Hp8 ltac:(clear - Hcn8; lia) Rin0 Hsnz0)
                as Hlt0;
              clear - Hc Hlt0; lia
            | clear Hc;
              paj_run_to_sh RUNTO HS HJ 0xa50; [ yr_awr | yr_meq; yr_k50 HS ] ] ] ] ] ]
    | exfalso;
      rewrite branch_ltu_U, (U_lit Ed 1 ltac:(lia)),
        (yr_U_off Ed 534%nat (d_cur cx n) 1 A534 Rcu ltac:(clear - Rcur C1; lia)) in Hc;
      apply Z.ltb_ge in Hc; clear - Hc Rcur; lia ] ] ].
Qed.

End g.
End h.
End f.
End d.
