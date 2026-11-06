(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 463 of its 496 lines of code are new or changed and 36 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntHdrLib.v; 288 of its 341 lines of code are new or changed and 443 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3TailT1.v, with its module paths, addresses and numbers changed; 31 of its 342 lines of code are new or changed and 30 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YRo YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoArm3 DiscoArm3TailDefs DiscoYEntBodyStmt DiscoYEntSeatStmt DiscoArm3TailK.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Ltac t1_ne := let E := fresh in intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E.
Ltac t1_in := repeat (first [left; reflexivity | right]).
Ltac t1_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.

Definition t1_ss0 : sstate := mkSS 0x2264 sr_atoms [] None (mkFacts [] [] []).
Definition t1_ss1 : sstate := setreg t1_ss0 1 (codeptr 0x2268) 0x2268.

Lemma t1_pres : forall (regs regs' : bvmap 5 word) (r : bv 5),
  aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof.
  intros regs regs' r HP Hr. pose proof (HP _ Hr) as X. rewrite Z_to_bv_bv_unsigned in X. exact X.
Qed.

Lemma t1_mod8 : forall s, s mod 16 = 0 -> s mod 8 = 0.
Proof.
  intros s Hs. apply Z.mod_divide in Hs; [|lia]. apply Z.mod_divide; [lia|].
  destruct Hs as [q Hq]. exists (2 * q). lia.
Qed.

Lemma t1_mod16 : forall a s, a mod 32 = 0 -> s mod 16 = 0 -> (a - s) mod 16 = 0.
Proof.
  intros a s Ha Hs. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hs; [|lia]. apply Z.mod_divide; [lia|].
  destruct Ha as [p Hp], Hs as [q Hq]. exists (2 * p - q). lia.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma t1_step : sym_step_pi (ptree_of_list lib_both3_0_listing) t1_ss0 = PCallx AS_free t1_ss1.
Proof. rewrite pl_tpi_eq. vm_compute. reflexivity. Qed.

Lemma t1_sav : forall (cx : dcx) (E : env) (W : world SEGS) (mem : word -> option byte) (off : Z) (n : nat) (r : bv 5),
  d_E cx E ->
  region_ok SEGS E (rd W mem) (YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks) ->
  In (YP09.mkChunk off (CVal 8 (SOff n 0))) dsave_chunks -> Z.of_nat n = bv_unsigned r ->
  rdword (aview SEGS (w_H W) mem) (d_S cx + off) = Some (bv_unsigned (getr (c_regs cx) r)).
Proof.
  intros cx E W mem off n r (EE & _) (_ & _ & _ & Hcs) Hin Hn.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. cbn [YP09.r_base base_val] in Hck.
  rewrite (EE AT_STK (2%bv : bv 5) eq_refl) in Hck.
  pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) r)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
  apply rdword_of_val_mem; [|exact Hr].
  change 8%nat with (N.to_nat 8).
  apply (val_of_chunk_ok SEGS E _ _ off 8 (SOff n 0) _ Hck).
  - cbn [sv_denot]. rewrite (EE n r Hn), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hr.
  - cbn. lia.
Qed.

Lemma t1_rok : forall (E : env) (m m' : word -> option byte) (r : YP09.region),
  region_ok SEGS E m r ->
  forallb (fun c => match YP09.c_val c with CData _ _ _ => false | _ => true end) (r_chunks r) = true ->
  forallb (chunk_inside r) (r_chunks r) = true ->
  (forall a, base_val E (r_base r) + r_lo r <= a < base_val E (r_base r) + r_hi r -> mbyte SEGS m' a = mbyte SEGS m a) ->
  (forall a, base_val E (r_base r) + r_wlo r <= a < base_val E (r_base r) + r_whi r -> writable_at SEGS m' a) ->
  region_ok SEGS E m' r.
Proof.
  intros E m m' r HR Hnc Hci K1 K2.
  apply (region_ok_transport SEGS E E m m' r HR eq_refl); [| exact K1 | intros a Ha _; exact (K2 a Ha) | exact Hci].
  intros c Hc. pose proof (proj1 (forallb_forall _ _) Hnc c Hc) as Hcc. cbn beta in Hcc.
  destruct (YP09.c_val c); [reflexivity | exact I | exact I | discriminate Hcc].
Qed.

Lemma t1_frame : forall (cx : dcx) (h : Z) (shf : Z -> Z) (W : world SEGS) (m : word -> option byte)
  (W2 : world SEGS) (m2 : word -> option byte),
  d_frame cx h shf W m ->
  0 <= d_A cx -> d_A cx + 472 <= 2 ^ 64 -> 0 <= d_FB cx -> d_FB cx + 4096 <= 2 ^ 64 ->
  0 <= shadow_addr (d_FB cx) -> shadow_addr (d_FB cx) + 512 <= 2 ^ 64 ->
  (forall a, d_S cx - 104 <= a < d_S cx -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a) ->
  (forall a, d_A cx <= a < d_A cx + 472 -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a /\ apresent (w_H W2) m2 a) ->
  (forall a, d_FB cx <= a < d_FB cx + 4096 -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a /\ apresent (w_H W2) m2 a) ->
  (forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 ->
     aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a /\ apresent (w_H W2) m2 a) ->
  d_frame cx h shf W2 m2.
Proof.
  intros cx h shf W m W2 m2 HFR A0 A1 F0 F1 S0 S1 K1 K2 K3 K4.
  pose proof (d_hslots_of_frame cx h shf W m HFR) as HSL.
  destruct HFR as (E & HE & HR & HFL & _).
  pose proof HE as (EE & _ & _ & E60 & EF & ESH).
  assert (B2 : base_val E (Some AT_STK) = d_S cx) by (cbn [base_val]; rewrite (EE AT_STK (2%bv : bv 5) eq_refl); reflexivity).
  assert (B60 : base_val E (Some AT_A) = d_A cx) by (cbn [base_val]; rewrite E60; unfold w64; apply unsigned_lit_small; lia).
  assert (BF : base_val E (Some AT_F) = d_FB cx) by (cbn [base_val]; rewrite EF; unfold w64; apply unsigned_lit_small; lia).
  assert (BSH : base_val E (Some AT_SH) = shadow_addr (d_FB cx))
    by (cbn [base_val]; rewrite ESH; unfold w64; apply unsigned_lit_small; lia).
  exists E. split; [exact HE|]. split; [|split].
  - rewrite Forall_forall in HR |- *. intros r Hr. pose proof (HR r Hr) as Hro.
    unfold d_regions in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]].
    + apply (t1_rok E _ _ _ Hro); [vm_compute; reflexivity | vm_compute; reflexivity | |];
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite B2; intros a Ha;
        [apply mbyte_of_aview; apply K1; lia | lia].
    + apply (t1_rok E _ _ _ Hro); [vm_compute; reflexivity | vm_compute; reflexivity | |];
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite B60; intros a Ha;
        [apply mbyte_of_aview; apply (proj1 (K2 a ltac:(lia))) | apply apresent_writable; apply (proj2 (K2 a ltac:(lia)))].
    + apply (t1_rok E _ _ _ Hro); [vm_compute; reflexivity | vm_compute; reflexivity | |];
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite BF; intros a Ha;
        change (fs_frame_bytes DFRAME_CLASS) with 4096 in Ha; unfold DFRAME_SIZE in Ha;
        [apply mbyte_of_aview; apply (proj1 (K3 a ltac:(lia))) | apply apresent_writable; apply (proj2 (K3 a ltac:(lia)))].
    + apply (t1_rok E _ _ _ Hro); [vm_compute; reflexivity | vm_compute; reflexivity | |];
        cbn [fshadow_region YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite BSH; intros a Ha;
        change (fs_frame_bytes DFRAME_CLASS / 8) with 512 in Ha; unfold DFRAME_SH in Ha;
        [apply mbyte_of_aview; apply (proj1 (K4 a ltac:(lia))) | apply apresent_writable; apply (proj2 (K4 a ltac:(lia)))].
  - rewrite <- HFL. apply rdword_ext. intros q Hq.
    refine (proj1 (K3 _ _)). change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
  - apply (d_hslots_kept cx h W W2 m m2); [intros a Ha; exact (proj1 (K2 a ltac:(lia))) | exact HSL].
Qed.

Lemma t1_shadow : forall (cx : dcx) (shf : Z -> Z) (W : world SEGS) (m : word -> option byte)
  (W2 : world SEGS) (m2 : word -> option byte),
  d_shadow cx shf W m ->
  (forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 -> aview SEGS (w_H W2) m2 a = aview SEGS (w_H W) m a) ->
  d_shadow cx shf W2 m2.
Proof.
  intros cx shf W m W2 m2 HS K q Hq. unfold DFRAME_SH in Hq. rewrite K by lia. apply HS. unfold DFRAME_SH. exact Hq.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis MT_TRIV : MT = ameter_triv.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : forall fq : YK11.FPState, afree_realizes (fx := fq) SEGS B.
Hypothesis DUNIV : duniv_ok B.
Hypothesis DROH : d_ro_hyps B.
Hypothesis DBFREE : d_body_free_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DCAN : d_can_hyps B tfib_K.

Theorem a3t_T1 : a3t_1_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros cx h i n now op W0 c0 T0 T1 buf W c [_ HAT].
  destruct HAT as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & HFRM & HBASE & HJ & HFRS & Hk & Hnev & HMLE & Hacc & HP).
  destruct HP as (Hi & Hn & Hnow & HRL & HR24 & (HSP1 & _) & HSP0 & HBODY).
  pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs3 & Rs2 & Rs4 & Rs11).
  pose proof HBASE as ((HPRE & Hra0 & _ & _ & _ & _ & _ & _ & Hev0 & _) & _).
  pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk0 & _ & Hach0 & _).
  pose proof Hstk0 as (_ & _ & _ & _ & _ & H47 & _ & HtopS & Htophi).
  pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & _ & Hnev3 & _ & HJk & _).
  pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k (conj HBASE (conj HJ HFRS)))
    as (Hal16 & HSlo & HShi & HF0 & HFc & HFia & HFo & HF32 & HFpres & HSpres & HWpres & _ & Hfin & EFA3 & _).
  pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HA1 & HA2).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold MFRAME, LLVMF_STK in HSlo, HA1, HWpres, HJk.
  pose proof pa_B_ok as (HB0 & HB1 & HB4).
  pose proof (pal_rt_below B PAL) as (Hrt & _).
  pose proof HBODY as (T & G & Lk & H & HFR & HSH & _ & HBLK & _).
  pose proof HBLK as (HPm & HFa & _ & _).
  set (nb := Z.max (slot_ser_defs.ser_cap op) 1).
  assert (Hin : In (buf, nb) (ablocks B ly3 S3)) by (apply (Permutation_in _ (Permutation_sym HPm)); left; reflexivity).
  set (regs1 := regupd regs 10 (w64 buf)).
  set (ms1 := YK11.mkst (fx := fq) regs1 (Z_to_bv 64 (BASE + 0x2264)) mem3 (YK11.seg_rom SEGS)).
  assert (F1 : fetch_word SEGS (Z_to_bv 64 (BASE + 0x2260)) = Some (Z_to_bv 32 0xc0513))
    by (apply pa_fetch_pw; vm_compute; reflexivity).
  assert (X1 : is_ecall (Z_to_bv 32 0xc0513) = false) by (vm_compute; reflexivity).
  assert (D1 : decode_any (Z_to_bv 32 0xc0513) = Some (OpImm ALU_ADD 10 24 0, 4%Z)) by vm_refl_bv.
  assert (S1 : RiscvSemantics.step SEGS (restrict (w_H W) (YK11.mkst (fx := fq) regs (w64 (BASE + R14X_OFF)) mem3
      (YK11.seg_rom SEGS))) = MachineOk (restrict (w_H W) ms1)).
  { unfold ms1, regs1. rewrite !restrict_mkst_fx. unfold w64, R14X_OFF.
    rewrite (YK11.step_addi (fx := fq) SEGS regs _ _ _ _ _ _ _ F1 X1 D1).
    change (bv_eqb (10%bv : bv 5) 0%bv) with false. cbv iota.
    change (bv_signed (0%bv : bv 12)) with 0. rewrite HR24. unfold v_addi, w64.
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia.
    replace (BASE + 0x2260 + 4) with (BASE + 0x2264) by lia. reflexivity. }
  set (E1 := Eimg (Ereg regs1 [])).
  assert (HEI : img_env VAL A_LIM E1) by apply Eimg_env.
  assert (HS1 : st_ok_pi SEGS VAL E1 t1_ss0 (restrict (w_H W) ms1)).
  { unfold ms1, t1_ss0. rewrite restrict_mkst_fx.
    apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
  destruct (sym_step_pi_call asym SEGS (clookup pa_tbl) VAL SIGMA lib_both3_0_listing (fx := fq) pa_fetch_ok pa_cert A_LIM A_LIM_text
    E1 t1_ss0 t1_ss1 AS_free (restrict (w_H W) ms1) HEI HS1 t1_step)
    as (ms2 & Hstep2 & HS2 & Hmem2 & _).
  assert (Hms : msteps SEGS (restrict (w_H W) (YK11.mkst (fx := fq) regs (w64 (BASE + R14X_OFF)) mem3 (YK11.seg_rom SEGS))) ms2).
  { eapply mst_step; [reflexivity | exact S1 |]. eapply mst_step; [reflexivity | exact Hstep2 | apply mst_refl]. }
  unfold cfg_at. apply (SRr_msteps SEGS pa_wx W _ ms2 md3 _ Hms). intros model' Hsame _.
  cbn [ms_mem YK11.mkst].
  pose proof (st_ok_mkst SEGS E1 _ ms2 HS2 eq_refl) as Hsh.
  cbn [ss_pc setpc] in Hsh. rewrite Hmem2 in Hsh. unfold ms1 in Hsh. rewrite restrict_mkst_fx in Hsh.
  cbn [ms_mem YK11.mkst] in Hsh.
  rewrite Hsh, unrestrict_mkst_mrestrict, (pal_free B PAL).
  set (regsT := ms_regs ms2) in *.
  assert (HA1' : env_agree 32 (Ereg regs1 []) E1) by (split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  pose proof (regs_kept_of_st_ok SEGS E1 _ ms2 regs1 []
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 10%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv]
    HS2 HA1' ltac:(vm_compute; reflexivity)) as RK.
  assert (T2 : getr regsT 2 = getr regs 2) by (unfold regsT; rewrite (RK 2%bv ltac:(t1_in)); unfold regs1; apply getr_other; t1_ne).
  assert (T3 : getr regsT 3 = getr regs 3) by (unfold regsT; rewrite (RK 3%bv ltac:(t1_in)); unfold regs1; apply getr_other; t1_ne).
  assert (T4 : getr regsT 4 = getr regs 4) by (unfold regsT; rewrite (RK 4%bv ltac:(t1_in)); unfold regs1; apply getr_other; t1_ne).
  assert (T8 : getr regsT 8 = getr regs 8) by (unfold regsT; rewrite (RK 8%bv ltac:(t1_in)); unfold regs1; apply getr_other; t1_ne).
  assert (T9 : getr regsT 9 = getr regs 9) by (unfold regsT; rewrite (RK 9%bv ltac:(t1_in)); unfold regs1; apply getr_other; t1_ne).
  assert (T18 : getr regsT 18 = getr regs 18) by (unfold regsT; rewrite (RK 18%bv ltac:(t1_in)); unfold regs1; apply getr_other; t1_ne).
  assert (T19 : getr regsT 19 = getr regs 19) by (unfold regsT; rewrite (RK 19%bv ltac:(t1_in)); unfold regs1; apply getr_other; t1_ne).
  assert (T20 : getr regsT 20 = getr regs 20) by (unfold regsT; rewrite (RK 20%bv ltac:(t1_in)); unfold regs1; apply getr_other; t1_ne).
  assert (T27 : getr regsT 27 = getr regs 27) by (unfold regsT; rewrite (RK 27%bv ltac:(t1_in)); unfold regs1; apply getr_other; t1_ne).
  assert (T10 : getr regsT 10 = w64 buf) by (unfold regsT; rewrite (RK 10%bv ltac:(t1_in)); unfold regs1; apply getr_same; t1_ne).
  assert (T1r : getr regsT 1 = Z_to_bv 64 (BASE + 0x2268)).
  { unfold regsT. rewrite (st_ok_reg SEGS E1 _ ms2 1 HS2). rewrite <- (codeptr_val E1 0x2268 HEI). f_equal. }
  assert (HspT : spZ regsT = d_A cx) by (unfold spZ; rewrite T2; exact Rsp).
  assert (Hs0T : s0Z regsT = d_S cx) by (unfold s0Z; rewrite T8, Rs0; unfold w64; apply unsigned_lit_small; lia).
  assert (HraT : raZ regsT = BASE + 0x2268) by (unfold raZ; rewrite T1r; apply unsigned_lit_small; lia).
  assert (HJ' : ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 model' k).
  { exact (ajournal_exec SEGS B LAWS pa_segs_low LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W mem3 md3 k mem3 model' (fun _ => False) HJ (fun x _ => eq_refl)
      (mem_grows_refl _) (fun x _ => eq_refl) Hsame (fun a (Hf : False) => False_ind _ Hf)). }
  pose proof HFR as (Ef & HEf & HRf & _).
  unfold d_regions in HRf. pose proof (Forall_inv HRf) as Rstk.
  assert (H8 : rdword (aview SEGS (w_H W) mem3) (d_S cx - 8) = Some RA_LLVMF).
  { replace (d_S cx - 8) with (d_S cx + -8) by lia.
    rewrite (t1_sav cx Ef W mem3 (-8) 1 1%bv HEf Rstk
      ltac:(apply (proj2 (in_map_iff _ _ _)); exists 0%nat; split; [reflexivity | apply in_seq; cbn; lia]) eq_refl).
    f_equal. exact Hra0. }
  assert (H16 : rdword (aview SEGS (w_H W) mem3) (d_S cx - 16) = Some (s0Z (c_regs cx))).
  { replace (d_S cx - 16) with (d_S cx + -16) by lia.
    exact (t1_sav cx Ef W mem3 (-16) 8 8%bv HEf Rstk
      ltac:(apply (proj2 (in_map_iff _ _ _)); exists 1%nat; split; [reflexivity | apply in_seq; cbn; lia]) eq_refl). }
  assert (Hrd : forall a, d_S cx <= a < 2 ^ 64 -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H (c_W cx)) (c_mem cx) a)
    by (intros a Ha; apply HJk; unfold LLVMF_STK in *; lia).
  assert (HCH : exists ch, chain_pre ly3 (aview SEGS (w_H W) mem3) regsT ch /\
    In (call_trace0 (pc_free_ra0 (as_code B)) regsT ch) (as_universe B)).
  { destruct (Z_lt_ge_dec (d_S cx) (ly_top (c_ly cx) - 16)) as [Htop | Htop].
    - exists [(d_S cx, RA_LLVMF, s0Z (c_regs cx))]. split.
      + apply (achain_chain_pre ly3 _ (d_A cx) (d_S cx)); [| lia | exact Hs0T | rewrite HraT; lia].
        apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop).
        apply (achain_push (c_ly cx) (aview SEGS (w_H (c_W cx)) (c_mem cx)) _ (d_S cx) (s0Z (c_regs cx)) RA_LLVMF [] (d_A cx)
          Hach0 ltac:(lia) Hrd H8 H16); first [exact (t1_mod8 _ Hal16) | unfold RA_LLVMF; lia].
      + apply DUNIV. unfold call_trace0, unwind_of_chain. cbn [flat_map app]. rewrite HraT.
        rewrite (proj2 (Z.eqb_neq (BASE + 0x2268) (pc_free_ra0 (as_code B))) ltac:(lia)).
        unfold d_sites. destruct (RA_LLVMF =? pc_free_ra0 (as_code B)); cbn [app firstn]; t1_in.
    - exists []. split.
      + apply (achain_chain_pre ly3 _ (d_A cx) (d_S cx)); [| lia | exact Hs0T | rewrite HraT; lia].
        left. split; [right; left; rewrite Etop; lia | reflexivity].
      + apply DUNIV. unfold call_trace0, unwind_of_chain. cbn [flat_map app]. rewrite HraT.
        rewrite (proj2 (Z.eqb_neq (BASE + 0x2268) (pc_free_ra0 (as_code B))) ltac:(lia)).
        unfold d_sites. cbn [app firstn]. t1_in. }
  destruct HCH as (ch & Hch & Htr).
  assert (HFP : In (buf, nb) (ablocks B (c_ly cx) (c_S cx)) -> forall q, 0 <= q < req_size nb -> inFP [] (buf + q)).
  { intros Hin0. exfalso. exact (proj1 (Forall_forall _ _) HFa (buf, nb) (or_intror (or_introl eq_refl)) Hin0). }
  eapply SRr_mono.
  { exact (aj_free_at SEGS B LAWS pa_segs_low (pal_env B PAL) ML (AFREE fq) W regsT mem3 LLVMF_STK (d_S cx) []
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(DFRAME_CLASS, c_fpos cx)] ly3 S3 model' k buf nb
      (d_A cx - d_S cx) (Z_to_bv 64 (BASE + 0x2268)) ch HJ' Hin T10 ltac:(rewrite HspT; lia) (t1_mod16 _ _ HA2 Hal16) ltac:(lia)
      ltac:(unfold ASTACK, LLVMF_STK, MFRAME in *; lia) ltac:(rewrite T3; exact Rgp) ltac:(rewrite T4; exact Rtp) T1r
      (ret_ok_codeptr_v 0x2268 ltac:(lia) eq_refl)
      ltac:(unfold EV_HEAD, EV_PRO, EV_ITER, EV_LIB, EV_MAX, MAX_OPS in *; lia) Hch Htr HFP). }
  intros W2 c2 HwleW (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & EL1 & EL2) & Hfr2 & HK).
  destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (HC2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly2 S2 W2 mem2 md2 (k + 1))
    by (split; [exact HBASE | split; [exact HJ2 | rewrite Hfr2; exact HFRS]]).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly2 S2 W2 mem2 md2 (k + 1) HC2)
    as (_ & _ & _ & _ & _ & _ & _ & _ & HFpres2 & HSpres2 & HWpres2 & _).
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 model' buf nb DFRAME_CLASS (c_fpos cx) (proj1 HJ') Hin Hfin) as Hdisj.
  destruct (al_blocks SEGS B LAWS ly3 S3 W mem3 model' buf nb (proj1 HJ') Hin) as (_ & _ & _ & Hbapp & _).
  unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj. rewrite EFA3 in Hdisj. change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hdisj.
  destruct (shadow_addr_bounds (d_FB cx) ltac:(lia)) as (Hsb1 & Hsb2).
  destruct (shadow_addr_bounds (d_FB cx + 4096) ltac:(lia)) as (Hsb3 & Hsb4).
  pose proof (shadow_range_end (d_FB cx) 4096 ltac:(lia)) as Hsre. change (4096 / 8) with 512 in Hsre.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  assert (KSTK : forall a, d_S cx - 104 <= a < d_S cx -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a)
    by (intros a Ha; apply K1; unfold ASTACK, MFRAME, LLVMF_STK in *; lia).
  assert (KA : forall a, d_A cx <= a < d_A cx + 472 ->
      aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a /\ apresent (w_H W2) mem2 a).
  { intros a Ha. split; [apply K1; unfold ASTACK, MFRAME, LLVMF_STK in *; lia | apply HWpres2; unfold MFRAME, LLVMF_STK in *; lia]. }
  assert (KF : forall a, d_FB cx <= a < d_FB cx + 4096 ->
      aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a /\ apresent (w_H W2) mem2 a).
  { intros a Ha. split; [|exact (HFpres2 a Ha)].
    apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS) with 4096. lia.
    - intros Hb. lia. }
  assert (KS : forall a, shadow_addr (d_FB cx) <= a < shadow_addr (d_FB cx) + 512 ->
      aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem3 a /\ apresent (w_H W2) mem2 a).
  { intros a Ha. split.
    - apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin).
      + right. unfold in_zr. cbn [fst snd]. rewrite EFA3. change (fs_frame_bytes DFRAME_CLASS / 8) with 512. lia.
      + intros Hb. lia.
    - replace a with (shadow_addr (d_FB cx) + (a - shadow_addr (d_FB cx))) by lia. apply HSpres2. lia. }
  assert (HFR2 : d_frame cx h dsh_loop W2 mem2).
  { apply (t1_frame cx h dsh_loop W mem3 W2 mem2 HFR).
    all: first [exact KSTK | exact KA | exact KF | exact KS | unfold MFRAME, LLVMF_STK in *; lia]. }
  assert (HSH2 : d_shadow cx dsh_loop W2 mem2) by exact (t1_shadow cx dsh_loop W mem3 W2 mem2 HSH (fun a Ha => proj1 (KS a Ha))).
  assert (VK : forall off v, 0 <= off -> off + 8 <= 472 ->
      val_mem SEGS (rd W mem3) (d_A cx + off) 8 v -> val_mem SEGS (rd W2 mem2) (d_A cx + off) 8 v).
  { intros off v Ho1 Ho2 Hv. apply (val_mem_kept SEGS (w_H W) (w_H W2) mem3 mem2 _ 8 v); [|exact Hv].
    intros q Hq. refine (proj1 (KA _ _)). lia. }
  assert (HBODY2 : d_body B cx h n [] dsh_loop ly2 S2 W2 mem2).
  { refine (DBFREE LAWS DROH DCAN cx h n [] [] (a3_xb buf op) dsh_loop dsh_loop ly3 S3 W mem3 model' k ly2 S2 W2 mem2 md2 (k + 1)
      (d_S cx + (d_A cx - d_S cx) - ASTACK) (d_S cx + (d_A cx - d_S cx)) l1 l2 HBODY (conj HBASE HJ') (conj HBASE HJ2)
      ltac:(cbn; lia) ltac:(unfold ASTACK, LLVMF_STK; lia) ltac:(lia) EL1 EL2 _ HFR2 HSH2).
    eapply acall_kept_mono_E; [exact (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 K6))))) |].
    intros a Ha. exists buf, nb. split; [left; reflexivity | exact Ha]. }
  pose proof HSP1 as ((HV208 & HV320) & HV192 & HV200).
  unfold a3t_f, a3t_at, d_arm_at, d_at.
  exists fq, ly2, S2, regs2, mem2, md2, (k + 1), (ACC_HEAD MT (i + 1)).
  split; [unfold cfg_at, w64, F_OFF; reflexivity|]. split; [exact HFRM|].
  split; [exact HBASE|]. split; [exact HJ2|]. split; [rewrite Hfr2; exact HFRS|].
  split; [rewrite <- (a3t_ev i); lia|].
  split; [pose proof HJ2 as (_ & _ & _ & _ & _ & _ & Hnev2 & _); rewrite <- (a3t_ev i); lia|].
  split; [rewrite MT_TRIV; exact I|]. split; [lia|].
  split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split.
  { split; [unfold spZ; rewrite (t1_pres regsT regs2 2%bv HP2 ltac:(t1_cs)); exact HspT|].
    split; [rewrite (t1_pres regsT regs2 3%bv HP2 ltac:(t1_cs)), T3; exact Rgp|].
    split; [rewrite (t1_pres regsT regs2 4%bv HP2 ltac:(t1_cs)), T4; exact Rtp|].
    split; [rewrite (t1_pres regsT regs2 8%bv HP2 ltac:(t1_cs)), T8; exact Rs0|].
    split; [rewrite (t1_pres regsT regs2 9%bv HP2 ltac:(t1_cs)), T9; exact Rs1|].
    split; [rewrite (t1_pres regsT regs2 19%bv HP2 ltac:(t1_cs)), T19; exact Rs3|].
    split; [rewrite (t1_pres regsT regs2 18%bv HP2 ltac:(t1_cs)), T18; exact Rs2|].
    split; [rewrite (t1_pres regsT regs2 20%bv HP2 ltac:(t1_cs)), T20; exact Rs4|].
    rewrite (t1_pres regsT regs2 27%bv HP2 ltac:(t1_cs)), T27; exact Rs11. }
  split; [exact I|].
  split; [split; [split; [apply VK; [lia | lia | exact HV208] | apply VK; [lia | lia | exact HV320]] |
    split; [apply VK; [lia | lia | exact HV192] | apply VK; [lia | lia | exact HV200]]]|].
  split; [split; [apply VK; [lia | lia | exact HV208] | apply VK; [lia | lia | exact HV320]]|].
  exact HBODY2.
Qed.

End h.
End f.
End d.
