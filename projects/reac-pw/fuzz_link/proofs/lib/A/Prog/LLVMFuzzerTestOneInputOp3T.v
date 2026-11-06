(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 344 of its 391 lines of code are new or changed and 1285 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_unmark arm, the middle of one turn of the per-mark loop
   the end of one turn of the per-mark loop (+0x838 .. +0x8d0): the frame object F + 0x20 out of scope again
   (shadow 0xf8), n_mark reloaded, and the loop test, to u_l_inv (j + 1) or u_x_inv.
   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputArmW LLVMFuzzerTestOneInputLp
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputOp3Lib LLVMFuzzerTestOneInputOp3Cut
  LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputMb LLVMFuzzerTestOneInputMdl LLVMFuzzerTestOneInputOp3K
  LLVMFuzzerTestOneInputArmK LLVMFuzzerTestOneInputOp3B LLVMFuzzerTestOneInputOp3C
  LLVMFuzzerTestOneInputOp3W.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c model_write_c LinkWalkBcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.


Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LV : LinkVals (L := link_listing).
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

Definition LU_mr : Z := AF_LLVMFuzzerTestOneInput + 0x808.   (* 0x82fdc, model_read's return *)

(* the runner's state at the loop head: the frame's shadow, its window the 32 bytes of F + 0x20 *)
Definition u_fs_rg : YP09.region := YP09.mkRegion (Some 19%nat) 0 112 4 36 [].
Definition u_l_facts : facts := mkFacts [(19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 0xffffff00000) 2)] [] [].
Definition u_l_ss : sstate := mkSS LU_body sr_atoms [u_fs_rg] None u_l_facts.

(* the frame's shadow with the object F + 0x20 in scope *)
Definition u_tsh_rg : YP09.region := YP09.mkRegion (Some 19%nat) 0 112 4 36 [].
Definition u_tmsh_rg : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (CZero 1)].
Definition u_tnm_rg : YP09.region := YP09.mkRegion (Some 21%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition u_t_facts : facts :=
  mkFacts [(19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 0xffffff00000) 2); (20%nat, mkAF 0 31 0);
           (21%nat, mkAF 4096 (2 ^ 47) 2); (32%nat, mkAF 0 32 0)] [] [].
Definition u_t_ss : sstate := mkSS LU_join sr_atoms [u_tsh_rg; u_tmsh_rg; u_tnm_rg] None u_t_facts.

(* a byte a run stored as the low byte of a value *)
Lemma u_byte_sv : forall (E : env) H (mem : word -> option byte) r base off e z,
  region_ok SEGS E (mrestrict H mem) r -> base_val E (YP09.r_base r) = base ->
  In (YP09.mkChunk off (CVal 1 e)) (YP09.r_chunks r) -> bv_unsigned (sv_denot E e) mod 256 = z ->
  aview SEGS H mem (base + off) = Some z.
Proof.
  intros E H mem r base off e z (_ & _ & _ & HC) Hb Hin Hz.
  rewrite Forall_forall in HC. specialize (HC _ Hin). rewrite Hb in HC.
  destruct (HC 0 ltac:(cbn; lia)) as (b & Hcb & Hmb). cbn [c_off YP09.c_val cbyte] in Hcb, Hmb.
  injection Hcb as <-. rewrite Z.add_0_r in Hmb. unfold aview. rewrite Hmb. cbn [option_map]. f_equal.
  unfold byte_of_word. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. rewrite Z.shiftr_0_r. exact Hz.
Qed.

Lemma u_blt1 : forall (E : env) a b x y, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y ->
  0 <= x < 2 ^ 62 -> 0 <= y < 2 ^ 62 ->
  branch_taken BC_LT (sv_denot E (SOff a 1)) (sv_denot E (SOff b 0)) = (x + 1 <? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite YO0c.branch_lt.
  change (bv_unsigned (sv_denot E (SOff a 1))) with (U E (SOff a 1)).
  change (bv_unsigned (sv_denot E (SOff b 0))) with (U E (SOff b 0)).
  rewrite !U_SOff, Ha, Hb, !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small x), (Z.mod_small y), Z.add_0_r, (Z.mod_small y), (Z.mod_small (x + 1)) by lia.
  unfold YO0b.s64. destruct (Z.ltb_spec (x + 1) (2 ^ 63)); [|lia]. destruct (Z.ltb_spec y (2 ^ 63)); [|lia].
  reflexivity.
Qed.

Lemma LF_SH0_mid : forall i, (4 <= i < 36)%nat -> nth i LF_SH0 0 = 248.
Proof. intros i Hi. do 36 (destruct i as [|i]; [cbn; lia || reflexivity|]). lia. Qed.

Lemma u_tail : forall POST i j,
  FROM POST (u_l_inv B MT MS la_nul LF_MO_SET LF_MO_OP i (j + 1)) ->
  FROM POST (u_x_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (u_j_inv B MT MS la_nul LF_MO_SET LF_MO_OP i j).
Proof.
  intros POST i j HL HX cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HJN.
  destruct HJN as (md & mk & P & N & kbs & mbs & gbs & T3 & Hsh & R23 & R20 & R18 & HU & Hj & Hns & HUW).
  pose proof HB as (HPRE & Hfrm & HGX & HLN & HMS & _).
  pose proof HU as (Hi & Hcore & Hreg & Hsv & Hhd & Hfs & Hsl & Hcur & Hjbk & Hblk & Hdat & Hop).
  pose proof Hreg as (R19 & R21 & R22 & R24 & R25 & R26 & R27).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HJ as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (HAR3 & _).
  destruct (lf_frame_place SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS
    cx fp ly3 S3 W3 (ms_mem ms3) md3 k2 HB HJ Hfr) as (HFa & F32 & F4 & Fc & Fapp & Fpres & Fshp & Fsep).
  pose proof Hblk as (Bmd & Bmk & Bmc & Bkc & BmT & BkT & Bm16 & Bk16 & Bmt & Bkt & Bap & Bpl & Bpk & Bram & Brak
    & Bamm & Bamk).
  destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 md MD_SIZE HAR3 Bmd) as (_ & Bm4 & Bmceil & _).
  change (req_size MD_SIZE) with 8856 in Bmceil.
  pose proof (Fsep md MD_SIZE Bmd) as DmF. unfold zdisjoint in DmF. cbn [fst snd] in DmF.
  change (req_size MD_SIZE) with 8856 in DmF.
  pose proof Hdat as (_ & _ & _ & _ & _ & _ & Dmd & Dmwf & _ & _ & (Dmn & Dmm) & _).
  pose proof Dmwf as (_ & _ & _ & _ & _ & (Wnm & _)). unfold MARKS_MAX in Wnm.
  set (F := lf_F cx fp) in *.
  assert (Hmd8 : md mod 8 = 0) by (rewrite Zmod_divides in Bm16 by lia; destruct Bm16 as (c & Hc8); rewrite Hc8;
    replace (16 * c) with ((2 * c) * 8) by lia; apply Z_mod_mult).
  assert (HFS : lf_SH cx fp = SHADOW_OFF + F / 8) by reflexivity.
  assert (SHB : kLowMemEnd + 512 <= lf_SH cx fp /\ lf_SH cx fp + 128 <= kHighMemBeg /\ lf_SH cx fp mod 4 = 0).
  { rewrite HFS. assert (D1 : 4096 / 8 <= F / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : F / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
    change (4096 / 8) with 512 in D1. change (0x7fffff800000 / 8) with 0xffffff00000 in D2.
    pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite F32, Z.add_0_r in D.
    assert (Q : F / 8 = 4 * (F / 32)) by (rewrite D at 1; replace (32 * (F / 32)) with
      ((4 * (F / 32)) * 8) by lia; apply Z.div_mul; lia).
    unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg. split; [lia|]. split; [lia|].
    rewrite Q. replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia.
    apply Z_mod_mult. }
  assert (MS8 : shadow_of_addr SHADOW_OFF (md + MD_N_MARK) = shadow_of_addr SHADOW_OFF md + 1106).
  { unfold shadow_of_addr, MD_N_MARK. pose proof (Z.div_mod md 8 ltac:(lia)) as D. rewrite Hmd8, Z.add_0_r in D.
    replace (md + 8852) with (4 + (md / 8 + 1106) * 8) by lia. rewrite Z.div_add by lia.
    rewrite Z.div_small by lia. lia. }
  set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (md_n_mark mbs)])) in *.
  assert (EL : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
  { intros n r Hn Hr. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat _ _ n r Hr). }
  assert (E32 : ew E 32 = Z_to_bv 64 (md_n_mark mbs)).
  { unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra _ [Z_to_bv 64 (md_n_mark mbs)] 0). }
  assert (E18 : ew E 18 = Z_to_bv 64 (shadow_of_addr SHADOW_OFF md + 1106))
    by (rewrite (EL 18%nat 18%bv ltac:(lia) eq_refl), R18, MS8; reflexivity).
  assert (E19 : ew E 19 = Z_to_bv 64 (lf_SH cx fp)) by (rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl); exact R19).
  assert (E20 : ew E 20 = Z_to_bv 64 j) by (rewrite (EL 20%nat 20%bv ltac:(lia) eq_refl); exact R20).
  assert (E21 : ew E 21 = Z_to_bv 64 (md + MD_N_MARK)) by (rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl); exact R21).
  assert (E24 : ew E 24 = Z_to_bv 64 (2 ^ 64 - 8)) by (rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl); exact R24).
  assert (Shm : shadow_of_addr SHADOW_OFF md = SHADOW_OFF + md / 8) by reflexivity.
  assert (Hmd47 : md + 8856 <= 2 ^ 47) by lia.
  assert (Mdv : 0 <= md / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (HS : st_ok_pi (fx := fy) SEGS pa_val E u_t_ss
    (restrict (w_H W3) (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LU_join)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold u_t_ss. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold u_tsh_rg, u_tmsh_rg, u_tnm_rg.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite E19, unsigned_lit_small by (unfold kHighMemBeg in *; clia).
        split; [unfold kLowMemEnd in *; clia|]. split; [unfold kHighMemBeg in *; clia|].
        split; [|apply Forall_nil]. intros o Ho. apply (apresent_writable SEGS). apply Fshp. lia.
      + rewrite E18, unsigned_lit_small by (rewrite Shm; unfold SHADOW_OFF; clia).
        split; [rewrite Shm; unfold SHADOW_OFF; clia|]. split; [rewrite Shm; unfold SHADOW_OFF; clia|].
        split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros ii Hii. rewrite Z.add_0_r.
        replace (shadow_of_addr SHADOW_OFF md + 1106 + ii) with (shadow_of_addr SHADOW_OFF md + (1106 + ii)) by lia.
        apply (u_blk_shadow0 _ md 8856 (1106 + ii) Hmd8 eq_refl); [exact Bram | lia].
      + rewrite E21, unsigned_lit_small by (unfold MD_N_MARK; clia).
        split; [unfold MD_N_MARK; clia|]. split; [unfold MD_N_MARK; clia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ _ 0 4 (SOff 32 0) (md_n_mark mbs));
          [rewrite (lf_sv_off E 32 _ 0 E32); [rewrite Z.add_0_r; reflexivity | | ];
           unfold md_n_mark, fld_u32; pose proof (u_rdn4_range mbs MD_N_MARK); lia
          | unfold md_n_mark, fld_u32; pose proof (u_rdn4_range mbs MD_N_MARK); cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. destruct Dmd as ((Hb & _) & HLm).
        exact (val_mem_of_abytes SEGS _ md mbs MD_N_MARK 4 Hb ltac:(unfold MD_N_MARK; lia)
          ltac:(unfold MD_N_MARK, MD_SIZE in *; lia)).
    - apply pairwise_disjoint_of_extents.
      unfold u_tsh_rg, u_tmsh_rg, u_tnm_rg, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (u_base E 19 _ E19) by (unfold kHighMemBeg in *; clia).
      rewrite (u_base E 18 _ E18) by (rewrite Shm; unfold SHADOW_OFF; clia).
      rewrite (u_base E 21 _ E21) by (unfold MD_N_MARK; clia).
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      rewrite Shm. rewrite HFS in *.
      pose proof (Z.div_mod F 8 ltac:(lia)) as DF.
      assert (F8 : F mod 8 = 0).
      { pose proof (Z.div_mod F 32 ltac:(lia)) as D. rewrite F32, Z.add_0_r in D. rewrite D.
        replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia. apply Z_mod_mult. }
      rewrite F8, Z.add_0_r in DF. pose proof (Z.div_mod md 8 ltac:(lia)) as DM. rewrite Hmd8, Z.add_0_r in DM.
      assert (Sep : md / 8 + 1107 <= F / 8 \/ F / 8 + 128 <= md / 8) by lia.
      unfold MD_N_MARK, SHADOW_OFF, kLowMemEnd, kHighMemBeg, amem_range in *.
      destruct Bamm as [Bl | Bh];
        [assert (Bl' : md + 8856 <= 2147450879) by exact Bl | assert (Bh' : 17594333495296 <= md) by exact (proj1 Bh)];
        repeat split; clia.
    - split; [|split; exact I]. cbn [u_t_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E19, E20, E21, E32. rewrite !unsigned_lit_small by (unfold MD_N_MARK, kHighMemBeg in *; clia).
      rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      assert (M4 : (md + MD_N_MARK) mod 2 ^ 2 = 0).
      { unfold MD_N_MARK. rewrite Zmod_divides in Bm16 by lia. destruct Bm16 as (c & Hc). rewrite Hc.
        replace (16 * c + 8852) with ((4 * c + 2213) * 4) by lia. change (2 ^ 2) with 4. apply Z_mod_mult. }
      change (2 ^ 2) with 4 in *. destruct SHB as (SB1 & SB2 & SB3).
      unfold MD_N_MARK, SHADOW_OFF, kLowMemEnd, kHighMemBeg in *.
      repeat match goal with |- _ /\ _ => split end; first [exact I | clia]. }
  rewrite (lf_shape_eta fy LU_join ms3 Hsh).
  assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
  pose proof (@paj_run_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fy rc SK link_listing PL_link PI B LAWS G_HARNESS HGX 0 []) as RUNTO.
  pose proof (paj_branch (fx := fy) (PI := PI)) as BR.
  assert (SHOK : sh_ok pa_segs (SLit 0) [] E
    (mrestrict (w_H W3) (ms_mem (@mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + LU_join)) (ms_mem ms3) (seg_rom SEGS)))))
    by (unfold sh_ok; apply Forall_nil).
  pose proof HJ as HJ0.
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { cbn [ss_mem u_t_ss]. apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_cons; [|apply awr_ok_x_nil]]].
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi YP09.r_base u_tsh_rg base_val] in Ha.
      rewrite E19, unsigned_lit_small in Ha by (unfold kHighMemBeg in *; clia).
      left. split; [|unfold LLVMF_STK, kHighMemBeg in *; clia]. right; right; right. exists LF_CID, fp.
      split; [left; reflexivity|]. right.
      unfold in_zr. cbn [fst snd]. rewrite HFa. change (fs_frame_bytes LF_CID / 8) with 128.
      unfold shadow_addr. fold F. rewrite <- HFS. lia.
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi u_tmsh_rg] in Ha. lia.
    - intros a Ha. cbn [YP09.r_wlo YP09.r_whi u_tnm_rg] in Ha. lia. }
  rename ms into msA, HF into HFA, HFr into HFrA, HG into HGA.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md4 := mdB) in * end.
  assert (Fd : m_fds md4 = m_fds md3) by (subst md4; rewrite !lf_wvb_fds; reflexivity).
  assert (Fs : m_fs md4 = m_fs md3) by (subst md4; rewrite !lf_wvb_fs; reflexivity).
  assert (U19 : bv_unsigned (ew E 19) = lf_SH cx fp)
    by (rewrite E19; apply unsigned_lit_small; unfold kHighMemBeg in *; clia).
  set (X := fun a => lf_SH cx fp + 4 <= a mod 2 ^ 64 < lf_SH cx fp + 36).
  assert (KA : kagree SEGS X (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem msA))).
  { apply (u_kagree_frame E (ss_mem u_t_ss) _ _ X HFrA). intros a (r & Hr & Hw). unfold X.
    rewrite Z_to_bv_unsigned in Hw. unfold bv_wrap in Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
    cbn [ss_mem u_t_ss In] in Hr. destruct Hr as [<- | [<- | [<- | []]]];
      cbn [YP09.r_wlo YP09.r_whi YP09.r_base u_tsh_rg u_tmsh_rg u_tnm_rg base_val] in Hw; lia. }
  assert (NX : forall a, (lf_saved_fp cx a \/ lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_slots_fp cx a \/
     lf_cur_fp cx a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a \/ lf_data_fp md mk a) -> X a ->
     lf_SH cx fp + 4 <= a < lf_SH cx fp + 36 /\
     ~ lf_saved_fp cx a /\ ~ lf_header_fp cx fp a /\ ~ lf_slots_fp cx a /\
     ~ lf_cur_fp cx a /\ ~ lf_jbk_fp MS la_nul cx T3 a /\ ~ lf_blocks_fp md mk a /\ ~ lf_data_fp md mk a).
  { intros a Hf HXa. pose proof (u_fp_range SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END
      LAWS cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 ms3 md3 a HB HJ0 Hfr Hjbk Hblk Hf) as R.
    unfold X in HXa. rewrite Z.mod_small in HXa by exact (proj1 R). split; [exact HXa|].
    exact (u_fs_out SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS TB HSEGS
      cx fp k2 _ _ _ _ md mk T3 _ ly3 S3 W3 ms3 md3 a HB HJ0 Hfr Hjbk Hblk ltac:(lia)). }
  pose proof (lf_saved_keep X cx W3 ms3 W3 msA KA
    (fun a Ha HXa => proj1 (proj2 (NX a ltac:(tauto) HXa)) Ha) Hsv) as Hsv'.
  pose proof (lf_header_keep X cx fp W3 ms3 W3 msA KA
    (fun a Ha HXa => proj1 (proj2 (proj2 (NX a ltac:(tauto) HXa))) Ha) Hhd) as Hhd'.
  pose proof (lf_slots_keep X cx md mk fp W3 ms3 W3 msA KA
    (fun a Ha HXa => proj1 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa)))) Ha) Hsl) as Hsl'.
  pose proof (lf_cur_keep X cx W3 ms3 W3 msA P N KA
    (fun a Ha HXa => proj1 (proj2 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa))))) Ha) Hcur) as Hcur'.
  pose proof (lf_jbk_keep B MT MS la_nul X cx fp k2 _ _ _ _ ly3 S3 W3 ms3 md3 T3 _ W3 msA md4 KA Fd Fs
    (fun a Ha HXa => proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa)))))) Ha) Hjbk) as Hjbk'.
  pose proof (lf_blocks_keep B X _ _ cx md mk T3 ly3 S3 KA
    (fun a Ha HXa => proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa))))))) Ha) Hblk) as Hblk'.
  pose proof (lf_data_keep X _ _ cx md mk kbs mbs gbs KA (wcarry_on_grows _ _ _ HGA)
    (fun a Ha HXa => proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (NX a ltac:(tauto) HXa))))))) Ha) Hdat) as Hdat'.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssA := ssx) in HS end.
  assert (RG0 : region_ok SEGS E (rdW W3 (ms_mem msA)) (nth 0 (ss_mem ssA) u_tsh_rg))
    by exact (st_ok_pi_region_nth E ssA (restrict (w_H W3) msA) 0 _ HS eq_refl).
  assert (Hfs' : lf_fshadow cx fp W3 msA LF_SH0).
  { apply (u_fsh_upd cx fp W3 ms3 msA X SH_Z LF_SH0 4 36 248 Hfs KA); [reflexivity | |].
    - intros i0 Hi0 Hn. assert (Hi1 : (i0 < 112)%nat) by exact Hi0.
      split; [|rewrite (SH_Z_nth i0 Hi1); destruct (Nat.leb_spec 4 i0), (Nat.ltb_spec i0 36); cbn [andb];
        try reflexivity; lia].
      unfold X. rewrite Z.mod_small by (unfold kHighMemBeg in *; lia). lia.
    - intros i0 Hi0 Hn. assert (Hi1 : (i0 < 112)%nat) by exact Hi0.
      split; [|apply LF_SH0_mid; lia].
      apply (u_byte_sv E (w_H W3) (ms_mem msA) _ (lf_SH cx fp) (Z.of_nat i0) (SOff 24 0) 248 RG0).
      + cbn [nth ss_mem ssA setpc YP09.r_base base_val]. exact U19.
      + assert (Hc : forall k, 4 <= k < 36 ->
          In (YP09.mkChunk k (CVal 1 (SOff 24 0))) (YP09.r_chunks (nth 0 (ss_mem ssA) u_tsh_rg))).
        { intros k Hk. cbn [nth ss_mem ssA setpc YP09.r_chunks].
          assert (Hk' : k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/
            k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/
            k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31 \/ k = 32 \/ k = 33 \/
            k = 34 \/ k = 35) by lia.
          repeat (destruct Hk' as [-> | Hk']; [cbn [In]; tauto|]). subst k. cbn [In]. tauto. }
        apply Hc. lia.
      + rewrite (lf_sv_off E 24 _ 0 E24) by lia. rewrite Z.add_0_r, Z_to_bv_unsigned. reflexivity. }
  assert (HUA : u_mem B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 LF_SH0 cx fp k2 ly3 S3 W3 msA md4).
  { prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19.
    prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22.
    prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
    prreg HS (27%bv : bv 5) Q27.
    rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl) in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl) in Q3.
    rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl) in Q4. rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in Q8.
    rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in Q9. rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in Q19.
    rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl) in Q21. rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in Q22.
    rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in Q24. rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in Q25.
    rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in Q26. rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl) in Q27.
    split; [exact Hi|]. split; [unfold lf_core in *; rewrite Q2, Q8, Q9, Q3, Q4; exact Hcore|].
    split; [unfold u_regs in *; rewrite Q19, Q21, Q22, Q24, Q25, Q26, Q27; exact Hreg|].
    split; [exact Hsv'|]. split; [exact Hhd'|]. split; [exact Hfs'|]. split; [exact Hsl'|]. split; [exact Hcur'|].
    split; [exact Hjbk'|]. split; [exact Hblk'|]. split; [exact Hdat' | exact Hop]. }
  (* close the frame shadow's write window *)
  pose proof (ar_close1 fy E _ _ 0%nat _ HS eq_refl ltac:(vm_compute; reflexivity)) as HS'. clear HS RG0.
  cbn [ss_pc ss_regs ss_resv ss_facts ss_mem list_upd] in HS'. rename HS' into HS.
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  - (* +0x8cc taken: another mark, back to the loop head *)
    rewrite (u_blt1 E 20 32 j (md_n_mark mbs) E20 E32 ltac:(lia) ltac:(lia)) in Hc. apply Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LU_body; [apply ar_awr_nowin; vm_compute; reflexivity|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    pose proof (ar_kagree_nowin _ _ _ _ HFrB ltac:(vm_compute; reflexivity)) as KB.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md5 := mdB) in * end.
    assert (Fd5 : m_fds md5 = m_fds md4) by (subst md5; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs5 : m_fs md5 = m_fs md4) by (subst md5; rewrite !lf_wvb_fs; reflexivity).
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
    prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
    prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
    prreg HS (27%bv : bv 5) Q27.
    rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl) in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl) in Q3.
    rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl) in Q4. rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in Q8.
    rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in Q9. rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in Q19.
    rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl) in Q21. rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in Q22.
    rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in Q24. rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in Q25.
    rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in Q26. rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl) in Q27.
    assert (UB : u_mem B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 LF_SH0 cx fp k2 ly3 S3 W3 msB md5).
    { pose proof HUA as (_ & _ & _ & HsvA & HhdA & HfsA & HslA & HcurA & HjbkA & HblkA & HdatA & _).
      split; [exact Hi|]. split; [unfold lf_core in *; rewrite Q2, Q8, Q9, Q3, Q4; exact Hcore|].
      split; [unfold u_regs in *; rewrite Q19, Q21, Q22, Q24, Q25, Q26, Q27; exact Hreg|].
      split; [exact (lf_saved_keep _ cx W3 msA W3 msB KB (fun a _ H => H) HsvA)|].
      split; [exact (lf_header_keep _ cx fp W3 msA W3 msB KB (fun a _ H => H) HhdA)|].
      split; [exact (lf_fshadow_keep _ cx fp W3 msA W3 msB LF_SH0 KB (fun a _ H => H) HfsA)|].
      split; [exact (lf_slots_keep _ cx md mk fp W3 msA W3 msB KB (fun a _ H => H) HslA)|].
      split; [exact (lf_cur_keep _ cx W3 msA W3 msB P N KB (fun a _ H => H) HcurA)|].
      split; [exact (lf_jbk_keep B MT MS la_nul _ cx fp k2 _ _ _ _ ly3 S3 W3 msA md4 T3 _ W3 msB md5 KB Fd5 Fs5
        (fun a _ H => H) HjbkA)|].
      split; [exact (lf_blocks_keep B _ _ _ cx md mk T3 ly3 S3 KB (fun a _ H => H) HblkA)|].
      split; [exact (lf_data_keep _ _ _ cx md mk kbs mbs gbs KB (wcarry_on_grows _ _ _ HGB) (fun a _ H => H) HdatA)|].
      exact Hop. }
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssB := ssx) in HS end.
    assert (E23 : ew E 23 = Z_to_bv 64 (md + MD_MARK + MARK_LEN * j))
      by (rewrite (EL 23%nat 23%bv ltac:(lia) eq_refl); exact R23).
    apply (HL cx fy fp k2 ly3 S3 W3 msB md5 HB Hfx HJ Hfr).
    exists md, mk, P, N, kbs, mbs, gbs, T3.
    split; [exact (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl)|].
    split.
    { rewrite Q23, E23, Z_to_bv_unsigned. unfold w64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite Z.mod_small by (unfold MD_MARK, MARK_LEN in *; clia). f_equal. unfold MARK_LEN. lia. }
    split.
    { rewrite Q20, E20, Z_to_bv_unsigned. unfold w64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite Z.mod_small by clia. reflexivity. }
    split; [rewrite Q18, E18, <- MS8; reflexivity|].
    split; [exact UB|]. split; [lia|]. split; [exact Hns|]. exact HUW.
  - (* not taken: every mark done, to +0x924 *)
    rewrite (u_blt1 E 20 32 j (md_n_mark mbs) E20 E32 ltac:(lia) ltac:(lia)) in Hc. apply Z.ltb_ge in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) LU_exit; [apply ar_awr_nowin; vm_compute; reflexivity|].
    rename ms into msB, HF into HFB, HFr into HFrB, HG into HGB.
    pose proof (ar_kagree_nowin _ _ _ _ HFrB ltac:(vm_compute; reflexivity)) as KB.
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdB |} _ => set (md5 := mdB) in * end.
    assert (Fd5 : m_fds md5 = m_fds md4) by (subst md5; rewrite !lf_wvb_fds; reflexivity).
    assert (Fs5 : m_fs md5 = m_fs md4) by (subst md5; rewrite !lf_wvb_fs; reflexivity).
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
    prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
    prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
    prreg HS (27%bv : bv 5) Q27.
    rewrite (EL 2%nat 2%bv ltac:(lia) eq_refl) in Q2. rewrite (EL 3%nat 3%bv ltac:(lia) eq_refl) in Q3.
    rewrite (EL 4%nat 4%bv ltac:(lia) eq_refl) in Q4. rewrite (EL 8%nat 8%bv ltac:(lia) eq_refl) in Q8.
    rewrite (EL 9%nat 9%bv ltac:(lia) eq_refl) in Q9. rewrite (EL 19%nat 19%bv ltac:(lia) eq_refl) in Q19.
    rewrite (EL 21%nat 21%bv ltac:(lia) eq_refl) in Q21. rewrite (EL 22%nat 22%bv ltac:(lia) eq_refl) in Q22.
    rewrite (EL 24%nat 24%bv ltac:(lia) eq_refl) in Q24. rewrite (EL 25%nat 25%bv ltac:(lia) eq_refl) in Q25.
    rewrite (EL 26%nat 26%bv ltac:(lia) eq_refl) in Q26. rewrite (EL 27%nat 27%bv ltac:(lia) eq_refl) in Q27.
    assert (UB : u_mem B MT MS la_nul LF_MO_SET LF_MO_OP i md mk P N kbs mbs gbs T3 LF_SH0 cx fp k2 ly3 S3 W3 msB md5).
    { pose proof HUA as (_ & _ & _ & HsvA & HhdA & HfsA & HslA & HcurA & HjbkA & HblkA & HdatA & _).
      split; [exact Hi|]. split; [unfold lf_core in *; rewrite Q2, Q8, Q9, Q3, Q4; exact Hcore|].
      split; [unfold u_regs in *; rewrite Q19, Q21, Q22, Q24, Q25, Q26, Q27; exact Hreg|].
      split; [exact (lf_saved_keep _ cx W3 msA W3 msB KB (fun a _ H => H) HsvA)|].
      split; [exact (lf_header_keep _ cx fp W3 msA W3 msB KB (fun a _ H => H) HhdA)|].
      split; [exact (lf_fshadow_keep _ cx fp W3 msA W3 msB LF_SH0 KB (fun a _ H => H) HfsA)|].
      split; [exact (lf_slots_keep _ cx md mk fp W3 msA W3 msB KB (fun a _ H => H) HslA)|].
      split; [exact (lf_cur_keep _ cx W3 msA W3 msB P N KB (fun a _ H => H) HcurA)|].
      split; [exact (lf_jbk_keep B MT MS la_nul _ cx fp k2 _ _ _ _ ly3 S3 W3 msA md4 T3 _ W3 msB md5 KB Fd5 Fs5
        (fun a _ H => H) HjbkA)|].
      split; [exact (lf_blocks_keep B _ _ _ cx md mk T3 ly3 S3 KB (fun a _ H => H) HblkA)|].
      split; [exact (lf_data_keep _ _ _ cx md mk kbs mbs gbs KB (wcarry_on_grows _ _ _ HGB) (fun a _ H => H) HdatA)|].
      exact Hop. }
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ => set (ssB := ssx) in HS end.
    apply (HX cx fy fp k2 ly3 S3 W3 msB md5 HB Hfx HJ Hfr).
    exists md, mk, P, N, kbs, mbs, gbs, T3.
    split; [exact (lf_shape_of_st_ok fy W3 _ ssB msB HS eq_refl)|].
    split; [rewrite Q18, E18, <- MS8; reflexivity|].
    split; [exact UB|]. split; [exact Hns|].
    assert (Hn : j + 1 = md_n_mark mbs) by lia.
    assert (Hlen : length (mk_names gbs) = Z.to_nat (md_n_mark mbs))
      by (first [rewrite Dmm | rewrite <- Dmm]; unfold md_marks; rewrite length_map, length_seq; reflexivity).
    rewrite Hn, <- Hlen, skipn_all in HUW. cbn [unmark_walk] in HUW. rewrite <- HUW. reflexivity.
Qed.

End a.
