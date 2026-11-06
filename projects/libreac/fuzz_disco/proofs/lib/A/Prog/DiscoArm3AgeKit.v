(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 959 of its 988 lines of code are new or changed and 40 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoEntObs.v; 413 of its 459 lines of code are new or changed and 942 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3AgeEnt.v; 274 of its 340 lines of code are new or changed and 393 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoArm3 DiscoArm3AgeSt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition a3_srx (r : nat) : sv :=
  match r with
  | 0%nat => SLit 0 | 2%nat => SOff AT_A 0 | 8%nat => SOff AT_STK 0 | 9%nat => SOff AT_A 0 | 18%nat => SOff 32 0
  | 20%nat => SLit WS_MASK | 25%nat => SLit 32
  | _ => SOff (AT_X + r) 0
  end.
Definition a3_sr : list sv := map a3_srx (seq 0 32).
Definition a3_vals (regs : bvmap 5 word) (ex : list word) : list word :=
  map (fun r => getr regs (Z_to_bv 5 (Z.of_nat r))) (seq 0 32) ++ ex.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Definition a3_flag (cx : dcx) : word := Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)).

Lemma a3_env_img : forall cx E vals, d_E cx E -> img_env VAL A_LIM (d_env cx E vals).
Proof. intros cx E vals HE. exact (proj1 (proj2 (proj2 (d_E_env cx E vals HE)))). Qed.

Lemma a3_dE_agree : forall cx E E' K, d_E cx E -> env_agree K E E' -> (AT_FL < K)%nat ->
  d_E cx E' /\ ew E' AT_FL = ew E AT_FL.
Proof.
  intros cx E E' K (EE & E32 & HEI & E60 & EF & ESH) (HA & _) HK.
  unfold AT_FL in HK.
  split; [|apply HA; unfold AT_FL; lia].
  unfold d_E. rewrite !HA by (unfold AT_A, AT_F, AT_SH; lia).
  split; [|split; [exact E32 | split; [|split; [exact E60 | split; [exact EF | exact ESH]]]]].
  - intros n r Hn. rewrite HA; [exact (EE n r Hn)|].
    pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr. lia.
  - intros a Ha. rewrite HA by (unfold A_LIM in Ha; lia). exact (HEI a Ha).
Qed.

Lemma a3_dE_ext : forall cx E vals K ws, d_E cx E -> (AT_FL < K)%nat ->
  d_E cx (extK (d_env cx E vals) K ws) /\ ew (extK (d_env cx E vals) K ws) AT_FL = a3_flag cx.
Proof.
  intros cx E vals K ws HE HK.
  destruct (a3_dE_agree cx (d_env cx E vals) (extK (d_env cx E vals) K ws) K (d_E_env cx E vals HE)
    (env_agree_extK _ K ws) HK) as (H1 & H2).
  split; [exact H1|]. rewrite H2. unfold a3_flag. apply d_env_fl.
Qed.

Lemma a3_env_reg : forall cx E regs ex (r : bv 5) a, a = (AT_X + Z.to_nat (bv_unsigned r))%nat ->
  ew (d_env cx E (a3_vals regs ex)) a = getr regs r.
Proof.
  intros cx E regs ex r a ->.
  pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite d_env_x by (unfold a3_vals; rewrite length_app, length_map, length_seq; lia).
  unfold a3_vals. rewrite app_nth1 by (rewrite length_map, length_seq; lia).
  rewrite (nth_indep _ _ ((fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))) 0%nat))
    by (rewrite length_map, length_seq; lia).
  pose proof (map_nth (fun r0 : nat => getr regs (Z_to_bv 5 (Z.of_nat r0))) (seq 0 32) 0%nat
    (Z.to_nat (bv_unsigned r))) as Hm.
  cbv beta in Hm |- *. rewrite Hm, seq_nth by lia. cbn [Nat.add]. rewrite Z2Nat.id by lia.
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma a3_regs_ok : forall B cx E regs ex, d_E cx E -> d_rL B cx regs ->
  regs_ok (d_env cx E (a3_vals regs ex)) a3_sr regs.
Proof.
  intros B cx E regs ex HE HL.
  pose proof (d_E_env cx E (a3_vals regs ex) HE) as HE'.
  destruct HE' as (HER & H32 & _ & HA60 & _ & _). unfold AT_A in HA60.
  destruct HL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ].
  all: match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) =>
         let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end.
  all: cbn [sv_denot].
  all: first
    [ rewrite getr_zero; reflexivity
    | rewrite HA60, Z.add_0_r, Z_to_bv_bv_unsigned;
      first [ rewrite <- Hsp; unfold spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity | exact H9 ]
    | rewrite (HER 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, H8; unfold w64, d_S, spZ;
      rewrite Z_to_bv_bv_unsigned; reflexivity
    | rewrite H32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; exact H18
    | exact H20
    | exact H25
    | match goal with |- getr ?rg ?x = Z_to_bv 64 (bv_unsigned (ew ?Ex ?a) + 0) =>
        rewrite (a3_env_reg cx E regs ex x a eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end ].
Qed.

Lemma a3_frame_E : forall B cx h n xb shf ly3 S3 W mem3,
  d_body B cx h n xb shf ly3 S3 W mem3 ->
  exists E, d_E cx E /\ Forall (region_ok SEGS E (rd W mem3)) (d_regions cx shf) /\
    rdword (aview SEGS (w_H W) mem3) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) =
      Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)).
Proof.
  intros B cx h n xb shf ly3 S3 W mem3 Hb.
  destruct Hb as (T & G & Lk & H & (E & HE & HR & HF & _ & _) & _).
  exists E. split; [exact HE|]. split; [exact HR | exact HF].
Qed.

Lemma a3_pcall_pi : forall (fq : YK11.FPState) E ss ms (s : dsym),
  st_ok (fx := fq) SEGS E (setpc ss (SIGMA s)) ms ->
  st_ok_pi (fx := fq) SEGS VAL E (setpc ss (SIGMA s - BASE)) ms.
Proof.
  intros fq E ss ms s HS. unfold st_ok_pi, abs_ss, setpc in *.
  cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
  replace (BASE + (SIGMA s - BASE)) with (SIGMA s) by lia. exact HS.
Qed.

Lemma a3_nowin : forall E rs a, forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> ~ in_wrange E rs a.
Proof.
  intros E rs a H (r & Hin & Ha). rewrite forallb_forall in H. specialize (H r Hin). apply Z.leb_le in H. lia.
Qed.

Lemma a3_kept_frame : forall E rs (H : word -> bool) m m' lo hi,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a, in_wrange E rs a -> lo <= a < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' lo hi HF Hw a Ha Hn. unfold aview, mbyte.
  rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by exact Ha. intros Hx. apply Hn. exact (Hw a Hx).
Qed.

Lemma a3_present_grows : forall (H : word -> bool) m m',
  mem_grows (mrestrict H m) (mrestrict H m') -> forall a, apresent H m a -> apresent H m' a.
Proof.
  intros H m m' HG a (HH & b & Hb). split; [exact HH|].
  specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite HH, Hb in HG. cbn in HG.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E'; [exists b'; reflexivity|].
  exfalso. apply HG; [discriminate | reflexivity].
Qed.

Lemma a3_mbyte_eq : forall (H : word -> bool) m m' x,
  aview SEGS H m' x = aview SEGS H m x -> mbyte SEGS (mrestrict H m') x = mbyte SEGS (mrestrict H m) x.
Proof.
  intros H m m' x Hv. unfold aview in Hv.
  destruct (mbyte SEGS (mrestrict H m') x) as [b1|], (mbyte SEGS (mrestrict H m) x) as [b2|];
    cbn [option_map] in Hv; try discriminate Hv; [|reflexivity].
  injection Hv as Hv. f_equal. apply bv_eq. exact Hv.
Qed.

Lemma a3_val_mem_keep : forall (W : world SEGS) m m' lo hi a len v,
  (forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  0 <= a -> a + Z.of_nat len <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat len -> ~ (lo <= x < hi)) ->
  val_mem SEGS (rd W m) a len v -> val_mem SEGS (rd W m') a len v.
Proof.
  intros W m m' lo hi a len v HK Ha0 Ha1 Hw HV k Hk.
  rewrite (a3_mbyte_eq (w_H W) m m' (a + Z.of_nat k)); [apply HV; exact Hk|].
  apply HK; [lia | apply Hw; lia].
Qed.

Lemma a3_garr8_keep : forall (W : world SEGS) m m' lo hi a l,
  (forall x, 0 <= x < 2 ^ 64 -> ~ (lo <= x < hi) -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat (length l) -> ~ (lo <= x < hi)) ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W m') a l.
Proof.
  intros W m m' lo hi a l HK Ha0 Ha1 Hw HG j Hj.
  destruct (HG j Hj) as (HV & Hr). split; [|exact Hr].
  apply (a3_val_mem_keep W m m' lo hi (a + Z.of_nat j) 1 _ HK); [lia | lia | | exact HV].
  intros x Hx. apply Hw. lia.
Qed.

Lemma a3_kept_all : forall (H : word -> bool) m m',
  (forall x, 0 <= x < 2 ^ 64 -> aview SEGS H m' x = aview SEGS H m x) -> forall x, aview SEGS H m' x = aview SEGS H m x.
Proof.
  intros H m m' HK x.
  assert (Hx : Z_to_bv 64 x = Z_to_bv 64 (x mod 2 ^ 64)).
  { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod.
    reflexivity. }
  pose proof (HK (x mod 2 ^ 64) (Z.mod_pos_bound x (2 ^ 64) ltac:(lia))) as Hm.
  unfold aview, mbyte in *. rewrite Hx. exact Hm.
Qed.

Lemma a3_val_mem_all : forall (W : world SEGS) m m' a len v,
  (forall x, aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  val_mem SEGS (rd W m) a len v -> val_mem SEGS (rd W m') a len v.
Proof.
  intros W m m' a len v HK HV k Hk.
  rewrite (a3_mbyte_eq (w_H W) m m' (a + Z.of_nat k) (HK _)). apply HV. exact Hk.
Qed.

Lemma a3_garr8_all : forall (W : world SEGS) m m' a l,
  (forall x, aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W m') a l.
Proof.
  intros W m m' a l HK HG j Hj.
  destruct (HG j Hj) as (HV & Hr). split; [exact (a3_val_mem_all W m m' _ 1 _ HK HV) | exact Hr].
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
Hypothesis DBKEEP : d_body_keep_stmt B.
Hypothesis DBRT : d_body_rt_stmt B.

Lemma a3_seat : forall (fq : YK11.FPState) cx pc h n xb shf ly3 S3 W regs mem3 md3 k ex acs fcs extra fa cs,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k ->
  d_rL B cx regs -> d_body B cx h n xb shf ly3 S3 W mem3 ->
  (forall E, d_E cx E ->
     atoms_ok (d_env cx E (a3_vals regs ex)) fa /\ conds_ok (d_env cx E (a3_vals regs ex)) cs /\
     Forall (YP09.chunk_ok SEGS (d_env cx E (a3_vals regs ex)) (rd W mem3) (d_A cx)) acs /\
     Forall (YP09.chunk_ok SEGS (d_env cx E (a3_vals regs ex)) (rd W mem3) (d_FB cx)) fcs /\
     Forall (region_ok SEGS (d_env cx E (a3_vals regs ex)) (rd W mem3)) extra /\
     pairwise_disjoint (d_env cx E (a3_vals regs ex)) extra /\
     Forall (fun r => all_disjoint (d_env cx E (a3_vals regs ex)) r (d_kregions shf acs fcs)) extra) ->
  regions_wf (d_kregions shf acs fcs ++ extra) = true ->
  exists E, d_E cx E /\
    st_ok_pi (fx := fq) SEGS VAL (d_env cx E (a3_vals regs ex)) (ss_d pc a3_sr shf acs fcs extra (d_facts fa cs))
      (restrict (w_H W) (YK11.mkst (fx := fq) regs (Z_to_bv 64 (BASE + pc)) mem3 (YK11.seg_rom SEGS))).
Proof.
  intros fq cx pc h n xb shf ly3 S3 W regs mem3 md3 k ex acs fcs extra fa cs HC HL Hb HP Hwf.
  destruct (a3_frame_E B cx h n xb shf ly3 S3 W mem3 Hb) as (E & HE & HR & HF).
  destruct (HP E HE) as (Hfa & Hcs & Hacs & Hfcs & Hext & Hpd & Hdx).
  exists E. split; [exact HE|].
  exact (DSEAT LAWS TL fq cx shf ly3 S3 W regs mem3 md3 k E pc a3_sr (a3_vals regs ex) acs fcs extra (d_facts fa cs)
    HC HE HR HF (a3_regs_ok B cx E regs ex HE HL)
    (DFACTS LAWS cx ly3 S3 W mem3 md3 k E (a3_vals regs ex) fa cs HC HE Hfa Hcs)
    Hacs Hfcs Hext Hpd Hdx Hwf).
Qed.

Lemma a3_land : forall (fq : YK11.FPState) cx pc kmax h i n now xb R X W ly3 S3 md k acc E ss ms,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) -> d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= kmax -> st_nev S3 <= st_nev (c_S cx) + kmax ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  d_E cx E -> ew E AT_FL = a3_flag cx -> d_land_chk dsh_loop (ss_mem ss) = true ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 216) 8 h ->
  val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 152) 8 (h + 440) ->
  (d_frame cx h dsh_loop W (ms_mem ms) -> d_shadow cx dsh_loop W (ms_mem ms) ->
     d_body B cx h n xb dsh_loop ly3 S3 W (ms_mem ms)) ->
  d_rL B cx (ms_regs ms) -> R (ms_regs ms) -> X W (ms_mem ms) -> d_sp0 cx i now W (ms_mem ms) ->
  a3_st B MT XM_LIB RLO RHI tfib_K cx pc kmax h i n now xb R X W (mkCfg ms md).
Proof.
  intros fq cx pc kmax h i n now xb R X W ly3 S3 md k acc E ss ms
    Hfrm0 Hbase HJ Hfrs Hk Hnev Hmo Hacc Hi Hn Hnow HS Hrv Hpc HE HFL Hchk H216 H152 Hbody HL HR HX Hsp0.
  destruct (DLAND LAWS FFL fq cx h dsh_loop ly3 S3 W md k E ss ms (conj Hbase (conj HJ Hfrs)) HE HFL HS Hchk
    H216 H152) as (Hfr & Hsh).
  unfold a3_st, d_at.
  exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md, k, acc.
  split.
  { unfold cfg_at. pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms.
    rewrite Hpc in Hms. rewrite Hms at 1. reflexivity. }
  refine (conj Hfrm0 (conj Hbase (conj HJ (conj Hfrs (conj Hk (conj Hnev (conj Hmo (conj Hacc _)))))))).
  exact (conj Hi (conj Hn (conj Hnow (conj HL (conj HR (conj HX (conj Hsp0 (Hbody Hfr Hsh)))))))).
Qed.

Lemma a3_land_win : forall cx ly3 S3 W mem md k mem3 lo hi h,
  d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem md k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem3 a) ->
  (forall a, d_A cx + 152 <= a < d_A cx + 160 \/ d_A cx + 216 <= a < d_A cx + 224 -> ~ (lo <= a < hi)) ->
  val_mem SEGS (rd W mem3) (d_A cx + 216) 8 h -> val_mem SEGS (rd W mem3) (d_A cx + 152) 8 (h + 440) ->
  val_mem SEGS (rd W mem) (d_A cx + 216) 8 h /\ val_mem SEGS (rd W mem) (d_A cx + 152) 8 (h + 440).
Proof.
  intros cx ly3 S3 W mem md k mem3 lo hi h HC HK Hwin H216 H152.
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem md k HC) as (_ & HSlo & HShi & _).
  pose proof alloc_ceiling_val as Hac. unfold LLVMF_STK in HSlo.
  assert (HSr : 0 <= d_S cx - MFRAME) by (unfold MFRAME; lia).
  destruct (d_A_range cx HSr) as (HAr & _). unfold MFRAME in HAr.
  assert (HA0 : 0 <= d_A cx) by lia.
  assert (HA1 : d_A cx + 224 <= 2 ^ 64) by lia.
  split.
  - apply (a3_val_mem_keep W mem3 mem lo hi); [exact HK | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
    | intros x Hx; apply Hwin; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; lia | exact H216].
  - apply (a3_val_mem_keep W mem3 mem lo hi); [exact HK | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
    | intros x Hx; apply Hwin; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; lia | exact H152].
Qed.

Lemma a3_land_keep : forall (fq : YK11.FPState) cx pc kmax h i n0 n now R X W ly3 S3 mem3 md k acc E ss ms lo hi,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) -> d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= kmax -> st_nev S3 <= st_nev (c_S cx) + kmax ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  0 <= i < MAX_OPS -> 0 <= n <= n0 -> 0 <= now < 2 ^ 64 ->
  d_body B cx h n0 [] dsh_loop ly3 S3 W mem3 ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  d_E cx E -> ew E AT_FL = a3_flag cx -> d_land_chk dsh_loop (ss_mem ss) = true ->
  d_S cx - LLVMF_STK <= lo -> hi <= d_S cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a) ->
  (forall a, ~ in_img SEGS a -> apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms) a) ->
  (forall a, d_A cx + 152 <= a < d_A cx + 160 \/ d_A cx + 216 <= a < d_A cx + 224 -> ~ (lo <= a < hi)) ->
  d_rL B cx (ms_regs ms) -> R (ms_regs ms) -> X W (ms_mem ms) -> d_sp0 cx i now W (ms_mem ms) ->
  a3_st B MT XM_LIB RLO RHI tfib_K cx pc kmax h i n now [] R X W (mkCfg ms md).
Proof.
  intros fq cx pc kmax h i n0 n now R X W ly3 S3 mem3 md k acc E ss ms lo hi
    Hfrm0 Hbase HJ Hfrs Hk Hnev Hmo Hacc Hi Hn Hnow Hb HS Hrv Hpc HE HFL Hchk Hlo Hhi HK HP Hwin HL HR HX Hsp0.
  pose proof Hb as (T & G & Lk & H & (E0 & _ & _ & _ & H216 & H152) & _).
  destruct (a3_land_win cx ly3 S3 W (ms_mem ms) md k mem3 lo hi h (conj Hbase (conj HJ Hfrs)) HK Hwin H216 H152)
    as (H216' & H152').
  apply (a3_land fq cx pc kmax h i n now [] R X W ly3 S3 md k acc E ss ms Hfrm0 Hbase HJ Hfrs Hk Hnev Hmo Hacc Hi
    ltac:(lia) Hnow HS Hrv Hpc HE HFL Hchk H216' H152'); [|exact HL | exact HR | exact HX | exact Hsp0].
  intros Hfr Hsh. exact (DBKEEP cx h n0 n dsh_loop ly3 S3 W mem3 (ms_mem ms) lo hi Hb Hlo Hhi HK HP Hfr Hsh Hn).
Qed.

Lemma a3_land_rt : forall (fq : YK11.FPState) cx pc kmax h i n0 n now xb R X W ly3 S3 mem3 md k acc E ss ms lo hi,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) -> d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= kmax -> st_nev S3 <= st_nev (c_S cx) + kmax ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  0 <= i < MAX_OPS -> 0 <= n <= n0 -> 0 <= now < 2 ^ 64 ->
  d_body B cx h n0 xb dsh_loop ly3 S3 W mem3 ->
  st_ok_pi (fx := fq) SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = pc ->
  d_E cx E -> ew E AT_FL = a3_flag cx -> d_land_chk dsh_loop (ss_mem ss) = true ->
  d_S cx - LLVMF_STK <= lo -> hi <= d_S cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a) ->
  (forall a, ~ in_img SEGS a -> apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms) a) ->
  (forall a, d_A cx + 152 <= a < d_A cx + 160 \/ d_A cx + 216 <= a < d_A cx + 224 -> ~ (lo <= a < hi)) ->
  d_rL B cx (ms_regs ms) -> R (ms_regs ms) -> X W (ms_mem ms) -> d_sp0 cx i now W (ms_mem ms) ->
  a3_st B MT XM_LIB RLO RHI tfib_K cx pc kmax h i n now xb R X W (mkCfg ms md).
Proof.
  intros fq cx pc kmax h i n0 n now xb R X W ly3 S3 mem3 md k acc E ss ms lo hi
    Hfrm0 Hbase HJ Hfrs Hk Hnev Hmo Hacc Hi Hn Hnow Hb HS Hrv Hpc HE HFL Hchk Hlo Hhi HK HP Hwin HL HR HX Hsp0.
  pose proof Hb as (T & G & Lk & H & (E0 & _ & _ & _ & H216 & H152) & _).
  destruct (a3_land_win cx ly3 S3 W (ms_mem ms) md k mem3 lo hi h (conj Hbase (conj HJ Hfrs)) HK Hwin H216 H152)
    as (H216' & H152').
  apply (a3_land fq cx pc kmax h i n now xb R X W ly3 S3 md k acc E ss ms Hfrm0 Hbase HJ Hfrs Hk Hnev Hmo Hacc Hi
    ltac:(lia) Hnow HS Hrv Hpc HE HFL Hchk H216' H152'); [|exact HL | exact HR | exact HX | exact Hsp0].
  intros Hfr Hsh.
  exact (DBRT cx h n0 n xb dsh_loop dsh_loop ly3 S3 W mem3 (ms_mem ms) lo hi (fun a => lo <= a < hi) Hb Hlo Hhi
    (fun a Ha => or_introl Ha) HK HP Hfr Hsh Hn).
Qed.

End h.
End f.
End d.
