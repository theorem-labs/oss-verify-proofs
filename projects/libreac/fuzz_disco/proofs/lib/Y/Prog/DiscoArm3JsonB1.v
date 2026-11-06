(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8c.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AE2d.v, proofs/cgif/cgif_file_fuzzer/lib/UI2d.v. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on image B (fuzz_grant.asan-ubsan, bin fde52226dc48, 0x8363c = BASE + 0x2c00, 367 slots), ported from lib/A/Prog/CtrlBuildGrantSweep.v at a working branch 5aae1e8a0ce (its Require closure: 196 files, 0 Admitted / admit / Axiom / Parameter), with the steps of the class-6 side-stack frame adapted from lib/A/Prog/CtrlStampHeadamp.v at the same commit (whose own cgif sources are proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, ACam.v, ACbf.v, ACf6.v, AChd.v); every address, constant and byte is image B's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/CtrlBuildGrantSweep.v, with its module paths and module names changed; 610 of its 649 lines of code are new or changed and 3971 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/Y/Prog/DiscoArm3AgeCall1.v; 453 of its 514 lines of code are new or changed and 588 lines of the source are left out. *)
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
YG00 YG0a YG01 YG0f YG0n YG0p YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC1g YC44 YC1h YC1i YC88 YI67 YCjr YCj1 YCja YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntSeatStmt DiscoYEntBodyStmt DiscoArm3TailK DiscoArm3 DiscoArm3JsonModel DiscoArm3JsonCut
DiscoArm3JsonJs DiscoArm3JsonK DiscoArm3JsonBDefs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require slot_ser_defs slot_ser_tokb.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition YB1_NP : nat := 563%nat.
Definition YB1_NB : nat := 564%nat.
Definition yb1_fa : list (nat * afact) :=
  [(551%nat, mkAF 32 32 0); (YB1_NP, mkAF 4096 (2 ^ 47 - 16) 0); (YB1_NB, mkAF 33 255 0)].
Definition yb1_cs : list acond :=
  [mkAC BC_LTU (SOff 552 0) (SOff 557 0); mkAC BC_LTU (SOff 552 1) (SOff 557 0);
   mkAC BC_GEU (SOff 556 0) (SOff 552 1); mkAC BC_NE (SOff YB1_NB 0) (SLit 125)].
Definition yb1_al0 : sv * sv := (SAlu ALU_ADD (SOff 555 0) (SOff 552 0), SOff YB1_NP 0).
Definition yb1_al1 : sv * sv := (SAlu ALU_ADD (SOff 555 0) (SOff 552 1), SOff YB1_NP 1).
Definition yb1_rs : smem :=
  [YP09.mkRegion (Some AT_STK) (-104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 352 360 dslot_chunks;
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 0 dfhdr_chunks;
   fshadow_region AT_SH DFRAME_CLASS 0 0 (dsh_chunks dsh_scr)].
Definition yb1_rg (v : sv) : YP09.region :=
  YP09.mkRegion (Some YB1_NP) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 123)); YP09.mkChunk 1 (CVal 1 v)].
Definition yb1_SH : list shent := [mkSHE YB1_NP 0 2].

Lemma yb_subregion : forall b lo hi wlo whi wlo' whi' cs cs',
  whi' <= wlo' \/ (wlo <= wlo' /\ whi' <= whi) -> (forall c, In c cs -> In c cs') ->
  subregion (YP09.mkRegion b lo hi wlo' whi' cs) (YP09.mkRegion b lo hi wlo whi cs').
Proof.
  intros b lo hi wlo whi wlo' whi' cs cs' Hw Hc. unfold subregion.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [exact Hw | exact Hc].
Qed.

Lemma yb1_sub : forall pc sr G, submem yb1_rs (ss_mem (ss_d pc sr dsh_scr [] [] [] G)).
Proof.
  intros pc sr G. cbn [ss_d ss_mem d_kregions app]. unfold yb1_rs, fshadow_region.
  apply submem_keep; [apply yb_subregion; [lia | intros c Hc; exact Hc]|].
  apply submem_keep; [apply yb_subregion; [lia | intros c Hc; rewrite app_nil_r; exact Hc]|].
  apply submem_keep; [apply yb_subregion; [lia | intros c Hc; rewrite app_nil_r; exact Hc]|].
  apply submem_keep; [apply yb_subregion; [lia | intros c Hc; exact Hc]|].
  apply submem_nil.
Qed.

Ltac yb_kv KV := apply KV; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | assumption].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing} {PX : PAXcalls lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma yb_dE_set : forall cx E0 E n w, d_E cx E /\ ew E AT_FL = ew E0 AT_FL -> (AT_FL < n)%nat ->
  d_E cx (ewset E n w) /\ ew (ewset E n w) AT_FL = ew E0 AT_FL.
Proof.
  intros cx E0 E n w ((EE & E32 & HEI & E60 & EF & ESH) & HF) Hn. unfold AT_FL in Hn.
  split; [|rewrite ew_ewset_other by (unfold AT_FL; lia); exact HF].
  split.
  { intros m r Hm. rewrite ew_ewset_other; [exact (EE m r Hm)|].
    pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32 in Hr. lia. }
  split; [rewrite ew_ewset_other by lia; exact E32|].
  split; [apply img_env_ewset_hi; [exact HEI | unfold A_LIM; lia]|].
  split; [rewrite ew_ewset_other by (unfold AT_A; lia); exact E60|].
  split; [rewrite ew_ewset_other by (unfold AT_F; lia); exact EF|].
  rewrite ew_ewset_other by (unfold AT_SH; lia); exact ESH.
Qed.

Ltac yb_dE := lazymatch goal with
  | |- d_E ?cx (ewset ?Ex ?nx ?wx) /\ _ => apply yb_dE_set; [yb_dE | unfold AT_FL; lia]
  | |- _ => split; [apply d_E_env; assumption | reflexivity]
  end.

Lemma yb_pcall_pi : forall (fq : YK11.FPState) E ss ms (s : asym),
  st_ok (fx := fq) SEGS E (setpc ss (SIGMA s)) ms ->
  st_ok_pi (fx := fq) SEGS VAL E (setpc ss (SIGMA s - BASE)) ms.
Proof.
  intros fq E ss ms s HS. unfold st_ok_pi, abs_ss, setpc in *.
  cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
  replace (BASE + (SIGMA s - BASE)) with (SIGMA s) by lia. exact HS.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis PAL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBRT : d_body_rt_stmt B.

Lemma yb_land_body : forall (fq : YK11.FPState) cx h n xb shf ly3 S3 (W : world SEGS) mem3 md k Ef ss ms lo hi,
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  d_body B cx h n xb shf ly3 S3 W mem3 ->
  d_E cx Ef -> ew Ef AT_FL = Z_to_bv 64 (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) ->
  st_ok_pi (fx := fq) SEGS VAL Ef ss (restrict (w_H W) ms) ->
  d_land_chk shf (ss_mem ss) = true ->
  d_hslots cx h W (ms_mem ms) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a) ->
  mem_grows (rd W mem3) (rd W (ms_mem ms)) ->
  d_S cx - LLVMF_STK <= lo -> hi <= d_S cx -> 0 <= n ->
  d_body B cx h n xb shf ly3 S3 W (ms_mem ms).
Proof.
  intros fq cx h n xb shf ly3 S3 W mem3 md k Ef ss ms lo hi HB HJ HFR HBODY HdE HFL HS Hchk HHS KM HG Hlo Hhi Hn0.
  pose proof (d_land_hs B MT XM_LIB RLO RHI tfib_K DLAND LAWS FFL fq cx h shf ly3 S3 W md k Ef ss ms
    (conj HB (conj HJ HFR)) HdE HFL HS Hchk HHS) as (HFRM1 & HSHD1).
  apply (DBRT cx h n n xb shf shf ly3 S3 W mem3 (ms_mem ms) lo hi (fun a => lo <= a < hi) HBODY Hlo Hhi).
  - intros a Ha. left. exact Ha.
  - intros a Ha Hna. exact (KM a Ha Hna).
  - intros a _ Hp. eapply apresent_grows; [exact HG | exact Hp].
  - exact HFRM1.
  - exact HSHD1.
  - lia.
Qed.

Theorem a3j_B1 : jseg_B1 B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W0 c0 T0 T1 buf fin ii count acc vpad W cf HIN.
unfold jobj_in, jcut, d_arm_at_pf, d_at in HIN.
destruct HIN as (HFROM & fq & ly3 & S3 & regs & mem3 & md3 & k & accm & -> & Hfrm0 & HBASE & HJ & HFR & Hk & Hnev &
  HMO & Hacc & Hi & Hn & Hnow & HRL & (R26 & R24 & R25 & (R21 & R22 & R23)) & (HSP1 & HTAB & HBUF & HXS) &
  HSP0 & HBODY).
destruct HXS as (HFIN & Hii & Hcount & Hlacc & HOBJS & HMEM).
pose proof HRL as (Rsp & Rgp & Rtp & Rs0 & Rs1 & Rs19 & Rs18 & Rs20 & Rs27).
pose proof HFIN as (HJR & Hfinb & HNOWS & HTLEN & HTOKS).
pose proof HBUF as (Hcap & HGARR).
pose proof HMEM as (Mlen & Mpad & Mobjs & Mall).
pose proof HBODY as (T & G & Lk & HH & HFRM & HSHD & HOBJ & HBLK & HINP & HIMG & HOFFF & HGEO & HCAN & HSTKF & HAWRF).
pose proof HFRM as (E & HE & HREG & HFLAG & _).
assert (HCTX : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj HBASE (conj HJ HFR)).
pose proof (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HCTX)
  as (GS16 & GSlo & GShi & GF4096 & GFceil & GFapp & GFoff & GF32 & GFpres & GFSpres & GSTKpres & HAR3 & HFin3 & EFA3 & EFL3).
pose proof alloc_ceiling_value as Hceil0.
pose proof (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (GA1 & GA32).
unfold MFRAME in GA1. unfold LLVMF_STK in GSlo.
pose proof HBLK as (HPerm0 & _ & _ & HOFFb).
assert (Hinbuf : In (buf, Z.max (slot_ser_defs.ser_cap op) 1) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym HPerm0)). unfold a3_xb. cbn [app]. left. reflexivity. }
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hinbuf) as (Hbuf16 & Hbuf4096 & Hbufceil & Hbufapp & _ & _ & _).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W mem3 md3 _ _ _ _ HAR3 Hinbuf HFin3) as Hbsep.
rewrite EFA3 in Hbsep. unfold zdisjoint in Hbsep. cbn [fst snd] in Hbsep.
change (fs_frame_bytes DFRAME_CLASS) with 4096 in Hbsep.
assert (Hreq : req_size (Z.max (slot_ser_defs.ser_cap op) 1) = slot_ser_defs.ser_cap op).
{ unfold req_size. destruct (Z.eqb_spec (Z.max (slot_ser_defs.ser_cap op) 1) 0); lia. }
rewrite Hreq in Hbufceil, Hbufapp, Hbsep.
assert (Hrle : a3_r T1 now <= 969) by (unfold a3_r; lia).
pose proof (jobjs_from_step (a3_text T1 now) fin ii count acc HOBJS) as (H123 & HCASE).
rewrite (json_ws_id (a3_text T1 now) (ii + 1) HNOWS ltac:(lia)) in HCASE.
pose proof (at_byte_true _ _ _ H123) as (Hlt0 & Hby0).
assert (Hlt1 : ii + 1 < jlen (a3_text T1 now)).
{ destruct HCASE as [(H125 & _) | (_ & HPF)].
  - exact (proj1 (at_byte_true _ _ _ H125)).
  - destruct (jpairs_from_step (a3_text T1 now) fin (ii + 1) jobj_empty count acc HPF)
      as (jj & kk & ks & kl & _ & _ & _ & _ & _ & HJS & _).
    exact (jscalar_in (a3_text T1 now) (ii + 1) jj kk ks kl HJS). }
assert (Hcnt : count + 1 <= fst fin).
{ destruct HCASE as [(_ & HAFT) | (_ & HPF)].
  - exact (jobjs_after_count _ _ _ _ _ _ HAFT).
  - exact (jpairs_from_count _ _ _ _ _ _ HPF). }
assert (Hrlen : a3_r T1 now = jlen (a3_text T1 now)) by reflexivity.
assert (Hb1 : 33 <= jbyte (a3_text T1 now) (ii + 1) <= 255) by (apply jno_ws_byte; [exact HNOWS | lia]).
destruct (jk_byte W mem3 buf (a3_text T1 now ++ [0]) ii HGARR
  ltac:(rewrite length_app; cbn [length]; unfold jlen in *; lia)) as (Hv0 & _).
destruct (jk_byte W mem3 buf (a3_text T1 now ++ [0]) (ii + 1) HGARR
  ltac:(rewrite length_app; cbn [length]; unfold jlen in *; lia)) as (Hv1 & _).
rewrite (jk_nth_app (a3_text T1 now) ii ltac:(lia)) in Hv0.
rewrite (jk_nth_app (a3_text T1 now) (ii + 1) ltac:(lia)) in Hv1.
rewrite Hby0 in Hv0.
replace (buf + (ii + 1)) with (buf + ii + 1) in Hv1 by lia.
assert (HL1 : length T1 = 400%nat).
{ destruct HTAB as ((removed & _ & Hpost) & _). exact (proj1 Hpost). }
assert (Hlo : Z.of_nat (length (map (fun b : byte => bv_unsigned b) (slot_ser_defs.objs_bytes buf vpad (acc ++ [jobj_empty]))))
  = 144 * (count + 1)).
{ rewrite length_map, (jb_objs_bytes_len buf vpad (acc ++ [jobj_empty]) Mlen Mall), length_app, Hlacc.
  cbn [length]. lia. }
set (nbv := if jbyte (a3_text T1 now) (ii + 1) =? 125 then 33 else jbyte (a3_text T1 now) (ii + 1)).
assert (Hnbv : 33 <= nbv <= 255 /\ nbv <> 125).
{ unfold nbv. destruct (Z.eqb_spec (jbyte (a3_text T1 now) (ii + 1)) 125); lia. }
set (ex := [Z_to_bv 64 (buf + ii); Z_to_bv 64 nbv]).
set (vals := jk_vals regs ex).
pose proof HE as (EE & E32 & HEI0 & E60 & EF & ESH).
assert (EO : forall nn, (nn < AT_FL)%nat -> ew (d_env cx E vals) nn = ew E nn)
  by (intros nn Hnn; apply d_env_old; exact Hnn).
assert (ENP : ew (d_env cx E vals) 563 = Z_to_bv 64 (buf + ii)) by exact (jk_xe cx E regs ex 0 ltac:(cbn; lia)).
assert (ENB : ew (d_env cx E vals) 564 = Z_to_bv 64 nbv) by exact (jk_xe cx E regs ex 1 ltac:(cbn; lia)).
assert (X3 : ew (d_env cx E vals) 534 = getr regs 3) by exact (jk_x cx E regs ex 3 ltac:(lia)).
assert (X4 : ew (d_env cx E vals) 535 = getr regs 4) by exact (jk_x cx E regs ex 4 ltac:(lia)).
assert (X18 : ew (d_env cx E vals) 549 = getr regs 18) by exact (jk_x cx E regs ex 18 ltac:(lia)).
assert (X20 : ew (d_env cx E vals) 551 = getr regs 20) by exact (jk_x cx E regs ex 20 ltac:(lia)).
assert (X21 : ew (d_env cx E vals) 552 = getr regs 21) by exact (jk_x cx E regs ex 21 ltac:(lia)).
assert (X22 : ew (d_env cx E vals) 553 = getr regs 22) by exact (jk_x cx E regs ex 22 ltac:(lia)).
assert (X23 : ew (d_env cx E vals) 554 = getr regs 23) by exact (jk_x cx E regs ex 23 ltac:(lia)).
assert (X24 : ew (d_env cx E vals) 555 = getr regs 24) by exact (jk_x cx E regs ex 24 ltac:(lia)).
assert (X25 : ew (d_env cx E vals) 556 = getr regs 25) by exact (jk_x cx E regs ex 25 ltac:(lia)).
assert (X26 : ew (d_env cx E vals) 557 = getr regs 26) by exact (jk_x cx E regs ex 26 ltac:(lia)).
assert (Ulnot : w64 (Z.lnot buf) = Z_to_bv 64 (2 ^ 64 - 1 - buf)) by (apply jk_lnot; lia).
assert (U21 : U (d_env cx E vals) (SOff 552 0) = ii) by (apply (U_atom _ 552 ii (eq_trans X21 R21)); lia).
assert (U211 : U (d_env cx E vals) (SOff 552 1) = ii + 1) by (apply (U_atom_off _ 552 ii 1 (eq_trans X21 R21)); lia).
assert (U24 : U (d_env cx E vals) (SOff 555 0) = buf) by (apply (U_atom _ 555 buf (eq_trans X24 R24)); lia).
assert (U25 : U (d_env cx E vals) (SOff 556 0) = 2 ^ 64 - 1 - buf)
  by (apply (U_atom _ 556 (2 ^ 64 - 1 - buf) (eq_trans X25 (eq_trans R25 Ulnot))); lia).
assert (U26 : U (d_env cx E vals) (SOff 557 0) = a3_r T1 now)
  by (apply (U_atom _ 557 (a3_r T1 now) (eq_trans X26 R26)); unfold a3_r; lia).
assert (UNP : U (d_env cx E vals) (SOff 563 0) = buf + ii) by (apply (U_atom _ 563 (buf + ii) ENP); lia).
assert (UNP1 : U (d_env cx E vals) (SOff 563 1) = buf + ii + 1) by (apply (U_atom_off _ 563 (buf + ii) 1 ENP); lia).
assert (UNB : U (d_env cx E vals) (SOff 564 0) = nbv) by (apply (U_atom _ 564 nbv ENB); lia).
assert (HFA : atoms_ok (d_env cx E vals) yb1_fa).
{ unfold yb1_fa. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  change YB1_NP with 563%nat. change YB1_NB with 564%nat.
  rewrite X20, Rs20, ENP, ENB. unfold w64. rewrite !unsigned_lit_small by lia.
  rewrite Z.pow_0_r, !Z.mod_1_r. repeat split; lia. }
assert (HCS : conds_ok (d_env cx E vals) yb1_cs).
{ unfold yb1_cs. cbn [conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
  change YB1_NB with 564%nat.
  rewrite branch_ltu_U, U21, U26. split; [apply Z.ltb_lt; lia|].
  rewrite branch_ltu_U, U211, U26. split; [apply Z.ltb_lt; lia|].
  rewrite branch_geu_U, U25, U211. split; [apply negb_true_iff, Z.ltb_ge; lia|].
  rewrite branch_ne_U, UNB, U_lit by lia. split; [apply negb_true_iff, Z.eqb_neq; lia | exact I]. }
pose proof (DSEAT LAWS PAL fq cx dsh_scr ly3 S3 W regs mem3 md3 k E OBJ_OFF jk_sr vals [] [] []
  (d_facts yb1_fa yb1_cs) HCTX HE HREG HFLAG (jk_regs_ok B cx E regs ex HE HRL)
  (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals yb1_fa yb1_cs HCTX HE HFA HCS)
  (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
pose proof (st_ok_pi_submem _ _ _ yb1_rs HS0 (yb1_sub _ _ _) ltac:(vm_compute; reflexivity)) as HS1.
clear HS0. cbn [ss_d ss_pc ss_regs ss_resv ss_facts] in HS1.
assert (HA0 : sv_denot (d_env cx E vals) (fst yb1_al0) = sv_denot (d_env cx E vals) (snd yb1_al0)).
{ unfold yb1_al0. cbn [fst snd]. apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
  change YB1_NP with 563%nat. rewrite U24, U21, UNP. rewrite zcanon_id by (unfold M64; lia). reflexivity. }
assert (HA1 : sv_denot (d_env cx E vals) (fst yb1_al1) = sv_denot (d_env cx E vals) (snd yb1_al1)).
{ unfold yb1_al1. cbn [fst snd]. apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
  change YB1_NP with 563%nat. rewrite U24, U211, UNP1. rewrite zcanon_id by (unfold M64; lia). lia. }
pose proof (st_ok_pi_add_alias _ _ _ _ _ HS1 HA0) as HS2. clear HS1.
pose proof (st_ok_pi_add_alias _ _ _ _ _ HS2 HA1) as HS3. clear HS2.
cbn [set_facts ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS3.
assert (B2 : bv_unsigned (ew (d_env cx E vals) 2) = d_S cx)
  by (rewrite EO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (B60 : bv_unsigned (ew (d_env cx E vals) 60) = d_A cx)
  by (rewrite EO by (unfold AT_FL; lia); change 60%nat with AT_A; rewrite E60; apply unsigned_lit_small; lia).
assert (B516 : bv_unsigned (ew (d_env cx E vals) 516) = d_FB cx)
  by (rewrite EO by (unfold AT_FL; lia); change 516%nat with AT_F; rewrite EF; apply unsigned_lit_small; lia).
assert (B529 : bv_unsigned (ew (d_env cx E vals) 529) = shadow_addr (d_FB cx))
  by (rewrite EO by (unfold AT_FL; lia); change 529%nat with AT_SH; rewrite ESH; apply unsigned_lit_small;
      unfold shadow_addr, SHADOW_OFF; lia).
assert (B552 : bv_unsigned (ew (d_env cx E vals) 552) = ii)
  by (rewrite X21, R21; unfold w64; apply unsigned_lit_small; lia).
assert (B563 : bv_unsigned (ew (d_env cx E vals) 563) = buf + ii) by (rewrite ENP; apply unsigned_lit_small; lia).
assert (U2w : ew (d_env cx E vals) 2 = w64 (d_S cx))
  by (rewrite EO by (unfold AT_FL; lia); rewrite (EE 2%nat 2%bv eq_refl);
      unfold w64, d_S, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (U60w : ew (d_env cx E vals) 60 = w64 (d_A cx))
  by (rewrite EO by (unfold AT_FL; lia); exact E60).
assert (U32w : ew (d_env cx E vals) 32 = w64 SHADOW_OFF)
  by (rewrite EO by (unfold AT_FL; lia); exact E32).
assert (U529w : ew (d_env cx E vals) 529 = w64 (shadow_addr (d_FB cx)))
  by (rewrite EO by (unfold AT_FL; lia); exact ESH).
assert (HDJ : forall v, all_disjoint (d_env cx E vals) (yb1_rg v) yb1_rs).
{ intros v. unfold yb1_rg, yb1_rs, fshadow_region. cbn [all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. change YB1_NP with 563%nat.
  change AT_STK with 2%nat. change AT_A with 60%nat. change AT_F with 516%nat. change AT_SH with 529%nat.
  rewrite B563, B2, B60, B516, B529. change (fs_frame_bytes DFRAME_CLASS) with 4096.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr, SHADOW_OFF in *.
  unfold LLVMF_STK in *. unfold a3_r, jlen in *. repeat split; lia. }
assert (HC0 : YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (buf + ii) (YP09.mkChunk 0 (CVal 1 (SLit 123)))).
{ apply (chunk_ok_val SEGS _ _ (buf + ii) 0 1 (SLit 123) 123); [reflexivity | cbn; lia | cbn; lia |].
  cbn [N.to_nat]. rewrite Z.add_0_r. exact Hv0. }
assert (HRG : forall v z, sv_denot (d_env cx E vals) v = Z_to_bv 64 z -> 0 <= z < 256 ->
  val_mem SEGS (rd W mem3) (buf + ii + 1) 1 z -> region_ok SEGS (d_env cx E vals) (rd W mem3) (yb1_rg v)).
{ intros v z Hvz Hz Hm. unfold region_ok, yb1_rg. cbv zeta.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  change YB1_NP with 563%nat. rewrite B563.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [exact HC0 | constructor; [|constructor]].
  apply (chunk_ok_val SEGS _ _ (buf + ii) 1 1 v z); [exact Hvz | cbn; lia | cbn; lia | cbn [N.to_nat]; exact Hm]. }
assert (U32 : U (d_env cx E vals) (SOff 32 0) = SHADOW_OFF).
{ apply (U_atom _ 32 SHADOW_OFF); [rewrite EO by (unfold AT_FL; lia); exact E32 | unfold SHADOW_OFF; lia]. }
assert (SHOK : sh_ok SEGS (SOff 32 0) yb1_SH (d_env cx E vals) (rd W mem3)).
{ unfold yb1_SH. constructor; [|constructor].
  apply (jk_shent B LAWS ly3 S3 W mem3 md3 _ YB1_NP buf (Z.max (slot_ser_defs.ser_cap op) 1) 0 2 HAR3 Hinbuf);
    [exact U32 | lia | change YB1_NP with 563%nat; rewrite UNP; lia
    | change YB1_NP with 563%nat; rewrite UNP, Hreq; unfold a3_r, jlen in *; lia]. }
assert (HEI : img_env VAL A_LIM (d_env cx E vals)) by exact (proj1 (proj2 (proj2 (d_E_env cx E vals HE)))).
pose proof (d_hslots_of_frame cx h dsh_scr W mem3 HFRM) as (H184 & H120 & H136 & H376 & H280 & H232 & H264).
pose proof HSP1 as ((H208 & H320) & H192 & H200).
pose proof (paj_run (fx := fq) B LAWS) as RUN.
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
unfold cfg_at, w64.
rewrite restrict_mkst_fx in HS3.
destruct HCASE as [(H125 & HAFT) | (H125f & HPF)].
- pose proof (at_byte_true _ _ _ H125) as (_ & Hby1). rewrite Hby1 in Hv1.
  pose proof (st_ok_pi_add_region _ _ _ (yb1_rg (SLit 125)) HS3 ltac:(vm_compute; reflexivity)
    (HRG (SLit 125) 125 eq_refl ltac:(lia) Hv1) (HDJ (SLit 125))) as HS.
  clear HS3. rewrite <- restrict_mkst_fx in HS.
  norm_ss HS.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan OEND_OFF.
  { lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fp b0 bc lyy own) end.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx));
      [reflexivity | rewrite B60; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
  lazymatch type of HFr with frame_of _ ?rs _ _ =>
    assert (HWR : forall a, in_wrange (d_env cx E vals) rs a -> d_A cx + 352 <= a < d_A cx + 360) end.
  { intros a (r & Hin & Ha).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin.
    destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia. }
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 352 <= a < d_A cx + 360) ->
    aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a)
    by (intros a Ha Hna; apply (aview_eq_of SEGS); apply HFr; rewrite unsigned_lit_small by lia;
        intros Hw; exact (Hna (HWR a Hw))).
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 352 <= a < d_A cx + 360) ->
    mbyte SEGS (rd W (ms_mem ms)) a = mbyte SEGS (rd W mem3) a)
    by (intros a Ha Hna; apply (mbyte_of_aview SEGS); apply KM; assumption).
  assert (KV : forall a (nn : nat) v, 0 <= a -> a + Z.of_nat nn <= 2 ^ 64 ->
    (a + Z.of_nat nn <= d_A cx + 352 \/ d_A cx + 360 <= a) ->
    val_mem SEGS (rd W mem3) a nn v -> val_mem SEGS (rd W (ms_mem ms)) a nn v)
    by (intros a nn v H0 H1 H2 Hv; apply (val_mem_frame SEGS (rd W mem3)); [intros x Hx; apply KB; lia | exact Hv]).
  assert (KG : forall a l, 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
    (a + Z.of_nat (length l) <= d_A cx + 352 \/ d_A cx + 360 <= a) ->
    garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W (ms_mem ms)) a l)
    by (intros a l H0 H1 H2 Hg; apply (garr8_frame SEGS (rd W mem3)); [exact Hg | intros x Hx; apply KB; lia]).
  assert (HHS1 : d_hslots cx h W (ms_mem ms)).
  { split; [yb_kv KV|]. split; [yb_kv KV|]. split; [yb_kv KV|]. split; [yb_kv KV|].
    split; [yb_kv KV|]. split; [yb_kv KV | yb_kv KV]. }
  lazymatch type of HS with st_ok_pi _ _ ?Ef ?ssf _ =>
    assert (HdEf : d_E cx Ef /\ ew Ef AT_FL = ew (d_env cx E vals) AT_FL) by yb_dE;
    assert (Hchk : d_land_chk dsh_scr (ss_mem ssf) = true) by (vm_compute; reflexivity) end.
  assert (HBODY1 : d_body B cx h n (a3_xb buf op) dsh_scr ly3 S3 W (ms_mem ms)).
  { apply (yb_land_body fq cx h n (a3_xb buf op) dsh_scr ly3 S3 W mem3 md' k _ _ ms (d_A cx + 352) (d_A cx + 360)
      HBASE HJ HFR HBODY (proj1 HdEf) (eq_trans (proj2 HdEf) (d_env_fl cx E vals)) HS Hchk HHS1 KM HG);
      unfold LLVMF_STK; lia. }
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
  prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25.
  prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl). cbn [ss_pc].
  apply SRr_ret. right.
  unfold joend_in, jcut. split; [exact HFROM|].
  unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, accm.
  split; [unfold cfg_at, w64, OEND_OFF; reflexivity|].
  split; [exact Hfrm0|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|].
  split; [exact Hnev|].
  split; [exact HMO|]. split; [exact Hacc|]. split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split.
  { split; [unfold spZ; rewrite Q2; exact B60|].
    split; [rewrite Q3, X3; exact Rgp|]. split; [rewrite Q4, X4; exact Rtp|].
    split; [rewrite Q8; exact U2w|]. split; [rewrite Q9; exact U60w|].
    split; [rewrite Q19; exact U32w|]. split; [rewrite Q18, X18; exact Rs18|].
    split; [rewrite Q20, X20; exact Rs20|]. rewrite Q27; exact U529w. }
  split.
  { split; [rewrite Q26, X26; exact R26|]. split; [rewrite Q24, X24; exact R24|].
    split; [rewrite Q25, X25; exact R25|].
    split; [rewrite Q21, B552; reflexivity | rewrite Q22, X22; exact R22]. }
  split.
  { split.
    { split; [split; yb_kv KV|]. split; yb_kv KV. }
    split.
    { split; [exact (proj1 HTAB)|].
      apply KG; [unfold d_obj, dobj_off; lia | rewrite length_map, HL1; unfold d_obj, dobj_off; lia
                | rewrite length_map, HL1; unfold d_obj, dobj_off; lia | exact (proj2 HTAB)]. }
    split.
    { split; [exact Hcap|].
      apply KG; [lia | rewrite length_app; cbn [length]; unfold a3_r in *; lia
                | rewrite length_app; cbn [length]; unfold a3_r in *; lia | exact HGARR]. }
    split; [exact HFIN|]. split; [lia|]. split; [exact Hcount|]. split; [exact Hlacc|].
    split; [exact H125|]. split; [exact HAFT|]. split; [reflexivity|].
    split; [exact (jb_empty_in (a3_text T1 now))|].
    split; [exact Mlen|].
    split.
    { apply KG; [lia | rewrite length_map, Mlen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                | rewrite length_map, Mlen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Mpad]. }
    split; [|exact Mall].
    apply KG; [unfold d_obj, dobj_off; lia | rewrite Hlo; unfold d_obj, dobj_off; lia
              | rewrite Hlo; unfold d_obj, dobj_off; lia | exact Mobjs]. }
  split; [split; yb_kv KV | exact HBODY1].
- assert (Hne : jbyte (a3_text T1 now) (ii + 1) <> 125).
  { rewrite at_byte_spec in H125f by (unfold jlen in *; lia). apply Z.eqb_neq. exact H125f. }
  assert (Enbv : nbv = jbyte (a3_text T1 now) (ii + 1)).
  { unfold nbv. destruct (Z.eqb_spec (jbyte (a3_text T1 now) (ii + 1)) 125); [contradiction | reflexivity]. }
  pose proof (st_ok_pi_add_region _ _ _ (yb1_rg (SOff YB1_NB 0)) HS3 ltac:(vm_compute; reflexivity)
    (HRG (SOff YB1_NB 0) nbv ltac:(change YB1_NB with 564%nat; apply jk_den0; [exact ENB | lia]) ltac:(lia)
      ltac:(rewrite Enbv; exact Hv1)) (HDJ (SOff YB1_NB 0))) as HS.
  clear HS3. rewrite <- restrict_mkst_fx in HS.
  norm_ss HS.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { lazymatch goal with |- awr_ok ?Ey ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok Ey rs' stk sp0 fp b0 bc lyy own) end.
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx));
      [reflexivity | rewrite B60; lia | cbn; unfold LLVMF_STK; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  set (md' := with_vm_backing (m_vm_lazy md3) mat md3) in *.
  lazymatch type of HFr with frame_of _ ?rs _ _ =>
    assert (HWR : forall a, in_wrange (d_env cx E vals) rs a -> d_A cx + 352 <= a < d_A cx + 360) end.
  { intros a (r & Hin & Ha).
    lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
    cbn [In] in Hin.
    destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]];
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia. }
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 352 <= a < d_A cx + 360) ->
    aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a)
    by (intros a Ha Hna; apply (aview_eq_of SEGS); apply HFr; rewrite unsigned_lit_small by lia;
        intros Hw; exact (Hna (HWR a Hw))).
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 352 <= a < d_A cx + 360) ->
    mbyte SEGS (rd W (ms_mem ms)) a = mbyte SEGS (rd W mem3) a)
    by (intros a Ha Hna; apply (mbyte_of_aview SEGS); apply KM; assumption).
  assert (KV : forall a (nn : nat) v, 0 <= a -> a + Z.of_nat nn <= 2 ^ 64 ->
    (a + Z.of_nat nn <= d_A cx + 352 \/ d_A cx + 360 <= a) ->
    val_mem SEGS (rd W mem3) a nn v -> val_mem SEGS (rd W (ms_mem ms)) a nn v)
    by (intros a nn v H0 H1 H2 Hv; apply (val_mem_frame SEGS (rd W mem3)); [intros x Hx; apply KB; lia | exact Hv]).
  assert (KG : forall a l, 0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 ->
    (a + Z.of_nat (length l) <= d_A cx + 352 \/ d_A cx + 360 <= a) ->
    garr8 SEGS (rd W mem3) a l -> garr8 SEGS (rd W (ms_mem ms)) a l)
    by (intros a l H0 H1 H2 Hg; apply (garr8_frame SEGS (rd W mem3)); [exact Hg | intros x Hx; apply KB; lia]).
  assert (HHS1 : d_hslots cx h W (ms_mem ms)).
  { split; [yb_kv KV|]. split; [yb_kv KV|]. split; [yb_kv KV|]. split; [yb_kv KV|].
    split; [yb_kv KV|]. split; [yb_kv KV | yb_kv KV]. }
  pose proof (yb_pcall_pi fq _ _ _ AS_json_scalar HS) as HSpi.
  lazymatch type of HSpi with st_ok_pi _ _ ?Ef ?ssf _ =>
    assert (HdEf : d_E cx Ef /\ ew Ef AT_FL = ew (d_env cx E vals) AT_FL) by yb_dE;
    assert (Hchk : d_land_chk dsh_scr (ss_mem ssf) = true) by (cbn [setpc ss_mem]; vm_compute; reflexivity);
    assert (B60f : bv_unsigned (ew Ef 60) = d_A cx) by (rewrite !ew_ewset_other by lia; exact B60);
    assert (D553 : sv_denot Ef (SOff 553 0) = Z_to_bv 64 count)
      by (apply jk_den0; [rewrite !ew_ewset_other by lia; rewrite X22, R22; reflexivity | lia]) end.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ HSpi eq_refl) as RA.
  cbn [ms_mem restrict] in RA.
  assert (V352 : val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 352) 8 count).
  { exact (field_of_region _ _ 60%nat (d_A cx) _ 0 472 352 360 352 8%N (SOff 553 0) count RA B60f
      ltac:(apply jk_in; vm_compute; reflexivity) D553 ltac:(cbn; lia) ltac:(cbn; lia)). }
  assert (HBODY1 : d_body B cx h n (a3_xb buf op) dsh_scr ly3 S3 W (ms_mem ms)).
  { apply (yb_land_body fq cx h n (a3_xb buf op) dsh_scr ly3 S3 W mem3 md' k _ _ ms (d_A cx + 352) (d_A cx + 360)
      HBASE HJ HFR HBODY (proj1 HdEf) (eq_trans (proj2 HdEf) (d_env_fl cx E vals)) HSpi Hchk HHS1 KM HG);
      unfold LLVMF_STK; lia. }
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
  prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
  prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
  prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
  prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
  pmkst HS.
  rewrite pa_sigma_json_scalar.
  apply SRr_ret. left.
  unfold jb_call, jsc_in, jcut. split; [exact HFROM|].
  unfold d_arm_at_pf, d_at.
  exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md', k, accm.
  split; [unfold cfg_at, w64; reflexivity|].
  split; [exact Hfrm0|]. split; [exact HBASE|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact Hk|].
  split; [exact Hnev|].
  split; [exact HMO|]. split; [exact Hacc|]. split; [exact Hi|]. split; [exact Hn|]. split; [exact Hnow|].
  split.
  { split; [unfold spZ; rewrite Q2; exact B60|].
    split; [rewrite Q3, X3; exact Rgp|]. split; [rewrite Q4, X4; exact Rtp|].
    split; [rewrite Q8; exact U2w|]. split; [rewrite Q9; exact U60w|].
    split; [rewrite Q19; exact U32w|]. split; [rewrite Q18, X18; exact Rs18|].
    split; [rewrite Q20, X20; exact Rs20|]. rewrite Q27; exact U529w. }
  split.
  { split; [rewrite Q26, X26; exact R26|]. split; [rewrite Q24, X24; exact R24|].
    split; [rewrite Q25, X25; exact R25|].
    split; [unfold w64, JSC_KEY_RA; exact Q1|].
    split; [rewrite Q10, X24; exact R24|].
    split; [rewrite Q11, B552; reflexivity|].
    split; [rewrite Q12, X26; exact R26|].
    split; [rewrite Q13, B60; unfold w64, JSC_KEY_OFF; reflexivity|].
    unfold jb_R. split; [rewrite Q22, X22; exact R22 | rewrite Q23, X23; exact R23]. }
  split.
  { split.
    { split; [split; yb_kv KV|]. split; yb_kv KV. }
    split.
    { split; [exact (proj1 HTAB)|].
      apply KG; [unfold d_obj, dobj_off; lia | rewrite length_map, HL1; unfold d_obj, dobj_off; lia
                | rewrite length_map, HL1; unfold d_obj, dobj_off; lia | exact (proj2 HTAB)]. }
    split.
    { split; [exact Hcap|].
      apply KG; [lia | rewrite length_app; cbn [length]; unfold a3_r in *; lia
                | rewrite length_app; cbn [length]; unfold a3_r in *; lia | exact HGARR]. }
    unfold jb_X. split; [exact HFIN|]. split; [exact Hii|]. split; [exact Hcount|]. split; [exact Hlacc|].
    split; [exact HPF|].
    split; [|exact V352].
    split; [exact Mlen|].
    split.
    { apply KG; [lia | rewrite length_map, Mlen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                | rewrite length_map, Mlen; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact Mpad]. }
    split; [|exact Mall].
    apply KG; [unfold d_obj, dobj_off; lia | rewrite Hlo; unfold d_obj, dobj_off; lia
              | rewrite Hlo; unfold d_obj, dobj_off; lia | exact Mobjs]. }
  split; [split; yb_kv KV | exact HBODY1].
Qed.

End h.
End f.
End d.
