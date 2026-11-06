(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_stamp_headamp on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACbf.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACf6.v, proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v, with its module paths and module names changed; 501 of its 566 lines of code are new or changed and 1213 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/DiscoArm3AgeLeft.v, with its module paths and module names changed; 223 of its 321 lines of code are new or changed and 468 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntBodyStmt DiscoEntSeat DiscoEntRecLib DiscoEntRecCut DiscoEntRecP1 DiscoEntRec2Kit.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK11.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma e1_zbv : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact H. Qed.
Lemma e1_U : forall E x a, sv_denot E x = Z_to_bv 64 a -> U E x = a mod 2 ^ 64.
Proof. intros E x a H. unfold U. rewrite H, Z_to_bv_unsigned. reflexivity. Qed.
Lemma e1_dn_atom : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma e1_dn_or : forall E x y a b, sv_denot E x = Z_to_bv 64 a -> sv_denot E y = Z_to_bv 64 b ->
  sv_denot E (SAlu ALU_OR x y) = Z_to_bv 64 (Z.lor (a mod 2 ^ 64) (b mod 2 ^ 64)).
Proof.
intros E x y a b Hx Hy. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
rewrite (e1_U E x a Hx), (e1_U E y b Hy). apply e1_zbv. unfold zcanon, M64. apply Z.mod_mod. lia.
Qed.
Lemma e1_lor : forall hi lo, 0 <= lo < 256 -> 0 <= hi -> hi mod 256 = 0 -> Z.lor hi lo = hi + lo.
Proof.
intros hi lo Hl Hh Hm. pose proof (Z.div_mod hi 256 ltac:(lia)) as D.
replace hi with ((hi / 256) * 256) by lia. apply rl_lor_add; [apply Z.div_pos; lia | lia].
Qed.
Lemma e1_dn_add : forall E x y a b, sv_denot E x = Z_to_bv 64 a -> sv_denot E y = Z_to_bv 64 b ->
  sv_denot E (SAlu ALU_ADD x y) = Z_to_bv 64 (a + b).
Proof.
intros E x y a b Hx Hy. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
rewrite (e1_U E x a Hx), (e1_U E y b Hy). apply e1_zbv. unfold zcanon, M64.
rewrite Z.mod_mod by lia. rewrite <- Zplus_mod. reflexivity.
Qed.
Ltac e1_dn A11 A12 A23 :=
  lazymatch goal with
  | |- sv_denot _ (SLit _) = _ => reflexivity
  | |- sv_denot _ (SAlu ALU_ADD _ _) = _ => eapply e1_dn_add; [e1_dn A11 A12 A23 | e1_dn A11 A12 A23]
  | |- sv_denot _ (SAlu ALU_OR _ _) = _ => eapply e1_dn_or; [e1_dn A11 A12 A23 | e1_dn A11 A12 A23]
  | |- sv_denot _ (SOff 542 0) = _ => exact A11
  | |- sv_denot _ (SOff 543 0) = _ => exact A12
  | |- sv_denot _ (SOff 554 0) = _ => exact A23
  end.

Ltac e1_win HS n wlo whi :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let RO := fresh "RO" in
pose proof (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) as RO;
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r wlo whi) HS ltac:(vm_compute; reflexivity) eq_refl
  ltac:(vm_compute; reflexivity)
  (region_ok_rewindow _ Ex _ r wlo whi RO ltac:(intros o Ho; apply (proj1 (proj2 (proj2 RO))); cbn; lia))) as HS3;
clear HS RO; rename HS3 into HS; norm_ss HS end.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

Lemma e1_vm_mod : forall (m : word -> option byte) a v, val_mem SEGS m a 8 v -> val_mem SEGS m a 8 (v mod 2 ^ 64).
Proof.
intros m a v H k Hk. rewrite (H k Hk). f_equal. f_equal.
first [unfold YO0f.le_byte | unfold YG0f.le_byte]. change (8 * Z.of_nat 8) with 64. rewrite Zmod_mod. reflexivity.
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
Hypothesis MT_TRIV : MT = ameter_triv.
Ltac e1_rew := cbn [ew havoc d_env AT_FL AT_X Nat.ltb Nat.leb Nat.sub Nat.add nth r2_vals].
Ltac e1_rU := e1_rew; repeat match goal with H : bv_unsigned (ew ?Ex ?q) = _ |- context [bv_unsigned (ew ?Ex ?q)] => rewrite H end.
Ltac e1_awr cx :=
  cbn [ss_mem];
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 60%nat (d_A cx - d_S cx));
      [ reflexivity | e1_rU; unfold w64; rewrite ?unsigned_lit_small by lia; lia
      | cbn [YP09.r_wlo]; unfold LLVMF_STK, MFRAME in *; lia | cbn [YP09.r_whi]; unfold MFRAME in *; lia | ] ].
Ltac e1_rwin :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros b wlo whi a Hin Ha; vm_compute in Hin;
  repeat (destruct Hin as [Hin|Hin];
    [ injection Hin; intros; subst; cbn [base_val] in Ha; first [ lia | revert Ha; e1_rU; intros Ha; lia ] | ]);
  destruct Hin.
Ltac e1_rupd :=
  lazymatch goal with
  | HFr : frame_of ?Eo ?rs (mrestrict ?Hh ?m1) (mrestrict _ ?m2),
    MEQ : forall a, _ -> ~ (?lo <= a < ?hi) -> aview _ _ ?m1 a = aview _ _ ?m0 a |- _ =>
    let MEQ2 := fresh "MEQ" in
    pose proof (rl_meq_frame Eo rs Hh m0 m1 m2 lo hi HFr ltac:(e1_rwin) MEQ) as MEQ2; clear MEQ; rename MEQ2 into MEQ
  end;
  lazymatch goal with
  | HG : mem_grows (mrestrict ?Hh ?m1) (mrestrict _ ?m2), MPR : forall a, apresent _ ?m0 a -> apresent _ ?m1 a |- _ =>
    let MPR2 := fresh "MPR" in pose proof (rl_pres_grow Hh m0 m1 m2 HG MPR) as MPR2; clear MPR; rename MPR2 into MPR
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.

Hypothesis DSEAT : d_seat_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DFACTS : d_facts_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DLAND : d_land_stmt B MT XM_LIB RLO RHI tfib_K.
Hypothesis DBRT : d_body_rt_stmt B.

Lemma e1_leaf : forall (cx : dcx) (h i n now op : Z) (W : world SEGS) (fq : YK11.FPState) ly3 S3
  (regs : bvmap 5 word) mem3 k acc (E : env) (vals : list word) (ss : sstate) (ms : machine_state) (md : Model),
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx -> frames S3 = [(DFRAME_CLASS, c_fpos cx)] ->
  0 <= k <= EV_HEAD i -> st_nev S3 <= st_nev (c_S cx) + EV_HEAD i ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i ->
  0 <= i < MAX_OPS -> 0 <= n -> 0 <= now < 2 ^ 64 -> r2_pure op ->
  d_rL B cx regs -> val_mem SEGS (rd W mem3) (d_A cx + 232) 8 i ->
  d_body B cx h n [] dsh_loop ly3 S3 W mem3 -> d_E cx E ->
  st_ok (fx := fq) SEGS (d_env cx E vals) ss (restrict (w_H W) ms) ->
  ss_pc ss = SIGMA DS___interceptor_trampoline_malloc -> ss_resv ss = None ->
  d_land_chk dsh_loop (ss_mem ss) = true ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 248 <= a < d_A cx + 416) ->
     aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem3 a) ->
  (forall a, apresent (w_H W) mem3 a -> apresent (w_H W) (ms_mem ms) a) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr (ms_regs ms) r = getr regs r) ->
  getr (ms_regs ms) 1 = w64 (BASE + RA_MAL) -> getr (ms_regs ms) 10 = w64 (r2_len cx n) ->
  getr (ms_regs ms) 27 = w64 op -> r2_rk cx n op (ms_regs ms) ->
  r2_mem cx n op W (ms_mem ms) -> val_mem SEGS (rd W (ms_mem ms)) (d_A cx + 344) 8 now ->
  p_mal B MT XM_LIB RLO RHI tfib_K cx h i n now op W (mkCfg ms md).
Proof.
intros cx h i n now op W fq ly3 S3 regs mem3 k acc E vals ss ms md
  Hfrm Hbase Hfrs Hk Hnev Hmo Hacc Hi Hn Hnow Hop HrL H232 Hbody HdE HS Hpc Hrv Hchk HJ MEQ MPR RG R1 R10 R27 HRK HMEM H344.
destruct ss as [p0 r0 f0 m0 v0 g0]. cbn [ss_pc ss_resv ss_mem] in Hpc, Hrv, Hchk. subst p0 v0.
assert (HSpi : st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals)
  (mkSST (SIGMA DS___interceptor_trampoline_malloc - BASE) r0 f0 m0 None g0) (restrict (w_H W) ms)).
{ unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
  replace (BASE + (SIGMA DS___interceptor_trampoline_malloc - BASE)) with (SIGMA DS___interceptor_trampoline_malloc) by ring.
  exact HS. }
assert (HM0 : mo_malloc MT REC_MAX = 0) by (rewrite MT_TRIV; reflexivity).
pose proof Hbase as ((HPRE & _) & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold YG0f.ASAN_CEIL in CR.
assert (HS608 : 608 <= d_S cx) by (unfold d_S, LLVMF_STK in *; lia).
destruct (rl_A_range cx HS608) as [HAr _].
assert (R2 := RG 2%bv ltac:(cbv; tauto)). assert (R3 := RG 3%bv ltac:(cbv; tauto)). assert (R4 := RG 4%bv ltac:(cbv; tauto)).
assert (R8 := RG 8%bv ltac:(cbv; tauto)). assert (R9 := RG 9%bv ltac:(cbv; tauto)). assert (R18 := RG 18%bv ltac:(cbv; tauto)).
assert (R20 := RG 20%bv ltac:(cbv; tauto)). assert (R25 := RG 25%bv ltac:(cbv; tauto)).
destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
unfold p_mal.
apply (r2_land_rt B MT XM_LIB RLO RHI tfib_K LAWS FFL DLAND DBRT fq cx
  (SIGMA DS___interceptor_trampoline_malloc - BASE) (EV_HEAD i) h i n n now [] _ _ W ly3 S3 mem3 md k acc
  (d_env cx E vals) _ ms (d_A cx + 248) (d_A cx + 416)
  Hfrm Hbase HJ Hfrs Hk Hnev Hmo ltac:(lia) Hi ltac:(lia) Hnow Hbody HSpi eq_refl eq_refl
  (d_E_env cx E vals HdE) (d_env_fl cx E vals) Hchk).
- unfold d_S, LLVMF_STK in *. lia.
- unfold d_S in *. lia.
- exact MEQ.
- intros a _ Ha. exact (MPR a Ha).
- intros a Ha. lia.
- split; [unfold spZ in *; rewrite R2; exact Hsp|].
  split; [rewrite R3; exact Hgp|]. split; [rewrite R4; exact Htp|]. split; [rewrite R8; exact H8|].
  split; [rewrite R9; exact H9|]. split; [rewrite R18; exact H18|]. split; [rewrite R20; exact H20|].
  rewrite R25; exact H25.
- exact (conj R1 (conj R10 (conj R27 HRK))).
- exact (conj Hop HMEM).
- split; [|exact H344].
  apply (r2_val_mem_keep W mem3 (ms_mem ms) (d_A cx + 248) (d_A cx + 416)); [exact MEQ | lia | cbn; unfold d_S in *; lia | | exact H232].
  intros x Hx. cbn in Hx. lia.
Qed.

Ltac e1_atom HSro r :=
  rewrite (HSro r); f_equal; vm_compute; reflexivity.

Theorem r2_e1 : r2_e1_spec B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op W c Hc.
destruct Hc as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hfrm & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  Hi & Hn & Hnow & Hop & Hop4 & lo & hi & Hlo & Hhi & Hhm & Hwant & HrL & R11 & R12 & R16 & R23 & R27 & R19 & R14 & R22 & R26 &
  V392 & Hsp0 & Hbody).
assert (HC : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k) by exact (conj Hbase (conj HJ Hfrs)).
pose proof Hbase as ((HPRE & _) & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold YG0f.ASAN_CEIL in CR.
assert (HS608 : 608 <= d_S cx) by (unfold d_S, LLVMF_STK in *; lia).
destruct (rl_A_range cx HS608) as [HAr HA32].
pose proof Hbody as (Tb & Gb & Lkb & Hb & Hframe & Hshadow & _ & _ & Hinput & _ & _ & Hgeo & _).
pose proof Hbase as ((_ & _ & _ & _ & Hpn & _) & _).
pose proof Hgeo as (_ & _ & _ & _ & _ & _ & _ & G8).
pose proof Hframe as (E & HdE & Hregs & Hflag & _ & _).
pose proof HdE as (EE & E32 & HEI0 & E60 & E516 & E529). unfold AT_A, AT_F, AT_SH in E60, E516, E529.
assert (UA : bv_unsigned (ew E 60) = d_A cx) by (rewrite E60; apply unsigned_lit_small; unfold d_S, LLVMF_STK in *; lia).
pose proof Hsp0 as (H232 & H344).
pose proof Hinput as (Hnr & _ & _).
assert (Hcn : 0 <= c_n cx < 2 ^ 26) by (destruct Hpn as [[HN _] | [HN _]]; lia).
assert (Rcur : 0 <= d_cur cx (rec_rem n) < 2 ^ 64).
{ unfold d_cur, rec_rem, rec_take. destruct Hpn as [[HN HP] | [HN _]].
  - rewrite HN, HP in *. unfold A_EMPTY. lia.
  - destruct (G8 ltac:(lia)) as (GP0 & GPN & _). pose proof (proj1 (@YG0f.ASAN_CEIL_range _)). lia. }
set (ex := [Z_to_bv 64 (r2_sx op mod 2 ^ 64); Z_to_bv 64 now]).
set (vals := r2_vals regs ex).
pose proof (r2_regs_ok B cx E regs ex HdE HrL) as HSro. fold vals in HSro.
pose proof (DFACTS LAWS cx ly3 S3 W mem3 md3 k E vals [] [] HC HdE I I) as Hfacts.
assert (EX0 : ew (d_env cx E vals) 563 = Z_to_bv 64 (r2_sx op mod 2 ^ 64))
  by exact (r2_env_ex cx E regs ex 0 563 eq_refl ltac:(cbn; lia)).
assert (EX1 : ew (d_env cx E vals) 564 = Z_to_bv 64 now)
  by exact (r2_env_ex cx E regs ex 1 564 eq_refl ltac:(cbn; lia)).
assert (Hacs : Forall (YP09.chunk_ok SEGS (d_env cx E vals) (rd W mem3) (d_A cx))
  [YP09.mkChunk 392 (CVal 8 (SOff (AT_X + 32) 0)); YP09.mkChunk 344 (CVal 8 (SOff (AT_X + 33) 0))]).
{ constructor; [|constructor; [|constructor]].
  - apply (chunk_ok_val SEGS _ _ (d_A cx) 392 8 (SOff (AT_X + 32) 0) (r2_sx op mod 2 ^ 64));
      [apply e1_dn_atom; exact EX0 | apply Z.mod_pos_bound; lia | lia | apply e1_vm_mod; exact V392].
  - apply (chunk_ok_val SEGS _ _ (d_A cx) 344 8 (SOff (AT_X + 33) 0) now);
      [apply e1_dn_atom; exact EX1 | lia | lia | exact H344]. }
pose proof (DSEAT LAWS TL fq cx dsh_loop ly3 S3 W regs mem3 md3 k E REC_J r2_sr vals _ [] [] (d_facts [] [])
  HC HdE Hregs Hflag HSro Hfacts Hacs (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
e1_win HS 516%nat 0 0. e1_win HS 529%nat 0 0. e1_win HS 60%nat 248 416.
assert (HEI : img_env VAL A_LIM (d_env cx E vals)) by exact (r2_env_img cx E vals HdE).
assert (A11 : sv_denot (d_env cx E vals) (SOff 542 0) = Z_to_bv 64 lo)
  by (change (Z_to_bv 64 lo) with (w64 lo); rewrite <- R11; symmetry; e1_atom HSro (11%bv : bv 5)).
assert (A12 : sv_denot (d_env cx E vals) (SOff 543 0) = Z_to_bv 64 hi)
  by (change (Z_to_bv 64 hi) with (w64 hi); rewrite <- R12; symmetry; e1_atom HSro (12%bv : bv 5)).
assert (A23 : sv_denot (d_env cx E vals) (SOff 554 0) = Z_to_bv 64 (rec_rem n))
  by (change (Z_to_bv 64 (rec_rem n)) with (w64 (rec_rem n)); rewrite <- R23; symmetry; e1_atom HSro (23%bv : bv 5)).
assert (Hrem : 0 <= rec_rem n <= n) by (unfold rec_rem, rec_take; lia).
assert (Hlh : Z.lor hi lo = rec_want (rest_of (c_pl cx) n)) by (rewrite e1_lor by lia; lia).
assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx + 248 <= a < d_A cx + 416) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem3 a) by (intros; reflexivity).
assert (MPR : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) mem3 a) by (intros a0 Ha0; exact Ha0).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
unfold cfg_at. change (w64 (BASE + REC_J)) with (Z_to_bv 64 (BASE + REC_J)).
paj_run_shc RUNP RUNC HS HJ.
{ e1_awr cx. }
e1_rupd.
psrr_branch_pi RUNP BR HS.
all: rewrite branch_ltu_U, (e1_U _ _ _ (e1_dn_or _ _ _ hi lo A12 A11)), (e1_U _ _ _ A23) in Hc;
  rewrite (Z.mod_small hi), (Z.mod_small lo), Hlh, (Z.mod_small (rec_want _)), (Z.mod_small (rec_rem n)) in Hc by lia;
  first [apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc].
all: paj_run_shc RUNP RUNC HS HJ; [e1_awr cx | e1_rupd].
all: lazymatch goal with HS' : st_ok _ ?Ev ?ssx (restrict _ ?msx) |- _ =>
  assert (RG : forall r r0 : bv 5, sr_get (ss_regs ssx) r = sr_get r2_sr r0 -> getr (ms_regs msx) r = getr regs r0)
    by (intros r r0 Heq; rewrite (st_ok_restrict_reg SEGS _ _ _ msx r HS'), Heq; symmetry; exact (HSro r0));
  assert (R1' : getr (ms_regs msx) 1 = w64 (BASE + RA_MAL))
    by (rewrite (st_ok_restrict_reg SEGS _ _ _ msx 1%bv HS');
        let v := eval vm_compute in (sr_get (ss_regs ssx) 1%bv) in change (sr_get (ss_regs ssx) 1%bv) with v;
        apply codeptr_val; exact HEI);
  assert (RLEN : forall r : bv 5, In r [10; 24]%bv -> getr (ms_regs msx) r = w64 (r2_len cx n));
  [ intros r Hr; cbv [In] in Hr; destruct Hr as [<-|[<-|[]]];
    rewrite (st_ok_restrict_reg SEGS _ _ _ msx _ HS');
    match goal with |- sv_denot ?Ex (sr_get (ss_regs ssx) ?rr) = _ =>
      let v := eval vm_compute in (sr_get (ss_regs ssx) rr) in change (sr_get (ss_regs ssx) rr) with v;
      let Hv := fresh "Hv" in eassert (Hv : sv_denot Ex v = Z_to_bv 64 _) by (e1_dn A11 A12 A23); rewrite Hv end;
    unfold w64, r2_len, rec_len; f_equal; rewrite ?Z.add_0_r, ?(Z.mod_small hi), ?(Z.mod_small lo) by lia; rewrite ?Hlh; lia
  | ];
  assert (RGL : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 25]%bv -> getr (ms_regs msx) r = getr regs r)
    by (intros r Hr; apply RG; cbv [In] in Hr; repeat (destruct Hr as [<-|Hr]; [vm_compute; reflexivity|]); destruct Hr);
  assert (HRK : r2_rk cx n op (ms_regs msx))
    by (split; [exact (RLEN 24%bv ltac:(cbv; tauto))|];
        rewrite (RG 23%bv 23%bv ltac:(vm_compute; reflexivity)), (RG 19%bv 19%bv ltac:(vm_compute; reflexivity)),
          (RG 22%bv 22%bv ltac:(vm_compute; reflexivity)), (RG 26%bv 26%bv ltac:(vm_compute; reflexivity));
        exact (conj R23 (conj R19 (conj R22 R26))));
  assert (R27' : getr (ms_regs msx) 27 = w64 op) by (rewrite (RG 27%bv 27%bv ltac:(vm_compute; reflexivity)); exact R27);
  let rs := eval vm_compute in (ss_mem ssx) in
  let i0 := idx_of_base rs 60%nat in let i0 := eval vm_compute in i0 in
  let r := eval vm_compute in (nth i0 rs got_regionP) in
  let RA := fresh "RA" in
  pose proof (st_ok_region_nth Ev ssx (restrict (w_H W) msx) i0 r HS' ltac:(vm_compute; reflexivity)) as RA;
  cbn [ms_mem restrict] in RA;
  assert (V408 : val_mem SEGS (rd W (ms_mem msx)) (d_A cx + 408) 8 op)
    by (refine (DiscoACjr.field_of_region Ev _ 60 (d_A cx) _ _ _ _ _ 408 8 (SOff 558 0) _ RA _ _ _ _ _);
        [ e1_rU; reflexivity | cbn [In]; repeat (first [left; reflexivity | right])
        | change (Z_to_bv 64 op) with (w64 op); rewrite <- R27; symmetry; e1_atom HSro (27%bv : bv 5)
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia ]);
  assert (V248 : val_mem SEGS (rd W (ms_mem msx)) (d_A cx + 248) 8 (d_cur cx (rec_rem n)))
    by (refine (DiscoACjr.field_of_region Ev _ 60 (d_A cx) _ _ _ _ _ 248 8 (SOff 547 0) _ RA _ _ _ _ _);
        [ e1_rU; reflexivity | cbn [In]; repeat (first [left; reflexivity | right])
        | change (Z_to_bv 64 (d_cur cx (rec_rem n))) with (w64 (d_cur cx (rec_rem n))); rewrite <- R16; symmetry;
          e1_atom HSro (16%bv : bv 5)
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia ]);
  assert (V392' : val_mem SEGS (rd W (ms_mem msx)) (d_A cx + 392) 8 (r2_sx op mod 2 ^ 64))
    by (refine (DiscoACjr.field_of_region Ev _ 60 (d_A cx) _ _ _ _ _ 392 8 (SOff 563 0) _ RA _ _ _ _ _);
        [ e1_rU; reflexivity | cbn [In]; repeat (first [left; reflexivity | right])
        | apply e1_dn_atom; exact EX0
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia | cbn; lia ]);
  assert (V344 : val_mem SEGS (rd W (ms_mem msx)) (d_A cx + 344) 8 now)
    by (refine (DiscoACjr.field_of_region Ev _ 60 (d_A cx) _ _ _ _ _ 344 8 (SOff 564 0) _ RA _ _ _ _ _);
        [ e1_rU; reflexivity | cbn [In]; repeat (first [left; reflexivity | right])
        | apply e1_dn_atom; exact EX1
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia ]);
  apply SRr_ret;
  exact (e1_leaf cx h i n now op W fq ly3 S3 regs mem3 k acc E vals ssx msx _
    Hfrm Hbase Hfrs Hk Hnev Hmo Hacc Hi Hn Hnow (conj Hop Hop4) HrL H232 Hbody HdE HS' eq_refl eq_refl
    ltac:(vm_compute; reflexivity) HJ MEQ MPR RGL R1' (RLEN 10%bv ltac:(cbv; tauto)) R27' HRK
    (conj V408 (conj V248 (rl_val_mem_mod _ _ _ V392'))) V344)
end.
Qed.

End h.
End f.
End d.
