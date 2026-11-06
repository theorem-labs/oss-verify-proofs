(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat StrFun FloatScan FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_scan_calls Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_memcpy F_memchr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_frexpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_frexpl.F_fmt_fp_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

(* [comment removed for export] *)

Definition SHLIM : Z := 0x97bdc.
Definition SHGETC : Z := 0x97c14.
Definition UFLOW : Z := 0x93fe0.
Definition TOREAD : Z := 0x9406c.
Definition STRING_READ : Z := 0x9abbc.

(* [comment removed for export] *)
Definition got_ssp := 0xa2c08%Z.
Definition ssp_guard := 0x5fd290%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs m ssp_guard [C8 canary].

(* [comment removed for export] *)
Record rfj := mkJ {
  j_flags : word; j_pad0 : list byte; j_close : word; j_wend : word; j_wpos : word; j_mbz1 : word; j_wbase : word;
  j_read : word; j_write : word; j_seek : word; j_bufsize : word; j_prev : word; j_next : word;
  j_fd : word; j_ppid : word; j_lockcount : word; j_mode : word; j_lock : word; j_lbf : word; j_pad1 : list byte;
  j_cookie : word; j_off : word; j_getln : word; j_mbz2 : word; j_pl : word; j_nl : word; j_locale : word }.

Definition M64 : Z := 18446744073709551615.

(* [comment removed for export] *)
Definition rf_rend (T p : Z) (w : bool) (f : shfile) : Z :=
  if sh_stdio f then (if w then T + p else T) else M64.

Definition rf_cells (T p : Z) (w : bool) (f : shfile) (J : rfj) : list cell :=
  let rend := rf_rend T p w f in
  [C4 (j_flags J); CB 4 (j_pad0 J); C8 (Z_to_bv 64 (T + sh_rpos f)); C8 (Z_to_bv 64 rend);
   C8 (j_close J); C8 (j_wend J); C8 (j_wpos J); C8 (j_mbz1 J); C8 (j_wbase J); C8 (j_read J); C8 (j_write J); C8 (j_seek J);
   C8 (Z_to_bv 64 T); C8 (j_bufsize J); C8 (j_prev J); C8 (j_next J); C4 (j_fd J); C4 (j_ppid J); C8 (j_lockcount J);
   C4 (j_mode J); C4 (j_lock J); C4 (j_lbf J); CB 4 (j_pad1 J);
   C8 (if sh_stdio f then Z_to_bv 64 rend else j_cookie J); C8 (j_off J); C8 (j_getln J); C8 (j_mbz2 J);
   C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 (if sh_shlim_neg f then M64 else 0)); C8 (Z_to_bv 64 (- sh_cnt0 f));
   C8 (j_pl J); C8 (j_nl J); C8 (j_locale J)].

(* [comment removed for export] *)
Definition rf_cells_raw (T p : Z) (w : bool) (f : shfile) (J : rfj) (she shl shc : word) : list cell :=
  let rend := rf_rend T p w f in
  [C4 (j_flags J); CB 4 (j_pad0 J); C8 (Z_to_bv 64 (T + sh_rpos f)); C8 (Z_to_bv 64 rend);
   C8 (j_close J); C8 (j_wend J); C8 (j_wpos J); C8 (j_mbz1 J); C8 (j_wbase J); C8 (j_read J); C8 (j_write J); C8 (j_seek J);
   C8 (Z_to_bv 64 T); C8 (j_bufsize J); C8 (j_prev J); C8 (j_next J); C4 (j_fd J); C4 (j_ppid J); C8 (j_lockcount J);
   C4 (j_mode J); C4 (j_lock J); C4 (j_lbf J); CB 4 (j_pad1 J);
   C8 (if sh_stdio f then Z_to_bv 64 rend else j_cookie J); C8 (j_off J); C8 (j_getln J); C8 (j_mbz2 J);
   C8 she; C8 shl; C8 shc;
   C8 (j_pl J); C8 (j_nl J); C8 (j_locale J)].

Lemma rf_cells_raw_eq : forall T p w f J,
  rf_cells T p w f J = rf_cells_raw T p w f J (Z_to_bv 64 (rf_rend T p w f)) (Z_to_bv 64 (if sh_shlim_neg f then M64 else 0)) (Z_to_bv 64 (- sh_cnt0 f)).
Proof. reflexivity. Qed.

Lemma rf_cells_size : forall T p w f J, length (j_pad0 J) = 4%nat -> length (j_pad1 J) = 4%nat -> cells_size (rf_cells T p w f J) = 232%nat.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition ssJ : rfj :=
  mkJ (Z_to_bv 64 0) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
      (Z_to_bv 64 STRING_READ) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
      (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 M64) (Z_to_bv 64 M64) (Z_to_bv 64 0) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]
      (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0).

(* [comment removed for export] *)
Definition RFI (T : Z) (txt : list Z) (p : Z) (w : bool) (J : rfj) (kmin c : Z) (f : shfile) : Prop :=
  sh_ok T txt f /\ (-1 <= c < 256)%Z /\
  (sh_shlim_neg f = false -> kmin <= sh_rpos f)%Z /\
  (sh_stdio f = false -> sh_shlim_neg f = false /\ sh_rpos f <= p + 1 /\ (c <> 0%Z -> sh_rpos f <= p))%Z /\
  (sh_stdio f = true -> sh_n f = p /\ sh_rpos f <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p) /\
                        (w = false -> sh_rpos f = 0 /\ sh_cnt0 f = 0 /\ sh_shlim_neg f = false) /\ J = ssJ /\ 0 <= sh_cnt0 f <= sh_rpos f)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shlim_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p : Z) (w : bool) (f : shfile) (J : rfj) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(Fp, Fp + 232)%Z] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' Fp (rf_cells T p w (sh_lim0 f) J).

Definition shlim_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (w : bool) (txt : list Z) (f : shfile) (J : rfj) (she shl shc : word),
  rw_cells asegs m Fp (rf_cells_raw T p w f J she shl shc) ->
  sh_ok T txt f -> length (j_pad0 J) = 4%nat -> length (j_pad1 J) = 4%nat ->
  (0 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= p <= zlength txt)%Z ->
  mem_inv asegs m ->
  evt asegs (shlim_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p w f J m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SHLIM) fc None m (seg_rom asegs)).

Ltac show_goal := match goal with |- ?g => idtac g end.
(* [comment removed for export] *)
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
  end.
Lemma sx32_M64 : sx32 (Z_to_bv 64 18446744073709551615) = Z_to_bv 64 18446744073709551615.
Proof. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit by lia. vm_compute. reflexivity. Qed.
Lemma zx32_lit : forall z, (0 <= z < 2^32)%Z -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.

Lemma shlim_spec : shlim_stmt.
Proof.
  unfold shlim_stmt. intros until shc. intros FC OK L0 L1 T0 T1 Hp MI.
  pose proof (munch_refl [(Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ FC) as B. unfold rf_cells_raw in FC, B. cbn [cells_size csize Nat.add] in B.
  destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst). unfold SHLIM.
  assert (RR : (0 <= rf_rend T p w f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); [destruct w|]; lia).
  unfold M64 in RR. pose_word_ranges.
  zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
  zs. br K1; change (Z.b2z (0 <? 0)) with 0%Z in K1; rewrite Z.land_0_l in K1; [clear K1 | exfalso; apply K1; reflexivity].
  zs. zs.
  apply evt_done. unfold shlim_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  unfold rf_cells, sh_lim0. cbn [sh_rpos sh_cnt0 sh_stdio sh_shlim_neg sh_n sh_buf].
  unfold rf_rend in *. cbn [sh_stdio].
  replace (- sh_rpos f)%Z with (T - (T + sh_rpos f))%Z by lia. hyp.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zero4 : list byte := [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Definition w0 : word := Z_to_bv 64 0.
(* [comment removed for export] *)
Definition ss_cells (T rpos rend : Z) (mode : word) (cookie shend : Z) (shl shc : word) : list cell :=
  [C4 w0; CB 4 zero4; C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend);
   C8 w0; C8 w0; C8 w0; C8 w0; C8 w0; C8 (Z_to_bv 64 STRING_READ); C8 w0; C8 w0;
   C8 (Z_to_bv 64 T); C8 w0; C8 w0; C8 w0; C4 w0; C4 w0; C8 w0;
   C4 mode; C4 (Z_to_bv 64 M64); C4 w0; CB 4 zero4;
   C8 (Z_to_bv 64 cookie); C8 w0; C8 w0; C8 w0;
   C8 (Z_to_bv 64 shend); C8 shl; C8 shc;
   C8 w0; C8 w0; C8 w0].

Lemma rf_cells_ss : forall T p w f, sh_stdio f = true ->
  rf_cells T p w f ssJ = ss_cells T (T + sh_rpos f) (rf_rend T p w f) (Z_to_bv 64 M64) (rf_rend T p w f) (rf_rend T p w f)
                            (Z_to_bv 64 (if sh_shlim_neg f then M64 else 0)) (Z_to_bv 64 (- sh_cnt0 f)).
Proof. intros T p w f ST. unfold rf_cells, ss_cells. rewrite ST. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition toread_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T cookie shend : Z) (shl shc : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 16, q); (Fp, Fp + 232)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' (q - 16) (q)
    /\ rw_cells asegs m' Fp (ss_cells T T T (Z_to_bv 64 M64) cookie shend shl shc).

Definition toread_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T rpos rend cookie shend : Z) (mode shl shc : word),
  rw_cells asegs m Fp (ss_cells T rpos rend mode cookie shend shl shc) ->
  (mode = Z_to_bv 64 0 \/ mode = Z_to_bv 64 M64) ->
  (0 <= T /\ T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= cookie < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
  stk asegs m (q - 16) (q) -> (4096 <= q)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv asegs m ->
  evt asegs (toread_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T cookie shend shl shc m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 TOREAD) fc None m (seg_rom asegs)).

Lemma toread_spec : toread_stmt.
Proof.
  unfold toread_stmt. intros until shc. intros FC Hmode RT Rrp Rre Rck Rsh ST SPLO SPF SPF2 Q0 Q1 MI.
  pose proof (munch_refl [(q - 16, q); (Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (rw_cells_bound _ _ _ _ FC) as B. unfold ss_cells, w0 in FC. cbn [cells_size csize Nat.add] in B.
  unfold TOREAD, M64 in *. pose_word_ranges.
  zs. carve_frame 16%nat ST.
  zs. zs. zs.
  destruct Hmode as [-> | ->].
  all: zs; rewrite ?(sx32_small 0), ?sx32_M64 by lia.
  all: do 6 zs.
  all: br K1.
  all: zs; rewrite (zx32_lit 0) by lia.
  all: do 5 zs.
  all: br K2.
  all: do 8 zs.
  all: zs; zs; zs; zs.
  all: release_frame FR ST q.
  all: apply evt_done; unfold toread_post; repeat (lazymatch goal with |- ex _ => eexists end).
  all: split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST|].
  all: unfold ss_cells, w0; replace (T + 0)%Z with T by lia; hyp.
Qed.



End CeilWrap.
(* [comment removed for export] *)
Ltac show_goal := match goal with |- ?g => idtac g end.
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
  end.
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
