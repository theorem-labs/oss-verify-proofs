(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* reac_ctrl_classify_box_frame, image B (fuzz_ctrl.asan-ubsan, libreac v1.9.0, entry 0x837c4): the stretch AFTER the
   call of reac_ctrl_parse (parse returns to 0x8380c), re-stated WITHOUT the side-stack premises, as input for the
   cgif-form glue lib/B/Prog/C_reac_ctrl_classify_box_frame.v.  It is the image-B twin of a Theorem Labs lane's image-A file
   lib/A/Prog/reac_ctrl_classify_box_frame_Fs.v (not in this delivery) (a working branch 059fc3a33e3), route (a) of
   a Theorem Labs lane's ruling, confirmed for image B by two Theorem Labs lanes (2026-10-29 03:37Z / 03:4xZ).

   rule 24: no function proved here as a new claim.  Every lemma below is a COPY of ctrl's own proved image-B
   footprint run lib/B/Prog/reac_ctrl_classify_box_frame_F.v (this worktree's blob 067b9cff36f, commit 9004a8e607b
   "WIP fuzz_ctrl image B split ... reac_ctrl_classify_box_frame_F pro_A"), with the changes listed below and nothing
   else.  Stretch A (0x837c4 .. the jal at 0x83808) is NOT copied: the glue applies that file's own `pro_A`
   (_F :1658-1698) qualified.
   This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not.

   COPIED VERBATIM, by source line range of reac_ctrl_classify_box_frame_F.v:
     :1-18    the Require / Import block and the scope (lib.Lib's vocabulary, image B's Img0 / AsanRT, the shared
              models, bcmp_wrap_c's published bcmp_wrap_contract_F, StepF last);
     :20-301  shw / shb and their sub-range lemmas, the acc_hint override (acc_close_with), acl_memcmp6, the
              addressable / rw_cells / shadow helpers (acl_app_in .. acl_bytes_rd) and the shadow-check tactics
              (steps_until_if, bjoin, chk_core, pre_sr, pre_no, no_extra, add1);
     :492-1367 Section Post, with the changes below: aQc, aJc, jc / sc / slia, acl_land3, uo / uv, acl_sh_not_in,
              epi, acl_chk, jc_v, st, tl, d9, d7a, d7b, d5, jc_call, d4, acl_CL_call, d3, d2, d1.
   NOT COPIED: :302-491 (the generic fp / fp_dj / thread-cell frame lemmas fl_tls_same, fl_tls_W, fl_cls_h, fl_stk,
   fl_fp_W, fl_fp_ret, fl_fp_sub, fl_dj_last, acl_tls_ret, fl_out_app, fl_dj_out, fl_dj_out_r, fl_cols, fl_col,
   fl_cellO): with the side-stack premises dropped nothing below uses them, and the two this file still needs
   (fl_out_app, fl_bytes and the rest of the fl_ family) come from lib/B/Prog/RcAsanFPLib.v, which it Imports;
   :1370-1734 (aWp, acl_out_fpw_lo, acl_out_Wp, acl_out_Wp_sh, acl_Wp_c, acl_Wp_f, acl_CL_mu, ja_parse, jc_parse,
   cal, pro, pro_A, reac_ctrl_classify_box_frame_holds_F): the parse call and stretch A, which the glue cuts.

   DROPPED PREMISES (a Theorem Labs lane 03:4xZ; the measured reason: ctrl's `fp [1%nat] m tp FS (S - 8864) S aWf aDf` premise
   asks `fp_dj aDf (fp_w [1%nat] FS)`, which is FALSE in cgif's world when o, v or u lies in a caller's class-1 fake
   frame, a state this function's spec allows (count_cid 1 (frames Sc) may be positive).  No instruction of this
   stretch and no premise of its two callee contracts names the side stack or a thread cell, so the proof only
   CARRIED them):
     - the Section variable FS;
     - the Section hypothesis FP0 (fp [1%nat] m (bv_unsigned tp) FS (S - 8864) S aWf aDf);
     - the definitions aWf, aDf and aTL, and the lemmas acl_fs, acl_out_fpw_d, acl_out_fpw_hi, acl_out_fpw_sh;
     - aJa's conjuncts `fp [1%nat] mc (bv_unsigned tp) FS (S - 8864) S aWf aDf` and `aTL mc`;
     - the `fp_w [1%nat] FS` part of aXs, so the write list aWc of the cut state and of the post is
       [(o, o + 36); (v, v + 4); (S - 8864, S); (shadow_addr (S - 8864), shadow_addr S)]: a SMALLER write set, so a
       STRONGER post;
     - the footprint hypotheses only the parse call used: RGBC, RGBCs (.str.4), RWINs (the window's shadow word
       cover), RFS (the side stack's header), RFW (the class-1 side-stack bytes), RTLS (the thread cells).
   CHANGED PROOF STEPS (each marked CHANGED at its lemma; the stepping lemmas epi, st, tl, d1 .. d9, jc_v, jc_call,
   acl_chk, acl_CL_call and acl_sh_not_in are the proved text unchanged): acl_out_Xs_sh, acl_out_Wc_sh and
   acl_out_Wc lose the premise `outside (fp_w [1%nat] FS) x` and the fl_out_app step; ja_win loses the fl_fp /
   fl_tls bullets and `unfold aWf in FP`; ja_v loses the fl_fp_W / fl_tls_W bullets and the assert Hs; acl_AO1,
   acl_AV1, acl_f1 and acl_u1 lose the acl_out_fpw_d arguments (and acl_f1 / acl_u1 the asserts INf / INu).

   The published spec lib/B/Prog/C_reac_ctrl_classify_box_frame.v treac_ctrl_classify_box_frame_spec is NOT weakened
   by any of this: no premise of it mentions the side stack, and this file is proof-internal (decisions.md item 15:
   frame-route identifiers are allowed, qualified, only inside Qed proof-internal lemmas).

   ROUTE (C) (a Theorem Labs lane 16:05Z / 16:12Z; the callee shape of a Theorem Labs lane's image-A stretch
   reac_ctrl_classify_box_frame_post_call_F_on, a working branch aaa83b256c6, lib/A/Prog/
   reac_ctrl_classify_box_frame_Fs.v (not in this delivery)): the universal `shadow_rw` leaves this file. Each change is marked
   `route (C)`:
     - reac_ctrl_classify_box_frame_post_call_shadow_R n u o (A's region, B's names): the range-check words of the two
       bcmp wrapper calls (bcmp(o + 4, u, 6) and bcmp(o + 10, u, 6) in d3), both reached only when k <> 0, so 50 <= n
       (HK).  Not in it: the stretch's own shadow loads of o, v, f, u take their values from the addressable premises
       (acl_chk); reac_ctrl_checksum_verify's footprint contract has no shadow premise; the stretch stores no shadow
       byte (aXs is carried, not written);
     - Hypothesis HSR: that region present in the base memory m; aJa's `shadow_rw mc` becomes the transport
       `forall P, shadow_rw_on P m -> shadow_rw_on P mc`; ja_win / ja_v keep it by B.ShadowRwOnK.fl_shadow_rw_on;
     - HBC is the bcmp wrapper's contract in its _on form (bcmp_wrap_c_on.bcmp_wrap_contract_F_on); d3 gives it its
       region from HSR by shadow_rw_on_mono.  It stays a Section hypothesis of this proof-internal file, so that the
       file's closure keeps the statement leaf only; the glue discharges it with the PROVED
       bcmp_wrap_on.bcmp_wrap_holds_F_on (root-free text of a working branch
       417f5c8e944);
     - HCV is gone: d4 cites the PROVED reac_ctrl_checksum_verify_F.reac_ctrl_checksum_verify_F_holds_on
       (reac_ctrl_checksum_verify_contract_F_on, no shadow premise);
     - d1_B loses its premise `shadow_rw m` (HSR replaces it). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcBoxLib RcParse RcClassify
  RcClassifyLib RcAsan RcAsanLib RcLay.
(* U's statement file only for reac_ctrl_classify_box_frame_ev, which B's does not define; B's, imported after it,
   shadows the names both define (REAC_CTRL_CLASSIFY_BOX_FRAME, REAC_CTRL_CLASSIFY_BOX_FRAME_K, the contract). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import reac_ctrl_classify_box_frame_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  memcmp_c bcmp_wrap_c reac_ctrl_parse_c reac_ctrl_checksum_verify_c reac_ctrl_classify_box_frame_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
(* route (C): the region form and its munch transport, the bcmp wrapper's _on statement, and checksum_verify's proved
   _on footprint run; Required only, named through the full-path aliases below. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ShadowRwOn ShadowRwOnK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require bcmp_wrap_c_on reac_ctrl_checksum_verify_F.
(* Last: StepF's step / if_* (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Local Open Scope Z_scope.
(* CHANGED (ctrlgate DUP, family StrFun: this closure reaches lib/Spec/StrFun.v and lib/B/Spec/StrFun.v, which both
   define memcmp_model and byte_range): the two names are written through full-path aliases of the constants they
   bind here (About, 07:0xZ: B.Spec.StrFun.memcmp_model and Prog.RcLib.byte_range); nothing else changes. *)
Module BSF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec.StrFun.
Module PRcL := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.RcLib.
(* route (C) *)
Module SRO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.ShadowRwOn.
Module SRK := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.ShadowRwOnK.
Module BWo := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.bcmp_wrap_c_on.
Module BCKF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_ctrl_checksum_verify_F.

(* The 8-aligned shadow WORD cover of [p, p + n), at a shadow offset sh the run reads from the runtime cell; at
   sh = ASAN_K it is the cover the contract states, since shadow_addr a = a / 8 + ASAN_K. *)
Definition shw (RNG : footprint) (sh p n : Z) : Prop :=
  rng RNG ((p / 8 + sh) / 8 * 8) (((p + n - 1) / 8 + sh) / 8 * 8 + 8 - (p / 8 + sh) / 8 * 8).

Lemma shw_sub : forall (RNG : footprint) sh p n p' n',
  p <= p' -> 0 < n' -> p' + n' <= p + n -> shw RNG sh p n -> shw RNG sh p' n'.
Proof.
  intros RNG sh p n p' n' H1 H2 H3 H. unfold shw in H |- *.
  apply (rng_sub' RNG _ _ _ _ H). Z.div_mod_to_equations; lia.
Qed.

(* The single shadow byte of a sub-range lies inside the word cover (the single-byte lb loads of this function). *)
Lemma shw_byte1 : forall (RNG : footprint) sh p n X,
  p <= X -> X < p + n -> shw RNG sh p n -> rng RNG (X / 8 + sh) 1.
Proof.
  intros RNG sh p n X H1 H2 H. unfold shw in H.
  apply (rng_sub' RNG _ _ _ _ H). Z.div_mod_to_equations; lia.
Qed.

(* The byte-exact shadow cover of [p, p + n) at offset sh (the form a byte-checked buffer's premise takes). *)
Definition shb (RNG : footprint) (sh p n : Z) : Prop :=
  rng RNG (p / 8 + sh) ((p + n - 1) / 8 + sh - (p / 8 + sh) + 1).

Lemma shb_byte1 : forall (RNG : footprint) sh p n X,
  p <= X -> X < p + n -> shb RNG sh p n -> rng RNG (X / 8 + sh) 1.
Proof.
  intros RNG sh p n X H1 H2 H. unfold shb in H.
  apply (rng_sub' RNG _ _ _ _ H). Z.div_mod_to_equations; lia.
Qed.

(* A sub-range of a word cover keeps the word cover (what a callee's word-cover premise takes). *)
Lemma shw_sub_w : forall (RNG : footprint) sh p n p' n',
  p <= p' -> 0 < n' -> p' + n' <= p + n -> shw RNG sh p n ->
  rng RNG ((p' / 8 + sh) / 8 * 8) (((p' + n' - 1) / 8 + sh) / 8 * 8 + 8 - (p' / 8 + sh) / 8 * 8).
Proof.
  intros RNG sh p n p' n' H1 H2 H3 H. unfold shw in H.
  apply (rng_sub' RNG _ _ _ _ H). Z.div_mod_to_equations; lia.
Qed.

(* The shadow bytes of a sub-range as a byte range (the form reac_ctrl_checksum_verify's shadow premise takes). *)
Lemma shw_bytes : forall (RNG : footprint) sh p n p' n',
  p <= p' -> 0 < n' -> p' + n' <= p + n -> shw RNG sh p n ->
  rng RNG (p' / 8 + sh) ((p' + n' - 1) / 8 - p' / 8 + 1).
Proof.
  intros RNG sh p n p' n' H1 H2 H3 H. unfold shw in H.
  apply (rng_sub' RNG _ _ _ _ H). Z.div_mod_to_equations; lia.
Qed.

(* a Theorem Labs lane's finding: StepF's alia has no Euclidean equations, so a shadow access x / 8 + off is not closed
   by the default solve_acc branches against a word/byte cover.  Override acc_hint to run
   Z.div_mod_to_equations; lia once the access address holds a division. *)
Ltac acc_close_with H :=
  lazymatch goal with
  | |- acc_in ?RNG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with
      | rng RNG ?lo ?len =>
          apply (rng_acc_litZ' RNG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true));
          Z.div_mod_to_equations; lia
      end
  | |- acc_in ?RNG (?a, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with
      | rng RNG ?lo ?len =>
          apply (rng_acc_varZ RNG lo len a n nz H (@eq_refl Z nz));
          Z.div_mod_to_equations; lia
      end
  end.
(* CHANGED (a Theorem Labs lane 09:31Z no-global-setting rule): the hook is redefined LOCALLY, so it does not travel with
   Require; this file's own steps are the only ones that need it. *)
#[local] Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?RNG (?a, ?n) =>
      let E := addr_expr a in
      lazymatch E with
      | context[Z.div _ _] =>
          match goal with
          | H : rng RNG _ _ |- _ => acc_close_with H
          | H : shw RNG _ _ _ |- _ => let H' := fresh in pose proof H as H'; unfold shw in H'; acc_close_with H'
          | H : shb RNG _ _ _ |- _ => let H' := fresh in pose proof H as H'; unfold shb in H'; acc_close_with H'
          end
      end
  end.

(* reac_ctrl_parse_contract_F (RNG first), IMG_LO, IMG_LEN, sh_lo and sh_len are the owner's (a Theorem Labs lane), from the
   reac_ctrl_parse_c.v import at the top: the statement the classify proof applies, discharged in `cal` from
   classify's own rng premises. *)

(* reac_ctrl_classify_box_frame, image B (asan-ubsan, entry 0x837c4): reac_ctrl_classify_box_frame_holds (the contract of
   lib/B/Prog/reac_ctrl_classify_box_frame_c.v) from the contracts of reac_ctrl_parse, the bcmp wrapper and
   reac_ctrl_checksum_verify. The plain proof (lib/Prog/reac_ctrl_classify_box_frame.v) with the lemmas epi, st, tl,
   d1 .. d9 of this build's code: the 64-byte frame, the shadow offset read from its cell, the shadow check before each
   instrumented load and store (each passes from the addressable-range premises, so __asan_report_* is not reached),
   and the runtime state (asan_cells, shadow_rw, the window addressable, fp, tls) carried across the calls. *)

(* The memcmp model of this image's bcmp wrapper on 6 bytes (cl_memcmp6 of lib/Prog/RcClassifyLib.v). *)
Lemma acl_memcmp6 : forall ls rs, length ls = 6%nat -> length rs = 6%nat ->
  exists w, BSF.memcmp_model ls rs 6 = Some w /\ -256 < w < 256 /\ (w =? 0) = cl_eq6 ls rs.
Proof.
  intros ls rs Hl Hr.
  destruct ls as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|? ?]]]]]]]; cbn in Hl; try lia.
  destruct rs as [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|? ?]]]]]]]; cbn in Hr; try lia.
  pose proof (PRcL.byte_range x0). pose proof (PRcL.byte_range x1). pose proof (PRcL.byte_range x2).
  pose proof (PRcL.byte_range x3). pose proof (PRcL.byte_range x4). pose proof (PRcL.byte_range x5).
  pose proof (PRcL.byte_range y0). pose proof (PRcL.byte_range y1). pose proof (PRcL.byte_range y2).
  pose proof (PRcL.byte_range y3). pose proof (PRcL.byte_range y4). pose proof (PRcL.byte_range y5).
  unfold cl_eq6. cbn [BSF.memcmp_model seq forallb nth].
  destruct (bv_unsigned x0 =? bv_unsigned y0) eqn:E0; cbn [andb];
    [|eexists; split; [reflexivity|]; apply Z.eqb_neq in E0; split; [lia|]; apply Z.eqb_neq; lia].
  destruct (bv_unsigned x1 =? bv_unsigned y1) eqn:E1; cbn [andb];
    [|eexists; split; [reflexivity|]; apply Z.eqb_neq in E1; split; [lia|]; apply Z.eqb_neq; lia].
  destruct (bv_unsigned x2 =? bv_unsigned y2) eqn:E2; cbn [andb];
    [|eexists; split; [reflexivity|]; apply Z.eqb_neq in E2; split; [lia|]; apply Z.eqb_neq; lia].
  destruct (bv_unsigned x3 =? bv_unsigned y3) eqn:E3; cbn [andb];
    [|eexists; split; [reflexivity|]; apply Z.eqb_neq in E3; split; [lia|]; apply Z.eqb_neq; lia].
  destruct (bv_unsigned x4 =? bv_unsigned y4) eqn:E4; cbn [andb];
    [|eexists; split; [reflexivity|]; apply Z.eqb_neq in E4; split; [lia|]; apply Z.eqb_neq; lia].
  destruct (bv_unsigned x5 =? bv_unsigned y5) eqn:E5; cbn [andb];
    [|eexists; split; [reflexivity|]; apply Z.eqb_neq in E5; split; [lia|]; apply Z.eqb_neq; lia].
  eexists; split; [reflexivity|]. split; [lia|]. reflexivity.
Qed.

Lemma acl_app_in : forall m p n i, addressable m p n -> 0 <= i < n -> app_mem (p + i).
Proof. intros m p n i (_ & _ & _ & HA) Hi. exact (proj1 (HA i Hi)). Qed.

Lemma acl_app_not_shadow : forall x, app_mem x -> in_shadow x -> False.
Proof. unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END. intros; lia. Qed.

Lemma acl_addr_sub : forall m p n p' n', addressable m p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n ->
  addressable m p' n'.
Proof.
  intros m p n p' n' (H0 & Hn & He & HA) H1 H2 H3. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply HA. lia.
Qed.

Lemma acl_addr_join : forall m p n n', addressable m p n -> addressable m (p + n) n' -> 0 <= n' ->
  addressable m p (n + n').
Proof.
  intros m p n n' (H0 & Hn & He & HA) (H0' & Hn' & He' & HA') Hn''.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z_lt_le_dec i n) as [L|L]; [apply HA; lia|].
  replace (p + i) with (p + n + (i - n)) by lia. apply HA'. lia.
Qed.

(* addressable survives writes apart from the shadow bytes of its range. *)
Lemma acl_addr_munch : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) Hm HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (rt_app_shadow (p + i) Hap) as Hs. pose proof (rt_shadow_bound _ Hs) as Hbd.
  unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. apply HW, Hi.
Qed.

(* rw_cells survive writes apart from their bytes. *)
Lemma acl_rw : forall W m m' A cs, rw_cells rsegs m A cs -> munch W m m' -> wmono rsegs m m' ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells rsegs m' A cs.
Proof.
  intros W m m' A cs [[Hwf Hb] Hw] Hm Hwm Ho. split; [split; [exact Hwf|]|].
  - eapply fl_bytes; [exact Hb | exact Hm |]. rewrite cells_bytes_length by exact Hwf. exact Ho.
  - eapply wr_at_transport; eassumption.
Qed.

(* The check of the w bytes at X = p + j (X mod 8 + w <= 8) of an addressable range: the shadow byte k is readable
   and passes (0, or above X mod 8 + w - 1). *)
Lemma acl_shadow : forall mc p n j w X, addressable mc p n -> 0 <= j -> 1 <= w -> j + w <= n ->
  X mod 8 + w <= 8 -> X = p + j ->
  exists k : byte, ov_read_bytes rsegs mc (wa (X / 8 + ASAN_K)) 1 = Some [k]
                   /\ (bv_signed k = 0 \/ X mod 8 + (w - 1) < bv_signed k) /\ -128 <= bv_signed k < 128.
Proof.
  intros mc p n j w X HA Hj Hw Hjw Hm ->.
  pose proof (rt_shadow_rd mc p n [] HA (fun _ _ => I)) as HSR.
  pose proof (rt_addressable mc p n HA) as HAD.
  destruct (asan_shadow_read rsegs mc ASAN_K p n [] j HSR ltac:(lia)) as (k & RK & BK).
  exists k. split; [exact RK|]. split; [|apply rc_byte_signed].
  exact (asan_check_lt rsegs mc ASAN_K p n j w k HAD Hj Hw Hjw Hm BK).
Qed.

Lemma acl_sh_lt : forall x L, L mod 8 = 0 -> x < L -> shadow_addr x < shadow_addr L.
Proof. unfold shadow_addr. intros x L HL Hx. Z.div_mod_to_equations. lia. Qed.

Lemma acl_sh_ge : forall x L, L <= x -> shadow_addr L <= shadow_addr x.
Proof. unfold shadow_addr. intros x L H. pose proof (Z.div_le_mono L x 8 ltac:(lia) H). lia. Qed.

Lemma acl_out_app_inv : forall A B x, outside (A ++ B) x -> outside A x /\ outside B x.
Proof.
  induction A as [|[lo hi] A IH]; intros B x H; cbn [app outside] in *; [split; [exact I | exact H]|].
  destruct H as [H1 H2]. destruct (IH B x H2) as [H3 H4]. split; [split; [exact H1 | exact H3] | exact H4].
Qed.

(* A point of application memory is apart from every shadow range [shadow_addr a, shadow_addr b) with 0 <= a and
   b <= APPMEM_END. *)
Lemma acl_sh_out : forall x a b, app_mem x -> 0 <= a -> b <= APPMEM_END -> ~ (shadow_addr a <= x < shadow_addr b).
Proof.
  intros x a b Hx Ha Hb. unfold shadow_addr.
  pose proof (Z.div_pos a 8 Ha ltac:(lia)) as H1.
  pose proof (Z.div_le_mono b APPMEM_END 8 ltac:(lia) Hb) as H2.
  replace (APPMEM_END / 8) with 0x100000000000 in H2 by reflexivity.
  unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

(* The shadow byte of a byte apart from [lo, hi) (lo a multiple of 8) is apart from the shadow of [lo, hi). *)
Lemma acl_win_sh : forall x lo hi, lo mod 8 = 0 -> ~ (lo <= x < hi) ->
  ~ (shadow_addr lo <= shadow_addr x < shadow_addr hi).
Proof.
  intros x lo hi Hm Hx [H1 H2]. destruct (Z_lt_le_dec x lo) as [L|L].
  - pose proof (acl_sh_lt x lo Hm L). lia.
  - pose proof (acl_sh_ge x hi ltac:(lia)). lia.
Qed.

Lemma acl_frame_mod8 : forall FS, FS mod 4096 = 0 -> fs_frame FS 1 0 mod 8 = 0.
Proof.
  intros FS H. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
  change (2 ^ 20) with 1048576. change (2 ^ 1) with 2. Z.div_mod_to_equations. lia.
Qed.

Lemma acl_S_mod8 : forall S j, S mod 16 = 0 -> j mod 8 = 0 -> (S - j) mod 8 = 0.
Proof. intros S j H1 H2. Z.div_mod_to_equations. lia. Qed.

(* The alignment of the checked accesses: o, v are multiples of 4. *)
Lemma acl_mod_al : forall x j w, x mod 4 = 0 -> 0 <= j -> j mod 4 + w <= 4 -> (x + j) mod 8 + w <= 8.
Proof. intros x j w H Hj Hw. Z.div_mod_to_equations. lia. Qed.

Lemma acl_mod_al0 : forall x, x mod 4 = 0 -> x mod 8 + 4 <= 8.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

Lemma acl_bytes_rd : forall mc A bs x, bytes_at rsegs mc A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs mc (wa x) = Some b.
Proof.
  intros mc A bs x (_ & _ & H) Hx.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:E.
  - exists b. rewrite <- E, <- H by lia. f_equal. f_equal. lia.
  - apply nth_error_None in E. lia.
Qed.

(* The shadow checks of this build (as in lib/A/Prog/declaration_of.v). *)
Ltac steps_until_if :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; steps_until_if
  | _ => idtac
  end.

Ltac bjoin G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

(* A shadow check of the access of w bytes at X (RX : 0 <= X < 2^64): SH gives the shadow byte k, its read at
   X / 8 + off and the check fact (k = 0, or X mod 8 + (w - 1) < k); `pre` steps to the shadow address (srli; add, or
   nothing when a register holds it), then the load of k and `bnez` go on when k = 0; else the slow path
   `andi r, X, 7` (and `addi r, r, w - 1` by `extra`) and `blt r, k` go on as the check passes. The register r is
   generalized at the join, and the call of __asan_report_* is not reached. *)
Ltac chk_core X RX r SH pre extra :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
  destruct SH as (k & RK & OK & KR);
  pre X RX; steps_until_if; clear RK;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (clear -KR; lia);
  lazymatch goal with
  | |- evtF ?segs ?RN ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RN Q (MS (bvmap_set r rr R) F B fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin G r
        | step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_land7; extra X;
          step;
          let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
          first [ rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 1) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 1 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia])
                | rewrite (rc_lts_signed (X mod 8 + 3) (bv_signed k)) by (clear -MB KR; lia);
                  replace (X mod 8 + 3 <? bv_signed k) with true
                    by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia]) ];
          clear MB; bjoin G r ]
      | intros ?; simp_regs; clear OK KR ]
  end.

Ltac pre_sr X RX := step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_shr3.
Ltac pre_no X RX := idtac.
Ltac no_extra X := idtac.
Ltac add1 X :=
  step; let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
  rewrite ?(unsigned_lit (X mod 8)) by (clear -MB; lia); clear MB.

(* route (C): the region of record of the stretch (A's reac_ctrl_classify_box_frame_post_call_shadow_R, B's names):
   the range-check words its two bcmp wrapper calls read, when the calls are reached (k <> 0, so 50 <= n). *)
Definition reac_ctrl_classify_box_frame_post_call_shadow_R (n u o : Z) (a : Z) : Prop :=
  50 <= n /\ (BWo.bcmp_wrap_shadow_R (o + 4) u 6 a \/ BWo.bcmp_wrap_shadow_R (o + 10) u 6 a).

Section Post.
  (* CHANGED (option (a), two Theorem Labs lanes 03:37Z): the Section variable FS is gone. *)
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f n u o v S k off : Z) (fr us vb B : list byte) (RNG : footprint).

  (* CHANGED: aWf, aDf (fp's write and data lists) and aTL (the thread cells apart from aXs) are DROPPED with FP0;
     aXs keeps only the shadow of the window (the fp_w [1%nat] FS part is DROPPED), so the stretch's write list aWc is
     o, v, the window and the window's shadow: a smaller write set, a stronger post. *)
  Definition aXs : list ivl := [(shadow_addr (S - 8864), shadow_addr S)].
  Definition aWc : list ivl := (o, o + 36) :: (v, v + 4) :: (S - 8864, S) :: aXs.

  (* The runtime state the post names.  CHANGED: the conjuncts fp [1%nat] mc (bv_unsigned tp) FS (S - 8864) S aWf aDf
     and aTL mc are DROPPED.  route (C): the universal `shadow_rw mc` is replaced by the transport from the base memory
     m (every shadow region present in m is present in mc). *)
  Definition aJa (mc : word -> option byte) : Prop :=
    asan_cells mc /\ (forall P : Z -> Prop, SRO.shadow_rw_on P m -> SRO.shadow_rw_on P mc) /\
    addressable mc (S - 8864) 8864.

  (* The cells the bcmp wrapper reads. *)
  Definition aCL (mc : word -> option byte) : Prop :=
    bytes_at rsegs mc REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs mc REAL_MEMCMP (le8 (wa MEMCMP)) /\
    bytes_at rsegs mc GOT_CF (le8 (wa CF)) /\ bytes_at rsegs mc (CF + 254) [Z_to_bv 8 1] /\
    bytes_at rsegs mc (CF + 255) [Z_to_bv 8 1].

  (* route (C): the bcmp wrapper's contract in its _on form (premise shadow_rw_on (bcmp_wrap_shadow_R L R N) m); no
     checksum_verify hypothesis: d4 cites its proved _on footprint run. *)
  Hypothesis HBC : BWo.bcmp_wrap_contract_F_on.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis Rf : 0 <= f < 2^64.
  Hypothesis Ru : 0 <= u < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis Rv : 0 <= v < 2^64.
  Hypothesis RS : 8864 <= S < 2^64.
  Hypothesis S16 : S mod 16 = 0.
  Hypothesis Lfr : length fr = 50%nat.
  Hypothesis Lus : length us = 6%nat.
  Hypothesis LB : length B = 36%nat.
  Hypothesis Rk : 0 <= k <= 13.
  Hypothesis HK : k <> 0 -> 50 <= n /\ B = cp_struct fr k /\ (k = 5 -> cp_rec fr = true).
  Hypothesis HF : 50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fr /\ (f + 50 <= S - 8864 \/ S <= f).
  Hypothesis HU : 50 <= n -> u + 6 <= 2^64 /\ bytes_at rsegs m u us /\ (u + 6 <= S - 8864 \/ S <= u).
  Hypothesis Ho0 : o <> 0.
  Hypothesis Ho4 : o mod 4 = 0.
  Hypothesis Ho36 : o + 36 <= 2^64.
  Hypothesis DOs : o + 36 <= S - 8864 \/ S <= o.
  Hypothesis DOf : 50 <= n -> o + 36 <= f \/ f + 50 <= o.
  Hypothesis DOu : o + 36 <= u \/ u + 6 <= o.
  Hypothesis Hv0 : v <> 0.
  Hypothesis Hv4 : v mod 4 = 0.
  Hypothesis Hv36 : v + 4 <= 2^64.
  Hypothesis DVs : v + 4 <= S - 8864 \/ S <= v.
  Hypothesis DVo : v + 4 <= o \/ o + 36 <= v.
  Hypothesis DVf : v + 4 <= f \/ f + 50 <= v.
  Hypothesis DVu : v + 4 <= u \/ u + 6 <= v.
  Hypothesis HHM : HIGHMEM_BEG <= S - 8864.
  Hypothesis HAE : S <= APPMEM_END.
  Hypothesis AFU : 50 <= n -> addressable m f 50 /\ addressable m u 6 /\ app_mem (u + 6) /\ app_mem (u + 7).
  Hypothesis AO : addressable m o 36.
  Hypothesis AV : addressable m v 4.
  Hypothesis HVR : v + 4 <= RT_LO \/ RT_HI <= v.
  (* route (C): the region of record present in the base memory (in place of the universal shadow_rw of aJa m). *)
  Hypothesis HSR : SRO.shadow_rw_on (reac_ctrl_classify_box_frame_post_call_shadow_R n u o) m.
  (* DROPPED: FP0 (fp [1%nat] m (bv_unsigned tp) FS (S - 8864) S aWf aDf). *)
  (* the footprint of the run: image (every absolute cell), this frame's window, each buffer and the shadow
     cover of each ASan-checked buffer (word cover for a callee-checked buffer, byte cover for v which only this
     function checks).  off is the shadow offset the run reads from the runtime cell (Hoff : off = ASAN_K). *)
  Hypothesis RBY : rng_bytes RNG.
  Hypothesis RIMG : rng RNG 0x10000 0x5ee000.
  Hypothesis RWIN : rng RNG (S - 8864) 8864.
  Hypothesis RGf : 50 <= n -> rng RNG f 50.
  Hypothesis RGfs : 50 <= n -> shw RNG off f 50.
  Hypothesis RGo : rng RNG o 36.
  Hypothesis RGos : shw RNG off o 36.
  Hypothesis RGu : 50 <= n -> rng RNG u 6.
  Hypothesis RGus : 50 <= n -> shw RNG off u 6.
  Hypothesis RGv : rng RNG v 4.
  Hypothesis RGvs : shb RNG off v 4.
  (* DROPPED (used only by the parse call `cal`, which this file does not hold): RGBC, RGBCs (.str.4), RWINs (the
     window's shadow word cover), RFS (the side stack's header), RFW (the class-1 side-stack bytes), RTLS (the
     cells of asan_tls_cells). *)

  Definition aQc (c : option Z) : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (cl_r c))
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch aWc m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - 8864) S /\
      rw_cells rsegs m' o [CB 36 B] /\ rw_cells rsegs m' v [CB 4 (reac_ctrl_classify_box_frame_ev c vb)] /\ aJa m'.

  Definition aJc (m1 : word -> option byte) (vc : list byte) : Prop :=
    rw_cells rsegs m1 (S + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    bytes_at rsegs m1 o B /\ wr_at rsegs m1 o 36 /\ rw_cells rsegs m1 v [CB 4 vc] /\
    munch aWc m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 (S - 8864) (S + -64) /\ aJa m1.

Ltac jc := unfold aJc; refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))));
  first [eassumption | unfold aWc; eassumption].

(* lia is slow with the section's disjunctions and implications in the context: sc clears them (a proof that needs
   one poses it first under another name). *)
Ltac sc := try clear HK; try clear HF; try clear HU; try clear DOs; try clear DOf; try clear DOu; try clear DVs;
  try clear DVo; try clear DVf; try clear DVu; try clear HVR; try clear AFU.
Ltac slia := sc; lia.

  Lemma acl_land3 : forall x, Z.land x 3 = x mod 4.
  Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

  (* The UBSan null and 4-alignment checks of o (s2) pass from o <> 0 and o mod 4 = 0, so the unimp is not reached. *)
  Ltac uo := step; rewrite (rc_eqb_lit o 0) by (clear -Ro; lia); if_false;
    step; step; rewrite (unsigned_lit o) by (clear -Ro; lia); rewrite acl_land3, Ho4; if_false.

  (* The UBSan null and 4-alignment checks of v (s0) pass from v <> 0 and v mod 4 = 0. The alignment byte that the
     check leaves in a0 is v mod 4 = 0, which the store path writes when no class literal overwrites it. *)
  Ltac uv := step; rewrite (rc_eqb_lit v 0) by (clear -Rv; lia); if_false;
    step; step; rewrite (unsigned_lit v) by (clear -Rv; lia); rewrite acl_land3, Hv4; if_false.

  (* DROPPED with FP0: acl_fs, acl_out_fpw_d, acl_out_fpw_hi, acl_out_fpw_sh (_F :613-652: the side stack's place and
     the disjointness of the data ranges from the class-1 side-stack bytes, which only served the fp_w part of aXs). *)

  (* CHANGED (_F :654-660): no premise `outside (fp_w [1%nat] FS) x`, and no fl_out_app step for the dropped fp_w
     part. *)
  Lemma acl_out_Xs_sh : forall x, app_mem x -> (x < S - 8864 \/ S <= x) ->
    outside aXs (shadow_addr x).
  Proof.
    intros x Hap Hx. unfold aXs.
    cbn [outside]. split; [|exact I].
    apply acl_win_sh; [apply acl_S_mod8; [exact S16 | reflexivity] | clear -Hx; lia].
  Qed.

  (* The bytes of o and of v are application memory: apart from every shadow byte. *)
  Lemma acl_sh_not_in : forall p q y, addressable m p q -> in_shadow y -> y < p \/ p + q <= y.
  Proof.
    intros p q y HA Hy. destruct (Z_lt_le_dec y p) as [L|L]; [left; exact L|].
    destruct (Z_lt_le_dec y (p + q)) as [L2|L2]; [|right; exact L2].
    exfalso. apply (acl_app_not_shadow y); [|exact Hy]. replace y with (p + (y - p)) by ring.
    apply (acl_app_in m p q); [exact HA | clear -L L2; lia].
  Qed.

  (* CHANGED (_F :671-679): no premise `outside (fp_w [1%nat] FS) x` (passed on to acl_out_Xs_sh). *)
  Lemma acl_out_Wc_sh : forall x, app_mem x -> (x < S - 8864 \/ S <= x) ->
    outside aWc (shadow_addr x).
  Proof.
    intros x Hap Hx. pose proof (rt_app_shadow x Hap) as Hs. unfold aWc. cbn [outside].
    split; [pose proof (acl_sh_not_in o 36 _ AO Hs) as Hq; clear -Hq; lia|].
    split; [pose proof (acl_sh_not_in v 4 _ AV Hs) as Hq; clear -Hq; lia|].
    split; [clear -Hs HHM; unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *; lia|].
    exact (acl_out_Xs_sh x Hap Hx).
  Qed.

  (* A byte of application memory apart from o, v and the window is outside the footprint.  CHANGED (_F :683-690):
     no premise `outside (fp_w [1%nat] FS) x` (H4), and no `apply fl_out_app; [exact H4|]` step for the dropped fp_w
     part. *)
  Lemma acl_out_Wc : forall x, app_mem x -> (x < o \/ o + 36 <= x) -> (x < v \/ v + 4 <= x) ->
    (x < S - 8864 \/ S <= x) -> outside aWc x.
  Proof.
    intros x Hap H1 H2 H3. unfold aWc, aXs. cbn [outside].
    split; [clear -H1; lia|]. split; [clear -H2; lia|]. split; [clear -H3; lia|].
    split; [|exact I].
    apply acl_sh_out; [exact Hap | clear -RS; lia | exact HAE].
  Qed.

  (* The runtime state survives writes inside the window.  CHANGED (_F :693-707): the fp and tls bullets (fl_fp,
     fl_tls) and `unfold aWf in FP` are dropped with aJa's fp / aTL conjuncts.  route (C): the shadow transport is kept
     by B.ShadowRwOnK.fl_shadow_rw_on (the twin of fl_shadow_rw). *)
  Lemma ja_win : forall W' m1 m2, aJa m1 -> munch W' m1 m2 -> wmono rsegs m1 m2 -> sub_fp W' [(S - 8864, S)] ->
    aJa m2.
  Proof.
    intros W' m1 m2 (AC & SW & AW) MU WM Hs.
    assert (SHo : forall x, in_shadow x -> outside W' x)
      by (intros x Hx; exact (fl_shadow_out W' (S - 8864) S x Hs HHM Hx)).
    split; [|split].
    - apply (fl_asan_cells W' m1 m2 AC MU). intros x Hx. apply (fl_out_lo W' (S - 8864) S x Hs). left.
      clear -Hx HHM. unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
    - intros P HP. exact (SRK.fl_shadow_rw_on P W' m1 m2 (SW P HP) MU WM SHo).
    - exact (fl_addressable W' m1 m2 _ _ AW MU SHo).
  Qed.

  (* The runtime state survives the store of the 4 bytes at v.  CHANGED (_F :710-727): the fp and tls bullets
     (fl_fp_W, fl_tls_W) and the assert Hs (sub_fp [(v, v + 4)] aWf, which only they used) are dropped.  route (C): the
     shadow transport is kept by B.ShadowRwOnK.fl_shadow_rw_on. *)
  Lemma ja_v : forall m1 m2, aJa m1 -> munch [(v, v + 4)] m1 m2 -> wmono rsegs m1 m2 ->
    (forall x, v <= x < v + 4 -> exists b, mrd rsegs m2 (wa x) = Some b) -> aJa m2.
  Proof.
    intros m1 m2 (AC & SW & AW) MU WM RD.
    assert (SHo : forall x, in_shadow x -> outside [(v, v + 4)] x)
      by (intros x Hx; cbn [outside]; split; [pose proof (acl_sh_not_in v 4 x AV Hx) as Hq; clear -Hq; lia | exact I]).
    split; [|split].
    - apply (fl_asan_cells _ m1 m2 AC MU). intros x Hx. cbn [outside]. split; [clear -Hx HVR; lia | exact I].
    - intros P HP. exact (SRK.fl_shadow_rw_on P _ m1 m2 (SW P HP) MU WM SHo).
    - exact (fl_addressable _ m1 m2 _ _ AW MU SHo).
  Qed.

  (* 0x83984: a0 = s1, the frame restored, return. *)
  Lemma epi : forall c x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 m1,
    aJc m1 (reac_ctrl_classify_box_frame_ev c vb) ->
    evtF rsegs RNG (aQc c)
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (cl_r c)) x10 x11 x12 x13 x14
               x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83984) fc None m1 (seg_rom rsegs)).
  Proof.
    intros c x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 m1
      (FR & HBo & WRo & HV & MU & WM & MI & ST & JA).
    do 11 step.
    replace (S + -64 + 64) with S by lia.
    pose proof (stk_release rsegs m1 _ _ _ ST FR ltac:(lia)) as ST2.
    cbn [cells_size csize Nat.add] in ST2. replace (S + -64 + Z.of_nat 64) with S in ST2 by lia.
    apply evtF_done. unfold aQc. do 14 eexists. exists m1.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST2|].
    split; [|split; [exact HV | exact JA]].
    rewrite <- LB. apply cl_rw_of; [exact HBo|]. rewrite LB. exact WRo.
  Qed.

  (* The 36 bytes at o and the 4 bytes at v stay addressable in a memory that the run reached writing only aWc.
     CHANGED (_F :750-765): the acl_out_fpw_d argument of acl_out_Wc_sh is dropped. *)
  Lemma acl_AO1 : forall m1, munch aWc m m1 -> addressable m1 o 36.
  Proof.
    intros m1 MU. apply (acl_addr_munch aWc m m1 o 36 AO MU). intros i Hi.
    pose proof (acl_app_in m o 36 i AO Hi) as Hap.
    apply acl_out_Wc_sh; [exact Hap | pose proof DOs as D; clear -Hi D; lia].
  Qed.

  Lemma acl_AV1 : forall m1, munch aWc m m1 -> addressable m1 v 4.
  Proof.
    intros m1 MU. apply (acl_addr_munch aWc m m1 v 4 AV MU). intros i Hi.
    pose proof (acl_app_in m v 4 i AV Hi) as Hap.
    apply acl_out_Wc_sh; [exact Hap | pose proof DVs as D; clear -Hi D; lia].
  Qed.

  (* The shadow check of the w bytes at X = p + j of an addressable range, with the offset off. *)
  Lemma acl_chk : forall mc p q j w X, addressable mc p q -> 0 <= j -> 1 <= w -> j + w <= q ->
    X mod 8 + w <= 8 -> X = p + j ->
    exists kk : byte, ov_read_bytes rsegs mc (wa (X / 8 + off)) 1 = Some [kk]
      /\ (bv_signed kk = 0 \/ X mod 8 + (w - 1) < bv_signed kk) /\ -128 <= bv_signed kk < 128.
  Proof. intros mc p q j w X H1 H2 H3 H4 H5 H6. rewrite Hoff. exact (acl_shadow mc p q j w X H1 H2 H3 H4 H5 H6). Qed.

  (* aJc after the store of the 4 bytes at v. *)
  Lemma jc_v : forall m1 m2 vc, aJc m1 vb ->
    rw_cells rsegs m2 (S + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at rsegs m2 o B -> wr_at rsegs m2 o 36 -> rw_cells rsegs m2 v [CB 4 vc] ->
    munch [(v, v + 4)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> stk rsegs m2 (S - 8864) (S + -64) ->
    aJc m2 vc.
  Proof.
    intros m1 m2 vc (_ & _ & _ & _ & MU & WM & _ & _ & JA) FR HBo WRo HV MUv WMv MI ST.
    refine (conj FR (conj HBo (conj WRo (conj HV (conj _ (conj (wmono_trans _ _ _ _ WM WMv) (conj MI (conj ST _)))))))).
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUv].
      intros x Hx. unfold aWc in Hx. cbn [outside] in *. destruct Hx as (_ & H & _). split; [exact H | exact I].
    - apply (ja_v m1 m2 JA MUv WMv). intros x Hx. destruct HV as [[Hwf HB] _].
      cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
      cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
      apply (acl_bytes_rd m2 v vc x HB). rewrite Hl. clear -Hx; lia.
  Qed.

  (* 0x838ec: the check of the 4 bytes at v, s1 = 0, the store of e (a0) at v, to the epilogue. *)
  Lemma st : forall e x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31 m1,
    aJc m1 vb ->
    evtF rsegs RNG (aQc (Some e))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 (Z_to_bv 64 e) x11 x12 x13 x14
               x15 x16 x17 x18 x19 x20 (Z_to_bv 64 off) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x838ec) fc None m1 (seg_rom rsegs)).
  Proof.
    intros e x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31 m1 J.
    pose proof J as (FR & HBo & WRo & HV & MU & _ & MI & ST & _).
    pose proof (acl_chk m1 v 4 0 4 v (acl_AV1 m1 MU) ltac:(slia) ltac:(slia) ltac:(slia) (acl_mod_al0 v Hv4)
      ltac:(ring)) as SH.
    clear MU.
    pose proof (munch_refl [(v, v + 4)] m1) as MUv. pose proof (wmono_refl rsegs m1) as WMv.
    pose proof DVs as DVs'. pose proof DVo as DVo'. pose proof Rv as RX. pose proof (jc_v m1) as JV.
    sc.
    chk_core v RX (Z_to_bv 5 12) SH pre_sr add1.
    step. step. step.
    apply cl_rw_c4 in HV.
    eapply (epi (Some e)).
    match goal with |- aJc ?mm _ => exact (JV mm _ J FR HBo WRo HV MUv WMv MI ST) end.
  Qed.

  (* 0x839b0: the tail of the classification on k (a1) and byte 19 of the frame (o + 23, checked); each arm runs the
     UBSan checks of v then the store. *)
  Lemma tl : k <> 0 -> forall x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x19 x20 x22 x28 x29 x30 x31 m1,
    aJc m1 vb ->
    evtF rsegs RNG (aQc (cl_tail k fr))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 (Z_to_bv 64 k) x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) x19 x20 (Z_to_bv 64 off) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x839b0) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K0 x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x19 x20 x22 x28 x29 x30 x31 m1 J.
    destruct (HK K0) as (HN & EB & _).
    pose proof J as (_ & HBo & _ & _ & MU & _).
    assert (R23 : ov_read_bytes rsegs m1 (wa (o + 23)) 1 = Some [cp_b fr 19])
      by (apply (cl_rd _ _ _ B _ 23 1); [exact HBo | slia | rewrite EB; reflexivity]).
    pose proof (acl_chk m1 o 36 23 1 (o + 23) (acl_AO1 m1 MU) ltac:(slia) ltac:(slia) ltac:(slia)
      (acl_mod_al o 23 1 Ho4 ltac:(slia) ltac:(slia)) eq_refl) as SH.
    assert (RX : 0 <= o + 23 < 2^64) by slia.
    pose proof st as STL. clear MU HBo. sc.
    step. step.
    rewrite (rc_eqb_lit k 2) by slia.
    destruct (Z.eqb_spec k 2) as [K2|K2]; cbv iota.
    { step.
      chk_core (o + 23) RX (Z_to_bv 5 12) SH pre_sr no_extra.
      step. step. step.
      rewrite (cl_zxb_eqb (cp_b fr 19) 3) by slia.
      destruct (Z.eqb_spec (bv_unsigned (cp_b fr 19)) 3) as [E19|E19]; cbn [negb]; cbv iota.
      - uv. step. step. replace (cl_tail k fr) with (Some 4) by (unfold cl_tail, cp_v; rewrite K2, E19; reflexivity).
        apply STL. exact J.
      - uv. step. step. replace (cl_tail k fr) with (Some 2)
          by (unfold cl_tail, cp_v; rewrite K2, (proj2 (Z.eqb_neq _ 3) E19); reflexivity).
        apply STL. exact J. }
    step. step.
    rewrite (rc_eqb_lit k 9) by slia.
    destruct (Z.eqb_spec k 9) as [K9|K9]; cbv iota.
    { uv. step. step. replace (cl_tail k fr) with (Some 5) by (unfold cl_tail; rewrite K9; reflexivity).
      apply STL. exact J. }
    step. step.
    rewrite (rc_eqb_lit k 7) by slia.
    destruct (Z.eqb_spec k 7) as [K7|K7]; cbn [negb]; cbv iota.
    { uv. step. step. replace (cl_tail k fr) with (Some 3) by (unfold cl_tail; rewrite K7; reflexivity).
      apply STL. exact J. }
    uv. step. step. replace (cl_tail k fr) with (Some 2)
      by (unfold cl_tail; rewrite (proj2 (Z.eqb_neq k 7) K7), (proj2 (Z.eqb_neq k 2) K2),
            (proj2 (Z.eqb_neq k 9) K9); reflexivity).
    apply STL. exact J.
  Qed.

  (* 0x83980: w2 (s4, the second bcmp) = 0 goes to tl (with a1 = k), else the epilogue with s1 = -1. *)
  Lemma d9 : k <> 0 -> forall w2, -256 < w2 < 256 -> (w2 =? 0) = cl_eq6 fr us ->
    forall x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> aJc m1 vb ->
    evtF rsegs RNG (aQc (cl_d9 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 (Z_to_bv 64 k) x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) x19 (Z_to_bv 64 w2) (Z_to_bv 64 off) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83980) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K0 w2 Rw Ew x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31 m1 E9 J.
    pose proof tl as TL. pose proof epi as EPI. sc.
    step.
    rewrite (cl_eqb0 w2) by (clear -Rw; lia). rewrite Ew.
    unfold cl_d9. destruct (cl_eq6 fr us); cbn [negb]; cbv iota.
    - eapply TL; [exact K0 | exact J].
    - subst x9. apply (EPI None). exact J.
  Qed.

  (* 0x838bc entered with a1 = 1 (k = 1): the broadcast word at o + 16 (checked); set (broadcast word <> 0): the
     UBSan checks of v then st 0; else d9. *)
  Lemma d7a : k = 1 -> forall w2, -256 < w2 < 256 -> (w2 =? 0) = cl_eq6 fr us ->
    forall x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> aJc m1 vb ->
    evtF rsegs RNG (aQc (cl_d7 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 (Z_to_bv 64 1) x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) x19 (Z_to_bv 64 w2) (Z_to_bv 64 off) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x838bc) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K1 w2 Rw Ew x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31 m1 E9 J.
    assert (K0 : k <> 0) by (clear -K1; lia). destruct (HK K0) as (HN & EB & _).
    pose proof J as (_ & HBo & _ & _ & MU & _).
    assert (RB : 0 <= (if cp_bcast fr then 1 else 0) < 128) by (destruct (cp_bcast fr); clear; lia).
    assert (R16 : ov_read_bytes rsegs m1 (wa (o + 16)) 4 = Some (le4 (Z_to_bv 64 (if cp_bcast fr then 1 else 0))))
      by (rewrite cl_le4_small by (clear -RB; lia); apply (cl_rd _ _ _ B _ 16 4);
          [exact HBo | slia | rewrite EB; apply cl_bc16]).
    pose proof (acl_chk m1 o 36 16 4 (o + 16) (acl_AO1 m1 MU) ltac:(slia) ltac:(slia) ltac:(slia)
      (acl_mod_al o 16 4 Ho4 ltac:(slia) ltac:(slia)) eq_refl) as SH.
    assert (RX : 0 <= o + 16 < 2^64) by slia.
    pose proof st as STL. pose proof d9 as D9. clear MU HBo. sc.
    step.
    chk_core (o + 16) RX (Z_to_bv 5 13) SH pre_sr add1.
    step. rewrite (cl_sx32 (if cp_bcast fr then 1 else 0)) by (clear -RB; lia).
    step. rewrite (rc_eqb_lit (if cp_bcast fr then 1 else 0) 0) by (clear -RB; lia).
    unfold cl_d7. destruct (cp_bcast fr); cbv iota.
    - change (1 =? 0) with false. cbv iota.
      step. step. if_false.
      uv.
      rewrite K1. apply (STL 0). exact J.
    - change (0 =? 0) with true. cbv iota.
      replace (Z_to_bv 64 1) with (Z_to_bv 64 k) by (rewrite K1; reflexivity).
      eapply D9; [exact K0 | exact Rw | exact Ew | exact E9 | exact J].
  Qed.

  (* 0x838bc entered with a1 = k (k <> 0, 1): the broadcast word at o + 16 (checked); set: k = 1 fails and the
     epilogue with -1, else d9. *)
  Lemma d7b : k <> 0 -> k <> 1 -> forall w2, -256 < w2 < 256 -> (w2 =? 0) = cl_eq6 fr us ->
    forall x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> aJc m1 vb ->
    evtF rsegs RNG (aQc (cl_d7 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 (Z_to_bv 64 k) x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) x19 (Z_to_bv 64 w2) (Z_to_bv 64 off) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x838bc) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K0 K1 w2 Rw Ew x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31 m1 E9 J.
    destruct (HK K0) as (HN & EB & _).
    pose proof J as (_ & HBo & _ & _ & MU & _).
    assert (RB : 0 <= (if cp_bcast fr then 1 else 0) < 128) by (destruct (cp_bcast fr); clear; lia).
    assert (R16 : ov_read_bytes rsegs m1 (wa (o + 16)) 4 = Some (le4 (Z_to_bv 64 (if cp_bcast fr then 1 else 0))))
      by (rewrite cl_le4_small by (clear -RB; lia); apply (cl_rd _ _ _ B _ 16 4);
          [exact HBo | slia | rewrite EB; apply cl_bc16]).
    pose proof (acl_chk m1 o 36 16 4 (o + 16) (acl_AO1 m1 MU) ltac:(slia) ltac:(slia) ltac:(slia)
      (acl_mod_al o 16 4 Ho4 ltac:(slia) ltac:(slia)) eq_refl) as SH.
    assert (RX : 0 <= o + 16 < 2^64) by slia.
    pose proof epi as EPI. pose proof d9 as D9. clear MU HBo. sc.
    step.
    chk_core (o + 16) RX (Z_to_bv 5 13) SH pre_sr add1.
    step. rewrite (cl_sx32 (if cp_bcast fr then 1 else 0)) by (clear -RB; lia).
    step. rewrite (rc_eqb_lit (if cp_bcast fr then 1 else 0) 0) by (clear -RB; lia).
    unfold cl_d7. destruct (cp_bcast fr); cbv iota.
    - change (1 =? 0) with false. cbv iota.
      step. step. rewrite (rc_eqb_lit k 1) by slia.
      rewrite (proj2 (Z.eqb_neq k 1) K1). cbn [negb]. cbv iota.
      subst x9. apply (EPI None). exact J.
    - change (0 =? 0) with true. cbv iota.
      eapply D9; [exact K0 | exact Rw | exact Ew | exact E9 | exact J].
  Qed.

  (* 0x83914 (after reac_ctrl_checksum_verify gave 0; s6 holds the shadow address of o): the kind word at o
     (checked); k = 5: byte 22 at o + 26 and the half word at o + 28 (each checked), to st 1 or the epilogue with -1;
     else d7b. *)
  Lemma d5 : k <> 0 -> k <> 1 -> forall w2, -256 < w2 < 256 -> (w2 =? 0) = cl_eq6 fr us ->
    forall x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> aJc m1 vb ->
    evtF rsegs RNG (aQc (cl_d5 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) x19 (Z_to_bv 64 w2) (Z_to_bv 64 off) (Z_to_bv 64 (o / 8 + off))
               s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83914) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K0 K1 w2 Rw Ew x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 m1 E9 J.
    destruct (HK K0) as (HN & EB & HR5).
    pose proof J as (_ & HBo & _ & _ & MU & _).
    pose proof (acl_AO1 m1 MU) as AO1.
    assert (R0 : ov_read_bytes rsegs m1 (wa (o + 0)) 4 = Some (le4 (Z_to_bv 64 k)))
      by (rewrite cl_le4_small by slia; apply (cl_rd _ _ _ B _ 0 4); [exact HBo | slia | rewrite EB; reflexivity]).
    pose proof (acl_chk m1 o 36 0 4 o AO1 ltac:(slia) ltac:(slia) ltac:(slia) (acl_mod_al0 o Ho4) ltac:(ring)) as SH0.
    pose proof (acl_chk m1 o 36 26 1 (o + 26) AO1 ltac:(slia) ltac:(slia) ltac:(slia)
      (acl_mod_al o 26 1 Ho4 ltac:(slia) ltac:(slia)) eq_refl) as SH26.
    pose proof (acl_chk m1 o 36 28 2 (o + 28) AO1 ltac:(slia) ltac:(slia) ltac:(slia)
      (acl_mod_al o 28 2 Ho4 ltac:(slia) ltac:(slia)) eq_refl) as SH28.
    pose proof Ro as RX0. assert (RX26 : 0 <= o + 26 < 2^64) by slia. assert (RX28 : 0 <= o + 28 < 2^64) by slia.
    pose proof epi as EPI. pose proof st as STL. pose proof d7b as D7B. clear MU AO1. sc.
    chk_core o RX0 (Z_to_bv 5 11) SH0 pre_no add1.
    step. rewrite (cl_sx32 k) by (clear -Rk; lia).
    step. step.
    rewrite (rc_eqb_lit k 5) by (clear -Rk; lia).
    unfold cl_d5. destruct (Z.eqb_spec k 5) as [K5|K5]; cbn [negb]; cbv iota.
    - pose proof (HR5 K5) as RC.
      assert (R26 : ov_read_bytes rsegs m1 (wa (o + 26)) 1 = Some [cp_b fr 22])
        by (apply (cl_rd _ _ _ B _ 26 1); [exact HBo | slia | rewrite EB; reflexivity]).
      assert (R28 : ov_read_bytes rsegs m1 (wa (o + 28)) 2 =
                    Some (le2 (Z_to_bv 64 (bv_unsigned (cp_b fr 35) + 256 * bv_unsigned (cp_b fr 34)))))
        by (rewrite cl_le2; apply (cl_rd _ _ _ B _ 28 2); [exact HBo | slia | rewrite EB; unfold cp_struct; rewrite RC;
              reflexivity]).
      clear HBo.
      step.
      chk_core (o + 26) RX26 (Z_to_bv 5 12) SH26 pre_sr no_extra.
      step. step.
      rewrite (cl_zxb_eqb (cp_b fr 22) 0) by (clear; lia).
      rewrite cl_join_lhu. unfold cp_v.
      destruct (Z.eqb_spec (bv_unsigned (cp_b fr 22)) 0) as [E22|E22]; cbn [negb andb]; cbv iota.
      2: { subst x9. apply (EPI None). exact J. }
      pose proof (PRcL.byte_range (cp_b fr 35)). pose proof (PRcL.byte_range (cp_b fr 34)).
      step.
      chk_core (o + 28) RX28 (Z_to_bv 5 12) SH28 pre_sr add1.
      step. rewrite cl_zx16 by lia.
      step. step.
      rewrite (rc_eqb_lit (bv_unsigned (cp_b fr 35) + 256 * bv_unsigned (cp_b fr 34)) 770) by lia.
      destruct (Z.eqb_spec (bv_unsigned (cp_b fr 35) + 256 * bv_unsigned (cp_b fr 34)) 770) as [H770|H770]; cbv iota.
      { rewrite orb_true_r. uv. step. step. apply (STL 1). exact J. }
      step. step.
      rewrite (rc_eqb_lit (bv_unsigned (cp_b fr 35) + 256 * bv_unsigned (cp_b fr 34)) 256) by lia.
      destruct (Z.eqb_spec (bv_unsigned (cp_b fr 35) + 256 * bv_unsigned (cp_b fr 34)) 256) as [H256|H256];
        cbn [negb]; cbv iota.
      { uv. step. step. apply (STL 1). exact J. }
      subst x9. apply (EPI None). exact J.
    - eapply D7B; [exact K0 | exact K1 | exact Rw | exact Ew | exact E9 | exact J].
  Qed.

  (* aJc across a call whose writes are inside [lo', S - 64), S - 8864 <= lo'. *)
  Lemma jc_call : forall m1 m2 vc lo', aJc m1 vc -> S - 8864 <= lo' ->
    munch [(lo', S + -64)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 -> stk rsegs m2 (S - 8864) (S + -64) ->
    aJc m2 vc.
  Proof.
    intros m1 m2 vc lo' (FR & HBo & WRo & HV & MU & WM & MI & ST & JA) Hlo MU2 WM2 MI2 ST2.
    pose proof DOs as DOs'. pose proof DVs as DVs'.
    assert (Hs : sub_fp [(lo', S + -64)] [(S - 8864, S)]).
    { intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [clear -Hx Hlo; lia | exact I]. }
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj MI2 (conj ST2 _)))))))).
    - eapply rw_cells_transport; [exact FR | exact MU2 | exact WM2 |].
      cbn [disjoint_from cells_size csize Nat.add]. split; [clear; lia | exact I].
    - eapply bytes_at_transport; [exact HBo | exact MU2 |]. cbn [disjoint_from]. rewrite LB.
      split; [clear -DOs' Hlo; lia | exact I].
    - eapply wr_at_transport; eassumption.
    - eapply rw_cells_transport; [exact HV | exact MU2 | exact WM2 |].
      cbn [disjoint_from cells_size csize Nat.add]. split; [clear -DVs' Hlo; lia | exact I].
    - eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2].
      intros x Hx. unfold aWc in Hx. cbn [outside] in *. destruct Hx as (_ & _ & H & _).
      split; [clear -H Hlo; lia | exact I].
    - eapply wmono_trans; eassumption.
    - exact (ja_win _ m1 m2 JA MU2 WM2 Hs).
  Qed.

  (* The 50 bytes at f are kept and stay addressable in a memory that the run reached writing only aWc.
     CHANGED (_F :1034-1051): the assert INf (In (f, f + 50) aDf) and the acl_out_fpw_d arguments are dropped. *)
  Lemma acl_f1 : 50 <= n -> forall m1, munch aWc m m1 -> bytes_at rsegs m1 f fr /\ addressable m1 f 50.
  Proof.
    intros HN m1 MU.
    destruct (HF HN) as (Hf0 & Hf50 & HFm & DFs). destruct (AFU HN) as (AF & _).
    pose proof (DOf HN) as DOf'. pose proof DVf as DVf'.
    assert (AP : forall i, 0 <= i < 50 -> app_mem (f + i)) by (intros i Hi; exact (acl_app_in m f 50 i AF Hi)).
    split.
    - apply (fl_bytes aWc m m1 f fr HFm MU). rewrite Lfr. intros x Hx.
      assert (Hap : app_mem x) by (replace x with (f + (x - f)) by ring; apply AP; clear -Hx; lia).
      apply acl_out_Wc; [exact Hap | clear -Hx DOf'; lia | clear -Hx DVf'; lia | clear -Hx DFs; lia].
    - apply (acl_addr_munch aWc m m1 f 50 AF MU). intros i Hi.
      apply acl_out_Wc_sh; [exact (AP i Hi) | clear -Hi DFs; lia].
  Qed.

  (* 0x8389c (after the second bcmp, a0 = w2): s6 = the shadow address of o, w2 to s4, the kind word at o
     (checked); k = 1: d7a; else reac_ctrl_checksum_verify(f): 0 goes to d5, else the epilogue with -1. *)
  Lemma d4 : k <> 0 -> forall w2, -256 < w2 < 256 -> (w2 =? 0) = cl_eq6 fr us ->
    forall x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x22 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> aJc m1 vb ->
    evtF rsegs RNG (aQc (cl_d4 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 (Z_to_bv 64 w2) x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) x20 (Z_to_bv 64 off) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8389c) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K0 w2 Rw Ew x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x22 x28 x29 x30 x31 m1 E9 J.
    destruct (HK K0) as (HN & EB & _).
    pose proof J as (_ & HBo & _ & _ & MU & _ & MI & ST & JA).
    pose proof JA as (AC & _ & _).
    assert (R0 : ov_read_bytes rsegs m1 (wa (o + 0)) 4 = Some (le4 (Z_to_bv 64 k)))
      by (rewrite cl_le4_small by slia; apply (cl_rd _ _ _ B _ 0 4); [exact HBo | slia | rewrite EB; reflexivity]).
    pose proof (acl_chk m1 o 36 0 4 o (acl_AO1 m1 MU) ltac:(slia) ltac:(slia) ltac:(slia) (acl_mod_al0 o Ho4)
      ltac:(ring)) as SH0.
    pose proof Ro as RX0.
    destruct (HF HN) as (Hf0 & Hf50 & _ & DFs). destruct (acl_f1 HN m1 MU) as (HF1 & AF1).
    pose proof (bytes_at_sub rsegs m1 f fr 18 32 HF1 ltac:(rewrite Lfr; clear; lia)) as H18.
    rewrite firstn_all2 in H18 by (rewrite length_skipn, Lfr; clear; lia). change (Z.of_nat 18) with 18 in H18.
    assert (A18 : addressable m1 (f + 18) 32) by (apply (acl_addr_sub m1 f 50); [exact AF1 | clear; lia..]).
    assert (ES : bv_unsigned (Z_to_bv 64 (S + -64)) = S + -64) by (apply unsigned_lit; slia).
    (* route (C): the PROVED footprint run without a shadow premise (was the Section hypothesis HCV). *)
    pose proof BCKF.reac_ctrl_checksum_verify_F_holds_on as HC. unfold reac_ctrl_checksum_verify_contract_F_on,
      REAC_CTRL_CHECKSUM_VERIFY, REAC_CTRL_CHECKSUM_VERIFY_FRAME in HC.
    pose proof epi as EPI. pose proof d5 as D5. pose proof d7a as D7A. pose proof (jc_call m1) as JC.
    clear MU HF1 AF1. sc.
    pre_sr o RX0.
    chk_core o RX0 (Z_to_bv 5 10) SH0 pre_no add1.
    step. rewrite (cl_sx32 k) by (clear -Rk; lia).
    step. step.
    rewrite (rc_eqb_lit k 1) by (clear -Rk; lia).
    unfold cl_d4. destruct (Z.eqb_spec k 1) as [K1|K1]; cbn [negb andb]; cbv iota.
    - replace (cl_d5 k fr us) with (cl_d7 k fr us) by (unfold cl_d5; rewrite K1; reflexivity).
      eapply D7A; [exact K1 | exact Rw | exact Ew | exact E9 | exact J].
    - step. step.
      eapply evtF_cut.
      { eapply HC with (p := f) (lo := S - 8864) (bs := skipn 18 fr).
        all: rewrite ?ES.
        - exact Hf0.
        - exact Hf50.
        - reflexivity.
        - rewrite length_skipn, Lfr. reflexivity.
        - exact H18.
        - exact ST.
        - clear; lia.
        - clear -DFs; lia.
        - exact AC.
        - exact A18.
        - intros x Hx. cbn [outside]. split; [|exact I].
          clear -Hx HHM. unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG,
            HIGHMEM_BEG in *. lia.
        - apply (rng_sub' RNG (S - 8864) 8864); [exact RWIN | split; lia].
        - apply (rng_sub' RNG 0x10000 0x5ee000); [exact RIMG | unfold GOT_CELL_K; split; lia].
        - apply (rng_sub' RNG 0x10000 0x5ee000); [exact RIMG | unfold CELL_K; split; lia].
        - apply (rng_sub' RNG f 50); [exact (RGf HN) | split; lia].
        - rewrite <- Hoff. apply (rng_sub' RNG _ _ _ _ (RGfs HN)).
          Z.div_mod_to_equations; lia. }
      intros ms' (t0'' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m2 & E & MU2 & WM2 & MI2 & ST2). subst ms'.
      rewrite ES in MU2, ST2.
      pose proof (JC m2 vb (S + -64 - 16) J ltac:(clear; lia) MU2 WM2 (MI2 MI) ST2) as J2.
      replace (ret_pc (Z_to_bv 64 0x83910)) with (Z_to_bv 64 0x83910)
        by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
      unfold cl_bsum.
      destruct (Z.eqb_spec (blocksum (skipn 18 fr)) 0) as [B0|B0]; cbn [negb andb]; cbv iota.
      + step. rewrite (cl_eqb0 0) by (clear; lia). change (0 =? 0) with true. cbn [negb]. cbv iota.
        eapply D5; [exact K0 | exact K1 | exact Rw | exact Ew | exact E9 | exact J2].
      + step. rewrite (cl_eqb0 (-1)) by (clear; lia). change (-1 =? 0) with false. cbn [negb]. cbv iota.
        subst x9. apply (EPI None). exact J2.
  Qed.

  (* The 6 bytes at u are kept and stay addressable in a memory that the run reached writing only aWc.
     CHANGED (_F :1126-1143): the assert INu (In (u, u + 6) aDf) and the acl_out_fpw_d arguments are dropped. *)
  Lemma acl_u1 : 50 <= n -> forall m1, munch aWc m m1 -> bytes_at rsegs m1 u us /\ addressable m1 u 6.
  Proof.
    intros HN m1 MU.
    destruct (HU HN) as (Hu6 & HUm & DUs). destruct (AFU HN) as (_ & AU & _).
    pose proof DOu as DOu'. pose proof DVu as DVu'.
    assert (AP : forall i, 0 <= i < 6 -> app_mem (u + i)) by (intros i Hi; exact (acl_app_in m u 6 i AU Hi)).
    split.
    - apply (fl_bytes aWc m m1 u us HUm MU). rewrite Lus. intros x Hx.
      assert (Hap : app_mem x) by (replace x with (u + (x - u)) by ring; apply AP; clear -Hx; lia).
      apply acl_out_Wc; [exact Hap | clear -Hx DOu'; lia | clear -Hx DVu'; lia | clear -Hx DUs; lia].
    - apply (acl_addr_munch aWc m m1 u 6 AU MU). intros i Hi.
      apply acl_out_Wc_sh; [exact (AP i Hi) | clear -Hi DUs; lia].
  Qed.

  (* The cells the bcmp wrapper reads survive a call whose writes are inside [lo', S - 64). *)
  Lemma acl_CL_call : forall m1 m2 lo', aCL m1 -> S - 8864 <= lo' -> munch [(lo', S + -64)] m1 m2 -> aCL m2.
  Proof.
    intros m1 m2 lo' (C1 & C2 & C3 & C4 & C5) Hlo MU2.
    assert (O : forall x, x < HIGHMEM_BEG -> outside [(lo', S + -64)] x)
      by (intros x Hx; cbn [outside]; split; [clear -Hx Hlo HHM; lia | exact I]).
    refine (conj _ (conj _ (conj _ (conj _ _)))); (eapply fl_bytes; [eassumption | exact MU2 |]);
      intros x Hx; apply O; rewrite ?length_le8 in Hx; cbn [length Z.of_nat Pos.of_succ_nat] in Hx;
      clear -Hx; unfold REAL_BCMP, REAL_MEMCMP, GOT_CF, CF, HIGHMEM_BEG in *; lia.
  Qed.

  (* 0x8387c (a0 = o + 4): bcmp(o + 4, u, 6) by the wrapper's asan contract: 0 (the source equals u) goes to the
     epilogue with -1, else bcmp(o + 10, u, 6) = w2 and d4. *)
  Lemma d3 : k <> 0 -> forall x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> aJc m1 vb -> aCL m1 ->
    evtF rsegs RNG (aQc (cl_d3 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 (Z_to_bv 64 (o + 4)) x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 u) (Z_to_bv 64 off) x22
               s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8387c) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K0 x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 m1 E9 J CL.
    destruct (HK K0) as (HN & EB & _).
    pose proof J as (_ & HBo & _ & _ & MU & _ & MI & ST & JA).
    pose proof JA as (AC & SW & _).
    pose proof CL as (CL1 & CL2 & CL3 & CL4 & CL5).
    destruct (HU HN) as (Hu6 & _ & DUs). destruct (AFU HN) as (_ & _ & AU6 & AU7).
    destruct (acl_u1 HN m1 MU) as (HU1 & AU1).
    pose proof (acl_AO1 m1 MU) as AO1.
    pose proof (bytes_at_sub rsegs m1 o B 4 6 HBo ltac:(rewrite LB; clear; lia)) as HS.
    replace (firstn 6 (skipn 4 B)) with [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11] in HS
      by (rewrite EB; reflexivity).
    change (Z.of_nat 4) with 4 in HS.
    destruct (acl_memcmp6 [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11] us eq_refl Lus)
      as (w1 & HM1 & Rw1 & Ew1).
    rewrite cl_eq6_src in Ew1.
    assert (AOi : forall i, 0 <= i < 36 -> app_mem (o + i)) by (intros i Hi; exact (acl_app_in m o 36 i AO Hi)).
    assert (A4 : addressable m1 (o + 4) 6) by (apply (acl_addr_sub m1 o 36); [exact AO1 | clear; lia..]).
    assert (EO4 : bv_unsigned (Z_to_bv 64 (o + 4)) = o + 4) by (apply unsigned_lit; slia).
    assert (EO10 : bv_unsigned (Z_to_bv 64 (o + 10)) = o + 10) by (apply unsigned_lit; slia).
    assert (EU : bv_unsigned (Z_to_bv 64 u) = u) by (apply unsigned_lit; slia).
    assert (E6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
    assert (ES : bv_unsigned (Z_to_bv 64 (S + -64)) = S + -64) by (apply unsigned_lit; slia).
    pose proof DOs as DOs'.
    pose proof HBC as HB. unfold BWo.bcmp_wrap_contract_F_on, BCMP_WRAP_K in HB. cbv zeta in HB.
    pose proof epi as EPI. pose proof d4 as D4. pose proof jc_call as JC. pose proof acl_CL_call as CLC.
    pose proof (acl_u1 HN) as U1. pose proof acl_AO1 as AOf.
    clear MU HBo AO1. sc.
    step. step. step.
    eapply evtF_cut.
    { eapply HB with (ls := [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11]) (rs := us)
        (v := w1) (lo := S - 8864).
      all: rewrite ?EO4, ?EU, ?E6, ?ES.
      - exact HS.
      - exact HU1.
      - exact HM1.
      - exact MI.
      - clear; lia.
      - exact A4.
      - exact AU1.
      - right. replace (o + 4 + 6) with (o + 10) by ring. apply AOi. clear; lia.
      - right. exact AU6.
      - right. replace (o + 4 + 7) with (o + 11) by ring. apply AOi. clear; lia.
      - right. exact AU7.
      - clear -DOs'; lia.
      - clear -DUs; lia.
      - exact ST.
      - clear -RS; lia.
      - exact HHM.
      - clear -HAE; lia.
      - exact AC.
      - (* route (C): the call's region, bcmp_wrap_shadow_R (o + 4) u 6, from HSR through the transport to m1 *)
        apply (SRO.shadow_rw_on_mono (reac_ctrl_classify_box_frame_post_call_shadow_R n u o));
          [intros a Ha; exact (conj HN (or_introl Ha)) | exact (SW _ HSR)].
      - exact CL1.
      - exact CL2.
      - exact CL3.
      - exact CL4.
      - exact CL5.
      - exact RBY.
      - exact RIMG.
      - apply (rng_sub' RNG (S - 8864) 8864); [exact RWIN | split; lia].
      - apply (rng_sub' RNG o 36); [exact RGo | split; lia].
      - right. unfold shadow_addr. rewrite <- Hoff. apply (rng_sub' RNG _ _ _ _ RGos).
        Z.div_mod_to_equations; lia.
      - apply (rng_sub' RNG u 6); [exact (RGu HN) | split; lia].
      - right. unfold shadow_addr. rewrite <- Hoff. apply (rng_sub' RNG _ _ _ _ (RGus HN)).
        Z.div_mod_to_equations; lia. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & E & MU2 & WM2
                & MI2 & ST2 & _).
    subst ms'. rewrite ES in MU2, ST2. unfold BCMP_WRAP_K in MU2.
    pose proof (JC m1 m2 vb (S + -64 - 4560) J ltac:(clear; lia) MU2 WM2 MI2 ST2) as J2.
    pose proof (CLC m1 m2 (S + -64 - 4560) CL ltac:(clear; lia) MU2) as CLm2.
    clear HS HU1 AU1 A4 MI ST AC SW CL1 CL2 CL3 CL4 CL5 MU2 WM2 MI2 ST2.
    replace (ret_pc (Z_to_bv 64 0x83888)) with (Z_to_bv 64 0x83888)
      by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
    step.
    rewrite (cl_eqb0 w1) by (clear -Rw1; lia). rewrite Ew1.
    unfold cl_d3. destruct (cl_eq6 (skipn 6 fr) us); cbv iota.
    { subst x9. apply (EPI None). exact J2. }
    pose proof J2 as (_ & HBo2 & _ & _ & MU2 & _ & MI2 & ST2 & JA2).
    pose proof JA2 as (AC2 & SW2 & _).
    pose proof CLm2 as (CL1 & CL2 & CL3 & CL4 & CL5).
    destruct (U1 m2 MU2) as (HU2 & AU2).
    assert (A10 : addressable m2 (o + 10) 6) by (apply (acl_addr_sub m2 o 36); [exact (AOf m2 MU2) | clear; lia..]).
    pose proof (bytes_at_sub rsegs m2 o B 10 6 HBo2 ltac:(rewrite LB; clear; lia)) as HD.
    replace (firstn 6 (skipn 10 B)) with [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5] in HD
      by (rewrite EB; reflexivity).
    change (Z.of_nat 10) with 10 in HD.
    destruct (acl_memcmp6 [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5] us eq_refl Lus)
      as (w2 & HM2 & Rw2 & Ew2).
    rewrite cl_eq6_dst in Ew2.
    clear MU2 HBo2.
    step. step. step. step.
    eapply evtF_cut.
    { eapply HB with (ls := [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5]) (rs := us)
        (v := w2) (lo := S - 8864).
      all: rewrite ?EO10, ?EU, ?E6, ?ES.
      - exact HD.
      - exact HU2.
      - exact HM2.
      - exact MI2.
      - clear; lia.
      - exact A10.
      - exact AU2.
      - right. replace (o + 10 + 6) with (o + 16) by ring. apply AOi. clear; lia.
      - right. exact AU6.
      - right. replace (o + 10 + 7) with (o + 17) by ring. apply AOi. clear; lia.
      - right. exact AU7.
      - clear -DOs'; lia.
      - clear -DUs; lia.
      - exact ST2.
      - clear -RS; lia.
      - exact HHM.
      - clear -HAE; lia.
      - exact AC2.
      - (* route (C): the call's region, bcmp_wrap_shadow_R (o + 10) u 6, from HSR through the transport to m2 *)
        apply (SRO.shadow_rw_on_mono (reac_ctrl_classify_box_frame_post_call_shadow_R n u o));
          [intros a Ha; exact (conj HN (or_intror Ha)) | exact (SW2 _ HSR)].
      - exact CL1.
      - exact CL2.
      - exact CL3.
      - exact CL4.
      - exact CL5.
      - exact RBY.
      - exact RIMG.
      - apply (rng_sub' RNG (S - 8864) 8864); [exact RWIN | split; lia].
      - apply (rng_sub' RNG o 36); [exact RGo | split; lia].
      - right. unfold shadow_addr. rewrite <- Hoff. apply (rng_sub' RNG _ _ _ _ RGos).
        Z.div_mod_to_equations; lia.
      - apply (rng_sub' RNG u 6); [exact (RGu HN) | split; lia].
      - right. unfold shadow_addr. rewrite <- Hoff. apply (rng_sub' RNG _ _ _ _ (RGus HN)).
        Z.div_mod_to_equations; lia. }
    intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 & E
                & MU3 & WM3 & MI3 & ST3 & _).
    subst ms'. rewrite ES in MU3, ST3. unfold BCMP_WRAP_K in MU3.
    pose proof (JC m2 m3 vb (S + -64 - 4560) J2 ltac:(clear; lia) MU3 WM3 MI3 ST3) as J3.
    replace (ret_pc (Z_to_bv 64 0x8389c)) with (Z_to_bv 64 0x8389c)
      by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
    eapply D4; [exact K0 | exact Rw2 | exact Ew2 | exact E9 | exact J3].
  Qed.

  (* 0x83814: the UBSan null/alignment checks of o, then the OUI bytes 6, 7, 8 of the frame at o + 4, o + 5, o + 6
     (each checked) against 00 40 ab: a mismatch goes to the epilogue with -1, else d3. *)
  Lemma d2 : k <> 0 -> forall x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> aJc m1 vb -> aCL m1 ->
    evtF rsegs RNG (aQc (cl_d2 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 u) (Z_to_bv 64 off) x22
               s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83814) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K0 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 m1 E9 J CL.
    destruct (HK K0) as (HN & EB & _).
    pose proof J as (_ & HBo & _ & _ & MU & _).
    assert (R4 : ov_read_bytes rsegs m1 (wa (o + 4)) 1 = Some [cp_b fr 6])
      by (apply (cl_rd _ _ _ B _ 4 1); [exact HBo | slia | rewrite EB; reflexivity]).
    assert (R5 : ov_read_bytes rsegs m1 (wa (o + 5)) 1 = Some [cp_b fr 7])
      by (apply (cl_rd _ _ _ B _ 5 1); [exact HBo | slia | rewrite EB; reflexivity]).
    assert (R6 : ov_read_bytes rsegs m1 (wa (o + 6)) 1 = Some [cp_b fr 8])
      by (apply (cl_rd _ _ _ B _ 6 1); [exact HBo | slia | rewrite EB; reflexivity]).
    pose proof (acl_AO1 m1 MU) as AO1.
    pose proof (acl_chk m1 o 36 4 1 (o + 4) AO1 ltac:(slia) ltac:(slia) ltac:(slia)
      (acl_mod_al o 4 1 Ho4 ltac:(slia) ltac:(slia)) eq_refl) as SH4.
    pose proof (acl_chk m1 o 36 5 1 (o + 5) AO1 ltac:(slia) ltac:(slia) ltac:(slia)
      (acl_mod_al o 5 1 Ho4 ltac:(slia) ltac:(slia)) eq_refl) as SH5.
    pose proof (acl_chk m1 o 36 6 1 (o + 6) AO1 ltac:(slia) ltac:(slia) ltac:(slia)
      (acl_mod_al o 6 1 Ho4 ltac:(slia) ltac:(slia)) eq_refl) as SH6.
    assert (RX4 : 0 <= o + 4 < 2^64) by slia. assert (RX5 : 0 <= o + 5 < 2^64) by slia.
    assert (RX6 : 0 <= o + 6 < 2^64) by slia.
    pose proof epi as EPI. pose proof d3 as D3. clear MU HBo AO1. sc.
    unfold cl_d2, cl_oui, cp_v.
    uo.
    step.
    chk_core (o + 4) RX4 (Z_to_bv 5 12) SH4 pre_sr no_extra.
    step. step. rewrite (cl_zxb_eqb (cp_b fr 6) 0) by (clear; lia).
    destruct (Z.eqb_spec (bv_unsigned (cp_b fr 6)) 0) as [E6|E6]; cbn [negb andb]; cbv iota.
    2: { subst x9. apply (EPI None). exact J. }
    step.
    chk_core (o + 5) RX5 (Z_to_bv 5 13) SH5 pre_sr no_extra.
    step. step. step. rewrite (cl_zxb_eqb (cp_b fr 7) 64) by (clear; lia).
    destruct (Z.eqb_spec (bv_unsigned (cp_b fr 7)) 64) as [E7|E7]; cbn [negb andb]; cbv iota.
    2: { subst x9. apply (EPI None). exact J. }
    step.
    chk_core (o + 6) RX6 (Z_to_bv 5 13) SH6 pre_sr no_extra.
    step. step. step. rewrite (cl_zxb_eqb (cp_b fr 8) 171) by (clear; lia).
    destruct (Z.eqb_spec (bv_unsigned (cp_b fr 8)) 171) as [E8|E8]; cbn [negb andb]; cbv iota.
    2: { subst x9. apply (EPI None). exact J. }
    eapply D3; [exact K0 | exact E9 | exact J | exact CL].
  Qed.

  (* 0x8380c (after reac_ctrl_parse, a0 = k): s1 = -1; k = 0 goes to the epilogue, else d2. *)
  Lemma d1 : forall x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 m1,
    aJc m1 vb -> aCL m1 ->
    evtF rsegs RNG (aQc (if k =? 0 then None else cl_d2 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 (Z_to_bv 64 k) x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 u) (Z_to_bv 64 off) x22
               s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8380c) fc None m1 (seg_rom rsegs)).
  Proof.
    intros x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 m1 J CL.
    pose proof epi as EPI. pose proof d2 as D2. sc.
    step. step.
    rewrite (rc_eqb_lit k 0) by (clear -Rk; lia).
    destruct (Z.eqb_spec k 0) as [K0|K0]; cbv iota.
    - apply (EPI None). exact J.
    - eapply D2; [exact K0 | reflexivity | exact J | exact CL].
  Qed.

  (* The stretch as the glue consumes it: a RESTATEMENT of d1, not a new run.  The cut state at 0x8380c is written
     out (aJc and aJa unfolded) over the Section's own base memory m, so its munch and wmono are reflexive, and the
     post is in `classify` form (RcClassifyLib.classify_d1, as reac_ctrl_classify_box_frame_holds_F does for `pro`).
     The glue instantiates k := fst (ctrlparse n fr) and B := snd (ctrlparse n fr).  route (C): no shadow premise of
     its own (the Section's HSR names the one region the run needs present); aJa's transport is the identity at m. *)
  Lemma d1_B : k = fst (ctrlparse n fr) ->
    forall x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word,
    rw_cells rsegs m (S + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at rsegs m o B -> wr_at rsegs m o 36 -> rw_cells rsegs m v [CB 4 vb] ->
    mem_inv rsegs m -> stk rsegs m (S - 8864) (S + -64) ->
    asan_cells m -> addressable m (S - 8864) 8864 ->
    aCL m ->
    evtF rsegs RNG (aQc (classify n fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 (Z_to_bv 64 k) x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 u) (Z_to_bv 64 off) x22
               s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x8380c) fc None m (seg_rom rsegs)).
  Proof.
    intros Ek x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31
      FR HBo WRo HV MI ST AC AW CL.
    rewrite classify_d1, <- Ek.
    apply (d1 x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 m); [| exact CL].
    unfold aJc, aJa.
    split; [exact FR|]. split; [exact HBo|]. split; [exact WRo|]. split; [exact HV|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|].
    split; [exact AC|]. split; [exact (fun (P : Z -> Prop) (HP : SRO.shadow_rw_on P m) => HP) | exact AW].
  Qed.

End Post.
