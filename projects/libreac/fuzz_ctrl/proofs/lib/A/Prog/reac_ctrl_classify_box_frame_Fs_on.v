(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/C_reac_ctrl_classify_box_frameLib.v, with its module paths, module names, addresses and numbers changed; 234 of its 914 lines of code are new or changed and 309 lines of the source are left out. *)
(* lib/A/Prog/reac_ctrl_classify_box_frame_Fs_on.v -- ROUTE (C) twin of lib/A/Prog/reac_ctrl_classify_box_frame_Fs.v (not in this delivery)
   (a Theorem Labs lane 16:2xZ, the frozen-file twin pattern; writer: a Theorem Labs lane).  rule 24: no function proved (the same two
   stretches of reac_ctrl_classify_box_frame's proved v1.9 run as Fs.v (not in this delivery), see Fs.v's (not in this delivery) header for the run of record, the
   image root, the tools and the compares).
   WHY A TWIN FILE: the image-A closure rule (TWIN-LEAF, 16:02Z) bars the root lib/MemNorm* from the classify glue's
   closure. Fs.v (not in this delivery) Requires bcmp_wrap_F.v (not in this delivery), which Requires the root lib/MemNormP, for its stretch 2's bcmp step (d3 cites
   bcmp_wrap_F.bcmp_wrap_holds_F); Fs.v (an earlier version, blob f1c19000153, not in this delivery) stays byte-identical (text of record a working branch)
   and this file Requires neither bcmp_wrap_F.v (not in this delivery) nor Fs.v (not in this delivery). It holds what the glue cites:
   - reac_ctrl_classify_box_frame_pre_call_F: Fs.v's stretch 1, statement and proof copied unchanged (it has no shadow
     premise);
   - reac_ctrl_classify_box_frame_post_call_shadow_R and reac_ctrl_classify_box_frame_post_call_F_on: stretch 2 in its
     _on form (below).
   Copied from Fs.v (the earlier version above, not in this delivery) unchanged apart from comment text: the Requires (lines 88-99), the tactics cls_accF .. add1 (lines 107-179, with the one
   token of line 123 written A.Bz.Lib.MState.unsigned_lit_wrap, the constant it binds in Fs.v: ctrlgate DUP, the closure
   reaches lib/A/Bz/Lib/MState.v and lib/Lib/MState.v), stretch 1 (lines 978-1028), and Section Post (lines 181-976)
   as Section PostOn with the route (C) changes listed below.
   R = the shadow bytes stretch 2 needs PRESENT through its shadow premise (the bytes it reads or stores through it):
   only the regions of its two bcmp wrapper calls, bcmp_wrap_shadow_R (o + 4) u 6 at 0x8326c and
   bcmp_wrap_shadow_R (o + 10) u 6 at 0x83280 (a Theorem Labs lane's bcmp_wrap_contract_F_on, bcmp_wrap_c_on.v), both reached
   only when k <> 0, hence 50 <= n (cl_hk). Not in R: the stretch's own instrumented checks of o, v, f and u load their
   shadow bytes with the values the addressable premises give (acl_chk; ROBS / RVBS / RFBS / RUBS are footprint rows);
   reac_ctrl_checksum_verify's footprint contract has no shadow premise (a Theorem Labs lane's
   reac_ctrl_checksum_verify_contract_F_on, proved by a Theorem Labs lane's reac_ctrl_checksum_verify_F_holds_on); and the
   stretch stores no shadow byte (Section Post's own note on aXs: the window-shadow row of aWc is carried, not written).
   The post's universal `shadow_rw m'` becomes the transport `forall P, shadow_rw_on P m1 -> shadow_rw_on P m'`: the
   stretch's own stores miss the shadow (A.ShadowRwOnK.fl_shadow_rw_on, the twin of Fs.v's fl_shadow_rw step) and the
   two callees write only their stack frames (jc_call / ja_win). The premises keep mem_inv as they are; no
   AsanRTInv.RT, FRA or SlotInv shell is used.
   Section PostOn is Section Post with exactly these changes outside comment text, each marked `route (C)`: a Variable m0 (the start memory)
   and the Hypothesis HSR (R at m0); aJa carries the transport from m0 in place of shadow_rw; ja_win / ja_v keep it by
   fl_shadow_rw_on; d4 cites reac_ctrl_checksum_verify_F_holds_on (one premise fewer); d3 cites
   bcmp_wrap_on.bcmp_wrap_holds_F_on (a Theorem Labs lane's root-free proof) and gives it its region from HSR by
   shadow_rw_on_mono.  It sits in Module PostOnM. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge
  RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcBoxLib RcParse RcClassify
  RcClassifyLib RcAsan RcAsanLib reac_ctrl_classify_box_frame_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  memcmp_c bcmp_wrap_c reac_ctrl_parse_c reac_ctrl_checksum_verify_c reac_ctrl_checksum_verify_F
  reac_ctrl_classify_box_frame_c reac_ctrl_classify_box_frame.
(* route (C): the region form, the flat-run transport, and the bcmp wrapper's _on leaf and its root-free proof (in place
   of Fs.v's bcmp_wrap_F). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOn A.ShadowRwOnK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require bcmp_wrap_c_on bcmp_wrap_on.
(* Last: StepF's step / if_* (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The metadata-byte access of an instrumented check is written (X / 8 + off), with off the shadow offset the run
   read from its cell, and its rng premise holds a division too; StepF's arithmetic has no Euclidean equations,
   so those two go through Z.div_mod_to_equations here.  Every other access closes with the stock solve_acc1. *)
Ltac cls_accF :=
  lazymatch goal with
  | |- acc_in ?RNG (?x, ?nn) =>
      let E := addr_expr x in
      lazymatch E with
      | context [Z.div _ _] =>
          let nz := eval cbv in (Z.of_nat nn) in
          match goal with
          | H : rng RNG ?lo ?len |- _ =>
              lazymatch lo with
              | context [Z.div _ _] =>
                  apply (rng_acc_varZ RNG lo len x nn nz H (@eq_refl Z nz));
                  try (match goal with Hf : _ = ASAN_K |- _ => rewrite Hf end);
                  cbv [wa]; rewrite ?A.Bz.Lib.MState.unsigned_lit_wrap;
                  unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia
              end
          end
      end
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= cls_accF.

(* The old file's shadow-check tactics over evtF (an Ltac body binds the tactics in scope where it is written, so
   the evt forms of the old file cannot serve here). *)
Ltac steps_until_if :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; steps_until_if
  | _ => idtac
  end.

Ltac bjoin G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

(* A shadow check of the access of w bytes at X (RX : 0 <= X < 2^64): SH gives the shadow byte k, its read at
   X / 8 + off and the check fact (k = 0, or X mod 8 + (w - 1) < k); `pre` steps to the shadow address (srli; add,
   or nothing when a register holds it), then the load of k and `bnez` go on when k = 0; else the slow path
   `andi r, X, 7` (and `addi r, r, w - 1` by `extra`) and `blt r, k` go on as the check passes. The register r is
   generalized at the join, and the error path (a call of the report entry) is not reached. *)
Ltac chk_core X RX r SH pre extra :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
  destruct SH as (k & RK & OK & KR);
  pre X RX; steps_until_if; clear RK;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (clear -KR; lia);
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RNG Q (MS (bvmap_set r rr R) F B fc rv mm ro));
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

(* R of stretch 2 (route (C)): the range-check words its two bcmp wrapper calls read, when the calls are reached. *)
Definition reac_ctrl_classify_box_frame_post_call_shadow_R (n u o : Z) (a : Z) : Prop :=
  50 <= n /\ (bcmp_wrap_c_on.bcmp_wrap_shadow_R (o + 4) u 6 a \/ bcmp_wrap_c_on.bcmp_wrap_shadow_R (o + 10) u 6 a).

Module PostOnM.

Section PostOn.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f n u o v S k off : Z) (fr us vb B : list byte).
  (* route (C): m0 is the memory the stretch starts from (the glue's m1); every shadow fact the run carries is the
     transport `forall P, shadow_rw_on P m0 -> shadow_rw_on P mc` (the post of record), and the only region it needs
     present is HSR's. *)
  Variable m0 : word -> option byte.

  (* CHANGED (side-stack premises dropped, a Theorem Labs lane's decision): the proved run's aWf, aDf, aTL and FS are gone;
     aXs is only the shadow of the window (its fp_w [1%nat] FS part is dropped), and aJa has no fp / aTL conjunct.
     This stretch writes neither the side stack nor any shadow byte; the proved run only carried those facts. *)
  Definition aXs : list ivl := [(shadow_addr (S - 8864), shadow_addr S)].
  Definition aWc : list ivl := (o, o + 36) :: (v, v + 4) :: (S - 8864, S) :: aXs.

  (* The runtime state the post names. *)
  (* route (C): the universal shadow_rw is replaced by the transport from m0 (CHANGED from Section Post). *)
  Definition aJa (mc : word -> option byte) : Prop :=
    asan_cells mc /\ (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m0 -> A.ShadowRwOn.shadow_rw_on P mc) /\
    addressable mc (S - 8864) 8864.

  (* The cells the bcmp wrapper reads. *)
  Definition aCL (mc : word -> option byte) : Prop :=
    bytes_at rsegs mc REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs mc REAL_MEMCMP (le8 (wa MEMCMP)) /\
    bytes_at rsegs mc GOT_CF (le8 (wa CF)) /\ bytes_at rsegs mc (CF + 254) [Z_to_bv 8 1] /\
    bytes_at rsegs mc (CF + 255) [Z_to_bv 8 1].

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
  (* route (C): the region of record at the start memory (in place of the universal shadow_rw of aJa m1). *)
  Hypothesis HSR : A.ShadowRwOn.shadow_rw_on (reac_ctrl_classify_box_frame_post_call_shadow_R n u o) m0.
  (* DROPPED: FP0 (fp [1%nat] m (bv_unsigned tp) FS (S - 8864) S aWf aDf). *)

  (* The footprint of the run and the region it holds, one premise per region (the contract's own list, without
     RSTKS and RBCS, which only the parse call used, and with RFP (rng_fp_cls1) DROPPED). *)
  Variable RNG : footprint.
  Hypothesis RBY : rng_bytes RNG.
  Hypothesis RIMG : rng RNG 0x10000 0x5ee000.
  Hypothesis RSTK : rng RNG (S - 8864) 8864.
  Hypothesis ROB : rng RNG o 36.
  Hypothesis ROBS : rng RNG (shadow_addr o / 8 * 8) (shadow_addr (o + 36 - 1) / 8 * 8 + 8 - shadow_addr o / 8 * 8).
  Hypothesis RVB : rng RNG v 4.
  Hypothesis RVBS : rng RNG (shadow_addr v / 8 * 8) (shadow_addr (v + 4 - 1) / 8 * 8 + 8 - shadow_addr v / 8 * 8).
  Hypothesis RFB : 50 <= n -> rng RNG f 50.
  Hypothesis RFBS : 50 <= n ->
    rng RNG (shadow_addr f / 8 * 8) (shadow_addr (f + 50 - 1) / 8 * 8 + 8 - shadow_addr f / 8 * 8).
  Hypothesis RUB : 50 <= n -> rng RNG u 6.
  Hypothesis RUBS : 50 <= n ->
    rng RNG (shadow_addr u / 8 * 8) (shadow_addr (u + 6 - 1) / 8 * 8 + 8 - shadow_addr u / 8 * 8).

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

  (* DROPPED with FP0: acl_fs, acl_out_fpw_d, acl_out_fpw_hi, acl_out_fpw_sh (the side stack's place and the
     disjointness of the data ranges from the class-1 side-stack bytes, which only served the fp_w part of aXs). *)

  (* CHANGED: no premise `outside (fp_w [1%nat] FS) x`, and no fl_out_app step for the dropped fp_w part. *)
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

  (* CHANGED: no premise `outside (fp_w [1%nat] FS) x` (passed on to acl_out_Xs_sh). *)
  Lemma acl_out_Wc_sh : forall x, app_mem x -> (x < S - 8864 \/ S <= x) ->
    outside aWc (shadow_addr x).
  Proof.
    intros x Hap Hx. pose proof (rt_app_shadow x Hap) as Hs. unfold aWc. cbn [outside].
    split; [pose proof (acl_sh_not_in o 36 _ AO Hs) as Hq; clear -Hq; lia|].
    split; [pose proof (acl_sh_not_in v 4 _ AV Hs) as Hq; clear -Hq; lia|].
    split; [clear -Hs HHM; unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *; lia|].
    exact (acl_out_Xs_sh x Hap Hx).
  Qed.

  (* A byte of application memory apart from o, v and the window is outside the footprint.  CHANGED: no premise
     `outside (fp_w [1%nat] FS) x` (H4), and no `apply fl_out_app; [exact H4|]` step for the dropped fp_w part. *)
  Lemma acl_out_Wc : forall x, app_mem x -> (x < o \/ o + 36 <= x) -> (x < v \/ v + 4 <= x) ->
    (x < S - 8864 \/ S <= x) -> outside aWc x.
  Proof.
    intros x Hap H1 H2 H3. unfold aWc, aXs. cbn [outside].
    split; [clear -H1; lia|]. split; [clear -H2; lia|]. split; [clear -H3; lia|].
    split; [|exact I].
    apply acl_sh_out; [exact Hap | clear -RS; lia | exact HAE].
  Qed.

  (* The runtime state survives writes inside the window.  CHANGED: the fp and tls bullets (fl_fp, fl_tls) and
     `unfold aWf in FP` are dropped with aJa's fp / aTL conjuncts. *)
  Lemma ja_win : forall W' m1 m2, aJa m1 -> munch W' m1 m2 -> wmono rsegs m1 m2 -> sub_fp W' [(S - 8864, S)] ->
    aJa m2.
  Proof.
    intros W' m1 m2 (AC & SW & AW) MU WM Hs.
    assert (SHo : forall x, in_shadow x -> outside W' x)
      by (intros x Hx; exact (fl_shadow_out W' (S - 8864) S x Hs HHM Hx)).
    split; [|split].
    - apply (fl_asan_cells W' m1 m2 AC MU). intros x Hx. apply (fl_out_lo W' (S - 8864) S x Hs). left.
      clear -Hx HHM. unfold RT_LO, RT_HI, HIGHMEM_BEG in *. lia.
    - intros P HP. exact (A.ShadowRwOnK.fl_shadow_rw_on P W' m1 m2 (SW P HP) MU WM SHo).
    - exact (fl_addressable W' m1 m2 _ _ AW MU SHo).
  Qed.

  (* The runtime state survives the store of the 4 bytes at v.  CHANGED: the fp and tls bullets (fl_fp_W,
     fl_tls_W) and the assert Hs (sub_fp [(v, v + 4)] aWf, which only they used) are dropped. *)
  Lemma ja_v : forall m1 m2, aJa m1 -> munch [(v, v + 4)] m1 m2 -> wmono rsegs m1 m2 ->
    (forall x, v <= x < v + 4 -> exists b, mrd rsegs m2 (wa x) = Some b) -> aJa m2.
  Proof.
    intros m1 m2 (AC & SW & AW) MU WM RD.
    assert (SHo : forall x, in_shadow x -> outside [(v, v + 4)] x)
      by (intros x Hx; cbn [outside]; split; [pose proof (acl_sh_not_in v 4 x AV Hx) as Hq; clear -Hq; lia | exact I]).
    split; [|split].
    - apply (fl_asan_cells _ m1 m2 AC MU). intros x Hx. cbn [outside]. split; [clear -Hx HVR; lia | exact I].
    - intros P HP. exact (A.ShadowRwOnK.fl_shadow_rw_on P _ m1 m2 (SW P HP) MU WM SHo).
    - exact (fl_addressable _ m1 m2 _ _ AW MU SHo).
  Qed.

  (* 0x83354: a0 = s1, the frame restored, return. *)
  Lemma epi : forall c x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31 m1,
    aJc m1 (reac_ctrl_classify_box_frame_ev c vb) ->
    evtF rsegs RNG (aQc c)
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (cl_r c)) x10 x11 x12 x13 x14
               x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83354) fc None m1 (seg_rom rsegs)).
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

  (* The 36 bytes at o and the 4 bytes at v stay addressable in a memory that the run reached writing only aWc. *)
  (* CHANGED (acl_AO1, acl_AV1): the acl_out_fpw_d argument of acl_out_Wc_sh is dropped. *)
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

  (* 0x832c4: the check of the 4 bytes at v, s1 = 0, the store of e at v, to the epilogue. *)
  Lemma st : forall e x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31 m1,
    aJc m1 vb ->
    evtF rsegs RNG (aQc (Some e))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 (Z_to_bv 64 e) x12 x13 x14
               x15 x16 x17 x18 x19 x20 (Z_to_bv 64 off) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x832c4) fc None m1 (seg_rom rsegs)).
  Proof.
    intros e x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31 m1 J.
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

  (* 0x833a8: the tail of the classification on k (a2) and byte 19 of the frame (o + 23, checked). *)
  Lemma tl : k <> 0 -> forall x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x19 x20 x22 x28 x29 x30 x31 m1,
    aJc m1 vb ->
    evtF rsegs RNG (aQc (cl_tail k fr))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 x11 (Z_to_bv 64 k) x13 x14
               x15 x16 x17 (Z_to_bv 64 o) x19 x20 (Z_to_bv 64 off) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x833a8) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K0 x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x19 x20 x22 x28 x29 x30 x31 m1 J.
    destruct (HK K0) as (HN & EB & _).
    pose proof J as (_ & HBo & _ & _ & MU & _).
    assert (R23 : ov_read_bytes rsegs m1 (wa (o + 23)) 1 = Some [cp_b fr 19])
      by (apply (cl_rd _ _ _ B _ 23 1); [exact HBo | slia | rewrite EB; reflexivity]).
    pose proof (acl_chk m1 o 36 23 1 (o + 23) (acl_AO1 m1 MU) ltac:(slia) ltac:(slia) ltac:(slia)
      (acl_mod_al o 23 1 Ho4 ltac:(slia) ltac:(slia)) eq_refl) as SH.
    assert (RX : 0 <= o + 23 < 2^64) by slia.
    pose proof st as STL. clear MU HBo. sc.
    step. step.
    rewrite (rc_eqb_lit k 9) by slia.
    destruct (Z.eqb_spec k 9) as [K9|K9]; cbv iota.
    { step. step. replace (cl_tail k fr) with (Some 5) by (unfold cl_tail; rewrite K9; reflexivity).
      apply STL. exact J. }
    step. step.
    rewrite (rc_eqb_lit k 7) by slia.
    destruct (Z.eqb_spec k 7) as [K7|K7]; cbv iota.
    { step. step. replace (cl_tail k fr) with (Some 3) by (unfold cl_tail; rewrite K7; reflexivity).
      apply STL. exact J. }
    step. step.
    rewrite (rc_eqb_lit k 2) by slia.
    destruct (Z.eqb_spec k 2) as [K2|K2]; cbn [negb]; cbv iota.
    2: { replace (cl_tail k fr) with (Some 2)
           by (unfold cl_tail; rewrite (proj2 (Z.eqb_neq k 7) K7), (proj2 (Z.eqb_neq k 2) K2),
                 (proj2 (Z.eqb_neq k 9) K9); reflexivity).
         apply STL. exact J. }
    step.
    chk_core (o + 23) RX (Z_to_bv 5 13) SH pre_sr no_extra.
    step. step. step.
    rewrite (cl_zxb_eqb (cp_b fr 19) 3) by slia.
    destruct (Z.eqb_spec (bv_unsigned (cp_b fr 19)) 3) as [E19|E19]; cbn [negb]; cbv iota.
    - step. step. replace (cl_tail k fr) with (Some 4) by (unfold cl_tail, cp_v; rewrite K2, E19; reflexivity).
      apply STL. exact J.
    - replace (cl_tail k fr) with (Some 2)
        by (unfold cl_tail, cp_v; rewrite K2, (proj2 (Z.eqb_neq _ 3) E19); reflexivity).
      apply STL. exact J.
  Qed.

  (* 0x83350: w2 (s4, the second bcmp) = 0 goes to tl, else the epilogue with s1 = -1. *)
  Lemma d9 : k <> 0 -> forall w2, -256 < w2 < 256 -> (w2 =? 0) = cl_eq6 fr us ->
    forall x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> aJc m1 vb ->
    evtF rsegs RNG (aQc (cl_d9 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 x11 (Z_to_bv 64 k) x13 x14
               x15 x16 x17 (Z_to_bv 64 o) x19 (Z_to_bv 64 w2) (Z_to_bv 64 off) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83350) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K0 w2 Rw Ew x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31 m1 E9 J.
    pose proof tl as TL. pose proof epi as EPI. sc.
    step.
    rewrite (cl_eqb0 w2) by (clear -Rw; lia). rewrite Ew.
    unfold cl_d9. destruct (cl_eq6 fr us); cbn [negb]; cbv iota.
    - eapply TL; [exact K0 | exact J].
    - subst x9. apply (EPI None). exact J.
  Qed.

  (* 0x832a4 (k = 1): the broadcast word at o + 16 (checked); set: st 0, else a2 = 1 and d9. *)
  Lemma d7a : k = 1 -> forall w2, -256 < w2 < 256 -> (w2 =? 0) = cl_eq6 fr us ->
    forall x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> aJc m1 vb ->
    evtF rsegs RNG (aQc (cl_d7 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) x19 (Z_to_bv 64 w2) (Z_to_bv 64 off) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x832a4) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K1 w2 Rw Ew x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31 m1 E9 J.
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
    chk_core (o + 16) RX (Z_to_bv 5 12) SH pre_sr add1.
    step. rewrite (cl_sx32 (if cp_bcast fr then 1 else 0)) by (clear -RB; lia).
    step. rewrite (rc_eqb_lit (if cp_bcast fr then 1 else 0) 0) by (clear -RB; lia).
    unfold cl_d7. destruct (cp_bcast fr); cbv iota.
    - change (1 =? 0) with false. cbv iota.
      step. rewrite K1. apply (STL 0). exact J.
    - change (0 =? 0) with true. cbv iota.
      step.
      replace (Z_to_bv 64 1) with (Z_to_bv 64 k) by (rewrite K1; reflexivity).
      eapply D9; [exact K0 | exact Rw | exact Ew | exact E9 | exact J].
  Qed.

  (* 0x83380 (k <> 0, 1): the broadcast word at o + 16 (checked); set: k = 1 fails and the epilogue with -1, else
     d9. *)
  Lemma d7b : k <> 0 -> k <> 1 -> forall w2, -256 < w2 < 256 -> (w2 =? 0) = cl_eq6 fr us ->
    forall x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> aJc m1 vb ->
    evtF rsegs RNG (aQc (cl_d7 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 x11 (Z_to_bv 64 k) x13 x14
               x15 x16 x17 (Z_to_bv 64 o) x19 (Z_to_bv 64 w2) (Z_to_bv 64 off) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83380) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K0 K1 w2 Rw Ew x1 x5 x6 x7 x9 x10 x11 x13 x14 x15 x16 x17 x19 x22 x28 x29 x30 x31 m1 E9 J.
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
      rewrite (proj2 (Z.eqb_neq k 1) K1). cbv iota.
      step. subst x9. apply (EPI None). exact J.
    - change (0 =? 0) with true. cbv iota.
      eapply D9; [exact K0 | exact Rw | exact Ew | exact E9 | exact J].
  Qed.

  (* 0x832ec (after reac_ctrl_checksum_verify gave 0; s6 holds the shadow address of o): the kind word at o
     (checked); k = 5: byte 22 at o + 26 and the half word at o + 28 (each checked), to st 1 or the epilogue with -1;
     else d7b. *)
  Lemma d5 : k <> 0 -> k <> 1 -> forall w2, -256 < w2 < 256 -> (w2 =? 0) = cl_eq6 fr us ->
    forall x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> aJc m1 vb ->
    evtF rsegs RNG (aQc (cl_d5 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) x19 (Z_to_bv 64 w2) (Z_to_bv 64 off) (Z_to_bv 64 (o / 8 + off))
               s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x832ec) fc None m1 (seg_rom rsegs)).
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
      pose proof (byte_range (cp_b fr 35)). pose proof (byte_range (cp_b fr 34)).
      step.
      chk_core (o + 28) RX28 (Z_to_bv 5 12) SH28 pre_sr add1.
      step. rewrite cl_zx16 by lia.
      step. step. step.
      rewrite (rc_eqb_lit (bv_unsigned (cp_b fr 35) + 256 * bv_unsigned (cp_b fr 34)) 256) by lia.
      destruct (Z.eqb_spec (bv_unsigned (cp_b fr 35) + 256 * bv_unsigned (cp_b fr 34)) 256); cbn [orb]; cbv iota.
      { apply (STL 1). exact J. }
      step. step.
      rewrite (rc_eqb_lit (bv_unsigned (cp_b fr 35) + 256 * bv_unsigned (cp_b fr 34)) 770) by lia.
      destruct (Z.eqb_spec (bv_unsigned (cp_b fr 35) + 256 * bv_unsigned (cp_b fr 34)) 770); cbv iota.
      { apply (STL 1). exact J. }
      step. subst x9. apply (EPI None). exact J.
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

  (* The 50 bytes at f are kept and stay addressable in a memory that the run reached writing only aWc.  CHANGED:
     the assert INf (In (f, f + 50) aDf) and the acl_out_fpw_d arguments are dropped. *)
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

  (* 0x83284 (after the second bcmp, a0 = w2): s6 = the shadow address of o, w2 to s4, the kind word at o
     (checked); k = 1: d7a; else reac_ctrl_checksum_verify(f): 0 goes to d5, else the epilogue with -1. *)
  Lemma d4 : k <> 0 -> forall w2, -256 < w2 < 256 -> (w2 =? 0) = cl_eq6 fr us ->
    forall x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x22 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> aJc m1 vb ->
    evtF rsegs RNG (aQc (cl_d4 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 (Z_to_bv 64 w2) x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) x20 (Z_to_bv 64 off) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83284) fc None m1 (seg_rom rsegs)).
  Proof.
    intros K0 w2 Rw Ew x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x22 x28 x29 x30 x31 m1 E9 J.
    destruct (HK K0) as (HN & EB & _).
    pose proof J as (_ & HBo & _ & _ & MU & _ & MI & ST & JA).
    pose proof JA as (AC & SW & _).
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
    pose proof reac_ctrl_checksum_verify_F_holds_on as HC. unfold reac_ctrl_checksum_verify_contract_F_on,
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
        - eapply rng_sub; [exact RSTK | clear; lia | clear; lia].
        - eapply rng_sub; [exact RIMG | unfold GOT_CELL_K; clear; lia | unfold GOT_CELL_K; clear; lia].
        - eapply rng_sub; [exact RIMG | unfold CELL_K; clear; lia | unfold CELL_K; clear; lia].
        - eapply rng_sub; [exact (RFB HN) | clear; lia | clear; lia].
        - eapply rng_sub; [exact (RFBS HN) | |];
            unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia. }
      intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & m2 & E & MU2 & WM2 & MI2 & ST2). subst ms'.
      rewrite ES in MU2, ST2.
      pose proof (JC m2 vb (S + -64 - 16) J ltac:(clear; lia) MU2 WM2 (MI2 MI) ST2) as J2.
      replace (ret_pc (Z_to_bv 64 0x832e8)) with (Z_to_bv 64 0x832e8)
        by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
      unfold cl_bsum.
      destruct (Z.eqb_spec (blocksum (skipn 18 fr)) 0) as [B0|B0]; cbn [negb andb]; cbv iota.
      + step. rewrite (cl_eqb0 0) by (clear; lia). change (0 =? 0) with true. cbn [negb]. cbv iota.
        eapply D5; [exact K0 | exact K1 | exact Rw | exact Ew | exact E9 | exact J2].
      + step. rewrite (cl_eqb0 (-1)) by (clear; lia). change (-1 =? 0) with false. cbn [negb]. cbv iota.
        subst x9. apply (EPI None). exact J2.
  Qed.

  (* The 6 bytes at u are kept and stay addressable in a memory that the run reached writing only aWc.  CHANGED:
     the assert INu (In (u, u + 6) aDf) and the acl_out_fpw_d arguments are dropped. *)
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

  (* 0x83264 (a0 = o + 4): bcmp(o + 4, u, 6) by the wrapper's asan contract: 0 (the source equals u) goes to the
     epilogue with -1, else bcmp(o + 10, u, 6) = w2 and d4. *)
  Lemma d3 : k <> 0 -> forall x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> aJc m1 vb -> aCL m1 ->
    evtF rsegs RNG (aQc (cl_d3 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 (Z_to_bv 64 (o + 4)) x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 u) (Z_to_bv 64 off) x22
               s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83264) fc None m1 (seg_rom rsegs)).
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
    pose proof bcmp_wrap_on.bcmp_wrap_holds_F_on as HB.
    unfold bcmp_wrap_c_on.bcmp_wrap_contract_F_on, BCMP_WRAP_K in HB.
    cbv zeta in HB.
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
      - apply (A.ShadowRwOn.shadow_rw_on_mono (reac_ctrl_classify_box_frame_post_call_shadow_R n u o));
          [intros a Ha; exact (conj HN (or_introl Ha)) | exact (SW _ HSR)].
      - exact CL1.
      - exact CL2.
      - exact CL3.
      - exact CL4.
      - exact CL5.
      - exact RBY.
      - exact RIMG.
      - eapply rng_sub; [exact RSTK | clear; lia | clear; lia].
      - eapply rng_sub; [exact ROB | clear; lia | clear; lia].
      - right. eapply rng_sub; [exact ROBS | |];
          unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
      - eapply rng_sub; [exact (RUB HN) | clear; lia | clear; lia].
      - right. eapply rng_sub; [exact (RUBS HN) | |];
          unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia. }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & E & MU2 & WM2
                & MI2 & ST2 & _).
    subst ms'. rewrite ES in MU2, ST2. unfold BCMP_WRAP_K in MU2.
    pose proof (JC m1 m2 vb (S + -64 - 4560) J ltac:(clear; lia) MU2 WM2 MI2 ST2) as J2.
    pose proof (CLC m1 m2 (S + -64 - 4560) CL ltac:(clear; lia) MU2) as CLm2.
    clear HS HU1 AU1 A4 MI ST AC SW CL1 CL2 CL3 CL4 CL5 MU2 WM2 MI2 ST2.
    replace (ret_pc (Z_to_bv 64 0x83270)) with (Z_to_bv 64 0x83270)
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
      - apply (A.ShadowRwOn.shadow_rw_on_mono (reac_ctrl_classify_box_frame_post_call_shadow_R n u o));
          [intros a Ha; exact (conj HN (or_intror Ha)) | exact (SW2 _ HSR)].
      - exact CL1.
      - exact CL2.
      - exact CL3.
      - exact CL4.
      - exact CL5.
      - exact RBY.
      - exact RIMG.
      - eapply rng_sub; [exact RSTK | clear; lia | clear; lia].
      - eapply rng_sub; [exact ROB | clear; lia | clear; lia].
      - right. eapply rng_sub; [exact ROBS | |];
          unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
      - eapply rng_sub; [exact (RUB HN) | clear; lia | clear; lia].
      - right. eapply rng_sub; [exact (RUBS HN) | |];
          unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia. }
    intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 & E
                & MU3 & WM3 & MI3 & ST3 & _).
    subst ms'. rewrite ES in MU3, ST3. unfold BCMP_WRAP_K in MU3.
    pose proof (JC m2 m3 vb (S + -64 - 4560) J2 ltac:(clear; lia) MU3 WM3 MI3 ST3) as J3.
    replace (ret_pc (Z_to_bv 64 0x83284)) with (Z_to_bv 64 0x83284)
      by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
    eapply D4; [exact K0 | exact Rw2 | exact Ew2 | exact E9 | exact J3].
  Qed.

  (* 0x83208: the OUI bytes 6, 7, 8 of the frame at o + 4, o + 5, o + 6 (each checked) against 00 40 ab: a mismatch
     goes to the epilogue with -1, else d3. *)
  Lemma d2 : k <> 0 -> forall x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 m1,
    x9 = Z_to_bv 64 (cl_r None) -> aJc m1 vb -> aCL m1 ->
    evtF rsegs RNG (aQc (cl_d2 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 x10 x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 u) (Z_to_bv 64 off) x22
               s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83208) fc None m1 (seg_rom rsegs)).
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

  (* 0x83200 (after reac_ctrl_parse, a0 = k): s1 = -1; k = 0 goes to the epilogue, else d2. *)
  Lemma d1 : forall x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 m1,
    aJc m1 vb -> aCL m1 ->
    evtF rsegs RNG (aQc (if k =? 0 then None else cl_d2 k fr us))
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 (Z_to_bv 64 k) x11 x12 x13 x14
               x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 u) (Z_to_bv 64 off) x22
               s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83200) fc None m1 (seg_rom rsegs)).
  Proof.
    intros x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 m1 J CL.
    pose proof epi as EPI. pose proof d2 as D2. sc.
    step. step.
    rewrite (rc_eqb_lit k 0) by (clear -Rk; lia).
    destruct (Z.eqb_spec k 0) as [K0|K0]; cbv iota.
    - apply (EPI None). exact J.
    - eapply D2; [exact K0 | reflexivity | exact J | exact CL].
  Qed.

End PostOn.

End PostOnM.

(* Stretch 1: 0x831b8 .. the jal at 0x831fc, stepped (pc 0x83578 = REAC_CTRL_PARSE, ra = 0x83200).  Fs.v's
   reac_ctrl_classify_box_frame_pre_call_F, statement and proof copied unchanged. *)
Theorem reac_ctrl_classify_box_frame_pre_call_F :
  forall (RNG : footprint)
         (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n u o v S : Z),
    8864 <= S < 2^64 -> HIGHMEM_BEG <= S - 8864 ->
    stk rsegs m (S - 8864) S -> mem_inv rsegs m -> asan_cells m ->
    rng RNG 0x10000 0x5ee000 -> rng RNG (S - 8864) 8864 ->
    evtF rsegs RNG
      (fun ms' => exists m1 : word -> option byte,
         ms' = MS (mkR (Z_to_bv 64 0x83200) (Z_to_bv 64 (S + -64)) gp tp t0 t1 t2 (Z_to_bv 64 v) s1
                       (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 o) (Z_to_bv 64 o) (Z_to_bv 64 v) a5 a6 a7
                       (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 u) (Z_to_bv 64 ASAN_K) s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x83578) fc None m1 (seg_rom rsegs) /\
         munch [(S + -64, S)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
         stk rsegs m1 (S - 8864) (S + -64) /\
         rw_cells rsegs m1 (S + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 u) (Z_to_bv 64 o)
               (Z_to_bv 64 v) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x831b8) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f n u o v S
    RS HHM ST MI AC RIMG RSTK.
  remember ASAN_K as off eqn:Hoff.
  (* pro (reac_ctrl_classify_box_frameF.v:1305-1322), without the continuation CAL. *)
  assert (HW : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
                 outside [(S + -64, S)] x).
  { intros x Hx. cbn [outside]. split; [|exact I].
    clear -Hx HHM. unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *.
    lia. }
  pose proof (rt_asan_rt m _ AC HW) as HRT. rewrite <- Hoff in HRT.
  pose proof (munch_refl [(S + -64, S)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  clear AC HW.
  (* pro's `sc.` is omitted: it only clears Section Post hypotheses, none of which is in scope here. *)
  step. carve_frame 64%nat ST. do 11 step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mp end.
  pose proof (asan_rt_munch rsegs m mp _ _ off _ _ HRT MU (fun x Hx => Hx)) as HRT1.
  pose proof (asan_rt_got_read rsegs mp _ _ off _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs mp _ _ off _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  do 5 step.
  clear RG RC HRT HRT1.
  (* cal's first step (reac_ctrl_classify_box_frameF.v:1211): the jal at 0x831fc. *)
  step.
  (* The cut state: what pro's `eapply CAL; eassumption` handed to cal. *)
  apply evtF_done. eexists.
  split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

(* Stretch 2, route (C): Fs.v's reac_ctrl_classify_box_frame_post_call_F with its premise `shadow_rw m1` narrowed to R
   at m1 and its post `shadow_rw m'` replaced by the transport from m1 (every other premise and conjunct unchanged). *)
Theorem reac_ctrl_classify_box_frame_post_call_F_on :
  forall (RNG : footprint) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m m1 : word -> option byte) (f n u o v S : Z) (fr us vb : list byte)
         (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    (* the Section's premises over the base memory m *)
    0 <= f < 2^64 -> 0 <= u < 2^64 -> 0 <= o < 2^64 -> 0 <= v < 2^64 -> 8864 <= S < 2^64 -> S mod 16 = 0 ->
    length fr = 50%nat -> length us = 6%nat ->
    (50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fr /\ (f + 50 <= S - 8864 \/ S <= f)) ->
    (50 <= n -> u + 6 <= 2^64 /\ bytes_at rsegs m u us /\ (u + 6 <= S - 8864 \/ S <= u)) ->
    o <> 0 -> o mod 4 = 0 -> o + 36 <= 2^64 -> (o + 36 <= S - 8864 \/ S <= o) ->
    (50 <= n -> o + 36 <= f \/ f + 50 <= o) -> (o + 36 <= u \/ u + 6 <= o) ->
    v <> 0 -> v mod 4 = 0 -> v + 4 <= 2^64 -> (v + 4 <= S - 8864 \/ S <= v) -> (v + 4 <= o \/ o + 36 <= v) ->
    (v + 4 <= f \/ f + 50 <= v) -> (v + 4 <= u \/ u + 6 <= v) ->
    HIGHMEM_BEG <= S - 8864 -> S <= APPMEM_END ->
    (50 <= n -> addressable m f 50 /\ addressable m u 6 /\ app_mem (u + 6) /\ app_mem (u + 7)) ->
    addressable m o 36 -> addressable m v 4 -> (v + 4 <= RT_LO \/ RT_HI <= v) ->
    (* the regions the stretch reads or writes *)
    rng_bytes RNG ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG (S - 8864) 8864 ->
    rng RNG o 36 ->
    rng RNG (shadow_addr o / 8 * 8) (shadow_addr (o + 36 - 1) / 8 * 8 + 8 - shadow_addr o / 8 * 8) ->
    rng RNG v 4 ->
    rng RNG (shadow_addr v / 8 * 8) (shadow_addr (v + 4 - 1) / 8 * 8 + 8 - shadow_addr v / 8 * 8) ->
    (50 <= n -> rng RNG f 50) ->
    (50 <= n -> rng RNG (shadow_addr f / 8 * 8) (shadow_addr (f + 50 - 1) / 8 * 8 + 8 - shadow_addr f / 8 * 8)) ->
    (50 <= n -> rng RNG u 6) ->
    (50 <= n -> rng RNG (shadow_addr u / 8 * 8) (shadow_addr (u + 6 - 1) / 8 * 8 + 8 - shadow_addr u / 8 * 8)) ->
    (* the cut state at 0x83200: aJc m1 vb /\ aCL m1 *)
    rw_cells rsegs m1 (S + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at rsegs m1 o (snd (ctrlparse n fr)) -> wr_at rsegs m1 o 36 -> rw_cells rsegs m1 v [CB 4 vb] ->
    munch [(o, o + 36); (v, v + 4); (S - 8864, S); (shadow_addr (S - 8864), shadow_addr S)] m m1 ->
    wmono rsegs m m1 -> mem_inv rsegs m1 -> stk rsegs m1 (S - 8864) (S + -64) ->
    asan_cells m1 -> A.ShadowRwOn.shadow_rw_on (reac_ctrl_classify_box_frame_post_call_shadow_R n u o) m1 ->
    addressable m1 (S - 8864) 8864 ->
    bytes_at rsegs m1 REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m1 REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m1 GOT_CF (le8 (wa CF)) -> bytes_at rsegs m1 (CF + 254) [Z_to_bv 8 1] ->
    bytes_at rsegs m1 (CF + 255) [Z_to_bv 8 1] ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (cl_r (classify n fr us)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(o, o + 36); (v, v + 4); (S - 8864, S); (shadow_addr (S - 8864), shadow_addr S)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - 8864) S /\
         rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))] /\
         rw_cells rsegs m' v [CB 4 (reac_ctrl_classify_box_frame_ev (classify n fr us) vb)] /\
         asan_cells m' /\ (forall P : Z -> Prop, A.ShadowRwOn.shadow_rw_on P m1 -> A.ShadowRwOn.shadow_rw_on P m') /\
         addressable m' (S - 8864) 8864)
      (MS (mkR x1 (Z_to_bv 64 (S + -64)) gp tp x5 x6 x7 (Z_to_bv 64 v) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 u) (Z_to_bv 64 ASAN_K) x22
               s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83200) fc None m1 (seg_rom rsegs)).
Proof.
  intros RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 f n u o v S fr us vb
    x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31
    Rf Ru Ro Rv RS S16 Lfr Lus HF HU Ho0 Ho4 Ho36 DOs DOf DOu Hv0 Hv4 Hv36 DVs DVo DVf DVu HHM HAE AFU AO AV HVR
    RBY RIMG RSTK ROB ROBS RVB RVBS RFB RFBS RUB RUBS
    FR HBo WRo HV MU WM MI ST AC SW AW CL1 CL2 CL3 CL4 CL5.
  pose proof (ctrlparse_kind_range n fr) as Rk.
  pose proof (ctrlparse_length n fr) as LB.
  pose proof (cl_hk n fr) as HK.
  pose proof (conj CL1 (conj CL2 (conj CL3 (conj CL4 CL5)))) as CL.
  pose proof (conj FR (conj HBo (conj WRo (conj HV (conj MU (conj WM (conj MI (conj ST
    (conj AC (conj (fun (P : Z -> Prop) (H : A.ShadowRwOn.shadow_rw_on P m1) => H) AW)))))))))) as J.
  eapply evtF_mono.
  - eapply PostOnM.d1 with (ra := ra) (gp := gp) (tp := tp) (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4)
      (s5 := s5) (s6 := s6) (s7 := s7) (s8 := s8) (s9 := s9) (s10 := s10) (s11 := s11) (F := F) (fc := fc) (m := m)
      (f := f) (n := n) (u := u) (o := o) (v := v) (S := S) (k := fst (ctrlparse n fr)) (off := ASAN_K)
      (fr := fr) (us := us) (vb := vb) (B := snd (ctrlparse n fr)) (RNG := RNG) (m1 := m1) (m0 := m1).
    all: first [exact J | exact CL | eassumption | reflexivity].
  - intros ms' H. rewrite classify_d1. exact H.
Qed.
