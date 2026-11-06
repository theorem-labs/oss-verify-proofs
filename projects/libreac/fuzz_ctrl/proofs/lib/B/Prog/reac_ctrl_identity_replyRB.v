(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/C_reac_ctrl_classify_box_frameLib.v, with its module names and numbers changed; 4975 of its 5172 lines of code are new or changed and 792 lines of the source are left out. *)
(* GENERATED FILE - do not edit.  GLUE/gen_reac_ctrl_identity_replyRB.py from the route-(C) run
   lib/B/Prog/reac_ctrl_identity_replyF_on.v (git blob 967305b245d9f403d5276d6c560cb7a09230829b)
   and GLUE/reac_ctrl_identity_replyRB.ins + GLUE/reac_ctrl_identity_replyRB.SC.ins
   (sha256 of their concatenation b425cb6f5de0ca99bc8ff7a94d6409ae86d49f2c0be328f274510e9596867d28).
   F_on's text up to `End Rep.` verbatim, then the insertions (the main insertions with the F_on generator's
   SW-site edits site (ii) :3012 / site (ii) :3014 applied), then `End Rep.` and `End Callees.`;
   F_on's tail (reac_ctrl_identity_reply_holds_F_on) is not copied.
   GLUE = analyses/libreac/fuzz_ctrl/glue-B/identity_reply. *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
(* GENERATED FILE - do not edit.  analyses/libreac/fuzz_ctrl/glue-B/identity_reply/gen_reac_ctrl_identity_replyF_on.py
   from the accepted lib/B/Prog/reac_ctrl_identity_replyF.v (git blob af7c0c619ef83864657423d92e8e0cdcab8d66af).
   Route (C) phase 2: the run with its Section premise `SW : shadow_rw m` narrowed to
   `shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) m`
   (lib/B/Prog/reac_ctrl_identity_reply_c_on.v), the callees taken in their `_on` forms (Section Callees), and the
   statement reac_ctrl_identity_reply_holds_F_on : reac_ctrl_identity_reply_contract_F_on.  The accepted file and its
   theorems are unchanged; the substitution table, each entry with its count, is the generator's SUBS. *)
(* The footprint twin of reac_ctrl_identity_reply.v (not in this delivery) (RECIPE.md step 1, route 2 (a working note, not in this delivery)): the same run as an
   ExecF.evtF under a footprint RNG (reac_ctrl_identity_reply_contract_F of reac_ctrl_identity_reply_c.v, which assumes fr apart from pa, pp and pn only when 50 <= len, where the plain contract always assumes it), by the
   script of lib/B/Prog/reac_ctrl_identity_reply.v (not in this delivery) over StepF's step. Every data access closes from one rng premise
   of that statement: the image (the GOT words, the runtime's cells), the window [S - K, S) and its shadow, the 50
   bytes at fr with their shadow, the bytes at pa, pp, pn with their shadow, the side stack's header and the class-1
   hint word, flag bytes, frames and frame shadow, and the thread cells of asan_tls_cells. The three callees are
   taken in their footprint form in the places where reac_ctrl_identity_reply.v's theorem takes their old contracts.
   reac_ctrl_identity_reply.v and its theorem are unchanged.

   reac_ctrl_identity_reply, image B (asan-ubsan, entry 0x848fc): the image-B twin of
   lib/A/Prog/reac_ctrl_identity_reply.v. Image B's frame code (+0x0 .. +0xec) is image A's with s5 and s6 exchanged
   (B: s5 = fr, s6 = pa); image B adds tests that branch to the trap instruction at +0x474 (0x84d70) before pointer
   arithmetic on fr and the OUT pointers. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcKind RcParse RcParseLib RcReply RcReplyLib RcAsan RcAsanLib RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  memcmp_c bcmp_wrap_c reac_ctrl_parse_c reac_ctrl_record_cksum_verify_c reac_ctrl_identity_reply_c
  asan_stack_malloc_c_on asan_stack_malloc_cF asan_stack_malloc_cF_on reac_ctrl_identity_reply_c_on.
(* Last: StepF's step / if_cases (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Local Open Scope Z_scope.

(* The callee forms this run takes are the hypotheses of Section Callees below (route (C)).  The accepted file's local
   copy of asan_stack_malloc_contract_F / asan_stack_malloc_1_contract_F, with its fs_shadow_area and IMG_HI, is not
   copied: those are the leaf lib/B/Prog/asan_stack_malloc_cF.v's (with ImgBounds' IMG_LO / IMG_HI), and the run takes
   asan_stack_malloc_1_contract_F_on from the leaf lib/B/Prog/asan_stack_malloc_cF_on.v by name. *)

(* ------------------------------------------------------------------------------------------------------------ *)
(* The shadow covers, carried through the proof as quantified facts (as lib/B/Prog/reac_ctrl_parseF.v does). Z.div
   is opaque to lia, and a GROUND rng premise whose bounds hold a division makes every later lia pay for that
   division's Euclidean equations, so the consequences of the statement's shadow premises are drawn once, each in a
   context with no other division, and used through shcov (the shadow byte of one checked byte), shcovo (the same
   at a shadow offset c that a loop carries in a register), shblk (the i-th shadow byte of an 8-aligned block),
   shkov (the aligned word cover a callee's _F contract names) and shspan (the byte-exact shadow span of a sub-range
   of the window). *)
Definition shcov (RG : ExecF.footprint) (p n : Z) : Prop :=
  forall x, p <= x < p + n -> ExecF.rng RG (x / 8 + ASAN_K) 1.
Definition shcovo (RG : ExecF.footprint) (c p n : Z) : Prop :=
  forall x, p <= x < p + n -> ExecF.rng RG (x / 8 + c) 1.
Definition shblk (RG : ExecF.footprint) (p k : Z) : Prop :=
  forall i, 0 <= i <= k -> ExecF.rng RG (p / 8 + ASAN_K + i) 1.
Definition shkov (RG : ExecF.footprint) (p n : Z) : Prop :=
  forall a b, p <= a -> a <= b -> b < p + n ->
    ExecF.rng RG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).
Definition shspan (RG : ExecF.footprint) (lo hi : Z) : Prop :=
  forall a b, lo <= a -> a <= b -> b <= hi -> ExecF.rng RG (shadow_addr a) (shadow_addr b - shadow_addr a).

Lemma shcov_sub : forall RG p n p' n', shcov RG p n -> p <= p' -> p' + n' <= p + n -> shcov RG p' n'.
Proof. intros RG p n p' n' H H1 H2 x Hx. apply H. lia. Qed.

Lemma shkov_sub : forall RG p n p' n', shkov RG p n -> p <= p' -> p' + n' <= p + n -> shkov RG p' n'.
Proof. intros RG p n p' n' H H1 H2 a b H3 H4 H5. apply H; lia. Qed.

Lemma rrF_floor8 : forall y, y / 8 * 8 <= y <= y / 8 * 8 + 7.
Proof. intros y. pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)). lia. Qed.

(* The aligned word cover of [p, p + n) gives the shadow byte of each of its bytes, *)
Lemma shkov_cov : forall RG p n, shkov RG p n -> shcov RG p n.
Proof.
  intros RG p n H x Hx. eapply ExecF.rng_sub; [exact (H x x ltac:(lia) ltac:(lia) ltac:(lia)) | |];
    pose proof (rrF_floor8 (x / 8 + ASAN_K)); lia.
Qed.

(* and the byte-exact shadow span of each of its sub-ranges. *)
Lemma shkov_exact : forall RG p n a b, shkov RG p n -> p <= a -> a <= b -> b < p + n ->
  ExecF.rng RG (shadow_addr a) (shadow_addr b - shadow_addr a + 1).
Proof.
  intros RG p n a b H H1 H2 H3. pose proof (H a b H1 H2 H3) as K. unfold shadow_addr.
  pose proof (Z.div_le_mono a b 8 ltac:(lia) H2).
  eapply ExecF.rng_sub; [exact K | |]; pose proof (rrF_floor8 (a / 8 + ASAN_K));
    pose proof (rrF_floor8 (b / 8 + ASAN_K)); lia.
Qed.

(* The statement's aligned word cover of fr's shadow, as shkov. *)
Lemma rrF_kov_stmt : forall RG p n, 1 <= n ->
  ExecF.rng RG (shadow_addr p / 8 * 8) (shadow_addr (p + (n - 1)) / 8 * 8 + 8 - shadow_addr p / 8 * 8) ->
  shkov RG p n.
Proof.
  intros RG p n Hn H a b H1 H2 H3. unfold shadow_addr in H.
  eapply ExecF.rng_sub; [exact H | |].
  - pose proof (Z.div_le_mono p a 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (p / 8 + ASAN_K) (a / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.div_le_mono b (p + (n - 1)) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (b / 8 + ASAN_K) ((p + (n - 1)) / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

(* The statement's byte-exact shadow span of pa / pp / pn, as shcov. *)
Lemma rrF_cov_exact : forall RG p n, 1 <= n ->
  ExecF.rng RG (shadow_addr p) (shadow_addr (p + (n - 1)) - shadow_addr p + 1) -> shcov RG p n.
Proof.
  intros RG p n Hn H x Hx. unfold shadow_addr in H.
  pose proof (Z.div_le_mono p x 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono x (p + (n - 1)) 8 ltac:(lia) ltac:(lia)).
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

(* The statement's byte-exact window shadow span, as shspan, shcov, and the aligned cover of [S - 288, S - 128)
   (the span of the real-stack frame [rA - 128, rA), S - 144 <= rA <= S - 128). *)
Lemma rrF_win_span : forall RG S, S mod 16 = 0 ->
  ExecF.rng RG (shadow_addr (S - 9072)) (shadow_addr S - shadow_addr (S - 9072)) -> shspan RG (S - 9072) S.
Proof.
  intros RG S H16 H a b H1 H2 H3. unfold shadow_addr in *.
  pose proof (Z.div_le_mono (S - 9072) a 8 ltac:(lia) H1). pose proof (Z.div_le_mono a b 8 ltac:(lia) H2).
  pose proof (Z.div_le_mono b S 8 ltac:(lia) H3).
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

Lemma rrF_win_cov : forall RG S, S mod 16 = 0 ->
  ExecF.rng RG (shadow_addr (S - 9072)) (shadow_addr S - shadow_addr (S - 9072)) -> shcov RG (S - 9072) 9072.
Proof.
  intros RG S H16 H x Hx. eapply ExecF.rng_sub; [exact H | |]; unfold shadow_addr; Z.div_mod_to_equations; lia.
Qed.

Lemma rrF_win_kov : forall RG S, S mod 16 = 0 ->
  ExecF.rng RG (shadow_addr (S - 9072)) (shadow_addr S - shadow_addr (S - 9072)) -> shkov RG (S - 288) 160.
Proof.
  intros RG S H16 H a b H1 H2 H3.
  eapply ExecF.rng_sub; [exact H | |]; unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
Qed.

Lemma rrF_div8 : forall z, (8 * z) / 8 = z.
Proof. intros z. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. Qed.

(* The class-1 frames' shadow comes as the BYTE-exact span [shadow_addr F0, shadow_addr F1) of fp_w. Both ends are
   the shadow byte of a 64-aligned address, so that span is a whole number of aligned shadow words. p0 and p1 below
   are F0 / 64 and F1 / 64. *)
Lemma rrF_span_cov : forall RG p0 p1,
  ExecF.rng RG (8 * p0 + ASAN_K) (8 * p1 + ASAN_K - (8 * p0 + ASAN_K)) -> shcov RG (64 * p0) (64 * p1 - 64 * p0).
Proof.
  intros RG p0 p1 H x Hx.
  assert (L1 : 8 * p0 <= x / 8).
  { pose proof (Z.div_le_mono (8 * (8 * p0)) x 8 ltac:(lia) ltac:(lia)) as D. rewrite rrF_div8 in D. lia. }
  assert (L2 : x / 8 <= 8 * p1 - 1).
  { pose proof (Z.div_le_mono x ((8 * p1 - 1) * 8 + 7) 8 ltac:(lia) ltac:(lia)) as D.
    rewrite Z.div_add_l in D by lia. rewrite (Z.div_small 7 8 ltac:(lia)) in D. lia. }
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

Lemma rrF_span_kov : forall RG p0 p1,
  ExecF.rng RG (8 * p0 + ASAN_K) (8 * p1 + ASAN_K - (8 * p0 + ASAN_K)) -> shkov RG (64 * p0) (64 * p1 - 64 * p0).
Proof.
  intros RG p0 p1 H a b H1 H2 H3.
  assert (KA : ASAN_K = 8 * 268431360) by reflexivity.
  assert (L1 : 8 * p0 <= a / 8).
  { pose proof (Z.div_le_mono (8 * (8 * p0)) a 8 ltac:(lia) ltac:(lia)) as D. rewrite rrF_div8 in D. lia. }
  assert (L2 : b / 8 <= 8 * p1 - 1).
  { pose proof (Z.div_le_mono b ((8 * p1 - 1) * 8 + 7) 8 ltac:(lia) ltac:(lia)) as D.
    rewrite Z.div_add_l in D by lia. rewrite (Z.div_small 7 8 ltac:(lia)) in D. lia. }
  assert (M1 : p0 + 268431360 <= (a / 8 + ASAN_K) / 8).
  { pose proof (Z.div_le_mono (8 * (p0 + 268431360)) (a / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)) as D.
    rewrite rrF_div8 in D. lia. }
  assert (M2 : (b / 8 + ASAN_K) / 8 <= p1 + 268431360 - 1).
  { pose proof (Z.div_le_mono (b / 8 + ASAN_K) ((p1 + 268431360 - 1) * 8 + 7) 8 ltac:(lia) ltac:(lia)) as D.
    rewrite Z.div_add_l in D by lia. rewrite (Z.div_small 7 8 ltac:(lia)) in D. lia. }
  eapply ExecF.rng_sub; [exact H | lia | lia].
Qed.

Lemma rrF_fs_frame1 : forall FS j, fs_frame FS 1 j = FS + 1085440 + j * 128.
Proof.
  intros FS j. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
  change (2 ^ 20) with 1048576. change (2 ^ 1) with 2. lia.
Qed.

Lemma rrF_fs_flag1 : forall FS i, fs_flag FS 1 i = FS + 20480 + i.
Proof. intros FS i. unfold fs_flag. cbn [Z.of_nat Pos.of_succ_nat]. lia. Qed.

(* The narrow __asan_stack_malloc_1 form's premises on the five runtime pointer cells and the two thread-pointer
   cells, from one rng fact per cell of fp_tls (lib/B/Prog/reac_ctrl_parseF.v's rcpF_tls_rng). *)
Lemma rrF_tls_rng : forall RG TP DT TS C T DB k,
  Forall (fun iv => rng RG (fst iv) (snd iv - fst iv)) (fp_tls TP DT TS C T DB k) ->
  rng RG (bv_unsigned DT + 8) 8 /\ rng RG (bv_unsigned TS + 8 * k) 8 /\ rng RG (bv_unsigned C + 152) 8 /\
  rng RG (bv_unsigned T + 48) 16 /\ rng RG (bv_unsigned DB + 24) 8 /\ rng RG (TP - 88) 8 /\ rng RG (TP - 8) 24.
Proof.
  intros RG TP DT TS C T DB k H. unfold fp_tls in H.
  apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [_ H].
  apply Forall_cons_iff in H as [R3 H]. apply Forall_cons_iff in H as [R4 H].
  apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [_ H].
  apply Forall_cons_iff in H as [R7 H]. apply Forall_cons_iff in H as [R8 H].
  apply Forall_cons_iff in H as [R9 H]. apply Forall_cons_iff in H as [R10 H].
  do 5 (apply Forall_cons_iff in H as [_ H]).
  apply Forall_cons_iff in H as [R16 _].
  cbn [fst snd] in R3, R4, R7, R8, R9, R10, R16.
  split; [eapply rng_sub; [exact R4 | lia | lia]|].
  split; [eapply rng_sub; [exact R8 | lia | lia]|].
  split; [eapply rng_sub; [exact R9 | lia | lia]|].
  split; [eapply rng_sub; [exact R10 | lia | lia]|].
  split; [eapply rng_sub; [exact R16 | lia | lia]|].
  split; [eapply rng_sub; [exact R7 | lia | lia]|].
  eapply rng_sub; [exact R3 | lia | lia].
Qed.

(* The narrow form's premise on the shadow of the class-1 frame area, from the frames' byte-exact shadow span in
   fp_w [1%nat] FS: the frames span 2^20 bytes, so their shadow is fs_shadow_area 1 bytes. *)
Lemma rrF_frame_sh : forall RG FS,
  Forall (fun iv => rng RG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
  rng RG (shadow_addr (fs_frame FS 1 0)) (fs_shadow_area 1).
Proof.
  intros RG FS H. unfold fp_w, fp_w1 in H. cbn [flat_map app] in H.
  apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [_ H].
  apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [H _].
  cbn [fst snd] in H.
  replace (fs_shadow_area 1) with (shadow_addr (fs_frame FS 1 (fs_M 1)) - shadow_addr (fs_frame FS 1 0));
    [exact H|].
  rewrite (rrF_fs_frame1 FS (fs_M 1)), (rrF_fs_frame1 FS 0). change (fs_M 1) with 8192.
  change (fs_shadow_area 1) with 131072. unfold shadow_addr.
  replace (FS + 1085440 + 0 * 128) with (FS + 1085440) by lia.
  replace (FS + 1085440 + 8192 * 128) with (FS + 1085440 + 131072 * 8) by lia.
  rewrite Z.div_add by lia. lia.
Qed.

(* The narrow form's premise on the class-1 frame area, from the frames' span in fp_w [1%nat] FS. *)
Lemma rrF_frame_area : forall RG FS,
  Forall (fun iv => rng RG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS) ->
  rng RG (fs_frame FS 1 0) (2 ^ 20).
Proof.
  intros RG FS H. unfold fp_w, fp_w1 in H. cbn [flat_map app] in H.
  apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [_ H].
  apply Forall_cons_iff in H as [H _].
  cbn [fst snd] in H.
  replace (2 ^ 20) with (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0); [exact H|].
  rewrite (rrF_fs_frame1 FS (fs_M 1)), (rrF_fs_frame1 FS 0). change (fs_M 1) with 8192. lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* A shadow access: its address holds a division, which StepF's [alia] does not reason about, so it goes through
   StepF's acc_hint hook and closes from one of the quantified covers above (lib/B/Prog/reac_ctrl_parseF.v's
   rcpF_rng1 / acc_hintF, with the shcovo case of the block-sum loop). *)
Ltac rrF_has_div E := lazymatch E with context [Z.div _ _] => idtac end.

Ltac rrF_rng1 :=
  lazymatch goal with
  | |- ExecF.rng ?RG ?E 1 =>
      first
        [ (* the i-th shadow byte of the 8-aligned block at p *)
          match goal with H : shblk RG _ _ |- _ => apply H; lia end
        | (* the shadow byte of X, a byte of a shcov range *)
          lazymatch E with ?X / 8 + ASAN_K =>
            match goal with H : shcov RG _ _ |- _ => apply (H X); lia end end
        | (* the shadow byte of X at the offset c of a shcovo range *)
          lazymatch E with ?X / 8 + ?c =>
            match goal with H : shcovo RG c _ _ |- _ => apply (H X); lia end end
        | (* the same, with the address written another way *)
          match goal with H : shblk RG ?p _ |- _ =>
            replace E with (p / 8 + ASAN_K + (E - (p / 8 + ASAN_K))) by lia;
            apply H; unfold ASAN_K in *; lia end
        | lazymatch E with ?X / 8 + ?c =>
            replace E with (X / 8 + ASAN_K) by (unfold ASAN_K in *; lia);
            match goal with H : shcov RG _ _ |- _ => apply (H X); lia end end
        | (* the offset register added first *)
          lazymatch E with ?c + ?X / 8 =>
            replace E with (X / 8 + c) by lia;
            first [ match goal with H : shcovo RG c _ _ |- _ => apply (H X); lia end
                  | match goal with H : shcov RG _ _ |- _ => apply (H X); lia end ] end ]
  end.

(* The hook also puts two access shapes into the one StepF's literal branch matches: an address written [wa E] (a
   pointer the run loaded from a GOT word) becomes [Z_to_bv 64 E], and a closed address written with named
   constants (GOT_UAR, CELL_K, ...) becomes its literal value. *)
Ltac acc_hintF :=
  lazymatch goal with
  | |- acc_in ?RG (wa ?E, ?nn) => change (acc_in RG (Z_to_bv 64 E, nn)); solve_acc1
  | |- acc_in ?RG (Z_to_bv 64 ?E, ?nn) =>
      tryif rrF_has_div E then
        (let nz := eval cbv in (Z.of_nat nn) in
         refine (rng_acc_litZ' RG E nz E nn nz _ (@eq_refl Z nz) (@eq_refl bool true)
                   (conj (Z.le_refl E) (Z.le_refl (E + nz))));
         rrF_rng1)
      else
        (tryif is_closed_lits E then fail else
           (let E' := eval vm_compute in E in
            is_Zlit E'; change (acc_in RG (Z_to_bv 64 E', nn)); solve_acc1))
  end.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= acc_hintF.

(* The store hook of this file: Tac.v's mem_after_store_opt (the hook reac_ctrl_identity_reply.v runs under) on evtF
   goals (lib/B/Prog/reac_ctrl_parseF.v's rcpF_store_opt). It folds Z_to_le_bytes of a literal into le8 / le4 / le2 /
   le1 as Tac's fix_lit_store does, and it does not run StepF's norm_lit_store_bytes, whose
   le1 (Z_to_bv 64 z) -> [Z_to_bv 8 z] folding would leave nothing for the script's own `rewrite rr_le1_0`. *)
Ltac rrF_fix_lit_store :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | _ => idtac
  end.

Ltac rrF_store_opt :=
  try rrF_fix_lit_store;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= rrF_store_opt.

(* The block-sum loop (+0x268 .. +0x2a0): 32 turns, each with the test a0 <> 0 and the shadow check of its byte.
   Image B: a0 = a3 = fr + 18 + i, a1 = the sum, a2 = the count, a4 / a5 the check's scratch; s5 = fr, s7 = fr + 18,
   s8 = s, s11 = the shadow offset. *)
Section BlkLoop.
  Variables (ra sp1 gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s6 s9 s10 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (fr off : Z) (g : list byte) (W : list ivl)
    (Q : machine_state -> Prop) (RNG : ExecF.footprint).
  Hypothesis Hfr : 0 < fr.
  Hypothesis Hfr50 : fr + 50 <= 2^64.
  Hypothesis Hl : length (ir_blk g) = 32%nat.
  Hypothesis HB : bytes_at rsegs mm (fr + 18) (ir_blk g).
  Hypothesis HSR : asan_shadow_rd rsegs mm off (fr + 18) 32 W.
  Hypothesis HAD : asan_addressable rsegs mm off (fr + 18) 32.
  (* The footprint of the loop: the 32 block bytes and their shadow bytes (at the offset s11 = off). *)
  Hypothesis RBK : rng RNG (fr + 18) 32.
  Hypothesis SCB : shcovo RNG off (fr + 18) 32.

  Abbreviation BK pc a0 a1 a2 a3 a4 a5 :=
    (MS (mkR ra sp1 gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 fr) s6 (Z_to_bv 64 (fr + 18)) (Z_to_bv 64 (ir_s g)) s9 s10 (Z_to_bv 64 off)
             t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Hypothesis EXIT : forall a0 a2 a3 a4 a5,
    evtF rsegs RNG Q (BK 0x84ba0 a0 (Z_to_bv 64 (psum (ir_blk g) 32)) a2 a3 a4 a5).

  Lemma rloopB : forall k i a4 a5, (i + k = 32)%nat -> (0 < k)%nat ->
    evtF rsegs RNG Q (BK 0x84b64 (Z_to_bv 64 (fr + 18 + Z.of_nat i)) (Z_to_bv 64 (psum (ir_blk g) i))
                    (Z_to_bv 64 (32 - Z.of_nat i)) (Z_to_bv 64 (fr + 18 + Z.of_nat i)) a4 a5).
  Proof using Hfr Hfr50 Hl HB HSR HAD RBK SCB EXIT.
    induction k as [|k IH]; intros i a4 a5 Hik Hk; [lia|].
    pose proof (psum_range (ir_blk g) i) as PR.
    assert (BODY : forall b4 b5,
      evtF rsegs RNG Q (BK 0x84b78 (Z_to_bv 64 (fr + 18 + Z.of_nat i)) (Z_to_bv 64 (psum (ir_blk g) i))
                      (Z_to_bv 64 (32 - Z.of_nat i)) (Z_to_bv 64 (fr + 18 + Z.of_nat i)) b4 b5)).
    { intros b4 b5.
      pose proof (rd_byte rsegs mm (fr + 18) (ir_blk g) i HB ltac:(lia)) as RD.
      step. step. step. step.
      rewrite psum_S_zxb.
      step. step.
      rewrite (rc_eqb64 (32 - Z.of_nat i + -1) 0) by lia.
      destruct k as [|k].
      - replace (32 - Z.of_nat i + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
        cbn [negb]. cbv iota.
        step.
        replace i with 31%nat in * by lia.
        apply EXIT.
      - replace (32 - Z.of_nat i + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        cbn [negb]. cbv iota.
        replace (32 - Z.of_nat i + -1) with (32 - Z.of_nat (S i)) by lia.
        replace (fr + 18 + Z.of_nat i + 1) with (fr + 18 + Z.of_nat (S i)) by lia.
        apply (IH (S i)); lia. }
    destruct (asan_shadow_read rsegs mm off (fr + 18) 32 W (Z.of_nat i) HSR ltac:(lia)) as (k0 & RK & BK0).
    pose proof (HAD (Z.of_nat i) k0 ltac:(lia) BK0) as OK.
    pose proof (rc_byte_signed k0) as KR.
    clear BK0.
    (* +0x268: the test a0 = fr + 18 + i <> 0; the trap branch is not taken *)
    step.
    rewrite (rc_beq0_false (fr + 18 + Z.of_nat i)) by lia. cbv iota.
    step.
    rewrite (unsigned_lit (fr + 18 + Z.of_nat i)) by lia. rewrite rc_shr3.
    step.
    step.
    clear RK.
    step.
    unfold sxb. rewrite (rc_eqb0_signed (bv_signed k0)) by lia.
    destruct (Z.eqb_spec (bv_signed k0) 0) as [K0|K0]; cbn [negb].
    - apply BODY.
    - step.
      rewrite (unsigned_lit (fr + 18 + Z.of_nat i)) by lia. rewrite rc_land7.
      step.
      rewrite (rc_lts_signed ((fr + 18 + Z.of_nat i) mod 8) (bv_signed k0))
        by (pose proof (Z.mod_pos_bound (fr + 18 + Z.of_nat i) 8 ltac:(lia)); lia).
      replace ((fr + 18 + Z.of_nat i) mod 8 <? bv_signed k0) with true
        by (symmetry; apply Z.ltb_lt; destruct OK; lia).
      apply BODY.
  Qed.

  (* The loop from its first turn (i = 0, 32 turns). *)
  Lemma rloopB0 : forall a4 a5,
    evtF rsegs RNG Q (BK 0x84b64 (Z_to_bv 64 (fr + 18)) (Z_to_bv 64 0) (Z_to_bv 64 32) (Z_to_bv 64 (fr + 18)) a4 a5).
  Proof using Hfr Hfr50 Hl HB HSR HAD RBK SCB EXIT.
    intros a4 a5. pose proof (rloopB 32 0 a4 a5 eq_refl ltac:(lia)) as H.
    cbn [Z.of_nat psum] in H. rewrite ?Z.add_0_r, ?Z.sub_0_r in H. exact H.
  Qed.
End BlkLoop.

(* The pointer-overflow tests compare against 2^64 - c (the literal -c): `li a0,-c; bltu a0,x` with x <= 2^64 - c is
   not taken. *)
Lemma rr_ltu_negl : forall x y, 0 <= x -> -2^64 < y < 0 -> x <= 2^64 + y ->
  bv_ltu (Z_to_bv 64 y) (Z_to_bv 64 x) = false.
Proof.
  intros x y Hx Hy Hxy. unfold bv_ltu. rewrite (unsigned_lit x) by lia. rewrite unsigned_lit_wrap.
  apply Z.ltb_ge. change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* Route (C): the three callee forms the narrowed run takes, as the hypotheses of ONE Section that holds the rest of the
   file, so reac_ctrl_identity_reply_holds_F_on at its end takes them in this order:
     asan_stack_malloc_1_contract_F_on            lib/B/Prog/asan_stack_malloc_cF_on.v (a Theorem Labs lane, 6a82e56a6ee);
     reac_ctrl_parse_contract_x_F_on              lib/B/Prog/reac_ctrl_parse_c.v (a Theorem Labs lane);
     reac_ctrl_record_cksum_verify_contract_F_on  lib/B/Prog/reac_ctrl_record_cksum_verify_c.v (a Theorem Labs lane,
                                                  5c355e74408: the accepted contract without its shadow premise).
   The CKV feed was found here: the accepted run passes `SWc : shadow_rw mc` (replyF:4746, from rJB :2375) to RecLoop's
   `SW : shadow_rw mm` (:475), which rloopR gives to reac_ctrl_record_cksum_verify_contract_F at :514 (its premise
   `(1 <= bv_unsigned a1 -> shadow_rw m)`, reac_ctrl_record_cksum_verify_c.v:55); under the narrowed parse post SWc is
   only a shadow_rw_on fact, so the CKV contract narrows with parse's.  CKV's own proof does not use that premise past
   reac_ctrl_record_cksum_verify_F.v:132, so its `_on` form drops it and RecLoop passes no shadow fact. *)
Section Callees.
  Hypothesis MALLOC : asan_stack_malloc_1_contract_F_on.
  Hypothesis PARSE : reac_ctrl_parse_contract_x_F_on.
  Hypothesis CKV : reac_ctrl_record_cksum_verify_contract_F_on.

(* The record sum (+0x2ac .. +0x2c0). Image A computes it in an inlined loop (A's RecLoop); image B calls
   reac_ctrl_record_cksum_verify(fr + 34, s - 8) (0x83cfc), whose own contract covers its loop and shadow checks.
   The segment: the test fr + 18 <= 2^64 - 17 (bltu, not taken), a0 = fr + 34, a1 = s - 8, the call at SP (the
   caller's sp) and the return to +0x2c0 with a0 = 0 (record sum 0 mod 128) or -1. *)
Section RecLoop.
  Variables (gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (fr s SP lo : Z) (g : list byte)
    (Q : machine_state -> Prop) (RNG : ExecF.footprint).
  Hypothesis Hfr : 0 < fr.
  Hypothesis Hfr50 : fr + 50 <= 2^64.
  Hypothesis Hs : 14 <= s <= 23.
  Hypothesis Hl : length (ir_rec g) = Z.to_nat (s - 8).
  Hypothesis HB : bytes_at rsegs mm (fr + 34) (ir_rec g).
  Hypothesis HAD : addressable mm (fr + 34) (s - 8).
  Hypothesis HSP : 0 <= SP < 2^64.
  Hypothesis HST : stk rsegs mm lo SP.
  Hypothesis HLO : lo + 16 <= SP.
  Hypothesis HFD : fr + 34 + (s - 8) <= SP - 16 \/ SP <= fr + 34.
  Hypothesis AC : asan_cells mm.
  Hypothesis HWO : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
    outside [(SP - 16, SP)] x.
  (* The footprint of the call: the image (GOT_CELL_K, CELL_K), the callee's 16-byte frame below SP, the s - 8
     record bytes at fr + 34 and the byte-exact shadow span of each sub-range of them. *)
  Hypothesis RIM : rng RNG 0x10000 0x5ee000.
  Hypothesis RSP : rng RNG (SP - 16) 16.
  Hypothesis RRC : rng RNG (fr + 34) (s - 8).
  Hypothesis SRC : forall a b, fr + 34 <= a -> a <= b -> b < fr + 34 + (s - 8) ->
    rng RNG (shadow_addr a) (shadow_addr b - shadow_addr a + 1).

  Abbreviation RK ra pc a0 a1 :=
    (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 (Z_to_bv 64 fr) s6 (Z_to_bv 64 (fr + 18)) (Z_to_bv 64 s) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  Hypothesis EXIT : forall (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : word -> option byte),
    munch [(SP - 16, SP)] mm m' -> wmono rsegs mm m' -> (mem_inv rsegs mm -> mem_inv rsegs m') ->
    stk rsegs m' lo SP ->
    evtF rsegs RNG Q
      (MS (mkR (Z_to_bv 64 0x84bbc) (Z_to_bv 64 SP) gp tp t0' t1 t2 s0 s1
               (Z_to_bv 64 (if recsum (ir_rec g) =? 0 then 0 else -1)) a1' a2' a3' a4' a5' a6' a7'
               s2 s3 s4 (Z_to_bv 64 fr) s6 (Z_to_bv 64 (fr + 18)) (Z_to_bv 64 s) s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x84bbc) fc None m' (seg_rom rsegs)).

  Lemma rloopR : forall ra a0 a1, evtF rsegs RNG Q (RK ra 0x84ba8 a0 a1).
  Proof using CKV Hfr Hfr50 Hs Hl HB HAD HSP HST HLO HFD AC HWO RIM RSP RRC SRC EXIT.
    intros ra a0 a1.
    (* +0x2ac: fr + 18 > 2^64 - 17 traps *)
    step. step. rewrite (rr_ltu_negl (fr + 18) (-17)) by lia. cbv iota.
    step. step. step.
    eapply evtF_cut.
    { eapply CKV with (lo := lo) (bs := ir_rec g); unfold REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME;
        rewrite ?(unsigned_lit SP), ?(unsigned_lit (fr + 34)), ?(unsigned_lit (s + -8)) by lia.
      - rewrite Hl. f_equal; lia.
      - right. split; [lia|]. split; [lia|]. split; [exact HB | lia].
      - exact HST.
      - exact HLO.
      - intros _. exact AC.
      - intros _. replace (s + -8) with (s - 8) by lia. exact HAD.
      - intros _. exact HWO.
      - (* the callee's frame *) exact RSP.
      - (* GOT_CELL_K *) eapply rng_sub; [exact RIM | unfold GOT_CELL_K; lia | unfold GOT_CELL_K; lia].
      - (* CELL_K *) eapply rng_sub; [exact RIM | unfold CELL_K; lia | unfold CELL_K; lia].
      - (* the record bytes *) intros _. replace (s + -8) with (s - 8) by lia. exact RRC.
      - (* their shadow span *) intros _. apply SRC; lia. }
    intros ms' (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m' & E & MU & WM & MI & ST). subst ms'.
    unfold REAC_CTRL_RECORD_CKSUM_VERIFY_FRAME in MU. rewrite (unsigned_lit SP) in MU, ST by lia.
    replace (ret_pc (Z_to_bv 64 0x84bbc)) with (Z_to_bv 64 0x84bbc)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    exact (EXIT t0' a1' a2' a3' a4' a5' a6' a7' m' MU WM MI ST).
  Qed.
End RecLoop.

(* ===================== Reply (asan-ubsan) main theorem ===================== *)
(* Geometry and shadow-check helpers, adapted from reac_ctrl_classify_box_frame.v. *)

Lemma rr_app_in : forall m p n i, addressable m p n -> 0 <= i < n -> app_mem (p + i).
Proof. intros m p n i (_ & _ & _ & HA) Hi. exact (proj1 (HA i Hi)). Qed.

Lemma rr_app_not_shadow : forall x, app_mem x -> in_shadow x -> False.
Proof. unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END. intros; lia. Qed.

Lemma rr_addr_sub : forall m p n p' n', addressable m p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n ->
  addressable m p' n'.
Proof.
  intros m p n p' n' (H0 & Hn & He & HA) H1 H2 H3. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply HA. lia.
Qed.

Lemma rr_addr_join : forall m p n n', addressable m p n -> addressable m (p + n) n' -> 0 <= n' ->
  addressable m p (n + n').
Proof.
  intros m p n n' (H0 & Hn & He & HA) (H0' & Hn' & He' & HA') Hn''.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z_lt_le_dec i n) as [L|L]; [apply HA; lia|].
  replace (p + i) with (p + n + (i - n)) by lia. apply HA'. lia.
Qed.

Lemma rr_addr_munch : forall W m m' p n, addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) Hm HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (rt_app_shadow (p + i) Hap) as Hs. pose proof (rt_shadow_bound _ Hs) as Hbd.
  unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. apply HW, Hi.
Qed.

Lemma rr_rw : forall W m m' A cs, rw_cells rsegs m A cs -> munch W m m' -> wmono rsegs m m' ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells rsegs m' A cs.
Proof.
  intros W m m' A cs [[Hwf Hb] Hw] Hm Hwm Ho. split; [split; [exact Hwf|]|].
  - eapply fl_bytes; [exact Hb | exact Hm |]. rewrite cells_bytes_length by exact Hwf. exact Ho.
  - eapply wr_at_transport; eassumption.
Qed.

Lemma rr_shadow : forall mc p n j w X, addressable mc p n -> 0 <= j -> 1 <= w -> j + w <= n ->
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

Lemma rr_sh_lt : forall x L, L mod 8 = 0 -> x < L -> shadow_addr x < shadow_addr L.
Proof. unfold shadow_addr. intros x L HL Hx. Z.div_mod_to_equations. lia. Qed.

Lemma rr_sh_ge : forall x L, L <= x -> shadow_addr L <= shadow_addr x.
Proof. unfold shadow_addr. intros x L H. pose proof (Z.div_le_mono L x 8 ltac:(lia) H). lia. Qed.

Lemma rr_out_app_inv : forall A B x, outside (A ++ B) x -> outside A x /\ outside B x.
Proof.
  induction A as [|[lo hi] A IH]; intros B x H; cbn [app outside] in *; [split; [exact I | exact H]|].
  destruct H as [H1 H2]. destruct (IH B x H2) as [H3 H4]. split; [split; [exact H1 | exact H3] | exact H4].
Qed.

Lemma rr_sh_out : forall x a b, app_mem x -> 0 <= a -> b <= APPMEM_END -> ~ (shadow_addr a <= x < shadow_addr b).
Proof.
  intros x a b Hx Ha Hb. unfold shadow_addr.
  pose proof (Z.div_pos a 8 Ha ltac:(lia)) as H1.
  pose proof (Z.div_le_mono b APPMEM_END 8 ltac:(lia) Hb) as H2.
  replace (APPMEM_END / 8) with 0x100000000000 in H2 by reflexivity.
  unfold app_mem, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

Lemma rr_win_sh : forall x lo hi, lo mod 8 = 0 -> ~ (lo <= x < hi) ->
  ~ (shadow_addr lo <= shadow_addr x < shadow_addr hi).
Proof.
  intros x lo hi Hm Hx [H1 H2]. destruct (Z_lt_le_dec x lo) as [L|L].
  - pose proof (rr_sh_lt x lo Hm L). lia.
  - pose proof (rr_sh_ge x hi ltac:(lia)). lia.
Qed.

Lemma rr_frame_mod8 : forall FS j, FS mod 4096 = 0 -> fs_frame FS 1 j mod 8 = 0.
Proof.
  intros FS j H. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
  change (2 ^ 20) with 1048576. change (2 ^ 1) with 2. Z.div_mod_to_equations. lia.
Qed.

Lemma rr_S_mod8 : forall S j, S mod 16 = 0 -> j mod 8 = 0 -> (S - j) mod 8 = 0.
Proof. intros S j H1 H2. Z.div_mod_to_equations. lia. Qed.

Lemma rr_mod_al : forall x j w, x mod 4 = 0 -> 0 <= j -> j mod 4 + w <= 4 -> (x + j) mod 8 + w <= 8.
Proof. intros x j w H Hj Hw. Z.div_mod_to_equations. lia. Qed.

Lemma rr_mod_al0 : forall x, x mod 4 = 0 -> x mod 8 + 4 <= 8.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

Lemma rr_mod2_al : forall x, x mod 2 = 0 -> x mod 8 + 2 <= 8.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

Lemma rr_bytes_rd : forall mc A bs x, bytes_at rsegs mc A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs mc (wa x) = Some b.
Proof.
  intros mc A bs x (_ & _ & H) Hx.
  destruct (nth_error bs (Z.to_nat (x - A))) as [b|] eqn:E.
  - exists b. rewrite <- E, <- H by lia. f_equal. f_equal. lia.
  - apply nth_error_None in E. lia.
Qed.

(* Frame lemmas the image-B RcAsanFPLib does not carry (present in the image-A one); copied verbatim, as
   lib/B/Prog/reac_ctrl_classify_box_frame.v does. They are generic in fp / fp_dj / the thread cells. *)
Lemma fl_out_app : forall A B x, outside A x -> outside B x -> outside (A ++ B) x.
Proof.
  induction A as [|[lo hi] A IH]; intros B x HA HB; cbn [app outside] in *; [exact HB|].
  destruct HA as [H1 H2]. split; [exact H1 | exact (IH B x H2 HB)].
Qed.

Lemma fl_dj_out : forall W L a b x, fp_dj W L -> In (a, b) L -> a <= x < b -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros L a b x H Hin Hx; cbn [outside]; [exact I|].
  unfold fp_dj in H. apply Forall_cons_iff in H as [H1 H2]. split.
  - rewrite Forall_forall in H1. pose proof (H1 _ Hin) as D. unfold ly_dj in D. cbn [fst snd] in D. lia.
  - exact (IH L a b x H2 Hin Hx).
Qed.

Lemma fl_dj_out_r : forall L X a b x, fp_dj L X -> In (a, b) L -> a <= x < b -> outside X x.
Proof.
  intros L X a b x H Hin Hx. unfold fp_dj in H. rewrite Forall_forall in H. pose proof (H _ Hin) as H1.
  cbn [fst snd] in H1. clear H Hin. induction X as [|[lo hi] X IH]; cbn [outside]; [exact I|].
  apply Forall_cons_iff in H1 as [D H1]. unfold ly_dj in D. cbn [fst snd] in D. split; [lia | exact (IH H1)].
Qed.

Ltac fl_col :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; rewrite ?length_app, ?length_le8, ?length_le4 in Hx; cbn [length] in Hx;
  match goal with O : forall y, _ <= y < _ -> outside _ y |- _ => apply O; lia end.

Lemma fl_tls_same : forall m m' W' TP DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k,
  asan_tls_cells m TP DT0 TS0 C0 T0 DB0 k0 -> asan_tls_cells m' TP DT TS C T DB k -> munch W' m m' ->
  Forall (fun d => forall x, fst d <= x < snd d -> outside W' x) (fp_tls TP DT0 TS0 C0 T0 DB0 k0) ->
  DT0 = DT /\ TS0 = TS /\ C0 = C /\ T0 = T /\ DB0 = DB /\ k0 = k.
Proof.
  intros m m' W' TP DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT Hm Hc.
  cbn [fp_tls] in Hc.
  repeat (let O := fresh "O" in apply Forall_cons_iff in Hc; destruct Hc as [O Hc]; cbn [fst snd] in O).
  destruct HT0 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17
    & A18 & A19).
  destruct HT as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17
    & B18 & B19).
  assert (EDT : DT0 = DT) by (apply (fl_le8_eq W' m m' (TP - 8) DT0 DT A3 B3 Hm); fl_col).
  assert (Ek : k0 = k) by (apply (fl_le4_eq W' m m' TSD_KEY k0 k A6 B6 A7 B7 Hm); fl_col).
  assert (ETS : TS0 = TS) by (apply (fl_le8_eq W' m m' (TP - 88) TS0 TS A8 B8 Hm); fl_col).
  subst DT0 k0 TS0.
  assert (EC : C0 = C) by (apply (fl_le8_eq W' m m' (bv_unsigned TS + 8 * k) C0 C A9 B9 Hm); fl_col).
  subst C0.
  assert (ET : T0 = T) by (apply (fl_le8_eq W' m m' (bv_unsigned C + 152) T0 T A10 B10 Hm); fl_col).
  assert (EDB : DB0 = DB) by (apply (fl_le8_eq W' m m' (TP + 8) DB0 DB A17 B17 Hm); fl_col).
  subst T0 DB0. repeat split.
Qed.

Lemma rr_tls_ret : forall cs m m' TP FS lo hi W D Y Wm,
  fp cs m TP FS lo hi W D ->
  (forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
     fp_dj (fp_tls TP DT TS C T DB k) (fp_w cs FS ++ Y)) ->
  munch Wm m m' -> sub_fp Wm (W ++ fp_w cs FS ++ Y) ->
  forall DT TS C T DB k, asan_tls_cells m' TP DT TS C T DB k -> fp_dj (fp_tls TP DT TS C T DB k) (fp_w cs FS ++ Y).
Proof.
  intros cs m m' TP FS lo hi W D Y Wm (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _)
    Htls Hm Hs DT TS C T DB k HT.
  assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x) (fp_tls TP DT0 TS0 C0 T0 DB0 k0)).
  { apply Forall_forall. intros [a b] Hin x Hx. apply Hs. apply fl_out_app.
    - exact (fl_dj_out W _ a b x HWd (in_or_app _ _ _ (or_introl Hin)) Hx).
    - exact (fl_dj_out_r _ _ a b x (Htls _ _ _ _ _ _ HT0) Hin Hx). }
  destruct (fl_tls_same m m' Wm TP DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT Hm Hc) as (E1 & E2 & E3 & E4 & E5 & E6).
  subst DT0 TS0 C0 T0 DB0 k0. exact (Htls _ _ _ _ _ _ HT0).
Qed.

Ltac steps_until_if :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; steps_until_if
  | _ => idtac
  end.

Ltac bjoin G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

Ltac chk_core X RX r SH pre extra :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
  destruct SH as (k & RK & OK & KR);
  pre X RX; steps_until_if; clear RK;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (clear -KR; lia);
  lazymatch goal with
  | |- evtF ?segs ?rgq ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs rgq Q (MS (bvmap_set r rr R) F B fc rv mm ro));
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

Lemma rr_bytes_ro : forall m A c, bytes_at rsegs m A (cbytes c) -> cell_wf c -> ro_cells rsegs m A [c].
Proof. intros m A c H Hw. split; [split; [exact Hw | exact I] | cbn [cells_bytes]; rewrite app_nil_r; exact H]. Qed.
Lemma rr_ro8 : forall m A v, bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof. intros m A v H. exact (rr_bytes_ro m A (C8 v) H I). Qed.
Lemma rr_ro4 : forall m A v, bytes_at rsegs m A (le4 v) -> ro_cells rsegs m A [C4 v].
Proof. intros m A v H. exact (rr_bytes_ro m A (C4 v) H I). Qed.
Lemma rr_land_align32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x / 32 * 32.
Proof.
  intros x Hx.
  replace 18446744073709551584 with (Z.land (Z.lnot (Z.ones 5)) (Z.ones 64)) by reflexivity.
  rewrite Z.land_assoc, (Z.land_comm x), <- Z.land_assoc, (Z.land_ones x 64) by lia.
  rewrite Z.mod_small by lia. rewrite Z.land_comm, <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* ---- Generic read/store transport helpers (adapted from reac_box_model_block.v). ---- *)
Definition rr_rd_mono (m m' : word -> option byte) : Prop :=
  forall x : word, (exists b, mrd rsegs m x = Some b) -> exists b, mrd rsegs m' x = Some b.

Lemma rr_rd_mono_refl : forall m, rr_rd_mono m m.
Proof. intros m x H. exact H. Qed.

Lemma rr_rd_mono_trans : forall m1 m2 m3, rr_rd_mono m1 m2 -> rr_rd_mono m2 m3 -> rr_rd_mono m1 m3.
Proof. intros m1 m2 m3 H1 H2 x Hx. apply H2, H1, Hx. Qed.

Lemma rr_wtm_cases : forall bs m (a x : word), write_to_mem m a bs x = m x \/ exists v, write_to_mem m a bs x = Some v.
Proof.
  induction bs as [|b bs IH]; intros m a x; cbn [write_to_mem]; [left; reflexivity|].
  destruct (IH (fun y => if bv_eqb y a then Some b else m y) (a + 1)%bv x) as [E|E]; [|right; exact E].
  rewrite E. destruct (bv_eqb x a); [right; eexists; reflexivity | left; reflexivity].
Qed.

Lemma rr_rd_mono_write : forall m0 m a bs, rr_rd_mono m0 m -> rr_rd_mono m0 (write_to_mem m a bs).
Proof.
  intros m0 m a bs H x Hx. destruct (H x Hx) as [v Hv]. unfold mrd in *.
  destruct (rr_wtm_cases bs m a x) as [E|[w E]]; rewrite E; [exists v; exact Hv | exists w; reflexivity].
Qed.

Lemma rr_rd_mono_munch : forall W m m', munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> exists b, mrd rsegs m' x = Some b) -> rr_rd_mono m m'.
Proof.
  intros W m m' Hm H x Hx. destruct (rc_outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - unfold mrd in *. rewrite (Hm x Ho). exact Hx.
  - exact (H x Ho).
Qed.

Lemma rr_stk_wv : forall m lo hi a, stk rsegs m lo hi -> lo <= a < hi -> wview rsegs m (wa a) <> None.
Proof. intros m lo hi a (_ & _ & H) Ha. exact (proj1 (H a Ha)). Qed.

Lemma rr_stk_mono : forall m m' lo hi, stk rsegs m lo hi -> wmono rsegs m m' -> rr_rd_mono m m' -> stk rsegs m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) Hw Hr. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hv Hb]. split; [apply Hw, Hv | apply Hr, Hb].
Qed.

Lemma rr_shadow_rw_on_mono : forall P m m', shadow_rw_on P m -> wmono rsegs m m' -> rr_rd_mono m m' ->
  shadow_rw_on P m'.
Proof.
  intros P m m' H Hw Hr a HP Ha. destruct (H a HP Ha) as [Hv Hb]. split; [apply Hw, Hv | apply Hr, Hb].
Qed.

Lemma rr_fs_place_mono : forall m m' FS, fs_place m FS -> wmono rsegs m m' -> rr_rd_mono m m' -> fs_place m' FS.
Proof.
  intros m m' FS (P1 & P2 & P3 & P4 & P5) Hw Hr. split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  split; [exact P4|]. exact (rr_stk_mono m m' _ _ P5 Hw Hr).
Qed.

Lemma rr_wv_store_ok : forall m m' a (n : nat),
  (forall i, 0 <= i < Z.of_nat n -> wview rsegs m (wa (a + i)) <> None) -> wmono rsegs m m' ->
  0 <= a -> a + Z.of_nat n <= 2^64 -> store_ok rsegs m' (wa a) n = true.
Proof.
  intros m m' a n H Hw Ha Hn.
  assert (WR : wr_at rsegs m' a (Z.of_nat n)) by (split; [lia|]; split; [lia|]; intros i Hi; apply Hw, H, Hi).
  pose proof (wr_at_store_ok rsegs m' a (Z.of_nat n) 0 n WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

Lemma rr_rd_of_bytes : forall m A bs, bytes_at rsegs m A bs ->
  forall y, A <= y < A + Z.of_nat (length bs) -> exists b, mrd rsegs m (wa y) = Some b.
Proof.
  intros m A bs (Ha & Hl & H) y Hy. pose proof (H (Z.to_nat (y - A)) ltac:(lia)) as E.
  replace (A + Z.of_nat (Z.to_nat (y - A))) with y in E by lia.
  destruct (nth_error bs (Z.to_nat (y - A))) as [v|] eqn:En; [exists v; exact E|].
  apply nth_error_None in En. lia.
Qed.

Lemma rr_rd_of_stk : forall m lo hi, stk rsegs m lo hi -> forall y, lo <= y < hi -> exists b, mrd rsegs m (wa y) = Some b.
Proof. intros m lo hi (_ & _ & H) y Hy. exact (proj2 (H y Hy)). Qed.

Lemma rr_not_outside_in : forall W x, ~ outside W x -> exists r, In r W /\ fst r <= x < snd r.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn in H; [exfalso; exact (H I)|].
  destruct (Z.le_gt_cases lo x); destruct (Z.lt_ge_cases x hi).
  - exists (lo, hi). split; [left; reflexivity | cbn; lia].
  - destruct (IH x) as (r & Hr & Hx); [intros Ho; apply H; split; [lia | exact Ho]|]. exists r. split; [right; exact Hr | exact Hx].
  - destruct (IH x) as (r & Hr & Hx); [intros Ho; apply H; split; [lia | exact Ho]|]. exists r. split; [right; exact Hr | exact Hx].
  - destruct (IH x) as (r & Hr & Hx); [intros Ho; apply H; split; [lia | exact Ho]|]. exists r. split; [right; exact Hr | exact Hx].
Qed.

Lemma rr_rd_mono_list : forall W m m', munch W m m' ->
  Forall (fun r => forall y, fst r <= y < snd r -> exists b, mrd rsegs m' (wa y) = Some b) W -> rr_rd_mono m m'.
Proof.
  intros W m m' Hm HF. apply (rr_rd_mono_munch W m m' Hm). intros x Hx.
  destruct (rr_not_outside_in W _ Hx) as (r & Hr & Hin). rewrite Forall_forall in HF.
  pose proof (HF r Hr (bv_unsigned x) Hin) as R. unfold wa in R. rewrite Z_to_bv_lit_self in R. exact R.
Qed.

Lemma rr_app_range : forall X n, 0 < n -> (forall i, 0 <= i < n -> app_mem (X + i)) ->
  X + n <= 2147450880 \/ 17594333495296 <= X.
Proof.
  intros X n Hn H. pose proof (H 0 ltac:(lia)) as H0. pose proof (H (n - 1) ltac:(lia)) as H1.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H0, H1.
  destruct (Z.le_gt_cases (X + n) 2147450880) as [L|L]; [left; exact L|].
  destruct (Z.le_gt_cases 17594333495296 X) as [G|G]; [right; exact G|].
  exfalso. pose proof (H (2147450880 - X) ltac:(lia)) as H2.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H2. lia.
Qed.

(* ---- Phase 2 (C6.2): the unpoison of p makes the 36 bytes [G + 32, G + 68) addressable. The code wrote
   SG[4 .. 7] = 0 (the 32 bytes [G + 32, G + 64) in scope) and SG[8] = 4 (the first 4 bytes of the next granule
   [G + 64, G + 68) in scope). ---- *)
Lemma rr_unpoison_addr : forall mc G,
  G mod 8 = 0 -> (forall i, 0 <= i < 36 -> app_mem (G + 32 + i)) ->
  bytes_at rsegs mc (shadow_addr (G + 32))
    [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] ->
  addressable mc (G + 32) 36.
Proof.
  intros mc G HG HAP HB.
  pose proof (HAP 0 ltac:(lia)) as AP0. pose proof (HAP 35 ltac:(lia)) as AP35.
  assert (Pge : 0 <= G + 32)
    by (destruct AP0 as [A|A]; unfold LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A; lia).
  assert (Pend : G + 32 + 36 <= APPMEM_END).
  { unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AP35. unfold APPMEM_END. lia. }
  split; [lia|]. split; [lia|]. split; [exact Pend|].
  intros i Hi. split; [exact (HAP i Hi)|].
  destruct HB as (HBa & HBl & HBnth). cbn [length] in HBl, HBnth.
  assert (Hq0 : 0 <= i / 8) by (apply Z.div_pos; lia).
  assert (ES : shadow_addr (G + 32 + i) = shadow_addr (G + 32) + Z.of_nat (Z.to_nat (i / 8))).
  { rewrite Z2Nat.id by exact Hq0. unfold shadow_addr.
    assert (D : (G + 32 + i) / 8 = (G + 32) / 8 + i / 8) by (Z.div_mod_to_equations; lia). lia. }
  set (j := Z.to_nat (i / 8)).
  pose proof (HBnth j) as RB.
  destruct (Z_lt_le_dec i 32) as [Lo|Hi32].
  - assert (Hj3 : (j < 4)%nat).
    { assert (i / 8 <= 3) by (Z.div_mod_to_equations; lia). subst j. lia. }
    assert (RBv : mrd rsegs mc (wa (shadow_addr (G + 32) + Z.of_nat j)) = Some (Z_to_bv 8 0)).
    { rewrite (RB ltac:(lia)). destruct j as [|[|[|[|j']]]]; cbn [nth_error]; try reflexivity; exfalso; lia. }
    exists (Z_to_bv 8 0). split.
    + rewrite ES. exact RBv.
    + left. vm_compute. reflexivity.
  - assert (Hj4 : j = 4%nat).
    { assert (i / 8 = 4) by (Z.div_mod_to_equations; lia). subst j. lia. }
    assert (RBv : mrd rsegs mc (wa (shadow_addr (G + 32) + Z.of_nat j)) = Some (Z_to_bv 8 4)).
    { rewrite (RB ltac:(lia)). rewrite Hj4. reflexivity. }
    exists (Z_to_bv 8 4). split.
    + rewrite ES. exact RBv.
    + right. replace (bv_signed (Z_to_bv 8 4)) with 4 by (vm_compute; reflexivity).
      split; [|lia].
      assert (M : (G + 32 + i) mod 8 = i mod 8) by (Z.div_mod_to_equations; lia).
      rewrite M. Z.div_mod_to_equations; lia.
Qed.

(* ---- Generic helpers for the segments (copied from lib/B/Prog/reac_ctrl_parse.v (not in this delivery) and the RcAsanFPLib.v of
   a working branch, renamed rr_*; generic in the memory, the frame base and the side-stack state). ---- *)

(* The store tactics also carry rr_rd_mono across a store. *)
Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | RMo : rr_rd_mono ?mq m |- _ => apply (rr_rd_mono_write mq m (wa a) bs) in RMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

Lemma rr_sh_add8 : forall G i, G mod 8 = 0 -> shadow_addr (G + 8 * i) = shadow_addr G + i.
Proof. intros G i Hf. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma rr_ble_nonneg : forall bs, 0 <= bytes_le_to_Z bs.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z]; [lia|].
  apply Z.lor_nonneg. split; [apply bv_unsigned_in_range | apply Z.shiftl_nonneg; exact IH].
Qed.

Lemma rr_ble_cons : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (rr_ble_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  assert (D : Z.land (bv_unsigned b) (bytes_le_to_Z bs * 256) = 0).
  { apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite <- (Z.mod_small (bv_unsigned b) (2 ^ 8)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  rewrite <- Z.lxor_lor by exact D. rewrite Z.add_nocarry_lxor by exact D. reflexivity.
Qed.

Lemma rr_le_bytes_ble : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite rr_ble_cons.
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (rr_ble_nonneg bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs) by (Z.div_mod_to_equations; lia).
    exact IH.
Qed.

(* Eight readable bytes are one word. *)
Lemma rr_rd8_le8 : forall m a, 0 <= a -> a + 8 <= 2^64 ->
  (forall i, 0 <= i < 8 -> exists b, mrd rsegs m (wa (a + i)) = Some b) -> exists w, bytes_at rsegs m a (le8 w).
Proof.
  intros m a Ha Hl H.
  destruct (H 0 ltac:(lia)) as [b0 E0]. destruct (H 1 ltac:(lia)) as [b1 E1].
  destruct (H 2 ltac:(lia)) as [b2 E2]. destruct (H 3 ltac:(lia)) as [b3 E3].
  destruct (H 4 ltac:(lia)) as [b4 E4]. destruct (H 5 ltac:(lia)) as [b5 E5].
  destruct (H 6 ltac:(lia)) as [b6 E6]. destruct (H 7 ltac:(lia)) as [b7 E7].
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])).
  assert (EL : le8 (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3; b4; b5; b6; b7])) = [b0; b1; b2; b3; b4; b5; b6; b7]).
  { rewrite <- store_bytes_8. cbn [width_bytes]. rewrite unsigned_lit_wrap.
    rewrite Z_to_le_bytes_mod by (cbn; lia).
    exact (rr_le_bytes_ble [b0; b1; b2; b3; b4; b5; b6; b7]). }
  rewrite EL. split; [lia|]. split; [cbn; lia|].
  intros i Hi. cbn [length] in Hi.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth_error]; simpl Z.of_nat;
    [rewrite Z.add_0_r in E0; replace (a + Z.of_nat 0) with a by lia; exact E0
    | exact E1 | exact E2 | exact E3 | exact E4 | exact E5 | exact E6 | exact E7 | lia].
Qed.

(* The 16 shadow bytes of a 128-byte frame of application memory are shadow bytes. *)
Lemma rr_frame_shadow_in : forall G i,
  0 <= G -> (G + 128 <= 2147450880 \/ 17594333495296 <= G) ->
  2147450880 <= G / 8 + ASAN_K -> G / 8 + ASAN_K + 16 <= 17594333495296 ->
  0 <= i < 16 -> in_shadow (G / 8 + ASAN_K + i).
Proof.
  intros G i H0 HG SHlo SHhi Hi.
  unfold in_shadow, ASAN_K, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *.
  destruct HG as [L|H]; [left | right]; Z.div_mod_to_equations; lia.
Qed.

Lemma rr_shadow16_stk_on : forall (P : Z -> Prop) mc G,
  shadow_rw_on P mc -> (forall i, 0 <= i < 16 -> P (G / 8 + ASAN_K + i)) ->
  0 <= G -> (G + 128 <= 2147450880 \/ 17594333495296 <= G) ->
  2147450880 <= G / 8 + ASAN_K -> G / 8 + ASAN_K + 16 <= 17594333495296 ->
  stk rsegs mc (G / 8 + ASAN_K) (G / 8 + ASAN_K + 16).
Proof.
  intros P mc G SR HP H0 HG SHlo SHhi. split; [lia|]. split; [lia|].
  intros a Ha. replace a with (G / 8 + ASAN_K + (a - (G / 8 + ASAN_K))) by lia.
  apply SR; [apply HP; lia|].
  apply rr_frame_shadow_in; [exact H0 | exact HG | exact SHlo | exact SHhi | lia].
Qed.

(* Route (C): a shadow byte of an addressable range is readable (from `addressable`, not from shadow_rw). *)
Lemma rr_addr_sh_rd : forall mc p n x, addressable mc p n -> shadow_addr p <= x < shadow_addr (p + n) ->
  exists b, mrd rsegs mc (wa x) = Some b.
Proof.
  intros mc p n x (Hp & Hn & _ & HA) Hx. unfold shadow_addr in Hx.
  destruct (Z_le_gt_dec p ((x - ASAN_K) * 8)) as [L|L].
  - assert (Hi : 0 <= (x - ASAN_K) * 8 - p < n) by (Z.div_mod_to_equations; lia).
    destruct (HA _ Hi) as (_ & b & Hb & _). exists b.
    replace (p + ((x - ASAN_K) * 8 - p)) with ((x - ASAN_K) * 8) in Hb by ring.
    unfold shadow_addr in Hb. rewrite Z.div_mul in Hb by lia.
    replace (x - ASAN_K + ASAN_K) with x in Hb by ring. exact Hb.
  - assert (Hi : 0 <= 0 < n) by (Z.div_mod_to_equations; lia).
    destruct (HA _ Hi) as (_ & b & Hb & _). exists b.
    rewrite Z.add_0_r in Hb. unfold shadow_addr in Hb.
    replace (p / 8 + ASAN_K) with x in Hb by (Z.div_mod_to_equations; lia). exact Hb.
Qed.

(* The 16 shadow bytes 0: the 128 bytes of the frame are addressable. *)
Lemma rr_frame_all_addr : forall mc G,
  0 <= G -> G mod 8 = 0 -> G + 128 <= APPMEM_END ->
  (forall i, 0 <= i < 128 -> app_mem (G + i)) ->
  (forall k, 0 <= k <= 15 -> exists b, mrd rsegs mc (wa (G / 8 + ASAN_K + k)) = Some b /\ bv_signed b = 0) ->
  addressable mc G 128.
Proof.
  intros mc G Hf0 Hmod Hend Hap Hz.
  split; [lia|]. split; [lia|]. split; [unfold APPMEM_END in *; lia|].
  intros i Hi. unfold addr_byte. split; [apply Hap; exact Hi|].
  assert (ESH : shadow_addr (G + i) = G / 8 + ASAN_K + i / 8).
  { unfold shadow_addr. replace (G + i) with (i + G / 8 * 8) by (Z.div_mod_to_equations; lia).
    rewrite Z.div_add by lia. lia. }
  assert (Hg : 0 <= i / 8 <= 15) by (Z.div_mod_to_equations; lia).
  destruct (Hz (i / 8) Hg) as (b & Hb & Hs).
  exists b. rewrite ESH. split; [exact Hb|]. unfold shadow_ok. left. exact Hs.
Qed.

Lemma rr_munch_mrd_out : forall W m1 m2 x, munch W m1 m2 -> 0 <= x < 2^64 -> outside W x ->
  mrd rsegs m2 (wa x) = mrd rsegs m1 (wa x).
Proof.
  intros W m1 m2 x MU Hx Hout. unfold mrd. rewrite (MU (wa x)); [reflexivity|].
  rewrite wa_unsigned by lia. exact Hout.
Qed.

Lemma rr_cols : forall W W' L, fp_dj W L -> sub_fp W' W ->
  Forall (fun d => forall x, fst d <= x < snd d -> outside W' x) L.
Proof.
  intros W W' L H Hs. apply Forall_forall. intros [a b] Hin x Hx. apply Hs. exact (fl_dj_out W L a b x H Hin Hx).
Qed.

Ltac rr_cellO Hm := eapply fl_bytes; [eassumption | exact Hm | fl_col].

(* The class-c state survives writes apart from the side stack's header [FS, FS + 36864). *)
Lemma rr_cls_h : forall W' m m' FS c, (forall x, FS <= x < FS + 36864 -> outside W' x) -> munch W' m m' ->
  fp_cls m FS c -> fp_cls m' FS c.
Proof.
  intros W' m m' FS c BEL Hm (Hc & h & flags & HH & HF & HFl & HFb).
  split; [exact Hc|]. exists h, flags.
  assert (B : FS <= fs_hint FS c /\ fs_hint FS c + 8 <= FS + 36864 /\
              FS <= fs_flag FS c 0 /\ fs_flag FS c 0 + fs_M c <= FS + 36864).
  { unfold fs_hint, fs_flag, fs_M. destruct c as [|[|[|[|[|[|[|c]]]]]]]; simpl; lia. }
  split; [eapply fl_bytes; [exact HH | exact Hm | intros x Hx; apply BEL; rewrite length_le8 in Hx; lia]|].
  split; [eapply fl_bytes; [exact HF | exact Hm | intros x Hx; apply BEL; lia]|].
  split; assumption.
Qed.

Lemma rr_stk : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H0 & H1 & H) Hm Hw HX. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as (Hv & b & Hb). split; [apply Hw, Hv|].
  destruct (HX a Ha) as [Ho | Hr]; [|exact Hr].
  exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
Qed.

(* fp after writes to W, the class bytes fp_w cs FS and the window's shadow, apart from the header points
   FS + 80 .. FS + 104; the side stack readable and the hint and the flag bytes read back 0/1 at m'
   (fl_fp_free of a working branch). *)
Lemma rr_fp_free : forall cs m m' TP FS lo hi W D Wm,
  fp cs m TP FS lo hi W D ->
  (forall DT TS C T DB k, asan_tls_cells m TP DT TS C T DB k ->
     fp_dj (fp_tls TP DT TS C T DB k) (fp_w cs FS ++ [(shadow_addr lo, shadow_addr hi)])) ->
  munch Wm m m' -> wmono rsegs m m' ->
  sub_fp Wm (W ++ fp_w cs FS ++ [(shadow_addr lo, shadow_addr hi)]) ->
  (forall x, FS + 80 <= x < FS + 104 -> outside Wm x) ->
  (forall x, FS <= x < FS + FS_SIZE -> outside Wm x \/ exists b, mrd rsegs m' (wa x) = Some b) ->
  (forall c, In c cs ->
     (exists h', bytes_at rsegs m' (fs_hint FS c) (le8 h')) /\
     (exists flags', bytes_at rsegs m' (fs_flag FS c 0) flags' /\ Z.of_nat (length flags') = fs_M c /\
        Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags')) ->
  fp cs m' TP FS lo hi W D.
Proof.
  intros cs m m' TP FS lo hi W D Wm (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HApp & HWd & HDd)
    Htls MU WM Hs O88 HRD Hcls.
  pose proof (Htls DT TS C T DB k HT) as TLSdj.
  assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x) (fp_tls TP DT TS C T DB k)).
  { apply Forall_forall. intros [a bnd] Hin x Hx. apply Hs. apply fl_out_app.
    - exact (fl_dj_out W _ a bnd x HWd (in_or_app _ _ _ (or_introl Hin)) Hx).
    - exact (fl_dj_out_r _ _ a bnd x TLSdj Hin Hx). }
  cbn [fp_tls] in Hc.
  repeat (let O := fresh "O" in apply Forall_cons_iff in Hc; destruct Hc as [O Hc]; cbn [fst snd] in O).
  pose proof HCL as HCL'.
  destruct HT as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18
    & T19).
  exists DT, TS, C, T, DB, k.
  split.
  { unfold asan_tls_cells.
    split; [rr_cellO MU|]. split; [rr_cellO MU|]. split; [rr_cellO MU|]. split; [rr_cellO MU|].
    split; [rr_cellO MU|]. split; [exact T6|]. split; [rr_cellO MU|]. split; [rr_cellO MU|].
    split; [rr_cellO MU|]. split; [rr_cellO MU|].
    split; [destruct T11 as (tb & te & T11); exists tb, te; rr_cellO MU|].
    split; [rr_cellO MU|]. split; [rr_cellO MU|]. split; [rr_cellO MU|]. split; [rr_cellO MU|].
    split; [rr_cellO MU|]. split; [rr_cellO MU|]. split; [exact T18|]. rr_cellO MU. }
  split; [rr_cellO MU|].
  split.
  { destruct HP as (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
    split; [exact P4|]. exact (rr_stk Wm m m' FS (FS + FS_SIZE) P5 MU WM HRD). }
  split; [rr_cellO MU|].
  split; [rr_cellO MU|].
  split.
  { apply Forall_forall. intros c Hin.
    pose proof (proj1 (Forall_forall _ _) HCL' c Hin) as HCc. destruct HCc as (Hc6 & _).
    destruct (Hcls c Hin) as ((h' & Hh') & (flags' & Hf' & Hl' & HF')).
    split; [exact Hc6|]. exists h', flags'. split; [exact Hh'|]. split; [exact Hf'|]. split; [exact Hl' | exact HF']. }
  split; [exact HFS|]. split; [exact HApp|]. split; [exact HWd | exact HDd].
Qed.

(* The last range of an apart list shrunk. *)
Lemma rr_dj_last : forall L X a b a' b', fp_dj L (X ++ [(a, b)]) -> a <= a' -> b' <= b ->
  fp_dj L (X ++ [(a', b')]).
Proof.
  intros L X a b a' b' H H1 H2. unfold fp_dj in *. eapply Forall_impl; [|exact H]. intros w Hw. cbn beta in Hw.
  apply Forall_app in Hw as [Hx Hy]. apply Forall_app. split; [exact Hx|].
  apply Forall_cons_iff in Hy as [Hy _]. constructor; [|constructor]. unfold ly_dj in *. cbn [fst snd] in *. lia.
Qed.

(* The class-1 flag array of m1 with byte j set to v (0 or 1) in m2, the other flag bytes kept: still 0/1. *)
Lemma rr_flags_set : forall (m1 m2 : word -> option byte) FS (j : Z) (v : byte) (flags : list byte),
  0 <= j < fs_M 1 -> (v = Z_to_bv 8 0 \/ v = Z_to_bv 8 1) ->
  bytes_at rsegs m1 (fs_flag FS 1 0) flags -> Z.of_nat (length flags) = fs_M 1 ->
  Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags ->
  mrd rsegs m2 (wa (fs_flag FS 1 j)) = Some v ->
  (forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1 -> x <> fs_flag FS 1 j ->
     mrd rsegs m2 (wa x) = mrd rsegs m1 (wa x)) ->
  exists flags', bytes_at rsegs m2 (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
     Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags'.
Proof.
  intros m1 m2 FS j v flags Hj Hv (Ba & Bl & BH) Hlen HFl Hvj Hoth.
  set (J := Z.to_nat j).
  assert (HJlt : (J < length flags)%nat) by (unfold J; lia).
  assert (EjZ : Z.of_nat J = j) by (unfold J; rewrite Z2Nat.id; lia).
  assert (Ej : fs_flag FS 1 j = fs_flag FS 1 0 + Z.of_nat J)
    by (rewrite EjZ; unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; lia).
  assert (HLfir : length (firstn J flags) = J) by (apply firstn_length_le; lia).
  assert (HLsk : length (skipn (Datatypes.S J) flags) = (length flags - Datatypes.S J)%nat) by (apply length_skipn).
  exists (firstn J flags ++ v :: skipn (Datatypes.S J) flags).
  assert (HL : length (firstn J flags ++ v :: skipn (Datatypes.S J) flags) = length flags).
  { rewrite length_app. cbn [length]. rewrite HLfir, HLsk. clear -HJlt. lia. }
  split; [|split].
  - split; [exact Ba|]. split; [rewrite HL; exact Bl|].
    intros i Hi. rewrite HL in Hi.
    assert (HiZ : Z.of_nat i < fs_M 1) by (rewrite <- Hlen; lia).
    destruct (lt_eq_lt_dec i J) as [[Hlt|Heq]|Hgt].
    + rewrite nth_error_app1 by (rewrite HLfir; lia).
      rewrite nth_error_firstn. replace (Nat.ltb i J) with true by (symmetry; apply Nat.ltb_lt; exact Hlt).
      rewrite Hoth.
      * apply BH. lia.
      * unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; clear -HiZ; lia.
      * rewrite Ej. clear -Hlt EjZ. lia.
    + subst i. rewrite nth_error_app2 by (rewrite HLfir; lia).
      rewrite HLfir, Nat.sub_diag. cbn [nth_error].
      replace (fs_flag FS 1 0 + Z.of_nat J) with (fs_flag FS 1 j) by (rewrite Ej; reflexivity). exact Hvj.
    + rewrite nth_error_app2 by (rewrite HLfir; lia). rewrite HLfir.
      destruct (i - J)%nat as [|d] eqn:Ed; [exfalso; clear -Hgt Ed; lia|].
      cbn [nth_error]. rewrite nth_error_skipn. replace (Datatypes.S J + d)%nat with i by lia.
      rewrite Hoth.
      * apply BH. lia.
      * unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; clear -HiZ; lia.
      * rewrite Ej. clear -Hgt EjZ. lia.
  - rewrite HL; exact Hlen.
  - apply Forall_app. split.
    + pose proof (firstn_skipn J flags) as Esp. rewrite <- Esp in HFl. apply Forall_app in HFl.
      exact (proj1 HFl).
    + apply Forall_cons; [exact Hv|].
      pose proof (firstn_skipn (Datatypes.S J) flags) as Esp. rewrite <- Esp in HFl. apply Forall_app in HFl.
      exact (proj2 HFl).
Qed.


(* The class-1 side-stack numbers. *)
Lemma rr_fsnum : forall FS0 j, fs_frame FS0 1 j = FS0 + 1085440 + j * 128 /\ fs_flag FS0 1 j = FS0 + 20480 + j /\
  fs_hint FS0 1 = FS0 + 8 /\ fs_M 1 = 8192.
Proof.
  intros FS0 j. unfold fs_frame, fs_flag, fs_hint, fs_M, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
  change (2 ^ 20) with 1048576. change (2 ^ 1) with 2. change (2 ^ 15) with 32768.
  change (2 ^ (15 - 1)) with 16384. change (2 ^ (14 - 1)) with 8192. lia.
Qed.

Lemma rr_fpw : forall FS0, fp_w [1%nat] FS0 =
  [(FS0 + 8, FS0 + 16); (FS0 + 20480, FS0 + 28672); (FS0 + 1085440, FS0 + 2134016);
   (shadow_addr (FS0 + 1085440), shadow_addr (FS0 + 2134016))].
Proof.
  intros FS0. unfold fp_w, fp_w1. cbn [flat_map app].
  destruct (rr_fsnum FS0 0) as (E1 & E2 & E3 & E4). destruct (rr_fsnum FS0 (fs_M 1)) as (E5 & _).
  rewrite E1, E2, E3, E5, E4. repeat (f_equal; try lia).
Qed.

(* A shadow byte is apart from a range of application memory. *)
Lemma rr_sh_notapp : forall y a b, in_shadow y -> (forall z, a <= z < b -> app_mem z) -> ~ (a <= y < b).
Proof. intros y a b Hy Hab Hin. exact (rr_app_not_shadow y (Hab y Hin) Hy). Qed.

(* ---- Generic helpers for segment 3 (the parse call). ---- *)
(* fp at a callee's return, where the callee's own side-stack state is given as fpx (the free-frame form). *)
Lemma rr_fp_retx : forall cs m0 m' TP FSq lo hi W D Y Wm lo' hi' W' D' X,
  fp cs m0 TP FSq lo hi W D ->
  (forall DT TS C T DB k, asan_tls_cells m0 TP DT TS C T DB k ->
     fp_dj (fp_tls TP DT TS C T DB k) (fp_w cs FSq ++ Y)) ->
  munch Wm m0 m' -> sub_fp Wm (W ++ fp_w cs FSq ++ Y) ->
  fpx cs m' TP FSq lo' hi' W' D' X -> fp cs m' TP FSq lo hi W D.
Proof.
  intros cs m0 m' TP FSq lo hi W D Y Wm lo' hi' W' D' X
    (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & HFS & HA & HWd & HDd) Htls Hm Hs
    (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & _ & _ & _ & _).
  assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x) (fp_tls TP DT0 TS0 C0 T0 DB0 k0)).
  { apply Forall_forall. intros [a b] Hin x Hx. apply Hs. apply fl_out_app.
    - exact (fl_dj_out W _ a b x HWd (in_or_app _ _ _ (or_introl Hin)) Hx).
    - exact (fl_dj_out_r _ _ a b x (Htls _ _ _ _ _ _ HT0) Hin Hx). }
  destruct (fl_tls_same m0 m' Wm TP DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT Hm Hc) as (E1 & E2 & E3 & E4 & E5 & E6).
  subst DT0 TS0 C0 T0 DB0 k0.
  exists DT, TS, C, T, DB, k.
  split; [exact HT|]. split; [exact HTP|]. split; [exact HP|]. split; [exact H88|]. split; [exact H96|].
  split; [exact HCL|]. split; [exact HFS|]. split; [exact HA|]. split; [exact HWd | exact HDd].
Qed.

Lemma rr_outside_In : forall L x, (forall r, In r L -> ~ (fst r <= x < snd r)) -> outside L x.
Proof.
  induction L as [|[a b] L IH]; intros x H; cbn [outside]; [exact I|].
  split; [exact (H (a, b) (or_introl eq_refl)) | apply IH; intros r Hr; apply H; right; exact Hr].
Qed.

(* A piece of [lo, hi) with the hole [a, b) cut out does not hold a byte of the hole. *)
Lemma rr_cut1_out : forall lo hi a b x r, a <= x < b -> In r (cut_ivls lo hi [(a, b)]) ->
  ~ (fst r <= x < snd r).
Proof.
  intros lo hi a b x r Hx Hin. apply nonempty_In in Hin.
  cbn [cut_ivls0 In] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; lia.
Qed.

(* The shadow of a range of application memory is in the shadow. *)
Lemma rr_sh_in : forall a b x, 0 <= a -> (b <= 2147450880 \/ 17594333495296 <= a) -> b <= APPMEM_END ->
  a <= b -> shadow_addr a <= x < shadow_addr b -> in_shadow x.
Proof.
  intros a b x Ha Hab Hb Hle Hx.
  unfold in_shadow, shadow_addr, ASAN_K, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *.
  destruct Hab as [L|H]; [left | right]; Z.div_mod_to_equations; lia.
Qed.

(* A 1-byte store at A + |l| just after the bytes l at A: the bytes l ++ [b] at A, and the run still wrote only
   [A, A + n). *)
Lemma rr_sb_next : forall (m0 m1 : word -> option byte) A n (l : list byte) (b : byte),
  0 <= A -> A + n <= 2^64 -> Z.of_nat (length l) < n ->
  bytes_at rsegs m1 A l -> munch [(A, A + n)] m0 m1 ->
  bytes_at rsegs (write_to_mem m1 (wa (A + Z.of_nat (length l))) [b]) A (l ++ [b]) /\
  munch [(A, A + n)] m0 (write_to_mem m1 (wa (A + Z.of_nat (length l))) [b]).
Proof.
  intros m0 m1 A n l b HA Hn Hl (_ & _ & HB) MU. split.
  - split; [lia|]. split; [rewrite length_app; cbn [length]; lia|].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. unfold mrd in *.
    rewrite write_to_mem_spec by (cbn [length]; lia). rewrite wa_unsigned by lia. cbn [length].
    destruct (Nat.lt_ge_cases i (length l)) as [Li|Li].
    + destruct (Z.leb_spec0 (A + Z.of_nat (length l)) (A + Z.of_nat i)); [lia|]. cbn [andb].
      rewrite nth_error_app1 by exact Li. exact (HB i Li).
    + assert (Ei : i = length l) by lia. subst i.
      destruct (Z.leb_spec0 (A + Z.of_nat (length l)) (A + Z.of_nat (length l))); [|lia].
      destruct (Z.ltb_spec0 (A + Z.of_nat (length l)) (A + Z.of_nat (length l) + Z.of_nat 1)); [|lia].
      cbn [andb]. rewrite Z.sub_diag. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
  - apply munch_write; [exact MU | lia | cbn [length]; lia | ]. cbn [inside length]. left. lia.
Qed.

(* Pointwise apart from a list of nonempty ranges is apart (fp_dj) from it. *)
Lemma rr_dj_of_out : forall a b L, a < b -> (forall r, In r L -> fst r < snd r) ->
  (forall x, a <= x < b -> outside L x) -> fp_dj [(a, b)] L.
Proof.
  intros a b L Hab Hne Hout. unfold fp_dj. constructor; [|constructor].
  apply Forall_forall. intros [c d] Hin. cbn [fst snd]. unfold ly_dj.
  pose proof (Hne _ Hin) as Hcd. cbn [fst snd] in Hcd.
  destruct (Z_le_gt_dec b c) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec d a) as [H2|H2]; [right; exact H2|].
  exfalso. apply (outside_In L (Z.max a c) (c, d) (Hout (Z.max a c) ltac:(lia)) Hin). cbn [fst snd]. lia.
Qed.

(* fpx for a callee: fp with a window [lo', hi') inside [lo, hi), the callee's writes W' apart from the thread
   cells and the header, its data ranges D' apart from the free-frame footprint. *)
Lemma rr_fpx_sub : forall cs (mq : word -> option byte) TP FSq lo hi W D lo' hi' W' D' X,
  fp cs mq TP FSq lo hi W D -> lo <= lo' -> hi' <= hi ->
  (forall DT TS C T DB k, asan_tls_cells mq TP DT TS C T DB k ->
     fp_dj W (fp_tls TP DT TS C T DB k ++ [(FSq, fs_frame FSq 0 0)]) ->
     fp_dj W' (fp_tls TP DT TS C T DB k ++ [(FSq, fs_frame FSq 0 0)])) ->
  fp_dj D' (fp_wx cs FSq X) ->
  fpx cs mq TP FSq lo' hi' W' D' X.
Proof.
  intros cs mq TP FSq lo hi W D lo' hi' W' D' X (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HA &
    HWd & HDd) H1 H2 HW HD.
  exists DT, TS, C, T, DB, k.
  split; [exact HT|]. split; [exact HTP|]. split; [exact HP|]. split; [exact H88|]. split; [exact H96|].
  split; [exact HCL|]. split; [lia|]. split; [intros a Ha; apply HA; lia|].
  split; [exact (HW _ _ _ _ _ _ HT HWd) | exact HD].
Qed.

Lemma rr_le1_0 : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.

Lemma rr_le1_4 : le1 (Z_to_bv 64 4) = [Z_to_bv 8 4].
Proof. reflexivity. Qed.

(* One 1-byte store in a run of stores to [A, A + n): the bytes so far, the writes, wmono, rr_rd_mono, mem_inv. *)
Lemma rr_sb_step : forall (mq m0 m1 : word -> option byte) A n (l : list byte) (b : byte) a,
  a = A + Z.of_nat (length l) -> 0 <= A -> A + n <= 2^64 -> Z.of_nat (length l) < n ->
  bytes_at rsegs m1 A l -> munch [(A, A + n)] m0 m1 -> wmono rsegs mq m1 -> rr_rd_mono m0 m1 ->
  mem_inv rsegs m1 -> store_ok rsegs m1 (wa a) 1 = true ->
  bytes_at rsegs (write_to_mem m1 (Z_to_bv 64 a) [b]) A (l ++ [b]) /\
  munch [(A, A + n)] m0 (write_to_mem m1 (Z_to_bv 64 a) [b]) /\
  wmono rsegs mq (write_to_mem m1 (Z_to_bv 64 a) [b]) /\ rr_rd_mono m0 (write_to_mem m1 (Z_to_bv 64 a) [b]) /\
  mem_inv rsegs (write_to_mem m1 (Z_to_bv 64 a) [b]).
Proof.
  intros mq m0 m1 A n l b a Ea HA Hn Hl HB MU WMq RMq MIq HSq. subst a.
  destruct (rr_sb_next m0 m1 A n l b HA Hn Hl HB MU) as [HB' MU'].
  split; [exact HB'|]. split; [exact MU'|]. split; [exact (wmono_write rsegs mq m1 _ _ WMq)|].
  split; [exact (rr_rd_mono_write m0 m1 _ _ RMq)|].
  exact (mem_inv_store rsegs m1 _ [b] MIq HSq).
Qed.

(* A byte of application memory is apart from a range of shadow bytes. *)
Lemma rr_app_out_sh : forall x A n, app_mem x -> 2147450880 <= A -> A + n <= 17594333495296 -> outside [(A, A + n)] x.
Proof.
  intros x A n Hx HA Hn. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hx. cbn [outside].
  split; [lia | exact I].
Qed.

Lemma rr_dj_sym : forall A B, fp_dj A B -> fp_dj B A.
Proof.
  intros A B H. unfold fp_dj in *. rewrite Forall_forall in *. intros b Hb. rewrite Forall_forall. intros a Ha.
  pose proof (H a Ha) as H1. rewrite Forall_forall in H1. pose proof (H1 b Hb) as H2. unfold ly_dj in *. lia.
Qed.

Lemma rr_dj_sub_r : forall L X X', fp_dj L X -> (forall r, In r X' -> In r X) -> fp_dj L X'.
Proof.
  intros L X X' H Hs. unfold fp_dj in *. eapply Forall_impl; [|exact H]. intros w Hw. cbn beta in Hw.
  rewrite Forall_forall in Hw |- *. intros d Hd. exact (Hw d (Hs d Hd)).
Qed.

(* A range inside [c, d), where [c, d) is apart from every range of L, is apart from L. *)
Lemma rr_dj_inside : forall a b c d L, fp_dj L [(c, d)] -> c <= a -> a <= b -> b <= d -> fp_dj [(a, b)] L.
Proof.
  intros a b c d L H H1 H2 H3. apply (fl_dj_sub c d a b L); [exact (rr_dj_sym _ _ H) | exact H1 | exact H3 | exact H2].
Qed.

Section Rep.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (fr len pa pp pn S FS : Z) (g ja jp jn : list byte).
  Hypothesis Rfr : 0 <= fr < 2^64.
  Hypothesis Rlen : 0 <= len < 2^64.
  Hypothesis Rpa : 0 <= pa < 2^64.
  Hypothesis Rpp : 0 <= pp < 2^64.
  Hypothesis Rpn : 0 <= pn < 2^64.
  Hypothesis HS : S < 2^64.
  Hypothesis S16 : S mod 16 = 0.
  Hypothesis HSK : 9072 <= S.
  Hypothesis ST : stk rsegs m (S - 9072) S.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis Hg : length g = 50%nat.
  Hypothesis HF : reply_args fr pa pp pn = true -> 50 <= len ->
    fr + 50 <= 2^64 /\ bytes_at rsegs m fr g /\ (fr + 50 <= S - 9072 \/ S <= fr) /\
    (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\ (pn + 8 <= fr \/ fr + 50 <= pn).
  Hypothesis HO : reply_args fr pa pp pn = true ->
    pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
    rw_cells rsegs m pa [CB 2 ja] /\ rw_cells rsegs m pp [CB 8 jp] /\ rw_cells rsegs m pn [CB 8 jn] /\
    (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
    (pa + 2 <= S - 9072 \/ S <= pa) /\ (pp + 8 <= S - 9072 \/ S <= pp) /\ (pn + 8 <= S - 9072 \/ S <= pn).
  Hypothesis AC : asan_cells m.
  Hypothesis SW : shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) m.
  Hypothesis HHM : HIGHMEM_BEG <= S - 9072.
  Hypothesis HAE : S <= APPMEM_END.
  Hypothesis AW : addressable m (S - 9072) 9072.
  Hypothesis AFfr : reply_args fr pa pp pn = true -> 50 <= len -> addressable m fr 50.
  Hypothesis AOUT : reply_args fr pa pp pn = true ->
    addressable m pa 2 /\ addressable m pp 8 /\ addressable m pn 8 /\
    (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn).
  Hypothesis ABC : addressable m REAC_CTRL_PARSE_BC 6.
  Hypothesis HBCMP : bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)).
  Hypothesis HMEMCMP : bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)).
  Hypothesis HGCF : bytes_at rsegs m GOT_CF (le8 (wa CF)).
  Hypothesis HCF254 : bytes_at rsegs m (CF + 254) [Z_to_bv 8 1].
  Hypothesis HCF255 : bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
  Hypothesis FP0 : fp [1%nat] m (bv_unsigned tp) FS (S - 9072) S
    (reac_ctrl_identity_reply_W fr pa pp pn S) (reac_ctrl_identity_reply_D fr len pa pp pn).
  Hypothesis TLS0 : reac_ctrl_identity_reply_tls m (bv_unsigned tp) FS (S - 9072) S.
  (* ---- The footprint premises of the run (reac_ctrl_identity_reply_contract_F). The shadow covers are QUANTIFIED
     (shcov / shkov / shspan); the ranges without a division stay ground, since StepF's solve_acc1 matches them in
     the context. The ranges guarded by reply_args (and 50 <= len) are taken where the run has those guards. ---- *)
  Variable RNG : ExecF.footprint.
  Hypothesis RBY : rng_bytes RNG.
  Hypothesis RIMG : rng RNG 0x10000 0x5ee000.
  Hypothesis RWIN : rng RNG (S - 9072) 9072.
  Hypothesis SSW : shspan RNG (S - 9072) S.
  Hypothesis SCW : shcov RNG (S - 9072) 9072.
  Hypothesis SKW : shkov RNG (S - 288) 160.
  Hypothesis RFR : reply_args fr pa pp pn = true -> 50 <= len -> rng RNG fr 50.
  Hypothesis SCF : reply_args fr pa pp pn = true -> 50 <= len -> shcov RNG fr 50.
  Hypothesis SKF : reply_args fr pa pp pn = true -> 50 <= len -> shkov RNG fr 50.
  Hypothesis RPA : reply_args fr pa pp pn = true -> rng RNG pa 2.
  Hypothesis SCPA : reply_args fr pa pp pn = true -> shcov RNG pa 2.
  Hypothesis RPP : reply_args fr pa pp pn = true -> rng RNG pp 8.
  Hypothesis SCPP : reply_args fr pa pp pn = true -> shcov RNG pp 8.
  Hypothesis RPN : reply_args fr pa pp pn = true -> rng RNG pn 8.
  Hypothesis SCPN : reply_args fr pa pp pn = true -> shcov RNG pn 8.
  Hypothesis SKBC : shkov RNG REAC_CTRL_PARSE_BC 6.
  Hypothesis RFSS : rng RNG FS (fs_frame FS 0 0 - FS).
  Hypothesis RFLG : rng RNG (fs_flag FS 1 0) (fs_M 1).
  Hypothesis RFRM : rng RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis SCFM : shcov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis SKFM : shkov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis RW1 : Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS).
  Hypothesis RTLS : forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
    Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k).

  Lemma rep_RS : 9072 <= S < 2^64.
  Proof. split; [exact HSK | exact HS]. Qed.

  (* The aligned frame base A = (S - 128) with its low 5 bits cleared (`andi sp,sp,-32`): A = S - 128 or S - 144. *)
  Definition rA := (S - 128) / 32 * 32.

  Lemma rA_facts : rA mod 32 = 0 /\ S - 144 <= rA <= S - 128.
  Proof. unfold rA. pose proof S16. Z.div_mod_to_equations. lia. Qed.

  (* The side stack's place and the data ranges apart from the class-1 side-stack bytes (fp in m). *)
  Lemma rr_fs : 0 < FS /\ FS mod 4096 = 0 /\ ASAN_GT <= FS /\ FS + FS_SIZE <= S - 9072 /\
    (forall a, FS <= a < FS + FS_SIZE -> app_mem a) /\
    fp_dj (reac_ctrl_identity_reply_D fr len pa pp pn) (fp_w [1%nat] FS).
  Proof.
    destruct FP0 as (DT & TS & C & T & DB & kk & _ & _ & HP & _ & _ & _ & HFS & _ & _ & HDd).
    destruct HP as (P1 & P2 & P3 & P4 & _). repeat split; assumption.
  Qed.

  (* ===== Segment 1: the prologue (+0x0 .. +0x130 = 0x848fc .. 0x84a2c), the class-1 frame request
     __asan_stack_malloc_1(128) and the choice of the side-stack frame or the real-stack fallback with its page
     probe, then the frame words and the 16 shadow bytes of the frame. (After the parse B proof of
     a working branch, entry/fwords.) ===== *)

  (* The 13 saved registers, lowest address (S - 104, s11) first. *)
  Definition rSAVES : list cell :=
    [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* The writes of the prologue: the window, the class-1 hint word, flag j (nn = 1), the frame and its shadow. *)
  Definition rWf (G j nn : Z) : list ivl :=
    [(S - 9072, S); (fs_hint FS 1, fs_hint FS 1 + 8); (fs_flag FS 1 j, fs_flag FS 1 j + nn);
     (G, G + 128); (shadow_addr G, shadow_addr G + 16)].

  (* The frame G: on the real stack (fv = s2 = 0, G = sp = rA - 128) or the side-stack frame j (fv = G, sp = rA). *)
  Definition rFK (G fv spc j nn : Z) : Prop :=
    (fv = 0 /\ G = rA - 128 /\ spc = rA - 128 /\ j = 0 /\ nn = 0) \/
    (0 <= j < fs_M 1 /\ G = fs_frame FS 1 j /\ fv = G /\ spc = rA /\ nn = 1).

  (* Route (C): the shadow bytes the run takes from SW lie in reac_ctrl_identity_reply_shadow_R
     (lib/B/Prog/reac_ctrl_identity_reply_c_on.v): the frame's 16 shadow bytes (the real frame: disjunct 1; a side
     frame: disjunct 2), __asan_stack_malloc_1's region and the class-1 frames' shadow (disjunct 2), and
     reac_ctrl_parse's region at its call (disjunct 3 on the real stack, disjunct 4 on the side stack), the last two
     under reply_args, which holds at the parse call (rKN). *)
  Lemma rr_malloc_inR : forall a, asan_stack_malloc_shadow_R FS 1 a ->
    reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS a.
  Proof. intros a Ha. unfold reac_ctrl_identity_reply_shadow_R. cbv zeta. right; left. exact Ha. Qed.

  Lemma rr_blk_inR : forall x, shadow_addr (FS + 1085440) <= x < shadow_addr (FS + 2134016) ->
    reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS x.
  Proof.
    intros x Hx. apply rr_malloc_inR. unfold asan_stack_malloc_shadow_R. rewrite (rrF_fs_frame1 FS 0).
    unfold shadow_addr in *. Z.div_mod_to_equations. lia.
  Qed.

  Lemma rk_inR : forall G fv spc j nn, rFK G fv spc j nn ->
    forall i, 0 <= i < 16 -> reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS (G / 8 + ASAN_K + i).
  Proof.
    intros G fv spc j nn HK i Hi.
    destruct HK as [(_ & EG & _) | (Hj & EG & _)]; subst G.
    - unfold reac_ctrl_identity_reply_shadow_R. cbv zeta. left. unfold rA, shadow_addr. lia.
    - apply rr_malloc_inR. unfold asan_stack_malloc_shadow_R. rewrite !rrF_fs_frame1.
      change (fs_M 1) with 8192 in Hj. unfold shadow_addr. Z.div_mod_to_equations. lia.
  Qed.

  Lemma rk_parse_inR : forall G fv spc j nn, rFK G fv spc j nn -> reply_args fr pa pp pn = true ->
    forall a, reac_ctrl_parse_shadow_R fr len (G + 32) spc FS a ->
    reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS a.
  Proof.
    intros G fv spc j nn HK RAb a Ha. unfold reac_ctrl_identity_reply_shadow_R. cbv zeta.
    destruct HK as [(_ & EG & Esp & _) | (Hj & EG & _ & Esp & _)]; subst G spc.
    - right; right; left. split; [exact RAb|]. unfold rA in Ha.
      replace ((S - 128) / 32 * 32 - 96) with ((S - 128) / 32 * 32 - 128 + 32) by ring. exact Ha.
    - right; right; right. split; [exact RAb|]. exists j. split; [exact Hj | exact Ha].
  Qed.

  Definition rBI (G j nn : Z) (mc : word -> option byte) : Prop :=
    munch (rWf G j nn) m mc /\ wmono rsegs m mc /\ rr_rd_mono m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (S - 104) rSAVES /\
    (nn = 1 -> bytes_at rsegs mc (G + 120) (le8 (Z_to_bv 64 (fs_flag FS 1 j))) /\
               bytes_at rsegs mc (fs_flag FS 1 j) [Z_to_bv 8 1]).

  Lemma rr_STW0 : forall a, S - 9072 <= a < S -> wview rsegs m (wa a) <> None.
  Proof. intros a Ha. exact (rr_stk_wv m _ _ _ ST Ha). Qed.

  (* What every frame gives: alignment, place, writable and AppMem bytes, writable shadow bytes. *)
  Lemma rk_facts : forall G fv spc j nn, rFK G fv spc j nn ->
    G mod 8 = 0 /\ FS + 36864 <= G /\ G + 128 <= rA /\ (spc = rA \/ spc = G) /\
    (forall i, 0 <= i < 128 -> wview rsegs m (wa (G + i)) <> None) /\
    (forall i, 0 <= i < 128 -> app_mem (G + i)) /\
    (G + 128 <= 2147450880 \/ 17594333495296 <= G) /\
    (forall i, 0 <= i < 16 -> wview rsegs m (wa (G / 8 + ASAN_K + i)) <> None) /\
    2147450880 <= G / 8 + ASAN_K /\ G / 8 + ASAN_K + 16 <= 17594333495296.
  Proof.
    intros G0 fv spc j nn HK.
    pose proof rA_facts as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HP & _ & _ & _ & HFS & HAPP & _).
    pose proof HP as (P1 & P2 & P3 & P4 & P5). unfold FS_SIZE in HFS, P4, P5.
    assert (B : G0 mod 8 = 0 /\ FS + 36864 <= G0 /\ G0 + 128 <= rA /\ (spc = rA \/ spc = G0) /\
                (forall i, 0 <= i < 128 -> wview rsegs m (wa (G0 + i)) <> None) /\
                (forall i, 0 <= i < 128 -> app_mem (G0 + i))).
    { destruct HK as [(Ef & Efr & Esp & Ej & En) | (Hj & Efr & Ef & Esp & En)]; subst G0.
      - split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [right; lia|].
        split; [intros i Hi; apply (rr_stk_wv m _ _ _ ST); lia|].
        intros i Hi. unfold app_mem. right. lia.
      - unfold fs_frame, fs_M, fs_B in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
        change (2 ^ (14 - 1)) with 8192 in Hj. change (2 ^ 1) with 2 in *. change (2 ^ 20) with 1048576 in *.
        split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [left; lia|].
        split; [intros i Hi; apply (rr_stk_wv m _ _ _ P5); lia|].
        intros i Hi. apply P4. lia. }
    destruct B as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (rr_app_range G0 128 ltac:(lia) B6) as B7.
    assert (B8 : forall i, 0 <= i < 16 -> G0 / 8 + ASAN_K + i = shadow_addr (G0 + 8 * i)).
    { intros i Hi. rewrite rr_sh_add8 by exact B1. unfold shadow_addr. lia. }
    do 7 (split; [assumption|]).
    split.
    - intros i Hi. pose proof (rk_inR G0 fv spc j nn HK i Hi) as HR. rewrite B8 in HR by exact Hi.
      rewrite B8 by exact Hi. apply (proj1 (SW _ HR (rt_app_shadow _ (B6 (8 * i) ltac:(lia))))).
    - unfold ASAN_K. split; Z.div_mod_to_equations; lia.
  Qed.

  (* ---- The footprint of the frame __asan_stack_malloc_1 gave: its 128 bytes, the shadow byte of each and the
     aligned shadow word cover of each sub-range are in RNG, whether it is the real-stack frame (inside the window)
     or a side frame (inside the class-1 frames). ---- *)
  Lemma rrF_frame : forall G fv spc j nn, rFK G fv spc j nn -> rng RNG G 128.
  Proof.
    intros G fv spc j nn HK. pose proof rA_facts as (HA32 & HAlo & HAhi).
    assert (EM : fs_M 1 = 8192) by reflexivity.
    destruct HK as [(Efv & EG & Espc & Ej & En) | (Hj & EG & Efv & Espc & En)]; subst G.
    - eapply rng_sub; [exact RWIN | lia | lia].
    - eapply rng_sub; [exact RFRM | rewrite !rrF_fs_frame1; lia | rewrite !rrF_fs_frame1; lia].
  Qed.

  Lemma rrF_frame_cov : forall G fv spc j nn, rFK G fv spc j nn -> shcov RNG G 128.
  Proof.
    intros G fv spc j nn HK. pose proof rA_facts as (HA32 & HAlo & HAhi).
    assert (EM : fs_M 1 = 8192) by reflexivity.
    destruct HK as [(Efv & EG & Espc & Ej & En) | (Hj & EG & Efv & Espc & En)]; subst G.
    - eapply shcov_sub; [exact SCW | lia | lia].
    - eapply shcov_sub; [exact SCFM | rewrite !rrF_fs_frame1; lia | rewrite !rrF_fs_frame1; lia].
  Qed.

  Lemma rrF_frame_kov : forall G fv spc j nn, rFK G fv spc j nn -> shkov RNG G 128.
  Proof.
    intros G fv spc j nn HK. pose proof rA_facts as (HA32 & HAlo & HAhi).
    assert (EM : fs_M 1 = 8192) by reflexivity.
    destruct HK as [(Efv & EG & Espc & Ej & En) | (Hj & EG & Efv & Espc & En)]; subst G.
    - eapply shkov_sub; [exact SKW | lia | lia].
    - eapply shkov_sub; [exact SKFM | rewrite !rrF_fs_frame1; lia | rewrite !rrF_fs_frame1; lia].
  Qed.

  (* The 16 shadow bytes of the frame, at the addresses the run forms: G / 8 + ASAN_K + i. *)
  Lemma rrF_frame_blk : forall G fv spc j nn, rFK G fv spc j nn -> shblk RNG G 15.
  Proof.
    intros G fv spc j nn HK.
    destruct (rk_facts G fv spc j nn HK) as (FR8 & _).
    pose proof (rrF_frame_cov G fv spc j nn HK) as HC.
    intros i Hi. pose proof (rr_sh_add8 G i FR8) as Hs. unfold shadow_addr in Hs.
    replace (G / 8 + ASAN_K + i) with ((G + 8 * i) / 8 + ASAN_K) by lia.
    apply HC. lia.
  Qed.

  (* The thread cells of a state reached by writes apart from them are m's, so the statement's one rng fact per
     cell of fp_tls holds for them (the pattern of rr_tls_ret). *)
  Lemma rrF_tls : forall mc Wm, munch Wm m mc ->
    sub_fp Wm (reac_ctrl_identity_reply_W fr pa pp pn S ++ fp_w [1%nat] FS ++
               [(shadow_addr (S - 9072), shadow_addr S)]) ->
    forall DT TS C T DB k, asan_tls_cells mc (bv_unsigned tp) DT TS C T DB k ->
      Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k).
  Proof.
    intros mc Wm Hm Hs DT TS C T DB k HT.
    pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _).
    assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x)
                   (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0)).
    { apply Forall_forall. intros [a b] Hin x Hx. apply Hs. apply fl_out_app.
      - exact (fl_dj_out _ _ a b x HWd (in_or_app _ _ _ (or_introl Hin)) Hx).
      - exact (fl_dj_out_r _ _ a b x (TLS0 _ _ _ _ _ _ HT0) Hin Hx). }
    destruct (fl_tls_same m mc Wm (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT Hm Hc)
      as (E1 & E2 & E3 & E4 & E5 & E6).
    subst DT0 TS0 C0 T0 DB0 k0. exact (RTLS _ _ _ _ _ _ HT0).
  Qed.

  (* The continuation at 0x84a2c (after `li a0,-1`). *)
  Definition rKB (Q : machine_state -> Prop) : Prop :=
    forall (G fv spc j nn : Z) (mc : word -> option byte)
           (rr x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      rFK G fv spc j nn -> rBI G j nn mc ->
      evtF rsegs RNG Q (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 rA)
                         (Z_to_bv 64 (-1)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 pn)
                         (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len) s8
                         (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) (wa ASAN_K) x28 x29 x30 x31)
                    F (Z_to_bv 64 0x84a2c) fc None mc (seg_rom rsegs)).

  Ltac rwst a nn tac :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) nn = true)
          by (eapply rr_wv_store_ok;
                [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; tac | eassumption | lia | lia ])
    end.

  Ltac rwstb a nn base fact :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) nn = true)
          by (eapply rr_wv_store_ok;
                [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
                  match goal with |- wview _ _ (wa ?X) <> None => replace X with (base + (X - base)) by lia end;
                  apply fact; lia
                | eassumption | lia | lia ])
    end.

  (* 0x849ac .. 0x84a2c: the stack slot A + 16, the 3 frame words and the 16 shadow bytes of the frame. *)
  Lemma rp_fwords : forall G fv spc j nn mc
    (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word) Q,
    rFK G fv spc j nn -> rBI G j nn mc -> rKB Q ->
    evtF rsegs RNG Q (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 rA)
                       x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 pn) (Z_to_bv 64 pp)
                       (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len) s8 x25 (Z_to_bv 64 G) (wa ASAN_K)
                       x28 x29 x30 x31)
                    F (Z_to_bv 64 0x849ac) fc None mc (seg_rom rsegs)).
  Proof.
    intros G fv spc j nn mc rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 Q HK HB K.
    pose proof rA_facts as (HA32 & HAlo & HAhi).
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SWh & SH1 & SH2).
    pose proof (rrF_frame G fv spc j nn HK) as RGFRM. pose proof (rrF_frame_blk G fv spc j nn HK) as SBFRM.
    pose proof rr_fs as (FS0 & _).
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI1 & SV & H120).
    assert (HHMl : 17594333495296 <= S - 9072) by (pose proof HHM as HH0; unfold HIGHMEM_BEG in HH0; exact HH0).
    unfold rWf, shadow_addr in MU.
    (* the block's own writes: the stack slot, the 3 frame words and the 16 shadow bytes *)
    pose proof (munch_refl [(rA + 16, rA + 24); (G, G + 24); (G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] mc) as MUw.
    rwst (rA + 16) 8%nat ltac:(apply rr_STW0; lia). step. store_done.
    step. step. step. step. step. step. step. step.
    rwstb G 8%nat G FW. step. store_done.
    rwstb (G + 8) 8%nat G FW. step. store_done.
    rwstb (G + 16) 8%nat G FW. step. store_done.
    step. step.
    rewrite (unsigned_lit G) by lia. rewrite rc_shr3.
    rwstb (G / 8 + ASAN_K + 0) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 1) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 2) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 3) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    step.
    rwstb (G / 8 + ASAN_K + 4) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 5) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 6) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 7) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 12) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 13) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 14) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 15) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 8) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 9) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 10) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 11) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    step.
    eapply K; [exact HK|].
    unfold rBI, rWf, shadow_addr. refine (conj MU (conj WM (conj RM (conj MI1 (conj SV _))))).
    intros Hn1. destruct (H120 Hn1) as (H1 & H2).
    destruct HK as [(_ & _ & _ & _ & E)|(Hj & EG & _ & _ & _)]; [lia|].
    pose proof rr_fs as (_ & _ & _ & HFSb & HFSapp & _).
    pose proof (rr_app_range FS FS_SIZE ltac:(unfold FS_SIZE; lia) ltac:(intros i Hi; apply HFSapp; lia)) as FSR.
    assert (EFl : fs_flag FS 1 j = FS + 20480 + j) by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (EGj : G = FS + 1085440 + j * 128)
      by (rewrite EG; unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; change (2 ^ 20) with 1048576; lia).
    assert (Hjb : 0 <= j < 8192)
      by (unfold fs_M in Hj; cbn [Z.of_nat Pos.of_succ_nat] in Hj; change (2 ^ (14 - 1)) with 8192 in Hj; exact Hj).
    unfold FS_SIZE, HIGHMEM_BEG, LOWMEM_END, ASAN_K in *.
    split.
    - eapply (bytes_at_transport rsegs _ mc _ (G + 120) _ H1 MUw). cbn [disjoint_from]. rewrite length_le8.
      split; [lia|]. split; [lia|]. split; [|exact I]. destruct FSR; [left|right]; Z.div_mod_to_equations; lia.
    - eapply (bytes_at_transport rsegs _ mc _ _ _ H2 MUw). cbn [disjoint_from length]. rewrite EFl.
      split; [lia|]. split; [lia|]. split; [|exact I]. destruct FSR; [left|right]; Z.div_mod_to_equations; lia.
  Qed.

  Ltac rsteps_to P :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 P) _ _ _ _) => idtac
    | _ => step; rsteps_to P
    end.

  (* ===== The cut after the fake-stack call (bF-glue.md: the stretch AFTER __asan_stack_malloc_1 starts at its
     return slot 0x8497c). The side-stack arm only (the glue's; the a0 = 0 arm is dead in cgif's form): a0 = the
     class-1 frame fs_frame FS 1 jj, the registers the call keeps, and rBI at the returned memory; then the frame
     choice and rp_fwords. rp_entry takes this lemma on its side-stack arm; its script is unchanged. ===== *)
  Lemma rp_stretchB0_F : forall Q, rKB Q -> forall (jj : Z) (m2 : word -> option byte)
      (u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word),
    0 <= jj < fs_M 1 -> rBI (fs_frame FS 1 jj) jj 1 m2 ->
    evtF rsegs RNG Q (MS (mkR (Z_to_bv 64 0x8497c) (Z_to_bv 64 rA) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 rA)
                       (Z_to_bv 64 (fs_frame FS 1 jj)) x1 x2 x3 x4 x5 x6 x7 s2 (Z_to_bv 64 pn) (Z_to_bv 64 pp)
                       (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len) s8 s9 s10 (wa ASAN_K) u3 u4 u5 u6)
                  F (Z_to_bv 64 0x8497c) fc None m2 (seg_rom rsegs)).
  Proof.
    intros Q K jj m2 u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 Hjj HB.
    pose proof rA_facts as (HA32 & HAlo & HAhi).
    destruct rr_fs as (F1 & F2 & F3 & F4 & F5 & _). unfold FS_SIZE in F4.
    pose proof (rrF_fs_frame1 FS jj) as EF.
    assert (EM1 : fs_M 1 = 8192) by reflexivity.
    step. step. step. step.
    rewrite (rc_neq0_64 (fs_frame FS 1 jj)) by (clear - EF EM1 Hjj F1 F4 HS; lia). cbn [negb]. cbv iota.
    eapply (rp_fwords (fs_frame FS 1 jj) (fs_frame FS 1 jj) rA jj 1); [right; repeat split; lia | exact HB | exact K].
  Qed.

  (* 0x848fc .. 0x849ac: the prologue, __asan_stack_malloc_1(128) (the flag at UAR is 1) and the frame choice. *)
  Lemma rp_entry : forall t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 Q (m0 : word -> option byte), m0 = m -> rKB Q ->
    evtF rsegs RNG Q (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fr) (Z_to_bv 64 len) (Z_to_bv 64 pa)
                     (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m0 (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 Q m0 Em0 K.
    unfold REAC_CTRL_IDENTITY_REPLY.
    pose proof rA_facts as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof FP0 as FPm. unfold reac_ctrl_identity_reply_W in FPm.
    assert (MU : munch [(S - 9072, S)] m m0) by (subst m0; apply munch_refl).
    assert (WM : wmono rsegs m m0) by (subst m0; apply wmono_refl).
    assert (RM : rr_rd_mono m m0) by (subst m0; apply rr_rd_mono_refl).
    assert (MI0 : mem_inv rsegs m0) by (subst m0; exact MI).
    pose proof AC as (CK & GCK & _ & _ & _ & UA & GUA & _).
    unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
    apply rr_ro8 in CK. apply rr_ro8 in GCK. apply rr_ro4 in UA. apply rr_ro8 in GUA.
    rewrite <- Em0 in CK, GCK, UA, GUA.
    pose proof ST as ST0c. rewrite <- Em0 in ST0c.
    pose proof (stk_split rsegs m0 _ (S - 104) _ ST0c ltac:(lia)) as [STw STs].
    pose proof (stk_split rsegs m0 _ (S - 128) _ STw ltac:(lia)) as [STw2 STz].
    clear ST0c.
    carve_frame 104%nat STs.
    carve_frame 24%nat STz.
    step.
    step.
    rsteps_to 0x8493c.
    step.
    assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (S + -128))) 18446744073709551584 = rA)
      by (rewrite unsigned_lit, rr_land_align32 by lia; unfold rA; f_equal; f_equal; lia).
    rewrite EA.
    rsteps_to 0x84970.
    step.
    replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
    step. step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    pose proof (fl_fp [1%nat] m m1 _ FS _ _ _ _ _ FPm MU WM ltac:(intros x Hx; exact Hx)) as FP1.
    destruct FP1 as (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HAPP & HWd & HDd).
    pose proof HCL as HCL0. apply Forall_cons_iff in HCL0.
    destruct HCL0 as [(_ & h & flags & HH & HFl & HFln & HFb) _].
    pose proof HWd as Hw0. unfold fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
    cbn [fp_tls app] in Hw0.
    repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
    pose proof HFS as HFS'. unfold FS_SIZE in HFS'.
    pose proof (stk_merge rsegs m1 _ _ _ STw2 STz ltac:(lia)) as STzc.
    destruct (stk_split rsegs m1 _ rA _ STzc ltac:(lia)) as [STA _].
    pose proof MALLOC as HM. unfold asan_stack_malloc_1_contract_F_on, asan_stack_malloc_contract_F_on in HM.
    cbv zeta in HM.
    specialize (HM (proj1 (Nat.leb_le 1 10) eq_refl)).
    pose proof rr_fs as (FS0 & _).
    eapply evtF_cut.
    { destruct (rrF_tls_rng RNG _ DT TS C T DB k
                  (rrF_tls m1 [(S - 9072, S)] MU
                     ltac:(intros xq Hxq; apply rr_out_app_inv in Hxq as [Hxq _];
                           unfold reac_ctrl_identity_reply_W, REAC_CTRL_IDENTITY_REPLY_K in Hxq;
                           cbn [outside] in Hxq |- *; split; [exact (proj1 Hxq) | exact I])
                     DT TS C T DB k HT))
        as (RTdt & RTts & RTc & RTt & RTdb & RTp88 & RTp8).
      eapply HM with (lo := S - 9072) (FS := FS) (h := h) (DT := DT) (TS := TS) (C := C) (T := T)
        (DB := DB) (k := k) (flags := flags); unfold ASAN_STACK_MALLOC_K; rewrite ?(unsigned_lit rA) by lia.
      - rewrite unsigned_lit by lia. unfold fs_B. cbn. lia.
      - rewrite unsigned_lit by lia. reflexivity.
      - exact (fl_asan_cells _ m m1 AC MU ltac:(intros x Hx; cbn [outside]; unfold RT_LO, RT_HI in Hx; split; [lia | exact I])).
      - exact (shadow_rw_on_mono _ _ m1 rr_malloc_inR (rr_shadow_rw_on_mono _ m m1 SW WM RM)).
      - exact MI0.
      - exact HT.
      - intros Hc. lia.
      - exact HTP.
      - exact HP.
      - exact H88.
      - exact H96.
      - exact HH.
      - exact HFl.
      - exact HFln.
      - exact HFb.
      - exact STA.
      - lia.
      - lia.
      - intros a Ha. apply HAPP. lia.
      - cbn [disjoint_from].
        repeat split; try exact I;
          match goal with |- _ + _ <= ?lo \/ ?hi <= _ =>
            match goal with Hd : ly_dj _ _ lo hi |- _ => unfold ly_dj in Hd; lia end end.
      - (* the image *) unfold lib.B.Prog.ImgBounds.IMG_LO, lib.B.Prog.ImgBounds.IMG_HI. exact RIMG.
      - (* the callee's window [rA - 208, rA) inside this function's window *)
        eapply rng_sub; [exact RWIN | lia | lia].
      - (* the runtime pointer cell at DT + 8 *) exact RTdt.
      - (* the runtime pointer cell at TS + 8 k *) exact RTts.
      - (* the runtime pointer cell at C + 152 *) exact RTc.
      - (* the runtime pointer cells at T + 48 *) exact RTt.
      - (* the runtime pointer cell at DB + 24 *) exact RTdb.
      - (* the side stack's header *) exact RFSS.
      - (* the class-1 frame area, from the frames' range in fp_w [1%nat] FS *) exact (rrF_frame_area RNG FS RW1).
      - (* the shadow of the class-1 frame area *) exact (rrF_frame_sh RNG FS RW1).
      - (* the thread-pointer cell at TP - 88 *) exact RTp88.
      - (* the thread-pointer cells at TP - 8 .. TP + 16 *) exact RTp8. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & u3 & u4 & u5 & u6 & m2 & E & WM2 & MI2 & ST2
                    & HP2 & (h2 & HH2) & ALT).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 0x8497c)) with (Z_to_bv 64 0x8497c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite (unsigned_lit rA) in ST2 by lia. unfold ASAN_STACK_MALLOC_K in *.
    unfold fs_hint in HH2. cbn [Z.of_nat] in HH2.
    pose proof HP as (P1 & P2 & P3 & P4 & P5). unfold ASAN_GT in P3. unfold FS_SIZE in P4, P5.
    destruct ALT as [(Hall & Ex0 & MU2) | (i & Hi & Hpre & Hnth & FRM)].
    - (* the real-stack frame [rA - 128, rA) *)
      subst x0. rewrite (unsigned_lit rA) in MU2 by lia. unfold fs_hint in MU2. cbn [Z.of_nat] in MU2.
      assert (RM2 : rr_rd_mono m1 m2).
      { apply (rr_rd_mono_list _ _ _ MU2). constructor; [|constructor; [|constructor]]; cbn [fst snd].
        - intros y Hy. apply (rr_rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
        - intros y Hy. apply (rr_rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch (rWf (rA - 128) 0 0) m m2).
      { apply (munch_trans _ m m1 m2).
        - eapply munch_weaken; [|exact MU]. unfold sub_fp, rWf, fs_hint. cbn [outside]. intros. repeat split; try exact I; lia.
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp, rWf, fs_hint. cbn [outside]. intros. repeat split; try exact I; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rr_rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add]; lia)) as FR2.
      clear MU MU2 WM WM2 RM RM2 FR FR0 STA STw STs STz STw2 STzc MI0.
      unfold rWf, shadow_addr in MU3.
      step. step. step. step.
      replace (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false by reflexivity. cbv iota.
      step. step. step.
      match goal with |- context [Z.land ?x 18446744073709551584] =>
        replace (Z.land x 18446744073709551584) with (rA - 128)
          by (rewrite ?(unsigned_lit rA), ?unsigned_lit by lia; rewrite rr_land_align32 by lia;
              Z.div_mod_to_equations; lia) end.
      step.
      assert (HSp : store_ok rsegs m2 (wa (rA - 4096)) 8 = true)
        by (eapply rr_wv_store_ok with (m := m2);
              [ intros i Hi; apply (rr_stk_wv m2 (S - 9072) rA); [exact ST2 | lia] | apply wmono_refl | lia | lia ]).
      rewrite (unsigned_lit rA) by lia.
      step. store_done.
      step.
      rewrite (rc_lts_signed (rA - 128) (rA - 4096)) by lia.
      replace (rA - 128 <? rA - 4096) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      step.
      eapply (rp_fwords (rA - 128) 0 (rA - 128) 0 0); [left; repeat split; lia | | exact K].
      unfold rBI. refine (conj _ (conj WM3 (conj RM3 (conj MI2 (conj _ _))))).
      + unfold rWf, shadow_addr. exact MU3.
      + unfold rSAVES. replace (S - 104) with (S + -104) by lia. exact FR2.
      + intros E; discriminate.
    - (* the side-stack frame fs_frame FS 1 jj *)
      unfold asan_stack_malloc_frame in FRM. cbv zeta in FRM.
      rewrite (unsigned_lit rA) in FRM by lia.
      replace (fs_B 1) with 128 in FRM by reflexivity.
      change (bv_unsigned (Z_to_bv 64 128)) with 128 in FRM.
      replace (fs_shadow_n 1 128) with 16 in FRM by reflexivity.
      destruct FRM as (Ex0 & Hm64 & _ & HFLg & H24 & H120 & HSH & HADD & STF & APF & FSlo & FShi & GT & FRA' & DIS
                       & MU2).
      remember ((bv_unsigned h + i) mod fs_M 1) as jj eqn:Ejj.
      assert (Hjj : 0 <= jj < fs_M 1) by (subst jj; apply Z.mod_pos_bound; reflexivity).
      remember (fs_frame FS 1 jj) as fra eqn:Efr.
      subst x0. unfold fs_hint in MU2. cbn [Z.of_nat] in MU2.
      unfold ASAN_GT in GT. unfold FS_SIZE in FShi.
      assert (EM1 : fs_M 1 = 8192) by reflexivity.
      rewrite EM1 in Hjj.
      assert (SHb : shadow_addr fra + 16 <= S - 9072)
        by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
      assert (EFl : fs_flag FS 1 jj = FS + 20480 + jj)
        by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; lia).
      assert (RM2 : rr_rd_mono m1 m2).
      { apply (rr_rd_mono_list _ _ _ MU2).
        repeat constructor; cbn [fst snd]; intros y Hy.
        - apply (rr_rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
        - apply (rr_rd_of_bytes _ _ _ HFLg). cbn. lia.
        - apply (rr_rd_of_bytes _ _ _ H24). rewrite length_le8. cbn. lia.
        - apply (rr_rd_of_bytes _ _ _ H120). rewrite length_le8. cbn. lia.
        - apply (rr_rd_of_bytes _ _ _ HSH). rewrite repeat_length, Z2Nat.id by lia. lia.
        - apply (rr_rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch (rWf fra jj 1) m m2).
      { apply (munch_trans _ m m1 m2).
        - eapply munch_weaken; [|exact MU]. unfold sub_fp, rWf, fs_hint. cbn [outside]. intros x Hout.
          repeat split; try exact I; clear -Hout HAlo HAhi HSK; lia.
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp, rWf, fs_hint. cbn [outside]. intros x Hout.
          repeat split; try exact I; clear -Hout HAlo HAhi HSK; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rr_rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2
        ltac:(cbn [disjoint_from cells_size csize Nat.add]; rewrite EFl;
              clear -HFS' FShi Hjj SHb HAlo HAhi HSK; lia)) as FR2.
      clear MU MU2 WM WM2 RM RM2 FR FR0 STA STw STs STz STw2 STzc MI0.
      rewrite Efr. apply (rp_stretchB0_F Q K jj m2); [rewrite EM1; exact Hjj |]. rewrite <- Efr.
      unfold rBI. refine (conj _ (conj WM3 (conj RM3 (conj MI2 (conj _ _))))).
      + exact MU3.
      + unfold rSAVES. replace (S - 104) with (S + -104) by lia. exact FR2.
      + intros _. split; [replace (fra + 120) with (fra + 128 - 8) by lia; exact H120 | exact HFLg].
  Qed.

  (* ===== The cut at the fake-stack call (bF-glue.md: the run split at the call, so the cgif-form glue
     lib/B/Prog/C_reac_ctrl_identity_reply.v lifts the stretch BEFORE it through the kit bridge and takes
     __asan_stack_malloc_1 by cgif's astack_malloc_realizes instead of walking it). rp_entry is unchanged; this is
     its prefix, by the same script, stated in the bridge's form (ExecF.evtF with a post on the reached state). ===== *)

  (* The state of the memory at the callee's first slot: what the prologue wrote and what the stretch after the
     call still needs (the saved registers, the frame slot, the runtime's cells, the window below the frame). *)
  Definition rMCALL (mc : word -> option byte) : Prop :=
    munch [(S - 9072, S)] m mc /\ wmono rsegs m mc /\ rr_rd_mono m mc /\ mem_inv rsegs mc /\
    ro_cells rsegs mc CELL_K [C8 (wa ASAN_K)] /\ ro_cells rsegs mc GOT_CELL_K [C8 (wa CELL_K)] /\
    ro_cells rsegs mc UAR [C4 (wa 1)] /\ ro_cells rsegs mc GOT_UAR [C8 (wa UAR)] /\
    stk rsegs mc (S - 9072) (S - 128) /\
    rw_cells rsegs mc (S - 104) rSAVES /\
    (exists junk, rw_cells rsegs mc (S - 128) [C8 (Z_to_bv 64 0); CB 16 junk]).

  (* 0x848fc .. the first slot of __asan_stack_malloc_1 (0x3d868): the prologue, the realignment to rA, the UAR
     test (the cell is 1, so the fallback arm is not taken here) and the call. a0 = 128 is the frame size, a1 the
     runtime's cell, a2 the UAR value, s11 the shadow offset; ra = 0x8497c is the return slot the stretch after the
     call starts from. *)
  Lemma rp_stretchA_F : forall t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 (m0 : word -> option byte), m0 = m ->
    evtF rsegs RNG
      (fun ms' => exists mc : word -> option byte, rMCALL mc /\
         ms' = MS (mkR (Z_to_bv 64 0x8497c) (Z_to_bv 64 rA) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 rA)
                       (Z_to_bv 64 128) (wa CELL_K) (sx32 (wa 1)) (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7
                       s2 (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len)
                       s8 s9 s10 (wa ASAN_K) t3 t4 t5 t6)
                  F (Z_to_bv 64 ASAN_STACK_MALLOC_1) fc None mc (seg_rom rsegs))
      (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fr) (Z_to_bv 64 len) (Z_to_bv 64 pa)
               (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m0 (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 m0 Em0.
    unfold REAC_CTRL_IDENTITY_REPLY.
    pose proof rA_facts as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (MU : munch [(S - 9072, S)] m m0) by (subst m0; apply munch_refl).
    assert (WM : wmono rsegs m m0) by (subst m0; apply wmono_refl).
    assert (RM : rr_rd_mono m m0) by (subst m0; apply rr_rd_mono_refl).
    assert (MI0 : mem_inv rsegs m0) by (subst m0; exact MI).
    pose proof AC as (CK & GCK & _ & _ & _ & UA & GUA & _).
    unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
    apply rr_ro8 in CK. apply rr_ro8 in GCK. apply rr_ro4 in UA. apply rr_ro8 in GUA.
    rewrite <- Em0 in CK, GCK, UA, GUA.
    pose proof ST as ST0c. rewrite <- Em0 in ST0c.
    pose proof (stk_split rsegs m0 _ (S - 104) _ ST0c ltac:(lia)) as [STw STs].
    pose proof (stk_split rsegs m0 _ (S - 128) _ STw ltac:(lia)) as [STw2 STz].
    clear ST0c.
    carve_frame 104%nat STs.
    carve_frame 24%nat STz.
    step.
    step.
    rsteps_to 0x8493c.
    step.
    assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (S + -128))) 18446744073709551584 = rA)
      by (rewrite unsigned_lit, rr_land_align32 by lia; unfold rA; f_equal; f_equal; lia).
    rewrite EA.
    rsteps_to 0x84970.
    step.
    replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
    step. step.
    apply evtF_done. cbv beta.
    eexists. split; [|reflexivity].
    unfold rMCALL, CELL_K, GOT_CELL_K, UAR, GOT_UAR.
    split; [exact MU|]. split; [exact WM|]. split; [exact RM|]. split; [exact MI0|].
    split; [exact CK|]. split; [exact GCK|]. split; [exact UA|]. split; [exact GUA|].
    split; [exact STw2|].
    split; [unfold rSAVES; replace (S - 104) with (S + -104) by lia; exact FR|].
    eexists. replace (S - 128) with (S + -128) by lia. exact FR0.
  Qed.


  (* ===== The run's footprints and the state that the exits share ===== *)

  Lemma rr_fsn : 0 < FS /\ FS mod 4096 = 0 /\ 6283264 <= FS /\ FS + 11571200 <= S - 9072 /\
    (forall a, FS <= a < FS + 11571200 -> app_mem a) /\ (FS + 11571200 <= 2147450880 \/ 17594333495296 <= FS).
  Proof.
    destruct rr_fs as (P1 & P2 & P3 & P4 & P5 & _). unfold ASAN_GT, FS_SIZE in *.
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P5|].
    apply (rr_app_range FS 11571200); [lia | intros i Hi; apply P5; lia].
  Qed.

  Definition rWW : list ivl := reac_ctrl_identity_reply_W fr pa pp pn S.
  Definition rDD : list ivl := reac_ctrl_identity_reply_D fr len pa pp pn.
  Definition rYY : list ivl := [(shadow_addr (S - 9072), shadow_addr S)].
  (* The writes of every path before the stores to the OUT pointers, and the run's footprint (the contract's). *)
  Definition rWB : list ivl := (S - 9072, S) :: fp_w [1%nat] FS ++ rYY.
  Definition rWP : list ivl := reac_ctrl_identity_reply_fp fr len pa pp pn S g ++ fp_w [1%nat] FS ++ rYY.

  Lemma rWB_WP : sub_fp rWB rWP.
  Proof.
    intros x Hx. unfold rWP, rWB, reac_ctrl_identity_reply_fp, REAC_CTRL_IDENTITY_REPLY_K in *.
    apply rr_out_app_inv in Hx as [H1 H2]. apply rr_out_app_inv in H1 as [_ H1].
    cbn [outside] in H1 |- *. destruct H1 as [H1 _]. split; [exact H1 | exact H2].
  Qed.

  Lemma rWP_full : sub_fp rWP (rWW ++ fp_w [1%nat] FS ++ rYY).
  Proof.
    intros x Hx. unfold rWP, rWW, reac_ctrl_identity_reply_fp, reac_ctrl_identity_reply_W,
      REAC_CTRL_IDENTITY_REPLY_K in *.
    apply rr_out_app_inv in Hx as [H1 H2]. cbn [outside app] in H1. destruct H1 as [H0 H1].
    apply fl_out_app; [|exact H2]. apply fl_out_app; [|cbn [outside]; split; [exact H0 | exact I]].
    unfold reply_ok. destruct (reply_args fr pa pp pn); cbn [andb]; [destruct (ir len g); [exact H1 | exact I] | exact I].
  Qed.

  Lemma rWB_full : sub_fp rWB (rWW ++ fp_w [1%nat] FS ++ rYY).
  Proof. intros x Hx. apply rWB_WP, rWP_full, Hx. Qed.

  Definition rAWX (G : Z) (mc : word -> option byte) : Prop :=
    forall x, S - 9072 <= x < S -> (x < G \/ G + 128 <= x) -> addr_byte mc x.

  Definition rOUTF (mc : word -> option byte) : Prop :=
    rw_cells rsegs mc pa [CB 2 (reply_addr g)] /\ rw_cells rsegs mc pp [CB 8 (le8 (Z_to_bv 64 (fr + 38)))] /\
    rw_cells rsegs mc pn [CB 8 (le8 (Z_to_bv 64 (ir_s g - 13)))].

  (* What every state of the run keeps: the saved registers, the window addressable apart from the frame, fp and
     tls, and (side frame) the flag-pointer word at G + 120 with the frame's flag byte 1. *)
  Definition rCore (G j nn : Z) (mc : word -> option byte) : Prop :=
    wmono rsegs m mc /\ rr_rd_mono m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (S - 104) rSAVES /\ rAWX G mc /\
    fp [1%nat] mc (bv_unsigned tp) FS (S - 9072) S rWW rDD /\
    reac_ctrl_identity_reply_tls mc (bv_unsigned tp) FS (S - 9072) S /\
    (nn = 1 -> bytes_at rsegs mc (G + 120) (le8 (Z_to_bv 64 (fs_flag FS 1 j))) /\
               bytes_at rsegs mc (fs_flag FS 1 j) [Z_to_bv 8 1]).

  (* The state at the epilogue's entry: the writes inside the run's footprint, and rCore. *)
  Definition rEI0 (G j nn : Z) (mc : word -> option byte) : Prop := munch rWP m mc /\ rCore G j nn mc.

  (* The frame's place: in the window below rA (real) or a class-1 frame of the side stack. *)
  Lemma rk_place : forall G fv spc j nn, rFK G fv spc j nn ->
    (nn = 0 /\ G = rA - 128) \/ (nn = 1 /\ 0 <= j < 8192 /\ G = FS + 1085440 + j * 128).
  Proof.
    intros G fv spc j nn [(_ & EG & _ & _ & En)|(Hj & EG & _ & _ & En)]; [left; split; assumption|right].
    destruct (rr_fsnum FS j) as (E1 & _ & _ & E4). rewrite E4 in Hj. rewrite E1 in EG. split; [exact En|]. split; [exact Hj | exact EG].
  Qed.

  Lemma rWf_WB : forall G fv spc j nn, rFK G fv spc j nn -> sub_fp (rWf G j nn) rWB.
  Proof.
    intros G fv spc j nn HK x Hx.
    pose proof rA_facts as (HA32 & HAlo & HAhi).
    destruct (rk_facts G fv spc j nn HK) as (FR8 & _).
    unfold rWB, rYY in Hx. rewrite rr_fpw in Hx. cbn [outside app] in Hx.
    destruct Hx as (H0 & H1 & H2 & H3 & H4 & H5 & _).
    destruct (rr_fsnum FS j) as (_ & E2 & E3 & _).
    unfold rWf. rewrite E2, E3. cbn [outside].
    pose proof (rr_sh_add8 G 16 FR8) as ESG. replace (G + 8 * 16) with (G + 128) in ESG by lia.
    destruct (rk_place G fv spc j nn HK) as [(En & EG)|(En & Hj & EG)]; subst nn.
    - split; [exact H0|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact I].
      rewrite <- ESG. intros [L1 L2]. apply H5. split.
      + pose proof (rr_sh_ge G (S - 9072) ltac:(lia)). lia.
      + pose proof (rr_sh_ge S (G + 128) ltac:(lia)). lia.
    - split; [exact H0|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact I].
      rewrite <- ESG. intros [L1 L2]. apply H4. split.
      + pose proof (rr_sh_ge G (FS + 1085440) ltac:(lia)). lia.
      + pose proof (rr_sh_ge (FS + 2134016) (G + 128) ltac:(lia)). lia.
  Qed.

  (* The shadow byte of a window byte apart from the frame is apart from the prologue's writes. *)
  Lemma rr_sh_out_Wf : forall G fv spc j nn x, rFK G fv spc j nn -> S - 9072 <= x < S -> (x < G \/ G + 128 <= x) ->
    outside (rWf G j nn) (shadow_addr x).
  Proof.
    intros G fv spc j nn x HK Hx HxG.
    pose proof rA_facts as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & _).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    assert (Hap : app_mem x) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; pose proof HAE; lia).
    pose proof (rt_app_shadow x Hap) as Hsh.
    destruct (rr_fsnum FS j) as (_ & E2 & E3 & _).
    unfold rWf. rewrite E2, E3. cbn [outside].
    pose proof (rr_sh_add8 G 16 FR8) as ESG. replace (G + 8 * 16) with (G + 128) in ESG by lia.
    assert (Hj0 : 0 <= j /\ j + nn <= 8192)
      by (destruct (rk_place G fv spc j nn HK) as [(En & _)|(En & Hj & _)]; [subst nn; destruct HK as [(_ & _ & _ & Ej & _)|(Hj' & _)]; [lia|]; destruct (rr_fsnum FS j) as (_ & _ & _ & E4); lia | lia]).
    split; [apply (rr_sh_notapp _ _ _ Hsh); intros z Hz; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; pose proof HAE; lia|].
    split; [apply (rr_sh_notapp _ _ _ Hsh); intros z Hz; apply F5; lia|].
    split; [apply (rr_sh_notapp _ _ _ Hsh); intros z Hz; apply F5; lia|].
    split; [apply (rr_sh_notapp _ _ _ Hsh); intros z Hz; replace z with (G + (z - G)) by lia; apply FAP; lia|].
    split; [|exact I]. rewrite <- ESG. apply rr_win_sh; [exact FR8 | lia].
  Qed.

  Lemma rr_awx_munch : forall G W mc mc', rAWX G mc -> munch W mc mc' ->
    (forall x, S - 9072 <= x < S -> (x < G \/ G + 128 <= x) -> outside W (shadow_addr x)) -> rAWX G mc'.
  Proof.
    intros G W mc mc' HA MU HOW x Hx HxG. destruct (HA x Hx HxG) as (Hap & b & Hb & Hok).
    split; [exact Hap|]. exists b. split; [|exact Hok].
    pose proof (rt_shadow_bound _ (rt_app_shadow x Hap)) as Hbd.
    rewrite (rr_munch_mrd_out W mc mc' (shadow_addr x) MU ltac:(lia) (HOW x Hx HxG)). exact Hb.
  Qed.

  Lemma rr_awx_m : forall G, rAWX G m.
  Proof.
    intros G x Hx _. destruct AW as (_ & _ & _ & HA). replace x with (S - 9072 + (x - (S - 9072))) by lia.
    apply HA. lia.
  Qed.

  (* The class-1 flag array after the prologue: m's, with byte j set to 1 when the side frame j was taken. *)
  Lemma rr_flags_BI : forall G fv spc j nn mc, rFK G fv spc j nn -> munch (rWf G j nn) m mc ->
    (nn = 1 -> bytes_at rsegs mc (fs_flag FS 1 j) [Z_to_bv 8 1]) ->
    exists flags', bytes_at rsegs mc (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags'.
  Proof.
    intros G fv spc j nn mc HK MU HFJ.
    pose proof rA_facts as (HA32 & HAlo & HAhi).
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & _).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & _ & _ & _ & HCL & _).
    apply Forall_inv in HCL. destruct HCL as (_ & h & flags & _ & HFl & HFln & HFb).
    destruct (rr_fsnum FS 0) as (_ & E2 & _ & E4).
    assert (OUTF : forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1 -> (nn = 0 \/ x <> fs_flag FS 1 j) ->
              outside (rWf G j nn) x).
    { intros x Hx Hxj. rewrite E2, E4 in Hx.
      destruct (rr_fsnum FS j) as (_ & E2j & E3 & _).
      assert (Hap : app_mem x) by (apply F5; lia).
      unfold rWf. rewrite E3. cbn [outside].
      split; [lia|]. split; [lia|]. split.
      { destruct (rk_place G fv spc j nn HK) as [(En & _)|(En & _)]; subst nn; [lia|].
        destruct Hxj as [Hxj|Hxj]; [discriminate|]. rewrite E2j in Hxj. lia. }
      split; [lia|]. split; [|exact I].
      pose proof (rr_sh_add8 G 16 FR8) as ESG. replace (G + 8 * 16) with (G + 128) in ESG by lia.
      rewrite <- ESG. apply rr_sh_out; [exact Hap | lia | pose proof HAE; lia]. }
    destruct (rk_place G fv spc j nn HK) as [(En & EG)|(En & Hj & EG)].
    - exists flags. split; [|split; [exact HFln | exact HFb]].
      eapply fl_bytes; [exact HFl | exact MU |]. intros x Hx. rewrite HFln in Hx. apply OUTF; [exact Hx | left; exact En].
    - subst nn. destruct (HFJ eq_refl) as (_ & _ & HB1).
      apply (rr_flags_set m mc FS j (Z_to_bv 8 1) flags); [rewrite E4; lia | right; reflexivity | exact HFl | exact HFln
        | exact HFb | |].
      + specialize (HB1 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in HB1. exact HB1.
      + intros x Hx Hxj. assert (Hbd : 0 <= x < 2^64) by (rewrite E2, E4 in Hx; pose proof HAE; unfold APPMEM_END in *; lia).
        exact (rr_munch_mrd_out _ m mc x MU Hbd (OUTF x Hx (or_intror Hxj))).
  Qed.


  (* The exits' state from the prologue's (rp_null's exit and rp_parse's call). *)
  Lemma rCore_of_BI : forall G fv spc j nn mc, rFK G fv spc j nn -> rBI G j nn mc -> rCore G j nn mc.
  Proof.
    intros G fv spc j nn mc HK (MU & WM & RM & MI1 & SV & H120).
    pose proof rA_facts as (HA32 & HAlo & HAhi).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & _).
    pose proof (rWf_WB G fv spc j nn HK) as HWB.
    assert (HFULL : sub_fp (rWf G j nn) (rWW ++ fp_w [1%nat] FS ++ rYY)) by (intros x Hx; apply HWB, rWB_full, Hx).
    assert (TLSm : forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
              fp_dj (fp_tls (bv_unsigned tp) DT TS C T DB k) (fp_w [1%nat] FS ++ rYY)) by exact TLS0.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (P1 & P2 & P3 & P4 & P5) & _).
    pose proof (rr_stk_mono m mc _ _ P5 WM RM) as STF. unfold FS_SIZE in STF.
    assert (O88 : forall x, FS + 80 <= x < FS + 104 -> outside (rWf G j nn) x).
    { intros x Hx. assert (Hap : app_mem x) by (apply F5; lia).
      destruct (rr_fsnum FS j) as (_ & E2 & E3 & _).
      unfold rWf. rewrite E2, E3. cbn [outside].
      assert (Hj0 : 0 <= j) by (destruct (rk_place G fv spc j nn HK) as [(_ & _)|(_ & Hj & _)];
        [destruct HK as [(_ & _ & _ & Ej & _)|(Hj' & _)]; [lia|]; destruct (rr_fsnum FS j) as (_ & _ & _ & E4); lia | lia]).
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact I].
      pose proof (rr_sh_add8 G 16 FR8) as ESG. replace (G + 8 * 16) with (G + 128) in ESG by lia.
      rewrite <- ESG. apply rr_sh_out; [exact Hap | lia | pose proof HAE; lia]. }
    split; [exact WM|]. split; [exact RM|]. split; [exact MI1|]. split; [exact SV|].
    split; [exact (rr_awx_munch G _ m mc (rr_awx_m G) MU (fun x Hx HxG => rr_sh_out_Wf G fv spc j nn x HK Hx HxG))|].
    split.
    { apply (rr_fp_free [1%nat] m mc (bv_unsigned tp) FS (S - 9072) S rWW rDD (rWf G j nn) FP0 TLSm MU WM HFULL O88).
      - intros x Hx. right. exact (rr_rd_of_stk mc _ _ STF x ltac:(unfold FS_SIZE in Hx; lia)).
      - intros c Hc. cbn [In] in Hc. destruct Hc as [<-|[]]. split.
        + apply rr_rd8_le8; [unfold fs_hint; cbn [Z.of_nat]; lia | unfold fs_hint; cbn [Z.of_nat]; pose proof HAE; unfold APPMEM_END in *; lia |].
          intros i Hi. apply (rr_rd_of_stk mc _ _ STF). unfold fs_hint; cbn [Z.of_nat]; lia.
        + exact (rr_flags_BI G fv spc j nn mc HK MU (fun E => proj2 (H120 E))). }
    split.
    { exact (rr_tls_ret [1%nat] m mc (bv_unsigned tp) FS (S - 9072) S rWW rDD rYY (rWf G j nn) FP0 TLSm MU HFULL). }
    exact H120.
  Qed.

  Lemma rEI0_of_BI : forall G fv spc j nn mc, rFK G fv spc j nn -> rBI G j nn mc -> rEI0 G j nn mc.
  Proof.
    intros G fv spc j nn mc HK HB. split; [|exact (rCore_of_BI G fv spc j nn mc HK HB)].
    destruct HB as (MU & _).
    exact (munch_weaken _ _ m mc (fun x Hx => rWf_WB G fv spc j nn HK x (rWB_WP x Hx)) MU).
  Qed.

  (* The epilogue's entry 0x84bdc (a0 = r, the return value). *)
  Definition rKE (Q : machine_state -> Prop) : Prop :=
    forall G fv spc j nn mc r (x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30
                              x31 : word),
      rFK G fv spc j nn -> rEI0 G j nn mc -> (reply_ok fr len pa pp pn g = true -> rOUTF mc) ->
      r = reply_ret fr len pa pp pn g ->
      evtF rsegs RNG Q (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 fv) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) x27
                        x28 x29 x30 x31) F (Z_to_bv 64 0x84bdc) fc None mc (seg_rom rsegs)).

  (* 0x84a3c: the four pointers are not null. *)
  Definition rKN (Q : machine_state -> Prop) : Prop :=
    forall (G fv spc j nn : Z) (mc : word -> option byte)
           (rr x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      rFK G fv spc j nn -> rBI G j nn mc -> reply_args fr pa pp pn = true ->
      evtF rsegs RNG Q (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 rA)
                         (Z_to_bv 64 (-1)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 pn)
                         (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len) s8
                         (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) (wa ASAN_K) x28 x29 x30 x31)
                    F (Z_to_bv 64 0x84a3c) fc None mc (seg_rom rsegs)).

  (* ===== Segment 2: the null tests (+0x130 .. +0x140 = 0x84a2c .. 0x84a3c): a null fr, pa, pp or pn goes to the
     epilogue 0x84bdc with a0 = -1. ===== *)
  Lemma rp_null : forall Q, rKE Q -> rKN Q -> rKB Q.
  Proof.
    intros Q KE KN G fv spc j nn mc rr x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HK HB.
    pose proof (rEI0_of_BI G fv spc j nn mc HK HB) as EI.
    destruct (reply_args fr pa pp pn) eqn:RAb.
    - pose proof RAb as RA. unfold reply_args in RA. rewrite !andb_true_iff, !negb_true_iff, !Z.eqb_neq in RA.
      destruct RA as [[[Rf Ra] Rp] Rn].
      step. rewrite (rc_beq0_false fr Rf) by lia. cbv iota.
      step. rewrite (rc_beq0_false pa Ra) by lia. cbv iota.
      step. rewrite (rc_beq0_false pp Rp) by lia. cbv iota.
      step. rewrite (rc_beq0_false pn Rn) by lia. cbv iota.
      exact (KN G fv spc j nn mc rr x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HK HB RAb).
    - assert (OK : reply_ok fr len pa pp pn g = false) by (unfold reply_ok; rewrite RAb; reflexivity).
      assert (RV : -1 = reply_ret fr len pa pp pn g) by (unfold reply_ret; rewrite RAb; reflexivity).
      assert (KX : forall (x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30
                           x31 : word),
        evtF rsegs RNG Q (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (-1)) x11 x12 x13 x14 x15 x16 x17
                           (Z_to_bv 64 fv) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) x27
                           x28 x29 x30 x31) F (Z_to_bv 64 0x84bdc) fc None mc (seg_rom rsegs)))
        by (intros; apply (KE G fv spc j nn mc (-1)); [exact HK | exact EI | rewrite OK; discriminate | exact RV]).
      step.
      destruct (Z.eq_dec fr 0) as [Z0|Z0].
      { rewrite (rc_beq0_true fr Z0). cbv iota. apply KX. }
      rewrite (rc_beq0_false fr Z0) by lia. cbv iota. step.
      destruct (Z.eq_dec pa 0) as [Z1|Z1].
      { rewrite (rc_beq0_true pa Z1). cbv iota. apply KX. }
      rewrite (rc_beq0_false pa Z1) by lia. cbv iota. step.
      destruct (Z.eq_dec pp 0) as [Z2|Z2].
      { rewrite (rc_beq0_true pp Z2). cbv iota. apply KX. }
      rewrite (rc_beq0_false pp Z2) by lia. cbv iota. step.
      destruct (Z.eq_dec pn 0) as [Z3|Z3].
      { rewrite (rc_beq0_true pn Z3). cbv iota. apply KX. }
      exfalso. unfold reply_args in RAb.
      rewrite (proj2 (Z.eqb_neq fr 0) Z0), (proj2 (Z.eqb_neq pa 0) Z1), (proj2 (Z.eqb_neq pp 0) Z2),
        (proj2 (Z.eqb_neq pn 0) Z3) in RAb. discriminate.
  Qed.

  (* ===== Segment 3: the unpoison of the record and the call of reac_ctrl_parse
     (+0x140 .. +0x16c = 0x84a3c .. 0x84a68). ===== *)

  (* The class-1 frame the run holds while it calls reac_ctrl_parse (the free-frame list X of the contract). *)
  Definition rFX (j nn : Z) : list (nat * Z) := if nn =? 1 then [(1%nat, j)] else [].

  (* The data ranges of the contract are apart from the class-1 side-stack bytes (fp's D-disjointness). *)
  Lemma rr_D_dj : forall a b, In (a, b) rDD -> fp_dj [(a, b)] (fp_w [1%nat] FS).
  Proof.
    intros a b Hin. pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDd).
    unfold fp_dj in HDd. rewrite Forall_forall in HDd. pose proof (HDd (a, b) Hin) as H. cbn [fst snd] in H.
    constructor; [exact H | constructor].
  Qed.

  Lemma rr_D_out : forall a b x, In (a, b) rDD -> a <= x < b -> outside (fp_w [1%nat] FS) x.
  Proof. intros a b x Hin Hx. exact (fl_dj_out_r [(a, b)] _ a b x (rr_D_dj a b Hin) (or_introl eq_refl) Hx). Qed.

  Lemma rr_D_fr : reply_args fr pa pp pn = true -> 50 <= len -> In (fr, fr + 50) rDD.
  Proof.
    intros RA HL. unfold rDD, reac_ctrl_identity_reply_D. rewrite RA.
    replace (len <? 50) with false by (symmetry; apply Z.ltb_ge; lia). cbn [app]. left. reflexivity.
  Qed.

  Lemma rr_D_out3 : reply_args fr pa pp pn = true ->
    In (pa, pa + 2) rDD /\ In (pp, pp + 8) rDD /\ In (pn, pn + 8) rDD.
  Proof.
    intros RA. unfold rDD, reac_ctrl_identity_reply_D. rewrite RA.
    split; [|split]; apply in_or_app; right; cbn [In]; [left | right; left | right; right; left]; reflexivity.
  Qed.

  (* A data range apart from the window is apart from the frame. *)
  Lemma rr_apartG : forall G fv spc j nn a b, rFK G fv spc j nn -> In (a, b) rDD -> a < b ->
    (b <= S - 9072 \/ S <= a) -> (b <= G \/ G + 128 <= a).
  Proof.
    intros G fv spc j nn a b HK Hin Hab Hw.
    pose proof rA_facts as (HA32 & HAlo & HAhi). destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    destruct (rk_place G fv spc j nn HK) as [(En & EG)|(En & Hj & EG)]; [subst G; lia|].
    destruct (Z.le_gt_cases b G) as [L|L]; [left; exact L|].
    destruct (Z.le_gt_cases (G + 128) a) as [R|R]; [right; exact R|].
    exfalso. pose proof (rr_D_out a b (Z.max a G) Hin ltac:(lia)) as HOd.
    rewrite rr_fpw in HOd. cbn [outside] in HOd. destruct HOd as (_ & _ & H3 & _). lia.
  Qed.

  (* A byte of the frame or of its shadow is apart from the writes the parse call may make on the side stack. *)
  Lemma rr_fx_out : forall G fv spc j nn x, rFK G fv spc j nn ->
    (G <= x < G + 128 \/ shadow_addr G <= x < shadow_addr G + 16) ->
    outside (fp_wx [1%nat] FS (rFX j nn)) x.
  Proof.
    intros G fv spc j nn x HK Hx.
    pose proof rA_facts as (HA32 & HAlo & HAhi). destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & FRA & _ & _ & _).
    pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
    pose proof (rr_sh_add8 G 16 FR8) as ESG. replace (G + 8 * 16) with (G + 128) in ESG by lia.
    assert (SHX : forall y, shadow_addr G <= y < shadow_addr G + 16 -> in_shadow y).
    { intros y Hy. apply (rr_sh_in G (G + 128)); [lia | exact FRA | unfold APPMEM_END; lia | lia | rewrite ESG; lia]. }
    assert (FSX : forall a b, FS <= a -> b <= FS + 11571200 -> shadow_addr G <= x < shadow_addr G + 16 ->
                  ~ (a <= x < b)).
    { intros a b Ha Hb Hs. apply (rr_sh_notapp _ _ _ (SHX _ Hs)). intros z Hz. apply F5. lia. }
    destruct (rk_place G fv spc j nn HK) as [(En & EG)|(En & Hj & EG)].
    - (* the real frame is in the window, above the whole side stack *)
      subst nn. replace (rFX j 0) with (@nil (nat * Z)) by reflexivity.
      rewrite fp_wx_nil. rewrite rr_fpw. cbn [outside].
      destruct Hx as [Hx|Hx].
      + assert (XAP : app_mem x) by (replace x with (G + (x - G)) by lia; apply FAP; lia).
        split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact I].
        apply rr_sh_out; [exact XAP | lia | unfold APPMEM_END; lia].
      + assert (SHhi : shadow_addr (FS + 2134016) <= shadow_addr G) by (apply rr_sh_ge; lia).
        split; [apply FSX; lia|]. split; [apply FSX; lia|]. split; [apply FSX; lia|]. split; [lia | exact I].
    - (* the side frame j: the hole of fp_wx *)
      subst nn. replace (rFX j 1) with [(1%nat, j)] by reflexivity.
      destruct (rr_fsnum FS j) as (Ej & Ejf & Ejh & EjM).
      destruct (rr_fsnum FS 0) as (E0 & E0f & _ & _).
      destruct (rr_fsnum FS (j + 1)) as (E1 & _ & _ & _).
      destruct (rr_fsnum FS (fs_M 1)) as (EM & _ & _ & EjM').
      assert (EGj : fs_frame FS 1 j = G) by lia.
      assert (EGj1 : fs_frame FS 1 (j + 1) = G + 128) by lia.
      assert (EF0 : fs_frame FS 1 0 = FS + 1085440) by lia.
      assert (EFM : fs_frame FS 1 (fs_M 1) = FS + 2134016) by (rewrite EM, EjM'; lia).
      apply rr_outside_In. intros r Hr.
      unfold fp_wx, fp_wx1 in Hr.
      cbn [flat_map] in Hr. rewrite !app_nil_r in Hr.
      assert (EJS : map snd (filter (fun ci : nat * Z => Nat.eqb (fst ci) 1) [(1%nat, j)]) = [j]) by reflexivity.
      rewrite EJS in Hr. cbn [map] in Hr.
      rewrite EF0, EFM, EGj, EGj1 in Hr.
      apply in_app_or in Hr as [Hr|Hr].
      { cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd].
        - rewrite Ejh. destruct Hx as [Hx|Hx]; [lia|]. apply FSX; lia.
        - rewrite E0f, EjM. destruct Hx as [Hx|Hx]; [lia|]. apply FSX; lia. }
      apply in_app_or in Hr as [Hr|Hr].
      + (* the frame pieces *)
        destruct Hx as [Hx|Hx].
        * exact (rr_cut1_out _ _ G (G + 128) x r Hx Hr).
        * pose proof (cut_ivls_in _ _ _ r Hr) as (Hr1 & Hr2). apply FSX; lia.
      + (* the frame-shadow pieces *)
        destruct Hx as [Hx|Hx].
        * pose proof (cut_ivls_in _ _ _ r Hr) as (Hr1 & Hr2).
          assert (XAP : app_mem x) by (replace x with (G + (x - G)) by lia; apply FAP; lia).
          intros Hin. apply (rr_sh_out x (FS + 1085440) (FS + 2134016)); [exact XAP | lia | unfold APPMEM_END; lia | lia].
        * rewrite <- ESG in Hx. exact (rr_cut1_out _ _ _ _ x r Hx Hr).
  Qed.

  (* The frame's 128 bytes are a stack (the real frame inside the window, the side frame inside the side stack). *)
  Lemma rk_stk : forall G fv spc j nn mc, rFK G fv spc j nn -> wmono rsegs m mc -> rr_rd_mono m mc ->
    stk rsegs mc G (G + 128).
  Proof.
    intros G fv spc j nn mc HK WM RM.
    pose proof rA_facts as (HA32 & HAlo & HAhi). destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    destruct (rk_place G fv spc j nn HK) as [(En & EG)|(En & Hj & EG)].
    - destruct (stk_split rsegs m _ G _ ST ltac:(lia)) as [_ ST1].
      destruct (stk_split rsegs m _ (G + 128) _ ST1 ltac:(lia)) as [ST2 _].
      exact (rr_stk_mono m mc _ _ ST2 WM RM).
    - pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (_ & _ & _ & _ & P5) & _). unfold FS_SIZE in P5.
      destruct (stk_split rsegs m _ G _ P5 ltac:(lia)) as [_ ST1].
      destruct (stk_split rsegs m _ (G + 128) _ ST1 ltac:(lia)) as [ST2 _].
      exact (rr_stk_mono m mc _ _ ST2 WM RM).
  Qed.

  (* The bytes the parse call may write are readable at its return, so the run keeps every byte it could read. *)
  Lemma rr_rd_parse : forall G spc X (mY mp : word -> option byte),
    S - 9072 <= spc - 8800 -> spc <= S -> 0 < G + 32 ->
    munch (reac_ctrl_parse_fp (G + 32) spc ++ fp_wx [1%nat] FS X ++
           [(shadow_addr (spc - 8800), shadow_addr spc)]) mY mp ->
    rw_cells rsegs mp (G + 32) [CB 36 (snd (ctrlparse len g))] ->
    stk rsegs mp (spc - 8800) spc -> fs_place mp FS ->
    shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) mp ->
    addressable mp (spc - 8800) 8800 -> rr_rd_mono mY mp.
  Proof.
    intros G spc X mY mp Hlo Hhi HG0 MU RC STw FSP SRW AWP.
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    pose proof HAE as HAE'. pose proof HHM as HHM'. unfold APPMEM_END, HIGHMEM_BEG in HAE', HHM'.
    pose proof FSP as (_ & _ & _ & FSapp & FSstk). unfold FS_SIZE in FSapp, FSstk.
    assert (WAPP : forall z, S - 9072 <= z < S -> app_mem z).
    { intros z Hz. pose proof (rr_app_in m (S - 9072) 9072 (z - (S - 9072)) AW ltac:(lia)) as Ha.
      replace (S - 9072 + (z - (S - 9072))) with z in Ha by lia. exact Ha. }
    apply (rr_rd_mono_munch _ mY mp MU). intros x Hx.
    assert (E : wa (bv_unsigned x) = x) by (unfold wa; apply Z_to_bv_lit_self).
    rewrite <- E.
    destruct (rr_not_outside_in _ _ Hx) as (r & Hr & Hin).
    apply in_app_or in Hr as [Hr|Hr].
    - unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in Hr.
      rewrite (proj2 (Z.eqb_neq (G + 32) 0) ltac:(lia)) in Hr. cbn [app In] in Hr.
      destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in Hin.
      + eapply (rc_rw_mrd rsegs mp (G + 32) 36 _ _ RC). cbn [Z.of_nat]. lia.
      + exact (rr_rd_of_stk mp _ _ STw _ Hin).
    - apply in_app_or in Hr as [Hr|Hr].
      + assert (HI : ~ outside (fp_w [1%nat] FS) (bv_unsigned x))
          by (intros Ho; exact (outside_In _ _ r (fp_wx_sub_w [1%nat] FS X _ Ho) Hr Hin)).
        destruct (rr_not_outside_in _ _ HI) as (r2 & Hr2 & Hin2).
        rewrite rr_fpw in Hr2. cbn [In] in Hr2.
        destruct Hr2 as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin2.
        * eapply (rr_rd_of_stk mp _ _ FSstk). lia.
        * eapply (rr_rd_of_stk mp _ _ FSstk). lia.
        * eapply (rr_rd_of_stk mp _ _ FSstk). lia.
        * assert (HSh : in_shadow (bv_unsigned x)).
          { apply (rr_sh_in (FS + 1085440) (FS + 2134016)); [lia | lia | unfold APPMEM_END; lia | lia | lia]. }
          exact (proj2 (SRW _ (rr_blk_inR _ Hin2) HSh)).
      + cbn [In] in Hr. destruct Hr as [<-|[]]; cbn [fst snd] in Hin.
        (* the callee's window shadow: readable from `addressable` at its return, not from shadow_rw *)
        apply (rr_addr_sh_rd mp (spc - 8800) 8800 (bv_unsigned x) AWP).
        replace (spc - 8800 + 8800) with spc by ring. exact Hin.
  Qed.

  (* The cells the run keeps at the OUT pointers, and that they stay addressable. *)
  Definition rOUTC (mc : word -> option byte) : Prop :=
    rw_cells rsegs mc pa [CB 2 ja] /\ rw_cells rsegs mc pp [CB 8 jp] /\ rw_cells rsegs mc pn [CB 8 jn] /\
    addressable mc pa 2 /\ addressable mc pp 8 /\ addressable mc pn 8.

  (* The state of the body, from the return of reac_ctrl_parse to the stores. *)
  Definition rJB (G j nn : Z) (mc : word -> option byte) : Prop :=
    munch rWB m mc /\ rCore G j nn mc /\
    rw_cells rsegs mc (G + 32) [CB 36 (snd (ctrlparse len g))] /\
    (50 <= len -> bytes_at rsegs mc fr g /\ addressable mc fr 50) /\ rOUTC mc /\
    stk rsegs mc (S - 9072) S /\ asan_cells mc /\
    shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) mc.

  Lemma rJB_EI0 : forall G j nn mc, rJB G j nn mc -> rEI0 G j nn mc.
  Proof.
    intros G j nn mc (MU & CORE & _). split; [|exact CORE].
    exact (munch_weaken _ _ m mc (fun x Hx => rWB_WP x Hx) MU).
  Qed.

  (* 0x84a68: the return of reac_ctrl_parse (a0 = the kind, s8 = the record at G + 32). *)
  Definition rKF (Q : machine_state -> Prop) : Prop :=
    forall (G fv spc j nn : Z) (mc : word -> option byte)
           (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      rFK G fv spc j nn -> rJB G j nn mc -> reply_args fr pa pp pn = true ->
      evtF rsegs RNG Q (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 rA)
                         (Z_to_bv 64 (fst (ctrlparse len g))) x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 fv) (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa)
                         (Z_to_bv 64 len) (Z_to_bv 64 (G + 32)) (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G)
                         (wa ASAN_K) x28 x29 x30 x31)
                    F (Z_to_bv 64 0x84a68) fc None mc (seg_rom rsegs)).

  (* 0x84a3c .. 0x84a58: s8 = G + 32, then the 5 shadow bytes SG[4 .. 8] = 0, 0, 0, 0, 4 (the 1-byte stores, each
     inside the frame's shadow). *)
  Lemma rr_unp_run : forall (G : Z) (mc : word -> option byte)
      (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31 : word)
      (Q : machine_state -> Prop),
    G mod 8 = 0 -> 0 <= G -> 2147450880 <= G / 8 + ASAN_K -> G / 8 + ASAN_K + 16 <= 17594333495296 ->
    (forall i, 0 <= i < 16 -> wview rsegs mc (wa (G / 8 + ASAN_K + i)) <> None) -> mem_inv rsegs mc ->
    shblk RNG G 15 ->
    (forall m5, munch [(G / 8 + ASAN_K + 4, G / 8 + ASAN_K + 9)] mc m5 -> wmono rsegs mc m5 -> rr_rd_mono mc m5 ->
       mem_inv rsegs m5 ->
       bytes_at rsegs m5 (G / 8 + ASAN_K + 4) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] ->
       evtF rsegs RNG Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 4) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21
                          x22 x23 (Z_to_bv 64 (G + 32)) (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) x27
                          x28 x29 x30 x31)
                    F (Z_to_bv 64 0x84a58) fc None m5 (seg_rom rsegs))) ->
    evtF rsegs RNG Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                       (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x84a3c) fc None mc (seg_rom rsegs)).
  Proof.
    intros G mc x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31 Q
      HG8 HG0 HSlo HShi SWc MIc SBFRM K5.
    assert (HA0 : 0 <= G / 8 + ASAN_K + 4) by (clear - HSlo; lia).
    assert (HA5 : G / 8 + ASAN_K + 4 + 5 <= 2^64) by (clear - HShi; lia).
    assert (Bq : bytes_at rsegs mc (G / 8 + ASAN_K + 4) (@nil byte))
      by (split; [exact HA0|]; split; [cbn [length Z.of_nat]; clear - HA5; lia | intros i Hi; cbn [length] in Hi; lia]).
    pose proof (munch_refl [(G / 8 + ASAN_K + 4, G / 8 + ASAN_K + 4 + 5)] mc) as Mq.
    pose proof (wmono_refl rsegs mc) as Wq. pose proof (rr_rd_mono_refl mc) as Rq. pose proof MIc as Iq. clear MIc.
    step.
    rwstb (G / 8 + ASAN_K + 4) 1%nat (G / 8 + ASAN_K) SWc. step. rewrite rr_le1_0.
    destruct (rr_sb_step mc mc mc (G / 8 + ASAN_K + 4) 5 (@nil byte) (Z_to_bv 8 0) (G / 8 + ASAN_K + 4)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) HA0 HA5 ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; lia)
                Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'. rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    set (m1 := write_to_mem mc (Z_to_bv 64 (G / 8 + ASAN_K + 4)) [Z_to_bv 8 0]) in *. clearbody m1.
    rwstb (G / 8 + ASAN_K + 5) 1%nat (G / 8 + ASAN_K) SWc. step. rewrite rr_le1_0.
    destruct (rr_sb_step mc mc m1 (G / 8 + ASAN_K + 4) 5 [Z_to_bv 8 0] (Z_to_bv 8 0) (G / 8 + ASAN_K + 5)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) HA0 HA5 ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; lia)
                Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'. rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    set (m2 := write_to_mem m1 (Z_to_bv 64 (G / 8 + ASAN_K + 5)) [Z_to_bv 8 0]) in *. clearbody m2.
    rwstb (G / 8 + ASAN_K + 6) 1%nat (G / 8 + ASAN_K) SWc. step. rewrite rr_le1_0.
    destruct (rr_sb_step mc mc m2 (G / 8 + ASAN_K + 4) 5 [Z_to_bv 8 0; Z_to_bv 8 0] (Z_to_bv 8 0) (G / 8 + ASAN_K + 6)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) HA0 HA5 ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; lia)
                Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'. rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    set (m3 := write_to_mem m2 (Z_to_bv 64 (G / 8 + ASAN_K + 6)) [Z_to_bv 8 0]) in *. clearbody m3.
    rwstb (G / 8 + ASAN_K + 7) 1%nat (G / 8 + ASAN_K) SWc. step. rewrite rr_le1_0.
    destruct (rr_sb_step mc mc m3 (G / 8 + ASAN_K + 4) 5 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] (Z_to_bv 8 0) (G / 8 + ASAN_K + 7)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) HA0 HA5 ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; lia)
                Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'. rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    set (m4 := write_to_mem m3 (Z_to_bv 64 (G / 8 + ASAN_K + 7)) [Z_to_bv 8 0]) in *. clearbody m4.
    step.
    rwstb (G / 8 + ASAN_K + 8) 1%nat (G / 8 + ASAN_K) SWc. step. rewrite rr_le1_4.
    destruct (rr_sb_step mc mc m4 (G / 8 + ASAN_K + 4) 5 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] (Z_to_bv 8 4) (G / 8 + ASAN_K + 8)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) HA0 HA5 ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; lia)
                Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'. rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    set (m5 := write_to_mem m4 (Z_to_bv 64 (G / 8 + ASAN_K + 8)) [Z_to_bv 8 4]) in *. clearbody m5.
    replace (G / 8 + ASAN_K + 4 + 5) with (G / 8 + ASAN_K + 9) in Mq by ring.
    exact (K5 m5 Mq Wq Rq Iq Bq).
  Qed.


  (* rBI after the 5 shadow stores (they are inside the frame's shadow, apart from every application byte). *)
  Lemma rr_BI_unp : forall G fv spc j nn mc m5, rFK G fv spc j nn -> rBI G j nn mc ->
    munch [(G / 8 + ASAN_K + 4, G / 8 + ASAN_K + 9)] mc m5 -> wmono rsegs mc m5 -> rr_rd_mono mc m5 ->
    mem_inv rsegs m5 -> rBI G j nn m5.
  Proof.
    intros G fv spc j nn mc m5 HK (MU & WM & RM & MI1 & SV & H120) MU5 WM5 RM5 MI5.
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & FRA & _ & SH1 & SH2).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (OUT5 : forall x, app_mem x -> outside [(G / 8 + ASAN_K + 4, G / 8 + ASAN_K + 9)] x).
    { intros x Hx. replace (G / 8 + ASAN_K + 9) with (G / 8 + ASAN_K + 4 + 5) by ring.
      apply rr_app_out_sh; [exact Hx | clear - SH1; lia | clear - SH2; lia]. }
    split.
    { apply (munch_trans _ m mc m5 MU). eapply munch_weaken; [|exact MU5].
      intros x Hx. unfold rWf, shadow_addr in Hx. cbn [outside] in Hx |- *.
      destruct Hx as (_ & _ & _ & _ & H5 & _). split; [|exact I]. clear - H5. lia. }
    split; [exact (wmono_trans rsegs m mc m5 WM WM5)|].
    split; [exact (rr_rd_mono_trans m mc m5 RM RM5)|].
    split; [exact MI5|].
    split.
    { apply (rr_rw _ mc m5 _ _ SV MU5 WM5). intros x Hx. apply OUT5.
      unfold rSAVES in Hx. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in Hx.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right. clear - Hx HHM' HAE' HSK. lia. }
    intros Hn. destruct (H120 Hn) as (H1 & H2). split.
    - eapply fl_bytes; [exact H1 | exact MU5 |]. intros x Hx. rewrite length_le8 in Hx. apply OUT5.
      replace x with (G + (x - G)) by ring. apply FAP. clear - Hx; lia.
    - eapply fl_bytes; [exact H2 | exact MU5 |]. intros x Hx. cbn [length Z.of_nat Pos.of_succ_nat] in Hx. apply OUT5.
      apply F5. destruct (rk_place G fv spc j nn HK) as [(En & _)|(En & Hj & _)]; [lia|].
      destruct (rr_fsnum FS j) as (_ & E2 & _). rewrite E2 in Hx. clear - Hx Hj. lia.
  Qed.

  (* The callee's window [spc - 8800, spc) is apart from the frame, so rAWX makes it addressable. *)
  Lemma rr_win_addr : forall G fv spc j nn mc, rFK G fv spc j nn -> rAWX G mc -> addressable mc (spc - 8800) 8800.
  Proof.
    intros G fv spc j nn mc HK HA.
    pose proof rA_facts as (HA32 & HAlo & HAhi). destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (Hw : S - 9072 <= spc - 8800 /\ spc <= S /\ (spc <= G \/ G + 128 <= spc - 8800)).
    { destruct HK as [(_ & EG & Esp & _ & _)|(Hj & EG & _ & Esp & _)].
      - subst. clear - HAlo HAhi. lia.
      - destruct (rr_fsnum FS j) as (Ej & _ & _ & EM). rewrite Ej in EG. rewrite EM in Hj. subst.
        clear - HAlo HAhi F4 Hj. lia. }
    split; [clear - Hw HSK; lia|]. split; [lia|]. split; [unfold APPMEM_END; clear - Hw HAE'; lia|].
    intros i Hi. apply HA; clear - Hw Hi; lia.
  Qed.

  (* A byte of a data range apart from the window, and its shadow byte, are apart from the run's writes rWB. *)
  Lemma rr_D_outWB : forall a b x, In (a, b) rDD -> (b <= S - 9072 \/ S <= a) -> a <= x < b -> app_mem x ->
    outside rWB x /\ outside rWB (shadow_addr x).
  Proof.
    intros a b x Hin Hw Hx Hap.
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof (rr_D_out a b x Hin Hx) as HOd. rewrite rr_fpw in HOd. cbn [outside] in HOd.
    destruct HOd as (O1 & O2 & O3 & O4 & _).
    pose proof (rt_app_shadow x Hap) as Hsh.
    assert (M1 : (FS + 1085440) mod 8 = 0) by (clear - F2; Z.div_mod_to_equations; lia).
    assert (M2 : (S - 9072) mod 8 = 0) by exact (rr_S_mod8 S 9072 S16 eq_refl).
    assert (WAPP : forall z, S - 9072 <= z < S -> app_mem z)
      by (intros z Hz; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; right; clear - Hz HHM' HAE'; lia).
    unfold rWB, rYY. rewrite rr_fpw. cbn [outside app].
    split.
    - split; [clear - Hw Hx; lia|]. split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4|].
      split; [|exact I]. apply rr_sh_out; [exact Hap | clear - HSK; lia | unfold APPMEM_END; clear - HAE'; lia].
    - split; [exact (rr_sh_notapp _ _ _ Hsh WAPP)|].
      split; [apply (rr_sh_notapp _ _ _ Hsh); intros z Hz; apply F5; clear - Hz; lia|].
      split; [apply (rr_sh_notapp _ _ _ Hsh); intros z Hz; apply F5; clear - Hz; lia|].
      split; [apply (rr_sh_notapp _ _ _ Hsh); intros z Hz; apply F5; clear - Hz; lia|].
      split; [exact (rr_win_sh x _ _ M1 O3)|].
      split; [|exact I]. apply (rr_win_sh x _ _ M2). clear - Hw Hx. lia.
  Qed.

  (* A byte below ASAN_GT (the image's cells), and its shadow byte, are apart from the run's writes rWB. *)
  Lemma rr_low_outWB : forall x, 0 <= x < ASAN_GT -> outside rWB x /\ outside rWB (shadow_addr x).
  Proof.
    intros x Hx.
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    unfold ASAN_GT in Hx.
    assert (Hap : app_mem x) by (unfold app_mem, LOWMEM_END; left; clear - Hx; lia).
    pose proof (rt_app_shadow x Hap) as Hsh.
    assert (M1 : (FS + 1085440) mod 8 = 0) by (clear - F2; Z.div_mod_to_equations; lia).
    assert (M2 : (S - 9072) mod 8 = 0) by exact (rr_S_mod8 S 9072 S16 eq_refl).
    assert (WAPP : forall z, S - 9072 <= z < S -> app_mem z)
      by (intros z Hz; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; right; clear - Hz HHM' HAE'; lia).
    pose proof (rr_sh_lt x (FS + 1085440) M1 ltac:(clear - Hx F3; lia)) as L1.
    pose proof (rr_sh_lt x (S - 9072) M2 ltac:(clear - Hx HHM'; lia)) as L2.
    pose proof (rr_sh_ge (FS + 1085440) x ltac:(clear - Hx F3; lia)) as L3.
    unfold rWB, rYY. rewrite rr_fpw. cbn [outside app].
    split.
    - split; [clear - Hx HHM'; lia|]. split; [clear - Hx F3; lia|]. split; [clear - Hx F3; lia|].
      split; [clear - Hx F3; lia|].
      split; [unfold shadow_addr, ASAN_K in *; clear - Hx L3; lia|].
      split; [|exact I]. pose proof (rr_sh_ge (S - 9072) x ltac:(clear - Hx HHM'; lia)) as L4.
      unfold shadow_addr, ASAN_K in *; clear - Hx L4; lia.
    - split; [exact (rr_sh_notapp _ _ _ Hsh WAPP)|].
      split; [apply (rr_sh_notapp _ _ _ Hsh); intros z Hz; apply F5; clear - Hz; lia|].
      split; [apply (rr_sh_notapp _ _ _ Hsh); intros z Hz; apply F5; clear - Hz; lia|].
      split; [apply (rr_sh_notapp _ _ _ Hsh); intros z Hz; apply F5; clear - Hz; lia|].
      split; [clear - L1; lia|]. split; [clear - L2; lia | exact I].
  Qed.


  (* The writes of the parse call (the contract's footprint, X = the run's own frame). *)
  Definition rWp (G spc j nn : Z) : list ivl :=
    reac_ctrl_parse_fp (G + 32) spc ++ fp_wx [1%nat] FS (rFX j nn) ++
    [(shadow_addr (spc - 8800), shadow_addr spc)].

  (* The callee's window: inside the run's window, apart from the frame; spc is 8-aligned. *)
  Lemma rk_cwin : forall G fv spc j nn, rFK G fv spc j nn ->
    S - 9072 <= spc - 8800 /\ spc <= S - 128 /\ spc mod 8 = 0 /\ (spc <= G \/ G + 128 <= spc - 8800).
  Proof.
    intros G fv spc j nn HK.
    pose proof rA_facts as (HA32 & HAlo & HAhi). destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    destruct HK as [(_ & EG & Esp & _ & _)|(Hj & EG & _ & Esp & _)].
    - subst. split; [clear - HAlo; lia|]. split; [clear - HAhi; lia|].
      split; [clear - HA32; Z.div_mod_to_equations; lia | clear; lia].
    - destruct (rr_fsnum FS j) as (Ej & _ & _ & EM). rewrite Ej in EG. rewrite EM in Hj. subst.
      split; [clear - HAlo; lia|]. split; [clear - HAhi; lia|].
      split; [clear - HA32; Z.div_mod_to_equations; lia | clear - HAlo F4 Hj; lia].
  Qed.

  Lemma rr_Wp_WB : forall G fv spc j nn, rFK G fv spc j nn -> sub_fp (rWp G spc j nn) rWB.
  Proof.
    intros G fv spc j nn HK x Hx.
    pose proof rA_facts as (HA32 & HAlo & HAhi). destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _).
    destruct (rk_cwin G fv spc j nn HK) as (C1 & C2 & C3 & C4).
    unfold rWB, rYY in Hx. cbn [outside app] in Hx. destruct Hx as (HW0 & Hx).
    apply rr_out_app_inv in Hx as [HFW HY]. cbn [outside] in HY. destruct HY as (HY & _).
    unfold rWp, reac_ctrl_parse_fp, REAC_CTRL_PARSE_K. rewrite (proj2 (Z.eqb_neq (G + 32) 0) ltac:(clear - FRlo F1; lia)).
    cbn [app outside].
    split.
    { destruct (rk_place G fv spc j nn HK) as [(En & EG)|(En & Hj & EG)].
      - clear - HW0 EG HAlo HAhi. lia.
      - rewrite rr_fpw in HFW. cbn [outside] in HFW. destruct HFW as (_ & _ & H3 & _). clear - H3 EG Hj. lia. }
    split; [clear - HW0 C1 C2; lia|].
    apply fl_out_app; [exact (fp_wx_sub_w [1%nat] FS (rFX j nn) x HFW) |].
    cbn [outside]. split; [|exact I].
    intros [L1 L2]. apply HY. split.
    + pose proof (rr_sh_ge (spc - 8800) (S - 9072) C1). clear - L1 H. lia.
    + pose proof (rr_sh_ge S spc ltac:(clear - C2; lia)). clear - L2 H. lia.
  Qed.

  (* An application byte apart from the record, the callee's window and fp_wx is apart from rWp. *)
  Lemma rr_out_Wp_app : forall G spc j nn x, app_mem x -> 8800 <= spc -> spc <= APPMEM_END ->
    (x < G + 32 \/ G + 68 <= x) -> (x < spc - 8800 \/ spc <= x) -> outside (fp_wx [1%nat] FS (rFX j nn)) x ->
    0 < G + 32 -> outside (rWp G spc j nn) x.
  Proof.
    intros G spc j nn x Hap Hs1 Hs2 H1 H2 H3 HG.
    unfold rWp, reac_ctrl_parse_fp, REAC_CTRL_PARSE_K. rewrite (proj2 (Z.eqb_neq (G + 32) 0) ltac:(clear - HG; lia)).
    cbn [app outside]. split; [clear - H1; lia|]. split; [clear - H2; lia|].
    apply fl_out_app; [exact H3|]. cbn [outside]. split; [|exact I].
    apply rr_sh_out; [exact Hap | clear - Hs1; lia | exact Hs2].
  Qed.

  (* The shadow byte of a window byte outside the callee's window is apart from rWp. *)
  Lemma rr_out_Wp_sh : forall G fv spc j nn x, rFK G fv spc j nn -> S - 9072 <= x < S -> (x < spc - 8800 \/ spc <= x) ->
    outside (rWp G spc j nn) (shadow_addr x).
  Proof.
    intros G fv spc j nn x HK Hx Hxs.
    pose proof rA_facts as (HA32 & HAlo & HAhi). destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & _).
    destruct (rk_cwin G fv spc j nn HK) as (C1 & C2 & C3 & C4).
    assert (Hap : app_mem x) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; right; clear - Hx HHM' HAE'; lia).
    pose proof (rt_app_shadow x Hap) as Hsh.
    assert (WAPP : forall z, S - 9072 <= z < S -> app_mem z)
      by (intros z Hz; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; right; clear - Hz HHM' HAE'; lia).
    assert (M1 : (FS + 1085440) mod 8 = 0) by (clear - F2; Z.div_mod_to_equations; lia).
    assert (M2 : (spc - 8800) mod 8 = 0) by (clear - C3; Z.div_mod_to_equations; lia).
    unfold rWp, reac_ctrl_parse_fp, REAC_CTRL_PARSE_K. rewrite (proj2 (Z.eqb_neq (G + 32) 0) ltac:(clear - FRlo F1; lia)).
    cbn [app outside].
    split; [apply (rr_sh_notapp _ _ _ Hsh); intros z Hz; replace z with (G + (z - G)) by ring; apply FAP; clear - Hz; lia|].
    split; [apply (rr_sh_notapp _ _ _ Hsh); intros z Hz; apply WAPP; clear - Hz C1 C2; lia|].
    apply fl_out_app.
    - apply (fp_wx_sub_w [1%nat] FS (rFX j nn)). rewrite rr_fpw. cbn [outside].
      split; [apply (rr_sh_notapp _ _ _ Hsh); intros z Hz; apply F5; clear - Hz; lia|].
      split; [apply (rr_sh_notapp _ _ _ Hsh); intros z Hz; apply F5; clear - Hz; lia|].
      split; [apply (rr_sh_notapp _ _ _ Hsh); intros z Hz; apply F5; clear - Hz; lia|].
      split; [|exact I]. apply (rr_win_sh x _ _ M1). clear - Hx F4. lia.
    - cbn [outside]. split; [|exact I]. apply (rr_win_sh x _ _ M2). clear - Hxs. lia.
  Qed.

  (* rAWX at the parse call's return: the callee's window by its post, the rest kept. *)
  Lemma rr_awx_parse : forall G fv spc j nn m5 mp, rFK G fv spc j nn -> rAWX G m5 ->
    munch (rWp G spc j nn) m5 mp -> addressable mp (spc - 8800) 8800 -> rAWX G mp.
  Proof.
    intros G fv spc j nn m5 mp HK HA MU AWp x Hx HxG.
    destruct (Z_lt_le_dec x (spc - 8800)) as [L|L]; [|destruct (Z_lt_le_dec x spc) as [L2|L2]].
    2: { destruct AWp as (_ & _ & _ & HAW). replace x with (spc - 8800 + (x - (spc - 8800))) by ring.
         apply HAW. clear - L L2. lia. }
    all: destruct (HA x Hx HxG) as (Hap & b & Hb & Hok); split; [exact Hap|]; exists b; split; [|exact Hok];
      pose proof (rt_shadow_bound _ (rt_app_shadow x Hap)) as Hbd;
      rewrite (rr_munch_mrd_out _ m5 mp (shadow_addr x) MU ltac:(clear - Hbd; lia)
                 (rr_out_Wp_sh G fv spc j nn x HK Hx ltac:(lia))); exact Hb.
  Qed.


  (* A data range apart from the window, addressable at entry, keeps its cells, its bytes and its shadow across
     writes inside rWB. *)
  Lemma rr_keepD : forall a n mX, In (a, a + n) rDD -> (a + n <= S - 9072 \/ S <= a) -> addressable m a n ->
    munch rWB m mX -> wmono rsegs m mX ->
    addressable mX a n /\
    (forall cs, rw_cells rsegs m a cs -> Z.of_nat (cells_size cs) <= n -> rw_cells rsegs mX a cs) /\
    (forall bs, bytes_at rsegs m a bs -> Z.of_nat (length bs) <= n -> bytes_at rsegs mX a bs).
  Proof.
    intros a n mX Hin Hw AD MU WM.
    assert (OUT : forall x, a <= x < a + n -> outside rWB x /\ outside rWB (shadow_addr x)).
    { intros x Hx. apply (rr_D_outWB a (a + n) x Hin Hw Hx).
      pose proof (rr_app_in m a n (x - a) AD ltac:(clear - Hx; lia)) as Hap.
      replace (a + (x - a)) with x in Hap by ring. exact Hap. }
    split; [|split].
    - apply (rr_addr_munch rWB m mX a n AD MU). intros i Hi. apply (proj2 (OUT (a + i) ltac:(clear - Hi; lia))).
    - intros cs Hc Hb. apply (rr_rw rWB m mX a cs Hc MU WM). intros x Hx. apply (proj1 (OUT x ltac:(clear - Hx Hb; lia))).
    - intros bs Hbs Hb. eapply fl_bytes; [exact Hbs | exact MU |]. intros x Hx.
      apply (proj1 (OUT x ltac:(clear - Hx Hb; lia))).
  Qed.

  (* The window bytes above the callee's window and the frame's own bytes above the record are apart from rWp. *)
  Lemma rr_out_Wp_win : forall G fv spc j nn x, rFK G fv spc j nn -> app_mem x ->
    ((rA <= x < S) \/ (G + 68 <= x < G + 128)) -> outside (rWp G spc j nn) x.
  Proof.
    intros G fv spc j nn x HK Hap Hx.
    pose proof rA_facts as (HA32 & HAlo & HAhi). destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & Fsp & _).
    destruct (rk_cwin G fv spc j nn HK) as (C1 & C2 & C3 & C4).
    apply rr_out_Wp_app; [exact Hap | lia | unfold APPMEM_END; lia | lia | lia | | lia].
    destruct Hx as [Hx|Hx].
    - apply (fp_wx_sub_w [1%nat] FS (rFX j nn)). rewrite rr_fpw. cbn [outside].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact I].
      apply rr_sh_out; [exact Hap | lia | unfold APPMEM_END; lia].
    - apply (rr_fx_out G fv spc j nn x HK). left. lia.
  Qed.

  (* rJB at the return of reac_ctrl_parse, from rBI before the call and the call's post. *)
  Lemma rr_JB_parse : forall G fv spc j nn m5 mp, rFK G fv spc j nn -> reply_args fr pa pp pn = true ->
    rBI G j nn m5 -> munch (rWp G spc j nn) m5 mp -> wmono rsegs m5 mp -> mem_inv rsegs mp ->
    stk rsegs mp (spc - 8800) spc -> rw_cells rsegs mp (G + 32) [CB 36 (snd (ctrlparse len g))] ->
    asan_cells mp -> shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) mp ->
    addressable mp (spc - 8800) 8800 ->
    fpx [1%nat] mp (bv_unsigned tp) FS (spc - 8800) spc (reac_ctrl_parse_W (G + 32) spc)
      (reac_ctrl_parse_D fr len (G + 32)) (rFX j nn) ->
    Forall (fun ci => bytes_at rsegs mp (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) (rFX j nn) ->
    rJB G j nn mp.
  Proof.
    intros G fv spc j nn m5 mp HK RAb HB5 MUp WMp MIp STp RCp ACp SWp AWp FPXp FLX.
    pose proof rA_facts as (HA32 & HAlo & HAhi). destruct rr_fsn as (F1 & _ & _ & F4 & _ & _).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & _).
    destruct (rk_cwin G fv spc j nn HK) as (C1 & C2 & _).
    assert (G32 : 0 < G + 32) by (clear - FRlo F1; lia).
    assert (C2' : spc <= S) by (clear - C2; lia).
    pose proof (rCore_of_BI G fv spc j nn m5 HK HB5) as (WM5 & RM5 & MI5 & SV5 & AWX5 & FP5 & TLS5 & H1205).
    pose proof HB5 as (MUf5 & _).
    pose proof (munch_weaken _ _ m m5 (rWf_WB G fv spc j nn HK) MUf5) as MU5.
    pose proof (munch_weaken _ _ m5 mp (rr_Wp_WB G fv spc j nn HK) MUp) as MUp'.
    pose proof (munch_trans _ m m5 mp MU5 MUp') as MUmp.
    pose proof (wmono_trans rsegs m m5 mp WM5 WMp) as WMmp.
    pose proof FPXp as (DT & TS & C & T & DB & k & _ & _ & FSPp & _).
    assert (RMp : rr_rd_mono m5 mp)
      by exact (rr_rd_parse G spc (rFX j nn) m5 mp C1 C2' G32 MUp RCp STp FSPp SWp AWp).
    pose proof (rr_rd_mono_trans _ _ _ RM5 RMp) as RMmp.
    assert (HFULL : sub_fp (rWp G spc j nn) (rWW ++ fp_w [1%nat] FS ++ rYY))
      by (intros x Hx; apply (rr_Wp_WB G fv spc j nn HK), rWB_full, Hx).
    pose proof RAb as RA. unfold reply_args in RA.
    rewrite !andb_true_iff, !negb_true_iff, !Z.eqb_neq in RA. destruct RA as [[[Rf Ra] Rp] Rn].
    unfold rJB.
    split; [exact MUmp|].
    split.
    { split; [exact WMmp|]. split; [exact RMmp|]. split; [exact MIp|].
      split.
      { apply (rr_rw _ m5 mp _ _ SV5 MUp WMp). intros x Hx. unfold rSAVES in Hx.
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in Hx.
        apply (rr_out_Wp_win G fv spc j nn x HK); [|left; clear - Hx HAhi; lia].
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right. clear - Hx HHM' HAE' HAhi HSK; lia. }
      split; [exact (rr_awx_parse G fv spc j nn m5 mp HK AWX5 MUp AWp)|].
      split; [exact (rr_fp_retx [1%nat] m5 mp (bv_unsigned tp) FS (S - 9072) S rWW rDD rYY (rWp G spc j nn)
                       (spc - 8800) spc _ _ (rFX j nn) FP5 TLS5 MUp HFULL FPXp)|].
      split; [exact (rr_tls_ret [1%nat] m5 mp (bv_unsigned tp) FS (S - 9072) S rWW rDD rYY (rWp G spc j nn)
                       FP5 TLS5 MUp HFULL)|].
      intros Hn. destruct (H1205 Hn) as (H1 & H2). split.
      - eapply fl_bytes; [exact H1 | exact MUp |]. intros x Hx. rewrite length_le8 in Hx.
        apply (rr_out_Wp_win G fv spc j nn x HK); [|right; clear - Hx; lia].
        replace x with (G + (x - G)) by ring. apply FAP. clear - Hx; lia.
      - subst nn. replace (rFX j 1) with [(1%nat, j)] in FLX by reflexivity.
        apply Forall_inv in FLX. exact FLX. }
    split; [exact RCp|].
    split.
    { intros HL. destruct (HF RAb HL) as (Ffr & HBf & Hwf & _ & _ & _).
      pose proof (AFfr RAb HL) as AF.
      destruct (rr_keepD fr 50 mp (rr_D_fr RAb HL) Hwf AF MUmp WMmp) as (A1 & _ & A3).
      split; [apply A3; [exact HBf | rewrite Hg; cbn; clear; lia] | exact A1]. }
    split.
    { destruct (HO RAb) as (Pa2 & Pp8 & Pn8 & Ca & Cp & Cn & _ & _ & _ & Wa & Wp & Wn).
      destruct (AOUT RAb) as (Aa & Ap & An & _).
      destruct (rr_D_out3 RAb) as (Ia & Ip & In').
      destruct (rr_keepD pa 2 mp Ia Wa Aa MUmp WMmp) as (Ka1 & Ka2 & _).
      destruct (rr_keepD pp 8 mp Ip Wp Ap MUmp WMmp) as (Kp1 & Kp2 & _).
      destruct (rr_keepD pn 8 mp In' Wn An MUmp WMmp) as (Kn1 & Kn2 & _).
      unfold rOUTC.
      split; [apply Ka2; [exact Ca | cbn; clear; lia]|]. split; [apply Kp2; [exact Cp | cbn; clear; lia]|].
      split; [apply Kn2; [exact Cn | cbn; clear; lia]|].
      split; [exact Ka1|]. split; [exact Kp1 | exact Kn1]. }
    split; [exact (rr_stk_mono m mp _ _ ST WMmp RMmp)|].
    split; [exact ACp | exact SWp].
  Qed.


  (* Every range of the class-1 free-frame footprint is nonempty. *)
  Lemma rr_fpwx_ne : forall j nn r, In r (fp_wx [1%nat] FS (rFX j nn)) -> fst r < snd r.
  Proof.
    intros j nn r Hr. destruct rr_fsn as (F1 & F2 & _).
    assert (M : (FS + 2134016) mod 8 = 0) by (clear - F2; Z.div_mod_to_equations; lia).
    unfold rFX in Hr. destruct (nn =? 1).
    - unfold fp_wx, fp_wx1 in Hr. cbn [flat_map] in Hr. rewrite app_nil_r in Hr.
      apply in_app_or in Hr as [Hr|Hr].
      + destruct (rr_fsnum FS 0) as (_ & _ & _ & EM).
        cbn [In] in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; [clear; lia | rewrite EM; clear; lia].
      + apply in_app_or in Hr as [Hr|Hr]; unfold cut_ivls, nonempty in Hr; apply filter_In in Hr as [_ Hr];
          apply Z.ltb_lt; exact Hr.
    - rewrite fp_wx_nil, rr_fpw in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; [clear; lia | clear; lia | clear; lia |].
      apply rr_sh_lt; [exact M | clear; lia].
  Qed.

  (* ===== The cut at the parse call (bF-glue.md; reac_ctrl_parse takes its own class-1 fake frame, so its run is an
     allocator event and the stretch before it ends AT the callee's first slot). 0x84a58 .. 0x84a64: a0 = fr,
     a1 = len, a2 = G + 32 and the `jal`; the memory is not touched, so the reached state is m5's. rp_call takes this
     prefix by evtF_cut; its script after the call is unchanged. ===== *)
  Lemma rp_call_pre_F : forall (G fv spc : Z) (m5 : word -> option byte)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    evtF rsegs RNG
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x84a68) (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 rA)
                              (Z_to_bv 64 fr) (Z_to_bv 64 len) (Z_to_bv 64 (G + 32)) x13 x14 x15 x16 x17
                              (Z_to_bv 64 fv) (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa)
                              (Z_to_bv 64 len) (Z_to_bv 64 (G + 32)) (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G)
                              (wa ASAN_K) x28 x29 x30 x31)
                         F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m5 (seg_rom rsegs))
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 rA) (Z_to_bv 64 4)
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 pn) (Z_to_bv 64 pp)
               (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len) (Z_to_bv 64 (G + 32))
               (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) (wa ASAN_K) x28 x29 x30 x31)
          F (Z_to_bv 64 0x84a58) fc None m5 (seg_rom rsegs)).
  Proof.
    intros G fv spc m5 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31.
    step. step. step. step.
    apply evtF_done. reflexivity.
  Qed.

  (* 0x84a58 .. 0x84a68: rp_call_pre_F, the call of reac_ctrl_parse by the free-frame contract (X = the run's own
     class-1 frame), then rKF. *)
  Lemma rp_call : forall Q, rKF Q -> forall (G fv spc j nn : Z) (mc m5 : word -> option byte)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    rFK G fv spc j nn -> rBI G j nn mc -> reply_args fr pa pp pn = true ->
    munch [(G / 8 + ASAN_K + 4, G / 8 + ASAN_K + 9)] mc m5 -> wmono rsegs mc m5 -> rr_rd_mono mc m5 ->
    mem_inv rsegs m5 ->
    bytes_at rsegs m5 (G / 8 + ASAN_K + 4) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] ->
    evtF rsegs RNG Q (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 rA) (Z_to_bv 64 4)
                       x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 pn) (Z_to_bv 64 pp)
                       (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len) (Z_to_bv 64 (G + 32))
                       (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) (wa ASAN_K) x28 x29 x30 x31)
                  F (Z_to_bv 64 0x84a58) fc None m5 (seg_rom rsegs)).
  Proof.
    intros Q KF G fv spc j nn mc m5 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      HK HB RAb MU5 WM5 RM5 MI5 BS5.
    eapply evtF_cut;
      [exact (rp_call_pre_F G fv spc m5 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31) |].
    intros ms' ->.
    pose proof rA_facts as (HA32 & HAlo & HAhi). destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & _).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & _).
    destruct (rk_cwin G fv spc j nn HK) as (C1 & C2 & C3 & C4).
    assert (G32 : 0 < G + 32) by (clear - FRlo F1; lia).
    assert (G32n : (G + 32 =? 0) = false) by (apply Z.eqb_neq; clear - G32; lia).
    pose proof RAb as RA. unfold reply_args in RA.
    rewrite !andb_true_iff, !negb_true_iff, !Z.eqb_neq in RA. destruct RA as [[[Rf Ra] Rp] Rn].
    pose proof (rr_BI_unp G fv spc j nn mc m5 HK HB MU5 WM5 RM5 MI5) as HB5.
    pose proof (rCore_of_BI G fv spc j nn m5 HK HB5) as (WMm5 & RMm5 & _ & _ & AWX5 & FP5 & TLS5 & H1205).
    pose proof HB5 as (MUf5 & _).
    pose proof (munch_weaken _ _ m m5 (rWf_WB G fv spc j nn HK) MUf5) as MUB5.
    (* the premises of the parse contract *)
    assert (PX : Forall (fun ci => fst ci = 1%nat /\ 0 <= snd ci < fs_M 1 /\
                          bytes_at rsegs m5 (fs_flag FS (fst ci) (snd ci)) [Z_to_bv 8 1]) (rFX j nn)).
    { destruct (rk_place G fv spc j nn HK) as [(En & _)|(En & Hj & _)]; subst nn; [constructor|].
      replace (rFX j 1) with [(1%nat, j)] by reflexivity. constructor; [|constructor]. cbn [fst snd].
      destruct (rr_fsnum FS j) as (_ & _ & _ & EM). rewrite EM.
      split; [reflexivity|]. split; [exact Hj | exact (proj2 (H1205 eq_refl))]. }
    assert (Hsp16 : spc mod 16 = 0).
    { destruct HK as [(_ & _ & Esp & _)|(_ & _ & _ & Esp & _)]; rewrite Esp; clear - HA32; Z.div_mod_to_equations; lia. }
    pose proof (rr_stk_mono m m5 _ _ ST WMm5 RMm5) as STW5.
    destruct (stk_split rsegs m5 _ (spc - 8800) _ STW5 ltac:(clear - C1 C2; lia)) as [_ STc0].
    destruct (stk_split rsegs m5 _ spc _ STc0 ltac:(clear - C2; lia)) as [STc _]. clear STc0.
    pose proof (rk_stk G fv spc j nn m5 HK WMm5 RMm5) as STfr.
    destruct (stk_split rsegs m5 _ (G + 68) _ STfr ltac:(clear; lia)) as [STfr1 _].
    destruct (stk_carve rsegs m5 G (G + 68) 36%nat STfr1 ltac:(clear; lia)) as [_ [junkR RC]].
    replace (G + 68 - Z.of_nat 36) with (G + 32) in RC by (clear; lia).
    assert (HFp : 50 <= len -> 0 < fr /\ fr + 50 <= 2^64 /\ (fr + 50 <= spc - 8800 \/ spc <= fr)).
    { intros HL. destruct (HF RAb HL) as (A1 & _ & A3 & _ & _ & _). split; [clear - Rf Rfr; lia|]. split; [exact A1|].
      clear - A3 C1 C2. lia. }
    assert (KFR : 50 <= len -> bytes_at rsegs m5 fr g /\ addressable m5 fr 50).
    { intros HL. destruct (HF RAb HL) as (_ & HBf & Hwf & _ & _ & _).
      destruct (rr_keepD fr 50 m5 (rr_D_fr RAb HL) Hwf (AFfr RAb HL) MUB5 WMm5) as (A1 & _ & A3).
      split; [apply A3; [exact HBf | rewrite Hg; cbn; clear; lia] | exact A1]. }
    assert (HRD : forall i, In i (cp_rd len g) -> mrd rsegs m5 (wa (fr + Z.of_nat i)) = nth_error g i).
    { intros i Hi. destruct (Z_lt_le_dec len 50) as [Ln|Ln].
      - unfold cp_rd in Hi. rewrite (proj2 (Z.leb_gt 50 len) Ln) in Hi. destruct Hi.
      - destruct (KFR Ln) as ((_ & _ & HB1) & _). apply HB1.
        pose proof (cp_rd_lt39 len g i Hi) as H39. rewrite Hg. clear - H39. lia. }
    assert (HOc : G + 32 <> 0 ->
              (G + 32) mod 4 = 0 /\ G + 32 + 36 <= 2^64 /\ rw_cells rsegs m5 (G + 32) [CB 36 junkR] /\
              (G + 32 + 36 <= spc - 8800 \/ spc <= G + 32) /\ (50 <= len -> G + 32 + 36 <= fr \/ fr + 50 <= G + 32)).
    { intros _. split; [clear - FR8; Z.div_mod_to_equations; lia|].
      split; [clear - FRhi HAhi HS; lia|]. split; [exact RC|]. split; [clear - C4; lia|].
      intros HL. destruct (HF RAb HL) as (_ & _ & Hwf & _ & _ & _).
      pose proof (rr_apartG G fv spc j nn fr (fr + 50) HK (rr_D_fr RAb HL) ltac:(clear; lia) Hwf) as Hap.
      clear - Hap. lia. }
    assert (ACm5 : asan_cells m5).
    { apply (fl_asan_cells rWB m m5 AC MUB5). intros x Hx. apply (proj1 (rr_low_outWB x ltac:(clear - Hx; unfold RT_LO, RT_HI, ASAN_GT in *; lia))). }
    pose proof (rr_shadow_rw_on_mono _ m m5 SW WMm5 RMm5) as SWm5.
    pose proof (rr_win_addr G fv spc j nn m5 HK AWX5) as AWc.
    assert (AOc : G + 32 <> 0 -> addressable m5 (G + 32) 36 /\ app_mem (G + 32 + 36) /\
                                  (G + 32 + 36 <= GOT_CF \/ CF + 256 <= G + 32)).
    { intros _. split; [|split].
      - apply (rr_unpoison_addr m5 G FR8).
        + intros i Hi. replace (G + 32 + i) with (G + (32 + i)) by ring. apply FAP. clear - Hi; lia.
        + replace (shadow_addr (G + 32)) with (G / 8 + ASAN_K + 4); [exact BS5|].
          unfold shadow_addr. replace (G + 32) with (G + 4 * 8) by ring. rewrite Z.div_add by (clear; lia). ring.
      - replace (G + 32 + 36) with (G + 68) by ring. apply FAP. clear; lia.
      - right. unfold CF. clear - FRlo F3. lia. }
    assert (OL : forall a bs, bytes_at rsegs m a bs -> 0 <= a -> a + Z.of_nat (length bs) <= ASAN_GT ->
                   bytes_at rsegs m5 a bs).
    { intros a bs Hb Ha Hl. eapply fl_bytes; [exact Hb | exact MUB5 |]. intros x Hx.
      apply (proj1 (rr_low_outWB x ltac:(clear - Ha Hl Hx; lia))). }
    assert (ABCc : addressable m5 REAC_CTRL_PARSE_BC 6).
    { apply (rr_addr_munch rWB m m5 _ 6 ABC MUB5). intros i Hi.
      apply (proj2 (rr_low_outWB (REAC_CTRL_PARSE_BC + i) ltac:(clear - Hi; unfold REAC_CTRL_PARSE_BC, ASAN_GT; lia))). }
    assert (BC1 : bytes_at rsegs m5 REAL_BCMP (le8 (wa BCMP)))
      by (apply (OL _ _ HBCMP); [unfold REAL_BCMP; clear; lia | rewrite length_le8; unfold REAL_BCMP, ASAN_GT; clear; lia]).
    assert (BC2 : bytes_at rsegs m5 REAL_MEMCMP (le8 (wa MEMCMP)))
      by (apply (OL _ _ HMEMCMP); [unfold REAL_MEMCMP; clear; lia | rewrite length_le8; unfold REAL_MEMCMP, ASAN_GT; clear; lia]).
    assert (BC3 : bytes_at rsegs m5 GOT_CF (le8 (wa CF)))
      by (apply (OL _ _ HGCF); [unfold GOT_CF; clear; lia | rewrite length_le8; unfold GOT_CF, ASAN_GT; clear; lia]).
    assert (BC4 : bytes_at rsegs m5 (CF + 254) [Z_to_bv 8 1])
      by (apply (OL _ _ HCF254); [unfold CF; clear; lia | cbn [length Z.of_nat]; unfold CF, ASAN_GT; clear; lia]).
    assert (BC5 : bytes_at rsegs m5 (CF + 255) [Z_to_bv 8 1])
      by (apply (OL _ _ HCF255); [unfold CF; clear; lia | cbn [length Z.of_nat]; unfold CF, ASAN_GT; clear; lia]).
    assert (FPX : fpx [1%nat] m5 (bv_unsigned tp) FS (spc - 8800) spc (reac_ctrl_parse_W (G + 32) spc)
                    (reac_ctrl_parse_D fr len (G + 32)) (rFX j nn)).
    { apply (rr_fpx_sub [1%nat] m5 (bv_unsigned tp) FS (S - 9072) S rWW rDD (spc - 8800) spc _ _ (rFX j nn) FP5
               ltac:(clear - C1; lia) ltac:(clear - C2; lia)).
      - intros DT TS C T DB k HT Hd. unfold reac_ctrl_parse_W, REAC_CTRL_PARSE_K. rewrite G32n. replace (G + 32 + 36) with (G + 68) by ring.
        unfold rWW, reac_ctrl_identity_reply_W, REAC_CTRL_IDENTITY_REPLY_K in Hd. apply fl_dj_cons in Hd as [Hd _].
        apply fl_dj_cons. split; [apply (fl_dj_sub _ _ _ _ _ Hd); clear - C1 C2; lia|].
        destruct (rk_place G fv spc j nn HK) as [(En & EG)|(En & Hj & EG)].
        + apply (fl_dj_sub _ _ _ _ _ Hd); clear - EG HAlo HAhi; lia.
        + pose proof (TLS5 DT TS C T DB k HT) as HT1. rewrite rr_fpw in HT1.
          apply (rr_dj_inside (G + 32) (G + 68) (FS + 1085440) (FS + 2134016)); [| clear - EG Hj; lia | clear; lia | clear - EG Hj; lia].
          unfold fp_dj at 1. apply Forall_app. split.
          * apply (rr_dj_sub_r _ _ _ HT1). intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[]].
            cbn [In app]. right. right. left. reflexivity.
          * constructor; [|constructor]. constructor; [|constructor].
            unfold fs_frame, fs_B, ly_dj. cbn [fst snd Z.of_nat]. clear - FRlo EG Hj. lia.
      - unfold reac_ctrl_parse_D. rewrite G32n. replace (G + 32 + 36) with (G + 68) by ring.
        unfold fp_dj. apply Forall_app. split.
        + destruct (Z.ltb_spec len 50) as [Ln|Ln]; [constructor|].
          pose proof (rr_D_dj fr (fr + 50) (rr_D_fr RAb Ln)) as H1.
          apply (fp_dj_cover _ _ _ (fp_wx_cover [1%nat] FS (rFX j nn))) in H1. exact H1.
        + apply (rr_dj_of_out (G + 32) (G + 68) _ ltac:(clear; lia) (rr_fpwx_ne j nn)).
          intros x Hx. apply (rr_fx_out G fv spc j nn x HK). left. clear - Hx. lia. }
    assert (TLSc : reac_ctrl_parse_tls m5 (bv_unsigned tp) FS (spc - 8800) spc).
    { intros DT TS C T DB k HT.
      apply (rr_dj_last _ (fp_w [1%nat] FS) (shadow_addr (S - 9072)) (shadow_addr S));
        [exact (TLS5 _ _ _ _ _ _ HT) | apply rr_sh_ge; clear - C1; lia | apply rr_sh_ge; clear - C2; lia]. }
    pose proof PARSE as HP. unfold reac_ctrl_parse_contract_x_F_on, REAC_CTRL_PARSE_K in HP.
    eapply evtF_cut.
    { eapply HP with (X := rFX j nn) (f := fr) (n := len) (o := G + 32) (S := spc) (FS := FS) (fr := g)
                     (junk := junkR).
      - exact PX.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact Rfr.
      - exact Rlen.
      - clear - G32 FRhi HAhi HS; lia.
      - clear - C2 HS; lia.
      - exact Hsp16.
      - clear - C1 HSK; lia.
      - exact STc.
      - exact MI5.
      - exact Hg.
      - exact HFp.
      - exact HRD.
      - exact HOc.
      - exact ACm5.
      - exact (shadow_rw_on_mono _ _ m5 (rk_parse_inR G fv spc j nn HK RAb) SWm5).
      - unfold HIGHMEM_BEG. clear - C1 HHM'; lia.
      - unfold APPMEM_END. clear - C2 HAE'; lia.
      - exact AWc.
      - intros HL. exact (proj2 (KFR HL)).
      - exact AOc.
      - exact ABCc.
      - exact BC1.
      - exact BC2.
      - exact BC3.
      - exact BC4.
      - exact BC5.
      - exact FPX.
      - exact TLSc.
      - (* the footprint is decided byte by byte *) exact RBY.
      - (* the image *) unfold IMG_LO, IMG_LEN. exact RIMG.
      - (* the callee's window *) eapply rng_sub; [exact RWIN | clear - C1 C2; lia | clear - C1 C2; lia].
      - (* its byte-exact shadow *) exact (SSW (spc - 8800) spc ltac:(clear - C1 C2; lia) ltac:(clear; lia)
                                              ltac:(clear - C1 C2; lia)).
      - (* the 50 bytes at fr *) intros HL. exact (RFR RAb HL).
      - (* their aligned shadow word cover *) intros HL. unfold sh_lo, sh_len.
        exact (SKF RAb HL fr (fr + 50 - 1) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
      - (* the record at G + 32 *) intros _.
        eapply rng_sub; [exact (rrF_frame G fv spc j nn HK) | clear; lia | clear; lia].
      - (* its aligned shadow word cover *) intros _. unfold sh_lo, sh_len.
        exact (rrF_frame_kov G fv spc j nn HK (G + 32) (G + 32 + 36 - 1) ltac:(clear; lia) ltac:(clear; lia)
                 ltac:(clear; lia)).
      - (* the 6 bytes at .str.4 *)
        eapply rng_sub; [exact RIMG | unfold REAC_CTRL_PARSE_BC; lia | unfold REAC_CTRL_PARSE_BC; lia].
      - (* their aligned shadow word cover *) unfold sh_lo, sh_len.
        exact (SKBC REAC_CTRL_PARSE_BC (REAC_CTRL_PARSE_BC + 6 - 1) ltac:(clear; lia) ltac:(clear; lia)
                 ltac:(clear; lia)).
      - (* the side stack's header *) exact RFSS.
      - (* the class-1 side-stack bytes *) exact RW1.
      - (* the thread cells, m's *) exact (rrF_tls m5 rWB MUB5 rWB_full). }
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mp & E & MUp & WMp
                & MIp & STp & RCp & ACp & SWp & AWp & FPXp & FLX & _ & _).
    subst ms'. specialize (RCp ltac:(clear - G32; lia)).
    replace (ret_pc (Z_to_bv 64 543336)) with (Z_to_bv 64 0x84a68)
      by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
    exact (KF G fv spc j nn mp (Z_to_bv 64 543336) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HK
             (rr_JB_parse G fv spc j nn m5 mp HK RAb HB5 MUp WMp MIp STp RCp ACp (SWp _ SWm5) AWp FPXp FLX)
             RAb).
  Qed.

  (* 0x84a3c .. 0x84a68: rr_unp_run, then rp_call. The B listing has no branch to the trap address in this range. *)
  Lemma rp_parse : forall Q, rKF Q -> rKN Q.
  Proof.
    intros Q KF G fv spc j nn mc rr x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HK HB RAb.
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & _ & _ & _ & _ & _ & _ & SH1 & SH2).
    pose proof rr_fsn as (F1 & _).
    pose proof HB as (_ & WM & RM & MI1 & _).
    assert (SWc : forall i, 0 <= i < 16 -> wview rsegs mc (wa (G / 8 + ASAN_K + i)) <> None).
    { intros i Hi. pose proof (rr_shadow_rw_on_mono _ m mc SW WM RM) as SRmc.
      destruct (rk_facts G fv spc j nn HK) as (_ & _ & _ & _ & _ & _ & FRA & _).
      apply (rr_stk_wv mc _ _ _ (rr_shadow16_stk_on _ mc G SRmc (rk_inR _ _ _ _ _ HK) ltac:(clear - FRlo F1; lia)
                                   FRA SH1 SH2)).
      clear - Hi; lia. }
    apply (rr_unp_run G mc rr (Z_to_bv 64 spc) x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 rA) (Z_to_bv 64 (-1)) x11 x12 x13
             x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa)
             (Z_to_bv 64 len) s8 (wa ASAN_K) x28 x29 x30 x31 Q FR8 ltac:(clear - FRlo F1; lia) SH1 SH2 SWc MI1
             (rrF_frame_blk G fv spc j nn HK)).
    intros m5 MU5 WM5 RM5 MI5 BS5.
    exact (rp_call Q KF G fv spc j nn mc m5 rr x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HK HB RAb
             MU5 WM5 RM5 MI5 BS5).
  Qed.

  (* ===================== Segments 5 and 6: the stores and the teardown ===================== *)

  (* The statement's post (the run's own sp = S). *)
  Definition rQ : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (reply_ret fr len pa pp pn g))
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch rWP m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - 9072) S /\
      (reply_ok fr len pa pp pn g = true -> rOUTF m') /\
      asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m') /\ addressable m' (S - 9072) 9072 /\
      fp [1%nat] m' (bv_unsigned tp) FS (S - 9072) S rWW rDD /\
      reac_ctrl_identity_reply_tls m' (bv_unsigned tp) FS (S - 9072) S.

  (* The runtime's own cells are apart from every write the run makes. *)
  Lemma rr_RT_outWP : forall x, RT_LO <= x < RT_HI -> outside rWP x.
  Proof.
    intros x Hx. unfold RT_LO, RT_HI in Hx.
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    pose proof HHM as HH. unfold HIGHMEM_BEG in HH.
    assert (SHW : 2147450880 <= shadow_addr (S - 9072))
      by (unfold shadow_addr, ASAN_K; clear - HH; Z.div_mod_to_equations; lia).
    assert (SHF : 2147450880 <= shadow_addr (FS + 1085440))
      by (unfold shadow_addr, ASAN_K; clear - F3; Z.div_mod_to_equations; lia).
    unfold rWP, rYY, reac_ctrl_identity_reply_fp, REAC_CTRL_IDENTITY_REPLY_K. rewrite rr_fpw.
    destruct (reply_ok fr len pa pp pn g) eqn:OK.
    - assert (RAb : reply_args fr pa pp pn = true)
        by (unfold reply_ok in OK; destruct (reply_args fr pa pp pn); [reflexivity | discriminate]).
      destruct (AOUT RAb) as (_ & _ & _ & Da & Dp & Dn). unfold RT_LO, RT_HI in Da, Dp, Dn.
      clear - Hx HH F3 SHW SHF Da Dp Dn. cbn [app outside].
      repeat split; first [exact I | lia].
    - clear - Hx HH F3 SHW SHF. cbn [app outside]. repeat split; first [exact I | lia].
  Qed.

  (* The frame's flag byte: 1 while the run holds the side frame, 0 once the teardown released it. *)
  Definition rFL (G j nn : Z) (mc : word -> option byte) : Prop :=
    nn = 1 -> bytes_at rsegs mc (G + 120) (le8 (Z_to_bv 64 (fs_flag FS 1 j))) /\
              (bytes_at rsegs mc (fs_flag FS 1 j) [Z_to_bv 8 0] \/
               bytes_at rsegs mc (fs_flag FS 1 j) [Z_to_bv 8 1]).

  (* The run's state through the teardown: rEI0 with the frame's flag byte 0 or 1. *)
  Definition rTI (G j nn : Z) (mc : word -> option byte) : Prop :=
    munch rWP m mc /\ wmono rsegs m mc /\ rr_rd_mono m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (S - 104) rSAVES /\ rAWX G mc /\
    fp [1%nat] mc (bv_unsigned tp) FS (S - 9072) S rWW rDD /\
    reac_ctrl_identity_reply_tls mc (bv_unsigned tp) FS (S - 9072) S /\ rFL G j nn mc.

  (* The run's state at the teardown's join 0x84c7c: the window is addressable again. *)
  Definition rTJ (mc : word -> option byte) : Prop :=
    munch rWP m mc /\ wmono rsegs m mc /\ rr_rd_mono m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (S - 104) rSAVES /\ addressable mc (S - 9072) 9072 /\
    fp [1%nat] mc (bv_unsigned tp) FS (S - 9072) S rWW rDD /\
    reac_ctrl_identity_reply_tls mc (bv_unsigned tp) FS (S - 9072) S.

  Lemma rTI_of_EI0 : forall G j nn mc, rEI0 G j nn mc -> rTI G j nn mc.
  Proof.
    intros G j nn mc (MU & WM & RM & MI1 & SV & AX & FP1 & TL & H120).
    split; [exact MU|]. split; [exact WM|]. split; [exact RM|]. split; [exact MI1|].
    split; [exact SV|]. split; [exact AX|]. split; [exact FP1|]. split; [exact TL|].
    intros Hn. destruct (H120 Hn) as (H1 & H2). split; [exact H1 | right; exact H2].
  Qed.

  (* The class-1 flag array after writes that touch no flag byte but the frame's own. *)
  Lemma rr_flags_td : forall G fv spc j nn (m1 m2 : word -> option byte) flags,
    rFK G fv spc j nn -> bytes_at rsegs m1 (fs_flag FS 1 0) flags -> Z.of_nat (length flags) = fs_M 1 ->
    Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags ->
    munch (rWf G j nn) m1 m2 ->
    (nn = 1 -> bytes_at rsegs m2 (fs_flag FS 1 j) [Z_to_bv 8 0] \/
               bytes_at rsegs m2 (fs_flag FS 1 j) [Z_to_bv 8 1]) ->
    exists flags', bytes_at rsegs m2 (fs_flag FS 1 0) flags' /\ Z.of_nat (length flags') = fs_M 1 /\
       Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags'.
  Proof.
    intros G fv spc j nn m1 m2 flags HK HFl HFln HFb MU HFJ.
    pose proof rA_facts as (HA32 & HAlo & HAhi).
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & _).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    destruct (rr_fsnum FS 0) as (_ & E2 & _ & E4).
    assert (OUTF : forall x, fs_flag FS 1 0 <= x < fs_flag FS 1 0 + fs_M 1 -> (nn = 0 \/ x <> fs_flag FS 1 j) ->
              outside (rWf G j nn) x).
    { intros x Hx Hxj. rewrite E2, E4 in Hx.
      destruct (rr_fsnum FS j) as (_ & E2j & E3 & _).
      assert (Hap : app_mem x) by (apply F5; lia).
      unfold rWf. rewrite E3. cbn [outside].
      split; [lia|]. split; [lia|]. split.
      { destruct (rk_place G fv spc j nn HK) as [(En & _)|(En & _)]; subst nn; [lia|].
        destruct Hxj as [Hxj|Hxj]; [discriminate|]. rewrite E2j in Hxj. lia. }
      split; [lia|]. split; [|exact I].
      pose proof (rr_sh_add8 G 16 FR8) as ESG. replace (G + 8 * 16) with (G + 128) in ESG by lia.
      rewrite <- ESG. apply rr_sh_out; [exact Hap | lia | pose proof HAE; lia]. }
    destruct (rk_place G fv spc j nn HK) as [(En & EG)|(En & Hj & EG)].
    - exists flags. split; [|split; [exact HFln | exact HFb]].
      eapply fl_bytes; [exact HFl | exact MU |]. intros x Hx. rewrite HFln in Hx.
      apply OUTF; [exact Hx | left; exact En].
    - subst nn.
      assert (HV : exists v, (v = Z_to_bv 8 0 \/ v = Z_to_bv 8 1) /\ mrd rsegs m2 (wa (fs_flag FS 1 j)) = Some v).
      { destruct (HFJ eq_refl) as [(_ & _ & HB1)|(_ & _ & HB1)];
          [exists (Z_to_bv 8 0); split; [left; reflexivity|] | exists (Z_to_bv 8 1); split; [right; reflexivity|]];
          (specialize (HB1 0%nat ltac:(cbn; lia)); rewrite Z.add_0_r in HB1; exact HB1). }
      destruct HV as (v & Hv & Hrd).
      apply (rr_flags_set m1 m2 FS j v flags);
        [rewrite E4; lia | exact Hv | exact HFl | exact HFln | exact HFb | exact Hrd |].
      intros x Hx Hxj.
      assert (Hbd : 0 <= x < 2^64) by (rewrite E2, E4 in Hx; pose proof HAE; unfold APPMEM_END in *; lia).
      exact (rr_munch_mrd_out _ m1 m2 x MU Hbd (OUTF x Hx (or_intror Hxj))).
  Qed.

  (* fp and the tls premise after writes inside the prologue's footprint (the frame, its shadow, the flag byte). *)
  Lemma rr_fp_td : forall G fv spc j nn (m1 m2 : word -> option byte),
    rFK G fv spc j nn ->
    fp [1%nat] m1 (bv_unsigned tp) FS (S - 9072) S rWW rDD ->
    reac_ctrl_identity_reply_tls m1 (bv_unsigned tp) FS (S - 9072) S ->
    munch (rWf G j nn) m1 m2 -> wmono rsegs m1 m2 -> rr_rd_mono m1 m2 ->
    (nn = 1 -> bytes_at rsegs m2 (fs_flag FS 1 j) [Z_to_bv 8 0] \/
               bytes_at rsegs m2 (fs_flag FS 1 j) [Z_to_bv 8 1]) ->
    fp [1%nat] m2 (bv_unsigned tp) FS (S - 9072) S rWW rDD /\
    reac_ctrl_identity_reply_tls m2 (bv_unsigned tp) FS (S - 9072) S.
  Proof.
    intros G fv spc j nn m1 m2 HK FP1 TLS1 MU WM RM HFJ.
    pose proof rA_facts as (HA32 & HAlo & HAhi).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & _).
    pose proof (rWf_WB G fv spc j nn HK) as HWB.
    assert (HFULL : sub_fp (rWf G j nn) (rWW ++ fp_w [1%nat] FS ++ rYY))
      by (intros x Hx; apply HWB, rWB_full, Hx).
    pose proof FP1 as (DT & TS & C & T & DB & k & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & HCL & _).
    pose proof (rr_stk_mono m1 m2 _ _ P5 WM RM) as STF. unfold FS_SIZE in STF.
    assert (O88 : forall x, FS + 80 <= x < FS + 104 -> outside (rWf G j nn) x).
    { intros x Hx. assert (Hap : app_mem x) by (apply F5; lia).
      destruct (rr_fsnum FS j) as (_ & E2 & E3 & _).
      unfold rWf. rewrite E2, E3. cbn [outside].
      assert (Hj0 : 0 <= j) by (destruct (rk_place G fv spc j nn HK) as [(_ & _)|(_ & Hj & _)];
        [destruct HK as [(_ & _ & _ & Ej & _)|(Hj' & _)]; [lia|];
         destruct (rr_fsnum FS j) as (_ & _ & _ & E4); lia | lia]).
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|exact I].
      pose proof (rr_sh_add8 G 16 FR8) as ESG. replace (G + 8 * 16) with (G + 128) in ESG by lia.
      rewrite <- ESG. apply rr_sh_out; [exact Hap | lia | pose proof HAE; lia]. }
    split.
    - apply (rr_fp_free [1%nat] m1 m2 (bv_unsigned tp) FS (S - 9072) S rWW rDD (rWf G j nn) FP1 TLS1 MU WM
               HFULL O88).
      + intros x Hx. right. exact (rr_rd_of_stk m2 _ _ STF x ltac:(unfold FS_SIZE in Hx; lia)).
      + intros c Hc. cbn [In] in Hc. destruct Hc as [<-|[]]. split.
        * apply rr_rd8_le8; [unfold fs_hint; cbn [Z.of_nat]; lia
                            | unfold fs_hint; cbn [Z.of_nat]; pose proof HAE; unfold APPMEM_END in *; lia |].
          intros i Hi. apply (rr_rd_of_stk m2 _ _ STF). unfold fs_hint; cbn [Z.of_nat]; lia.
        * apply Forall_inv in HCL. destruct HCL as (_ & h & flags & _ & HFl & HFln & HFb).
          exact (rr_flags_td G fv spc j nn m1 m2 flags HK HFl HFln HFb MU HFJ).
    - exact (rr_tls_ret [1%nat] m1 m2 (bv_unsigned tp) FS (S - 9072) S rWW rDD rYY (rWf G j nn) FP1 TLS1 MU HFULL).
  Qed.

  (* rTI after writes inside the frame's 16 shadow bytes. *)
  Lemma rr_TI_sh : forall G fv spc j nn mc mc', rFK G fv spc j nn -> rTI G j nn mc ->
    munch [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] mc mc' -> wmono rsegs mc mc' -> rr_rd_mono mc mc' ->
    mem_inv rsegs mc' -> rTI G j nn mc'.
  Proof.
    intros G fv spc j nn mc mc' HK (MU & WM & RM & MI1 & SV & AX & FP1 & TL & FL) MU5 WM5 RM5 MI5.
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & FRA & _ & SH1 & SH2).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (OUT5 : forall x, app_mem x -> outside [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] x)
      by (intros x Hx; apply rr_app_out_sh; [exact Hx | clear - SH1; lia | clear - SH2; lia]).
    assert (SUBf : sub_fp [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] (rWf G j nn)).
    { intros x Hx. unfold rWf, shadow_addr in Hx. cbn [outside] in Hx |- *.
      destruct Hx as (_ & _ & _ & _ & H5 & _). split; [exact H5 | exact I]. }
    assert (MUf : munch (rWf G j nn) mc mc') by exact (munch_weaken _ _ mc mc' SUBf MU5).
    assert (SHO : forall x, S - 9072 <= x < S -> (x < G \/ G + 128 <= x) ->
                    outside [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] (shadow_addr x)).
    { intros x Hx HxG. cbn [outside]. split; [|exact I].
      pose proof (rr_sh_add8 G 16 FR8) as ESG. replace (G + 8 * 16) with (G + 128) in ESG by lia.
      unfold shadow_addr in ESG |- *. rewrite <- ESG.
      pose proof (rr_win_sh x G (G + 128) FR8 ltac:(clear - HxG; lia)) as HW.
      unfold shadow_addr in HW. exact HW. }
    split; [exact (munch_trans _ m mc mc' MU (munch_weaken _ _ mc mc'
             (fun x Hx => SUBf x (rWf_WB G fv spc j nn HK x (rWB_WP x Hx))) MU5))|].
    split; [exact (wmono_trans rsegs m mc mc' WM WM5)|].
    split; [exact (rr_rd_mono_trans m mc mc' RM RM5)|].
    split; [exact MI5|].
    split.
    { apply (rr_rw _ mc mc' _ _ SV MU5 WM5). intros x Hx. apply OUT5.
      unfold rSAVES in Hx. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in Hx.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right. clear - Hx HHM' HAE' HSK. lia. }
    split; [exact (rr_awx_munch G _ mc mc' AX MU5 SHO)|].
    destruct (rr_fp_td G fv spc j nn mc mc' HK FP1 TL MUf WM5 RM5
                ltac:(intros Hn; destruct (FL Hn) as (_ & HB2); destruct (rr_fsnum FS j) as (_ & E2j & _);
                      destruct HB2 as [HB2|HB2]; [left|right];
                      (eapply fl_bytes; [exact HB2 | exact MU5 |];
                       intros x Hx; cbn [length Z.of_nat Pos.of_succ_nat] in Hx; apply OUT5; apply F5;
                       rewrite E2j in Hx;
                       assert (Hjb : 0 <= j < 8192)
                         by (destruct (rk_place G fv spc j nn HK) as [(En & _)|(En & Hj & _)]; [lia | lia]);
                       clear - Hx Hjb; lia))) as (FP2 & TL2).
    split; [exact FP2|]. split; [exact TL2|].
    intros Hn. destruct (FL Hn) as (HB1 & HB2). destruct (rr_fsnum FS j) as (_ & E2j & _).
    assert (Hjb : 0 <= j < 8192)
      by (destruct (rk_place G fv spc j nn HK) as [(En & _)|(En & Hj & _)]; [lia | lia]).
    split.
    - eapply fl_bytes; [exact HB1 | exact MU5 |]. intros x Hx. rewrite length_le8 in Hx. apply OUT5.
      replace x with (G + (x - G)) by ring. apply FAP. clear - Hx; lia.
    - destruct HB2 as [HB2|HB2]; [left|right];
        (eapply fl_bytes; [exact HB2 | exact MU5 |];
         intros x Hx; cbn [length Z.of_nat Pos.of_succ_nat] in Hx; apply OUT5; apply F5;
         rewrite E2j in Hx; clear - Hx Hjb; lia).
  Qed.

  (* A store of w bytes inside a run of stores to [A, A + n): the writes, wmono, rr_rd_mono, mem_inv. *)
  Lemma rr_st_runw : forall (mq m0 m1 : word -> option byte) (A n a : Z) (bs : list byte) (w : nat),
    length bs = w -> 0 <= A -> A + n <= 2^64 -> A <= a -> a + Z.of_nat w <= A + n ->
    munch [(A, A + n)] m0 m1 -> wmono rsegs mq m1 -> rr_rd_mono m0 m1 -> mem_inv rsegs m1 ->
    store_ok rsegs m1 (wa a) w = true ->
    munch [(A, A + n)] m0 (write_to_mem m1 (Z_to_bv 64 a) bs) /\
    wmono rsegs mq (write_to_mem m1 (Z_to_bv 64 a) bs) /\
    rr_rd_mono m0 (write_to_mem m1 (Z_to_bv 64 a) bs) /\
    mem_inv rsegs (write_to_mem m1 (Z_to_bv 64 a) bs).
  Proof.
    intros mq m0 m1 A n a bs w Hw HA Hn Ha1 Ha2 MU WMq RMq MIq HSq. rewrite <- Hw in Ha2, HSq.
    split; [apply munch_write; [exact MU | lia | lia | cbn [inside]; left; lia]|].
    split; [exact (wmono_write rsegs mq m1 _ _ WMq)|].
    split; [exact (rr_rd_mono_write m0 m1 _ _ RMq)|].
    exact (mem_inv_store rsegs m1 _ bs MIq HSq).
  Qed.

  (* Four zero bytes read back as four zero shadow bytes. *)
  Lemma rr_b4_rd : forall mc A, bytes_at rsegs mc A [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
    forall i, 0 <= i < 4 -> exists b, mrd rsegs mc (wa (A + i)) = Some b /\ bv_signed b = 0.
  Proof.
    intros mc A (_ & _ & HB) i Hi. exists (Z_to_bv 8 0). split; [|reflexivity].
    specialize (HB (Z.to_nat i) ltac:(cbn [length]; lia)). rewrite Z2Nat.id in HB by lia.
    rewrite HB. destruct (Z.to_nat i) as [|[|[|[|k]]]] eqn:Ei; try reflexivity.
    exfalso. assert (Z.of_nat (Z.to_nat i) = i) by (rewrite Z2Nat.id; lia). rewrite Ei in *. cbn in *. lia.
  Qed.

  (* 0x84c7c .. 0x84cb8: sp = S - 128, the 13 saved registers restored, sp = S, ret. *)
  Lemma rp_ret : forall mc r
      (x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
       x31 : word),
    rTJ mc -> (reply_ok fr len pa pp pn g = true -> rOUTF mc) -> r = reply_ret fr len pa pp pn g ->
    evtF rsegs RNG rQ (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                        x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x84c7c) fc None mc (seg_rom rsegs)).
  Proof.
    intros mc r x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
      x31 (MU & WM & RM & MI1 & SV & AW1 & FP1 & TL1) HOF Er.
    replace (S - 104) with (S + -104) in SV by lia. unfold rSAVES in SV.
    pose proof (rr_stk_mono m mc _ _ ST WM RM) as STm.
    assert (ACm : asan_cells mc) by (apply (fl_asan_cells rWP m mc AC MU); exact rr_RT_outWP).
    pose proof (fun P (HP : shadow_rw_on P m) => rr_shadow_rw_on_mono P m mc HP WM RM) as SWm.
    do 16 step.
    apply evtF_done. unfold rQ. subst r.
    do 14 eexists. exists mc.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI1|]. split; [exact STm|].
    split; [exact HOF|]. split; [exact ACm|]. split; [exact SWm|]. split; [exact AW1|].
    split; [exact FP1 | exact TL1].
  Qed.

  (* The frame's 16 shadow bytes are inside the prologue's footprint. *)
  Lemma rr_sh16_Wf : forall G j nn, sub_fp [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] (rWf G j nn).
  Proof.
    intros G j nn x Hx. unfold rWf, shadow_addr in Hx. cbn [outside] in Hx |- *.
    destruct Hx as (_ & _ & _ & _ & H5 & _). split; [exact H5 | exact I].
  Qed.

  (* The cells at the OUT pointers survive the writes inside the prologue's footprint. *)
  Lemma rr_OUTF_wf : forall G fv spc j nn (m1 m2 : word -> option byte), rFK G fv spc j nn ->
    munch (rWf G j nn) m1 m2 -> wmono rsegs m1 m2 -> reply_ok fr len pa pp pn g = true -> rOUTF m1 -> rOUTF m2.
  Proof.
    intros G fv spc j nn m1 m2 HK MU WM OK (Ha & Hp & Hn).
    assert (RAb : reply_args fr pa pp pn = true)
      by (unfold reply_ok in OK; destruct (reply_args fr pa pp pn); [reflexivity | discriminate]).
    destruct (HO RAb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Wa & Wp & Wn).
    destruct (AOUT RAb) as (Aa & Ap & An & _).
    destruct (rr_D_out3 RAb) as (Ia & Ip & In').
    assert (OUT : forall a n x, In (a, a + n) rDD -> (a + n <= S - 9072 \/ S <= a) -> addressable m a n ->
             a <= x < a + n -> outside (rWf G j nn) x).
    { intros a n x Hin Hw AD Hx.
      pose proof (rr_app_in m a n (x - a) AD ltac:(clear - Hx; lia)) as Hap.
      replace (a + (x - a)) with x in Hap by ring.
      exact (rWf_WB G fv spc j nn HK x (proj1 (rr_D_outWB a (a + n) x Hin Hw Hx Hap))). }
    split; [|split].
    - apply (rr_rw _ m1 m2 _ _ Ha MU WM). intros x Hx.
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in Hx.
      exact (OUT pa 2 x Ia Wa Aa ltac:(clear - Hx; lia)).
    - apply (rr_rw _ m1 m2 _ _ Hp MU WM). intros x Hx.
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in Hx.
      exact (OUT pp 8 x Ip Wp Ap ltac:(clear - Hx; lia)).
    - apply (rr_rw _ m1 m2 _ _ Hn MU WM). intros x Hx.
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in Hx.
      exact (OUT pn 8 x In' Wn An ltac:(clear - Hx; lia)).
  Qed.

  (* The window is addressable again: apart from the frame by rAWX, the real frame by its shadow bytes 0. *)
  Lemma rr_win_addr_full : forall G fv spc j nn mc, rFK G fv spc j nn -> rAWX G mc ->
    (nn = 0 -> addressable mc G 128) -> addressable mc (S - 9072) 9072.
  Proof.
    intros G fv spc j nn mc HK AX HG.
    pose proof rA_facts as (HA32 & HAlo & HAhi). destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    pose proof HSK as HSK'. pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
    split; [clear - HSK'; lia|]. split; [clear; lia|]. split; [unfold APPMEM_END; clear - HAE'; lia|].
    intros i Hi.
    destruct (rk_place G fv spc j nn HK) as [(En & EG)|(En & Hj & EG)].
    - destruct (Z_lt_le_dec (S - 9072 + i) G) as [L|L]; [apply AX; [clear - Hi; lia | left; exact L]|].
      destruct (Z_lt_le_dec (S - 9072 + i) (G + 128)) as [L2|L2].
      + destruct (HG En) as (_ & _ & _ & HA).
        replace (S - 9072 + i) with (G + (S - 9072 + i - G)) by ring. apply HA. clear - L L2; lia.
      + apply AX; [clear - Hi; lia | right; exact L2].
    - apply AX; [clear - Hi; lia|]. right. clear - EG Hj F4 Hi. lia.
  Qed.

  (* 0x84c3c .. 0x84c78: the real frame's 16 shadow bytes := 0 (four runs of four). *)
  Lemma rr_z16 : forall (G : Z) (mc : word -> option byte) (Q : machine_state -> Prop)
      (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30
       x31 : word),
    0 <= G / 8 + ASAN_K -> G / 8 + ASAN_K + 16 <= 2^64 ->
    (forall i, 0 <= i < 16 -> wview rsegs mc (wa (G / 8 + ASAN_K + i)) <> None) -> mem_inv rsegs mc ->
    shblk RNG G 15 ->
    (forall m16, munch [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] mc m16 -> wmono rsegs mc m16 ->
       rr_rd_mono mc m16 -> mem_inv rsegs m16 ->
       (forall k, 0 <= k <= 15 -> exists b, mrd rsegs m16 (wa (G / 8 + ASAN_K + k)) = Some b /\ bv_signed b = 0) ->
       evtF rsegs RNG Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                          (Z_to_bv 64 (G / 8 + ASAN_K)) x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x84c7c) fc None m16 (seg_rom rsegs))) ->
    evtF rsegs RNG Q (MS (mkR x1 x2 gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24
                       (Z_to_bv 64 (G / 8 + ASAN_K)) x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x84c3c) fc None mc (seg_rom rsegs)).
  Proof.
    intros G mc Q x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29
      x30 x31 HA0 HA16 SWh MIc SBFRM K16.
    pose proof (wmono_refl rsegs mc) as Wq. pose proof MIc as Iq.
    (* run 1: shadow bytes 4,5,6,7 *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (Bq : bytes_at rsegs mm (G / 8 + ASAN_K + 4) (@nil byte))
        by (split; [clear - HA0; lia|]; split;
              [cbn [length Z.of_nat]; clear - HA16; lia | intros i Hi; cbn [length] in Hi; lia]);
      pose proof (munch_refl [(G / 8 + ASAN_K + 4, G / 8 + ASAN_K + 4 + 4)] mm) as Mq;
      pose proof (rr_rd_mono_refl mm) as Rq end.
    rwstb (G / 8 + ASAN_K + 4) 1%nat (G / 8 + ASAN_K) SWh. step. rewrite rr_le1_0.
    destruct (rr_sb_step _ _ _ (G / 8 + ASAN_K + 4) 4 (@nil byte) (Z_to_bv 8 0) (G / 8 + ASAN_K + 4)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) ltac:(clear - HA0; lia) ltac:(clear - HA16; lia)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear - HA0; lia) Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'.
    rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 5) 1%nat (G / 8 + ASAN_K) SWh. step. rewrite rr_le1_0.
    destruct (rr_sb_step _ _ _ (G / 8 + ASAN_K + 4) 4 [Z_to_bv 8 0] (Z_to_bv 8 0) (G / 8 + ASAN_K + 5)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) ltac:(clear - HA0; lia) ltac:(clear - HA16; lia)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear - HA0; lia) Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'.
    rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 6) 1%nat (G / 8 + ASAN_K) SWh. step. rewrite rr_le1_0.
    destruct (rr_sb_step _ _ _ (G / 8 + ASAN_K + 4) 4 [Z_to_bv 8 0; Z_to_bv 8 0] (Z_to_bv 8 0) (G / 8 + ASAN_K + 6)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) ltac:(clear - HA0; lia) ltac:(clear - HA16; lia)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear - HA0; lia) Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'.
    rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 7) 1%nat (G / 8 + ASAN_K) SWh. step. rewrite rr_le1_0.
    destruct (rr_sb_step _ _ _ (G / 8 + ASAN_K + 4) 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] (Z_to_bv 8 0)
                (G / 8 + ASAN_K + 7)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) ltac:(clear - HA0; lia) ltac:(clear - HA16; lia)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear - HA0; lia) Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'.
    rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rename Bq into BA. rename Mq into MA. rename Rq into RA.
    (* run 2: shadow bytes 0,1,2,3 *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (Bq : bytes_at rsegs mm (G / 8 + ASAN_K) (@nil byte))
        by (split; [clear - HA0; lia|]; split;
              [cbn [length Z.of_nat]; clear - HA16; lia | intros i Hi; cbn [length] in Hi; lia]);
      pose proof (munch_refl [(G / 8 + ASAN_K, G / 8 + ASAN_K + 4)] mm) as Mq;
      pose proof (rr_rd_mono_refl mm) as Rq end.
    rwstb (G / 8 + ASAN_K) 1%nat (G / 8 + ASAN_K) SWh. step. rewrite rr_le1_0.
    destruct (rr_sb_step _ _ _ (G / 8 + ASAN_K) 4 (@nil byte) (Z_to_bv 8 0) (G / 8 + ASAN_K)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) ltac:(clear - HA0; lia) ltac:(clear - HA16; lia)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear - HA0; lia) Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'.
    rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 1) 1%nat (G / 8 + ASAN_K) SWh. step. rewrite rr_le1_0.
    destruct (rr_sb_step _ _ _ (G / 8 + ASAN_K) 4 [Z_to_bv 8 0] (Z_to_bv 8 0) (G / 8 + ASAN_K + 1)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) ltac:(clear - HA0; lia) ltac:(clear - HA16; lia)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear - HA0; lia) Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'.
    rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 2) 1%nat (G / 8 + ASAN_K) SWh. step. rewrite rr_le1_0.
    destruct (rr_sb_step _ _ _ (G / 8 + ASAN_K) 4 [Z_to_bv 8 0; Z_to_bv 8 0] (Z_to_bv 8 0) (G / 8 + ASAN_K + 2)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) ltac:(clear - HA0; lia) ltac:(clear - HA16; lia)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear - HA0; lia) Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'.
    rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 3) 1%nat (G / 8 + ASAN_K) SWh. step. rewrite rr_le1_0.
    destruct (rr_sb_step _ _ _ (G / 8 + ASAN_K) 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] (Z_to_bv 8 0)
                (G / 8 + ASAN_K + 3)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) ltac:(clear - HA0; lia) ltac:(clear - HA16; lia)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear - HA0; lia) Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'.
    rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rename Bq into BB. rename Mq into MB. rename Rq into RB.
    (* run 3: shadow bytes 12,13,14,15 *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (Bq : bytes_at rsegs mm (G / 8 + ASAN_K + 12) (@nil byte))
        by (split; [clear - HA0; lia|]; split;
              [cbn [length Z.of_nat]; clear - HA16; lia | intros i Hi; cbn [length] in Hi; lia]);
      pose proof (munch_refl [(G / 8 + ASAN_K + 12, G / 8 + ASAN_K + 12 + 4)] mm) as Mq;
      pose proof (rr_rd_mono_refl mm) as Rq end.
    rwstb (G / 8 + ASAN_K + 12) 1%nat (G / 8 + ASAN_K) SWh. step. rewrite rr_le1_0.
    destruct (rr_sb_step _ _ _ (G / 8 + ASAN_K + 12) 4 (@nil byte) (Z_to_bv 8 0) (G / 8 + ASAN_K + 12)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) ltac:(clear - HA0; lia) ltac:(clear - HA16; lia)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear - HA0; lia) Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'.
    rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 13) 1%nat (G / 8 + ASAN_K) SWh. step. rewrite rr_le1_0.
    destruct (rr_sb_step _ _ _ (G / 8 + ASAN_K + 12) 4 [Z_to_bv 8 0] (Z_to_bv 8 0) (G / 8 + ASAN_K + 13)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) ltac:(clear - HA0; lia) ltac:(clear - HA16; lia)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear - HA0; lia) Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'.
    rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 14) 1%nat (G / 8 + ASAN_K) SWh. step. rewrite rr_le1_0.
    destruct (rr_sb_step _ _ _ (G / 8 + ASAN_K + 12) 4 [Z_to_bv 8 0; Z_to_bv 8 0] (Z_to_bv 8 0) (G / 8 + ASAN_K + 14)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) ltac:(clear - HA0; lia) ltac:(clear - HA16; lia)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear - HA0; lia) Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'.
    rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 15) 1%nat (G / 8 + ASAN_K) SWh. step. rewrite rr_le1_0.
    destruct (rr_sb_step _ _ _ (G / 8 + ASAN_K + 12) 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] (Z_to_bv 8 0)
                (G / 8 + ASAN_K + 15)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) ltac:(clear - HA0; lia) ltac:(clear - HA16; lia)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear - HA0; lia) Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'.
    rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rename Bq into BC. rename Mq into MC. rename Rq into RC.
    (* run 4: shadow bytes 8,9,10,11 *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (Bq : bytes_at rsegs mm (G / 8 + ASAN_K + 8) (@nil byte))
        by (split; [clear - HA0; lia|]; split;
              [cbn [length Z.of_nat]; clear - HA16; lia | intros i Hi; cbn [length] in Hi; lia]);
      pose proof (munch_refl [(G / 8 + ASAN_K + 8, G / 8 + ASAN_K + 8 + 4)] mm) as Mq;
      pose proof (rr_rd_mono_refl mm) as Rq end.
    rwstb (G / 8 + ASAN_K + 8) 1%nat (G / 8 + ASAN_K) SWh. step. rewrite rr_le1_0.
    destruct (rr_sb_step _ _ _ (G / 8 + ASAN_K + 8) 4 (@nil byte) (Z_to_bv 8 0) (G / 8 + ASAN_K + 8)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) ltac:(clear - HA0; lia) ltac:(clear - HA16; lia)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear - HA0; lia) Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'.
    rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 9) 1%nat (G / 8 + ASAN_K) SWh. step. rewrite rr_le1_0.
    destruct (rr_sb_step _ _ _ (G / 8 + ASAN_K + 8) 4 [Z_to_bv 8 0] (Z_to_bv 8 0) (G / 8 + ASAN_K + 9)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) ltac:(clear - HA0; lia) ltac:(clear - HA16; lia)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear - HA0; lia) Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'.
    rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 10) 1%nat (G / 8 + ASAN_K) SWh. step. rewrite rr_le1_0.
    destruct (rr_sb_step _ _ _ (G / 8 + ASAN_K + 8) 4 [Z_to_bv 8 0; Z_to_bv 8 0] (Z_to_bv 8 0) (G / 8 + ASAN_K + 10)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) ltac:(clear - HA0; lia) ltac:(clear - HA16; lia)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear - HA0; lia) Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'.
    rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 11) 1%nat (G / 8 + ASAN_K) SWh. step. rewrite rr_le1_0.
    destruct (rr_sb_step _ _ _ (G / 8 + ASAN_K + 8) 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] (Z_to_bv 8 0)
                (G / 8 + ASAN_K + 11)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) ltac:(clear - HA0; lia) ltac:(clear - HA16; lia)
                ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; clear - HA0; lia) Bq Mq Wq Rq Iq HS0)
      as (Bq' & Mq' & Wq' & Rq' & Iq').
    clear Bq Mq Wq Rq Iq HS0. cbn [app] in Bq'.
    rename Bq' into Bq, Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rename Bq into BD. rename Mq into MD. rename Rq into RD.
    (* the four runs' bytes, each kept across the runs that follow it *)
    pose proof (fl_bytes _ _ _ _ _ BA MB ltac:(intros x Hx;
      cbn [length Z.of_nat Pos.of_succ_nat] in Hx; cbn [outside]; split; [clear - Hx; lia | exact I])) as BA1.
    pose proof (fl_bytes _ _ _ _ _ BA1 MC ltac:(intros x Hx;
      cbn [length Z.of_nat Pos.of_succ_nat] in Hx; cbn [outside]; split; [clear - Hx; lia | exact I])) as BA2.
    pose proof (fl_bytes _ _ _ _ _ BA2 MD ltac:(intros x Hx;
      cbn [length Z.of_nat Pos.of_succ_nat] in Hx; cbn [outside]; split; [clear - Hx; lia | exact I])) as BA3.
    pose proof (fl_bytes _ _ _ _ _ BB MC ltac:(intros x Hx;
      cbn [length Z.of_nat Pos.of_succ_nat] in Hx; cbn [outside]; split; [clear - Hx; lia | exact I])) as BB1.
    pose proof (fl_bytes _ _ _ _ _ BB1 MD ltac:(intros x Hx;
      cbn [length Z.of_nat Pos.of_succ_nat] in Hx; cbn [outside]; split; [clear - Hx; lia | exact I])) as BB2.
    pose proof (fl_bytes _ _ _ _ _ BC MD ltac:(intros x Hx;
      cbn [length Z.of_nat Pos.of_succ_nat] in Hx; cbn [outside]; split; [clear - Hx; lia | exact I])) as BC1.
    (* the whole run's writes *)
    pose proof (munch_weaken [(G / 8 + ASAN_K + 4, G / 8 + ASAN_K + 4 + 4)]
      [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] _ _
      ltac:(intros x Hx; cbn [outside] in Hx |- *; destruct Hx as [Hx1 _]; split; [clear - Hx1; lia | exact I])
      MA) as MA'.
    pose proof (munch_weaken [(G / 8 + ASAN_K, G / 8 + ASAN_K + 4)]
      [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] _ _
      ltac:(intros x Hx; cbn [outside] in Hx |- *; destruct Hx as [Hx1 _]; split; [clear - Hx1; lia | exact I])
      MB) as MB'.
    pose proof (munch_weaken [(G / 8 + ASAN_K + 12, G / 8 + ASAN_K + 12 + 4)]
      [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] _ _
      ltac:(intros x Hx; cbn [outside] in Hx |- *; destruct Hx as [Hx1 _]; split; [clear - Hx1; lia | exact I])
      MC) as MC'.
    pose proof (munch_weaken [(G / 8 + ASAN_K + 8, G / 8 + ASAN_K + 8 + 4)]
      [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] _ _
      ltac:(intros x Hx; cbn [outside] in Hx |- *; destruct Hx as [Hx1 _]; split; [clear - Hx1; lia | exact I])
      MD) as MD'.
    apply (K16 _ (munch_trans _ _ _ _ (munch_trans _ _ _ _ (munch_trans _ _ _ _ MA' MB') MC') MD') Wq
             (rr_rd_mono_trans _ _ _ (rr_rd_mono_trans _ _ _ (rr_rd_mono_trans _ _ _ RA RB) RC) RD) Iq).
    intros k Hk.
    destruct (Z_lt_le_dec k 4) as [H1|H1].
    - exact (rr_b4_rd _ _ BB2 k ltac:(clear - Hk H1; lia)).
    - destruct (Z_lt_le_dec k 8) as [H2|H2].
      + replace (G / 8 + ASAN_K + k) with (G / 8 + ASAN_K + 4 + (k - 4)) by ring.
        exact (rr_b4_rd _ _ BA3 (k - 4) ltac:(clear - H1 H2; lia)).
      + destruct (Z_lt_le_dec k 12) as [H3|H3].
        * replace (G / 8 + ASAN_K + k) with (G / 8 + ASAN_K + 8 + (k - 8)) by ring.
          exact (rr_b4_rd _ _ BD (k - 8) ltac:(clear - H2 H3; lia)).
        * replace (G / 8 + ASAN_K + k) with (G / 8 + ASAN_K + 12 + (k - 12)) by ring.
          exact (rr_b4_rd _ _ BC1 (k - 12) ltac:(clear - H3 Hk; lia)).
  Qed.

  (* rEI0 after writes inside the frame's 16 shadow bytes (the flag byte stays 1). *)
  Lemma rr_EI0_sh : forall G fv spc j nn mc mc', rFK G fv spc j nn -> rEI0 G j nn mc ->
    munch [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] mc mc' -> wmono rsegs mc mc' -> rr_rd_mono mc mc' ->
    mem_inv rsegs mc' -> rEI0 G j nn mc'.
  Proof.
    intros G fv spc j nn mc mc' HK (MU & WM & RM & MI1 & SV & AX & FP1 & TL & H120) MU5 WM5 RM5 MI5.
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & FRA & _ & SH1 & SH2).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (OUT5 : forall x, app_mem x -> outside [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] x)
      by (intros x Hx; apply rr_app_out_sh; [exact Hx | clear - SH1; lia | clear - SH2; lia]).
    assert (SUBf : sub_fp [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] (rWf G j nn)) by exact (rr_sh16_Wf G j nn).
    assert (MUf : munch (rWf G j nn) mc mc') by exact (munch_weaken _ _ mc mc' SUBf MU5).
    assert (SHO : forall x, S - 9072 <= x < S -> (x < G \/ G + 128 <= x) ->
                    outside [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] (shadow_addr x)).
    { intros x Hx HxG. cbn [outside]. split; [|exact I].
      pose proof (rr_sh_add8 G 16 FR8) as ESG. replace (G + 8 * 16) with (G + 128) in ESG by lia.
      unfold shadow_addr in ESG |- *. rewrite <- ESG.
      pose proof (rr_win_sh x G (G + 128) FR8 ltac:(clear - HxG; lia)) as HW.
      unfold shadow_addr in HW. exact HW. }
    split.
    { exact (munch_trans _ m mc mc' MU (munch_weaken _ _ mc mc'
             (fun x Hx => SUBf x (rWf_WB G fv spc j nn HK x (rWB_WP x Hx))) MU5)). }
    split; [exact (wmono_trans rsegs m mc mc' WM WM5)|].
    split; [exact (rr_rd_mono_trans m mc mc' RM RM5)|].
    split; [exact MI5|].
    split.
    { apply (rr_rw _ mc mc' _ _ SV MU5 WM5). intros x Hx. apply OUT5.
      unfold rSAVES in Hx. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in Hx.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right. clear - Hx HHM' HAE' HSK. lia. }
    split; [exact (rr_awx_munch G _ mc mc' AX MU5 SHO)|].
    destruct (rr_fp_td G fv spc j nn mc mc' HK FP1 TL MUf WM5 RM5
                ltac:(intros Hn; destruct (H120 Hn) as (_ & HB2); right;
                      destruct (rr_fsnum FS j) as (_ & E2j & _);
                      (eapply fl_bytes; [exact HB2 | exact MU5 |];
                       intros x Hx; cbn [length Z.of_nat Pos.of_succ_nat] in Hx; apply OUT5; apply F5;
                       rewrite E2j in Hx;
                       assert (Hjb : 0 <= j < 8192)
                         by (destruct (rk_place G fv spc j nn HK) as [(En & _)|(En & Hj & _)]; [lia | lia]);
                       clear - Hx Hjb; lia))) as (FP2 & TL2).
    split; [exact FP2|]. split; [exact TL2|].
    intros Hn. destruct (H120 Hn) as (HB1 & HB2). destruct (rr_fsnum FS j) as (_ & E2j & _).
    assert (Hjb : 0 <= j < 8192)
      by (destruct (rk_place G fv spc j nn HK) as [(En & _)|(En & Hj & _)]; [lia | lia]).
    split.
    - eapply fl_bytes; [exact HB1 | exact MU5 |]. intros x Hx. rewrite length_le8 in Hx. apply OUT5.
      replace x with (G + (x - G)) by ring. apply FAP. clear - Hx; lia.
    - eapply fl_bytes; [exact HB2 | exact MU5 |]. intros x Hx. cbn [length Z.of_nat Pos.of_succ_nat] in Hx.
      apply OUT5. apply F5. rewrite E2j in Hx. clear - Hx Hjb; lia.
  Qed.

  (* rTI after the 8-byte magic store at the frame base G. *)
  Lemma rr_TI_fr : forall G fv spc j nn mc mc', rFK G fv spc j nn -> rTI G j nn mc ->
    munch [(G, G + 8)] mc mc' -> wmono rsegs mc mc' -> rr_rd_mono mc mc' -> mem_inv rsegs mc' -> rTI G j nn mc'.
  Proof.
    intros G fv spc j nn mc mc' HK (MU & WM & RM & MI1 & SV & AX & FP1 & TL & FL) MU5 WM5 RM5 MI5.
    pose proof rA_facts as (HA32 & HAlo & HAhi).
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & FRA & _ & SH1 & SH2).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (SUBf : sub_fp [(G, G + 8)] (rWf G j nn)).
    { intros x Hx. unfold rWf in Hx. cbn [outside] in Hx. destruct Hx as (_ & _ & _ & HG & _).
      cbn [outside]. split; [clear - HG; lia | exact I]. }
    assert (MUf : munch (rWf G j nn) mc mc') by exact (munch_weaken _ _ mc mc' SUBf MU5).
    assert (OUTsh : forall x, S - 9072 <= x < S -> (x < G \/ G + 128 <= x) -> outside [(G, G + 8)] (shadow_addr x)).
    { intros x Hx HxG. cbn [outside]. split; [|exact I].
      assert (Hap : app_mem x)
        by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; clear - Hx HHM' HAE'; lia).
      pose proof (rt_app_shadow x Hap) as Hsh.
      assert (HN : ~ (G <= shadow_addr x < G + 8)).
      { apply (rr_sh_notapp (shadow_addr x) G (G + 8) Hsh). intros z Hz. replace z with (G + (z - G)) by lia.
        apply FAP. clear - Hz; lia. }
      clear - HN; lia. }
    split.
    { exact (munch_trans _ m mc mc' MU (munch_weaken _ _ mc mc'
             (fun x Hx => SUBf x (rWf_WB G fv spc j nn HK x (rWB_WP x Hx))) MU5)). }
    split; [exact (wmono_trans rsegs m mc mc' WM WM5)|].
    split; [exact (rr_rd_mono_trans m mc mc' RM RM5)|].
    split; [exact MI5|].
    split.
    { apply (rr_rw _ mc mc' _ _ SV MU5 WM5). intros x Hx.
      unfold rSAVES in Hx. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in Hx.
      cbn [outside]. split; [clear - Hx FRhi HAhi; lia | exact I]. }
    split; [exact (rr_awx_munch G _ mc mc' AX MU5 OUTsh)|].
    destruct (rr_fp_td G fv spc j nn mc mc' HK FP1 TL MUf WM5 RM5
                ltac:(intros Hn; destruct (FL Hn) as (_ & HB2); destruct (rr_fsnum FS j) as (_ & E2j & _);
                      assert (EGj : G = FS + 1085440 + j * 128 /\ 0 <= j < 8192)
                        by (destruct (rk_place G fv spc j nn HK) as [(En & _)|(En & Hj & EG)]; [lia|];
                            split; [exact EG | exact Hj]);
                      destruct HB2 as [HB2|HB2]; [left|right];
                      (eapply fl_bytes; [exact HB2 | exact MU5 |];
                       intros x Hx; cbn [length Z.of_nat Pos.of_succ_nat] in Hx; cbn [outside]; split; [|exact I];
                       rewrite E2j in Hx; clear - Hx EGj; lia))) as (FP2 & TL2).
    split; [exact FP2|]. split; [exact TL2|].
    intros Hn. destruct (FL Hn) as (HB1 & HB2). destruct (rr_fsnum FS j) as (_ & E2j & _).
    assert (EGj : G = FS + 1085440 + j * 128 /\ 0 <= j < 8192)
      by (destruct (rk_place G fv spc j nn HK) as [(En & _)|(En & Hj & EG)]; [lia|]; split; [exact EG | exact Hj]).
    split.
    - eapply fl_bytes; [exact HB1 | exact MU5 |]. intros x Hx. rewrite length_le8 in Hx. cbn [outside].
      split; [clear - Hx; lia | exact I].
    - destruct HB2 as [HB2|HB2]; [left|right];
        (eapply fl_bytes; [exact HB2 | exact MU5 |];
         intros x Hx; cbn [length Z.of_nat Pos.of_succ_nat] in Hx; cbn [outside]; split; [|exact I];
         rewrite E2j in Hx; clear - Hx EGj; lia).
  Qed.

  (* rTI after the flag byte at fs_flag FS 1 j is cleared to 0 (side frame, nn = 1). *)
  Lemma rr_TI_flag : forall G fv spc j nn mc mc', rFK G fv spc j nn -> nn = 1 -> rTI G j nn mc ->
    munch [(fs_flag FS 1 j, fs_flag FS 1 j + 1)] mc mc' -> wmono rsegs mc mc' -> rr_rd_mono mc mc' ->
    mem_inv rsegs mc' -> bytes_at rsegs mc' (fs_flag FS 1 j) [Z_to_bv 8 0] -> rTI G j nn mc'.
  Proof.
    intros G fv spc j nn mc mc' HK En (MU & WM & RM & MI1 & SV & AX & FP1 & TL & FL) MU5 WM5 RM5 MI5 HBF.
    pose proof rA_facts as (HA32 & HAlo & HAhi).
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & FRA & _ & SH1 & SH2).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (rr_fsnum FS j) as (_ & E2j & _).
    assert (EGj : G = FS + 1085440 + j * 128 /\ 0 <= j < 8192)
      by (destruct (rk_place G fv spc j nn HK) as [(E0 & _)|(_ & Hj & EG)]; [lia|]; split; [exact EG | exact Hj]).
    assert (FGE : app_mem (fs_flag FS 1 j)) by (apply F5; rewrite E2j; clear - EGj; lia).
    assert (SUBf : sub_fp [(fs_flag FS 1 j, fs_flag FS 1 j + 1)] (rWf G j nn)).
    { intros x Hx. unfold rWf in Hx. cbn [outside] in Hx. destruct Hx as (_ & _ & HFl & _).
      cbn [outside]. split; [clear - HFl En; subst nn; lia | exact I]. }
    assert (MUf : munch (rWf G j nn) mc mc') by exact (munch_weaken _ _ mc mc' SUBf MU5).
    assert (OUTsh : forall x, S - 9072 <= x < S -> (x < G \/ G + 128 <= x) ->
                      outside [(fs_flag FS 1 j, fs_flag FS 1 j + 1)] (shadow_addr x)).
    { intros x Hx HxG. cbn [outside]. split; [|exact I].
      assert (Hap : app_mem x)
        by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *; clear - Hx HHM' HAE'; lia).
      pose proof (rt_app_shadow x Hap) as Hsh.
      assert (HN : ~ (fs_flag FS 1 j <= shadow_addr x < fs_flag FS 1 j + 1)).
      { apply (rr_sh_notapp (shadow_addr x) (fs_flag FS 1 j) (fs_flag FS 1 j + 1) Hsh).
        intros z Hz. assert (Ez : z = fs_flag FS 1 j) by (clear - Hz; lia). rewrite Ez. exact FGE. }
      clear - HN; lia. }
    split.
    { exact (munch_trans _ m mc mc' MU (munch_weaken _ _ mc mc'
             (fun x Hx => SUBf x (rWf_WB G fv spc j nn HK x (rWB_WP x Hx))) MU5)). }
    split; [exact (wmono_trans rsegs m mc mc' WM WM5)|].
    split; [exact (rr_rd_mono_trans m mc mc' RM RM5)|].
    split; [exact MI5|].
    split.
    { apply (rr_rw _ mc mc' _ _ SV MU5 WM5). intros x Hx.
      unfold rSAVES in Hx. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in Hx.
      cbn [outside]. split; [rewrite E2j; clear - Hx EGj F4 HHM' HSK; lia | exact I]. }
    split; [exact (rr_awx_munch G _ mc mc' AX MU5 OUTsh)|].
    destruct (rr_fp_td G fv spc j nn mc mc' HK FP1 TL MUf WM5 RM5 ltac:(intros _; left; exact HBF))
      as (FP2 & TL2).
    split; [exact FP2|]. split; [exact TL2|].
    intros Hn. destruct (FL Hn) as (HB1 & _). split.
    - eapply fl_bytes; [exact HB1 | exact MU5 |]. intros x Hx. rewrite length_le8 in Hx. cbn [outside].
      split; [rewrite E2j; clear - Hx EGj; lia | exact I].
    - left. exact HBF.
  Qed.

  (* ===== Segment 6 (real frame): 0x84c3c .. ret, the shadow bytes 0. ===== *)
  Lemma rp_td_real : forall G fv spc j nn mc r
      (x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
    rFK G fv spc j nn -> nn = 0 -> rTI G j nn mc -> (reply_ok fr len pa pp pn g = true -> rOUTF mc) ->
    r = reply_ret fr len pa pp pn g ->
    evtF rsegs RNG rQ (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                        x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (G / 8 + ASAN_K)) x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x84c3c) fc None mc (seg_rom rsegs)).
  Proof.
    intros G fv spc j nn mc r x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28
      x29 x30 x31 HK En TI HOF Er.
    pose proof TI as (MUt & WMt & RMt & MI1t & SVt & AXt & FPt & TLt & FLt).
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & FRA & _ & SH1 & SH2).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6). pose proof rA_facts as (HA32 & HAlo & HAhi).
    assert (HG0 : 0 <= G) by (clear - FRlo F1; lia).
    assert (SWmc : shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) mc)
      by exact (rr_shadow_rw_on_mono _ m mc SW WMt RMt).
    assert (SWh : forall i, 0 <= i < 16 -> wview rsegs mc (wa (G / 8 + ASAN_K + i)) <> None).
    { intros i Hi.
      apply (rr_stk_wv mc _ _ _ (rr_shadow16_stk_on _ mc G SWmc (rk_inR _ _ _ _ _ HK) HG0 FRA SH1 SH2)).
      clear - Hi; lia. }
    apply (rr_z16 G mc rQ x1 x2 x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
             x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) SWh MI1t
             (rrF_frame_blk G fv spc j nn HK)).
    intros m16 MU16 WM16 RM16 MI16 Z16.
    pose proof (rr_TI_sh G fv spc j nn mc m16 HK TI MU16 WM16 RM16 MI16) as TI16.
    pose proof TI16 as (MUf & WMf & RMf & MIf & SVf & AXf & FPf & TLf & FLf).
    assert (HGaddr : nn = 0 -> addressable m16 G 128).
    { intros _. apply rr_frame_all_addr; [exact HG0 | exact FR8
        | clear - FRhi HAhi HAE; lia | exact FAP | exact Z16]. }
    eapply rp_ret.
    - split; [exact MUf|]. split; [exact WMf|]. split; [exact RMf|]. split; [exact MIf|]. split; [exact SVf|].
      split; [exact (rr_win_addr_full G fv spc j nn m16 HK AXf HGaddr)|]. split; [exact FPf | exact TLf].
    - intros HOK. exact (rr_OUTF_wf G fv spc j nn mc m16 HK
        (munch_weaken _ _ mc m16 (rr_sh16_Wf G j nn) MU16) WM16 HOK (HOF HOK)).
    - exact Er.
  Qed.

  (* The frame base word [G, G+8) and the flag byte are inside the prologue's footprint. *)
  Lemma rr_frame8_Wf : forall G j nn, sub_fp [(G, G + 8)] (rWf G j nn).
  Proof.
    intros G j nn x Hx. unfold rWf in Hx. cbn [outside] in Hx. destruct Hx as (_ & _ & _ & HG & _).
    cbn [outside]. split; [clear - HG; lia | exact I].
  Qed.

  Lemma rr_flagj_Wf : forall G j, sub_fp [(fs_flag FS 1 j, fs_flag FS 1 j + 1)] (rWf G j 1).
  Proof.
    intros G j x Hx. unfold rWf in Hx. cbn [outside] in Hx. destruct Hx as (_ & _ & HFl & _).
    cbn [outside]. split; [clear - HFl; lia | exact I].
  Qed.

  (* ===== The cut at the inline flag release (bF-glue.md; the glue takes the store 0x84c34 `sb zero,0(a1)` by
     ProgWorld.ctl_release_of_free_law 1, the journal switching AT the store). Segment 6 (side frame) is split
     there: rp_td_pre_F runs 0x84bec .. 0x84c34 (the 16 shadow bytes 0xf5, then `ld a1,120(s2)`), ending AT the
     store with a1 = fs_flag FS 1 j; rp_td_post_F runs from 0x84c38 (`j 0x84c7c`, then rp_ret). Their scripts are
     rp_td_side's, which now chains them around the store. ===== *)
  Lemma rp_td_pre_F : forall G spc j nn mc r
      (x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
    rFK G G spc j nn -> nn = 1 -> rTI G j nn mc ->
    evtF rsegs RNG
      (fun ms' => exists m16 : word -> option byte,
         rTI G j nn m16 /\ munch [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] mc m16 /\ wmono rsegs mc m16 /\
         ms' = MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 r) (Z_to_bv 64 (fs_flag FS 1 j))
                       x12 x13 x14 x15 x16 x17 (Z_to_bv 64 G) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (G / 8 + ASAN_K))
                       x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x84c34) fc None m16 (seg_rom rsegs))
      (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 G) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (G / 8 + ASAN_K)) x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x84bec) fc None mc (seg_rom rsegs)).
  Proof.
    intros G spc j nn mc r x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31
      HK En TI.
    pose proof TI as (MUt & WMt & RMt & MI1t & SVt & AXt & FPt & TLt & FLt).
    destruct (rk_facts G G spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & FRA & _ & SH1 & SH2).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6). pose proof rA_facts as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (rr_fsnum FS j) as (_ & E2j & _).
    assert (EGj : G = FS + 1085440 + j * 128 /\ 0 <= j < 8192)
      by (destruct (rk_place G G spc j nn HK) as [(E0 & _)|(_ & Hj & EG)]; [lia|]; split; [exact EG | exact Hj]).
    pose proof (rrF_frame G G spc j nn HK) as RGFRM. pose proof (rrF_frame_blk G G spc j nn HK) as SBFRM.
    assert (RGFLj : rng RNG (fs_flag FS 1 j) 1).
    { assert (EMj : fs_M 1 = 8192) by reflexivity. destruct EGj as (_ & Hj8).
      eapply rng_sub; [exact RFLG | rewrite !rrF_fs_flag1; lia | rewrite !rrF_fs_flag1; lia]. }
    assert (HG0 : 0 <= G) by (clear - FRlo F1; lia).
    assert (SWmc : shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) mc)
      by exact (rr_shadow_rw_on_mono _ m mc SW WMt RMt).
    assert (SWh : forall i, 0 <= i < 16 -> wview rsegs mc (wa (G / 8 + ASAN_K + i)) <> None).
    { intros i Hi.
      apply (rr_stk_wv mc _ _ _ (rr_shadow16_stk_on _ mc G SWmc (rk_inR _ _ _ _ _ HK) HG0 FRA SH1 SH2)).
      clear - Hi; lia. }
    pose proof (munch_refl [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] mc) as Mq.
    pose proof (wmono_refl rsegs mc) as Wq. pose proof (rr_rd_mono_refl mc) as Rq. pose proof MI1t as Iq.
    step. (* li a1,-11 *)
    rwstb (G / 8 + ASAN_K + 4) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 4) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 5) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 5) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 6) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 6) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 7) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 7) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 1) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 1) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 2) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 2) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 3) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 3) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 12) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 12) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 13) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 13) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 14) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 14) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 15) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 15) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 8) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 8) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 9) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 9) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 10) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 10) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 11) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 11) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    (* at 0x84c30: ld a1,120(s2=G); a1 := fs_flag FS 1 j *)
    pose proof (rr_TI_sh G G spc j nn mc _ HK TI Mq Wq Rq Iq) as TI16.
    pose proof TI16 as (MU16t & WM16t & RM16t & MI16t & SV16t & AX16t & FP16t & TL16t & FL16t).
    destruct (FL16t En) as (HB120 & _).
    pose proof (rr_ro8 _ _ _ HB120) as RO120.
    step. (* ld a1,120(s2) *)
    apply evtF_done. cbv beta. eexists.
    split; [exact TI16|]. split; [exact Mq|]. split; [exact Wq|]. reflexivity.
  Qed.

  (* 0x84c38 .. ret: after the flag store, `j 0x84c7c` and rp_ret. *)
  Lemma rp_td_post_F : forall G spc j nn mc r
      (x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
    rFK G G spc j nn -> nn = 1 -> rTI G j nn mc -> (reply_ok fr len pa pp pn g = true -> rOUTF mc) ->
    r = reply_ret fr len pa pp pn g ->
    evtF rsegs RNG rQ (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 G) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (G / 8 + ASAN_K)) x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x84c38) fc None mc (seg_rom rsegs)).
  Proof.
    intros G spc j nn mc r x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31
      HK En TI HOF Er.
    pose proof TI as (MU18 & WM18 & RM18 & MI18 & SV18 & AX18 & FP18 & TL18 & FL18).
    step. (* j 0x84c7c *)
    eapply rp_ret.
    - split; [exact MU18|]. split; [exact WM18|]. split; [exact RM18|]. split; [exact MI18|]. split; [exact SV18|].
      split; [exact (rr_win_addr_full G G spc j nn mc HK AX18 ltac:(intros E0; exfalso; clear - E0 En; lia))|].
      split; [exact FP18 | exact TL18].
    - exact HOF.
    - exact Er.
  Qed.

  (* ===== Segment 6 (side frame): 0x84bec .. 0x84c38, the shadow bytes 0xf5 and the flag byte 0: rp_td_pre_F, the
     store, rp_td_post_F. ===== *)
  Lemma rp_td_side : forall G fv spc j nn mc r
      (x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
    rFK G fv spc j nn -> nn = 1 -> fv = G -> rTI G j nn mc -> (reply_ok fr len pa pp pn g = true -> rOUTF mc) ->
    r = reply_ret fr len pa pp pn g ->
    evtF rsegs RNG rQ (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 fv) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (G / 8 + ASAN_K)) x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x84bec) fc None mc (seg_rom rsegs)).
  Proof.
    intros G fv spc j nn mc r x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29
      x30 x31 HK En Efv TI HOF Er. subst fv.
    pose proof TI as (MUt & WMt & RMt & MI1t & SVt & AXt & FPt & TLt & FLt).
    destruct (rk_facts G G spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & FRA & _ & SH1 & SH2).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6). pose proof rA_facts as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (rr_fsnum FS j) as (_ & E2j & _).
    assert (EGj : G = FS + 1085440 + j * 128 /\ 0 <= j < 8192)
      by (destruct (rk_place G G spc j nn HK) as [(E0 & _)|(_ & Hj & EG)]; [lia|]; split; [exact EG | exact Hj]).
    pose proof (rrF_frame G G spc j nn HK) as RGFRM. pose proof (rrF_frame_blk G G spc j nn HK) as SBFRM.
    assert (RGFLj : rng RNG (fs_flag FS 1 j) 1).
    { assert (EMj : fs_M 1 = 8192) by reflexivity. destruct EGj as (_ & Hj8).
      eapply rng_sub; [exact RFLG | rewrite !rrF_fs_flag1; lia | rewrite !rrF_fs_flag1; lia]. }
    eapply evtF_cut;
      [exact (rp_td_pre_F G spc j nn mc r x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 HK En TI) |].
    intros ms' (m16 & TI16 & Mq & Wq & ->).
    pose proof TI16 as (MU16t & WM16t & RM16t & MI16t & SV16t & AX16t & FP16t & TL16t & FL16t).
    pose proof FP16t as (DT & TS & C & T & DB & k & _ & _ & (P1 & P2 & P3 & P4 & P5) & _).
    pose proof (rr_stk_wv _ FS (FS + FS_SIZE) (fs_flag FS 1 j) P5
                  ltac:(rewrite E2j; unfold FS_SIZE; clear - EGj; lia)) as WVF.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m16 _) =>
      assert (BqF : bytes_at rsegs m16 (fs_flag FS 1 j) (@nil byte))
        by (split; [rewrite E2j; clear - EGj F1; lia|]; split;
              [cbn [length Z.of_nat]; rewrite E2j; clear - EGj F4 HAE'; lia | intros i Hi; cbn [length] in Hi; lia]);
      assert (HSF : store_ok rsegs m16 (wa (fs_flag FS 1 j)) 1 = true)
        by (eapply rr_wv_store_ok;
              [ intros i Hi; replace (fs_flag FS 1 j + i) with (fs_flag FS 1 j) by (clear - Hi; lia); exact WVF
              | exact (wmono_refl rsegs m16) | rewrite E2j; clear - EGj F1; lia
              | rewrite E2j; clear - EGj F4 HAE'; lia ]) end.
    step. rewrite rr_le1_0.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m16 _ _) _) =>
      destruct (rr_sb_step _ _ m16 (fs_flag FS 1 j) 1 (@nil byte) (Z_to_bv 8 0) (fs_flag FS 1 j)
                  ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) ltac:(rewrite E2j; clear - EGj F1; lia)
                  ltac:(rewrite E2j; clear - EGj F4 HAE'; lia) ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; lia)
                  BqF (munch_refl [(fs_flag FS 1 j, fs_flag FS 1 j + 1)] m16) (wmono_refl rsegs m16)
                  (rr_rd_mono_refl m16) MI16t HSF) as (BqF' & MqF' & WqF' & RqF' & IqF') end.
    cbn [app] in BqF'.
    pose proof (rr_TI_flag G G spc j nn _ _ HK En TI16 MqF' WqF' RqF' IqF' BqF') as TI18.
    pose proof TI18 as (MU18 & WM18 & RM18 & MI18 & SV18 & AX18 & FP18 & TL18 & FL18).
    pose proof (munch_trans _ mc _ _
      (munch_weaken _ _ mc _ (rr_sh16_Wf G j nn) Mq)
      (munch_weaken [(fs_flag FS 1 j, fs_flag FS 1 j + 1)] (rWf G j nn) _ _
         ltac:(rewrite En; exact (rr_flagj_Wf G j)) MqF')) as MUrwf.
    exact (rp_td_post_F G spc j nn _ r x1 x2 x5 x6 x7 x9 (Z_to_bv 64 (fs_flag FS 1 j)) x12 x13 x14 x15 x16 x17 x19
             x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 HK En TI18
             (fun HOK => rr_OUTF_wf G G spc j nn mc _ HK MUrwf (wmono_trans rsegs mc _ _ Wq WqF') HOK (HOF HOK)) Er).
  Qed.

  (* ===== Segment 6 entry: 0x84bdc .. the frame choice (rKE Q is the teardown from 0x84bdc). ===== *)
  Lemma rp_epi : rKE rQ.
  Proof.
    intros G fv spc j nn mc r x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30
      x31 HK EI HOF Er.
    pose proof (rTI_of_EI0 G j nn mc EI) as TI.
    pose proof TI as (MUt & WMt & RMt & MI1t & SVt & AXt & FPt & TLt & FLt).
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & FRA & _ & SH1 & SH2).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6). pose proof rA_facts as (HA32 & HAlo & HAhi).
    assert (HG0 : 0 <= G) by (clear - FRlo F1; lia).
    pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
    pose proof (rrF_frame G fv spc j nn HK) as RGFRM.
    assert (WVG : forall i, 0 <= i < 8 -> wview rsegs mc (wa (G + i)) <> None).
    { intros i Hi. destruct (rk_facts G fv spc j nn HK) as (_ & _ & _ & _ & FW & _).
      apply WMt. apply FW. clear - Hi; lia. }
    pose proof (munch_refl [(G, G + 8)] mc) as Mqg. pose proof (wmono_refl rsegs mc) as Wqg.
    pose proof (rr_rd_mono_refl mc) as Rqg. pose proof MI1t as Iqg.
    do 2 step. (* lui a1; addiw a1 *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HSG : store_ok rsegs mm (wa G) 8 = true)
        by (eapply rr_wv_store_ok;
              [ intros i Hi; apply WVG; clear - Hi; lia | exact (wmono_refl rsegs mm)
              | clear - HG0; lia | clear - FRhi HAhi HAE'; lia ]) end.
    step. (* sd a1,0(s10) *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 G 8 G bs 8%nat ltac:(apply length_le8) ltac:(clear - HG0; lia)
        ltac:(clear - FRhi HAhi HAE'; lia) ltac:(clear - HG0; lia) ltac:(clear - HG0; lia)
        Mqg Wqg Rqg Iqg HSG) as (Mqg' & Wqg' & Rqg' & Iqg') end.
    clear Mqg Wqg Rqg Iqg HSG. rename Mqg' into Mqg, Wqg' into Wqg, Rqg' into Rqg, Iqg' into Iqg.
    pose proof (rr_TI_fr G fv spc j nn mc _ HK TI Mqg Wqg Rqg Iqg) as TIg.
    step. (* beqz s2 *)
    pose proof HK as HKc.
    destruct HKc as [(Efv0 & EG0 & Esp0 & Ej0 & En0)|(Hj1 & EG1 & Efv1 & Esp1 & En1)].
    - (* nn = 0, fv = 0: beqz taken -> 0x84c3c *)
      rewrite (rc_beq0_true fv Efv0). cbv iota.
      eapply rp_td_real; [exact HK | exact En0 | exact TIg
        | intros HOK; exact (rr_OUTF_wf G fv spc j nn mc _ HK
            (munch_weaken _ _ mc _ (rr_frame8_Wf G j nn) Mqg) Wqg HOK (HOF HOK))
        | exact Er].
    - (* nn = 1, fv = G: beqz not taken -> 0x84bec *)
      assert (Gpos : 0 < G) by (clear - FRlo F1; lia).
      assert (Gub : G < 2 ^ 64) by (clear - FRhi HAhi HS; lia).
      rewrite (rc_beq0_false fv ltac:(rewrite Efv1; clear - Gpos; lia)
                 ltac:(rewrite Efv1; clear - Gpos Gub; lia)). cbv iota.
      eapply rp_td_side; [exact HK | exact En1 | exact Efv1 | exact TIg
        | intros HOK; exact (rr_OUTF_wf G fv spc j nn mc _ HK
            (munch_weaken _ _ mc _ (rr_frame8_Wf G j nn) Mqg) Wqg HOK (HOF HOK))
        | exact Er].
  Qed.

  (* 0x84bc4: the join of the fail and success paths (a0 = r), before the shared teardown. *)
  Definition rKT (Q : machine_state -> Prop) : Prop :=
    forall G fv spc j nn mc r (x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29
                               x30 x31 : word),
      rFK G fv spc j nn -> rEI0 G j nn mc -> (reply_ok fr len pa pp pn g = true -> rOUTF mc) ->
      r = reply_ret fr len pa pp pn g ->
      evtF rsegs RNG Q (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 fv) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) x27
                        x28 x29 x30 x31) F (Z_to_bv 64 0x84bc4) fc None mc (seg_rom rsegs)).

  (* 0x84bc4 .. 0x84bdc: the 5 shadow bytes 0xf8, then rKE. *)
  Lemma rp_f8 : forall Q, rKE Q -> rKT Q.
  Proof.
    intros Q KE G fv spc j nn mc r x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29
      x30 x31 HK EI HOF Er.
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & FRA & _ & SH1 & SH2).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    assert (HG0 : 0 <= G) by (clear - FRlo F1; lia).
    pose proof (rrF_frame_blk G fv spc j nn HK) as SBFRM.
    pose proof EI as (MUe & WMe & RMe & MI1e & SVe & AXe & FPe & TLe & H120e).
    assert (SWmc : shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) mc)
      by exact (rr_shadow_rw_on_mono _ m mc SW WMe RMe).
    assert (SWh : forall i, 0 <= i < 16 -> wview rsegs mc (wa (G / 8 + ASAN_K + i)) <> None).
    { intros i Hi.
      apply (rr_stk_wv mc _ _ _ (rr_shadow16_stk_on _ mc G SWmc (rk_inR _ _ _ _ _ HK) HG0 FRA SH1 SH2)).
      clear - Hi; lia. }
    pose proof (munch_refl [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] mc) as Mq.
    pose proof (wmono_refl rsegs mc) as Wq. pose proof (rr_rd_mono_refl mc) as Rq. pose proof MI1e as Iq.
    step. (* li a1,-8 *)
    rwstb (G / 8 + ASAN_K + 4) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 4) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 5) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 5) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 6) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 6) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 7) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 7) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 8) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 8) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    pose proof (rr_EI0_sh G fv spc j nn mc _ HK EI Mq Wq Rq Iq) as EI5.
    eapply KE; [exact HK | exact EI5
      | intros HOK; exact (rr_OUTF_wf G fv spc j nn mc _ HK
          (munch_weaken _ _ mc _ (rr_sh16_Wf G j nn) Mq) Wq HOK (HOF HOK))
      | exact Er].
  Qed.

  (* 0x84bc0: the fail exit (args valid but the record is not a reply): a0 := 0, to rKT with r = 0. *)
  Definition rKV (Q : machine_state -> Prop) : Prop :=
    forall G fv spc j nn mc (x1 x2 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29
                             x30 x31 : word),
      rFK G fv spc j nn -> rEI0 G j nn mc -> reply_args fr pa pp pn = true -> ir len g = false ->
      evtF rsegs RNG Q (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 x10 x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 fv) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) x27
                        x28 x29 x30 x31) F (Z_to_bv 64 0x84bc0) fc None mc (seg_rom rsegs)).

  Lemma rp_fail : forall Q, rKT Q -> rKV Q.
  Proof.
    intros Q KT G fv spc j nn mc x1 x2 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28
      x29 x30 x31 HK EI RAb EIR.
    assert (RR : reply_ret fr len pa pp pn g = 0) by (unfold reply_ret; rewrite RAb, EIR; reflexivity).
    assert (OK : reply_ok fr len pa pp pn g = false) by (unfold reply_ok; rewrite RAb, EIR; reflexivity).
    step. (* li a0,0 *)
    eapply KT; [exact HK | exact EI | intros HOK; rewrite OK in HOK; discriminate | symmetry; exact RR].
  Qed.

  (* ===================== Segment 5: the output stores (0x84cbc .. 0x84d68) ===================== *)
  (* An aligned 8-byte access reads a shadow byte 0 (the whole granule is addressable: byte p+7 forces it). *)
  Lemma rr_shadow0 : forall mc p n, addressable mc p n -> p mod 8 = 0 -> 8 <= n ->
    exists k : byte, ov_read_bytes rsegs mc (wa (p / 8 + ASAN_K)) 1 = Some [k] /\ bv_signed k = 0.
  Proof.
    intros mc p n AD Hmod Hn. pose proof AD as (Hp & Hn0 & Hend & HA).
    destruct (rt_addr_byte mc (p + 7) (HA 7 ltac:(lia))) as (k & Hbytes & Hok).
    unfold asan_shadow in Hbytes.
    assert (Eq7 : (p + 7) / 8 = p / 8) by (clear - Hmod; Z.div_mod_to_equations; lia).
    rewrite Eq7 in Hbytes.
    exists k. split.
    - pose proof (rd_byte rsegs mc (p / 8 + ASAN_K) [k] 0%nat Hbytes ltac:(cbn [length]; lia)) as RD.
      cbn [nth Z.of_nat] in RD. rewrite Z.add_0_r in RD. exact RD.
    - unfold shadow_ok in Hok. assert (Hm7 : (p + 7) mod 8 = 7) by (clear - Hmod; Z.div_mod_to_equations; lia).
      destruct Hok as [H0|(Hlt & Hle)]; [exact H0 | rewrite Hm7 in Hlt; lia].
  Qed.

  (* ===================== Segment 5: the three OUT stores (0x84cbc .. 0x84d6c) ===================== *)

  (* A hypothesis the step machinery must not transport: wrapped while a run of stores goes by. *)
  Definition rr_hide (P : Prop) : Prop := P.
  Lemma rr_hide_in : forall P : Prop, P -> rr_hide P. Proof. intros P H. exact H. Qed.
  Lemma rr_hide_out : forall P : Prop, rr_hide P -> P. Proof. intros P H. exact H. Qed.

  Definition rOUTW : list ivl := [(pa, pa + 2); (pp, pp + 8); (pn, pn + 8)].

  (* OUT is apart from the side stack's header [FS, FS + 36864). *)
  Lemma rr_out_hdr : reply_args fr pa pp pn = true -> forall x, FS <= x < FS + 36864 -> outside rOUTW x.
  Proof.
    intros RA x Hx.
    pose proof FP0 as (DT & TS & C & T & DB & kk & _ & _ & _ & _ & _ & _ & _ & _ & HWd & _).
    assert (HDy : outside rWW x).
    { eapply (fl_dj_out _ _ FS (fs_frame FS 0 0) x HWd);
        [ apply in_or_app; right; left; reflexivity
        | replace (fs_frame FS 0 0) with (FS + 36864)
            by (unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; lia);
          exact Hx ]. }
    unfold rWW, reac_ctrl_identity_reply_W, REAC_CTRL_IDENTITY_REPLY_K in HDy. rewrite RA in HDy.
    unfold rOUTW. cbn [outside] in HDy |- *. destruct HDy as (_ & H1 & H2 & H3 & _).
    exact (conj H1 (conj H2 (conj H3 I))).
  Qed.

  (* OUT is apart from the class-1 frames of the side stack. *)
  Lemma rr_out_frames : reply_args fr pa pp pn = true ->
    forall x, fs_frame FS 1 0 <= x < fs_frame FS 1 (fs_M 1) -> outside rOUTW x.
  Proof.
    intros RA x Hx.
    pose proof FP0 as (DT & TS & C & T & DB & kk & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDd).
    assert (HDy : outside rDD x).
    { eapply (fl_dj_out _ _ (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1)) x HDd);
        [ cbn [fp_w flat_map fp_w1 app]; right; right; left; reflexivity | exact Hx ]. }
    unfold rDD, reac_ctrl_identity_reply_D in HDy. rewrite RA in HDy. unfold rOUTW.
    destruct (len <? 50); cbn [app outside] in HDy |- *;
      [ destruct HDy as (H1 & H2 & H3 & _) | destruct HDy as (_ & H1 & H2 & H3 & _) ];
      exact (conj H1 (conj H2 (conj H3 I))).
  Qed.

  (* The shadow of application memory is apart from OUT (OUT is application memory). *)
  Lemma rr_sh_outOUT : forall mz, addressable mz pa 2 -> addressable mz pp 8 -> addressable mz pn 8 ->
    forall y, app_mem y -> outside rOUTW (shadow_addr y).
  Proof.
    intros mz Aa Ap An y Hy. assert (Hsh : in_shadow (shadow_addr y)) by (apply rt_app_shadow; exact Hy).
    unfold rOUTW. cbn [outside].
    split; [ intros [H1 H2]; apply (rr_app_not_shadow (shadow_addr y)); [| exact Hsh];
             replace (shadow_addr y) with (pa + (shadow_addr y - pa)) by lia;
             apply (rr_app_in mz pa 2); [ exact Aa | lia ] |].
    split; [ intros [H1 H2]; apply (rr_app_not_shadow (shadow_addr y)); [| exact Hsh];
             replace (shadow_addr y) with (pp + (shadow_addr y - pp)) by lia;
             apply (rr_app_in mz pp 8); [ exact Ap | lia ] |].
    split; [ intros [H1 H2]; apply (rr_app_not_shadow (shadow_addr y)); [| exact Hsh];
             replace (shadow_addr y) with (pn + (shadow_addr y - pn)) by lia;
             apply (rr_app_in mz pn 8); [ exact An | lia ] | exact I ].
  Qed.

  Lemma rOUTW_WP : reply_ok fr len pa pp pn g = true -> sub_fp rOUTW rWP.
  Proof.
    intros OK x Hx. unfold rWP, reac_ctrl_identity_reply_fp, REAC_CTRL_IDENTITY_REPLY_K in Hx.
    apply rr_out_app_inv in Hx as [H1 _]. rewrite OK in H1. cbn [app outside] in H1.
    unfold rOUTW. cbn [outside]. destruct H1 as (A1 & A2 & A3 & _). exact (conj A1 (conj A2 (conj A3 I))).
  Qed.

  Lemma rOUTW_full : reply_args fr pa pp pn = true -> sub_fp rOUTW (rWW ++ fp_w [1%nat] FS ++ rYY).
  Proof.
    intros RA x Hx. apply rr_out_app_inv in Hx as [H1 _].
    unfold rWW, reac_ctrl_identity_reply_W, REAC_CTRL_IDENTITY_REPLY_K in H1. rewrite RA in H1.
    unfold rOUTW. cbn [outside] in H1 |- *. destruct H1 as (_ & A1 & A2 & A3 & _).
    exact (conj A1 (conj A2 (conj A3 I))).
  Qed.

  (* The alignment and pointer-test facts of the UBSan checks (as lib/U/Prog/reac_ctrl_identity_reply.v). *)
  Lemma rr_land1 : forall x, x mod 2 = 0 -> 0 <= x < 2^64 ->
    Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 x)) 1) = Z_to_bv 64 0.
  Proof using.
    intros x H R. rewrite unsigned_lit by (clear - R; lia). change 1 with (Z.ones 1).
    rewrite Z.land_ones by (clear - R; lia).
    change (2^1) with 2. rewrite H. reflexivity.
  Qed.

  Lemma rr_land7 : forall x, x mod 8 = 0 -> 0 <= x < 2^64 ->
    Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 x)) 7) = Z_to_bv 64 0.
  Proof using.
    intros x H R. rewrite unsigned_lit by (clear - R; lia). change 7 with (Z.ones 3).
    rewrite Z.land_ones by (clear - R; lia).
    change (2^3) with 8. rewrite H. reflexivity.
  Qed.

  Lemma rr_ltu_negr : forall x y, 0 <= x -> -2^64 < y < 0 -> x < 2^64 + y ->
    bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = true.
  Proof using.
    intros x y Hx Hy Hxy. unfold bv_ltu. rewrite (unsigned_lit x) by (clear - Hx Hy Hxy; lia).
    rewrite unsigned_lit_wrap. apply Z.ltb_lt. clear - Hx Hy Hxy.
    change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
  Qed.

  Lemma rr_eqb_m1 : bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0) = false.
  Proof using. unfold bv_eqb. rewrite !unsigned_lit_wrap. reflexivity. Qed.

  (* The bytes of rw_cells are readable. *)
  Lemma rr_rw_rd : forall mz A cs y, rw_cells rsegs mz A cs ->
    A <= y < A + Z.of_nat (length (cells_bytes cs)) -> exists b, mrd rsegs mz (wa y) = Some b.
  Proof using. intros mz A cs y [[_ HB] _] Hy. exact (rr_bytes_rd mz A _ y HB Hy). Qed.

  (* A UBSan pointer test `li a0,-c; bltu a0,s7` with s7 = fr + 18: not taken. *)
  Ltac rubn c := step; step; rewrite (rr_ltu_negl (fr + 18) c) by lia; cbv iota.
  (* An alignment test `andi; bnez` that is not taken. *)
  Ltac rbnz0 := rewrite (rc_eqb64 0 0) by lia; change (0 =? 0) with true; cbn [negb]; cbv iota.

  (* 0x84cbc: the success exit of the tag tests: the three OUT stores, then a0 = 1 and the teardown join. *)
  Definition rKS (Q : machine_state -> Prop) : Prop :=
    forall (G fv spc j nn : Z) (mc : word -> option byte)
           (x1 x2 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      rFK G fv spc j nn -> rJB G j nn mc -> reply_ok fr len pa pp pn g = true ->
      evtF rsegs RNG Q (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 rA) x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 fv) (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa)
                         (Z_to_bv 64 (fr + 18)) (Z_to_bv 64 (ir_s g)) (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G)
                         (wa ASAN_K) x28 x29 x30 x31)
                    F (Z_to_bv 64 0x84cbc) fc None mc (seg_rom rsegs)).

  (* rEI0 after writes inside OUT only (the three OUT stores of the success path). *)
  Lemma rr_EI0_out : forall G fv spc j nn mc, rFK G fv spc j nn -> reply_ok fr len pa pp pn g = true ->
    munch rWB m mc -> rCore G j nn mc -> addressable mc pa 2 -> addressable mc pp 8 -> addressable mc pn 8 ->
    forall mf, munch rOUTW mc mf -> wmono rsegs mc mf -> rr_rd_mono mc mf -> mem_inv rsegs mf -> rEI0 G j nn mf.
  Proof.
    intros G fv spc j nn mc HK OKr MUb CORE ADpa ADpp ADpn mf MUo WQ RQ MIf.
    assert (RAb : reply_args fr pa pp pn = true)
      by (unfold reply_ok in OKr; destruct (reply_args fr pa pp pn); [reflexivity | discriminate]).
    destruct CORE as (WMc & RMc & MIc & SVc & AXc & FPc & TLc & FLc).
    destruct (HO RAb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Wpa & Wpp & Wpn).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof (rr_out_hdr RAb) as OUThdr. pose proof (rr_out_frames RAb) as OUTfr.
    pose proof (rr_sh_outOUT mc ADpa ADpp ADpn) as SHapp.
    destruct rr_fsn as (F1 & _ & _ & F4 & _ & _).
    destruct (rr_fsnum FS 0) as (E1 & E2 & E3 & E4).
    pose proof FPc as (DTq & TSq & Cq & Tq & DBq & kkq & _ & _ & HPl & _ & _ & HCLq & _).
    destruct HPl as (P1 & P2 & P3 & P4 & P5).
    pose proof (rr_stk_mono mc mf FS (FS + FS_SIZE) P5 WQ RQ) as STF.
    split.
    { eapply munch_trans; [ exact (munch_weaken rWB rWP m mc rWB_WP MUb)
                          | exact (munch_weaken rOUTW rWP mc mf (rOUTW_WP OKr) MUo) ]. }
    split; [exact (wmono_trans rsegs m mc mf WMc WQ)|].
    split; [exact (rr_rd_mono_trans m mc mf RMc RQ)|].
    split; [exact MIf|].
    split.
    { apply (rr_rw rOUTW mc mf _ _ SVc MUo WQ). intros x Hx. unfold rSAVES in Hx.
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in Hx. unfold rOUTW. cbn [outside].
      split; [clear - Hx Wpa; lia|]. split; [clear - Hx Wpp; lia|]. split; [clear - Hx Wpn; lia | exact I]. }
    split.
    { apply (rr_awx_munch G rOUTW mc mf AXc MUo). intros x Hx _.
      apply SHapp. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right.
      clear - Hx HHM' HAE' HSK; lia. }
    split.
    { eapply (rr_fp_free [1%nat] mc mf (bv_unsigned tp) FS (S - 9072) S rWW rDD rOUTW FPc TLc MUo WQ
                (rOUTW_full RAb)).
      - intros x Hx. apply OUThdr. clear - Hx; lia.
      - intros x Hx. right. exact (rr_rd_of_stk mf FS (FS + FS_SIZE) STF x Hx).
      - intros c Hc. cbn [In] in Hc. destruct Hc as [<-|[]]. split.
        + apply rr_rd8_le8; [ rewrite E3; clear - F1; lia | rewrite E3; clear - F1 F4 HS; lia |].
          intros i Hi. apply (rr_rd_of_stk mf FS (FS + FS_SIZE) STF).
          rewrite E3. unfold FS_SIZE. clear - Hi F1; lia.
        + apply Forall_inv in HCLq. destruct HCLq as (_ & hq & flags & _ & HFg & HFln & HFb).
          exists flags. split; [|split; [exact HFln | exact HFb]].
          eapply fl_bytes; [exact HFg | exact MUo |].
          intros x Hx. apply OUThdr. rewrite HFln, E4, E2 in Hx. clear - Hx; lia. }
    split; [exact (rr_tls_ret [1%nat] mc mf (bv_unsigned tp) FS (S - 9072) S rWW rDD rYY rOUTW FPc TLc MUo
                     (rOUTW_full RAb))|].
    intros Hn. destruct (FLc Hn) as (HB1 & HB2).
    destruct (rk_place G fv spc j nn HK) as [(En & _)|(_ & Hj & EG)]; [exfalso; clear - Hn En; lia|].
    destruct (rr_fsnum FS j) as (Ej & Ejf & _ & _). destruct (rr_fsnum FS (fs_M 1)) as (EM & _).
    split.
    - eapply fl_bytes; [exact HB1 | exact MUo |]. intros x Hx. rewrite length_le8 in Hx.
      apply OUTfr. clear - Hx Hj EG E1 EM E4 Ej; lia.
    - eapply fl_bytes; [exact HB2 | exact MUo |]. intros x Hx.
      cbn [length Z.of_nat Pos.of_succ_nat] in Hx. apply OUThdr. clear - Hx Hj Ejf E4; lia.
  Qed.

  (* 0x84cbc .. 0x84d6c: sh reply_addr at pa, sd (fr + 38) at pp, sd (ir_s - 13) at pn, a0 = 1, j 0x84bc4.
     Each shadow check's slow path uses a scratch register (chk_core's r): a2 for fr + 36, a3 for fr + 37 and pa. *)
  Lemma rp_stores : forall Q, rKT Q -> rKS Q.
  Proof.
    intros Q KT G fv spc j nn mc x1 x2 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HK RJB OKr.
    assert (RAb : reply_args fr pa pp pn = true)
      by (unfold reply_ok in OKr; destruct (reply_args fr pa pp pn); [reflexivity | discriminate]).
    assert (EIR : ir len g = true)
      by (unfold reply_ok in OKr; rewrite RAb in OKr; exact OKr).
    destruct (ir_bytes len g EIR) as (HL50 & _).
    destruct RJB as (MUb & CORE & RCrec & HBfr & OUTC & STKc & ACc & SWc).
    pose proof CORE as (_ & _ & MIc & _).
    destruct (HBfr HL50) as (HBg & AFg).
    destruct OUTC as (RWpa & RWpp & RWpn & ADpa & ADpp & ADpn).
    destruct (HO RAb) as (Hpa2 & Hpp8 & Hpn8 & _ & _ & _ & Dpa_pp & Dpa_pn & Dpp_pn & _ & _ & _).
    apply rr_hide_in in Dpa_pp, Dpa_pn, Dpp_pn.
    (* the state at the join, from the facts at mc: built outside the run of stores *)
    pose proof (rr_EI0_out G fv spc j nn mc HK OKr MUb CORE ADpa ADpp ADpn) as FIN.
    pose proof (rr_sh_outOUT mc ADpa ADpp ADpn) as SHapp.
    (* the footprint of this segment: the 50 bytes at fr, pa, pp, pn and the shadow byte of each checked byte *)
    pose proof (RFR RAb HL50) as RGFR. pose proof (SCF RAb HL50) as SCFR.
    pose proof (RPA RAb) as RGPA. pose proof (SCPA RAb) as SCpa.
    pose proof (RPP RAb) as RGPP. pose proof (SCPP RAb) as SCpp.
    pose proof (RPN RAb) as RGPN. pose proof (SCPN RAb) as SCpn.
    clear HF HO AOUT AFfr ABC HBCMP HMEMCMP HGCF HCF254 HCF255 TLS0 PARSE MALLOC CKV AC SW ST AW MI FP0
      HHM HAE Rlen S16 HSK MUb CORE RCrec STKc ACc SWc HBfr.
    clear RBY RWIN SSW SCW SKW RFR SCF SKF RPA SCPA RPP SCPP RPN SCPN SKBC RFSS RFLG RFRM SCFM SKFM RW1 RTLS.
    (* the bounds and the shadow facts *)
    destruct (rt_addressable_bound mc fr 50 AFg) as (Hfr0 & _ & Hfr47).
    destruct (rt_addressable_bound mc pa 2 ADpa) as (Hpa0 & _ & Hpa47).
    destruct (rt_addressable_bound mc pp 8 ADpp) as (Hpp0 & _ & Hpp47).
    destruct (rt_addressable_bound mc pn 8 ADpn) as (Hpn0 & _ & Hpn47).
    assert (RX36 : 0 <= fr + 36 < 2 ^ 64) by (clear - Hfr0 Hfr47; lia).
    assert (RX37 : 0 <= fr + 37 < 2 ^ 64) by (clear - Hfr0 Hfr47; lia).
    assert (RXpa : 0 <= pa < 2 ^ 64) by (clear - Hpa0 Hpa47; lia).
    assert (APpm : app_mem pp)
      by (pose proof (rr_app_in mc pp 8 0 ADpp ltac:(lia)) as Hz; rewrite Z.add_0_r in Hz; exact Hz).
    assert (APnm : app_mem pn)
      by (pose proof (rr_app_in mc pn 8 0 ADpn ltac:(lia)) as Hz; rewrite Z.add_0_r in Hz; exact Hz).
    pose proof (rr_shadow mc fr 50 36 1 (fr + 36) AFg ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(pose proof (Z.mod_pos_bound (fr + 36) 8 ltac:(lia)); lia) eq_refl) as SH36.
    pose proof (rr_shadow mc fr 50 37 1 (fr + 37) AFg ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(pose proof (Z.mod_pos_bound (fr + 37) 8 ltac:(lia)); lia) eq_refl) as SH37.
    pose proof (rr_shadow mc pa 2 0 2 pa ADpa ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(apply rr_mod2_al; exact Hpa2) ltac:(ring)) as SHpa.
    assert (AApp : asan_addressable rsegs mc ASAN_K pp 8) by (apply rt_addressable; exact ADpp).
    assert (A3pp : asan_rt3 rsegs mc ASAN_K pp 8) by (apply rt_rt3; exact ADpp).
    destruct (asan_shadow_read rsegs mc ASAN_K pp 8 [] 0
                (rt_shadow_rd mc pp 8 [] ADpp (fun x _ => I)) ltac:(lia)) as (kp & RKpp & BKpp).
    assert (Skp0 : bv_signed kp = 0)
      by (apply (asan_check_8 rsegs mc ASAN_K pp 8 0 kp AApp A3pp ltac:(lia) ltac:(lia));
          [ rewrite Z.add_0_r; exact Hpp8 | exact BKpp ]).
    assert (Ukp0 : bv_unsigned kp = 0) by (apply rc_signed0_unsigned0; exact Skp0).
    rewrite Z.add_0_r in BKpp. clear RKpp.
    assert (AApn : asan_addressable rsegs mc ASAN_K pn 8) by (apply rt_addressable; exact ADpn).
    assert (A3pn : asan_rt3 rsegs mc ASAN_K pn 8) by (apply rt_rt3; exact ADpn).
    destruct (asan_shadow_read rsegs mc ASAN_K pn 8 [] 0
                (rt_shadow_rd mc pn 8 [] ADpn (fun x _ => I)) ltac:(lia)) as (kn & RKpn & BKpn).
    assert (Skn0 : bv_signed kn = 0)
      by (apply (asan_check_8 rsegs mc ASAN_K pn 8 0 kn AApn A3pn ltac:(lia) ltac:(lia));
          [ rewrite Z.add_0_r; exact Hpn8 | exact BKpn ]).
    assert (Ukn0 : bv_unsigned kn = 0) by (apply rc_signed0_unsigned0; exact Skn0).
    rewrite Z.add_0_r in BKpn. clear RKpn.
    (* the frame's 50 bytes as cells: the loads of g[36] and g[37] read them before any ov_read_bytes fact *)
    pose proof (rc_ro_of_bytes rsegs mc fr g HBg) as RO. rewrite Hg in RO. cbn [map seq] in RO.
    clear HBg AFg ADpa ADpp ADpn AApp A3pp AApn A3pn Skp0 Skn0 Hg.
    apply rr_hide_in in BKpp, BKpn.
    apply rr_hide_out in Dpa_pp, Dpa_pn, Dpp_pn.
    pose proof (munch_refl [(pa, pa + 2); (pp, pp + 8); (pn, pn + 8)] mc) as MUapp.
    pose proof (wmono_refl rsegs mc) as WQ.
    (* 0x84cbc .. 0x84cc0: fr + 18 <= 2^64 - 19 *)
    rubn (-19).
    (* 0x84cc4 .. 0x84cd4 (+ slow path 0x84db0): a0 = fr + 36, its shadow check *)
    step.
    chk_core (fr + 36) RX36 (Z_to_bv 5 12) SH36 pre_sr no_extra.
    (* 0x84cd8 .. 0x84ce4: fr + 18 <= 2^64 - 20; pa even *)
    rubn (-20).
    step. rewrite (rr_land1 pa) by lia.
    step. rbnz0.
    (* 0x84ce8 .. 0x84cfc (+ the interleaved lbu g[36]; slow path 0x84dbc): a0 = fr + 37, its shadow check *)
    step.
    chk_core (fr + 37) RX37 (Z_to_bv 5 13) SH37 pre_sr no_extra.
    (* 0x84d00 .. 0x84d10 (+ the interleaved lbu g[37]; slow path 0x84dc8): the shadow check of the 2 bytes at pa *)
    chk_core pa RXpa (Z_to_bv 5 13) SHpa pre_sr add1.
    clear RO.
    (* 0x84d14 .. 0x84d20: a0 = (g[36] << 8) | g[37]; sh a0,0(s6) *)
    step. step. step. step.
    (* 0x84d24 .. 0x84d2c: fr + 18 <= 2^64 - 21; pp 8-aligned *)
    step. rewrite (rr_ltu_negl (fr + 18) (-21)) by lia. cbv iota.
    step. rewrite (rr_land7 pp) by lia.
    step. rbnz0.
    (* 0x84d30 .. 0x84d3c: the shadow check of the 8 bytes at pp (no slow path: the byte is 0) *)
    step. rewrite ?(unsigned_lit pp) by lia. rewrite rc_shr3.
    step.
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        assert (BKpp1 : bytes_at rsegs mcur (asan_shadow ASAN_K pp) [kp])
          by (eapply rc_bytes_at_munch; [ exact (rr_hide_out _ BKpp) | exact MUapp |
               intros z Hz; cbn [length] in Hz;
               replace z with (asan_shadow ASAN_K pp) by lia;
               exact (SHapp pp APpm) ]);
        assert (HRp : ov_read_bytes rsegs mcur (wa (pp / 8 + ASAN_K)) 1 = Some [kp])
          by (replace (wa (pp / 8 + ASAN_K)) with (wa (asan_shadow ASAN_K pp + 0))
                by (unfold asan_shadow; f_equal; lia);
              rewrite (bytes_at_read rsegs mcur (asan_shadow ASAN_K pp) [kp] 0 1 BKpp1
                         ltac:(lia) ltac:(cbn; lia));
              reflexivity)
    end.
    step. step.
    unfold zxb. rewrite ?w0_lit. rewrite Ukp0.
    replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
    cbn [negb]. cbv iota.
    clear HRp BKpp1.
    (* 0x84d40 .. 0x84d4c: a0 = fr + 38; pn 8-aligned; sd a0,0(s4) *)
    step.
    step. rewrite (rr_land7 pn) by lia.
    step.
    step. rbnz0.
    (* 0x84d50 .. 0x84d5c: the shadow check of the 8 bytes at pn *)
    step. rewrite ?(unsigned_lit pn) by lia. rewrite rc_shr3.
    step.
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        assert (BKpn1 : bytes_at rsegs mcur (asan_shadow ASAN_K pn) [kn])
          by (eapply rc_bytes_at_munch; [ exact (rr_hide_out _ BKpn) | exact MUapp |
               intros z Hz; cbn [length] in Hz;
               replace z with (asan_shadow ASAN_K pn) by lia;
               exact (SHapp pn APnm) ]);
        assert (HRn : ov_read_bytes rsegs mcur (wa (pn / 8 + ASAN_K)) 1 = Some [kn])
          by (replace (wa (pn / 8 + ASAN_K)) with (wa (asan_shadow ASAN_K pn + 0))
                by (unfold asan_shadow; f_equal; lia);
              rewrite (bytes_at_read rsegs mcur (asan_shadow ASAN_K pn) [kn] 0 1 BKpn1
                         ltac:(lia) ltac:(cbn; lia));
              reflexivity)
    end.
    step. step.
    unfold zxb. rewrite ?w0_lit. rewrite Ukn0.
    replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
    cbn [negb]. cbv iota.
    clear HRn BKpn1.
    (* 0x84d60 .. 0x84d6c: s8 = ir_s - 13; sd s8,0(s3); a0 = 1; j 0x84bc4 *)
    step. step. step. step.
    (* the teardown join *)
    assert (ERET : Z_to_bv 64 1 = Z_to_bv 64 (reply_ret fr len pa pp pn g))
      by (unfold reply_ret; rewrite RAb, EIR; reflexivity).
    rewrite ERET.
    eapply KT; [ exact HK | | | reflexivity ].
    - apply FIN; [exact MUapp | exact WQ | | exact MIc].
      apply (rr_rd_mono_list _ mc _ MUapp).
      constructor; [|constructor; [|constructor; [|constructor]]]; cbn [fst snd]; intros y Hy.
      + apply (rr_rw_rd _ pa _ y RWpa). cbn [cells_bytes cbytes]. rewrite app_nil_r, length_le2. clear - Hy; lia.
      + apply (rr_rw_rd _ pp _ y RWpp). cbn [cells_bytes cbytes]. rewrite app_nil_r, length_le8. clear - Hy; lia.
      + apply (rr_rw_rd _ pn _ y RWpn). cbn [cells_bytes cbytes]. rewrite app_nil_r, length_le8. clear - Hy; lia.
    - intros _. split; [|split].
      + eapply rc_rw_flat; [exact RWpa|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
        rewrite (rc_le2_pack (cp_b g 37) (cp_b g 36)). reflexivity.
      + eapply rc_rw_flat; [exact RWpp|]. cbn [cells_bytes cbytes]. apply app_nil_r.
      + eapply rc_rw_flat; [exact RWpn|]. cbn [cells_bytes cbytes]. apply app_nil_r.
  Qed.

  (* ===================== Segment 4: the tag tests, the block sum and the record sum (0x84a68 .. 0x84cbc) ===== *)

  Lemma rr_ir_false : (ir len g = true -> False) -> ir len g = false.
  Proof. intros H. destruct (ir len g); [exfalso; exact (H eq_refl) | reflexivity]. Qed.

  (* The frame bytes' values in the form of ir (cp_v g i, and ir_s g for byte 26). *)
  Ltac rcv := repeat match goal with
    | |- context [bv_unsigned (cp_b g ?i)] => change (bv_unsigned (cp_b g i)) with (cp_v g i)
    | |- context [bv_unsigned (nth ?i g (Z_to_bv 8 0))] => change (bv_unsigned (nth i g (Z_to_bv 8 0))) with (cp_v g i)
    end;
    try change (cp_v g 26) with (ir_s g).

  (* rJB across the call of reac_ctrl_record_cksum_verify: the callee writes only the 16 bytes below sp. *)
  Lemma rr_JB_ck : forall G fv spc j nn mc m', rFK G fv spc j nn -> reply_args fr pa pp pn = true ->
    rJB G j nn mc -> munch [(spc - 16, spc)] mc m' -> wmono rsegs mc m' -> mem_inv rsegs m' ->
    stk rsegs m' (S - 9072) spc -> rJB G j nn m'.
  Proof.
    intros G fv spc j nn mc m' HK RAb (MUb & CORE & RCrec & HBfr & OUTC & STKc & ACc & SWc) MUc WMc' MIp STp.
    destruct CORE as (WMc & RMc & MIc & SVc & AXc & FPc & TLc & FLc).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (rk_cwin G fv spc j nn HK) as (C1 & C2 & C3 & C4).
    assert (OUTw : forall x, (x < S - 9072 \/ S <= x) -> outside [(spc - 16, spc)] x)
      by (intros x Hx; cbn [outside]; split; [clear - Hx C1 C2; lia | exact I]).
    assert (SHw : forall x, app_mem x -> outside [(spc - 16, spc)] (shadow_addr x)).
    { intros x Hx. cbn [outside]. split; [|exact I]. intros Hin.
      apply (rr_app_not_shadow (shadow_addr x)); [| exact (rt_app_shadow x Hx)].
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right. clear - Hin C1 C2 HHM' HAE'; lia. }
    assert (RMc' : rr_rd_mono mc m').
    { apply (rr_rd_mono_list _ mc m' MUc). constructor; [|constructor].
      cbn [fst snd]. intros y Hy. apply (rr_rd_of_stk m' (S - 9072) spc STp). clear - Hy C1; lia. }
    assert (SUBw : sub_fp [(spc - 16, spc)] rWB).
    { intros x Hx. unfold rWB in Hx. cbn [outside] in Hx. destruct Hx as (Hw & _).
      cbn [outside]. split; [clear - Hw C1 C2; lia | exact I]. }
    assert (HFULL : sub_fp [(spc - 16, spc)] (rWW ++ fp_w [1%nat] FS ++ rYY)).
    { intros x Hx. apply rr_out_app_inv in Hx as [H1 _].
      unfold rWW, reac_ctrl_identity_reply_W, REAC_CTRL_IDENTITY_REPLY_K in H1. cbn [outside] in H1.
      destruct H1 as (H1 & _). cbn [outside]. split; [clear - H1 C1 C2; lia | exact I]. }
    unfold rJB.
    split; [exact (munch_trans _ m mc m' MUb (munch_weaken _ _ mc m' SUBw MUc))|].
    split.
    { split; [exact (wmono_trans rsegs m mc m' WMc WMc')|].
      split; [exact (rr_rd_mono_trans m mc m' RMc RMc')|].
      split; [exact MIp|].
      split.
      { apply (rr_rw _ mc m' _ _ SVc MUc WMc'). intros x Hx. unfold rSAVES in Hx.
        cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in Hx. cbn [outside].
        split; [clear - Hx C2; lia | exact I]. }
      split.
      { apply (rr_awx_munch G _ mc m' AXc MUc). intros x Hx _. apply SHw.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right. clear - Hx HHM' HAE' HSK; lia. }
      split.
      { eapply (rr_fp_free [1%nat] mc m' (bv_unsigned tp) FS (S - 9072) S rWW rDD [(spc - 16, spc)] FPc TLc MUc
                  WMc' HFULL).
        - intros x Hx. apply OUTw. left. clear - Hx F4; lia.
        - intros x Hx. left. apply OUTw. left. unfold FS_SIZE in Hx. clear - Hx F4; lia.
        - intros c Hc. cbn [In] in Hc. destruct Hc as [<-|[]].
          pose proof FPc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HCLq & _).
          apply Forall_inv in HCLq. destruct HCLq as (_ & hq & flags & HHq & HFg & HFln & HFb).
          destruct (rr_fsnum FS 0) as (_ & E2 & E3 & E4).
          split.
          + exists hq. eapply fl_bytes; [exact HHq | exact MUc |]. intros x Hx. apply OUTw. left.
            rewrite length_le8, E3 in Hx. clear - Hx F4; lia.
          + exists flags. split; [|split; [exact HFln | exact HFb]].
            eapply fl_bytes; [exact HFg | exact MUc |]. intros x Hx. apply OUTw. left.
            rewrite HFln, E4, E2 in Hx. clear - Hx F4; lia. }
      split; [exact (rr_tls_ret [1%nat] mc m' (bv_unsigned tp) FS (S - 9072) S rWW rDD rYY [(spc - 16, spc)]
                       FPc TLc MUc HFULL)|].
      intros Hn. destruct (FLc Hn) as (HB1 & HB2).
      destruct (rk_place G fv spc j nn HK) as [(En & _)|(_ & Hj & EG)]; [exfalso; clear - Hn En; lia|].
      destruct (rr_fsnum FS j) as (_ & Ejf & _).
      split.
      - eapply fl_bytes; [exact HB1 | exact MUc |]. intros x Hx. rewrite length_le8 in Hx. apply OUTw. left.
        clear - Hx EG Hj F4; lia.
      - eapply fl_bytes; [exact HB2 | exact MUc |]. intros x Hx. cbn [length Z.of_nat Pos.of_succ_nat] in Hx.
        apply OUTw. left. rewrite Ejf in Hx. clear - Hx Hj F4; lia. }
    split.
    { apply (rr_rw _ mc m' _ _ RCrec MUc WMc'). intros x Hx.
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in Hx. cbn [outside]. split; [|exact I].
      destruct C4 as [C4|C4]; clear - Hx C4; lia. }
    split.
    { intros HL. destruct (HBfr HL) as (HBg & AFg). destruct (HF RAb HL) as (_ & _ & Hwf & _ & _ & _).
      split.
      - eapply fl_bytes; [exact HBg | exact MUc |]. intros x Hx. rewrite Hg in Hx. apply OUTw.
        destruct Hwf as [Hwf|Hwf]; [left | right]; clear - Hx Hwf; lia.
      - apply (rr_addr_munch _ mc m' fr 50 AFg MUc). intros i Hi. apply SHw. exact (rr_app_in mc fr 50 i AFg Hi). }
    split.
    { destruct OUTC as (RWpa & RWpp & RWpn & ADpa & ADpp & ADpn).
      destruct (HO RAb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Wa & Wp & Wn).
      unfold rOUTC.
      split; [apply (rr_rw _ mc m' _ _ RWpa MUc WMc'); intros x Hx;
              cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in Hx; apply OUTw; clear - Hx Wa; lia|].
      split; [apply (rr_rw _ mc m' _ _ RWpp MUc WMc'); intros x Hx;
              cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in Hx; apply OUTw; clear - Hx Wp; lia|].
      split; [apply (rr_rw _ mc m' _ _ RWpn MUc WMc'); intros x Hx;
              cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in Hx; apply OUTw; clear - Hx Wn; lia|].
      split; [apply (rr_addr_munch _ mc m' pa 2 ADpa MUc); intros i Hi; apply SHw;
              exact (rr_app_in mc pa 2 i ADpa Hi)|].
      split; [apply (rr_addr_munch _ mc m' pp 8 ADpp MUc); intros i Hi; apply SHw;
              exact (rr_app_in mc pp 8 i ADpp Hi)|].
      apply (rr_addr_munch _ mc m' pn 8 ADpn MUc); intros i Hi; apply SHw; exact (rr_app_in mc pn 8 i ADpn Hi). }
    split; [exact (rr_stk_mono m m' _ _ ST (wmono_trans rsegs m mc m' WMc WMc')
                     (rr_rd_mono_trans m mc m' RMc RMc'))|].
    split.
    - apply (fl_asan_cells _ mc m' ACc MUc). intros x Hx. apply OUTw. left. unfold RT_LO, RT_HI in Hx.
      clear - Hx HHM'; lia.
    - exact (rr_shadow_rw_on_mono _ mc m' SWc WMc' RMc').
  Qed.

  (* 0x84a68 .. 0x84cbc / 0x84bc0: the tag tests (the kind 5, the type word 0x500, the bytes 32, 33, s, 27 and
     26 + s, each read after its shadow check (scratch a2) and each pointer computation after its UBSan test), the
     block sum (rloopB0, 0x84b64 .. 0x84ba0), the record sum (rloopR, 0x84ba8 .. 0x84bbc: the call of
     reac_ctrl_record_cksum_verify) and the test of its result. A failed test goes to 0x84bc0 with ir false. *)
  Lemma rp_tag : forall Q, rKV Q -> rKS Q -> rKF Q.
  Proof.
    intros Q KV KS G fv spc j nn mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HK RJB RAb.
    pose proof (rJB_EI0 G j nn mc RJB) as EI.
    pose proof (ctrlparse_kind_range len g) as KR.
    (* 0x84a68 .. 0x84a6c: the kind is 5 *)
    step. step.
    rewrite (rc_eqb64 (fst (ctrlparse len g)) 5) by lia.
    destruct (Z.eqb_spec (fst (ctrlparse len g)) 5) as [K5|K5]; cbn [negb]; cbv iota.
    2:{ eapply KV; [exact HK | exact EI | exact RAb |].
        apply rr_ir_false. intros Ht. apply ir_true in Ht. destruct Ht as (Ht & _). exact (K5 Ht). }
    destruct (ctrlparse_rec len g (or_introl K5)) as (HD & _ & N28 & N29).
    assert (HL50 : 50 <= len)
      by (unfold cp_hdr in HD; rewrite !andb_true_iff in HD; destruct HD as [[HD _] _]; apply Z.leb_le in HD;
          exact HD).
    pose proof RJB as (MUb & CORE & RCrec & HBfr & OUTC & STKc & ACc & SWc).
    pose proof CORE as (_ & _ & MIc & _).
    destruct (HBfr HL50) as (HBg & AFg).
    destruct (HF RAb HL50) as (Hf50 & _ & Hwf & _ & _ & _).
    (* the footprint of this segment: the 50 bytes at fr with their shadow, and the frame (the record at G + 32) *)
    pose proof (RFR RAb HL50) as RGFR. pose proof (SCF RAb HL50) as SCFR. pose proof (SKF RAb HL50) as SKFR.
    pose proof (rrF_frame G fv spc j nn HK) as RGFRM.
    destruct (rk_cwin G fv spc j nn HK) as (Cw1 & Cw2 & _ & _).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (Hfr0 : 0 < fr).
    { pose proof RAb as RA. unfold reply_args in RA. rewrite !andb_true_iff, !negb_true_iff, !Z.eqb_neq in RA.
      destruct RA as [[[Rf _] _] _]. clear - Rf Rfr; lia. }
    pose proof (ctrlparse_length len g) as LB.
    pose proof (cp_v_range' g 32) as R32. pose proof (cp_v_range' g 33) as R33.
    pose proof (cp_v_range' g 34) as R34. pose proof (cp_v_range' g 35) as R35.
    pose proof (cp_v_range' g 26) as Rs. pose proof (cp_v_range' g 27) as R27.
    assert (Rs' : 0 <= ir_s g < 256) by exact Rs.
    (* the record's type word, as one 2-byte cell *)
    apply (rc_rw_rebytes rsegs _ (G + 32) _
             [CB 28 (firstn 28 (snd (ctrlparse len g))); C2 (Z_to_bv 64 (cp_v g 34 * 256 + cp_v g 35));
              CB 6 (skipn 30 (snd (ctrlparse len g)))]) in RCrec.
    2:{ cbn [cells_wf cell_wf]. rewrite firstn_length_le, length_skipn, LB by lia. repeat split. }
    2:{ cbn [cells_bytes cbytes]. unfold cp_v. rewrite rc_le2_pair. rewrite !app_nil_r. rewrite <- N28, <- N29.
        symmetry. apply rc_b36_split. exact LB. }
    clear N28 N29 LB HD.
    (* the frame's 50 bytes as cells, and the shadow facts of the checked bytes *)
    pose proof (rc_ro_of_bytes rsegs mc fr g HBg) as RO. rewrite Hg in RO. cbn [map seq] in RO.
    assert (RX32 : 0 <= fr + 32 < 2^64) by (clear - Hfr0 Hf50; lia).
    assert (RX33 : 0 <= fr + 33 < 2^64) by (clear - Hfr0 Hf50; lia).
    assert (RX26 : 0 <= fr + 26 < 2^64) by (clear - Hfr0 Hf50; lia).
    assert (RX27 : 0 <= fr + 27 < 2^64) by (clear - Hfr0 Hf50; lia).
    pose proof (rr_shadow mc fr 50 32 1 (fr + 32) AFg ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (fr + 32) 8 eq_refl); lia) eq_refl) as SH32.
    pose proof (rr_shadow mc fr 50 33 1 (fr + 33) AFg ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (fr + 33) 8 eq_refl); lia) eq_refl) as SH33.
    pose proof (rr_shadow mc fr 50 26 1 (fr + 26) AFg ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (fr + 26) 8 eq_refl); lia) eq_refl) as SH26.
    pose proof (rr_shadow mc fr 50 27 1 (fr + 27) AFg ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (fr + 27) 8 eq_refl); lia) eq_refl) as SH27.
    (* 0x84a70 .. 0x84a78: the type word (lhu 28(s8), no shadow check) is 0x500 *)
    step.
    unfold zx16. rewrite (unsigned_lit (cp_v g 34 * 256 + cp_v g 35)) by lia.
    rewrite (Z.mod_small (cp_v g 34 * 256 + cp_v g 35)) by lia.
    step. step.
    rewrite (rc_eqb64 (cp_v g 34 * 256 + cp_v g 35) 1280) by lia.
    destruct (Z.eqb_spec (cp_v g 34 * 256 + cp_v g 35) 1280) as [T|T]; cbn [negb]; cbv iota.
    2:{ eapply KV; [exact HK | exact EI | exact RAb |].
        apply rr_ir_false. intros Ht. apply ir_true in Ht. destruct Ht as (_ & Ht & _). exact (T Ht). }
    (* 0x84a7c .. 0x84a80: fr >= 2^64 - 18 traps; 0x84a84: s7 = fr + 18; 0x84a88 .. 0x84a8c: s7 > 2^64 - 15 traps *)
    step. step. rewrite (rr_ltu_negr fr (-18)) by lia. cbn [negb]. cbv iota.
    step.
    rubn (-15).
    (* 0x84a90 .. 0x84aac: the byte at fr + 32 is 0x12 *)
    step.
    chk_core (fr + 32) RX32 (Z_to_bv 5 12) SH32 pre_sr no_extra.
    step. step. step.
    rewrite (rc_eqb_zxb (cp_b g 32) 18) by lia. rcv.
    destruct (Z.eqb_spec (cp_v g 32) 18) as [E32|E32]; cbn [negb]; cbv iota.
    2:{ eapply KV; [exact HK | exact EI | exact RAb |].
        apply rr_ir_false. intros Ht. apply ir_true in Ht. destruct Ht as (_ & _ & Ht & _). exact (E32 Ht). }
    (* 0x84ab0 .. 0x84ad4: the byte at fr + 33 is 0x12 *)
    rubn (-16).
    step.
    chk_core (fr + 33) RX33 (Z_to_bv 5 12) SH33 pre_sr no_extra.
    step. step. step.
    rewrite (rc_eqb_zxb (cp_b g 33) 18) by lia. rcv.
    destruct (Z.eqb_spec (cp_v g 33) 18) as [E33|E33]; cbn [negb]; cbv iota.
    2:{ eapply KV; [exact HK | exact EI | exact RAb |].
        apply rr_ir_false. intros Ht. apply ir_true in Ht. destruct Ht as (_ & _ & _ & Ht & _). exact (E33 Ht). }
    (* 0x84ad8 .. 0x84b00: s = the byte at fr + 26; s - 24 <u -10 fails unless 14 <= s <= 23 *)
    rubn (-9).
    step.
    chk_core (fr + 26) RX26 (Z_to_bv 5 12) SH26 pre_sr no_extra.
    step. step. rewrite ?rc_uzxb. rcv.
    step. step.
    rewrite (rc_srange (ir_s g)) by exact Rs'.
    destruct ((14 <=? ir_s g) && (ir_s g <=? 23)) eqn:SR; cbn [negb]; cbv iota.
    2:{ eapply KV; [exact HK | exact EI | exact RAb |].
        apply rr_ir_false. intros Ht. apply ir_true in Ht. destruct Ht as (_ & _ & _ & _ & Ht & _).
        rewrite andb_false_iff, !Z.leb_gt in SR. clear - Ht SR; lia. }
    rewrite andb_true_iff, !Z.leb_le in SR.
    (* 0x84b04: s7 > 2^64 - 10 traps; 0x84b08 .. 0x84b24: the byte at fr + 27 is 0xf0 *)
    step. rewrite (rr_ltu_negl (fr + 18) (-10)) by lia. cbv iota.
    step.
    chk_core (fr + 27) RX27 (Z_to_bv 5 12) SH27 pre_sr no_extra.
    step. step. step.
    rewrite (rc_eqb_zxb (cp_b g 27) 240) by lia. rcv.
    destruct (Z.eqb_spec (cp_v g 27) 240) as [E27|E27]; cbn [negb]; cbv iota.
    2:{ eapply KV; [exact HK | exact EI | exact RAb |].
        apply rr_ir_false. intros Ht. apply ir_true in Ht. destruct Ht as (_ & _ & _ & _ & _ & Ht & _).
        exact (E27 Ht). }
    (* 0x84b28 .. 0x84b30: a0 = s + 8; ~(fr + 18) <u s + 8 traps *)
    step. step. rewrite ?rc_uzxb. rcv.
    try rewrite (unsigned_lit (fr + 18)) by lia. rewrite (zb_lxor_ones (fr + 18)) by lia.
    step. rewrite (rc_ltu64 (18446744073709551615 - (fr + 18)) (ir_s g + 8)) by lia.
    replace (18446744073709551615 - (fr + 18) <? ir_s g + 8) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota.
    (* 0x84b34 .. 0x84b50: the byte at fr + 18 + s + 8 = fr + 26 + s is 0xf7 *)
    step.
    try replace (fr + 18 + (ir_s g + 8)) with (fr + 18 + ir_s g + 8) by ring.
    assert (RX5 : 0 <= fr + 18 + ir_s g + 8 < 2^64) by (clear - Hfr0 Hf50 SR; lia).
    pose proof (rr_shadow mc fr 50 (26 + ir_s g) 1 (fr + 18 + ir_s g + 8) AFg ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (fr + 18 + ir_s g + 8) 8 eq_refl); lia) ltac:(lia)) as SH5.
    chk_core (fr + 18 + ir_s g + 8) RX5 (Z_to_bv 5 12) SH5 pre_sr no_extra.
    pose proof (rd_byte rsegs mc fr g (Z.to_nat (26 + ir_s g)) HBg ltac:(rewrite Hg; lia)) as RD8.
    step. step. step.
    match goal with |- context [zxb (nth ?i g (Z_to_bv 8 0))] =>
      rewrite (rc_eqb_zxb (nth i g (Z_to_bv 8 0)) 247) by lia end.
    rcv.
    destruct (Z.eqb_spec (cp_v g (Z.to_nat (26 + ir_s g))) 247) as [E8|E8]; cbn [negb]; cbv iota.
    2:{ eapply KV; [exact HK | exact EI | exact RAb |].
        apply rr_ir_false. intros Ht. apply ir_true in Ht. destruct Ht as (_ & _ & _ & _ & _ & _ & Ht & _).
        exact (E8 Ht). }
    clear RD8 RO.
    (* 0x84b54 .. 0x84b60: a1 = 0, a2 = 32, a3 = a0 = fr + 18; then the block sum loop *)
    step. step. step. step.
    match goal with |- context [zxb ?b] => change (zxb b) with (Z_to_bv 64 (ir_s g)) end.
    pose proof (rc_bytes_skip rsegs mc fr g 18 HBg ltac:(rewrite Hg; lia)) as HBk.
    change (skipn 18 g) with (ir_blk g) in HBk. change (Z.of_nat 18) with 18 in HBk.
    eapply rloopB0.
    - exact Hfr0.
    - exact Hf50.
    - unfold ir_blk. rewrite length_skipn, Hg. reflexivity.
    - exact HBk.
    - apply (rt_shadow_rd mc (fr + 18) 32 []).
      + exact (rr_addr_sub mc fr 50 (fr + 18) 32 AFg ltac:(lia) ltac:(lia) ltac:(lia)).
      + intros x _. exact I.
    - apply rt_addressable. exact (rr_addr_sub mc fr 50 (fr + 18) 32 AFg ltac:(lia) ltac:(lia) ltac:(lia)).
    - (* the 32 block bytes *) eapply rng_sub; [exact RGFR | lia | lia].
    - (* their shadow bytes *) intros x Hx. exact (SCFR x ltac:(lia)).
    - (* 0x84ba0 .. 0x84ba4: the block sum is 0 mod 256 *)
      intros a0' a2' a3' a4' a5'.
      remember (psum (ir_blk g) 32) as ps eqn:Eps.
      assert (PB : 0 <= ps <= 255 * 32)
        by (subst ps; pose proof (psum_range (ir_blk g) 32) as PB; change (Z.of_nat 32) with 32 in PB; exact PB).
      step. step.
      rewrite (rc_zb0 ps) by lia.
      replace (ps mod 256) with (blocksum (ir_blk g)) by (unfold blocksum; rewrite Eps; reflexivity).
      destruct (Z.eqb_spec (blocksum (ir_blk g)) 0) as [B5|B5]; cbn [negb]; cbv iota.
      2:{ eapply KV; [exact HK | exact EI | exact RAb |].
          apply rr_ir_false. intros Ht. apply ir_true in Ht.
          destruct Ht as (_ & _ & _ & _ & _ & _ & _ & Ht & _). exact (B5 Ht). }
      clear Eps PB.
      (* 0x84ba8 .. 0x84bbc: the record sum, by the call of reac_ctrl_record_cksum_verify *)
      pose proof (rc_bytes_skip rsegs mc fr g 34 HBg ltac:(rewrite Hg; lia)) as HBr.
      apply (rc_bytes_first rsegs mc _ _ (Z.to_nat (ir_s g - 8))) in HBr. change (Z.of_nat 34) with 34 in HBr.
      change (firstn (Z.to_nat (ir_s g - 8)) (skipn 34 g)) with (ir_rec g) in HBr.
      eapply rloopR with (lo := S - 9072).
      + exact Hfr0.
      + exact Hf50.
      + exact SR.
      + exact (rc_len_rec g Hg SR).
      + exact HBr.
      + exact (rr_addr_sub mc fr 50 (fr + 34) (ir_s g - 8) AFg ltac:(lia) ltac:(lia) ltac:(lia)).
      + clear - Cw1 Cw2 HS HSK; lia.
      + exact (proj1 (stk_split rsegs mc (S - 9072) spc S STKc ltac:(lia))).
      + clear - Cw1; lia.
      + destruct Hwf as [Hwf|Hwf]; [left | right]; clear - Hwf Cw1 Cw2 SR; lia.
      + exact ACc.
      + intros x Hx. cbn [outside]. split; [|exact I]. intros Hin.
        destruct Hx as [Hx|[Hx|Hx]].
        * unfold GOT_CELL_K in Hx. clear - Hx Hin Cw1 HHM'; lia.
        * unfold CELL_K in Hx. clear - Hx Hin Cw1 HHM'; lia.
        * apply (rr_app_not_shadow x); [| exact Hx].
          unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right. clear - Hin Cw1 Cw2 HHM' HAE'; lia.
      + (* the image *) exact RIMG.
      + (* the callee's frame [spc - 16, spc) *) eapply rng_sub; [exact RWIN | clear - Cw1 Cw2; lia | clear - Cw1 Cw2; lia].
      + (* the record bytes *) eapply rng_sub; [exact RGFR | clear - SR; lia | clear - SR; lia].
      + (* the byte-exact shadow span of each sub-range of them *)
        intros a b Ha Hab Hb. exact (shkov_exact RNG fr 50 a b SKFR ltac:(lia) Hab ltac:(lia)).
      + (* 0x84bbc: beqz a0 (a0 = 0: the record sum is 0 mod 128; else -1) *)
        intros c0 c1 c2 c3 c4 c5 c6 c7 m' MUc WMc' MIf STp.
        pose proof (rr_JB_ck G fv spc j nn mc m' HK RAb RJB MUc WMc' (MIf MIc) STp) as RJB'.
        destruct (Z.eqb_spec (recsum (ir_rec g)) 0) as [B6|B6]; cbv iota.
        2:{ step. rewrite rr_eqb_m1. cbv iota.
            eapply KV; [exact HK | exact (rJB_EI0 G j nn m' RJB') | exact RAb |].
            apply rr_ir_false. intros Ht. apply ir_true in Ht.
            destruct Ht as (_ & _ & _ & _ & _ & _ & _ & _ & Ht). exact (B6 Ht). }
        step. rewrite (rc_beq0_true 0 eq_refl). cbv iota.
        assert (EIR : ir len g = true).
        { unfold ir. rewrite K5, T, E32, E33, E27, E8, B5, B6.
          rewrite (proj2 (Z.leb_le 14 (ir_s g)) ltac:(lia)), (proj2 (Z.leb_le (ir_s g) 23) ltac:(lia)).
          reflexivity. }
        assert (OKr : reply_ok fr len pa pp pn g = true) by (unfold reply_ok; rewrite RAb, EIR; reflexivity).
        eapply KS; [exact HK | exact RJB' | exact OKr].
  Qed.

  (* The run from the entry to the return: every segment chained, Q := rQ. *)
  Lemma rp_main : forall t0 t1 t2 a5 a6 a7 t3 t4 t5 t6,
    evtF rsegs RNG rQ (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fr) (Z_to_bv 64 len) (Z_to_bv 64 pa)
                       (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY) fc None m (seg_rom rsegs)).
  Proof using All.
    intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6.
    apply (rp_entry t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 rQ m eq_refl).
    apply rp_null; [exact rp_epi|].
    apply rp_parse. apply rp_tag.
    - apply rp_fail. apply rp_f8. exact rp_epi.
    - apply rp_stores. apply rp_f8. exact rp_epi.
  Qed.


  (* ======================================================================================================
     RB INSERTIONS (placed by doc/gen_reac_ctrl_identity_replyRB.py before `End Rep.` of the accepted
     reac_ctrl_identity_replyF.v).  Each is a cut lemma for the cgif glue; the scripts are the accepted file's,
     copied VERBATIM except for the named difference.  Unit decisions.md (a working note, not in this delivery) (a Theorem Labs lane 05:51Z) / a Theorem Labs lane's re-base
     ruling (00:49Z): re-based stretches come from copies in a separate file; the accepted _F file stays
     byte-identical.
     ====================================================================================================== *)

  (* COPY of rp_stretchB0_F (accepted :1664-1680), for ANY return-address register.  Difference: the first mkR
     argument is the binder rr0 instead of 0x8497c.  Reason: the core's post of the fake-stack call keeps only the
     callee-saved registers (YG0d.aregs_preserved; ra is not one of them); the four steps before rp_fwords do not read
     ra and rp_fwords is generic in it. *)
  Lemma rp_stretchB0g_F : forall Q, rKB Q -> forall (jj : Z) (m2 : word -> option byte)
      (rr0 u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word),
    0 <= jj < fs_M 1 -> rBI (fs_frame FS 1 jj) jj 1 m2 ->
    evtF rsegs RNG Q (MS (mkR rr0 (Z_to_bv 64 rA) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 rA)
                       (Z_to_bv 64 (fs_frame FS 1 jj)) x1 x2 x3 x4 x5 x6 x7 s2 (Z_to_bv 64 pn) (Z_to_bv 64 pp)
                       (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len) s8 s9 s10 (wa ASAN_K) u3 u4 u5 u6)
                  F (Z_to_bv 64 0x8497c) fc None m2 (seg_rom rsegs)).
  Proof.
    intros Q K jj m2 rr0 u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 Hjj HB.
    pose proof rA_facts as (HA32 & HAlo & HAhi).
    destruct rr_fs as (F1 & F2 & F3 & F4 & F5 & _). unfold FS_SIZE in F4.
    pose proof (rrF_fs_frame1 FS jj) as EF.
    assert (EM1 : fs_M 1 = 8192) by reflexivity.
    step. step. step. step.
    rewrite (rc_neq0_64 (fs_frame FS 1 jj)) by (clear - EF EM1 Hjj F1 F4 HS; lia). cbn [negb]. cbv iota.
    eapply (rp_fwords (fs_frame FS 1 jj) (fs_frame FS 1 jj) rA jj 1); [right; repeat split; lia | exact HB | exact K].
  Qed.

  (* NEW continuation at 0x84a58 (after the unpoison run).  rp_call (accepted :2816) has exactly this shape for
     Q := its rKF continuation.  Reason: the glue's stretch BEFORE reac_ctrl_parse ends at the callee's first slot
     (reac_ctrl_parse takes its own class-1 fake frame, an allocator event the bridge cannot lift across). *)
  Definition rKC (Q : machine_state -> Prop) : Prop :=
    forall (G fv spc j nn : Z) (mc m5 : word -> option byte)
           (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      rFK G fv spc j nn -> rBI G j nn mc -> reply_args fr pa pp pn = true ->
      munch [(G / 8 + ASAN_K + 4, G / 8 + ASAN_K + 9)] mc m5 -> wmono rsegs mc m5 -> rr_rd_mono mc m5 ->
      mem_inv rsegs m5 ->
      bytes_at rsegs m5 (G / 8 + ASAN_K + 4) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] ->
      evtF rsegs RNG Q (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 rA) (Z_to_bv 64 4)
                         x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 pn) (Z_to_bv 64 pp)
                         (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len) (Z_to_bv 64 (G + 32))
                         (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) (wa ASAN_K) x28 x29 x30 x31)
                    F (Z_to_bv 64 0x84a58) fc None m5 (seg_rom rsegs)).

  (* COPY of rp_parse (accepted :3005-3023) with the continuation rKC.  Difference: the last step applies KC instead
     of rp_call.  Reason: as for rKC. *)
  Lemma rp_parse_C : forall Q, rKC Q -> rKN Q.
  Proof.
    intros Q KC G fv spc j nn mc rr x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HK HB RAb.
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & _ & _ & _ & _ & _ & _ & SH1 & SH2).
    pose proof rr_fsn as (F1 & _).
    pose proof HB as (_ & WM & RM & MI1 & _).
    assert (SWc : forall i, 0 <= i < 16 -> wview rsegs mc (wa (G / 8 + ASAN_K + i)) <> None).
    { intros i Hi. pose proof (rr_shadow_rw_on_mono _ m mc SW WM RM) as SRmc.
      destruct (rk_facts G fv spc j nn HK) as (_ & _ & _ & _ & _ & _ & FRA & _).
      apply (rr_stk_wv mc _ _ _ (rr_shadow16_stk_on _ mc G SRmc (rk_inR _ _ _ _ _ HK) ltac:(clear - FRlo F1; lia)
                                   FRA SH1 SH2)).
      clear - Hi; lia. }
    apply (rr_unp_run G mc rr (Z_to_bv 64 spc) x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 rA) (Z_to_bv 64 (-1)) x11 x12 x13
             x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa)
             (Z_to_bv 64 len) s8 (wa ASAN_K) x28 x29 x30 x31 Q FR8 ltac:(clear - FRlo F1; lia) SH1 SH2 SWc MI1
             (rrF_frame_blk G fv spc j nn HK)).
    intros m5 MU5 WM5 RM5 MI5 BS5.
    exact (KC G fv spc j nn mc m5 rr x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HK HB RAb
             MU5 WM5 RM5 MI5 BS5).
  Qed.

  (* ---- The S-B chain with its continuations FIXED at one frame (G fv spc j nn): the cgif glue must know, at the end of
     the stretch, that the frame is the one the fake-stack call returned (G = fs_frame FS 1 jj); the accepted
     continuations rKB / rKN / rKE quantify over every frame and lose that link.  Each definition is the original with
     its frame binders made parameters and its rFK premise dropped (rFK becomes a premise of the lemma instead); each
     lemma is the original script with only the continuation's arguments changed (named below).  Reason: as above;
     unit decision 125 (copies in a separate file, the accepted _F file byte-identical). ---- *)

  (* COPY of rKB (accepted :1559-1567): the frame binders G fv spc j nn are parameters; the rFK premise is dropped. *)
  Definition rKBG (G fv spc j nn : Z) (Q : machine_state -> Prop) : Prop :=
    forall (mc : word -> option byte)
           (rr x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      rBI G j nn mc ->
      evtF rsegs RNG Q (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 rA)
                         (Z_to_bv 64 (-1)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 pn)
                         (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len) s8
                         (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) (wa ASAN_K) x28 x29 x30 x31)
                    F (Z_to_bv 64 0x84a2c) fc None mc (seg_rom rsegs)).

  (* COPY of rKN (accepted :2154-2162): the frame binders G fv spc j nn are parameters; the rFK premise is dropped. *)
  Definition rKNG (G fv spc j nn : Z) (Q : machine_state -> Prop) : Prop :=
    forall (mc : word -> option byte)
           (rr x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      rBI G j nn mc -> reply_args fr pa pp pn = true ->
      evtF rsegs RNG Q (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 rA)
                         (Z_to_bv 64 (-1)) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 pn)
                         (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len) s8
                         (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) (wa ASAN_K) x28 x29 x30 x31)
                    F (Z_to_bv 64 0x84a3c) fc None mc (seg_rom rsegs)).

  (* COPY of rKE (accepted :2144-2151): the frame binders G fv spc j nn are parameters; the rFK premise is dropped;
     the continuation ALSO gets rBI G j nn mc (the null branch 0x84a2c .. 0x84bdc makes no store, so the state's
     fine munch from the frame-word run still holds; rEI0 alone weakens it to rWB). *)
  Definition rKEG (G fv spc j nn : Z) (Q : machine_state -> Prop) : Prop :=
    forall mc r (x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30
                              x31 : word),
      rBI G j nn mc -> rEI0 G j nn mc -> (reply_ok fr len pa pp pn g = true -> rOUTF mc) ->
      r = reply_ret fr len pa pp pn g ->
      evtF rsegs RNG Q (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 fv) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) x27
                        x28 x29 x30 x31) F (Z_to_bv 64 0x84bdc) fc None mc (seg_rom rsegs)).

  (* COPY of rKC (this file): the frame binders G fv spc j nn are parameters; the rFK premise is dropped. *)
  Definition rKCG (G fv spc j nn : Z) (Q : machine_state -> Prop) : Prop :=
    forall (mc m5 : word -> option byte)
           (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      rBI G j nn mc -> reply_args fr pa pp pn = true ->
      munch [(G / 8 + ASAN_K + 4, G / 8 + ASAN_K + 9)] mc m5 -> wmono rsegs mc m5 -> rr_rd_mono mc m5 ->
      mem_inv rsegs m5 ->
      bytes_at rsegs m5 (G / 8 + ASAN_K + 4) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] ->
      evtF rsegs RNG Q (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 rA) (Z_to_bv 64 4)
                         x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 pn) (Z_to_bv 64 pp)
                         (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len) (Z_to_bv 64 (G + 32))
                         (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) (wa ASAN_K) x28 x29 x30 x31)
                    F (Z_to_bv 64 0x84a58) fc None m5 (seg_rom rsegs)).

  (* COPY of rp_fwords (accepted :1591-1652).  Difference: continuation rKBG G fv spc j nn Q instead of rKB Q; `eapply K; [exact HK|]` becomes `eapply K`. *)
  Lemma rp_fwordsG : forall G fv spc j nn mc
    (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word) Q,
    rFK G fv spc j nn -> rBI G j nn mc -> rKBG G fv spc j nn Q ->
    evtF rsegs RNG Q (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 rA)
                       x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 pn) (Z_to_bv 64 pp)
                       (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len) s8 x25 (Z_to_bv 64 G) (wa ASAN_K)
                       x28 x29 x30 x31)
                    F (Z_to_bv 64 0x849ac) fc None mc (seg_rom rsegs)).
  Proof.
    intros G fv spc j nn mc rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 Q HK HB K.
    pose proof rA_facts as (HA32 & HAlo & HAhi).
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SWh & SH1 & SH2).
    pose proof (rrF_frame G fv spc j nn HK) as RGFRM. pose proof (rrF_frame_blk G fv spc j nn HK) as SBFRM.
    pose proof rr_fs as (FS0 & _).
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI1 & SV & H120).
    assert (HHMl : 17594333495296 <= S - 9072) by (pose proof HHM as HH0; unfold HIGHMEM_BEG in HH0; exact HH0).
    unfold rWf, shadow_addr in MU.
    (* the block's own writes: the stack slot, the 3 frame words and the 16 shadow bytes *)
    pose proof (munch_refl [(rA + 16, rA + 24); (G, G + 24); (G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] mc) as MUw.
    rwst (rA + 16) 8%nat ltac:(apply rr_STW0; lia). step. store_done.
    step. step. step. step. step. step. step. step.
    rwstb G 8%nat G FW. step. store_done.
    rwstb (G + 8) 8%nat G FW. step. store_done.
    rwstb (G + 16) 8%nat G FW. step. store_done.
    step. step.
    rewrite (unsigned_lit G) by lia. rewrite rc_shr3.
    rwstb (G / 8 + ASAN_K + 0) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 1) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 2) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 3) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    step.
    rwstb (G / 8 + ASAN_K + 4) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 5) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 6) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 7) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 12) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 13) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 14) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 15) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 8) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 9) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 10) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    rwstb (G / 8 + ASAN_K + 11) 1%nat (G / 8 + ASAN_K) SWh. step. store_done.
    step.
    eapply K.
    unfold rBI, rWf, shadow_addr. refine (conj MU (conj WM (conj RM (conj MI1 (conj SV _))))).
    intros Hn1. destruct (H120 Hn1) as (H1 & H2).
    destruct HK as [(_ & _ & _ & _ & E)|(Hj & EG & _ & _ & _)]; [lia|].
    pose proof rr_fs as (_ & _ & _ & HFSb & HFSapp & _).
    pose proof (rr_app_range FS FS_SIZE ltac:(unfold FS_SIZE; lia) ltac:(intros i Hi; apply HFSapp; lia)) as FSR.
    assert (EFl : fs_flag FS 1 j = FS + 20480 + j) by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; lia).
    assert (EGj : G = FS + 1085440 + j * 128)
      by (rewrite EG; unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; change (2 ^ 20) with 1048576; lia).
    assert (Hjb : 0 <= j < 8192)
      by (unfold fs_M in Hj; cbn [Z.of_nat Pos.of_succ_nat] in Hj; change (2 ^ (14 - 1)) with 8192 in Hj; exact Hj).
    unfold FS_SIZE, HIGHMEM_BEG, LOWMEM_END, ASAN_K in *.
    split.
    - eapply (bytes_at_transport rsegs _ mc _ (G + 120) _ H1 MUw). cbn [disjoint_from]. rewrite length_le8.
      split; [lia|]. split; [lia|]. split; [|exact I]. destruct FSR; [left|right]; Z.div_mod_to_equations; lia.
    - eapply (bytes_at_transport rsegs _ mc _ _ _ H2 MUw). cbn [disjoint_from length]. rewrite EFl.
      split; [lia|]. split; [lia|]. split; [|exact I]. destruct FSR; [left|right]; Z.div_mod_to_equations; lia.
  Qed.

  (* COPY of rp_null (accepted :2166-2201).  Difference: continuations rKEG / rKNG / rKBG at the frame; the frame binders and HK come first in intros; KN and KE are applied without G fv spc j nn and HK, and KE also gets HB. *)
  Lemma rp_nullG : forall Q G fv spc j nn, rFK G fv spc j nn ->
    rKEG G fv spc j nn Q -> rKNG G fv spc j nn Q -> rKBG G fv spc j nn Q.
  Proof.
    intros Q G fv spc j nn HK KE KN mc rr x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HB.
    pose proof (rEI0_of_BI G fv spc j nn mc HK HB) as EI.
    destruct (reply_args fr pa pp pn) eqn:RAb.
    - pose proof RAb as RA. unfold reply_args in RA. rewrite !andb_true_iff, !negb_true_iff, !Z.eqb_neq in RA.
      destruct RA as [[[Rf Ra] Rp] Rn].
      step. rewrite (rc_beq0_false fr Rf) by lia. cbv iota.
      step. rewrite (rc_beq0_false pa Ra) by lia. cbv iota.
      step. rewrite (rc_beq0_false pp Rp) by lia. cbv iota.
      step. rewrite (rc_beq0_false pn Rn) by lia. cbv iota.
      exact (KN mc rr x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HB RAb).
    - assert (OK : reply_ok fr len pa pp pn g = false) by (unfold reply_ok; rewrite RAb; reflexivity).
      assert (RV : -1 = reply_ret fr len pa pp pn g) by (unfold reply_ret; rewrite RAb; reflexivity).
      assert (KX : forall (x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30
                           x31 : word),
        evtF rsegs RNG Q (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (-1)) x11 x12 x13 x14 x15 x16 x17
                           (Z_to_bv 64 fv) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) x27
                           x28 x29 x30 x31) F (Z_to_bv 64 0x84bdc) fc None mc (seg_rom rsegs)))
        by (intros; apply (KE mc (-1)); [exact HB | exact EI | rewrite OK; discriminate | exact RV]).
      step.
      destruct (Z.eq_dec fr 0) as [Z0|Z0].
      { rewrite (rc_beq0_true fr Z0). cbv iota. apply KX. }
      rewrite (rc_beq0_false fr Z0) by lia. cbv iota. step.
      destruct (Z.eq_dec pa 0) as [Z1|Z1].
      { rewrite (rc_beq0_true pa Z1). cbv iota. apply KX. }
      rewrite (rc_beq0_false pa Z1) by lia. cbv iota. step.
      destruct (Z.eq_dec pp 0) as [Z2|Z2].
      { rewrite (rc_beq0_true pp Z2). cbv iota. apply KX. }
      rewrite (rc_beq0_false pp Z2) by lia. cbv iota. step.
      destruct (Z.eq_dec pn 0) as [Z3|Z3].
      { rewrite (rc_beq0_true pn Z3). cbv iota. apply KX. }
      exfalso. unfold reply_args in RAb.
      rewrite (proj2 (Z.eqb_neq fr 0) Z0), (proj2 (Z.eqb_neq pa 0) Z1), (proj2 (Z.eqb_neq pp 0) Z2),
        (proj2 (Z.eqb_neq pn 0) Z3) in RAb. discriminate.
  Qed.

  (* COPY of rp_parse_C (this file).  Difference: continuations rKCG / rKNG at the frame; KC is applied without G fv spc j nn and HK. *)
  Lemma rp_parse_CG : forall Q G fv spc j nn, rFK G fv spc j nn ->
    rKCG G fv spc j nn Q -> rKNG G fv spc j nn Q.
  Proof.
    intros Q G fv spc j nn HK KC mc rr x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HB RAb.
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & _ & _ & _ & _ & _ & _ & SH1 & SH2).
    pose proof rr_fsn as (F1 & _).
    pose proof HB as (_ & WM & RM & MI1 & _).
    assert (SWc : forall i, 0 <= i < 16 -> wview rsegs mc (wa (G / 8 + ASAN_K + i)) <> None).
    { intros i Hi. pose proof (rr_shadow_rw_on_mono _ m mc SW WM RM) as SRmc.
      destruct (rk_facts G fv spc j nn HK) as (_ & _ & _ & _ & _ & _ & FRA & _).
      apply (rr_stk_wv mc _ _ _ (rr_shadow16_stk_on _ mc G SRmc (rk_inR _ _ _ _ _ HK) ltac:(clear - FRlo F1; lia)
                                   FRA SH1 SH2)).
      clear - Hi; lia. }
    apply (rr_unp_run G mc rr (Z_to_bv 64 spc) x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 rA) (Z_to_bv 64 (-1)) x11 x12 x13
             x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa)
             (Z_to_bv 64 len) s8 (wa ASAN_K) x28 x29 x30 x31 Q FR8 ltac:(clear - FRlo F1; lia) SH1 SH2 SWc MI1
             (rrF_frame_blk G fv spc j nn HK)).
    intros m5 MU5 WM5 RM5 MI5 BS5.
    exact (KC mc m5 rr x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HB RAb
             MU5 WM5 RM5 MI5 BS5).
  Qed.

  (* COPY of rp_stretchB0g_F (this file).  Difference: continuation rKBG at the frame fs_frame FS 1 jj; calls rp_fwordsG. *)
  Lemma rp_stretchB0G : forall Q (jj : Z),
    rKBG (fs_frame FS 1 jj) (fs_frame FS 1 jj) rA jj 1 Q -> forall (m2 : word -> option byte)
      (rr0 u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word),
    0 <= jj < fs_M 1 -> rBI (fs_frame FS 1 jj) jj 1 m2 ->
    evtF rsegs RNG Q (MS (mkR rr0 (Z_to_bv 64 rA) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 rA)
                       (Z_to_bv 64 (fs_frame FS 1 jj)) x1 x2 x3 x4 x5 x6 x7 s2 (Z_to_bv 64 pn) (Z_to_bv 64 pp)
                       (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len) s8 s9 s10 (wa ASAN_K) u3 u4 u5 u6)
                  F (Z_to_bv 64 0x8497c) fc None m2 (seg_rom rsegs)).
  Proof.
    intros Q jj K m2 rr0 u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 Hjj HB.
    pose proof rA_facts as (HA32 & HAlo & HAhi).
    destruct rr_fs as (F1 & F2 & F3 & F4 & F5 & _). unfold FS_SIZE in F4.
    pose proof (rrF_fs_frame1 FS jj) as EF.
    assert (EM1 : fs_M 1 = 8192) by reflexivity.
    step. step. step. step.
    rewrite (rc_neq0_64 (fs_frame FS 1 jj)) by (clear - EF EM1 Hjj F1 F4 HS; lia). cbn [negb]. cbv iota.
    eapply (rp_fwordsG (fs_frame FS 1 jj) (fs_frame FS 1 jj) rA jj 1); [right; repeat split; lia | exact HB | exact K].
  Qed.


  (* ======================================================================================================
     STRETCH C WITH ITS OWN WRITE LIST.  GENERATED by gen_reac_ctrl_identity_replyRB_SC.py (sha256 fdc4582990bf; internal record) from
     reac_ctrl_identity_replyF_on.v (not in this delivery), the route-(C) run generated from the accepted reac_ctrl_identity_replyF.v (not in this delivery) (do
     not edit; every copy below is one declaration of F_on with the substitutions of that script's table).
     Stretch C runs from reac_ctrl_parse's return 0x84a68 to the ret, the inline class-1 release (the store at
     0x84c34) inside it.  Its base is Section Rep's m: the glue instantiates m := the memory after reac_ctrl_parse,
     so wmono / rr_rd_mono / munch from the base collapse there by refl.  The accepted continuations carry the
     coarse lists rWB (:1954) / rWP (:1955); both contain all of fp_w [1%nat] FS (the class-1 hint word, every flag
     byte, every frame and its shadow), bytes the allocator owns, which the journal step cannot take.  The run
     writes only rWSC G j.
     SHAPE (a Theorem Labs lane's cmInvW, lib/B/Prog/C_reac_box_catalogue_matchLibW.v at bf33012d564): each copied invariant
     is the accepted one AND munch (rWSC G j) m mc.  So every accepted helper is used UNCHANGED on the first
     conjunct (rJB_EI0, rTI_of_EI0, rr_JB_ck, rr_EI0_out, rr_EI0_sh, rr_TI_sh, rr_TI_fr, rr_TI_flag, rr_OUTF_wf,
     rr_win_addr_full, rr_z16, rp_td_pre_F); each copied lemma is the accepted script, and the fine munch goes
     around each run of stores by munch_trans with the run's own munch, weakened into rWSC G j (rWSC_sh16,
     rWSC_fr8, rWSC_flag, rWSC_out, rWSC_win).  While the accepted script runs stores, the fine munch is wrapped in
     the file's own rr_hide (:4123), so the store machinery does not transport it.  The continuations take a post
     indexed by the frame, QF G j, in place of one Q, so the final post rQSC G j names the frame the run used
     (G = fs_frame FS 1 jj in the glue).
     ====================================================================================================== *)

  (* The writes of stretch C from its base m.  Each entry, with the store that needs it:
       (S - 9072, S)        the call of reac_ctrl_record_cksum_verify writes [spc - 16, spc) (rp_tag, accepted :4733);
       (G, G + 128)         the word at G := 0x45e0360e (rp_epi, the store at accepted :3994);
       the frame's shadow   its 16 bytes (rp_f8 :4047-4076, rr_z16 via rp_td_real, rp_td_pre_F :3786-3880);
       the frame's flag     the release store 0x84c34 `sb zero,0(a1)` (rp_td_side, accepted :3952);
       rOUTW (:4127)        the three OUT stores (rp_stores), on the success path only.
     The OUT cells are under reply_ok, not reply_args: rp_stores runs only with reply_ok = true (rKS's premise),
     so this list is the finer one; munch_weaken gives the reply_args form. *)
  Definition rWSC (G j : Z) : list ivl :=
    (S - 9072, S) :: (G, G + 128) :: (shadow_addr G, shadow_addr G + 16) :: (fs_flag FS 1 j, fs_flag FS 1 j + 1) ::
    (if reply_ok fr len pa pp pn g then rOUTW else []).

  Lemma rWSC_win : forall G j a b, S - 9072 <= a -> b <= S -> sub_fp [(a, b)] (rWSC G j).
  Proof.
    intros G j a b Ha Hb x Hx. unfold rWSC in Hx. cbn [outside] in Hx |- *. destruct Hx as (H1 & _).
    split; [clear - H1 Ha Hb; lia | exact I].
  Qed.

  Lemma rWSC_fr8 : forall G j, sub_fp [(G, G + 8)] (rWSC G j).
  Proof.
    intros G j x Hx. unfold rWSC in Hx. cbn [outside] in Hx |- *. destruct Hx as (_ & H2 & _).
    split; [clear - H2; lia | exact I].
  Qed.

  Lemma rWSC_sh16 : forall G j, sub_fp [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] (rWSC G j).
  Proof.
    intros G j x Hx. unfold rWSC, shadow_addr in Hx. cbn [outside] in Hx |- *. destruct Hx as (_ & _ & H3 & _).
    split; [first [exact H3 | clear - H3; lia] | exact I].
  Qed.

  Lemma rWSC_flag : forall G j, sub_fp [(fs_flag FS 1 j, fs_flag FS 1 j + 1)] (rWSC G j).
  Proof.
    intros G j x Hx. unfold rWSC in Hx. cbn [outside] in Hx |- *. destruct Hx as (_ & _ & _ & H4 & _).
    split; [exact H4 | exact I].
  Qed.

  Lemma rWSC_out : reply_ok fr len pa pp pn g = true -> forall G j, sub_fp rOUTW (rWSC G j).
  Proof.
    intros OK G j x Hx. unfold rWSC in Hx. rewrite OK in Hx. cbn [outside] in Hx.
    destruct Hx as (_ & _ & _ & _ & H5). exact H5.
  Qed.

  (* COPY of rJB (accepted :2371-2375), statement: rJB AND munch (rWSC G j) m mc.  At the base (mc = m) the added
     conjunct is munch_refl (rJBSC_base). *)
  Definition rJBSC (G j nn : Z) (mc : word -> option byte) : Prop := rJB G j nn mc /\ munch (rWSC G j) m mc.

  Lemma rJBSC_base : forall G j nn, rJB G j nn m -> rJBSC G j nn m.
  Proof. intros G j nn H. exact (conj H (munch_refl (rWSC G j) m)). Qed.

  (* COPY of rEI0 (accepted :1994), statement: rEI0 AND munch (rWSC G j) m mc. *)
  Definition rEI0SC (G j nn : Z) (mc : word -> option byte) : Prop := rEI0 G j nn mc /\ munch (rWSC G j) m mc.

  (* COPY of rTI (accepted :3066-3070), statement: rTI AND munch (rWSC G j) m mc. *)
  Definition rTISC (G j nn : Z) (mc : word -> option byte) : Prop := rTI G j nn mc /\ munch (rWSC G j) m mc.

  (* COPY of rTJ (accepted :3073-3077), statement: rTJ AND munch (rWSC G j) m mc AND, for a side frame, the frame's
     flag byte 0 (the release store 0x84c34 wrote it; rp_td_sideSC carries the store's own bytes_at fact to here).
     rTJ names no frame, so G j are parameters here. *)
  Definition rTJSC (G j : Z) (mc : word -> option byte) : Prop :=
    rTJ mc /\ munch (rWSC G j) m mc /\ (G = fs_frame FS 1 j -> bytes_at rsegs mc (fs_flag FS 1 j) [Z_to_bv 8 0]).

  (* The real-stack frame (rFK's first arm: nn = 0, j = 0, G = rA - 128) is never a class-1 side frame: every side
     frame lies below FS + 11571200 <= S - 9072 (rr_fsn), and rA - 128 >= S - 272 (rA_facts). *)
  Lemma rr_real_not_side : forall G fv spc j nn, rFK G fv spc j nn -> nn = 0 -> G <> fs_frame FS 1 j.
  Proof.
    intros G fv spc j nn HK En EG. rewrite (rrF_fs_frame1 FS j) in EG.
    pose proof rA_facts as (_ & HAlo & _). destruct rr_fsn as (_ & _ & _ & F4 & _).
    destruct HK as [(_ & EG0 & _ & Ej0 & _)|(_ & _ & _ & _ & En1)]; [|clear - En En1; lia].
    rewrite Ej0 in EG. clear - EG EG0 F4 HAlo. lia.
  Qed.

  (* COPY of rQ (F_on :3057-3066;
     accepted :3028-3037).  Statement: the frame G j are parameters; munch (rWSC G j) m m' in place of
     munch rWP m m'; one more conjunct: for a side frame (G = fs_frame FS 1 j), the frame's flag byte is 0 in m'
     (the release store 0x84c34; the journal's free step and ctl_release_of_free_law need it). *)
  Definition rQSC (G j : Z) : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (reply_ret fr len pa pp pn g))
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch (rWSC G j) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - 9072) S /\
      (reply_ok fr len pa pp pn g = true -> rOUTF m') /\
      asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m') /\ addressable m' (S - 9072) 9072 /\
      fp [1%nat] m' (bv_unsigned tp) FS (S - 9072) S rWW rDD /\
      reac_ctrl_identity_reply_tls m' (bv_unsigned tp) FS (S - 9072) S /\
      (G = fs_frame FS 1 j -> bytes_at rsegs m' (fs_flag FS 1 j) [Z_to_bv 8 0]).

  (* COPY of rKE (F_on :2169-2176;
     accepted :2144-2151).  Statement: the post is QF G j in place of Q; rEI0SC in place of rEI0. *)
  Definition rKESC (QF : Z -> Z -> machine_state -> Prop) : Prop :=
    forall G fv spc j nn mc r (x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30
                              x31 : word),
      rFK G fv spc j nn -> rEI0SC G j nn mc -> (reply_ok fr len pa pp pn g = true -> rOUTF mc) ->
      r = reply_ret fr len pa pp pn g ->
      evtF rsegs RNG (QF G j) (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 fv) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) x27
                        x28 x29 x30 x31) F (Z_to_bv 64 0x84bdc) fc None mc (seg_rom rsegs)).

  (* COPY of rKT (F_on :4057-4064;
     accepted :4022-4029).  Statement: the post is QF G j in place of Q; rEI0SC in place of rEI0. *)
  Definition rKTSC (QF : Z -> Z -> machine_state -> Prop) : Prop :=
    forall G fv spc j nn mc r (x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29
                               x30 x31 : word),
      rFK G fv spc j nn -> rEI0SC G j nn mc -> (reply_ok fr len pa pp pn g = true -> rOUTF mc) ->
      r = reply_ret fr len pa pp pn g ->
      evtF rsegs RNG (QF G j) (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 fv) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) x27
                        x28 x29 x30 x31) F (Z_to_bv 64 0x84bc4) fc None mc (seg_rom rsegs)).

  (* COPY of rKV (F_on :4123-4129;
     accepted :4085-4091).  Statement: the post is QF G j in place of Q; rEI0SC in place of rEI0. *)
  Definition rKVSC (QF : Z -> Z -> machine_state -> Prop) : Prop :=
    forall G fv spc j nn mc (x1 x2 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29
                             x30 x31 : word),
      rFK G fv spc j nn -> rEI0SC G j nn mc -> reply_args fr pa pp pn = true -> ir len g = false ->
      evtF rsegs RNG (QF G j) (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 x10 x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 fv) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) x27
                        x28 x29 x30 x31) F (Z_to_bv 64 0x84bc0) fc None mc (seg_rom rsegs)).

  (* COPY of rKS (F_on :4269-4277;
     accepted :4231-4239).  Statement: the post is QF G j in place of Q; rJBSC in place of rJB. *)
  Definition rKSSC (QF : Z -> Z -> machine_state -> Prop) : Prop :=
    forall (G fv spc j nn : Z) (mc : word -> option byte)
           (x1 x2 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      rFK G fv spc j nn -> rJBSC G j nn mc -> reply_ok fr len pa pp pn g = true ->
      evtF rsegs RNG (QF G j) (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 rA) x10 x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 fv) (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa)
                         (Z_to_bv 64 (fr + 18)) (Z_to_bv 64 (ir_s g)) (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G)
                         (wa ASAN_K) x28 x29 x30 x31)
                    F (Z_to_bv 64 0x84cbc) fc None mc (seg_rom rsegs)).

  (* COPY of rKF (F_on :2410-2419;
     accepted :2384-2393), the continuation at reac_ctrl_parse's return 0x84a68.  Statement: the post
     is QF G j in place of Q; rJBSC in place of rJB. *)
  Definition rKFSC (QF : Z -> Z -> machine_state -> Prop) : Prop :=
    forall (G fv spc j nn : Z) (mc : word -> option byte)
           (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      rFK G fv spc j nn -> rJBSC G j nn mc -> reply_args fr pa pp pn = true ->
      evtF rsegs RNG (QF G j) (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 rA)
                         (Z_to_bv 64 (fst (ctrlparse len g))) x11 x12 x13 x14 x15 x16 x17
                         (Z_to_bv 64 fv) (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa)
                         (Z_to_bv 64 len) (Z_to_bv 64 (G + 32)) (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G)
                         (wa ASAN_K) x28 x29 x30 x31)
                    F (Z_to_bv 64 0x84a68) fc None mc (seg_rom rsegs)).

  (* COPY of rp_ret (F_on :3285-3306;
     accepted :3256-3277).  Statement: G j first; rTJSC G j in place of rTJ; post rQSC G j in place
     of rQ.  Script: the intro pattern also names MUw (the fine munch) and FL0 (the side frame's flag byte 0); the
     post's munch conjunct is MUw and its last conjunct FL0 (the run makes no store: mc is the end memory). *)
  Lemma rp_retSC : forall G j mc r
      (x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
       x31 : word),
    rTJSC G j mc -> (reply_ok fr len pa pp pn g = true -> rOUTF mc) -> r = reply_ret fr len pa pp pn g ->
    evtF rsegs RNG (rQSC G j) (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                        x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x84c7c) fc None mc (seg_rom rsegs)).
  Proof.
    intros G j mc r x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
      x31 ((MU & WM & RM & MI1 & SV & AW1 & FP1 & TL1) & MUw & FL0) HOF Er.
    replace (S - 104) with (S + -104) in SV by lia. unfold rSAVES in SV.
    pose proof (rr_stk_mono m mc _ _ ST WM RM) as STm.
    assert (ACm : asan_cells mc) by (apply (fl_asan_cells rWP m mc AC MU); exact rr_RT_outWP).
    pose proof (fun P (HP : shadow_rw_on P m) => rr_shadow_rw_on_mono P m mc HP WM RM) as SWm.
    do 16 step.
    apply evtF_done. unfold rQSC. subst r.
    do 14 eexists. exists mc.
    split; [reflexivity|].
    split; [exact MUw|]. split; [exact WM|]. split; [exact MI1|]. split; [exact STm|].
    split; [exact HOF|]. split; [exact ACm|]. split; [exact SWm|]. split; [exact AW1|].
    split; [exact FP1|]. split; [exact TL1 | exact FL0].
  Qed.

  (* COPY of rp_td_post_F (F_on :3928-3946;
     accepted :3893-3911).  Statement: rTISC in place of rTI; one more premise, the frame's
     flag byte 0 in mc (the release store's own fact, from rp_td_sideSC); post rQSC G j in place of rQ.  Script:
     rp_retSC in place of rp_ret, its rTJSC's other conjuncts MUw and the flag byte (no store here; the flag fact
     is wrapped in rr_hide across the jump). *)
  Lemma rp_td_post_FSC : forall G spc j nn mc r
      (x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
    rFK G G spc j nn -> nn = 1 -> rTISC G j nn mc ->
    bytes_at rsegs mc (fs_flag FS 1 j) [Z_to_bv 8 0] -> (reply_ok fr len pa pp pn g = true -> rOUTF mc) ->
    r = reply_ret fr len pa pp pn g ->
    evtF rsegs RNG (rQSC G j) (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 G) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (G / 8 + ASAN_K)) x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x84c38) fc None mc (seg_rom rsegs)).
  Proof.
    intros G spc j nn mc r x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31
      HK En (TI & MUw) HF0 HOF Er.
    apply rr_hide_in in HF0.
    pose proof TI as (MU18 & WM18 & RM18 & MI18 & SV18 & AX18 & FP18 & TL18 & FL18).
    step. (* j 0x84c7c *)
    eapply rp_retSC.
    - split; [|split; [exact MUw | exact (fun _ => rr_hide_out _ HF0)]].
      split; [exact MU18|]. split; [exact WM18|]. split; [exact RM18|]. split; [exact MI18|]. split; [exact SV18|].
      split; [exact (rr_win_addr_full G G spc j nn mc HK AX18 ltac:(intros E0; exfalso; clear - E0 En; lia))|].
      split; [exact FP18 | exact TL18].
    - exact HOF.
    - exact Er.
  Qed.

  (* COPY of rp_td_real (F_on :3729-3764;
     accepted :3700-3732), the real-frame teardown (nn = 0).  Statement: rTISC in place of rTI;
     post rQSC G j in place of rQ.  Script: rr_z16 at Q := rQSC G j; rp_retSC in place of rp_ret, the fine munch
     carried across the 16 shadow stores by MU16 (rWSC_sh16); the flag conjunct is vacuous (rr_real_not_side). *)
  Lemma rp_td_realSC : forall G fv spc j nn mc r
      (x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
    rFK G fv spc j nn -> nn = 0 -> rTISC G j nn mc -> (reply_ok fr len pa pp pn g = true -> rOUTF mc) ->
    r = reply_ret fr len pa pp pn g ->
    evtF rsegs RNG (rQSC G j) (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                        x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (G / 8 + ASAN_K)) x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x84c3c) fc None mc (seg_rom rsegs)).
  Proof.
    intros G fv spc j nn mc r x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x26 x27 x28
      x29 x30 x31 HK En (TI & MUw) HOF Er.
    pose proof TI as (MUt & WMt & RMt & MI1t & SVt & AXt & FPt & TLt & FLt).
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & FRA & _ & SH1 & SH2).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6). pose proof rA_facts as (HA32 & HAlo & HAhi).
    assert (HG0 : 0 <= G) by (clear - FRlo F1; lia).
    assert (SWmc : shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) mc)
      by exact (rr_shadow_rw_on_mono _ m mc SW WMt RMt).
    assert (SWh : forall i, 0 <= i < 16 -> wview rsegs mc (wa (G / 8 + ASAN_K + i)) <> None).
    { intros i Hi.
      apply (rr_stk_wv mc _ _ _ (rr_shadow16_stk_on _ mc G SWmc (rk_inR _ _ _ _ _ HK) HG0 FRA SH1 SH2)).
      clear - Hi; lia. }
    apply (rr_z16 G mc (rQSC G j) x1 x2 x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
             x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) SWh MI1t
             (rrF_frame_blk G fv spc j nn HK)).
    intros m16 MU16 WM16 RM16 MI16 Z16.
    pose proof (rr_TI_sh G fv spc j nn mc m16 HK TI MU16 WM16 RM16 MI16) as TI16.
    pose proof TI16 as (MUf & WMf & RMf & MIf & SVf & AXf & FPf & TLf & FLf).
    assert (HGaddr : nn = 0 -> addressable m16 G 128).
    { intros _. apply rr_frame_all_addr; [exact HG0 | exact FR8
        | clear - FRhi HAhi HAE; lia | exact FAP | exact Z16]. }
    eapply rp_retSC.
    - split; [|split; [exact (munch_trans _ m mc m16 MUw (munch_weaken _ _ mc m16 (rWSC_sh16 G j) MU16))
                     | exact (fun EGF => False_ind _ (rr_real_not_side G fv spc j nn HK En EGF))]].
      split; [exact MUf|]. split; [exact WMf|]. split; [exact RMf|]. split; [exact MIf|]. split; [exact SVf|].
      split; [exact (rr_win_addr_full G fv spc j nn m16 HK AXf HGaddr)|]. split; [exact FPf | exact TLf].
    - intros HOK. exact (rr_OUTF_wf G fv spc j nn mc m16 HK
        (munch_weaken _ _ mc m16 (rr_sh16_Wf G j nn) MU16) WM16 HOK (HOF HOK)).
    - exact Er.
  Qed.

  (* COPY of rp_td_side (F_on :3950-4004;
     accepted :3915-3969), the side-frame teardown with the release store 0x84c34.  Statement:
     rTISC in place of rTI; post rQSC G j in place of rQ.  Script: rp_td_pre_F UNCHANGED; the fine munch hidden
     during the stores, then carried by Mq (rp_td_pre_F's 16 shadow bytes, rWSC_sh16) and MqF' (the flag byte,
     rWSC_flag) into rp_td_post_FSC, with the store's own fact BqF' (the flag byte is 0). *)
  Lemma rp_td_sideSC : forall G fv spc j nn mc r
      (x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 : word),
    rFK G fv spc j nn -> nn = 1 -> fv = G -> rTISC G j nn mc -> (reply_ok fr len pa pp pn g = true -> rOUTF mc) ->
    r = reply_ret fr len pa pp pn g ->
    evtF rsegs RNG (rQSC G j) (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 fv) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 (G / 8 + ASAN_K)) x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x84bec) fc None mc (seg_rom rsegs)).
  Proof.
    intros G fv spc j nn mc r x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29
      x30 x31 HK En Efv (TI & MUw) HOF Er. subst fv.
    apply rr_hide_in in MUw.
    pose proof TI as (MUt & WMt & RMt & MI1t & SVt & AXt & FPt & TLt & FLt).
    destruct (rk_facts G G spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & FRA & _ & SH1 & SH2).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6). pose proof rA_facts as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (rr_fsnum FS j) as (_ & E2j & _).
    assert (EGj : G = FS + 1085440 + j * 128 /\ 0 <= j < 8192)
      by (destruct (rk_place G G spc j nn HK) as [(E0 & _)|(_ & Hj & EG)]; [lia|]; split; [exact EG | exact Hj]).
    pose proof (rrF_frame G G spc j nn HK) as RGFRM. pose proof (rrF_frame_blk G G spc j nn HK) as SBFRM.
    assert (RGFLj : rng RNG (fs_flag FS 1 j) 1).
    { assert (EMj : fs_M 1 = 8192) by reflexivity. destruct EGj as (_ & Hj8).
      eapply rng_sub; [exact RFLG | rewrite !rrF_fs_flag1; lia | rewrite !rrF_fs_flag1; lia]. }
    eapply evtF_cut;
      [exact (rp_td_pre_F G spc j nn mc r x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 HK En TI) |].
    intros ms' (m16 & TI16 & Mq & Wq & ->).
    pose proof TI16 as (MU16t & WM16t & RM16t & MI16t & SV16t & AX16t & FP16t & TL16t & FL16t).
    pose proof FP16t as (DT & TS & C & T & DB & k & _ & _ & (P1 & P2 & P3 & P4 & P5) & _).
    pose proof (rr_stk_wv _ FS (FS + FS_SIZE) (fs_flag FS 1 j) P5
                  ltac:(rewrite E2j; unfold FS_SIZE; clear - EGj; lia)) as WVF.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m16 _) =>
      assert (BqF : bytes_at rsegs m16 (fs_flag FS 1 j) (@nil byte))
        by (split; [rewrite E2j; clear - EGj F1; lia|]; split;
              [cbn [length Z.of_nat]; rewrite E2j; clear - EGj F4 HAE'; lia | intros i Hi; cbn [length] in Hi; lia]);
      assert (HSF : store_ok rsegs m16 (wa (fs_flag FS 1 j)) 1 = true)
        by (eapply rr_wv_store_ok;
              [ intros i Hi; replace (fs_flag FS 1 j + i) with (fs_flag FS 1 j) by (clear - Hi; lia); exact WVF
              | exact (wmono_refl rsegs m16) | rewrite E2j; clear - EGj F1; lia
              | rewrite E2j; clear - EGj F4 HAE'; lia ]) end.
    step. rewrite rr_le1_0.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m16 _ _) _) =>
      destruct (rr_sb_step _ _ m16 (fs_flag FS 1 j) 1 (@nil byte) (Z_to_bv 8 0) (fs_flag FS 1 j)
                  ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; ring) ltac:(rewrite E2j; clear - EGj F1; lia)
                  ltac:(rewrite E2j; clear - EGj F4 HAE'; lia) ltac:(cbn [length Z.of_nat Pos.of_succ_nat]; lia)
                  BqF (munch_refl [(fs_flag FS 1 j, fs_flag FS 1 j + 1)] m16) (wmono_refl rsegs m16)
                  (rr_rd_mono_refl m16) MI16t HSF) as (BqF' & MqF' & WqF' & RqF' & IqF') end.
    cbn [app] in BqF'.
    pose proof (rr_TI_flag G G spc j nn _ _ HK En TI16 MqF' WqF' RqF' IqF' BqF') as TI18.
    pose proof TI18 as (MU18 & WM18 & RM18 & MI18 & SV18 & AX18 & FP18 & TL18 & FL18).
    pose proof (munch_trans _ mc _ _
      (munch_weaken _ _ mc _ (rr_sh16_Wf G j nn) Mq)
      (munch_weaken [(fs_flag FS 1 j, fs_flag FS 1 j + 1)] (rWf G j nn) _ _
         ltac:(rewrite En; exact (rr_flagj_Wf G j)) MqF')) as MUrwf.
    exact (rp_td_post_FSC G spc j nn _ r x1 x2 x5 x6 x7 x9 (Z_to_bv 64 (fs_flag FS 1 j)) x12 x13 x14 x15 x16 x17 x19
             x20 x21 x22 x23 x24 x26 x27 x28 x29 x30 x31 HK En
             (conj TI18 (munch_trans _ m mc _ (rr_hide_out _ MUw)
                (munch_trans _ mc _ _ (munch_weaken _ _ mc _ (rWSC_sh16 G j) Mq)
                   (munch_weaken _ _ _ _ (rWSC_flag G j) MqF'))))
             BqF'
             (fun HOK => rr_OUTF_wf G G spc j nn mc _ HK MUrwf (wmono_trans rsegs mc _ _ Wq WqF') HOK (HOF HOK)) Er).
  Qed.

  (* COPY of rp_epi (F_on :4007-4054;
     accepted :3972-4019).  Statement: rKESC rQSC in place of rKE rQ.  Script: the fine munch hidden
     during the store at G, then carried by Mqg (rWSC_fr8) into TIgSC; rp_td_realSC / rp_td_sideSC in place of
     rp_td_real / rp_td_side, given TIgSC in place of TIg. *)
  Lemma rp_epiSC : rKESC rQSC.
  Proof.
    intros G fv spc j nn mc r x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30
      x31 HK (EI & MUw) HOF Er.
    apply rr_hide_in in MUw.
    pose proof (rTI_of_EI0 G j nn mc EI) as TI.
    pose proof TI as (MUt & WMt & RMt & MI1t & SVt & AXt & FPt & TLt & FLt).
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & FRA & _ & SH1 & SH2).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6). pose proof rA_facts as (HA32 & HAlo & HAhi).
    assert (HG0 : 0 <= G) by (clear - FRlo F1; lia).
    pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
    pose proof (rrF_frame G fv spc j nn HK) as RGFRM.
    assert (WVG : forall i, 0 <= i < 8 -> wview rsegs mc (wa (G + i)) <> None).
    { intros i Hi. destruct (rk_facts G fv spc j nn HK) as (_ & _ & _ & _ & FW & _).
      apply WMt. apply FW. clear - Hi; lia. }
    pose proof (munch_refl [(G, G + 8)] mc) as Mqg. pose proof (wmono_refl rsegs mc) as Wqg.
    pose proof (rr_rd_mono_refl mc) as Rqg. pose proof MI1t as Iqg.
    do 2 step. (* lui a1; addiw a1 *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HSG : store_ok rsegs mm (wa G) 8 = true)
        by (eapply rr_wv_store_ok;
              [ intros i Hi; apply WVG; clear - Hi; lia | exact (wmono_refl rsegs mm)
              | clear - HG0; lia | clear - FRhi HAhi HAE'; lia ]) end.
    step. (* sd a1,0(s10) *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 G 8 G bs 8%nat ltac:(apply length_le8) ltac:(clear - HG0; lia)
        ltac:(clear - FRhi HAhi HAE'; lia) ltac:(clear - HG0; lia) ltac:(clear - HG0; lia)
        Mqg Wqg Rqg Iqg HSG) as (Mqg' & Wqg' & Rqg' & Iqg') end.
    clear Mqg Wqg Rqg Iqg HSG. rename Mqg' into Mqg, Wqg' into Wqg, Rqg' into Rqg, Iqg' into Iqg.
    pose proof (rr_TI_fr G fv spc j nn mc _ HK TI Mqg Wqg Rqg Iqg) as TIg.
    pose proof (conj TIg (munch_trans _ m mc _ (rr_hide_out _ MUw) (munch_weaken _ _ mc _ (rWSC_fr8 G j) Mqg)))
      as TIgSC.
    step. (* beqz s2 *)
    pose proof HK as HKc.
    destruct HKc as [(Efv0 & EG0 & Esp0 & Ej0 & En0)|(Hj1 & EG1 & Efv1 & Esp1 & En1)].
    - (* nn = 0, fv = 0: beqz taken -> 0x84c3c *)
      rewrite (rc_beq0_true fv Efv0). cbv iota.
      eapply rp_td_realSC; [exact HK | exact En0 | exact TIgSC
        | intros HOK; exact (rr_OUTF_wf G fv spc j nn mc _ HK
            (munch_weaken _ _ mc _ (rr_frame8_Wf G j nn) Mqg) Wqg HOK (HOF HOK))
        | exact Er].
    - (* nn = 1, fv = G: beqz not taken -> 0x84bec *)
      assert (Gpos : 0 < G) by (clear - FRlo F1; lia).
      assert (Gub : G < 2 ^ 64) by (clear - FRhi HAhi HS; lia).
      rewrite (rc_beq0_false fv ltac:(rewrite Efv1; clear - Gpos; lia)
                 ltac:(rewrite Efv1; clear - Gpos Gub; lia)). cbv iota.
      eapply rp_td_sideSC; [exact HK | exact En1 | exact Efv1 | exact TIgSC
        | intros HOK; exact (rr_OUTF_wf G fv spc j nn mc _ HK
            (munch_weaken _ _ mc _ (rr_frame8_Wf G j nn) Mqg) Wqg HOK (HOF HOK))
        | exact Er].
  Qed.

  (* COPY of rp_f8 (F_on :4067-4120;
     accepted :4032-4082).  Statement: rKESC QF -> rKTSC QF in place of rKE Q -> rKT Q.  Script: the
     fine munch hidden during the 5 shadow stores, then carried by Mq (rWSC_sh16) into KE's rEI0SC. *)
  Lemma rp_f8SC : forall QF, rKESC QF -> rKTSC QF.
  Proof.
    intros Q KE G fv spc j nn mc r x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29
      x30 x31 HK (EI & MUw) HOF Er.
    apply rr_hide_in in MUw.
    destruct (rk_facts G fv spc j nn HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & FRA & _ & SH1 & SH2).
    destruct rr_fsn as (F1 & F2 & F3 & F4 & F5 & F6).
    assert (HG0 : 0 <= G) by (clear - FRlo F1; lia).
    pose proof (rrF_frame_blk G fv spc j nn HK) as SBFRM.
    pose proof EI as (MUe & WMe & RMe & MI1e & SVe & AXe & FPe & TLe & H120e).
    assert (SWmc : shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) mc)
      by exact (rr_shadow_rw_on_mono _ m mc SW WMe RMe).
    assert (SWh : forall i, 0 <= i < 16 -> wview rsegs mc (wa (G / 8 + ASAN_K + i)) <> None).
    { intros i Hi.
      apply (rr_stk_wv mc _ _ _ (rr_shadow16_stk_on _ mc G SWmc (rk_inR _ _ _ _ _ HK) HG0 FRA SH1 SH2)).
      clear - Hi; lia. }
    pose proof (munch_refl [(G / 8 + ASAN_K, G / 8 + ASAN_K + 16)] mc) as Mq.
    pose proof (wmono_refl rsegs mc) as Wq. pose proof (rr_rd_mono_refl mc) as Rq. pose proof MI1e as Iq.
    step. (* li a1,-8 *)
    rwstb (G / 8 + ASAN_K + 4) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 4) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 5) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 5) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 6) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 6) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 7) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 7) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    rwstb (G / 8 + ASAN_K + 8) 1%nat (G / 8 + ASAN_K) SWh. step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ ?bs) _) =>
      destruct (rr_st_runw _ _ m1 (G / 8 + ASAN_K) 16 (G / 8 + ASAN_K + 8) bs 1%nat ltac:(apply length_le1)
        ltac:(clear - SH1; lia) ltac:(clear - SH2; lia) ltac:(clear - SH1; lia) ltac:(clear - SH1 SH2; lia)
        Mq Wq Rq Iq HS0) as (Mq' & Wq' & Rq' & Iq') end.
    clear Mq Wq Rq Iq HS0. rename Mq' into Mq, Wq' into Wq, Rq' into Rq, Iq' into Iq.
    pose proof (rr_EI0_sh G fv spc j nn mc _ HK EI Mq Wq Rq Iq) as EI5.
    eapply KE; [exact HK
      | exact (conj EI5 (munch_trans _ m mc _ (rr_hide_out _ MUw) (munch_weaken _ _ mc _ (rWSC_sh16 G j) Mq)))
      | intros HOK; exact (rr_OUTF_wf G fv spc j nn mc _ HK
          (munch_weaken _ _ mc _ (rr_sh16_Wf G j nn) Mq) Wq HOK (HOF HOK))
      | exact Er].
  Qed.

  (* COPY of rp_fail (F_on :4131-4139;
     accepted :4093-4101).  Statement: rKTSC QF -> rKVSC QF in place of rKT Q -> rKV Q.  Script:
     unchanged (no store; EI is the rEI0SC pair and goes to KT whole). *)
  Lemma rp_failSC : forall QF, rKTSC QF -> rKVSC QF.
  Proof.
    intros Q KT G fv spc j nn mc x1 x2 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28
      x29 x30 x31 HK EI RAb EIR.
    assert (RR : reply_ret fr len pa pp pn g = 0) by (unfold reply_ret; rewrite RAb, EIR; reflexivity).
    assert (OK : reply_ok fr len pa pp pn g = false) by (unfold reply_ok; rewrite RAb, EIR; reflexivity).
    step. (* li a0,0 *)
    eapply KT; [exact HK | exact EI | intros HOK; rewrite OK in HOK; discriminate | symmetry; exact RR].
  Qed.

  (* COPY of rp_stores (F_on :4338-4494;
     accepted :4300-4456).  Statement: rKTSC QF -> rKSSC QF in place of rKT Q -> rKS Q.  Script:
     beside FIN (built before the run of stores, as the accepted script builds it), FINW carries the fine munch
     to the end memory by the run's MUapp (rWSC_out); MUw is cleared before the stores; KT's rEI0SC is split into
     FIN's goal and FINW's. *)
  Lemma rp_storesSC : forall QF, rKTSC QF -> rKSSC QF.
  Proof.
    intros Q KT G fv spc j nn mc x1 x2 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HK (RJB & MUw) OKr.
    assert (RAb : reply_args fr pa pp pn = true)
      by (unfold reply_ok in OKr; destruct (reply_args fr pa pp pn); [reflexivity | discriminate]).
    assert (EIR : ir len g = true)
      by (unfold reply_ok in OKr; rewrite RAb in OKr; exact OKr).
    destruct (ir_bytes len g EIR) as (HL50 & _).
    destruct RJB as (MUb & CORE & RCrec & HBfr & OUTC & STKc & ACc & SWc).
    pose proof CORE as (_ & _ & MIc & _).
    destruct (HBfr HL50) as (HBg & AFg).
    destruct OUTC as (RWpa & RWpp & RWpn & ADpa & ADpp & ADpn).
    destruct (HO RAb) as (Hpa2 & Hpp8 & Hpn8 & _ & _ & _ & Dpa_pp & Dpa_pn & Dpp_pn & _ & _ & _).
    apply rr_hide_in in Dpa_pp, Dpa_pn, Dpp_pn.
    (* the state at the join, from the facts at mc: built outside the run of stores *)
    pose proof (rr_EI0_out G fv spc j nn mc HK OKr MUb CORE ADpa ADpp ADpn) as FIN.
    pose proof (fun (mf : word -> option byte) (MUo : munch rOUTW mc mf) =>
                  munch_trans _ m mc mf MUw (munch_weaken _ _ mc mf (rWSC_out OKr G j) MUo)) as FINW.
    clear MUw.
    pose proof (rr_sh_outOUT mc ADpa ADpp ADpn) as SHapp.
    (* the footprint of this segment: the 50 bytes at fr, pa, pp, pn and the shadow byte of each checked byte *)
    pose proof (RFR RAb HL50) as RGFR. pose proof (SCF RAb HL50) as SCFR.
    pose proof (RPA RAb) as RGPA. pose proof (SCPA RAb) as SCpa.
    pose proof (RPP RAb) as RGPP. pose proof (SCPP RAb) as SCpp.
    pose proof (RPN RAb) as RGPN. pose proof (SCPN RAb) as SCpn.
    clear HF HO AOUT AFfr ABC HBCMP HMEMCMP HGCF HCF254 HCF255 TLS0 PARSE MALLOC CKV AC SW ST AW MI FP0
      HHM HAE Rlen S16 HSK MUb CORE RCrec STKc ACc SWc HBfr.
    clear RBY RWIN SSW SCW SKW RFR SCF SKF RPA SCPA RPP SCPP RPN SCPN SKBC RFSS RFLG RFRM SCFM SKFM RW1 RTLS.
    (* the bounds and the shadow facts *)
    destruct (rt_addressable_bound mc fr 50 AFg) as (Hfr0 & _ & Hfr47).
    destruct (rt_addressable_bound mc pa 2 ADpa) as (Hpa0 & _ & Hpa47).
    destruct (rt_addressable_bound mc pp 8 ADpp) as (Hpp0 & _ & Hpp47).
    destruct (rt_addressable_bound mc pn 8 ADpn) as (Hpn0 & _ & Hpn47).
    assert (RX36 : 0 <= fr + 36 < 2 ^ 64) by (clear - Hfr0 Hfr47; lia).
    assert (RX37 : 0 <= fr + 37 < 2 ^ 64) by (clear - Hfr0 Hfr47; lia).
    assert (RXpa : 0 <= pa < 2 ^ 64) by (clear - Hpa0 Hpa47; lia).
    assert (APpm : app_mem pp)
      by (pose proof (rr_app_in mc pp 8 0 ADpp ltac:(lia)) as Hz; rewrite Z.add_0_r in Hz; exact Hz).
    assert (APnm : app_mem pn)
      by (pose proof (rr_app_in mc pn 8 0 ADpn ltac:(lia)) as Hz; rewrite Z.add_0_r in Hz; exact Hz).
    pose proof (rr_shadow mc fr 50 36 1 (fr + 36) AFg ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(pose proof (Z.mod_pos_bound (fr + 36) 8 ltac:(lia)); lia) eq_refl) as SH36.
    pose proof (rr_shadow mc fr 50 37 1 (fr + 37) AFg ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(pose proof (Z.mod_pos_bound (fr + 37) 8 ltac:(lia)); lia) eq_refl) as SH37.
    pose proof (rr_shadow mc pa 2 0 2 pa ADpa ltac:(lia) ltac:(lia) ltac:(lia)
                 ltac:(apply rr_mod2_al; exact Hpa2) ltac:(ring)) as SHpa.
    assert (AApp : asan_addressable rsegs mc ASAN_K pp 8) by (apply rt_addressable; exact ADpp).
    assert (A3pp : asan_rt3 rsegs mc ASAN_K pp 8) by (apply rt_rt3; exact ADpp).
    destruct (asan_shadow_read rsegs mc ASAN_K pp 8 [] 0
                (rt_shadow_rd mc pp 8 [] ADpp (fun x _ => I)) ltac:(lia)) as (kp & RKpp & BKpp).
    assert (Skp0 : bv_signed kp = 0)
      by (apply (asan_check_8 rsegs mc ASAN_K pp 8 0 kp AApp A3pp ltac:(lia) ltac:(lia));
          [ rewrite Z.add_0_r; exact Hpp8 | exact BKpp ]).
    assert (Ukp0 : bv_unsigned kp = 0) by (apply rc_signed0_unsigned0; exact Skp0).
    rewrite Z.add_0_r in BKpp. clear RKpp.
    assert (AApn : asan_addressable rsegs mc ASAN_K pn 8) by (apply rt_addressable; exact ADpn).
    assert (A3pn : asan_rt3 rsegs mc ASAN_K pn 8) by (apply rt_rt3; exact ADpn).
    destruct (asan_shadow_read rsegs mc ASAN_K pn 8 [] 0
                (rt_shadow_rd mc pn 8 [] ADpn (fun x _ => I)) ltac:(lia)) as (kn & RKpn & BKpn).
    assert (Skn0 : bv_signed kn = 0)
      by (apply (asan_check_8 rsegs mc ASAN_K pn 8 0 kn AApn A3pn ltac:(lia) ltac:(lia));
          [ rewrite Z.add_0_r; exact Hpn8 | exact BKpn ]).
    assert (Ukn0 : bv_unsigned kn = 0) by (apply rc_signed0_unsigned0; exact Skn0).
    rewrite Z.add_0_r in BKpn. clear RKpn.
    (* the frame's 50 bytes as cells: the loads of g[36] and g[37] read them before any ov_read_bytes fact *)
    pose proof (rc_ro_of_bytes rsegs mc fr g HBg) as RO. rewrite Hg in RO. cbn [map seq] in RO.
    clear HBg AFg ADpa ADpp ADpn AApp A3pp AApn A3pn Skp0 Skn0 Hg.
    apply rr_hide_in in BKpp, BKpn.
    apply rr_hide_out in Dpa_pp, Dpa_pn, Dpp_pn.
    pose proof (munch_refl [(pa, pa + 2); (pp, pp + 8); (pn, pn + 8)] mc) as MUapp.
    pose proof (wmono_refl rsegs mc) as WQ.
    (* 0x84cbc .. 0x84cc0: fr + 18 <= 2^64 - 19 *)
    rubn (-19).
    (* 0x84cc4 .. 0x84cd4 (+ slow path 0x84db0): a0 = fr + 36, its shadow check *)
    step.
    chk_core (fr + 36) RX36 (Z_to_bv 5 12) SH36 pre_sr no_extra.
    (* 0x84cd8 .. 0x84ce4: fr + 18 <= 2^64 - 20; pa even *)
    rubn (-20).
    step. rewrite (rr_land1 pa) by lia.
    step. rbnz0.
    (* 0x84ce8 .. 0x84cfc (+ the interleaved lbu g[36]; slow path 0x84dbc): a0 = fr + 37, its shadow check *)
    step.
    chk_core (fr + 37) RX37 (Z_to_bv 5 13) SH37 pre_sr no_extra.
    (* 0x84d00 .. 0x84d10 (+ the interleaved lbu g[37]; slow path 0x84dc8): the shadow check of the 2 bytes at pa *)
    chk_core pa RXpa (Z_to_bv 5 13) SHpa pre_sr add1.
    clear RO.
    (* 0x84d14 .. 0x84d20: a0 = (g[36] << 8) | g[37]; sh a0,0(s6) *)
    step. step. step. step.
    (* 0x84d24 .. 0x84d2c: fr + 18 <= 2^64 - 21; pp 8-aligned *)
    step. rewrite (rr_ltu_negl (fr + 18) (-21)) by lia. cbv iota.
    step. rewrite (rr_land7 pp) by lia.
    step. rbnz0.
    (* 0x84d30 .. 0x84d3c: the shadow check of the 8 bytes at pp (no slow path: the byte is 0) *)
    step. rewrite ?(unsigned_lit pp) by lia. rewrite rc_shr3.
    step.
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        assert (BKpp1 : bytes_at rsegs mcur (asan_shadow ASAN_K pp) [kp])
          by (eapply rc_bytes_at_munch; [ exact (rr_hide_out _ BKpp) | exact MUapp |
               intros z Hz; cbn [length] in Hz;
               replace z with (asan_shadow ASAN_K pp) by lia;
               exact (SHapp pp APpm) ]);
        assert (HRp : ov_read_bytes rsegs mcur (wa (pp / 8 + ASAN_K)) 1 = Some [kp])
          by (replace (wa (pp / 8 + ASAN_K)) with (wa (asan_shadow ASAN_K pp + 0))
                by (unfold asan_shadow; f_equal; lia);
              rewrite (bytes_at_read rsegs mcur (asan_shadow ASAN_K pp) [kp] 0 1 BKpp1
                         ltac:(lia) ltac:(cbn; lia));
              reflexivity)
    end.
    step. step.
    unfold zxb. rewrite ?w0_lit. rewrite Ukp0.
    replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
    cbn [negb]. cbv iota.
    clear HRp BKpp1.
    (* 0x84d40 .. 0x84d4c: a0 = fr + 38; pn 8-aligned; sd a0,0(s4) *)
    step.
    step. rewrite (rr_land7 pn) by lia.
    step.
    step. rbnz0.
    (* 0x84d50 .. 0x84d5c: the shadow check of the 8 bytes at pn *)
    step. rewrite ?(unsigned_lit pn) by lia. rewrite rc_shr3.
    step.
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
        assert (BKpn1 : bytes_at rsegs mcur (asan_shadow ASAN_K pn) [kn])
          by (eapply rc_bytes_at_munch; [ exact (rr_hide_out _ BKpn) | exact MUapp |
               intros z Hz; cbn [length] in Hz;
               replace z with (asan_shadow ASAN_K pn) by lia;
               exact (SHapp pn APnm) ]);
        assert (HRn : ov_read_bytes rsegs mcur (wa (pn / 8 + ASAN_K)) 1 = Some [kn])
          by (replace (wa (pn / 8 + ASAN_K)) with (wa (asan_shadow ASAN_K pn + 0))
                by (unfold asan_shadow; f_equal; lia);
              rewrite (bytes_at_read rsegs mcur (asan_shadow ASAN_K pn) [kn] 0 1 BKpn1
                         ltac:(lia) ltac:(cbn; lia));
              reflexivity)
    end.
    step. step.
    unfold zxb. rewrite ?w0_lit. rewrite Ukn0.
    replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
    cbn [negb]. cbv iota.
    clear HRn BKpn1.
    (* 0x84d60 .. 0x84d6c: s8 = ir_s - 13; sd s8,0(s3); a0 = 1; j 0x84bc4 *)
    step. step. step. step.
    (* the teardown join *)
    assert (ERET : Z_to_bv 64 1 = Z_to_bv 64 (reply_ret fr len pa pp pn g))
      by (unfold reply_ret; rewrite RAb, EIR; reflexivity).
    rewrite ERET.
    eapply KT; [ exact HK | split | | reflexivity ].
    - apply FIN; [exact MUapp | exact WQ | | exact MIc].
      apply (rr_rd_mono_list _ mc _ MUapp).
      constructor; [|constructor; [|constructor; [|constructor]]]; cbn [fst snd]; intros y Hy.
      + apply (rr_rw_rd _ pa _ y RWpa). cbn [cells_bytes cbytes]. rewrite app_nil_r, length_le2. clear - Hy; lia.
      + apply (rr_rw_rd _ pp _ y RWpp). cbn [cells_bytes cbytes]. rewrite app_nil_r, length_le8. clear - Hy; lia.
      + apply (rr_rw_rd _ pn _ y RWpn). cbn [cells_bytes cbytes]. rewrite app_nil_r, length_le8. clear - Hy; lia.
    - exact (FINW _ MUapp).
    - intros _. split; [|split].
      + eapply rc_rw_flat; [exact RWpa|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
        rewrite (rc_le2_pack (cp_b g 37) (cp_b g 36)). reflexivity.
      + eapply rc_rw_flat; [exact RWpp|]. cbn [cells_bytes cbytes]. apply app_nil_r.
      + eapply rc_rw_flat; [exact RWpn|]. cbn [cells_bytes cbytes]. apply app_nil_r.
  Qed.

  (* COPY of rp_tag (F_on :4609-4809;
     accepted :4571-4773).  Statement: rKVSC QF -> rKSSC QF -> rKFSC QF in place of
     rKV Q -> rKS Q -> rKF Q.  Script: EI is the rEI0SC pair (rJB_EI0 with MUw), so every fail exit is unchanged;
     after the call of reac_ctrl_record_cksum_verify, RJB' is the rJBSC pair (rr_JB_ck UNCHANGED as RJB0, the
     fine munch carried by the callee's munch [(spc - 16, spc)], rWSC_win from rk_cwin). *)
  Lemma rp_tagSC : forall QF, rKVSC QF -> rKSSC QF -> rKFSC QF.
  Proof.
    intros Q KV KS G fv spc j nn mc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HK (RJB & MUw) RAb.
    pose proof (conj (rJB_EI0 G j nn mc RJB) MUw) as EI.
    pose proof (ctrlparse_kind_range len g) as KR.
    (* 0x84a68 .. 0x84a6c: the kind is 5 *)
    step. step.
    rewrite (rc_eqb64 (fst (ctrlparse len g)) 5) by lia.
    destruct (Z.eqb_spec (fst (ctrlparse len g)) 5) as [K5|K5]; cbn [negb]; cbv iota.
    2:{ eapply KV; [exact HK | exact EI | exact RAb |].
        apply rr_ir_false. intros Ht. apply ir_true in Ht. destruct Ht as (Ht & _). exact (K5 Ht). }
    destruct (ctrlparse_rec len g (or_introl K5)) as (HD & _ & N28 & N29).
    assert (HL50 : 50 <= len)
      by (unfold cp_hdr in HD; rewrite !andb_true_iff in HD; destruct HD as [[HD _] _]; apply Z.leb_le in HD;
          exact HD).
    pose proof RJB as (MUb & CORE & RCrec & HBfr & OUTC & STKc & ACc & SWc).
    pose proof CORE as (_ & _ & MIc & _).
    destruct (HBfr HL50) as (HBg & AFg).
    destruct (HF RAb HL50) as (Hf50 & _ & Hwf & _ & _ & _).
    (* the footprint of this segment: the 50 bytes at fr with their shadow, and the frame (the record at G + 32) *)
    pose proof (RFR RAb HL50) as RGFR. pose proof (SCF RAb HL50) as SCFR. pose proof (SKF RAb HL50) as SKFR.
    pose proof (rrF_frame G fv spc j nn HK) as RGFRM.
    destruct (rk_cwin G fv spc j nn HK) as (Cw1 & Cw2 & _ & _).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (Hfr0 : 0 < fr).
    { pose proof RAb as RA. unfold reply_args in RA. rewrite !andb_true_iff, !negb_true_iff, !Z.eqb_neq in RA.
      destruct RA as [[[Rf _] _] _]. clear - Rf Rfr; lia. }
    pose proof (ctrlparse_length len g) as LB.
    pose proof (cp_v_range' g 32) as R32. pose proof (cp_v_range' g 33) as R33.
    pose proof (cp_v_range' g 34) as R34. pose proof (cp_v_range' g 35) as R35.
    pose proof (cp_v_range' g 26) as Rs. pose proof (cp_v_range' g 27) as R27.
    assert (Rs' : 0 <= ir_s g < 256) by exact Rs.
    (* the record's type word, as one 2-byte cell *)
    apply (rc_rw_rebytes rsegs _ (G + 32) _
             [CB 28 (firstn 28 (snd (ctrlparse len g))); C2 (Z_to_bv 64 (cp_v g 34 * 256 + cp_v g 35));
              CB 6 (skipn 30 (snd (ctrlparse len g)))]) in RCrec.
    2:{ cbn [cells_wf cell_wf]. rewrite firstn_length_le, length_skipn, LB by lia. repeat split. }
    2:{ cbn [cells_bytes cbytes]. unfold cp_v. rewrite rc_le2_pair. rewrite !app_nil_r. rewrite <- N28, <- N29.
        symmetry. apply rc_b36_split. exact LB. }
    clear N28 N29 LB HD.
    (* the frame's 50 bytes as cells, and the shadow facts of the checked bytes *)
    pose proof (rc_ro_of_bytes rsegs mc fr g HBg) as RO. rewrite Hg in RO. cbn [map seq] in RO.
    assert (RX32 : 0 <= fr + 32 < 2^64) by (clear - Hfr0 Hf50; lia).
    assert (RX33 : 0 <= fr + 33 < 2^64) by (clear - Hfr0 Hf50; lia).
    assert (RX26 : 0 <= fr + 26 < 2^64) by (clear - Hfr0 Hf50; lia).
    assert (RX27 : 0 <= fr + 27 < 2^64) by (clear - Hfr0 Hf50; lia).
    pose proof (rr_shadow mc fr 50 32 1 (fr + 32) AFg ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (fr + 32) 8 eq_refl); lia) eq_refl) as SH32.
    pose proof (rr_shadow mc fr 50 33 1 (fr + 33) AFg ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (fr + 33) 8 eq_refl); lia) eq_refl) as SH33.
    pose proof (rr_shadow mc fr 50 26 1 (fr + 26) AFg ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (fr + 26) 8 eq_refl); lia) eq_refl) as SH26.
    pose proof (rr_shadow mc fr 50 27 1 (fr + 27) AFg ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (fr + 27) 8 eq_refl); lia) eq_refl) as SH27.
    (* 0x84a70 .. 0x84a78: the type word (lhu 28(s8), no shadow check) is 0x500 *)
    step.
    unfold zx16. rewrite (unsigned_lit (cp_v g 34 * 256 + cp_v g 35)) by lia.
    rewrite (Z.mod_small (cp_v g 34 * 256 + cp_v g 35)) by lia.
    step. step.
    rewrite (rc_eqb64 (cp_v g 34 * 256 + cp_v g 35) 1280) by lia.
    destruct (Z.eqb_spec (cp_v g 34 * 256 + cp_v g 35) 1280) as [T|T]; cbn [negb]; cbv iota.
    2:{ eapply KV; [exact HK | exact EI | exact RAb |].
        apply rr_ir_false. intros Ht. apply ir_true in Ht. destruct Ht as (_ & Ht & _). exact (T Ht). }
    (* 0x84a7c .. 0x84a80: fr >= 2^64 - 18 traps; 0x84a84: s7 = fr + 18; 0x84a88 .. 0x84a8c: s7 > 2^64 - 15 traps *)
    step. step. rewrite (rr_ltu_negr fr (-18)) by lia. cbn [negb]. cbv iota.
    step.
    rubn (-15).
    (* 0x84a90 .. 0x84aac: the byte at fr + 32 is 0x12 *)
    step.
    chk_core (fr + 32) RX32 (Z_to_bv 5 12) SH32 pre_sr no_extra.
    step. step. step.
    rewrite (rc_eqb_zxb (cp_b g 32) 18) by lia. rcv.
    destruct (Z.eqb_spec (cp_v g 32) 18) as [E32|E32]; cbn [negb]; cbv iota.
    2:{ eapply KV; [exact HK | exact EI | exact RAb |].
        apply rr_ir_false. intros Ht. apply ir_true in Ht. destruct Ht as (_ & _ & Ht & _). exact (E32 Ht). }
    (* 0x84ab0 .. 0x84ad4: the byte at fr + 33 is 0x12 *)
    rubn (-16).
    step.
    chk_core (fr + 33) RX33 (Z_to_bv 5 12) SH33 pre_sr no_extra.
    step. step. step.
    rewrite (rc_eqb_zxb (cp_b g 33) 18) by lia. rcv.
    destruct (Z.eqb_spec (cp_v g 33) 18) as [E33|E33]; cbn [negb]; cbv iota.
    2:{ eapply KV; [exact HK | exact EI | exact RAb |].
        apply rr_ir_false. intros Ht. apply ir_true in Ht. destruct Ht as (_ & _ & _ & Ht & _). exact (E33 Ht). }
    (* 0x84ad8 .. 0x84b00: s = the byte at fr + 26; s - 24 <u -10 fails unless 14 <= s <= 23 *)
    rubn (-9).
    step.
    chk_core (fr + 26) RX26 (Z_to_bv 5 12) SH26 pre_sr no_extra.
    step. step. rewrite ?rc_uzxb. rcv.
    step. step.
    rewrite (rc_srange (ir_s g)) by exact Rs'.
    destruct ((14 <=? ir_s g) && (ir_s g <=? 23)) eqn:SR; cbn [negb]; cbv iota.
    2:{ eapply KV; [exact HK | exact EI | exact RAb |].
        apply rr_ir_false. intros Ht. apply ir_true in Ht. destruct Ht as (_ & _ & _ & _ & Ht & _).
        rewrite andb_false_iff, !Z.leb_gt in SR. clear - Ht SR; lia. }
    rewrite andb_true_iff, !Z.leb_le in SR.
    (* 0x84b04: s7 > 2^64 - 10 traps; 0x84b08 .. 0x84b24: the byte at fr + 27 is 0xf0 *)
    step. rewrite (rr_ltu_negl (fr + 18) (-10)) by lia. cbv iota.
    step.
    chk_core (fr + 27) RX27 (Z_to_bv 5 12) SH27 pre_sr no_extra.
    step. step. step.
    rewrite (rc_eqb_zxb (cp_b g 27) 240) by lia. rcv.
    destruct (Z.eqb_spec (cp_v g 27) 240) as [E27|E27]; cbn [negb]; cbv iota.
    2:{ eapply KV; [exact HK | exact EI | exact RAb |].
        apply rr_ir_false. intros Ht. apply ir_true in Ht. destruct Ht as (_ & _ & _ & _ & _ & Ht & _).
        exact (E27 Ht). }
    (* 0x84b28 .. 0x84b30: a0 = s + 8; ~(fr + 18) <u s + 8 traps *)
    step. step. rewrite ?rc_uzxb. rcv.
    try rewrite (unsigned_lit (fr + 18)) by lia. rewrite (zb_lxor_ones (fr + 18)) by lia.
    step. rewrite (rc_ltu64 (18446744073709551615 - (fr + 18)) (ir_s g + 8)) by lia.
    replace (18446744073709551615 - (fr + 18) <? ir_s g + 8) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota.
    (* 0x84b34 .. 0x84b50: the byte at fr + 18 + s + 8 = fr + 26 + s is 0xf7 *)
    step.
    try replace (fr + 18 + (ir_s g + 8)) with (fr + 18 + ir_s g + 8) by ring.
    assert (RX5 : 0 <= fr + 18 + ir_s g + 8 < 2^64) by (clear - Hfr0 Hf50 SR; lia).
    pose proof (rr_shadow mc fr 50 (26 + ir_s g) 1 (fr + 18 + ir_s g + 8) AFg ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (fr + 18 + ir_s g + 8) 8 eq_refl); lia) ltac:(lia)) as SH5.
    chk_core (fr + 18 + ir_s g + 8) RX5 (Z_to_bv 5 12) SH5 pre_sr no_extra.
    pose proof (rd_byte rsegs mc fr g (Z.to_nat (26 + ir_s g)) HBg ltac:(rewrite Hg; lia)) as RD8.
    step. step. step.
    match goal with |- context [zxb (nth ?i g (Z_to_bv 8 0))] =>
      rewrite (rc_eqb_zxb (nth i g (Z_to_bv 8 0)) 247) by lia end.
    rcv.
    destruct (Z.eqb_spec (cp_v g (Z.to_nat (26 + ir_s g))) 247) as [E8|E8]; cbn [negb]; cbv iota.
    2:{ eapply KV; [exact HK | exact EI | exact RAb |].
        apply rr_ir_false. intros Ht. apply ir_true in Ht. destruct Ht as (_ & _ & _ & _ & _ & _ & Ht & _).
        exact (E8 Ht). }
    clear RD8 RO.
    (* 0x84b54 .. 0x84b60: a1 = 0, a2 = 32, a3 = a0 = fr + 18; then the block sum loop *)
    step. step. step. step.
    match goal with |- context [zxb ?b] => change (zxb b) with (Z_to_bv 64 (ir_s g)) end.
    pose proof (rc_bytes_skip rsegs mc fr g 18 HBg ltac:(rewrite Hg; lia)) as HBk.
    change (skipn 18 g) with (ir_blk g) in HBk. change (Z.of_nat 18) with 18 in HBk.
    eapply rloopB0.
    - exact Hfr0.
    - exact Hf50.
    - unfold ir_blk. rewrite length_skipn, Hg. reflexivity.
    - exact HBk.
    - apply (rt_shadow_rd mc (fr + 18) 32 []).
      + exact (rr_addr_sub mc fr 50 (fr + 18) 32 AFg ltac:(lia) ltac:(lia) ltac:(lia)).
      + intros x _. exact I.
    - apply rt_addressable. exact (rr_addr_sub mc fr 50 (fr + 18) 32 AFg ltac:(lia) ltac:(lia) ltac:(lia)).
    - (* the 32 block bytes *) eapply rng_sub; [exact RGFR | lia | lia].
    - (* their shadow bytes *) intros x Hx. exact (SCFR x ltac:(lia)).
    - (* 0x84ba0 .. 0x84ba4: the block sum is 0 mod 256 *)
      intros a0' a2' a3' a4' a5'.
      remember (psum (ir_blk g) 32) as ps eqn:Eps.
      assert (PB : 0 <= ps <= 255 * 32)
        by (subst ps; pose proof (psum_range (ir_blk g) 32) as PB; change (Z.of_nat 32) with 32 in PB; exact PB).
      step. step.
      rewrite (rc_zb0 ps) by lia.
      replace (ps mod 256) with (blocksum (ir_blk g)) by (unfold blocksum; rewrite Eps; reflexivity).
      destruct (Z.eqb_spec (blocksum (ir_blk g)) 0) as [B5|B5]; cbn [negb]; cbv iota.
      2:{ eapply KV; [exact HK | exact EI | exact RAb |].
          apply rr_ir_false. intros Ht. apply ir_true in Ht.
          destruct Ht as (_ & _ & _ & _ & _ & _ & _ & Ht & _). exact (B5 Ht). }
      clear Eps PB.
      (* 0x84ba8 .. 0x84bbc: the record sum, by the call of reac_ctrl_record_cksum_verify *)
      pose proof (rc_bytes_skip rsegs mc fr g 34 HBg ltac:(rewrite Hg; lia)) as HBr.
      apply (rc_bytes_first rsegs mc _ _ (Z.to_nat (ir_s g - 8))) in HBr. change (Z.of_nat 34) with 34 in HBr.
      change (firstn (Z.to_nat (ir_s g - 8)) (skipn 34 g)) with (ir_rec g) in HBr.
      eapply rloopR with (lo := S - 9072).
      + exact Hfr0.
      + exact Hf50.
      + exact SR.
      + exact (rc_len_rec g Hg SR).
      + exact HBr.
      + exact (rr_addr_sub mc fr 50 (fr + 34) (ir_s g - 8) AFg ltac:(lia) ltac:(lia) ltac:(lia)).
      + clear - Cw1 Cw2 HS HSK; lia.
      + exact (proj1 (stk_split rsegs mc (S - 9072) spc S STKc ltac:(lia))).
      + clear - Cw1; lia.
      + destruct Hwf as [Hwf|Hwf]; [left | right]; clear - Hwf Cw1 Cw2 SR; lia.
      + exact ACc.
      + intros x Hx. cbn [outside]. split; [|exact I]. intros Hin.
        destruct Hx as [Hx|[Hx|Hx]].
        * unfold GOT_CELL_K in Hx. clear - Hx Hin Cw1 HHM'; lia.
        * unfold CELL_K in Hx. clear - Hx Hin Cw1 HHM'; lia.
        * apply (rr_app_not_shadow x); [| exact Hx].
          unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right. clear - Hin Cw1 Cw2 HHM' HAE'; lia.
      + (* the image *) exact RIMG.
      + (* the callee's frame [spc - 16, spc) *) eapply rng_sub; [exact RWIN | clear - Cw1 Cw2; lia | clear - Cw1 Cw2; lia].
      + (* the record bytes *) eapply rng_sub; [exact RGFR | clear - SR; lia | clear - SR; lia].
      + (* the byte-exact shadow span of each sub-range of them *)
        intros a b Ha Hab Hb. exact (shkov_exact RNG fr 50 a b SKFR ltac:(lia) Hab ltac:(lia)).
      + (* 0x84bbc: beqz a0 (a0 = 0: the record sum is 0 mod 128; else -1) *)
        intros c0 c1 c2 c3 c4 c5 c6 c7 m' MUc WMc' MIf STp.
        pose proof (rr_JB_ck G fv spc j nn mc m' HK RAb RJB MUc WMc' (MIf MIc) STp) as RJB0.
        pose proof (conj RJB0 (munch_trans _ m mc m' MUw (munch_weaken _ _ mc m'
                      (rWSC_win G j (spc - 16) spc ltac:(clear - Cw1; lia) ltac:(clear - Cw2; lia)) MUc)))
          as RJB'.
        destruct (Z.eqb_spec (recsum (ir_rec g)) 0) as [B6|B6]; cbv iota.
        2:{ step. rewrite rr_eqb_m1. cbv iota.
            eapply KV; [exact HK | exact (conj (rJB_EI0 G j nn m' RJB0) (proj2 RJB')) | exact RAb |].
            apply rr_ir_false. intros Ht. apply ir_true in Ht.
            destruct Ht as (_ & _ & _ & _ & _ & _ & _ & _ & Ht). exact (B6 Ht). }
        step. rewrite (rc_beq0_true 0 eq_refl). cbv iota.
        assert (EIR : ir len g = true).
        { unfold ir. rewrite K5, T, E32, E33, E27, E8, B5, B6.
          rewrite (proj2 (Z.leb_le 14 (ir_s g)) ltac:(lia)), (proj2 (Z.leb_le (ir_s g) 23) ltac:(lia)).
          reflexivity. }
        assert (OKr : reply_ok fr len pa pp pn g = true) by (unfold reply_ok; rewrite RAb, EIR; reflexivity).
        eapply KS; [exact HK | exact RJB' | exact OKr].
  Qed.

  (* The W-fine stretch C: from the continuation at reac_ctrl_parse's return 0x84a68 to the post rQSC G j, which
     carries munch (rWSC G j) m m'.  The chain of rp_main after rp_parse (accepted :4784-4786), on the copies. *)
  Lemma rp_CSC : rKFSC rQSC.
  Proof.
    apply rp_tagSC.
    - apply rp_failSC. apply rp_f8SC. exact rp_epiSC.
    - apply rp_storesSC. apply rp_f8SC. exact rp_epiSC.
  Qed.
End Rep.

End Callees.
