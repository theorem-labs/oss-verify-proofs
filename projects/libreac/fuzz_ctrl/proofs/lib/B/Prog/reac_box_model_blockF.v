(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 722 of its 760 lines of code are new or changed and 210 lines of the source are left out. *)
(* The footprint twin of reac_box_model_block.v (image B, asan-ubsan; RECIPE.md step 1, route 2 (a working note, not in this delivery)): the
   same runs as ExecF.evtF under a footprint RNG, by the scripts of the plain files over StepF's step.  This file is
   the twin of lib/B/Prog/reac_box_model_block.v and the prelude the other F files of this function share: the
   footprint forms of the six callees (__asan_stack_malloc_0, __asan_memset, __asan_memcpy, build_dt1_single,
   dt1_head, name_field), the quantified shadow covers the run draws from the statement's rng premises, the evtF
   twins of the plain file's step tactics, and Section MainF (KBF, fwordsF, entryF, td_tailF, epi0F).  Every
   definition and every pure lemma of reac_box_model_block.v is reused from there: this file only restates what
   mentions `evt`.

   Callee footprint forms: __asan_memcpy and __asan_memset from their owner's files asan_memcpy_cF.v /
   asan_memset_cF.v (a working branch 71a8e88cc7e, merged into this branch); name_field from
   name_field_c.v (a working branch 40a1a45d985, merged); dt1_head from dt1_head_c.v and
   build_dt1_single from build_dt1_single_c.v (a working branch 6939dc6611d, taken by
   path with its build_dt1_singleF.v; build_dt1_single_c.v's form is still a working branch text, one more
   change pending from its owner); __asan_stack_malloc's is kept once below, marked.  __asan_memcpy's and
   __asan_memset's forms carry RngBytes.rng_bytes, so reac_box_model_block_contract_F does. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcParseLib RcKindLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c dt1_head_c name_field_c reac_box_model_block_c
  reac_box_model_block.
(* The owners' footprint forms of __asan_memcpy / __asan_memset (a Theorem Labs lane 9869f1d1f86, with IMG_LO / IMG_HI of
   its ImgBounds.v); name_field's (a Theorem Labs lane dbe8f2b8dec) is in name_field_c above. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Export asan_memcpy_cF asan_memset_cF.
(* Last: StepF's step / if_false / mem_after_store (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require RngBytes.
Import ListNotations.
Open Scope Z_scope.

(* Local copy of reac_box_model_block.v:215's store hook: that file made it Local (a Theorem Labs lane, approved by a Theorem Labs lane, 2026-10-30). *)
Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | RMo : rd_mono ?mq m |- _ => apply (rd_mono_write mq m (wa a) bs) in RMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The store hook of this file: Tac.v's mem_after_store_opt (the hook the plain files run under) on evtF goals.  It
   folds Z_to_le_bytes of a literal into le8 / le4 / le2 / le1 as Tac's fix_lit_store does, and it does not run
   StepF's norm_lit_store_bytes, whose le1 (Z_to_bv 64 z) -> [Z_to_bv 8 z] folding would leave nothing for the
   scripts' own `rewrite rc_le1_*`. *)
Ltac mbF_fix_lit_store :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | _ => idtac
  end.

Ltac mbF_store_opt :=
  try mbF_fix_lit_store;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= mbF_store_opt.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The one callee footprint form that has no published owner text yet, kept ONCE here, as the one text the Section
   hypotheses of this proof name (to be replaced by a Require of its owner's file when it lands):
   - asan_stack_malloc_contract_F (with fs_shadow_area): LOCAL COPY, OWNER PENDING (fake-stack owners a Theorem Labs lane /
     a Theorem Labs lane publish only the cgif-world astack_malloc_realizes); text (from a working branch d0b3606c9c9) of
     lib/B/Prog/reac_ctrl_parseF.v (at head lib/B/Prog/reac_ctrl_parseF.v:53) (a Theorem Labs lane's narrow form, itself a local copy there), instantiated at class 0
     below.  A result that rests on it is conditional (F6). *)
Definition fs_shadow_area (c : nat) : Z := fs_M c * fs_B c / 8.
Definition asan_stack_malloc_contract_F (c : nat) (entry K : Z) : Prop :=
  (c <= 10)%nat ->
  forall (RNG : footprint) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo FS : Z) (h DT TS C T DB : word) (k : Z) (flags : list byte),
  let L := bv_unsigned a0 in let TP := bv_unsigned tp in let S0 := bv_unsigned sp in
  1 <= L <= fs_B c -> L mod 8 = 0 ->
  asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
  asan_tls_cells m TP DT TS C T DB k ->
  ((7 <= c)%nat -> bytes_at rsegs m (CF + 120) (le8 (Z_to_bv 64 (2 ^ 64 - 1)))) ->
  bytes_at rsegs m TP (le8 (Z_to_bv 64 FS)) -> fs_place m FS ->
  bytes_at rsegs m (FS + 88) (le8 (Z_to_bv 64 20)) -> bytes_at rsegs m (FS + 96) [Z_to_bv 8 0] ->
  bytes_at rsegs m (fs_hint FS c) (le8 h) ->
  bytes_at rsegs m (fs_flag FS c 0) flags -> Z.of_nat (length flags) = fs_M c ->
  Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags ->
  stk rsegs m lo S0 -> lo + K <= S0 -> FS + FS_SIZE <= S0 - K -> (forall a, S0 - K <= a < S0 -> app_mem a) ->
  disjoint_from [(TP - 88, TP - 80); (TP - 8, TP + 16); (bv_unsigned DT + 8, bv_unsigned DT + 16);
                 (bv_unsigned TS + 8 * k, bv_unsigned TS + 8 * k + 8); (bv_unsigned C + 152, bv_unsigned C + 160);
                 (bv_unsigned T + 48, bv_unsigned T + 64); (bv_unsigned DB + 24, bv_unsigned DB + 32)] (S0 - K) K ->
  rng RNG IMG_LO (IMG_HI - IMG_LO) ->
  rng RNG (S0 - K) K ->
  rng RNG (bv_unsigned DT + 8) 8 -> rng RNG (bv_unsigned TS + 8 * k) 8 -> rng RNG (bv_unsigned C + 152) 8 ->
  rng RNG (bv_unsigned T + 48) 16 -> rng RNG (bv_unsigned DB + 24) 8 ->
  rng RNG FS (fs_frame FS 0 0 - FS) -> rng RNG (fs_frame FS c 0) (2 ^ 20) ->
  rng RNG (shadow_addr (fs_frame FS c 0)) (fs_shadow_area c) ->
  rng RNG (TP - 88) 8 -> rng RNG (TP - 8) 24 ->
  evtF rsegs RNG (asan_stack_malloc_post c K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L FS h flags lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 entry) fc None m (seg_rom rsegs)).
Definition asan_stack_malloc_0_contract_F : Prop :=
  asan_stack_malloc_contract_F 0 ASAN_STACK_MALLOC_0 ASAN_STACK_MALLOC_K.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The shadow facts the run draws from the statement's shadow premises.  Z.div is opaque to lia and a GROUND rng
   premise whose bounds hold a division puts Euclidean variables into every later lia call, so each consequence is
   drawn once here and carried QUANTIFIED: the shadow byte of one checked byte (shcov), the eight shadow bytes of
   one 64-byte frame (shblk), the byte-exact shadow span of a sub-range (shspan, the shape dt1_head's and
   name_field's _F contracts name) and the 8-aligned shadow word cover of a sub-range (shkov, the shape
   __asan_memset's and __asan_memcpy's name). *)
Definition shcov (RG : footprint) (p n : Z) : Prop :=
  forall x, p <= x < p + n -> rng RG (x / 8 + ASAN_K) 1.
Definition shblk (RG : footprint) (q : Z) : Prop :=
  forall i, 0 <= i < 8 -> rng RG (q + i) 1.
Definition shspan (RG : footprint) (p n : Z) : Prop :=
  forall a b, p <= a -> a <= b -> b < p + n -> rng RG (a / 8 + ASAN_K) (b / 8 - a / 8 + 1).
Definition shkov (RG : footprint) (p n : Z) : Prop :=
  forall a b, p <= a -> a <= b -> b < p + n ->
    rng RG ((a / 8 + ASAN_K) / 8 * 8) ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8).

Lemma shcov_sub : forall RG p n p' n', shcov RG p n -> p <= p' -> p' + n' <= p + n -> shcov RG p' n'.
Proof. intros RG p n p' n' H H1 H2 x Hx. apply H. lia. Qed.
Lemma shspan_sub : forall RG p n p' n', shspan RG p n -> p <= p' -> p' + n' <= p + n -> shspan RG p' n'.
Proof. intros RG p n p' n' H H1 H2 a b H3 H4 H5. apply H; lia. Qed.
Lemma shkov_sub : forall RG p n p' n', shkov RG p n -> p <= p' -> p' + n' <= p + n -> shkov RG p' n'.
Proof. intros RG p n p' n' H H1 H2 a b H3 H4 H5. apply H; lia. Qed.

Lemma mbF_floor8 : forall y, y / 8 * 8 <= y <= y / 8 * 8 + 7.
Proof. intros y. pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)). lia. Qed.

(* The statement's 8-aligned shadow word cover of [p, p + n) gives the shadow byte of each of its bytes, the
   byte-exact span of each of its sub-ranges and the aligned cover of each of its sub-ranges. *)
Lemma mbF_cov : forall RG p n, 0 < n -> sh_cover RG p n -> shcov RG p n.
Proof.
  intros RG p n Hn H x Hx. unfold sh_cover, shadow_addr in H.
  eapply rng_sub; [exact H | |].
  - pose proof (Z.div_le_mono p x 8 ltac:(lia) ltac:(lia)). pose proof (mbF_floor8 (p / 8 + ASAN_K)). lia.
  - pose proof (Z.div_le_mono x (p + n - 1) 8 ltac:(lia) ltac:(lia)).
    pose proof (mbF_floor8 ((p + n - 1) / 8 + ASAN_K)). lia.
Qed.

Lemma mbF_span : forall RG p n, 0 < n -> sh_cover RG p n -> shspan RG p n.
Proof.
  intros RG p n Hn H a b H1 H2 H3. unfold sh_cover, shadow_addr in H.
  eapply rng_sub; [exact H | |].
  - pose proof (Z.div_le_mono p a 8 ltac:(lia) ltac:(lia)). pose proof (mbF_floor8 (p / 8 + ASAN_K)). lia.
  - pose proof (Z.div_le_mono b (p + n - 1) 8 ltac:(lia) ltac:(lia)).
    pose proof (mbF_floor8 ((p + n - 1) / 8 + ASAN_K)). lia.
Qed.

Lemma mbF_kov : forall RG p n, 0 < n -> sh_cover RG p n -> shkov RG p n.
Proof.
  intros RG p n Hn H a b H1 H2 H3. unfold sh_cover, shadow_addr in H.
  eapply rng_sub; [exact H | |].
  - pose proof (Z.div_le_mono p a 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (p / 8 + ASAN_K) (a / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.div_le_mono b (p + n - 1) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (b / 8 + ASAN_K) ((p + n - 1) / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)). lia.
Qed.

(* The eight shadow bytes of a 64-byte frame inside a covered region. *)
Lemma mbF_blk : forall RG p n fr, shcov RG p n -> fr mod 8 = 0 -> p <= fr -> fr + 64 <= p + n ->
  shblk RG (fr / 8 + ASAN_K).
Proof.
  intros RG p n fr H Hm H1 H2 i Hi.
  replace (fr / 8 + ASAN_K + i) with ((fr + 8 * i) / 8 + ASAN_K) by (Z.div_mod_to_equations; lia).
  apply H. lia.
Qed.

(* The class-0 frames' shadow comes as the BYTE-exact span [shadow_addr F0, shadow_addr F1) of fp_w; both ends are
   the shadow byte of a 64-aligned address, so that span is a whole number of aligned shadow words and it gives the
   same three consequences. *)
Lemma mbF_div8 : forall z, (8 * z) / 8 = z.
Proof. intros z. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. Qed.

Lemma mbF_span_cov : forall RG a b, a mod 8 = 0 -> b mod 8 = 0 ->
  rng RG (shadow_addr a) (shadow_addr b - shadow_addr a) -> shcov RG a (b - a).
Proof.
  intros RG a b Ha Hb H x Hx. unfold shadow_addr in H.
  eapply rng_sub; [exact H | |]; Z.div_mod_to_equations; lia.
Qed.

Lemma mbF_span_span : forall RG a b, a mod 8 = 0 -> b mod 8 = 0 ->
  rng RG (shadow_addr a) (shadow_addr b - shadow_addr a) -> shspan RG a (b - a).
Proof.
  intros RG a b Ha Hb H u v H1 H2 H3. unfold shadow_addr in H.
  eapply rng_sub; [exact H | |]; Z.div_mod_to_equations; lia.
Qed.

Lemma mbF_span_kov : forall RG p0 p1,
  rng RG (8 * p0 + ASAN_K) (8 * p1 + ASAN_K - (8 * p0 + ASAN_K)) -> shkov RG (64 * p0) (64 * p1 - 64 * p0).
Proof.
  intros RG p0 p1 H a b H1 H2 H3.
  assert (KA : ASAN_K = 8 * 268431360) by reflexivity.
  assert (L1 : 8 * p0 <= a / 8).
  { pose proof (Z.div_le_mono (8 * (8 * p0)) a 8 ltac:(lia) ltac:(lia)) as D. rewrite mbF_div8 in D. lia. }
  assert (L2 : b / 8 <= 8 * p1 - 1).
  { pose proof (Z.div_le_mono b ((8 * p1 - 1) * 8 + 7) 8 ltac:(lia) ltac:(lia)) as D.
    rewrite Z.div_add_l in D by lia. rewrite (Z.div_small 7 8 ltac:(lia)) in D. lia. }
  assert (M1 : p0 + 268431360 <= (a / 8 + ASAN_K) / 8).
  { pose proof (Z.div_le_mono (8 * (p0 + 268431360)) (a / 8 + ASAN_K) 8 ltac:(lia) ltac:(lia)) as D.
    rewrite mbF_div8 in D. lia. }
  assert (M2 : (b / 8 + ASAN_K) / 8 <= p1 + 268431360 - 1).
  { pose proof (Z.div_le_mono (b / 8 + ASAN_K) ((p1 + 268431360 - 1) * 8 + 7) 8 ltac:(lia) ltac:(lia)) as D.
    rewrite Z.div_add_l in D by lia. rewrite (Z.div_small 7 8 ltac:(lia)) in D. lia. }
  eapply rng_sub; [exact H | lia | lia].
Qed.

(* The same three consequences when the range may be empty (a name of length 0): a cover of no byte is vacuous. *)
Lemma mbF_cov0 : forall RG p n, sh_cover RG p n -> shcov RG p n.
Proof.
  intros RG p n H x Hx. destruct (Z_lt_le_dec 0 n) as [Hn|Hn]; [exact (mbF_cov RG p n Hn H x Hx) | lia].
Qed.
Lemma mbF_span0 : forall RG p n, sh_cover RG p n -> shspan RG p n.
Proof.
  intros RG p n H a b H1 H2 H3. destruct (Z_lt_le_dec 0 n) as [Hn|Hn];
    [exact (mbF_span RG p n Hn H a b H1 H2 H3) | lia].
Qed.
Lemma mbF_kov0 : forall RG p n, sh_cover RG p n -> shkov RG p n.
Proof.
  intros RG p n H a b H1 H2 H3. destruct (Z_lt_le_dec 0 n) as [Hn|Hn];
    [exact (mbF_kov RG p n Hn H a b H1 H2 H3) | lia].
Qed.

(* The 8-aligned shadow word cover in the form __asan_memcpy's (mbF_shw) and __asan_memset's (mbF_shws) footprint
   forms name (sh_word_rng of rng_asan.v, its one home since a Theorem Labs lane 78b8d116a58, with its N = 0 guard), for a range
   inside a region with a shkov. *)
Lemma mbF_shw : forall RG p n q k, shkov RG p n -> 0 <= k -> p <= q -> q + k <= p + n ->
  rng_asan.sh_word_rng RG q k.
Proof.
  intros RG p n q k H Hk H1 H2. destruct (Z.eq_dec k 0) as [E|E]; [left; exact E | right].
  unfold rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, shadow_addr. apply (H q (q + k - 1)); lia.
Qed.
Lemma mbF_shws : forall RG p n q k, shkov RG p n -> 0 <= k -> p <= q -> q + k <= p + n ->
  rng_asan.sh_word_rng RG q k.
Proof.
  intros RG p n q k H Hk H1 H2. destruct (Z.eq_dec k 0) as [E|E]; [left; exact E | right].
  unfold rng_asan.sh_al8_lo, rng_asan.sh_al8_hi, shadow_addr. apply (H q (q + k - 1)); lia.
Qed.

(* The seven rng facts __asan_stack_malloc's footprint form asks of the thread cells, out of the statement's one
   Forall over fp_tls at the witnesses of m. *)
Lemma mbF_tls_rng : forall RG (m : word -> option byte) TP DT TS C T DB k,
  (forall DT' TS' C' T' DB' k', asan_tls_cells m TP DT' TS' C' T' DB' k' ->
     Forall (fun iv => rng RG (fst iv) (snd iv - fst iv)) (fp_tls TP DT' TS' C' T' DB' k')) ->
  asan_tls_cells m TP DT TS C T DB k ->
  rng RG (TP - 88) 8 /\ rng RG (TP - 8) 24 /\ rng RG (bv_unsigned DT + 8) 8 /\
  rng RG (bv_unsigned TS + 8 * k) 8 /\ rng RG (bv_unsigned C + 152) 8 /\
  rng RG (bv_unsigned T + 48) 16 /\ rng RG (bv_unsigned DB + 24) 8.
Proof.
  intros RG m TP DT TS C T DB k H HT. pose proof (H DT TS C T DB k HT) as HF.
  cbn [fp_tls] in HF.
  repeat (let Hx := fresh "Hx" in apply Forall_cons_iff in HF; destruct HF as [Hx HF];
          cbv beta in Hx; cbn [fst snd] in Hx).
  split; [|split; [|split; [|split; [|split; [|split]]]]];
    match goal with
    | H : rng RG _ _ |- rng RG _ _ => eapply rng_sub; [exact H | lia | lia]
    end.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The whole footprint of a run of this function, as the Section hypothesis every file of the proof carries: the
   regions of reac_box_model_block_contract_F with the shadow consequences already drawn, each under the guard its
   data premise carries.  reac_box_model_block_holdsF.v builds it from the statement's premises; `mbF_open H`
   unpacks it into the named facts the step tactics search for. *)
Definition mbF_rng (RNG : footprint) (m : word -> option byte) (sp tp : word) (p b o FS : Z)
    (row nb : list byte) : Prop :=
  (* the image: the code, the jump table at 0x219f4, the two JOIN blocks, the GOT and [RT_LO, RT_HI) *)
  rng RNG 0x10000 0x5ee000
  (* the function's own window and its shadow *)
  /\ rng RNG (bv_unsigned sp - 4272) 4272
  /\ shcov RNG (bv_unsigned sp - 4272) 4272
  /\ shspan RNG (bv_unsigned sp - 4272) 4272
  /\ shkov RNG (bv_unsigned sp - 4272) 4272
  (* the side stack: the header [FS, fs_frame FS 0 0) (hint words, flag bytes) and the class-0 frames *)
  /\ rng RNG FS 36864
  /\ rng RNG (FS + 36864) 1048576
  /\ shcov RNG (FS + 36864) 1048576
  /\ shspan RNG (FS + 36864) 1048576
  /\ shkov RNG (FS + 36864) 1048576
  (* the cells asan_tls_cells names, at the witnesses of m *)
  /\ (forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
        Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k))
  (* the row, the output block, the JOIN block b selects and the name *)
  /\ (p <> 0 -> rng RNG (p + 16) 275 /\ shcov RNG (p + 16) 275 /\ shspan RNG (p + 16) 275
                /\ shkov RNG (p + 16) 275)
  /\ (p <> 0 -> o <> 0 -> rng RNG o 32 /\ shcov RNG o 32 /\ shspan RNG o 32 /\ shkov RNG o 32)
  /\ (b = 1 -> shcov RNG JOIN_0014 32 /\ shspan RNG JOIN_0014 32 /\ shkov RNG JOIN_0014 32)
  /\ (b = 2 -> shcov RNG JOIN_0013 32 /\ shspan RNG JOIN_0013 32 /\ shkov RNG JOIN_0013 32)
  /\ (p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
        rng RNG (rname row) (Z.of_nat (length nb)) /\ shcov RNG (rname row) (Z.of_nat (length nb))
        /\ shspan RNG (rname row) (Z.of_nat (length nb)) /\ shkov RNG (rname row) (Z.of_nat (length nb)))
  (* the footprint is byte-wise (the premise __asan_memcpy's and __asan_memset's forms take) *)
  /\ RngBytes.rng_bytes RNG.

(* RIMG image, RWIN/SWIN/PWIN/KWIN window (range, shadow byte, shadow span, aligned cover), RHDR side-stack header,
   RFR/SFR/PFR/KFR class-0 frames, RTLS thread cells, RROW row, ROUT output block, RJ4/RJ3 JOIN, RNM name, RBY the
   byte-wise footprint. *)
Ltac mbF_open H :=
  let RIMG := fresh "RIMG" in let RWIN := fresh "RWIN" in let SWIN := fresh "SWIN" in
  let PWIN := fresh "PWIN" in let KWIN := fresh "KWIN" in let RHDR := fresh "RHDR" in
  let RFR := fresh "RFR" in let SFR := fresh "SFR" in let PFR := fresh "PFR" in let KFR := fresh "KFR" in
  let RTLS := fresh "RTLS" in let RROW := fresh "RROW" in let ROUT := fresh "ROUT" in
  let RJ4 := fresh "RJ4" in let RJ3 := fresh "RJ3" in let RNM := fresh "RNM" in let RBY := fresh "RBY" in
  destruct H as (RIMG & RWIN & SWIN & PWIN & KWIN & RHDR & RFR & SFR & PFR & KFR & RTLS
                 & RROW & ROUT & RJ4 & RJ3 & RNM & RBY).

(* ------------------------------------------------------------------------------------------------------------ *)
(* A shadow access: its address holds a division, which StepF's [alia] does not reason about, so it goes through
   StepF's acc_hint hook and closes from one of the quantified covers above (the offset the run carries in s3 is
   `off`, with Hoff : off = ASAN_K in every Section). *)
Ltac mbF_has_div E := lazymatch E with context [Z.div _ _] => idtac end.

Ltac mbF_rng1 :=
  lazymatch goal with
  | |- rng ?RG ?E ?L =>
      first
        [ match goal with H : shblk RG ?q |- _ =>
            replace E with (q + (E - q)) by lia; apply H; lia end
        | match goal with H : shcov RG _ _ |- _ =>
            lazymatch E with
            | ?X / 8 + ASAN_K => apply (H X); lia
            | ?X / 8 + _ => replace E with (X / 8 + ASAN_K) by lia; apply (H X); lia
            end
          end
        | match goal with H : shcov RG _ _ |- _ =>
            lazymatch E with
            | ?X / 8 + ?c + ?d => replace E with ((X + 8 * d) / 8 + ASAN_K)
                                    by (clear -c d; Z.div_mod_to_equations; lia);
                                  apply (H (X + 8 * d)); lia
            end
          end ]
  end.

Ltac mbF_acc_hint :=
  lazymatch goal with
  | |- acc_in ?RG (wa ?E, ?nn) => change (acc_in RG (Z_to_bv 64 E, nn)); solve_acc1
  | |- acc_in ?RG (Z_to_bv 64 ?E, ?nn) =>
      tryif mbF_has_div E then
        (let nz := eval cbv in (Z.of_nat nn) in
         refine (rng_acc_litZ' RG E nz E nn nz _ (@eq_refl Z nz) (@eq_refl bool true)
                   (conj (Z.le_refl E) (Z.le_refl (E + nz))));
         mbF_rng1)
      else
        (tryif is_closed_lits E then fail else
           (let E' := eval vm_compute in E in
            is_Zlit E'; change (acc_in RG (Z_to_bv 64 E', nn)); solve_acc1))
  end.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= mbF_acc_hint.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The evtF twins of the step tactics of reac_box_model_block.v, under the same names (this file is imported after
   it, so these shadow the evt ones).  Each body is the plain one with `evt` replaced by `evtF`. *)
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
  | |- evtF ?segs ?rg ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs rg Q (MS (bvmap_set r rr R) F B fc rv mm ro));
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

Ltac nf := lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false; [cbv iota | symmetry; unfold_cond; fold_lit_ux; cond_unlit; solve_cond_rec]
  end.
Ltac nt := lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true; [cbv iota | symmetry; unfold_cond; fold_lit_ux; cond_unlit; solve_cond_rec]
  end.
Ltac bstep := step; nf.
Ltac nfc := lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with false by (vm_compute; reflexivity); cbv iota
  end.
Ltac bst := step; first [nf | nfc].

Ltac st0 := lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?x ?bs) _) =>
      is_var x;
      replace (write_to_mem mm x bs) with (write_to_mem mm (wa (bv_unsigned x + Z.of_nat 0)) bs)
        by (f_equal; symmetry; apply rc_wa_add0)
  end; mem_after_store_opt.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The thread cells again, when the witnesses come from a memory the run has already written in (the prologue
   writes only inside the window, so fl_tls_same identifies them with the witnesses of m). *)
Lemma mbF_tls_rng1 : forall RG (m m1 : word -> option byte) (sp tp : word) (p o FS : Z) (W' : list ivl)
    DT TS C T DB k,
  (forall DT' TS' C' T' DB' k', asan_tls_cells m (bv_unsigned tp) DT' TS' C' T' DB' k' ->
     Forall (fun iv => rng RG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT' TS' C' T' DB' k')) ->
  fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
     (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) ->
  munch W' m m1 -> sub_fp W' [(bv_unsigned sp - 4272, bv_unsigned sp)] ->
  asan_tls_cells m1 (bv_unsigned tp) DT TS C T DB k ->
  rng RG (bv_unsigned tp - 88) 8 /\ rng RG (bv_unsigned tp - 8) 24 /\ rng RG (bv_unsigned DT + 8) 8 /\
  rng RG (bv_unsigned TS + 8 * k) 8 /\ rng RG (bv_unsigned C + 152) 8 /\
  rng RG (bv_unsigned T + 48) 16 /\ rng RG (bv_unsigned DB + 24) 8.
Proof.
  intros RG m m1 sp tp p o FS W' DT TS C T DB k HR HFP MU HS HT1.
  pose proof HFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _).
  assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside W' x)
                 (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0)).
  { apply Forall_forall. intros [a bnd] Hin x Hx. apply HS.
    pose proof (fl_dj_out _ _ a bnd x HWd (in_or_app _ _ _ (or_introl Hin)) Hx) as Ho.
    unfold reac_box_model_block_W in Ho. cbn [outside] in Ho |- *.
    split; [exact (proj1 Ho) | exact I]. }
  destruct (fl_tls_same m m1 W' (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HT1 MU Hc)
    as (E1 & E2 & E3 & E4 & E5 & E6).
  subst DT0 TS0 C0 T0 DB0 k0.
  exact (mbF_tls_rng RG m (bv_unsigned tp) DT TS C T DB k HR HT0).
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The twin of Section Main of reac_box_model_block.v: the same variables and premises, the footprint form of
   __asan_stack_malloc_0 in place of its old contract, and the run's footprint as the one hypothesis HRNG.  Every
   definition and every pure lemma of Section Main is reused from there with explicit arguments. *)
Section MainF.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte) (RNG : footprint).
  Hypothesis HSM : asan_stack_malloc_0_contract_F.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw m.
  Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 4272.
  Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
  Hypothesis AW0 : addressable m (bv_unsigned sp - 4272) 4272.
  Hypothesis FP0 : fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
    (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o).
  Hypothesis TLS0 : reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp).
  Hypothesis HRNG : mbF_rng RNG m sp tp p b o FS row nb.

  (* The body's entry point, as an evtF: the twin of KB. *)
  Definition KBF (Q : machine_state -> Prop) : Prop :=
    forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
           (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      FK FS A fr f spc j n w56 ->
      BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n) fr w56 mc ->
      evtF rsegs RNG Q (MS (mkR (Z_to_bv 64 0x86648) (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 A)
                         a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) s5
                         (Z_to_bv 64 b) (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11
                         t3' t4' t5' t6') F (Z_to_bv 64 0x866d4) fc None mc (seg_rom rsegs)).

  Ltac bi_intro H :=
    let MU := fresh "MU" in let WM := fresh "WM" in let RM := fresh "RM" in let MI := fresh "MI" in
    let SV := fresh "SV" in let HH := fresh "HH" in let hh := fresh "h" in let F56 := fresh "F56" in
    destruct H as (MU & WM & RM & MI & SV & (hh & HH) & F56).

  Ltac wv_tac :=
    let ii := fresh "ii" in let Hii := fresh "Hii" in intros ii Hii;
    first [ match goal with
            | STW : forall a, bv_unsigned sp - 4272 <= a < bv_unsigned sp -> wview rsegs m (wa a) <> None |- _ =>
                apply STW; lia
            end
          | apply (STW0 sp m ST0); lia
          | match goal with
            | FW : forall i, 0 <= i < 64 -> wview rsegs m (wa (?fr + i)) <> None |- wview _ _ (wa ?x) <> None =>
                replace x with (fr + (x - fr)) by lia; apply FW; lia
            end
          | match goal with
            | SW : forall i, 0 <= i < 8 -> wview rsegs m (wa (?s + i)) <> None |- wview _ _ (wa ?x) <> None =>
                replace x with (s + (x - s)) by lia; apply SW; lia
            end ].

  Ltac wst a n :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) n = true)
          by (eapply wv_store_ok; [ wv_tac | eassumption | lia | lia ])
    end.

  (* +0xa0 .. +0x100: the frame record (fr at A+24), the three magic frame words and the frame's shadow. *)
  Lemma fwordsF : forall fr f spc j n w56 mc (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) Q,
    FK FS A fr f spc j n w56 -> BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n) fr w56 mc -> KBF Q ->
    evtF rsegs RNG Q (MS (mkR (Z_to_bv 64 0x86648) (Z_to_bv 64 spc) gp tp t0' t1' t2' sp (Z_to_bv 64 A)
                       a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) s5
                       (Z_to_bv 64 b) (Z_to_bv 64 fr) s8 (wa off) s10 s11
                       t3' t4' t5' t6') F (Z_to_bv 64 0x86678) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Q HK HB K.
    mbF_open HRNG.
    pose proof (HA1 sp A HA HS16) as (HA32 & HAlo & HAhi). pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    (* OPEN (a Theorem Labs lane, ctl_post_acall_kept): FW / SW, the class-0 frame's writability, come from the ENTRY facts
       across the malloc (WM3); the malloc post's own STF / HADD (mb_retF) may replace them. *)
    destruct (fk_facts sp tp m p o FS off A Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 fr f spc j n w56 HK)
      as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & HP & _ & _ & _ & HFS & _).
    pose proof HFS as HFS'. unfold FS_SIZE in HFS'. pose proof HP as (P1 & P2 & P3 & P4 & P5).
    unfold ASAN_GT in P3. unfold FS_SIZE in P4, P5.
    assert (FSA : FS + 8 <= 2147450880 \/ 17594333495296 <= FS).
    { pose proof (P4 FS ltac:(lia)) as A0. pose proof (P4 (FS + 7) ltac:(lia)) as A7.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in A0, A7. lia. }
    pose proof HB as HB'. bi_intro HB'. unfold Wf, shadow_addr in MU.
    assert (Hspc : 0 <= spc < 2 ^ 64) by lia.
    (* the eight shadow bytes of the frame: the frame is in the window (real stack) or in the class-0 frames *)
    assert (BLK : shblk RNG (fr / 8 + ASAN_K)).
    { pose proof HK as HK'.
      destruct HK' as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)].
      - apply (mbF_blk RNG (bv_unsigned sp - 4272) 4272 fr SWIN FR8); lia.
      - unfold fs_frame, fs_B in Efr. cbn [Z.of_nat] in Efr. change (fs_M 0%nat) with 16384 in Hj.
        apply (mbF_blk RNG (FS + 36864) 1048576 fr SFR FR8); lia. }
    (* the 64 bytes of the frame: in the window (real stack) or in the class-0 frames *)
    assert (RFRM : rng RNG fr 64).
    { pose proof HK as HK'.
      destruct HK' as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)].
      - eapply rng_sub; [exact RWIN | lia | lia].
      - unfold fs_frame, fs_B in Efr. cbn [Z.of_nat] in Efr. change (fs_M 0%nat) with 16384 in Hj.
        eapply rng_sub; [exact RFR | lia | lia]. }
    assert (HS1 : store_ok rsegs mc (wa (A + 24)) 8 = true)
      by (eapply wv_store_ok; [intros i Hi; apply (STW0 sp m ST0); lia | exact WM | lia | lia]).
    step. store_done.
    do 8 step.
    wst fr 8%nat. step. store_done.
    wst (fr + 8) 8%nat. step. store_done.
    wst (fr + 16) 8%nat. step. store_done.
    step. step.
    rewrite (unsigned_lit fr) by lia. rewrite rc_shr3.
    wst (fr / 8 + off + 4) 1%nat. step. store_done.
    wst (fr / 8 + off + 5) 1%nat. step. store_done.
    wst (fr / 8 + off + 6) 1%nat. step. store_done.
    wst (fr / 8 + off + 7) 1%nat. step. store_done.
    step.
    wst (fr / 8 + off) 1%nat. step. store_done.
    wst (fr / 8 + off + 1) 1%nat. step. store_done.
    wst (fr / 8 + off + 2) 1%nat. step. store_done.
    wst (fr / 8 + off + 3) 1%nat. step. store_done.
    eapply K; [exact HK|].
    split; [unfold Wf, shadow_addr; exact MU|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [assumption|]. split; [eexists; eassumption | assumption].
  Qed.

  (* ---- The cut at the class-0 request (a Theorem Labs lane 00:3xZ: the glue's stretch A, the event, stretch B) ---------
     entryF is cut at the call of __asan_stack_malloc_0 (jal 0x86644, ra 0x86648): mb_preF is the stretch from the
     entry to the callee's entry 0x3d6f4; mb_callF applies the runtime's footprint form there (HSM: F6-conditional,
     the glue replaces it by cgif's astack_malloc_realizes SEGS B 0); mb_retF is the stretch from the return to the
     body (KBF).  The scripts are entryF's, verbatim, split at the cut; mb_pre_facts is what entryF carried across
     it. *)
  Definition mb_pre_facts (m1 : word -> option byte) : Prop :=
    munch [(bv_unsigned sp - 4272, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ rd_mono m m1 /\ mem_inv rsegs m1 /\
    rw_cells rsegs m1 (bv_unsigned sp + -88)
      [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    stk rsegs m1 (bv_unsigned sp - 4272) (bv_unsigned sp - 160) /\
    stk rsegs m1 (bv_unsigned sp - 160) (bv_unsigned sp + -88).

  (* The state at the callee's entry 0x3d6f4: ra = 0x86648, sp = A, a0 = 64 (the request size), s0 = sp at entry,
     s1 = A, s3 = o, s4 = p, s6 = b, s9 = the shadow offset; a1 / a2 hold the values the prologue loaded. *)
  Definition mb_call_state (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : word -> option byte) : machine_state :=
    MS (mkR (Z_to_bv 64 0x86648) (Z_to_bv 64 A) gp tp t0 t1 t2 sp (Z_to_bv 64 A) (Z_to_bv 64 64) (wa 693944)
            (sx32 (wa 1)) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 o) (Z_to_bv 64 p) s5 (Z_to_bv 64 b) s7 s8 (wa off) s10 s11
            t3 t4 t5 t6)
       F (Z_to_bv 64 0x3d6f4) fc None m1 (seg_rom rsegs).

  (* Stretch A: 0x865d8 .. the jal at 0x86644 (entryF's script up to the call). *)
  Lemma mb_preF : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q (m0 : word -> option byte), m0 = m ->
    (forall m1, mb_pre_facts m1 -> evtF rsegs RNG Q (mb_call_state t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1)) ->
    evtF rsegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 b) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None m0 (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q m0 Em0 KC.
    mbF_open HRNG.
    pose proof FP0 as FPm. unfold reac_box_model_block_W in FPm. pose proof (STW0 sp m ST0) as STW.
    unfold REAC_BOX_MODEL_BLOCK.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (HA1 sp A HA HS16) as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (MU : munch [(bv_unsigned sp - 4272, bv_unsigned sp)] m m0) by (subst m0; apply munch_refl).
    assert (WM : wmono rsegs m m0) by (subst m0; apply wmono_refl).
    assert (RM : rd_mono m m0) by (subst m0; apply rd_mono_refl).
    assert (MI : mem_inv rsegs m0) by (subst m0; exact MI0).
    pose proof AC0 as (CK & GCK & _ & _ & _ & UA & GUA & _).
    unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
    rewrite <- Hoff in CK.
    apply bytes_ro8 in CK. apply bytes_ro8 in GCK. apply bytes_ro4 in UA. apply bytes_ro8 in GUA.
    rewrite <- Em0 in CK, GCK, UA, GUA.
    pose proof ST0 as ST0c. rewrite <- Em0 in ST0c.
    pose proof (stk_split rsegs m0 _ (bv_unsigned sp - 160) _ ST0c ltac:(lia)) as [STa STb].
    clear ST0c.
    carve_frame 88%nat STb.
    step.
    assert (HS0 : store_ok rsegs m0 (wa (bv_unsigned sp + -160)) 8 = true).
    { eapply wv_store_ok; [ | apply wmono_refl | lia | lia]. intros i Hi.
      apply (stk_wv m0 (bv_unsigned sp - 160) (bv_unsigned sp + -88)); [exact STb | lia]. }
    step. store_done.
    do 11 step.
    step. step.
    assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -160))) 18446744073709551584 = A)
      by (rewrite unsigned_lit, land_align32 by lia; rewrite HA; f_equal; f_equal; lia).
    rewrite EA.
    do 11 step.
    replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
    step. step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
    apply KC. exact (conj MU (conj WM (conj RM (conj MI (conj FR (conj STa STb)))))).
  Qed.

  (* Stretch B, its start: from the return 0x86648 (the post of the class-0 request) to the body (KBF): fwords and
     the frame shadow (entryF's script after the call). *)
  Lemma mb_retF : forall Q (m1 : word -> option byte) (h : word) (flags : list byte) (ms' : machine_state),
    KBF Q -> mb_pre_facts m1 ->
    asan_stack_malloc_post 0%nat ASAN_STACK_MALLOC_K (Z_to_bv 64 0x86648) (Z_to_bv 64 A) gp tp sp (Z_to_bv 64 A) s2
      (Z_to_bv 64 o) (Z_to_bv 64 p) s5 (Z_to_bv 64 b) s7 s8 (wa off) s10 s11 F fc (bv_unsigned (Z_to_bv 64 64)) FS
      h flags (bv_unsigned sp - 4272) m1 ms' ->
    evtF rsegs RNG Q ms'.
  Proof.
    intros Q m1 h flags ms' K (MU & WM & RM & MI & FR & STa & STb) PO.
    mbF_open HRNG.
    pose proof FP0 as FPm. unfold reac_box_model_block_W in FPm. pose proof (STW0 sp m ST0) as STW.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (HA1 sp A HA HS16) as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof (fl_fp [0%nat] m m1 _ FS _ _ _ _ _ FPm MU WM ltac:(intros x Hx; exact Hx)) as FP1.
    destruct FP1 as (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HAPP & HWd & HDd).
    pose proof HFS as HFS'. unfold FS_SIZE in HFS'.
    pose proof (stk_merge rsegs m1 _ _ _ STa STb ltac:(lia)) as STc.
    destruct (stk_split rsegs m1 _ A _ STc ltac:(lia)) as [STA _].
    destruct PO as (u0 & u1 & u2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & u3 & u4 & u5 & u6 & m2 & E & WM2 & MI2 & ST2
                    & HP2 & (h2 & HH2) & ALT).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 0x86648)) with (Z_to_bv 64 0x86648) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite (unsigned_lit A) in ST2 by lia. unfold ASAN_STACK_MALLOC_K in *.
    unfold fs_hint in HH2. cbn [Z.of_nat] in HH2. rewrite Z.add_0_r in HH2.
    pose proof FPm as (DT' & TS' & C' & T' & DB' & k' & _ & _ & HPm & _).
    pose proof HPm as (P1 & P2 & P3 & P4 & P5). unfold ASAN_GT in P3. unfold FS_SIZE in P4, P5.
    destruct ALT as [(Hall & Ex0 & MU2) | (i & Hi & Hpre & Hnth & FRM)].
    - (* the real-stack frame [A - 64, A) *)
      subst x0. rewrite (unsigned_lit A) in MU2 by lia. unfold fs_hint in MU2. cbn [Z.of_nat] in MU2.
      rewrite Z.add_0_r in MU2.
      assert (RM2 : rd_mono m1 m2).
      { apply (rd_mono_list _ _ _ MU2). constructor; [|constructor; [|constructor]]; cbn [fst snd].
        - intros y Hy. apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
        - intros y Hy. apply (rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch (Wf sp FS (A - 64) 0 0) m m2).
      { apply (munch_trans _ m m1 m2).
        - eapply munch_weaken; [|exact MU]. unfold sub_fp, Wf. cbn [outside]. intros. repeat split; try exact I; lia.
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp, Wf. cbn [outside]. intros. repeat split; try exact I; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize Nat.add SAVES];
        lia)) as FR2.
      destruct (rd8_le8 m2 (A - 8) ltac:(lia) ltac:(lia) ltac:(intros y Hy; apply (rd_of_stk _ _ _ ST2); lia))
        as (w56 & F56).
      clear MU MU2 WM WM2 RM RM2 FR STA STa STb STc MI.
      unfold Wf, shadow_addr in MU3.
      step. step. step. step.
      replace (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false by reflexivity. cbv iota.
      step. step.
      match goal with |- context [Z.land ?x 18446744073709551584] =>
        replace (Z.land x 18446744073709551584) with (A - 64)
          by (rewrite ?(unsigned_lit A), ?unsigned_lit by lia; rewrite land_align32 by lia;
              Z.div_mod_to_equations; lia) end.
      step. step.
      rewrite (unsigned_lit A) by lia.
      wst (A - 4096) 8%nat. step. store_done.
      step.
      rewrite (rc_lts_signed (A - 64) (A - 4096)) by lia.
      replace (A - 64 <? A - 4096) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
      step.
      eapply (fwordsF (A - 64) 0 (A - 64) 0 0 w56); [left; repeat split; lia | | exact K].
      split; [unfold Wf, shadow_addr; exact MU3|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [eexists; eassumption|].
      replace (A - 64 + 56) with (A - 8) by lia. assumption.
    - (* the side-stack frame fs_frame FS 0 jj *)
      unfold asan_stack_malloc_frame in FRM. cbv zeta in FRM.
      rewrite (unsigned_lit A), (unsigned_lit 64) in FRM by lia.
      replace (fs_B 0) with 64 in FRM by reflexivity.
      replace (fs_shadow_n 0 64) with 8 in FRM by reflexivity.
      destruct FRM as (Ex0 & Hm64 & _ & HFL & H24 & H56 & HSH & HADD & STF & APF & FSlo & FShi & GT & FRA' & DIS
                       & MU2).
      remember ((bv_unsigned h + i) mod fs_M 0) as jj eqn:Ejj.
      assert (Hjj : 0 <= jj < fs_M 0) by (subst jj; apply Z.mod_pos_bound; reflexivity).
      remember (fs_frame FS 0 jj) as fr eqn:Efr.
      subst x0. unfold fs_hint in MU2. cbn [Z.of_nat] in MU2. rewrite Z.add_0_r in MU2.
      unfold ASAN_GT in GT. unfold FS_SIZE in FShi.
      assert (EFl : fs_flag FS 0 jj = FS + 4096 + jj) by (unfold fs_flag; cbn; lia).
      assert (EM0 : fs_M 0 = 16384) by reflexivity.
      rewrite EM0 in Hjj.
      assert (SHb : shadow_addr fr + 8 <= bv_unsigned sp - 4272)
        by (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia).
      assert (RM2 : rd_mono m1 m2).
      { apply (rd_mono_list _ _ _ MU2).
        repeat constructor; cbn [fst snd]; intros y Hy.
        - apply (rd_of_bytes _ _ _ HH2). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ HFL). cbn. lia.
        - apply (rd_of_bytes _ _ _ H24). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ H56). rewrite length_le8. cbn. lia.
        - apply (rd_of_bytes _ _ _ HSH). rewrite repeat_length, Z2Nat.id by lia. lia.
        - apply (rd_of_stk _ _ _ ST2). lia. }
      assert (MU3 : munch (Wf sp FS fr jj 1) m m2).
      { apply (munch_trans _ m m1 m2).
        - eapply munch_weaken; [|exact MU]. unfold sub_fp, Wf. cbn [outside]. intros. repeat split; try exact I; lia.
        - eapply munch_weaken; [|exact MU2]. unfold sub_fp, Wf. cbn [outside]. intros. repeat split; try exact I; lia. }
      pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM3. pose proof (rd_mono_trans _ _ _ RM RM2) as RM3.
      pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU2 WM2 ltac:(rewrite EFl; cbn [disjoint_from cells_size csize Nat.add SAVES];
        lia)) as FR2.
      clear MU MU2 WM WM2 RM RM2 FR STA STa STb STc MI.
      step. step. step. step.
      rewrite (rc_neq0_64 fr) by lia. cbn [negb]. cbv iota.
      eapply (fwordsF fr fr A jj 1 (Z_to_bv 64 (fs_flag FS 0 jj))); [right; repeat split; lia | | exact K].
      split; [exact MU3|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [eexists; eassumption|].
      replace (fr + 56) with (fr + 64 - 8) by lia. assumption.
  Qed.

  (* The call: the runtime's footprint form at the callee's entry, then stretch B. *)
  Lemma mb_callF : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q (m1 : word -> option byte),
    KBF Q -> mb_pre_facts m1 -> evtF rsegs RNG Q (mb_call_state t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q m1 K PF.
    pose proof PF as (MU & WM & RM & MI & FR & STa & STb).
    mbF_open HRNG.
    pose proof FP0 as FPm. unfold reac_box_model_block_W in FPm. pose proof (STW0 sp m ST0) as STW.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    pose proof (HA1 sp A HA HS16) as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    unfold mb_call_state.
    (* the side-stack state at m1 *)
    pose proof (fl_fp [0%nat] m m1 _ FS _ _ _ _ _ FPm MU WM ltac:(intros x Hx; exact Hx)) as FP1.
    destruct FP1 as (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HAPP & HWd & HDd).
    pose proof HCL as HCL0. apply Forall_cons_iff in HCL0. destruct HCL0 as [(_ & h & flags & HH & HF & HFl & HFb) _].
    pose proof HWd as Hw0. unfold fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
    cbn [fp_tls app] in Hw0.
    repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
    pose proof HFS as HFS'. unfold FS_SIZE in HFS'.
    pose proof (stk_merge rsegs m1 _ _ _ STa STb ltac:(lia)) as STc.
    destruct (stk_split rsegs m1 _ A _ STc ltac:(lia)) as [STA _].
    pose proof HP as (Q1 & Q2 & Q3 & Q4 & Q5).
    destruct (mbF_tls_rng1 RNG m m1 sp tp p o FS [(bv_unsigned sp - 4272, bv_unsigned sp)] DT TS C T DB k
                RTLS FP0 MU ltac:(intros x Hx; exact Hx) HT) as (R88 & R8 & RDT & RTS & RC & RT48 & RDB).
    pose proof HSM as HM. unfold asan_stack_malloc_0_contract_F, asan_stack_malloc_contract_F in HM.
    cbv zeta in HM. specialize (HM (Nat.le_0_l 10)).
    eapply evtF_cut.
    { eapply HM with (lo := bv_unsigned sp - 4272) (FS := FS) (h := h) (DT := DT) (TS := TS) (C := C) (T := T)
        (DB := DB) (k := k) (flags := flags); unfold ASAN_STACK_MALLOC_K; rewrite ?(unsigned_lit A) by lia.
      - rewrite unsigned_lit by lia. unfold fs_B. cbn. lia.
      - rewrite unsigned_lit by lia. reflexivity.
      - exact (fl_asan_cells _ m m1 AC0 MU ltac:(intros x Hx; cbn [outside]; unfold RT_LO, RT_HI in Hx; split; [lia | exact I])).
      - exact (shadow_rw_mono m m1 SR0 WM RM).
      - exact MI.
      - exact HT.
      - intros Hc. lia.
      - exact HTP.
      - exact HP.
      - exact H88.
      - exact H96.
      - exact HH.
      - exact HF.
      - exact HFl.
      - exact HFb.
      - exact STA.
      - lia.
      - lia.
      - intros a Ha. apply HAPP. lia.
      - cbn [disjoint_from].
        repeat split; try exact I;
          match goal with |- _ + _ <= ?lo \/ ?hi <= _ =>
            match goal with Hd : ly_dj _ _ lo hi |- _ => unfold ly_dj in Hd; lia end end.
      - (* the image *) eapply rng_sub; [exact RIMG | unfold IMG_LO, IMG_HI; lia | unfold IMG_LO, IMG_HI; lia].
      - (* the window of the call *) eapply rng_sub; [exact RWIN | lia | lia].
      - exact RDT.
      - exact RTS.
      - exact RC.
      - exact RT48.
      - exact RDB.
      - (* the side stack's header *)
        eapply rng_sub; [exact RHDR | unfold fs_frame, fs_B; cbn [Z.of_nat]; lia
                        | unfold fs_frame, fs_B; cbn [Z.of_nat]; lia].
      - (* the class-0 frames *)
        eapply rng_sub; [exact RFR | unfold fs_frame, fs_B; cbn [Z.of_nat]; lia
                        | unfold fs_frame, fs_B; cbn [Z.of_nat]; lia].
      - (* the shadow of the class-0 frames *)
        replace (fs_frame FS 0 0) with (FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
        replace (fs_shadow_area 0) with 131072 by reflexivity. unfold shadow_addr.
        replace 131072 with ((FS + 1085439) / 8 - (FS + 36864) / 8 + 1) by (Z.div_mod_to_equations; lia).
        apply (PFR (FS + 36864) (FS + 1085439)); lia.
      - exact R88.
      - exact R8. }
    intros ms' PO. exact (mb_retF Q m1 h flags ms' K PF PO).
  Qed.

  Lemma entryF : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q (m0 : word -> option byte), m0 = m -> KBF Q ->
    evtF rsegs RNG Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 b) (Z_to_bv 64 o) a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_BOX_MODEL_BLOCK) fc None m0 (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q m0 Em0 K.
    apply (mb_preF t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q m0 Em0).
    intros m1 PF. exact (mb_callF t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q m1 K PF).
  Qed.

  (* 0x86e74: a0 = s5, the saved registers (ra, s0..s9) restored and the frame popped, ret. *)
  Lemma td_tailF : forall (r : Z) (m' : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (spc fr f : Z),
    r = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
    rw_cells rsegs m' (bv_unsigned sp + -88) (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) ->
    wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (bv_unsigned sp - 4272) (bv_unsigned sp) ->
    asan_cells m' -> shadow_rw m' -> addressable m' (bv_unsigned sp - 4272) 4272 ->
    fp [0%nat] m' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
       (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) ->
    reac_box_model_block_tls m' (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp) ->
    (if (p =? 0) || (o =? 0)
     then munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp)] ++
                 reac_box_model_block_X (bv_unsigned sp) FS) m m'
     else bytes_at rsegs m' o (synth row b nb) /\
          munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp); (o, o + 32)] ++
                 reac_box_model_block_X (bv_unsigned sp) FS) m m') ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) (Z_to_bv 64 b) (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86e74) fc None m' (seg_rom rsegs)).
  Proof.
    intros r m' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 spc fr f
      Er FR WM MI ST AC SW AW FP TL POSTMU.
    subst r. mbF_open HRNG.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp. unfold SAVES in FR.
    do 15 step.
    apply evtF_done. unfold Q0, reac_box_model_block_post. cbv beta.
    do 14 eexists. exists m'. split; [reflexivity|].
    split; [exact POSTMU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact AC|]. split; [exact SW|]. split; [exact AW|]. split; [exact FP | exact TL].
  Qed.

  (* 0x86e74: the epilogue, but with s6 (clobbered by the jump-table dispatch) left general. Like td_tail but the
     s6 slot is a parameter: the restore (ld s6, 96(sp)) overwrites it, so its input value is irrelevant. *)
  Lemma epi0F : forall (r : Z) (m' : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word) (spc fr f : Z),
    r = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
    rw_cells rsegs m' (bv_unsigned sp + -88) (SAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9) ->
    wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' (bv_unsigned sp - 4272) (bv_unsigned sp) ->
    asan_cells m' -> shadow_rw m' -> addressable m' (bv_unsigned sp - 4272) 4272 ->
    fp [0%nat] m' (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
       (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o) ->
    reac_box_model_block_tls m' (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp) ->
    (if (p =? 0) || (o =? 0)
     then munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp)] ++
                 reac_box_model_block_X (bv_unsigned sp) FS) m m'
     else bytes_at rsegs m' o (synth row b nb) /\
          munch ([(bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K, bv_unsigned sp); (o, o + 32)] ++
                 reac_box_model_block_X (bv_unsigned sp) FS) m m') ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 r) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86e74) fc None m' (seg_rom rsegs)).
  Proof.
    intros r m' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 spc fr f
      Er FR WM MI ST AC SW AW FP TL POSTMU.
    subst r. mbF_open HRNG.
    pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp. unfold SAVES in FR.
    do 15 step.
    apply evtF_done. unfold Q0, reac_box_model_block_post. cbv beta.
    do 14 eexists. exists m'. split; [reflexivity|].
    split; [exact POSTMU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact AC|]. split; [exact SW|]. split; [exact AW|]. split; [exact FP | exact TL].
  Qed.
End MainF.
