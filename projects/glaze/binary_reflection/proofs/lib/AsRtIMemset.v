(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.


(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.

Definition imemset_words : list (bv 32) :=
  [W_7ff30; W_7ff34; W_7ff38; W_7ff3c; W_7ff40; W_7ff44; W_7ff48; W_7ff4c; W_7ff50; W_7ff54; W_7ff58; W_7ff5c; W_7ff60; W_7ff64; W_7ff68; W_7ff6c; W_7ff70; W_7ff74; W_7ff78; W_7ff7c; W_7ff80; W_7ff84; W_7ff88; W_7ff8c]%list.
End FPGen1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPGen2.
Context {fx : FPState}.

Definition imemset_clob : list reg := [11; 12; 13].

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cbyte_ (c : word) : byte := Z_to_bv 8 (bv_unsigned c).
Definition cpat_ (c : word) : word := Z_to_bv 64 (bv_unsigned c * M8).

Lemma cpat_bytes : forall c : word, (bv_unsigned c < 256)%Z ->
  word_to_le_bytes 8 (cpat_ c) = repeat (cbyte_ c) 8.
Proof using. intros c Hc. pose proof (u64_range c). apply rep8_bytes. lia. Qed.

Section IMEMSET.
  Variable segs : list Segment.
  Variable base : word.
  Variable mem0 : word -> option byte.
  Variables s c : word.
  Variable n : Z.
  Variable rom : word -> option byte.
  Hypothesis HCODE : code_at segs base 0 imemset_words.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnw : (bv_unsigned s + n < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok segs mem0 s (Z.to_nat n) = true.
  (* [comment removed for export] *)
  Hypothesis HC256 : align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z.

  #[local] Abbreviation cbyte := (cbyte_ c).
  #[local] Abbreviation cpat := (cpat_ c).
  #[local] Abbreviation MS := (msetk mem0 s (cbyte_ c)).
  #[local] Abbreviation CL := (fun r => In r imemset_clob).

  (* [comment removed for export] *)
  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; cbn [code_at imemset_words Z.add Pos.add Pos.succ] in HC;
    destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56 & C60 & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & _).

  (* [comment removed for export] *)
  Ltac msb F D kk :=
    chain_step; [reflexivity
      | eapply MmapSim.step_sb_at with (a := at_ s kk) (v := c) (b := cbyte);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity | reflexivity
        | apply (wr_s segs mem0 s n cbyte Hn Hnw Hok); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]
      | step_simpl];
    rewrite (msetk_extend1 mem0 s cbyte kk) by lia; vn.

  (* [comment removed for export] *)
  Ltac msd F D kk :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := at_ s kk) (v := cpat);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | apply (wr_s segs mem0 s n cbyte Hn Hnw Hok); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]
      | step_simpl];
    rewrite (cpat_bytes c) by lia;
    rewrite (msetk_extend mem0 s cbyte kk 8) by lia; change (Z.of_nat 8) with 8%Z; zlit_at; vn.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bl_loop : forall (i : nat) regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = c -> getr regs 13 = at_ s k -> getr regs 12 = at_ s n ->
    (0 <= k < n)%Z -> Z.of_nat i = (n - 1 - k)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 24) (MS k) rom) (mkst regs' ret (MS n) rom)
      /\ regs_agree CL regs regs'.
  Proof using Hok Hnw Hn HCODE.
    get_code. pose proof (u64_range s) as Hs.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hi.
    - wd_eexists. split.
      + msb C24 D_7ff48 k.                        (* [comment removed for export] *)
        an C28 D_7ff4c.                           (* [comment removed for export] *)
        ab_ft C32 D_7ff50 ltac:(condz).           (* [comment removed for export] *)
        an C36 D_7ff54.                           (* [comment removed for export] *)
        aret C92 D_7ff8c ret.
        replace (k + 1)%Z with n by lia. wd_refl.
      + (lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end). solve_regs_agree.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 24) (MS (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = c /\ getr r 13 = at_ s (k + 1)
                         /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
      + wd_eexists. split.
        * msb C24 D_7ff48 k.
          an C28 D_7ff4c.
          ab_tk C32 D_7ff50 ltac:(condz).         (* [comment removed for export] *)
          wd_refl.
        * post. (lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end). solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
        destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al_loop : forall (i : nat) regs (ret : word) k,
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 11 = cpat -> getr regs 13 = at_ s k -> getr regs 12 = at_ s n ->
    (0 <= k)%Z -> (k + 16 <= n)%Z -> (Z.of_nat i * 16 = n - k - 16)%Z ->
    (bv_unsigned c < 256)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 76) (MS k) rom) (mkst regs' ret (MS n) rom)
      /\ regs_agree CL regs regs'.
  Proof using Hok Hnw Hn HCODE.
    get_code. pose proof (u64_range s) as Hs. pose proof (u64_range c) as Hc.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hk16 Hi Hc256.
    - wd_eexists. split.
      + msd C76 D_7ff7c k.                        (* [comment removed for export] *)
        msd C80 D_7ff80 (k + 8)%Z.                (* [comment removed for export] *)
        an C84 D_7ff84.                           (* [comment removed for export] *)
        ab_ft C88 D_7ff88 ltac:(condz).           (* [comment removed for export] *)
        aret C92 D_7ff8c ret.
        replace (k + 8 + 8)%Z with n by lia. wd_refl.
      + (lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end). solve_regs_agree.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 76) (MS (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = cpat /\ getr r 13 = at_ s (k + 16)
                         /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
      + wd_eexists. split.
        * msd C76 D_7ff7c k.
          msd C80 D_7ff80 (k + 8)%Z.
          an C84 D_7ff84.
          ab_tk C88 D_7ff88 ltac:(condz).         (* [comment removed for export] *)
          replace (k + 8 + 8)%Z with (k + 16)%Z by lia. wd_refl.
        * post. (lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end). solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
        destruct (IH r1 ret (k + 16)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia) Hc256) as (r2 & RUN & AG2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem imemset_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = s -> getr regs 11 = c -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps segs (mkst regs (at_ base 0) mem0 rom)
                  (mkst regs' ret (wbytes mem0 s (repeat (cbyte_ c) (Z.to_nat n))) rom)
      /\ regs_agree CL regs regs'.
  Proof using HC256 Hok Hnw Hn HCODE.
    get_code. intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range s) as Hs. pose proof (u64_range c) as Hc.
    pose proof (align15_range n s Hn) as HA.
    change (wbytes mem0 s (repeat (cbyte_ c) (Z.to_nat n))) with (MS n). change mem0 with (MS 0).
    (* [comment removed for export] *)
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MS 0) rom)
             (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = c /\ getr r 12 = Z_to_bv 64 n
                       /\ getr r 13 = Z_to_bv 64 (align15 n s) /\ regs_agree CL regs r)).
    { wd_eexists. split.
      - an C0 D_7ff30.                            (* [comment removed for export] *)
        av C4 D_7ff34 (Z_to_bv 64 (align15 n s))
           ltac:(rewrite <- (u_align15 n s) by lia; symmetry; apply Z_to_bv_bv_unsigned).  (* [comment removed for export] *)
        wd_refl.
      - post. (lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end). solve_regs_agree. }
    cbv beta. intros r0 (R1 & R10 & R11 & R12 & R13 & AG0).
    destruct (Z.eq_dec (align15 n s) 0) as [HA0|HA0].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hz|Hnz].
      + wd_eexists. split.
        * ab_tk C8 D_7ff38 ltac:(condz).          (* [comment removed for export] *)
          ab_tk C40 D_7ff58 ltac:(condz).         (* [comment removed for export] *)
          aret C92 D_7ff8c ret.
          rewrite Hz. wd_refl.
        * exact AG0.
      + pose proof (HC256 HA0 Hnz) as Hc256.
        pose proof (align15_n16 n s Hn HA0) as Hn16.
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 76) (MS 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = cpat /\ getr r 13 = at_ s 0
                           /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
        * wd_eexists. split.
          -- ab_tk C8 D_7ff38 ltac:(condz).       (* [comment removed for export] *)
             ab_ft C40 D_7ff58 ltac:(condz).      (* [comment removed for export] *)
             av C44 D_7ff5c (at_ s n) ltac:(apply v_add_at; lia).           (* [comment removed for export] *)
             av C48 D_7ff60 (Z_to_bv 64 (bv_unsigned c * 2 ^ 8)) ltac:(apply v_slli_mul; lia).  (* [comment removed for export] *)
             av_or C52 D_7ff64 (Z_to_bv 64 (bv_unsigned c * 257))
               ltac:(rewrite v_or_shl by (wd_ulia); f_equal; lia).                        (* [comment removed for export] *)
             av C56 D_7ff68 (Z_to_bv 64 (bv_unsigned c * 257 * 2 ^ 16))
               ltac:(rewrite v_slli_mul by lia; unorm; reflexivity).                          (* [comment removed for export] *)
             av_or C60 D_7ff6c (Z_to_bv 64 (bv_unsigned c * 16843009))
               ltac:(rewrite v_or_shl by (wd_ulia); unorm; f_equal; lia).                 (* [comment removed for export] *)
             av C64 D_7ff70 (Z_to_bv 64 (bv_unsigned c * 16843009 * 2 ^ 32))
               ltac:(rewrite v_slli_mul by lia; unorm; reflexivity).                          (* [comment removed for export] *)
             av_or C68 D_7ff74 (cpat_ c)
               ltac:(rewrite v_or_shl by (wd_ulia); (lazymatch goal with |- ?G => let G' := eval unfold cpat_, M8 in G in change_no_check G' end); unorm; f_equal; lia). (* [comment removed for export] *)
             an C72 D_7ff78.                      (* [comment removed for export] *)
             wd_refl.
          -- post; rewrite ?at_0; try reflexivity. (lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end). ra_chain.
        * cbv beta. intros r1 (S1 & S11 & S13 & S12 & AG1).
          assert (Hdiv : (n = 16 * (n / 16))%Z) by (pose proof (Z.div_mod n 16 ltac:(lia)); lia).
          assert (Hi : exists i : nat, (Z.of_nat i * 16 = n - 0 - 16)%Z) by (exists (Z.to_nat (n / 16 - 1)); lia).
          destruct Hi as (i & Hi).
          destruct (al_loop i r1 ret 0 Hret S1 S11 S13 S12 ltac:(lia) ltac:(lia) Hi Hc256) as (r2 & RUN & AG2).
          exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hz|Hnz].
      + wd_eexists. split.
        * ab_ft C8 D_7ff38 ltac:(condz).          (* [comment removed for export] *)
          ab_tk C12 D_7ff3c ltac:(condz).         (* [comment removed for export] *)
          aret C92 D_7ff8c ret.
          rewrite Hz. wd_refl.
        * exact AG0.
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 24) (MS 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = c /\ getr r 13 = at_ s 0
                           /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
        * wd_eexists. split.
          -- ab_ft C8 D_7ff38 ltac:(condz).       (* [comment removed for export] *)
             ab_ft C12 D_7ff3c ltac:(condz).      (* [comment removed for export] *)
             av C16 D_7ff40 (at_ s n) ltac:(apply v_add_at; lia).           (* [comment removed for export] *)
             an C20 D_7ff44.                      (* [comment removed for export] *)
             wd_refl.
          -- post; rewrite ?at_0; try reflexivity. (lazymatch goal with |- ?G => let G' := eval unfold imemset_clob in G in change_no_check G' end). ra_chain.
        * cbv beta. intros r1 (S1 & S11 & S13 & S12 & AG1).
          destruct (bl_loop (Z.to_nat (n - 1)) r1 ret 0 Hret S1 S11 S13 S12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
          exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.
End IMEMSET.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End FPGen2.


From OSSVerify.glaze.binary_reflection.images Require Import Asan.

(* [comment removed for export] *)
Section FPGen3.
Context {fx : FPState}.

Definition asan_imemset_entry : word := 0x7ff38.

Lemma asan_imemset_code :
  code_at Asan.M.loaded_segments asan_imemset_entry 0 imemset_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold imemset_words in G in change_no_check G' end). code_at_vm. Qed.

Theorem asan_imemset : forall mem0 (s c : word) n rom regs (ret : word),
  (0 <= n)%Z -> (bv_unsigned s + n < 2 ^ 64)%Z ->
  store_ok Asan.M.loaded_segments mem0 s (Z.to_nat n) = true ->
  (align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z) ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = s -> getr regs 11 = c -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps Asan.M.loaded_segments
           (mkst regs asan_imemset_entry mem0 rom)
           (mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) rom)
    /\ regs_agree (fun r => In r imemset_clob) regs regs'.
Proof using.
  intros mem0 s c n rom regs ret Hn Hnw Hok HC256.
  rewrite <- (at_0 asan_imemset_entry).
  apply (imemset_run _ _ mem0 s c n rom asan_imemset_code Hn Hnw Hok HC256).
Qed.

End FPGen3.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
