(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import SumsLib Sums_code.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition imemset_words : list (bv 32) :=
  [W_a9b08; W_a9b0c; W_a9b10; W_a9b14; W_a9b18; W_a9b1c; W_a9b20; W_a9b24;
   W_a9b28; W_a9b2c; W_a9b30; W_a9b34; W_a9b38; W_a9b3c; W_a9b40; W_a9b44;
   W_a9b48; W_a9b4c; W_a9b50; W_a9b54; W_a9b58; W_a9b5c; W_a9b60; W_a9b64].

(* [comment removed for export] *)
Definition imemset_clob : list reg := [11; 12; 13].

(* [comment removed for export] *)
Definition align15 (n : Z) (s : word) : Z := Z.land (Z.lor n (bv_unsigned s)) 15.

Lemma land15_range : forall x, (0 <= x)%Z -> (0 <= Z.land x 15 < 16)%Z.
Proof.
  intros x Hx. change 15%Z with (Z.ones 4). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma align15_range : forall n s, (0 <= n)%Z -> (0 <= align15 n s < 16)%Z.
Proof.
  intros n s Hn. unfold align15. apply land15_range. apply Z.lor_nonneg. pose proof (u64_range s). lia.
Qed.

Lemma u_align15 : forall n (s : word), (0 <= n < 2 ^ 64)%Z ->
  bv_unsigned (v_andi (v_or (Z_to_bv 64 n) s) 15) = align15 n s.
Proof.
  intros n s Hn. pose proof (u64_range s) as Hs.
  pose proof (Z_lor_range n (bv_unsigned s) Hn Hs) as Hl.
  unfold v_andi, v_or, align15. rewrite (u_Z2bv n) by lia.
  rewrite (u_Z2bv (Z.lor n (bv_unsigned s))) by lia.
  change (bv_wrap 64 15) with 15%Z.
  pose proof (land15_range (Z.lor n (bv_unsigned s)) ltac:(lia)).
  apply u_Z2bv; lia.
Qed.

Lemma align15_n16 : forall n s, (0 <= n)%Z -> align15 n s = 0%Z -> (n mod 16 = 0)%Z.
Proof.
  intros n s Hn H. unfold align15 in H. pose proof (u64_range s).
  rewrite Z.land_lor_distr_l in H. apply Z.lor_eq_0_iff in H as [H _].
  change 15%Z with (Z.ones 4) in H. rewrite Z.land_ones in H by lia. exact H.
Qed.

(* [comment removed for export] *)
Definition cbyte_ (c : word) : byte := Z_to_bv 8 (bv_unsigned c).
Definition cpat_ (c : word) : word := Z_to_bv 64 (bv_unsigned c * M8).

Lemma cpat_bytes : forall c : word, (bv_unsigned c < 256)%Z ->
  word_to_le_bytes 8 (cpat_ c) = repeat (cbyte_ c) 8.
Proof. intros c Hc. pose proof (u64_range c). apply rep8_bytes. lia. Qed.

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
    (* [comment removed for export] *)
    code_nth HC HCODE imemset_words 0%nat C0; code_nth HC HCODE imemset_words 1%nat C4; code_nth HC HCODE imemset_words 2%nat C8;
    code_nth HC HCODE imemset_words 3%nat C12; code_nth HC HCODE imemset_words 4%nat C16; code_nth HC HCODE imemset_words 5%nat C20;
    code_nth HC HCODE imemset_words 6%nat C24; code_nth HC HCODE imemset_words 7%nat C28; code_nth HC HCODE imemset_words 8%nat C32;
    code_nth HC HCODE imemset_words 9%nat C36; code_nth HC HCODE imemset_words 10%nat C40; code_nth HC HCODE imemset_words 11%nat C44;
    code_nth HC HCODE imemset_words 12%nat C48; code_nth HC HCODE imemset_words 13%nat C52; code_nth HC HCODE imemset_words 14%nat C56;
    code_nth HC HCODE imemset_words 15%nat C60; code_nth HC HCODE imemset_words 16%nat C64; code_nth HC HCODE imemset_words 17%nat C68;
    code_nth HC HCODE imemset_words 18%nat C72; code_nth HC HCODE imemset_words 19%nat C76; code_nth HC HCODE imemset_words 20%nat C80;
    code_nth HC HCODE imemset_words 21%nat C84; code_nth HC HCODE imemset_words 22%nat C88; code_nth HC HCODE imemset_words 23%nat C92;
    clear HC.

  (* [comment removed for export] *)
  Ltac msb F D kk :=
    chain_step; [reflexivity
      | eapply MmapSim.step_sb_at with (a := at_ s kk) (v := c) (b := cbyte);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity | reflexivity
        | apply (wr_s segs mem0 s n cbyte Hn Hnw Hok); cbn; lia ]
      | step_simpl];
    rewrite (msetk_extend1 mem0 s cbyte kk) by lia; vn.

  (* [comment removed for export] *)
  Ltac msd F D kk :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := at_ s kk) (v := cpat);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | apply (wr_s segs mem0 s n cbyte Hn Hnw Hok); cbn; lia ]
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
  Proof.
    get_code. pose proof (u64_range s) as Hs.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hi.
    - eexists. split.
      + msb C24 D_a9b20 k.                        (* [comment removed for export] *)
        an C28 D_a9b24.                           (* [comment removed for export] *)
        ab_ft C32 D_a9b28 ltac:(condz).           (* [comment removed for export] *)
        an C36 D_a9b2c.                           (* [comment removed for export] *)
        aret C92 D_a9b64 ret.
        replace (k + 1)%Z with n by lia. apply mst_refl.
      + unfold imemset_clob. solve_regs_agree.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 24) (MS (k + 1)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = c /\ getr r 13 = at_ s (k + 1)
                         /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
      + eexists. split.
        * msb C24 D_a9b20 k.
          an C28 D_a9b24.
          ab_tk C32 D_a9b28 ltac:(condz).         (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold imemset_clob. solve_regs_agree.
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
  Proof.
    get_code. pose proof (u64_range s) as Hs. pose proof (u64_range c) as Hc.
    induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hk16 Hi Hc256.
    - eexists. split.
      + msd C76 D_a9b54 k.                        (* [comment removed for export] *)
        msd C80 D_a9b58 (k + 8)%Z.                (* [comment removed for export] *)
        an C84 D_a9b5c.                           (* [comment removed for export] *)
        ab_ft C88 D_a9b60 ltac:(condz).           (* [comment removed for export] *)
        aret C92 D_a9b64 ret.
        replace (k + 8 + 8)%Z with n by lia. apply mst_refl.
      + unfold imemset_clob. solve_regs_agree.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 76) (MS (k + 16)) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = cpat /\ getr r 13 = at_ s (k + 16)
                         /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
      + eexists. split.
        * msd C76 D_a9b54 k.
          msd C80 D_a9b58 (k + 8)%Z.
          an C84 D_a9b5c.
          ab_tk C88 D_a9b60 ltac:(condz).         (* [comment removed for export] *)
          replace (k + 8 + 8)%Z with (k + 16)%Z by lia. apply mst_refl.
        * post. unfold imemset_clob. solve_regs_agree.
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
  Proof.
    get_code. intros regs ret Hret H1 H10 H11 H12.
    pose proof (u64_range s) as Hs. pose proof (u64_range c) as Hc.
    pose proof (align15_range n s Hn) as HA.
    change (wbytes mem0 s (repeat (cbyte_ c) (Z.to_nat n))) with (MS n). change mem0 with (MS 0).
    (* [comment removed for export] *)
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 8) (MS 0) rom)
             (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = c /\ getr r 12 = Z_to_bv 64 n
                       /\ getr r 13 = Z_to_bv 64 (align15 n s) /\ regs_agree CL regs r)).
    { eexists. split.
      - an C0 D_a9b08.                            (* [comment removed for export] *)
        av C4 D_a9b0c (Z_to_bv 64 (align15 n s))
           ltac:(rewrite <- (u_align15 n s) by lia; symmetry; apply Z_to_bv_bv_unsigned).  (* [comment removed for export] *)
        apply mst_refl.
      - post. unfold imemset_clob. solve_regs_agree. }
    cbv beta. intros r0 (R1 & R10 & R11 & R12 & R13 & AG0).
    destruct (Z.eq_dec (align15 n s) 0) as [HA0|HA0].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hz|Hnz].
      + eexists. split.
        * ab_tk C8 D_a9b10 ltac:(condz).          (* [comment removed for export] *)
          ab_tk C40 D_a9b30 ltac:(condz).         (* [comment removed for export] *)
          aret C92 D_a9b64 ret.
          rewrite Hz. apply mst_refl.
        * exact AG0.
      + pose proof (HC256 HA0 Hnz) as Hc256.
        pose proof (align15_n16 n s Hn HA0) as Hn16.
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 76) (MS 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = cpat /\ getr r 13 = at_ s 0
                           /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_tk C8 D_a9b10 ltac:(condz).       (* [comment removed for export] *)
             ab_ft C40 D_a9b30 ltac:(condz).      (* [comment removed for export] *)
             av C44 D_a9b34 (at_ s n) ltac:(apply v_add_at; lia).           (* [comment removed for export] *)
             av C48 D_a9b38 (Z_to_bv 64 (bv_unsigned c * 2 ^ 8)) ltac:(apply v_slli_mul; lia).  (* [comment removed for export] *)
             av_or C52 D_a9b3c (Z_to_bv 64 (bv_unsigned c * 257))
               ltac:(rewrite v_or_shl by (unorm; lia); f_equal; lia).                        (* [comment removed for export] *)
             av C56 D_a9b40 (Z_to_bv 64 (bv_unsigned c * 257 * 2 ^ 16))
               ltac:(rewrite v_slli_mul by lia; unorm; reflexivity).                          (* [comment removed for export] *)
             av_or C60 D_a9b44 (Z_to_bv 64 (bv_unsigned c * 16843009))
               ltac:(rewrite v_or_shl by (unorm; lia); unorm; f_equal; lia).                 (* [comment removed for export] *)
             av C64 D_a9b48 (Z_to_bv 64 (bv_unsigned c * 16843009 * 2 ^ 32))
               ltac:(rewrite v_slli_mul by lia; unorm; reflexivity).                          (* [comment removed for export] *)
             av_or C68 D_a9b4c (cpat_ c)
               ltac:(rewrite v_or_shl by (unorm; lia); unfold cpat_, M8; unorm; f_equal; lia). (* [comment removed for export] *)
             an C72 D_a9b50.                      (* [comment removed for export] *)
             apply mst_refl.
          -- post; rewrite ?at_0; try reflexivity. unfold imemset_clob. ra_chain.
        * cbv beta. intros r1 (S1 & S11 & S13 & S12 & AG1).
          assert (Hdiv : (n = 16 * (n / 16))%Z) by (pose proof (Z.div_mod n 16 ltac:(lia)); lia).
          assert (Hi : exists i : nat, (Z.of_nat i * 16 = n - 0 - 16)%Z) by (exists (Z.to_nat (n / 16 - 1)); lia).
          destruct Hi as (i & Hi).
          destruct (al_loop i r1 ret 0 Hret S1 S11 S13 S12 ltac:(lia) ltac:(lia) Hi Hc256) as (r2 & RUN & AG2).
          exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec n 0) as [Hz|Hnz].
      + eexists. split.
        * ab_ft C8 D_a9b10 ltac:(condz).          (* [comment removed for export] *)
          ab_tk C12 D_a9b14 ltac:(condz).         (* [comment removed for export] *)
          aret C92 D_a9b64 ret.
          rewrite Hz. apply mst_refl.
        * exact AG0.
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 24) (MS 0) rom)
                 (fun r => getr r 1 = ret /\ getr r 11 = c /\ getr r 13 = at_ s 0
                           /\ getr r 12 = at_ s n /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C8 D_a9b10 ltac:(condz).       (* [comment removed for export] *)
             ab_ft C12 D_a9b14 ltac:(condz).      (* [comment removed for export] *)
             av C16 D_a9b18 (at_ s n) ltac:(apply v_add_at; lia).           (* [comment removed for export] *)
             an C20 D_a9b1c.                      (* [comment removed for export] *)
             apply mst_refl.
          -- post; rewrite ?at_0; try reflexivity. unfold imemset_clob. ra_chain.
        * cbv beta. intros r1 (S1 & S11 & S13 & S12 & AG1).
          destruct (bl_loop (Z.to_nat (n - 1)) r1 ret 0 Hret S1 S11 S13 S12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
          exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.
End IMEMSET.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.

(* [comment removed for export] *)
Definition asan_imemset_entry : word := 0x1d101c.

Lemma asan_imemset_code :
  code_at AsanUbsan.M.loaded_segments asan_imemset_entry 0 imemset_words.
Proof. unfold imemset_words. code_at_vm. Qed.

Theorem asan_imemset : forall mem0 (s c : word) n rom regs (ret : word),
  (0 <= n)%Z -> (bv_unsigned s + n < 2 ^ 64)%Z ->
  store_ok AsanUbsan.M.loaded_segments mem0 s (Z.to_nat n) = true ->
  (align15 n s = 0%Z -> n <> 0%Z -> (bv_unsigned c < 256)%Z) ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = s -> getr regs 11 = c -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps AsanUbsan.M.loaded_segments
           (mkst regs asan_imemset_entry mem0 rom)
           (mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) rom)
    /\ regs_agree (fun r => In r imemset_clob) regs regs'.
Proof.
  intros mem0 s c n rom regs ret Hn Hnw Hok HC256.
  rewrite <- (at_0 asan_imemset_entry).
  apply (imemset_run _ _ mem0 s c n rom asan_imemset_code Hn Hnw Hok HC256).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
