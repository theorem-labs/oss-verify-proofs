(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemchr. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MuslStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemchr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
Definition mstrlen_words : list (option (bv 32)) :=
  [
   Some W_f5934; Some W_f5938; Some W_f593c; Some W_f5940; Some W_f5944; Some W_f5948; Some W_f594c;
   Some W_f5950; Some W_f5954; Some W_f5958; Some W_f595c; Some W_f5960; Some W_f5964; Some W_f5968;
   Some W_f596c; None; None; None; None; Some W_f5980; Some W_f5984; Some W_f5988; Some W_f598c;
   Some W_f5990; Some W_f5994; Some W_f5998; Some W_f599c; Some W_f59a0; Some W_f59a4; Some W_f59a8;
   Some W_f59ac; Some W_f59b0; Some W_f59b4; Some W_f59b8; Some W_f59bc; Some W_f59c0
  ]%list.


(* [comment removed for export] *)
Definition TWs (x : word) : word := v_and (v_or (v_sub (Z_to_bv 64 Mc) x) x) (Z_to_bv 64 Hc).
Lemma TWs_TW : forall x, TWs x = TW x.
Proof using. intros x. (lazymatch goal with |- ?G => let G' := eval unfold TWs, TW in G in change_no_check G' end). rewrite !v_xor_0. reflexivity. Qed.

(* [comment removed for export] *)
Definition sl_consts (segs : list Segment) (base : word) (cM cH : Z) : Prop :=
  exists x1 x4 : word, forall regs mem rom (vM vH : word),
    rdn segs mem (Z_to_bv 64 cM) 8 = Some (word_to_le_bytes 8 vM) ->
    rdn segs mem (Z_to_bv 64 cH) 8 = Some (word_to_le_bytes 8 vH) ->
    msteps segs (mkst regs (at_ base 60) mem rom)
                (mkst (regupd (regupd (regupd (regupd regs 11 x1) 14 x4) 13 vM) 14 vH) (at_ base 76) mem rom).

(* [comment removed for export] *)
Record strlH (segs : list Segment) (mem : word -> option byte) (s : word) (buf : list byte) (K : Z) : Prop := STRLH {
  Hbuf : rdn segs mem s (length buf) = Some buf;
  Hwin : ((bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf))%Z;
  Hnw  : (bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64)%Z;
  HK0  : (0 <= K)%Z;
  Hzero : bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0%Z;
  Hnz  : forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0%Z }.

Section STRLEN.
  Variable segs : list Segment.
  Variable base : word.
  Variables cM cH : Z.
  Hypothesis HCODE : code_ato segs base 0 mstrlen_words.
  Hypothesis HCONST : sl_consts segs base cM cH.

  Lemma Fo0 : fetch_word segs (at_ base 0) = Some W_f5934.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 0 _ HCODE eq_refl). Qed.
  Lemma Fo4 : fetch_word segs (at_ base 4) = Some W_f5938.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 1 _ HCODE eq_refl). Qed.
  Lemma Fo8 : fetch_word segs (at_ base 8) = Some W_f593c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 2 _ HCODE eq_refl). Qed.
  Lemma Fo12 : fetch_word segs (at_ base 12) = Some W_f5940.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 3 _ HCODE eq_refl). Qed.
  Lemma Fo16 : fetch_word segs (at_ base 16) = Some W_f5944.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 4 _ HCODE eq_refl). Qed.
  Lemma Fo20 : fetch_word segs (at_ base 20) = Some W_f5948.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 5 _ HCODE eq_refl). Qed.
  Lemma Fo24 : fetch_word segs (at_ base 24) = Some W_f594c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 6 _ HCODE eq_refl). Qed.
  Lemma Fo28 : fetch_word segs (at_ base 28) = Some W_f5950.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 7 _ HCODE eq_refl). Qed.
  Lemma Fo32 : fetch_word segs (at_ base 32) = Some W_f5954.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 8 _ HCODE eq_refl). Qed.
  Lemma Fo36 : fetch_word segs (at_ base 36) = Some W_f5958.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 9 _ HCODE eq_refl). Qed.
  Lemma Fo40 : fetch_word segs (at_ base 40) = Some W_f595c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 10 _ HCODE eq_refl). Qed.
  Lemma Fo44 : fetch_word segs (at_ base 44) = Some W_f5960.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 11 _ HCODE eq_refl). Qed.
  Lemma Fo48 : fetch_word segs (at_ base 48) = Some W_f5964.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 12 _ HCODE eq_refl). Qed.
  Lemma Fo52 : fetch_word segs (at_ base 52) = Some W_f5968.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 13 _ HCODE eq_refl). Qed.
  Lemma Fo56 : fetch_word segs (at_ base 56) = Some W_f596c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 14 _ HCODE eq_refl). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Fo76 : fetch_word segs (at_ base 76) = Some W_f5980.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 19 _ HCODE eq_refl). Qed.
  Lemma Fo80 : fetch_word segs (at_ base 80) = Some W_f5984.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 20 _ HCODE eq_refl). Qed.
  Lemma Fo84 : fetch_word segs (at_ base 84) = Some W_f5988.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 21 _ HCODE eq_refl). Qed.
  Lemma Fo88 : fetch_word segs (at_ base 88) = Some W_f598c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 22 _ HCODE eq_refl). Qed.
  Lemma Fo92 : fetch_word segs (at_ base 92) = Some W_f5990.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 23 _ HCODE eq_refl). Qed.
  Lemma Fo96 : fetch_word segs (at_ base 96) = Some W_f5994.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 24 _ HCODE eq_refl). Qed.
  Lemma Fo100 : fetch_word segs (at_ base 100) = Some W_f5998.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 25 _ HCODE eq_refl). Qed.
  Lemma Fo104 : fetch_word segs (at_ base 104) = Some W_f599c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 26 _ HCODE eq_refl). Qed.
  Lemma Fo108 : fetch_word segs (at_ base 108) = Some W_f59a0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 27 _ HCODE eq_refl). Qed.
  Lemma Fo112 : fetch_word segs (at_ base 112) = Some W_f59a4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 28 _ HCODE eq_refl). Qed.
  Lemma Fo116 : fetch_word segs (at_ base 116) = Some W_f59a8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 29 _ HCODE eq_refl). Qed.
  Lemma Fo120 : fetch_word segs (at_ base 120) = Some W_f59ac.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 30 _ HCODE eq_refl). Qed.
  Lemma Fo124 : fetch_word segs (at_ base 124) = Some W_f59b0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 31 _ HCODE eq_refl). Qed.
  Lemma Fo128 : fetch_word segs (at_ base 128) = Some W_f59b4.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 32 _ HCODE eq_refl). Qed.
  Lemma Fo132 : fetch_word segs (at_ base 132) = Some W_f59b8.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 33 _ HCODE eq_refl). Qed.
  Lemma Fo136 : fetch_word segs (at_ base 136) = Some W_f59bc.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 34 _ HCODE eq_refl). Qed.
  Lemma Fo140 : fetch_word segs (at_ base 140) = Some W_f59c0.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 mstrlen_words 35 _ HCODE eq_refl). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable mem : word -> option byte.
  Variable s : word.
  Variable buf : list byte.
  Variable K : Z.
  Variable rom : word -> option byte.
  Hypothesis HOK : strlH segs mem s buf K.
  Hypothesis HM : rdn segs mem (Z_to_bv 64 cM) 8 = Some (LE8 (Z_to_bv 64 Mc)).
  Hypothesis HH : rdn segs mem (Z_to_bv 64 cH) 8 = Some (LE8 (Z_to_bv 64 Hc)).

  #[local] Notation L := (Z.of_nat (length buf)) (only parsing).
  Definition b_ (j : Z) : byte := nth (Z.to_nat j) buf (Z_to_bv 8 0).
  Definition sb_ (j : Z) (m : nat) : list byte := sub buf (Z.to_nat j) m.

  Let Hbuf := Hbuf _ _ _ _ _ HOK.
  Let Hwin : ((U s + K) / 8 * 8 + 8 <= U s + L)%Z := Hwin _ _ _ _ _ HOK.
  Let Hnw : (U s + L < 2 ^ 64)%Z := Hnw _ _ _ _ _ HOK.
  Let HK0 : (0 <= K)%Z := HK0 _ _ _ _ _ HOK.

  Lemma KL : (K + 1 <= L)%Z.
  Proof using Hwin HOK s mem segs.
    clear -Hwin HK0. pose proof (u64_range s).
    pose proof (Z.div_mod (U s + K) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (U s + K) 8 ltac:(lia)). lia.
  Qed.

  Definition KE : Z := ((U s + K) / 8 * 8 + 8 - U s)%Z.
  Lemma KE_facts : (K + 1 <= KE <= K + 8)%Z /\ (KE <= L)%Z /\ ((U s + KE) mod 8 = 0)%Z.
  Proof using HK0 Hwin HOK mem segs.
    (lazymatch goal with |- ?G => let G' := eval unfold KE in G in change_no_check G' end). clear -Hwin HK0. pose proof (u64_range s).
    pose proof (Z.div_mod (U s + K) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (U s + K) 8 ltac:(lia)).
    repeat split; try lia.
    replace (U s + ((U s + K) / 8 * 8 + 8 - U s))%Z with (8 + ((U s + K) / 8) * 8)%Z by lia.
    rewrite Z.mod_add by lia. reflexivity.
  Qed.

  Lemma bz : U (b_ K) = 0%Z.
  Proof using HOK s mem segs. exact (Hzero _ _ _ _ _ HOK). Qed.
  Lemma bnz : forall j, (0 <= j < K)%Z -> U (b_ j) <> 0%Z.
  Proof using HOK s mem segs. intros j Hj. (lazymatch goal with |- ?G => let G' := eval unfold b_ in G in change_no_check G' end). apply (Hnz _ _ _ _ _ HOK). lia. Qed.

  Lemma rd_w : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= L)%Z -> rdn segs mem (at_ s j) m = Some (sb_ j m).
  Proof using Hbuf HOK K.
    intros j m Hj Hm. (lazymatch goal with |- ?G => let G' := eval unfold sb_ in G in change_no_check G' end).
    replace (at_ s j) with (at_ s (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
    apply (rdn_sub segs mem (length buf)); [exact Hbuf | lia].
  Qed.
  Lemma rd_b : forall j, (0 <= j)%Z -> (j + 1 <= L)%Z -> rdn segs mem (at_ s j) 1 = Some [b_ j].
  Proof using Hbuf HOK K. intros j Hj H1. rewrite (rd_w j 1) by lia. (lazymatch goal with |- ?G => let G' := eval unfold sb_, b_ in G in change_no_check G' end). rewrite sub_nth; [reflexivity | lia]. Qed.
  Lemma sb_len : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= L)%Z -> length (sb_ j m) = m.
  Proof using K s. intros j m Hj Hm. (lazymatch goal with |- ?G => let G' := eval unfold sb_ in G in change_no_check G' end). apply sub_length. lia. Qed.
  Lemma sb_nth : forall j (i : nat), (0 <= j)%Z -> (i < 8)%nat -> (j + 8 <= L)%Z -> nth i (sb_ j 8) (Z_to_bv 8 0) = b_ (j + Z.of_nat i).
  Proof using K s. intros j i Hj Hi H8. (lazymatch goal with |- ?G => let G' := eval unfold sb_, b_ in G in change_no_check G' end). rewrite nth_sub by lia. f_equal. lia. Qed.

  Lemma m_lbu : forall regs pc w rd rs (imm : bv 12) j0 j,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
    getr regs rs = at_ s j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= j)%Z -> (j + 1 <= L)%Z ->
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (b_ j))) (v_addi pc 4) mem rom).
  Proof using Hbuf HOK K.
    intros regs pc w rd rs imm j0 j Hf He Hd Hrs Hj Hj0 Hj1.
    eapply step_lbu; [exact Hf | exact He | exact Hd |].
    rewrite Hrs, at_addi, Hj. apply rd_b; lia.
  Qed.
  Lemma m_ld : forall regs pc w rd rs (imm : bv 12) j0 j,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ8 true rd rs imm, 4%Z) ->
    getr regs rs = at_ s j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= j)%Z -> (j + 8 <= L)%Z ->
    RiscvSemantics.step segs (mkst regs pc mem rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LDv (sb_ j 8))) (v_addi pc 4) mem rom).
  Proof using Hbuf HOK K.
    intros regs pc w rd rs imm j0 j Hf He Hd Hrs Hj Hj0 Hj8.
    eapply step_ld; [exact Hf | exact He | exact Hd | |].
    - rewrite Hrs, at_addi, Hj. apply (rd_w j 8); lia.
    - symmetry. apply u_LDv. apply sb_len; lia.
  Qed.

  Lemma al_room : forall j, ((U s + j) mod 8 = 0)%Z -> (0 <= j <= K)%Z -> (j + 8 <= KE)%Z.
  Proof using HK0 HOK buf mem segs.
    intros j Hal Hj. (lazymatch goal with |- ?G => let G' := eval unfold KE in G in change_no_check G' end). clear -Hal Hj HK0. pose proof (u64_range s).
    pose proof (Z.div_mod (U s + K) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (U s + K) 8 ltac:(lia)).
    pose proof (Z.div_mod (U s + j) 8 ltac:(lia)).
    assert ((U s + j) / 8 <= (U s + K) / 8)%Z by (apply Z.div_le_mono; lia). lia.
  Qed.

  Lemma tw_hit : forall j, (0 <= j <= K)%Z -> (K < j + 8)%Z -> (j + 8 <= L)%Z ->
    c_eq (TWs (LDv (sb_ j 8))) (Z_to_bv 64 Hc) = false.
  Proof using HOK s mem segs.
    intros j Hj HKj HL. rewrite TWs_TW. apply (TW_haszero _ (Z.to_nat (K - j))).
    - apply sb_len; lia.
    - lia.
    - rewrite sb_nth by lia. rewrite <- bz. f_equal. (lazymatch goal with |- ?G => let G' := eval unfold b_ in G in change_no_check G' end). f_equal. lia.
    - intros jj Hjj. rewrite sb_nth by lia. apply bnz. lia.
  Qed.
  Lemma tw_miss : forall j, (0 <= j)%Z -> (j + 8 <= K)%Z -> (j + 8 <= L)%Z ->
    c_eq (TWs (LDv (sb_ j 8))) (Z_to_bv 64 Hc) = true.
  Proof using HOK s mem segs.
    intros j Hj HKj HL. rewrite TWs_TW. apply TW_nozero.
    - apply sb_len; lia.
    - intros i Hi. rewrite sb_nth by lia. apply bnz. lia.
  Qed.

  Lemma v_sub_at : forall k, (0 <= k)%Z -> (U s + k < 2 ^ 64)%Z -> v_sub (at_ s k) s = Z_to_bv 64 k.
  Proof using K buf. intros k Hk Hnw'. pose proof (u64_range s). (lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end). rewrite at_u by lia. f_equal. lia. Qed.

  Lemma andi7_u : forall j, (0 <= U s + j < 2 ^ 64)%Z -> U (v_andi (at_ s j) 7) = ((U s + j) mod 8)%Z.
  Proof using K buf.
    intros j Hj. rewrite u_andi by lia. rewrite at_u by lia.
    change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
  Qed.
  Lemma andi7_u0 : U (v_andi s 7) = (U s mod 8)%Z.
  Proof using.
    pose proof (u64_range s). rewrite u_andi by lia.
    change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mlbu F D jj :=
    chain_step; [reflexivity
      | eapply m_lbu with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi, ?at_at; lazymatch goal with |- s = at_ s _ => exact (eq_sym (at_0 s)) | |- _ => first [reflexivity | f_equal; lia] end | imm_norm; lia | lia | lia]
      | step_simpl]; vn.
  Ltac mld F D jj :=
    chain_step; [reflexivity
      | eapply m_ld with (j := jj);
        [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi, ?at_at; lazymatch goal with |- s = at_ s _ => exact (eq_sym (at_0 s)) | |- _ => first [reflexivity | f_equal; lia] end | imm_norm; lia | lia | lia]
      | step_simpl]; vn.
  Ltac condb :=
    rwH; rewrite c_eq_LBv_0;
    first [ apply Z.eqb_eq; rewrite <- bz; f_equal; f_equal; lia
          | apply Z.eqb_neq; apply bnz; lia ].
  Ltac cond := try (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); cond_lia.
  Ltac condw lem :=
    rwH;
    lazymatch goal with |- c_eq (v_and (v_or (v_sub _ ?x) _) _) _ = ?b =>
      change (c_eq (TWs x) (Z_to_bv 64 Hc) = b) end;
    apply lem; lia.
  Ltac post := repeat split; gres; rwH; rewrite ?at_addi, ?at_at; try reflexivity; try (f_equal; lia);
               try ((lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); unorm; f_equal; lia); try solve_keeps_cs.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_ret : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s -> getr regs 11 = at_ s K ->
    exists regs',
      msteps segs (mkst regs (at_ base 128) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ keeps_cs regs regs'.
  Proof using HK0 Hnw Hwin HOK buf HCODE.
    intros regs ret Hret H1 H10 H11. pose proof KL. pose proof (u64_range base). wd_eexists. split.
    - an Fo128 D_f59b4.                            (* [comment removed for export] *)
      aret Fo132 D_f59b8 ret.
      wd_refl.
    - post. rewrite v_sub_at; [reflexivity | lia | lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma t_loop : forall (i : nat) regs (ret : word) j,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s -> getr regs 12 = at_ s j -> getr regs 11 = at_ s (j - 1) ->
    (0 <= j <= K)%Z -> (Z.of_nat i = K - j)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 112) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ keeps_cs regs regs'.
  Proof using HK0 Hnw Hwin Hbuf HOK buf HCODE.
    pose proof KL as HKL. pose proof (u64_range base) as Hbr.
    induction i as [|i IH]; intros regs ret j Hret H1 H10 H12 H11 Hj Hi.
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 128) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = at_ s K /\ keeps_cs regs r)).
      + wd_eexists. split.
        * mlbu Fo112 D_f59a4 K.                     (* [comment removed for export] *)
          an Fo116 D_f59a8.                      (* [comment removed for export] *)
          an Fo120 D_f59ac.                      (* [comment removed for export] *)
          ab_ft Fo124 D_f59b0 ltac:(condb).      (* [comment removed for export] *)
          wd_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R11 & KC).
        destruct (t_ret r1 ret Hret R1 R10 R11) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 112) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (j + 1) /\ getr r 11 = at_ s (j + 1 - 1)
                         /\ keeps_cs regs r)).
      + wd_eexists. split.
        * mlbu Fo112 D_f59a4 j.                     (* [comment removed for export] *)
          an Fo116 D_f59a8.                      (* [comment removed for export] *)
          an Fo120 D_f59ac.                      (* [comment removed for export] *)
          ab_tk Fo124 D_f59b0 ltac:(condb).      (* [comment removed for export] *)
          wd_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R12 & R11 & KC).
        destruct (IH r1 ret (j + 1)%Z Hret R1 R10 R12 R11 ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma w_loop : forall (i : nat) regs (ret : word) j,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s -> getr regs 12 = at_ s (j - 8) -> getr regs 11 = at_ s (j - 9) ->
    getr regs 13 = Z_to_bv 64 Mc -> getr regs 14 = Z_to_bv 64 Hc ->
    (0 <= j <= K)%Z -> ((U s + j) mod 8 = 0)%Z -> (Z.of_nat i = (K - j) / 8)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 84) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ keeps_cs regs regs'.
  Proof using HK0 Hnw Hwin Hbuf HOK buf HCODE.
    pose proof KL as HKL. pose proof KE_facts as (HKE1 & HKE2 & HKE3). pose proof (u64_range base) as Hbr.
    induction i as [|i IH]; intros regs ret j Hret H1 H10 H12 H11 H13 H14 Hj Hal Hi;
      pose proof (al_room j Hal Hj) as HR.
    - (* [comment removed for export] *)
      assert (HKj : (K < j + 8)%Z).
      { clear -Hi Hj. pose proof (Z.div_mod (K - j) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia)). lia. }
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 112) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s j /\ getr r 11 = at_ s (j - 1)
                         /\ keeps_cs regs r)).
      + wd_eexists. split.
        * mld Fo84 D_f5988 j.                       (* [comment removed for export] *)
          an Fo88 D_f598c.                       (* [comment removed for export] *)
          an Fo92 D_f5990.                       (* [comment removed for export] *)
          an Fo96 D_f5994.                       (* [comment removed for export] *)
          an Fo100 D_f5998.                      (* [comment removed for export] *)
          an Fo104 D_f599c.                      (* [comment removed for export] *)
          ab_ft Fo108 D_f59a0 ltac:(condw tw_hit).   (* [comment removed for export] *)
          wd_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R12 & R11 & KC).
        destruct (t_loop (Z.to_nat (K - j)) r1 ret j Hret R1 R10 R12 R11 ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    - (* [comment removed for export] *)
      assert (HKj : (j + 8 <= K)%Z).
      { clear -Hi Hj. pose proof (Z.div_mod (K - j) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia)). lia. }
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 84) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (j + 8 - 8) /\ getr r 11 = at_ s (j + 8 - 9)
                         /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc /\ keeps_cs regs r)).
      + wd_eexists. split.
        * mld Fo84 D_f5988 j.
          an Fo88 D_f598c.
          an Fo92 D_f5990.
          an Fo96 D_f5994.
          an Fo100 D_f5998.
          an Fo104 D_f599c.
          ab_tk Fo108 D_f59a0 ltac:(condw tw_miss).  (* [comment removed for export] *)
          wd_refl.
        * post.
      + cbv beta. intros r1 (R1 & R10 & R12 & R11 & R13 & R14 & KC).
        destruct (IH r1 ret (j + 8)%Z Hret R1 R10 R12 R11 R13 R14 ltac:(lia)
                    ltac:(rewrite Z.add_assoc, <- Zplus_mod_idemp_l, Hal; reflexivity)
                    ltac:(clear -Hi HKj; pose proof (Z.div_mod (K - j) 8 ltac:(lia));
                          pose proof (Z.mod_pos_bound (K - j) 8 ltac:(lia));
                          pose proof (Z.div_mod (K - (j + 8)) 8 ltac:(lia));
                          pose proof (Z.mod_pos_bound (K - (j + 8)) 8 ltac:(lia)); nia)) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma a_entry : forall regs (ret : word) j,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s -> getr regs 12 = at_ s j ->
    (0 <= j <= K)%Z -> ((U s + j) mod 8 = 0)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 60) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ keeps_cs regs regs'.
  Proof using HK0 Hnw Hwin Hbuf HH HM HOK buf HCONST HCODE cH cM.
    intros regs ret j Hret H1 H10 H12 Hj Hal. pose proof (u64_range base) as Hbr.
    destruct HCONST as (x1 & x4 & GL).
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 84) mem rom)
             (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (j - 8) /\ getr r 11 = at_ s (j - 9)
                       /\ getr r 13 = Z_to_bv 64 Mc /\ getr r 14 = Z_to_bv 64 Hc /\ keeps_cs regs r)).
    - wd_eexists. split.
      + eapply msteps_trans; [exact (GL regs mem rom (Z_to_bv 64 Mc) (Z_to_bv 64 Hc) HM HH)|].
        an Fo76 D_f5980.                         (* [comment removed for export] *)
        an Fo80 D_f5984.                         (* [comment removed for export] *)
        wd_refl.
      + post.
    - cbv beta. intros r1 (R1 & R10 & R12 & R11 & R13 & R14 & KC).
      destruct (w_loop (Z.to_nat ((K - j) / 8)) r1 ret j Hret R1 R10 R12 R11 R13 R14 Hj Hal
                  ltac:(clear -Hj; pose proof (Z.div_pos (K - j) 8); lia)) as (r2 & RUN & A10 & K2).
      exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma h_loop : forall (i : nat) regs (ret : word) j,
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s -> getr regs 11 = at_ s j -> getr regs 12 = at_ s (j + 1) ->
    (0 <= j < K)%Z -> (Z.of_nat i = K - 1 - j)%Z ->
    exists regs',
      msteps segs (mkst regs (at_ base 28) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ keeps_cs regs regs'.
  Proof using HK0 Hnw Hwin Hbuf HH HM HOK buf HCONST HCODE cH cM.
    pose proof KL as HKL. pose proof (u64_range s) as Hs. pose proof (u64_range base) as Hbr.
    induction i as [|i IH]; intros regs ret j Hret H1 H10 H11 H12 Hj Hi.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec ((U s + (j + 1)) mod 8) 0) as [Hal|Hal].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 60) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (j + 1) /\ keeps_cs regs r)).
        * wd_eexists. split.
          -- an Fo28 D_f5950.                    (* [comment removed for export] *)
             an Fo32 D_f5954.                    (* [comment removed for export] *)
             ab_tk Fo36 D_f5958
               ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); rewrite ?at_addi; rewrite andi7_u by lia; unorm; apply Z.eqb_eq; exact Hal).  (* [comment removed for export] *)
             wd_refl.
          -- post.
        * cbv beta. intros r1 (R1 & R10 & R12 & KC).
          destruct (a_entry r1 ret (j + 1)%Z Hret R1 R10 R12 ltac:(lia) Hal) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 128) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = at_ s K /\ keeps_cs regs r)).
        * wd_eexists. split.
          -- an Fo28 D_f5950.                    (* [comment removed for export] *)
             an Fo32 D_f5954.                    (* [comment removed for export] *)
             ab_ft Fo36 D_f5958
               ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); rewrite ?at_addi; rewrite andi7_u by lia; unorm; apply Z.eqb_neq; exact Hal).  (* [comment removed for export] *)
             mlbu Fo40 D_f595c (j + 1)%Z.           (* [comment removed for export] *)
             an Fo44 D_f5960.                    (* [comment removed for export] *)
             an Fo48 D_f5964.                    (* [comment removed for export] *)
             ab_ft Fo52 D_f5968 ltac:(condb).    (* [comment removed for export] *)
             an Fo56 D_f596c.                    (* [comment removed for export] *)
             wd_refl.
          -- post.
        * cbv beta. intros r1 (R1 & R10 & R11 & KC).
          destruct (t_ret r1 ret Hret R1 R10 R11) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    - destruct (Z.eq_dec ((U s + (j + 1)) mod 8) 0) as [Hal|Hal].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 60) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s (j + 1) /\ keeps_cs regs r)).
        * wd_eexists. split.
          -- an Fo28 D_f5950.
             an Fo32 D_f5954.
             ab_tk Fo36 D_f5958
               ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); rewrite ?at_addi; rewrite andi7_u by lia; unorm; apply Z.eqb_eq; exact Hal).
             wd_refl.
          -- post.
        * cbv beta. intros r1 (R1 & R10 & R12 & KC).
          destruct (a_entry r1 ret (j + 1)%Z Hret R1 R10 R12 ltac:(lia) Hal) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 28) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = at_ s (j + 1) /\ getr r 12 = at_ s (j + 1 + 1)
                           /\ keeps_cs regs r)).
        * wd_eexists. split.
          -- an Fo28 D_f5950.
             an Fo32 D_f5954.
             ab_ft Fo36 D_f5958
               ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); rewrite ?at_addi; rewrite andi7_u by lia; unorm; apply Z.eqb_neq; exact Hal).
             mlbu Fo40 D_f595c (j + 1)%Z.           (* [comment removed for export] *)
             an Fo44 D_f5960.
             an Fo48 D_f5964.
             ab_tk Fo52 D_f5968 ltac:(condb).    (* [comment removed for export] *)
             wd_refl.
          -- post.
        * cbv beta. intros r1 (R1 & R10 & R11 & R12 & KC).
          destruct (IH r1 ret (j + 1)%Z Hret R1 R10 R11 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma strlen_run0 : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s ->
    exists regs',
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ keeps_cs regs regs'.
  Proof using HK0 Hnw Hwin Hbuf HH HM HOK buf HCONST HCODE cH cM.
    intros regs ret Hret H1 H10.
    pose proof KL as HKL. pose proof (u64_range s) as Hs. pose proof (u64_range base) as Hbr.
    rewrite <- (at_0 s) in H10.
    pose proof (Z.mod_pos_bound (U s) 8 ltac:(lia)) as HMd.
    destruct (Z.eq_dec (U s mod 8) 0) as [Hal|Hal].
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 60) mem rom)
               (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 12 = at_ s 0 /\ keeps_cs regs r)).
      + wd_eexists. split.
        * an Fo0 D_f5934.                        (* [comment removed for export] *)
          an Fo4 D_f5938.                        (* [comment removed for export] *)
          ab_tk Fo8 D_f593c
            ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); rewrite ?at_add_0_r, andi7_u0; unorm; apply Z.eqb_eq; exact Hal).
          wd_refl.
        * post; rewrite ?at_0; reflexivity.
      + cbv beta. intros r1 (R1 & R10 & R12 & KC).
        destruct (a_entry r1 ret 0 Hret R1 R10 R12 ltac:(lia) ltac:(rewrite Z.add_0_r; exact Hal)) as (r2 & RUN & A10 & K2).
        exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
    - destruct (Z.eq_dec K 0) as [K0|K0].
      + (* [comment removed for export] *)
        wd_eexists. split.
        * an Fo0 D_f5934.
          an Fo4 D_f5938.
          ab_ft Fo8 D_f593c
            ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); rewrite ?at_add_0_r, andi7_u0; unorm; apply Z.eqb_neq; exact Hal).
          mlbu Fo12 D_f5940 K.                       (* [comment removed for export] *)
          ab_tk Fo16 D_f5944 ltac:(condb).       (* [comment removed for export] *)
          an Fo136 D_f59bc.                      (* [comment removed for export] *)
          aret Fo140 D_f59c0 ret.
          wd_refl.
        * post; rewrite ?at_0; try reflexivity. rewrite K0. (lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end). f_equal. lia.
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 28) mem rom)
                 (fun r => getr r 1 = ret /\ getr r 10 = s /\ getr r 11 = at_ s 0 /\ getr r 12 = at_ s (0 + 1)
                           /\ keeps_cs regs r)).
        * wd_eexists. split.
          -- an Fo0 D_f5934.
             an Fo4 D_f5938.
             ab_ft Fo8 D_f593c
               ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); rewrite ?at_add_0_r, andi7_u0; unorm; apply Z.eqb_neq; exact Hal).
             mlbu Fo12 D_f5940 (K - K)%Z.           (* [comment removed for export] *)
             ab_ft Fo16 D_f5944 ltac:(condb).    (* [comment removed for export] *)
             an Fo20 D_f5948.                    (* [comment removed for export] *)
             an Fo24 D_f594c.                    (* [comment removed for export] *)
             wd_refl.
          -- post; rewrite ?at_0; try reflexivity; f_equal; lia.
        * cbv beta. intros r1 (R1 & R10 & R11 & R12 & KC).
          destruct (h_loop (Z.to_nat (K - 1)) r1 ret 0 Hret R1 R10 R11 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & A10 & K2).
          exists r2. split; [exact RUN | split; [exact A10 | eapply keeps_cs_trans; eassumption]].
  Qed.
End STRLEN.

(* [comment removed for export] *)
Record strlen_tab : Type := STRT { st_base : word; st_cM : Z; st_cH : Z }.
Record strlen_tab_ok (segs : list Segment) (t : strlen_tab) : Prop := STRTOK {
  sto_code : code_ato segs (st_base t) 0 mstrlen_words;
  sto_consts : sl_consts segs (st_base t) (st_cM t) (st_cH t) }.

Theorem strlen_run : forall segs t, strlen_tab_ok segs t ->
  forall mem (s : word) buf K rom regs (ret : word),
  strlH segs mem s buf K ->
  rdn segs mem (Z_to_bv 64 (st_cM t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 Mc)) ->
  rdn segs mem (Z_to_bv 64 (st_cH t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 Hc)) ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 10 = s ->
  exists regs',
    msteps segs (mkst regs (st_base t) mem rom) (mkst regs' ret mem rom)
    /\ getr regs' 10 = Z_to_bv 64 K /\ keeps_cs regs regs'.
Proof using.
  intros segs t [T1 T2] mem s buf K rom regs ret HOK HM HH Hret H1 H10.
  rewrite <- (at_0 (st_base t)).
  exact (strlen_run0 segs (st_base t) (st_cM t) (st_cH t) T1 T2 mem s buf K rom HOK HM HH regs ret Hret H1 H10).
Qed.
End FPGen1.
