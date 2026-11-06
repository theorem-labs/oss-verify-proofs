(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
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
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Definition m2s_words : list (option (bv 32)) :=
  [
   None; None; Some W_6fb0c; Some W_6fb10; Some W_6fb14; Some W_6fb18; Some W_6fb1c; Some W_6fb20; None; None;
   None; None; Some W_6fb34; Some W_6fb38; Some W_6fb3c; Some W_6fb40; Some W_6fb44; None; None; Some W_6fb50;
   Some W_6fb54; Some W_6fb58; Some W_6fb5c; Some W_6fb60; Some W_6fb64; Some W_6fb68; Some W_6fb6c
  ]%list.


Definition m2s_clob : list reg := [5; 10; 11; 12; 13; 14; 15; 16; 17].

Record m2s_tab : Type := M2ST { mt_base : word; mt_g_shoff : Z; mt_p_shoff : Z; mt_g_midbeg : Z; mt_p_midbeg : Z;
  mt_g_midend : Z; mt_p_midend : Z; mt_g_hiend : Z; mt_p_hiend : Z }.

Record m2s_tab_ok (segs : list Segment) (t : m2s_tab) : Prop := M2STOK {
  mto_code : code_ato segs (mt_base t) 0 m2s_words;
  mto_g0 : gload segs (mt_base t) 0 11 (mt_g_shoff t);
  mto_g32 : gload segs (mt_base t) 32 13 (mt_g_midbeg t);
  mto_g40 : gload segs (mt_base t) 40 14 (mt_g_midend t);
  mto_g68 : gload segs (mt_base t) 68 14 (mt_g_hiend t) }.

Definition m2s_cells (t : m2s_tab) : list Z :=
  [mt_g_shoff t; mt_p_shoff t; mt_g_midbeg t; mt_p_midbeg t; mt_g_midend t; mt_p_midend t; mt_g_hiend t; mt_p_hiend t]%Z.

(* [comment removed for export] *)
Record m2sH (segs : list Segment) (t : m2s_tab) (mem : word -> option byte) (p : word) (midend : word) : Prop := M2SH {
  mh_g_shoff : rdn segs mem (Z_to_bv 64 (mt_g_shoff t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_shoff t)));
  mh_shoff : rdn segs mem (Z_to_bv 64 (mt_p_shoff t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fff8000));
  mh_g_midbeg : rdn segs mem (Z_to_bv 64 (mt_g_midbeg t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_midbeg t)));
  mh_midbeg : rdn segs mem (Z_to_bv 64 (mt_p_midbeg t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  mh_g_midend : rdn segs mem (Z_to_bv 64 (mt_g_midend t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_midend t)));
  mh_midend : rdn segs mem (Z_to_bv 64 (mt_p_midend t)) 8 = Some (word_to_le_bytes 8 midend);
  mh_g_hiend : rdn segs mem (Z_to_bv 64 (mt_g_hiend t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (mt_p_hiend t)));
  mh_hiend : rdn segs mem (Z_to_bv 64 (mt_p_hiend t)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff));
  mh_cells : Forall (fun c => 0 <= c /\ c + 8 <= 2 ^ 64)%Z (m2s_cells t);
  mh_lo : (0x10007fff8000 <= bv_unsigned p \/ bv_unsigned p <= 0x7fff7fff)%Z;   (* [comment removed for export] *)
  mh_hi : (bv_unsigned p <= 0x7fffffffffff)%Z }.

Section M2S.
  Variable segs : list Segment.
  Variable base : word.
  Variables g_shoff g_midbeg g_midend g_hiend : Z.
  Hypothesis HCODE : code_ato segs base 0 m2s_words.
  Hypothesis G0 : gload segs base 0 11 g_shoff.
  Hypothesis G32 : gload segs base 32 13 g_midbeg.
  Hypothesis G40 : gload segs base 40 14 g_midend.
  Hypothesis G68 : gload segs base 68 14 g_hiend.

  Lemma Fo8 : fetch_word segs (at_ base 8) = Some W_6fb0c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 2 _ HCODE eq_refl). Qed.
  Lemma Fo12 : fetch_word segs (at_ base 12) = Some W_6fb10.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 3 _ HCODE eq_refl). Qed.
  Lemma Fo16 : fetch_word segs (at_ base 16) = Some W_6fb14.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 4 _ HCODE eq_refl). Qed.
  Lemma Fo20 : fetch_word segs (at_ base 20) = Some W_6fb18.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 5 _ HCODE eq_refl). Qed.
  Lemma Fo24 : fetch_word segs (at_ base 24) = Some W_6fb1c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 6 _ HCODE eq_refl). Qed.
  Lemma Fo28 : fetch_word segs (at_ base 28) = Some W_6fb20.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 7 _ HCODE eq_refl). Qed.
  Lemma Fo48 : fetch_word segs (at_ base 48) = Some W_6fb34.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 12 _ HCODE eq_refl). Qed.
  Lemma Fo52 : fetch_word segs (at_ base 52) = Some W_6fb38.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 13 _ HCODE eq_refl). Qed.
  Lemma Fo56 : fetch_word segs (at_ base 56) = Some W_6fb3c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 14 _ HCODE eq_refl). Qed.
  Lemma Fo60 : fetch_word segs (at_ base 60) = Some W_6fb40.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 15 _ HCODE eq_refl). Qed.
  Lemma Fo64 : fetch_word segs (at_ base 64) = Some W_6fb44.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 16 _ HCODE eq_refl). Qed.
  Lemma Fo76 : fetch_word segs (at_ base 76) = Some W_6fb50.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 19 _ HCODE eq_refl). Qed.
  Lemma Fo80 : fetch_word segs (at_ base 80) = Some W_6fb54.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 20 _ HCODE eq_refl). Qed.
  Lemma Fo84 : fetch_word segs (at_ base 84) = Some W_6fb58.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 21 _ HCODE eq_refl). Qed.
  Lemma Fo88 : fetch_word segs (at_ base 88) = Some W_6fb5c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 22 _ HCODE eq_refl). Qed.
  Lemma Fo92 : fetch_word segs (at_ base 92) = Some W_6fb60.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 23 _ HCODE eq_refl). Qed.
  Lemma Fo96 : fetch_word segs (at_ base 96) = Some W_6fb64.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 24 _ HCODE eq_refl). Qed.
  Lemma Fo100 : fetch_word segs (at_ base 100) = Some W_6fb68.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 25 _ HCODE eq_refl). Qed.
  Lemma Fo104 : fetch_word segs (at_ base 104) = Some W_6fb6c.   (* [comment removed for export] *)
  Proof using HCODE. exact (code_ato_get segs base 0 m2s_words 26 _ HCODE eq_refl). Qed.


  (* [comment removed for export] *) Ltac gl G Hr := eapply msteps_trans; [ eapply G; exact Hr | ]; zlit_at.
  Theorem m2s_run0 : forall (p_shoff p_midbeg p_midend p_hiend : Z) mem rom (p midend ra : word) regs,
    rdn segs mem (Z_to_bv 64 g_shoff) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 p_shoff)) ->
    rdn segs mem (Z_to_bv 64 p_shoff) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fff8000)) ->
    rdn segs mem (Z_to_bv 64 g_midbeg) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 p_midbeg)) ->
    rdn segs mem (Z_to_bv 64 p_midbeg) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    rdn segs mem (Z_to_bv 64 g_midend) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 p_midend)) ->
    rdn segs mem (Z_to_bv 64 p_midend) 8 = Some (word_to_le_bytes 8 midend) ->
    rdn segs mem (Z_to_bv 64 g_hiend) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 p_hiend)) ->
    rdn segs mem (Z_to_bv 64 p_hiend) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7fffffffffff)) ->
    (0 <= p_shoff /\ p_shoff + 8 <= 2 ^ 64)%Z -> (0 <= p_midbeg /\ p_midbeg + 8 <= 2 ^ 64)%Z ->
    (0 <= p_midend /\ p_midend + 8 <= 2 ^ 64)%Z -> (0 <= p_hiend /\ p_hiend + 8 <= 2 ^ 64)%Z ->
    (0x10007fff8000 <= bv_unsigned p \/ bv_unsigned p <= 0x7fff7fff)%Z -> (bv_unsigned p <= 0x7fffffffffff)%Z ->
    getr regs 10 = p -> getr regs 1 = ra -> ret_ok ra ->
    exists r,
      msteps segs (mkst regs (at_ base 0) mem rom) (mkst r ra mem rom)
      /\ getr r 10 = Z_to_bv 64 (bv_unsigned p / 8 + 0x7fff8000)
      /\ regs_agree (fun r => In r m2s_clob) regs r.
  Proof using G68 G40 G32 G0 HCODE.
    intros p_shoff p_midbeg p_midend p_hiend mem rom p midend ra regs R1 R2 R3 R4 R5 R6 R7 R8 B1 B2 B3 B4 Hrng Hhi H10 H1 Hret.
    pose proof (u64_range p) as Hp.
    Ltac cld0 F D vv Hr :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Hr | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
    destruct Hrng as [Hlo | Hlow].
    2:{ (* [comment removed for export] *)
      assert (Hd : (0 <= bv_unsigned p / 8 < 2 ^ 28)%Z)
        by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      wd_eexists. split; [|split].
      - gl G0 R1.                                          (* [comment removed for export] *)
        cld0 Fo8 D_6fb0c (Z_to_bv 64 0x7fff8000) R2.       (* [comment removed for export] *)
        an Fo12 D_6fb10.                                   (* [comment removed for export] *)
        an Fo16 D_6fb14.                                   (* [comment removed for export] *)
        an Fo20 D_6fb18.                                   (* [comment removed for export] *)
        an Fo24 D_6fb1c.                                   (* [comment removed for export] *)
        ab_tk Fo28 D_6fb20 ltac:(condz).                 (* [comment removed for export] *)
        av Fo96 D_6fb64 (Z_to_bv 64 (bv_unsigned p / 8)) ltac:(apply v_srli_3).   (* [comment removed for export] *)
        av Fo100 D_6fb68 (Z_to_bv 64 (bv_unsigned p / 8 + 0x7fff8000)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).  (* [comment removed for export] *)
        aret Fo104 D_6fb6c ra.                             (* [comment removed for export] *)
        wd_refl.
      - gres. reflexivity.
      - (lazymatch goal with |- ?G => let G' := eval unfold m2s_clob in G in change_no_check G' end). solve_regs_agree. }
    assert (Hd : (2 ^ 40 <= bv_unsigned p / 8 < 2 ^ 44)%Z)
      by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]).
    Ltac cld F D vv Hr :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Hr | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
    wd_eexists. split; [|split].
    - gl G0 R1.                                          (* [comment removed for export] *)
      cld Fo8 D_6fb0c (Z_to_bv 64 0x7fff8000) R2.        (* [comment removed for export] *)
      an Fo12 D_6fb10.                                   (* [comment removed for export] *)
      an Fo16 D_6fb14.                                   (* [comment removed for export] *)
      an Fo20 D_6fb18.                                   (* [comment removed for export] *)
      an Fo24 D_6fb1c.                                   (* [comment removed for export] *)
      ab_ft Fo28 D_6fb20 ltac:(condz).                 (* [comment removed for export] *)
      gl G32 R3.                                         (* [comment removed for export] *)
      gl G40 R5.                                         (* [comment removed for export] *)
      cld Fo48 D_6fb34 (Z_to_bv 64 0) R4.                (* [comment removed for export] *)
      cld Fo52 D_6fb38 midend R6.                        (* [comment removed for export] *)
      an Fo56 D_6fb3c.                                   (* [comment removed for export] *)
      ab_tk Fo60 D_6fb40 ltac:(condz).                 (* [comment removed for export] *)
      gl G68 R7.                                         (* [comment removed for export] *)
      cld Fo76 D_6fb50 (Z_to_bv 64 0x7fffffffffff) R8.   (* [comment removed for export] *)
      an Fo80 D_6fb54.                                   (* [comment removed for export] *)
      an Fo84 D_6fb58.                                   (* [comment removed for export] *)
      ab_ft Fo88 D_6fb5c ltac:(condz).                 (* [comment removed for export] *)
      ab_ft Fo92 D_6fb60 ltac:(condz).                 (* [comment removed for export] *)
      av Fo96 D_6fb64 (Z_to_bv 64 (bv_unsigned p / 8)) ltac:(apply v_srli_3).   (* [comment removed for export] *)
      av Fo100 D_6fb68 (Z_to_bv 64 (bv_unsigned p / 8 + 0x7fff8000)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; f_equal; lia).  (* [comment removed for export] *)
      aret Fo104 D_6fb6c ra.                             (* [comment removed for export] *)
      wd_refl.
    - gres. reflexivity.
    - (lazymatch goal with |- ?G => let G' := eval unfold m2s_clob in G in change_no_check G' end). solve_regs_agree.
  Qed.
End M2S.

Theorem m2s_run : forall segs t, m2s_tab_ok segs t ->
  forall mem rom (p midend ra : word) regs,
  m2sH segs t mem p midend ->
  getr regs 10 = p -> getr regs 1 = ra -> ret_ok ra ->
  exists r,
    msteps segs (mkst regs (mt_base t) mem rom) (mkst r ra mem rom)
    /\ getr r 10 = Z_to_bv 64 (bv_unsigned p / 8 + 0x7fff8000)
    /\ regs_agree (fun r => In r m2s_clob) regs r.
Proof using.
  intros segs t [TC G0 G32 G40 G68] mem rom p midend ra regs [R1 R2 R3 R4 R5 R6 R7 R8 HC Hlo Hhi] H10 H1 Hret.
  unfold m2s_cells in HC.
  repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
  rewrite <- (at_0 (mt_base t)).
  eapply (m2s_run0 segs (mt_base t) _ _ _ _ TC G0 G32 G40 G68 (mt_p_shoff t) (mt_p_midbeg t) (mt_p_midend t) (mt_p_hiend t)
            mem rom p midend ra regs); try eassumption.
Qed.

(* [comment removed for export] *)
  (* [comment removed for export] *)
End FPGen1.
 Ltac rr Hx := rewrite rdn_mrestrict; [ assumption | wd_ulia_c | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); exact Hx ].
Section FPGen2.
Context {fx : FPState}.

End FPGen2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
