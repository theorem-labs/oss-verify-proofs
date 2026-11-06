(* reac_code_emit on image A: the contract's Post from the FILE at the end of the walk (`em_apost`, consumed by
   lib/A/Prog/reac_code_emitExit.v).

   reac_code_emit_apost quantifies over EVERY format, piece list, argument list, text and pending count the Pre
   admits at the entry memory. They are all the walk's own (em_base's witnesses):
   - the format: a C string at one address is one byte list (em_acstr_unique), and a format that parses holds
     bytes 1..255 only (LinkWalkMkFmt.v pf_parse_bytes), where `map (Z_to_bv 8)` is injective (em_map_inj);
   - the pieces: pf_parse is a function;
   - the arguments: the pieces consume the four vararg registers in order, and each consumed register fixes its
     argument (a %d by its value modulo 2^32 inside the int range, a %s by its C string) (em_args_unique);
   - the text: pf_text is a function;
   - the pending count: LinkWalkMkFile.v amf_k_unique.
   The FILE at the end is then the contract's amemfile_k by LinkWalkMkFile.v amemfile_k_of_amf_k.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI04 YI16 YM05 YG0v YG0f YG0d YG0n YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable LinkSyms LinkList LinkAddr LinkPa.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkMkFile LinkWalkMkFmt.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_decide_c reac_code_emit_c reac_code_emitDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Module PFC := printf_facts_c.

Section u.
Variable segs : list Segment.

(* a C string at one address is one byte list *)
Lemma em_acstr_unique : forall (m : word -> option byte) p (s1 s2 : list byte),
  acstr_at segs m p s1 -> acstr_at segs m p s2 -> s1 = s2.
Proof.
  intros m p s1 s2 ((_ & _ & H1) & N1) ((_ & _ & H2) & N2).
  assert (Hl : length s1 = length s2).
  { destruct (Nat.lt_trichotomy (length s1) (length s2)) as [Hlt | [Heq | Hgt]]; [exfalso | exact Heq | exfalso].
    - pose proof (H1 (length s1) ltac:(rewrite length_app; cbn [length]; lia)) as A.
      pose proof (H2 (length s1) ltac:(rewrite length_app; cbn [length]; lia)) as B.
      rewrite nth_error_app2 in A by lia. rewrite Nat.sub_diag in A. cbn [nth_error] in A.
      rewrite nth_error_app1 in B by lia. rewrite A in B.
      apply N2. symmetry in B. exact (nth_error_In _ _ B).
    - pose proof (H2 (length s2) ltac:(rewrite length_app; cbn [length]; lia)) as A.
      pose proof (H1 (length s2) ltac:(rewrite length_app; cbn [length]; lia)) as B.
      rewrite nth_error_app2 in A by lia. rewrite Nat.sub_diag in A. cbn [nth_error] in A.
      rewrite nth_error_app1 in B by lia. rewrite A in B.
      apply N1. symmetry in B. exact (nth_error_In _ _ B). }
  apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length s1)) as [Hi | Hi].
  - pose proof (H1 i ltac:(rewrite length_app; cbn [length]; lia)) as A.
    pose proof (H2 i ltac:(rewrite length_app; cbn [length]; lia)) as B.
    rewrite nth_error_app1 in A by lia. rewrite nth_error_app1 in B by lia. congruence.
  - rewrite (proj2 (nth_error_None s1 i)) by lia. rewrite (proj2 (nth_error_None s2 i)) by lia. reflexivity.
Qed.

End u.

(* bytes 0..255 are what Z_to_bv 8 keeps *)
Lemma em_map_inj : forall l1 l2 : list Z,
  Forall (fun c => 0 <= c < 256) l1 -> Forall (fun c => 0 <= c < 256) l2 ->
  map (Z_to_bv 8) l1 = map (Z_to_bv 8) l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] H1 H2 H; cbn [map] in H; try discriminate H; [reflexivity|].
  assert (Hab : Z_to_bv 8 a = Z_to_bv 8 b) by congruence.
  assert (Hl : map (Z_to_bv 8) l1 = map (Z_to_bv 8) l2) by congruence.
  inversion H1 as [|? ? Ha H1']; subst. inversion H2 as [|? ? Hb H2']; subst.
  f_equal; [|exact (IH l2 H1' H2' Hl)].
  assert (E : bv_unsigned (Z_to_bv 8 a) = bv_unsigned (Z_to_bv 8 b)) by (rewrite Hab; reflexivity).
  rewrite !Z_to_bv_unsigned in E. unfold bv_wrap, bv_modulus in E. change (2 ^ Z.of_N 8) with 256 in E.
  rewrite !Z.mod_small in E by lia. exact E.
Qed.

Lemma em_rng_of_parse : forall f ps, PFC.pf_parse f = Some ps -> Forall (fun c => 0 <= c < 256) f.
Proof.
  intros f ps H. eapply Forall_impl; [|exact (pf_parse_bytes f ps H)]. intros c Hc. cbv beta in Hc. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.

(* the pieces consume the vararg registers in order, and each consumed register fixes its argument *)
Lemma em_args_unique : forall (regs : bvmap 5 word) K (m : word -> option byte) f ps a1 a2 rs T1 T2,
  Forall apf_link_piece ps ->
  PFC.pf_text ps a1 = Some T1 -> PFC.pf_text ps a2 = Some T2 ->
  apf_args_ok pa_segs regs K m f rs a1 -> apf_args_ok pa_segs regs K m f rs a2 -> a1 = a2.
Proof.
  intros regs K m f ps. induction ps as [|p ps IH]; intros a1 a2 rs T1 T2 HK H1 H2 A1 A2.
  - destruct a1; [|discriminate H1]. destruct a2; [reflexivity | discriminate H2].
  - inversion HK as [|? ? Hp HK']; subst.
    destruct p as [b| | | | | | |]; cbn [apf_link_piece] in Hp; try contradiction.
    + cbn [PFC.pf_text] in H1, H2.
      destruct (PFC.pf_text ps a1) as [t1|] eqn:E1; [|discriminate H1].
      destruct (PFC.pf_text ps a2) as [t2|] eqn:E2; [|discriminate H2].
      exact (IH a1 a2 rs t1 t2 HK' E1 E2 A1 A2).
    + destruct a1 as [|[v1|u1|s1] a1]; cbn [PFC.pf_text] in H1; try discriminate H1.
      destruct a2 as [|[v2|u2|s2] a2]; cbn [PFC.pf_text] in H2; try discriminate H2.
      destruct (PFC.pf_text ps a1) as [t1|] eqn:E1; [|discriminate H1].
      destruct (PFC.pf_text ps a2) as [t2|] eqn:E2; [|discriminate H2].
      destruct rs as [|r rs]; [destruct A1|].
      destruct A1 as ((V1a & V1b) & A1). destruct A2 as ((V2a & V2b) & A2).
      assert (Ev : v1 = v2).
      { rewrite V1b in V2b. pose proof (Z.mod_pos_bound v1 (2 ^ 32) ltac:(lia)).
        pose proof (Z.mod_pos_bound v2 (2 ^ 32) ltac:(lia)). lia. }
      subst v2. f_equal. exact (IH a1 a2 rs t1 t2 HK' E1 E2 A1 A2).
    + destruct a1 as [|[v1|u1|s1] a1]; cbn [PFC.pf_text] in H1; try discriminate H1.
      destruct a2 as [|[v2|u2|s2] a2]; cbn [PFC.pf_text] in H2; try discriminate H2.
      destruct (PFC.pf_text ps a1) as [t1|] eqn:E1; [|discriminate H1].
      destruct (PFC.pf_text ps a2) as [t2|] eqn:E2; [|discriminate H2].
      destruct rs as [|r rs]; [destruct A1|].
      destruct A1 as ((S1r & S1c & _) & A1). destruct A2 as ((S2r & S2c & _) & A2).
      pose proof (em_acstr_unique pa_segs m _ _ _ S1c S2c) as Es.
      apply em_map_inj in Es;
        [| eapply Forall_impl; [|exact S1r]; intros c Hc; cbv beta in Hc; lia
         | eapply Forall_impl; [|exact S2r]; intros c Hc; cbv beta in Hc; lia].
      subst s2. f_equal. exact (IH a1 a2 rs t1 t2 HK' E1 E2 A1 A2).
Qed.

Lemma em_apost : forall cx (W2 : world pa_segs) mem2 regs2,
  em_base SK B cx ->
  amf_k pa_segs link_amf (rdW W2 mem2) (e_f cx) (e_kf cx + EMIT_HEAD + Z.of_nat (length (e_T cx))) ->
  awrange pa_segs (rdW W2 mem2) (e_f cx) AMF_BLOCK ->
  awrange pa_segs (rdW W2 mem2) LA_G_SAID SAID_SIZE ->
  reac_code_emit_apost pa_segs (e_regs cx) (e_m cx) regs2 (rdW W2 mem2).
Proof.
  intros cx W2 mem2 regs2 HB HA HW HG fmt ps args T k HF HK.
  destruct HB as (_ & _ & _ & _ & _ & HMF & _ & _ & HFMT & _).
  destruct HFMT as (C1 & _ & _ & _ & P1 & _ & K1 & T1 & A1).
  destruct HF as (C2 & _ & _ & _ & P2 & _ & _ & T2 & A2).
  pose proof (em_acstr_unique pa_segs _ _ _ _ C1 C2) as Hm.
  apply em_map_inj in Hm; [| exact (em_rng_of_parse _ _ P1) | exact (em_rng_of_parse _ _ P2)].
  rewrite <- Hm in P2. rewrite P1 in P2. injection P2 as <-.
  pose proof (em_args_unique _ _ _ _ _ _ _ _ _ _ K1 T1 T2 A1 A2) as <-.
  rewrite T1 in T2. injection T2 as <-.
  destruct (amf_k_of_amemfile_k pa_segs _ _ _ HMF) as (H1 & _ & _).
  destruct (amf_k_of_amemfile_k pa_segs _ _ _ HK) as (H2 & _ & _).
  pose proof (amf_k_unique pa_segs link_amf _ _ _ _ H1 H2) as <-.
  exact (amemfile_k_of_amf_k pa_segs (rdW W2 mem2) (e_f cx) _ HA HW HG).
Qed.

About em_apost.
Print Assumptions em_apost.

End b.
End a.
