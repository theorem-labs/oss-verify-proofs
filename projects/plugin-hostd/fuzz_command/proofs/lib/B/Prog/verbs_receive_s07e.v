(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the recorder-call kit of segment S07 (route add, B 0x8d2e8) of the walk of
   verbs_receive on the ASan+UBSan build of plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_iface.v, vr_s07_stmt): the
   live blocks after a recorder call (perm_text07, perm_notext07), the recorder kept by a call whose footprint is
   empty (recj07), the footprints of sup_add and descriptors_add (fp_add07, fp_desc07), a word of the copy handed
   to a recorder function (tok_blk07), the sign test `bltz` (lt0_07), the text sup_add returns (add_text07). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI00 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_add_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_s07a verbs_receive_s07b verbs_receive_s07c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module PV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec.Verbs.

(* the live blocks after a recorder call that returns a text block x0 (sup_add) or none (descriptors_add): the
   recorder's new set O2, the text, and the walk's blocks T that the call kept *)
Lemma perm_text07 : forall (bl bl2 O O2 T : list (Z * Z)) (x0 : Z * Z),
List.NoDup bl2 -> Permutation bl (O ++ T) -> List.NoDup (O ++ T) -> List.NoDup O2 ->
(forall x, In x O2 -> In x O \/ ~ In x bl) ->
(forall x, In x bl2 -> (In x bl /\ ~ In x O) \/ In x O2 \/ x = x0) ->
(forall x, In x bl -> ~ In x O -> In x bl2) ->
In x0 bl2 -> (forall x, In x bl -> ~ In x O -> x <> x0) -> ~ In x0 O2 ->
(forall x, In x O2 -> In x bl2) ->
Permutation bl2 (O2 ++ x0 :: T).
Proof.
intros bl bl2 O O2 T x0 Hnd2 HP HndOT HndO2 HO2 Hcl Hkeep Hx0 Hx0n Hx0O HO2b.
destruct (nodup_app07 _ _ HndOT) as (HndO & HndT & HdOT).
assert (HT : forall x, In x T -> In x bl /\ ~ In x O).
{ intros x Hx. split; [apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hx|].
  intros HxO. exact (HdOT x HxO Hx). }
apply perm_of_mem07; [exact Hnd2 | exact HndO2 | | |].
- apply List.NoDup_cons; [|exact HndT]. intros Hin. destruct (HT _ Hin) as [H1 H2]. exact (Hx0n x0 H1 H2 eq_refl).
- intros x Hx [<- | Hx2]; [exact (Hx0O Hx)|]. destruct (HT _ Hx2) as [H1 H2].
  destruct (HO2 x Hx) as [H3|H3]; [exact (H2 H3) | exact (H3 H1)].
- intros x. split.
  + intros Hx. destruct (Hcl x Hx) as [(H1 & H2) | [H1 | H1]].
    * right. right. pose proof (Permutation_in _ HP H1) as H3. apply in_app_or in H3 as [H3|H3]; [contradiction | exact H3].
    * left. exact H1.
    * right. left. symmetry. exact H1.
  + intros [Hx | [<- | Hx]]; [exact (HO2b x Hx) | exact Hx0 |]. destruct (HT _ Hx) as [H1 H2]. exact (Hkeep x H1 H2).
Qed.

Lemma perm_notext07 : forall (bl bl2 O O2 T : list (Z * Z)),
List.NoDup bl2 -> Permutation bl (O ++ T) -> List.NoDup (O ++ T) -> List.NoDup O2 ->
(forall x, In x O2 -> In x O \/ ~ In x bl) ->
(forall x, In x bl2 -> (In x bl /\ ~ In x O) \/ In x O2) ->
(forall x, In x bl -> ~ In x O -> In x bl2) ->
(forall x, In x O2 -> In x bl2) ->
Permutation bl2 (O2 ++ T).
Proof.
intros bl bl2 O O2 T Hnd2 HP HndOT HndO2 HO2 Hcl Hkeep HO2b.
destruct (nodup_app07 _ _ HndOT) as (HndO & HndT & HdOT).
assert (HT : forall x, In x T -> In x bl /\ ~ In x O).
{ intros x Hx. split; [apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hx|].
  intros HxO. exact (HdOT x HxO Hx). }
apply perm_of_mem07; [exact Hnd2 | exact HndO2 | exact HndT | |].
- intros x Hx Hx2. destruct (HT _ Hx2) as [H1 H2].
  destruct (HO2 x Hx) as [H3|H3]; [exact (H2 H3) | exact (H3 H1)].
- intros x. split.
  + intros Hx. destruct (Hcl x Hx) as [(H1 & H2) | H1].
    * right. pose proof (Permutation_in _ HP H1) as H3. apply in_app_or in H3 as [H3|H3]; [contradiction | exact H3].
    * left. exact H1.
  + intros [Hx | Hx]; [exact (HO2b x Hx)|]. destruct (HT _ Hx) as [H1 H2]. exact (Hkeep x H1 H2).
Qed.

(* the signed test of `bltz` on a register holding v *)
Lemma lt0_07 : forall E n v, ew E n = Z_to_bv 64 v -> -2 ^ 63 <= v < 2 ^ 63 ->
branch_taken BC_LT (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v <? 0).
Proof.
intros E n v Hn Hv. cbn [branch_taken]. rewrite bv_lts_signed.
change (bv_signed (sv_denot E (SOff n 0))) with (Sg E (SOff n 0)). change (bv_signed (sv_denot E (SLit 0))) with (Sg E (SLit 0)).
rewrite S_SOff, S_SLit, Hn, Z.add_0_r, Z_to_bv_unsigned, bv_swrap_wrap.
rewrite !swrap64_id by (unfold half64; lia). reflexivity.
Qed.

Lemma swrap32_range07 : forall z, -2 ^ 31 <= bv_swrap 32 z < 2 ^ 31.
Proof.
intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
assert (E : 2 ^ Z.of_N 32 = 4294967296) by reflexivity. rewrite E.
change (Z.div 4294967296 2) with 2147483648.
pose proof (Z.mod_pos_bound (z + 2147483648) 4294967296 ltac:(lia)). lia.
Qed.
Lemma atoi_range07 : forall s, -2 ^ 31 <= atoi_a s < 2 ^ 31.
Proof. intros s. unfold atoi_a. apply swrap32_range07. Qed.
Lemma rc_range07 : forall x, -2 ^ 31 <= reply_code_a x < 2 ^ 31.
Proof. intros x. unfold reply_code_a. destruct (list_eq_dec _ _ _); [apply atoi_range07 | lia]. Qed.

(* the text sup_add returns is resp of an int *)
Lemma add_text07 : forall R u id pl cl, -2 ^ 31 <= r_code R < 2 ^ 31 -> -2 ^ 31 <= id < 2 ^ 31 ->
(length (snd (sup_add_m R (Some u) id pl cl)) <= 16)%nat.
Proof.
intros R u id pl cl HC Hid. unfold sup_add_m. cbv zeta.
set (A := [sarg (Some u); dec id; darg pl (bstr "-"%string); darg cl (bstr "-"%string)]).
assert (E : r_code (rec_record R REC_ADD A) = r_code R) by (unfold rec_record; destruct (Nat.ltb _ _); reflexivity).
destruct (orb (id <? 0) (10000 <=? id)); [cbn [snd hand_back]; pose proof (resp_length (-1) ltac:(lia)); lia|].
destruct (negb (r_refuse (rec_record R REC_ADD A) =? 0)); cbn [snd hand_back].
- rewrite E. pose proof (resp_length (r_code R) HC). lia.
- pose proof (resp_length id Hid). lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis PROGU : vr_prog_unowned B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the footprints of sup_add and descriptors_add are g_rec, record.spill and the recorder's blocks *)
Lemma fp_add07 : forall O, fpok07 O
  ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8) ::
   (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O).
Proof.
intros O a Ha.
apply inFP_cons in Ha as [Ha|Ha]; [left; cbn [fst snd] in Ha; unfold OFF_NCALLS, A_G_REC, REC_SIZE in *; lia|].
apply inFP_cons in Ha as [Ha|Ha]; [left; cbn [fst snd] in Ha; unfold OFF_CALLS, OFF_ANSWER, A_G_REC, REC_SIZE in *; lia|].
apply inFP_cons in Ha as [Ha|Ha]; [left; cbn [fst snd] in Ha; unfold OFF_STATE, A_G_REC, REC_SIZE in *; lia|].
apply inFP_cons in Ha as [Ha|Ha]; [right; left; exact Ha|].
right; right. exact (inFP_ablocks_fp_inv O a Ha).
Qed.
Lemma fp_desc07 : forall O, fpok07 O
  ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O).
Proof.
intros O a Ha.
apply inFP_cons in Ha as [Ha|Ha]; [left; exact Ha|].
apply inFP_cons in Ha as [Ha|Ha]; [right; left; exact Ha|].
right; right. exact (inFP_ablocks_fp_inv O a Ha).
Qed.

(* the recorder over a call whose footprint is empty (sup_reply_code) *)
Lemma recj07 : forall lyc Sc W mem md ly2 S2 W2 mem2 md2 STK1 sp1 EV1 R O,
AR SEGS B lyc Sc W mem md -> rec_repA B lyc Sc (rdW W mem) R O ->
ajournal SEGS B STK1 sp1 [] lyc Sc W mem md [] ly2 S2 W2 mem2 md2 EV1 ->
(forall pn, In pn O -> In pn (ablocks B ly2 S2)) ->
rec_repA B ly2 S2 (rdW W2 mem2) R O.
Proof.
intros lyc Sc W mem md ly2 S2 W2 mem2 md2 STK1 sp1 EV1 R O HAR Hrec HJc Hsurv.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & F3 & _).
assert (Hsp : forall a, fp_spares [] a).
{ intros a. apply fp_spares_closed; [intros (r & Hr & _); destruct Hr | intros (r & Hr & _); destruct Hr]. }
apply (rec_repA_agree B lyc Sc ly2 S2 (rdW W mem) (rdW W2 mem2) R O Hrec).
- intros pn Hpn _. exact (Hsurv pn Hpn).
- intros kk Hkk. assert (G : A_G_REC <= A_G_REC + kk < A_G_REC + REC_SIZE) by lia.
  destruct (PROGU _ (inFP_PG_rec07 _ G)) as (Hi & Ho & He). exact (F3 _ Hi Ho He (Hsp _)).
- intros kk Hkk. assert (G : A_REC_SPILL <= A_REC_SPILL + kk < A_REC_SPILL + SC_SIZE) by lia.
  destruct (PROGU _ (inFP_PG_spill07 _ G)) as (Hi & Ho & He). exact (F3 _ Hi Ho He (Hsp _)).
- intros [p n] Hpn kk Hkk. cbn [fst snd] in *.
  pose proof (rec_repA_in_blocks B _ _ _ _ _ _ Hrec Hpn) as Hin.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
  apply (F2 p n kk Hin (Hsurv _ Hpn) ltac:(lia)). intros (r & Hr & _). destruct Hr.
Qed.

(* a word of the copy handed to a recorder function as a block string, none of the recorder's *)
Lemma tok_blk07 : forall e F c tp lyc Sc Wc memc mdc Rc Oc tmps j p w,
AR SEGS B lyc Sc Wc memc mdc -> vr_copy B e F c tp Wc memc ->
rec_repA B lyc Sc (rdW Wc memc) Rc Oc -> In (vr_cb e c) tmps ->
Permutation (ablocks B lyc Sc) (Oc ++ tmps ++ e_rest e) ->
nth_error tp j = Some p -> nth_error (Verbs.toks (e_D e)) j = Some w ->
in_blockA (ablocks B lyc Sc) p (Z.of_nat (length w) + 1) /\
Forall (fun qk => iv_apart p (Z.of_nat (length w) + 1) (fst qk) (snd qk)) Oc /\
astr_atR (rdW Wc memc) p w /\ Z.of_nat (length w) + 1 <= LMAX + 1 /\ 4096 <= p /\ p < 2 ^ 64 /\
Z.of_nat (length w) <= 8192.
Proof.
intros e F c tp lyc Sc Wc memc mdc Rc Oc tmps j p w HAR Hcopy Hrec Hcbin Hperm Hjp Hjw.
pose proof Hcopy as [Hcf Hta]. destruct Hta as (Htk8 & Htkl & Htkp & Htkw).
destruct (Htkw j p w Hjp Hjw) as (Hstr & Hwl & Hc1 & Hc2).
assert (Hcbin' : In (vr_cb e c) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; apply in_or_app; left; exact Hcbin).
assert (Hcbno : ~ In (vr_cb e c) Oc) by exact (perm_tmp_notin B _ _ _ _ _ _ _ _ _ HAR Hperm Hcbin).
unfold vr_cb in Hcbin', Hcbno. cbn [fst snd] in *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcbin') as (_ & Hc4096 & Hcc & _ & _ & _ & Hcn).
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as Hrs.
pose proof asan_consts as (C1 & _).
split; [exists c, (Z.of_nat (length (Verbs.line (e_D e))) + 1); split; [exact Hcbin' | lia]|].
split; [apply (tok_apart B lyc Sc Wc memc mdc Rc Oc c (Z.of_nat (length (Verbs.line (e_D e))) + 1) p
  (Z.of_nat (length w) + 1) HAR Hrec Hcbin' Hcbno); lia|].
split; [exact Hstr|]. split; [unfold LMAX; lia|]. split; [lia|]. split; [lia | exact Hwl].
Qed.

End e.
End f.
End d.
