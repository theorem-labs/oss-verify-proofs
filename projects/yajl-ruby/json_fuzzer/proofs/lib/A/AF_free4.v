(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_qkit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanOps.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
Ltac pg := match goal with |- ?g => idtac "GOAL:"; idtac g end.
Ltac djs := cbn [disjoint_from length cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Pos.add]; rewrite ?length_le8, ?length_le4; repeat split; try exact I; lia.
Ltac phyps := match goal with |- _ => repeat match goal with H : ?t |- _ => idtac H ":" t; fail end end.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
(* [comment removed for export] *)
Local Ltac slia ::= first [ exact I | dlia | split; [dlia | exact I] ].
Local Ltac flia ::= first [ assumption | lia ].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition recW (sp : Z) (L : list batch) : list (Z * Z) :=
  [(sp + -80, sp + -48); (0xaa890, 0xaa8b0)] ++ map (fun b => (b_addr b + 0, b_addr b + 0 + 8)) L.

(* [comment removed for export] *)
Definition mergeW (sp : Z) (AL : list Z) : list (Z * Z) :=
  [(sp + -96, sp + -48); (0xaa890, 0xaa8b0)] ++ map (fun x => (x + 0, x + 0 + 8192)) AL.



Lemma pop_prefix_stop : forall l mn, qbytes l <= mn -> pop_prefix l (qbytes l) mn = ([], l).
Proof. aceil. intros [|b l] mn H; [reflexivity|]. rewrite qbytes_cons in H |- *. cbn [pop_prefix]. destruct (Z.ltb_spec mn (b_size b + qbytes l)); [lia| reflexivity]. Qed.

Lemma pop_prefix_split : forall gq bytes mn p k, pop_prefix gq bytes mn = (p, k) -> gq = p ++ k.
Proof. aceil.
  induction gq as [|b gq IH]; cbn [pop_prefix]; intros bytes mn p k H.
  - injection H as <- <-. reflexivity.
  - simpl in H. destruct (mn <? bytes).
    + destruct (pop_prefix gq (bytes - b_size b) mn) as [p' k'] eqn:E. injection H as <- <-. cbn. f_equal. eapply IH. exact E.
    + injection H as <- <-. reflexivity.
Qed.

Lemma pop_prefix_step : forall b l bytes mn p k, mn < bytes -> pop_prefix l (bytes - b_size b) mn = (p, k) -> pop_prefix (b :: l) bytes mn = (b :: p, k).
Proof. aceil. intros b l bytes mn p k H1 H2. simpl. rewrite (proj2 (Z.ltb_lt _ _) H1). rewrite H2. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint updn {X} (l : list X) (j : nat) (vs : list X) : list X :=
  match vs with [] => l | v :: vs' => updn (upd l j v) (S j) vs' end.
Lemma updn_length : forall {X} (vs l : list X) j, length (updn l j vs) = length l.
Proof. aceil. induction vs; cbn; intros; [reflexivity|]. rewrite IHvs, upd_length. reflexivity. Qed.
Lemma upd_app_mid : forall {X} (pre mid post : list X) (x v : X), upd (pre ++ x :: mid ++ post) (length pre) v = pre ++ v :: mid ++ post.
Proof. aceil. induction pre; cbn; intros; [reflexivity|]. rewrite IHpre. reflexivity. Qed.
Lemma updn_spec : forall {X} (vs pre mid post : list X),
  (length vs <= length mid)%nat -> updn (pre ++ mid ++ post) (length pre) vs = pre ++ vs ++ skipn (length vs) mid ++ post.
Proof. aceil.
  induction vs as [|v vs IH]; intros pre mid post HL; [reflexivity|].
  destruct mid as [|x mid]; cbn in HL; [lia|]. cbn [updn skipn]. change ((x :: mid) ++ post) with (x :: mid ++ post).
  rewrite upd_app_mid. replace (S (length pre)) with (length (pre ++ [v])) by (rewrite length_app; cbn; lia).
  replace (pre ++ v :: mid ++ post) with ((pre ++ [v]) ++ mid ++ post) by (rewrite <- app_assoc; reflexivity).
  rewrite IH by lia. rewrite <- app_assoc. reflexivity.
Qed.
Lemma firstn_skipn_succ : forall {X} (l : list X) i w n, nth_error l i = Some w -> firstn (S n) (skipn i l) = w :: firstn n (skipn (S i) l).
Proof. aceil.
  intros X l i w n N. pose proof (nth_error_split l i w N) as (l1 & l2 & -> & L1). subst i.
  rewrite skipn_app, skipn_all, Nat.sub_diag. cbn. f_equal.
  replace (S (length l1)) with (length (l1 ++ [w])) by (rewrite length_app; cbn; lia).
  replace (l1 ++ w :: l2) with ((l1 ++ [w]) ++ l2) by (rewrite <- app_assoc; reflexivity).
  rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Section RECYCLE.
Variable P : acc -> Prop.
Variables (ra gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (sp lo T qmin : Z).
Notation INST := 0xaa518.
Notation q := (0xaa518 + 728).

Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= sp + -96.
Hypothesis SPH : sp <= 2^47.
Hypothesis HT : (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) /\ T + 4096 <= alloc_ceiling.   (* [comment removed for export] *)
Hypothesis HMIN : 0 <= qmin < 2^40.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= sp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa4000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Lemma merge_copy_loop : forall k i mx wsc (na ca cc cn : Z) (wsn : list word) (Q0 : machine_state -> Prop)
    (rax t0x t1x t5x a2x a3x a4x a6x t6x x8 x9 x18 x19 x20 : word),
  Z.to_nat (cn - i) = k -> 0 <= i < cn -> 0 <= cc -> cc + cn <= 1021 ->
  Z.of_nat (length wsn) = 1021 -> Z.of_nat (length wsc) = 1021 ->
  kHighMemBeg <= na -> na + 8192 <= lo -> kHighMemBeg <= ca -> ca + 8192 <= lo -> (na + 8192 <= ca \/ ca + 8192 <= na) ->
  (forall a n, na <= a -> a + Z.of_nat n <= na + 8192 -> P (Z_to_bv 64 a, n)) ->
  (forall a n, ca <= a -> a + Z.of_nat n <= ca + 8192 -> P (Z_to_bv 64 a, n)) ->
  mem_inv asegs mx -> u64arr asegs mx (na + 24) wsn -> u64arr asegs mx (ca + 24) wsc ->
  (forall m' (t5' : word),
     mem_inv asegs m' -> munch [(ca + 24 + 8 * cc, ca + 24 + 8 * (cc + cn))] mx m' -> wmono asegs mx m' ->
     u64arr asegs m' (na + 24) wsn ->
     u64arr asegs m' (ca + 24) (updn wsc (Z.to_nat (cc + i)) (firstn (Z.to_nat (cn - i)) (skipn (Z.to_nat i) wsn))) ->
     evtA asegs P Q0 (MS (mkR rax (Z_to_bv 64 (sp + -96)) gp tp t0x t1x (Z_to_bv 64 (na + 24 + 8 * cn)) x8 x9 (Z_to_bv 64 0xaa890) (Z_to_bv 64 (sp + -80)) a2x a3x a4x (Z_to_bv 64 1021) a6x (Z_to_bv 64 8192)
                             x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (ca + 24 + 8 * (cc + cn))) (Z_to_bv 64 (na + 24 + 8 * cn)) t5' t6x) F (Z_to_bv 64 0x34c20) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q0 (MS (mkR rax (Z_to_bv 64 (sp + -96)) gp tp t0x t1x (Z_to_bv 64 (na + 24 + 8 * i)) x8 x9 (Z_to_bv 64 0xaa890) (Z_to_bv 64 (sp + -80)) a2x a3x a4x (Z_to_bv 64 1021) a6x (Z_to_bv 64 8192)
                          x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (ca + 24 + 8 * (cc + i))) (Z_to_bv 64 (na + 24 + 8 * cn)) t5x t6x) F (Z_to_bv 64 0x34c0c) fc None mx (seg_rom asegs)).
Proof. aceil.
  induction k as [|k IH]; intros i mx wsc na ca cc cn wsn Q0 rax t0x t1x t5x a2x a3x a4x a6x t6x x8 x9 x18 x19 x20 Hk Hi Hcc Hcn LN LC N1 N2 C1 C2 APNC PNA PCA MI ARN ARC CONT; [lia|].
  pose proof LOC as LOC0. aceil. rewrite kHighMemBeg_val in N1, C1.
  assert (MU : munch [(ca + 24 + 8 * cc, ca + 24 + 8 * (cc + cn))] mx mx) by apply munch_refl.
  assert (WM : wmono asegs mx mx) by apply wmono_refl.
  destruct (nth_error wsn (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; lia].
  pose proof (u64arr_read asegs mx (na + 24) wsn i w (Z_to_bv 64 (na + 24 + 8 * i)) ARN NTH ltac:(lia) ltac:(reflexivity)) as RD.
  zstepA. clear RD. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?m0 _) =>
    pose proof (u64arr_store_ok asegs m0 (ca + 24) wsc (cc + i) (Z_to_bv 64 (ca + 24 + 8 * (cc + i))) ARC ltac:(lia) ltac:(reflexivity)) as SOK;
    pose proof (u64arr_write asegs m0 (ca + 24) wsc (cc + i) w ARC ltac:(lia)) as ARC' end.
  stepA. (* [comment removed for export] *)
  all: lazymatch goal with |- P _ => apply PCA; lia | _ => idtac end.
  clear ARC. store_done. rename ARC' into ARC.
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases KL; zify_cond KL.
  - (* [comment removed for export] *)
    replace (na + 24 + 8 * i + 8) with (na + 24 + 8 * (i + 1)) by lia. replace (ca + 24 + 8 * (cc + i) + 8) with (ca + 24 + 8 * (cc + (i + 1))) by lia.
    eapply (IH (i + 1)); [lia| revert KL; rewrite ?unsigned_lit by lia; intros KL; lia| exact Hcc| exact Hcn| exact LN| rewrite upd_length; exact LC
      | rewrite kHighMemBeg_val; lia| lia| rewrite kHighMemBeg_val; lia| lia| lia| exact PNA| exact PCA| exact MI| exact ARN| exact ARC|].
    intros m' t5' MI' MU' WM' ARN' ARC'. eapply CONT; [exact MI'| eapply munch_trans; [exact MU| exact MU']| eapply wmono_trans; [exact WM| exact WM']| exact ARN'|].
    replace (Z.to_nat (cn - i)) with (S (Z.to_nat (cn - (i + 1)))) by lia. rewrite (firstn_skipn_succ wsn _ w _ NTH).
    replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia. cbn [updn]. replace (S (Z.to_nat (cc + i))) with (Z.to_nat (cc + (i + 1))) by lia. exact ARC'.
  - (* [comment removed for export] *)
    assert (Ei : cn = i + 1) by (revert KL; rewrite ?unsigned_lit by lia; intros KL; lia).
    replace (na + 24 + 8 * i + 8) with (na + 24 + 8 * cn) by lia. replace (ca + 24 + 8 * (cc + i) + 8) with (ca + 24 + 8 * (cc + cn)) by lia.
    eapply CONT; [exact MI| exact MU| exact WM| exact ARN|].
    replace (Z.to_nat (cn - i)) with (S O) by lia. rewrite (firstn_skipn_succ wsn _ w _ NTH). cbn [firstn updn]. exact ARC.
Qed.

(* [comment removed for export] *)
Lemma merge_tmp_ne : forall out mx (na : Z) AL (rax t1x t2x t3x t4x t5x y3 y4 a4x w2 w3 a2x : word),
  Forall (bok lo T) out -> kHighMemBeg <= na -> na + 8192 <= lo -> Forall (fun b => far na (b_addr b)) out -> bapart out ->
  out <> [] -> blen out + 1 < 2^40 ->
  In na AL -> (forall b, In b out -> In (b_addr b) AL) ->
  (forall a0 a k, In a0 AL -> a0 <= a -> a + Z.of_nat k <= a0 + 8192 -> P (Z_to_bv 64 a, k)) ->
  mem_inv asegs mx ->
  rw_cells asegs mx na [C8 (Z_to_bv 64 0); C8 w2; C8 w3] ->
  rw_cells asegs mx (sp + -80) [C8 (Z_to_bv 64 (blen out)); C8 (Z_to_bv 64 (bhd out)); C8 (Z_to_bv 64 (blast out)); C8 (Z_to_bv 64 (qbytes out))] ->
  bcells mx out ->
  (forall m' (t1' : word),
     mem_inv asegs m' -> munch [(sp + -80, sp + -48); (blast out + 0, blast out + 0 + 8)] mx m' -> wmono asegs mx m' ->
     rw_cells asegs m' na [C8 (Z_to_bv 64 0); C8 w2; C8 w3] ->
     rw_cells asegs m' (sp + -80) [C8 (Z_to_bv 64 (blen out + 1)); C8 (Z_to_bv 64 (bhd (out ++ [mkBatch na [] 8192]))); C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 (qbytes out))] ->
     bcellsn m' out na ->
     evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (sp + -96)) gp tp (Z_to_bv 64 na) t1' t2x (Z_to_bv 64 0xaa890) (Z_to_bv 64 qmin) (Z_to_bv 64 0xaa890) (Z_to_bv 64 (sp + -80)) a2x (Z_to_bv 64 (blen out + 1)) a4x (Z_to_bv 64 1021) (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192)
                             (Z_to_bv 64 698352) y3 y4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (Z_to_bv 64 0x34ca0) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (sp + -96)) gp tp (Z_to_bv 64 na) t1x t2x (Z_to_bv 64 0xaa890) (Z_to_bv 64 qmin) (Z_to_bv 64 0xaa890) (Z_to_bv 64 (sp + -80)) a2x (Z_to_bv 64 (blen out)) a4x (Z_to_bv 64 1021) (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192)
                          (Z_to_bv 64 698352) y3 y4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (Z_to_bv 64 0x34c68) fc None mx (seg_rom asegs)).
Proof. aceil.
  intros out mx na AL rax t1x t2x t3x t4x t5x y3 y4 a4x w2 w3 a2x OKO N1 N2 FO APO NE LEN INN INO PQA MI HNX TMP QO CONT.
  pose proof LOC as LOC0. aceil. rewrite kHighMemBeg_val in N1.
  assert (PNA : forall a k, na <= a -> a + Z.of_nat k <= na + 8192 -> P (Z_to_bv 64 a, k)) by (intros; eapply PQA; [exact INN| lia| lia]).
  assert (MU : munch [(sp + -80, sp + -48); (blast out + 0, blast out + 0 + 8)] mx mx) by apply munch_refl.
  assert (WM : wmono asegs mx mx) by apply wmono_refl.
  destruct (exists_last NE) as [out0 [bl EP]]. subst out. rewrite blast_app1 in *.
  assert (INl : In (b_addr bl) AL) by (apply INO; apply in_app_iff; right; left; reflexivity).
  assert (OKl : bok lo T bl) by (apply Forall_app in OKO; destruct OKO as [_ X]; exact (Forall_inv X)).
  assert (Fl : far na (b_addr bl)) by (apply Forall_app in FO; destruct FO as [_ X]; exact (Forall_inv X)).
  assert (APl : Forall (fun b => far (b_addr bl) (b_addr b)) out0).
  { apply Forall_forall. intros b' Hb'. apply far_sym. exact (bapart_app_cross out0 [bl] b' bl APO Hb' ltac:(left; reflexivity)). }
  apply bcellsn_app in QO. destruct QO as [QO [Hl _]].
  destruct bl as [la lits lsz]. unfold bok in OKl. unfold far in Fl, APl. cbn [b_addr b_size b_items bhd_or] in Hl, OKl, INl, Fl, APl, QO, TMP, CONT, MU |- *.
  rewrite kHighMemBeg_val in OKl || idtac. pose proof OKl as (Rl1 & Rl2 & Rl3 & Rl4 & Rl5).
  assert (PL : forall a k, la <= a -> a + Z.of_nat k <= la + 8192 -> P (Z_to_bv 64 a, k)) by (intros; eapply PQA; [exact INl| lia| lia]).
  apply Forall_app in OKO. destruct OKO as [OKO _]. apply Forall_app in FO. destruct FO as [FO _]. unfold far in FO.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  eapply CONT; [exact MI| exact MU| exact WM| exact HNX| | ].
  - rewrite (bhd_or_app (out0 ++ [_]) [_]) by (intros X; apply app_eq_nil in X; destruct X; discriminate). exact TMP.
  - apply bcellsn_app. split; [exact QO| cbn; split; [exact Hl| exact I]].
Qed.

Lemma merge_tmp_e : forall mx (na : Z) AL (rax t1x t2x t3x t4x t5x y3 y4 a4x a2x : word) (w2 w3 : word),
  kHighMemBeg <= na -> na + 8192 <= lo -> In na AL ->
  (forall a0 a k, In a0 AL -> a0 <= a -> a + Z.of_nat k <= a0 + 8192 -> P (Z_to_bv 64 a, k)) ->
  mem_inv asegs mx ->
  rw_cells asegs mx na [C8 (Z_to_bv 64 0); C8 w2; C8 w3] ->
  rw_cells asegs mx (sp + -80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (qbytes []))] ->
  (forall m' (t1' : word),
     mem_inv asegs m' -> munch [(sp + -80, sp + -48)] mx m' -> wmono asegs mx m' ->
     rw_cells asegs m' na [C8 (Z_to_bv 64 0); C8 w2; C8 w3] ->
     rw_cells asegs m' (sp + -80) [C8 (Z_to_bv 64 (blen (@nil batch) + 1)); C8 (Z_to_bv 64 (bhd ([] ++ [mkBatch na [] 8192]))); C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 (qbytes []))] ->
     bcellsn m' [] na ->
     evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (sp + -96)) gp tp (Z_to_bv 64 na) t1' t2x (Z_to_bv 64 0xaa890) (Z_to_bv 64 qmin) (Z_to_bv 64 0xaa890) (Z_to_bv 64 (sp + -80)) a2x (Z_to_bv 64 (blen (@nil batch) + 1)) a4x (Z_to_bv 64 1021) (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192)
                             (Z_to_bv 64 698352) y3 y4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (Z_to_bv 64 0x34ca0) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (sp + -96)) gp tp (Z_to_bv 64 na) t1x t2x (Z_to_bv 64 0xaa890) (Z_to_bv 64 qmin) (Z_to_bv 64 0xaa890) (Z_to_bv 64 (sp + -80)) a2x (Z_to_bv 64 0) a4x (Z_to_bv 64 1021) (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192)
                          (Z_to_bv 64 698352) y3 y4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (Z_to_bv 64 0x34c90) fc None mx (seg_rom asegs)).
Proof. aceil.
  intros mx na AL rax t1x t2x t3x t4x t5x y3 y4 a4x a2x w2 w3 N1 N2 INN PQA MI HNX TMP CONT.
  pose proof LOC as LOC0. aceil. rewrite kHighMemBeg_val in N1.
  assert (MU : munch [(sp + -80, sp + -48)] mx mx) by apply munch_refl.
  assert (WM : wmono asegs mx mx) by apply wmono_refl.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  eapply CONT; [exact MI| exact MU| exact WM| exact HNX| cbn [bhd_or app b_addr length Z.of_nat Z.add Pos.of_succ_nat]; cbn [bhd_or app b_addr length Z.of_nat Z.add] in TMP; exact TMP| exact I].
Qed.

(* [comment removed for export] *)
Lemma merge_link : forall done rest' out mx (ca na cz' f N QB : Z) (its' : list Z) AL (rax t1x t2x t3x t4x t5x y3 y4 a2x : word) (j0 : list byte),
  Forall (bok lo T) (done ++ rest' ++ out) -> kHighMemBeg <= ca -> ca + 8192 <= lo -> kHighMemBeg <= na -> na + 8192 <= lo -> far ca na ->
  Forall (fun b => far ca (b_addr b) /\ far na (b_addr b)) (done ++ rest' ++ out) -> bapart (done ++ rest' ++ out) ->
  0 < N < 2^40 -> blen out + 1 < 2^40 ->
  In ca AL -> In na AL -> (forall b, In b out -> In (b_addr b) AL) ->
  (forall a0 a k, In a0 AL -> a0 <= a -> a + Z.of_nat k <= a0 + 8192 -> P (Z_to_bv 64 a, k)) ->
  mem_inv asegs mx ->
  rw_cells asegs mx 0xaa890 [C8 (Z_to_bv 64 N); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 (blast (mkBatch na [] 0 :: rest'))); C8 (Z_to_bv 64 QB)] ->
  rw_cells asegs mx ca [C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 cz'); C8 (Z_to_bv 64 (blen its'))] ->
  rw_cells asegs mx na [C8 (Z_to_bv 64 (bhd rest')); C8 (Z_to_bv 64 8192); C8 (Z_to_bv 64 0)] ->
  bcellsn mx done ca -> bcells mx rest' ->
  rw_cells asegs mx (sp + -80) [C8 (Z_to_bv 64 (blen out)); C8 (Z_to_bv 64 (bhd out)); C8 (Z_to_bv 64 (blast out)); C8 (Z_to_bv 64 (qbytes out))] ->
  bcells mx out ->
  rw_cells asegs mx (sp + -96) [CB 8 j0; C8 (Z_to_bv 64 0x34a60)] ->
  (forall m' (t1' t2' : word),
     mem_inv asegs m' -> munch ([(sp + -80, sp + -48); (0xaa890, 0xaa8b0); (ca + 0, ca + 0 + 8); (na + 0, na + 0 + 8)] ++ map (fun b => (b_addr b + 0, b_addr b + 0 + 8)) out) mx m' -> wmono asegs mx m' ->
     rw_cells asegs m' 0xaa890 [C8 (Z_to_bv 64 (N - 1)); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 (blast (mkBatch ca its' cz' :: rest'))); C8 (Z_to_bv 64 QB)] ->
     rw_cells asegs m' ca [C8 (Z_to_bv 64 (bhd rest')); C8 (Z_to_bv 64 cz'); C8 (Z_to_bv 64 (blen its'))] ->
     bcellsn m' done ca -> bcells m' rest' ->
     rw_cells asegs m' (sp + -80) [C8 (Z_to_bv 64 (blen out + 1)); C8 (Z_to_bv 64 (bhd (out ++ [mkBatch na [] 8192]))); C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 (qbytes out))] ->
     bcells m' (out ++ [mkBatch na [] 8192]) ->
     rw_cells asegs m' (sp + -96) [CB 8 j0; C8 (Z_to_bv 64 0x34a60)] ->
     evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (sp + -96)) gp tp (Z_to_bv 64 na) t1' t2' (Z_to_bv 64 0xaa890) (Z_to_bv 64 qmin) (Z_to_bv 64 0xaa890) (Z_to_bv 64 (sp + -80)) a2x (Z_to_bv 64 (blen out + 1)) (Z_to_bv 64 ca) (Z_to_bv 64 1021) (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192)
                             (Z_to_bv 64 698352) y3 y4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (Z_to_bv 64 0x34ca0) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (sp + -96)) gp tp (Z_to_bv 64 na) t1x t2x (Z_to_bv 64 0xaa890) (Z_to_bv 64 qmin) (Z_to_bv 64 0xaa890) (Z_to_bv 64 (sp + -80)) a2x (Z_to_bv 64 N) (Z_to_bv 64 ca) (Z_to_bv 64 1021) (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192)
                          (Z_to_bv 64 698352) y3 y4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (Z_to_bv 64 0x34c40) fc None mx (seg_rom asegs)).
Proof. aceil.
  intros done rest' out mx ca na cz' f N QB its' AL rax t1x t2x t3x t4x t5x y3 y4 a2x j0 OKL C1 C2 N1 N2 FCN FARS APL HN HO INC INN INO PQA MI GQ HC HNX QD QR TMP QO FRM CONT.
  pose proof LOC as LOC0. aceil. rewrite kHighMemBeg_val in C1, N1. unfold far in FCN.
  assert (OKD : Forall (bok lo T) done) by (apply Forall_app in OKL; tauto).
  assert (OKR : Forall (bok lo T) rest') by (apply Forall_app in OKL; destruct OKL as [_ X]; apply Forall_app in X; tauto).
  assert (OKO : Forall (bok lo T) out) by (apply Forall_app in OKL; destruct OKL as [_ X]; apply Forall_app in X; tauto).
  assert (FD : Forall (fun b => far ca (b_addr b) /\ far na (b_addr b)) done) by (apply Forall_app in FARS; tauto).
  assert (FR' : Forall (fun b => far ca (b_addr b) /\ far na (b_addr b)) rest') by (apply Forall_app in FARS; destruct FARS as [_ X]; apply Forall_app in X; tauto).
  assert (FO : Forall (fun b => far ca (b_addr b) /\ far na (b_addr b)) out) by (apply Forall_app in FARS; destruct FARS as [_ X]; apply Forall_app in X; tauto).
  unfold far in FD, FR', FO.
  assert (PCA : forall a k, ca <= a -> a + Z.of_nat k <= ca + 8192 -> P (Z_to_bv 64 a, k)) by (intros; eapply PQA; [exact INC| lia| lia]).
  assert (PNA : forall a k, na <= a -> a + Z.of_nat k <= na + 8192 -> P (Z_to_bv 64 a, k)) by (intros; eapply PQA; [exact INN| lia| lia]).
  assert (MU : munch ([(sp + -80, sp + -48); (0xaa890, 0xaa8b0); (ca + 0, ca + 0 + 8); (na + 0, na + 0 + 8)] ++ map (fun b => (b_addr b + 0, b_addr b + 0 + 8)) out) mx mx) by apply munch_refl.
  assert (WM : wmono asegs mx mx) by apply wmono_refl.
  pose proof (qbytes_nonneg lo T out OKO) as QO0.
  (* [comment removed for export] *)
  assert (FIN_NE : forall m9 (t1' t2' : word),
    mem_inv asegs m9 -> munch ([(sp + -80, sp + -48); (0xaa890, 0xaa8b0); (ca + 0, ca + 0 + 8); (na + 0, na + 0 + 8)] ++ map (fun b => (b_addr b + 0, b_addr b + 0 + 8)) out) mx m9 -> wmono asegs mx m9 ->
    out <> [] ->
    rw_cells asegs m9 0xaa890 [C8 (Z_to_bv 64 (N - 1)); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 (blast (mkBatch ca its' cz' :: rest'))); C8 (Z_to_bv 64 QB)] ->
    rw_cells asegs m9 ca [C8 (Z_to_bv 64 (bhd rest')); C8 (Z_to_bv 64 cz'); C8 (Z_to_bv 64 (blen its'))] ->
    rw_cells asegs m9 na [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 8192); C8 (Z_to_bv 64 0)] ->
    bcellsn m9 done ca -> bcells m9 rest' ->
    rw_cells asegs m9 (sp + -80) [C8 (Z_to_bv 64 (blen out)); C8 (Z_to_bv 64 (bhd out)); C8 (Z_to_bv 64 (blast out)); C8 (Z_to_bv 64 (qbytes out))] ->
    bcells m9 out -> rw_cells asegs m9 (sp + -96) [CB 8 j0; C8 (Z_to_bv 64 0x34a60)] ->
    evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (sp + -96)) gp tp (Z_to_bv 64 na) t1' t2' (Z_to_bv 64 0xaa890) (Z_to_bv 64 qmin) (Z_to_bv 64 0xaa890) (Z_to_bv 64 (sp + -80)) a2x (Z_to_bv 64 (blen out)) (Z_to_bv 64 ca) (Z_to_bv 64 1021) (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192)
                            (Z_to_bv 64 698352) y3 y4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (Z_to_bv 64 0x34c68) fc None m9 (seg_rom asegs))).
  { intros m9 t1' t2' MI9 MU9 WM9 NEO GQ9 HC9 HNX9 QD9 QR9 TMP9 QO9 FRM9.
    eapply (merge_tmp_ne out m9 na AL); [exact OKO| rewrite kHighMemBeg_val; lia| lia| eapply Forall_impl; [| exact FO]; cbv beta; intros b Hb; unfold far; lia
      | do 2 apply bapart_app_inv in APL; exact APL| exact NEO| lia| exact INN| exact INO| exact PQA| exact MI9| exact HNX9| exact TMP9| exact QO9|].
    intros m' t1'' MI' MU' WM' HNX' TMP' QO'.
    destruct (blast_in out NEO) as (bl & INbl & Ebl). pose proof (proj1 (Forall_forall _ _) FO bl INbl) as Fbl. pose proof (proj1 (Forall_forall _ _) OKO bl INbl) as OKbl.
    cbv beta in Fbl, OKbl. unfold bok in OKbl. rewrite Ebl in *.
    assert (FRbl : Forall (fun b => far (b_addr bl) (b_addr b)) (done ++ rest')).
    { apply Forall_forall. intros b Hb. apply far_sym. rewrite app_assoc in APL. exact (bapart_app_cross (done ++ rest') out b bl APL Hb INbl). }
    apply Forall_app in FRbl. destruct FRbl as [FRD FRR]. unfold far in FRD, FRR.
    eapply CONT; [exact MI'| eapply munch_trans; [exact MU9| eapply munch_cover; [exact MU'| solve_covers]]| eapply wmono_trans; [exact WM9| exact WM']| | | | | exact TMP'| |].
    - eapply rw_cells_transport; [exact GQ9| exact MU'| exact WM'| djs].
    - eapply rw_cells_transport; [exact HC9| exact MU'| exact WM'| djs].
    - eapply bcellsn_transport; [exact QD9| exact MU'| exact WM'| ].
      apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) OKD b Hb) as Hb1. pose proof (proj1 (Forall_forall _ _) FRD b Hb) as Hb2. cbv beta in Hb1, Hb2. unfold bok in Hb1. djs.
    - eapply bcellsn_transport; [exact QR9| exact MU'| exact WM'| ].
      apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) OKR b Hb) as Hb1. pose proof (proj1 (Forall_forall _ _) FRR b Hb) as Hb2. cbv beta in Hb1, Hb2. unfold bok in Hb1. djs.
    - apply bcellsn_app. split; [exact QO'| cbn; split; [exact HNX'| exact I]].
    - eapply rw_cells_transport; [exact FRM9| exact MU'| exact WM'| djs]. }
  assert (FIN_E : forall m9 (t1' t2' : word),
    mem_inv asegs m9 -> munch ([(sp + -80, sp + -48); (0xaa890, 0xaa8b0); (ca + 0, ca + 0 + 8); (na + 0, na + 0 + 8)] ++ map (fun b => (b_addr b + 0, b_addr b + 0 + 8)) out) mx m9 -> wmono asegs mx m9 ->
    out = [] ->
    rw_cells asegs m9 0xaa890 [C8 (Z_to_bv 64 (N - 1)); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 (blast (mkBatch ca its' cz' :: rest'))); C8 (Z_to_bv 64 QB)] ->
    rw_cells asegs m9 ca [C8 (Z_to_bv 64 (bhd rest')); C8 (Z_to_bv 64 cz'); C8 (Z_to_bv 64 (blen its'))] ->
    rw_cells asegs m9 na [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 8192); C8 (Z_to_bv 64 0)] ->
    bcellsn m9 done ca -> bcells m9 rest' ->
    rw_cells asegs m9 (sp + -80) [C8 (Z_to_bv 64 (blen out)); C8 (Z_to_bv 64 (bhd out)); C8 (Z_to_bv 64 (blast out)); C8 (Z_to_bv 64 (qbytes out))] ->
    rw_cells asegs m9 (sp + -96) [CB 8 j0; C8 (Z_to_bv 64 0x34a60)] ->
    evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (sp + -96)) gp tp (Z_to_bv 64 na) t1' t2' (Z_to_bv 64 0xaa890) (Z_to_bv 64 qmin) (Z_to_bv 64 0xaa890) (Z_to_bv 64 (sp + -80)) a2x (Z_to_bv 64 (blen out)) (Z_to_bv 64 ca) (Z_to_bv 64 1021) (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192)
                            (Z_to_bv 64 698352) y3 y4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (Z_to_bv 64 0x34c90) fc None m9 (seg_rom asegs))).
  { intros m9 t1' t2' MI9 MU9 WM9 EO GQ9 HC9 HNX9 QD9 QR9 TMP9 FRM9. subst out. cbn [bhd_or blast length Z.of_nat] in TMP9 |- *.
    eapply (merge_tmp_e m9 na AL); [rewrite kHighMemBeg_val; lia| lia| exact INN| exact PQA| exact MI9| exact HNX9| exact TMP9|].
    intros m' t1'' MI' MU' WM' HNX' TMP' QO'.
    eapply CONT; [exact MI'| eapply munch_trans; [exact MU9| eapply munch_cover; [exact MU'| solve_covers]]| eapply wmono_trans; [exact WM9| exact WM']| | | | | exact TMP'| |].
    - eapply rw_cells_transport; [exact GQ9| exact MU'| exact WM'| djs].
    - eapply rw_cells_transport; [exact HC9| exact MU'| exact WM'| djs].
    - eapply bcellsn_transport; [exact QD9| exact MU'| exact WM'| ].
      eapply Forall_impl; [| exact OKD]. cbv beta. intros b Hb1. unfold bok in Hb1. djs.
    - eapply bcellsn_transport; [exact QR9| exact MU'| exact WM'| ].
      eapply Forall_impl; [| exact OKR]. cbv beta. intros b Hb1. unfold bok in Hb1. djs.
    - cbn. split; [exact HNX'| exact I].
    - eapply rw_cells_transport; [exact FRM9| exact MU'| exact WM'| djs]. }
  zstepA. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  destruct rest' as [|b2 rest''].
  - (* [comment removed for export] *)
    cbn [blast bhd_or b_addr] in GQ, HNX, FIN_NE, FIN_E |- *.
    cstep. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    replace (N + -1) with (N - 1) in GQ by lia.
    zstepA. if_cases KO; zify_cond KO.
    + eapply FIN_NE; [exact MI| exact MU| exact WM| | exact GQ| exact HC| exact HNX| exact QD| exact I| exact TMP| exact QO| exact FRM].
      intros ->. cbn in KO. apply KO. reflexivity.
    + eapply FIN_E; [exact MI| exact MU| exact WM| | exact GQ| exact HC| exact HNX| exact QD| exact I| exact TMP| exact FRM].
      destruct out; [reflexivity| exfalso; cbn [length] in KO; rewrite Nat2Z.inj_succ in KO; revert KO; rewrite ?unsigned_lit by lia; lia].
  - (* [comment removed for export] *)
    destruct (blast_in (b2 :: rest'') ltac:(discriminate)) as (bl2 & INbl2 & Ebl2).
    pose proof (proj1 (Forall_forall _ _) FR' bl2 INbl2) as Fbl2. cbv beta in Fbl2.
    pose proof (proj1 (Forall_forall _ _) OKR bl2 INbl2) as OKbl2. cbv beta in OKbl2. unfold bok in OKbl2.
    rewrite (blast_cons (mkBatch na [] 0)) in GQ |- * by discriminate. rewrite (blast_cons (mkBatch ca its' cz')) in FIN_NE, FIN_E by discriminate.
    rewrite Ebl2 in GQ, FIN_NE, FIN_E |- *.
    zstepA. if_cases KB; zify_cond KB. { exfalso. revert KB. rewrite ?unsigned_lit by lia. lia. } clear KB.
    zstepA. zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    replace (N + -1) with (N - 1) in GQ by lia.
    zstepA. if_cases KO; zify_cond KO.
    + eapply FIN_E; [exact MI| exact MU| exact WM| | exact GQ| exact HC| exact HNX| exact QD| exact QR| exact TMP| exact FRM].
      destruct out; [reflexivity| exfalso; cbn [length] in KO; rewrite Nat2Z.inj_succ in KO; revert KO; rewrite ?unsigned_lit by lia; lia].
    + eapply FIN_NE; [exact MI| exact MU| exact WM| | exact GQ| exact HC| exact HNX| exact QD| exact QR| exact TMP| exact QO| exact FRM].
      intros ->. cbn in KO. apply KO. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma merge_exit : forall mx (QB ex : Z) (rax t0x t1x t2x t3x t4x t5x a3x a4x y3 y4 : word) (gc gf gl : word) (j0 : list byte),
  0 <= ex <= QB -> QB < 2^62 ->
  mem_inv asegs mx ->
  rw_cells asegs mx 0xaa890 [C8 gc; C8 gf; C8 gl; C8 (Z_to_bv 64 QB)] ->
  rw_cells asegs mx (sp + -96) [CB 8 j0; C8 (Z_to_bv 64 0x34a60)] ->
  (forall m',
     mem_inv asegs m' -> munch [(0xaa890, 0xaa8b0)] mx m' -> wmono asegs mx m' ->
     rw_cells asegs m' 0xaa890 [C8 gc; C8 gf; C8 gl; C8 (Z_to_bv 64 (QB - ex))] ->
     rw_cells asegs m' (sp + -96) [CB 8 j0; C8 (Z_to_bv 64 0x34a60)] ->
     evtA asegs P Q (MS (mkR (Z_to_bv 64 0x34a60) (Z_to_bv 64 (sp + -80)) gp tp t0x t1x t2x (Z_to_bv 64 0xaa890) (Z_to_bv 64 qmin) (Z_to_bv 64 0xaa890) (Z_to_bv 64 (QB - ex)) (Z_to_bv 64 ex) a3x a4x (Z_to_bv 64 1021) (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192)
                             (Z_to_bv 64 698352) y3 y4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (Z_to_bv 64 0x34a60) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (sp + -96)) gp tp t0x t1x t2x (Z_to_bv 64 0xaa890) (Z_to_bv 64 qmin) (Z_to_bv 64 0xaa890) (Z_to_bv 64 (sp + -80)) (Z_to_bv 64 ex) a3x a4x (Z_to_bv 64 1021) (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192)
                          (Z_to_bv 64 698352) y3 y4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (Z_to_bv 64 0x34cb8) fc None mx (seg_rom asegs)).
Proof. aceil.
  intros mx QB ex rax t0x t1x t2x t3x t4x t5x a3x a4x y3 y4 gc gf gl j0 HEX HQB MI GQ FRM CONT.
  pose proof LOC as LOC0. aceil.
  assert (MU : munch [(0xaa890, 0xaa8b0)] mx mx) by apply munch_refl.
  assert (WM : wmono asegs mx mx) by apply wmono_refl.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  eapply CONT; [exact MI| exact MU| exact WM| exact GQ| exact FRM].
Qed.

(* [comment removed for export] *)
Lemma merge_loop : forall rest' nx cur done out mx (ex QB : Z) AL (rax t1x t2x t3x t4x t5x a3x y3 y4 : word) (j0 : list byte),
  Forall (bok lo T) ((done ++ cur :: nx :: rest') ++ out) -> bapart ((done ++ cur :: nx :: rest') ++ out) ->
  blen ((done ++ cur :: nx :: rest') ++ out) < 2^40 -> QB = qbytes (done ++ cur :: nx :: rest') + ex -> 0 <= ex -> QB + qbytes out + 8192 * blen (done ++ cur :: nx :: rest') < 2^62 ->
  (forall b, In b ((done ++ cur :: nx :: rest') ++ out) -> In (b_addr b) AL) ->
  (forall a0 a k, In a0 AL -> a0 <= a -> a + Z.of_nat k <= a0 + 8192 -> P (Z_to_bv 64 a, k)) ->
  mem_inv asegs mx ->
  rw_cells asegs mx 0xaa890 [C8 (Z_to_bv 64 (blen (done ++ cur :: nx :: rest'))); C8 (Z_to_bv 64 (bhd (done ++ cur :: nx :: rest'))); C8 (Z_to_bv 64 (blast (done ++ cur :: nx :: rest'))); C8 (Z_to_bv 64 QB)] ->
  bcells mx (done ++ cur :: nx :: rest') -> bitemsl mx (cur :: nx :: rest') -> bitemsl mx done ->
  rw_cells asegs mx (sp + -80) [C8 (Z_to_bv 64 (blen out)); C8 (Z_to_bv 64 (bhd out)); C8 (Z_to_bv 64 (blast out)); C8 (Z_to_bv 64 (qbytes out))] ->
  bcells mx out -> bitemsl mx out ->
  rw_cells asegs mx (sp + -96) [CB 8 j0; C8 (Z_to_bv 64 0x34a60)] ->
  (forall m' l o ex' (t0' t1' t2' t3' t4' t5' a3' a4' : word),
     merge_batches_aux cur (nx :: rest') out = (l, o) ->
     mem_inv asegs m' -> munch (mergeW sp AL) mx m' -> wmono asegs mx m' ->
     rw_cells asegs m' 0xaa890 [C8 (Z_to_bv 64 (blen (done ++ l))); C8 (Z_to_bv 64 (bhd (done ++ l))); C8 (Z_to_bv 64 (blast (done ++ l))); C8 (Z_to_bv 64 (qbytes (done ++ l)))] ->
     bcells m' (done ++ l) -> bitemsl m' (done ++ l) ->
     rw_cells asegs m' (sp + -80) [C8 (Z_to_bv 64 (blen o)); C8 (Z_to_bv 64 (bhd o)); C8 (Z_to_bv 64 (blast o)); C8 (Z_to_bv 64 (qbytes o))] ->
     bcells m' o -> bitemsl m' o ->
     Forall (bok lo T) ((done ++ l) ++ o) -> bapart ((done ++ l) ++ o) ->
     blen ((done ++ l) ++ o) = blen ((done ++ cur :: nx :: rest') ++ out) -> qbytes (done ++ l) + qbytes o = qbytes (done ++ cur :: nx :: rest') + qbytes out ->
     (forall b, In b ((done ++ l) ++ o) -> In (b_addr b) AL) ->
     rw_cells asegs m' (sp + -96) [CB 8 j0; C8 (Z_to_bv 64 0x34a60)] ->
     evtA asegs P Q (MS (mkR (Z_to_bv 64 0x34a60) (Z_to_bv 64 (sp + -80)) gp tp t0' t1' t2' (Z_to_bv 64 0xaa890) (Z_to_bv 64 qmin) (Z_to_bv 64 0xaa890) (Z_to_bv 64 (qbytes (done ++ l))) (Z_to_bv 64 ex') a3' a4' (Z_to_bv 64 1021) (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192)
                             (Z_to_bv 64 698352) y3 y4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6) F (Z_to_bv 64 0x34a60) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (sp + -96)) gp tp (Z_to_bv 64 (b_addr nx)) t1x t2x (Z_to_bv 64 0xaa890) (Z_to_bv 64 qmin) (Z_to_bv 64 0xaa890) (Z_to_bv 64 (sp + -80)) (Z_to_bv 64 ex) a3x (Z_to_bv 64 (b_addr cur)) (Z_to_bv 64 1021) (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192)
                          (Z_to_bv 64 698352) y3 y4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (Z_to_bv 64 0x34bd4) fc None mx (seg_rom asegs)).
Proof. aceil.
  intros rest'. remember (length rest') as n eqn:Hn. revert rest' Hn.
  induction n as [n IHn] using (well_founded_induction Wf_nat.lt_wf).
  intros rest' Hn nx cur done out mx ex QB AL rax t1x t2x t3x t4x t5x a3x y3 y4 j0 OKL APL LENL EQB EX0 QBL INA PQA MI GQ QC QI ID TMP QO IO FRM CONT.
  pose proof LOC as LOC0; aceil.
  destruct cur as [ca ci cz]; destruct nx as [na ni nz]; cbn [b_addr b_items b_size] in *.
  assert (OKc : bok lo T (mkBatch ca ci cz)) by (apply (proj1 (Forall_forall _ _) OKL); apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
  assert (OKn : bok lo T (mkBatch na ni nz)) by (apply (proj1 (Forall_forall _ _) OKL); apply in_app_iff; left; apply in_app_iff; right; right; left; reflexivity).
  unfold bok in OKc, OKn; cbn [b_addr b_size b_items] in OKc, OKn.
  (* [comment removed for export] *)
  pose proof (proj1 OKc) as CA1. pose proof (proj1 (proj2 OKc)) as CA2. pose proof (proj1 OKn) as NA1. pose proof (proj1 (proj2 OKn)) as NA2.
  assert (INC : In ca AL) by (apply (INA (mkBatch ca ci cz)); apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
  assert (INN : In na AL) by (apply (INA (mkBatch na ni nz)); apply in_app_iff; left; apply in_app_iff; right; right; left; reflexivity).
  assert (PCA : forall a k, ca <= a -> a + Z.of_nat k <= ca + 8192 -> P (Z_to_bv 64 a, k)) by (intros; eapply PQA; [exact INC| lia| lia]).
  assert (PNA : forall a k, na <= a -> a + Z.of_nat k <= na + 8192 -> P (Z_to_bv 64 a, k)) by (intros; eapply PQA; [exact INN| lia| lia]).
  rewrite qbytes_app, !qbytes_cons in EQB; cbn [b_size] in EQB.
  pose proof (proj1 (bapart_app _ _) APL) as (APF & APO & APX).
  pose proof (proj1 (bapart_app done _) APF) as (APD & APC & APDX). cbn [bapart apl map b_addr] in APC. destruct APC as (FC & FN & APR). pose proof (Forall_inv FC) as FCN. pose proof (Forall_inv_tail FC) as FCR. cbv beta in FCN.
  assert (FDS : Forall (fun b => far ca (b_addr b) /\ far na (b_addr b)) done).
  { apply Forall_forall. intros b Hb. split; apply far_sym; [exact (APDX b (mkBatch ca ci cz) Hb ltac:(left; reflexivity))| exact (APDX b (mkBatch na ni nz) Hb ltac:(right; left; reflexivity))]. }
  assert (FRS : Forall (fun b => far ca (b_addr b) /\ far na (b_addr b)) rest').
  { apply Forall_forall. intros b Hb. split; [apply (proj1 (Forall_forall _ _) FCR)| apply (proj1 (Forall_forall _ _) FN)]; apply in_map; exact Hb. }
  assert (FOS : Forall (fun b => far ca (b_addr b) /\ far na (b_addr b)) out).
  { apply Forall_forall. intros b Hb. split; [exact (APX (mkBatch ca ci cz) b ltac:(apply in_app_iff; right; left; reflexivity) Hb)| exact (APX (mkBatch na ni nz) b ltac:(apply in_app_iff; right; right; left; reflexivity) Hb)]. }
  pose proof FCN as FCN0. unfold far in FCN.
  pose proof FDS as FDS0. pose proof FRS as FRS0. pose proof FOS as FOS0. unfold far in FDS, FRS, FOS.
  replace (blast (done ++ mkBatch ca ci cz :: mkBatch na ni nz :: rest')) with (blast (mkBatch na [] 0 :: rest')) in GQ by (rewrite blast_app by discriminate; rewrite (blast_cons (mkBatch ca ci cz)) by discriminate; apply blast_cons_addr; reflexivity).
  remember (blen (done ++ mkBatch ca ci cz :: mkBatch na ni nz :: rest')) as N eqn:EN in GQ.
  remember (bhd (done ++ mkBatch ca ci cz :: mkBatch na ni nz :: rest')) as f eqn:Ef in GQ.
  apply bcellsn_app in QC; destruct QC as [QD QC]; cbn [bcellsn bhd_or b_addr b_size b_items] in QC; destruct QC as (HC & HNX & QR).
  cbn [bitemsl] in QI; destruct QI as (IC & IN & IR).
  assert (OKD : Forall (bok lo T) done) by (apply Forall_app in OKL; destruct OKL as [X _]; apply Forall_app in X; tauto).
  assert (OKR : Forall (bok lo T) rest') by (apply Forall_app in OKL; destruct OKL as [X _]; apply Forall_app in X; destruct X as [_ X]; exact (Forall_inv_tail (Forall_inv_tail X))).
  assert (OKO : Forall (bok lo T) out) by (apply Forall_app in OKL; tauto).
  assert (LENS : blen done + blen rest' + 2 + blen out = blen ((done ++ mkBatch ca ci cz :: mkBatch na ni nz :: rest') ++ out)) by (rewrite !length_app; cbn [length]; lia).
  pose proof (qbytes_nonneg lo T _ OKD) as QD0. pose proof (qbytes_nonneg lo T _ OKR) as QR0. pose proof (qbytes_nonneg lo T _ OKO) as QO0.
  assert (MU : munch (mergeW sp AL) mx mx) by apply munch_refl; unfold mergeW in MU.
  assert (WM : wmono asegs mx mx) by apply wmono_refl.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases KM; zify_cond KM.
  - (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    destruct rest' as [|b3 rest3].
    + (* [comment removed for export] *)
      cbn [bhd_or] in *. cstep. (* [comment removed for export] *)
      lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m9 end.
      eapply (merge_exit m9 QB ex); [lia| lia| exact MI| exact GQ| exact FRM|].
      intros m' MI' MU' WM' GQ' FRM'. subst N f.
      replace (blast [mkBatch na [] 0]) with (blast (done ++ [mkBatch ca ci cz; mkBatch na ni nz])) in GQ' by (rewrite blast_app by discriminate; reflexivity).
      rewrite qbytes_nil in EQB. replace (QB - ex) with (qbytes (done ++ [mkBatch ca ci cz; mkBatch na ni nz])) in GQ' |- * by (rewrite qbytes_app, !qbytes_cons, qbytes_nil; cbn [b_size]; lia).
      eapply (CONT m' [mkBatch ca ci cz; mkBatch na ni nz] out ex).
      * cbn [merge_batches_aux]. unfold zlen. cbn [b_items b_addr b_size]. replace (blen ci + blen ni <=? kBatchCap) with false by (symmetry; apply Z.leb_gt; unfold kBatchCap; revert KM; rewrite ?unsigned_lit by lia; lia). reflexivity.
      * exact MI'.
      * eapply munch_trans; [exact MU| eapply munch_cover; [exact MU'| solve_covers]].
      * eapply wmono_trans; [exact WM| exact WM'].
      * exact GQ'.
      * apply bcellsn_app. split; [eapply bcellsn_transport; [exact QD| exact MU'| exact WM'| eapply Forall_impl; [| exact OKD]; cbv beta; intros b Hb1; unfold bok in Hb1; djs]|].
        cbn. split; [| split; [| exact I]].
        -- eapply rw_cells_transport; [exact HC| exact MU'| exact WM'| djs].
        -- eapply rw_cells_transport; [exact HNX| exact MU'| exact WM'| djs].
      * apply bitemsl_app. split; [eapply bitemsl_transport; [exact ID| exact MU'| exact WM'| eapply Forall_impl; [| exact OKD]; cbv beta; intros b Hb1; unfold bok in Hb1; djs]|].
        cbn [bitemsl]. split; [| split; [| exact I]]; (eapply bitems_transport; [eassumption| exact MU'| exact WM'| cbn [b_addr]; djs]).
      * eapply rw_cells_transport; [exact TMP| exact MU'| exact WM'| djs].
      * eapply bcellsn_transport; [exact QO| exact MU'| exact WM'| eapply Forall_impl; [| exact OKO]; cbv beta; intros b Hb1; unfold bok in Hb1; djs].
      * eapply bitemsl_transport; [exact IO| exact MU'| exact WM'| eapply Forall_impl; [| exact OKO]; cbv beta; intros b Hb1; unfold bok in Hb1; djs].
      * exact OKL.
      * exact APL.
      * reflexivity.
      * rewrite !qbytes_app. reflexivity.
      * exact INA.
      * exact FRM'.
    + (* [comment removed for export] *)
      pose proof (Forall_inv OKR) as OK3. cbv beta in OK3. unfold bok in OK3.
      cbn [bhd_or] in *.
      zstepA. if_cases K6; zify_cond K6. { exfalso. revert K6. rewrite ?unsigned_lit by lia. lia. } clear K6.
      lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m9 end.
      assert (EA : forall l : list batch, (done ++ [mkBatch ca ci cz]) ++ l = done ++ mkBatch ca ci cz :: l) by (intros; rewrite <- app_assoc; reflexivity).
      subst N f. replace (blast (mkBatch na [] 0 :: b3 :: rest3)) with (blast (done ++ mkBatch ca ci cz :: mkBatch na ni nz :: b3 :: rest3)) in GQ by (rewrite blast_app by discriminate; reflexivity).
      eapply (IHn (length rest3) ltac:(subst n; cbn; lia) rest3 eq_refl b3 (mkBatch na ni nz) (done ++ [mkBatch ca ci cz]) out m9 ex QB AL);
        rewrite ?EA; [exact OKL| exact APL| exact LENL| cbn [b_addr b_items b_size]; rewrite ?qbytes_cons in EQB; rewrite qbytes_app, !qbytes_cons; cbn [b_size]; lia| exact EX0| exact QBL| exact INA| exact PQA| exact MI| exact GQ
        | | cbn [bitemsl]; exact (conj IN IR)| apply bitemsl_app; split; [exact ID| cbn [bitemsl]; exact (conj IC I)]| exact TMP| exact QO| exact IO| exact FRM|].
      * apply bcellsn_app. split; [exact QD| exact (conj HC (conj HNX QR))].
      * intros m' l o ex' t0' t1' t2' t3' t4' t5' a3' a4' MB. rewrite !EA. intros. eapply CONT; try eassumption.
        cbn [merge_batches_aux]. unfold zlen. cbn [b_items b_addr b_size]. cbn [merge_batches_aux b_items b_addr b_size] in MB.
        replace (blen ci + blen ni <=? kBatchCap) with false by (symmetry; apply Z.leb_gt; unfold kBatchCap; revert KM; rewrite ?unsigned_lit by lia; lia).
        unfold zlen in MB. rewrite MB. reflexivity.
  - (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. if_cases KS; zify_cond KS. { exfalso. clear -CEILB KS OKc EQB QBL QD0 QR0 QO0 EX0. rewrite ?Z.shiftr_div_pow2 in KS by lia. Z.div_mod_to_equations. lia. } clear KS.
    destruct IC as (junkc & ARC & LENC). destruct IN as (junkn & ARN & LENN). cbn [b_addr b_items] in ARC, ARN, LENC, LENN.
    lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m0 end.
    eapply (evtA_cut asegs P (fun ms1 => exists m1 (t2' t3' t4' t5' : word), ms1 = MS (mkR rax (Z_to_bv 64 (sp + -96)) gp tp (Z_to_bv 64 na) (Z_to_bv 64 (blen ni + blen ci)) t2' (Z_to_bv 64 0xaa890) (Z_to_bv 64 qmin) (Z_to_bv 64 0xaa890) (Z_to_bv 64 (sp + -80)) (Z_to_bv 64 ex) (Z_to_bv 64 cz) (Z_to_bv 64 ca) (Z_to_bv 64 1021) (Z_to_bv 64 (-8192)) (Z_to_bv 64 8192)
                                    (Z_to_bv 64 698352) y3 y4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6) F (Z_to_bv 64 0x34c20) fc None m1 (seg_rom asegs)
          /\ mem_inv asegs m1 /\ munch [(ca + 24 + 8 * blen ci, ca + 24 + 8 * (blen ci + blen ni))] m0 m1 /\ wmono asegs m0 m1
          /\ u64arr asegs m1 (na + 24) (map (fun z : Z => Z_to_bv 64 z) ni ++ junkn)
          /\ u64arr asegs m1 (ca + 24) (updn (map (fun z : Z => Z_to_bv 64 z) ci ++ junkc) (Z.to_nat (blen ci + 0)) (firstn (Z.to_nat (blen ni - 0)) (skipn (Z.to_nat 0) (map (fun z : Z => Z_to_bv 64 z) ni ++ junkn)))))).
    { zstepA. if_cases KZ; zify_cond KZ.
      - apply evtA_done. exists m0. do 4 eexists. split; [reflexivity|]. split; [exact MI|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact ARN|].
        replace (Z.to_nat (blen ni - 0)) with 0%nat by (revert KZ; rewrite ?unsigned_lit by lia; lia). cbn [firstn updn]. exact ARC.
      - do 6 zstepA. (* [comment removed for export] *)
        replace (Z_to_bv 64 (na + 24)) with (Z_to_bv 64 (na + 24 + 8 * 0)) by (f_equal; lia).
        replace (Z_to_bv 64 (ca + Z.shiftl (blen ci) 3 + 24)) with (Z_to_bv 64 (ca + 24 + 8 * (blen ci + 0))) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
        replace (Z_to_bv 64 (na + 24 + Z.shiftl (blen ni) 3)) with (Z_to_bv 64 (na + 24 + 8 * blen ni)) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
        eapply (merge_copy_loop (Z.to_nat (blen ni - 0)) 0 m0 (map (fun z : Z => Z_to_bv 64 z) ci ++ junkc) na ca (blen ci) (blen ni) (map (fun z : Z => Z_to_bv 64 z) ni ++ junkn));
          [reflexivity| revert KZ; rewrite ?unsigned_lit by lia; intros KZ; lia| lia| revert KM; rewrite ?unsigned_lit by lia; intros KM; lia
          | rewrite length_app, length_map; lia| rewrite length_app, length_map; lia
          | rewrite kHighMemBeg_val; lia| lia| rewrite kHighMemBeg_val; lia| lia| unfold far in FCN; lia| exact PNA| exact PCA| exact MI| exact ARN| exact ARC|].
        intros m1 t5' MI1 MU1 WM1 ARN1 ARC1. apply evtA_done. exists m1. do 4 eexists. split; [reflexivity|].
        split; [exact MI1|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact ARN1| exact ARC1]. }
    clear ARC ARN.
    intros ms1 (m1 & t2' & t3' & t4' & t5' & -> & MI1 & MU1 & WM1 & ARN1 & ARC1).
    remember (map (fun z : Z => Z_to_bv 64 z) ni ++ junkn) as wsn eqn:Ewsn in *.
    remember (updn (map (fun z : Z => Z_to_bv 64 z) ci ++ junkc) (Z.to_nat (blen ci + 0)) (firstn (Z.to_nat (blen ni - 0)) (skipn (Z.to_nat 0) wsn))) as wsc eqn:Ewsc in *.
    assert (LWN : Z.of_nat (length wsn) = 1021) by (subst wsn; rewrite length_app, length_map; lia).
    assert (LWC : Z.of_nat (length wsc) = 1021) by (subst wsc; rewrite updn_length, length_app, length_map; lia).
    (* [comment removed for export] *)
    assert (DJ1 : forall b, bok lo T b -> far ca (b_addr b) \/ b_addr b = na -> disjoint_from [(ca + 24 + 8 * blen ci, ca + 24 + 8 * (blen ci + blen ni))] (b_addr b) 24).
    { intros b Hb1 Hb2. unfold bok in Hb1. unfold far in Hb2. djs. }
    carry_rw GQ MU1 WM1. carry_rw HC MU1 WM1. carry_rw TMP MU1 WM1.
    eapply rw_cells_transport in HNX; [| exact MU1| exact WM1| pose proof (DJ1 (mkBatch na ni nz)) as X; cbn [b_addr] in X; apply X; [unfold bok; cbn [b_addr b_items b_size]; lia| right; reflexivity]].
    eapply rw_cells_transport in FRM; [| exact MU1| exact WM1| djs].
    eapply bcellsn_transport in QD; [| exact MU1| exact WM1| apply Forall_forall; intros b Hb; apply DJ1; [exact (proj1 (Forall_forall _ _) OKD b Hb)| left; exact (proj1 (proj1 (Forall_forall _ _) FDS b Hb))] ].
    eapply bcellsn_transport in QR; [| exact MU1| exact WM1| apply Forall_forall; intros b Hb; apply DJ1; [exact (proj1 (Forall_forall _ _) OKR b Hb)| left; exact (proj1 (proj1 (Forall_forall _ _) FRS b Hb))] ].
    eapply bcellsn_transport in QO; [| exact MU1| exact WM1| apply Forall_forall; intros b Hb; apply DJ1; [exact (proj1 (Forall_forall _ _) OKO b Hb)| left; exact (proj1 (proj1 (Forall_forall _ _) FOS b Hb))] ].
    assert (DJ2 : forall b, bok lo T b -> far ca (b_addr b) \/ b_addr b = na -> disjoint_from [(ca + 24 + 8 * blen ci, ca + 24 + 8 * (blen ci + blen ni))] (b_addr b + 24) 8168).
    { intros b Hb1 Hb2. unfold bok in Hb1. unfold far in Hb2. djs. }
    eapply bitemsl_transport in ID; [| exact MU1| exact WM1| apply Forall_forall; intros b Hb; apply DJ2; [exact (proj1 (Forall_forall _ _) OKD b Hb)| left; exact (proj1 (proj1 (Forall_forall _ _) FDS b Hb))] ].
    eapply bitemsl_transport in IR; [| exact MU1| exact WM1| apply Forall_forall; intros b Hb; apply DJ2; [exact (proj1 (Forall_forall _ _) OKR b Hb)| left; exact (proj1 (proj1 (Forall_forall _ _) FRS b Hb))] ].
    eapply bitemsl_transport in IO; [| exact MU1| exact WM1| apply Forall_forall; intros b Hb; apply DJ2; [exact (proj1 (Forall_forall _ _) OKO b Hb)| left; exact (proj1 (proj1 (Forall_forall _ _) FOS b Hb))] ].
    clear MI. rename MI1 into MI.
    assert (MU' : munch (mergeW sp AL) m0 m1) by (eapply munch_trans; [exact MU| eapply munch_cover; [exact MU1| solve_covers]]). clear MU MU1. rename MU' into MU. unfold mergeW in MU.
    assert (WM' : wmono asegs m0 m1) by (eapply wmono_trans; [exact WM| exact WM1]). clear WM WM1. rename WM' into WM.
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    replace (cz + nz + -8192) with (cz + (nz - 8192)) in HC by lia.
    replace (blen ni + blen ci) with (blen (ci ++ ni)) in HC by (rewrite length_app; lia).
    assert (EA3 : forall l, (done ++ mkBatch ca ci cz :: mkBatch na ni nz :: rest') ++ l = done ++ mkBatch ca ci cz :: mkBatch na ni nz :: (rest' ++ l)) by (intros; rewrite <- app_assoc; reflexivity).
    assert (APL3 : bapart (done ++ rest' ++ out)).
    { rewrite EA3 in APL. apply bapart_drop in APL. apply bapart_drop in APL. exact APL. }
    pose proof (blast_cases out) as BLO.
    assert (BLOF : blast out = 0 \/ (far ca (blast out) /\ far na (blast out) /\ forall b, In b out -> b_addr b = blast out \/ far (blast out) (b_addr b))).
    { destruct BLO as [[_ E]|(bl & INbl & E)]; [left; exact E| right]. rewrite E.
      pose proof (proj1 (Forall_forall _ _) FOS0 bl INbl) as X. cbv beta in X. destruct X as [X1 X2]. split; [exact X1|]. split; [exact X2|].
      intros b Hb. destruct (apl_in_cases (map b_addr out) (b_addr b) (b_addr bl) APO ltac:(apply in_map; exact Hb) ltac:(apply in_map; exact INbl)) as [Y|Y]; [left; exact Y| right; apply far_sym; exact Y]. }
    eapply (merge_link done rest' out m1 ca na (cz + (nz - 8192)) f N QB (ci ++ ni) AL);
      [ apply Forall_app; split; [exact OKD| apply Forall_app; split; [exact OKR| exact OKO]]
      | rewrite kHighMemBeg_val; lia| lia| rewrite kHighMemBeg_val; lia| lia| exact FCN0
      | apply Forall_app; split; [exact FDS0| apply Forall_app; split; [exact FRS0| exact FOS0]]
      | exact APL3| subst N; rewrite length_app; cbn [length]; lia| lia
      | exact INC| exact INN| intros b Hb; apply INA; apply in_app_iff; right; exact Hb| exact PQA| exact MI| exact GQ| exact HC| exact HNX| exact QD| exact QR| exact TMP| exact QO| exact FRM|].
    clear MI GQ HC HNX QD QR TMP QO FRM.
    intros m2 t1'' t2'' MI MU2 WM2 GQ HC QD QR TMP QO FRM.
    (* [comment removed for export] *)
    assert (DJ3 : forall x, 0x10007fff8000 <= x -> x + 8192 <= lo -> (x = ca \/ far ca x) -> (x = na \/ far na x) -> (forall b, In b out -> x = b_addr b \/ far x (b_addr b)) ->
                  disjoint_from ([(sp + -80, sp + -48); (0xaa890, 0xaa8b0); (ca + 0, ca + 0 + 8); (na + 0, na + 0 + 8)] ++ map (fun b => (b_addr b + 0, b_addr b + 0 + 8)) out) (x + 24) 8168).
    { intros x H1 H2 H3 H4 H5. unfold far in H3, H4, H5. apply disjoint_from_app; [djs|]. apply disjoint_bmap. intros b Hb. specialize (H5 b Hb). lia. }
    eapply u64arr_transport in ARN1; [| exact MU2| exact WM2| rewrite LWN; apply (DJ3 na); [exact NA1| exact NA2| right; exact FCN0| left; reflexivity| intros b Hb; right; exact (proj2 (proj1 (Forall_forall _ _) FOS0 b Hb))]].
    eapply u64arr_transport in ARC1; [| exact MU2| exact WM2| rewrite LWC; apply (DJ3 ca); [exact CA1| exact CA2| left; reflexivity| right; apply far_sym; exact FCN0| intros b Hb; right; exact (proj1 (proj1 (Forall_forall _ _) FOS0 b Hb))]].
    eapply bitemsl_transport in ID; [| exact MU2| exact WM2|].
    2:{ apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) OKD b Hb) as Hb1. pose proof (proj1 (Forall_forall _ _) FDS0 b Hb) as Hb2. cbv beta in Hb1, Hb2. unfold bok in Hb1.
        apply DJ3; [clear -Hb1; lia| clear -Hb1; lia| right; exact (proj1 Hb2)| right; exact (proj2 Hb2)|].   (* [comment removed for export] *)
        intros b' Hb'. right. rewrite EA3 in APL. exact (bapart_app_cross done _ b b' APL Hb ltac:(right; right; apply in_app_iff; right; exact Hb')). }
    eapply bitemsl_transport in IR; [| exact MU2| exact WM2|].
    2:{ apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) OKR b Hb) as Hb1. pose proof (proj1 (Forall_forall _ _) FRS0 b Hb) as Hb2. cbv beta in Hb1, Hb2. unfold bok in Hb1.
        apply DJ3; [clear -Hb1; lia| clear -Hb1; lia| right; exact (proj1 Hb2)| right; exact (proj2 Hb2)|].   (* [comment removed for export] *)
        intros b' Hb'. right. exact (APX b b' ltac:(apply in_app_iff; right; right; right; exact Hb) Hb'). }
    eapply bitemsl_transport in IO; [| exact MU2| exact WM2|].
    2:{ apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) OKO b Hb) as Hb1. pose proof (proj1 (Forall_forall _ _) FOS0 b Hb) as Hb2. cbv beta in Hb1, Hb2. unfold bok in Hb1.
        apply DJ3; [clear -Hb1; lia| clear -Hb1; lia| right; exact (proj1 Hb2)| right; exact (proj2 Hb2)|].   (* [comment removed for export] *)
        intros b' Hb'. exact (apl_in_cases (map b_addr out) (b_addr b) (b_addr b') APO ltac:(apply in_map; exact Hb) ltac:(apply in_map; exact Hb')). }
    assert (MU' : munch (mergeW sp AL) m0 m2).
    { eapply munch_trans; [exact MU| eapply munch_cover; [exact MU2| unfold mergeW]].
      intros lo1 hi1 Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
      - revert lo1 hi1 Hin. solve_covers.
      - apply in_map_iff in Hin. destruct Hin as (b & E & Hb). injection E as <- <-.
        exists (b_addr b + 0), (b_addr b + 0 + 8192). split; [| lia]. apply in_app_iff. right. apply (in_map (fun x => (x + 0, x + 0 + 8192))). apply INA. apply in_app_iff. right. exact Hb. }
    clear MU MU2. rename MU' into MU. unfold mergeW in MU.
    assert (WM' : wmono asegs m0 m2) by (eapply wmono_trans; [exact WM| exact WM2]). clear WM WM2. rename WM' into WM.
    clear DJ1 DJ2 DJ3.
    (* [comment removed for export] *)
    set (cur' := mkBatch ca (ci ++ ni) (cz + (nz - 8192))) in *. set (sh := mkBatch na [] 8192) in *.
    assert (OKc' : bok lo T cur') by (unfold bok; subst cur'; cbn [b_addr b_size b_items]; rewrite length_app; revert KM; rewrite ?unsigned_lit by lia; intros KM; lia).
    assert (OKsh : bok lo T sh) by (unfold bok; subst sh; cbn [b_addr b_size b_items length]; lia).
    assert (OKO' : Forall (bok lo T) (out ++ [sh])) by (apply Forall_app; split; [exact OKO| constructor; [exact OKsh| constructor]]).
    assert (PERM : Permutation (map b_addr ((done ++ mkBatch ca ci cz :: mkBatch na ni nz :: rest') ++ out)) (map b_addr ((done ++ cur' :: rest') ++ (out ++ [sh])))).
    { subst cur' sh. rewrite !map_app. cbn [map b_addr]. rewrite ?map_app. cbn [map b_addr]. rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
      apply perm_skip. rewrite (app_assoc (map b_addr rest')). apply Permutation_cons_append. }
    assert (APL' : bapart ((done ++ cur' :: rest') ++ (out ++ [sh]))) by (eapply bapart_perm; [exact PERM| exact APL]).
    assert (OKL' : Forall (bok lo T) ((done ++ cur' :: rest') ++ (out ++ [sh]))).
    { apply Forall_app; split; [apply Forall_app; split; [exact OKD| constructor; [exact OKc'| exact OKR]]| exact OKO']. }
    assert (INA' : forall b, In b ((done ++ cur' :: rest') ++ (out ++ [sh])) -> In (b_addr b) AL).
    { intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [apply in_app_iff in Hb; destruct Hb as [Hb|[<-|Hb]]| apply in_app_iff in Hb; destruct Hb as [Hb|[<-|[]]]].
      - apply INA. apply in_app_iff. left. apply in_app_iff. left. exact Hb.
      - exact INC.
      - apply INA. apply in_app_iff. left. apply in_app_iff. right. right. right. exact Hb.
      - apply INA. apply in_app_iff. right. exact Hb.
      - exact INN. }
    assert (LEN' : blen ((done ++ cur' :: rest') ++ (out ++ [sh])) = blen ((done ++ mkBatch ca ci cz :: mkBatch na ni nz :: rest') ++ out)) by (rewrite !length_app; cbn [length]; rewrite ?length_app; cbn [length]; lia).
    assert (QBC : qbytes (done ++ cur' :: rest') + qbytes (out ++ [sh]) = qbytes (done ++ mkBatch ca ci cz :: mkBatch na ni nz :: rest') + qbytes out /\ qbytes (out ++ [sh]) = qbytes out + 8192 /\ qbytes (done ++ cur' :: rest') = qbytes done + (cz + (nz - 8192)) + qbytes rest').
    { subst cur' sh. rewrite ?qbytes_app, ?qbytes_cons, ?qbytes_app, ?qbytes_cons, ?qbytes_nil. cbn [b_size]. lia. }
    destruct QBC as (QBC & QSH & QC').
    remember (bhd (out ++ [sh])) as f2 eqn:Ef2 in TMP.
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    rewrite <- QSH in TMP. replace (blen out + 1) with (blen (out ++ [sh])) in TMP by (rewrite length_app; cbn [length]; lia).
    replace (Z_to_bv 64 na) with (Z_to_bv 64 (blast (out ++ [sh]))) in TMP by (rewrite blast_app1; reflexivity). subst f2.
    lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m9 end.
    assert (BIc' : bitems m9 cur').
    { subst cur'. unfold bitems. cbn [b_addr b_items]. exists (skipn (length ni) junkc).
      split; [| rewrite length_app, length_skipn; lia].
      replace (map (fun z : Z => Z_to_bv 64 z) (ci ++ ni) ++ skipn (length ni) junkc) with wsc; [exact ARC1|].
      subst wsc wsn. rewrite map_app. change (Z.to_nat 0) with 0%nat. rewrite skipn_O.
      replace (Z.to_nat (blen ni - 0)) with (length (map (fun z : Z => Z_to_bv 64 z) ni)) by (rewrite length_map; lia).
      rewrite firstn_app, firstn_all, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
      replace (Z.to_nat (blen ci + 0)) with (length (map (fun z : Z => Z_to_bv 64 z) ci)) by (rewrite length_map; lia).
      rewrite <- (app_nil_r junkc). rewrite (updn_spec (map (fun z : Z => Z_to_bv 64 z) ni) (map (fun z : Z => Z_to_bv 64 z) ci) junkc []) by (rewrite length_map; lia).
      rewrite length_map, !app_nil_r, app_assoc. reflexivity. }
    assert (BIsh : bitems m9 sh) by (subst sh; unfold bitems; cbn [b_addr b_items map app length]; exists wsn; split; [exact ARN1| lia]).
    destruct rest' as [|b3 rest3].
    + (* [comment removed for export] *)
      cbn [bhd_or] in *. cstep. (* [comment removed for export] *)
      eapply (merge_exit m9 QB (ex + 8192)); [rewrite qbytes_nil in *; lia| lia| exact MI| exact GQ| exact FRM|].
      intros m' MI' MU' WM' GQ' FRM'. subst N f.
      rewrite ?qbytes_nil in *. replace (QB - (ex + 8192)) with (qbytes (done ++ [cur'])) in GQ' |- * by lia.
      eapply (CONT m' [cur'] (out ++ [sh]) (ex + 8192)).
      * subst cur' sh. cbn [merge_batches_aux]. unfold zlen. cbn [b_items b_addr b_size].
        replace (blen ci + blen ni <=? kBatchCap) with true by (symmetry; apply Z.leb_le; unfold kBatchCap; revert KM; rewrite ?unsigned_lit by lia; lia). change kBatchSize with 8192. reflexivity.
      * exact MI'.
      * eapply munch_trans; [exact MU| eapply munch_cover; [exact MU'| solve_covers]].
      * eapply wmono_trans; [exact WM| exact WM'].
      * replace (blen (done ++ [mkBatch ca ci cz; mkBatch na ni nz]) - 1) with (blen (done ++ [cur'])) in GQ' by (rewrite !length_app; cbn [length]; lia).
        replace (bhd (done ++ [mkBatch ca ci cz; mkBatch na ni nz])) with (bhd (done ++ [cur'])) in GQ' by (subst cur'; destruct done; reflexivity).
        replace (blast [cur']) with (blast (done ++ [cur'])) in GQ' by (rewrite blast_app1; subst cur'; reflexivity). exact GQ'.
      * apply bcellsn_app. split; [eapply bcellsn_transport; [exact QD| exact MU'| exact WM'| eapply Forall_impl; [| exact OKD]; cbv beta; intros b Hb1; unfold bok in Hb1; djs]|].
        subst cur'. cbn. split; [| exact I]. eapply rw_cells_transport; [exact HC| exact MU'| exact WM'| djs].
      * apply bitemsl_app. split; [eapply bitemsl_transport; [exact ID| exact MU'| exact WM'| eapply Forall_impl; [| exact OKD]; cbv beta; intros b Hb1; unfold bok in Hb1; djs]|].
        cbn [bitemsl]. split; [| exact I]. eapply bitems_transport; [exact BIc'| exact MU'| exact WM'| subst cur'; cbn [b_addr]; djs].
      * eapply rw_cells_transport; [exact TMP| exact MU'| exact WM'| djs].
      * eapply bcellsn_transport; [exact QO| exact MU'| exact WM'| eapply Forall_impl; [| exact OKO']; cbv beta; intros b Hb1; unfold bok in Hb1; djs].
      * eapply bitemsl_transport; [| exact MU'| exact WM'| eapply Forall_impl; [| exact OKO']; cbv beta; intros b Hb1; unfold bok in Hb1; djs].
        apply bitemsl_app. split; [exact IO| cbn [bitemsl]; split; [exact BIsh| exact I]].
      * exact OKL'.
      * exact APL'.
      * exact LEN'.
      * exact QBC.
      * exact INA'.
      * exact FRM'.
    + (* [comment removed for export] *)
      pose proof (Forall_inv OKR) as OK3. cbv beta in OK3. unfold bok in OK3.
      cbn [bhd_or] in *.
      zstepA. if_cases K7; zify_cond K7. 2:{ exfalso. revert K7. rewrite ?unsigned_lit by lia. lia. }
      subst N f.
      eapply (IHn (length rest3) ltac:(subst n; cbn; lia) rest3 eq_refl b3 cur' done (out ++ [sh]) m9 (ex + 8192) QB AL);
        [exact OKL'| exact APL'| rewrite LEN'; exact LENL| rewrite QC', ?qbytes_cons in *; rewrite ?qbytes_cons in EQB; lia| lia
        | rewrite QSH; rewrite length_app in QBL |- *; cbn [length] in QBL |- *; lia| exact INA'| exact PQA| exact MI| | | | exact ID| exact TMP| exact QO| | exact FRM|].
      * replace (blen (done ++ mkBatch ca ci cz :: mkBatch na ni nz :: b3 :: rest3) - 1) with (blen (done ++ cur' :: b3 :: rest3)) in GQ by (rewrite !length_app; cbn [length]; lia).
        replace (bhd (done ++ mkBatch ca ci cz :: mkBatch na ni nz :: b3 :: rest3)) with (bhd (done ++ cur' :: b3 :: rest3)) in GQ by (subst cur'; destruct done; reflexivity).
        replace (blast (cur' :: b3 :: rest3)) with (blast (done ++ cur' :: b3 :: rest3)) in GQ by (rewrite blast_app by discriminate; reflexivity). exact GQ.
      * apply bcellsn_app. split; [exact QD|]. subst cur'. exact (conj HC QR).
      * cbn [bitemsl]. split; [exact BIc'| exact IR].
      * apply bitemsl_app. split; [exact IO| cbn [bitemsl]; split; [exact BIsh| exact I]].
      * intros m' l o ex' t0'' t1''' t2''' t3'' t4'' t5'' a3' a4' MB. intros. eapply CONT; try eassumption.
        -- subst cur' sh. cbn [merge_batches_aux]. unfold zlen. cbn [b_items b_addr b_size]. cbn [merge_batches_aux] in MB. unfold zlen in MB. cbn [b_items b_addr b_size] in MB.
           replace (blen ci + blen ni <=? kBatchCap) with true by (symmetry; apply Z.leb_le; unfold kBatchCap; revert KM; rewrite ?unsigned_lit by lia; lia).
           change kBatchSize with 8192. exact MB.
        -- eapply munch_trans; [exact MU| eassumption].
        -- eapply wmono_trans; [exact WM| eassumption].
        -- etransitivity; [eassumption| exact LEN'].
        -- etransitivity; [eassumption| exact QBC].
Qed.

(* [comment removed for export] *)
Lemma rec_pop_tail : forall pp rr0 L mx (ba bsz : Z) bits (a5x t0x t2x c0 l0 rax x8 x9 a2x a3x x18 x19 x20 t3x t4x t5x : word),
  let b := mkBatch ba bits bsz in
  L = pp ++ b :: rr0 ->
  Forall (bok lo T) L -> bapart L -> blen L < 2^40 -> qbytes L < 2^62 ->
  (forall b a k, In b L -> b_addr b <= a -> a + Z.of_nat k <= b_addr b + 8192 -> P (Z_to_bv 64 a, k)) ->
  mem_inv asegs mx ->
  rw_cells asegs mx 0xaa890 [C8 (Z_to_bv 64 (blen rr0)); C8 (Z_to_bv 64 (bhd rr0)); C8 (Z_to_bv 64 (blast rr0)); C8 (Z_to_bv 64 (qbytes rr0))] ->
  bcells mx (pp ++ [b]) -> bcells mx rr0 ->
  rw_cells asegs mx (sp + -80) [C8 c0; C8 (Z_to_bv 64 (bhd (pp ++ [b]))); C8 l0; C8 (Z_to_bv 64 (qbytes pp))] ->
  (forall m' (t2' : word),
     mem_inv asegs m' -> munch (recW sp L) mx m' -> wmono asegs mx m' -> qbytes rr0 <= qmin ->
     rw_cells asegs m' 0xaa890 [C8 (Z_to_bv 64 (blen rr0)); C8 (Z_to_bv 64 (bhd rr0)); C8 (Z_to_bv 64 (blast rr0)); C8 (Z_to_bv 64 (qbytes rr0))] ->
     bcells m' (pp ++ [b]) -> bcells m' rr0 ->
     rw_cells asegs m' (sp + -80) [C8 (Z_to_bv 64 (blen pp + 1)); C8 (Z_to_bv 64 (bhd (pp ++ [b]))); C8 (Z_to_bv 64 ba); C8 (Z_to_bv 64 (qbytes pp + bsz))] ->
     evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (sp + -80)) gp tp (Z_to_bv 64 (bhd rr0)) (Z_to_bv 64 ba) t2' x8 x9 (Z_to_bv 64 698352) (Z_to_bv 64 qmin) a2x a3x (Z_to_bv 64 (blen pp + 1)) (Z_to_bv 64 ba) (Z_to_bv 64 (blen rr0)) (Z_to_bv 64 (bhd rr0))
                             x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (Z_to_bv 64 0x34b10) fc None m' (seg_rom asegs))) ->
  (forall m' (t2' : word),
     mem_inv asegs m' -> munch (recW sp L) mx m' -> wmono asegs mx m' -> qmin < qbytes rr0 ->
     rw_cells asegs m' 0xaa890 [C8 (Z_to_bv 64 (blen rr0)); C8 (Z_to_bv 64 (bhd rr0)); C8 (Z_to_bv 64 (blast rr0)); C8 (Z_to_bv 64 (qbytes rr0))] ->
     bcells m' (pp ++ [b]) -> bcells m' rr0 ->
     rw_cells asegs m' (sp + -80) [C8 c0; C8 (Z_to_bv 64 (bhd (pp ++ [b]))); C8 l0; C8 (Z_to_bv 64 (qbytes pp + bsz))] ->
     evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (sp + -80)) gp tp (Z_to_bv 64 (bhd rr0)) (Z_to_bv 64 ba) t2' x8 x9 (Z_to_bv 64 698352) (Z_to_bv 64 qmin) a2x a3x (Z_to_bv 64 (blen pp + 1)) (Z_to_bv 64 ba) (Z_to_bv 64 (blen rr0)) (Z_to_bv 64 (bhd rr0))
                             x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (Z_to_bv 64 0x34ab4) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (sp + -80)) gp tp t0x (Z_to_bv 64 ba) t2x x8 x9 (Z_to_bv 64 698352) (Z_to_bv 64 qmin) a2x a3x (Z_to_bv 64 (blen pp)) a5x (Z_to_bv 64 (blen rr0)) (Z_to_bv 64 (bhd rr0))
                          x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (Z_to_bv 64 0x34a90) fc None mx (seg_rom asegs)).
Proof. aceil.
  intros pp rr0 L mx ba bsz bits a5x t0x t2x c0 l0 rax x8 x9 a2x a3x x18 x19 x20 t3x t4x t5x b EL OKL APL LENL QBL PQB MI GQ QPP QRR TMP KEXIT KHEAD. subst b.
  pose proof LOC as LOC0. aceil.
  assert (OKP : Forall (bok lo T) pp) by (rewrite EL in OKL; apply Forall_app in OKL; tauto).
  assert (OKR1 : Forall (bok lo T) (mkBatch ba bits bsz :: rr0)) by (rewrite EL in OKL; apply Forall_app in OKL; tauto).
  pose proof (Forall_inv OKR1) as OKb. pose proof (Forall_inv_tail OKR1) as OKR. clear OKR1.
  assert (INb : In (mkBatch ba bits bsz) L) by (rewrite EL; apply in_app_iff; right; left; reflexivity).
  assert (PB : forall a k, ba <= a -> a + Z.of_nat k <= ba + 8192 -> P (Z_to_bv 64 a, k)) by (intros; eapply PQB; [exact INb| cbn; lia| cbn; lia]).
  assert (QX : 0 <= qbytes pp /\ 0 <= qbytes rr0 /\ qbytes pp + bsz + qbytes rr0 = qbytes L).
  { rewrite EL, qbytes_app, qbytes_cons. cbn [b_size]. pose proof (qbytes_nonneg lo T rr0 OKR). pose proof (qbytes_nonneg lo T pp OKP). lia. }
  assert (LENS : blen pp + blen rr0 + 1 = blen L) by (rewrite EL, length_app; cbn [length]; lia).
  unfold bok in OKb. cbn [b_addr b_size b_items] in OKb, PB, INb, QPP, TMP, KEXIT, KHEAD.
  pose proof OKb as (Rb1 & Rb2 & Rb3 & Rb4 & Rb5).
  (* [comment removed for export] *)
  apply bcellsn_app in QPP. destruct QPP as [QPP [Hb _]]. cbn [bhd_or b_addr b_size b_items] in Hb.
  assert (MU : munch (recW sp L) mx mx) by apply munch_refl. unfold recW in MU.
  assert (WM : wmono asegs mx mx) by apply wmono_refl.
  clear OKL.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. if_cases KX; zify_cond KX.
  - (* [comment removed for export] *)
    zstepA. zstepA. (* [comment removed for export] *)
    eapply KEXIT; [exact MI| exact MU| exact WM| clear -CEILB KX QX QBL HMIN Rb4; Z.div_mod_to_equations; lia| exact GQ| | exact QRR| exact TMP].
    apply bcellsn_app. split; [exact QPP| cbn; split; [exact Hb| exact I]].
  - eapply KHEAD; [exact MI| exact MU| exact WM| | exact GQ| | exact QRR| exact TMP].
    + clear -CEILB KX QX QBL HMIN Rb4. Z.div_mod_to_equations. lia.
    +
    apply bcellsn_app. split; [exact QPP| cbn; split; [exact Hb| exact I]].
Qed.

(* [comment removed for export] *)
Lemma rec_pop_loop : forall rr pp L mx (a5x a7x t1x t2x c0 l0 rax x8 x9 a2x a3x x18 x19 x20 t3x t4x t5x : word),
  L = pp ++ rr -> rr <> [] -> qmin < qbytes rr ->
  Forall (bok lo T) L -> bapart L -> blen L < 2^40 -> qbytes L < 2^62 ->
  (forall b a k, In b L -> b_addr b <= a -> a + Z.of_nat k <= b_addr b + 8192 -> P (Z_to_bv 64 a, k)) ->
  mem_inv asegs mx ->
  rw_cells asegs mx 0xaa890 [C8 (Z_to_bv 64 (blen rr)); C8 (Z_to_bv 64 (bhd rr)); C8 (Z_to_bv 64 (blast rr)); C8 (Z_to_bv 64 (qbytes rr))] ->
  bcells mx pp -> bcells mx rr ->
  rw_cells asegs mx (sp + -80) [C8 c0; C8 (Z_to_bv 64 (bhd pp)); C8 l0; C8 (Z_to_bv 64 (qbytes pp))] ->
  (pp <> [] -> a5x = Z_to_bv 64 (blast pp)) ->
  (forall m' popped rr' (a5' a7' t0' t1' t2' : word),
     pop_prefix rr (qbytes rr) qmin = (popped, rr') ->
     mem_inv asegs m' -> munch (recW sp L) mx m' -> wmono asegs mx m' ->
     rw_cells asegs m' 0xaa890 [C8 (Z_to_bv 64 (blen rr')); C8 (Z_to_bv 64 (bhd rr')); C8 (Z_to_bv 64 (blast rr')); C8 (Z_to_bv 64 (qbytes rr'))] ->
     bcells m' (pp ++ popped) -> bcells m' rr' -> qbytes rr' <= qmin ->
     rw_cells asegs m' (sp + -80) [C8 (Z_to_bv 64 (blen (pp ++ popped))); C8 (Z_to_bv 64 (bhd (pp ++ popped))); C8 (Z_to_bv 64 (blast (pp ++ popped))); C8 (Z_to_bv 64 (qbytes (pp ++ popped)))] ->
     evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (sp + -80)) gp tp t0' t1' t2' x8 x9 (Z_to_bv 64 698352) (Z_to_bv 64 qmin) a2x a3x (Z_to_bv 64 (blen (pp ++ popped))) a5' (Z_to_bv 64 (blen rr')) a7'
                             x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (Z_to_bv 64 0x34b10) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (sp + -80)) gp tp (Z_to_bv 64 (bhd rr)) t1x t2x x8 x9 (Z_to_bv 64 698352) (Z_to_bv 64 qmin) a2x a3x (Z_to_bv 64 (blen pp)) a5x (Z_to_bv 64 (blen rr)) a7x
                          x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (Z_to_bv 64 0x34ab4) fc None mx (seg_rom asegs)).
Proof. aceil.
  induction rr as [|b rr0 IH]; intros pp L mx a5x a7x t1x t2x c0 l0 rax x8 x9 a2x a3x x18 x19 x20 t3x t4x t5x EL NE LT OKL APL LENL QBL PQB MI GQ QPP QRR TMP LASTP CONT; [congruence|].
  pose proof LOC as LOC0. aceil.
  (* [comment removed for export] *)
  assert (OKP : Forall (bok lo T) pp) by (rewrite EL in OKL; apply Forall_app in OKL; tauto).
  assert (OKR1 : Forall (bok lo T) (b :: rr0)) by (rewrite EL in OKL; apply Forall_app in OKL; tauto).
  pose proof (Forall_inv OKR1) as OKb. pose proof (Forall_inv_tail OKR1) as OKR. clear OKR1.
  assert (INb : In b L) by (rewrite EL; apply in_app_iff; right; left; reflexivity).
  assert (APR : Forall (fun b' => b_addr b + 8192 <= b_addr b' \/ b_addr b' + 8192 <= b_addr b) rr0).
  { apply Forall_forall. intros b' Hb'. rewrite EL in APL. apply bapart_app_inv in APL. exact (bapart_hd _ _ _ APL Hb'). }
  assert (APP : Forall (fun b' => b_addr b + 8192 <= b_addr b' \/ b_addr b' + 8192 <= b_addr b) pp).
  { apply Forall_forall. intros b' Hb'. rewrite EL in APL.
    destruct (bapart_app_cross pp (b :: rr0) b' b APL Hb' ltac:(left; reflexivity)); lia. }
  assert (LENS : blen pp + blen rr0 + 1 < 2^40) by (rewrite EL, length_app in LENL; cbn [length] in LENL; lia).
  assert (PB : forall a k, b_addr b <= a -> a + Z.of_nat k <= b_addr b + 8192 -> P (Z_to_bv 64 a, k)) by (intros; eapply PQB; [exact INb| lia| lia]).
  assert (QX : 0 <= qbytes pp /\ 0 <= qbytes rr0 /\ qbytes pp + b_size b + qbytes rr0 = qbytes L).
  { rewrite EL, qbytes_app, qbytes_cons. pose proof (qbytes_nonneg lo T rr0 OKR). pose proof (qbytes_nonneg lo T pp OKP). lia. }
  cbn [bcellsn] in QRR. destruct QRR as [Hb QRR].
  destruct b as [ba bits bsz]. unfold bok in OKb. cbn [b_addr b_size b_items bhd_or] in Hb, OKb, APR, APP, PB, INb, LT, QX |- *.
  rewrite qbytes_cons in LT, GQ. cbn [b_size length] in LT, GQ |- *. rewrite Nat2Z.inj_succ in GQ |- *.
  pose proof OKb as (Rb1 & Rb2 & Rb3 & Rb4 & Rb5).
  assert (MU : munch (recW sp L) mx mx) by apply munch_refl. unfold recW in MU.
  assert (WM : wmono asegs mx mx) by apply wmono_refl.
  apply hide in OKL.
  zstepA. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. } clear K0. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  (* [comment removed for export] *)
  eapply (evtA_cut asegs P (fun ms1 => exists m1, ms1 = MS (mkR rax (Z_to_bv 64 (sp + -80)) gp tp (Z_to_bv 64 ba) t1x t2x x8 x9 (Z_to_bv 64 698352) (Z_to_bv 64 qmin) a2x a3x
                                  (Z_to_bv 64 (blen pp)) a5x (Z_to_bv 64 (Z.succ (blen rr0))) (Z_to_bv 64 (bhd rr0)) x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (Z_to_bv 64 0x34ac8) fc None m1 (seg_rom asegs)
        /\ mem_inv asegs m1 /\ munch ([(sp + -80, sp + -48); (0xaa890, 0xaa8b0)] ++ map (fun b => (b_addr b + 0, b_addr b + 0 + 8)) L) mx m1 /\ wmono asegs mx m1
        /\ rw_cells asegs m1 0xaa890 [C8 (Z_to_bv 64 (Z.succ (blen rr0))); C8 (Z_to_bv 64 (bhd rr0)); C8 (Z_to_bv 64 (blast rr0)); C8 (Z_to_bv 64 (bsz + qbytes rr0))]
        /\ bcells m1 pp /\ bcells m1 rr0 /\ rw_cells asegs m1 ba [C8 (Z_to_bv 64 (bhd rr0)); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 (blen bits))]
        /\ rw_cells asegs m1 (sp + -80) [C8 c0; C8 (Z_to_bv 64 (bhd pp)); C8 l0; C8 (Z_to_bv 64 (qbytes pp))])).
  { destruct rr0 as [|b2 rr1].
    - cbn [bhd_or]. cstep. (* [comment removed for export] *)
      zstepA. (* [comment removed for export] *)
      apply evtA_done. eexists. split; [reflexivity|]. cbn [bhd_or blast]. repeat (split; [assumption|]). assumption.
    - pose proof (Forall_inv OKR) as OK2. unfold bok in OK2. rewrite kHighMemBeg_val in OK2 || idtac.
      cbn [bhd_or]. zstepA. if_cases K1; zify_cond K1. 2:{ exfalso. revert K1. rewrite ?unsigned_lit by lia. lia. } clear K1.
      apply evtA_done. eexists. split; [reflexivity|]. cbn [bhd_or]. rewrite blast_cons in GQ by discriminate. repeat (split; [assumption|]). assumption. }
  clear MI MU WM GQ QPP QRR Hb TMP. try clear m.
  intros ms1 (mx1 & -> & MI & MU & WM & GQ & QPP & QRR & Hb & TMP).
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  replace (Z.succ (blen rr0) + -1) with (blen rr0) in * by lia.
  try replace ((bsz + qbytes rr0) mod 18446744073709551616 - bsz) with (qbytes rr0) in * by (clear -CEILB QX QBL Rb4; Z.div_mod_to_equations; lia).
  try replace (bsz + qbytes rr0 - bsz) with (qbytes rr0) in * by lia.
  (* [comment removed for export] *)
  zstepA. if_cases KP; zify_cond KP.
  - (* [comment removed for export] *)
    assert (NEP : pp <> []) by (intros ->; cbn in KP; apply KP; reflexivity).
    specialize (LASTP NEP). subst a5x.
    destruct (exists_last NEP) as [pp0 [bl EP]]. subst pp. rewrite blast_app1 in *.
    assert (INl : In bl L) by (rewrite EL; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).
    assert (OKl : bok lo T bl) by (apply Forall_app in OKP; destruct OKP as [_ X]; exact (Forall_inv X)).
    apply bcellsn_app in QPP. destruct QPP as [QPP [Hl _]].
    destruct bl as [la lits lsz]. unfold bok in OKl. cbn [b_addr b_size b_items bhd_or] in Hl, OKl, INl, QPP |- *.
    assert (PL : forall a k, la <= a -> a + Z.of_nat k <= la + 8192 -> P (Z_to_bv 64 a, k)) by (intros; eapply PQB; [exact INl| cbn; lia| cbn; lia]).
    assert (APl : la + 8192 <= ba \/ ba + 8192 <= la) by (apply Forall_app in APP; destruct APP as [_ X]; pose proof (Forall_inv X) as Y; cbn in Y; lia).
    pose proof OKl as (Rl1 & Rl2 & Rl3 & Rl4 & Rl5).
    assert (APLR : Forall (fun b' => la + 8192 <= b_addr b' \/ b_addr b' + 8192 <= la) rr0).
    { apply Forall_forall. intros b' Hb'. rewrite EL in APL.
      exact (bapart_app_cross _ _ (mkBatch la lits lsz) b' APL ltac:(apply in_app_iff; right; left; reflexivity) ltac:(right; exact Hb')). }
    assert (APLP : Forall (fun b' => la + 8192 <= b_addr b' \/ b_addr b' + 8192 <= la) pp0).
    { apply Forall_forall. intros b' Hb'. rewrite EL in APL. apply bapart_app_l in APL.
      destruct (bapart_app_cross pp0 [mkBatch la lits lsz] b' (mkBatch la lits lsz) APL Hb' ltac:(left; reflexivity)); cbn [b_addr] in *; lia. }
    zstepA. (* [comment removed for export] *)
    apply unhide in OKL.
    lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m9 end.
    eapply (rec_pop_tail (pp0 ++ [mkBatch la lits lsz]) rr0 L m9 ba bsz bits);
      [exact EL| exact OKL| exact APL| exact LENL| exact QBL| exact PQB| exact MI| exact GQ| | exact QRR| | |].
    + apply bcellsn_app. split; [apply bcellsn_app; split; [exact QPP| cbn; split; [exact Hl| exact I]]| cbn; split; [exact Hb| exact I]].
    + rewrite (bhd_or_app (pp0 ++ [_]) [_]) by (intros X; apply app_eq_nil in X; destruct X; discriminate). exact TMP.
    + (* [comment removed for export] *)
      clear IH. intros m' t2' MI' MU' WM' LE GQ' QPP' QRR' TMP'.
      replace (blen (pp0 ++ [mkBatch la lits lsz]) + 1) with (blen ((pp0 ++ [mkBatch la lits lsz]) ++ [mkBatch ba bits bsz])) in TMP' |- * by (rewrite (length_app _ [mkBatch ba bits bsz]); cbn [length]; lia).
      eapply (CONT m' [mkBatch ba bits bsz] rr0).
      * apply pop_prefix_step; [rewrite qbytes_cons; cbn [b_size]; lia|]. rewrite qbytes_cons. cbn [b_size]. replace (bsz + qbytes rr0 - bsz) with (qbytes rr0) by lia. apply pop_prefix_stop. exact LE.
      * exact MI'.
      * eapply munch_trans; [exact MU| exact MU'].
      * eapply wmono_trans; [exact WM| exact WM'].
      * exact GQ'.
      * exact QPP'.
      * exact QRR'.
      * exact LE.
      * rewrite blast_app1, (qbytes_app _ [mkBatch ba bits bsz]), qbytes_cons, qbytes_nil. cbn [b_addr b_size]. rewrite Z.add_0_r. exact TMP'.
    + (* [comment removed for export] *)
      intros m' t2' MI' MU' WM' LT' GQ' QPP' QRR' TMP'.
      assert (NE' : rr0 <> []) by (intros ->; rewrite qbytes_nil in LT'; lia).
      replace (blen (pp0 ++ [mkBatch la lits lsz]) + 1) with (blen ((pp0 ++ [mkBatch la lits lsz]) ++ [mkBatch ba bits bsz])) by (rewrite (length_app _ [_]); cbn [length]; lia).
      eapply (IH ((pp0 ++ [mkBatch la lits lsz]) ++ [mkBatch ba bits bsz]) L m' _ _ _ t2' c0 l0);
        [rewrite <- app_assoc; exact EL| exact NE'| exact LT'| exact OKL| exact APL| exact LENL| exact QBL| exact PQB| exact MI'| exact GQ'| exact QPP'| exact QRR'
        | rewrite (qbytes_app _ [_]), qbytes_cons, qbytes_nil; cbn [b_size]; rewrite Z.add_0_r; exact TMP'
        | intros _; rewrite blast_app1; reflexivity |].
      (* [comment removed for export] *)
      intros m'' popped rr' a5' a7' t0' t1' t2'' PP MI'' MU'' WM'' GQ'' QPP'' QRR'' LE'' TMP''.
      rewrite <- (app_assoc (pp0 ++ [mkBatch la lits lsz]) [mkBatch ba bits bsz] popped) in *. change ([mkBatch ba bits bsz] ++ popped) with (mkBatch ba bits bsz :: popped) in *.
      eapply (CONT m'' (mkBatch ba bits bsz :: popped) rr').
      * apply pop_prefix_step; [rewrite qbytes_cons; cbn [b_size]; lia|]. rewrite qbytes_cons. cbn [b_size]. replace (bsz + qbytes rr0 - bsz) with (qbytes rr0) by lia. exact PP.
      * exact MI''.
      * eapply munch_trans; [exact MU| eapply munch_trans; [exact MU'| exact MU'']].
      * eapply wmono_trans; [exact WM| eapply wmono_trans; [exact WM'| exact WM'']].
      * exact GQ''.
      * exact QPP''.
      * exact QRR''.
      * exact LE''.
      * exact TMP''.
  - (* [comment removed for export] *)
    assert (EP : pp = []) by (destruct pp; [reflexivity| exfalso; cbn [length] in KP; rewrite Nat2Z.inj_succ in KP; revert KP; rewrite ?unsigned_lit by lia; lia]).
    subst pp. cbn [bhd_or qbytes app] in *.
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    apply unhide in OKL.
    lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m9 end.
    eapply (rec_pop_tail [] rr0 L m9 ba bsz bits);
      [exact EL| exact OKL| exact APL| exact LENL| exact QBL| exact PQB| exact MI| exact GQ| cbn; split; [exact Hb| exact I] | exact QRR| cbn [app bhd_or b_addr]; exact TMP | |].
    + (* [comment removed for export] *)
      clear IH. intros m' t2' MI' MU' WM' LE GQ' QPP' QRR' TMP'.
      change (0 + 1) with (blen ([] ++ [mkBatch ba bits bsz])) in TMP' |- *.
      eapply (CONT m' [mkBatch ba bits bsz] rr0).
      * apply pop_prefix_step; [rewrite qbytes_cons; cbn [b_size]; lia|]. rewrite qbytes_cons. cbn [b_size]. replace (bsz + qbytes rr0 - bsz) with (qbytes rr0) by lia. apply pop_prefix_stop. exact LE.
      * exact MI'.
      * eapply munch_trans; [exact MU| exact MU'].
      * eapply wmono_trans; [exact WM| exact WM'].
      * exact GQ'.
      * exact QPP'.
      * exact QRR'.
      * exact LE.
      * cbn [app blast bhd_or b_addr]. rewrite qbytes_cons, qbytes_nil, Z.add_0_r. cbn [b_size]. exact TMP'.
    + (* [comment removed for export] *)
      intros m' t2' MI' MU' WM' LT' GQ' QPP' QRR' TMP'.
      assert (NE' : rr0 <> []) by (intros ->; rewrite qbytes_nil in LT'; lia).
      change (Z_to_bv 64 (0 + 1)) with (Z_to_bv 64 (blen [mkBatch ba bits bsz])).
      eapply (IH [mkBatch ba bits bsz] L m' _ _ _ t2' c0 l0);
        [exact EL| exact NE'| exact LT'| exact OKL| exact APL| exact LENL| exact QBL| exact PQB| exact MI'| exact GQ'| exact QPP'| exact QRR'
        | rewrite qbytes_cons, qbytes_nil; cbn [b_size]; rewrite Z.add_0_r; exact TMP'
        | intros _; reflexivity |].
      intros m'' popped rr' a5' a7' t0' t1' t2'' PP MI'' MU'' WM'' GQ'' QPP'' QRR'' LE'' TMP''.
      eapply (CONT m'' (mkBatch ba bits bsz :: popped) rr').
      * apply pop_prefix_step; [rewrite qbytes_cons; cbn [b_size]; lia|]. rewrite qbytes_cons. cbn [b_size]. replace (bsz + qbytes rr0 - bsz) with (qbytes rr0) by lia. exact PP.
      * exact MI''.
      * eapply munch_trans; [exact MU| eapply munch_trans; [exact MU'| exact MU'']].
      * eapply wmono_trans; [exact WM| eapply wmono_trans; [exact WM'| exact WM'']].
      * exact GQ''.
      * exact QPP''.
      * exact QRR''.
      * exact LE''.
      * exact TMP''.
Qed.


(* [comment removed for export] *)
Definition rheadW (sp : Z) (gq : list batch) : list (Z * Z) :=
  [(sp + -96, sp); (0xaa888, 0xaa88c); (0xaa890, 0xaa8b0)] ++ map (fun x => (x + 0, x + 0 + 8192)) (map b_addr gq).

(* [comment removed for export] *)
Lemma recycle_head : forall gq mx (ra0 t0x t1x t2x a2x a3x a4x a5x a6x a7x : word),
  Forall (bok lo T) gq -> bapart gq -> blen gq < 2^40 -> 8192 * qbytes gq < 2^60 ->
  (forall b a k, In b gq -> b_addr b <= a -> a + Z.of_nat k <= b_addr b + 8192 -> P (Z_to_bv 64 a, k)) ->
  mem_inv asegs mx -> stk asegs mx lo sp ->
  rw_cells asegs mx 0xaa888 [C4 (Z_to_bv 64 256)] ->
  rw_cells asegs mx 0xaa890 [C8 (Z_to_bv 64 (blen gq)); C8 (Z_to_bv 64 (bhd gq)); C8 (Z_to_bv 64 (blast gq)); C8 (Z_to_bv 64 (qbytes gq))] ->
  bcells mx gq -> bitemsl mx gq ->
  (forall m' gq1 emp popped kept (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' x8 x9 x18 x19 x20 : word),
     (if (kBatchSize * zlen gq <? qbytes gq) && (qbytes gq * 100 <? kBatchSize * zlen gq * 200) then merge_batches gq else (gq, [])) = (gq1, emp) ->
     pop_prefix gq1 (qbytes gq1) qmin = (popped, kept) ->
     mem_inv asegs m' -> stk asegs m' lo (sp + -80) -> munch (rheadW sp gq) mx m' -> wmono asegs mx m' ->
     rw_cells asegs m' 0xaa888 [C4 (Z_to_bv 64 0)] ->
     rw_cells asegs m' 0xaa890 [C8 (Z_to_bv 64 (blen kept)); C8 (Z_to_bv 64 (bhd kept)); C8 (Z_to_bv 64 (blast kept)); C8 (Z_to_bv 64 (qbytes kept))] ->
     bcells m' kept -> bitemsl m' kept ->
     rw_cells asegs m' (sp + -80) [C8 (Z_to_bv 64 (blen (emp ++ popped))); C8 (Z_to_bv 64 (bhd (emp ++ popped))); C8 (Z_to_bv 64 (blast (emp ++ popped))); C8 (Z_to_bv 64 (qbytes (emp ++ popped)));
                                   C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0] ->
     bcells m' (emp ++ popped) -> bitemsl m' (emp ++ popped) -> qbytes kept <= qmin ->
     Forall (bok lo T) (kept ++ (emp ++ popped)) -> bapart (kept ++ (emp ++ popped)) ->
     (forall b, In b (kept ++ (emp ++ popped)) -> In (b_addr b) (map b_addr gq)) ->
     evtA asegs P Q (MS (mkR (Z_to_bv 64 0x34b28) (Z_to_bv 64 (sp + -80)) gp tp t0' t1' t2' x8 x9 (Z_to_bv 64 698352) (Z_to_bv 64 (sp + -80)) a2x a3x a4' a5' a6' a7'
                             x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6) F (Z_to_bv 64 0x34d20) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra0 (Z_to_bv 64 sp) gp tp t0x t1x t2x s0 s1 (Z_to_bv 64 698352) (Z_to_bv 64 qmin) a2x a3x a4x a5x a6x a7x
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x349b8) fc None mx (seg_rom asegs)).
Proof. aceil.
  intros gq mx ra0 t0x t1x t2x a2x a3x a4x a5x a6x a7x OKL APL LENL QBL PQB MI SK QMTX GQ QC QI CONT.
  pose proof LOC as LOC0. aceil.
  pose proof (qbytes_nonneg lo T gq OKL) as QNN. pose proof (qbytes_lb lo T gq OKL) as QLB.
  assert (PQA : forall a0 a k, In a0 (map b_addr gq) -> a0 <= a -> a + Z.of_nat k <= a0 + 8192 -> P (Z_to_bv 64 a, k)).
  { intros a0 a k Hin H1 H2. apply in_map_iff in Hin. destruct Hin as (b & <- & Hb). exact (PQB b a k Hb H1 H2). }
  assert (MU : munch (rheadW sp gq) mx mx) by apply munch_refl. unfold rheadW in MU.
  assert (WM : wmono asegs mx mx) by apply wmono_refl.
  rewrite <- (Z_to_bv_bv_unsigned' sp) in SK |- * || idtac.
  carve_frame 80%nat SK.
  do 7 zstepA. (* [comment removed for export] *)
  do 4 zstepA. (* [comment removed for export] *)
  do 4 zstepA. (* [comment removed for export] *)
  replace (Z.land (697624 + 728 + 152) 18446744073709551612) with 698504 by reflexivity.
  zstepA. (* [comment removed for export] *) change (sx32 (Z_to_bv 64 256)) with (Z_to_bv 64 256).
  do 4 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?Z.shiftl_mul_pow2 by lia. intros K1. clear -CEILB K1 QLB LENL QNN QBL. Z.div_mod_to_equations. lia. } clear K1.
  (* [comment removed for export] *)
  apply (rwc_split asegs _ _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0]) in FR. cbn [cells_size csize Nat.add Nat.mul] in FR. destruct FR as [TMP FR]. replace (sp + -80 + Z.of_nat 32) with (sp + -48) in FR by lia.
  assert (TAIL : forall m1 gq1 emp (t0' t1' t2' a4' a5' a7' t3' t4' t5' rax x8 x9 x18 x19 x20 : word),
      (if (kBatchSize * zlen gq <? qbytes gq) && (qbytes gq * 100 <? kBatchSize * zlen gq * 200) then merge_batches gq else (gq, [])) = (gq1, emp) ->
      mem_inv asegs m1 -> stk asegs m1 lo (sp + -80) -> munch (rheadW sp gq) mx m1 -> wmono asegs mx m1 ->
      rw_cells asegs m1 0xaa888 [C4 (Z_to_bv 64 257)] ->
      rw_cells asegs m1 0xaa890 [C8 (Z_to_bv 64 (blen gq1)); C8 (Z_to_bv 64 (bhd gq1)); C8 (Z_to_bv 64 (blast gq1)); C8 (Z_to_bv 64 (qbytes gq1))] ->
      bcells m1 gq1 -> bitemsl m1 gq1 ->
      rw_cells asegs m1 (sp + -80) [C8 (Z_to_bv 64 (blen emp)); C8 (Z_to_bv 64 (bhd emp)); C8 (Z_to_bv 64 (blast emp)); C8 (Z_to_bv 64 (qbytes emp))] ->
      rw_cells asegs m1 (sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0] ->
      bcells m1 emp -> bitemsl m1 emp ->
      Forall (bok lo T) (gq1 ++ emp) -> bapart (gq1 ++ emp) -> (forall b, In b (gq1 ++ emp) -> In (b_addr b) (map b_addr gq)) ->
      blen (gq1 ++ emp) = blen gq -> qbytes gq1 + qbytes emp = qbytes gq ->
      evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (sp + -80)) gp tp t0' t1' t2' x8 x9 (Z_to_bv 64 698352) (Z_to_bv 64 qmin) a2x a3x a4' a5' (Z_to_bv 64 (blen gq1)) a7'
                              x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6) F (Z_to_bv 64 0x34a74) fc None m1 (seg_rom asegs))).
  { clear MI SK QMTX GQ QC QI MU WM TMP FR.
    intros m1 gq1 emp t0' t1' t2' a4' a5' a7' t3' t4' t5' rax x8 x9 x18 x19 x20 MRG MI SK MU WM QMTX GQ QC QI TMP FR QE IE OK1 AP1 IN1 LEN1 QB1.
    unfold rheadW in MU.
    assert (OKG : Forall (bok lo T) gq1) by (apply Forall_app in OK1; tauto). assert (OKE : Forall (bok lo T) emp) by (apply Forall_app in OK1; tauto).
    pose proof (qbytes_nonneg lo T gq1 OKG) as QG0. pose proof (qbytes_nonneg lo T emp OKE) as QE0.
    assert (PQ1 : forall b a k, In b (emp ++ gq1) -> b_addr b <= a -> a + Z.of_nat k <= b_addr b + 8192 -> P (Z_to_bv 64 a, k)).
    { intros b a k Hb H1 H2. apply (PQA (b_addr b)); [| lia| lia]. apply IN1. apply in_app_iff. apply in_app_iff in Hb. tauto. }
    (* [comment removed for export] *)
    assert (FIN : forall m2 popped kept (t0'' t1'' t2'' a5'' a7'' : word),
      pop_prefix gq1 (qbytes gq1) qmin = (popped, kept) ->
      mem_inv asegs m2 -> munch ([(sp + -96, sp); (0xaa888, 0xaa88c); (0xaa890, 0xaa8b0)] ++ map (fun x => (x + 0, x + 0 + 8192)) (map b_addr gq)) mx m2 -> wmono asegs mx m2 ->
      rw_cells asegs m2 0xaa888 [C4 (Z_to_bv 64 257)] ->
      rw_cells asegs m2 0xaa890 [C8 (Z_to_bv 64 (blen kept)); C8 (Z_to_bv 64 (bhd kept)); C8 (Z_to_bv 64 (blast kept)); C8 (Z_to_bv 64 (qbytes kept))] ->
      bcells m2 (emp ++ popped) -> bcells m2 kept -> qbytes kept <= qmin ->
      rw_cells asegs m2 (sp + -80) [C8 (Z_to_bv 64 (blen (emp ++ popped))); C8 (Z_to_bv 64 (bhd (emp ++ popped))); C8 (Z_to_bv 64 (blast (emp ++ popped))); C8 (Z_to_bv 64 (qbytes (emp ++ popped)))] ->
      rw_cells asegs m2 (sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0] ->
      bitemsl m2 gq1 -> bitemsl m2 emp -> stk asegs m2 lo (sp + -80) ->
      evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (sp + -80)) gp tp t0'' t1'' t2'' x8 x9 (Z_to_bv 64 698352) (Z_to_bv 64 qmin) a2x a3x (Z_to_bv 64 (blen (emp ++ popped))) a5'' (Z_to_bv 64 (blen kept)) a7''
                              x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6) F (Z_to_bv 64 0x34b10) fc None m2 (seg_rom asegs))).
    { clear MI MU WM QMTX GQ QC TMP FR QI IE SK.
      intros m2 popped kept t0'' t1'' t2'' a5'' a7'' PP MI MU WM QMTX GQ QP QK LE TMP FR QI IE SK.
      pose proof (pop_prefix_split _ _ _ _ _ PP) as EG.
      assert (OKK : Forall (bok lo T) kept) by (rewrite EG in OKG; apply Forall_app in OKG; tauto).
      assert (OKP : Forall (bok lo T) (emp ++ popped)) by (rewrite EG in OKG; apply Forall_app in OKG; apply Forall_app; tauto).
      zstepA. (* [comment removed for export] *)
      match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) =>
        assert (QMB : rw_cells asegs mc 0xaa888 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C2 (Z_to_bv 64 0)])
          by (eapply rw_cells_reshape; [| | exact QMTX]; [cbn; tauto| vm_compute; reflexivity]) end.
      clear QMTX.
      zstepA. (* [comment removed for export] *)
      zstepA. (* [comment removed for export] *)
      zstepA. (* [comment removed for export] *)
      match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) =>
        assert (QMTX : rw_cells asegs mc 0xaa888 [C4 (Z_to_bv 64 0)])
          by (eapply rw_cells_reshape; [| | exact QMB]; [cbn; tauto| vm_compute; reflexivity]) end.
      clear QMB.
      zstepA. (* [comment removed for export] *)
      zstepA. (* [comment removed for export] *)
      assert (PERM2 : Permutation (map b_addr (gq1 ++ emp)) (map b_addr (kept ++ (emp ++ popped)))).
      { rewrite EG, !map_app. rewrite <- app_assoc. eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- app_assoc. apply Permutation_refl. }
      eapply (CONT m2 gq1 emp popped kept); [exact MRG| exact PP| exact MI| exact SK| exact MU| exact WM| exact QMTX| exact GQ| exact QK| | | exact QP| | exact LE| | |].
      - rewrite EG in QI. apply bitemsl_app in QI. tauto.
      - eapply (rwc_join_at asegs m2 (sp + -80) (sp + -48) [_; _; _; _]); [exact TMP| exact FR| cbn; lia].
      - rewrite EG in QI. apply bitemsl_app in QI. apply bitemsl_app. tauto.
      - apply Forall_forall. intros b Hb. apply (proj1 (Forall_forall _ _) OK1). rewrite EG. rewrite !in_app_iff in Hb |- *. tauto.
      - eapply bapart_perm; [exact PERM2| exact AP1].
      - intros b Hb. apply IN1. rewrite EG. rewrite !in_app_iff in Hb |- *. tauto. }
    clear CONT.
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. if_cases KQ; zify_cond KQ.
    - (* [comment removed for export] *)
      pose proof (fun m2 => FIN m2 [] gq1) as FIN0. rewrite !app_nil_r in FIN0.
      eapply FIN0; [apply pop_prefix_stop; revert KQ; rewrite ?unsigned_lit by lia; intros KQ; lia| exact MI| exact MU| exact WM| exact QMTX| exact GQ| exact QE| exact QC
        | revert KQ; rewrite ?unsigned_lit by lia; intros KQ; lia| exact TMP| exact FR| exact QI| exact IE| exact SK].
    - zstepA. (* [comment removed for export] *)
      zstepA. (* [comment removed for export] *)
      assert (NE1 : gq1 <> []) by (intros ->; rewrite qbytes_nil in KQ; revert KQ; rewrite ?unsigned_lit by lia; lia).
      lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m9 end.
      eapply (rec_pop_loop gq1 emp (emp ++ gq1) m9);
        [reflexivity| exact NE1| revert KQ; rewrite ?unsigned_lit by lia; intros KQ; lia
        | apply Forall_app; split; [exact OKE| exact OKG]| eapply bapart_perm; [| exact AP1]; rewrite !map_app; apply Permutation_app_comm
        | rewrite length_app in LEN1 |- *; lia| rewrite qbytes_app; clear -CEILB QB1 QBL QG0 QE0 QNN; lia| exact PQ1| exact MI| exact GQ| exact QE| exact QC| exact TMP| intros _; reflexivity|].
      clear MI GQ QE QC TMP.
      intros m' popped kept a5'' a7'' t0'' t1'' t2'' PP MI MU' WM' GQ QP QK LE TMP.
      eapply (FIN m' popped kept); [exact PP| exact MI| | | | exact GQ| exact QP| exact QK| exact LE| exact TMP| | | |].
      + eapply munch_trans; [exact MU| eapply munch_cover; [exact MU'| unfold recW]].
        apply covers_app_split; [solve_covers|]. intros lo1 hi1 Hin. apply in_map_iff in Hin. destruct Hin as (b & E & Hb). injection E as <- <-.
        exists (b_addr b + 0), (b_addr b + 0 + 8192). split; [| lia]. apply in_app_iff. right. apply (in_map (fun x => (x + 0, x + 0 + 8192))). apply IN1. rewrite in_app_iff in Hb |- *. tauto.
      + eapply wmono_trans; [exact WM| exact WM'].
      + eapply rw_cells_transport; [exact QMTX| exact MU'| exact WM'|]. unfold recW. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. apply disjoint_from_app; [djs|].
        apply disjoint_bmap. intros b Hb. pose proof (proj1 (Forall_forall _ _) OK1 b ltac:(rewrite in_app_iff in Hb |- *; tauto)) as X. unfold bok in X. lia.
      + eapply rw_cells_transport; [exact FR| exact MU'| exact WM'|]. unfold recW. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul]. apply disjoint_from_app; [djs|].
        apply disjoint_bmap. intros b Hb. pose proof (proj1 (Forall_forall _ _) OK1 b ltac:(rewrite in_app_iff in Hb |- *; tauto)) as X. unfold bok in X. lia.
      + eapply bitemsl_transport; [exact QI| exact MU'| exact WM'|]. apply Forall_forall. intros b Hb. unfold recW. apply disjoint_from_app; [pose proof (proj1 (Forall_forall _ _) OKG b Hb) as X; unfold bok in X; djs|].
        apply disjoint_bmap. intros b' Hb'. pose proof (proj1 (Forall_forall _ _) OKG b Hb) as X. unfold bok in X.
        destruct (apl_in_cases (map b_addr (gq1 ++ emp)) (b_addr b) (b_addr b') AP1 ltac:(apply in_map; apply in_app_iff; left; exact Hb) ltac:(apply in_map; rewrite in_app_iff in Hb' |- *; tauto)) as [Y|Y]; [| unfold far in Y]; lia.
      + eapply bitemsl_transport; [exact IE| exact MU'| exact WM'|]. apply Forall_forall. intros b Hb. unfold recW. apply disjoint_from_app; [pose proof (proj1 (Forall_forall _ _) OKE b Hb) as X; unfold bok in X; djs|].
        apply disjoint_bmap. intros b' Hb'. pose proof (proj1 (Forall_forall _ _) OKE b Hb) as X. unfold bok in X.
        destruct (apl_in_cases (map b_addr (gq1 ++ emp)) (b_addr b) (b_addr b') AP1 ltac:(apply in_map; apply in_app_iff; right; exact Hb) ltac:(apply in_map; rewrite in_app_iff in Hb' |- *; tauto)) as [Y|Y]; [| unfold far in Y]; lia.
      + eapply stk_transport; [exact SK| exact MU'| exact WM'|]. intros x Hx. left. unfold recW. apply (proj2 (outside_app _ _ _)). split; [cbn; lia|].
        apply (proj2 (outside_forall _ _)). intros lo1 hi1 Hin. apply in_map_iff in Hin. destruct Hin as (b & E & Hb). injection E as <- <-.
        pose proof (proj1 (Forall_forall _ _) OK1 b ltac:(rewrite in_app_iff in Hb |- *; tauto)) as X. unfold bok in X. lia. }
  assert (NOMRG : forall m1 (rax x8 x9 x18 x19 x20 t0' t1' t2' a4' a5' a7' : word),
      (kBatchSize * zlen gq <? qbytes gq) && (qbytes gq * 100 <? kBatchSize * zlen gq * 200) = false ->
      mem_inv asegs m1 -> stk asegs m1 lo (sp + -80) -> munch (rheadW sp gq) mx m1 -> wmono asegs mx m1 ->
      rw_cells asegs m1 0xaa888 [C4 (Z_to_bv 64 257)] ->
      rw_cells asegs m1 0xaa890 [C8 (Z_to_bv 64 (blen gq)); C8 (Z_to_bv 64 (bhd gq)); C8 (Z_to_bv 64 (blast gq)); C8 (Z_to_bv 64 (qbytes gq))] ->
      bcells m1 gq -> bitemsl m1 gq ->
      rw_cells asegs m1 (sp + -80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
      rw_cells asegs m1 (sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0] ->
      evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (sp + -80)) gp tp t0' t1' t2' x8 x9 (Z_to_bv 64 698352) (Z_to_bv 64 qmin) a2x a3x a4' a5' (Z_to_bv 64 (blen gq)) a7'
              x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34a74) fc None m1 (seg_rom asegs))).
  { intros m1 rax x8 x9 x18 x19 x20 t0' t1' t2' a4' a5' a7' NC MI1 SK1 MU1 WM1 Q1 G1 C1 I1 T1 F1.
    eapply (TAIL m1 gq []); rewrite ?NC, ?app_nil_r; cbn [bcellsn bitemsl length blast bhd_or Z.of_nat]; rewrite ?qbytes_nil; try eassumption; try reflexivity; try exact I.
    - intros b Hb. apply in_map. exact Hb.
    - lia. }
    zstepA. if_cases K2; zify_cond K2.
    - (* [comment removed for export] *)
      eapply NOMRG; try eassumption.
      apply andb_false_intro1. apply Z.ltb_ge. unfold zlen, kBatchSize. revert K2. rewrite ?Z.shiftl_mul_pow2 by lia. intros K2. clear -CEILB K2 QLB LENL QNN QBL. Z.div_mod_to_equations. lia.
    - do 4 zstepA. (* [comment removed for export] *)
      zstepA. if_cases K3; zify_cond K3.
      + eapply NOMRG; try eassumption.
        apply andb_false_intro2. apply Z.ltb_ge. unfold zlen, kBatchSize. revert K3. rewrite ?unsigned_lit by lia. intros K3. clear -CEILB K3 QLB LENL QNN QBL. Z.div_mod_to_equations. lia.
      + (* [comment removed for export] *)
        assert (MC : (kBatchSize * zlen gq <? qbytes gq) && (qbytes gq * 100 <? kBatchSize * zlen gq * 200) = true).
        { unfold zlen, kBatchSize. apply andb_true_intro. split; apply Z.ltb_lt; [revert K2; rewrite ?Z.shiftl_mul_pow2 by lia; intros K2; clear -CEILB K2 QLB LENL QNN QBL| revert K3; rewrite ?unsigned_lit by lia; intros K3; clear -CEILB K3 QLB LENL QNN QBL]; Z.div_mod_to_equations; lia. }
        do 7 zstepA. (* [comment removed for export] *)
        zstepA. (* [comment removed for export] *)
        rewrite <- (Z_to_bv_bv_unsigned' (Z_to_bv 64 (sp + -80))) in SK || idtac. carve_frame 16%nat SK.
        zstepA. zstepA. (* [comment removed for export] *)
        destruct gq as [|b1 [|b2 rest]].
        * exfalso. cbn in K2. revert K2. rewrite ?unsigned_lit by lia. cbn. lia.
        * (* [comment removed for export] *)
          cbn [bcellsn bitemsl bhd_or blast] in QC, QI, GQ. destruct QC as [Hb1 _]. destruct QI as [Ib1 _].
          pose proof (Forall_inv OKL) as OK1. cbv beta in OK1. unfold bok in OK1.
          assert (P1 : forall a k, b_addr b1 <= a -> a + Z.of_nat k <= b_addr b1 + 8192 -> P (Z_to_bv 64 a, k)) by (intros; eapply PQB; [left; reflexivity| lia| lia]).
          zstepA. (* [comment removed for export] *)
          zstepA. if_cases K4; zify_cond K4. { exfalso. revert K4. rewrite ?unsigned_lit by lia. lia. } clear K4.
          zstepA. (* [comment removed for export] *)
          cstep. (* [comment removed for export] *)
          zstepA. zstepA. zstepA. (* [comment removed for export] *)
          zstepA. zstepA. (* [comment removed for export] *)
          release_frame FR0 SK (sp + -80).
          zstepA. (* [comment removed for export] *)
          do 4 zstepA. (* [comment removed for export] *)
          zstepA. (* [comment removed for export] *)
          eapply (TAIL m [b1] []); cbn [bcellsn bitemsl app length blast bhd_or Z.of_nat]; rewrite ?qbytes_nil; try eassumption; try reflexivity; try exact I.
          -- rewrite MC. cbn [merge_batches merge_batches_aux]. reflexivity.
          -- cbn [length Z.of_nat Pos.of_succ_nat] in GQ. replace (qbytes [b1] - 0) with (qbytes [b1]) in GQ by lia. exact GQ.
          -- split; [exact Hb1| exact I].
          -- split; [exact Ib1| exact I].
          -- intros b Hb. apply in_map. exact Hb.
          -- lia.
        * cbn [bcellsn bitemsl bhd_or] in QC, QI, GQ. destruct QC as (Hb1 & Hb2 & QC). destruct QI as (Ib1 & Ib2 & QI).
          pose proof (Forall_inv OKL) as OK1. pose proof (Forall_inv (Forall_inv_tail OKL)) as OK2. cbv beta in OK1, OK2. unfold bok in OK1, OK2.
          assert (P1 : forall a k, b_addr b1 <= a -> a + Z.of_nat k <= b_addr b1 + 8192 -> P (Z_to_bv 64 a, k)) by (intros; eapply PQB; [left; reflexivity| lia| lia]).
          assert (P2 : forall a k, b_addr b2 <= a -> a + Z.of_nat k <= b_addr b2 + 8192 -> P (Z_to_bv 64 a, k)) by (intros; eapply PQB; [right; left; reflexivity| lia| lia]).
          zstepA. (* [comment removed for export] *)
          zstepA. if_cases K4; zify_cond K4. { exfalso. revert K4. rewrite ?unsigned_lit by lia. lia. } clear K4.
          zstepA. (* [comment removed for export] *)
          zstepA. if_cases K5; zify_cond K5. { exfalso. revert K5. rewrite ?unsigned_lit by lia. lia. } clear K5.
          do 4 zstepA. (* [comment removed for export] *)
          zstepA. (* [comment removed for export] *)
          lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m9 end.
          eapply (merge_loop rest b2 b1 [] [] m9 0 (qbytes (b1 :: b2 :: rest)) (map b_addr (b1 :: b2 :: rest)));
            cbn [app]; rewrite ?app_nil_r;
            [exact OKL| exact APL| exact LENL| lia| lia
            | rewrite qbytes_nil; clear -CEILB QBL QNN LENL; nia| intros b Hb; apply in_map; exact Hb| exact PQA| exact MI
            | exact GQ| cbn [bcellsn bhd_or]; exact (conj Hb1 (conj Hb2 QC))| cbn [bitemsl]; exact (conj Ib1 (conj Ib2 QI))| exact I
            | cbn [length Z.of_nat bhd_or blast]; rewrite qbytes_nil; exact TMP| exact I| exact I| exact FR0|].
          cbn [app]. clear MI GQ Hb1 Hb2 QC Ib1 Ib2 QI TMP.
          intros m' l o ex' t0' t1' t2' t3' t4' t5' a3' a4' MB MI MU' WM' GQ QC QI TMP QO IO OKL' APL' LEN' QBC INA' FRM.
          eapply stk_transport in SK; [| exact MU'| exact WM'|].
          2:{ intros x Hx. left. unfold mergeW. apply (proj2 (outside_app _ _ _)). split; [cbn; lia|].
              apply outside_amap. intros a0 Ha0. apply in_map_iff in Ha0. destruct Ha0 as (b & <- & Hb).
              pose proof (proj1 (Forall_forall _ _) OKL b Hb) as X. unfold bok in X. lia. }
          eapply rw_cells_transport in FR; [| exact MU'| exact WM'| unfold mergeW; apply disjoint_from_app; [djs| apply disjoint_amap; intros a0 Ha0; apply in_map_iff in Ha0; destruct Ha0 as (b & <- & Hb); pose proof (proj1 (Forall_forall _ _) OKL b Hb) as X; unfold bok in X; lia]].
          release_frame FRM SK (sp + -80).
          do 4 zstepA. (* [comment removed for export] *)
          zstepA. (* [comment removed for export] *)
          eapply (TAIL m' l o); try eassumption.
          -- rewrite MC. cbn [merge_batches]. exact MB.
          -- eapply munch_trans; [exact MU| eapply munch_cover; [exact MU'| unfold mergeW, rheadW]]. apply covers_app_split; [solve_covers| apply covers_self_r].
          -- eapply wmono_trans; [exact WM| exact WM'].
          -- eapply rw_cells_transport; [exact QMTX| exact MU'| exact WM'| unfold mergeW; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply disjoint_from_app; [djs| apply disjoint_amap; intros a0 Ha0; apply in_map_iff in Ha0; destruct Ha0 as (b & <- & Hb); pose proof (proj1 (Forall_forall _ _) OKL b Hb) as X; unfold bok in X; lia]].
          -- rewrite qbytes_nil in QBC. lia.
Qed.

(* [comment removed for export] *)
Lemma recycle_tail : forall mx (ra0 x8 x9 x18 x19 x20 t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x : word) (w0 w1 w2 w3 : word),
  mem_inv asegs mx -> stk asegs mx lo (sp + -80) ->
  rw_cells asegs mx (sp + -80) [C8 w0; C8 w1; C8 w2; C8 w3; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra0] ->
  (forall m', mem_inv asegs m' -> stk asegs m' lo sp -> munch [] mx m' -> wmono asegs mx m' ->
     evtA asegs P Q (MS (mkR ra0 (Z_to_bv 64 sp) gp tp t0x t1x t2x s0 s1 a0x a1x a2x a3x a4x a5x a6x a7x
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (ret_pc ra0) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR (Z_to_bv 64 0x34b28) (Z_to_bv 64 (sp + -80)) gp tp t0x t1x t2x x8 x9 a0x a1x a2x a3x a4x a5x a6x a7x
                          x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6) F (Z_to_bv 64 0x34b28) fc None mx (seg_rom asegs)).
Proof. aceil.
  intros mx ra0 x8 x9 x18 x19 x20 t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x w0 w1 w2 w3 MI SK FR CONT.
  pose proof LOC as LOC0. aceil.
  assert (MU : munch [] mx mx) by apply munch_refl. assert (WM : wmono asegs mx mx) by apply wmono_refl.
  do 6 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  release_frame FR SK sp.
  zstepA. (* [comment removed for export] *)
  eapply CONT; [exact MI| | exact MU| exact WM]. replace (sp + -80 + 80) with sp in SK by lia. exact SK.
Qed.
End RECYCLE.
End RC__1.
