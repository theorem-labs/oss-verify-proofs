(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxfInst CxfL1 CxfL2 CxfL3 CxfLeaf CxfNat.
Import ListNotations.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CXFIL.
Import CXFI.
Notation "x && y" := (if x then y else false) (at level 40, left associativity) : bool_scope.
Notation "x || y" := (if x then true else y) (at level 50, left associativity) : bool_scope.
Import AX2.
Import AX2L.
Import APC.
Import APCL.
Definition smemo : Type := list (expr * expr).
Lemma L_CXFIL_smemo : @smemo = @CXFI.smemo.
Proof. unfold smemo. reflexivity. Qed.

Definition sm_get (m : smemo) (x : expr) : option expr :=
  match m with
  | [] => None
  | (k, v) :: _ => if expr_eqb x k then Some v else None
  end.
Lemma L_CXFIL_sm_get : @sm_get = @CXFI.sm_get.
Proof. unfold sm_get. rewrite ?L_CXFIL_smemo, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Section Pass.
Variables (J : nat) (e : expr).
Definition sm_ok (m : smemo) : Prop := forall k v, In (k, v) m -> v = esubst J e k.
Definition bsubM (x : expr) (m : smemo) : expr * smemo :=
  match x with
  | ELit _ => (x, m)
  | EVar n => ((if CXNAT.eqbF n J then e else x), m)
  | _ => match sm_get m x with
         | Some v => (v, m)
         | None => let v := esubst J e x in (v, [(x, v)])
         end
  end.
Definition asubM (a : saddr) (m : smemo) : saddr * smemo := let '(b, m') := bsubM (a_base a) m in (SA b (a_off a), m').
Definition ksubM (K : kentry) (m : smemo) : kentry * smemo :=
  match K with
  | KWord a w v => let '(a', m') := asubM a m in (KWord a' w (esubst J e v), m')
  | KZero a n => let '(a', m') := asubM a m in (KZero a' (esubst J e n), m')
  | KBlob a n k => let '(a', m') := asubM a m in (KBlob a' (esubst J e n) k, m')
  | KImg lo hi => (K, m)
  | KAlign x mm => (KAlign (esubst J e x) mm, m)
  | KRange x lo hi => (KRange (esubst J e x) lo hi, m)
  | KWr a n => let '(a', m') := asubM a m in (KWr a' (esubst J e n), m')
  | KDisj a1 n1 a2 n2 => let '(a1', m1) := asubM a1 m in let '(a2', m2) := asubM a2 m1 in (KDisj a1' (esubst J e n1) a2' (esubst J e n2), m2)
  | KFill a n c => let '(a', m') := asubM a m in (KFill a' (esubst J e n) c, m')
  | KUnk a n => let '(a', m') := asubM a m in (KUnk a' (esubst J e n), m')
  end.
Fixpoint knsubM (k : list kentry) (m : smemo) : list kentry :=
  match k with
  | [] => []
  | K :: r => let '(K', m') := ksubM K m in K' :: knsubM r m'
  end.
End Pass.
Lemma L_CXFIL_sm_ok : @sm_ok = @CXFI.sm_ok.
Proof. unfold sm_ok. rewrite ?L_CXFIL_smemo, ?AX2L.L_AX2L_esubst, ?APCL.L_APCL_esubst. reflexivity. Qed.

Lemma L_CXFIL_bsubM : @bsubM = @CXFI.bsubM.
Proof. unfold bsubM. rewrite ?L_CXFIL_smemo, ?L_CXFIL_sm_get, ?AX2L.L_AX2L_esubst, ?APCL.L_APCL_esubst, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_CXFIL_asubM : @asubM = @CXFI.asubM.
Proof. unfold asubM. rewrite ?L_CXFIL_smemo, ?L_CXFIL_bsubM. reflexivity. Qed.

Lemma L_CXFIL_ksubM : @ksubM = @CXFI.ksubM.
Proof. unfold ksubM. rewrite ?L_CXFIL_smemo, ?L_CXFIL_asubM, ?AX2L.L_AX2L_esubst, ?APCL.L_APCL_esubst. reflexivity. Qed.

Lemma L_CXFIL_knsubM : @knsubM = @CXFI.knsubM.
Proof. unfold knsubM. rewrite ?L_CXFIL_smemo, ?L_CXFIL_ksubM. reflexivity. Qed.

Fixpoint rebuild (x : expr) : expr :=
  match x with
  | ELit _ => x
  | EVar _ => x
  | EAlu op a b => mkAlu op (rebuild a) (rebuild b)
  | EAluw op a b => mkAluw op (rebuild a) (rebuild b)
  | EMd op a b => mkMd op (rebuild a) (rebuild b)
  | EMdw op a b => mkMdw op (rebuild a) (rebuild b)
  | EExt sx lo n a => EExt sx lo n (rebuild a)
  | EBlob _ _ _ _ => x
  end.
Lemma L_CXFIL_rebuild : @rebuild = @CXFI.rebuild.
Proof. unfold rebuild. rewrite ?AX2L.L_AX2L_mkAlu, ?AX2L.L_AX2L_mkAluw, ?AX2L.L_AX2L_mkMd, ?AX2L.L_AX2L_mkMdw. reflexivity. Qed.

Fixpoint esubst_seq (s : list (nat * expr)) (x : expr) : expr :=
  match s with
  | [] => x
  | (J, e) :: r => esubst J e (esubst_seq r x)
  end.
Lemma L_CXFIL_esubst_seq : @esubst_seq = @CXFI.esubst_seq.
Proof. unfold esubst_seq. rewrite ?AX2L.L_AX2L_esubst, ?APCL.L_APCL_esubst. reflexivity. Qed.

Definition stable (s : list (nat * expr)) (x : expr) : bool :=
  if forallb (fun p => negb (mentions_var (fst p) x)) s then expr_eqb (rebuild x) x else false.
Lemma L_CXFIL_stable : @stable = @CXFI.stable.
Proof. unfold stable. rewrite ?L_CXFIL_rebuild, ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_mentions_var. reflexivity. Qed.

Definition ksubst_seq (s : list (nat * expr)) (K : kentry) : kentry := fold_right (fun p K => ksubst (fst p) (snd p) K) K s.
Lemma L_CXFIL_ksubst_seq : @ksubst_seq = @CXFI.ksubst_seq.
Proof. unfold ksubst_seq. rewrite ?APCL.L_APCL_ksubst. reflexivity. Qed.

Definition astable (s : list (nat * expr)) (a : saddr) : bool := stable s (a_base a).
Lemma L_CXFIL_astable : @astable = @CXFI.astable.
Proof. unfold astable. rewrite ?L_CXFIL_stable. reflexivity. Qed.

Definition kstable (s : list (nat * expr)) (K : kentry) : bool :=
  match K with
  | KWord a _ v => if astable s a then stable s v else false
  | KZero a n | KWr a n | KUnk a n | KBlob a n _ | KFill a n _ => if astable s a then stable s n else false
  | KImg _ _ => true
  | KAlign x _ | KRange x _ _ => stable s x
  | KDisj a1 n1 a2 n2 => if astable s a1 then if stable s n1 then if astable s a2 then stable s n2 else false else false else false
  end.
Lemma L_CXFIL_kstable : @kstable = @CXFI.kstable.
Proof. unfold kstable. rewrite ?L_CXFIL_stable, ?L_CXFIL_astable. reflexivity. Qed.

Fixpoint mk_dom (s : list (nat * expr)) : ptree unit :=
  match s with [] => PTLeaf | (J, _) :: r => pt_set (vkey J) tt (mk_dom r) end.
Lemma L_CXFIL_mk_dom : @mk_dom = @CXFI.mk_dom.
Proof. unfold mk_dom. rewrite ?AX2L.L_AX2L_pt_set, ?APCL.L_APCL_vkey. reflexivity. Qed.

Fixpoint vars_free (dom : ptree unit) (x : expr) : bool :=
  match x with
  | ELit _ => true
  | EVar n => match pt_get dom (vkey n) with None => true | Some _ => false end
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if vars_free dom a then vars_free dom b else false
  | EExt _ _ _ a => vars_free dom a
  | EBlob _ _ _ _ => true
  end.
Lemma L_CXFIL_vars_free : @vars_free = @CXFI.vars_free.
Proof. unfold vars_free. rewrite ?AX2L.L_AX2L_pt_get, ?APCL.L_APCL_vkey. reflexivity. Qed.

Definition stableD (dom : ptree unit) (x : expr) : bool := if vars_free dom x then expr_eqb (rebuild x) x else false.
Lemma L_CXFIL_stableD : @stableD = @CXFI.stableD.
Proof. unfold stableD. rewrite ?L_CXFIL_rebuild, ?L_CXFIL_vars_free, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Definition bcache : Type := option (expr * bool).
Lemma L_CXFIL_bcache : @bcache = @CXFI.bcache.
Proof. unfold bcache. reflexivity. Qed.

Definition bflag (dom : ptree unit) (b : expr) (c : bcache) : bool * bcache :=
  match c with
  | Some (b0, f) => if expr_eqb b b0 then (f, c) else let f' := stableD dom b in (f', Some (b, f'))
  | None => let f' := stableD dom b in (f', Some (b, f'))
  end.
Lemma L_CXFIL_bflag : @bflag = @CXFI.bflag.
Proof. unfold bflag. rewrite ?L_CXFIL_stableD, ?L_CXFIL_bcache, ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Definition bc_ok (dom : ptree unit) (c : bcache) : Prop := forall b0 f, c = Some (b0, f) -> f = stableD dom b0.
Lemma L_CXFIL_bc_ok : @bc_ok = @CXFI.bc_ok.
Proof. unfold bc_ok. rewrite ?L_CXFIL_stableD, ?L_CXFIL_bcache. reflexivity. Qed.

Definition kstableC (dom : ptree unit) (K : kentry) (c : bcache) : bool * bcache :=
  match K with
  | KWord a _ v => let '(f, c') := bflag dom (a_base a) c in ((if f then stableD dom v else false), c')
  | KZero a n | KWr a n | KUnk a n | KBlob a n _ | KFill a n _ => let '(f, c') := bflag dom (a_base a) c in ((if f then stableD dom n else false), c')
  | KImg _ _ => (true, c)
  | KAlign x _ | KRange x _ _ => (stableD dom x, c)
  | KDisj a1 n1 a2 n2 =>
      let '(f1, c1) := bflag dom (a_base a1) c in let '(f2, c2) := bflag dom (a_base a2) c1 in
      ((if f1 then if stableD dom n1 then if f2 then stableD dom n2 else false else false else false), c2)
  end.
Lemma L_CXFIL_kstableC : @kstableC = @CXFI.kstableC.
Proof. unfold kstableC. rewrite ?L_CXFIL_stableD, ?L_CXFIL_bcache, ?L_CXFIL_bflag. reflexivity. Qed.

Fixpoint kn_skip (s : list (nat * expr)) (dom : ptree unit) (k : list kentry) (c : bcache) : list kentry :=
  match k with
  | [] => []
  | K :: r => let '(ok, c') := kstableC dom K c in (if ok then K else ksubst_seq s K) :: kn_skip s dom r c'
  end.
Lemma L_CXFIL_kn_skip : @kn_skip = @CXFI.kn_skip.
Proof. unfold kn_skip. rewrite ?L_CXFIL_ksubst_seq, ?L_CXFIL_bcache, ?L_CXFIL_kstableC. reflexivity. Qed.

Definition inst_m (inv : acs) (J : nat) (e : expr) : acs :=
  ACS (mk_ss (pc inv) (map (esubst J e) (s_regs (a_ss inv))) (knsubM J e (kn inv) []) (nxt inv))
      (map (msubst J e) (a_maps inv)) (a_totsz inv) (a_ylo inv) (a_eager inv)
      (map (psubst J e) (a_vis inv)) (map (psubst J e) (a_ghost inv)) (a_abytes inv)
      (esubst J e (a_brk inv)) (fsubst J e (a_fd inv)) (a_tidset inv).
Lemma L_CXFIL_inst_m : @inst_m = @CXFI.inst_m.
Proof. unfold inst_m. rewrite ?L_CXFIL_knsubM, ?AX2L.L_AX2L_esubst, ?APCL.L_APCL_esubst, ?APCL.L_APCL_fsubst, ?APCL.L_APCL_kn, ?APCL.L_APCL_mk_ss, ?APCL.L_APCL_msubst, ?APCL.L_APCL_nxt, ?APCL.L_APCL_pc, ?APCL.L_APCL_psubst. reflexivity. Qed.

Fixpoint inst_list_m (ch : acs) (s : list (nat * expr)) : acs :=
  match s with
  | [] => ch
  | (J, e) :: r => inst_m (inst_list_m ch r) J e
  end.
Lemma L_CXFIL_inst_list_m : @inst_list_m = @CXFI.inst_list_m.
Proof. unfold inst_list_m. rewrite ?L_CXFIL_inst_m. reflexivity. Qed.

Definition inst_list_s (ch : acs) (s : list (nat * expr)) : acs :=
  match s with
  | [] => ch
  | _ => set_kn (inst_list_m (set_kn ch []) s) (kn_skip s (mk_dom s) (kn ch) None)
  end.
Lemma L_CXFIL_inst_list_s : @inst_list_s = @CXFI.inst_list_s.
Proof. unfold inst_list_s. rewrite ?L_CXFIL_mk_dom, ?L_CXFIL_kn_skip, ?L_CXFIL_inst_list_m, ?APCL.L_APCL_kn, ?APCL.L_APCL_set_kn. reflexivity. Qed.

End CXFIL.
