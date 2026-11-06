(* K0Closure.v -- K0's universe closure as ONE checked theorem (a Theorem Labs lane's route (b), 2026-10-29 15:04Z).

   A function's entry context is `raZ regs :: spine ch`: its return address, then the return addresses of the
   frame-pointer chain its s0 reaches (YCbq.v:222 spine).  An image's context tables (lib/A/ACej.v CTX_<f>, from
   universe.py (sha256 8510965be502; internal record)) list the contexts each function and each allocator entry can see.  The tables are
   CLOSED when every call edge F -r-> G carries every context of F into G's table:
     K0Lit   [r]           the caller's s0 ends the chain (an integer, a heap / static / fake-stack pointer: below sp,
                           so YG00.v:367 bad_next holds and chain_pre gives ch = []), or the caller's frame lies within
                           16 bytes of the stack top;
     K0Fp    r :: c        the caller's s0 is its own frame pointer, so the chain starts with the caller's record;
     K0Pass  r :: tl c     the caller's s0 is its caller's frame pointer (the caller's own chain, without its ra);
     K0Tail  c             a tail call: the callee runs with the caller's ra and s0.
   and when every allocator entry context y gives a trace in the universe U (k0_trace pc0 y is exactly
   call_trace_of_spine's right-hand side, YCbq.v:2802).  k0_closed decides both by computation; the image file proves
   it by vm_compute once, and the lemmas below give the walks (k0_callee: the callee's context premise from the
   caller's) and the allocator instance (k0_call_trace: the depot's universe premise from the context premise). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0d YCbq.
Import ListNotations.
Local Open Scope Z_scope.

Inductive k0kind : Set := K0Lit | K0Fp | K0Pass | K0Tail.

Definition k0kind_eqb (a b : k0kind) : bool :=
  match a, b with
  | K0Lit, K0Lit | K0Fp, K0Fp | K0Pass, K0Pass | K0Tail, K0Tail => true
  | _, _ => false
  end.

(* the callee's entry context from the caller's context c, at return site r *)
Definition k0_out (k : k0kind) (r : Z) (c : list Z) : list Z :=
  match k with K0Lit => [r] | K0Fp => r :: c | K0Pass => r :: tl c | K0Tail => c end.

(* the trace the allocator stores at entry context y (YCbq.v:2802 call_trace_of_spine) *)
Definition k0_trace (pc0 : Z) (y : list Z) : list Z :=
  firstn kUnwindMax (pc0 :: flat_map (fun ra => if ra =? pc0 then [] else [ra]) y).

Fixpoint k0_eqZL (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Z.eqb x y && k0_eqZL a' b'
  | _, _ => false
  end.
Fixpoint k0_eqZLL (a b : list (list Z)) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => k0_eqZL x y && k0_eqZLL a' b'
  | _, _ => false
  end.
Fixpoint k0_mem (t : list Z) (l : list (list Z)) : bool :=
  match l with [] => false | u :: l' => k0_eqZL t u || k0_mem t l' end.
Fixpoint k0_all {X} (f : X -> bool) (l : list X) : bool :=
  match l with [] => true | x :: l' => f x && k0_all f l' end.

Lemma k0_eqZL_eq : forall a b, k0_eqZL a b = true -> a = b.
Proof.
  induction a as [|x a IH]; destruct b as [|y b]; cbn; intros H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. exact (IH b H2).
Qed.
Lemma k0_eqZLL_eq : forall a b, k0_eqZLL a b = true -> a = b.
Proof.
  induction a as [|x a IH]; destruct b as [|y b]; cbn; intros H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. f_equal; [exact (k0_eqZL_eq x y H1) | exact (IH b H2)].
Qed.
Lemma k0_mem_In : forall t l, k0_mem t l = true -> In t l.
Proof.
  induction l as [|u l IH]; cbn; intros H; [discriminate|].
  apply orb_prop in H as [H|H]; [left; symmetry; exact (k0_eqZL_eq t u H) | right; exact (IH H)].
Qed.
Lemma k0_all_In : forall {X} (f : X -> bool) l x, k0_all f l = true -> In x l -> f x = true.
Proof.
  intros X f. induction l as [|y l IH]; cbn; intros x H Hin; [destruct Hin|].
  apply andb_prop in H as [H1 H2]. destruct Hin as [<-|Hin]; [exact H1 | exact (IH x H2 Hin)].
Qed.
Lemma k0kind_eqb_eq : forall a b, k0kind_eqb a b = true -> a = b.
Proof. intros [] []; cbn; intros H; try discriminate; reflexivity. Qed.

(* an edge: (caller's table, return site, callee's table, kind); a site table: (pc0, the allocator entry table) *)
Definition k0_edge : Type := (list (list Z) * Z * list (list Z) * k0kind)%type.
Definition k0_edge_ok (e : k0_edge) : bool :=
  match e with (CF, r, CG, k) => k0_all (fun c => k0_mem (k0_out k r c) CG) CF end.
Definition k0_site_ok (U : list (list Z)) (s : Z * list (list Z)) : bool :=
  match s with (pc0, L) => k0_mem [pc0] U && k0_all (fun y => k0_mem (k0_trace pc0 y) U) L end.
Definition k0_closed (E : list k0_edge) (A : list (Z * list (list Z))) (U : list (list Z)) : bool :=
  k0_all k0_edge_ok E && k0_all (k0_site_ok U) A.

Definition k0_has_edge (E : list k0_edge) (CF : list (list Z)) (r : Z) (CG : list (list Z)) (k : k0kind) : bool :=
  existsb (fun e => match e with (CF', r', CG', k') =>
    k0_eqZLL CF CF' && Z.eqb r r' && k0_eqZLL CG CG' && k0kind_eqb k k' end) E.
Definition k0_has_site (A : list (Z * list (list Z))) (pc0 : Z) (L : list (list Z)) : bool :=
  existsb (fun s => match s with (p, L') => Z.eqb pc0 p && k0_eqZLL L L' end) A.

Section closure.
Variables (E : list k0_edge) (A : list (Z * list (list Z))) (U : list (list Z)).
Hypothesis CL : k0_closed E A U = true.

(* THE CALLEE'S CONTEXT FROM THE CALLER'S: one listed edge carries every context of the caller's table *)
Lemma k0_callee : forall CF r CG k, k0_has_edge E CF r CG k = true ->
  forall c, In c CF -> In (k0_out k r c) CG.
Proof.
  intros CF r CG k H c Hc. apply existsb_exists in H as ([[[CF' r'] CG'] k'] & Hin & Heq).
  apply andb_prop in Heq as [Heq H4]. apply andb_prop in Heq as [Heq H3]. apply andb_prop in Heq as [H1 H2].
  apply k0_eqZLL_eq in H1, H3. apply Z.eqb_eq in H2. apply k0kind_eqb_eq in H4. subst CF' r' CG' k'.
  apply andb_prop in CL as [CE _].
  pose proof (k0_all_In k0_edge_ok E _ CE Hin) as HE. cbn [k0_edge_ok] in HE.
  exact (k0_mem_In _ _ (k0_all_In _ CF c HE Hc)).
Qed.
Lemma k0_callee_fp : forall CF r CG, k0_has_edge E CF r CG K0Fp = true -> forall c, In c CF -> In (r :: c) CG.
Proof. intros CF r CG H. exact (k0_callee CF r CG K0Fp H). Qed.
Lemma k0_callee_lit : forall CF r CG, k0_has_edge E CF r CG K0Lit = true -> forall c, In c CF -> In [r] CG.
Proof. intros CF r CG H. exact (k0_callee CF r CG K0Lit H). Qed.
Lemma k0_callee_pass : forall CF r CG, k0_has_edge E CF r CG K0Pass = true -> forall c, In c CF -> In (r :: tl c) CG.
Proof. intros CF r CG H. exact (k0_callee CF r CG K0Pass H). Qed.
Lemma k0_callee_tail : forall CF CG, k0_has_edge E CF 0 CG K0Tail = true -> forall c, In c CF -> In c CG.
Proof. intros CF CG H. exact (k0_callee CF 0 CG K0Tail H). Qed.

(* THE SITE TRACE IN U: every entry context of a listed allocator table, and the frame0-not-ok trace [pc0] *)
Lemma k0_site : forall pc0 L, k0_has_site A pc0 L = true ->
  In [pc0] U /\ forall y, In y L -> In (k0_trace pc0 y) U.
Proof.
  intros pc0 L H. apply existsb_exists in H as ([p L'] & Hin & Heq).
  apply andb_prop in Heq as [H1 H2]. apply Z.eqb_eq in H1. apply k0_eqZLL_eq in H2. subst p L'.
  apply andb_prop in CL as [_ CA].
  pose proof (k0_all_In (k0_site_ok U) A _ CA Hin) as HS. cbn [k0_site_ok] in HS.
  apply andb_prop in HS as [H0 HL]. split; [exact (k0_mem_In _ _ H0)|].
  intros y Hy. exact (k0_mem_In _ _ (k0_all_In _ L y HL Hy)).
Qed.

(* what the allocator instance needs: the depot's universe premise (YG0dcf.v:162-163 form) from the entry context *)
Lemma k0_call_trace : forall pc0 L, k0_has_site A pc0 L = true ->
  forall ly regs ch, In (raZ regs :: spine ch) L -> In (call_trace ly pc0 regs ch) U.
Proof.
  intros pc0 L H ly regs ch Hc. destruct (k0_site pc0 L H) as [H0 H1].
  apply call_trace_in; [exact H0|]. rewrite call_trace_of_spine. exact (H1 _ Hc).
Qed.
End closure.
