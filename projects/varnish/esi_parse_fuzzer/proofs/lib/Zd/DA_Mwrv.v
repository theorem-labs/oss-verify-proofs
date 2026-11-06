(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr MState Frame Regs6ss.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SrzEqv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState AClient.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 AInioec ALogic AInit0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AxSyioe Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm Bothny9 AsanInit Starr0h Stargqr Bothgt0 Bothrgj.

Module BothA0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Instr Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Hull Ledger Refund.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asanqj4 Asan12c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AInioec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AInv ARtStmts LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanAcct AxSyioe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm Bothny9 AsanInit Starr0h Stargqr Bothgt0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Bothgt0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require BothA0K.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Bothrgj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Bothg1t.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothny9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Starr0h OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Stargqr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothgt0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothgt0.Bothcs6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.BothA0K OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothrgj.Bothoo5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothg1t.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Definition pg (v : nat) : expr := EMd Instr.M_MUL (ELit 4096) (EVar v).
Definition e_sp0 : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 16) (EVar 6)).
Definition e_ri : expr := EAlu Instr.ALU_ADD (pg 208) (EMd Instr.M_MUL (ELit (-4096)) (EVar 209)).
(* [comment removed for export] *)
Definition LOWSHZ : Z := 2147446784.        (* [comment removed for export] *)
Definition KHIZ : Z := 17594333495296.      (* [comment removed for export] *)


(* [comment removed for export] *)
#[local] Notation I := (al_instance AL_pboth).
#[local] Notation b8 z := (Z_to_bv 8 z) (only parsing).
#[local] Notation wz z := (Z_to_bv 64 z) (only parsing).
Definition A0_CELLS : list (Z * list byte) :=
  [ (I + off_primary_reserved_size, Lib.Mem.le8 (wz kSpaceReserve));            (* [comment removed for export] *)
    (I + off_release_interval, Lib.Mem.le4 (wz 0xffffffff));                    (* [comment removed for export] *)
    (I + off_PremappedHeap, [b8 0]);                                            (* [comment removed for export] *)
    (I + off_sec_page_size, Lib.Mem.le8 (wz 4096));                             (* [comment removed for export] *)
    (I + off_sec_ptr_array_size, Lib.Mem.le8 (wz kPtrArrayReserve));            (* [comment removed for export] *)
    (I + off_q_max_size, Lib.Mem.le8 (wz kQuarantineMaxSize));                  (* [comment removed for export] *)
    (I + off_q_min_size, Lib.Mem.le8 (wz kQuarantineMinSize));                  (* [comment removed for export] *)
    (I + off_q_max_cache_size, Lib.Mem.le8 (wz kQuarantineCacheSize));          (* [comment removed for export] *)
    (I + off_max_user_malloc, Lib.Mem.le8 (wz kMaxUserDefinedMallocSize));      (* [comment removed for export] *)
    (I + off_min_redzone, Lib.Mem.le2 (wz kMinRedzone));                        (* [comment removed for export] *)
    (I + off_max_redzone, Lib.Mem.le2 (wz kMaxRedzone));                        (* [comment removed for export] *)
    (I + off_alloc_dealloc_mismatch, [b8 1]);                                   (* [comment removed for export] *)
    (al_kHighMemEnd_var AL_pboth, Lib.Mem.le8 (wz kHighMemEnd));                (* [comment removed for export] *)
    (al_kMidMemBeg_var AL_pboth, Lib.Mem.le8 (wz 0));                           (* [comment removed for export] *)
    (al_kMidMemEnd_var AL_pboth, Lib.Mem.le8 (wz 0));                           (* [comment removed for export] *)
    (al_malloc_context_size AL_pboth, Lib.Mem.le4 (wz kMallocContextSize));     (* [comment removed for export] *)
    (al_can_poison_memory AL_pboth, [b8 1]);                                    (* [comment removed for export] *)
    (al_page_size_cache AL_pboth, Lib.Mem.le8 (wz 4096));                       (* [comment removed for export] *)
    (al_may_return_null AL_pboth, [b8 1]);                                      (* [comment removed for export] *)
    (al_rss_limit_exceeded AL_pboth, [b8 0]);                                   (* [comment removed for export] *)
    (al_dying_flag AL_pboth, Lib.Mem.le4 (wz 0));                               (* [comment removed for export] *)
    (al_malloc_hooks AL_pboth, repeat (b8 0) 80);                               (* [comment removed for export] *)
    (I + off_sec_mutex, [b8 0]);                                                (* [comment removed for export] *)
    (I + off_q_cache_mutex, [b8 0]);                                            (* [comment removed for export] *)
    (I + off_q_recycle_mutex, [b8 0]);                                          (* [comment removed for export] *)
    (I + off_fallback_mutex, [b8 0]);                                           (* [comment removed for export] *)
    (al_internal_alloc_inited AL_pboth + 1, [b8 0]);                            (* [comment removed for export] *)
    (I + off_sec_n_reserved, Lib.Mem.le8 (wz 0));                               (* [comment removed for export] *)
    (I + off_sec_n_chunks, Lib.Mem.le8 (wz 0));                                 (* [comment removed for export] *)
    (I + off_q_cache_list_size, repeat (b8 0) 32);                              (* [comment removed for export] *)
    (al_internal_alloc_inited AL_pboth, [b8 0]);                                (* [comment removed for export] *)
    (al_depot_n_uniq_ids AL_pboth, Lib.Mem.le4 (wz 1));                         (* [comment removed for export] *)
    (al_stackStore AL_pboth + 8, Lib.Mem.le8 (wz kStackStoreBlockBytes));       (* [comment removed for export] *)
    (al_stackStore AL_pboth + 28, Lib.Mem.le4 (wz 0));                          (* [comment removed for export] *)
    (bv_unsigned (cl_tp LayoutPA.LPA) - 88, Lib.Mem.le8 (wz 0x608f80))          (* [comment removed for export] *)
  ].

(* [comment removed for export] *)
Definition DEPOT_SLOT_A : Z := 1718136.   (* [comment removed for export] *)
Definition DEPOT_SLOT_B : Z := 2202228.   (* [comment removed for export] *)
(* [comment removed for export] *)
Record a0kd (cs : acs) (k1 : list Z) : Prop := A0KD {
  kd_hash  : khas cs (KWord (SA (pg 480) 16) 8%nat (ELit (ADepotM.depot_hashC k1))) = true;
  kd_len   : khas cs (KWord (SA (pg 481) 0) 8%nat (ELit (Z.of_nat (length k1)))) = true;
  kd_keys  : forall t w, nth_error k1 t = Some w -> khas cs (KWord (SA (pg 481) (8 * (1 + Z.of_nat t))) 8%nat (ELit w)) = true;
  kd_frz   : khas cs (KZero (SA (pg 481) (8 * (1 + Z.of_nat (length k1)))) (ELit (kStackStoreBlockBytes - 8 * (1 + Z.of_nat (length k1))))) = true;
  kd_total : khas cs (KWord (SA (ELit 0) (al_stackStore AL_pboth)) 8%nat (ELit (1 + Z.of_nat (length k1)))) = true;
  kd_stored: khas cs (KWord (SA (ELit 0) (al_stackStore AL_pboth + 24)) 4%nat (ELit (1 + Z.of_nat (length k1)))) = true;
  kd_tab   : khas cs (KWord (SA (ELit 0) (al_theDepot AL_pboth + 4 * ADepotM.depot_bucket k1)) 4%nat (ELit 1)) = true;
  (* [comment removed for export] *)
  kd_tabo  : khas cs (KWord (SA (ELit 0) (DEPOT_SLOT_A + DEPOT_SLOT_B - (al_theDepot AL_pboth + 4 * ADepotM.depot_bucket k1))) 4%nat (ELit 0)) = true;
  kd_img_lo: khas cs (KImg 1600168 DEPOT_SLOT_A) = true;
  kd_img_md: khas cs (KImg (DEPOT_SLOT_A + 4) DEPOT_SLOT_B) = true;
  kd_img_hi: khas cs (KImg (DEPOT_SLOT_B + 4) 5859992) = true;
  kd_own   : al_theDepot AL_pboth + 4 * ADepotM.depot_bucket k1 = DEPOT_SLOT_A \/ al_theDepot AL_pboth + 4 * ADepotM.depot_bucket k1 = DEPOT_SLOT_B;
  kd_k1    : (1 <= length k1 <= 255)%nat /\ Forall (fun w => 0 <= w < 2^64) k1
}.
Definition K1_1 : list Z := [0x44500; 0x45850].
Definition K1_2 : list Z := [0x44500].
(* [comment removed for export] *)
Ltac a0kd_tac keys_tac :=
  constructor;
  lazymatch goal with
  | |- forall t w, _ -> _ => keys_tac
  | |- _ /\ _ => split; [cbn; lia|]; repeat constructor; cbn; lia
  | |- _ \/ _ => first [left; vm_compute; reflexivity | right; vm_compute; reflexivity]
  | |- _ => vm_compute; reflexivity
  end.
Lemma a0kd_s1 : a0kd HS_both2_1 K1_1.
Proof. a0kd_tac ltac:(intros [|[|[|t]]] w H; cbn in H; try discriminate; injection H as <-; vm_compute; reflexivity). Qed.
Lemma a0kd_s2 : a0kd HS_both2_2 K1_2.
Proof. a0kd_tac ltac:(intros [|[|t]] w H; cbn in H; try discriminate; injection H as <-; vm_compute; reflexivity). Qed.
Lemma a0kd_s3 : a0kd HS_both2b_1 K1_1.
Proof. a0kd_tac ltac:(intros [|[|[|t]]] w H; cbn in H; try discriminate; injection H as <-; vm_compute; reflexivity). Qed.
Lemma a0kd_s4 : a0kd HS_both2b_2 K1_2.
Proof. a0kd_tac ltac:(intros [|[|t]] w H; cbn in H; try discriminate; injection H as <-; vm_compute; reflexivity). Qed.

Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac fold_lit_mods :=
  repeat match goal with |- context [Z.modulo ?a (Z.pow ?b ?c)] =>
    is_zlit a; is_zlit b; is_zlit c; let v := eval vm_compute in (Z.modulo a (Z.pow b c)) in change (Z.modulo a (Z.pow b c)) with v end.

(* [comment removed for export] *)
Ltac in_lit := cbn [In]; repeat (first [ left; reflexivity | right ]).
(* [comment removed for export] *)
Fixpoint AllT {A : Type} (P : A -> Prop) (l : list A) (G : Prop) : Prop :=
  match l with [] => G | x :: l' => P x -> AllT P l' G end.
Lemma allT_gen : forall (A : Type) (P : A -> Prop) (l : list A) (G : Prop), ((forall q, In q l -> P q) -> G) -> AllT P l G.
Proof.
  intros A P l. induction l as [|x l IH]; intros G H; cbn [AllT].
  - apply H. intros q [].
  - intros px. apply IH. intros Hl. apply H. intros q [<-|Hq]; [exact px| exact (Hl q Hq)].
Qed.
Lemma allT_intro : forall (A : Type) (P : A -> Prop) (l : list A), AllT P l (forall q, In q l -> P q).
Proof. intros A P l. apply allT_gen. exact (fun H => H). Qed.
Lemma allT_forall : forall (A : Type) (P : A -> Prop) (l : list A), AllT P l (Forall P l).
Proof. intros A P l. apply allT_gen. intros H. apply Forall_forall. exact H. Qed.
Lemma allT_eq : forall (A : Type) (l : list A) (x : A) (G : Prop), AllT (fun x' => x = x' -> G) l (In x l -> G).
Proof. intros A l x G. apply allT_gen. intros H Hin. exact (H x Hin eq_refl). Qed.
Fixpoint AllT2 {A B : Type} (P : A -> B -> Prop) (l : list (A * B)) (G : Prop) : Prop :=
  match l with [] => G | (a, b) :: l' => P a b -> AllT2 P l' G end.
Lemma allT2_gen : forall (A B : Type) (P : A -> B -> Prop) (l : list (A * B)) (G : Prop),
  ((forall a b, In (a, b) l -> P a b) -> G) -> AllT2 P l G.
Proof.
  intros A B P l. induction l as [|[a b] l IH]; intros G H; cbn [AllT2].
  - apply H. intros a b [].
  - intros px. apply IH. intros Hl. apply H. intros a' b' [EQ|Hq]; [injection EQ as <- <-; exact px| exact (Hl a' b' Hq)].
Qed.
Lemma allT2_eq : forall (A B : Type) (l : list (A * B)) (a : A) (b : B) (G : Prop),
  AllT2 (fun a' b' => a = a' -> b = b' -> G) l (In (a, b) l -> G).
Proof. intros A B l a b G. apply allT2_gen. intros H Hin. exact (H a b Hin eq_refl eq_refl). Qed.
Fixpoint AllPairsT {A : Type} (D : A -> A -> Prop) (l : list A) (G : Prop) : Prop :=
  match l with [] => G | x :: l' => AllT (D x) l' (AllPairsT D l' G) end.
Fixpoint EqT {A : Type} (l1 l2 : list A) (G : Prop) : Prop :=
  match l1, l2 with
  | x :: l1', y :: l2' => x = y -> EqT l1' l2' G
  | _, _ => G
  end.
Lemma eqT_gen : forall (A : Type) (l1 l2 : list A) (G : Prop), length l1 = length l2 -> (l1 = l2 -> G) -> EqT l1 l2 G.
Proof.
  intros A l1. induction l1 as [|x l1 IH]; intros [|y l2] G HL H; cbn [EqT]; try discriminate HL.
  - exact (H eq_refl).
  - intros ->. apply IH; [injection HL as HL; exact HL|]. intros ->. exact (H eq_refl).
Qed.
Lemma eqT_intro : forall (A : Type) (l1 l2 : list A), length l1 = length l2 -> EqT l1 l2 (l1 = l2).
Proof. intros A l1 l2 HL. apply eqT_gen; [exact HL| exact (fun H => H)]. Qed.
(* [comment removed for export] *)
Ltac a0_natz_hook := idtac.
Ltac refine_n t n := lazymatch n with O => refine t | S ?m => refine_n uconstr:(t _) m end.
(* [comment removed for export] *)
Ltac all_in_lit :=
  a0_natz_hook;
  lazymatch goal with |- forall q, In q ?L -> @?P q =>
    let n := eval lazy in (length L) in refine_n uconstr:(allT_intro _ P L) n; cbv beta
  end.
(* [comment removed for export] *)
Ltac forall_lit :=
  a0_natz_hook;
  lazymatch goal with |- Forall ?P ?L =>
    let n := eval lazy in (length L) in refine_n uconstr:(allT_forall _ P L) n; cbv beta
  end.
(* [comment removed for export] *)
Ltac in_cases1 H :=
  lazymatch type of H with
  | In ?x ?L => lazymatch goal with |- ?G =>
      let n := eval lazy in (length L) in revert H; refine_n uconstr:(allT_eq _ L x G) n; intros -> end
  end.
(* [comment removed for export] *)
Ltac in_cases2 H :=
  lazymatch type of H with
  | In (?b, ?n) ?L => lazymatch goal with |- ?G =>
      let k := eval lazy in (length L) in revert H; refine_n uconstr:(allT2_eq _ _ L b n G) k; intros -> -> end
  end.
Ltac in_nth_try L k n :=
  lazymatch n with
  | O => fail "in_nth: no position"
  | S ?m => first [ exact (nth_error_In L k eq_refl) | in_nth_try L (S k) m ]
  end.
Ltac in_nth := lazymatch goal with |- In ?x ?L => let n := eval lazy in (length L) in in_nth_try L O n end.
(* [comment removed for export] *)
Ltac list_eq_lit :=
  lazymatch goal with |- ?l1 = ?l2 =>
    let n := eval lazy in (length l2) in refine_n uconstr:(eqT_intro _ l1 l2 eq_refl) n
  end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pages_of (iv : Z * Z) : list (Z * Z) :=
  map (fun i => (fst iv + 4096 * Z.of_nat i, fst iv + 4096 * Z.of_nat i + 4096)) (seq 0 (Z.to_nat ((snd iv - fst iv) / 4096))).
Definition covb (l : list (word * word)) (iv : Z * Z) : bool :=
  existsb (fun e => (bv_unsigned (fst e) <=? fst iv) && (snd iv <=? bv_unsigned (fst e) + bv_unsigned (snd e)))%bool l.
Lemma covb_true : forall l iv, covb l iv = true <-> exists e, In e l /\ bv_unsigned (fst e) <= fst iv /\ snd iv <= bv_unsigned (fst e) + bv_unsigned (snd e).
Proof.
  intros l iv. unfold covb. rewrite existsb_exists. split.
  - intros [e [He Hb]]. apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. exists e. tauto.
  - intros [e (He & H1 & H2)]. exists e. split; [exact He|]. apply andb_true_iff. split; apply Z.leb_le; assumption.
Qed.
Lemma in_pages_of : forall lo hi q q', In (q, q') (pages_of (lo, hi)) <->
  exists i : nat, (Z.of_nat i < (hi - lo) / 4096) /\ q = lo + 4096 * Z.of_nat i /\ q' = q + 4096.
Proof.
  intros lo hi q q'. unfold pages_of. cbn [fst snd]. rewrite in_map_iff. split.
  - intros [i [Ei Hi]]. apply in_seq in Hi. injection Ei as <- <-. exists i. split; [lia| split; [reflexivity| lia]].
  - intros [i (Hi & -> & ->)]. exists i. split; [f_equal; lia|]. apply in_seq. lia.
Qed.
Lemma hull_bytes_app : forall l1 l2, Hull.hull_bytes (l1 ++ l2) = Hull.hull_bytes l1 + Hull.hull_bytes l2.
Proof. induction l1 as [|iv l1 IH]; intros l2; [reflexivity|]. cbn [Hull.hull_bytes app]. rewrite IH. lia. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hull_bytes1 : forall lo hi, 0 <= lo -> lo <= hi -> page_size * Z.of_nat (Hull.hull_npages (lo, hi)) <= hi - lo + 8192.
Proof.
  intros lo hi H0 H1. unfold Hull.hull_npages, page_size. cbn [fst snd].
  set (x := (hi - 1) / 4096 - lo / 4096 + 1). assert (X0 : 4096 * x <= hi - lo + 8192) by (subst x; Z.div_mod_to_equations; lia).
  destruct (Z_lt_le_dec x 0); [rewrite Z2Nat.nonpos by lia; lia| rewrite Z2Nat.id by lia; lia].
Qed.
Lemma hull_bytes_le_sum : forall l (B : Z), 0 <= B ->
  Forall (fun iv => 0 <= fst iv /\ fst iv <= snd iv <= fst iv + B) l -> Hull.hull_bytes l <= Z.of_nat (length l) * (B + 8192).
Proof.
  intros l B HB HF. induction HF as [|[lo hi] l [H1 H2] HF IH]; [cbn; lia|].
  cbn [Hull.hull_bytes length fst snd] in *. pose proof (hull_bytes1 lo hi H1 ltac:(lia)). rewrite Nat2Z.inj_succ. nia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hull_bytes_nonneg : forall l, 0 <= Hull.hull_bytes l.
Proof. induction l as [|iv l IH]; cbn [Hull.hull_bytes]; [lia|]. pose proof Hull.page_size_pos. nia. Qed.
Lemma hull_bytes_filter_le : forall f l, Hull.hull_bytes (List.filter f l) <= Hull.hull_bytes l.
Proof.
  intros f l. induction l as [|iv l IH]; cbn [List.filter Hull.hull_bytes]; [lia|].
  pose proof Hull.page_size_pos. destruct (f iv); cbn [Hull.hull_bytes]; nia.
Qed.
(* [comment removed for export] *)
Lemma hull_bytes_den_le : forall (l : list (Z * Z)),
  Forall (fun d => 0 <= fst d /\ 0 <= snd d) l ->
  Hull.hull_bytes (map (fun d => (fst d, fst d + snd d)) l) <= fold_right (fun d a => snd d + 8192 + a) 0 l.
Proof.
  intros l HF. induction HF as [|[b n] l [H1 H2] HF IH]; [cbn; lia|].
  cbn [map Hull.hull_bytes fold_right fst snd] in *. pose proof (hull_bytes1 b (b + n) H1 ltac:(lia)). lia.
Qed.
Lemma page_hullb_in : forall (H : Hull.hull) lo hi q, In (lo, hi) H -> lo <= q -> q + 4096 <= hi -> Hull.page_hullb H q = true.
Proof.
  intros H lo hi q Hin H1 H2. unfold Hull.page_hullb. apply existsb_exists. exists (lo, hi). split; [exact Hin|].
  unfold Hull.page_meets_ivb, page_size. cbn [fst snd]. apply andb_true_iff. split; [apply Z.ltb_lt| apply Z.ltb_lt]; lia.
Qed.


(* [comment removed for export] *)
Section PRE.
  Context {Clg : Ceiling.Ceiling}.
  Record a0_pre (P : aplace) (k1 : list Z) (sp0 : Z) (FULL : mem) (md : Model) : Prop := A0PRE {
    q_place  : AInv.wf_place AL_pboth P;
    q_consts : AInv.consts_repr_ LayoutPA.LPA AL_pboth P FULL;
    q_locks  : AInv.locks_repr_ LayoutPA.LPA AL_pboth P [] FULL;
    q_ri_zero : zero_at FULL (p_ri P) 4096;
    q_thr_zero : zero_at FULL (p_thr P + 80) (2800 - 80);
    q_thr_map  : mapped FULL (p_thr P) 4096 /\ mapped FULL (p_ctx P) 0x10000;
    q_qglobal_zero : ACells.fill_at BSEGS FULL (al_instance AL_pboth + off_q_cache_list_size) 32 0;
    q_sec_zero : ACells.u64_at BSEGS FULL (al_instance AL_pboth + off_sec_n_reserved) 0 /\
                 ACells.u64_at BSEGS FULL (al_instance AL_pboth + off_sec_n_chunks) 0;
    q_ia     : ACells.u8_at BSEGS FULL (al_internal_alloc_inited AL_pboth) 0 /\ ACells.fill_at BSEGS FULL (al_internal_allocator_inst AL_pboth) 0x81030 0;
    q_depot  : a0_depot_raw P k1 FULL;
    q_k1     : In k1 (p_dkeys P);
    q_fs_hints : zero_at FULL (p_fs P) 88;
    q_fs_log   : ACells.u64_at BSEGS FULL (p_fs P + 88) kFakeStackSizeLog /\ ACells.u8_at BSEGS FULL (p_fs P + 96) 0;
    q_fs_flags : zero_at FULL (p_fs P + kFakeFlagsOffset) (kFakeFramesOffset - kFakeFlagsOffset);
    q_fs_map   : mapped FULL (p_fs P) kFakeStackBytes /\ mapped FULL (sh (p_fs P)) (kFakeStackBytes / 8);
    q_maps   : mapped FULL (sp0 - 0x800000) 0x800000;
    q_stkshadow_map : mapped FULL (fst stack_shadow_iv) (snd stack_shadow_iv);
    q_imgshadow_map : mapped FULL 0x7fffa000 0xbf400;
    q_hidden : forall z, in_shadow_maps z -> ~ in_vis_shadow (VIS0 P) z -> FULL (Z_to_bv 64 z) = Some (Z_to_bv 8 0);
    (* [comment removed for export] *)
    q_x1 : Forall (fun lh => 0 <= fst lh /\ fst lh <= snd lh <= 2^47) (p_extra P);
    q_x2 : forall lo hi a, In (lo, hi) (p_extra P) -> lo <= a < hi ->
             (0 <= a <= kLowMemEnd \/ kHighMemBeg <= a < Ceiling.alloc_ceiling) ->
             forall z, sh a - sh a mod 8 <= z < sh a - sh a mod 8 + 8 -> exists lo' hi', In (lo', hi') (p_extra P) /\ lo' <= z < hi';
    q_x3 : forall lo hi, In (lo, hi) (p_extra P) -> lo mod 4096 = 0 /\ hi mod 4096 = 0;
    q_x4 : cl_image_hi LayoutPA.LPA <= p_brk P <= cl_image_hi LayoutPA.LPA + 2^31;
    q_x5 : forall pc ra, In pc LayoutPA.pa_site_pcs -> In ra (cl_sites LayoutPA.LPA) -> In [pc; ra] (p_dkeys P) /\ In [pc] (p_dkeys P);
    q_x6 : Hull.hull_bytes (p_extra P) <= 2^28 + 2^26;   (* [comment removed for export] *)
    (* [comment removed for export] *)
    q_x7 : forall lo hi a, In (lo, hi) (p_extra P) -> lo <= a < hi -> ~ (p_sb P <= a < p_sb P + kSpaceSize);
    (* [comment removed for export] *)
    q_x8 : AInv.TLIM_MIN <= p_tlim P;
    q_ledger : AInv.aledger_ AL_pboth P (fun _ => region_zero) (SR [] 0) md;   (* [comment removed for export] *)
    q_bigmaps : AInv.wf_bigmaps_ P (SR [] 0);
    q_minv   : Hull.MInv (a0_hull P k1) (a0_lhull P k1) (a0_eager P k1) md;   (* [comment removed for export] *)
    q_halted : m_halted md = None;
    q_reserved : vm_reserved (m_vmmaps md) = segments_reserved BSEGS;
    q_gap : In (Z_to_bv 64 kShadowGapBeg, Z_to_bv 64 (kHighShadowMapBeg - kShadowGapBeg)) (vm_maps (m_vmmaps md));
    q_vmmaps : exists fog : list (Z * Z),
      Z.of_nat (length fog) <= 2 /\ Forall (fun bs => 0 <= fst bs /\ 0 < snd bs <= 8192 /\ fst bs + snd bs <= 2^47) fog /\
      (forall e, In e (vm_maps (m_vmmaps md)) ->
          let bs := (bv_unsigned (fst e), bv_unsigned (snd e)) in
          In bs (AInv.big_maps_ P (SR [] 0)) \/ In bs fog \/ bs = (kShadowGapBeg, kHighShadowMapBeg - kShadowGapBeg)) /\
      (forall bs, In bs fog -> In (Z_to_bv 64 (fst bs), Z_to_bv 64 (snd bs)) (vm_maps (m_vmmaps md))) /\
      (forall lo hi a, In (lo, hi) (p_extra P) -> lo <= a < hi -> 0 <= a < Ceiling.alloc_ceiling ->
          ~ (kLowShadowMapBeg <= a < kHighMemBeg) ->
          (cl_image_lo LayoutPA.LPA <= a < cl_image_hi LayoutPA.LPA) \/ in_regions (AInv.big_maps_ P (SR [] 0)) a \/ in_regions fog a)
  }.
End PRE.

Section A0.
  Context {Clg : Ceiling.Ceiling}.   (* [comment removed for export] *)
  Variable sp : word.
  Hypothesis HCEIL : Ceiling.alloc_ceiling = bv_unsigned sp - 0x800000.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Context {BL : AsanInit.BootLim}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HLIM : AInv.TLIM_MIN <= (@AsanInit.blim BL).
  #[local] Notation SINV := (SINV0 BPH sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 BPH sp rdraw argv envp uid hw).
  #[local] Notation LIM := (@AsanInit.blim BL).
  Variable cs : acs.
  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis CS : cs_ok BSEGS BOTH LIM SINV argH fs E cs R FULL model.
  Hypothesis AK : a0k cs.
  Variable gh : list (expr * expr).
  Hypothesis ASS : a0s cs gh.
  (* [comment removed for export] *)
  Hypothesis GH : (gh = A0_GHOST_A /\ khas cs (KRange (EVar 5) 1546 524277) = true
                   /\ khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (pg 5) 0) (ELit 8192)) = true)
                  \/ gh = A0_GHOST_B.
  Hypothesis EAG : 0 <= a_eager cs <= 2^25.   (* [comment removed for export] *)
  Hypothesis CC : cells_okb cs A0_CELLS = true.
  Variable k1 : list Z.
  Hypothesis KD : a0kd cs k1.
  Hypothesis HK1 : In k1 LayoutPA.pa_dkeys.
  Hypothesis CCL : cells_okb cs (cl_consts LayoutPA.LPA) = true.
  #[local] Notation KH := (khas cs).
  #[local] Notation U v := (bv_unsigned (ev E v)).
  #[local] Notation usp := (bv_unsigned sp).

  (* [comment removed for export] *)
  Definition pgv (v : nat) : Z := 4096 * U v.
  Ltac a0_natz_hook ::= try change (pgv 4115%nat) with (pgv (Z.to_nat 4115)); try change (pgv 498%nat) with (pgv (Z.to_nat 498)); try change (pgv 481%nat) with (pgv (Z.to_nat 481)); try change (pgv 480%nat) with (pgv (Z.to_nat 480)); try change (pgv 405%nat) with (pgv (Z.to_nat 405)); try change (pgv 322%nat) with (pgv (Z.to_nat 322)); try change (pgv 257%nat) with (pgv (Z.to_nat 257)); try change (pgv 228%nat) with (pgv (Z.to_nat 228)); try change (pgv 227%nat) with (pgv (Z.to_nat 227)); try change (pgv 226%nat) with (pgv (Z.to_nat 226)); try change (pgv 208%nat) with (pgv (Z.to_nat 208)); try change (pgv 207%nat) with (pgv (Z.to_nat 207)).
  Ltac a0_natz_ap := try change (pgv 4115%nat) with (pgv (Z.to_nat 4115)) in *; try change (U 4115%nat) with (U (Z.to_nat 4115)) in *; try change (pgv 498%nat) with (pgv (Z.to_nat 498)) in *; try change (U 498%nat) with (U (Z.to_nat 498)) in *; try change (pgv 481%nat) with (pgv (Z.to_nat 481)) in *; try change (U 481%nat) with (U (Z.to_nat 481)) in *; try change (pgv 480%nat) with (pgv (Z.to_nat 480)) in *; try change (U 480%nat) with (U (Z.to_nat 480)) in *; try change (pgv 405%nat) with (pgv (Z.to_nat 405)) in *; try change (U 405%nat) with (U (Z.to_nat 405)) in *; try change (pgv 322%nat) with (pgv (Z.to_nat 322)) in *; try change (U 322%nat) with (U (Z.to_nat 322)) in *; try change (pgv 257%nat) with (pgv (Z.to_nat 257)) in *; try change (U 257%nat) with (U (Z.to_nat 257)) in *; try change (pgv 228%nat) with (pgv (Z.to_nat 228)) in *; try change (U 228%nat) with (U (Z.to_nat 228)) in *; try change (pgv 227%nat) with (pgv (Z.to_nat 227)) in *; try change (U 227%nat) with (U (Z.to_nat 227)) in *; try change (pgv 226%nat) with (pgv (Z.to_nat 226)) in *; try change (U 226%nat) with (U (Z.to_nat 226)) in *; try change (pgv 208%nat) with (pgv (Z.to_nat 208)) in *; try change (U 208%nat) with (U (Z.to_nat 208)) in *; try change (pgv 207%nat) with (pgv (Z.to_nat 207)) in *; try change (U 207%nat) with (U (Z.to_nat 207)) in *.
  (* [comment removed for export] *)
  Ltac a0_natz_one n := lazymatch n with Z.to_nat _ => fail | _ => idtac end; let z := eval cbv in (Z.of_nat n) in lazymatch z with Zpos _ => idtac end;
    let b := eval cbv in (Z.leb 200 z) in lazymatch b with true => idtac end; try change (pgv n) with (pgv (Z.to_nat z)) in *; try change (U n) with (U (Z.to_nat z)) in *.
  Ltac a0_natz_all := repeat match goal with
    | |- context [pgv ?n] => a0_natz_one n | |- context [ev E ?n] => a0_natz_one n
    | H : context [pgv ?n] |- _ => a0_natz_one n | H : context [ev E ?n] |- _ => a0_natz_one n end.
  Definition stk_top : Z := 32768 * U 0%nat + 4096 * U 356%nat.
  Definition PGSP : Z := 32768 * U 0%nat + 4096 * U 10%nat.                 (* [comment removed for export] *)
  Definition riZ : Z := pgv 208 - 4096 * U 209%nat + 137439019008.           (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition appr (p : expr * expr) : Z * Z := (uE E (fst p), uE E (fst p) + uE E (snd p)).
  Definition shr (p : expr * expr) : Z * Z := (pagedown (sh_lo BOTH E p), pageup (sh_hi BOTH E p)).
  Definition VMM : list (word * word) := vm_maps (m_vmmaps model).
  Definition EXTRA : list (Z * Z) :=
    List.filter (covb VMM) (map appr (a_vis cs)) ++ List.filter (covb VMM) (flat_map (fun p => pages_of (appr p)) (a_ghost cs))
    ++ map shr (a_vis cs ++ a_ghost cs).
  Definition P : aplace :=
    {| p_b6 := pgv 208; p_pa := pgv 226; p_thr := pgv 227; p_ctx := pgv 228; p_nodes0 := pgv 480; p_frames0 := pgv 481;
       p_fs := pgv 405; p_itab := pgv 207; p_m64k := pgv 78; p_gvec := pgv 4115; p_dvec := pgv 498; p_m11 := pgv 257; p_dtls := pgv 322;
       p_tlsb := 0x5e8310; p_tlse := 0x5e83ec;   (* [comment removed for export] *)
       p_sp0 := usp; p_stk_span := entry_stack_span argv envp; p_stk_top := stk_top; p_stk_bot := stk_top - 8388608;
       p_eager0 := a_eager cs; p_brk := pgv 5;
       p_dkeys := LayoutPA.pa_dkeys;
       p_extra := EXTRA;
       p_tlim := LIM |}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ulit : forall z, 0 <= z < 2^64 -> bv_unsigned (edenot E (ELit z)) = z.
  Proof. intros z Hz. rewrite edenot_lit, u_lit64a. apply Z.mod_small. exact Hz. Qed.
  Lemma R0 : 4294901760 <= U 0%nat <= 4294967295. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_0 cs AK)). Qed.
  Lemma R6 : 0 <= U 6%nat <= 2047. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_6 cs AK)). Qed.
  Lemma R78 : 1546 <= U 78%nat <= 34359736304. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_78 cs AK)). Qed.
  Lemma R207 : 1546 <= U 207%nat <= 34359735410. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_207 cs AK)). Qed.
  Lemma R208 : 4295491576 <= U 208%nat <= 34326181871. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_208 cs AK)). Qed.
  Lemma R209 : 0 <= U 209%nat <= 15. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_209 cs AK)). Qed.
  Lemma R226 : 1546 <= U 226%nat <= 34359734272. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_226 cs AK)). Qed.
  Lemma R227 : 1 <= U 227%nat <= 34359736319. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_227 cs AK)). Qed.
  Lemma R228 : 1546 <= U 228%nat <= 34359736304. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_228 cs AK)). Qed.
  Lemma R257 : 1 <= U 257%nat <= 34359736319. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_257 cs AK)). Qed.
  Lemma R322 : 1 <= U 322%nat <= 34359736319. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_322 cs AK)). Qed.
  Lemma R323 : 1 <= U 323%nat <= 34359736319. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_323 cs AK)). Qed.
  Lemma R356 : 0 <= U 356%nat <= 8. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_356 cs AK)). Qed.
  Lemma R405 : 1546 <= U 405%nat <= 34359733495. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_405 cs AK)). Qed.
  Lemma R422 : 1 <= U 422%nat <= 34359736319. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_422 cs AK)). Qed.
  Lemma R423 : 1 <= U 423%nat <= 34359736319. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_423 cs AK)). Qed.
  Lemma R480 : 1546 <= U 480%nat <= 34359736064. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_480 cs AK)). Qed.
  Lemma R481 : 1546 <= U 481%nat <= 34359734272. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_481 cs AK)). Qed.
  Lemma R498 : 1 <= U 498%nat <= 34359736319. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_498 cs AK)). Qed.
  Lemma R4115 : 1 <= U 4115%nat <= 34359736319. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_4115 cs AK)). Qed.
  Lemma R5 : 1546 <= U 5%nat <= 525834. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_5 cs AK)). Qed.
  Lemma Upg : forall v lo hi, KH (KRange (EVar v) lo hi) = true -> 0 <= lo -> 4096 * hi < 2^64 -> bv_unsigned (edenot E (pg v)) = pgv v.
  Proof. intros v lo hi H Hlo Hhi. unfold pg, pgv. exact (ub_scale sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS 4096 v lo hi H ltac:(lia) Hlo Hhi). Qed.
  Lemma U78 : bv_unsigned (edenot E (pg 78)) = pgv 78. Proof. exact (Upg 78%nat _ _ (k_rng_78 cs AK) ltac:(lia) ltac:(lia)). Qed.
  Lemma U207 : bv_unsigned (edenot E (pg 207)) = pgv 207. Proof. exact (Upg 207%nat _ _ (k_rng_207 cs AK) ltac:(lia) ltac:(lia)). Qed.
  Lemma U208 : bv_unsigned (edenot E (pg 208)) = pgv 208. Proof. exact (Upg 208%nat _ _ (k_rng_208 cs AK) ltac:(lia) ltac:(lia)). Qed.
  Lemma U226 : bv_unsigned (edenot E (pg 226)) = pgv 226. Proof. exact (Upg 226%nat _ _ (k_rng_226 cs AK) ltac:(lia) ltac:(lia)). Qed.
  Lemma U227 : bv_unsigned (edenot E (pg 227)) = pgv 227. Proof. exact (Upg 227%nat _ _ (k_rng_227 cs AK) ltac:(lia) ltac:(lia)). Qed.
  Lemma U228 : bv_unsigned (edenot E (pg 228)) = pgv 228. Proof. exact (Upg 228%nat _ _ (k_rng_228 cs AK) ltac:(lia) ltac:(lia)). Qed.
  Lemma U257 : bv_unsigned (edenot E (pg 257)) = pgv 257. Proof. exact (Upg 257%nat _ _ (k_rng_257 cs AK) ltac:(lia) ltac:(lia)). Qed.
  Lemma U322 : bv_unsigned (edenot E (pg 322)) = pgv 322. Proof. exact (Upg 322%nat _ _ (k_rng_322 cs AK) ltac:(lia) ltac:(lia)). Qed.
  Lemma U323 : bv_unsigned (edenot E (pg 323)) = pgv 323. Proof. exact (Upg 323%nat _ _ (k_rng_323 cs AK) ltac:(lia) ltac:(lia)). Qed.
  Lemma U405 : bv_unsigned (edenot E (pg 405)) = pgv 405. Proof. exact (Upg 405%nat _ _ (k_rng_405 cs AK) ltac:(lia) ltac:(lia)). Qed.
  Lemma U422 : bv_unsigned (edenot E (pg 422)) = pgv 422. Proof. exact (Upg 422%nat _ _ (k_rng_422 cs AK) ltac:(lia) ltac:(lia)). Qed.
  Lemma U423 : bv_unsigned (edenot E (pg 423)) = pgv 423. Proof. exact (Upg 423%nat _ _ (k_rng_423 cs AK) ltac:(lia) ltac:(lia)). Qed.
  Lemma U480 : bv_unsigned (edenot E (pg 480)) = pgv 480. Proof. exact (Upg 480%nat _ _ (k_rng_480 cs AK) ltac:(lia) ltac:(lia)). Qed.
  Lemma U481 : bv_unsigned (edenot E (pg 481)) = pgv 481. Proof. exact (Upg 481%nat _ _ (k_rng_481 cs AK) ltac:(lia) ltac:(lia)). Qed.
  Lemma U498 : bv_unsigned (edenot E (pg 498)) = pgv 498. Proof. exact (Upg 498%nat _ _ (k_rng_498 cs AK) ltac:(lia) ltac:(lia)). Qed.
  Lemma U4115 : bv_unsigned (edenot E (pg 4115)) = pgv 4115. Proof. exact (Upg 4115%nat _ _ (k_rng_4115 cs AK) ltac:(lia) ltac:(lia)). Qed.
  Lemma U5 : bv_unsigned (edenot E (pg 5)) = pgv 5. Proof. exact (Upg 5%nat _ _ (k_rng_5 cs AK) ltac:(lia) ltac:(lia)). Qed.
  Lemma uE_pg : forall v, uE E (pg v) = bv_unsigned (edenot E (pg v)). Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma in_maps_den : forall am, In am A0_MAPS -> is_fog am = false -> In (edenot E (am_base am), edenot E (am_len am)) VMM.
  Proof.
    intros am Hin Hf. pose proof (pre_in_maps sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS am) as X. rewrite (s_maps cs gh ASS) in X. exact (X Hin Hf).
  Qed.
  Lemma in_maps_bounds : forall m, In m A0_MAPS -> is_fog m = false ->
    0 < bv_unsigned (edenot E (am_len m))
    /\ bv_unsigned (edenot E (am_base m)) mod 4096 = 0 /\ bv_unsigned (edenot E (am_len m)) mod 4096 = 0
    /\ (bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= img_lo BOTH \/ img_hi BOTH <= bv_unsigned (edenot E (am_base m)))
    /\ bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) <= alloc_top (m_vmmaps model).
  Proof.
    intros m Hin Hf. exact (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ CS) _ (in_maps_den m Hin Hf)).
  Qed.
  Lemma alloc_top_val : alloc_top (m_vmmaps model) = usp - 8388608.
  Proof. pose proof (pre_top sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit cs E R FULL model CS). lia. Qed.
  Lemma AP_gen : forall v sz k, In (AM (pg v) (ELit sz) k) A0_MAPS -> is_fog (AM (pg v) (ELit sz) k) = false ->
    bv_unsigned (edenot E (pg v)) = pgv v -> 0 <= sz < 2^64 ->
    0 < sz /\ (pgv v + sz <= img_lo ASAN \/ img_hi ASAN <= pgv v) /\ pgv v + sz <= usp - 8388608.
  Proof.
    intros v sz k Hin Hf HU Hsz. pose proof (in_maps_bounds (AM (pg v) (ELit sz) k) Hin Hf) as X.
    cbn [am_base am_len] in X. rewrite HU, (ulit sz) in X by exact Hsz. rewrite alloc_top_val in X. tauto.
  Qed.
  Lemma AP4115 : 0 < 4096 /\ (pgv 4115 + 4096 <= img_lo BOTH \/ img_hi BOTH <= pgv 4115) /\ pgv 4115 + 4096 <= usp - 8388608.
  Proof. exact (AP_gen 4115%nat 4096 KRW ltac:(in_nth) eq_refl U4115 ltac:(lia)). Qed.
  Lemma AP498 : 0 < 4096 /\ (pgv 498 + 4096 <= img_lo BOTH \/ img_hi BOTH <= pgv 498) /\ pgv 498 + 4096 <= usp - 8388608.
  Proof. exact (AP_gen 498%nat 4096 KRW ltac:(in_nth) eq_refl U498 ltac:(lia)). Qed.
  Lemma AP481 : 0 < 8388608 /\ (pgv 481 + 8388608 <= img_lo BOTH \/ img_hi BOTH <= pgv 481) /\ pgv 481 + 8388608 <= usp - 8388608.
  Proof. exact (AP_gen 481%nat 8388608 KRWLAZY ltac:(in_nth) eq_refl U481 ltac:(lia)). Qed.
  Lemma AP480 : 0 < 1048576 /\ (pgv 480 + 1048576 <= img_lo BOTH \/ img_hi BOTH <= pgv 480) /\ pgv 480 + 1048576 <= usp - 8388608.
  Proof. exact (AP_gen 480%nat 1048576 KRW ltac:(in_nth) eq_refl U480 ltac:(lia)). Qed.
  Lemma AP405 : 0 < 11571200 /\ (pgv 405 + 11571200 <= img_lo BOTH \/ img_hi BOTH <= pgv 405) /\ pgv 405 + 11571200 <= usp - 8388608.
  Proof. exact (AP_gen 405%nat 11571200 KRW ltac:(in_nth) eq_refl U405 ltac:(lia)). Qed.
  Lemma AP322 : 0 < 4096 /\ (pgv 322 + 4096 <= img_lo BOTH \/ img_hi BOTH <= pgv 322) /\ pgv 322 + 4096 <= usp - 8388608.
  Proof. exact (AP_gen 322%nat 4096 KRW ltac:(in_nth) eq_refl U322 ltac:(lia)). Qed.
  Lemma AP257 : 0 < 4096 /\ (pgv 257 + 4096 <= img_lo BOTH \/ img_hi BOTH <= pgv 257) /\ pgv 257 + 4096 <= usp - 8388608.
  Proof. exact (AP_gen 257%nat 4096 KRW ltac:(in_nth) eq_refl U257 ltac:(lia)). Qed.
  Lemma AP228 : 0 < 65536 /\ (pgv 228 + 65536 <= img_lo BOTH \/ img_hi BOTH <= pgv 228) /\ pgv 228 + 65536 <= usp - 8388608.
  Proof. exact (AP_gen 228%nat 65536 KRW ltac:(in_nth) eq_refl U228 ltac:(lia)). Qed.
  Lemma AP227 : 0 < 4096 /\ (pgv 227 + 4096 <= img_lo BOTH \/ img_hi BOTH <= pgv 227) /\ pgv 227 + 4096 <= usp - 8388608.
  Proof. exact (AP_gen 227%nat 4096 KRW ltac:(in_nth) eq_refl U227 ltac:(lia)). Qed.
  Lemma AP226 : 0 < 8388608 /\ (pgv 226 + 8388608 <= img_lo BOTH \/ img_hi BOTH <= pgv 226) /\ pgv 226 + 8388608 <= usp - 8388608.
  Proof. exact (AP_gen 226%nat 8388608 KNONELAZY ltac:(in_nth) eq_refl U226 ltac:(lia)). Qed.
  Lemma AP208 : 0 < 137439023104 /\ (pgv 208 + 137439023104 <= img_lo BOTH \/ img_hi BOTH <= pgv 208) /\ pgv 208 + 137439023104 <= usp - 8388608.
  Proof. exact (AP_gen 208%nat 137439023104 KRW ltac:(in_nth) eq_refl U208 ltac:(lia)). Qed.
  Lemma AP207 : 0 < 3727360 /\ (pgv 207 + 3727360 <= img_lo BOTH \/ img_hi BOTH <= pgv 207) /\ pgv 207 + 3727360 <= usp - 8388608.
  Proof. exact (AP_gen 207%nat 3727360 KRW ltac:(in_nth) eq_refl U207 ltac:(lia)). Qed.
  Lemma AP78 : 0 < 65536 /\ (pgv 78 + 65536 <= img_lo BOTH \/ img_hi BOTH <= pgv 78) /\ pgv 78 + 65536 <= usp - 8388608.
  Proof. exact (AP_gen 78%nat 65536 KRW ltac:(in_nth) eq_refl U78 ltac:(lia)). Qed.
  (* [comment removed for export] *)
  Lemma disj_of_k : forall b1 n1 b2 n2 B1 B2, KH (KDisj (SA b1 0) (ELit n1) (SA b2 0) (ELit n2)) = true ->
    bv_unsigned (edenot E b1) = B1 -> bv_unsigned (edenot E b2) = B2 -> 0 <= n1 < 2^64 -> 0 <= n2 < 2^64 -> B1 + n1 <= B2 \/ B2 + n2 <= B1.
  Proof.
    intros b1 n1 b2 n2 B1 B2 H U1 U2 N1 N2. apply (khas_ok sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS) in H. cbn [kentry_ok] in H.
    unfold estart, elenZ in H. cbn [a_base a_off edenot] in H. rewrite U1, U2, !u_lit64a, !Z.mod_small in H by lia. lia.
  Qed.
  Lemma LH4115 : pgv 4115 + 4096 <= LOWSHZ \/ KHIZ <= pgv 4115.
  Proof. pose proof (disj_of_k _ _ _ _ _ _ (k_band_0 cs AK) (ulit 2147446784 ltac:(lia)) U4115 ltac:(lia) ltac:(lia)). unfold LOWSHZ, KHIZ. lia. Qed.
  Lemma LH498 : pgv 498 + 4096 <= LOWSHZ \/ KHIZ <= pgv 498.
  Proof. pose proof (disj_of_k _ _ _ _ _ _ (k_band_2 cs AK) (ulit 2147446784 ltac:(lia)) U498 ltac:(lia) ltac:(lia)). unfold LOWSHZ, KHIZ. lia. Qed.
  Lemma LH481 : pgv 481 + 8388608 <= LOWSHZ \/ KHIZ <= pgv 481.
  Proof. pose proof (disj_of_k _ _ _ _ _ _ (k_band_4 cs AK) (ulit 2147446784 ltac:(lia)) U481 ltac:(lia) ltac:(lia)). unfold LOWSHZ, KHIZ. lia. Qed.
  Lemma LH480 : pgv 480 + 1048576 <= LOWSHZ \/ KHIZ <= pgv 480.
  Proof. pose proof (disj_of_k _ _ _ _ _ _ (k_band_6 cs AK) (ulit 2147446784 ltac:(lia)) U480 ltac:(lia) ltac:(lia)). unfold LOWSHZ, KHIZ. lia. Qed.
  Lemma LH405 : pgv 405 + 11571200 <= LOWSHZ \/ KHIZ <= pgv 405.
  Proof. pose proof (disj_of_k _ _ _ _ _ _ (k_band_12 cs AK) (ulit 2147446784 ltac:(lia)) U405 ltac:(lia) ltac:(lia)). unfold LOWSHZ, KHIZ. lia. Qed.
  Lemma LH322 : pgv 322 + 4096 <= LOWSHZ \/ KHIZ <= pgv 322.
  Proof. pose proof (disj_of_k _ _ _ _ _ _ (k_band_16 cs AK) (ulit 2147446784 ltac:(lia)) U322 ltac:(lia) ltac:(lia)). unfold LOWSHZ, KHIZ. lia. Qed.
  Lemma LH257 : pgv 257 + 4096 <= LOWSHZ \/ KHIZ <= pgv 257.
  Proof. pose proof (disj_of_k _ _ _ _ _ _ (k_band_18 cs AK) (ulit 2147446784 ltac:(lia)) U257 ltac:(lia) ltac:(lia)). unfold LOWSHZ, KHIZ. lia. Qed.
  Lemma LH228 : pgv 228 + 65536 <= LOWSHZ \/ KHIZ <= pgv 228.
  Proof. pose proof (disj_of_k _ _ _ _ _ _ (k_band_20 cs AK) (ulit 2147446784 ltac:(lia)) U228 ltac:(lia) ltac:(lia)). unfold LOWSHZ, KHIZ. lia. Qed.
  Lemma LH227 : pgv 227 + 4096 <= LOWSHZ \/ KHIZ <= pgv 227.
  Proof. pose proof (disj_of_k _ _ _ _ _ _ (k_band_22 cs AK) (ulit 2147446784 ltac:(lia)) U227 ltac:(lia) ltac:(lia)). unfold LOWSHZ, KHIZ. lia. Qed.
  Lemma LH226 : pgv 226 + 8388608 <= LOWSHZ \/ KHIZ <= pgv 226.
  Proof. pose proof (disj_of_k _ _ _ _ _ _ (k_band_24 cs AK) (ulit 2147446784 ltac:(lia)) U226 ltac:(lia) ltac:(lia)). unfold LOWSHZ, KHIZ. lia. Qed.
  Lemma LH208 : pgv 208 + 137439023104 <= LOWSHZ \/ KHIZ <= pgv 208.
  Proof. pose proof (disj_of_k _ _ _ _ _ _ (k_band_26 cs AK) (ulit 2147446784 ltac:(lia)) U208 ltac:(lia) ltac:(lia)). unfold LOWSHZ, KHIZ. lia. Qed.
  Lemma LH207 : pgv 207 + 3727360 <= LOWSHZ \/ KHIZ <= pgv 207.
  Proof. pose proof (disj_of_k _ _ _ _ _ _ (k_band_28 cs AK) (ulit 2147446784 ltac:(lia)) U207 ltac:(lia) ltac:(lia)). unfold LOWSHZ, KHIZ. lia. Qed.
  Lemma LH78 : pgv 78 + 65536 <= LOWSHZ \/ KHIZ <= pgv 78.
  Proof. pose proof (disj_of_k _ _ _ _ _ _ (k_band_30 cs AK) (ulit 2147446784 ltac:(lia)) U78 ltac:(lia) ltac:(lia)). unfold LOWSHZ, KHIZ. lia. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma AP4115z : ltac:(let T := type of AP4115 in let T' := eval pattern 4115%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 4115)) in exact Rz end).
  Proof. exact AP4115. Qed.
  Lemma LH4115z : ltac:(let T := type of LH4115 in let T' := eval pattern 4115%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 4115)) in exact Rz end).
  Proof. exact LH4115. Qed.
  Lemma R4115z : ltac:(let T := type of R4115 in let T' := eval pattern 4115%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 4115)) in exact Rz end).
  Proof. exact R4115. Qed.
  Lemma AP498z : ltac:(let T := type of AP498 in let T' := eval pattern 498%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 498)) in exact Rz end).
  Proof. exact AP498. Qed.
  Lemma LH498z : ltac:(let T := type of LH498 in let T' := eval pattern 498%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 498)) in exact Rz end).
  Proof. exact LH498. Qed.
  Lemma R498z : ltac:(let T := type of R498 in let T' := eval pattern 498%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 498)) in exact Rz end).
  Proof. exact R498. Qed.
  Lemma AP481z : ltac:(let T := type of AP481 in let T' := eval pattern 481%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 481)) in exact Rz end).
  Proof. exact AP481. Qed.
  Lemma LH481z : ltac:(let T := type of LH481 in let T' := eval pattern 481%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 481)) in exact Rz end).
  Proof. exact LH481. Qed.
  Lemma R481z : ltac:(let T := type of R481 in let T' := eval pattern 481%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 481)) in exact Rz end).
  Proof. exact R481. Qed.
  Lemma AP480z : ltac:(let T := type of AP480 in let T' := eval pattern 480%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 480)) in exact Rz end).
  Proof. exact AP480. Qed.
  Lemma LH480z : ltac:(let T := type of LH480 in let T' := eval pattern 480%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 480)) in exact Rz end).
  Proof. exact LH480. Qed.
  Lemma R480z : ltac:(let T := type of R480 in let T' := eval pattern 480%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 480)) in exact Rz end).
  Proof. exact R480. Qed.
  Lemma AP405z : ltac:(let T := type of AP405 in let T' := eval pattern 405%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 405)) in exact Rz end).
  Proof. exact AP405. Qed.
  Lemma LH405z : ltac:(let T := type of LH405 in let T' := eval pattern 405%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 405)) in exact Rz end).
  Proof. exact LH405. Qed.
  Lemma R405z : ltac:(let T := type of R405 in let T' := eval pattern 405%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 405)) in exact Rz end).
  Proof. exact R405. Qed.
  Lemma AP322z : ltac:(let T := type of AP322 in let T' := eval pattern 322%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 322)) in exact Rz end).
  Proof. exact AP322. Qed.
  Lemma LH322z : ltac:(let T := type of LH322 in let T' := eval pattern 322%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 322)) in exact Rz end).
  Proof. exact LH322. Qed.
  Lemma R322z : ltac:(let T := type of R322 in let T' := eval pattern 322%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 322)) in exact Rz end).
  Proof. exact R322. Qed.
  Lemma AP257z : ltac:(let T := type of AP257 in let T' := eval pattern 257%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 257)) in exact Rz end).
  Proof. exact AP257. Qed.
  Lemma LH257z : ltac:(let T := type of LH257 in let T' := eval pattern 257%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 257)) in exact Rz end).
  Proof. exact LH257. Qed.
  Lemma R257z : ltac:(let T := type of R257 in let T' := eval pattern 257%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 257)) in exact Rz end).
  Proof. exact R257. Qed.
  Lemma AP228z : ltac:(let T := type of AP228 in let T' := eval pattern 228%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 228)) in exact Rz end).
  Proof. exact AP228. Qed.
  Lemma LH228z : ltac:(let T := type of LH228 in let T' := eval pattern 228%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 228)) in exact Rz end).
  Proof. exact LH228. Qed.
  Lemma R228z : ltac:(let T := type of R228 in let T' := eval pattern 228%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 228)) in exact Rz end).
  Proof. exact R228. Qed.
  Lemma AP227z : ltac:(let T := type of AP227 in let T' := eval pattern 227%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 227)) in exact Rz end).
  Proof. exact AP227. Qed.
  Lemma LH227z : ltac:(let T := type of LH227 in let T' := eval pattern 227%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 227)) in exact Rz end).
  Proof. exact LH227. Qed.
  Lemma R227z : ltac:(let T := type of R227 in let T' := eval pattern 227%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 227)) in exact Rz end).
  Proof. exact R227. Qed.
  Lemma AP226z : ltac:(let T := type of AP226 in let T' := eval pattern 226%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 226)) in exact Rz end).
  Proof. exact AP226. Qed.
  Lemma LH226z : ltac:(let T := type of LH226 in let T' := eval pattern 226%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 226)) in exact Rz end).
  Proof. exact LH226. Qed.
  Lemma R226z : ltac:(let T := type of R226 in let T' := eval pattern 226%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 226)) in exact Rz end).
  Proof. exact R226. Qed.
  Lemma AP208z : ltac:(let T := type of AP208 in let T' := eval pattern 208%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 208)) in exact Rz end).
  Proof. exact AP208. Qed.
  Lemma LH208z : ltac:(let T := type of LH208 in let T' := eval pattern 208%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 208)) in exact Rz end).
  Proof. exact LH208. Qed.
  Lemma R208z : ltac:(let T := type of R208 in let T' := eval pattern 208%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 208)) in exact Rz end).
  Proof. exact R208. Qed.
  Lemma AP207z : ltac:(let T := type of AP207 in let T' := eval pattern 207%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 207)) in exact Rz end).
  Proof. exact AP207. Qed.
  Lemma LH207z : ltac:(let T := type of LH207 in let T' := eval pattern 207%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 207)) in exact Rz end).
  Proof. exact LH207. Qed.
  Lemma R207z : ltac:(let T := type of R207 in let T' := eval pattern 207%nat in T in lazymatch T' with ?F _ => let Rz := eval cbv beta in (F (Z.to_nat 207)) in exact Rz end).
  Proof. exact R207. Qed.
  Ltac hi_tac :=
    a0_natz_hook;
    first [ solve [cbn [img_lo img_hi BOTH] in *; unfold pgv in *; lia]
          | lazymatch goal with |- context [pgv ?v0] => let v := eval cbv in v0 in
              let X := fresh in let Y := fresh in
              first [ (constr_eq v 4115%nat; pose proof AP4115z as X; pose proof R4115z as Y) | (constr_eq v 498%nat; pose proof AP498z as X; pose proof R498z as Y) | (constr_eq v 481%nat; pose proof AP481z as X; pose proof R481z as Y) | (constr_eq v 480%nat; pose proof AP480z as X; pose proof R480z as Y) | (constr_eq v 405%nat; pose proof AP405z as X; pose proof R405z as Y) | (constr_eq v 322%nat; pose proof AP322z as X; pose proof R322z as Y) | (constr_eq v 257%nat; pose proof AP257z as X; pose proof R257z as Y) | (constr_eq v 228%nat; pose proof AP228z as X; pose proof R228z as Y) | (constr_eq v 227%nat; pose proof AP227z as X; pose proof R227z as Y) | (constr_eq v 226%nat; pose proof AP226z as X; pose proof R226z as Y) | (constr_eq v 208%nat; pose proof AP208z as X; pose proof R208z as Y) | (constr_eq v 207%nat; pose proof AP207z as X; pose proof R207z as Y) | (constr_eq v 78%nat; pose proof AP78 as X; pose proof R78 as Y) ];
              try (change v with v0 in X); try (change v with v0 in Y);
              cbn [img_lo img_hi BOTH] in *; unfold pgv in *; lia end ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma neg4096_mul_mod : forall u, 0 <= u -> (18446744073709547520 * u) mod 2^64 = (- (4096 * u)) mod 2^64.
  Proof.
    intros u Hu. replace (18446744073709547520 * u) with (- (4096 * u) + u * 2^64) by (change (2^64) with 18446744073709551616; lia).
    apply Z_mod_plus_full.
  Qed.
  Lemma mod_unique0 : forall x M, 0 < M -> - M < x < M -> x mod M = 0 -> x = 0.
  Proof.
    intros x M HM Hx H0. pose proof (Z.mod_pos_bound x M HM). pose proof (Z_div_mod_eq_full x M).
    assert (x / M = 0 \/ x / M = -1) by nia. nia.
  Qed.

  Lemma Uri : bv_unsigned (edenot E e_ri) = pgv 208 - 4096 * U 209%nat.
  Proof.
    unfold e_ri. cbn [edenot]. rewrite u_add64, U208, u_mul64, u_lit64a.
    pose proof R208 as A. pose proof R209 as B. unfold pgv.
    change ((-4096) mod 2^64) with 18446744073709547520. rewrite neg4096_mul_mod by lia.
    rewrite Zplus_mod_idemp_r. apply Z.mod_small. change (2^64) with 18446744073709551616. lia.
  Qed.

  Lemma v222_mod : 4096 * U 209%nat = pgv 208 mod 65536.
  Proof.
    pose proof (khas_ok sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ (k_rng_v209rel cs AK)) as K. cbn [kentry_ok edenot] in K.
    rewrite u_add64, u_and64, !u_mul64, !u_lit64a in K. pose proof R208 as A. pose proof R209 as B. unfold pgv.
    change (4096 mod 2^64) with 4096 in K. change (65535 mod 2^64) with (Z.ones 16) in K. rewrite Z.land_ones in K by lia. change (2^16) with 65536 in K.
    change ((-4096) mod 2^64) with 18446744073709547520 in K. rewrite neg4096_mul_mod in K by lia. rewrite Zplus_mod_idemp_l in K.
    rewrite (Z.mod_small (4096 * U 208%nat) (2^64)) in K by (change (2^64) with 18446744073709551616; lia).
    pose proof (Z.mod_pos_bound (4096 * U 208%nat) 65536 ltac:(lia)) as MB.
    assert (Z0 : (- (4096 * U 209%nat) + (4096 * U 208%nat) mod 65536) = 0).
    { apply (mod_unique0 _ (2^64)); [lia| change (2^64) with 18446744073709551616; lia| lia]. }
    lia.
  Qed.

  Lemma sb_val : p_sb P = pgv 208 - 4096 * U 209%nat + 0x10000.
  Proof. unfold p_sb, space_beg_of. cbn [p_b6 P]. rewrite <- v222_mod. lia. Qed.
  Lemma ri_val : p_ri P = bv_unsigned (edenot E e_ri) + 137439019008.
  Proof. unfold p_ri. rewrite sb_val, Uri. unfold kSpaceSize. change (2^37) with 137438953472. lia. Qed.

  Lemma riZ_val : p_ri P = riZ.
  Proof. unfold riZ. rewrite ri_val, Uri. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Notation ZSYM := (zero_sym sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS).
  #[local] Notation MSYM := (mapped_sym sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS).
  #[local] Notation WSYM := (word_sym sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS).
  #[local] Notation WIMG := (word_lit_img sp rdraw brk0 argv envp uid hw fs Hsp Hva cs E R FULL model CS).
  #[local] Notation Lbytes_at := (Lib.Mem.bytes_at BSEGS).
  Lemma Usp0 : bv_unsigned (edenot E e_sp0) = usp.
  Proof.
    unfold e_sp0. cbn [edenot]. rewrite u_add64, !u_mul64, !u_lit64a.
    pose proof (pre_sp0 sp rdraw brk0 argv envp uid hw fs Hsp cs E R FULL model CS) as S0. pose proof R0 as A. pose proof R6 as B.
    change (32768 mod 2^64) with 32768. change (16 mod 2^64) with 16. change (2^64) with 18446744073709551616 in *.
    rewrite (Z.mod_small (32768 * _)) by lia. rewrite (Z.mod_small (16 * _)) by lia. rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma Ustk : stk_top = bv_unsigned (edenot E (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 356)))).
  Proof.
    unfold stk_top. cbn [edenot]. rewrite u_add64, !u_mul64, !u_lit64a. pose proof R0 as A. pose proof R356 as B.
    change (32768 mod 2^64) with 32768. change (4096 mod 2^64) with 4096. change (2^64) with 18446744073709551616 in *.
    rewrite (Z.mod_small (32768 * _)) by lia. rewrite (Z.mod_small (4096 * _)) by lia. rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma Ustkb : stk_top - 8388608 = bv_unsigned (edenot E (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 356))) (ELit (-8388608)))).
  Proof.
    pose proof Ustk as UT. cbn [edenot] in UT |- *. rewrite u_add64. rewrite <- UT. rewrite u_lit64a. unfold stk_top. pose proof R0 as A. pose proof R356 as B.
    change ((-8388608) mod 2^64) with 18446744073701163008.
    replace (32768 * U 0%nat + 4096 * U 356%nat + 18446744073701163008) with ((32768 * U 0%nat + 4096 * U 356%nat - 8388608) + 1 * 2^64) by (change (2^64) with 18446744073709551616; lia).
    rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. change (2^64) with 18446744073709551616. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A_ri_zero : zero_at FULL (p_ri P) 4096.
  Proof.
    intros i Hi. rewrite ri_val. apply (ZSYM e_ri _ 137439019008 4096 eq_refl (k_ri_z cs AK)); lia.
  Qed.
  Lemma A_thr_zero : zero_at FULL (p_thr P + 80) (2800 - 80).
  Proof.
    intros i Hi. cbn [p_thr P].
    pose proof (ZSYM (pg 227) (pgv 227) 80 3088 U227 (k_thr_z80 cs AK) ltac:(lia) i ltac:(lia)) as X. exact X.
  Qed.
  Lemma A_thr_map : mapped FULL (p_thr P) 4096 /\ mapped FULL (p_ctx P) 0x10000.
  Proof.
    pose proof R227 as A. pose proof R228 as B. split; intros i Hi; cbn [p_thr p_ctx P].
    - replace (pgv 227 + i) with (pgv 227 + 0 + i) by lia. apply (MSYM (pg 227) (pgv 227) 0 4096 U227 (k_thr_wr cs AK)); hi_tac.
    - replace (pgv 228 + i) with (pgv 228 + 0 + i) by lia. apply (MSYM (pg 228) (pgv 228) 0 0x10000 U228 (k_ctx_wr cs AK)); hi_tac.
  Qed.
  Lemma A_fs_hints : zero_at FULL (p_fs P) 88.
  Proof. intros i Hi. cbn [p_fs P]. replace (pgv 405 + i) with (pgv 405 + 0 + i) by lia. apply (ZSYM (pg 405) (pgv 405) 0 88 U405 (k_fs_z0 cs AK)); lia. Qed.
  Lemma A_fs_flags : zero_at FULL (p_fs P + kFakeFlagsOffset) (kFakeFramesOffset - kFakeFlagsOffset).
  Proof.
    intros i Hi. unfold kFakeFlagsOffset, kFakeFramesOffset in *. cbn [p_fs P].
    replace (pgv 405 + 4096 + i) with (pgv 405 + 96 + (4000 + i)) by lia.
    apply (ZSYM (pg 405) (pgv 405) 96 0xb08fa0 U405 (k_fs_z96 cs AK)); [lia|]. change (2^15) with 32768 in Hi. lia.
  Qed.
  Lemma sh_pg : forall v, sh (pgv v) = 512 * U v + 2147450880.
  Proof. intros v. unfold sh, pgv, kShadowOffset. replace (4096 * U v) with (512 * U v * 8) by lia. rewrite Z.div_mul by lia. lia. Qed.
  Lemma Ush : forall v lo hi, KH (KRange (EVar v) lo hi) = true -> 0 <= lo -> 4096 * hi < 2^64 ->
    bv_unsigned (edenot E (EMd Instr.M_MUL (ELit 512) (EVar v))) = 512 * U v.
  Proof. intros v lo hi H Hlo Hhi. exact (ub_scale sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS 512 v lo hi H ltac:(lia) Hlo Hhi). Qed.
  Lemma A_fs_map : mapped FULL (p_fs P) kFakeStackBytes /\ mapped FULL (sh (p_fs P)) (kFakeStackBytes / 8).
  Proof using CS AK.
    pose proof R405 as A. pose proof R405z as Az. unfold kFakeStackBytes. change (4096 + 2 ^ 15 + 11 * 2 ^ 20) with 11571200. change (11571200 / 8) with 1446400.
    split; intros i Hi; cbn [p_fs P].
    - replace (pgv 405 + i) with (pgv 405 + 0 + i) by lia. apply (MSYM (pg 405) (pgv 405) 0 11571200 U405 (k_fs_wr cs AK)); hi_tac.
    - rewrite sh_pg. apply (MSYM (EMd Instr.M_MUL (ELit 512) (EVar 405)) (512 * U 405%nat) 2147450880 1446400 (Ush 405%nat _ _ (k_rng_405 cs AK) ltac:(lia) ltac:(lia)) (k_fs_shwr cs AK)); hi_tac.
  Qed.
  Lemma usp_range : 0x7fff80000000 <= usp <= 2^47 /\ usp mod 16 = 0.
  Proof. pose proof Hsp as (H1 & H2 & H3). unfold sp_window_lo, sp_window_hi in *. lia. Qed.
  (* [comment removed for export] *)
  Definition e_pgsh : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 0)) (EMd Instr.M_MUL (ELit 512) (EVar 10)).
  Definition e_shlen : expr :=
    EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 0)) (EMd Instr.M_MUL (ELit (-512)) (EVar 10))) (ELit 17592187092992).
  Definition pgsh : Z := 4096 * U 0%nat + 512 * U 10%nat.
  Lemma R10 : 0 <= U 10%nat <= 7. Proof. exact (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ (k_rng_10 cs AK)). Qed.
  Lemma V10 : U 10%nat = (usp mod 32768) / 4096.
  Proof.
    rewrite (pre_ev_lt9 sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS 10%nat) by (unfold NX0; lia). unfold E0. cbn [ev vals0 nth].
    pose proof usp_range as [UR _]. rewrite u_lit64a. apply Z.mod_small. Z.div_mod_to_equations. lia.
  Qed.
  Lemma pgsh_val : 8 * pgsh = usp - usp mod 4096.
  Proof. unfold pgsh. rewrite (pre_v0 sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS), V10. Z.div_mod_to_equations. lia. Qed.
  Lemma Upgsh : bv_unsigned (edenot E e_pgsh) = pgsh.
  Proof.
    unfold e_pgsh, pgsh. cbn [edenot]. rewrite !u_add64, !u_mul64, !u_lit64a. pose proof R0 as A. pose proof R10 as B.
    change (4096 mod 2^64) with 4096. change (512 mod 2^64) with 512. change (2^64) with 18446744073709551616 in *.
    rewrite (Z.mod_small (4096 * _)) by lia. rewrite (Z.mod_small (512 * _)) by lia. rewrite Z.mod_small by lia. lia.
  Qed.
  Lemma Ushlen : bv_unsigned (edenot E e_shlen) = 17592187092992 - pgsh.
  Proof.
    unfold e_shlen, pgsh. cbn [edenot]. rewrite !u_add64, !u_mul64, !u_lit64a. pose proof R0 as A. pose proof R10 as B.
    change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
  Qed.
  Lemma A_stkshadow_map : mapped FULL (fst stack_shadow_iv) (snd stack_shadow_iv).
  Proof.
    unfold stack_shadow_iv, shadow_region, round_down, round_up, sh, kShadowOffset. cbn [fst snd]. rewrite HCEIL.
    pose proof usp_range as [UR UA]. pose proof pgsh_val as PV.
    intros i Hi.
    pose proof (khas_ok sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ (k_stksh_wr cs AK)) as KW. cbn [kentry_ok] in KW. destruct KW as [_ KW].
    unfold estart, elenZ in KW. cbn [a_base a_off] in KW. fold e_pgsh in KW. fold e_shlen in KW. rewrite Upgsh, Ushlen in KW.
    match goal with |- FULL (Z_to_bv 64 ?a) <> None =>
      specialize (KW (a - (pgsh + 2146402304)) 1%nat ltac:(Z.div_mod_to_equations; lia) ltac:(cbn; Z.div_mod_to_equations; lia));
      replace (pgsh + 2146402304 + (a - (pgsh + 2146402304))) with a in KW by lia;
      intros X;
      apply (store_ok_present _ 1%nat (Z_to_bv 64 a) KW ltac:(rewrite u_lit64a, Z.mod_small; cbn; Z.div_mod_to_equations; lia) 0%nat ltac:(lia));
      rewrite u_lit64a, Z.mod_small, ?Nat2Z.inj_0, Z.add_0_r by (Z.div_mod_to_equations; lia);
      [ apply (find_segment1_none_outside BSEGS (img_lo BOTH) (img_hi BOTH) _ both_segs_in_hull); cbn [img_lo img_hi BOTH]; Z.div_mod_to_equations; lia
      | unfold Mr, mrestrict; destruct (hid BOTH argH E cs model (Z_to_bv 64 a)); [reflexivity|exact X] ]
    end.
  Qed.
  Lemma A_imgshadow_map : mapped FULL 0x7fffa000 0xbf400.
  Proof. intros i Hi. replace (0x7fffa000 + i) with (0 + 2147459072 + i) by lia. apply (MSYM (ELit 0) 0 2147459072 783360 (ub_lit E) (k_imgsh_wr cs AK)); hi_tac. Qed.
  Lemma A_maps : mapped FULL (usp - 0x800000) 0x800000.
  Proof.
    pose proof usp_range as [U _]. intros i Hi. replace (usp - 0x800000 + i) with (usp + (-8388608) + i) by lia.
    apply (MSYM e_sp0 usp (-8388608) 8388608 Usp0 (k_stk_wr cs AK)); hi_tac.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma CELL : forall i a bs, nth_error A0_CELLS i = Some (a, bs) -> Lbytes_at FULL a bs.
  Proof. intros i a bs H. exact (cells_nth sp rdraw brk0 argv envp uid hw fs Hsp Hva cs E R FULL model CS A0_CELLS i a bs CC H). Qed.
  Ltac cell i := exact (CELL i _ _ eq_refl).

  Lemma wz_of_U : forall (w : word) z, bv_unsigned w = z -> w = Z_to_bv 64 z.
  Proof. intros w z H. apply bv_eq. rewrite u_lit64a, <- H. pose proof (u64_range w). rewrite Z.mod_small by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma u64_sym : forall b B off ve V, bv_unsigned (edenot E b) = B -> KH (KWord (SA b off) 8 ve) = true ->
    bv_unsigned (edenot E ve) = V -> 0 <= B + off -> (B + off + 8 <= img_lo BOTH \/ img_hi BOTH <= B + off) -> B + off + 8 <= 2^64 ->
    ACells.u64_at BSEGS FULL (B + off) V.
  Proof.
    intros b B off ve V Ub H Uv H0 Hlo Hhi. unfold ACells.u64_at, Lib.Mem.le8. rewrite <- (wz_of_U _ _ Uv).
    exact (WSYM b B off 8 ve Ub H H0 Hlo Hhi).
  Qed.
  Lemma u64_symL : forall b B off v, bv_unsigned (edenot E b) = B -> KH (KWord (SA b off) 8 (ELit v)) = true ->
    0 <= v < 2^64 -> 0 <= B + off -> (B + off + 8 <= img_lo BOTH \/ img_hi BOTH <= B + off) -> B + off + 8 <= 2^64 -> ACells.u64_at BSEGS FULL (B + off) v.
  Proof. intros b B off v Ub H Hv H0 Hlo Hhi. apply (u64_sym b B off (ELit v) v Ub H); [apply ulit; exact Hv| exact H0| exact Hlo| exact Hhi]. Qed.
  Lemma u32_symL : forall b B off v, bv_unsigned (edenot E b) = B -> KH (KWord (SA b off) 4 (ELit v)) = true ->
    0 <= B + off -> (B + off + 4 <= img_lo BOTH \/ img_hi BOTH <= B + off) -> B + off + 4 <= 2^64 -> ACells.u32_at BSEGS FULL (B + off) v.
  Proof. intros b B off v Ub H H0 Hlo Hhi. unfold ACells.u32_at, Lib.Mem.le4. exact (WSYM b B off 4 (ELit v) Ub H H0 Hlo Hhi). Qed.
  Lemma u8_symL : forall b B off v, bv_unsigned (edenot E b) = B -> KH (KWord (SA b off) 1 (ELit v)) = true ->
    0 <= B + off -> (B + off + 1 <= img_lo BOTH \/ img_hi BOTH <= B + off) -> B + off + 1 <= 2^64 -> ACells.u8_at BSEGS FULL (B + off) v.
  Proof.
    intros b B off v Ub H H0 Hlo Hhi. unfold ACells.u8_at.
    pose proof (WSYM b B off 1 (ELit v) Ub H H0 Hlo Hhi) as X. cbn [word_to_le_bytes Z_to_le_bytes edenot] in X.
    replace (Z_to_bv 8 v) with (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 v))); [exact X|].
    apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 8) with (2^8). change (bv_modulus 64) with (2^64).
    symmetry. apply Znumtheory.Zmod_div_mod; [lia| lia| exists (2^56); reflexivity].
  Qed.
  (* [comment removed for export] *)
  Lemma u64_img : forall a ve V, KH (KWord (SA (ELit 0) a) 8 ve) = true -> bv_unsigned (edenot E ve) = V ->
    img_lo BOTH <= a -> a + 8 <= img_hi BOTH -> ACells.u64_at BSEGS FULL a V.
  Proof. intros a ve V H Uv Hlo Hhi. unfold ACells.u64_at, Lib.Mem.le8. rewrite <- (wz_of_U _ _ Uv). exact (WIMG a 8 ve H Hlo Hhi). Qed.
  (* [comment removed for export] *)
  Lemma u8_zero : forall a, FULL (Z_to_bv 64 a) = Some (Z_to_bv 8 0) -> 0 <= a < 2^64 -> ACells.u8_at BSEGS FULL a 0.
  Proof.
    intros a H Ha. unfold ACells.u8_at. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    destruct i; [| lia]. rewrite Z.add_0_r. unfold Lib.Mem.mrd, Lib.Mem.wa. rewrite H. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma log2_lt64 : forall x, 0 <= x < 2^64 -> Z.log2 x < 64.
  Proof. intros x Hx. destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.log2_nonpos; lia|]. apply Z.log2_lt_pow2; lia. Qed.
  Lemma lxor_u64 : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> 0 <= Z.lxor a b < 2^64.
  Proof.
    intros a b Ha Hb. split; [apply Z.lxor_nonneg; lia|].
    destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NZ]; [lia|].
    apply Z.log2_lt_pow2; [pose proof (proj2 (Z.lxor_nonneg a b) ltac:(lia)); lia|].
    eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
    apply Z.max_lub_lt; apply log2_lt64; lia.
  Qed.
  Lemma depot_hashC_range : forall ws, 0 <= ADepotM.depot_hashC ws < 2^64.
  Proof. intros ws. unfold ADepotM.depot_hashC. apply lxor_u64; unfold ADepotM.uw; apply u64_range. Qed.

  Lemma len_k1 : 1 <= Z.of_nat (length k1) <= 255.
  Proof. pose proof (kd_k1 cs k1 KD) as [[A B] _]. lia. Qed.

  Lemma A_depot : a0_depot_raw P k1 FULL.
  Proof using Hsp Hva CS AK CC KD.
    pose proof R480 as A5. pose proof R481 as A6. pose proof R480z as A5z. pose proof R481z as A6z. pose proof len_k1 as LK.
    constructor; cbn [p_nodes0 p_frames0 P].
    - exact (kd_k1 cs k1 KD).
    - (* [comment removed for export] *) intros b Hb.
      assert (BK : 0 <= ADepotM.depot_bucket k1 < 2^20) by (unfold ADepotM.depot_bucket; apply Z.mod_pos_bound; lia).
      destruct (Z.eqb_spec b (ADepotM.depot_bucket k1)) as [->|NE].
      + unfold ACells.u32_at, Lib.Mem.le4. exact (WIMG _ 4 (ELit 1) (kd_tab cs k1 KD) ltac:(cbn -[Z.pow]; lia) ltac:(cbn -[Z.pow ADepotM.depot_bucket]; lia)).
      + (* [comment removed for export] *)
        pose proof (kd_own cs k1 KD) as OWN.
        destruct (Z.eq_dec (al_theDepot AL_pboth + 4 * b) (DEPOT_SLOT_A + DEPOT_SLOT_B - (al_theDepot AL_pboth + 4 * ADepotM.depot_bucket k1))) as [EO|NO].
        * assert (OT : DEPOT_SLOT_A + DEPOT_SLOT_B - (al_theDepot AL_pboth + 4 * ADepotM.depot_bucket k1) = DEPOT_SLOT_A
                       \/ DEPOT_SLOT_A + DEPOT_SLOT_B - (al_theDepot AL_pboth + 4 * ADepotM.depot_bucket k1) = DEPOT_SLOT_B)
            by (clear - OWN; destruct OWN as [O|O]; rewrite O; [right | left]; lia).
          rewrite EO. unfold ACells.u32_at, Lib.Mem.le4.
          exact (WIMG _ 4 (ELit 0) (kd_tabo cs k1 KD)
                   ltac:(clear - OT; destruct OT as [O|O]; rewrite O; unfold DEPOT_SLOT_A, DEPOT_SLOT_B; cbn -[Z.pow]; lia)
                   ltac:(clear - OT; destruct OT as [O|O]; rewrite O; unfold DEPOT_SLOT_A, DEPOT_SLOT_B; cbn -[Z.pow]; lia)).
        * unfold ACells.u32_at. change (Lib.Mem.le4 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) (Z.to_nat 4)).
          assert (NA : al_theDepot AL_pboth + 4 * b <> DEPOT_SLOT_A /\ al_theDepot AL_pboth + 4 * b <> DEPOT_SLOT_B).
          { clear - OWN NO NE. split; intros X; destruct OWN as [O|O]; rewrite O in NO; unfold DEPOT_SLOT_A, DEPOT_SLOT_B in *; lia. }
          destruct NA as [NA NB]. clear OWN NO. unfold DEPOT_SLOT_A, DEPOT_SLOT_B in *. cbn in NA, NB.
          destruct (Z_lt_le_dec (al_theDepot AL_pboth + 4 * b) 1718136) as [LT|GE]; [| destruct (Z_lt_le_dec (al_theDepot AL_pboth + 4 * b) 2202228) as [LT2|GE2]].
          -- cbn in LT. apply (img_zero_fill sp rdraw brk0 argv envp uid hw fs Hsp Hva cs E R FULL model CS _ _ _ 4 (kd_img_lo cs k1 KD));
               [unfold DEPOT_SLOT_A, DEPOT_SLOT_B; cbn; lia| unfold DEPOT_SLOT_A, DEPOT_SLOT_B; cbn; lia| lia| unfold DEPOT_SLOT_A, DEPOT_SLOT_B; cbn; lia| unfold DEPOT_SLOT_A, DEPOT_SLOT_B; cbn; lia|].
             intros a Ha. apply img0_depot_tab. cbn in Ha |- *. lia.
          -- cbn in GE, LT2. apply (img_zero_fill sp rdraw brk0 argv envp uid hw fs Hsp Hva cs E R FULL model CS _ _ _ 4 (kd_img_md cs k1 KD));
               [unfold DEPOT_SLOT_A, DEPOT_SLOT_B; cbn; lia| unfold DEPOT_SLOT_A, DEPOT_SLOT_B; cbn; lia| lia| unfold DEPOT_SLOT_A, DEPOT_SLOT_B; cbn; lia| unfold DEPOT_SLOT_A, DEPOT_SLOT_B; cbn; lia|].
             intros a Ha. apply img0_depot_tab. cbn in Ha |- *. lia.
          -- cbn in GE, GE2. apply (img_zero_fill sp rdraw brk0 argv envp uid hw fs Hsp Hva cs E R FULL model CS _ _ _ 4 (kd_img_hi cs k1 KD));
               [unfold DEPOT_SLOT_A, DEPOT_SLOT_B; cbn; lia| unfold DEPOT_SLOT_A, DEPOT_SLOT_B; cbn; lia| lia| unfold DEPOT_SLOT_A, DEPOT_SLOT_B; cbn; lia| unfold DEPOT_SLOT_A, DEPOT_SLOT_B; cbn; lia|].
             intros a Ha. apply img0_depot_tab. cbn in Ha |- *. lia.
    - (* [comment removed for export] *) cell 31%nat.
    - (* [comment removed for export] *) apply (u64_img _ (pg 480) _ (k_map1_0 cs AK) U480); cbn; lia.
    - (* [comment removed for export] *) intros j Hj. unfold kDepotNodesL1 in Hj. unfold ACells.u64_at. change (Lib.Mem.le8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) (Z.to_nat 8)).
      apply (img_zero_fill sp rdraw brk0 argv envp uid hw fs Hsp Hva cs E R FULL model CS _ _ _ 8 (k_img_map1 cs AK)); [cbn; lia| cbn; change (2^15) with 32768 in Hj; lia| lia| cbn; lia| cbn; lia|].
      intros a Ha. apply img0_depot_map1. cbn in Ha |- *. change (2^15) with 32768 in Hj. lia.
    - (* [comment removed for export] *) split; [| split].
      + apply (u64_symL (pg 480) (pgv 480) 16 _ U480 (kd_hash cs k1 KD)); [| hi_tac| hi_tac| hi_tac].
        apply depot_hashC_range.
      + apply (u32_symL (pg 480) (pgv 480) 24 0 U480 (k_nd_24 cs AK)); hi_tac.
      + apply (u32_symL (pg 480) (pgv 480) 28 1 U480 (k_nd_28 cs AK)); hi_tac.
    - (* [comment removed for export] *) split; intros i Hi.
      + replace (pgv 480 + i) with (pgv 480 + 0 + i) by lia. apply (ZSYM (pg 480) (pgv 480) 0 16 U480 (k_nd_z0 cs AK)); lia.
      + apply (ZSYM (pg 480) (pgv 480) 32 0xfffe0 U480 (k_nd_z32 cs AK)); unfold kDepotNodesBlock in *; lia.
    - (* [comment removed for export] *) apply (u64_img _ (ELit (1 + Z.of_nat (length k1))) _ (kd_total cs k1 KD)); [cbn [edenot]; rewrite u_lit64a; apply Z.mod_small; lia| cbn; lia| cbn; lia].
    - (* [comment removed for export] *) cell 32%nat.
    - (* [comment removed for export] *) split; [| split].
      + apply (u64_img _ (pg 481) _ (k_ss_blk0 cs AK) U481); cbn; lia.
      + unfold ACells.u32_at, Lib.Mem.le4. exact (WIMG _ 4 (ELit _) (kd_stored cs k1 KD) ltac:(cbn; lia) ltac:(cbn; lia)).
      + cell 33%nat.
    - (* [comment removed for export] *) split; [| split].
      + replace (pgv 481) with (pgv 481 + 0) by lia. apply (u64_symL (pg 481) (pgv 481) 0 _ U481 (kd_len cs k1 KD)); [lia| hi_tac| hi_tac| hi_tac].
      + intros t w Ht. pose proof (kd_k1 cs k1 KD) as [_ FW]. pose proof (proj1 (Forall_forall _ _) FW w (nth_error_In _ _ Ht)) as Wr. cbn beta in Wr.
        assert (TL : (t < length k1)%nat) by (apply nth_error_Some; rewrite Ht; discriminate).
        apply (u64_symL (pg 481) (pgv 481) _ _ U481 (kd_keys cs k1 KD t w Ht)); [lia| hi_tac| hi_tac| hi_tac].
      + intros i Hi. apply (ZSYM (pg 481) (pgv 481) _ _ U481 (kd_frz cs k1 KD)); unfold kStackStoreBlockBytes in *; lia.
    - (* [comment removed for export] *) split; intros i Hi.
      + replace (pgv 480 + i) with (pgv 480 + 0 + i) by lia. apply (MSYM (pg 480) (pgv 480) 0 0x100000 U480 (k_nd_wr cs AK)); unfold kDepotNodesBlock in *; hi_tac.
      + replace (pgv 481 + i) with (pgv 481 + 0 + i) by lia. apply (MSYM (pg 481) (pgv 481) 0 0x800000 U481 (k_fr_wr cs AK)); unfold kStackStoreBlockBytes in *; hi_tac.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition den (p : expr * expr) : Z * Z := (uE E (fst p), uE E (snd p)).
  Lemma Uri_page : uE E (EAlu Instr.ALU_ADD e_ri (ELit 137439019008)) = riZ.
  Proof.
    unfold uE. cbn [edenot]. rewrite u_add64. rewrite Uri, u_lit64a. unfold riZ. pose proof R208. pose proof R209. unfold pgv.
    change (137439019008 mod 2^64) with 137439019008. apply Z.mod_small. change (2^64) with 18446744073709551616. lia.
  Qed.
  Lemma PGSP_val : PGSP = usp - usp mod 4096.
  Proof. unfold PGSP. pose proof pgsh_val as PV. unfold pgsh in PV. lia. Qed.
  Lemma usp_top : PGSP <= usp /\ usp < PGSP + 4096 /\ 0x7fff80000000 <= usp <= 2^47.
  Proof. pose proof PGSP_val. pose proof usp_range as [A B]. Z.div_mod_to_equations. lia. Qed.
  Lemma Uband_b : uE E (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 10))) (ELit (-8388608))) = PGSP - 8388608.
  Proof.
    unfold uE, PGSP. cbn [edenot]. rewrite !u_add64, !u_mul64, !u_lit64a. pose proof R0 as A. pose proof R10 as B.
    change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
  Qed.
  Lemma Uband_n : uE E (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-32768)) (EVar 0)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 10))) (ELit 140737496743936)) = 140737496743936 - PGSP.
  Proof.
    unfold uE, PGSP. cbn [edenot]. rewrite !u_add64, !u_mul64, !u_lit64a. pose proof R0 as A. pose proof R10 as B.
    change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
  Qed.
  Definition VISL : list (Z * Z) :=
    [(pgv 4115, 4096); (pgv 498, 4096); (pgv 481, 8388608); (pgv 480, 1048576); (pgv 405, 11571200); (pgv 322, 4096);
     (pgv 257, 4096); (pgv 228, 65536); (pgv 227, 4096); (riZ, 4096); (pgv 207, 3727360); (pgv 78, 65536);
     (65536, 6266880); (PGSP - 8388608, 140737496743936 - PGSP)].
  (* [comment removed for export] *)
  Ltac a0_den1 := first [ exact U78 | exact U207 | exact U208 | exact U226 | exact U227 | exact U228 | exact U257 | exact U322 | exact U323 | exact U405 | exact U422 | exact U423 | exact U480 | exact U481 | exact U498 | exact U4115 | exact U5 | exact Uri_page | exact Uband_b | exact Uband_n
                        | (apply ulit; lia) | (unfold uE; apply ulit; lia) ].
  Lemma vis_denl : map den (a_vis cs) = VISL.
  Proof.
    rewrite (s_vis cs gh ASS). list_eq_lit; unfold den; cbn [fst snd]; apply f_equal2; a0_den1.
  Qed.
  (* [comment removed for export] *)
  Definition GHLA : list (Z * Z) := [(pgv 323, 4096); (pgv 422 + 4096, 4096); (pgv 423, 4096); (pgv 5, 8192); (pgv 422 + 4096, 4096); (pgv 423, 4096)].
  Definition GHLB : list (Z * Z) := [(pgv 323, 4096); (pgv 422 + 4096, 4096); (pgv 423, 4096); (pgv 422 + 4096, 4096); (pgv 423, 4096)].
  Lemma U422p : uE E (EAlu Instr.ALU_ADD (pg 422) (ELit 4096)) = pgv 422 + 4096.
  Proof.
    unfold uE. cbn [edenot]. rewrite u_add64. rewrite U422, u_lit64a. pose proof R422. unfold pgv. change (2^64) with 18446744073709551616 in *. Z.div_mod_to_equations. lia.
  Qed.
  (* [comment removed for export] *)
  Definition gok (q : Z * Z) : Prop :=
    4096 <= fst q /\ fst q mod 4096 = 0 /\ (snd q = 4096 \/ snd q = 8192) /\ fst q + snd q <= 2^47
    /\ (fst q + snd q <= LOWSHZ \/ KHIZ <= fst q).
  Ltac gok_tac := a0_natz_all; unfold gok, LOWSHZ, KHIZ in *; cbn [fst snd]; unfold pgv in *; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
                  first [lia | Z.div_mod_to_equations; lia].
  Lemma ghost_facts : exists GHL, map den gh = GHL /\ Forall gok GHL /\ (length GHL <= 6)%nat.
  Proof.
    pose proof R323 as A1. pose proof R422 as A2. pose proof R423 as A3. pose proof R5 as A5.
    pose proof (disj_of_k _ _ _ _ _ _ (k_band_14 cs AK) (ulit 2147446784 ltac:(lia)) U323 ltac:(lia) ltac:(lia)) as B1.
    pose proof (disj_of_k _ _ _ _ _ _ (k_band_9 cs AK) (ulit 2147446784 ltac:(lia)) U422p ltac:(lia) ltac:(lia)) as B2.
    pose proof (disj_of_k _ _ _ _ _ _ (k_band_8 cs AK) (ulit 2147446784 ltac:(lia)) U423 ltac:(lia) ltac:(lia)) as B3.
    assert (DA : map den A0_GHOST_A = GHLA).
    { list_eq_lit; unfold den; cbn [fst snd]; apply f_equal2; first [exact U422p | a0_den1]. }
    assert (DB : map den A0_GHOST_B = GHLB).
    { list_eq_lit; unfold den; cbn [fst snd]; apply f_equal2; first [exact U422p | a0_den1]. }
    destruct GH as [(EQ & R5t & D5)|EQ]; rewrite EQ.
    - exists GHLA. split; [exact DA|]. split; [| cbn; lia].
      pose proof (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ R5t) as A5t.
      pose proof (disj_of_k _ _ _ _ _ _ D5 (ulit 2147446784 ltac:(lia)) U5 ltac:(lia) ltac:(lia)) as B5.
      unfold pgv in *. forall_lit; gok_tac.
    - exists GHLB. split; [exact DB|]. split; [| cbn; lia].
      unfold pgv in *. forall_lit; gok_tac.
  Qed.
  (* [comment removed for export] *)
  Lemma ghost_b6 : forall p, In p (a_ghost cs) -> uE E (fst p) + uE E (snd p) <= pgv 208 \/ pgv 208 + 137439023104 <= uE E (fst p).
  Proof.
    intros p Hp. rewrite (s_ghost cs gh ASS) in Hp.
    pose proof (disj_of_k _ _ _ _ _ _ (k_disj_208_323 cs AK) U208 U323 ltac:(lia) ltac:(lia)) as D1.
    pose proof (disj_of_k _ _ _ _ _ _ (k_disj_208_422p cs AK) U208 U422p ltac:(lia) ltac:(lia)) as D2.
    pose proof (disj_of_k _ _ _ _ _ _ (k_disj_208_423 cs AK) U208 U423 ltac:(lia) ltac:(lia)) as D3.
    pose proof R208 as Q208.
    assert (DA : map den A0_GHOST_A = GHLA).
    { list_eq_lit; unfold den; cbn [fst snd]; apply f_equal2; first [exact U422p | a0_den1]. }
    assert (DB : map den A0_GHOST_B = GHLB).
    { list_eq_lit; unfold den; cbn [fst snd]; apply f_equal2; first [exact U422p | a0_den1]. }
    pose proof (in_map den _ _ Hp) as Hd. unfold den in Hd at 1. cbn [fst snd] in Hd.
    remember (uE E (fst p)) as b eqn:Hb. remember (uE E (snd p)) as n eqn:Hn. clear Hb Hn.
    destruct GH as [(EQ & R5t & D5)|EQ]; rewrite EQ, ?DA, ?DB in Hd.
    - pose proof (pre_range sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ _ _ R5t) as A5t.
      in_cases2 Hd; (clear - D1 D2 D3 Q208 A5t; a0_natz_all; unfold pgv in *; lia).
    - in_cases2 Hd; (clear - D1 D2 D3 Q208; a0_natz_all; unfold pgv in *; lia).
  Qed.
  (* [comment removed for export] *)
  Definition vok (q : Z * Z) : Prop :=
    4096 <= fst q /\ fst q mod 4096 = 0 /\ 0 < snd q /\ snd q mod 4096 = 0 /\ fst q + snd q <= 2^47
    /\ (fst q + snd q <= LOWSHZ \/ KHIZ <= fst q).
  Lemma pgv_mod : forall v, pgv v mod 4096 = 0.
  Proof. intros v. unfold pgv. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
  Lemma riZ_facts : pgv 208 + 4096 <= riZ - 137438953472 /\ riZ + 4096 <= pgv 208 + 137439023104 /\ riZ mod 4096 = 0.
  Proof.
    pose proof R208. pose proof R209. pose proof v222_mod as VM. pose proof (Z.mod_pos_bound (pgv 208) 65536 ltac:(lia)).
    unfold riZ. split; [lia|]. split; [lia|].
    unfold pgv. replace (4096 * U 208%nat - 4096 * U 209%nat + 137439019008) with ((U 208%nat - U 209%nat + 33554448) * 4096) by lia. apply Z_mod_mult.
  Qed.
  Ltac vok_tac := a0_natz_all; unfold vok, LOWSHZ, KHIZ in *; cbn [fst snd img_lo img_hi BOTH] in *; rewrite ?pgv_mod; unfold pgv in *;
                  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [lia | reflexivity | Z.div_mod_to_equations; lia].
  Lemma VOK4115 : vok (pgv 4115, 4096).
  Proof. pose proof AP4115z. pose proof LH4115z. pose proof R4115z. pose proof usp_range as [UR _]. vok_tac. Qed.
  Lemma VOK498 : vok (pgv 498, 4096).
  Proof. pose proof AP498z. pose proof LH498z. pose proof R498z. pose proof usp_range as [UR _]. vok_tac. Qed.
  Lemma VOK481 : vok (pgv 481, 8388608).
  Proof. pose proof AP481z. pose proof LH481z. pose proof R481z. pose proof usp_range as [UR _]. vok_tac. Qed.
  Lemma VOK480 : vok (pgv 480, 1048576).
  Proof. pose proof AP480z. pose proof LH480z. pose proof R480z. pose proof usp_range as [UR _]. vok_tac. Qed.
  Lemma VOK405 : vok (pgv 405, 11571200).
  Proof. pose proof AP405z. pose proof LH405z. pose proof R405z. pose proof usp_range as [UR _]. vok_tac. Qed.
  Lemma VOK322 : vok (pgv 322, 4096).
  Proof. pose proof AP322z. pose proof LH322z. pose proof R322z. pose proof usp_range as [UR _]. vok_tac. Qed.
  Lemma VOK257 : vok (pgv 257, 4096).
  Proof. pose proof AP257z. pose proof LH257z. pose proof R257z. pose proof usp_range as [UR _]. vok_tac. Qed.
  Lemma VOK228 : vok (pgv 228, 65536).
  Proof. pose proof AP228z. pose proof LH228z. pose proof R228z. pose proof usp_range as [UR _]. vok_tac. Qed.
  Lemma VOK227 : vok (pgv 227, 4096).
  Proof. pose proof AP227z. pose proof LH227z. pose proof R227z. pose proof usp_range as [UR _]. vok_tac. Qed.
  Lemma VOK207 : vok (pgv 207, 3727360).
  Proof. pose proof AP207z. pose proof LH207z. pose proof R207z. pose proof usp_range as [UR _]. vok_tac. Qed.
  Lemma VOK78 : vok (pgv 78, 65536).
  Proof. pose proof AP78. pose proof LH78. pose proof R78. pose proof usp_range as [UR _]. vok_tac. Qed.
  Lemma VOKri : vok (riZ, 4096).
  Proof. pose proof AP208. pose proof R208. pose proof R209. (first [ pose proof (riZ_facts) as dR_1; dand3 dR_1 as RI1 RI2 RI3 | pose proof riZ_facts as (RI1 & RI2 & RI3) ]). pose proof usp_range as [UR _].
         unfold vok, LOWSHZ, KHIZ in *; cbn [fst snd img_lo img_hi BOTH] in *. unfold pgv in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; first [lia | exact RI3 | reflexivity]. Qed.
  Lemma VOKimg : vok (65536, 6266880).
  Proof. vok_tac. Qed.
  Lemma VOKband : vok (PGSP - 8388608, 140737496743936 - PGSP).
  Proof. pose proof usp_top as UT. pose proof PGSP_val as PV. unfold PGSP in *. pose proof R0. pose proof R10. vok_tac. Qed.
  Lemma visl_ok : Forall vok VISL.
  Proof.
    forall_lit; [ exact VOK4115 | exact VOK498 | exact VOK481 | exact VOK480 | exact VOK405 | exact VOK322 | exact VOK257 | exact VOK228 | exact VOK227 | exact VOKri | exact VOK207 | exact VOK78 | exact VOKimg | exact VOKband ].
  Qed.
  Lemma vis_ok : forall p, In p (a_vis cs) -> vok (den p).
  Proof. intros p Hp. apply (proj1 (Forall_forall _ _) visl_ok). rewrite <- vis_denl. apply in_map. exact Hp. Qed.
  Lemma ghost_ok : forall p, In p (a_ghost cs) -> gok (den p).
  Proof.
    intros p Hp. (first [ dand4 ghost_facts as GHL EQ F _ | destruct ghost_facts as (GHL & EQ & F & _) ]). rewrite (s_ghost cs gh ASS) in Hp. rewrite <- EQ in F.
    apply (proj1 (Forall_forall _ _) F). apply in_map. exact Hp.
  Qed.
  (* [comment removed for export] *)
  Lemma visl_vis0 : forall q, In q VISL -> In q (AState.VIS0 P) \/ q = (PGSP - 8388608, 140737496743936 - PGSP).
  Proof.
    all_in_lit; first [right; reflexivity | left; first [in_nth | rewrite <- riZ_val; in_nth]].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma existsb_false_forall : forall {X} (f : X -> bool) l, (forall x, In x l -> f x = false) -> existsb f l = false.
  Proof.
    intros X f l H. destruct (existsb f l) eqn:Eq; [|reflexivity]. apply existsb_exists in Eq as [x [Hx Fx]]. rewrite (H x Hx) in Fx. discriminate.
  Qed.
  Lemma in_vis_false : forall z, LOWSHZ <= z < KHIZ -> in_vis E cs z = false.
  Proof.
    intros z Hz. unfold in_vis. apply existsb_false_forall. intros p Hp. pose proof (vis_ok p Hp) as V. unfold vok, den in V. cbn [fst snd] in V.
    apply Bool.andb_false_iff. (first [ dand6 V as _ _ _ _ _ [D|D] | destruct V as (_ & _ & _ & _ & _ & [D|D]) ]); [right; apply Z.ltb_ge; lia| left; apply Z.leb_gt; lia].
  Qed.
  Lemma in_ghost_false : forall z, LOWSHZ <= z < KHIZ -> in_ghost E cs z = false.
  Proof.
    intros z Hz. unfold in_ghost. apply existsb_false_forall. intros p Hp. pose proof (ghost_ok p Hp) as V. unfold gok, den in V. cbn [fst snd] in V.
    apply Bool.andb_false_iff. (first [ dand5 V as _ _ _ _ [D|D] | destruct V as (_ & _ & _ & _ & [D|D]) ]); [right; apply Z.ltb_ge; lia| left; apply Z.leb_gt; lia].
  Qed.
  (* [comment removed for export] *)
  Lemma in_sh_false : forall z, ~ AState.in_vis_shadow (AState.VIS0 P) z ->
    ~ (2147450880 + (PGSP - 8388608) / 8 <= z < 2147450880 + (usp - 8388608) / 8) -> in_sh BOTH E cs z = false.
  Proof.
    intros z Hn Hband. unfold in_sh. apply existsb_false_forall. intros p Hp.
    destruct ((sh_lo BOTH E p <=? z) && (z <? sh_hi BOTH E p))%bool eqn:Eq; [|reflexivity]. exfalso.
    apply Bool.andb_true_iff in Eq as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    unfold sh_lo, sh_hi in E1, E2. cbn [shadow_off BOTH] in E1, E2.
    pose proof (in_map den _ _ Hp) as Hd. rewrite vis_denl in Hd.
    destruct (visl_vis0 _ Hd) as [HV|EQ].
    - apply Hn. exists (uE E (fst p)), (uE E (snd p)). split; [exact HV|]. unfold kShadowOffset. lia.
    - unfold den in EQ. injection EQ as E3 E4. rewrite E3, E4 in *. pose proof usp_top as UT.
      destruct (Z_lt_le_dec z (2147450880 + (usp - 8388608) / 8)) as [LT|GE]; [apply Hband; lia|].
      apply Hn. exists (usp - 8388608), (2^47 - (usp - 8388608)). split.
      + unfold AState.VIS0. cbn [In]. do 13 right. left. unfold stack_band_iv. rewrite HCEIL. reflexivity.
      + unfold kShadowOffset. replace (usp - 8388608 + (2 ^ 47 - (usp - 8388608))) with (2^47) by lia.
        replace (PGSP - 8388608 + (140737496743936 - PGSP)) with (2^47) in E2 by lia. lia.
  Qed.
  Lemma A_hidden : forall z, in_shadow_maps z -> ~ AState.in_vis_shadow (AState.VIS0 P) z -> FULL (Z_to_bv 64 z) = Some (Z_to_bv 8 0).
  Proof.
    intros z Hz Hn. pose proof usp_top as UT. pose proof PGSP_val as PV.
    (* [comment removed for export] *)
    destruct (Z_le_gt_dec (pgsh + 2146402304) z) as [GE|LT].
    { destruct (Z_lt_le_dec z KHIZ) as [LT2|GE2].
      - pose proof (khas_ok sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS _ (k_stksh_z cs AK)) as KZ. cbn [kentry_ok] in KZ. destruct KZ as [_ KZ].
        unfold estart, elenZ in KZ. cbn [a_base a_off] in KZ. fold e_pgsh in KZ. fold e_shlen in KZ. rewrite Upgsh, Ushlen in KZ.
        specialize (KZ (z - (pgsh + 2146402304)) ltac:(unfold KHIZ in LT2; lia)).
        replace (pgsh + 2146402304 + (z - (pgsh + 2146402304))) with z in KZ by lia.
        unfold Mr, mrestrict in KZ. destruct (hid BOTH argH E cs model (Z_to_bv 64 z)); [discriminate KZ| exact KZ].
      - exfalso. unfold in_shadow_maps, kLowShadowMapBeg, kHighShadowMapBeg, kHighShadowMapSize, KHIZ in *. lia. }
    assert (SHF : in_sh BOTH E cs z = false).
    { apply in_sh_false; [exact Hn|]. pose proof pgsh_val. unfold pgsh, PGSP in *. intros [G1 G2]. Z.div_mod_to_equations. lia. }
    unfold in_shadow_maps, kLowShadowMapBeg, kHighShadowMapBeg, kHighShadowMapSize in Hz.
    destruct Hz as [Hz|Hz].
    - apply (pre_hidden_zero sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit cs E R FULL model CS {| am_base := ELit 2147446784; am_len := ELit 268435456; am_kind := KRWLAZY |} z).
      + rewrite (s_maps cs gh ASS). in_nth.
      + reflexivity.
      + reflexivity.
      + unfold uE. cbn [am_base am_len]. rewrite !edenot_lit, !u_lit64a. fold_lit_mods. lia.
      + unfold CEIL. lia.
      + cbn [img_hi BOTH]. lia.
      + apply in_vis_false. unfold LOWSHZ, KHIZ. lia.
      + exact SHF.
      + apply in_ghost_false. unfold LOWSHZ, KHIZ. lia.
    - apply (pre_hidden_zero sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit cs E R FULL model CS {| am_base := ELit 2201439137792; am_len := ELit 15392894357504; am_kind := KRWLAZY |} z).
      + rewrite (s_maps cs gh ASS). in_nth.
      + reflexivity.
      + reflexivity.
      + unfold uE. cbn [am_base am_len]. rewrite !edenot_lit, !u_lit64a. fold_lit_mods. lia.
      + unfold CEIL. lia.
      + cbn [img_hi BOTH]. lia.
      + apply in_vis_false. unfold LOWSHZ, KHIZ. lia.
      + exact SHF.
      + apply in_ghost_false. unfold LOWSHZ, KHIZ. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma or_swap_a0 : forall A B : Prop, A \/ B -> B \/ A.
  Proof. intros A B [H|H]; [right|left]; exact H. Qed.
  Lemma D_498_4115 : pgv 498 + 4096 <= pgv 4115 \/ pgv 4115 + 4096 <= pgv 498.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_498_4115 cs AK) U498 U4115 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_4115_498 : pgv 4115 + 4096 <= pgv 498 \/ pgv 498 + 4096 <= pgv 4115.
  Proof. exact (or_swap_a0 _ _ D_498_4115). Qed.   (* [comment removed for export] *)
  Lemma D_481_4115 : pgv 481 + 8388608 <= pgv 4115 \/ pgv 4115 + 4096 <= pgv 481.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_481_4115 cs AK) U481 U4115 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_4115_481 : pgv 4115 + 4096 <= pgv 481 \/ pgv 481 + 8388608 <= pgv 4115.
  Proof. exact (or_swap_a0 _ _ D_481_4115). Qed.   (* [comment removed for export] *)
  Lemma D_480_4115 : pgv 480 + 1048576 <= pgv 4115 \/ pgv 4115 + 4096 <= pgv 480.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_480_4115 cs AK) U480 U4115 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_4115_480 : pgv 4115 + 4096 <= pgv 480 \/ pgv 480 + 1048576 <= pgv 4115.
  Proof. exact (or_swap_a0 _ _ D_480_4115). Qed.   (* [comment removed for export] *)
  Lemma D_405_4115 : pgv 405 + 11571200 <= pgv 4115 \/ pgv 4115 + 4096 <= pgv 405.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_405_4115 cs AK) U405 U4115 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_4115_405 : pgv 4115 + 4096 <= pgv 405 \/ pgv 405 + 11571200 <= pgv 4115.
  Proof. exact (or_swap_a0 _ _ D_405_4115). Qed.   (* [comment removed for export] *)
  Lemma D_322_4115 : pgv 322 + 4096 <= pgv 4115 \/ pgv 4115 + 4096 <= pgv 322.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_322_4115 cs AK) U322 U4115 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_4115_322 : pgv 4115 + 4096 <= pgv 322 \/ pgv 322 + 4096 <= pgv 4115.
  Proof. exact (or_swap_a0 _ _ D_322_4115). Qed.   (* [comment removed for export] *)
  Lemma D_257_4115 : pgv 257 + 4096 <= pgv 4115 \/ pgv 4115 + 4096 <= pgv 257.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_257_4115 cs AK) U257 U4115 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_4115_257 : pgv 4115 + 4096 <= pgv 257 \/ pgv 257 + 4096 <= pgv 4115.
  Proof. exact (or_swap_a0 _ _ D_257_4115). Qed.   (* [comment removed for export] *)
  Lemma D_228_4115 : pgv 228 + 65536 <= pgv 4115 \/ pgv 4115 + 4096 <= pgv 228.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_228_4115 cs AK) U228 U4115 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_4115_228 : pgv 4115 + 4096 <= pgv 228 \/ pgv 228 + 65536 <= pgv 4115.
  Proof. exact (or_swap_a0 _ _ D_228_4115). Qed.   (* [comment removed for export] *)
  Lemma D_227_4115 : pgv 227 + 4096 <= pgv 4115 \/ pgv 4115 + 4096 <= pgv 227.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_227_4115 cs AK) U227 U4115 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_4115_227 : pgv 4115 + 4096 <= pgv 227 \/ pgv 227 + 4096 <= pgv 4115.
  Proof. exact (or_swap_a0 _ _ D_227_4115). Qed.   (* [comment removed for export] *)
  Lemma D_226_4115 : pgv 226 + 8388608 <= pgv 4115 \/ pgv 4115 + 4096 <= pgv 226.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_226_4115 cs AK) U226 U4115 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_4115_226 : pgv 4115 + 4096 <= pgv 226 \/ pgv 226 + 8388608 <= pgv 4115.
  Proof. exact (or_swap_a0 _ _ D_226_4115). Qed.   (* [comment removed for export] *)
  Lemma D_208_4115 : pgv 208 + 137439023104 <= pgv 4115 \/ pgv 4115 + 4096 <= pgv 208.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_208_4115 cs AK) U208 U4115 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_4115_208 : pgv 4115 + 4096 <= pgv 208 \/ pgv 208 + 137439023104 <= pgv 4115.
  Proof. exact (or_swap_a0 _ _ D_208_4115). Qed.   (* [comment removed for export] *)
  Lemma D_207_4115 : pgv 207 + 3727360 <= pgv 4115 \/ pgv 4115 + 4096 <= pgv 207.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_207_4115 cs AK) U207 U4115 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_4115_207 : pgv 4115 + 4096 <= pgv 207 \/ pgv 207 + 3727360 <= pgv 4115.
  Proof. exact (or_swap_a0 _ _ D_207_4115). Qed.   (* [comment removed for export] *)
  Lemma D_78_4115 : pgv 78 + 65536 <= pgv 4115 \/ pgv 4115 + 4096 <= pgv 78.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_78_4115 cs AK) U78 U4115 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_4115_78 : pgv 4115 + 4096 <= pgv 78 \/ pgv 78 + 65536 <= pgv 4115.
  Proof. exact (or_swap_a0 _ _ D_78_4115). Qed.   (* [comment removed for export] *)
  Lemma D_481_498 : pgv 481 + 8388608 <= pgv 498 \/ pgv 498 + 4096 <= pgv 481.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_481_498 cs AK) U481 U498 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_498_481 : pgv 498 + 4096 <= pgv 481 \/ pgv 481 + 8388608 <= pgv 498.
  Proof. exact (or_swap_a0 _ _ D_481_498). Qed.   (* [comment removed for export] *)
  Lemma D_480_498 : pgv 480 + 1048576 <= pgv 498 \/ pgv 498 + 4096 <= pgv 480.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_480_498 cs AK) U480 U498 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_498_480 : pgv 498 + 4096 <= pgv 480 \/ pgv 480 + 1048576 <= pgv 498.
  Proof. exact (or_swap_a0 _ _ D_480_498). Qed.   (* [comment removed for export] *)
  Lemma D_405_498 : pgv 405 + 11571200 <= pgv 498 \/ pgv 498 + 4096 <= pgv 405.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_405_498 cs AK) U405 U498 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_498_405 : pgv 498 + 4096 <= pgv 405 \/ pgv 405 + 11571200 <= pgv 498.
  Proof. exact (or_swap_a0 _ _ D_405_498). Qed.   (* [comment removed for export] *)
  Lemma D_322_498 : pgv 322 + 4096 <= pgv 498 \/ pgv 498 + 4096 <= pgv 322.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_322_498 cs AK) U322 U498 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_498_322 : pgv 498 + 4096 <= pgv 322 \/ pgv 322 + 4096 <= pgv 498.
  Proof. exact (or_swap_a0 _ _ D_322_498). Qed.   (* [comment removed for export] *)
  Lemma D_257_498 : pgv 257 + 4096 <= pgv 498 \/ pgv 498 + 4096 <= pgv 257.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_257_498 cs AK) U257 U498 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_498_257 : pgv 498 + 4096 <= pgv 257 \/ pgv 257 + 4096 <= pgv 498.
  Proof. exact (or_swap_a0 _ _ D_257_498). Qed.   (* [comment removed for export] *)
  Lemma D_228_498 : pgv 228 + 65536 <= pgv 498 \/ pgv 498 + 4096 <= pgv 228.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_228_498 cs AK) U228 U498 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_498_228 : pgv 498 + 4096 <= pgv 228 \/ pgv 228 + 65536 <= pgv 498.
  Proof. exact (or_swap_a0 _ _ D_228_498). Qed.   (* [comment removed for export] *)
  Lemma D_227_498 : pgv 227 + 4096 <= pgv 498 \/ pgv 498 + 4096 <= pgv 227.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_227_498 cs AK) U227 U498 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_498_227 : pgv 498 + 4096 <= pgv 227 \/ pgv 227 + 4096 <= pgv 498.
  Proof. exact (or_swap_a0 _ _ D_227_498). Qed.   (* [comment removed for export] *)
  Lemma D_226_498 : pgv 226 + 8388608 <= pgv 498 \/ pgv 498 + 4096 <= pgv 226.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_226_498 cs AK) U226 U498 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_498_226 : pgv 498 + 4096 <= pgv 226 \/ pgv 226 + 8388608 <= pgv 498.
  Proof. exact (or_swap_a0 _ _ D_226_498). Qed.   (* [comment removed for export] *)
  Lemma D_208_498 : pgv 208 + 137439023104 <= pgv 498 \/ pgv 498 + 4096 <= pgv 208.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_208_498 cs AK) U208 U498 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_498_208 : pgv 498 + 4096 <= pgv 208 \/ pgv 208 + 137439023104 <= pgv 498.
  Proof. exact (or_swap_a0 _ _ D_208_498). Qed.   (* [comment removed for export] *)
  Lemma D_207_498 : pgv 207 + 3727360 <= pgv 498 \/ pgv 498 + 4096 <= pgv 207.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_207_498 cs AK) U207 U498 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_498_207 : pgv 498 + 4096 <= pgv 207 \/ pgv 207 + 3727360 <= pgv 498.
  Proof. exact (or_swap_a0 _ _ D_207_498). Qed.   (* [comment removed for export] *)
  Lemma D_78_498 : pgv 78 + 65536 <= pgv 498 \/ pgv 498 + 4096 <= pgv 78.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_78_498 cs AK) U78 U498 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_498_78 : pgv 498 + 4096 <= pgv 78 \/ pgv 78 + 65536 <= pgv 498.
  Proof. exact (or_swap_a0 _ _ D_78_498). Qed.   (* [comment removed for export] *)
  Lemma D_480_481 : pgv 480 + 1048576 <= pgv 481 \/ pgv 481 + 8388608 <= pgv 480.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_480_481 cs AK) U480 U481 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_481_480 : pgv 481 + 8388608 <= pgv 480 \/ pgv 480 + 1048576 <= pgv 481.
  Proof. exact (or_swap_a0 _ _ D_480_481). Qed.   (* [comment removed for export] *)
  Lemma D_405_481 : pgv 405 + 11571200 <= pgv 481 \/ pgv 481 + 8388608 <= pgv 405.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_405_481 cs AK) U405 U481 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_481_405 : pgv 481 + 8388608 <= pgv 405 \/ pgv 405 + 11571200 <= pgv 481.
  Proof. exact (or_swap_a0 _ _ D_405_481). Qed.   (* [comment removed for export] *)
  Lemma D_322_481 : pgv 322 + 4096 <= pgv 481 \/ pgv 481 + 8388608 <= pgv 322.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_322_481 cs AK) U322 U481 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_481_322 : pgv 481 + 8388608 <= pgv 322 \/ pgv 322 + 4096 <= pgv 481.
  Proof. exact (or_swap_a0 _ _ D_322_481). Qed.   (* [comment removed for export] *)
  Lemma D_257_481 : pgv 257 + 4096 <= pgv 481 \/ pgv 481 + 8388608 <= pgv 257.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_257_481 cs AK) U257 U481 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_481_257 : pgv 481 + 8388608 <= pgv 257 \/ pgv 257 + 4096 <= pgv 481.
  Proof. exact (or_swap_a0 _ _ D_257_481). Qed.   (* [comment removed for export] *)
  Lemma D_228_481 : pgv 228 + 65536 <= pgv 481 \/ pgv 481 + 8388608 <= pgv 228.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_228_481 cs AK) U228 U481 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_481_228 : pgv 481 + 8388608 <= pgv 228 \/ pgv 228 + 65536 <= pgv 481.
  Proof. exact (or_swap_a0 _ _ D_228_481). Qed.   (* [comment removed for export] *)
  Lemma D_227_481 : pgv 227 + 4096 <= pgv 481 \/ pgv 481 + 8388608 <= pgv 227.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_227_481 cs AK) U227 U481 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_481_227 : pgv 481 + 8388608 <= pgv 227 \/ pgv 227 + 4096 <= pgv 481.
  Proof. exact (or_swap_a0 _ _ D_227_481). Qed.   (* [comment removed for export] *)
  Lemma D_226_481 : pgv 226 + 8388608 <= pgv 481 \/ pgv 481 + 8388608 <= pgv 226.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_226_481 cs AK) U226 U481 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_481_226 : pgv 481 + 8388608 <= pgv 226 \/ pgv 226 + 8388608 <= pgv 481.
  Proof. exact (or_swap_a0 _ _ D_226_481). Qed.   (* [comment removed for export] *)
  Lemma D_208_481 : pgv 208 + 137439023104 <= pgv 481 \/ pgv 481 + 8388608 <= pgv 208.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_208_481 cs AK) U208 U481 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_481_208 : pgv 481 + 8388608 <= pgv 208 \/ pgv 208 + 137439023104 <= pgv 481.
  Proof. exact (or_swap_a0 _ _ D_208_481). Qed.   (* [comment removed for export] *)
  Lemma D_207_481 : pgv 207 + 3727360 <= pgv 481 \/ pgv 481 + 8388608 <= pgv 207.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_207_481 cs AK) U207 U481 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_481_207 : pgv 481 + 8388608 <= pgv 207 \/ pgv 207 + 3727360 <= pgv 481.
  Proof. exact (or_swap_a0 _ _ D_207_481). Qed.   (* [comment removed for export] *)
  Lemma D_78_481 : pgv 78 + 65536 <= pgv 481 \/ pgv 481 + 8388608 <= pgv 78.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_78_481 cs AK) U78 U481 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_481_78 : pgv 481 + 8388608 <= pgv 78 \/ pgv 78 + 65536 <= pgv 481.
  Proof. exact (or_swap_a0 _ _ D_78_481). Qed.   (* [comment removed for export] *)
  Lemma D_405_480 : pgv 405 + 11571200 <= pgv 480 \/ pgv 480 + 1048576 <= pgv 405.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_405_480 cs AK) U405 U480 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_480_405 : pgv 480 + 1048576 <= pgv 405 \/ pgv 405 + 11571200 <= pgv 480.
  Proof. exact (or_swap_a0 _ _ D_405_480). Qed.   (* [comment removed for export] *)
  Lemma D_322_480 : pgv 322 + 4096 <= pgv 480 \/ pgv 480 + 1048576 <= pgv 322.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_322_480 cs AK) U322 U480 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_480_322 : pgv 480 + 1048576 <= pgv 322 \/ pgv 322 + 4096 <= pgv 480.
  Proof. exact (or_swap_a0 _ _ D_322_480). Qed.   (* [comment removed for export] *)
  Lemma D_257_480 : pgv 257 + 4096 <= pgv 480 \/ pgv 480 + 1048576 <= pgv 257.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_257_480 cs AK) U257 U480 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_480_257 : pgv 480 + 1048576 <= pgv 257 \/ pgv 257 + 4096 <= pgv 480.
  Proof. exact (or_swap_a0 _ _ D_257_480). Qed.   (* [comment removed for export] *)
  Lemma D_228_480 : pgv 228 + 65536 <= pgv 480 \/ pgv 480 + 1048576 <= pgv 228.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_228_480 cs AK) U228 U480 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_480_228 : pgv 480 + 1048576 <= pgv 228 \/ pgv 228 + 65536 <= pgv 480.
  Proof. exact (or_swap_a0 _ _ D_228_480). Qed.   (* [comment removed for export] *)
  Lemma D_227_480 : pgv 227 + 4096 <= pgv 480 \/ pgv 480 + 1048576 <= pgv 227.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_227_480 cs AK) U227 U480 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_480_227 : pgv 480 + 1048576 <= pgv 227 \/ pgv 227 + 4096 <= pgv 480.
  Proof. exact (or_swap_a0 _ _ D_227_480). Qed.   (* [comment removed for export] *)
  Lemma D_226_480 : pgv 226 + 8388608 <= pgv 480 \/ pgv 480 + 1048576 <= pgv 226.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_226_480 cs AK) U226 U480 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_480_226 : pgv 480 + 1048576 <= pgv 226 \/ pgv 226 + 8388608 <= pgv 480.
  Proof. exact (or_swap_a0 _ _ D_226_480). Qed.   (* [comment removed for export] *)
  Lemma D_208_480 : pgv 208 + 137439023104 <= pgv 480 \/ pgv 480 + 1048576 <= pgv 208.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_208_480 cs AK) U208 U480 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_480_208 : pgv 480 + 1048576 <= pgv 208 \/ pgv 208 + 137439023104 <= pgv 480.
  Proof. exact (or_swap_a0 _ _ D_208_480). Qed.   (* [comment removed for export] *)
  Lemma D_207_480 : pgv 207 + 3727360 <= pgv 480 \/ pgv 480 + 1048576 <= pgv 207.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_207_480 cs AK) U207 U480 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_480_207 : pgv 480 + 1048576 <= pgv 207 \/ pgv 207 + 3727360 <= pgv 480.
  Proof. exact (or_swap_a0 _ _ D_207_480). Qed.   (* [comment removed for export] *)
  Lemma D_78_480 : pgv 78 + 65536 <= pgv 480 \/ pgv 480 + 1048576 <= pgv 78.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_78_480 cs AK) U78 U480 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_480_78 : pgv 480 + 1048576 <= pgv 78 \/ pgv 78 + 65536 <= pgv 480.
  Proof. exact (or_swap_a0 _ _ D_78_480). Qed.   (* [comment removed for export] *)
  Lemma D_322_405 : pgv 322 + 4096 <= pgv 405 \/ pgv 405 + 11571200 <= pgv 322.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_322_405 cs AK) U322 U405 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_405_322 : pgv 405 + 11571200 <= pgv 322 \/ pgv 322 + 4096 <= pgv 405.
  Proof. exact (or_swap_a0 _ _ D_322_405). Qed.   (* [comment removed for export] *)
  Lemma D_257_405 : pgv 257 + 4096 <= pgv 405 \/ pgv 405 + 11571200 <= pgv 257.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_257_405 cs AK) U257 U405 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_405_257 : pgv 405 + 11571200 <= pgv 257 \/ pgv 257 + 4096 <= pgv 405.
  Proof. exact (or_swap_a0 _ _ D_257_405). Qed.   (* [comment removed for export] *)
  Lemma D_228_405 : pgv 228 + 65536 <= pgv 405 \/ pgv 405 + 11571200 <= pgv 228.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_228_405 cs AK) U228 U405 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_405_228 : pgv 405 + 11571200 <= pgv 228 \/ pgv 228 + 65536 <= pgv 405.
  Proof. exact (or_swap_a0 _ _ D_228_405). Qed.   (* [comment removed for export] *)
  Lemma D_227_405 : pgv 227 + 4096 <= pgv 405 \/ pgv 405 + 11571200 <= pgv 227.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_227_405 cs AK) U227 U405 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_405_227 : pgv 405 + 11571200 <= pgv 227 \/ pgv 227 + 4096 <= pgv 405.
  Proof. exact (or_swap_a0 _ _ D_227_405). Qed.   (* [comment removed for export] *)
  Lemma D_226_405 : pgv 226 + 8388608 <= pgv 405 \/ pgv 405 + 11571200 <= pgv 226.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_226_405 cs AK) U226 U405 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_405_226 : pgv 405 + 11571200 <= pgv 226 \/ pgv 226 + 8388608 <= pgv 405.
  Proof. exact (or_swap_a0 _ _ D_226_405). Qed.   (* [comment removed for export] *)
  Lemma D_208_405 : pgv 208 + 137439023104 <= pgv 405 \/ pgv 405 + 11571200 <= pgv 208.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_208_405 cs AK) U208 U405 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_405_208 : pgv 405 + 11571200 <= pgv 208 \/ pgv 208 + 137439023104 <= pgv 405.
  Proof. exact (or_swap_a0 _ _ D_208_405). Qed.   (* [comment removed for export] *)
  Lemma D_207_405 : pgv 207 + 3727360 <= pgv 405 \/ pgv 405 + 11571200 <= pgv 207.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_207_405 cs AK) U207 U405 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_405_207 : pgv 405 + 11571200 <= pgv 207 \/ pgv 207 + 3727360 <= pgv 405.
  Proof. exact (or_swap_a0 _ _ D_207_405). Qed.   (* [comment removed for export] *)
  Lemma D_78_405 : pgv 78 + 65536 <= pgv 405 \/ pgv 405 + 11571200 <= pgv 78.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_78_405 cs AK) U78 U405 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_405_78 : pgv 405 + 11571200 <= pgv 78 \/ pgv 78 + 65536 <= pgv 405.
  Proof. exact (or_swap_a0 _ _ D_78_405). Qed.   (* [comment removed for export] *)
  Lemma D_257_322 : pgv 257 + 4096 <= pgv 322 \/ pgv 322 + 4096 <= pgv 257.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_257_322 cs AK) U257 U322 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_322_257 : pgv 322 + 4096 <= pgv 257 \/ pgv 257 + 4096 <= pgv 322.
  Proof. exact (or_swap_a0 _ _ D_257_322). Qed.   (* [comment removed for export] *)
  Lemma D_228_322 : pgv 228 + 65536 <= pgv 322 \/ pgv 322 + 4096 <= pgv 228.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_228_322 cs AK) U228 U322 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_322_228 : pgv 322 + 4096 <= pgv 228 \/ pgv 228 + 65536 <= pgv 322.
  Proof. exact (or_swap_a0 _ _ D_228_322). Qed.   (* [comment removed for export] *)
  Lemma D_227_322 : pgv 227 + 4096 <= pgv 322 \/ pgv 322 + 4096 <= pgv 227.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_227_322 cs AK) U227 U322 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_322_227 : pgv 322 + 4096 <= pgv 227 \/ pgv 227 + 4096 <= pgv 322.
  Proof. exact (or_swap_a0 _ _ D_227_322). Qed.   (* [comment removed for export] *)
  Lemma D_226_322 : pgv 226 + 8388608 <= pgv 322 \/ pgv 322 + 4096 <= pgv 226.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_226_322 cs AK) U226 U322 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_322_226 : pgv 322 + 4096 <= pgv 226 \/ pgv 226 + 8388608 <= pgv 322.
  Proof. exact (or_swap_a0 _ _ D_226_322). Qed.   (* [comment removed for export] *)
  Lemma D_208_322 : pgv 208 + 137439023104 <= pgv 322 \/ pgv 322 + 4096 <= pgv 208.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_208_322 cs AK) U208 U322 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_322_208 : pgv 322 + 4096 <= pgv 208 \/ pgv 208 + 137439023104 <= pgv 322.
  Proof. exact (or_swap_a0 _ _ D_208_322). Qed.   (* [comment removed for export] *)
  Lemma D_207_322 : pgv 207 + 3727360 <= pgv 322 \/ pgv 322 + 4096 <= pgv 207.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_207_322 cs AK) U207 U322 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_322_207 : pgv 322 + 4096 <= pgv 207 \/ pgv 207 + 3727360 <= pgv 322.
  Proof. exact (or_swap_a0 _ _ D_207_322). Qed.   (* [comment removed for export] *)
  Lemma D_78_322 : pgv 78 + 65536 <= pgv 322 \/ pgv 322 + 4096 <= pgv 78.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_78_322 cs AK) U78 U322 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_322_78 : pgv 322 + 4096 <= pgv 78 \/ pgv 78 + 65536 <= pgv 322.
  Proof. exact (or_swap_a0 _ _ D_78_322). Qed.   (* [comment removed for export] *)
  Lemma D_228_257 : pgv 228 + 65536 <= pgv 257 \/ pgv 257 + 4096 <= pgv 228.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_228_257 cs AK) U228 U257 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_257_228 : pgv 257 + 4096 <= pgv 228 \/ pgv 228 + 65536 <= pgv 257.
  Proof. exact (or_swap_a0 _ _ D_228_257). Qed.   (* [comment removed for export] *)
  Lemma D_227_257 : pgv 227 + 4096 <= pgv 257 \/ pgv 257 + 4096 <= pgv 227.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_227_257 cs AK) U227 U257 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_257_227 : pgv 257 + 4096 <= pgv 227 \/ pgv 227 + 4096 <= pgv 257.
  Proof. exact (or_swap_a0 _ _ D_227_257). Qed.   (* [comment removed for export] *)
  Lemma D_226_257 : pgv 226 + 8388608 <= pgv 257 \/ pgv 257 + 4096 <= pgv 226.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_226_257 cs AK) U226 U257 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_257_226 : pgv 257 + 4096 <= pgv 226 \/ pgv 226 + 8388608 <= pgv 257.
  Proof. exact (or_swap_a0 _ _ D_226_257). Qed.   (* [comment removed for export] *)
  Lemma D_208_257 : pgv 208 + 137439023104 <= pgv 257 \/ pgv 257 + 4096 <= pgv 208.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_208_257 cs AK) U208 U257 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_257_208 : pgv 257 + 4096 <= pgv 208 \/ pgv 208 + 137439023104 <= pgv 257.
  Proof. exact (or_swap_a0 _ _ D_208_257). Qed.   (* [comment removed for export] *)
  Lemma D_207_257 : pgv 207 + 3727360 <= pgv 257 \/ pgv 257 + 4096 <= pgv 207.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_207_257 cs AK) U207 U257 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_257_207 : pgv 257 + 4096 <= pgv 207 \/ pgv 207 + 3727360 <= pgv 257.
  Proof. exact (or_swap_a0 _ _ D_207_257). Qed.   (* [comment removed for export] *)
  Lemma D_78_257 : pgv 78 + 65536 <= pgv 257 \/ pgv 257 + 4096 <= pgv 78.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_78_257 cs AK) U78 U257 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_257_78 : pgv 257 + 4096 <= pgv 78 \/ pgv 78 + 65536 <= pgv 257.
  Proof. exact (or_swap_a0 _ _ D_78_257). Qed.   (* [comment removed for export] *)
  Lemma D_227_228 : pgv 227 + 4096 <= pgv 228 \/ pgv 228 + 65536 <= pgv 227.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_227_228 cs AK) U227 U228 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_228_227 : pgv 228 + 65536 <= pgv 227 \/ pgv 227 + 4096 <= pgv 228.
  Proof. exact (or_swap_a0 _ _ D_227_228). Qed.   (* [comment removed for export] *)
  Lemma D_226_228 : pgv 226 + 8388608 <= pgv 228 \/ pgv 228 + 65536 <= pgv 226.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_226_228 cs AK) U226 U228 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_228_226 : pgv 228 + 65536 <= pgv 226 \/ pgv 226 + 8388608 <= pgv 228.
  Proof. exact (or_swap_a0 _ _ D_226_228). Qed.   (* [comment removed for export] *)
  Lemma D_208_228 : pgv 208 + 137439023104 <= pgv 228 \/ pgv 228 + 65536 <= pgv 208.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_208_228 cs AK) U208 U228 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_228_208 : pgv 228 + 65536 <= pgv 208 \/ pgv 208 + 137439023104 <= pgv 228.
  Proof. exact (or_swap_a0 _ _ D_208_228). Qed.   (* [comment removed for export] *)
  Lemma D_207_228 : pgv 207 + 3727360 <= pgv 228 \/ pgv 228 + 65536 <= pgv 207.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_207_228 cs AK) U207 U228 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_228_207 : pgv 228 + 65536 <= pgv 207 \/ pgv 207 + 3727360 <= pgv 228.
  Proof. exact (or_swap_a0 _ _ D_207_228). Qed.   (* [comment removed for export] *)
  Lemma D_78_228 : pgv 78 + 65536 <= pgv 228 \/ pgv 228 + 65536 <= pgv 78.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_78_228 cs AK) U78 U228 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_228_78 : pgv 228 + 65536 <= pgv 78 \/ pgv 78 + 65536 <= pgv 228.
  Proof. exact (or_swap_a0 _ _ D_78_228). Qed.   (* [comment removed for export] *)
  Lemma D_226_227 : pgv 226 + 8388608 <= pgv 227 \/ pgv 227 + 4096 <= pgv 226.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_226_227 cs AK) U226 U227 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_227_226 : pgv 227 + 4096 <= pgv 226 \/ pgv 226 + 8388608 <= pgv 227.
  Proof. exact (or_swap_a0 _ _ D_226_227). Qed.   (* [comment removed for export] *)
  Lemma D_208_227 : pgv 208 + 137439023104 <= pgv 227 \/ pgv 227 + 4096 <= pgv 208.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_208_227 cs AK) U208 U227 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_227_208 : pgv 227 + 4096 <= pgv 208 \/ pgv 208 + 137439023104 <= pgv 227.
  Proof. exact (or_swap_a0 _ _ D_208_227). Qed.   (* [comment removed for export] *)
  Lemma D_207_227 : pgv 207 + 3727360 <= pgv 227 \/ pgv 227 + 4096 <= pgv 207.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_207_227 cs AK) U207 U227 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_227_207 : pgv 227 + 4096 <= pgv 207 \/ pgv 207 + 3727360 <= pgv 227.
  Proof. exact (or_swap_a0 _ _ D_207_227). Qed.   (* [comment removed for export] *)
  Lemma D_78_227 : pgv 78 + 65536 <= pgv 227 \/ pgv 227 + 4096 <= pgv 78.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_78_227 cs AK) U78 U227 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_227_78 : pgv 227 + 4096 <= pgv 78 \/ pgv 78 + 65536 <= pgv 227.
  Proof. exact (or_swap_a0 _ _ D_78_227). Qed.   (* [comment removed for export] *)
  Lemma D_208_226 : pgv 208 + 137439023104 <= pgv 226 \/ pgv 226 + 8388608 <= pgv 208.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_208_226 cs AK) U208 U226 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_226_208 : pgv 226 + 8388608 <= pgv 208 \/ pgv 208 + 137439023104 <= pgv 226.
  Proof. exact (or_swap_a0 _ _ D_208_226). Qed.   (* [comment removed for export] *)
  Lemma D_207_226 : pgv 207 + 3727360 <= pgv 226 \/ pgv 226 + 8388608 <= pgv 207.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_207_226 cs AK) U207 U226 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_226_207 : pgv 226 + 8388608 <= pgv 207 \/ pgv 207 + 3727360 <= pgv 226.
  Proof. exact (or_swap_a0 _ _ D_207_226). Qed.   (* [comment removed for export] *)
  Lemma D_78_226 : pgv 78 + 65536 <= pgv 226 \/ pgv 226 + 8388608 <= pgv 78.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_78_226 cs AK) U78 U226 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_226_78 : pgv 226 + 8388608 <= pgv 78 \/ pgv 78 + 65536 <= pgv 226.
  Proof. exact (or_swap_a0 _ _ D_78_226). Qed.   (* [comment removed for export] *)
  Lemma D_207_208 : pgv 207 + 3727360 <= pgv 208 \/ pgv 208 + 137439023104 <= pgv 207.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_207_208 cs AK) U207 U208 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_208_207 : pgv 208 + 137439023104 <= pgv 207 \/ pgv 207 + 3727360 <= pgv 208.
  Proof. exact (or_swap_a0 _ _ D_207_208). Qed.   (* [comment removed for export] *)
  Lemma D_78_208 : pgv 78 + 65536 <= pgv 208 \/ pgv 208 + 137439023104 <= pgv 78.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_78_208 cs AK) U78 U208 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_208_78 : pgv 208 + 137439023104 <= pgv 78 \/ pgv 78 + 65536 <= pgv 208.
  Proof. exact (or_swap_a0 _ _ D_78_208). Qed.   (* [comment removed for export] *)
  Lemma D_78_207 : pgv 78 + 65536 <= pgv 207 \/ pgv 207 + 3727360 <= pgv 78.
  Proof. exact (disj_of_k _ _ _ _ _ _ (k_disj_78_207 cs AK) U78 U207 ltac:(lia) ltac:(lia)). Qed.
  Lemma D_207_78 : pgv 207 + 3727360 <= pgv 78 \/ pgv 78 + 65536 <= pgv 207.
  Proof. exact (or_swap_a0 _ _ D_78_207). Qed.   (* [comment removed for export] *)
  Ltac kdisj := first [ exact D_498_4115 | exact D_4115_498 | exact D_481_4115 | exact D_4115_481 | exact D_480_4115 | exact D_4115_480 | exact D_405_4115 | exact D_4115_405 | exact D_322_4115 | exact D_4115_322 | exact D_257_4115 | exact D_4115_257 | exact D_228_4115 | exact D_4115_228 | exact D_227_4115 | exact D_4115_227 | exact D_226_4115 | exact D_4115_226 | exact D_208_4115 | exact D_4115_208 | exact D_207_4115 | exact D_4115_207 | exact D_78_4115 | exact D_4115_78 | exact D_481_498 | exact D_498_481 | exact D_480_498 | exact D_498_480 | exact D_405_498 | exact D_498_405 | exact D_322_498 | exact D_498_322 | exact D_257_498 | exact D_498_257 | exact D_228_498 | exact D_498_228 | exact D_227_498 | exact D_498_227 | exact D_226_498 | exact D_498_226 | exact D_208_498 | exact D_498_208 | exact D_207_498 | exact D_498_207 | exact D_78_498 | exact D_498_78 | exact D_480_481 | exact D_481_480 | exact D_405_481 | exact D_481_405 | exact D_322_481 | exact D_481_322 | exact D_257_481 | exact D_481_257 | exact D_228_481 | exact D_481_228 | exact D_227_481 | exact D_481_227 | exact D_226_481 | exact D_481_226 | exact D_208_481 | exact D_481_208 | exact D_207_481 | exact D_481_207 | exact D_78_481 | exact D_481_78 | exact D_405_480 | exact D_480_405 | exact D_322_480 | exact D_480_322 | exact D_257_480 | exact D_480_257 | exact D_228_480 | exact D_480_228 | exact D_227_480 | exact D_480_227 | exact D_226_480 | exact D_480_226 | exact D_208_480 | exact D_480_208 | exact D_207_480 | exact D_480_207 | exact D_78_480 | exact D_480_78 | exact D_322_405 | exact D_405_322 | exact D_257_405 | exact D_405_257 | exact D_228_405 | exact D_405_228 | exact D_227_405 | exact D_405_227 | exact D_226_405 | exact D_405_226 | exact D_208_405 | exact D_405_208 | exact D_207_405 | exact D_405_207 | exact D_78_405 | exact D_405_78 | exact D_257_322 | exact D_322_257 | exact D_228_322 | exact D_322_228 | exact D_227_322 | exact D_322_227 | exact D_226_322 | exact D_322_226 | exact D_208_322 | exact D_322_208 | exact D_207_322 | exact D_322_207 | exact D_78_322 | exact D_322_78 | exact D_228_257 | exact D_257_228 | exact D_227_257 | exact D_257_227 | exact D_226_257 | exact D_257_226 | exact D_208_257 | exact D_257_208 | exact D_207_257 | exact D_257_207 | exact D_78_257 | exact D_257_78 | exact D_227_228 | exact D_228_227 | exact D_226_228 | exact D_228_226 | exact D_208_228 | exact D_228_208 | exact D_207_228 | exact D_228_207 | exact D_78_228 | exact D_228_78 | exact D_226_227 | exact D_227_226 | exact D_208_227 | exact D_227_208 | exact D_207_227 | exact D_227_207 | exact D_78_227 | exact D_227_78 | exact D_208_226 | exact D_226_208 | exact D_207_226 | exact D_226_207 | exact D_78_226 | exact D_226_78 | exact D_207_208 | exact D_208_207 | exact D_78_208 | exact D_208_78 | exact D_78_207 | exact D_207_78 ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition MAPSL : list (Z * Z) :=
    [ (pgv 4115, 4096); (pgv 498, 4096); (pgv 481, 8388608); (pgv 480, 1048576); (pgv 405, 11571200); (pgv 322, 4096); (pgv 257, 4096); (pgv 228, 65536); (pgv 227, 4096); (pgv 226, 8388608); (pgv 208, 137439023104); (pgv 207, 3727360); (pgv 78, 65536);
      (2201439137792, 15392894357504); (2415882240, 2199023255552); (2147446784, 268435456) ].
  Definition mden (m : amap) : Z * Z := (bv_unsigned (edenot E (am_base m)), bv_unsigned (edenot E (am_len m))).
  Lemma maps_denl : map mden (List.filter (fun m => negb (is_fog m)) A0_MAPS) = MAPSL.
  Proof.
    list_eq_lit; unfold mden; cbn [am_base am_len]; apply f_equal2; a0_den1.
  Qed.
  Lemma tracked_mapsl : forall m, In m A0_MAPS -> is_fog m = false -> In (mden m) MAPSL.
  Proof.
    intros m Hm Hf. rewrite <- maps_denl. apply in_map. apply filter_In. split; [exact Hm| rewrite Hf; reflexivity].
  Qed.
  Lemma mapsl_vmm : forall b s, In (b, s) MAPSL -> In (Z_to_bv 64 b, Z_to_bv 64 s) VMM.
  Proof.
    intros b s Hin. rewrite <- maps_denl in Hin. apply in_map_iff in Hin as [m [Em Hm]]. apply filter_In in Hm as [Hm Hf].
    unfold mden in Em. injection Em as <- <-. rewrite !Z_to_bv_bv_unsigned. apply in_maps_den; [exact Hm|]. destruct (is_fog m); [discriminate| reflexivity].
  Qed.
  (* [comment removed for export] *)
  Definition BML : list (Z * Z) :=
    [ (pgv 208, 137439023104); (pgv 226, 8388608); (2201439137792, 15392894357504); (2147446784, 268435456);
      (pgv 227, 4096); (pgv 228, 65536); (pgv 405, 11571200); (pgv 480, 1048576); (pgv 481, 8388608); (pgv 207, 3727360); (pgv 78, 65536);
      (pgv 4115, 4096); (pgv 498, 4096); (pgv 257, 4096); (pgv 322, 4096) ].
  Lemma bml_eq : AInv.big_maps_ P (SR [] 0) = BML.
  Proof.
    unfold AInv.big_maps_, BML. rewrite app_nil_r.
    cbn [p_b6 p_pa p_thr p_ctx p_fs p_nodes0 p_frames0 p_itab p_m64k p_gvec p_dvec p_m11 p_dtls P sr_chunks map app].
    unfold kSpaceReserve, kPtrArrayReserve, kHighShadowMapBeg, kHighShadowMapSize, kLowShadowMapBeg, kFakeStackBytes, kDepotNodesBlock, kStackStoreBlockBytes. reflexivity.
  Qed.
  Lemma bml_mapsl : forall q, In q BML -> In q MAPSL.
  Proof. all_in_lit; in_nth. Qed.
  Lemma mapsl_bml : forall q, In q MAPSL -> In q BML \/ q = (2415882240, 2199023255552).
  Proof. all_in_lit; first [right; reflexivity | left; in_nth]. Qed.
  Lemma bml_vmm : forall b sz, In (b, sz) BML -> In (Z_to_bv 64 b, Z_to_bv 64 sz) VMM.
  Proof. intros b sz Hin. apply mapsl_vmm. apply bml_mapsl. exact Hin. Qed.
  (* [comment removed for export] *)
  Lemma tracked_den : forall m, In m A0_MAPS -> is_fog m = false ->
    In (bv_unsigned (edenot E (am_base m)), bv_unsigned (edenot E (am_len m))) BML
    \/ (bv_unsigned (edenot E (am_base m)), bv_unsigned (edenot E (am_len m))) = (2415882240, 2199023255552).
  Proof. intros m Hm Hf. exact (mapsl_bml _ (tracked_mapsl m Hm Hf)). Qed.
  Lemma bml_bounds : forall b sz, In (b, sz) BML -> 0 <= b /\ 0 < sz /\ b + sz <= usp - 8388608 /\ b + sz <= 2^47.
  Proof.
    pose proof usp_range as [UR _].
    intros b sz Hq. in_cases2 Hq; hi_tac.
  Qed.

  (* [comment removed for export] *)
  Lemma region_free_apart_img : forall a n, 0 <= a -> 0 <= n -> a + n < 2^64 ->
    (a + n <= img_lo BOTH \/ img_hi BOTH <= a) ->
    region_free (segments_reserved BSEGS) (Z_to_bv 64 a) (Z_to_bv 64 n) = true.
  Proof.
    intros a n Ha Hn Han Hap. pose proof both_res_hull as RH. cbn [img_lo img_hi BOTH] in RH, Hap.
    induction (segments_reserved BSEGS) as [|[b sz] l IH]; [reflexivity|].
    inversion RH as [|x l' [H1 H2] H3]; subst. cbn [region_free]. rewrite (IH H3). rewrite Bool.andb_true_r.
    unfold iv_overlap. cbn [fst snd] in H1, H2. rewrite !u_lit64a. rewrite (Z.mod_small a), (Z.mod_small n) by lia.
    pose proof (u64_range sz).
    apply Bool.negb_true_iff. apply Bool.andb_false_iff. destruct Hap as [Hap|Hap]; [right; apply Z.ltb_ge; lia| left; apply Z.ltb_ge; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma A_cuts : Refund.cuts_covered model.
  Proof.
    intros x Hx. change (Ledger.zcovb (vm_maps (m_vmmaps model)) x) with (in_ivs x (vm_maps (m_vmmaps model))).
    unfold Ledger.cuts in Hx. rewrite Ledger.zcovb_app in Hx. apply Bool.orb_prop in Hx. destruct Hx as [Hx|Hx].
    - exact (co_nasub _ _ _ _ _ _ _ _ _ _ _ CS x Hx).
    - exact (co_lzsub _ _ _ _ _ _ _ _ _ _ _ CS x Hx).
  Qed.

  (* [comment removed for export] *)
  Lemma A_nashadow :
    region_free (vm_noaccess (m_vmmaps model)) (Z_to_bv 64 kLowShadowMapBeg) (Z_to_bv 64 (kShadowGapBeg - kLowShadowMapBeg)) = true /\
    region_free (vm_noaccess (m_vmmaps model)) (Z_to_bv 64 kHighShadowMapBeg) (Z_to_bv 64 kHighShadowMapSize) = true.
  Proof.
    unfold kLowShadowMapBeg, kShadowGapBeg, kHighShadowMapBeg, kHighShadowMapSize. split.
    - pose proof (cs_ok_lazy_region_free _ _ _ _ _ _ _ _ _ _ _ (AM (ELit 2147446784) (ELit 268435456) KRWLAZY) CS
                    ltac:(rewrite (s_maps cs gh ASS); in_nth) eq_refl) as X.
      cbn [am_base am_len edenot] in X. apply X.
      + rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
      + rewrite !Z_to_bv_unsigned. vm_compute. discriminate.
    - pose proof (cs_ok_lazy_region_free _ _ _ _ _ _ _ _ _ _ _ (AM (ELit 2201439137792) (ELit 15392894357504) KRWLAZY) CS
                    ltac:(rewrite (s_maps cs gh ASS); in_nth) eq_refl) as X.
      cbn [am_base am_len edenot] in X. apply X.
      + rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
      + rewrite !Z_to_bv_unsigned. vm_compute. discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma A_lzfree : AInv.alzfree_ AL_pboth P (fun _ => region_zero) model.
  Proof.
    unfold AInv.alzfree_. cbv zeta. cbn [al_image_lo al_image_hi AL_pboth p_sp0 p_stk_span P rg_mapped_user rg_mapped_fa region_zero].
    split; [| split].
    - exact (lazy_free_image _ _ fs cs E R FULL model CS).
    - apply (lazy_free_above_top _ _ fs cs E R FULL model CS). rewrite alloc_top_val. lia.
    - intros c Hc. split; apply Hull.lazy_free_empty; lia.
  Qed.
  Lemma A_ledger : AInv.aledger_ AL_pboth P (fun _ => region_zero) (SR [] 0) model.
  Proof.
    pose proof AP208 as B6. pose proof AP226 as BPA. pose proof R208. pose proof R226.
    unfold AInv.aledger_. cbv zeta. split; [| split; [| split; [| split; [| split; [| split; [apply Forall_nil| split; [exact A_cuts | split; [exact A_nashadow | exact A_lzfree]]]]]]]].
    - intros b sz Hin. rewrite bml_eq in Hin. exact (bml_vmm b sz Hin).
    - rewrite (co_res _ _ _ _ _ _ _ _ _ _ _ CS). cbn [p_b6 P]. unfold kSpaceReserve. pose proof usp_range as [UR _].
      apply region_free_apart_img; unfold pgv in *; change (2^37) with 137438953472; try lia.
    - rewrite (co_res _ _ _ _ _ _ _ _ _ _ _ CS). cbn [p_pa P]. unfold kPtrArrayReserve. pose proof usp_range as [UR _].
      apply region_free_apart_img; unfold pgv in *; lia.
    - rewrite (co_res _ _ _ _ _ _ _ _ _ _ _ CS). unfold kHighShadowMapBeg, kHighShadowMapSize. apply region_free_apart_img; cbn [img_lo img_hi BOTH]; lia.
    - cbn [p_tlim P]. rewrite (pre_limit sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS). reflexivity.   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  Ltac kdisj_tab a b := lazymatch constr:((a, b)) with (4115%nat, 498%nat) => exact D_4115_498 | (4115%nat, 481%nat) => exact D_4115_481 | (4115%nat, 480%nat) => exact D_4115_480 | (4115%nat, 405%nat) => exact D_4115_405 | (4115%nat, 322%nat) => exact D_4115_322 | (4115%nat, 257%nat) => exact D_4115_257 | (4115%nat, 228%nat) => exact D_4115_228 | (4115%nat, 227%nat) => exact D_4115_227 | (4115%nat, 226%nat) => exact D_4115_226 | (4115%nat, 208%nat) => exact D_4115_208 | (4115%nat, 207%nat) => exact D_4115_207 | (4115%nat, 78%nat) => exact D_4115_78 | (498%nat, 4115%nat) => exact D_498_4115 | (498%nat, 481%nat) => exact D_498_481 | (498%nat, 480%nat) => exact D_498_480 | (498%nat, 405%nat) => exact D_498_405 | (498%nat, 322%nat) => exact D_498_322 | (498%nat, 257%nat) => exact D_498_257 | (498%nat, 228%nat) => exact D_498_228 | (498%nat, 227%nat) => exact D_498_227 | (498%nat, 226%nat) => exact D_498_226 | (498%nat, 208%nat) => exact D_498_208 | (498%nat, 207%nat) => exact D_498_207 | (498%nat, 78%nat) => exact D_498_78 | (481%nat, 4115%nat) => exact D_481_4115 | (481%nat, 498%nat) => exact D_481_498 | (481%nat, 480%nat) => exact D_481_480 | (481%nat, 405%nat) => exact D_481_405 | (481%nat, 322%nat) => exact D_481_322 | (481%nat, 257%nat) => exact D_481_257 | (481%nat, 228%nat) => exact D_481_228 | (481%nat, 227%nat) => exact D_481_227 | (481%nat, 226%nat) => exact D_481_226 | (481%nat, 208%nat) => exact D_481_208 | (481%nat, 207%nat) => exact D_481_207 | (481%nat, 78%nat) => exact D_481_78 | (480%nat, 4115%nat) => exact D_480_4115 | (480%nat, 498%nat) => exact D_480_498 | (480%nat, 481%nat) => exact D_480_481 | (480%nat, 405%nat) => exact D_480_405 | (480%nat, 322%nat) => exact D_480_322 | (480%nat, 257%nat) => exact D_480_257 | (480%nat, 228%nat) => exact D_480_228 | (480%nat, 227%nat) => exact D_480_227 | (480%nat, 226%nat) => exact D_480_226 | (480%nat, 208%nat) => exact D_480_208 | (480%nat, 207%nat) => exact D_480_207 | (480%nat, 78%nat) => exact D_480_78 | (405%nat, 4115%nat) => exact D_405_4115 | (405%nat, 498%nat) => exact D_405_498 | (405%nat, 481%nat) => exact D_405_481 | (405%nat, 480%nat) => exact D_405_480 | (405%nat, 322%nat) => exact D_405_322 | (405%nat, 257%nat) => exact D_405_257 | (405%nat, 228%nat) => exact D_405_228 | (405%nat, 227%nat) => exact D_405_227 | (405%nat, 226%nat) => exact D_405_226 | (405%nat, 208%nat) => exact D_405_208 | (405%nat, 207%nat) => exact D_405_207 | (405%nat, 78%nat) => exact D_405_78 | (322%nat, 4115%nat) => exact D_322_4115 | (322%nat, 498%nat) => exact D_322_498 | (322%nat, 481%nat) => exact D_322_481 | (322%nat, 480%nat) => exact D_322_480 | (322%nat, 405%nat) => exact D_322_405 | (322%nat, 257%nat) => exact D_322_257 | (322%nat, 228%nat) => exact D_322_228 | (322%nat, 227%nat) => exact D_322_227 | (322%nat, 226%nat) => exact D_322_226 | (322%nat, 208%nat) => exact D_322_208 | (322%nat, 207%nat) => exact D_322_207 | (322%nat, 78%nat) => exact D_322_78 | (257%nat, 4115%nat) => exact D_257_4115 | (257%nat, 498%nat) => exact D_257_498 | (257%nat, 481%nat) => exact D_257_481 | (257%nat, 480%nat) => exact D_257_480 | (257%nat, 405%nat) => exact D_257_405 | (257%nat, 322%nat) => exact D_257_322 | (257%nat, 228%nat) => exact D_257_228 | (257%nat, 227%nat) => exact D_257_227 | (257%nat, 226%nat) => exact D_257_226 | (257%nat, 208%nat) => exact D_257_208 | (257%nat, 207%nat) => exact D_257_207 | (257%nat, 78%nat) => exact D_257_78 | (228%nat, 4115%nat) => exact D_228_4115 | (228%nat, 498%nat) => exact D_228_498 | (228%nat, 481%nat) => exact D_228_481 | (228%nat, 480%nat) => exact D_228_480 | (228%nat, 405%nat) => exact D_228_405 | (228%nat, 322%nat) => exact D_228_322 | (228%nat, 257%nat) => exact D_228_257 | (228%nat, 227%nat) => exact D_228_227 | (228%nat, 226%nat) => exact D_228_226 | (228%nat, 208%nat) => exact D_228_208 | (228%nat, 207%nat) => exact D_228_207 | (228%nat, 78%nat) => exact D_228_78 | (227%nat, 4115%nat) => exact D_227_4115 | (227%nat, 498%nat) => exact D_227_498 | (227%nat, 481%nat) => exact D_227_481 | (227%nat, 480%nat) => exact D_227_480 | (227%nat, 405%nat) => exact D_227_405 | (227%nat, 322%nat) => exact D_227_322 | (227%nat, 257%nat) => exact D_227_257 | (227%nat, 228%nat) => exact D_227_228 | (227%nat, 226%nat) => exact D_227_226 | (227%nat, 208%nat) => exact D_227_208 | (227%nat, 207%nat) => exact D_227_207 | (227%nat, 78%nat) => exact D_227_78 | (226%nat, 4115%nat) => exact D_226_4115 | (226%nat, 498%nat) => exact D_226_498 | (226%nat, 481%nat) => exact D_226_481 | (226%nat, 480%nat) => exact D_226_480 | (226%nat, 405%nat) => exact D_226_405 | (226%nat, 322%nat) => exact D_226_322 | (226%nat, 257%nat) => exact D_226_257 | (226%nat, 228%nat) => exact D_226_228 | (226%nat, 227%nat) => exact D_226_227 | (226%nat, 208%nat) => exact D_226_208 | (226%nat, 207%nat) => exact D_226_207 | (226%nat, 78%nat) => exact D_226_78 | (208%nat, 4115%nat) => exact D_208_4115 | (208%nat, 498%nat) => exact D_208_498 | (208%nat, 481%nat) => exact D_208_481 | (208%nat, 480%nat) => exact D_208_480 | (208%nat, 405%nat) => exact D_208_405 | (208%nat, 322%nat) => exact D_208_322 | (208%nat, 257%nat) => exact D_208_257 | (208%nat, 228%nat) => exact D_208_228 | (208%nat, 227%nat) => exact D_208_227 | (208%nat, 226%nat) => exact D_208_226 | (208%nat, 207%nat) => exact D_208_207 | (208%nat, 78%nat) => exact D_208_78 | (207%nat, 4115%nat) => exact D_207_4115 | (207%nat, 498%nat) => exact D_207_498 | (207%nat, 481%nat) => exact D_207_481 | (207%nat, 480%nat) => exact D_207_480 | (207%nat, 405%nat) => exact D_207_405 | (207%nat, 322%nat) => exact D_207_322 | (207%nat, 257%nat) => exact D_207_257 | (207%nat, 228%nat) => exact D_207_228 | (207%nat, 227%nat) => exact D_207_227 | (207%nat, 226%nat) => exact D_207_226 | (207%nat, 208%nat) => exact D_207_208 | (207%nat, 78%nat) => exact D_207_78 | (78%nat, 4115%nat) => exact D_78_4115 | (78%nat, 498%nat) => exact D_78_498 | (78%nat, 481%nat) => exact D_78_481 | (78%nat, 480%nat) => exact D_78_480 | (78%nat, 405%nat) => exact D_78_405 | (78%nat, 322%nat) => exact D_78_322 | (78%nat, 257%nat) => exact D_78_257 | (78%nat, 228%nat) => exact D_78_228 | (78%nat, 227%nat) => exact D_78_227 | (78%nat, 226%nat) => exact D_78_226 | (78%nat, 208%nat) => exact D_78_208 | (78%nat, 207%nat) => exact D_78_207 end.
  Ltac band_tab a H := lazymatch a with 4115%nat => pose proof LH4115 as H | 498%nat => pose proof LH498 as H | 481%nat => pose proof LH481 as H | 480%nat => pose proof LH480 as H | 405%nat => pose proof LH405 as H | 322%nat => pose proof LH322 as H | 257%nat => pose proof LH257 as H | 228%nat => pose proof LH228 as H | 227%nat => pose proof LH227 as H | 226%nat => pose proof LH226 as H | 208%nat => pose proof LH208 as H | 207%nat => pose proof LH207 as H | 78%nat => pose proof LH78 as H end.
  Ltac bm_pair :=
    cbn [fst snd]; lazymatch goal with
    | |- pgv ?a + _ <= pgv ?b \/ _ => kdisj_tab a b
    | |- pgv ?a + _ <= _ \/ _ => let H := fresh in band_tab a H; unfold LOWSHZ, KHIZ in H; clear - H; lia
    | |- _ + _ <= pgv ?a \/ _ => let H := fresh in band_tab a H; unfold LOWSHZ, KHIZ in H; clear - H; lia
    | |- _ => lia
    end.
  Fixpoint pairwise_disj (l : list (Z * Z)) : Prop :=
    match l with [] => True | q :: r => Forall (fun q' => fst q + snd q <= fst q' \/ fst q' + snd q' <= fst q) r /\ pairwise_disj r end.
  Lemma pairwise_disj_nth : forall l, pairwise_disj l -> forall i j bi si bj sj,
    nth_error l i = Some (bi, si) -> nth_error l j = Some (bj, sj) -> i <> j -> bi + si <= bj \/ bj + sj <= bi.
  Proof.
    induction l as [|[b s] l IH]; intros PD i j bi si bj sj Hi Hj NE; [destruct i; discriminate|].
    destruct PD as [F PD]. destruct i as [|i], j as [|j]; cbn in Hi, Hj.
    - congruence.
    - injection Hi as <- <-. pose proof (proj1 (Forall_forall _ _) F _ (nth_error_In _ _ Hj)) as X. cbn in X. exact X.
    - injection Hj as <- <-. pose proof (proj1 (Forall_forall _ _) F _ (nth_error_In _ _ Hi)) as X. cbn in X. lia.
    - eapply IH; [exact PD| exact Hi| exact Hj| congruence].
  Qed.
  Lemma pairwise_disj_gen : forall l (G : Prop), (pairwise_disj l -> G) ->
    AllPairsT (fun q q' : Z * Z => fst q + snd q <= fst q' \/ fst q' + snd q' <= fst q) l G.
  Proof.
    induction l as [|x l IH]; intros G H; cbn [AllPairsT].
    - exact (H Logic.I).
    - apply allT_gen. intros HF. apply IH. intros PD. apply H. split; [apply Forall_forall; exact HF| exact PD].
  Qed.
  Lemma pairwise_disj_intro : forall l,
    AllPairsT (fun q q' : Z * Z => fst q + snd q <= fst q' \/ fst q' + snd q' <= fst q) l (pairwise_disj l).
  Proof. intros l. apply pairwise_disj_gen. exact (fun H => H). Qed.
  Lemma bml_disj : pairwise_disj BML.
  Proof.
    let n := eval lazy in (let k := length BML in Nat.div (k * (k - 1)) 2) in
    refine_n uconstr:(pairwise_disj_intro BML) n;
    lazymatch goal with |- ?G0 =>
      let g := eval cbv beta in G0 in let g := eval cbn [fst snd] in g in
      lazymatch g with
      | pgv ?a + _ <= pgv ?b \/ _ => kdisj_tab a b      (* [comment removed for export] *)
      | _ => change g; bm_pair
      end
    end.
  Qed.
  Lemma A_bigmaps : AInv.wf_bigmaps_ P (SR [] 0).
  Proof.
    unfold AInv.wf_bigmaps_. rewrite bml_eq. split.
    - exact (pairwise_disj_nth BML bml_disj).
    - intros b sz Hin. pose proof (bml_bounds _ _ Hin). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma A_reserved : vm_reserved (m_vmmaps model) = segments_reserved BSEGS.
  Proof. exact (pre_res sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS). Qed.
  Lemma A_gap : In (Z_to_bv 64 kShadowGapBeg, Z_to_bv 64 (kHighShadowMapBeg - kShadowGapBeg)) (vm_maps (m_vmmaps model)).
  Proof. unfold kShadowGapBeg, kHighShadowMapBeg. apply (mapsl_vmm 2415882240). in_nth. Qed.


  (* [comment removed for export] *)
  Lemma vg_ok : forall p, In p (a_vis cs ++ a_ghost cs) ->
    4096 <= uE E (fst p) /\ uE E (fst p) mod 4096 = 0 /\ 0 < uE E (snd p) /\ uE E (snd p) mod 4096 = 0 /\ uE E (fst p) + uE E (snd p) <= 2^47
    /\ (uE E (fst p) + uE E (snd p) <= LOWSHZ \/ KHIZ <= uE E (fst p)).
  Proof.
    intros p Hp. apply in_app_or in Hp. destruct Hp as [Hp|Hp].
    - pose proof (vis_ok p Hp) as V. unfold vok, den in V. cbn [fst snd] in V. exact V.
    - pose proof (ghost_ok p Hp) as V. unfold gok, den in V. cbn [fst snd] in V. (first [ dand5 V as A B C D F | destruct V as (A & B & C & D & F) ]).
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia. destruct C as [-> | ->]; reflexivity.
  Qed.
  Lemma pagedown_le : forall z, pagedown z <= z /\ z - 4096 < pagedown z.
  Proof. intros z. unfold pagedown. Z.div_mod_to_equations. lia. Qed.
  Lemma pageup_ge : forall z, z <= pageup z /\ pageup z < z + 4096.
  Proof. intros z. unfold pageup. Z.div_mod_to_equations. lia. Qed.
  Lemma pagedown_id : forall z, z mod 4096 = 0 -> pagedown z = z.
  Proof. intros z Hz. unfold pagedown. Z.div_mod_to_equations. lia. Qed.
  Lemma pageup_id : forall z, z mod 4096 = 0 -> pageup z = z.
  Proof. intros z Hz. unfold pageup. Z.div_mod_to_equations. lia. Qed.
  Lemma pagedown_mod : forall z, pagedown z mod 4096 = 0.
  Proof. intros z. unfold pagedown. apply Z_mod_mult. Qed.
  Lemma pageup_mod : forall z, pageup z mod 4096 = 0.
  Proof. intros z. unfold pageup. apply Z_mod_mult. Qed.
  Lemma pagedown_ge : forall z c, c mod 4096 = 0 -> c <= z -> c <= pagedown z.
  Proof. intros z c Hc Hz. unfold pagedown. Z.div_mod_to_equations. nia. Qed.
  Lemma pageup_le : forall z c, c mod 4096 = 0 -> z <= c -> pageup z <= c.
  Proof. intros z c Hc Hz. unfold pageup. Z.div_mod_to_equations. nia. Qed.
  Lemma shr_facts : forall p, In p (a_vis cs ++ a_ghost cs) ->
    2147450880 <= fst (shr p) /\ fst (shr p) <= snd (shr p) <= KHIZ /\ fst (shr p) mod 4096 = 0 /\ snd (shr p) mod 4096 = 0
    /\ snd (shr p) <= fst (shr p) + (uE E (snd p) / 8 + 8192)
    /\ (forall a, uE E (fst p) <= a < uE E (fst p) + uE E (snd p) -> fst (shr p) <= sh a - sh a mod 8 /\ sh a - sh a mod 8 + 8 <= snd (shr p)).
  Proof.
    intros p Hp. (first [ pose proof ((vg_ok p Hp)) as dR_6; dand6 dR_6 as F1 F2 F3 F4 F5 F6 | pose proof (vg_ok p Hp) as (F1 & F2 & F3 & F4 & F5 & F6) ]). unfold shr, sh_lo, sh_hi, KHIZ. cbn [shadow_off BOTH fst snd].
    clear - F1 F2 F3 F4 F5 F6. unfold LOWSHZ, KHIZ in F6.
    pose proof (pagedown_le (2147450880 + uE E (fst p) / 8)) as [D1 D2]. pose proof (pageup_ge (2147450880 + (uE E (fst p) + uE E (snd p)) / 8)) as [G1 G2].
    assert (M1 : (2147450880 + uE E (fst p) / 8) mod 8 = 0) by (clear - F2; Z.div_mod_to_equations; lia).
    assert (M2 : (2147450880 + (uE E (fst p) + uE E (snd p)) / 8) mod 8 = 0) by (clear - F2 F4; Z.div_mod_to_equations; lia).
    assert (S8 : (uE E (fst p) + uE E (snd p)) / 8 = uE E (fst p) / 8 + uE E (snd p) / 8) by (clear - F2 F4; Z.div_mod_to_equations; lia).
    assert (B0 : 512 <= uE E (fst p) / 8) by (clear - F1; Z.div_mod_to_equations; lia).
    assert (N0 : 0 <= uE E (snd p) / 8) by (clear - F3; Z.div_mod_to_equations; lia).
    assert (T8 : (uE E (fst p) + uE E (snd p)) / 8 <= 17592186044416) by (clear - F5; Z.div_mod_to_equations; lia).
    split; [apply pagedown_ge; [reflexivity| lia]|].
    split; [split; [lia| apply pageup_le; [reflexivity| lia]]|].
    split; [apply pagedown_mod|]. split; [apply pageup_mod|]. split; [lia|].
    intros a Ha. unfold sh, kShadowOffset.
    assert (L1 : uE E (fst p) / 8 <= a / 8) by (apply Z.div_le_mono; lia).
    assert (L2 : a / 8 < (uE E (fst p) + uE E (snd p)) / 8) by (clear - Ha F2 F4; Z.div_mod_to_equations; lia).
    remember (uE E (fst p) / 8) as B8 eqn:HB. remember ((uE E (fst p) + uE E (snd p)) / 8) as N8 eqn:HN. remember (a / 8) as A8 eqn:HA8.
    clear - D1 G1 M1 M2 L1 L2. Z.div_mod_to_equations. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma in_EXTRA : forall lo hi, In (lo, hi) EXTRA ->
    (covb VMM (lo, hi) = true /\ ((exists p, In p (a_vis cs) /\ (lo, hi) = appr p)
                                 \/ (exists g, In g (a_ghost cs) /\ In (lo, hi) (pages_of (appr g)))))
    \/ (exists p, In p (a_vis cs ++ a_ghost cs) /\ (lo, hi) = shr p).
  Proof.
    intros lo hi Hin. unfold EXTRA in Hin. rewrite !in_app_iff, !filter_In, in_map_iff, in_flat_map, in_map_iff in Hin.
    destruct Hin as [[[p [Ep Hp]] C] | [[[g [Hg Hpg]] C] | [p [Ep Hp]]]].
    - left. split; [exact C|]. left. exists p. split; [exact Hp| symmetry; exact Ep].
    - left. split; [exact C|]. right. exists g. split; [exact Hg| exact Hpg].
    - right. exists p. split; [exact Hp| symmetry; exact Ep].
  Qed.
  (* [comment removed for export] *)
  Lemma cov_where : forall lo hi, covb VMM (lo, hi) = true ->
    exists e, In e VMM /\ bv_unsigned (fst e) <= lo /\ hi <= bv_unsigned (fst e) + bv_unsigned (snd e)
              /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= usp - 8388608 /\ 0 <= bv_unsigned (fst e).
  Proof.
    intros lo hi C. apply (proj1 (covb_true _ _)) in C as [e (He & H1 & H2)]. cbn [fst snd] in H1, H2.
    exists e. (first [ pose proof ((proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ CS) e He)) as dR_7; dand5 dR_7 as _ _ _ _ B5 | pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ CS) e He) as (_ & _ & _ & _ & B5) ]). cbn beta in B5.
    rewrite alloc_top_val in B5. pose proof (u64_range (fst e)). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; lia.
  Qed.

  Lemma A_vmmaps : exists fog : list (Z * Z),
      Z.of_nat (length fog) <= 2 /\ Forall (fun bs => 0 <= fst bs /\ 0 < snd bs <= 8192 /\ fst bs + snd bs <= 2^47) fog /\
      (forall e, In e (vm_maps (m_vmmaps model)) ->
          let bs := (bv_unsigned (fst e), bv_unsigned (snd e)) in
          In bs (AInv.big_maps_ P (SR [] 0)) \/ In bs fog \/ bs = (kShadowGapBeg, kHighShadowMapBeg - kShadowGapBeg)) /\
      (forall bs, In bs fog -> In (Z_to_bv 64 (fst bs), Z_to_bv 64 (snd bs)) (vm_maps (m_vmmaps model))) /\
      (forall lo hi a, In (lo, hi) (p_extra P) -> lo <= a < hi -> 0 <= a < Ceiling.alloc_ceiling ->
          ~ (kLowShadowMapBeg <= a < kHighMemBeg) ->
          (cl_image_lo LayoutPA.LPA <= a < cl_image_hi LayoutPA.LPA) \/ in_regions (AInv.big_maps_ P (SR [] 0)) a \/ in_regions fog a).
  Proof.
    (first [ pose proof ((pre_vmmaps sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS)) as dR_8; dex1 dR_8 as fogW; dand4 dR_8 as L1 L2 L3 L4 | pose proof ((pre_vmmaps sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS)) as dR_8; dand5 dR_8 as fogW L1 L2 L3 L4 | destruct (pre_vmmaps sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS) as (fogW & L1 & L2 & L3 & L4) ]).
    rewrite (s_maps cs gh ASS) in L1, L3, L4. change (nfog A0_MAPS) with 2%nat in L1.
    pose proof usp_range as [UR _].
    set (fog := map (fun e : word * word => (bv_unsigned (fst e), bv_unsigned (snd e))) fogW).
    assert (FOGIN : forall e, In e fogW -> In (bv_unsigned (fst e), bv_unsigned (snd e)) fog).
    { intros e He. unfold fog. apply (in_map (fun e : word * word => (bv_unsigned (fst e), bv_unsigned (snd e))) _ _ He). }
    (* [comment removed for export] *)
    assert (ENT : forall e a, In e VMM -> bv_unsigned (fst e) <= a < bv_unsigned (fst e) + bv_unsigned (snd e) ->
                   ~ (kLowShadowMapBeg <= a < kHighMemBeg) -> in_regions BML a \/ in_regions fog a).
    { intros e a He Ha NB. destruct (L4 e He) as [(m & Hm & Hf & ->)|HF].
      - destruct (tracked_den m Hm Hf) as [HB|HG].
        + left. eexists _, _. split; [exact HB|]. unfold amap_den in Ha. cbn [fst snd] in Ha. exact Ha.
        + exfalso. unfold amap_den in Ha. cbn [fst snd] in Ha. injection HG as E1 E2. rewrite E1, E2 in Ha.
          unfold kLowShadowMapBeg, kHighMemBeg in NB. lia.
      - right. eexists _, _. split; [exact (FOGIN e HF)|]. exact Ha. }
    exists fog. split; [| split; [| split; [| split]]].
    - unfold fog. rewrite map_length. lia.
    - apply Forall_forall. intros bs Hbs. unfold fog in Hbs. apply in_map_iff in Hbs as [e [<- He]]. cbn [fst snd].
      (first [ pose proof ((proj1 (Forall_forall _ _) L3 e He)) as dR_9; dex1 dR_9 as m; dand3 dR_9 as Hm Hf Hsz | pose proof ((proj1 (Forall_forall _ _) L3 e He)) as dR_9; dand4 dR_9 as m Hm Hf Hsz | destruct (proj1 (Forall_forall _ _) L3 e He) as (m & Hm & Hf & Hsz) ]).
      (first [ pose proof ((proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ CS) e (L2 e He))) as dR_10; dand5 dR_10 as B1 _ _ _ B5 | pose proof (proj1 (Forall_forall _ _) (co_bounds _ _ _ _ _ _ _ _ _ _ _ CS) e (L2 e He)) as (B1 & _ & _ & _ & B5) ]). cbn beta in B1, B5.
      rewrite alloc_top_val in B5. pose proof (u64_range (fst e)).
      assert (SZ : uE E (am_len m) = 8192).
      { in_cases1 Hm; first [discriminate Hf | apply ulit; lia]. }
      rewrite SZ in Hsz. lia.
    - intros e He. cbv zeta. rewrite bml_eq. destruct (L4 e He) as [(m & Hm & Hf & ->)|HF].
      + unfold amap_den. cbn [fst snd]. destruct (tracked_den m Hm Hf) as [HB|HG]; [left; exact HB| right; right].
        unfold kShadowGapBeg, kHighShadowMapBeg. exact HG.
      + right. left. exact (FOGIN e HF).
    - intros bs Hbs. unfold fog in Hbs. apply in_map_iff in Hbs as [e [<- He]]. cbn [fst snd]. rewrite !Z_to_bv_bv_unsigned.
      rewrite <- surjective_pairing. exact (L2 e He).
    - intros lo hi a Hin Ha _ NB. cbn [p_extra P] in Hin. rewrite bml_eq.
      destruct (in_EXTRA lo hi Hin) as [[C _] | [p [Hp EQ]]].
      + right. (first [ pose proof ((cov_where lo hi C)) as dR_11; dex1 dR_11 as e; dand5 dR_11 as He E1 E2 _ _ | pose proof ((cov_where lo hi C)) as dR_11; dand6 dR_11 as e He E1 E2 _ _ | destruct (cov_where lo hi C) as (e & He & E1 & E2 & _ & _) ]). apply (ENT e a He); [lia| exact NB].
      + exfalso. (first [ pose proof ((shr_facts p Hp)) as dR_12; dand3 dR_12 as S1 S2 _ | pose proof (shr_facts p Hp) as (S1 & S2 & _) ]). rewrite <- EQ in S1, S2. cbn [fst snd] in S1, S2.
        unfold kLowShadowMapBeg, kHighMemBeg, KHIZ in *. lia.
  Qed.

  Lemma u64_zero_at : forall a, (forall i, 0 <= i < 8 -> FULL (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0)) -> 0 <= a -> a + 8 <= 2^64 -> ACells.u64_at BSEGS FULL a 0.
  Proof.
    intros a H Ha Hhi. unfold ACells.u64_at. change (Lib.Mem.le8 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) (Z.to_nat 8)).
    apply (fill_bytes FULL a 8 0); [lia|lia|lia| exact H].
  Qed.
  Lemma A_locks : AInv.locks_repr_ LayoutPA.LPA AL_pboth P [] FULL.
  Proof.
    pose proof R208. pose proof R209. unfold AInv.locks_repr_. rewrite !AInv.lockb_nil. split.
    - intros c Hc. unfold kRegionInfoSize. pose proof A_ri_zero as RZ. unfold zero_at in RZ.
      assert (RI : 0 <= p_ri P /\ p_ri P + 4096 <= 2^64) by (rewrite ri_val, Uri; unfold pgv; lia).
      split; apply u64_zero_at; try lia; intros i Hi.
      + replace (p_ri P + 128 * c + 0 + i) with (p_ri P + (128 * c + i)) by lia. apply RZ. lia.
      + replace (p_ri P + 128 * c + 8 + i) with (p_ri P + (128 * c + 8 + i)) by lia. apply RZ. lia.
    - split; [cell 22%nat|]. split; [cell 23%nat|]. split; [cell 24%nat|]. split; [cell 25%nat| cell 26%nat].
  Qed.

  Lemma A_consts : AInv.consts_repr_ LayoutPA.LPA AL_pboth P FULL.
  Proof.
    pose proof R208. pose proof R209. pose proof R226. pose proof R227. pose proof R228. pose proof R405. pose proof R322. pose proof R0. pose proof R356.
    unfold AInv.consts_repr_. cbn [p_b6 p_pa p_thr p_ctx p_fs p_dtls p_stk_top p_stk_bot p_tlsb p_tlse P].
    split. { exact (cells_bytes sp rdraw brk0 argv envp uid hw fs Hsp Hva cs E R FULL model CS _ CCL). }
    split. { apply (u64_img _ (pg 208) _ (k_inst_b6 cs AK) U208); cbn; lia. }
    split. { cell 0%nat. }
    split. { apply (u64_img _ _ _ (k_inst_sb cs AK)); [| cbn; lia| cbn; lia].
             cbn [edenot]. rewrite u_add64.
             change (alu64 Instr.ALU_ADD (mul_div Instr.M_MUL (Z_to_bv 64 4096) (ev E 208)) (mul_div Instr.M_MUL (Z_to_bv 64 (-4096)) (ev E 209))) with (edenot E e_ri).
             rewrite Uri, u_lit64a, sb_val. change (65536 mod 2^64) with 65536. apply Z.mod_small. unfold pgv. change (2^64) with 18446744073709551616. lia. }
    split. { cell 1%nat. }
    split. { apply (u64_img _ _ _ (k_inst_ri cs AK)); [| cbn; lia| cbn; lia]. rewrite riZ_val, <- Uri_page. unfold uE. reflexivity. }
    split. { cell 2%nat. }
    split. { cell 3%nat. }
    split. { apply (u64_img _ (pg 226) _ (k_inst_pa1 cs AK) U226); cbn; lia. }
    split. { apply (u64_img _ (pg 226) _ (k_inst_pa2 cs AK) U226); cbn; lia. }
    split. { cell 4%nat. } split. { cell 5%nat. } split. { cell 6%nat. } split. { cell 7%nat. } split. { cell 8%nat. }
    split. { cell 9%nat. } split. { cell 10%nat. } split. { cell 11%nat. }
    split. { cell 12%nat. } split. { cell 13%nat. } split. { cell 14%nat. }
    split. { intros i Hi. cbn [al_kHighMemEnd_var AL_pboth]. unfold LayoutPA.LPA. cbn [cl_shared]. unfold LayoutPA.pa_shared. lia. }
    split. { reflexivity. } split. { reflexivity. }
    split. { cell 15%nat. } split. { cell 16%nat. } split. { cell 17%nat. } split. { cell 18%nat. } split. { cell 19%nat. }
    split. { cell 20%nat. } split. { cell 21%nat. }
    unfold Asanqj4.off_th_context, Asanqj4.off_th_stack_top, Asanqj4.off_th_stack_bottom, Asanqj4.off_th_stack_switching, Asanqj4.off_th_unwinding.
    split. { apply (u64_sym (pg 227) (pgv 227) 0 (pg 228) _ U227 (k_thr_0 cs AK) U228); hi_tac. }
    split. { apply (u64_sym (pg 227) (pgv 227) 8 _ _ U227 (k_thr_8 cs AK)); [symmetry; exact Ustk| hi_tac| hi_tac| hi_tac]. }
    split. { apply (u64_sym (pg 227) (pgv 227) 16 _ _ U227 (k_thr_16 cs AK)); [symmetry; exact Ustkb| hi_tac| hi_tac| hi_tac]. }
    split. { apply (u8_symL (pg 227) (pgv 227) 40 0 U227 (k_thr_40 cs AK)); hi_tac. }
    split. { apply (u8_symL (pg 227) (pgv 227) 3168 0 U227 (k_thr_3168 cs AK)); hi_tac. }
    split. { unfold kMainTid. apply (u32_symL (pg 228) (pgv 228) 8 0 U228 (k_ctx_8 cs AK)); hi_tac. }
    split. { apply (u64_sym (pg 228) (pgv 228) 152 (pg 227) _ U228 (k_ctx_152 cs AK) U227); hi_tac. }
    split. { exists 6328192. split; [| split].
             - cell 34%nat.
             - intros i Hi. unfold LayoutPA.LPA. cbn [cl_shared]. unfold LayoutPA.pa_shared. lia.
             - apply (u64_img _ (pg 228) _ (k_tsd_ctx cs AK) U228); cbn; lia. }
    split. { cbn [cl_tp LayoutPA.LPA]. rewrite u_lit64a. change (6192088 mod 2^64) with 6192088. apply (u64_img _ (pg 405) _ (k_tp_fs cs AK) U405); cbn; lia. }
    split. { cbn [cl_tp LayoutPA.LPA]. rewrite u_lit64a. change (6192088 mod 2^64 + 8) with 6192096. apply (u64_img _ (pg 322) _ (k_tp_dtls cs AK) U322); cbn; lia. }
    split. { cbn [cl_tp LayoutPA.LPA]. rewrite u_lit64a. change (6192088 mod 2^64) with 6192088. apply (u64_symL (pg 322) (pgv 322) 24 _ U322 (k_dtls_24 cs AK)); hi_tac. }
    split. { apply (u64_symL (pg 227) (pgv 227) 48 _ U227 (k_thr_48 cs AK)); hi_tac. }
    apply (u64_symL (pg 227) (pgv 227) 56 _ U227 (k_thr_56 cs AK)); hi_tac.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac pl_tac :=
    a0_natz_hook;
    lazymatch goal with |- context [pgv ?v0] => let v := eval cbv in v0 in
      let X := fresh in let Y := fresh in let W := fresh in
      first [ (constr_eq v 4115%nat; pose proof AP4115z as X; pose proof LH4115z as Y; pose proof R4115z as W) | (constr_eq v 498%nat; pose proof AP498z as X; pose proof LH498z as Y; pose proof R498z as W) | (constr_eq v 481%nat; pose proof AP481z as X; pose proof LH481z as Y; pose proof R481z as W) | (constr_eq v 480%nat; pose proof AP480z as X; pose proof LH480z as Y; pose proof R480z as W) | (constr_eq v 405%nat; pose proof AP405z as X; pose proof LH405z as Y; pose proof R405z as W) | (constr_eq v 322%nat; pose proof AP322z as X; pose proof LH322z as Y; pose proof R322z as W) | (constr_eq v 257%nat; pose proof AP257z as X; pose proof LH257z as Y; pose proof R257z as W) | (constr_eq v 228%nat; pose proof AP228z as X; pose proof LH228z as Y; pose proof R228z as W) | (constr_eq v 227%nat; pose proof AP227z as X; pose proof LH227z as Y; pose proof R227z as W) | (constr_eq v 226%nat; pose proof AP226z as X; pose proof LH226z as Y; pose proof R226z as W) | (constr_eq v 208%nat; pose proof AP208z as X; pose proof LH208z as Y; pose proof R208z as W) | (constr_eq v 207%nat; pose proof AP207z as X; pose proof LH207z as Y; pose proof R207z as W) | (constr_eq v 78%nat; pose proof AP78 as X; pose proof LH78 as Y; pose proof R78 as W) ];
      try (change v with v0 in X); try (change v with v0 in Y); try (change v with v0 in W);
      unfold app_rangeA, LOWSHZ, KHIZ, kLowShadowMapBeg, kHighMemBeg in *;
      cbn [al_image_lo al_image_hi AL_pboth img_lo img_hi BOTH] in *; rewrite ?pgv_mod; unfold pgv in *; lia end.
  Lemma A_place : AInv.wf_place AL_pboth P.
  Proof.
    pose proof usp_range as [US UM]. pose proof (entry_stack_span_bound argv envp Hva Hve) as SPAN. unfold entry_stack_span_max in SPAN.
    pose proof sb_val as SB. pose proof Hfit as FIT. unfold entry_stack_fits in FIT. pose proof R0. pose proof R356. pose proof R209.
    unfold AInv.wf_place. cbv zeta.
    cbn [p_b6 p_pa p_thr p_ctx p_nodes0 p_frames0 p_fs p_itab p_m64k p_gvec p_dvec p_m11 p_dtls p_tlsb p_tlse p_sp0 p_stk_span p_stk_top p_stk_bot p_eager0 p_dkeys P] in SB.
    unfold sp_window_lo, sp_window_hi, stack_max_size in *.
    a0_natz_ap.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
      cbn [p_b6 p_pa p_thr p_ctx p_nodes0 p_frames0 p_fs p_itab p_m64k p_gvec p_dvec p_m11 p_dtls p_tlsb p_tlse p_sp0 p_stk_span p_stk_top p_stk_bot p_eager0 p_dkeys P];
      try rewrite SB; try rewrite HCEIL; unfold kSpaceSize, kPtrArrayReserve, kDepotNodesBlock, kStackStoreBlockBytes, kFakeStackBytes, stk_top;
      unfold sp_window_lo, sp_window_hi, stack_max_size;
      first [ exact LayoutPA.pa_dkeys_short | exact LayoutPA.pa_dkeys_hashes | exact LayoutPA.pa_dkeys_len | reflexivity
            | symmetry; exact sb_val | pl_tac | lia | idtac ].
    all: fail "A_place: open goal".
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pages_facts : forall g lo hi, In g (a_vis cs ++ a_ghost cs) -> In (lo, hi) (pages_of (appr g)) ->
    lo mod 4096 = 0 /\ hi = lo + 4096 /\ uE E (fst g) <= lo /\ hi <= uE E (fst g) + uE E (snd g).
  Proof.
    intros g lo hi Hg Hin. (first [ pose proof ((vg_ok g Hg)) as dR_13; dand6 dR_13 as F1 F2 F3 F4 F5 F6 | pose proof (vg_ok g Hg) as (F1 & F2 & F3 & F4 & F5 & F6) ]). unfold appr in Hin. cbn [fst snd] in Hin.
    apply (proj1 (in_pages_of _ _ _ _)) in Hin as [i (Hi & -> & ->)].
    replace (uE E (fst g) + uE E (snd g) - uE E (fst g)) with (uE E (snd g)) in Hi by lia.
    split; [rewrite Z.add_mod, F2, (Z.mul_comm 4096), Z_mod_mult by lia; reflexivity|]. split; [reflexivity|].
    Z.div_mod_to_equations. nia.
  Qed.
  Lemma extra_facts : forall lo hi, In (lo, hi) EXTRA ->
    0 <= lo /\ lo <= hi <= 2^47 /\ lo mod 4096 = 0 /\ hi mod 4096 = 0.
  Proof.
    pose proof usp_range as [UR _].
    intros lo hi Hin. destruct (in_EXTRA lo hi Hin) as [[C K] | [p [Hp EQ]]].
    - destruct K as [[p [Hp EQ]] | [g [Hg Hpg]]].
      + (first [ pose proof ((vg_ok p ltac:(apply in_or_app; left; exact Hp))) as dR_14; dand6 dR_14 as F1 F2 F3 F4 F5 F6 | pose proof (vg_ok p ltac:(apply in_or_app; left; exact Hp)) as (F1 & F2 & F3 & F4 & F5 & F6) ]).
        unfold appr in EQ. cbn [fst snd] in EQ. injection EQ as -> ->. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia. rewrite Z.add_mod, F2, F4 by lia. reflexivity.
      + (first [ pose proof ((vg_ok g ltac:(apply in_or_app; right; exact Hg))) as dR_15; dand6 dR_15 as F1 F2 F3 F4 F5 F6 | pose proof (vg_ok g ltac:(apply in_or_app; right; exact Hg)) as (F1 & F2 & F3 & F4 & F5 & F6) ]).
        (first [ pose proof ((pages_facts g lo hi ltac:(apply in_or_app; right; exact Hg) Hpg)) as dR_16; dand4 dR_16 as P1 -> P3 P4 | pose proof (pages_facts g lo hi ltac:(apply in_or_app; right; exact Hg) Hpg) as (P1 & -> & P3 & P4) ]).
        OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia. rewrite Z.add_mod, P1 by lia. reflexivity.
    - (first [ pose proof ((shr_facts p Hp)) as dR_17; dand5 dR_17 as S1 S2 S3 S4 _ | pose proof (shr_facts p Hp) as (S1 & S2 & S3 & S4 & _) ]). rewrite <- EQ in S1, S2, S3, S4. cbn [fst snd] in S1, S2, S3, S4. unfold KHIZ in S2. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma extra_closure : forall lo hi a, In (lo, hi) EXTRA -> lo <= a < hi ->
    (0 <= a <= kLowMemEnd \/ kHighMemBeg <= a < Ceiling.alloc_ceiling) ->
    forall z, sh a - sh a mod 8 <= z < sh a - sh a mod 8 + 8 -> exists lo' hi', In (lo', hi') EXTRA /\ lo' <= z < hi'.
  Proof.
    intros lo hi a Hin Ha APP z Hz.
    assert (SH : forall p, In p (a_vis cs ++ a_ghost cs) -> uE E (fst p) <= a < uE E (fst p) + uE E (snd p) ->
                 exists lo' hi', In (lo', hi') EXTRA /\ lo' <= z < hi').
    { intros p Hp Hap. (first [ pose proof ((shr_facts p Hp)) as dR_18; dand6 dR_18 as _ _ _ _ _ W | pose proof (shr_facts p Hp) as (_ & _ & _ & _ & _ & W) ]). destruct (W a Hap) as [W1 W2].
      exists (fst (shr p)), (snd (shr p)). split; [| lia]. unfold EXTRA. rewrite !in_app_iff. right. right.
      rewrite <- surjective_pairing. apply in_map. exact Hp. }
    destruct (in_EXTRA lo hi Hin) as [[C K] | [p [Hp EQ]]].
    - destruct K as [[p [Hp EQ]] | [g [Hg Hpg]]].
      + apply (SH p ltac:(apply in_or_app; left; exact Hp)). unfold appr in EQ. cbn [fst snd] in EQ. injection EQ as -> ->. exact Ha.
      + (first [ pose proof ((pages_facts g lo hi ltac:(apply in_or_app; right; exact Hg) Hpg)) as dR_19; dand4 dR_19 as P1 P2 P3 P4 | pose proof (pages_facts g lo hi ltac:(apply in_or_app; right; exact Hg) Hpg) as (P1 & P2 & P3 & P4) ]).
        apply (SH g ltac:(apply in_or_app; right; exact Hg)). lia.
    - exfalso. (first [ pose proof ((shr_facts p Hp)) as dR_20; dand3 dR_20 as S1 S2 _ | pose proof (shr_facts p Hp) as (S1 & S2 & _) ]). rewrite <- EQ in S1, S2. cbn [fst snd] in S1, S2.
      rewrite HCEIL in APP. pose proof usp_range as [UR _]. unfold kLowMemEnd, kHighMemBeg, KHIZ in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma flat_map_pages_len : forall l, (forall p, In p l -> In p (a_vis cs ++ a_ghost cs) /\ uE E (snd p) <= 8192) ->
    (length (flat_map (fun p => pages_of (appr p)) l) <= 2 * length l)%nat.
  Proof.
    induction l as [|p l IH]; intros H; [cbn; lia|].
    change (flat_map (fun p0 => pages_of (appr p0)) (p :: l)) with (pages_of (appr p) ++ flat_map (fun p0 => pages_of (appr p0)) l).
    rewrite app_length. specialize (IH ltac:(intros q Hq; apply H; right; exact Hq)). destruct (H p ltac:(left; reflexivity)) as [Hp Hn].
    (first [ pose proof ((vg_ok p Hp)) as dR_21; dand6 dR_21 as F1 F2 F3 F4 F5 F6 | pose proof (vg_ok p Hp) as (F1 & F2 & F3 & F4 & F5 & F6) ]).
    assert (LP : (length (pages_of (appr p)) <= 2)%nat).
    { unfold pages_of, appr. cbn [fst snd]. rewrite map_length, seq_length.
      replace (uE E (fst p) + uE E (snd p) - uE E (fst p)) with (uE E (snd p)) by lia. clear - Hn F3. Z.div_mod_to_equations. lia. }
    cbn [length]. lia.
  Qed.
  (* [comment removed for export] *)
  Definition VISL13 : list (Z * Z) :=
    [(pgv 4115, 4096); (pgv 498, 4096); (pgv 481, 8388608); (pgv 480, 1048576); (pgv 405, 11571200); (pgv 322, 4096);
     (pgv 257, 4096); (pgv 228, 65536); (pgv 227, 4096); (riZ, 4096); (pgv 207, 3727360); (pgv 78, 65536);
     (65536, 6266880)].
  Lemma VISL_split : VISL = VISL13 ++ [(PGSP - 8388608, 140737496743936 - PGSP)].
  Proof. reflexivity. Qed.
  Lemma map_appr_den : forall l, map appr l = map (fun d => (fst d, fst d + snd d)) (map den l).
  Proof. intros l. rewrite map_map. reflexivity. Qed.
  Lemma fold_shr_den : forall l,
    fold_right (fun p a => uE E (snd p) / 8 + 16384 + a) 0 l = fold_right (fun d a => snd d / 8 + 16384 + a) 0 (map den l).
  Proof. intros l. induction l as [|p l IH]; [reflexivity|]. cbn [fold_right map]. rewrite IH. reflexivity. Qed.
  (* [comment removed for export] *)
  Lemma hull_bytes_shr_le : forall l, (forall p, In p l -> In p (a_vis cs ++ a_ghost cs)) ->
    Hull.hull_bytes (map shr l) <= fold_right (fun p a => uE E (snd p) / 8 + 16384 + a) 0 l.
  Proof.
    intros l Hl. induction l as [|p l IH]; [cbn; lia|].
    cbn [map Hull.hull_bytes fold_right]. specialize (IH ltac:(intros q Hq; apply Hl; right; exact Hq)).
    (first [ pose proof ((shr_facts p (Hl p (or_introl eq_refl)))) as dR_26; dand6 dR_26 as S1 S2 S3 S4 S5 _ | pose proof (shr_facts p (Hl p (or_introl eq_refl))) as (S1 & S2 & S3 & S4 & S5 & _) ]).
    destruct (shr p) as [lo hi]. cbn [fst snd] in S1, S2, S3, S4, S5.
    pose proof (hull_bytes1 lo hi ltac:(lia) ltac:(lia)). lia.
  Qed.
  Lemma fold_le_len : forall (A : Type) (w : A -> Z) (B : Z) (l : list A),
    (forall x, In x l -> w x <= B) -> fold_right (fun x a => w x + a) 0 l <= Z.of_nat (length l) * B.
  Proof.
    intros A w B l H. induction l as [|x l IH]; [cbn; lia|]. cbn [fold_right length].
    specialize (IH ltac:(intros y Hy; apply H; right; exact Hy)). pose proof (H x (or_introl eq_refl)). rewrite Nat2Z.inj_succ. lia.
  Qed.
  Lemma extra_weight : Hull.hull_bytes EXTRA <= 2^28 + 2^26.
  Proof.
    pose proof usp_range as [UR _]. pose proof usp_top as UT.
    (first [ dand4 ghost_facts as GHL EQG FG LG | destruct ghost_facts as (GHL & EQG & FG & LG) ]).
    assert (LGH : (length (a_ghost cs) <= 6)%nat) by (rewrite (s_ghost cs gh ASS), <- (map_length den), EQG; exact LG).
    (first [ pose proof (riZ_facts) as dR_22; dand3 dR_22 as RI1 RI2 RI3 | pose proof riZ_facts as (RI1 & RI2 & RI3) ]). pose proof AP208 as B6. pose proof R208 as Q208.
    unfold EXTRA. rewrite !hull_bytes_app.
    (* [comment removed for export] *)
    assert (W1 : Hull.hull_bytes (List.filter (covb VMM) (map appr (a_vis cs))) <= 31264768).
    { rewrite map_appr_den, vis_denl, VISL_split, map_app, filter_app, hull_bytes_app.
      assert (X1 : Hull.hull_bytes (map (fun d => (fst d, fst d + snd d)) VISL13) <= 31264768).
      { eapply Z.le_trans; [apply hull_bytes_den_le|].
        - unfold VISL13. forall_lit; cbn [fst snd]; hi_tac.
        - cbn [fold_right fst snd VISL13]. lia. }
      pose proof (hull_bytes_filter_le (covb VMM) (map (fun d => (fst d, fst d + snd d)) VISL13)) as X2.
      assert (X3 : Hull.hull_bytes (List.filter (covb VMM) (map (fun d => (fst d, fst d + snd d)) [(PGSP - 8388608, 140737496743936 - PGSP)])) = 0).
      { cbn [map fst snd List.filter]. destruct (covb VMM (PGSP - 8388608, PGSP - 8388608 + (140737496743936 - PGSP))) eqn:C; [|reflexivity].
        exfalso. (first [ pose proof ((cov_where _ _ C)) as dR_23; dex1 dR_23 as e; dand5 dR_23 as He E1 E2 E3 E0 | pose proof ((cov_where _ _ C)) as dR_23; dand6 dR_23 as e He E1 E2 E3 E0 | destruct (cov_where _ _ C) as (e & He & E1 & E2 & E3 & E0) ]).
        clear - E2 E3 UR UT. lia. }
      lia. }
    (* [comment removed for export] *)
    assert (W2 : Hull.hull_bytes (List.filter (covb VMM) (flat_map (fun p => pages_of (appr p)) (a_ghost cs))) <= 12 * (4096 + 8192)).
    { eapply Z.le_trans; [apply (hull_bytes_le_sum _ 4096 ltac:(lia))|].
      - apply Forall_forall. intros [lo hi] Hin. apply filter_In in Hin as [Hin C]. apply in_flat_map in Hin as [g [Hg Hpg]]. cbn [fst snd].
        (first [ pose proof ((pages_facts g lo hi ltac:(apply in_or_app; right; exact Hg) Hpg)) as dR_24; dand4 dR_24 as P1 P2 P3 P4 | pose proof (pages_facts g lo hi ltac:(apply in_or_app; right; exact Hg) Hpg) as (P1 & P2 & P3 & P4) ]).
        pose proof (vg_ok g ltac:(apply in_or_app; right; exact Hg)). lia.
      - apply Z.mul_le_mono_nonneg_r; [lia|].
        pose proof (filter_length_le (covb VMM) (flat_map (fun p => pages_of (appr p)) (a_ghost cs))) as FL.
        pose proof (flat_map_pages_len (a_ghost cs) ltac:(intros q Hq; split; [apply in_or_app; right; exact Hq|];
            (first [ pose proof ((ghost_ok q Hq)) as dR_25; dand4 dR_25 as _ _ GC _ | pose proof (ghost_ok q Hq) as (_ & _ & GC & _) ]); unfold den in GC; cbn [fst snd] in GC; lia)) as PL. lia. }
    (* [comment removed for export] *)
    assert (W3 : Hull.hull_bytes (map shr (a_vis cs ++ a_ghost cs)) <= 274000000).
    { rewrite map_app, hull_bytes_app.
      pose proof (hull_bytes_shr_le (a_vis cs) ltac:(intros q Hq; apply in_or_app; left; exact Hq)) as V1.
      rewrite fold_shr_den, vis_denl in V1. unfold VISL in V1. cbn [fold_right fst snd] in V1.
      change (4096 / 8) with 512 in V1. change (8388608 / 8) with 1048576 in V1. change (1048576 / 8) with 131072 in V1.
      change (11571200 / 8) with 1446400 in V1. change (65536 / 8) with 8192 in V1. change (3727360 / 8) with 465920 in V1.
      change (6266880 / 8) with 783360 in V1.
      assert (SB : (140737496743936 - PGSP) / 8 <= 269485056) by (clear - UR UT; Z.div_mod_to_equations; lia).
      pose proof (hull_bytes_shr_le (a_ghost cs) ltac:(intros q Hq; apply in_or_app; right; exact Hq)) as G1.
      pose proof (fold_le_len _ (fun p => uE E (snd p) / 8 + 16384) 17408 (a_ghost cs)
                    ltac:(intros q Hq; (first [ pose proof ((ghost_ok q Hq)) as dR_27; dand4 dR_27 as _ _ GC _ | pose proof (ghost_ok q Hq) as (_ & _ & GC & _) ]);
                          unfold den in GC; cbn [fst snd] in GC; clear - GC; Z.div_mod_to_equations; lia)) as G2.
      cbn beta in G2. clear - V1 SB G1 G2 LGH. lia. }
    lia.
  Qed.
  (* [comment removed for export] *)
  Lemma extra_not_primary : forall lo hi a, In (lo, hi) EXTRA -> lo <= a < hi -> ~ (p_sb P <= a < p_sb P + kSpaceSize).
  Proof.
    intros lo hi a Hin Ha Hsb. unfold kSpaceSize in Hsb. rewrite sb_val in Hsb.
    (first [ pose proof (riZ_facts) as dR_28; dand3 dR_28 as RI1 RI2 RI3 | pose proof riZ_facts as (RI1 & RI2 & RI3) ]). pose proof AP208 as B6. pose proof LH208 as BH. pose proof R208 as Q208. pose proof R209 as Q209.
    pose proof usp_top as UT.
    pose proof D_4115_208 as D4115. pose proof D_498_208 as D498. pose proof D_481_208 as D481. pose proof D_480_208 as D480.
    pose proof D_405_208 as D405. pose proof D_322_208 as D322. pose proof D_257_208 as D257. pose proof D_228_208 as D228.
    pose proof D_227_208 as D227. pose proof D_207_208 as D207. pose proof D_78_208 as D78.
    destruct (in_EXTRA lo hi Hin) as [[C [[p [Hp EQ]] | [g [Hg Hpg]]]] | [p [Hp EQ]]].
    - (* [comment removed for export] *)
      pose proof (in_map den _ _ Hp) as Hd. rewrite vis_denl in Hd. unfold den in Hd.
      unfold appr in EQ. injection EQ as EQ1 EQ2. subst lo hi.
      remember (uE E (fst p)) as b eqn:Hb. remember (uE E (snd p)) as n eqn:Hn. clear Hb Hn.
      in_cases2 Hd; first [ clear - Ha Hsb Q208 Q209 D4115; a0_natz_all; unfold pgv in *; lia | clear - Ha Hsb Q208 Q209 D498; a0_natz_all; unfold pgv in *; lia
              | clear - Ha Hsb Q208 Q209 D481; a0_natz_all; unfold pgv in *; lia  | clear - Ha Hsb Q208 Q209 D480; a0_natz_all; unfold pgv in *; lia
              | clear - Ha Hsb Q208 Q209 D405; a0_natz_all; unfold pgv in *; lia  | clear - Ha Hsb Q208 Q209 D322; a0_natz_all; unfold pgv in *; lia
              | clear - Ha Hsb Q208 Q209 D257; a0_natz_all; unfold pgv in *; lia  | clear - Ha Hsb Q208 Q209 D228; a0_natz_all; unfold pgv in *; lia
              | clear - Ha Hsb Q208 Q209 D227; a0_natz_all; unfold pgv in *; lia  | clear - Ha Hsb Q208 Q209 D207; a0_natz_all; unfold pgv in *; lia
              | clear - Ha Hsb Q208 Q209 D78; a0_natz_all; unfold pgv in *; lia
              | clear - Ha Hsb Q208 Q209 RI1 RI2 RI3; unfold riZ, pgv in *; lia
              | clear - Ha Hsb Q208 Q209 UT B6; a0_natz_all; unfold pgv in *; lia ].
    - (* [comment removed for export] *)
      (first [ pose proof ((pages_facts g lo hi ltac:(apply in_or_app; right; exact Hg) Hpg)) as dR_29; dand4 dR_29 as P1 P2 P3 P4 | pose proof (pages_facts g lo hi ltac:(apply in_or_app; right; exact Hg) Hpg) as (P1 & P2 & P3 & P4) ]).
      pose proof (ghost_b6 g Hg) as GB. clear - Ha Hsb P1 P2 P3 P4 GB Q208 Q209. unfold pgv in *. lia.
    - (* [comment removed for export] *)
      (first [ pose proof ((shr_facts p Hp)) as dR_30; dand3 dR_30 as S1 S2 _ | pose proof (shr_facts p Hp) as (S1 & S2 & _) ]). rewrite <- EQ in S1, S2. cbn [fst snd] in S1, S2.
      unfold KHIZ, LOWSHZ in *. clear - Ha Hsb S1 S2 BH Q208 Q209. unfold pgv in *. lia.
  Qed.

  (* [comment removed for export] *)


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma classes_regions_zero : forall sb n, classes_regions_ sb (fun _ => region_zero) n = [].
  Proof. intros sb n. induction n as [|n IH]; [reflexivity|]. cbn [classes_regions_]. rewrite IH. reflexivity. Qed.
  Lemma lclasses_regions_zero : forall sb n, lclasses_regions_ sb (fun _ => region_zero) n = [].
  Proof. intros sb n. induction n as [|n IH]; [reflexivity|]. cbn [lclasses_regions_]. rewrite IH. reflexivity. Qed.
  Lemma classes_eager_zero : forall n, classes_eager_ (fun _ => region_zero) n = 0.
  Proof. intros n. induction n as [|n IH]; [reflexivity|]. cbn [classes_eager_]. rewrite IH. reflexivity. Qed.
  Lemma hull0_eq : a0_hull P k1 = LayoutPA.pa_image_ivs ++ Hull.hull_of (fixed_regions_ AL_pboth P) ++ EXTRA.
  Proof.
    unfold a0_hull, AInv.pa_hull, ahull_of, ahull_of_, aregions_, A0_of. cbn [a_pl a_reg a_sec a_deadsh sr_chunks p_extra P].
    rewrite classes_regions_zero. cbn [sec_regions_ flat_map app]. rewrite app_nil_r. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma lhull0_eq : a0_lhull P k1 = Hull.hull_of (lfixed_regions_ AL_pboth P) ++ EXTRA.
  Proof.
    unfold a0_lhull, AInv.pa_lhull, alhull_of, alhull_of_, alregions_, A0_of. cbn [a_pl a_reg a_sec a_deadsh sr_chunks p_extra P].
    rewrite lclasses_regions_zero. cbn [lsec_regions_ map app]. rewrite app_nil_r. reflexivity.
  Qed.
  Lemma eager0_eq : a0_eager P k1 = a_eager cs.
  Proof.
    unfold a0_eager, AInv.pa_eager, aeager_of, aeager_of_, A0_of. cbn [a_pl a_reg a_sec sr_chunks sr_reserved p_eager0 P].
    rewrite classes_eager_zero. cbn. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma cov_sub : forall b n lo hi, In (b, n) BML -> 0 <= b -> b + n < 2^64 -> b <= lo -> hi <= b + n -> covb VMM (lo, hi) = true.
  Proof.
    intros b n lo hi Hin H0 H2 H3 H4. apply (proj2 (covb_true _ _)). exists (Z_to_bv 64 b, Z_to_bv 64 n). split; [exact (bml_vmm b n Hin)|].
    cbn [fst snd]. (first [ pose proof ((bml_bounds b n Hin)) as dR_31; dand3 dR_31 as _ B1 _ | pose proof (bml_bounds b n Hin) as (_ & B1 & _) ]). rewrite !u_lit64a, !Z.mod_small by lia. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma vis_cov : forall p q (e : word * word), In p (a_vis cs) -> uE E (fst p) <= q -> q + 4096 <= uE E (fst p) + uE E (snd p) ->
    In e VMM -> bv_unsigned (fst e) <= q -> q + 4096 <= bv_unsigned (fst e) + bv_unsigned (snd e) ->
    bv_unsigned (fst e) + bv_unsigned (snd e) <= alloc_top (m_vmmaps model) ->
    (bv_unsigned (fst e) + bv_unsigned (snd e) <= img_lo BOTH \/ img_hi BOTH <= bv_unsigned (fst e)) ->
    covb VMM (appr p) = true.
  Proof.
    intros p q e Hp Q1 Q2 He E1 E2 E3 E4. rewrite alloc_top_val in E3. cbn [img_lo img_hi BOTH] in E4. pose proof usp_top as UT.
    (first [ pose proof (riZ_facts) as dR_32; dand3 dR_32 as RI1 RI2 RI3 | pose proof riZ_facts as (RI1 & RI2 & RI3) ]). pose proof AP208 as B6. pose proof R208 as Q208.
    pose proof (in_map den _ _ Hp) as Hd. rewrite vis_denl in Hd. unfold den in Hd. unfold appr.
    remember (uE E (fst p)) as b eqn:Hb. remember (uE E (snd p)) as n eqn:Hn. clear Hb Hn. cbn [fst snd].
    in_cases2 Hd; first [ lazymatch goal with
              | |- covb VMM (pgv ?v, pgv _ + ?m) = true => apply (cov_sub (pgv v) m); [in_nth | hi_tac | hi_tac | lia | lia]
              | |- covb VMM (riZ, _) = true => apply (cov_sub (pgv 208) 137439023104); [in_nth | hi_tac | hi_tac | lia | lia]
              end
            | (* [comment removed for export] *)
              exfalso; unfold pgv in *; lia ].
  Qed.
  (* [comment removed for export] *)
  Lemma shreg_bounds : forall b s, 0 <= b -> 0 < s -> s <= 2164260864 -> b + s <= 2^47 ->
    0 <= fst (shadow_region b s) /\ fst (shadow_region b s) <= fst (shadow_region b s) + snd (shadow_region b s) <= fst (shadow_region b s) + 270540800.
  Proof.
    clear. intros b s H0 H1 H2 H3. unfold shadow_region, Asan12c.round_down, Asan12c.round_up, sh, kShadowOffset. cbn [fst snd].
    Z.div_mod_to_equations. lia.
  Qed.
  Lemma shreg_bounds_sz : forall b s, 0 <= b -> 0 < s -> s <= 11571200 -> b + s <= 2^47 ->
    0 <= fst (shadow_region b s) /\ fst (shadow_region b s) <= fst (shadow_region b s) + snd (shadow_region b s) <= fst (shadow_region b s) + 11571216.
  Proof.
    clear. intros b s H0 H1 H2 H3. unfold shadow_region, Asan12c.round_down, Asan12c.round_up, sh, kShadowOffset. cbn [fst snd].
    Z.div_mod_to_equations. lia.
  Qed.
  Lemma A_minv : Hull.MInv (a0_hull P k1) (a0_lhull P k1) (a0_eager P k1) model.
  Proof.
    pose proof usp_range as [US UM]. pose proof usp_top as UT.
    pose proof (entry_stack_span_bound argv envp Hva Hve) as SPAN. unfold entry_stack_span_max in SPAN.
    rewrite hull0_eq, lhull0_eq, eager0_eq.
    apply (minv_of_cs3 _ _ fs cs E R FULL model CS).
    - (* [comment removed for export] *)
      intros lo hi q e Hin Q1 Q2 QA He E1 E2 E3 E4.
      unfold allowA in Hin. apply in_flat_map in Hin as [p [Hp Hin]]. unfold allow1 in Hin. cbn [In] in Hin.
      (first [ pose proof ((vg_ok p Hp)) as dR_33; dand6 dR_33 as F1 F2 F3 F4 F5 F6 | pose proof (vg_ok p Hp) as (F1 & F2 & F3 & F4 & F5 & F6) ]).
      destruct Hin as [EQ|[EQ|[]]].
      + (* [comment removed for export] *)
        rewrite (pagedown_id _ F2), (pageup_id _ ltac:(rewrite Z.add_mod, F2, F4 by lia; reflexivity)) in EQ.
        injection EQ as EQ1 EQ2. subst lo hi.
        apply in_app_or in Hp. destruct Hp as [Hp|Hp].
        * apply (page_hullb_in _ (uE E (fst p)) (uE E (fst p) + uE E (snd p))); [| lia| lia].
          rewrite !in_app_iff. right. unfold EXTRA. rewrite !in_app_iff. left. apply filter_In. split.
          -- change (uE E (fst p), uE E (fst p) + uE E (snd p)) with (appr p). apply in_map. exact Hp.
          -- exact (vis_cov p q e Hp Q1 Q2 He E1 E2 E3 E4).
        * apply (page_hullb_in _ q (q + 4096)); [| lia| lia].
          rewrite !in_app_iff. right. unfold EXTRA. rewrite !in_app_iff. right. left. apply filter_In. split.
          -- apply in_flat_map. exists p. split; [exact Hp|]. unfold appr. cbn [fst snd]. apply (proj2 (in_pages_of _ _ _ _)).
             exists (Z.to_nat ((q - uE E (fst p)) / 4096)). rewrite Z2Nat.id by (Z.div_mod_to_equations; lia).
             replace (uE E (fst p) + uE E (snd p) - uE E (fst p)) with (uE E (snd p)) by lia.
             split; [Z.div_mod_to_equations; nia|]. split; [Z.div_mod_to_equations; nia| reflexivity].
          -- apply (proj2 (covb_true _ _)). exists e. cbn [fst snd]. tauto.
      + (* [comment removed for export] *)
        apply (page_hullb_in _ lo hi); [| lia| lia]. rewrite !in_app_iff. right. unfold EXTRA. rewrite !in_app_iff. right. right.
        rewrite <- EQ. change (pagedown (sh_lo BOTH E p), pageup (sh_hi BOTH E p)) with (shr p). apply in_map. exact Hp.
    - (* [comment removed for export] *)
      rewrite (fixed_regions_split AL_pboth P). cbn [Hull.hull_of List.map fst snd p_sp0 p_stk_span P].
      apply Hull.hull_cover_app.
      + pose proof (lazy_free_image _ _ fs cs E R FULL model CS) as LI. cbn [img_lo img_hi BOTH] in LI.
        unfold LayoutPA.pa_image_ivs. intros lo hi Hin. right.
        in_cases2 Hin; (apply (Hull.lazy_free_shrink _ 65536 6332416); [exact LI | lia | lia]).
      + apply Hull.hull_cover_cons; [| apply Hull.hull_cover_self].
        right. cbn [fst snd]. apply (lazy_free_above_top _ _ fs cs E R FULL model CS). rewrite alloc_top_val. lia.
    - lia.
    - (* [comment removed for export] *)
      pose proof HLIM as HBL. rewrite AInv.TLIM_MIN_eq in HBL. rewrite !hull_bytes_app. pose proof extra_weight as XW.   (* [comment removed for export] *)
      assert (FF : Forall (fun iv => 0 <= fst iv /\ fst iv <= snd iv <= fst iv + 270540800) (firstn 1 (Hull.hull_of (lfixed_regions_ AL_pboth P)))
                   /\ Forall (fun iv => 0 <= fst iv /\ fst iv <= snd iv <= fst iv + 11571216) (skipn 1 (Hull.hull_of (lfixed_regions_ AL_pboth P)))).
      { (first [ pose proof (riZ_facts) as dR_34; dand3 dR_34 as RI1 RI2 RI3 | pose proof riZ_facts as (RI1 & RI2 & RI3) ]). pose proof AP208 as B6. pose proof R208 as Q208.
        unfold Hull.hull_of, lfixed_regions_. rewrite riZ_val. unfold stack_shadow_iv. rewrite HCEIL.
        cbn [firstn skipn List.map fst snd p_sp0 p_stk_span p_thr p_ctx p_fs p_nodes0 p_frames0 p_pa p_itab p_m64k p_dtls p_gvec p_dvec p_m11 P al_image_lo al_image_hi AL_pboth].
        unfold kFakeStackBytes, kDepotNodesBlock, kStackStoreBlockBytes, kChunksBlockCount.
        split; (forall_lit; cbn [fst snd]; first [ apply shreg_bounds; hi_tac | apply shreg_bounds_sz; hi_tac | hi_tac ]). }
      destruct FF as [FF1 FF2].
      pose proof (hull_bytes_le_sum _ 270540800 ltac:(lia) FF1) as FW1. pose proof (hull_bytes_le_sum _ 11571216 ltac:(lia) FF2) as FW2.
      rewrite <- (firstn_skipn 1 (Hull.hull_of (lfixed_regions_ AL_pboth P))), hull_bytes_app.
      replace (Z.of_nat (length (firstn 1 (Hull.hull_of (lfixed_regions_ AL_pboth P))))) with 1 in FW1 by reflexivity.
      replace (Z.of_nat (length (skipn 1 (Hull.hull_of (lfixed_regions_ AL_pboth P))))) with 23 in FW2 by reflexivity.
      lia.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A_qglobal_zero : ACells.fill_at BSEGS FULL (al_instance AL_pboth + off_q_cache_list_size) 32 0.
  Proof. unfold ACells.fill_at. cell 29%nat. Qed.
  Lemma A_sec_zero : ACells.u64_at BSEGS FULL (al_instance AL_pboth + off_sec_n_reserved) 0 /\ ACells.u64_at BSEGS FULL (al_instance AL_pboth + off_sec_n_chunks) 0.
  Proof. split; [cell 27%nat | cell 28%nat]. Qed.
  Lemma A_ia : ACells.u8_at BSEGS FULL (al_internal_alloc_inited AL_pboth) 0 /\ ACells.fill_at BSEGS FULL (al_internal_allocator_inst AL_pboth) 0x81030 0.
  Proof.
    split; [cell 30%nat|]. unfold ACells.fill_at. cbn [al_internal_allocator_inst AL_pboth].
    apply (img_zero_fill sp rdraw brk0 argv envp uid hw fs Hsp Hva cs E R FULL model CS _ _ _ 0x81030 (k_img_ia cs AK)); [cbn; lia| cbn; lia| lia| cbn; lia| cbn; lia|].
    intros a Ha. apply img0_ia_inst. lia.
  Qed.
  Lemma A_fs_log : ACells.u64_at BSEGS FULL (p_fs P + 88) kFakeStackSizeLog /\ ACells.u8_at BSEGS FULL (p_fs P + 96) 0.
  Proof using CS AK.
    pose proof R405. pose proof R405z. cbn [p_fs P]. split.
    - unfold kFakeStackSizeLog. apply (u64_symL (pg 405) (pgv 405) 88 20 U405 (k_fs_88 cs AK)); hi_tac.
    - apply u8_zero; [| unfold pgv; lia]. replace (pgv 405 + 96) with (pgv 405 + 96 + 0) by lia.
      apply (ZSYM (pg 405) (pgv 405) 96 0xb08fa0 U405 (k_fs_z96 cs AK)); lia.
  Qed.
  Lemma A_halted : m_halted model = None.
  Proof. exact (pre_halted sp rdraw brk0 argv envp uid hw fs cs E R FULL model CS). Qed.

  (* [comment removed for export] *)
  Theorem a0_pre_of_cs : a0_pre P k1 usp FULL model.
  Proof.
    constructor.
    all: first [ exact A_place | exact A_consts | exact A_locks | exact A_ri_zero | exact A_thr_zero | exact A_thr_map
               | exact A_qglobal_zero | exact A_sec_zero | exact A_ia | exact A_depot | exact HK1 | exact A_fs_hints | exact A_fs_log
               | exact A_fs_flags | exact A_fs_map | exact A_maps | exact A_stkshadow_map | exact A_imgshadow_map
               | exact A_hidden | exact extra_closure | exact LayoutPA.pa_dkeys_sites | (pose proof extra_weight; cbn [p_extra P]; lia) | exact extra_not_primary
               | exact A_ledger | exact A_bigmaps | exact A_minv | exact A_halted | exact A_reserved | exact A_gap | exact A_vmmaps
               | idtac ].
    - (* [comment removed for export] *) apply Forall_forall. intros [lo hi] Hin. cbn [fst snd]. pose proof (extra_facts lo hi Hin). lia.
    - (* [comment removed for export] *) intros lo hi Hin. pose proof (extra_facts lo hi Hin). tauto.
    - (* [comment removed for export] *) pose proof R5. cbn [p_brk P]. unfold LayoutPA.LPA. cbn [cl_image_hi]. unfold pgv. lia.
    - (* [comment removed for export] *) cbn [p_tlim P]. exact HLIM.
  Qed.
End A0.

End BothA0.


Module Bothvij.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInioec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require PropExec AxSyioe Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asanqlm Bothny9 AsanInit Starr0h Stargqr Bothgt0 BothA0K.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothny9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Starr0h OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Stargqr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothgt0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.BothA0K OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Mwrv.BothA0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Boot1pr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.AxSyetn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Boot1pr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP. Import APS.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition fact_iv (K : kentry) : option (Z * Z) :=
  match K with
  | KWord (SA (ELit 0) b) w (ELit _) => Some (b, b + Z.of_nat w)
  | KZero (SA (ELit 0) b) (ELit n) => Some (b, b + n)
  | KFill (SA (ELit 0) b) (ELit n) _ => Some (b, b + n)
  | KImg lo hi => Some (lo, hi)
  | _ => None
  end.
Definition touchW (wlo whi : Z) (K : kentry) : bool :=
  match fact_iv K with Some (l, h) => (l <? whi) && (wlo <? h) | None => false end.

Ltac b2z := repeat match goal with
  | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  end.

Lemma kbyte_skip : forall wlo whi K k x, wlo <= x < whi -> touchW wlo whi K = false -> kbyte (K :: k) x = kbyte k x.
Proof.
  intros wlo whi K k x Hx HT. unfold touchW, fact_iv in HT. cbn [kbyte].
  destruct K as [sa w v|sa n|sa n kk|lo hi|e m0|e lo hi|sa n|a1 n1 a2 n2|sa n c|sa n]; try reflexivity.
  - destruct sa as [bse off]. destruct bse; try reflexivity. destruct z; try reflexivity. destruct v; try reflexivity.
    destruct ((off <=? x) && (x <? off + Z.of_nat w))%bool eqn:C; [|reflexivity]. exfalso. b2z.
    apply andb_false_iff in HT. destruct HT as [HT|HT]; [apply Z.ltb_ge in HT|apply Z.ltb_ge in HT]; lia.
  - destruct sa as [bse off]. destruct bse; try reflexivity. destruct z; try reflexivity. destruct n; try reflexivity.
    destruct ((off <=? x) && (x <? off + z) && (0 <=? z) && (z <? 2 ^ 64))%bool eqn:C; [|reflexivity]. exfalso. b2z.
    apply andb_false_iff in HT. destruct HT as [HT|HT]; [apply Z.ltb_ge in HT|apply Z.ltb_ge in HT]; lia.
  - destruct sa as [bse off]. destruct bse; try reflexivity. destruct z; try reflexivity. destruct n; try reflexivity.
    destruct ((off <=? x) && (x <? off + z) && (0 <=? z) && (z <? 2 ^ 64))%bool eqn:C; [|reflexivity]. exfalso. b2z.
    apply andb_false_iff in HT. destruct HT as [HT|HT]; [apply Z.ltb_ge in HT|apply Z.ltb_ge in HT]; lia.
Qed.

Lemma kbyte_congr : forall K k1 k2 x, kbyte k1 x = kbyte k2 x -> kbyte (K :: k1) x = kbyte (K :: k2) x.
Proof.
  intros K k1 k2 x H. cbn [kbyte].
  destruct K as [sa w v|sa n|sa n kk|lo hi|e m0|e lo hi|sa n|a1 n1 a2 n2|sa n c|sa n]; try exact H.
  - destruct sa as [bse off]. destruct bse; try exact H. destruct z; try exact H. destruct v; try exact H.
    destruct ((off <=? x) && (x <? off + Z.of_nat w))%bool; [reflexivity|exact H].
  - destruct sa as [bse off]. destruct bse; try exact H. destruct z; try exact H. destruct n; try exact H.
    destruct ((off <=? x) && (x <? off + z) && (0 <=? z) && (z <? 2 ^ 64))%bool; [reflexivity|exact H].
  - destruct sa as [bse off]. destruct bse; try exact H. destruct z; try exact H. destruct n; try exact H.
    destruct ((off <=? x) && (x <? off + z) && (0 <=? z) && (z <? 2 ^ 64))%bool; [reflexivity|exact H].
Qed.

Lemma kbyte_filter : forall wlo whi k x, wlo <= x < whi -> kbyte (List.filter (touchW wlo whi) k) x = kbyte k x.
Proof.
  intros wlo whi k x Hx. induction k as [|K k IH]; [reflexivity|]. cbn [List.filter].
  destruct (touchW wlo whi K) eqn:T.
  - apply kbyte_congr. exact IH.
  - rewrite (kbyte_skip wlo whi K k x Hx T). exact IH.
Qed.

Lemma existsb_filter : forall (A : Type) (f p : A -> bool) (l : list A),
  (forall a, f a = true -> p a = true) -> existsb f (List.filter p l) = existsb f l.
Proof.
  intros A f p l H. induction l as [|a l IH]; [reflexivity|]. cbn [List.filter existsb].
  destruct (p a) eqn:P.
  - cbn [existsb]. rewrite IH. reflexivity.
  - rewrite IH. destruct (f a) eqn:F; [rewrite (H a F) in P; discriminate|reflexivity].
Qed.

Lemma kimg_cov1_filter : forall wlo whi k x, wlo <= x < whi -> kimg_cov1 (List.filter (touchW wlo whi) k) x = kimg_cov1 k x.
Proof.
  intros wlo whi k x Hx. unfold kimg_cov1. apply existsb_filter. intros K HK.
  destruct K; try discriminate. unfold touchW, fact_iv. b2z. apply andb_true_iff. split; apply Z.ltb_lt; lia.
Qed.

Lemma kzero_covr_filter : forall wlo whi k a n, wlo <= a -> a + n <= whi -> 0 < n ->
  kzero_covr (List.filter (touchW wlo whi) k) a n = kzero_covr k a n.
Proof.
  intros wlo whi k a n H1 H2 H3. unfold kzero_covr. apply existsb_filter. intros K HK.
  destruct K as [sa w v|sa m|sa m kk|lo hi|e m0|e lo hi|sa m|a1 n1 a2 n2|sa m c|sa m]; try discriminate.
  destruct sa as [bse off]. destruct bse; try discriminate. destruct z; try discriminate. destruct m; try discriminate.
  unfold touchW, fact_iv. b2z. apply andb_true_iff. split; apply Z.ltb_lt; lia.
Qed.

Lemma kimg_covr_filter : forall wlo whi k a n, wlo <= a -> a + n <= whi -> 0 < n ->
  kimg_covr (List.filter (touchW wlo whi) k) a n = kimg_covr k a n.
Proof.
  intros wlo whi k a n H1 H2 H3. unfold kimg_covr. apply existsb_filter. intros K HK.
  destruct K; try discriminate. unfold touchW, fact_iv. b2z. apply andb_true_iff. split; apply Z.ltb_lt; lia.
Qed.

Lemma bytes_okb_filter : forall wlo whi k bs a, wlo <= a -> a + Z.of_nat (length bs) <= whi ->
  bytes_okb (List.filter (touchW wlo whi) k) a bs = bytes_okb k a bs.
Proof.
  intros wlo whi k bs. induction bs as [|b bs IH]; intros a H1 H2; [reflexivity|].
  cbn [bytes_okb]. cbn [length] in H2. rewrite Nat2Z.inj_succ in H2.
  rewrite (IH (a + 1)) by lia. unfold byte_okb.
  rewrite (kbyte_filter wlo whi k a) by lia. rewrite (kimg_cov1_filter wlo whi k a) by lia. reflexivity.
Qed.

Lemma cell_okb_filter : forall wlo whi k a bs, wlo <= a -> a + Z.of_nat (length bs) <= whi -> 0 < Z.of_nat (length bs) ->
  cell_okb (List.filter (touchW wlo whi) k) a bs = cell_okb k a bs.
Proof.
  intros wlo whi k a bs H1 H2 H3. unfold cell_okb. cbv zeta.
  rewrite (kzero_covr_filter wlo whi k a _ H1 H2 H3), (kimg_covr_filter wlo whi k a _ H1 H2 H3), (bytes_okb_filter wlo whi k bs a H1 H2).
  reflexivity.
Qed.

(* [comment removed for export] *)
Definition T64 : Z := 18446744073709551616.
Fixpoint existsbL {T : Type} (f : T -> bool) (l : list T) : bool :=
  match l with [] => false | x :: r => if f x then true else existsbL f r end.
Lemma existsbL_eq : forall (T : Type) (f : T -> bool) l, existsbL f l = existsb f l.
Proof. intros T f l. induction l as [|x r IH]; [reflexivity|]. cbn [existsbL existsb]. rewrite IH. reflexivity. Qed.
Fixpoint kbyteF (k : list kentry) (a : Z) : option byte :=
  match k with
  | [] => None
  | KWord (SA (ELit 0) b) w (ELit v) :: k' =>
      if (if b <=? a then a <? b + Z.of_nat w else false)
      then Some (Z_to_bv 8 (Z.shiftr (bv_unsigned (Z_to_bv 64 v)) (8 * (a - b)))) else kbyteF k' a
  | KZero (SA (ELit 0) b) (ELit n) :: k' =>
      if (if (if (if b <=? a then a <? b + n else false) then 0 <=? n else false) then n <? T64 else false) then Some (Z_to_bv 8 0) else kbyteF k' a
  | KFill (SA (ELit 0) b) (ELit n) c :: k' =>
      if (if (if (if b <=? a then a <? b + n else false) then 0 <=? n else false) then n <? T64 else false) then Some (Z_to_bv 8 c) else kbyteF k' a
  | _ :: k' => kbyteF k' a
  end.
Lemma kbyteF_eq : forall k a, kbyteF k a = kbyte k a.
Proof.
  induction k as [|K k IH]; intros a; [reflexivity|]. cbn [kbyteF kbyte].
  repeat match goal with |- context [match ?x with _ => _ end] => is_var x; destruct x end;
    rewrite ?IH; reflexivity.
Qed.
Definition kimg_cov1F (k : list kentry) (a : Z) : bool :=
  existsbL (fun K => match K with KImg lo hi => if (if (if lo <=? a then a <? hi else false) then img_lo BOTH <=? lo else false) then hi <=? img_hi BOTH else false | _ => false end) k.
Lemma kimg_cov1F_eq : forall k a, kimg_cov1F k a = kimg_cov1 k a.
Proof. intros. unfold kimg_cov1F, kimg_cov1. rewrite existsbL_eq. reflexivity. Qed.
Definition byte_okbF (k : list kentry) (a : Z) (b : byte) : bool :=
  match kbyteF k a with
  | Some b' => bv_eqb b' b
  | None => if kimg_cov1F k a then match seg_rom BSEGS (Z_to_bv 64 a) with Some b' => bv_eqb b' b | None => false end else false
  end.
Lemma byte_okbF_eq : forall k a b, byte_okbF k a b = byte_okb k a b.
Proof. intros. unfold byte_okbF, byte_okb. rewrite kbyteF_eq, kimg_cov1F_eq. reflexivity. Qed.
Fixpoint bytes_okbF (k : list kentry) (a : Z) (bs : list byte) : bool :=
  match bs with [] => true | b :: bs' => if byte_okbF k a b then bytes_okbF k (a + 1) bs' else false end.
Lemma bytes_okbF_eq : forall k bs a, bytes_okbF k a bs = bytes_okb k a bs.
Proof. intros k bs. induction bs as [|b bs IH]; intros a; [reflexivity|]. cbn [bytes_okbF bytes_okb]. rewrite byte_okbF_eq, IH. reflexivity. Qed.
Definition kzero_covrF (k : list kentry) (a n : Z) : bool :=
  existsbL (fun K => match K with
    | KZero (SA (ELit 0) b) (ELit m) => if (if (if b <=? a then a + n <=? b + m else false) then 0 <=? m else false) then m <? T64 else false
    | _ => false end) k.
Lemma kzero_covrF_eq : forall k a n, kzero_covrF k a n = kzero_covr k a n.
Proof. intros. unfold kzero_covrF, kzero_covr. rewrite existsbL_eq. reflexivity. Qed.
Definition kimg_covrF (k : list kentry) (a n : Z) : bool :=
  existsbL (fun K => match K with
    | KImg lo hi => if (if (if lo <=? a then a + n <=? hi else false) then img_lo BOTH <=? lo else false) then hi <=? img_hi BOTH else false
    | _ => false end) k.
Lemma kimg_covrF_eq : forall k a n, kimg_covrF k a n = kimg_covr k a n.
Proof. intros. unfold kimg_covrF, kimg_covr. rewrite existsbL_eq. reflexivity. Qed.
(* [comment removed for export] *)
Fixpoint zbytes_eqb (zs : list Z) (bs : list byte) : bool :=
  match zs, bs with
  | [], [] => true
  | z :: zs', b :: bs' => if Z.eqb z (bv_unsigned b) then zbytes_eqb zs' bs' else false
  | _, _ => false
  end.
Lemma zbytes_eqb_eq : forall zs bs, zbytes_eqb zs bs = true -> zs = map bv_unsigned bs.
Proof.
  induction zs as [|z zs IH]; intros [|b bs] H; cbn [zbytes_eqb] in H; try discriminate H; [reflexivity|].
  destruct (Z.eqb_spec z (bv_unsigned b)) as [->|]; [|discriminate H]. cbn [map]. rewrite (IH bs H). reflexivity.
Qed.
Lemma bytes_eqb_refl : forall bs, bytes_eqb bs bs = true.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn [bytes_eqb]. rewrite IH. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma map_bvu_inj : forall (xs ys : list byte), map bv_unsigned xs = map bv_unsigned ys -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; cbn [map] in H; try discriminate H; [reflexivity|].
  injection H as H1 H2. apply bv_eq in H1. rewrite H1, (IH ys H2). reflexivity.
Qed.
Definition img_cellF (a : Z) (bs : list byte) : bool :=
  match IMGF.img_bytesI BSEGS a (length bs) with Some zs => zbytes_eqb zs bs | None => false end.
Lemma img_cellF_sound : forall a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> img_cellF a bs = true ->
  match rdn BSEGS (fun _ => None) (Z_to_bv 64 a) (length bs) with Some bs' => bytes_eqb bs' bs | None => false end = true.
Proof.
  intros a bs Ha Hn H. unfold img_cellF in H. rewrite IMGF.img_bytesI_eq in H.
  destruct bs as [|b0 bs0]; [reflexivity|]. set (bs := b0 :: bs0) in *.
  assert (Hlt : a < 2 ^ 64) by (subst bs; cbn [length] in Hn; lia).
  assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; change (bv_modulus 64) with (2 ^ 64); lia).
  destruct (AX2.img_bytes BSEGS a (length bs)) as [zs|] eqn:E; [|discriminate H].
  apply zbytes_eqb_eq in H.
  destruct (AX2S.rdn_img BSEGS (fun _ => None) (length bs) (Z_to_bv 64 a) zs) as (bs' & Hr & Hm);
    [rewrite Hu; exact Hn | reflexivity | rewrite Hu; exact E |].
  rewrite Hr. rewrite H in Hm. apply map_bvu_inj in Hm. subst bs'. apply bytes_eqb_refl.
Qed.
Definition cell_okbF (k : list kentry) (a : Z) (bs : list byte) : bool :=
  let n := Z.of_nat (length bs) in
  if kzero_covrF k a n then forallb (fun b => bv_eqb b (Z_to_bv 8 0)) bs
  else if kimg_covrF k a n then img_cellF a bs
  else bytes_okbF k a bs.
Lemma cell_okbF_sound : forall k a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> cell_okbF k a bs = true -> cell_okb k a bs = true.
Proof.
  intros k a bs Ha Hn H. unfold cell_okbF in H. unfold cell_okb. cbv zeta in H |- *.
  rewrite kzero_covrF_eq, kimg_covrF_eq, bytes_okbF_eq in H.
  destruct (kzero_covr k a (Z.of_nat (length bs))); [exact H|].
  destruct (kimg_covr k a (Z.of_nat (length bs))); [|exact H].
  apply img_cellF_sound; assumption.
Qed.

(* [comment removed for export] *)
Definition win_tbl (k : list kentry) (ws : list (Z * Z)) : list (Z * Z * list kentry) :=
  map (fun w => (fst w, snd w, List.filter (touchW (fst w) (snd w)) k)) ws.
Definition cell_okb_tbl (k : list kentry) (tbl : list (Z * Z * list kentry)) (a : Z) (bs : list byte) : bool :=
  let n := Z.of_nat (length bs) in
  match find (fun e => (fst (fst e) <=? a) && (a + n <=? snd (fst e)) && (0 <? n))%bool tbl with
  | Some e => cell_okbF (snd e) a bs
  | None =>   (* [comment removed for export] *)
      if 0 <? n then cell_okbF (List.filter (touchW a (a + n)) k) a bs else cell_okbF k a bs
  end.
Lemma cell_okb_tbl_sound : forall k ws a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  cell_okb_tbl k (win_tbl k ws) a bs = true -> cell_okb k a bs = true.
Proof.
  intros k ws a bs Ha Hn H. unfold cell_okb_tbl in H. cbv zeta in H.
  destruct (find _ (win_tbl k ws)) as [e|] eqn:F.
  2:{ destruct (0 <? Z.of_nat (length bs)) eqn:E0; apply cell_okbF_sound in H; try assumption.
      apply Z.ltb_lt in E0. rewrite cell_okb_filter in H by lia. exact H. }
  apply cell_okbF_sound in H; try assumption.
  apply find_some in F. destruct F as [HI HP]. unfold win_tbl in HI. apply in_map_iff in HI. destruct HI as [w [<- _]].
  cbn [fst snd] in *. b2z. rewrite cell_okb_filter in H by assumption. exact H.
Qed.
Definition cells_okb_fast (cs : acs) (ws : list (Z * Z)) (l : list (Z * list byte)) : bool :=
  let k := kn cs in let tbl := win_tbl k ws in
  forallb (fun c => (0 <=? fst c) && (fst c + Z.of_nat (length (snd c)) <=? 2 ^ 64) && cell_okb_tbl k tbl (fst c) (snd c))%bool l.
Lemma cells_okb_fast_sound : forall cs ws l, cells_okb_fast cs ws l = true -> cells_okb cs l = true.
Proof.
  intros cs ws l H. unfold cells_okb_fast in H. cbv zeta in H. unfold cells_okb.
  rewrite forallb_forall in H |- *. intros c Hc. specialize (H c Hc).
  apply andb_true_iff in H. destruct H as [H HC]. rewrite H. cbn [andb]. apply andb_true_iff in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. exact (cell_okb_tbl_sound _ _ _ _ H1 H2 HC).
Qed.

(* [comment removed for export] *)
Fixpoint uniq_adj (ws : list (Z * Z)) (prev : Z) : list (Z * Z) :=
  match ws with [] => [] | w :: r => if fst w =? prev then uniq_adj r prev else w :: uniq_adj r (fst w) end.
Definition wins (S : Z) (l : list (Z * list byte)) : list (Z * Z) :=
  uniq_adj (map (fun c => let p := fst c / S * S in (p, p + S)) l) (-1).

(* [comment removed for export] *)
Definition zrun_okb_tbl (k : list kentry) (tbl : list (Z * Z * list kentry)) (p : Z * nat) : bool :=
  let a := fst p in let n := Z.of_nat (snd p) in
  ((0 <=? a) && (a + n <=? 2 ^ 64) &&
   match find (fun e => (fst (fst e) <=? a) && (a + n <=? snd (fst e)) && (0 <? n))%bool tbl with
   | Some e => kzero_covrF (snd e) a n
   | None => kzero_covrF k a n
   end)%bool.
Lemma forallb_repeat : forall (A : Type) (f : A -> bool) x n, f x = true -> forallb f (repeat x n) = true.
Proof. intros A f x n H. induction n as [|n IH]; [reflexivity|]. cbn [repeat forallb]. rewrite H, IH. reflexivity. Qed.
Lemma zrun_cells : forall cs ws zl, forallb (zrun_okb_tbl (kn cs) (win_tbl (kn cs) ws)) zl = true ->
  cells_okb cs (map (fun p => (fst p, repeat (Z_to_bv 8 0) (snd p))) zl) = true.
Proof.
  intros cs ws zl H. unfold cells_okb. rewrite forallb_forall in H |- *. intros c Hc.
  apply in_map_iff in Hc. destruct Hc as [p [<- Hp]]. specialize (H p Hp). unfold zrun_okb_tbl in H. cbv zeta in H.
  cbn [fst snd]. rewrite repeat_length.
  apply andb_true_iff in H. destruct H as [H HZ]. rewrite H. cbn [andb].
  assert (KZ : kzero_covr (kn cs) (fst p) (Z.of_nat (snd p)) = true).
  { destruct (find _ (win_tbl (kn cs) ws)) as [e|] eqn:F; rewrite kzero_covrF_eq in HZ; [|exact HZ].
    apply find_some in F. destruct F as [HI HP]. unfold win_tbl in HI. apply in_map_iff in HI. destruct HI as [w [<- _]].
    cbn [fst snd] in *. b2z. rewrite kzero_covr_filter in HZ by assumption. exact HZ. }
  unfold cell_okb. cbv zeta. rewrite repeat_length, KZ. apply forallb_repeat. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma cells_okb_app : forall cs l1 l2, cells_okb cs (l1 ++ l2) = true -> cells_okb cs l1 = true /\ cells_okb cs l2 = true.
Proof. intros cs l1 l2 H. unfold cells_okb in H |- *. rewrite forallb_app in H. apply andb_true_iff in H. exact H. Qed.
Lemma cells_okb_app_intro : forall cs l1 l2, cells_okb cs l1 = true -> cells_okb cs l2 = true -> cells_okb cs (l1 ++ l2) = true.
Proof. intros cs l1 l2 H1 H2. unfold cells_okb in H1, H2 |- *. rewrite forallb_app, H1, H2. reflexivity. Qed.

(* [comment removed for export] *)
Definition chk_g (cs : acs) (clsA : bool) (ws : list (Z * Z)) (l : list (Z * list byte)) (zl : list (Z * nat)) : bool :=
  (cells_okb_fast cs ws l && forallb (zrun_okb_tbl (kn cs) (win_tbl (kn cs) ws)) zl && (0 <=? a_eager cs) && (a_eager cs <=? 2^25)
   && (if clsA then khas cs (KRange (EVar 5) 1546 524277)
                    && khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (pg 5) 0) (ELit 8192))
       else true))%bool.
Definition ghA (cs : acs) : Prop :=
  khas cs (KRange (EVar 5) 1546 524277) = true
  /\ khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (pg 5) 0) (ELit 8192)) = true.
Lemma chk_g_sound : forall cs clsA ws l zl, chk_g cs clsA ws l zl = true ->
  cells_okb cs l = true /\ cells_okb cs (map (fun p => (fst p, repeat (Z_to_bv 8 0) (snd p))) zl) = true
  /\ 0 <= a_eager cs <= 2^25 /\ (clsA = true -> ghA cs).
Proof.
  intros cs clsA ws l zl H. unfold chk_g in H. rewrite !andb_true_iff in H. destruct H as [[[[H1 HZ] H2] H3] H4].
  apply cells_okb_fast_sound in H1. apply zrun_cells in HZ. apply Z.leb_le in H2. apply Z.leb_le in H3.
  split; [exact H1|]. split; [exact HZ|]. split; [lia|].
  intros ->. apply andb_true_iff in H4. exact H4.
Qed.
Lemma consts_split : cl_consts LPA = pa_cells ++ pa_gshadow ++ pa_zshadow.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma chk_cells_of : forall cs clsA ws, chk_g cs clsA ws (A0_CELLS ++ pa_cells ++ pa_gshadow) pa_zero_shadow = true ->
  cells_okb cs A0_CELLS = true /\ cells_okb cs (cl_consts LPA) = true /\ 0 <= a_eager cs <= 2^25 /\ (clsA = true -> ghA cs).
Proof.
  intros cs clsA ws H. destruct (chk_g_sound _ _ _ _ _ H) as (C1 & CZ & EG & G).
  destruct (cells_okb_app _ _ _ C1) as [CA CB]. destruct (cells_okb_app _ _ _ CB) as [CP CG].
  split; [exact CA|]. split; [|split; [exact EG|exact G]].
  rewrite consts_split. apply cells_okb_app_intro; [exact CP|]. apply cells_okb_app_intro; [exact CG|exact CZ].
Qed.
(* [comment removed for export] *)
Definition WS1 : list (Z * Z) := Eval vm_compute in wins 256 ((A0_CELLS ++ pa_cells ++ pa_gshadow) ++ map (fun p => (fst p, @nil byte)) pa_zero_shadow).
Lemma chk_1 : chk_g HS_both2_1 true WS1 (A0_CELLS ++ pa_cells ++ pa_gshadow) pa_zero_shadow = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma chk_2 : chk_g HS_both2_2 true WS1 (A0_CELLS ++ pa_cells ++ pa_gshadow) pa_zero_shadow = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma chk_3 : chk_g HS_both2b_1 false WS1 (A0_CELLS ++ pa_cells ++ pa_gshadow) pa_zero_shadow = true. Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma chk_4 : chk_g HS_both2b_2 false WS1 (A0_CELLS ++ pa_cells ++ pa_gshadow) pa_zero_shadow = true. Proof. vm_cast_no_check (eq_refl true). Qed.

Section Main.
  Context {Clg : Ceiling.Ceiling}.
  Variable sp : word.
  Hypothesis HCEIL : Ceiling.alloc_ceiling = bv_unsigned sp - 0x800000.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Context {BL : AsanInit.BootLim}.   (* [comment removed for export] *)
  Hypothesis HLIM : AInv.TLIM_MIN <= (@AsanInit.blim BL).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition P_of (E : env) (cs : acs) (model : Model) : aplace := P sp argv envp cs E model.

  (* [comment removed for export] *)
  Lemma a0_raw_of_cs : forall cs gh (k1 : list Z) E R FULL model,
    cs_ok BSEGS BOTH (@AsanInit.blim BL) (SINV0 BPH sp rdraw brk0 argv envp uid hw) (argH0 BPH sp rdraw argv envp uid hw) fs E cs R FULL model ->
    a0k cs -> a0s cs gh -> ((gh = A0_GHOST_A /\ ghA cs) \/ gh = A0_GHOST_B) -> 0 <= a_eager cs <= 2^25 ->
    cells_okb cs A0_CELLS = true -> a0kd cs k1 -> In k1 pa_dkeys -> cells_okb cs (cl_consts LPA) = true ->
    a0_raw (P_of E cs model) k1 (bv_unsigned sp) FULL model.
  Proof.
    intros cs gh k1 E R FULL model CS AK ASS GH EAG CC KD HK1 CCL.
    assert (GH' : (gh = A0_GHOST_A /\ khas cs (KRange (EVar 5) 1546 524277) = true
                   /\ khas cs (KDisj (SA (ELit 2147446784) 0) (ELit 17592186048512) (SA (pg 5) 0) (ELit 8192)) = true)
                  \/ gh = A0_GHOST_B) by (unfold ghA in GH; tauto).
    pose proof (a0_pre_of_cs sp HCEIL rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit HLIM cs E R FULL model CS AK gh ASS GH' EAG CC k1 KD HK1 CCL) as Q.
    destruct Q as [Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10 Y11 Y12 Y13 Y14 Y15 Y16 Y17 Y18 Y19 X1 X2 X3 X4 X5 X6 X7 X8 Y20 Y21 Y22 Y23 Y24 Y25 Y26].
    unfold P_of. constructor.
    all: first [ assumption | reflexivity
               | (* [comment removed for export] *)
                 unfold AInv.wf_extra; exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj X7 X8))))))) ].
  Qed.

  Theorem a0_raw_1 : forall E R FULL model,
    cs_ok BSEGS BOTH (@AsanInit.blim BL) (SINV0 BPH sp rdraw brk0 argv envp uid hw) (argH0 BPH sp rdraw argv envp uid hw) fs E HS_both2_1 R FULL model ->
    a0_raw (P_of E HS_both2_1 model) K1_1 (bv_unsigned sp) FULL model.
  Proof. intros E R FULL model HC. destruct (chk_cells_of _ _ _ chk_1) as (C1 & C2 & EG & G).
         exact (a0_raw_of_cs _ _ _ E R FULL model HC a0k_1 a0s_1 (or_introl (conj eq_refl (G eq_refl))) EG C1 a0kd_s1 pa_dkeys_start2 C2). Qed.
  Theorem a0_raw_2 : forall E R FULL model,
    cs_ok BSEGS BOTH (@AsanInit.blim BL) (SINV0 BPH sp rdraw brk0 argv envp uid hw) (argH0 BPH sp rdraw argv envp uid hw) fs E HS_both2_2 R FULL model ->
    a0_raw (P_of E HS_both2_2 model) K1_2 (bv_unsigned sp) FULL model.
  Proof. intros E R FULL model HC. destruct (chk_cells_of _ _ _ chk_2) as (C1 & C2 & EG & G).
         exact (a0_raw_of_cs _ _ _ E R FULL model HC a0k_2 a0s_2 (or_introl (conj eq_refl (G eq_refl))) EG C1 a0kd_s2 pa_dkeys_start1 C2). Qed.
  Theorem a0_raw_3 : forall E R FULL model,
    cs_ok BSEGS BOTH (@AsanInit.blim BL) (SINV0 BPH sp rdraw brk0 argv envp uid hw) (argH0 BPH sp rdraw argv envp uid hw) fs E HS_both2b_1 R FULL model ->
    a0_raw (P_of E HS_both2b_1 model) K1_1 (bv_unsigned sp) FULL model.
  Proof. intros E R FULL model HC. destruct (chk_cells_of _ _ _ chk_3) as (C1 & C2 & EG & G).
         exact (a0_raw_of_cs _ _ _ E R FULL model HC a0k_3 a0s_3 (or_intror eq_refl) EG C1 a0kd_s3 pa_dkeys_start2 C2). Qed.
  Theorem a0_raw_4 : forall E R FULL model,
    cs_ok BSEGS BOTH (@AsanInit.blim BL) (SINV0 BPH sp rdraw brk0 argv envp uid hw) (argH0 BPH sp rdraw argv envp uid hw) fs E HS_both2b_2 R FULL model ->
    a0_raw (P_of E HS_both2b_2 model) K1_2 (bv_unsigned sp) FULL model.
  Proof. intros E R FULL model HC. destruct (chk_cells_of _ _ _ chk_4) as (C1 & C2 & EG & G).
         exact (a0_raw_of_cs _ _ _ E R FULL model HC a0k_4 a0s_4 (or_intror eq_refl) EG C1 a0kd_s4 pa_dkeys_start1 C2). Qed.
End Main.
End Bothvij.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AxSyioe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanz3l OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanPlan.Asanfbz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Asanqlm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothny9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.AsanInit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Starr0h OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Stargqr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothgt0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bothrgj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Mwrv.BothA0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Mwrv.Bothvij.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Ey6n DA_Eg3i DA_Cells DA_Ldix DA_Entry DA_Mib4 DA_Inv DA_Main DA_Am90.

Module DA_Ekdk.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA RA_m7de.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AGlofzw ARtStmts ARt_png.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Ey6n DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition PS_ENTRY : Z := 0x59c74.
Definition PS_FRAME : Z := 64.
Definition META_SH : Z := 0x8000dac0.   (* [comment removed for export] *)

Definition poison_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (0x8000dac0, 0x8000dac0 + 2016)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' 0x8000dac0 [CB 2016 (repeat (Z_to_bv 8 0) 2016)].

Lemma ro_cells_cons_split : forall m A c cs,
  ro_cells rsegs m A (c :: cs) -> ro_cells rsegs m A [c] /\ ro_cells rsegs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs [WF BA]. cbn [cells_wf] in WF. destruct WF as [WF1 WF2].
  cbn [cells_bytes] in BA. apply bytes_at_app in BA. destruct BA as [BA1 BA2].
  rewrite (cbytes_length c WF1) in BA2.
  split; split; cbn [cells_wf cells_bytes]; try tauto. rewrite app_nil_r. exact BA1.
Qed.

Section Poison.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : lo + 64 <= bv_unsigned sp.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPHI : bv_unsigned sp <= 2^47.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis CO : dtor_consts m.
  Hypothesis A0 : a0 = Z_to_bv 64 GMETA.
  Hypothesis A1 : a1 = Z_to_bv 64 16128.
  Hypothesis A2 : a2 = Z_to_bv 64 0.
  Hypothesis SH : rw_cells rsegs m 0x8000dac0 [CB 2016 junk0].

  (* [comment removed for export] *)
  Lemma poison_consts_of_dtor : poison_consts m.
  Proof.
    destruct CO as (Cgot1 & Cgot2 & Cpsz & Cgot3 & Crep & Cthr & Cbase & Cinit & Ccan & Creal & Cmem & Ctab).
    apply ro_cells_cons_split in Cgot3. destruct Cgot3 as [G38 Cgot3]. 
    apply ro_cells_cons_split in Cgot3. destruct Cgot3 as [G40 Cgot3]. 
    apply ro_cells_cons_split in Cgot3. destruct Cgot3 as [G48 Cgot3]. 
    apply ro_cells_cons_split in Cgot3. destruct Cgot3 as [G50 Cgot3]. 
    apply ro_cells_cons_split in Cgot3. destruct Cgot3 as [G58 Cgot3]. 
    apply ro_cells_cons_split in Cgot3. destruct Cgot3 as [G60 G68]. 
    repeat match goal with H : ro_cells _ _ (?a + Z.of_nat ?k) _ |- _ =>
      let v := eval cbv in (a + Z.of_nat k) in change (a + Z.of_nat k) with v in H end.
    unfold poison_consts. change (0x1466e8 + 120) with 0x146760.
    unfold kShadowOffset, kHighMemEnd.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; assumption.
  Qed.

  Lemma poison_spec :
    evt rsegs (poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PS_ENTRY) fc None m (seg_rom rsegs)).
  Proof.
    pose proof poison_consts_of_dtor as PC.
    assert (SH' : rw_cells rsegs m (sh GMETA) [CB (Z.to_nat (16128 / 8)) junk0]) by exact SH.
    eapply evt_mono.
    - eapply (poison_ok ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                GMETA 16128 0 lo junk0 MI ST ltac:(lia) CEIL A0 A1 A2);
        [ reflexivity | reflexivity | lia
        | left; unfold GMETA, kLowShadowMapBeg, Asanljo.kLowShadowMapBeg; lia
        | unfold GMETA; lia | lia | intros _; reflexivity | exact PC | exact SH' | exact RA ].
    - intros ms' POST. unfold ARtStmts.poison_post in POST.
      (first [ dex16 POST as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m'; dand6 POST as -> MU WM MI' ST' BA | dand22 POST as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MU WM MI' ST' BA | destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & BA) ]).
      unfold poison_post. hot_eexists_k16. split; [reflexivity|].
      change (sh GMETA) with 0x8000dac0 in MU, BA. change (16128 / 8) with 2016 in MU, BA. change (Z.to_nat 2016) with 2016%nat in BA.
      split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
      destruct SH as [[WF _] WR]. split; [split|].
      + cbn [cells_wf cell_wf]. rewrite repeat_length. split; [reflexivity|exact I].
      + cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BA.
      + eapply wr_at_transport; [exact WR | exact WM].
  Qed.
End Poison.
End DA_Ekdk.

Module DA_Ehtc.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA RA_m7de.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AGlofzw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Ey6n DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_E4z1.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ey6n OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Mwrv.DA_Ekdk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_E4z1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Lemma rw_cells_app_inv : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) -> rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] Hw]. apply cells_wf_app in Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  rewrite cells_size_app, Nat2Z.inj_add in Hw. (first [ dand3 Hw as Ha Hl Hw | destruct Hw as (Ha & Hl & Hw) ]).
  split; (split; [split; assumption|]); (split; [lia|]); (split; [lia|]); intros i Hi.
  - apply Hw. lia.
  - replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Hw. lia.
Qed.

(* [comment removed for export] *)
Lemma gtab_odrs_in : forallb (fun r => negb (g_has_odr r) || existsb (Z.eqb (g_odr r)) gtab_odrs)%bool gtab = true.
Proof. vm_compute. reflexivity. Qed.

Lemma godrs_of_cells : forall m b1 b2 b3 b4,
  rw_cells rsegs m ODR_A [C1 b1; C1 b2] -> rw_cells rsegs m ODR_B [C1 b3; C1 b4] -> godrs m gtab.
Proof.
  intros m b1 b2 b3 b4 HA HB.
  apply (rw_cells_app_inv m ODR_A [C1 b1] [C1 b2]) in HA as [A0 A1].
  apply (rw_cells_app_inv m ODR_B [C1 b3] [C1 b4]) in HB as [B0 B1']. unfold ODR_A, ODR_B in *.
  change (6189696 + Z.of_nat (cells_size [C1 b1])) with 6189697 in A1. change (6189760 + Z.of_nat (cells_size [C1 b3])) with 6189761 in B1'.
  unfold godrs. apply Forall_forall. intros r Hr Ho.
  pose proof (proj1 (forallb_forall _ _) gtab_odrs_in r Hr) as IN. cbn beta in IN. rewrite Ho in IN. cbn [negb orb] in IN.
  unfold gtab_odrs in IN. cbn [existsb] in IN. rewrite Bool.orb_false_r in IN.
  repeat (apply Bool.orb_prop in IN; destruct IN as [IN|IN]); apply Z.eqb_eq in IN; rewrite IN.
  - exists b4. exact B1'.
  - exists b1. exact A0.
  - exists b2. exact A1.
  - exists b3. exact B0.
Qed.

(* [comment removed for export] *)

Lemma gtab_all_ok : Forall grec_ok gtab.
Proof. apply Forall_forall. intros r Hr. apply grec_ok_of_b. exact (proj1 (forallb_forall _ _) gtab_ok r Hr). Qed.

Lemma gshadows_transport_img_stk : forall W m m' bss, munch W m m' -> wmono rsegs m m' ->
  (forall A n, 0x7fffa000 <= A -> A + n <= 0x800c8c00 -> disjoint_from W A n) ->
  gshadows m gtab bss -> gshadows m' gtab bss.
Proof.
  intros W m m' bss MU WM HD GS. eapply gshadows_transport; [exact MU | exact WM | | exact gtab_all_ok | exact GS].
  apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) gtab_all_ok r Hr) as OK.
  unfold grec_ok, IMGHI in OK. apply HD; unfold gsh; Z.div_mod_to_equations; lia.
Qed.

Section Dtor.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (bss : list (list byte)) (b1 b2 b3 b4 : byte) (junk0 : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : lo + DTOR_FRAME <= bv_unsigned sp.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPHI : bv_unsigned sp <= 2^47.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis CO : dtor_consts m.
  Hypothesis FLAG : rw_cells rsegs m ELF_FLAG [C8 (Z_to_bv 64 1)].
  Hypothesis MUX : rw_cells rsegs m MU_GLOBALS [C8 (Z_to_bv 64 0)].
  Hypothesis ODA : rw_cells rsegs m ODR_A [C1 b1; C1 b2].
  Hypothesis ODB : rw_cells rsegs m ODR_B [C1 b3; C1 b4].
  Hypothesis GS : gshadows m gtab bss.
  Hypothesis MSH : rw_cells rsegs m (gsh GMETA) [CB 2016 junk0].

  #[using="MSH GS ODB ODA MUX FLAG CO SPHI CEIL LO ST MI junk0 b4 b3 b2 b1 bss Clg"] Lemma dtor_walk :
    evt rsegs (dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DTOR_ENTRY) fc None m (seg_rom rsegs)).
  Proof.
    unfold DTOR_ENTRY. unfold DTOR_FRAME in LO. unfold ELF_FLAG in FLAG. unfold MU_GLOBALS in MUX. unfold ODR_A in ODA. unfold ODR_B in ODB.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    pose proof CO as CO'. (first [ dand12 CO' as Cgot1 Cgot2 Cpsz Cgot3 Crep Cthr Cbase Cinit Ccan Creal Cmem Ctab | destruct CO' as (Cgot1 & Cgot2 & Cpsz & Cgot3 & Crep & Cthr & Cbase & Cinit & Ccan & Creal & Cmem & Ctab) ]).
    unfold GMETA, GCOUNT in Cgot1. change (710144 + 64 * Z.of_nat 252) with 726272 in Cgot1.
    change (gsh GMETA) with 0x8000dac0 in MSH. clear Ctab.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp); (0xb2470, 0xb2470 + 8)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 16%nat ST.
    run_to 0x45884. at_pc 0x45884.
    carve_frame 16%nat ST.
    run_to 0x4524c. at_pc 0x4524c.
    carve_frame 176%nat ST.
    run_to 0x45408. at_pc 0x45408.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (GS1 : gshadows mc gtab bss)
        by (eapply (gshadows_transport_img_stk _ m mc bss MU WM); [| exact GS]; intros A n HA HB; cbn [disjoint_from]; lia);
      pose proof (godrs_of_cells mc b1 b2 b3 b4 ODA ODB) as GO1;
      assert (Ctab1 : ro_cells rsegs mc GMETA (gtab_cells gtab))
        by (destruct CO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ctab); eapply ro_cells_transport; [exact Ctab | exact MU |];
            rewrite gtab_cells_size, gtab_length; unfold GMETA, GCOUNT; cbn [disjoint_from]; lia)
    end.
    apply (munch_weaken _ (dtor_W (bv_unsigned sp))) in MU.
    2:{ unfold sub_fp, dtor_W, DTOR_FRAME, ELF_FLAG, MU_GLOBALS, LOWSH_LO, LOWSH_HI, ODRLO, ODRHI. cbn [outside]. intros x Hx. lia. }
    unfold dtor_W, DTOR_FRAME, ELF_FLAG, MU_GLOBALS, LOWSH_LO, LOWSH_HI, ODRLO, ODRHI in MU.
    call (unreg_loop gtab [] bss).
    1:{ reflexivity. }
    1:{ intros H. pose proof gtab_length as L. rewrite H in L. discriminate L. }
    1:{ assumption. }
    1:{ exact (conj Crep (conj Cthr (conj Cbase (conj Cinit (conj Ccan Creal))))). }
    1: reflexivity. 1: reflexivity.
    1:{ cbn [length Z.of_nat]. unfold GMETA. reflexivity. }
    1: reflexivity. 1: reflexivity. 1: reflexivity.
    1:{ rewrite gtab_length. reflexivity. }
    1:{ cbn [length Z.of_nat]. rewrite Z.mul_0_r, Z.add_0_r. exact Ctab1. }
    1:{ exact GS1. }
    1:{ exact GO1. }
    clear GS1 GO1.
    (* [comment removed for export] *)
    run_to 0x59c74. at_pc 0x59c74.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (Ctab2 : ro_cells rsegs mc GMETA (gtab_cells gtab))
        by (destruct CO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ctab); eapply ro_cells_transport; [exact Ctab | exact MU |];
            rewrite gtab_cells_size, gtab_length; unfold GMETA, GCOUNT; cbn [disjoint_from]; lia)
    end.
    callz poison_spec.
    1:{ assumption. }
    1:{ rewrite unsigned_lit by lia. exact ST. }
    1:{ rewrite unsigned_lit by lia. lia. }
    1:{ exact CEIL. }
    1:{ rewrite unsigned_lit by lia. reflexivity. }
    1:{ exact (conj Cgot1 (conj Cgot2 (conj Cpsz (conj Cgot3 (conj Crep (conj Cthr (conj Cbase (conj Cinit (conj Ccan (conj Creal (conj Cmem Ctab2))))))))))). }
    1:{ unfold GMETA. reflexivity. }
    1: reflexivity. 1: reflexivity.
    1:{ exact MSH. }
    (* [comment removed for export] *)
    run_to 0x45718. at_pc 0x45718.
    (* [comment removed for export] *)
    azstep. at_pc 0x458bc. run_to 0x458cc. azstep. at_pc 0x87668. azstep. azstep. azstep.
    release_frame FR1 PC (bv_unsigned sp + -32). release_frame FR0 PC (bv_unsigned sp + -16). release_frame FR PC (bv_unsigned sp).
    unfold dtor_post. finish.
  Qed.
End Dtor.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem dtor_spec : dtor_spec_stmt.
Proof.
  unfold dtor_spec_stmt. intros. eapply dtor_walk; eassumption.
Qed.

End CEIL.
End DA_Ehtc.

Module DA_Ehwr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA RA_m7de.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AGlofzw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Tac DA_Ey6n DA_E4z1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Eg3i.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ey6n OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_E4z1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Mwrv.DA_Ehtc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Eg3i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition STDIO_EXIT : Z := 0x9de64.

(* [comment removed for export] *)
Definition W1 (usp : Z) : list (Z * Z) :=
  [(usp - 320, usp); (0x607e48, 0x607e48 + 4); (0x607c28, 0x607c28 + 24); (0xb1550, 0xb1550 + 1);
   (0xb1500, 0xb1500 + 8); (0xb2470, 0xb2470 + 8); (0x7fffa000, 0x800c8c00); (0x5e7280, 0x5e72c2)].

Definition part1_post (ra sp gp tp s0 a0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo tid : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 a0' m',
    ms' = MS (mkR (Z_to_bv 64 0x983e0) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 a0 s1 a0' a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 STDIO_EXIT) fc None m' (seg_rom rsegs)
    /\ munch (W1 (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp + -16)
    /\ rw_cells rsegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra].

Section Part1.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (tid : Z) (ini : Z) (fin : byte) (bss : list (list byte)) (b1 b2 b3 b4 : byte) (junk0 : list byte) (wp0 rp0 wp2 rp2 : word).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis TP : tp = Z_to_bv 64 TPV.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis LO : lo + EXIT_STACK <= bv_unsigned sp.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPHI : bv_unsigned sp <= 2^47.
  Hypothesis EC : exit_cells m tid ini fin bss b1 b2 b3 b4 junk0 wp0 rp0 wp2 rp2.

  #[using="EC SPHI CEIL LO ST TP MI rp2 wp2 rp0 wp0 junk0 b4 b3 b2 b1 bss fin Clg"] Lemma exit_part1 :
    evt rsegs (part1_post ra sp gp tp s0 a0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo tid m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 EXIT_ENTRY) fc None m (seg_rom rsegs)).
  Proof.
    destruct EC. subst tp. unfold EXIT_ENTRY, TPV. unfold EXIT_STACK in LO.
    unfold TID_CELL in ec_tid. unfold EXIT_LOCK in ec_lock. unfold ATEXIT in *. unfold TR_INCB, CALL_TRAMP, AEF_GUARD in *.   (* [comment removed for export] *) unfold NEED_LOCKS in ec_nlock. unfold COV_FLAG in ec_cov.
    lit_addrs.
    unfold ELF_FLAG in ec_flag. unfold MU_GLOBALS in ec_mux. unfold ODR_A in ec_odra. unfold ODR_B in ec_odrb. change (gsh GMETA) with 0x8000dac0 in ec_msh.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
    clear ec_ofl ec_uin ec_uout ec_uerr ec_in ec_err.
    (* [comment removed for export] *)
    pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (0x607e48, 0x607e48 + 4); (0x607c28, 0x607c28 + 24); (0xb1550, 0xb1550 + 1)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 16%nat ST.
    pose proof ec_dtor as CO. destruct CO as (Cgot1 & Cgot2 & Cpsz & Cgot3 & Crep & Cthr & Cbase & Cinit & Ccan & Creal & Cmem & _).
    destruct ec_ini as [Eini | Eini]; subst ini.
    - (* [comment removed for export] *)
      rewrite ?Z.add_0_r in ec_slot. rewrite ?Z.mul_0_l in ec_bf1, ec_ba1.
      run_to 0x983a8. rewrite (sx32_small tid) by lia. azstep. br_not_taken. run_to 0x98190. at_pc 0x98190.
      (* [comment removed for export] *)
      carve_frame 48%nat ST.
      run_to 0x983d8. at_pc 0x983d8.
      release_frame FR0 ST (bv_unsigned sp + -16).
      (* [comment removed for export] *)
      azstep. at_pc 0x98328. carve_frame 32%nat ST.
      run_to 0x35ef4. at_pc 0x35ef4.
      (* [comment removed for export] *)
      carve_frame 16%nat ST.
      run_to 0x98358. at_pc 0x98358.
      release_frame FR1 ST (bv_unsigned sp + -48).
      run_to 0x87644. at_pc 0x87644.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        assert (GS1 : gshadows mc gtab bss)
          by (eapply (gshadows_transport_img_stk _ m mc bss MU WM); [| exact ec_gsh]; intros A n HA HB; cbn [disjoint_from]; lia);
        assert (Ctab1 : ro_cells rsegs mc GMETA (gtab_cells gtab))
          by (destruct ec_dtor as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ctab); eapply ro_cells_transport; [exact Ctab | exact MU |];
              rewrite gtab_cells_size, gtab_length; unfold GMETA, GCOUNT; cbn [disjoint_from]; lia)
      end.
      apply (munch_weaken _ (W1 (bv_unsigned sp))) in MU.
      2:{ unfold sub_fp, W1. cbn [outside]. intros x Hx. lia. }
      unfold W1 in MU.
      callz dtor_spec.
      1:{ assumption. }
      1:{ rewrite unsigned_lit by lia. exact ST. }
      1:{ rewrite unsigned_lit by lia. unfold DTOR_FRAME. lia. }
      1:{ exact CEIL. }
      1:{ rewrite unsigned_lit by lia. lia. }
      1:{ rewrite unsigned_lit by lia. reflexivity. }
      1:{ exact (conj Cgot1 (conj Cgot2 (conj Cpsz (conj Cgot3 (conj Crep (conj Cthr (conj Cbase (conj Cinit (conj Ccan (conj Creal (conj Cmem Ctab1))))))))))). }
      1:{ exact ec_flag. }
      1:{ exact ec_mux. }
      1:{ exact ec_odra. }
      1:{ exact ec_odrb. }
      1:{ exact GS1. }
      1:{ exact ec_msh. }
      run_to 0x9de64. at_pc 0x9de64.
      release_frame FR0 PC (bv_unsigned sp + -16).
      unfold part1_post, STDIO_EXIT. finish.
    - (* [comment removed for export] *)
      change (1 + 1) with 2 in ec_slot. rewrite ?Z.mul_1_l in ec_bf1, ec_ba1.
      run_to 0x983a8. rewrite (sx32_small tid) by lia. azstep. br_not_taken. run_to 0x98190. at_pc 0x98190.
      (* [comment removed for export] *)
      carve_frame 48%nat ST.
      run_to 0x983d8. at_pc 0x983d8.
      release_frame FR0 ST (bv_unsigned sp + -16).
      (* [comment removed for export] *)
      azstep. at_pc 0x98328. carve_frame 32%nat ST.
      run_to 0x35ef4. at_pc 0x35ef4.
      (* [comment removed for export] *)
      carve_frame 16%nat ST.
      run_to 0x98358. at_pc 0x98358.
      release_frame FR1 ST (bv_unsigned sp + -48).
      run_to 0x87644. at_pc 0x87644.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        assert (GS1 : gshadows mc gtab bss)
          by (eapply (gshadows_transport_img_stk _ m mc bss MU WM); [| exact ec_gsh]; intros A n HA HB; cbn [disjoint_from]; lia);
        assert (Ctab1 : ro_cells rsegs mc GMETA (gtab_cells gtab))
          by (destruct ec_dtor as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ctab); eapply ro_cells_transport; [exact Ctab | exact MU |];
              rewrite gtab_cells_size, gtab_length; unfold GMETA, GCOUNT; cbn [disjoint_from]; lia)
      end.
      apply (munch_weaken _ (W1 (bv_unsigned sp))) in MU.
      2:{ unfold sub_fp, W1. cbn [outside]. intros x Hx. lia. }
      unfold W1 in MU.
      callz dtor_spec.
      1:{ assumption. }
      1:{ rewrite unsigned_lit by lia. exact ST. }
      1:{ rewrite unsigned_lit by lia. unfold DTOR_FRAME. lia. }
      1:{ exact CEIL. }
      1:{ rewrite unsigned_lit by lia. lia. }
      1:{ rewrite unsigned_lit by lia. reflexivity. }
      1:{ exact (conj Cgot1 (conj Cgot2 (conj Cpsz (conj Cgot3 (conj Crep (conj Cthr (conj Cbase (conj Cinit (conj Ccan (conj Creal (conj Cmem Ctab1))))))))))). }
      1:{ exact ec_flag. }
      1:{ exact ec_mux. }
      1:{ exact ec_odra. }
      1:{ exact ec_odrb. }
      1:{ exact GS1. }
      1:{ exact ec_msh. }
      run_to 0x9de64. at_pc 0x9de64.
      release_frame FR0 PC (bv_unsigned sp + -16).
      unfold part1_post, STDIO_EXIT. finish.
  Qed.
End Part1.
End DA_Ehwr.

Module DA_Exit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec RelSpec CatSim LibWbxd MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import Divembc SpinAlg Hull Restrict Lazyiq4 EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AGlofzw.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require DA_W756.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_W756.DA_Erys.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_Tac DA_Ey6n DA_Eg3i.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_En8l.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ey6n OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Mwrv.DA_Ehwr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_En8l.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma pa_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma hclean_mapped_in_hull : forall A (m : word -> option byte) (x : word),
  (forall a, hidc A a = true -> m a = None) -> m x <> None -> in_hullb A (bv_unsigned x) = true.
Proof.
  intros A m x Hc Hx. destruct (hidc A x) eqn:E.
  - exfalso. apply Hx. apply Hc. exact E.
  - unfold hidc in E. apply Bool.negb_false_iff in E. exact E.
Qed.

(* [comment removed for export] *)
Ltac xa_unfold_segs :=
  unfold rsegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments;
  cbn [find_segment];
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_000)) with 0x25000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_001)) with 0x35000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_001)) with 0x73000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_002)) with 0xa8000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_002)) with 0x2000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_003)) with 0xaa000%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_003)) with 0x560000%Z by (vm_compute; reflexivity).

Lemma xa_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x60a000 <= z) -> find_segment rsegs z n = None.
Proof.
  intros z n Hn Hz. xa_unfold_segs.
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x25000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0x35000 z); destruct (Z.leb_spec0 (z + n) (0x35000 + 0x73000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xa8000 z); destruct (Z.leb_spec0 (z + n) (0xa8000 + 0x2000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xaa000 z); destruct (Z.leb_spec0 (z + n) (0xaa000 + 0x560000)); cbn [andb]; try lia.
  all: reflexivity.
Qed.

Lemma xa_wview_overlay : forall m (x : word), (bv_unsigned x + 1 <= 0x10000 \/ 0x60a000 <= bv_unsigned x) -> wview rsegs m x = m x.
Proof. intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite xa_find_segment_none by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma image_rw_in_hull : forall A (x : word),
  H_off_segments rsegs (hidc A) -> 0xaa000 <= bv_unsigned x -> bv_unsigned x + 1 <= 0x60a000 -> in_hullb A (bv_unsigned x) = true.
Proof.
  intros A x HA Hlo Hhi. destruct (hidc A x) eqn:E.
  - exfalso. pose proof (HA x E) as Hf. revert Hf. xa_unfold_segs.
    destruct (Z.leb_spec0 0x10000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0x10000 + 0x25000)); cbn [andb]; try lia; try discriminate.
    all: destruct (Z.leb_spec0 0x35000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0x35000 + 0x73000)); cbn [andb]; try lia; try discriminate.
    all: destruct (Z.leb_spec0 0xa8000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0xa8000 + 0x2000)); cbn [andb]; try lia; try discriminate.
    all: destruct (Z.leb_spec0 0xaa000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0xaa000 + 0x560000)); cbn [andb]; try lia; try discriminate.
  - unfold hidc in E. apply Bool.negb_false_iff in E. exact E.
Qed.

(* [comment removed for export] *)
Lemma rdn_cell_C8 : forall m A cs k v,
  rw_cells rsegs m A cs -> cell_at cs k = Some (C8 v) ->
  rdn rsegs m (wa (A + Z.of_nat k)) 8%nat = Some (word_to_le_bytes 8 v).
Proof.
  intros m A cs k v H Hk. rewrite <- ov_rdn. exact (rw_cells_read_at rsegs m A cs k (C8 v) 8%nat _ H Hk eq_refl eq_refl).
Qed.

(* [comment removed for export] *)
Lemma rw_cells_mapped_off : forall m A cs i,
  rw_cells rsegs m A cs -> 0 <= i < Z.of_nat (cells_size cs) -> (A + Z.of_nat (cells_size cs) <= 0x10000 \/ 0x60a000 <= A) ->
  m (wa (A + i)) <> None.
Proof.
  intros m A cs i [[Hwf Hb] (Ha & Hl & Hw)] Hi Hoff. specialize (Hw i Hi).
  rewrite xa_wview_overlay in Hw; [exact Hw|]. rewrite wa_unsigned by lia. lia.
Qed.

Lemma rw_cells_munrestrict : forall Hh full m a cs,
  zrange_visible Hh a (Z.of_nat (cells_size cs)) -> rw_cells rsegs m a cs -> rw_cells rsegs (munrestrict Hh full m) a cs.
Proof.
  intros Hh full m a cs Hv [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - apply (proj1 (bytes_at_munrestrict rsegs Hh full m a _ ltac:(rewrite cells_bytes_length by exact Hwf; exact Hv))). exact Hb.
  - apply (proj1 (wr_at_munrestrict rsegs Hh full m a _ Hv)). exact Hw.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_visible_off : forall A m a cs,
  (forall x, hidc A x = true -> m x = None) ->
  rw_cells rsegs m a cs -> (a + Z.of_nat (cells_size cs) <= 0x10000 \/ 0x60a000 <= a) ->
  zrange_visible (hidc A) a (Z.of_nat (cells_size cs)).
Proof.
  intros A m a cs Hcl H Hoff i Hi. destruct (hidc A (wa (a + i))) eqn:E; [|reflexivity].
  exfalso. exact (rw_cells_mapped_off m a cs i H Hi Hoff (Hcl _ E)).
Qed.

Lemma image_rw_visible : forall A a n,
  H_off_segments rsegs (hidc A) -> 0xaa000 <= a -> a + n <= 0x60a000 -> zrange_visible (hidc A) a n.
Proof.
  intros A a n HA Hlo Hhi i Hi. unfold hidc. apply Bool.negb_false_iff.
  apply image_rw_in_hull; [exact HA| rewrite wa_unsigned by lia; lia | rewrite wa_unsigned by lia; lia].
Qed.

Ltac lit_addrs_goal :=
  repeat match goal with
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  end.

Lemma t_exit_nil : forall code fs, t_exit code fs [].
Proof. intros. unfold t_exit, t_emit. left. exact I. Qed.

Section Exit.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model)
            (A AL : hull) (E : Z) (lo : Z)
            (tid : Z) (ini : Z) (fin : byte) (bss : list (list byte)) (b1 b2 b3 b4 : byte) (junk0 : list byte) (wp0 rp0 wp2 rp2 : word)
            (pending : list byte).
  Let Hd := hidc A.
  Let v := mrestrict Hd m.
  Hypothesis HA : H_off_segments rsegs Hd.
  Hypothesis HI : MInv A AL E md.
  Hypothesis Hh : m_halted md = None.
  Hypothesis MI : mem_inv rsegs v.
  Hypothesis TP : tp = Z_to_bv 64 TPV.
  Hypothesis ST : stk rsegs v lo (bv_unsigned sp).
  Hypothesis LO : lo + EXIT_STACK <= bv_unsigned sp.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPHI : bv_unsigned sp <= 2^47.
  Hypothesis EC : exit_cells v tid ini fin bss b1 b2 b3 b4 junk0 wp0 rp0 wp2 rp2.

  Let T (mo : Model) : TSet := t_emit (W 1 pending) (t_exit (bv_and a0 (Z_to_bv 64 255)) (m_fs mo)).

  (* [comment removed for export] *)
  Section Loop.
    Variables (sp2 : word) (wb wp : Z) (wend bufp bufsz rp1 canary : word).
    Hypothesis LO2 : lo + 304 <= bv_unsigned sp2.
    Hypothesis SPHI2 : bv_unsigned sp2 + 16 <= 2^47.
    (* [comment removed for export] *)
    Variable m1 : word -> option byte.
    Hypothesis SOUT1 : stdout_pending m1 wb wp wend bufp bufsz rp1 canary pending.

    #[using="SOUT1 m1 SPHI2 LO2 CEIL HA Clg"] Lemma flush_loop : forall (n : nat) (rem d : Z) (ra' t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' : word)
        (full m2 : word -> option byte) (j8 : list byte) (mo : Model),
      rem <= Z.of_nat n -> 1 <= rem -> 0 <= d -> d + rem = Z.of_nat (length pending) ->
      MInv A AL E mo -> m_halted mo = None -> m_fs mo = m_fs md ->
      fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
      (forall a, Hd a = true -> m2 a = None) ->
      mem_inv rsegs m2 -> stk rsegs m2 lo (bv_unsigned sp2 + -128) ->
      rw_cells rsegs m2 (bv_unsigned sp2 + -128) (wframe s1 s2 s3 s4 s5 s6 canary j8 (wb + d) rem) ->
      wcells sp2 a0 wp2 rp2 wb wp wend bufp bufsz rp1 canary pending m2 ->
      srealizes rsegs
        (mkCfg (wst sp2 gp tp s7 s8 s9 s10 s11 F fc ra' t0' t1' t2' a3' a4' a5' a6' (Z_to_bv 64 (bv_unsigned sp2 + -120)) t3' t4' t5' t6'
                    rem 0x9d994 (munrestrict Hd full m2)) mo)
        (t_emit (W 1 (skipn (Z.to_nat d) pending)) (t_exit (bv_and a0 (Z_to_bv 64 255)) (m_fs md))).
    Proof.
      induction n as [|n IH]; intros rem d ra' t0' t1' t2' a3' a4' a5' a6' t3' t4' t5' t6' full m2 j8 mo
        Hn R1 D0 DR HIo Hho Hfs Hfd Hcl MI2 ST2 FRW WC; [lia|].
      assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
      pose proof SOUT1 as SO. destruct SO. unfold STDOUT_BUF in sp_range.
      pose proof WC as WC'. (first [ dand14 WC' as FRE Wpos Wbase Wbuf Wfd Wrpos Wcan Wuerr We1 We2 We3 We4 We5 Wbytes | destruct WC' as (FRE & Wpos & Wbase & Wbuf & Wfd & Wrpos & Wcan & Wuerr & We1 & We2 & We3 & We4 & We5 & Wbytes) ]).
      (* [comment removed for export] *)
      unfold wst.
      eapply (srz_writev2_hull rsegs A AL E _ mo (Z_to_bv 64 66) 1 (Z_to_bv 64 (bv_unsigned sp2 + -120))
                (Z_to_bv 64 (wb + d)) (Z_to_bv 64 rem) (Z_to_bv 64 0) (skipn (Z.to_nat d) pending)
                (t_exit (bv_and a0 (Z_to_bv 64 255)) (m_fs md))).
      - reflexivity.
      - exact Hho.
      - reflexivity.
      - exact Hfd.
      - lia.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - (* [comment removed for export] *)
        assert (VF : zrange_visible Hd (bv_unsigned sp2 + -128) (Z.of_nat (cells_size (wframe s1 s2 s3 s4 s5 s6 canary j8 (wb + d) rem)))).
        { eapply rw_cells_visible_off; [exact Hcl | exact FRW | cbn [wframe cells_size csize Nat.add]; lia]. }
        pose proof (rw_cells_munrestrict Hd full m2 _ _ VF FRW) as FRWu. unfold wframe in FRWu.
        cbn [iov_array ms_mem].
        pose proof (rdn_cell_C8 _ _ _ 8 _ FRWu eq_refl) as R8. pose proof (rdn_cell_C8 _ _ _ 16 _ FRWu eq_refl) as R16.
        pose proof (rdn_cell_C8 _ _ _ 24 _ FRWu eq_refl) as R24. pose proof (rdn_cell_C8 _ _ _ 32 _ FRWu eq_refl) as R32.
        unfold wa in R8, R16, R24, R32. rewrite !unsigned_lit by lia.
        replace (bv_unsigned sp2 + -128 + Z.of_nat 8) with (bv_unsigned sp2 + -120) in R8 by lia.
        replace (bv_unsigned sp2 + -128 + Z.of_nat 16) with (bv_unsigned sp2 + -120 + 8) in R16 by lia.
        replace (bv_unsigned sp2 + -128 + Z.of_nat 24) with (bv_unsigned sp2 + -120 + 16) in R24 by lia.
        replace (bv_unsigned sp2 + -128 + Z.of_nat 32) with (bv_unsigned sp2 + -120 + 16 + 8) in R32 by lia.
        OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; rewrite ?unsigned_lit by lia; try lia.
      - (* [comment removed for export] *)
        cbn [ms_mem]. rewrite word_to_nat_Z by lia.
        assert (VB : zrange_visible Hd wb (Z.of_nat (length pending))) by (eapply image_rw_visible; [exact HA | lia | lia]).
        pose proof (proj1 (bytes_at_munrestrict rsegs Hd full m2 wb pending VB) Wbytes) as WBu.
        rewrite <- (firstn_all2 (n:=Z.to_nat rem) (skipn (Z.to_nat d) pending)) by (rewrite length_skipn; lia).
        replace (Z_to_bv 64 (wb + d)) with (wa (wb + Z.of_nat (Z.to_nat d))) by (unfold wa; f_equal; lia).
        eapply bytes_at_rdn; [exact WBu | lia].
      - rewrite unsigned_lit by lia. lia.
      - rewrite unsigned_lit by lia. unfold rw_bytes_max. lia.
      - rewrite unsigned_lit by lia. lia.
      - rewrite unsigned_lit by lia. unfold TASK_SIZE. lia.
      - rewrite ?unsigned_lit by lia. unfold TASK_SIZE. lia.
      - rewrite ?unsigned_lit by lia. unfold TASK_SIZE. lia.
      - exact HIo.
      - (* [comment removed for export] *)
        intros k Hk. apply (hclean_mapped_in_hull A m2); [exact Hcl|].
        replace (woff (Z_to_bv 64 (bv_unsigned sp2 + -120)) k) with (wa (bv_unsigned sp2 + -128 + (8 + Z.of_nat k))).
        2:{ unfold woff, wa. f_equal. rewrite unsigned_lit by lia. lia. }
        eapply rw_cells_mapped_off; [exact FRW | cbn [wframe cells_size csize Nat.add]; lia | cbn [wframe cells_size csize Nat.add]; lia].
      - (* [comment removed for export] *)
        intros k Hk. rewrite word_to_nat_Z in Hk by lia.
        apply (image_rw_in_hull A _ HA); rewrite woff_small by (rewrite unsigned_lit by lia; lia); rewrite unsigned_lit by lia; lia.
      - apply t_exit_nil.
      - (* [comment removed for export] *)
        intros k' mo' Hk1 Hk2 HIo' Hsame. rewrite length_skipn in Hk2.
        rewrite advance_set_gpr0_MSsvc. simp_regs.
        assert (Hho' : m_halted mo' = None) by (rewrite (same_but_materialized_halted _ _ Hsame); exact Hho).
        set (k := Z.of_nat k') in *.
        pose (QQ := fun ms' => (k = rem /\ done_post sp2 gp tp a0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m2 ms')
                            \/ (k < rem /\ more_post sp2 gp tp a0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo wp2 rp2 wb wp wend bufp bufsz rp1 canary pending
                                              (Z_to_bv 64 0x9d99c) t0' t1' t2' (Z_to_bv 64 (bv_unsigned sp2 + -120)) t3' t4' t5' t6' (wb + d) rem k j8 m2 ms')).
        eapply (srz_evt_restrict rsegs A HA pa_wx AL E QQ _ mo'); [exact HIo' | exact Hho' | |].
        { rewrite restrict_MS, mrestrict_munrestrict', (mrestrict_clean_id _ m2 Hcl).
          eapply evt_cut.
          { eapply writev_after2; [exact MI2 | lia | lia]. }
          intros ms3 P3. unfold after_post in P3. subst ms3.
          destruct (Z.eqb_spec k rem) as [Ek|Nk].
          - eapply evt_mono; [eapply writev_done; [exact LO2 | exact CEIL | exact MI2 | exact ST2 | exact FRW | exact WC] |].
            intros ms4 P4. left. split; [exact Ek | exact P4].
          - eapply evt_mono; [eapply (writev_more sp2 gp tp a0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 lo wp2 rp2 LO2 CEIL SPHI2
                                          wb wp wend bufp bufsz rp1 canary pending SOUT1);
                                 [exact MI2 | exact ST2 | exact FRW | exact WC | lia | lia | lia] |].
            intros ms4 P4. right. split; [lia | exact P4]. }
        intros msr mo2 HQ HIo2 Hsame2 Hcl2.
        destruct HQ as [[Ek P4] | [Nk P4]].
        + (* [comment removed for export] *)
          unfold done_post in P4. (first [ dex15 P4 as ra4 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 m4; dand4 P4 as -> MU4 WM4 MI4 | dand19 P4 as ra4 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 m4 -> MU4 WM4 MI4 | destruct P4 as (ra4 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & m4 & -> & MU4 & WM4 & MI4) ]).
          rewrite skipn_all2 by (rewrite length_skipn; lia).
          eapply srz_conseq; [| apply t_eq_sym; apply t_emit_nil_eq; apply t_exit_nil].
          rewrite unrestrict_MSsvc.
          replace (m_fs md) with (m_fs mo2).
          2:{ rewrite <- Hfs. pose proof (same_but_materialized_frame _ _ Hsame2) as X2. pose proof (same_but_materialized_frame _ _ Hsame) as X1.
              transitivity (m_fs mo'); [apply X2 | apply X1]. }
          lazymatch goal with |- srealizes _ (mkCfg ?msx _) _ =>
            change (srealizes rsegs (mkCfg msx mo2) (t_exit (bv_and (ms_gpr msx 0) (Z_to_bv 64 255)) (m_fs mo2)));
            apply (srz_exit rsegs msx mo2 (Z_to_bv 64 94)) end.
          * rewrite (same_but_materialized_halted _ _ Hsame2). exact Hho'.
          * reflexivity.
          * right. reflexivity.
        + (* [comment removed for export] *)
          unfold more_post in P4. (first [ dex5 P4 as y3 y4 y5 y6 m4; dand7 P4 as -> MU4 WM4 MI4 ST4 FRW4 WC4 | dand12 P4 as y3 y4 y5 y6 m4 -> MU4 WM4 MI4 ST4 FRW4 WC4 | destruct P4 as (y3 & y4 & y5 & y6 & m4 & -> & MU4 & WM4 & MI4 & ST4 & FRW4 & WC4) ]).
          unfold wst. rewrite unrestrict_MSsvc.
          rewrite skipn_skipn. replace (k' + Z.to_nat d)%nat with (Z.to_nat (d + k)) by lia.
          replace (wb + d + k) with (wb + (d + k)) in FRW4 by lia.
          pose proof (same_but_materialized_frame _ _ Hsame2) as X2. pose proof (same_but_materialized_frame _ _ Hsame) as X1.
          eapply (IH (rem - k) (d + k)); try eassumption; try lia.
          * rewrite (same_but_materialized_halted _ _ Hsame2). exact Hho'.
          * transitivity (m_fs mo'); [apply X2 | rewrite <- Hfs; apply X1].
          * replace (m_fds mo2) with (m_fds mo); [exact Hfd|]. symmetry. transitivity (m_fds mo'); [apply X2 | apply X1].
    Qed.

    #[using="SOUT1 m1 SPHI2 LO2 CEIL HA Clg"] Lemma flush_first : forall (rem d : Z) (ra' t0' t1' t2' a3' a4' a5' a6' s4' t3' t4' t5' t6' : word)
        (full m2 : word -> option byte) (j8 : list byte) (mo : Model),
      1 <= rem -> 0 <= d -> d + rem = Z.of_nat (length pending) ->
      MInv A AL E mo -> m_halted mo = None -> m_fs mo = m_fs md ->
      fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
      (forall a, Hd a = true -> m2 a = None) ->
      mem_inv rsegs m2 -> stk rsegs m2 lo (bv_unsigned sp2 + -128) ->
      rw_cells rsegs m2 (bv_unsigned sp2 + -128) (wframe s1 s2 s3 s4 s5 s6 canary j8 (wb + d) rem) ->
      wcells sp2 a0 wp2 rp2 wb wp wend bufp bufsz rp1 canary pending m2 ->
      srealizes rsegs
        (mkCfg (wst sp2 gp tp s7 s8 s9 s10 s11 F fc ra' t0' t1' t2' a3' a4' a5' a6' s4' t3' t4' t5' t6'
                    rem 0x9d90c (munrestrict Hd full m2)) mo)
        (t_emit (W 1 (skipn (Z.to_nat d) pending)) (t_exit (bv_and a0 (Z_to_bv 64 255)) (m_fs md))).
    Proof.
      intros rem d ra' t0' t1' t2' a3' a4' a5' a6' s4' t3' t4' t5' t6' full m2 j8 mo
        R1 D0 DR HIo Hho Hfs Hfd Hcl MI2 ST2 FRW WC.
      assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia).
      pose proof SOUT1 as SO. destruct SO. unfold STDOUT_BUF in sp_range.
      pose proof WC as WC'. (first [ dand14 WC' as FRE Wpos Wbase Wbuf Wfd Wrpos Wcan Wuerr We1 We2 We3 We4 We5 Wbytes | destruct WC' as (FRE & Wpos & Wbase & Wbuf & Wfd & Wrpos & Wcan & Wuerr & We1 & We2 & We3 & We4 & We5 & Wbytes) ]).
      (* [comment removed for export] *)
      unfold wst.
      eapply (srz_writev2_hull rsegs A AL E _ mo (Z_to_bv 64 66) 1 (Z_to_bv 64 (bv_unsigned sp2 + -120))
                (Z_to_bv 64 (wb + d)) (Z_to_bv 64 rem) (Z_to_bv 64 0) (skipn (Z.to_nat d) pending)
                (t_exit (bv_and a0 (Z_to_bv 64 255)) (m_fs md))).
      - reflexivity.
      - exact Hho.
      - reflexivity.
      - exact Hfd.
      - lia.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - (* [comment removed for export] *)
        assert (VF : zrange_visible Hd (bv_unsigned sp2 + -128) (Z.of_nat (cells_size (wframe s1 s2 s3 s4 s5 s6 canary j8 (wb + d) rem)))).
        { eapply rw_cells_visible_off; [exact Hcl | exact FRW | cbn [wframe cells_size csize Nat.add]; lia]. }
        pose proof (rw_cells_munrestrict Hd full m2 _ _ VF FRW) as FRWu. unfold wframe in FRWu.
        cbn [iov_array ms_mem].
        pose proof (rdn_cell_C8 _ _ _ 8 _ FRWu eq_refl) as R8. pose proof (rdn_cell_C8 _ _ _ 16 _ FRWu eq_refl) as R16.
        pose proof (rdn_cell_C8 _ _ _ 24 _ FRWu eq_refl) as R24. pose proof (rdn_cell_C8 _ _ _ 32 _ FRWu eq_refl) as R32.
        unfold wa in R8, R16, R24, R32. rewrite !unsigned_lit by lia.
        replace (bv_unsigned sp2 + -128 + Z.of_nat 8) with (bv_unsigned sp2 + -120) in R8 by lia.
        replace (bv_unsigned sp2 + -128 + Z.of_nat 16) with (bv_unsigned sp2 + -120 + 8) in R16 by lia.
        replace (bv_unsigned sp2 + -128 + Z.of_nat 24) with (bv_unsigned sp2 + -120 + 16) in R24 by lia.
        replace (bv_unsigned sp2 + -128 + Z.of_nat 32) with (bv_unsigned sp2 + -120 + 16 + 8) in R32 by lia.
        OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; rewrite ?unsigned_lit by lia; try lia.
      - (* [comment removed for export] *)
        cbn [ms_mem]. rewrite word_to_nat_Z by lia.
        assert (VB : zrange_visible Hd wb (Z.of_nat (length pending))) by (eapply image_rw_visible; [exact HA | lia | lia]).
        pose proof (proj1 (bytes_at_munrestrict rsegs Hd full m2 wb pending VB) Wbytes) as WBu.
        rewrite <- (firstn_all2 (n:=Z.to_nat rem) (skipn (Z.to_nat d) pending)) by (rewrite length_skipn; lia).
        replace (Z_to_bv 64 (wb + d)) with (wa (wb + Z.of_nat (Z.to_nat d))) by (unfold wa; f_equal; lia).
        eapply bytes_at_rdn; [exact WBu | lia].
      - rewrite unsigned_lit by lia. lia.
      - rewrite unsigned_lit by lia. unfold rw_bytes_max. lia.
      - rewrite unsigned_lit by lia. lia.
      - rewrite unsigned_lit by lia. unfold TASK_SIZE. lia.
      - rewrite ?unsigned_lit by lia. unfold TASK_SIZE. lia.
      - rewrite ?unsigned_lit by lia. unfold TASK_SIZE. lia.
      - exact HIo.
      - (* [comment removed for export] *)
        intros k Hk. apply (hclean_mapped_in_hull A m2); [exact Hcl|].
        replace (woff (Z_to_bv 64 (bv_unsigned sp2 + -120)) k) with (wa (bv_unsigned sp2 + -128 + (8 + Z.of_nat k))).
        2:{ unfold woff, wa. f_equal. rewrite unsigned_lit by lia. lia. }
        eapply rw_cells_mapped_off; [exact FRW | cbn [wframe cells_size csize Nat.add]; lia | cbn [wframe cells_size csize Nat.add]; lia].
      - (* [comment removed for export] *)
        intros k Hk. rewrite word_to_nat_Z in Hk by lia.
        apply (image_rw_in_hull A _ HA); rewrite woff_small by (rewrite unsigned_lit by lia; lia); rewrite unsigned_lit by lia; lia.
      - apply t_exit_nil.
      - (* [comment removed for export] *)
        intros k' mo' Hk1 Hk2 HIo' Hsame. rewrite length_skipn in Hk2.
        rewrite advance_set_gpr0_MSsvc. simp_regs.
        assert (Hho' : m_halted mo' = None) by (rewrite (same_but_materialized_halted _ _ Hsame); exact Hho).
        set (k := Z.of_nat k') in *.
        pose (QQ := fun ms' => (k = rem /\ done_post sp2 gp tp a0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m2 ms')
                            \/ (k < rem /\ more_post sp2 gp tp a0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo wp2 rp2 wb wp wend bufp bufsz rp1 canary pending
                                              (Z_to_bv 64 0x9d914) t0' t1' t2' s4' t3' t4' t5' t6' (wb + d) rem k j8 m2 ms')).
        eapply (srz_evt_restrict rsegs A HA pa_wx AL E QQ _ mo'); [exact HIo' | exact Hho' | |].
        { rewrite restrict_MS, mrestrict_munrestrict', (mrestrict_clean_id _ m2 Hcl).
          eapply evt_cut.
          { eapply writev_after1; [exact MI2 | lia | lia]. }
          intros ms3 P3. unfold after_post in P3. subst ms3.
          destruct (Z.eqb_spec k rem) as [Ek|Nk].
          - eapply evt_mono; [eapply writev_done; [exact LO2 | exact CEIL | exact MI2 | exact ST2 | exact FRW | exact WC] |].
            intros ms4 P4. left. split; [exact Ek | exact P4].
          - eapply evt_mono; [eapply (writev_more sp2 gp tp a0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 lo wp2 rp2 LO2 CEIL SPHI2
                                          wb wp wend bufp bufsz rp1 canary pending SOUT1);
                                 [exact MI2 | exact ST2 | exact FRW | exact WC | lia | lia | lia] |].
            intros ms4 P4. right. split; [lia | exact P4]. }
        intros msr mo2 HQ HIo2 Hsame2 Hcl2.
        destruct HQ as [[Ek P4] | [Nk P4]].
        + (* [comment removed for export] *)
          unfold done_post in P4. (first [ dex15 P4 as ra4 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 m4; dand4 P4 as -> MU4 WM4 MI4 | dand19 P4 as ra4 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 m4 -> MU4 WM4 MI4 | destruct P4 as (ra4 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & m4 & -> & MU4 & WM4 & MI4) ]).
          rewrite skipn_all2 by (rewrite length_skipn; lia).
          eapply srz_conseq; [| apply t_eq_sym; apply t_emit_nil_eq; apply t_exit_nil].
          rewrite unrestrict_MSsvc.
          replace (m_fs md) with (m_fs mo2).
          2:{ rewrite <- Hfs. pose proof (same_but_materialized_frame _ _ Hsame2) as X2. pose proof (same_but_materialized_frame _ _ Hsame) as X1.
              transitivity (m_fs mo'); [apply X2 | apply X1]. }
          lazymatch goal with |- srealizes _ (mkCfg ?msx _) _ =>
            change (srealizes rsegs (mkCfg msx mo2) (t_exit (bv_and (ms_gpr msx 0) (Z_to_bv 64 255)) (m_fs mo2)));
            apply (srz_exit rsegs msx mo2 (Z_to_bv 64 94)) end.
          * rewrite (same_but_materialized_halted _ _ Hsame2). exact Hho'.
          * reflexivity.
          * right. reflexivity.
        + (* [comment removed for export] *)
          unfold more_post in P4. (first [ dex5 P4 as y3 y4 y5 y6 m4; dand7 P4 as -> MU4 WM4 MI4 ST4 FRW4 WC4 | dand12 P4 as y3 y4 y5 y6 m4 -> MU4 WM4 MI4 ST4 FRW4 WC4 | destruct P4 as (y3 & y4 & y5 & y6 & m4 & -> & MU4 & WM4 & MI4 & ST4 & FRW4 & WC4) ]).
          unfold wst. rewrite unrestrict_MSsvc.
          rewrite skipn_skipn. replace (k' + Z.to_nat d)%nat with (Z.to_nat (d + k)) by lia.
          replace (wb + d + k) with (wb + (d + k)) in FRW4 by lia.
          pose proof (same_but_materialized_frame _ _ Hsame2) as X2. pose proof (same_but_materialized_frame _ _ Hsame) as X1.
          eapply (flush_loop (length pending) (rem - k) (d + k)); try eassumption; try lia.
          * rewrite (same_but_materialized_halted _ _ Hsame2). exact Hho'.
          * transitivity (m_fs mo'); [apply X2 | rewrite <- Hfs; apply X1].
          * replace (m_fds mo2) with (m_fds mo); [exact Hfd|]. symmetry. transitivity (m_fds mo'); [apply X2 | apply X1].
    Qed.
  End Loop.

  (* [comment removed for export] *)
  #[using="EC SPHI CEIL LO ST TP MI Hh HI HA rp2 wp2 rp0 wp0 junk0 b4 b3 b2 b1 bss fin tid lo E Clg"] Theorem exit_asan_sec :
    (   (pending = [] /\ exists wp1 rp1, file_clean v STDOUT_F wp1 rp1)
     \/ (exists wb wp wend bufp bufsz rp1 canary, stdout_pending v wb wp wend bufp bufsz rp1 canary pending
           /\ fd_lookup (m_fds md) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)))) ->
    srealizes rsegs
      (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 EXIT_ENTRY) fc None m (seg_rom rsegs)) md)
      (t_emit (W 1 pending) (t_exit (bv_and a0 (Z_to_bv 64 255)) (m_fs md))).
  Proof.
    intros CASE.
    assert (CEILv : 0x7fff7f800000 <= lo) by (pose proof alloc_ceiling_val; lia). unfold EXIT_STACK in LO.
    pose proof EC as EC'. destruct EC'.
    (first [ dand5 ec_in as I1 I2 I3 I4 I5 | destruct ec_in as (I1 & I2 & I3 & I4 & I5) ]). (first [ dand5 ec_err as E1 E2 E3 E4 E5 | destruct ec_err as (E1 & E2 & E3 & E4 & E5) ]).
    unfold NEED_LOCKS, OFL_HEAD, STDIN_F, STDOUT_F, STDERR_F in *. lit_addrs.
    clear ec_tid ec_lock ec_fin ec_alock ec_slot ec_head ec_bnext ec_bf0 ec_ba0 ec_cov ec_figot ec_fiarr ec_done ec_dfgot ec_dso
          ec_dtor ec_flag ec_mux ec_odra ec_odrb ec_gsh ec_msh.
    destruct CASE as [[-> (wp1 & rp1 & FOUT)] | (wb & wp & wend & bufp & bufsz & rp1 & canary & SOUT & FD1)].
    - (* [comment removed for export] *)
      (first [ dand5 FOUT as O1 O2 O3 O4 O5 | destruct FOUT as (O1 & O2 & O3 & O4 & O5) ]). lit_addrs.
      eapply (srz_evt_restrict rsegs A HA pa_wx AL E
                (fun ms' => exists mq, part2c_post (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp a0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mq ms') _ md);
        [exact HI | exact Hh | |].
      { rewrite restrict_MS. fold v.
        eapply evt_cut; [eapply exit_part1; eassumption|].
        intros ms1 P1. unfold part1_post in P1.
        (first [ dex16 P1 as x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 xa m1; dand6 P1 as -> MU1 WM1 MI1 ST1 FRX1 | dand22 P1 as x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 xa m1 -> MU1 WM1 MI1 ST1 FRX1 | destruct P1 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & xa & m1 & -> & MU1 & WM1 & MI1 & ST1 & FRX1) ]).
        unfold W1 in MU1. transport_after_call rsegs v m1 MU1 WM1.
        unfold STDIO_EXIT. eapply evt_mono; [| intros msq Pq; exists m1; exact Pq].
        eapply (exit_part2_clean (Z_to_bv 64 (bv_unsigned sp + -16))); rewrite ?unsigned_lit by lia; try eassumption; try lia.
        all: unfold file_clean, STDIN_F, STDOUT_F, STDERR_F; lit_addrs_goal; repeat (split; [eassumption|]); eassumption. }
      intros msr mo1 [mq HQ] HIo1 Hsame1 Hcl1. unfold part2c_post in HQ.
      (first [ dex15 HQ as ra4 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 m4; dand4 HQ as -> MU4 WM4 MI4 | dand19 HQ as ra4 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 m4 -> MU4 WM4 MI4 | destruct HQ as (ra4 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & m4 & -> & MU4 & WM4 & MI4) ]).
      cbn [W map]. eapply srz_conseq; [| apply t_eq_sym; apply t_emit_nil_eq; apply t_exit_nil].
      rewrite unrestrict_MSsvc.
      replace (m_fs md) with (m_fs mo1) by (apply (same_but_materialized_frame _ _ Hsame1)).
      lazymatch goal with |- srealizes _ (mkCfg ?msx _) _ =>
        change (srealizes rsegs (mkCfg msx mo1) (t_exit (bv_and (ms_gpr msx 0) (Z_to_bv 64 255)) (m_fs mo1)));
        apply (srz_exit rsegs msx mo1 (Z_to_bv 64 94)) end.
      + rewrite (same_but_materialized_halted _ _ Hsame1). exact Hh.
      + reflexivity.
      + right. reflexivity.
    - (* [comment removed for export] *)
      pose proof SOUT as SO. destruct SO. destruct sp_ssp as [G1 G2]. unfold STDOUT_F, STDIO_WRITE, SSP_GOT, SSP_GUARD, STDOUT_BUF in *. lit_addrs.
      eapply (srz_evt_restrict rsegs A HA pa_wx AL E
                (fun ms' => exists mq y0 y1 y2 y4 y5 y6 y10 y11 y12 y13, stdout_pending mq wb wp wend bufp bufsz rp1 canary pending /\
                   part2p_post (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp y0 y1 y2 a0 s1 y4 y5 y6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y10 y11 y12 y13 F fc mq lo wp2 rp2
                               wb wp wend bufp bufsz rp1 canary pending ms') _ md);
        [exact HI | exact Hh | |].
      { rewrite restrict_MS. fold v.
        eapply evt_cut; [eapply exit_part1; eassumption|].
        intros ms1 P1. unfold part1_post in P1.
        (first [ dex16 P1 as x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 xa m1; dand6 P1 as -> MU1 WM1 MI1 ST1 FRX1 | dand22 P1 as x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 xa m1 -> MU1 WM1 MI1 ST1 FRX1 | destruct P1 as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & xa & m1 & -> & MU1 & WM1 & MI1 & ST1 & FRX1) ]).
        unfold W1 in MU1. transport_after_call rsegs v m1 MU1 WM1.
        assert (SOUT1 : stdout_pending m1 wb wp wend bufp bufsz rp1 canary pending).
        { constructor; unfold STDOUT_F, STDOUT_BUF, SSP_GOT, SSP_GUARD, STDIO_WRITE; lit_addrs_goal; try eassumption; try lia. split; assumption. }
        unfold STDIO_EXIT.
        eapply (evt_mono rsegs (part2p_post (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x0 x1 x2 a0 s1 x6 x7 x8 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x10 x11 x12 x13
                                  F fc m1 lo wp2 rp2 wb wp wend bufp bufsz rp1 canary pending)).
        2:{ intros msq Pq. exists m1, x0, x1, x2, x6, x7, x8, x10, x11, x12, x13. split; [exact SOUT1 | exact Pq]. }
        eapply (exit_part2_pending (Z_to_bv 64 (bv_unsigned sp + -16))); rewrite ?unsigned_lit by lia; try eassumption; try lia.
        all: unfold file_clean, STDIN_F, STDOUT_F, STDERR_F; lit_addrs_goal; repeat (split; [eassumption|]); eassumption. }
      (intros msr mo1; (first [ intro dR_14; dex11 dR_14 as mq y0 y1 y2 y4 y5 y6 y10 y11 y12 y13; destruct dR_14 as [SOUTq HQ] | intro dR_14; dand13 dR_14 as mq y0 y1 y2 y4 y5 y6 y10 y11 y12 y13 SOUTq HQ | intros (mq & y0 & y1 & y2 & y4 & y5 & y6 & y10 & y11 & y12 & y13 & SOUTq & HQ) ]); intros HIo1 Hsame1 Hcl1). unfold part2p_post in HQ.
      (first [ dex3 HQ as z3 j8 m2; dand7 HQ as -> MU2 WM2 MI2 ST2 FRW WC | dand10 HQ as z3 j8 m2 -> MU2 WM2 MI2 ST2 FRW WC | destruct HQ as (z3 & j8 & m2 & -> & MU2 & WM2 & MI2 & ST2 & FRW & WC) ]).
      unfold wst, WRITEV_ECALL1. rewrite unrestrict_MSsvc. cbn [ms_mem MS].
      pose proof (same_but_materialized_frame _ _ Hsame1) as X1.
      pose proof SOUTq as SO. destruct SO. unfold STDOUT_BUF in sp_range.
      eapply (flush_first (Z_to_bv 64 (bv_unsigned sp + -16)) wb wp wend bufp bufsz rp1 canary _ _ mq SOUTq (wp - wb) 0);
        rewrite ?unsigned_lit by lia; try eassumption; try lia.
      + rewrite (same_but_materialized_halted _ _ Hsame1). exact Hh.
      + apply X1.
      + replace (m_fds mo1) with (m_fds md); [exact FD1 | symmetry; apply X1].
      + rewrite unsigned_lit in ST2 by lia. exact ST2.
      + rewrite unsigned_lit in FRW by lia. rewrite Z.add_0_r. exact FRW.
      Unshelve. all: rewrite ?unsigned_lit by lia; lia.
  Qed.
End Exit.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem exit_asan : exit_spec_stmt.
Proof.
  unfold exit_spec_stmt. intros. eapply exit_asan_sec; eassumption.
Qed.

End CEIL.
End DA_Exit.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_H5g8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_H5g8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_H5g8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_H5g8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require DA_File.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ey6n OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Eg3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Cells OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Ldix OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Entry OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Mib4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Main OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Am90 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Mwrv.DA_Exit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Fpom OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Usage OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Ouhu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_H5g8.DA_Dir OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_File.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16 A_Cocsh.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import PF_L6 PF_L7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP. Import APS.
Open Scope bv_scope.
Local Open Scope Z_scope.

Section Top.
  Context {Clg : Ceiling} {DR : DepotRep}.
  (* [comment removed for export] *)
  Variable sp : word.
  Hypothesis HCEIL : alloc_ceiling = bv_unsigned sp - 0x800000.
  Variable rdraw : EntryDraw.
  Variable brk0 : word.
  Variables argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Context {BL : AsanInit.BootLim}.   (* [comment removed for export] *)
  Hypothesis HLIM : AInv.TLIM_MIN <= (@AsanInit.blim BL).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Hypotheses (Hmalloc : pa_malloc_obligation) (Hfree : pa_free_obligation) (Hcalloc : pa_calloc_obligation)
             (Hrealloc : pa_realloc_obligation) (Hsmalloc : pa_smalloc_obligation) (Hsfree : pa_sfree_obligation).
  Hypothesis DINIT : depot_init_ok2 (DR:=DR).
  Hypothesis AINIT : ainit_top_stmt (DR:=DR).

  #[local] Instance AIp : AsanAlloc LPA := pasan_AsanAlloc Hmalloc Hfree Hcalloc Hrealloc Hsmalloc Hsfree.

  (* [comment removed for export] *)
  Hypothesis AI16p : AsanAlloc16 (AI:=AIp).
  Hypothesis LIB : alib_call_ok (AI:=AIp).
  Let MALLOC1 : malloc1_stmt (AI:=AIp) := malloc1_ok (AI:=AIp) (AI16:=AI16p).
  Let FREE1 : free1_stmt (AI:=AIp) := free1_ok (AI:=AIp).

  Let usp : Z := bv_unsigned sp.
  Let HCEILu : alloc_ceiling = usp - 0x800000. Proof. exact HCEIL. Qed.

  (* [comment removed for export] *)
  Let EXIT : exit_spec_stmt := exit_asan.
  Let FWRITE : fwrite_diag_stmt := fwrite_diag_ok.
  Let FPRINTF : fprintf_diag_stmt := fprintf_diag_ok.
  Let VPF1 : vprintf_first_stmt := vprintf_first_ok.
  Let VPF2 : vprintf_next_stmt := vprintf_next_ok.

  (* [comment removed for export] *)
  Let USAGE : usage_stmt usp argv envp fs := usage_ok usp HCEILu argv envp fs Hva FPRINTF EXIT.
  Let OPENFAIL : open_fail_stmt' usp argv envp fs := open_fail_ok2 usp HCEILu argv envp fs Hva FPRINTF EXIT.
  Let DIR : dir_stmt usp argv envp fs := dir_ok usp HCEILu argv envp fs Hva MALLOC1 FPRINTF EXIT.
  Let FILE : file_stmt usp argv envp fs := file_ok usp HCEILu argv envp fs Hva MALLOC1 FREE1 LIB VPF1 VPF2 FPRINTF FWRITE EXIT.

  (* [comment removed for export] *)
  Lemma entry_A0_of_facts : forall span A0, a0_facts usp A0 -> p_stk_span (a_pl A0) = span -> entry_A0 usp span A0.
  Proof.
    intros span A0 F SP. constructor; cbn.
    - exact (a0_live _ _ F).
    - exact (a0_frames _ _ F).
    - exact (a0_bytes _ _ F).
    - exact (a0_nlive _ _ F).
    - exact (a0_cred _ _ F).
    - exact (a0_scred _ _ F).
    - exact (a0_pcred _ _ F).   (* [comment removed for export] *)
    - intros a Ha. apply (a0_vis _ _ F). right. left. rewrite SP. exact Ha.
    - intros a Ha. apply (a0_vis _ _ F). right. right. right. unfold STKSH_LO, STKSH_HI in Ha.
      pose proof ALogic1.stack_shadow_iv_facts as (_ & SF2 & SF3 & _). unfold kHighMemBeg in SF3. lia.
  Qed.

  #[local] Notation CSOK HS := (fun E R FULL model =>
     cs_ok BSEGS BOTH (@AsanInit.blim BL) (SINV0 BPH sp rdraw brk0 argv envp uid hw) (argH0 BPH sp rdraw argv envp uid hw) fs E HS R FULL model).

  (* [comment removed for export] *)
  Lemma asan_main_hole_of :
    forall (HS : acs) (K1 : list Z),
      (forall E R FULL model, CSOK HS E R FULL model -> entry_raw usp argv envp fs R FULL model) ->
      (forall E R FULL model, CSOK HS E R FULL model -> a0_raw (P_of sp argv envp E HS model) K1 usp FULL model) ->
      forall E R FULL model, spec argv fs [] -> CSOK HS E R FULL model ->
        srealizes BSEGS (cfg_of BSEGS R 0x867f8 FULL model) (spec argv fs).
  Proof.
    intros HS K1 HER HAR E R FULL model NIL CS.
    pose proof (HER E R FULL model CS) as ER. pose proof (HAR E R FULL model CS) as AR.
    assert (TOP : alloc_top (m_vmmaps model) = alloc_ceiling).
    { pose proof (pre_top sp rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit HS E R FULL model CS) as PT. rewrite HCEIL. unfold usp. lia. }
    destruct (AINIT _ _ _ _ _ DINIT AR TOP) as (A0 & PAINV & FACTS & EQA0).
    assert (SPAN : p_stk_span (a_pl A0) = e_span argv envp) by (rewrite EQA0; reflexivity).
    pose proof (entry_A0_of_facts (e_span argv envp) A0 FACTS SPAN) as EA.
    pose proof (main_view_of_entry (AI:=AIp) usp argv envp fs R FULL model A0 ER PAINV EA) as MV.
    pose proof (dinv_of_main_view (AI:=AIp) usp argv envp fs A0 FULL model MV) as DI.
    pose proof ER as ER'. destruct ER' as [Hra Hsp' Hgp Htp Ha0 Ha1].
    unfold cfg_of. change (mkst R (Z_to_bv 64 550904) FULL (seg_rom BSEGS))
      with (MS R bvmap_empty (Z_to_bv 64 550904) (Z_to_bv 32 0) None FULL (seg_rom BSEGS)).
    apply (srealizes_of_mkR BSEGS R bvmap_empty (Z_to_bv 64 550904) (Z_to_bv 32 0) None FULL (seg_rom BSEGS) model (spec argv fs)
             (Z_to_bv 64 RA_MAIN) (Z_to_bv 64 (SPM usp)) (getr R 3) (Z_to_bv 64 TPV) (getr R 5) (getr R 6) (getr R 7)
             (getr R 8) (getr R 9) (Z_to_bv 64 (e_argc argv)) (Z_to_bv 64 (usp + 8)) (getr R 12) (getr R 13) (getr R 14)
             (getr R 15) (getr R 16) (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
             (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31));
      try reflexivity; [exact Hra | exact Hsp' | exact Htp | exact Ha0 | exact Ha1 |].
    exact (main_realizes (AI:=AIp) usp argv envp fs USAGE OPENFAIL DIR FILE
             (getr R 3) (getr R 5) (getr R 6) (getr R 7) (getr R 8) (getr R 9) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
             (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26)
             (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31) bvmap_empty (Z_to_bv 32 0) FULL model A0 DI EA).
  Qed.

  Theorem asan_main_hole_1 : forall E R FULL model, spec argv fs [] -> CSOK HS_both2_1 E R FULL model ->
    srealizes BSEGS (cfg_of BSEGS R 0x867f8 FULL model) (spec argv fs).
  Proof. exact (asan_main_hole_of HS_both2_1 K1_1 (entry_raw_1 sp HCEIL rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit)
                                                  (a0_raw_1 sp HCEIL rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit HLIM)). Qed.
  Theorem asan_main_hole_2 : forall E R FULL model, spec argv fs [] -> CSOK HS_both2_2 E R FULL model ->
    srealizes BSEGS (cfg_of BSEGS R 0x867f8 FULL model) (spec argv fs).
  Proof. exact (asan_main_hole_of HS_both2_2 K1_2 (entry_raw_2 sp HCEIL rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit)
                                                  (a0_raw_2 sp HCEIL rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit HLIM)). Qed.
  Theorem asan_main_hole_3 : forall E R FULL model, spec argv fs [] -> CSOK HS_both2b_1 E R FULL model ->
    srealizes BSEGS (cfg_of BSEGS R 0x867f8 FULL model) (spec argv fs).
  Proof. exact (asan_main_hole_of HS_both2b_1 K1_1 (entry_raw_3 sp HCEIL rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit)
                                                   (a0_raw_3 sp HCEIL rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit HLIM)). Qed.
  Theorem asan_main_hole_4 : forall E R FULL model, spec argv fs [] -> CSOK HS_both2b_2 E R FULL model ->
    srealizes BSEGS (cfg_of BSEGS R 0x867f8 FULL model) (spec argv fs).
  Proof. exact (asan_main_hole_of HS_both2b_2 K1_2 (entry_raw_4 sp HCEIL rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit)
                                                   (a0_raw_4 sp HCEIL rdraw brk0 argv envp uid hw fs Hsp Hva Hve Hfit HLIM)). Qed.
End Top.
