(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare StoreOk MmapSim AllocSim ShapeAlg PureModel VmLedger VmGap AllocIface AsanCeil.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import RefStep RefStmts.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_live MallocInv_wf MallocInv_steps
  MallocInv_coh MallocInv_ops MallocInv_env MallocInv_auxv AllocBase AllocCalloc AllocSure AllocCredit MallocAllocLayout MallocIfaceX
  MallocInv_hints MallocInv_ameta_iface MallocInv_ametax_iface MallocSureCap MallocSureCredit MallocSurePot MallocSureInv MallocGlue MallocSure.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition chk_cost (m : Z) : bool :=
  Z.max (acostS (stc_m m)) (acostS (stc_m m + 1)) <=? Z.max 8448 (32 * m + 8294).

Lemma chk_costs : forallb chk_cost (MallocLayout.Zseq 0 (Z.to_nat 8191)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma malloc_dp_cost : forall n, 0 <= n -> malloc_dp n <= alloc_cost n.
Proof.
  intros n Hn. unfold alloc_cost. destruct (Z.lt_ge_cases n MMAP_THRESHOLD) as [Hlt | Hge].
  - rewrite (malloc_dp_small n Hlt), stc_eq.
    assert (Hm : 0 <= (n + 3) / 16 < 8191).
    { unfold MMAP_THRESHOLD in Hlt. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    pose proof (proj1 (forallb_forall _ _) chk_costs ((n + 3) / 16)
                  (MallocLayout.Zseq_In (Z.to_nat 8191) 0 ((n + 3) / 16) ltac:(rewrite Z2Nat.id by lia; clear - Hm; lia))) as C.
    unfold chk_cost in C. apply Z.leb_le in C.
    pose proof (Z.mod_pos_bound (n + 3) 16 ltac:(lia)) as D2. pose proof (Z_div_mod_eq_full (n + 3) 16) as D3.
    set (m := (n + 3) / 16) in *. set (c := Z.max (acostS (stc_m m)) (acostS (stc_m m + 1))) in *. clearbody c. lia.
  - rewrite (malloc_dp_big n Hge). unfold MMAP_THRESHOLD in Hge. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML}.
Local Notation u := bv_unsigned (only parsing).

Definition g_roomP (A : astate) (h : VmMaps) (k p : Z) : Prop :=
  g_room A h k 0 /\ p <= (ROOM_BCAP - vm_backed_bytes h) + pot2 A.

Lemma pot_credmax : forall A, 0 <= pot2 A <= ROOM_CREDMAX.
Proof. intros A. unfold ROOM_CREDMAX. exact (pot2_range A). Qed.

Lemma g_roomP_mono : forall A h k p k' p', g_roomP A h k p -> 0 <= k' <= k -> p' <= p -> g_roomP A h k' p'.
Proof. intros A h k p k' p' [R HP] Hk Hp. split; [exact (g_room_mono A h k 0 k' 0 R Hk ltac:(lia)) | lia]. Qed.

(* [comment removed for export] *)
Lemma g_room_bytes : forall A h k b, g_room A h k 0 -> 0 <= b -> vm_backed_bytes h + b <= ROOM_BCAP -> g_room A h k b.
Proof.
  intros A h k b (R1 & R2 & R3 & R4 & R5 & R6) Hb HB. unfold g_room. repeat split; try assumption; lia.
Qed.

Lemma g_roomP_of_room : forall A h k b, g_room A h k b -> g_roomP A h k b.
Proof.
  intros A h k b R. pose proof R as (R1 & R2 & R3 & _). pose proof (pot_credmax A). split; [exact (g_room_mono A h k b k 0 R ltac:(lia) ltac:(lia)) | lia].
Qed.

Lemma g_room_of_roomP : forall A h k p, g_roomP A h k p -> ROOM_CREDMAX <= p -> g_room A h k (p - ROOM_CREDMAX).
Proof.
  intros A h k p [R HP] Hp. pose proof (pot_credmax A). apply (g_room_bytes A h k _ R); lia.
Qed.

(* [comment removed for export] *)
Lemma g_roomP_margin : forall A h k p n, g_roomP A h k p -> 0 <= n -> alloc_margin n + ROOM_CREDMAX <= p -> g_room A h k (alloc_margin n).
Proof.
  intros A h k p n [R HP] Hn Hp. pose proof (pot_credmax A). pose proof (alloc_margin_ge n Hn).
  apply (g_room_bytes A h k _ R); lia.
Qed.

(* [comment removed for export] *)
Lemma g_roomP_malloc : forall A A' h h' n k p,
  0 <= n -> malloc_growX n A A' h h' ->
  g_roomP A h k p -> 1 <= k -> alloc_margin n + ROOM_CREDMAX <= p -> g_roomP A' h' (k - 1) (p - alloc_cost n).
Proof.
  intros A A' h h' n k p Hn GR RP Hk Hp.
  pose proof (g_room_malloc A A' h h' n k (alloc_margin n) Hn GR (g_roomP_margin A h k p n RP Hn Hp) Hk ltac:(lia)) as R'.
  replace (alloc_margin n - alloc_margin n) with 0 in R' by lia.
  split; [exact R'|]. destruct GR as [_ PG]. destruct RP as [_ HP]. pose proof (malloc_dp_cost n Hn). unfold pgrow in PG. lia.
Qed.

End WithLayout.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Credit.
  Context {ML : MallocLayout} {MLok : MallocLayoutOk ML}.
  Local Notation u := bv_unsigned (only parsing).
  Local Existing Instance mallocng_alloc_layout.
  Local Existing Instance mallocng_calloc_layout.

  (* [comment removed for export] *)
  Hypothesis malloc_okX : forall (HT : HeapTop) A s (sp0 : word) argv envp (sp : word) (n : Z),
    call_env (HT:=HT) A s sp0 argv envp -> a_xmaps A = [] -> 0 <= n < 2^61 ->
    tsafe (m_malloc sp (Z_to_bv 64 n) s) (malloc_postX (HT:=HT) A n s).
  Hypothesis free_okX : forall (HT : HeapTop) A s (p sp0 : word) argv envp,
    call_env (HT:=HT) A s sp0 argv envp -> a_xmaps A = [] ->
    (p = Z_to_bv 64 0 \/ exists n, mlive A p = Some n) ->
    tsafe (m_free p s) (free_postX (HT:=HT) A p s).
  Hypothesis calloc_okX : forall (HT : HeapTop) A s (sp0 : word) argv envp (sp : word) (fuel : nat) (cnt sz : Z),
    call_env (HT:=HT) A s sp0 argv envp -> a_xmaps A = [] -> replaced_clear (ms_mem s) ->
    0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> 0 <= cnt * sz < 2^61 -> cnt * sz / 4096 < Z.of_nat fuel ->
    tsafe (m_calloc fuel sp (Z_to_bv 64 cnt) (Z_to_bv 64 sz) s) (calloc_postX (HT:=HT) A (cnt * sz) s).
  (* [comment removed for export] *)
  Hypothesis malloc_refines : forall fx : FPState, malloc_stmt (fx:=fx).
  Hypothesis free_refines : forall fx : FPState, free_stmt (fx:=fx).
  Hypothesis calloc_refines : forall fx : FPState, calloc_stmt (fx:=fx).

  (* [comment removed for export] *)
  Definition mallocng_credit : AllocCredit (AL:=mallocng_alloc_layout) (CL:=mallocng_calloc_layout).
  Proof.
    refine {| acr_sure := mallocng_sure malloc_okX free_okX calloc_okX malloc_refines free_refines calloc_refines;
              aroomP := g_roomP;
              aroomP_mono := g_roomP_mono;
              aroomP_of_aroom := g_roomP_of_room;
              aroom_of_aroomP := g_room_of_roomP |}.
    - (* [comment removed for export] *)
      abstract (
        intros fx A m md regs n ret sp0 argv envp S HG Hpure Henv H10 Hn H1 Hret H4 Hal Htop Hsp0 Hwin HK;
        apply (glue_malloc_g malloc_okX malloc_refines fx A m md regs n ret sp0 argv envp S HG Hpure Henv H10 Hn H1 Hret H4 Hal Htop Hsp0 Hwin);
        intros A' m' vm' regs' res X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 GR _;
        apply (HK A' m' vm' regs' res X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11);
        intros k p HR Hk Hp; exact (g_roomP_malloc A A' _ vm' n k p (proj1 Hn) GR HR Hk Hp)).
    - (* [comment removed for export] *)
      abstract (
        intros fx A m md regs cnt sz ret sp0 argv envp S HG Hpure Henv H10 H11 Hcnt Hsz Hn H1 Hret H4 Hal Htop Hsp0 Hwin HK;
        apply (glue_calloc_g calloc_okX calloc_refines fx A m md regs cnt sz ret sp0 argv envp S HG Hpure Henv H10 H11 Hcnt Hsz Hn H1 Hret H4 Hal Htop Hsp0 Hwin);
        intros A' m' vm' regs' res X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 GR _;
        apply (HK A' m' vm' regs' res X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11);
        intros k p HR Hk Hp; exact (g_roomP_malloc A A' _ vm' (cnt * sz) k p (proj1 Hn) GR HR Hk Hp)).
    - (* [comment removed for export] *)
      abstract (
        intros fx A m md regs n k p ret sp0 argv envp S HG Hpure Henv H10 Hn HR Hk Hp Hmax H1 Hret H4 Hal Htop Hsp0 Hwin HK;
        apply (glue_malloc_g malloc_okX malloc_refines fx A m md regs n ret sp0 argv envp S HG Hpure Henv H10 Hn H1 Hret H4 Hal Htop Hsp0 Hwin);
        intros A' m' vm' regs' res X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 GR NR;
        destruct X4 as [(E0 & _) | (Hnz & F1 & F2 & F3 & F4)];
        [ exfalso; apply (g_noroom_absurd A m (m_vmmaps md) n k (alloc_margin n) HG (conj (proj1 Hn) Hmax)
                            (g_roomP_margin A (m_vmmaps md) k p n HR (proj1 Hn) Hp) Hk (Z.le_refl _));
          apply NR; rewrite E0; reflexivity
        | apply (HK A' m' vm' regs' res X1 X2 X3 Hnz F1 F2 F3 F4 X5 X6 X7 X8 X9 X10 X11);
          exact (g_roomP_malloc A A' _ vm' n k p (proj1 Hn) GR HR Hk Hp) ]).
    - (* [comment removed for export] *)
      abstract (
        intros fx A m md regs cnt sz k p ret sp0 argv envp S HG Hpure Henv H10 H11 Hcnt Hsz Hn HR Hk Hp Hmax H1 Hret H4 Hal Htop Hsp0 Hwin HK;
        apply (glue_calloc_g calloc_okX calloc_refines fx A m md regs cnt sz ret sp0 argv envp S HG Hpure Henv H10 H11 Hcnt Hsz Hn H1 Hret H4 Hal Htop Hsp0 Hwin);
        intros A' m' vm' regs' res X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 GR NR;
        destruct X4 as [(E0 & _) | (Hnz & F1 & F2 & F3 & F4 & F5)];
        [ exfalso; apply (g_noroom_absurd A m (m_vmmaps md) (cnt * sz) k (alloc_margin (cnt * sz)) HG (conj (proj1 Hn) Hmax)
                            (g_roomP_margin A (m_vmmaps md) k p (cnt * sz) HR (proj1 Hn) Hp) Hk (Z.le_refl _));
          apply NR; rewrite E0; reflexivity
        | apply (HK A' m' vm' regs' res X1 X2 X3 Hnz F1 F2 F3 F4 F5 X5 X6 X7 X8 X9 X10 X11);
          exact (g_roomP_malloc A A' _ vm' (cnt * sz) k p (proj1 Hn) GR HR Hk Hp) ]).
  Defined.

  (* [comment removed for export] *)
  Lemma mallocng_credit_sure :
    acr_sure (AllocCredit:=mallocng_credit) = mallocng_sure malloc_okX free_okX calloc_okX malloc_refines free_refines calloc_refines.
  Proof. reflexivity. Qed.

End Credit.
