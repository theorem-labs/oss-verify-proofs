(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim Hoare StoreOk MmapSim AllocSim ShapeAlg PureModel VmLedger VmGap AllocIface AsanCeil.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import RefStep RefStmts.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_live MallocInv_wf MallocInv_steps
  MallocInv_coh MallocInv_ops MallocInv_env MallocInv_auxv AllocBase AllocCalloc AllocSure MallocAllocLayout MallocIfaceX
  MallocInv_hints MallocInv_ameta_iface MallocInv_ametax_iface MallocSureCap MallocSureInv MallocGlue.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ROOM_CMAX : Z := ROOM_KMAX.       (* [comment removed for export] *)
Definition ROOM_MCAP : Z := 4 * ROOM_KMAX.
Definition ROOM_AMAX : Z := 17000.
(* [comment removed for export] *)
Definition ROOM_LMAX : Z := ROOM_NMAX + 2^22.

(* [comment removed for export] *)
Definition stc_m (m : Z) : Z :=
  if m <? 10 then m else
  let m1 := m + 1 in
  let i := (Z.log2 m1 - 3) * 4 + 8 in
  let i1 := if size_class (i + 1) <? m1 then i + 2 else i in
  if size_class i1 <? m1 then i1 + 1 else i1.

Lemma stc_eq : forall n, size_to_class_z n = stc_m ((n + 3) / 16).
Proof. intros n. reflexivity. Qed.

(* [comment removed for export] *)
Definition chk_cap (m : Z) : bool :=
  let cap := Z.max (grp_cap (stc_m m)) (grp_cap (stc_m m + 1)) in
  (cap <=? 2^20) && (if m <=? 126 then 36864 + cap <=? 2^17 else 36864 + cap <=? 832 * m + 69476).

Lemma chk_caps : forallb chk_cap (MallocLayout.Zseq 0 (Z.to_nat 8191)) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma malloc_db_margin : forall n, 0 <= n -> malloc_db n + 4096 <= alloc_margin n.
Proof.
  intros n Hn. destruct (Z.lt_ge_cases n MMAP_THRESHOLD) as [Hlt | Hge].
  - rewrite (malloc_db_small n Hlt). unfold malloc_cap. rewrite stc_eq.
    assert (Hm : 0 <= (n + 3) / 16 < 8191).
    { unfold MMAP_THRESHOLD in Hlt. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    pose proof (proj1 (forallb_forall _ _) chk_caps ((n + 3) / 16) (MallocLayout.Zseq_In (Z.to_nat 8191) 0 ((n + 3) / 16) ltac:(rewrite Z2Nat.id by lia; clear - Hm; lia))) as C.
    unfold chk_cap in C. cbv zeta in C.
    pose proof (Z.mul_div_le (n + 3) 16 ltac:(lia)) as D1.
    pose proof (Z.mod_pos_bound (n + 3) 16 ltac:(lia)) as D2. pose proof (Z_div_mod_eq_full (n + 3) 16) as D3.
    set (m := (n + 3) / 16) in *. set (cap := Z.max (grp_cap (stc_m m)) (grp_cap (stc_m m + 1))) in *. clearbody cap.
    apply andb_prop in C. destruct C as [C1 C2]. apply Z.leb_le in C1.
    unfold alloc_margin.
    destruct (Z.leb_spec m 126) as [Hm126 | Hm126]; apply Z.leb_le in C2.
    + destruct (Z.leb_spec n 2028); lia.
    + destruct (Z.leb_spec n 2028); lia.
  - rewrite (malloc_db_big n Hge). unfold alloc_margin, MMAP_THRESHOLD in *. destruct (Z.leb_spec n 2028); lia.
Qed.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML}.
Local Notation u := bv_unsigned (only parsing).

Definition g_room (A : astate) (h : VmMaps) (k b : Z) : Prop :=
  0 <= k /\ 0 <= b /\
  vm_backed_bytes h + b <= ROOM_BCAP /\ ROOM_BCAP <= vm_limit h /\
  Z.of_nat (length (vm_maps h)) - Z.of_nat (length (a_areas A)) + k <= ROOM_CMAX /\
  exists M, muse A <= M /\ 101 * (Z.of_nat (length (a_areas A)) - 1) <= M /\ M + 4 * k <= ROOM_MCAP.

Lemma g_room_mono : forall A h k b k' b',
  g_room A h k b -> 0 <= k' <= k -> 0 <= b' <= b -> g_room A h k' b'.
Proof.
  intros A h k b k' b' (R1 & R2 & R3 & R4 & R5 & M & R6 & R7 & R8) Hk Hb. unfold g_room.
  repeat split; try lia. exists M. repeat split; lia.
Qed.

Lemma g_room_nonneg : forall A h k b, g_room A h k b -> 0 <= k /\ 0 <= b.
Proof. intros A h k b (R1 & R2 & _). split; assumption. Qed.

Lemma g_room_init : forall h0 k b,
  vm_maps h0 = [] -> vm_noaccess h0 = [] -> ROOM_BCAP <= vm_limit h0 ->
  0 <= k <= ROOM_KMAX -> 0 <= b <= ROOM_BCAP -> g_room MallocInv_defs.A0 h0 k b.
Proof.
  intros h0 k b Hm Hna Hlim Hk Hb. unfold g_room.
  assert (E : vm_backed_bytes h0 = 0) by (unfold vm_backed_bytes, vm_backed_maps; rewrite Hm, Hna; reflexivity).
  rewrite E, Hm. cbn [length Z.of_nat a_areas MallocInv_defs.A0]. unfold ROOM_CMAX, ROOM_MCAP in *.
  repeat split; try lia. exists 0. unfold muse, spare. cbn. unfold MallocInv_defs.ctx0. lia.
Qed.

(* [comment removed for export] *)
Lemma g_room_areas : forall A h k b, g_room A h k b -> Z.of_nat (length (a_areas A)) <= ROOM_AMAX.
Proof.
  intros A h k b (R1 & _ & _ & _ & _ & M & _ & R7 & R8). unfold ROOM_MCAP, ROOM_KMAX, ROOM_AMAX in *. lia.
Qed.

(* [comment removed for export] *)
Lemma g_room_malloc : forall A A' h h' n k b,
  0 <= n -> malloc_growX n A A' h h' ->
  g_room A h k b -> 1 <= k -> alloc_margin n <= b -> g_room A' h' (k - 1) (b - alloc_margin n).
Proof.
  intros A A' h h' n k b Hn [[G1 G2 _ _ _ G6 _ G8 G9 G10] _] (R1 & R2 & R3 & R4 & R5 & M & R6 & R7 & R8) Hk Hb.
  pose proof (malloc_db_margin n Hn) as HM.
  unfold g_room. rewrite G6. repeat split; try lia. exists (M + 4). repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma g_room_free : forall A A' h h' k b,
  sgrow 0 0 0 A A' h h' -> g_room A h k b -> g_room A' h' k b.
Proof.
  intros A A' h h' k b [G1 G2 _ _ _ G6 _ G8 G9 G10] (R1 & R2 & R3 & R4 & R5 & M & R6 & R7 & R8).
  unfold g_room. rewrite G6. repeat split; try lia. exists M. repeat split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithTop.
Context {HT : HeapTop}.

(* [comment removed for export] *)
Lemma room_numbers : forall (backed areas xm maps len : Z),
  0 <= backed <= ROOM_BCAP -> 0 <= areas <= ROOM_AMAX -> 0 <= xm <= ROOM_NMAX + 4115 ->
  0 <= maps <= ROOM_CMAX + ROOM_AMAX -> 0 < len <= ROOM_LMAX ->
  2^32 + (backed + 4096 * (areas + 1) + 48 * (4096 * (areas + 50)) + xm) + maps * (len + 4095) + len <= alloc_ceiling.
Proof.
  intros backed areas xm maps len Hb Ha Hx Hm Hl. pose proof alloc_ceiling_range as HC.
  assert (P : maps * (len + 4095) <= (ROOM_CMAX + ROOM_AMAX) * (ROOM_LMAX + 4095)) by (apply Z.mul_le_mono_nonneg; lia).
  unfold ROOM_LMAX, ROOM_BCAP, ROOM_AMAX, ROOM_NMAX, ROOM_CMAX, ROOM_KMAX in *. lia.
Qed.

Lemma pow2_block : forall sh, 0 <= sh -> 0 < 2 ^ (sh + 13) /\ 2 ^ (sh + 13) mod 4096 = 0.
Proof.
  intros sh Hsh. split; [apply Z.pow_pos_nonneg; lia|].
  replace (sh + 13) with ((sh + 1) + 12) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 12) with 4096. apply Z_mod_mult.
Qed.

Theorem noroomX_absurd : forall A h n k b,
  a_xmaps A = [] -> 0 <= n <= ROOM_NMAX ->
  g_room A h k b -> 1 <= k -> alloc_margin n <= b ->
  ~ malloc_noroomX n A h.
Proof.
  intros A h n k b Hxm Hn (R1 & R2 & R3 & R4 & R5 & M & R6 & R7 & R8) Hk Hb (A1 & s1 & HW1 & HV1 & [G1 G2 _ _ _ G6 _ G8 G9 G10] & HX & HD).
  rewrite Hxm in HX. cbn [lsum] in HX.
  pose proof (malloc_db_margin n (proj1 Hn)) as HM. pose proof (alloc_margin_le n) as HML.
  pose proof (MallocSureInv.lsum_nonneg (a_xmaps A1)) as HX0.
  set (h1 := ms_vm s1) in *.
  assert (Bk : 0 <= vm_backed_bytes h1) by (unfold vm_backed_bytes; apply VmGap.live_bytes_nonneg).
  assert (Bk0 : 0 <= vm_backed_bytes h) by (unfold vm_backed_bytes; apply VmGap.live_bytes_nonneg).
  assert (HA1 : Z.of_nat (length (a_areas A1)) <= ROOM_AMAX) by (unfold ROOM_MCAP, ROOM_KMAX, ROOM_AMAX in *; lia).
  assert (NUM : forall len, 0 < len <= ROOM_LMAX ->
     2^32 + (vm_backed_bytes h1 + 4096 * (Z.of_nat (length (a_areas A1)) + 1)
             + 48 * (4096 * (Z.of_nat (length (a_areas A1)) + 50)) + lsum (a_xmaps A1))
       + Z.of_nat (length (vm_maps h1)) * (len + 4095) + len <= alloc_ceiling).
  { intros len Hlen. apply room_numbers; [lia | lia | lia | unfold ROOM_CMAX in *; lia | exact Hlen]. }
  destruct HD as [NR | (len & L1 & L2 & L3 & L4)].
  - (* [comment removed for export] *)
    apply NR. right. split; [fold h1; rewrite G6; pose proof (malloc_db_pos n (proj1 Hn)); lia|].
    pose proof (wf_ctx_nonneg A1 HW1 KAac) as Haac.
    destruct (Z.eq_dec (a_ctx A1 KAac) 0) as [E0 | NE]; [right | left; lia].
    pose proof (wf_ctx_nonneg A1 HW1 KShift) as Hsh. destruct (pow2_block (a_ctx A1 KShift) Hsh) as [P1 P2].
    pose proof (next_block_le A1 HW1 E0) as NB.
    apply (node_gap_na A1 h1 _ HW1 HV1 P1 P2). apply NUM. unfold ROOM_AMAX, ROOM_LMAX, ROOM_NMAX in *. lia.
  - (* [comment removed for export] *)
    assert (Hlen : 0 < len <= ROOM_LMAX) by (unfold ROOM_LMAX, ROOM_NMAX in *; lia).
    assert (Hbud : vm_backed_bytes h1 + len <= vm_limit h1) by (rewrite G6; lia).
    destruct (node_gap A1 h1 len HW1 HV1 (proj1 L1) L2 (NUM len Hlen) Hbud) as (a & Ha).
    specialize (L4 a). cbn [mmap_grant_ok] in L4. rewrite Ha in L4. discriminate L4.
Qed.

End WithTop.
End WithLayout.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sure.
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
  Lemma g_noroom_absurd : forall A m vm n k b,
    g_inv A m vm -> 0 <= n <= ROOM_NMAX -> g_room A vm k b -> 1 <= k -> alloc_margin n <= b ->
    ~ g_noroom n A vm.
  Proof.
    intros A m vm n k b (_ & _ & Hxm & _) Hn HR Hk Hb (H & HN).
    exact (noroomX_absurd (HT:=HTof vm H) A vm n k b Hxm Hn HR Hk Hb HN).
  Qed.

  (* [comment removed for export] *)
  Definition mallocng_sure : AllocSure (AL:=mallocng_alloc_layout) (CL:=mallocng_calloc_layout).
  Proof.
    refine {| asr_calloc := mallocng_calloc malloc_okX free_okX calloc_okX malloc_refines free_refines calloc_refines;
              aroom := g_room;
              aroom_mono := g_room_mono;
              aroom_nonneg := g_room_nonneg |}.
    - (* [comment removed for export] *)
      abstract (intros h0 k b IL Hlim Hk Hb; exact (g_room_init h0 k b (il_maps h0 IL) (il_noaccess h0 IL) Hlim Hk Hb)).
    - (* [comment removed for export] *)
      abstract (
        intros fx A m md regs n ret sp0 argv envp S HG Hpure Henv H10 Hn H1 Hret H4 Hal Htop Hsp0 Hwin HK;
        apply (glue_malloc_g malloc_okX malloc_refines fx A m md regs n ret sp0 argv envp S HG Hpure Henv H10 Hn H1 Hret H4 Hal Htop Hsp0 Hwin);
        intros A' m' vm' regs' res X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 GR _;
        apply (HK A' m' vm' regs' res X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11);
        intros k b HR Hk Hb; exact (g_room_malloc A A' _ vm' n k b (proj1 Hn) GR HR Hk Hb)).
    - (* [comment removed for export] *)
      abstract (
        intros fx A m md regs p ret sp0 argv envp S HG Hpure Henv H10 Hp H1 Hret H4 Hal Htop Hsp0 Hwin HK;
        apply (glue_free_g free_okX free_refines fx A m md regs p ret sp0 argv envp S HG Hpure Henv H10 Hp H1 Hret H4 Hal Htop Hsp0 Hwin);
        intros A' m' vm' regs' X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 GR;
        apply (HK A' m' vm' regs' X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12);
        intros k b HR; exact (g_room_free A A' _ vm' k b GR HR)).
    - (* [comment removed for export] *)
      abstract (
        intros fx A m md regs cnt sz ret sp0 argv envp S HG Hpure Henv H10 H11 Hcnt Hsz Hn H1 Hret H4 Hal Htop Hsp0 Hwin HK;
        apply (glue_calloc_g calloc_okX calloc_refines fx A m md regs cnt sz ret sp0 argv envp S HG Hpure Henv H10 H11 Hcnt Hsz Hn H1 Hret H4 Hal Htop Hsp0 Hwin);
        intros A' m' vm' regs' res X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 GR _;
        apply (HK A' m' vm' regs' res X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11);
        intros k b HR Hk Hb; exact (g_room_malloc A A' _ vm' (cnt * sz) k b (proj1 Hn) GR HR Hk Hb)).
    - (* [comment removed for export] *)
      abstract (
        intros fx A m md regs n k b ret sp0 argv envp S HG Hpure Henv H10 Hn HR Hk Hb Hmax H1 Hret H4 Hal Htop Hsp0 Hwin HK;
        apply (glue_malloc_g malloc_okX malloc_refines fx A m md regs n ret sp0 argv envp S HG Hpure Henv H10 Hn H1 Hret H4 Hal Htop Hsp0 Hwin);
        intros A' m' vm' regs' res X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 GR NR;
        destruct X4 as [(E0 & _) | (Hnz & F1 & F2 & F3 & F4)];
        [ exfalso; apply (g_noroom_absurd A m (m_vmmaps md) n k b HG (conj (proj1 Hn) Hmax) HR Hk Hb);
          apply NR; rewrite E0; reflexivity
        | apply (HK A' m' vm' regs' res X1 X2 X3 Hnz F1 F2 F3 F4 X5 X6 X7 X8 X9 X10 X11);
          exact (g_room_malloc A A' _ vm' n k b (proj1 Hn) GR HR Hk Hb) ]).
    - (* [comment removed for export] *)
      abstract (
        intros fx A m md regs cnt sz k b ret sp0 argv envp S HG Hpure Henv H10 H11 Hcnt Hsz Hn HR Hk Hb Hmax H1 Hret H4 Hal Htop Hsp0 Hwin HK;
        apply (glue_calloc_g calloc_okX calloc_refines fx A m md regs cnt sz ret sp0 argv envp S HG Hpure Henv H10 H11 Hcnt Hsz Hn H1 Hret H4 Hal Htop Hsp0 Hwin);
        intros A' m' vm' regs' res X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 GR NR;
        destruct X4 as [(E0 & _) | (Hnz & F1 & F2 & F3 & F4 & F5)];
        [ exfalso; apply (g_noroom_absurd A m (m_vmmaps md) (cnt * sz) k b HG (conj (proj1 Hn) Hmax) HR Hk Hb);
          apply NR; rewrite E0; reflexivity
        | apply (HK A' m' vm' regs' res X1 X2 X3 Hnz F1 F2 F3 F4 F5 X5 X6 X7 X8 X9 X10 X11);
          exact (g_room_malloc A A' _ vm' (cnt * sz) k b (proj1 Hn) GR HR Hk Hb) ]).
  Defined.

End Sure.
