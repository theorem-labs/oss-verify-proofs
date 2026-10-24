(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM02 YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Export YM0b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Record malloc_pcs := MPcs {
pc_malloc_impl : Z;
pc_free_impl : Z;
pc_get_meta : Z; pc_nontrivial_free : Z; pc_alloc_meta : Z; pc_alloc_slot : Z; pc_enframe : Z;
pc_vm_wait : Z; pc_mmap : Z; pc_mprotect : Z; pc_munmap : Z;
pc_syscall_ret : Z; pc_errno_location : Z; pc_stack_chk_fail : Z; pc_lock : Z; pc_unlock : Z;
pc_memcpy : Z; pc_memset : Z;
pc_allzerop : option Z;
pc_mremap : option Z
}.
Record malloc_syms := MSyms {
ms_segs : list Segment;
ms_pcs : malloc_pcs;
ms_malloc : Z;
ms_free : Z;
ms_calloc : option Z;
ms_ctx : Z;
ms_lock : Z;
ms_libc : Z;
ms_got_guard : Z;
ms_guard : Z;
ms_replaced : option Z;
ms_size_classes : Z; ms_small_cnt : Z; ms_med_cnt : Z; ms_debruijn : Z;
ms_tp : Z;
ms_errno_off : Z;
ms_realloc : option Z
}.
Definition errno_addr (B : malloc_syms) : Z := ms_tp B + ms_errno_off B.
Definition ALLOC_STACK : Z := 8192.
Definition callee_saved (r : Z) : Prop :=
r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ (18 <= r <= 27).
Definition regs_preserved (regs regs' : bvmap 5 word) : Prop :=
forall r, callee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Definition ptr_addr (L : layout) (p : sptr) : Z := loc_addr L (LMem p).
Definition reg_addr (L : layout) (r : nat) : Z := ly_reg L r.
Definition blocks (L : layout) (A : astate) : list (Z * Z) :=
map (fun b => (ptr_addr L (fst b), snd b)) (user_blocks A).
Definition layout_le (A : astate) (L L' : layout) : Prop :=
ly_ctx L' = ly_ctx L /\ ly_sec L' = ly_sec L /\ ly_brk0 L' = ly_brk0 L /\
forall r, (r < length (st_regions A))%nat -> ly_reg L' r = ly_reg L r.
Lemma layout_le_refl : forall A L, layout_le A L L.
Proof. intros A L. repeat split; reflexivity. Qed.
Definition MR_t : Type := layout -> astate -> (word -> option byte) -> Model -> Prop.
Definition present (mem : word -> option byte) (a : Z) : Prop :=
exists b, mem (Z_to_bv 64 a) = Some b.
Definition word_mem (segs : list Segment) (mem : word -> option byte) (a v : Z) : Prop :=
forall k, (k < 8)%nat -> mbyte segs mem (a + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v 8 k)).
Definition in_img (B : malloc_syms) (a : Z) : Prop := ms_segs B <> [] /\ exists s, In s (segments_reserved (ms_segs B)) /\
bv_unsigned (fst s) <= a < bv_unsigned (fst s) + bv_unsigned (snd s).
Definition AUXV_TYPES : list Z := [3; 4; 5; 16; 6; 11; 12; 23; 25; 0].
Definition auxv_pre (B : malloc_syms) (sec : Z) (lo : Z) (mem : word -> option byte) : Prop :=
exists av ar,
word_mem (ms_segs B) mem (ms_libc B + 8) av /\
(forall k, (k < 10)%nat -> word_mem (ms_segs B) mem (av + 16 * Z.of_nat k) (nth k AUXV_TYPES 0)) /\
word_mem (ms_segs B) mem (av + 16 * 8 + 8) ar /\
word_mem (ms_segs B) mem (ar + 8) sec /\
4096 <= av /\ av + 160 <= 2 ^ 63 /\ 4096 <= ar /\ ar + 16 <= 2 ^ 63 /\
lo <= av /\ lo <= ar.
Lemma auxv_pre_mono : forall B sec lo lo' mem, lo' <= lo -> auxv_pre B sec lo mem -> auxv_pre B sec lo' mem.
Proof.
intros B sec lo lo' mem Hle (av & ar & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
exists av, ar. repeat (split; [assumption|]). split; lia.
Qed.
Definition static_owned (B : malloc_syms) (a : Z) : Prop :=
(ms_lock B <= a < ms_lock B + 4) \/
(ms_libc B + 3 = a) \/ (ms_libc B + 8 <= a < ms_libc B + 16) \/ (ms_libc B + 48 <= a < ms_libc B + 56) \/
(ms_got_guard B <= a < ms_got_guard B + 8) \/ (ms_guard B <= a < ms_guard B + 8) \/
(ms_debruijn B - 108 <= a < ms_debruijn B + 32) \/ (ms_size_classes B <= a < ms_size_classes B + 96) \/
(ms_small_cnt B <= a < ms_small_cnt B + 27) \/ (ms_med_cnt B <= a < ms_med_cnt B + 4).
Definition owned (B : malloc_syms) (L : layout) (A : astate) (a : Z) : Prop :=
alloc_owned L A a \/ static_owned B a.
Record MR_laws (B : malloc_syms) (MR : MR_t) : Prop := {
mr_wf : forall L A mem md, MR L A mem md -> WF A;
mr_blocks : forall L A mem md p n i,
MR L A mem md -> In (p, n) (user_blocks A) -> 0 <= i < n ->
present mem (ptr_addr L p + i) /\
4096 <= ptr_addr L p /\ ptr_addr L p + n <= alloc_ceiling /\
~ owned B L A (ptr_addr L p + i);
mr_blocks_aligned : forall L A mem md p n,
MR L A mem md -> In (p, n) (user_blocks A) -> ptr_addr L p mod 16 = 0;
mr_blocks_range : forall L A mem md p n,
MR L A mem md -> In (p, n) (user_blocks A) -> 4096 <= ptr_addr L p /\ ptr_addr L p + n <= alloc_ceiling;
mr_blocks_disjoint : forall L A mem md,
MR L A mem md -> pairwise ranges_disjoint (blocks L A);
mr_frame : forall L A mem mem' md md',
MR L A mem md ->
(forall a, owned B L A a -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
(forall a, owned B L A a -> present mem a -> present mem' a) ->
(forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> present mem' (ptr_addr L p + i)) ->
m_vmmaps md' = m_vmmaps md -> m_halted md' = None ->
m_vm_lazy md' = [] -> m_vm_materialized md' = [] ->
MR L A mem' md';
mr_owned_low : forall L A mem md a, MR L A mem md -> owned B L A a -> 0 <= a < alloc_ceiling;
mr_model : forall L A mem md,
MR L A mem md -> m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [];
mr_ceil : forall L A mem md,
MR L A mem md -> YM05.ceil_of_top (alloc_top (m_vmmaps md))
}.
Definition req_len (q : kreq) : Z :=
match q with
| KMmapRW len | KMmapNone len => page_round len
| KMprotect _ => PGSZ
| KBrkGrow n => PGSZ * n
| KMremap _ _ new_len => new_len
| _ => 0
end.
Definition region_slots (rg : region) : Z :=
if rg_live rg then match rg_kind rg with RkBrk => rg_len rg / PGSZ | _ => 1 end else 0.
Definition nslots (s : astate) : Z :=
fold_right (fun rg acc => region_slots rg + acc) 0 (st_regions s).
Definition MG_LIVE : Z := 2 ^ 34.
Definition MG_SLOTS : Z := 2 ^ 15.
Definition MG_REQ : Z := 2 ^ 28.
Definition mgrant (s : astate) (q : kreq) : Prop :=
match q with
| KMmapRW _ | KMmapNone _ | KMprotect _ =>
0 < req_len q /\ live_bytes s + req_len q <= MG_LIVE /\ nslots s <= MG_SLOTS /\ req_len q <= MG_REQ
| KBrkGrow n => st_brk s = BrkNever /\ st_regions s = [] /\ n = 2
| KMremap _ _ _ => False
| _ => True
end.
Section h.
Variable segs : list Segment.
Definition knode (c1 : config) (q : kreq) (snap : astate) (Kont : Z -> config -> Prop) : Prop :=
match q with
| KJunk _ => exists z, 0 <= z < 256 /\ Kont z c1
| _ =>
exists (I : Type) (nx : I -> config) (bit : I -> Z) (i0 : I),
node_ok segs c1 I (fun _ => []) nx /\
(forall i, Kont (bit i) (nx i)) /\
(if fallible q
then (if spurious q
then (forall i, bit i = 0 \/ bit i = 1) /\ (exists i, bit i = 0) /\
(mgrant snap q -> exists i, bit i = 1)
else
(forall i, bit i = 0 \/ bit i = 1) /\ (mgrant snap q -> forall i, bit i = 1))
else forall i, bit i = 1)
end.
Fixpoint mreal {R : Type} (c : config) (t : itree astate R) (Q : R -> config -> Prop)
{struct t} : Prop :=
match t with
| IRet r => SR segs c (Q r)
| IFail _ => True
| IAsk q snap k => SR segs c (fun c1 => knode c1 q snap (fun z c2 => mreal c2 (k z) Q))
end.
Lemma mreal_mono {R} : forall (t : itree astate R) c (Q Q' : R -> config -> Prop),
(forall r c', Q r c' -> Q' r c') -> mreal c t Q -> mreal c t Q'.
Proof.
induction t as [r | q s k IH | f]; intros c Q Q' HQ H; cbn in *.
- eapply SR_mono; [exact H | intros c' H'; apply HQ, H'].
- eapply SR_mono; [exact H |]. intros c1 Hk. destruct q;
try (destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hcl); exists J, nx, bit, i0;
split; [exact Hn|]; split; [intros i; eapply IH; [exact HQ | apply Hc] | exact Hcl]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. eapply IH; [exact HQ | exact Hc].
- exact I.
Qed.
Lemma mreal_SR_pre {R} : forall (t : itree astate R) c Q (P : config -> Prop),
SR segs c P -> (forall c', P c' -> mreal c' t Q) -> mreal c t Q.
Proof.
intros t c Q P HP H. destruct t as [r | q s k | f]; cbn in *.
- eapply SR_bind; [exact HP | exact H].
- eapply SR_bind; [exact HP | exact H].
- exact I.
Qed.
Lemma mreal_ibind {A R} : forall (t : itree astate A) (f : A -> itree astate R) c
(P : A -> config -> Prop) (Q : R -> config -> Prop),
mreal c t P -> (forall a c', P a c' -> mreal c' (f a) Q) -> mreal c (ibind t f) Q.
Proof.
induction t as [a | q s k IH | e]; intros f c P Q H Hf; cbn in *.
- eapply mreal_SR_pre; [exact H | exact (Hf a)].
- eapply SR_mono; [exact H|]. intros c1 Hk. destruct q;
try (destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hcl); exists J, nx, bit, i0;
split; [exact Hn|]; split; [intros i; eapply IH; [apply Hc | exact Hf] | exact Hcl]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. eapply IH; [exact Hc | exact Hf].
- exact I.
Qed.
Lemma mreal_mbind {A R} : forall (m : M A) (f : A -> M R) (s : astate) c
(P : A * astate -> config -> Prop) (Q : R * astate -> config -> Prop),
mreal c (m s) P -> (forall a s' c', P (a, s') c' -> mreal c' (f a s') Q) -> mreal c (bind m f s) Q.
Proof.
intros m f s c P Q H Hf. unfold bind. eapply mreal_ibind; [exact H|]. intros [a s'] c' HP. apply Hf, HP.
Qed.
Lemma mreal_ret {R} : forall (r : R) (s : astate) c (Q : R * astate -> config -> Prop),
Q (r, s) c -> mreal c (ret r s) Q.
Proof. intros r s c Q H. cbn. apply SR_ret. exact H. Qed.
Theorem mreal_SR {R} : forall (t : itree astate R) c (Q : R -> config -> Prop),
mreal c t Q -> safe t -> SR segs c (fun c' => exists r tr, cpath t tr r /\ Q r c').
Proof.
induction t as [r | q s k IH | f]; intros c Q H Hs; cbn in *.
- eapply SR_mono; [exact H | intros c' H'; exists r, []; split; [reflexivity | exact H']].
- eapply SR_bind; [exact H|]. intros c1 Hk.
assert (STEP : forall z c2, canswer q z -> mreal c2 (k z) Q ->
SR segs c2 (fun c' => exists r tr, cpath (IAsk q s k) tr r /\ Q r c')).
{ intros z c2 Hz Hm. eapply SR_mono; [eapply IH; [exact Hm | apply Hs; apply canswer_answer_ok; exact Hz]|].
intros c' (r & tr & Hy & HQ). exists r, ((q, z) :: tr). cbn. auto. }
destruct q; cbn in STEP;
try (destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hcl);
apply (SR_node segs c1 J nx i0); [exact Hn|]; intros i; eapply STEP; [| apply Hc];
first [exact (Hcl i) | apply (proj1 Hcl)]; fail).
destruct Hk as (z & Hz & Hc). eapply STEP; [exact Hz | exact Hc].
- destruct Hs.
Qed.
Lemma rz_silent_all : forall c (I : Type) (nx : I -> config) (i0 : I) T,
node_ok segs c I (fun _ => []) nx -> (forall i, realizes segs (nx i) T) -> realizes segs c T.
Proof.
intros c I nx i0 T Hn H. apply (SR_node segs c I nx i0 (fun c' => exists i, c' = nx i) Hn).
- intros i. apply SR_ret. exists i. reflexivity.
- intros c' [i ->]. apply H.
Qed.
Lemma rz_split : forall c (I : Type) (nx : I -> config) (bit : I -> Z) (TA TB : TSet),
node_ok segs c I (fun _ => []) nx ->
(forall i, bit i = 0 \/ bit i = 1) -> (exists i, bit i = 0) -> (exists i, bit i = 1) ->
(forall i, bit i = 0 -> realizes segs (nx i) TA) ->
(forall i, bit i = 1 -> realizes segs (nx i) TB) ->
realizes segs c (t_alt2 TA TB).
Proof.
intros c I nx bit TA TB [Hsnd Hcmp] Hbits [ia Hia] [ib Hib] HA HB.
set (IA := {i : I | bit i = 0}). set (IB := {i : I | bit i = 1}).
set (nx' := fun j : IA + IB => match j with inl (exist _ i _) => nx i | inr (exist _ i _) => nx i end).
apply (rz_alt2 segs c IA IB nx' TA TB (exist _ ia Hia) (exist _ ib Hib)).
- split.
+ intros [[i Hi]|[i Hi]]; cbn; apply Hsnd.
+ intros e st Hst. destruct (Hcmp e st Hst) as (i & -> & ->).
destruct (Hbits i) as [Hi|Hi].
* exists (inl (exist _ i Hi)). split; reflexivity.
* exists (inr (exist _ i Hi)). split; reflexivity.
- intros [i Hi]. cbn. apply HA, Hi.
- intros [i Hi]. cbn. apply HB, Hi.
Qed.
Theorem mreal_tset {R} : forall (t : itree astate R) c (Q : R -> config -> Prop) (K : R -> TSet),
mreal c t Q -> safe t -> jinv K t -> gtree mgrant t ->
(forall r c' tr, cpath t tr r -> Q r c' -> realizes segs c' (K r)) ->
realizes segs c (tset t K).
Proof.
induction t as [r | q s k IH | f]; intros c Q K H Hs Hj Hg HK; cbn in H, Hs.
- apply (SR_realizes segs c (Q r)); [exact H | intros c' H'; cbn; apply (HK r c' []); [reflexivity | exact H']].
- apply (SR_realizes segs c _ _ H). intros c1 Hk.
assert (HKz : forall z, canswer q z -> forall r c' tr, cpath (k z) tr r -> Q r c' -> realizes segs c' (K r)).
{ intros z Hz r c' tr Hp HQ. apply (HK r c' ((q, z) :: tr)); [cbn; auto | exact HQ]. }
destruct q as [|np| |ln|ln|pg|rr ln|mr mol mnl|p]; cbn in Hk, Hj, Hg, HKz |- *.
+   destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hb).
apply (rz_silent_all c1 J nx i0); [exact Hn|]. intros i.
eapply IH; [rewrite <- (Hb i); apply Hc | apply Hs; exact I | exact Hj | exact Hg | apply HKz; reflexivity].
+   destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & H1).
destruct Hj as [Hj0 Hj1]. destruct Hg as (G & Hg0 & Hg1).
apply (rz_silent_all c1 J nx i0); [exact Hn|]. intros i.
eapply IH; [rewrite <- (H1 G i); apply Hc | apply Hs; exact I | exact Hj1 | exact Hg1 | apply HKz; auto].
+   destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hb).
apply (rz_silent_all c1 J nx i0); [exact Hn|]. intros i.
eapply IH; [rewrite <- (Hb i); apply Hc | apply Hs; exact I | exact Hj | exact Hg | apply HKz; reflexivity].
+   destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & H1).
destruct Hj as [Hj0 Hj1]. destruct Hg as (G & Hg0 & Hg1).
apply (rz_silent_all c1 J nx i0); [exact Hn|]. intros i.
eapply IH; [rewrite <- (H1 G i); apply Hc | apply Hs; exact I | exact Hj1 | exact Hg1 | apply HKz; auto].
+   destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & H1).
destruct Hj as [Hj0 Hj1]. destruct Hg as (G & Hg0 & Hg1).
apply (rz_silent_all c1 J nx i0); [exact Hn|]. intros i.
eapply IH; [rewrite <- (H1 G i); apply Hc | apply Hs; exact I | exact Hj1 | exact Hg1 | apply HKz; auto].
+   destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & H1).
destruct Hj as [Hj0 Hj1]. destruct Hg as (G & Hg0 & Hg1).
apply (rz_silent_all c1 J nx i0); [exact Hn|]. intros i.
eapply IH; [rewrite <- (H1 G i); apply Hc | apply Hs; exact I | exact Hj1 | exact Hg1 | apply HKz; auto].
+   destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hb).
apply (rz_silent_all c1 J nx i0); [exact Hn|]. intros i.
eapply IH; [rewrite <- (Hb i); apply Hc | apply Hs; exact I | exact Hj | exact Hg | apply HKz; reflexivity].
+   destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hbits & H0 & H1).
destruct Hj as [Hj0 Hj1]. destruct Hg as (G & Hg0 & Hg1).
eapply rz_split; [exact Hn | exact Hbits | exact H0 | apply H1; exact G | |];
intros i Hi; (eapply IH; [rewrite <- Hi; apply Hc | apply Hs; exact I | | | apply HKz; auto]); assumption.
+   destruct Hk as (z & Hz & Hc). destruct Hj as [Heq Hj].
eapply rz_conseq; [| apply (Heq z Hz)].
eapply IH; [exact Hc | apply Hs; exact Hz | apply Hj; exact Hz | apply Hg; exact Hz | apply HKz; exact Hz].
- destruct Hs.
Qed.
End h.
Section o.
Variable B : malloc_syms.
Variable MR : MR_t.
Let segs := ms_segs B.
Definition spZ (regs : bvmap 5 word) : Z := bv_unsigned (getr regs 2).
Definition scratch (regs : bvmap 5 word) (a : Z) : Prop :=
(spZ regs - ALLOC_STACK <= a < spZ regs) \/ (errno_addr B <= a < errno_addr B + 4).
Definition call_pre (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
MR L A mem md /\ WF A /\ bounded A /\
YK0s.ret_ok (getr regs 1) /\
spZ regs mod 16 = 0 /\ alloc_ceiling + ALLOC_STACK <= spZ regs /\ spZ regs < 2 ^ 63 /\
(forall a, spZ regs - ALLOC_STACK <= a < spZ regs -> writable_at segs mem a) /\
getr regs 4 = Z_to_bv 64 (ms_tp B) /\
(forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at segs mem a) /\
(st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem).
Definition call_post (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(E : Z -> Prop)
(L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
MR L' A' mem' md' /\ WF A' /\ bounded A' /\ layout_le A L L' /\
(forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ptr_addr L' p = ptr_addr L p) /\
regs_preserved regs regs' /\
(exists vm', md' = with_vmmaps vm' md) /\
(forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) ->
~ owned B L A a -> ~ owned B L' A' a -> ~ scratch regs a -> ~ E a ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> 0 <= i < n ->
mbyte segs mem' (ptr_addr L p + i) = mbyte segs mem (ptr_addr L p + i)) /\
(forall a, scratch regs a -> writable_at segs mem' a).
Definition allzero_block (A : astate) (q : sptr) : bool :=
match find_frame_in (st_metas A) q with
| Some (g, _) =>
match mlookup (st_metas A) g with
| Some (MUsed am) => (48 <=? am_sc am) || (stride_of am <? class_size (am_sc am))
| _ => false
end
| None => false
end.
Definition malloc_leaf (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (n : Z)
(r : option sptr * astate) (c' : config) : Prop :=
exists L' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
call_post L A regs mem md (fun _ => False) L' (snd r) regs' mem' md' /\
match fst r with
| None => getr regs' 10 = Z_to_bv 64 0 /\ user_blocks (snd r) = user_blocks A
| Some q => getr regs' 10 = Z_to_bv 64 (ptr_addr L' q) /\ ptr_addr L' q <> 0 /\
(exists l1 l2, user_blocks (snd r) = l1 ++ (q, n) :: l2 /\ user_blocks A = l1 ++ l2) /\
(allzero_block (snd r) q = true ->
forall i, 0 <= i < n -> mbyte segs mem' (ptr_addr L' q + i) = Some (Z_to_bv 8 0))
end.
End o.
Section u.
Variable B : malloc_syms.
Variable MR : MR_t.
Let segs := ms_segs B.
Definition malloc_realizes : Prop :=
forall L A regs mem md n,
call_pre B MR L A regs mem md ->
getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
mreal segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
(malloc n A)
(malloc_leaf B MR L A regs mem md n).
Definition free_leaf (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(p : sptr) (n : Z) (r : unit * astate) (c' : config) : Prop :=
exists L' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
call_post B MR L A regs mem md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' (snd r) regs' mem' md' /\
(exists l1 l2, user_blocks A = l1 ++ (p, n) :: l2 /\ user_blocks (snd r) = l1 ++ l2).
Definition free_realizes : Prop :=
forall L A regs mem md p n,
call_pre B MR L A regs mem md ->
In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
mreal segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
(free (Some p) A)
(free_leaf L A regs mem md p n).
Definition free_null_realizes : Prop :=
forall regs mem md,
YK0s.ret_ok (getr regs 1) -> getr regs 10 = Z_to_bv 64 0 ->
m_halted md = None -> m_vm_lazy md = [] ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
(fun c' => c' = mkCfg (mkst regs (getr regs 1) mem (seg_rom segs)) md).
Definition CALLOC_STACK : Z := ALLOC_STACK + 32.
Definition scratch_k (stk : Z) (regs : bvmap 5 word) (a : Z) : Prop :=
(spZ regs - stk <= a < spZ regs) \/ (errno_addr B <= a < errno_addr B + 4).
Definition call_pre_k (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
MR L A mem md /\ WF A /\ bounded A /\
YK0s.ret_ok (getr regs 1) /\
spZ regs mod 16 = 0 /\ alloc_ceiling + stk <= spZ regs /\ spZ regs < 2 ^ 63 /\
(forall a, spZ regs - stk <= a < spZ regs -> writable_at segs mem a) /\
getr regs 4 = Z_to_bv 64 (ms_tp B) /\
(forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at segs mem a) /\
(st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem).
Definition call_post_k (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(E : Z -> Prop)
(L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
MR L' A' mem' md' /\ WF A' /\ bounded A' /\ layout_le A L L' /\
(forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> ptr_addr L' p = ptr_addr L p) /\
regs_preserved regs regs' /\
(exists vm', md' = with_vmmaps vm' md) /\
(forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) ->
~ owned B L A a -> ~ owned B L' A' a -> ~ scratch_k stk regs a -> ~ E a ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A') -> 0 <= i < n ->
mbyte segs mem' (ptr_addr L p + i) = mbyte segs mem (ptr_addr L p + i)) /\
(forall a, scratch_k stk regs a -> writable_at segs mem' a).
Lemma call_pre_k_alloc : forall L A regs mem md, call_pre B MR L A regs mem md <-> call_pre_k ALLOC_STACK L A regs mem md.
Proof. intros. unfold call_pre, call_pre_k. tauto. Qed.
Lemma call_post_k_alloc : forall L A regs mem md E L' A' regs' mem' md',
call_post B MR L A regs mem md E L' A' regs' mem' md' <-> call_post_k ALLOC_STACK L A regs mem md E L' A' regs' mem' md'.
Proof. intros. unfold call_post, call_post_k, scratch, scratch_k. tauto. Qed.
Definition calloc_leaf (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(sz : Z) (r : option sptr * astate) (c' : config) : Prop :=
exists L' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
call_post_k CALLOC_STACK L A regs mem md (fun _ => False) L' (snd r) regs' mem' md' /\
match fst r with
| None => getr regs' 10 = Z_to_bv 64 0 /\ user_blocks (snd r) = user_blocks A
| Some q => getr regs' 10 = Z_to_bv 64 (ptr_addr L' q) /\ ptr_addr L' q <> 0 /\
(exists l1 l2, user_blocks (snd r) = l1 ++ (q, sz) :: l2 /\ user_blocks A = l1 ++ l2) /\
(forall i, 0 <= i < sz -> mbyte segs mem' (ptr_addr L' q + i) = Some (Z_to_bv 8 0))
end.
Definition calloc_realizes : Prop :=
forall pc L A regs mem md m n,
ms_calloc B = Some pc ->
call_pre_k CALLOC_STACK L A regs mem md ->
getr regs 10 = Z_to_bv 64 m -> getr regs 11 = Z_to_bv 64 n ->
0 <= m -> 0 <= n -> m * n < 4096 ->
mreal segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
(malloc (m * n) A)
(calloc_leaf L A regs mem md (m * n)).
Definition REALLOC_STACK : Z := ALLOC_STACK + 64.
Definition realloc_leaf (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(p : sptr) (nold n : Z) (r : option sptr * astate) (c' : config) : Prop :=
exists L' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
call_post_k REALLOC_STACK L A regs mem md (fun a => ptr_addr L p <= a < ptr_addr L p + nold) L' (snd r) regs' mem' md' /\
match fst r with
| None => getr regs' 10 = Z_to_bv 64 0 /\ user_blocks (snd r) = user_blocks A
| Some q => getr regs' 10 = Z_to_bv 64 (ptr_addr L' q) /\ ptr_addr L' q <> 0 /\
(exists l1 l2 m1 m2, user_blocks A = l1 ++ (p, nold) :: l2 /\ m1 ++ m2 = l1 ++ l2 /\
user_blocks (snd r) = m1 ++ (q, n) :: m2) /\
(forall i, 0 <= i < Z.min n nold ->
mbyte segs mem' (ptr_addr L' q + i) = mbyte segs mem (ptr_addr L p + i))
end.
Definition realloc_realizes : Prop :=
forall pc L A regs mem md p nold n,
ms_realloc B = Some pc ->
call_pre_k REALLOC_STACK L A regs mem md ->
In (p, nold) (user_blocks A) ->
getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> getr regs 11 = Z_to_bv 64 n ->
MMAP_THRESHOLD <= n -> MMAP_THRESHOLD < nold   ->
nold + PGSZ <= n < 2 ^ 62 ->
mreal segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
(realloc (Some p) n A)
(realloc_leaf L A regs mem md p nold n).
End u.
Section w.
Variable B : malloc_syms.
Variable MR : MR_t.
Let segs := ms_segs B.
Theorem malloc_SR :
malloc_realizes B MR ->
forall L A regs mem md n,
call_pre B MR L A regs mem md -> getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
(fun c' => exists r tr, cpath (malloc n A) tr r /\ malloc_leaf B MR L A regs mem md n r c').
Proof.
intros HM L A regs mem md n Hpre Hn Hrange.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
apply (mreal_SR segs _ _ _ (HM L A regs mem md n Hpre Hn Hrange)). apply malloc_safe; [exact HW | lia].
Qed.
Theorem free_SR :
free_realizes B MR ->
forall L A regs mem md p n,
call_pre B MR L A regs mem md -> In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
(fun c' => exists r tr, cpath (free (Some p) A) tr r /\ free_leaf B MR L A regs mem md p n r c').
Proof.
intros HF L A regs mem md p n Hpre Hin Hp.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
apply (mreal_SR segs _ _ _ (HF L A regs mem md p n Hpre Hin Hp)). eapply free_safe; [exact HW | exact Hin].
Qed.
Theorem malloc_tset :
malloc_realizes B MR ->
forall L A regs mem md n (K : option sptr * astate -> TSet),
call_pre B MR L A regs mem md -> getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
jinv K (malloc n A) -> gtree mgrant (malloc n A) ->
(forall r c' tr, cpath (malloc n A) tr r -> malloc_leaf B MR L A regs mem md n r c' -> realizes segs c' (K r)) ->
realizes segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
(tset (malloc n A) K).
Proof.
intros HM L A regs mem md n K Hpre Hn Hrange Hj Hg HK.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
apply (mreal_tset segs _ _ _ K (HM L A regs mem md n Hpre Hn Hrange)); [apply malloc_safe; [exact HW | lia] | exact Hj | exact Hg | exact HK].
Qed.
Theorem free_tset :
free_realizes B MR ->
forall L A regs mem md p n (K : unit * astate -> TSet),
call_pre B MR L A regs mem md -> In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
jinv K (free (Some p) A) -> gtree mgrant (free (Some p) A) ->
(forall r c' tr, cpath (free (Some p) A) tr r -> free_leaf B MR L A regs mem md p n r c' -> realizes segs c' (K r)) ->
realizes segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
(tset (free (Some p) A) K).
Proof.
intros HF L A regs mem md p n K Hpre Hin Hp Hj Hg HK.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
apply (mreal_tset segs _ _ _ K (HF L A regs mem md p n Hpre Hin Hp)); [eapply free_safe; [exact HW | exact Hin] | exact Hj | exact Hg | exact HK].
Qed.
End w.
Section y.
Variable B : malloc_syms.
Let segs := ms_segs B.
Record heap_pristine (mem : word -> option byte) (md : Model) : Prop := {
hp_ctx   : forall i, 0 <= i < CTX_SIZE -> mbyte segs mem (ms_ctx B + i) = Some (Z_to_bv 8 0);
hp_lock  : forall k, (k < 4)%nat -> mbyte segs mem (ms_lock B + Z.of_nat k) = Some (Z_to_bv 8 0);
hp_needlocks : mbyte segs mem (ms_libc B + 3) = Some (Z_to_bv 8 0);
hp_pagesize  : word_mem segs mem (ms_libc B + 48) 4096;
hp_got   : word_mem segs mem (ms_got_guard B) (ms_guard B);
hp_guard : exists g, word_mem segs mem (ms_guard B) g;
hp_tables : forall a, (ms_debruijn B - 108 <= a < ms_debruijn B + 32 \/ ms_size_classes B <= a < ms_size_classes B + 96 \/
ms_small_cnt B <= a < ms_small_cnt B + 27 \/ ms_med_cnt B <= a < ms_med_cnt B + 4) ->
mbyte segs mem a = seg_rom segs (Z_to_bv 64 a);
hp_vm    : vm_maps (m_vmmaps md) = [] /\ vm_noaccess (m_vmmaps md) = [] /\
vm_brk (m_vmmaps md) = vm_start_brk (m_vmmaps md) /\
valid_brk segs (vm_brk (m_vmmaps md)) /\
bv_unsigned (vm_brk (m_vmmaps md)) + 2 * 4096 <= alloc_ceiling /\
vm_reserved (m_vmmaps md) = segments_reserved segs /\
SRC_LIM_MIN <= vm_limit (m_vmmaps md) /\
vm_backing_used md <= 0;
hp_model : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [];
hp_ceil : YM05.ceil_of_top (alloc_top (m_vmmaps md))
}.
End y.
End d.
Section a0. Context {rc : YM05.RunCeil}.
Record AllocAPI (B : malloc_syms) := {
aa_MR : MR_t;
aa_laws : MR_laws B aa_MR;
aa_init : forall mem md sec, heap_pristine B mem md -> 0 <= sec < 2 ^ 64 ->
exists L, aa_MR L init_state mem md /\ ly_sec L = sec;
aa_malloc : forall {fx : YK11.FPState}, malloc_realizes B aa_MR;
aa_free : forall {fx : YK11.FPState}, free_realizes B aa_MR;
aa_free_null : forall {fx : YK11.FPState}, free_null_realizes B;
aa_calloc : forall {fx : YK11.FPState}, calloc_realizes B aa_MR
}.
End a0.
Arguments aa_MR {rc B}. Arguments aa_laws {rc B}. Arguments aa_init {rc B}. Arguments aa_malloc {rc B} _ {fx}.
Arguments aa_free {rc B} _ {fx}. Arguments aa_free_null {rc B} _ {fx}. Arguments aa_calloc {rc B} _ {fx}.
Section b0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma init_ok : WF init_state /\ bounded init_state.
Proof.
split; [apply wf_init|].
unfold bounded, usage_of, znth. cbn -[Z.lt Z.le Z.pow]. split; [|lia].
intros sc. destruct (Z.to_nat sc) as [|k] eqn:E; cbn; [lia|].
assert (H : forall k, 0 <= nth k (repeat 0 47) 0 < 2 ^ 48).
{ intros j. destruct (nth_in_or_default j (repeat 0 47) 0) as [Hin | ->]; [apply repeat_spec in Hin; subst|]; lia. }
apply H.
Qed.
Section c0.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.
Theorem api_malloc :
forall L A regs mem md n,
call_pre B MR L A regs mem md -> getr regs 10 = Z_to_bv 64 n -> 0 <= n < 2 ^ 62 ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
(fun c' => exists L' A' regs' mem' md' (res : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
call_post B MR L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
getr regs' 10 = Z_to_bv 64 res /\
((res = 0 /\ blocks L' A' = blocks L A)
\/ (res <> 0 /\ res mod 16 = 0 /\
exists b1 b2, blocks L' A' = b1 ++ (res, n) :: b2 /\ blocks L A = b1 ++ b2))).
Proof.
intros L A regs mem md n Hpre Hn Hr.
eapply SR_mono; [eapply (malloc_SR B MR (aa_malloc API)); eassumption|].
intros c' ([p A'] & tr & Hy & (L' & regs' & mem' & md' & -> & Hpost & Hres)). cbn [fst snd] in *.
assert (Haddr : forall l, incl l (user_blocks A) -> incl l (user_blocks A') ->
map (fun b : sptr * Z => (ptr_addr L' (fst b), snd b)) l = map (fun b : sptr * Z => (ptr_addr L (fst b), snd b)) l).
{ destruct Hpost as (_ & _ & _ & _ & Hstab & _). intros l. induction l as [|[q k] l IH]; intros H1 H2; [reflexivity|].
cbn [map fst snd]. rewrite (Hstab q k); [| apply H1; left; reflexivity | apply H2; left; reflexivity].
rewrite IH; [reflexivity | intros x Hx; apply H1; right; exact Hx | intros x Hx; apply H2; right; exact Hx]. }
exists L', A', regs', mem', md'.
destruct p as [q|].
- destruct Hres as (Ha0 & Hnz & (l1 & l2 & E1 & E2) & _).
assert (I1 : incl l1 (user_blocks A)) by (rewrite E2; intros x Hx; apply in_app_iff; left; exact Hx).
assert (I2 : incl l2 (user_blocks A)) by (rewrite E2; intros x Hx; apply in_app_iff; right; exact Hx).
assert (I1' : incl l1 (user_blocks A')) by (rewrite E1; intros x Hx; apply in_app_iff; left; exact Hx).
assert (I2' : incl l2 (user_blocks A')) by (rewrite E1; intros x Hx; apply in_app_iff; right; right; exact Hx).
exists (ptr_addr L' q). split; [reflexivity|]. split; [exact Hpost|]. split; [exact Ha0|].
right. split; [exact Hnz|]. split.
+ destruct Hpost as (HMR & HW' & _). eapply (mr_blocks_aligned B MR (aa_laws API)); [exact HMR |].
rewrite E1. apply in_app_iff. right. left. reflexivity.
+ exists (map (fun b : sptr * Z => (ptr_addr L (fst b), snd b)) l1), (map (fun b : sptr * Z => (ptr_addr L (fst b), snd b)) l2).
unfold blocks. rewrite E1, E2, !map_app. cbn [map fst snd].
rewrite <- (Haddr l1 I1 I1'). rewrite <- (Haddr l2 I2 I2'). split; reflexivity.
- destruct Hres as (Ha0 & Eub). exists 0. split; [reflexivity|]. split; [exact Hpost|]. split; [exact Ha0|].
left. split; [reflexivity|]. unfold blocks. rewrite Eub. apply Haddr; rewrite ?Eub; intros x Hx; exact Hx.
Qed.
Theorem api_free :
forall L A regs mem md p n,
call_pre B MR L A regs mem md -> In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
(fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
call_post B MR L A regs mem md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' mem' md' /\
exists b1 b2, blocks L A = b1 ++ (ptr_addr L p, n) :: b2 /\ blocks L' A' = b1 ++ b2).
Proof.
intros L A regs mem md p n Hpre Hin Hp.
eapply SR_mono; [eapply (free_SR B MR (aa_free API)); eassumption|].
intros c' ([[] A'] & tr & Hy & (L' & regs' & mem' & md' & -> & Hpost & (l1 & l2 & E1 & E2))). cbn [fst snd] in *.
assert (Haddr : forall l, incl l (user_blocks A) -> incl l (user_blocks A') ->
map (fun b : sptr * Z => (ptr_addr L' (fst b), snd b)) l = map (fun b : sptr * Z => (ptr_addr L (fst b), snd b)) l).
{ destruct Hpost as (_ & _ & _ & _ & Hstab & _). intros l. induction l as [|[q k] l IH]; intros H1 H2; [reflexivity|].
cbn [map fst snd]. rewrite (Hstab q k); [| apply H1; left; reflexivity | apply H2; left; reflexivity].
rewrite IH; [reflexivity | intros x Hx; apply H1; right; exact Hx | intros x Hx; apply H2; right; exact Hx]. }
assert (I1 : incl l1 (user_blocks A)) by (rewrite E1; intros x Hx; apply in_app_iff; left; exact Hx).
assert (I2 : incl l2 (user_blocks A)) by (rewrite E1; intros x Hx; apply in_app_iff; right; right; exact Hx).
assert (I1' : incl l1 (user_blocks A')) by (rewrite E2; intros x Hx; apply in_app_iff; left; exact Hx).
assert (I2' : incl l2 (user_blocks A')) by (rewrite E2; intros x Hx; apply in_app_iff; right; exact Hx).
exists L', A', regs', mem', md'. split; [reflexivity|]. split; [exact Hpost|].
exists (map (fun b : sptr * Z => (ptr_addr L (fst b), snd b)) l1), (map (fun b : sptr * Z => (ptr_addr L (fst b), snd b)) l2).
unfold blocks. rewrite E1, E2, !map_app. cbn [map fst snd].
rewrite <- (Haddr l1 I1 I1'). rewrite <- (Haddr l2 I2 I2'). split; reflexivity.
Qed.
Theorem api_free_null :
forall regs mem md,
YK0s.ret_ok (getr regs 1) -> getr regs 10 = Z_to_bv 64 0 -> m_halted md = None -> m_vm_lazy md = [] ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
(fun c' => c' = mkCfg (mkst regs (getr regs 1) mem (seg_rom segs)) md).
Proof. exact (aa_free_null API). Qed.
Theorem api_calloc :
forall pc L A regs mem md m n,
ms_calloc B = Some pc ->
call_pre_k B MR CALLOC_STACK L A regs mem md -> getr regs 10 = Z_to_bv 64 m -> getr regs 11 = Z_to_bv 64 n ->
0 <= m -> 0 <= n -> m * n < 4096 ->
SR segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md)
(fun c' => exists r tr, cpath (malloc (m * n) A) tr r /\ calloc_leaf B MR L A regs mem md (m * n) r c').
Proof.
intros pc L A regs mem md m n Hpc Hpre Hm Hn Hrm Hrn Hsm.
assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
apply (mreal_SR segs _ _ _ (aa_calloc API pc L A regs mem md m n Hpc Hpre Hm Hn Hrm Hrn Hsm)).
apply malloc_safe; [exact HW | nia].
Qed.
End c0.
End b0.
