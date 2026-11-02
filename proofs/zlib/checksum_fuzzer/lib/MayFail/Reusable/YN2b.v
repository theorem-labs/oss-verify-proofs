(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN2b.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN31.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition reg_lo (rg : region) : Z :=
match rg_kind rg with RkBrk => PGSZ | _ => 0 end.
Definition iv_lo (e : word * word) : Z := bv_unsigned (fst e).
Definition iv_len (e : word * word) : Z := bv_unsigned (snd e).
Section h.
Variable B : malloc_syms.
Record ledger_x (L : layout) (A : astate) (md : Model) : Prop := {
lx_cov : forall r rg x, region_of A r = Some rg -> rg_live rg = true ->
ly_reg L r + reg_lo rg <= x < ly_reg L r + rg_len rg ->
exists e, In e (vm_maps (m_vmmaps md)) /\ iv_lo e <= x < iv_lo e + iv_len e;
lx_maps : forall e, In e (vm_maps (m_vmmaps md)) -> 0 < iv_len e /\ iv_lo e + iv_len e <= 2 ^ 64;
lx_disj : forall e1 e2, In e1 (vm_maps (m_vmmaps md)) -> In e2 (vm_maps (m_vmmaps md)) ->
e1 = e2 \/ ranges_disjoint (iv_lo e1, iv_len e1) (iv_lo e2, iv_len e2);
lx_regs : forall r1 r2 rg1 rg2, r1 <> r2 ->
region_of A r1 = Some rg1 -> region_of A r2 = Some rg2 -> rg_live rg1 = true -> rg_live rg2 = true ->
reg_lo rg1 < rg_len rg1 -> reg_lo rg2 < rg_len rg2 ->
ranges_disjoint (ly_reg L r1 + reg_lo rg1, rg_len rg1 - reg_lo rg1)
(ly_reg L r2 + reg_lo rg2, rg_len rg2 - reg_lo rg2);
lx_in : forall e, In e (vm_maps (m_vmmaps md)) ->
exists r rg, region_of A r = Some rg /\ rg_live rg = true /\
ly_reg L r <= iv_lo e /\ iv_lo e + iv_len e <= ly_reg L r + rg_len rg;
lx_lb : State.live_bytes (vm_maps (m_vmmaps md)) <= live_bytes A;
lx_noacc : forall e, In e (vm_noaccess (m_vmmaps md)) ->
exists E, In E (vm_maps (m_vmmaps md)) /\ iv_lo E <= iv_lo e /\ iv_lo e + iv_len e <= iv_lo E + iv_len E /\
(forall r rg, region_of A r = Some rg -> rg_live rg = true -> rg_kind rg = RkMap -> 0 < rg_len rg ->
ranges_disjoint (iv_lo E, iv_len E) (ly_reg L r, rg_len rg))
}.
Definition rsv_ok (A : astate) : Prop :=
forall g am i fr, In (g, am, i, fr) (frames A) -> fr_kind fr = FUser -> 0 <= reserved_of am fr < 2 ^ 32.
Definition ama_ok (A : astate) : Prop :=
st_areas A <> [] -> (prid (st_avail_meta_areas A) < length (st_regions A))%nat.
Definition MRx : MR_t := fun L A mem md => MRc B L A mem md /\ ledger_x L A md /\ rsv_ok A /\ ama_ok A /\ span_ok A.
Lemma MRx_MRc : forall L A mem md, MRx L A mem md -> MRc B L A mem md.
Proof. intros L A mem md [H _]. exact H. Qed.
Lemma MRx_ledger_x : forall L A mem md, MRx L A mem md -> ledger_x L A md.
Proof. intros L A mem md (_ & H & _). exact H. Qed.
Lemma MRx_rsv : forall L A mem md, MRx L A mem md -> rsv_ok A.
Proof. intros L A mem md (_ & _ & H & _). exact H. Qed.
Lemma MRx_ama : forall L A mem md, MRx L A mem md -> ama_ok A.
Proof. intros L A mem md (_ & _ & _ & H & _). exact H. Qed.
Lemma MRx_span : forall L A mem md, MRx L A mem md -> span_ok A.
Proof. intros L A mem md (_ & _ & _ & _ & H). exact H. Qed.
Lemma MRx_intro : forall L A mem md, MRc B L A mem md -> ledger_x L A md -> rsv_ok A -> ama_ok A -> span_ok A -> MRx L A mem md.
Proof. intros. split; [assumption | split; [assumption | split; [assumption | split; assumption]]]. Qed.
Lemma ledger_x_same_regions : forall L A A' md md',
ledger_x L A md -> st_regions A' = st_regions A -> vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md) ->
vm_noaccess (m_vmmaps md') = vm_noaccess (m_vmmaps md)   ->
ledger_x L A' md'.
Proof.
intros L A A' md md' X ER EM EN. unfold region_of in *. split; unfold region_of, live_bytes; rewrite ?ER, ?EM, ?EN; apply X.
Qed.
Lemma ledger_x_vmmaps_eq : forall L A md md',
ledger_x L A md -> m_vmmaps md' = m_vmmaps md -> ledger_x L A md'.
Proof. intros L A md md' X E. eapply ledger_x_same_regions; [exact X | reflexivity | rewrite E; reflexivity | rewrite E; reflexivity]. Qed.
Lemma ledger_x_layout : forall L L' A md,
ledger_x L A md -> (forall r rg, region_of A r = Some rg -> ly_reg L' r = ly_reg L r) -> ledger_x L' A md.
Proof.
intros L L' A md X EL. split.
- intros r rg x Hr Hl Hx. rewrite (EL r rg Hr) in Hx. exact (lx_cov _ _ _ X r rg x Hr Hl Hx).
- apply X.
- apply X.
- intros r1 r2 rg1 rg2 Hne H1 H2 L1 L2 N1 N2. rewrite (EL r1 rg1 H1), (EL r2 rg2 H2). exact (lx_regs _ _ _ X r1 r2 rg1 rg2 Hne H1 H2 L1 L2 N1 N2).
- intros e He. destruct (lx_in _ _ _ X e He) as (r & rg & Hr & Hl & H1 & H2).
exists r, rg. rewrite (EL r rg Hr). auto.
- apply X.
- intros e He. destruct (lx_noacc _ _ _ X e He) as (E & HE & H1 & H2 & HR).
exists E. split; [exact HE|]. split; [exact H1|]. split; [exact H2|].
intros r rg Hr Hl Hk Hp. rewrite (EL r rg Hr). exact (HR r rg Hr Hl Hk Hp).
Qed.
Lemma In_map_remove : forall maps lo e, In e (map_remove maps lo) <-> In e maps /\ fst e <> lo.
Proof.
intros maps lo e. unfold map_remove. rewrite filter_In. split.
- intros [H1 H2]. split; [exact H1|]. intros E. rewrite E, bv_eqb_refl in H2. discriminate.
- intros [H1 H2]. split; [exact H1|]. apply negb_true_iff. apply bv_eqb_neq. exact H2.
Qed.
Lemma live_bytes_map_remove : forall maps lo n,
In (lo, n) maps -> State.live_bytes (map_remove maps lo) + bv_unsigned n <= State.live_bytes maps.
Proof.
induction maps as [|[a sz] maps IH]; intros lo n Hin; [destruct Hin|].
unfold map_remove in *. cbn [List.filter fst State.live_bytes]. destruct Hin as [E | Hin].
- injection E as -> ->. rewrite bv_eqb_refl. cbn [negb State.live_bytes].
assert (G : forall l, State.live_bytes (List.filter (fun p : word * word => negb (bv_eqb (fst p) lo)) l) <= State.live_bytes l).
{ induction l as [|[b m] l IHl]; cbn [List.filter fst State.live_bytes]; [lia|]. pose proof (u64_range m). destruct (negb (bv_eqb b lo)); cbn [State.live_bytes]; lia. }
specialize (G maps). lia.
- specialize (IH lo n Hin). pose proof (u64_range sz). destruct (negb (bv_eqb a lo)); cbn [State.live_bytes]; lia.
Qed.
Lemma live_bytes_kill : forall A A' r rg,
region_of A r = Some rg -> rg_live rg = true ->
(forall k, region_of A' k = if Nat.eqb k r then Some (mkRegion RkMap (rg_len rg) [] false) else region_of A k) ->
live_bytes A' = live_bytes A - rg_len rg.
Proof.
intros A A' r rg Hr Hl HA'. unfold live_bytes. unfold region_of in *.
revert r Hr HA'. generalize (st_regions A') as l'. generalize (st_regions A) as l.
induction l as [|x l IH]; intros l' r Hr HA'; [destruct r; discriminate|].
destruct l' as [|y l'].
{ specialize (HA' r). cbn in HA'. rewrite Nat.eqb_refl in HA'. destruct r; discriminate. }
destruct r as [|r].
- cbn in Hr. injection Hr as ->. pose proof (HA' 0%nat) as H0. cbn in H0. injection H0 as ->.
assert (E : l' = l).
{ apply nth_error_ext. intros k. specialize (HA' (S k)). cbn in HA'. exact HA'. }
subst l'. cbn. rewrite Hl. lia.
- pose proof (HA' 0%nat) as H0. cbn in H0. injection H0 as ->.
cbn. rewrite (IH l' r Hr) by (intros k; specialize (HA' (S k)); cbn in HA'; exact HA').
destruct (rg_live x); lia.
Qed.
Lemma In_iv_subtract_sub : forall a sz lo hi e,
hi < 2 ^ 64 -> In e (iv_subtract a sz lo hi) ->
iv_lo (a, sz) <= iv_lo e /\ iv_lo e + iv_len e <= iv_lo (a, sz) + iv_len (a, sz).
Proof.
intros a sz lo hi e Hhi Hin. unfold iv_subtract in Hin. cbv zeta in Hin.
pose proof (u64_range a) as Ha. pose proof (u64_range sz) as Hsz. unfold iv_lo, iv_len. cbn [fst snd].
apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
- destruct (bv_unsigned a <? lo) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E.
destruct Hin as [<- | []]. cbn [fst snd]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
pose proof (Z.mod_le (Z.min (bv_unsigned sz) (lo - bv_unsigned a)) (2 ^ 64) ltac:(lia) ltac:(lia)). lia.
- destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E.
destruct Hin as [<- | []]. cbn [fst snd]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (Z.max (bv_unsigned a) hi)) by lia.
pose proof (Z.mod_le (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi) (2 ^ 64) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma In_maps_subtract_sub : forall l lo hi e,
hi < 2 ^ 64 -> In e (maps_subtract l lo hi) ->
exists e0, In e0 l /\ iv_lo e0 <= iv_lo e /\ iv_lo e + iv_len e <= iv_lo e0 + iv_len e0.
Proof.
induction l as [|[a sz] l IH]; intros lo hi e Hhi Hin; [destruct Hin|].
cbn [maps_subtract] in Hin. apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
- exists (a, sz). split; [left; reflexivity|]. exact (In_iv_subtract_sub a sz lo hi e Hhi Hin).
- destruct (IH lo hi e Hhi Hin) as (e0 & H0 & H1 & H2). exists e0. split; [right; exact H0 | auto].
Qed.
Lemma munmap_model_noaccess : forall addr n md,
vm_noaccess (m_vmmaps (munmap_model addr n md)) = maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n).
Proof. reflexivity. Qed.
Lemma ledger_x_munmap : forall L A A' md r rg,
ledger_x L A md ->
region_of A r = Some rg -> rg_live rg = true -> rg_kind rg = RkMap ->
In (Z_to_bv 64 (ly_reg L r), Z_to_bv 64 (rg_len rg)) (vm_maps (m_vmmaps md)) ->
0 <= ly_reg L r -> 0 <= rg_len rg -> ly_reg L r + rg_len rg < 2 ^ 64 ->
(forall k, region_of A' k = if Nat.eqb k r then Some (mkRegion RkMap (rg_len rg) [] false) else region_of A k) ->
ledger_x L A' (munmap_model (Z_to_bv 64 (ly_reg L r)) (Z_to_bv 64 (rg_len rg)) md).
Proof.
intros L A A' md r rg X Hr Hl Hk Hin Hlo Hlen0 Hhi HA'.
assert (Elen : bv_unsigned (Z_to_bv 64 (rg_len rg)) = rg_len rg).
{ rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
assert (Hlen : 0 < rg_len rg).
{ destruct (lx_maps _ _ _ X _ Hin) as [H _]. unfold iv_len in H. cbn [snd] in H. rewrite Elen in H. exact H. }
assert (Ebase : bv_unsigned (Z_to_bv 64 (ly_reg L r)) = ly_reg L r).
{ rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
assert (VM : vm_maps (m_vmmaps (munmap_model (Z_to_bv 64 (ly_reg L r)) (Z_to_bv 64 (rg_len rg)) md))
= map_remove (vm_maps (m_vmmaps md)) (Z_to_bv 64 (ly_reg L r))) by reflexivity.
split; rewrite ?VM.
- intros r2 rg2 x Hr2 Hl2 Hx. rewrite HA' in Hr2.
destruct (Nat.eqb_spec r2 r) as [->|Hne]; [injection Hr2 as <-; discriminate|].
destruct (lx_cov _ _ _ X r2 rg2 x Hr2 Hl2 Hx) as (e & He & Hex).
exists e. split; [|exact Hex]. apply In_map_remove. split; [exact He|]. intros Efst.
destruct (lx_disj _ _ _ X e _ He Hin) as [-> | D].
+ unfold iv_lo, iv_len in Hex. cbn [fst snd] in Hex. rewrite Ebase, Elen in Hex.
pose proof (lx_regs _ _ _ X r2 r rg2 rg Hne Hr2 Hr Hl2 Hl) as D2.
unfold ranges_disjoint, reg_lo in D2. cbn [fst snd] in D2. rewrite Hk in D2.
unfold reg_lo in Hx. destruct (rg_kind rg2); unfold PGSZ in *; lia.
+ unfold ranges_disjoint, iv_lo, iv_len in D. cbn [fst snd] in D. rewrite Efst, Ebase, Elen in D.
destruct (lx_maps _ _ _ X e He) as [P _]. unfold iv_len, iv_lo in *. rewrite Efst, Ebase in Hex. lia.
- intros e He. apply In_map_remove in He as [He _]. exact (lx_maps _ _ _ X e He).
- intros e1 e2 H1 H2. apply In_map_remove in H1 as [H1 _]. apply In_map_remove in H2 as [H2 _].
exact (lx_disj _ _ _ X e1 e2 H1 H2).
- intros r1 r2 rg1 rg2 Hne H1 H2 L1 L2 M1 M2. rewrite HA' in H1, H2.
destruct (Nat.eqb_spec r1 r) as [->|N1]; [injection H1 as <-; discriminate|].
destruct (Nat.eqb_spec r2 r) as [->|N2]; [injection H2 as <-; discriminate|].
exact (lx_regs _ _ _ X r1 r2 rg1 rg2 Hne H1 H2 L1 L2 M1 M2).
- intros e He. apply In_map_remove in He as [He Hne].
destruct (lx_in _ _ _ X e He) as (r2 & rg2 & Hr2 & Hl2 & G1 & G2).
destruct (Nat.eq_dec r2 r) as [->|Hne2].
+
rewrite Hr in Hr2. injection Hr2 as <-.
destruct (lx_disj _ _ _ X e _ He Hin) as [-> | D]; [exfalso; apply Hne; reflexivity|].
exfalso. unfold ranges_disjoint, iv_lo, iv_len in D. cbn [fst snd] in D. rewrite Ebase, Elen in D.
destruct (lx_maps _ _ _ X e He) as [P _]. unfold iv_lo, iv_len in *. lia.
+ exists r2, rg2. rewrite HA'. rewrite (proj2 (Nat.eqb_neq _ _) Hne2). auto.
- rewrite (live_bytes_kill A A' r rg Hr Hl HA').
pose proof (live_bytes_map_remove _ _ _ Hin) as LB. rewrite Elen in LB. pose proof (lx_lb _ _ _ X). lia.
-
intros e He. rewrite munmap_model_noaccess, Ebase, Elen in He.
destruct (In_maps_subtract_sub _ _ _ _ Hhi He) as (e0 & He0 & S1 & S2).
destruct (lx_noacc _ _ _ X e0 He0) as (E & HE & G1 & G2 & HR).
exists E. split.
+ apply In_map_remove. split; [exact HE|]. intros Efst.
pose proof (HR r rg Hr Hl Hk Hlen) as D. destruct (lx_maps _ _ _ X E HE) as [P _].
unfold ranges_disjoint, iv_lo, iv_len in *. cbn [fst snd] in D. rewrite Efst, Ebase in D. lia.
+ split; [lia|]. split; [lia|]. intros r2 rg2 Hr2 Hl2 Hk2 Hp2. rewrite HA' in Hr2.
destruct (Nat.eqb_spec r2 r) as [->|Hne2]; [injection Hr2 as <-; discriminate|]. exact (HR r2 rg2 Hr2 Hl2 Hk2 Hp2).
Qed.
Lemma rsv_ok_sub : forall A A', rsv_ok A -> (forall f, In f (frames A') -> In f (frames A)) -> rsv_ok A'.
Proof. intros A A' H Hs g am i fr Hin Hk. apply (H g am i fr); [apply Hs; exact Hin | exact Hk]. Qed.
Theorem MRx_laws : MR_laws B MRx.
Proof.
pose proof (MRc_laws B) as LW. split.
- intros L A mem md M. exact (mr_wf _ _ LW L A mem md (MRx_MRc _ _ _ _ M)).
- intros L A mem md p n i M. exact (mr_blocks _ _ LW L A mem md p n i (MRx_MRc _ _ _ _ M)).
- intros L A mem md p n M. exact (mr_blocks_aligned _ _ LW L A mem md p n (MRx_MRc _ _ _ _ M)).
- intros L A mem md p n M. exact (mr_blocks_range _ _ LW L A mem md p n (MRx_MRc _ _ _ _ M)).
- intros L A mem md M. exact (mr_blocks_disjoint _ _ LW L A mem md (MRx_MRc _ _ _ _ M)).
- intros L A mem mem' md md' M Hown Hpres Hblk Hvm Hh Hlz Hmat. destruct M as (M & X & R & AA & SPK).
split; [| split; [| split; [exact R | split; [exact AA | exact SPK]]]].
+ exact (mr_frame _ _ LW L A mem mem' md md' M Hown Hpres Hblk Hvm Hh Hlz Hmat).
+ eapply ledger_x_vmmaps_eq; [exact X | exact Hvm].
- intros L A mem md a M. exact (mr_owned_low _ _ LW L A mem md a (MRx_MRc _ _ _ _ M)).
- intros L A mem md M. exact (mr_model _ _ LW L A mem md (MRx_MRc _ _ _ _ M)).
-   intros L A mem md M. exact (mr_ceil _ _ LW L A mem md (MRx_MRc _ _ _ _ M)).
Qed.
Lemma ledger_x_init : forall L md, vm_maps (m_vmmaps md) = [] -> vm_noaccess (m_vmmaps md) = []   ->
ledger_x L init_state md.
Proof.
intros L md E EN. split; rewrite ?E, ?EN.
- intros r rg x Hr. unfold region_of in Hr. cbn in Hr. destruct r; discriminate.
- intros e [].
- intros e1 e2 [].
- intros r1 r2 rg1 rg2 _ H1. unfold region_of in H1. cbn in H1. destruct r1; discriminate.
- intros e [].
- cbn. lia.
- intros e [].
Qed.
Lemma rsv_ok_init : rsv_ok init_state.
Proof. intros g am i fr Hin. cbn in Hin. destruct Hin. Qed.
Lemma ama_ok_init : ama_ok init_state.
Proof. intros H. exfalso. apply H. reflexivity. Qed.
Theorem MRx_init : forall mem md sec,
syms_ok B -> heap_pristine B mem md -> 0 <= sec < 2 ^ 64 -> exists L, MRx L init_state mem md /\ ly_sec L = sec.
Proof.
intros mem md sec SO HP Hsec. exists (layout0 B (bv_unsigned (vm_brk (m_vmmaps md))) sec). split; [| reflexivity].
split; [apply MRc_init; assumption | split; [| split; [apply rsv_ok_init | split; [apply ama_ok_init | apply span_ok_init]]]].
apply ledger_x_init; [exact (proj1 (hp_vm _ _ _ HP)) | exact (proj1 (proj2 (hp_vm _ _ _ HP)))].
Qed.
End h.
Lemma mreal_itok {R} : forall segs (t : itree astate R) c (P : R -> config -> Prop) (Q : R -> Prop),
mreal segs c t P -> itok t Q -> mreal segs c t (fun r c' => P r c' /\ Q r).
Proof.
intros segs t. induction t as [r | q s k IH | f]; intros c P Q HM HT; cbn in *.
- eapply SR_mono; [exact HM|]. intros c' HP. split; [exact HP | exact HT].
- destruct HT as [_ HT]. eapply SR_mono; [exact HM|]. intros c1 Hk.
destruct q;
try (destruct Hk as (J & nx & bit & j0 & Hn & Hc & Hcl); exists J, nx, bit, j0;
split; [exact Hn|]; split; [| exact Hcl]; intros j; apply IH; [apply Hc | apply HT; exact I]).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. apply IH; [exact Hc | apply HT; exact Hz].
- exact I.
Qed.
Section o.
Variable B : malloc_syms.
Let segs := ms_segs B.
Record midrep (L : layout) (A : astate) (mem : word -> option byte) (md : Model) : Prop := {
mid_syms : syms_ok B;
mid_mem : memrep B L A mem;
mid_tailg : tail_geom L A;
mid_statics : statics_ok B mem;
mid_ledger : ledger_ok B L A md;
mid_ledgerx : ledger_x L A md;
mid_layout : layout_ok L A;
mid_ctx : ly_ctx L = ms_ctx B;
mid_sec : 0 <= ly_sec L < 2 ^ 64;
mid_md : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = []
}.
Lemma MRx_midrep : forall L A mem md, MRx B L A mem md -> midrep L A mem md.
Proof.
intros L A mem md (M & X & _ & _). split; try (exact X).
- exact (mc_syms _ _ _ _ _ M).
- exact (MRc_memrep B L A mem md M).
- exact (mc_tail_geom _ _ _ _ _ M).
- exact (mc_statics _ _ _ _ _ M).
- exact (mc_ledger _ _ _ _ _ M).
- exact (mc_layout _ _ _ _ _ M).
- exact (mc_ctx _ _ _ _ _ M).
- exact (mc_sec _ _ _ _ _ M).
- exact (mc_md _ _ _ _ _ M).
Qed.
Lemma midrep_MRx : forall L A mem md,
midrep L A mem md -> WF A -> bounded A -> rsv_ok A -> ama_ok A -> span_ok A -> MRx B L A mem md.
Proof.
intros L A mem md M HW HB HR HA HSP. apply MRx_intro; [| exact (mid_ledgerx _ _ _ _ M) | exact HR | exact HA | exact HSP].
destruct (mid_md _ _ _ _ M) as (H1 & H2 & H3).
apply (MRc_intro B L A mem md (mid_syms _ _ _ _ M) HW HB (mid_layout _ _ _ _ M) (mid_ctx _ _ _ _ M) (mid_sec _ _ _ _ M)
(mid_mem _ _ _ _ M) (mid_tailg _ _ _ _ M) (mid_statics _ _ _ _ M) (mid_ledger _ _ _ _ M) H1 H2 H3).
Qed.
Definition in_nonmap_region (L : layout) (A : astate) (x : Z) : Prop :=
(exists r rg, region_of A r = Some rg /\ rg_live rg = true /\ rg_kind rg <> RkMap /\
ly_reg L r <= x < ly_reg L r + rg_len rg) /\
~ (exists r rg, region_of A r = Some rg /\ rg_live rg = true /\ rg_kind rg = RkMap /\
ly_reg L r <= x < ly_reg L r + rg_len rg).
Definition call_scratch (sp : Z) (stack : Z) (x : Z) : Prop :=
(sp - stack <= x < sp) \/ (errno_addr B <= x < errno_addr B + 4).
Definition callee_pre (regs : bvmap 5 word) (mem : word -> option byte) (stack : Z) : Prop :=
YK0s.ret_ok (getr regs 1) /\
spZ regs mod 16 = 0 /\ alloc_ceiling + stack <= spZ regs /\ spZ regs < 2 ^ 63 /\
(forall a, spZ regs - stack <= a < spZ regs -> writable_at segs mem a) /\
getr regs 4 = Z_to_bv 64 (ms_tp B) /\
(forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at segs mem a).
Definition callee_post (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(stack : Z)
(L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
midrep L' A' mem' md' /\ layout_le A L L' /\
regs_preserved regs regs' /\
(exists vm', md' = with_vmmaps vm' md) /\
(forall x, 0 <= x < 2 ^ 64 ->
~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE) -> ~ in_nonmap_region L' A' x -> ~ call_scratch (spZ regs) stack x ->
mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) /\
(forall a, call_scratch (spZ regs) stack a -> writable_at segs mem' a).
Definition AM_STACK : Z := 160.
Definition AS_STACK : Z := ALLOC_STACK - 48.
Definition alloc_meta_hyp : Prop :=
forall X R U L A regs mem md,
Inv X R U A ->
(forall x am, In x X -> MT A x <> Some (MUsed am)) ->
ama_ok A -> bounded A ->
midrep L A mem md ->
(st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem) ->
callee_pre regs mem AM_STACK ->
mreal segs (mkCfg (mkst regs (Z_to_bv 64 (pc_alloc_meta (ms_pcs B))) mem (seg_rom segs)) md)
(alloc_meta A)
(fun r c' => exists L' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
callee_post L A regs mem md AM_STACK L' (snd r) regs' mem' md' /\ ama_ok (snd r) /\ bounded (snd r) /\
getr regs' 10 = Z_to_bv 64 (match fst r with None => 0 | Some m => ptr_addr L' m end) /\
(match fst r with Some m => ptr_addr L' m <> 0 | None => True end)).
Definition alloc_slot_hyp : Prop :=
forall L A regs mem md sc n,
Inv [] None U0 A -> ama_ok A -> bounded A -> rsv_ok A -> span_ok A -> 0 <= sc < 48 -> 0 <= n < MMAP_THRESHOLD -> n + IB <= class_size sc ->
midrep L A mem md ->
(st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem) ->
callee_pre regs mem AS_STACK ->
getr regs 10 = Z_to_bv 64 sc -> getr regs 11 = Z_to_bv 64 n ->
mreal segs (mkCfg (mkst regs (Z_to_bv 64 (pc_alloc_slot (ms_pcs B))) mem (seg_rom segs)) md)
(alloc_slot NEST_FUEL sc n A)
(fun r c' => exists L' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
midrep L' (snd r) mem' md' /\ ama_ok (snd r) /\ bounded (snd r) /\ rsv_ok (snd r) /\ span_ok (snd r) /\ layout_le A L L' /\
regs_preserved regs regs' /\
(exists vm', md' = with_vmmaps vm' md) /\
(forall x, 0 <= x < 2 ^ 64 ->
~ owned B L A x -> ~ owned B L' (snd r) x -> ~ in_nonmap_region L' (snd r) x ->
~ call_scratch (spZ regs) AS_STACK x ->
mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) /\
(forall a, call_scratch (spZ regs) AS_STACK a -> writable_at segs mem' a) /\
getr regs' 10 = Z_to_bv 64 (fst r) /\
(0 <= fst r -> forall g am, active_hd (snd r) sc = Some g -> MT (snd r) g = Some (MUsed am) ->
stride_of am < class_size sc ->
forall i, 0 <= i < stride_of am - IB ->
mbyte segs mem' (ptr_addr L' (slot_start am (fst r)) + i) = Some (Z_to_bv 8 0))).
Definition malloc_small_hyp : Prop :=
forall L A regs mem md n,
call_pre B (MRx B) L A regs mem md ->
getr regs 10 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD ->
mreal segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
(malloc n A)
(malloc_leaf B (MRx B) L A regs mem md n).
End o.
End d.
