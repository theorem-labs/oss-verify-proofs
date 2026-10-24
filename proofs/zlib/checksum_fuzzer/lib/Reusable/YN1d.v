(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0s YK0h YK0i YK14 YK1b YK1a YK15 YK0v YK02 YP0n YM06 YK1j YM00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s YO0x YO0z YO14 YO0v YO0q YO0u YO15 YO10 YO12 YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0c YO0b YN01 YN03 YN02
YN2b YN2e YN0g YN0d YN0c YN25 YN0a YN0p
YN2j YN2h YN2n YN2m YN2d
YN2k YN0j YN0h YN0i YN1k YN2w YN31.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation B := src0_msyms.
Ltac inlist := cbn; repeat (first [left; reflexivity | right]).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mbyte_ext1 : forall m m' a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte src0segs m' a = mbyte src0segs m a.
Proof. intros m m' a E. unfold mbyte. rewrite E. reflexivity. Qed.
Lemma writable_ext1 : forall m m' a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> writable_at src0segs m a -> writable_at src0segs m' a.
Proof. intros m m' a E. unfold writable_at, wview. rewrite E. exact (fun H => H). Qed.
Lemma word_mem_ext1 : forall m m' a v, (forall k, (k < 8)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
word_mem src0segs m a v -> word_mem src0segs m' a v.
Proof. intros m m' a v E H k Hk. rewrite (mbyte_ext1 m m' _ (E k Hk)). apply H. exact Hk. Qed.
Lemma st_ok_mkst : forall E ss ms, st_ok src0segs E ss ms -> ss_resv ss = None ->
ms = mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (seg_rom src0segs).
Proof.
intros E ss [rg fr pc svc rv fcsr m rom] (S1 & S2 & S3 & S4 & S5 & S6 & _) Hrv. cbn in *. rewrite Hrv in S4. cbn in S4. subst. reflexivity.
Qed.
Lemma filter_all {T} : forall (f : T -> bool) l, (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof.
intros f l H. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)). f_equal. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.
Lemma used_metasX_all : forall X s, rawX X s ->
(forall g am, In (g, am) (used_metas s) -> MT s g = Some (MUsed am)) ->
used_metasX X s = used_metas s.
Proof.
intros X s XR UM. unfold used_metasX. apply filter_all. intros [g am] Hin. cbn [fst].
destruct (memb g X) eqn:E; [| reflexivity]. exfalso. apply (proj1 (memb_In g X)) in E. pose proof (UM g am Hin) as H2. destruct (XR g E) as [H1|H1]; rewrite H1 in H2; discriminate.
Qed.
Section AS.
Variables (X : list sptr) (U : Z -> Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (sc n stk : Z).
Hypothesis HI : Inv X None U A.
Hypothesis XR : rawX X A.
Hypothesis AMA : ama_ok A.
Hypothesis BND : bounded A.
Hypothesis RSV : rsv_ok A.
Hypothesis SPOK : span_ok A.
Hypothesis Hsc : 0 <= sc < 48.
Hypothesis Hn : 0 <= n < MMAP_THRESHOLD.
Hypothesis MID : midrep B L A mem md.
Hypothesis AUXP : st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem.
Hypothesis PRE : callee_pre B regs mem stk.
Hypothesis Hstk : ASF <= stk <= AS_STACK.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 sc.
Hypothesis R11 : getr regs 11 = Z_to_bv 64 n.
Hypothesis AMH : alloc_meta_hyp B.
Variable g : Z.
Hypothesis Hg : word_mem src0segs mem GUARD g.
Variables (j1 j2 : Z).
Let sp : Z := bv_unsigned (getr regs 2).
Let XC : Xclean X A := fun x am Hx H => ltac:(destruct (XR x Hx) as [EXR|EXR]; rewrite EXR in H; discriminate).
Definition cs (k : nat) : Z :=
match k with
| 32%nat => g
| 33%nat => LOCK + 8 * sc
| 34%nat => onum L (active_hd A sc)
| 35%nat => scl_of sc
| 36%nat => SCT + 2 * sc
| 37%nat => j1
| 38%nat => j2
| _ => 0
end.
Let E00 : env := E0 regs cs.
Definition POST (r : Z * astate) (c' : config) : Prop :=
exists L' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom src0segs)) md' /\
midrep B L' (snd r) mem' md' /\ ama_ok (snd r) /\ bounded (snd r) /\ rsv_ok (snd r) /\ span_ok (snd r) /\ layout_le A L L' /\
regs_preserved regs regs' /\
(exists vm', md' = with_vmmaps vm' md) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE) -> ~ owned B L A x -> ~ owned B L' (snd r) x -> ~ in_nonmap_region L' (snd r) x ->
~ call_scratch B (spZ regs) stk x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) /\
(forall a, call_scratch B (spZ regs) stk a -> writable_at src0segs mem' a) /\
getr regs' 10 = Z_to_bv 64 (fst r) /\
(0 <= fst r -> forall gg am, active_hd (snd r) sc = Some gg -> MT (snd r) gg = Some (MUsed am) -> stride_of am < class_size sc ->
forall i, 0 <= i < stride_of am - IB -> mbyte src0segs mem' (ptr_addr L' (slot_start am (fst r)) + i) = Some (Z_to_bv 8 0)) /\
as_keep X A (snd r) /\ word_mem src0segs mem' GUARD g.
Definition FRM (W : Z -> Prop) (m : word -> option byte) : Prop :=
forall x, 0 <= x < 2 ^ 64 -> ~ W x -> m (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Definition WS (x : Z) : Prop := sp - ASF <= x < sp.
Definition at_st (ss : sstate) (W : Z -> Prop) (mdl : Model) (c : config) : Prop :=
exists E ms, c = mkCfg ms mdl /\ st_ok src0segs E ss ms /\ env_agree 40 E00 E /\ FRM W (ms_mem ms).
Lemma pre_facts : YK0s.ret_ok (getr regs 1) /\ sp mod 16 = 0 /\ alloc_ceiling + stk <= sp /\ sp < 2 ^ 63 /\
(forall a, sp - stk <= a < sp -> writable_at src0segs mem a) /\ getr regs 4 = Z_to_bv 64 TP /\
(forall a, ERRNO <= a < ERRNO + 4 -> writable_at src0segs mem a).
Proof.
destruct PRE as (P1 & P2 & P3 & P4 & P5 & P6 & P7). unfold spZ in *. fold sp in P2, P3, P4, P5.
repeat split; try assumption.
Qed.
Lemma md_facts : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [].
Proof. exact (mid_md _ _ _ _ _ MID). Qed.
Lemma agree_cs : forall E k, env_agree 40 E00 E -> (32 <= k < 40)%nat -> ew E k = Z_to_bv 64 (cs k).
Proof. intros E k [HA _] Hk. rewrite (HA k) by lia. subst E00. apply E0_cx. lia. Qed.
Lemma sv_cs : forall E k, env_agree 40 E00 E -> (32 <= k < 40)%nat -> sv_denot E (SOff k 0) = Z_to_bv 64 (cs k).
Proof. intros E k HA Hk. cbn [sv_denot]. rewrite (agree_cs E k HA Hk). pose proof (u64_range (Z_to_bv 64 (cs k))). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma agree_reg : forall E k, env_agree 40 E00 E -> (1 <= k <= 31)%nat -> ew E k = getr regs (Z_to_bv 5 (Z.of_nat k)).
Proof. intros E k [HA _] Hk. rewrite (HA k) by lia. subst E00. apply E0_reg. lia. Qed.
Lemma guard_of_state : forall E ss ms i, st_ok src0segs E ss ms -> env_agree 40 E00 E -> nth_error (ss_mem ss) i = Some R_guard ->
word_mem src0segs (ms_mem ms) GUARD g.
Proof.
intros E ss ms i HS HA Hi. destruct (st_ok_region src0segs E ss ms i R_guard HS Hi) as (_ & _ & _ & HC).
cbn [r_chunks R_guard r_base base_val] in HC. apply Forall_inv in HC.
replace GUARD with (0 + GUARD) by lia. apply (word_mem_of_chunk src0segs E (ms_mem ms) 0 GUARD (SOff 32 0) g HC).
rewrite (sv_cs E 32 HA) by lia. reflexivity.
Qed.
Lemma key_addr_range : forall q, In q (keys A) -> 4096 <= ptr_addr L q /\ ptr_addr L q + META_SIZE <= alloc_ceiling /\
(forall x, ptr_addr L q <= x < ptr_addr L q + META_SIZE -> ~ in_img B x).
Proof.
intros q Hq. destruct (inv_keys HI) as (_ & KP & _ & _ & Hamc). destruct (KP q Hq) as (a & k & Ha & Hk & ->).
assert (Hh : handed A a <= METAS_PER_AREA) by (unfold handed; destruct (sptr_eqb a _); lia).
rewrite ptr_addr_padd. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *.
pose proof (fun x Hx => areas_off_img B X None U L A mem md HI MID a x Ha Hx) as AO. unfold PGSZ in AO.
split; [| split].
- destruct (AO (ptr_addr L a) ltac:(lia)) as [_ R]. lia.
- destruct (AO (ptr_addr L a + 4095) ltac:(lia)) as [_ R]. nia.
- intros x Hx. apply (proj1 (AO x ltac:(nia))).
Qed.
Lemma cs_facts : LOCK <= cs 33 <= LOCK + 376 /\ cs 33 mod 8 = 0 /\ 0 <= cs 34 <= 2 ^ 63 /\ 1 <= cs 35 <= 8191 /\ SCT <= cs 36 <= SCT + 94 /\ cs 36 mod 2 = 0 /\
(cs 34 = 0 <-> active_hd A sc = None) /\ class_size sc = 16 * cs 35.
Proof.
pose proof (proj1 alloc_ceiling_val) as AC. cbn [cs].
assert (H33 : (LOCK + 8 * sc) mod 8 = 0) by (rewrite Z.mul_comm, Z.mod_add by lia; unfold LOCK, src0_D_malloc_lock; reflexivity).
assert (H36 : (SCT + 2 * sc) mod 2 = 0) by (rewrite Z.mul_comm, Z.mod_add by lia; unfold SCT, src0_D_size_classes; reflexivity).
pose proof (class_size_bounds sc Hsc) as CB. unfold class_size, UNIT in CB.
assert (Escl : scl_of sc = znth sc size_classes) by (unfold scl_of; replace (sc <? 48) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
split; [lia|]. split; [exact H33|]. split.
{ destruct (active_hd A sc) as [q|] eqn:Eh; cbn [onum]; [| lia].
pose proof (active_head_key X None U A HI (Z.to_nat sc) q ltac:(lia) ltac:(unfold active_hd in Eh; exact Eh)) as Hk.
pose proof (key_addr_range q Hk) as (R1 & R2 & _). unfold META_SIZE in R2. lia. }
split; [rewrite Escl; lia|]. split; [lia|]. split; [exact H36|]. split.
- destruct (active_hd A sc) as [q|] eqn:Eh; cbn [onum]; [| split; intros; reflexivity].
pose proof (active_head_key X None U A HI (Z.to_nat sc) q ltac:(lia) ltac:(unfold active_hd in Eh; exact Eh)) as Hk.
pose proof (key_addr_range q Hk) as (R1 & R2 & _). unfold META_SIZE in R2. split; [intros H0; exfalso; lia | intros H0; discriminate].
- rewrite Escl. unfold class_size, UNIT. reflexivity.
Qed.
Lemma midrep_stack_gen : forall X' L1 A1 m md1 m', Inv X' None U A1 -> Xclean X' A1 -> ama_ok A1 -> midrep B L1 A1 m md1 ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WS x -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) -> midrep B L1 A1 m' md1.
Proof.
intros X1 L1 A1 m1 md1 m' HI1 XC1 AMA1 MID1 FR. pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts as (_ & _ & P3 & _).
assert (Wdec : forall x, WS x \/ ~ WS x) by (intros x; unfold WS; lia).
assert (LOW : forall x, WS x -> alloc_ceiling <= x) by (intros x Hx; unfold WS, ASF in *; lia).
pose proof (inv_areas HI1) as (NDA & Hareas & _). pose proof (mid_syms _ _ _ _ _ MID1) as SO.
assert (MR' : memrep B L1 A1 m').
{ refine (memrep_xfer B X1 None U L1 L1 A1 A1 m1 m' md1 HI1 XC1 AMA1 MID1 eq_refl [] _ _ NDA _ _ eq_refl eq_refl _ WS Wdec FR _ [] _ _ _ _ _ _ _ _ _).
- rewrite app_nil_r. reflexivity.
- intros p q l H. discriminate.
- intros k rg H _ _. exact H.
- intros k rg H _ _. exact H.
- intros; reflexivity.
- intros x k rg Hx Hk Hl Hkd Hin. pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID1) k rg Hk Hl) as (_ & _ & Phi & _). pose proof (LOW x Hx). lia.
- intros x a Hx Ha Hin. exfalso. destruct (areas_off_img B X1 None U L1 A1 m1 md1 HI1 MID1 a x Ha Hin) as [_ Rx]. pose proof (LOW x Hx). lia.
- intros x a Hx Ha Hin. exfalso. destruct (areas_off_img B X1 None U L1 A1 m1 md1 HI1 MID1 a x Ha Hin) as [_ Rx]. pose proof (LOW x Hx). lia.
- intros q [].
- intros q [].
- intros; reflexivity.
- intros p H. discriminate.
- intros p c H. discriminate.
- intros p x H. discriminate.
- intros c Hc. left. split; [exact Hc|]. intros k Hk Hw. pose proof (LOW _ Hw) as LW.
destruct (In_ctx_cells A1 c Hc) as (off & El & Ho1 & Ho2). rewrite El in LW. pose proof (so_ctx_hi _ SO). rewrite B_ctx in *. unfold CTX, src0_D_malloc_context, CTX_SIZE in *. lia. }
split.
- exact SO.
- exact MR'.
- eapply (tail_geom_xfer B X1 None U L1 L1 A1 A1 m1 md1 HI1 XC1 MID1); [reflexivity | intros k rg H _ _; exact H | reflexivity | intros; reflexivity].
- apply (YN2d.statics_ok_ext B A1 0 m1); [| exact (mid_statics _ _ _ _ _ MID1)]. intros x Hx. apply FR; [| intros Hw; pose proof (LOW x Hw); pose proof (so_img_hi _ SO x (so_statics_img _ SO x Hx)); lia].
pose proof (so_img_hi _ SO x (so_statics_img _ SO x Hx)). lia.
- exact (mid_ledger _ _ _ _ _ MID1).
- exact (mid_ledgerx _ _ _ _ _ MID1).
- exact (mid_layout _ _ _ _ _ MID1).
- exact (mid_ctx _ _ _ _ _ MID1).
- exact (mid_sec _ _ _ _ _ MID1).
- exact (mid_md _ _ _ _ _ MID1).
Qed.
Lemma midrep_stack : forall m', (forall x, 0 <= x < 2 ^ 64 -> ~ WS x -> m' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) -> midrep B L A m' md.
Proof. intros m' FR. exact (midrep_stack_gen X L A mem md m' HI XC AMA MID FR). Qed.
Let ms0 := mkst regs (Z_to_bv 64 src0_A_alloc_slot) mem (seg_rom src0segs).
Ltac lits := unfold LOCK, CTX, LIBC, ERRNO, TP, GOT, GUARD, SCT, ASF, src0_D_malloc_lock, src0_D_malloc_context, src0_D_libc, src0_tp,
src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_size_classes in *.
Lemma st_entry : st_ok src0segs E00 ss_as ms0.
Proof.
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
pose proof (mid_statics _ _ _ _ _ MID) as ST.
unfold st_ok, ss_as, ms0, mkst; cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]).
split; [apply (regs_ok_am regs cs P6)|]. split.
- apply mem_ok_intro; [vm_compute; reflexivity | |].
+ unfold mem_as. repeat apply Forall_cons; try apply Forall_nil;
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_stackS R_got R_guard R_pgsz]; subst E00 sp; cbn [ew E0]; lits; try lia;
try (intros o Ho; first [apply P5; lia | lia]); repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_word src0segs _ mem 0 _ _ GUARD); [reflexivity | exact (st_got _ _ ST)].
* apply (chunk_ok_word src0segs _ mem 0 _ _ (cs 32%nat)); [apply (E_cx regs cs); lia | exact Hg].
* apply (chunk_ok_word src0segs _ mem 0 _ _ 4096); [reflexivity | exact (st_pagesize _ _ ST)].
+ subst E00 sp. cbn [pairwise_disjoint all_disjoint mem_as].
repeat split; unfold extent_disjoint; cbn [base_val r_base r_lo r_hi ew E0 R_stackS R_got R_guard R_pgsz]; lits; lia.
- subst E00 sp. unfold facts_as, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
unfold afact_ok, F_spS, F_sc, F_n; cbn [af_lo af_hi af_al2 ew E0]. lits.
replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : reg) by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : reg) by (apply bv_eq; reflexivity).
rewrite R10, R11. unfold MMAP_THRESHOLD in Hn. rewrite !u64_of_Z by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. change (2 ^ 4) with 16.
repeat split; lia.
Qed.
Let SO : syms_ok B := mid_syms _ _ _ _ _ MID.
Let MR : memrep B L A mem := mid_mem _ _ _ _ _ MID.
Lemma B_segs : ms_segs B = src0segs. Proof. reflexivity. Qed.
Lemma B_ctx : ms_ctx B = CTX. Proof. reflexivity. Qed.
Lemma B_errno : errno_addr B = ERRNO. Proof. reflexivity. Qed.
Lemma ctx_word : forall off v, In (MCell (LCtx off) 8 v) (ctx_cells A) -> (forall z, v <> VLo5 z) ->
word_mem src0segs mem (CTX + off) (sval_num L v).
Proof.
intros off v Hin Hv. pose proof (memrep_cell B L A mem _ MR ltac:(unfold image; apply in_app_iff; left; exact Hin)) as C.
unfold cell_mem in C. cbn [mc_loc mc_w mc_val loc_addr] in C. rewrite (mid_ctx _ _ _ _ _ MID), B_ctx in C.
destruct v as [z|p|z|]; try exact C. exfalso. exact (Hv z eq_refl).
Qed.
Lemma active_word : word_mem src0segs mem (cs 33 + 88) (cs 34).
Proof.
cbn [cs]. replace (LOCK + 8 * sc + 88) with (CTX + (CTX_active + 8 * Z.of_nat (Z.to_nat sc))) by (unfold LOCK, CTX, CTX_active, src0_D_malloc_lock, src0_D_malloc_context; lia).
replace (onum L (active_hd A sc)) with (sval_num L (optr (active_hd A sc))) by (destruct (active_hd A sc); reflexivity).
apply ctx_word; [| destruct (active_hd A sc); intros z; discriminate].
unfold ctx_cells. apply in_app_iff. right. apply in_app_iff. left. apply in_map_iff. exists (Z.to_nat sc). split; [reflexivity | apply in_seq; lia].
Qed.
Lemma ctxw : forall m x, CTX <= x < CTX + 928 -> writable_at src0segs m x.
Proof. intros m x Hx. exact (proj1 (so_ctx_rw _ SO m x ltac:(rewrite B_ctx; unfold CTX_SIZE; exact Hx))). Qed.
Lemma FRM_run : forall (W : Z -> Prop) E rs m m' (sk : list (option nat * Z * Z)),
FRM W m -> frame_of E rs m m' -> wsub rs sk = true ->
(forall b lo hi x, In (b, lo, hi) sk -> base_val E b + lo <= x < base_val E b + hi -> W x) -> FRM W m'.
Proof.
intros W E rs m m' sk HF Hfr Hs HW x Hx Hnw. rewrite <- (HF x Hx Hnw). apply (frame_of_at E rs m m' x Hfr Hx).
intros Hw. destruct (in_wrange_wsub regs E rs sk x Hs Hw) as (b & lo & hi & Hin & Hbx). exact (Hnw (HW b lo hi x Hin Hbx)).
Qed.
Definition SKS : list (option nat * Z * Z) := [(Some 2%nat, -ASF, 0)].
Lemma FRM_runS : forall (W : Z -> Prop) E rs m m',
(forall x, WS x -> W x) -> env_agree 40 E00 E -> FRM W m -> frame_of E rs m m' -> wsub rs SKS = true -> FRM W m'.
Proof.
intros W E rs m m' HW HA HF Hfr Hs. eapply (FRM_run W E); [exact HF | exact Hfr | exact Hs |].
intros b lo hi x Hin Hx. apply HW. unfold SKS in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <- <-.
cbn [base_val] in Hx. rewrite (agree_reg E 2 HA ltac:(lia)) in Hx. replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) in Hx by (apply bv_eq; reflexivity). unfold WS. fold sp in Hx. lia.
Qed.
Lemma wsubs1 : wsub (ss_mem ss_as) SKS = true /\ wsub (ss_mem ss_S1) SKS = true /\ wsub (ss_mem (add_cond ss_hd C_hd0)) SKS = true /\ wsub (ss_mem ss_S2) SKS = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma station_S1 : forall E ms, st_ok src0segs E ss_a1 ms -> env_agree 40 E00 E -> FRM WS (ms_mem ms) -> st_ok src0segs E ss_S1 ms.
Proof.
intros E ms HS HA HF. pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
destruct cs_facts as (C33 & C33m & C34 & C35 & C36 & C36m & _).
assert (E33 : ew E 33 = Z_to_bv 64 (cs 33)) by (apply (agree_cs E 33 HA); lia).
assert (E10 : ew E 10 = Z_to_bv 64 sc) by (rewrite (agree_reg E 10 HA) by lia; exact R10).
assert (HS1 : st_ok src0segs E (mkSS (ss_pc ss_a1) (sr_set (ss_regs ss_a1) 23 (SOff 33 0)) (ss_mem ss_a1) (ss_resv ss_a1) (ss_facts ss_a1)) ms).
{ apply (st_ok_regs src0segs E ss_a1 ms). exact HS. intros r.
destruct (decide (r = 23%bv)) as [Er|Er].
- subst r. rewrite sr_get_set_same by reflexivity.
assert (SG : sr_get (ss_regs ss_a1) 23 = SAlu ALU_ADD (SAlu ALU_SLL (SOff 10 0) (SLit 3)) (SLit LOCK)) by (vm_compute; reflexivity). rewrite SG.
apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E33, E10, alu64_add, alu64_sll.
assert (R33 : 0 <= cs 33 < 2 ^ 64) by (lits; lia).
rewrite ?(u64_of_Z sc), ?(u64_of_Z (cs 33)) by lia. rewrite !Z.add_0_r. rewrite ?(u64_of_Z sc), ?(u64_of_Z (cs 33)), ?(u64_of_Z 3) by lia.
rewrite (u64_of_Z LOCK) by (lits; lia).
change (3 mod 64) with 3. rewrite sll64_small by (change (2 ^ 3) with 8; lia). rewrite add64_small by (change (2 ^ 3) with 8; lits; lia). cbn [cs]. change (2 ^ 3) with 8. lia.
- rewrite sr_get_set_other by exact Er. reflexivity. }
assert (HS2 : st_ok src0segs E (mkSS (ss_pc ss_a1) (sr_set (ss_regs ss_a1) 23 (SOff 33 0)) (R_act :: ss_mem ss_a1) (ss_resv ss_a1) (ss_facts ss_a1)) ms).
{ apply (st_ok_add_region src0segs E _ ms R_act HS1); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_act]; rewrite E33, (u64_of_Z (cs 33)) by (lits; lia); [lits; lia | lits; lia | |].
+ intros o Ho. lia.
+ apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_word src0segs E (ms_mem ms) (cs 33) 88 _ (cs 34)); [exact (sv_cs E 34 HA ltac:(lia)) |].
apply (word_mem_ext1 mem); [| exact active_word]. intros k Hk. apply HF; [lits; lia | unfold WS; lits; lia].
- assert (SK : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_a1) = [(Some 2%nat, -ASF, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56)]) by (vm_compute; reflexivity).
apply Forall_forall. intros r Hr. cbn [ss_mem] in Hr. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr. rewrite SK in Hr.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_act]. change (base_val E (Some 33%nat)) with (bv_unsigned (ew E 33)). rewrite E33, (u64_of_Z (cs 33)) by (lits; lia).
cbn [In] in Hr. destruct Hr as [Hr|[Hr|[Hr|[Hr|[]]]]]; apply (f_equal (fun t => match t with (b, lo, hi) => (b, lo, hi) end)) in Hr; cbn in Hr; injection Hr as E1 E2 E3;
rewrite <- E1, <- E2, <- E3; cbn [base_val]; rewrite ?(agree_reg E 2 HA) by lia; try replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity); fold sp; lits; lia. }
apply (st_ok_add_fact src0segs E _ ms 34 F_hd) in HS2. 2:{ unfold afact_ok, F_hd. cbn [af_lo af_hi af_al2]. rewrite (agree_cs E 34 HA) by lia. rewrite u64_of_Z by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
apply (st_ok_add_fact src0segs E _ ms 33 F_s7) in HS2. 2:{ unfold afact_ok, F_s7. cbn [af_lo af_hi af_al2]. rewrite E33. rewrite u64_of_Z by (lits; lia). change (2 ^ 3) with 8. lia. }
exact HS2.
Qed.
Lemma reach_hd : SR src0segs (mkCfg ms0 md) (at_st ss_hd WS md).
Proof.
pose proof md_facts as (Mh & Mlz & _).
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E00 ss_as ss_a1); [exact Mh | exact Mlz | exact st_entry | apply run_as |].
intros ms1 HS1 HF1.
assert (F1 : FRM WS (ms_mem ms1)).
{ eapply (FRM_runS WS E00); [intros x Hx; exact Hx | apply env_agree_refl | intros x _ _; reflexivity | exact HF1 | exact (proj1 wsubs1)]. }
pose proof (station_S1 E00 ms1 HS1 (env_agree_refl _ _) F1) as HS2.
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E00 ss_S1 ss_hd); [exact Mh | exact Mlz | exact HS2 | apply run_S1 |].
intros ms2 HS3 HF3. apply SR_ret. exists E00, ms2. split; [reflexivity|]. split; [exact HS3|]. split; [apply env_agree_refl|].
eapply (FRM_runS WS E00); [intros x Hx; exact Hx | apply env_agree_refl | exact F1 | exact HF3 | exact (proj1 (proj2 wsubs1))].
Qed.
Lemma sct_bytes : forall k, (k < 2)%nat -> mbyte src0segs mem (cs 36 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (cs 35) 2 k)).
Proof.
pose proof SO as SO'. pose proof (mid_statics _ _ _ _ _ MID) as ST. cbn [cs].
assert (Escl : scl_of sc = znth sc size_classes) by (unfold scl_of; replace (sc <? 48) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
rewrite Escl.
destruct (so_size_classes _ SO' (Z.to_nat sc) ltac:(lia)) as (lo & hi & Hlo & Hhi & Hsum). rewrite Z2Nat.id in Hlo, Hhi by lia.
pose proof (u8_range lo). pose proof (u8_range hi).
pose proof (st_tables _ _ ST) as STB. unfold table_addr in STB.
cbn [ms_segs ms_debruijn ms_size_classes ms_small_cnt ms_med_cnt src0_msyms] in STB.
cbn [ms_segs ms_size_classes src0_msyms] in Hlo, Hhi. unfold w64 in STB, Hlo, Hhi.
unfold znth. rewrite <- Hsum.
intros kk Hkk. rewrite STB by (unfold SCT, src0_D_size_classes, src0_D_debruijn32, src0_D_small_cnt_tab, src0_D_med_cnt_tab; lia).
destruct kk as [|[|]]; [| | lia]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ].
+ rewrite Z.add_0_r. unfold SCT. rewrite Hlo. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 lo) at 1. f_equal.
unfold le_byte. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite (Z.mod_small _ 65536) by lia. rewrite (Z.mul_comm 256 (bv_unsigned hi)), Z_mod_plus_full. symmetry. apply Z.mod_small. lia.
+ change (Z.of_nat 1) with 1. unfold SCT. rewrite Hhi. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 hi) at 1. f_equal.
unfold le_byte. change (2 ^ (8 * Z.of_nat 2)) with 65536. change (8 * Z.of_nat 1) with 8.
rewrite (Z.mod_small _ 65536) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
rewrite (Z.mul_comm 256 (bv_unsigned hi)), Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. symmetry. apply Z.mod_small. lia.
Qed.
Lemma station_S2 : forall E ms, st_ok src0segs E ss_t0 ms -> env_agree 40 E00 E -> FRM WS (ms_mem ms) -> st_ok src0segs E ss_S2 ms.
Proof.
intros E ms HS HA HF. pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
destruct cs_facts as (C33 & C33m & C34 & C35 & C36 & C36m & _).
assert (E36 : ew E 36 = Z_to_bv 64 (cs 36)) by (apply (agree_cs E 36 HA); lia).
assert (E10 : ew E 10 = Z_to_bv 64 sc) by (rewrite (agree_reg E 10 HA) by lia; exact R10).
assert (R36 : 0 <= cs 36 < 2 ^ 64) by (lits; lia).
assert (HS1 : st_ok src0segs E (mkSS (ss_pc ss_t0) (sr_set (ss_regs ss_t0) 10 (SOff 36 0)) (ss_mem ss_t0) (ss_resv ss_t0) (ss_facts ss_t0)) ms).
{ apply (st_ok_regs src0segs E ss_t0 ms). exact HS. intros r.
destruct (decide (r = 10%bv)) as [Er|Er].
- subst r. rewrite sr_get_set_same by reflexivity.
assert (SG : sr_get (ss_regs ss_t0) 10 = SAlu ALU_ADD (SAlu ALU_SLL (SOff 10 0) (SLit 1)) (SLit SCT)) by (vm_compute; reflexivity). rewrite SG.
apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E36, E10, alu64_add, alu64_sll.
rewrite ?(u64_of_Z sc), ?(u64_of_Z (cs 36)) by lia. rewrite !Z.add_0_r. rewrite ?(u64_of_Z sc), ?(u64_of_Z (cs 36)), ?(u64_of_Z 1) by lia.
rewrite (u64_of_Z SCT) by (lits; lia).
change (1 mod 64) with 1. rewrite sll64_small by (change (2 ^ 1) with 2; lia). rewrite add64_small by (change (2 ^ 1) with 2; lits; lia). cbn [cs]. change (2 ^ 1) with 2. lia.
- rewrite sr_get_set_other by exact Er. reflexivity. }
assert (HS2 : st_ok src0segs E (mkSS (ss_pc ss_t0) (sr_set (ss_regs ss_t0) 10 (SOff 36 0)) (R_sct :: ss_mem ss_t0) (ss_resv ss_t0) (ss_facts ss_t0)) ms).
{ apply (st_ok_add_region src0segs E _ ms R_sct HS1); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_sct]; rewrite E36, (u64_of_Z (cs 36)) by lia; [lits; lia | lits; lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_cval src0segs E (ms_mem ms) (cs 36) 0 2 _ (cs 35)); [exact (sv_cs E 35 HA ltac:(lia)) | lia |].
intros k Hk. rewrite Z.add_0_r. rewrite (mbyte_ext1 mem); [apply sct_bytes; exact Hk|]. apply HF; [lits; lia | unfold WS; lits; lia].
- assert (SK : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_t0) = [(Some 33%nat, 88, 96); (Some 2%nat, -ASF, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56)]) by (vm_compute; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 (cs 33)) by (apply (agree_cs E 33 HA); lia).
apply Forall_forall. intros r Hr. cbn [ss_mem] in Hr. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr. rewrite SK in Hr.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_sct]. change (base_val E (Some 36%nat)) with (bv_unsigned (ew E 36)). rewrite E36, (u64_of_Z (cs 36)) by lia.
cbn [In] in Hr. destruct Hr as [Hr|[Hr|[Hr|[Hr|[Hr|[]]]]]]; apply (f_equal (fun t => match t with (b, lo, hi) => (b, lo, hi) end)) in Hr; cbn in Hr; injection Hr as E1 E2 E3;
rewrite <- E1, <- E2, <- E3; cbn [base_val]; rewrite ?(agree_reg E 2 HA) by lia; rewrite ?E33, ?(u64_of_Z (cs 33)) by (lits; lia);
try replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity); fold sp; lits; lia. }
apply (st_ok_add_fact src0segs E _ ms 35 F_sz) in HS2. 2:{ unfold afact_ok, F_sz. cbn [af_lo af_hi af_al2]. rewrite (agree_cs E 35 HA) by lia. rewrite u64_of_Z by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
apply (st_ok_add_fact src0segs E _ ms 36 F_sct) in HS2. 2:{ unfold afact_ok, F_sct. cbn [af_lo af_hi af_al2]. rewrite E36. rewrite u64_of_Z by lia. change (2 ^ 1) with 2. lia. }
exact HS2.
Qed.
Lemma reach_G0 : forall c, active_hd A sc = None -> j1 = J1LIT -> j2 = 0 -> at_st ss_hd WS md c -> SR src0segs c (at_st ss_G0 WS md).
Proof.
intros c Hhd Hj1 Hj2 (E & ms & -> & HS & HA & HF). pose proof md_facts as (Mh & Mlz & _). destruct cs_facts as (_ & _ & _ & _ & _ & _ & C34z & _).
apply (st_ok_add_cond src0segs E ss_hd ms BC_EQ (SOff 34 0) (SLit 0)) in HS.
2:{ rewrite (sv_cs E 34 HA ltac:(lia)). cbn [sv_denot]. rewrite (proj2 C34z Hhd). rewrite branch_eq. reflexivity. }
change (add_cond ss_hd (mkAC BC_EQ (SOff 34 0) (SLit 0))) with (add_cond ss_hd C_hd0) in HS.
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E _ ss_t0); [exact Mh | exact Mlz | exact HS | apply run_hd0 |].
intros ms1 HS1 HF1.
assert (F1 : FRM WS (ms_mem ms1)) by (eapply (FRM_runS WS E); [intros x Hx; exact Hx | exact HA | exact HF | exact HF1 | exact (proj1 (proj2 (proj2 wsubs1)))]).
pose proof (station_S2 E ms1 HS1 HA F1) as HS2.
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL src0_A_alloc_meta E ss_S2 ss_G0r RS_running); [exact Mh | exact Mlz | exact HS2 | apply run_S2 |].
intros ms2 HS3 HF3. apply SR_ret. exists E, ms2. split; [reflexivity|]. split.
{ change ss_G0 with (mkSS (ss_pc ss_G0r) (sr_set (sr_set (ss_regs ss_G0r) 11 (SOff 37 0)) 12 (SOff 38 0)) (ss_mem ss_G0r) (ss_resv ss_G0r) (ss_facts ss_G0r)).
apply (st_ok_regs src0segs E ss_G0r ms2 _ HS3). intros r. pose proof G0r_regs as [G11 G12].
destruct (decide (r = 12%bv)) as [->|N12]; [| destruct (decide (r = 11%bv)) as [->|N11]].
- rewrite sr_get_set_same by reflexivity. rewrite G12, (sv_cs E 38 HA), (sv_cs E 34 HA) by lia. f_equal. cbn [cs]. rewrite Hj2. symmetry. exact (proj2 C34z Hhd).
- rewrite sr_get_set_other, sr_get_set_same by (reflexivity || (intros H; discriminate)). rewrite G11, (sv_cs E 37 HA) by lia. cbn [cs sv_denot]. rewrite Hj1. reflexivity.
- rewrite !sr_get_set_other by assumption. reflexivity. }
split; [exact HA|].
eapply (FRM_runS WS E); [intros x Hx; exact Hx | exact HA | exact F1 | exact HF3 | exact (proj2 (proj2 (proj2 wsubs1)))].
Qed.
Definition Qam (s : astate) (r : option sptr * astate) : Prop :=
am_frame s (snd r) /\ ub_same s (snd r) /\
match fst r with
| None => Inv X None U (snd r) /\ (forall g' am, usedX X (snd r) g' am <-> usedX X s g' am)
| Some m => Inv (m :: X) None U (snd r) /\ memb m X = false /\ In m (keys (snd r)) /\
(MT (snd r) m = Some MRaw \/ MT (snd r) m = Some (MFree None None)) /\
(forall g' am, usedX (m :: X) (snd r) g' am <-> usedX X s g' am)
end.
Lemma alloc_meta_Q : forall s, Inv X None U s -> rawX X s -> itok (alloc_meta s) (fun r => Qam s r /\ (rawX X (snd r) /\ as_keep X s (snd r))).
Proof.
intros s HIs RXs. apply itok_iall; [| exact (iall_conj _ _ _ (alloc_meta_rawX X None U s HIs RXs) (alloc_meta_keep X None U s HIs))].
apply (alloc_meta_spec X None U s (Qam s) HIs).
- intros s' HI' FR US UB. unfold Qam. cbn [fst snd]. auto.
- intros m s' HI' Hm Hk HMT FR US UB. unfold Qam. cbn [fst snd]. repeat (split; [assumption|]). exact US.
Qed.
Lemma chunk_ok_ext : forall E m m' base c,
chunk_ok src0segs E m base c -> (forall i, 0 <= i < c_len c -> m' (Z_to_bv 64 (base + c_off c + i)) = m (Z_to_bv 64 (base + c_off c + i))) ->
chunk_ok src0segs E m' base c.
Proof.
intros E m m' base c Hc Hm i Hi. destruct (Hc i Hi) as (b & H1 & H2). exists b. split; [exact H1|]. rewrite (mbyte_ext1 m m' _ (Hm i Hi)). exact H2.
Qed.
Lemma nonmap_low : forall L1 A1 m1 md1 x, midrep B L1 A1 m1 md1 -> in_nonmap_region L1 A1 x -> 4096 <= x < alloc_ceiling /\ ~ in_img B x.
Proof.
intros L1 A1 m1 md1 x M ((r & rg & Hr & Hl & Hk & Hx) & _).
pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ M) r rg Hr Hl) as (_ & Plo & Phi & Pimg). split; [lia | apply Pimg; exact Hx].
Qed.
Lemma statics_not_ctx : forall x, (GOT <= x < GOT + 8 \/ GUARD <= x < GUARD + 8 \/ LIBC + 48 <= x < LIBC + 56) -> ~ (CTX <= x < CTX + CTX_SIZE) /\ in_img B x /\ 0 <= x < 2 ^ 64.
Proof. intros x Hx. unfold CTX_SIZE. lits. split; [lia|]. split; [apply src0_rwseg_img; lia | lia]. Qed.
Lemma region_ok_ext : forall E m m' r, region_ok src0segs E m r ->
(forall c i, In c (r_chunks r) -> 0 <= i < c_len c -> m' (Z_to_bv 64 (base_val E (r_base r) + c_off c + i)) = m (Z_to_bv 64 (base_val E (r_base r) + c_off c + i))) ->
(forall o, r_wlo r <= o < r_whi r -> writable_at src0segs m' (base_val E (r_base r) + o)) ->
region_ok src0segs E m' r.
Proof.
intros E m m' r (R1 & R2 & R3 & R4) Hc Hw. split; [exact R1|]. split; [exact R2|]. split; [exact Hw|].
rewrite Forall_forall in R4 |- *. intros c Hin. apply (chunk_ok_ext E m m'); [apply R4; exact Hin | intros i Hi; apply (Hc c i Hin Hi)].
Qed.
Let XC' : forall x am, In x X -> MT A x <> Some (MUsed am) := XC.
Lemma call_am : forall c, at_st ss_G0 WS md c ->
mreal src0segs c (alloc_meta A)
(fun r c' => (Qam A r /\ (rawX X (snd r) /\ as_keep X A (snd r))) /\
exists L' mem' md' E', layout_le A L L' /\ midrep B L' (snd r) mem' md' /\ ama_ok (snd r) /\ bounded (snd r) /\
(exists vm', md' = with_vmmaps vm' md) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ WS x -> ~ (ERRNO <= x < ERRNO + 4) -> ~ (CTX <= x < CTX + CTX_SIZE) -> ~ in_nonmap_region L' (snd r) x ->
mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) /\
(forall a, ERRNO <= a < ERRNO + 4 -> writable_at src0segs mem' a) /\
env_agree 40 E00 E' /\
c' = mkCfg (mkst (ms_regs (cfg_ms c')) (Z_to_bv 64 PS_RAM) mem' (seg_rom src0segs)) md' /\
match fst r with
| None => st_ok src0segs E' ss_R0 (cfg_ms c')
| Some m => ew E' 40 = Z_to_bv 64 (ptr_addr L' m) /\ st_ok src0segs E' ss_R1 (cfg_ms c')
end).
Proof.
intros c (E & ms & -> & HS & HA & HF).
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7). pose proof md_facts as (Mh & Mlz & Mmat).
pose proof (u64_range (getr regs 2)) as SPR. fold sp in SPR. assert (EASF : ASF = 384) by reflexivity.
pose proof (st_ok_mkst E ss_G0 ms HS eq_refl) as Ems. rewrite ss_G0_pc in Ems.
destruct HS as (S1 & S2 & S3 & S4 & S5 & S6 & Hregs & Hmem & HG).
set (regs1 := ms_regs ms) in *. set (mem1 := ms_mem ms) in *.
assert (E2 : ew E 2 = getr regs 2) by (rewrite (agree_reg E 2 HA) by lia; reflexivity).
assert (R2 : getr regs1 2 = Z_to_bv 64 (sp - 144)).
{ rewrite (Hregs 2%bv). change (sr_get (ss_regs ss_G0) 2) with (SOff 2 (-144)). cbn [sv_denot]. rewrite E2. fold sp. apply f_equal. lia. }
assert (SPZ : spZ regs1 = sp - 144) by (unfold spZ; rewrite R2; apply u64_of_Z; unfold ASF in Hstk; lia).
assert (MID1 : midrep B L A mem1 md) by (apply midrep_stack; exact HF).
assert (RSTK : nth_error (ss_mem ss_G0) 2 = Some (YP09.mkRegion (Some 2%nat) (-ASF) 0 (-ASF) 0 (r_chunks R_frame))) by (vm_compute; reflexivity).
pose proof (st_ok_region src0segs E ss_G0 ms 2 _ (conj S1 (conj S2 (conj S3 (conj S4 (conj S5 (conj S6 (conj Hregs (conj Hmem HG)))))))) RSTK) as (_ & _ & WSTK & CSTK).
cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in WSTK, CSTK. rewrite E2 in WSTK, CSTK. fold sp in WSTK, CSTK. fold mem1 in WSTK, CSTK.
assert (PRE1 : callee_pre B regs1 mem1 AM_STACK).
{ unfold callee_pre. rewrite SPZ. rewrite AMS_eq. unfold AMS. split; [| split; [| split; [| split; [| split; [| split]]]]].
- rewrite (Hregs 1%bv). change (sr_get (ss_regs ss_G0) 1) with (SLit PS_RAM). cbn [sv_denot]. vm_compute. reflexivity.
- rewrite <- Zminus_mod_idemp_l. rewrite P2. reflexivity.
- unfold ASF in Hstk. lia.
- lia.
- intros a Ha. rewrite B_segs. replace a with (sp + (a - sp)) by lia. apply WSTK. unfold ASF. lia.
- rewrite (Hregs 4%bv). reflexivity.
- intros a Ha. rewrite B_segs. rewrite B_errno in Ha. apply (writable_ext1 mem); [apply HF; [lits; lia | unfold WS; lits; lia] | apply P7; exact Ha]. }
assert (AUX1 : st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs1) mem1).
{ intros Hi. rewrite SPZ. apply (auxv_pre_mono B (ly_sec L) sp); [lia|].
apply (auxv_pre_ext (ly_sec L) sp mem); [| | exact (AUXP Hi)].
- intros x Hx. apply mbyte_ext1. apply HF; [lia | unfold WS; lia].
- intros x Hx. apply mbyte_ext1. cbn [ms_libc src0_msyms] in Hx. apply HF; [lits; lia | unfold WS; lits; lia]. }
rewrite Ems. fold regs1 mem1.
pose proof (AMH X None U L A regs1 mem1 md HI XC' AMA BND MID1 AUX1 PRE1) as M. rewrite B_segs in M. change (pc_alloc_meta (ms_pcs B)) with src0_A_alloc_meta in M.
pose proof (mreal_itok _ _ _ _ _ M (alloc_meta_Q A HI XR)) as M2.
eapply mreal_mono; [| exact M2]. cbv beta. intros r c' [(L' & regs' & mem' & md' & -> & CP & AMA' & BND' & R10' & NZ) Q].
split; [exact Q|]. destruct CP as (MID' & LE & PRS & VM & FRp & SCRp). rewrite SPZ in FRp, SCRp. rewrite AMS_eq in FRp, SCRp. unfold AMS in FRp, SCRp.
assert (FR2 : forall x, 0 <= x < 2 ^ 64 -> ~ WS x -> ~ (ERRNO <= x < ERRNO + 4) -> ~ (CTX <= x < CTX + CTX_SIZE) -> ~ in_nonmap_region L' (snd r) x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
{ intros x Hx W1 W2 W3 W4. rewrite (FRp x Hx); [apply HF; [exact Hx | exact W1] | rewrite B_ctx; exact W3 | exact W4 |].
unfold call_scratch. rewrite B_errno. intros [H|H]; [apply W1; unfold WS, ASF; lia | exact (W2 H)]. }
assert (REGS : forall (n0 : nat) E0 (rv : sv) (rs0 : smem), (40 <= n0)%nat -> env_agree 40 E E0 -> getr regs' 10 = sv_denot E0 rv -> sv_atoms_lt n0 rv = true ->
exists E', env_agree n0 E0 E' /\ regs_ok E' (ss_regs (junk_regs AM_JUNK n0 (mkSS PS_RAM (sr_set (ss_regs ss_G0) 10 rv) rs0 None (ss_facts ss_G0)))) regs').
{ intros n0 E0 rv rs0 Hn0 HA0 Hrv Hat.
assert (Hregs0 : regs_ok E0 (ss_regs ss_G0) regs1) by (eapply (regs_ok_agree 40 E E0); [exact HA0 | vm_compute; reflexivity | exact Hregs]).
assert (HSI : st_ok src0segs E0 (mkSS PS_RAM (sr_set (ss_regs ss_G0) 10 rv) [] None (mkFacts [] [] [])) (mkst (regupd regs1 10 (getr regs' 10)) (Z_to_bv 64 PS_RAM) mem' (seg_rom src0segs))).
{ unfold st_ok, mkst; cbn. repeat (split; [reflexivity|]). split; [| split; [apply mem_ok_intro; [reflexivity | apply Forall_nil | exact I] | repeat split; apply Forall_nil]].
generalize (regs_ok_set E0 (ss_regs ss_G0) regs1 10 (getr regs' 10) rv Hregs0 (eq_sym Hrv)). cbn [bv_eqb]. exact (fun H => H). }
assert (AT : ss_atoms_lt n0 (mkSS PS_RAM (sr_set (ss_regs ss_G0) 10 rv) [] None (mkFacts [] [] [])) = true).
{ unfold ss_atoms_lt. cbn [ss_regs ss_mem ss_facts ss_resv mem_atoms_lt facts_atoms_lt forallb f_atoms f_conds f_alias andb].
rewrite (regs_atoms_lt_set n0 (ss_regs ss_G0) 10 rv); [reflexivity | apply (regs_atoms_lt_mono 40 n0); [lia | vm_compute; reflexivity] | exact Hat]. }
assert (NZ' : forallb (fun r : reg => negb (bv_eqb r 0)) AM_JUNK = true) by (vm_compute; reflexivity).
assert (EXT : forall r0, ~ In r0 AM_JUNK -> getr regs' r0 = getr (regupd regs1 10 (getr regs' 10)) r0).
{ apply (reg_cases_lit (fun r0 => ~ In r0 AM_JUNK -> getr regs' r0 = getr (regupd regs1 10 (getr regs' 10)) r0)).
intros r0 Hr0 Hnj. cbv [all_regs In] in Hr0.
repeat (destruct Hr0 as [<-|Hr0]; [ first [ solve [exfalso; apply Hnj; inlist]
| reflexivity
| unfold getr, regupd, reg_get; rewrite bvmap_get_set_same; reflexivity
| match goal with |- getr _ ?r = _ =>
let PR := fresh "PR" in let k := eval vm_compute in (bv_unsigned r) in
assert (PR : getr regs' r = getr regs1 r) by (replace r with (Z_to_bv 5 k) by (apply bv_eq; reflexivity); apply (PRS k); unfold callee_saved; lia);
etransitivity; [exact PR | unfold getr, regupd, reg_get; rewrite bvmap_get_set_other by (intros HH; discriminate HH); reflexivity] end ] |]).
destruct Hr0. }
destruct (st_ok_clobber src0segs AM_JUNK n0 E0 _ _ regs' (Z_to_bv 64 PS_RAM) mem' (seg_rom src0segs) HSI AT NZ' EXT) as (E' & HA' & HS').
exists E'. split; [exact HA'|]. destruct HS' as (_ & _ & _ & _ & _ & _ & RR & _). exact RR. }
assert (LOWn : forall x, in_nonmap_region L' (snd r) x -> x < alloc_ceiling /\ ~ in_img B x) by (intros x Hx; destruct (nonmap_low L' (snd r) mem' md' x MID' Hx) as [H1 H2]; split; [lia | exact H2]).
assert (KEEPhi : forall x, sp - ASF <= x < sp -> ~ (sp - 144 - 160 <= x < sp - 144) -> mem' (Z_to_bv 64 x) = mem1 (Z_to_bv 64 x)).
{ intros x Hx Hns. unfold ASF in Hx. apply (FRp x ltac:(lia)); [rewrite B_ctx; unfold CTX_SIZE; lits; lia | intros Hn'; destruct (LOWn x Hn'); lia | unfold call_scratch; rewrite B_errno; lits; lia]. }
assert (KEEPimg : forall x, (GOT <= x < GOT + 8 \/ GUARD <= x < GUARD + 8 \/ LIBC + 48 <= x < LIBC + 56) -> mem' (Z_to_bv 64 x) = mem1 (Z_to_bv 64 x)).
{ intros x Hx. destruct (statics_not_ctx x Hx) as (N1 & N2 & N3). apply (FRp x N3); [rewrite B_ctx; exact N1 | intros Hn'; exact (proj2 (LOWn x Hn') N2) | unfold call_scratch; rewrite B_errno; lits; lia]. }
assert (RG3 : nth_error (ss_mem ss_G0) 3 = Some R_got /\ nth_error (ss_mem ss_G0) 4 = Some R_guard) by (vm_compute; split; reflexivity).
assert (HS0 : st_ok src0segs E ss_G0 ms) by exact (conj S1 (conj S2 (conj S3 (conj S4 (conj S5 (conj S6 (conj Hregs (conj Hmem HG)))))))).
assert (RG5 : nth_error (ss_mem ss_G0) 5 = Some R_pgsz) by (vm_compute; reflexivity).
assert (MEM4 : mem_ok src0segs E mem' [R_frame; R_got; R_guard; R_pgsz]).
{ apply mem_ok_intro; [vm_compute; reflexivity | |].
- apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
+ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_frame]; rewrite E2; fold sp; unfold ASF; [lia | lia | |].
* intros o Ho. destruct (Z_lt_le_dec (sp + o) (sp - 144)) as [Hlo|Hhi']; [destruct (Z_lt_le_dec (sp + o) (sp - 144 - 160)) as [Hlo2|Hmid] |].
-- apply (writable_ext1 mem1); [apply KEEPhi; lia | apply WSTK; lia].
-- rewrite <- B_segs. apply SCRp. unfold call_scratch. left. lia.
-- apply (writable_ext1 mem1); [apply KEEPhi; lia | apply WSTK; lia].
* rewrite Forall_forall in CSTK |- *. intros c Hin. apply (chunk_ok_ext E mem1 mem'); [apply CSTK; exact Hin|].
intros i Hi. cbn [r_chunks R_frame In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; cbn [c_off c_len cv_len c_val] in Hi |- *; apply KEEPhi; lia.
+ apply (region_ok_ext E mem1 mem' R_got (st_ok_region src0segs E ss_G0 ms 3 _ HS0 (proj1 RG3))); cbn [r_chunks r_base r_wlo r_whi base_val R_got]; [| intros o Ho; lia].
intros c i [<-|[]] Hi. cbn [c_off c_len cv_len c_val] in Hi |- *. apply KEEPimg. lia.
+ apply (region_ok_ext E mem1 mem' R_guard (st_ok_region src0segs E ss_G0 ms 4 _ HS0 (proj2 RG3))); cbn [r_chunks r_base r_wlo r_whi base_val R_guard]; [| intros o Ho; lia].
intros c i [<-|[]] Hi. cbn [c_off c_len cv_len c_val] in Hi |- *. apply KEEPimg. lia.
+ apply (region_ok_ext E mem1 mem' R_pgsz (st_ok_region src0segs E ss_G0 ms 5 _ HS0 RG5)); cbn [r_chunks r_base r_wlo r_whi base_val R_pgsz]; [| intros o Ho; lia].
intros c i [<-|[]] Hi. cbn [c_off c_len cv_len c_val] in Hi |- *. apply KEEPimg. lia.
- cbn [pairwise_disjoint all_disjoint]. repeat split; unfold extent_disjoint; cbn [base_val r_base r_lo r_hi R_frame R_got R_guard R_pgsz]; rewrite ?E2; fold sp; unfold ASF; lits; lia. }
assert (MEM' : mem_ok src0segs E mem' [R_frame; R_got; R_guard]).
{ apply (mem_ok_sub src0segs E mem' [R_frame; R_got; R_guard; R_pgsz] [R_frame; R_got; R_guard]); [apply submemb_sound; vm_compute; reflexivity | vm_compute; reflexivity | exact MEM4]. }
assert (ER1 : getr regs1 1 = Z_to_bv 64 PS_RAM) by (rewrite (Hregs 1%bv); reflexivity). rewrite ER1.
exists L', mem', md'.
destruct (fst r) as [m|] eqn:Efr.
-
pose proof (mid_syms _ _ _ _ _ MID') as SO'.
assert (HM : 4096 <= ptr_addr L' m /\ ptr_addr L' m + META_SIZE <= alloc_ceiling /\ ptr_addr L' m mod 8 = 0).
{ destruct Q as [Qm _]. unfold Qam in Qm. rewrite Efr in Qm. destruct Qm as (_ & _ & HI' & _ & Hk & _).
destruct (inv_keys HI') as (_ & KP & _ & _ & Hamc). destruct (KP m Hk) as (a & k & Ha & Hkk & ->).
assert (Hh : handed (snd r) a <= METAS_PER_AREA) by (unfold handed; destruct (sptr_eqb a _); lia).
pose proof (fun x Hx => areas_off_img B _ None U L' (snd r) mem' md' HI' MID' a x Ha Hx) as AO.
pose proof (inv_areas HI') as (_ & Har & _). destruct (Har a Ha) as (ra & oa & rga & Ea & Hoa & _ & Hra & Hla & _).
pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID') ra rga Hra Hla) as (Pal & _).
rewrite ptr_addr_padd. rewrite Ea at 3. unfold ptr_addr at 3. cbn [loc_addr]. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *.
split; [destruct (AO (ptr_addr L' a) ltac:(lia)) as [_ R0]; lia|]. split; [destruct (AO (ptr_addr L' a + 4095) ltac:(lia)) as [_ R0]; nia|].
replace (ly_reg L' ra) with (4096 * (ly_reg L' ra / 4096)) by (pose proof (Z.div_mod (ly_reg L' ra) 4096 ltac:(lia)); lia).
replace oa with (4096 * (oa / 4096)) at 1 by (pose proof (Z.div_mod oa 4096 ltac:(lia)); lia).
replace (4096 * (ly_reg L' ra / 4096) + 4096 * (oa / 4096) + (24 + 40 * k)) with ((512 * (ly_reg L' ra / 4096) + 512 * (oa / 4096) + 3 + 5 * k) * 8) by lia.
apply Z_mod_mult. }
unfold META_SIZE in HM.
set (E1 := ewset E 40 (Z_to_bv 64 (ptr_addr L' m))).
assert (HA1 : env_agree 40 E E1) by (apply env_agree_ewset).
assert (E1_40 : ew E1 40 = Z_to_bv 64 (ptr_addr L' m)) by (unfold E1; apply ew_ewset_same).
destruct (REGS 41%nat E1 (SOff 40 0) [R_frame; R_got; R_guard; R_pgsz] ltac:(lia) HA1 ltac:(rewrite R10'; cbn [sv_denot]; rewrite E1_40, u64_of_Z by lia; rewrite Z.add_0_r; reflexivity) eq_refl) as (E' & HA' & RR).
exists E'. split; [exact LE|]. split; [exact MID'|]. split; [exact AMA'|]. split; [exact BND'|]. split; [exact VM|]. split; [exact FR2|].
split; [intros a Ha; rewrite <- B_segs; apply SCRp; unfold call_scratch; right; rewrite B_errno; exact Ha|].
split; [apply (agree_step 40 40 _ _ _ HA); [apply (agree_step 40 41 _ _ _ HA1 HA'); lia | lia]|].
split; [reflexivity|]. cbn [cfg_ms]. split; [destruct HA' as [X' _]; rewrite (X' 40%nat) by lia; exact E1_40|].
unfold st_ok, mkst; cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact RR|]. split.
+ eapply (mem_ok_agree src0segs 41 E1 E'); [exact HA' | vm_compute; reflexivity |]. eapply (mem_ok_agree src0segs 40 E E1); [exact HA1 | vm_compute; reflexivity | exact MEM4].
+ eapply (facts_ok_agree 41 E1 E'); [exact HA' | vm_compute; reflexivity |].
change (ss_facts ss_R1) with (mkFacts ((40%nat, F_meta) :: f_atoms (ss_facts ss_G0)) (f_conds (ss_facts ss_G0)) (f_alias (ss_facts ss_G0))).
apply facts_ok_add_atom; [eapply (facts_ok_agree 40 E E1); [exact HA1 | vm_compute; reflexivity | exact HG] |].
unfold afact_ok, F_meta. cbn [af_lo af_hi af_al2]. rewrite E1_40, u64_of_Z by lia. change (2 ^ 3) with 8. unfold META_SIZE in HM. lia.
- destruct (REGS 40%nat E (SLit 0) [R_frame; R_got; R_guard] ltac:(lia) (env_agree_refl _ _) R10' eq_refl) as (E' & HA' & RR).
exists E'. split; [exact LE|]. split; [exact MID'|]. split; [exact AMA'|]. split; [exact BND'|]. split; [exact VM|]. split; [exact FR2|].
split; [intros a Ha; rewrite <- B_segs; apply SCRp; unfold call_scratch; right; rewrite B_errno; exact Ha|].
split; [eapply (agree_step 40 40 _ _ _ HA HA'); lia|].
split; [reflexivity|]. cbn [cfg_ms].
unfold st_ok, mkst; cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact RR|]. split.
+ eapply (mem_ok_agree src0segs 40 E E'); [exact HA' | vm_compute; reflexivity | exact MEM'].
+ eapply (facts_ok_agree 40 E E'); [exact HA' | vm_compute; reflexivity | exact HG].
Qed.
Lemma in_frames_intro : forall s g' am i fr, In (g', am) (used_metas s) -> 0 <= i <= am_last am -> ss_fr (nth_slot am i) = Some fr ->
In (g', am, i, fr) (frames s).
Proof.
intros s g' am i fr Hu Hi Hf. unfold frames. apply in_flat_map. exists (g', am). split; [exact Hu|].
apply in_flat_map. exists i. split; [apply In_zseq; lia|]. rewrite Hf. left. reflexivity.
Qed.
Lemma rsv_ok_xfer : forall X' s', Inv X' None U s' -> Xclean X' s' ->
(forall g' am, usedX X' s' g' am -> usedX X A g' am) -> rsv_ok s'.
Proof.
intros X' s' HI' XCs US g' am i fr Hin Hk. destruct (in_frames_inv s' g' am i fr Hin) as (Hu & Hi & Hf).
apply (RSV g' am i fr); [| exact Hk]. apply in_frames_intro; [| exact Hi | exact Hf].
apply (proj2 (used_metas_usedX' X None U A HI XC g' am)). apply US. apply (proj1 (used_metas_usedX' X' None U s' HI' XCs g' am)). exact Hu.
Qed.
Lemma span_ok_xfer : forall X' s', Xclean X' s' -> (forall g' am, usedX X' s' g' am -> usedX X A g' am) -> span_ok s'.
Proof.
intros X' s' XCs US g' am Hm Hlt.
destruct (memb g' X') eqn:E; [exfalso; exact (XCs g' am (proj1 (memb_In g' X') E) Hm)|].
exact (SPOK g' am (proj1 (usedX_MT _ _ _ _ (US g' am (usedX_intro X' s' g' am E Hm)))) Hlt).
Qed.
Lemma fetch_retS : fetch_word src0segs (Z_to_bv 64 PS_JR) = Some (0x00008067%bv : bv 32).
Proof. rewrite <- (Z_to_bv_bv_unsigned 32 (0x00008067%bv : bv 32)). apply src0tbl_ok. vm_compute. reflexivity. Qed.
Lemma SR_final_retS : forall E ss ms mdl Q,
st_ok src0segs E ss ms -> ss_resv ss = None -> ss_pc ss = PS_JR ->
sr_get (ss_regs ss) 1 = SOff 1 0 -> YK0s.ret_ok (ew E 1) ->
m_halted mdl = None -> m_vm_lazy mdl = [] ->
Q (mkCfg (mkst (ms_regs ms) (ew E 1) (ms_mem ms) (seg_rom src0segs)) mdl) ->
SR src0segs (mkCfg ms mdl) Q.
Proof.
intros E ss ms mdl Q HS Hrv Hpc Hra Hret Hh Hlz HQ.
pose proof (st_ok_reg src0segs E ss ms 1 HS) as R1. rewrite Hra in R1. cbn [sv_denot] in R1.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R1.
rewrite (st_ok_mkst E ss ms HS Hrv). rewrite Hpc.
eapply SR_step; [exact Hh | exact Hlz | reflexivity | |].
- eapply step_jalr_x0; [apply fetch_retS | reflexivity | apply decode_ret | exact R1].
- cbn [ms_regs ms_mem mkst]. change (bv_signed (0%bv : bv 12)) with 0. unfold YK0s.ret_ok in Hret. rewrite Hret.
apply SR_ret. exact HQ.
Qed.
Definition cs_regsS : list nat := [2; 3; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition finalS_check (ss : sstate) (rv : sv) : bool :=
forallb (fun k => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat k))) (SOff k 0)) cs_regsS
&& sv_eqb (sr_get (ss_regs ss) 4) (SLit TP) && sv_eqb (sr_get (ss_regs ss) 1) (SOff 1 0) && sv_eqb (sr_get (ss_regs ss) 10) rv
&& Z.eqb (ss_pc ss) PS_JR && match ss_resv ss with None => true | _ => false end.
Lemma finalS : forall E ss ms rv,
finalS_check ss rv = true -> st_ok src0segs E ss ms -> env_agree 40 E00 E ->
regs_preserved regs (ms_regs ms) /\ ew E 1 = getr regs 1 /\ sr_get (ss_regs ss) 1 = SOff 1 0 /\ ss_pc ss = PS_JR /\ ss_resv ss = None /\
getr (ms_regs ms) 10 = sv_denot E rv.
Proof.
intros E ss ms rv Hc HS HA. pose proof pre_facts as (_ & _ & _ & _ & _ & P6 & _).
unfold finalS_check in Hc. apply andb_prop in Hc as [Hc Hrs]. apply andb_prop in Hc as [Hc Hpc]. apply andb_prop in Hc as [Hc H10]. apply andb_prop in Hc as [Hc H1]. apply andb_prop in Hc as [Hc H4].
apply Z.eqb_eq in Hpc. apply sv_eqb_eq in H1. apply sv_eqb_eq in H4. apply sv_eqb_eq in H10. rewrite forallb_forall in Hc.
split; [| split; [exact (agree_reg E 1 HA ltac:(lia)) | split; [exact H1 | split; [exact Hpc | split; [destruct (ss_resv ss); [discriminate | reflexivity] | rewrite (st_ok_reg src0segs _ ss ms 10 HS), H10; reflexivity]]]]].
intros r Hr. rewrite (st_ok_reg src0segs _ ss ms _ HS).
assert (CASE : r = 4 \/ exists k, In k cs_regsS /\ r = Z.of_nat k).
{ unfold callee_saved in Hr. unfold cs_regsS.
destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [right; exists 2%nat | right; exists 3%nat | left; reflexivity | right; exists 8%nat | right; exists 9%nat |];
try (split; [inlist | reflexivity]).
right. exists (Z.to_nat r). split; [|lia].
assert (H : (18 <= Z.to_nat r <= 27)%nat) by lia. revert H. generalize (Z.to_nat r) as m. intros m H.
do 18 (destruct m as [|m]; [lia|]). do 10 (destruct m as [|m]; [inlist|]). lia. }
destruct CASE as [-> | (k & Hk & ->)].
- replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite H4. cbn [sv_denot]. symmetry. exact P6.
- specialize (Hc k Hk). apply sv_eqb_eq in Hc. rewrite Hc. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
apply (agree_reg E k HA). unfold cs_regsS in Hk. cbn [In] in Hk. lia.
Qed.
Lemma f0E_checks : finalS_check ss_f0E (SLit (2 ^ 64 - 1)) = true /\ wsub (ss_mem ss_R0) SKS = true /\
nth_error (ss_mem ss_f0E) 0 = Some R_frame /\ nth_error (ss_mem ss_f0E) 2 = Some R_guard.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma leaf_R0_fail : forall s' L' mem' md' E' ms,
Inv X None U s' -> rawX X s' -> as_keep X A s' -> (forall g' am, usedX X s' g' am <-> usedX X A g' am) ->
layout_le A L L' -> midrep B L' s' mem' md' -> ama_ok s' -> bounded s' -> (exists vm', md' = with_vmmaps vm' md) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ WS x -> ~ (ERRNO <= x < ERRNO + 4) -> ~ (CTX <= x < CTX + CTX_SIZE) -> ~ in_nonmap_region L' s' x -> mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) ->
(forall a, ERRNO <= a < ERRNO + 4 -> writable_at src0segs mem' a) ->
env_agree 40 E00 E' -> ms = mkst (ms_regs ms) (Z_to_bv 64 PS_RAM) mem' (seg_rom src0segs) -> st_ok src0segs E' ss_R0 ms ->
SR src0segs (mkCfg ms md') (POST (-1, s')).
Proof.
intros s' L' mem' md' E' ms HI' RX' AK' US LE MID' AMA' BND' VM FR ERRW HA Ems HS.
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7). assert (EASF : ASF = 384) by reflexivity.
pose proof (mid_md _ _ _ _ _ MID') as (Mh' & Mlz' & Mmat').
assert (XCs : Xclean X s') by (intros x am Hx Hm; destruct (RX' x Hx) as [EXR|EXR]; rewrite EXR in Hm; discriminate).
assert (Emem : ms_mem ms = mem') by (rewrite Ems; reflexivity).
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E' ss_R0 ss_f0E); [exact Mh' | exact Mlz' | exact HS | apply run_R0 |].
intros ms4 HS4 HF4. rewrite Emem in HF4.
destruct f0E_checks as (CK & WSB & MF & MG).
assert (F4 : forall x, 0 <= x < 2 ^ 64 -> ~ WS x -> ms_mem ms4 (Z_to_bv 64 x) = mem' (Z_to_bv 64 x)).
{ intros x Hx Hnw. apply (frame_of_at E' (ss_mem ss_R0) mem' (ms_mem ms4) x HF4 Hx). intros Hw.
destruct (in_wrange_wsub regs E' (ss_mem ss_R0) SKS x WSB Hw) as (b & lo & hi & Hin & Hbx). apply Hnw.
unfold SKS in Hin. destruct Hin as [Hin|[]]. injection Hin as <- <- <-. cbn [base_val] in Hbx. rewrite (agree_reg E' 2 HA ltac:(lia)) in Hbx.
replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) in Hbx by (apply bv_eq; reflexivity). unfold WS. fold sp in Hbx. lia. }
destruct (finalS E' ss_f0E ms4 (SLit (2 ^ 64 - 1)) CK HS4 HA) as (PRS & E1 & Hra & Hpc & Hrv & RA0).
apply (SR_final_retS E' ss_f0E ms4 md' _ HS4 Hrv Hpc Hra); [rewrite E1; exact P1 | exact Mh' | exact Mlz' |].
exists L', (ms_regs ms4), (ms_mem ms4), md'. cbn [fst snd].
split; [rewrite E1; reflexivity|]. split.
{ apply (midrep_stack_gen X L' s' mem' md' _ HI' XCs AMA' MID' F4). }
split; [exact AMA'|]. split; [exact BND'|]. split.
{ apply (rsv_ok_xfer X s' HI' XCs). intros g' am H. exact (proj1 (US g' am) H). }
split. { apply (span_ok_xfer X s' XCs). intros g' am H. exact (proj1 (US g' am) H). }
split; [exact LE|]. split; [exact PRS|]. split; [exact VM|]. split.
{ intros x Hx Nc No No' Nn Ns. unfold call_scratch, spZ in Ns. rewrite B_errno in Ns. fold sp in Ns. rewrite B_ctx in Nc.
rewrite (F4 x Hx) by (unfold WS; lia). apply (FR x Hx); [unfold WS; lia | lia | exact Nc | exact Nn]. }
split.
{ intros a Ha. unfold call_scratch, spZ in Ha. rewrite B_errno in Ha. fold sp in Ha. destruct Ha as [Ha|Ha].
- destruct (Z_lt_le_dec a (sp - ASF)) as [Hlo|Hhi].
+ apply (writable_ext1 mem'); [apply F4; [lia | unfold WS; lia] |]. apply (writable_ext1 mem); [apply FR; [lia | unfold WS; lia | lits; lia | lits; unfold CTX_SIZE; lia | intros Hnm; destruct (nonmap_low L' s' mem' md' a MID' Hnm); lia] |].
apply P5. lia.
+ apply (writable_of_region regs E' ss_f0E ms4 0 R_frame a HS4 MF). cbn [r_base r_wlo r_whi base_val R_frame]. rewrite (agree_reg E' 2 HA ltac:(lia)).
replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity). fold sp. lia.
- apply (writable_ext1 mem'); [apply F4; [lits; lia | unfold WS; lits; lia] | apply ERRW; exact Ha]. }
split; [rewrite RA0; apply bv_eq; reflexivity|].
split; [intros H; lia|].
split; [exact AK' | exact (guard_of_state E' ss_f0E ms4 2 HS4 HA MG)].
Qed.
Definition after_am (r : option sptr * astate) (c' : config) : Prop :=
(Qam A r /\ (rawX X (snd r) /\ as_keep X A (snd r))) /\
exists L' mem' md' E', layout_le A L L' /\ midrep B L' (snd r) mem' md' /\ ama_ok (snd r) /\ bounded (snd r) /\
(exists vm', md' = with_vmmaps vm' md) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ WS x -> ~ (ERRNO <= x < ERRNO + 4) -> ~ (CTX <= x < CTX + CTX_SIZE) -> ~ in_nonmap_region L' (snd r) x ->
mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)) /\
(forall a, ERRNO <= a < ERRNO + 4 -> writable_at src0segs mem' a) /\
env_agree 40 E00 E' /\
c' = mkCfg (mkst (ms_regs (cfg_ms c')) (Z_to_bv 64 PS_RAM) mem' (seg_rom src0segs)) md' /\
match fst r with
| None => st_ok src0segs E' ss_R0 (cfg_ms c')
| Some m => ew E' 40 = Z_to_bv 64 (ptr_addr L' m) /\ st_ok src0segs E' ss_R1 (cfg_ms c')
end.
Definition SEG_group_body (fuel : nat) : Prop :=
forall m s' c', after_am (Some m, s') c' -> mreal src0segs c' (ibind (group_body fuel sc n m s') KS) POST.
Theorem from_G0 : forall fuel c, active_hd A sc = None -> SEG_group_body fuel -> at_st ss_G0 WS md c ->
mreal src0segs c (ibind (alloc_group (S fuel) sc n A) KS) POST.
Proof.
intros fuel c Hhd REST AT. rewrite alloc_group_tree, ibind_assoc.
apply (mreal_ibind src0segs (alloc_meta A) (fun r => ibind (KG fuel sc n r) KS) c after_am POST).
- exact (call_am c AT).
- intros [[m|] s'] c' POSTam.
+ exact (REST m s' c' POSTam).
+ destruct POSTam as [[Q [RX' AK']] (L' & mem' & md' & E' & LE & MID' & AMA' & BND' & VM & FR & ERRW & HA' & Ec & HS)]. cbn [fst snd] in *.
unfold KG. cbn [fst snd ibind KS mreal]. destruct c' as [ms' mdx]. cbn [cfg_ms cfg_model] in *. injection Ec as Ems Emd. subst mdx.
destruct Q as (_ & _ & HI' & US).
exact (leaf_R0_fail s' L' mem' md' E' ms' HI' RX' AK' US LE MID' AMA' BND' VM FR ERRW HA' Ems HS).
Qed.
Theorem slice_T0 : forall fuel, active_hd A sc = None -> j1 = J1LIT -> j2 = 0 -> SEG_group_body fuel ->
mreal src0segs (mkCfg ms0 md) (alloc_slot (S (S fuel)) sc n A) POST.
Proof.
intros fuel Hhd Hj1 Hj2 REST. rewrite alloc_slot_tree, (try_avail_none sc A Hhd). cbn [ibind]. unfold after_try. cbn [fst snd Z.eqb negb].
eapply mreal_SR_pre; [eapply SR_bind; [exact reach_hd | intros c1 H1; exact (reach_G0 c1 Hhd Hj1 Hj2 H1)] |].
intros c2 H2. exact (from_G0 fuel c2 Hhd REST H2).
Qed.
End AS.
Definition SEG_head_at (fuel : nat) : Prop :=
forall X U L A regs mem md sc n stk g,
Inv X None U A -> rawX X A -> ama_ok A -> bounded A -> rsv_ok A -> span_ok A -> 0 <= sc < 48 -> 0 <= n < MMAP_THRESHOLD ->
midrep B L A mem md -> (st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem) -> callee_pre B regs mem stk -> ASF <= stk <= AS_STACK ->
getr regs 10 = Z_to_bv 64 sc -> getr regs 11 = Z_to_bv 64 n -> word_mem src0segs mem GUARD g ->
active_hd A sc <> None ->
(forall k, U k = 0) ->
as_budget sc <= stk ->
(need sc <= S (S fuel))%nat ->
mreal src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_alloc_slot) mem (seg_rom src0segs)) md) (alloc_slot (S (S fuel)) sc n A)
(POST X L A regs mem md sc stk g).
Definition SEG_head : Prop := forall fuel, SEG_head_at fuel.
Definition SEG_group_at (fuel : nat) : Prop :=
forall X U L A regs mem md sc n stk g j1 j2,
Inv X None U A -> rawX X A -> ama_ok A -> bounded A -> rsv_ok A -> span_ok A -> 0 <= sc < 48 -> 0 <= n < MMAP_THRESHOLD ->
midrep B L A mem md -> (st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem) -> callee_pre B regs mem stk -> ASF <= stk <= AS_STACK ->
getr regs 10 = Z_to_bv 64 sc -> getr regs 11 = Z_to_bv 64 n -> word_mem src0segs mem GUARD g ->
(forall k, U k = 0) -> as_budget sc <= stk -> (need sc <= S (S fuel))%nat ->
SEG_group_body X U L A regs mem md sc n stk g j1 j2 fuel.
Definition SEG_group : Prop := forall fuel, SEG_group_at fuel.
Definition ASH (fuel : nat) : Prop :=
forall X U L A regs mem md sc n stk g,
Inv X None U A -> rawX X A -> ama_ok A -> bounded A -> rsv_ok A -> span_ok A -> 0 <= sc < 48 -> 0 <= n < MMAP_THRESHOLD ->
midrep B L A mem md -> (st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) mem) -> callee_pre B regs mem stk -> ASF <= stk <= AS_STACK ->
getr regs 10 = Z_to_bv 64 sc -> getr regs 11 = Z_to_bv 64 n -> word_mem src0segs mem GUARD g ->
(forall k, U k = 0) -> as_budget sc <= stk -> (need sc <= fuel)%nat ->
mreal src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_alloc_slot) mem (seg_rom src0segs)) md) (alloc_slot fuel sc n A)
(POST X L A regs mem md sc stk g).
Lemma user_block_in_map : forall X U A L p n x, Inv X None U A -> Xclean X A -> In (p, n) (user_blocks A) ->
ptr_addr L p <= x < ptr_addr L p + n ->
exists k rg, region_of A k = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\ ly_reg L k <= x < ly_reg L k + rg_len rg.
Proof.
intros X U A L p n x HI XC Hin Hx.
unfold user_blocks in Hin. apply in_flat_map in Hin as [[g am] [Hg Hin]]. cbn [snd] in Hin.
apply in_flat_map in Hin as [idx [Hidx Hin]]. apply In_zseq in Hidx.
destruct (ss_fr (nth_slot am idx)) as [fr|] eqn:Efr; [|destruct Hin].
destruct (fr_kind fr) eqn:Ek; [|destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
pose proof (proj1 (used_metas_usedX' X None U A HI XC g am) Hg) as Hu.
destruct (used_group_region X None U A g am HI Hu) as (rg & Hr & Hk & Hl & Ho & Hext & _).
pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
pose proof G as (_ & _ & Gsl & _).
pose proof (Gsl idx ltac:(lia)) as (_ & _ & S3). rewrite Efr in S3. destruct S3 as (_ & _ & (Nf & Of & Bf & _) & _).
exists (prid (am_mem am)), rg. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hl|].
unfold ptr_addr, slot_start in Hx. rewrite !loc_addr_LMem, !prid_padd, !poff_padd in Hx. unfold group_extent in Hext.
assert (Hsi : stride_of am * idx <= stride_of am * am_last am) by (apply Z.mul_le_mono_nonneg_l; lia).
unfold UNIT, IB in *. nia.
Qed.
Definition CTX_OWNED : Prop := forall U L A mem md x, Inv [] None U A -> midrep B L A mem md ->
ms_ctx B <= x < ms_ctx B + CTX_SIZE -> owned B L A x.
Lemma ctx_owned_ok : CTX_OWNED.
Proof.
intros U L A mem md x HI MID Hx. left. split.
- exists (LCtx 0, CTX_SIZE). split; [left; reflexivity|]. cbn [fst snd loc_addr]. rewrite (mid_ctx _ _ _ _ _ MID). lia.
- intros ([bp bn] & Hb & Hbx). cbn [fst snd] in Hbx.
destruct (user_block_in_map [] U A L bp bn x HI (Xclean_nil A) Hb Hbx) as (k & rg & Hrg & Hkind & Hlive & Hkx).
destruct (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID) k rg Hrg Hlive) as (_ & _ & _ & Himg).
apply (Himg x Hkx). apply (so_ctx_img _ (mid_syms _ _ _ _ _ MID)). exact Hx.
Qed.
Theorem src0_alloc_slot_partial : alloc_meta_hyp B -> SEG_head -> SEG_group -> alloc_slot_hyp B.
Proof.
intros AMH SH SG. pose proof ctx_owned_ok as CO. unfold alloc_slot_hyp. intros L A regs mem md sc n HW AMA BND RSV SPOK Hsc Hn Hfit MID AUXP PRE R10 R11. set (U := U0).
destruct (st_guard _ _ (mid_statics _ _ _ _ _ MID)) as [g Hg].
assert (RX : rawX [] A) by (intros x []).
assert (Hstk : ASF <= AS_STACK <= AS_STACK) by (unfold ASF, AS_STACK, ALLOC_STACK; lia).
assert (HB : as_budget sc <= AS_STACK) by (pose proof (as_budget_range sc ltac:(lia)); unfold AS_STACK, ALLOC_STACK; lia).
assert (HN : (need sc <= S (S 62))%nat) by (apply need_le_fuel; lia).
change NEST_FUEL with (S (S 62%nat)). change (pc_alloc_slot (ms_pcs B)) with src0_A_alloc_slot. change (ms_segs B) with src0segs.
assert (M : mreal src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_alloc_slot) mem (seg_rom src0segs)) md) (alloc_slot (S (S 62)) sc n A) (POST [] L A regs mem md sc AS_STACK g)).
{ destruct (active_hd A sc) as [h|] eqn:Eh.
- apply (SH 62%nat [] U L A regs mem md sc n AS_STACK g HW RX AMA BND RSV SPOK Hsc Hn MID AUXP PRE Hstk R10 R11 Hg); [rewrite Eh; discriminate | intros k; reflexivity | exact HB | exact HN].
- apply (slice_T0 [] U L A regs mem md sc n AS_STACK HW RX AMA BND RSV SPOK Hsc Hn MID AUXP PRE Hstk R10 R11 AMH g Hg J1LIT 0 62%nat Eh eq_refl eq_refl).
exact (SG 62%nat [] U L A regs mem md sc n AS_STACK g J1LIT 0 HW RX AMA BND RSV SPOK Hsc Hn MID AUXP PRE Hstk R10 R11 Hg (fun k => eq_refl) HB HN). }
eapply mreal_mono; [| exact M]. cbv beta. intros r c' (L' & regs' & mem' & md' & Ec & MID' & AMA' & BND' & RSV' & SPOK' & LE & PRS & VM & FR & SCR & RA0 & UZ & AK & GD).
exists L', regs', mem', md'. repeat (split; [assumption|]). split; [| split; [exact SCR | split; [exact RA0 | exact UZ]]].
intros x Hx No No' Nn Ns. apply (FR x Hx); try assumption. intros Hc. apply No. exact (CO U L A mem md x HW MID Hc).
Qed.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
