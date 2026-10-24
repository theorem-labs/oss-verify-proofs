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
YN2j YN2h YN2n YN2m YN2d YN2i
YN2k YN0j YN0h YN0i YN1k YN2w YN1d YN31 YN0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation B := src0_msyms.
Ltac inlist := cbn; repeat (first [left; reflexivity | right]).
Ltac lits := unfold LOCK, CTX, LIBC, ERRNO, TP, GOT, GUARD, SCT, SCNT, MCNT, ASF, src0_D_malloc_lock, src0_D_malloc_context, src0_D_libc, src0_tp,
src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab in *.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ab_st (sc : Z) (s : astate) : astate :=
match bounce_idx sc with
| Some k =>
let useq := znth k (st_unmap_seq s) in
let b := znth k (st_bounces s) in
if negb (useq =? 0) && (st_seq s - useq <? 10)
then set_bounces (zset k (if b + 1 <? 100 then b + 1 else 150) (st_bounces s)) s
else s
| None => s
end.
Definition seq_st (s : astate) : astate :=
if st_seq s =? 255 then set_seq 1 (set_unmap_seq (repeat 0 32) s) else set_seq (st_seq s + 1) s.
Lemma account_bounce_eq : forall sc s, account_bounce sc s = IRet (tt, ab_st sc s).
Proof. intros sc s. unfold account_bounce, ab_st. destruct (bounce_idx sc); reflexivity. Qed.
Lemma step_seq_eq : forall s, step_seq s = IRet (tt, seq_st s).
Proof. reflexivity. Qed.
End d.
Local Open Scope mm_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition mm_granted (sc : Z) (m : sptr) (cnt needed : Z) : M (option sptr) :=
r <- new_region RkMap (page_round needed) ;;
s0 <- get ;;
put (set_mmap_counter (Z.land (st_mmap_counter s0 + 1) (2^32 - 1)) s0) ;;
install_group m sc cnt
(if (if cnt - 1 <? (4096 - UNIT) / class_size sc - 1 then cnt - 1 else (4096 - UNIT) / class_size sc - 1) <? 0 then 0
else if cnt - 1 <? (4096 - UNIT) / class_size sc - 1 then cnt - 1 else (4096 - UNIT) / class_size sc - 1)
(needed / 4096) (SP r 0) slot_zero ;;
ret (Some m).
Lemma mm_body_eq : forall sc req m s,
mm_body sc req m s =
IAsk (KMmapRW (snd (mmap_plan s sc req (initial_cnt sc (usage_of s sc)) (usage_of s sc)))) (seq_st (ab_st sc s))
(fun z => (if negb (negb (z =? 0)) then (free_meta m ;; ret None)
else mm_granted sc m (fst (mmap_plan s sc req (initial_cnt sc (usage_of s sc)) (usage_of s sc)))
(snd (mmap_plan s sc req (initial_cnt sc (usage_of s sc)) (usage_of s sc)))) (seq_st (ab_st sc s))).
Proof.
intros sc req m s. unfold mm_body. unfold bind at 1. rewrite account_bounce_eq. cbn [ibind].
unfold bind at 1. rewrite step_seq_eq. cbn [ibind]. unfold bind at 1. unfold ask. cbn [ibind]. reflexivity.
Qed.
Lemma ab_st_fields : forall sc s,
st_metas (ab_st sc s) = st_metas s /\ st_areas (ab_st sc s) = st_areas s /\ st_regions (ab_st sc s) = st_regions s /\
st_brk (ab_st sc s) = st_brk s /\ st_usage (ab_st sc s) = st_usage s /\ st_active (ab_st sc s) = st_active s /\
st_seq (ab_st sc s) = st_seq s /\ st_unmap_seq (ab_st sc s) = st_unmap_seq s /\ st_mmap_counter (ab_st sc s) = st_mmap_counter s /\
st_init_done (ab_st sc s) = st_init_done s /\ st_free_meta_head (ab_st sc s) = st_free_meta_head s /\
st_avail_meta_areas (ab_st sc s) = st_avail_meta_areas s.
Proof.
intros sc s. unfold ab_st. destruct (bounce_idx sc) as [k|]; [| repeat split; reflexivity].
destruct (negb _ && _); repeat split; reflexivity.
Qed.
Lemma seq_st_fields : forall s,
st_metas (seq_st s) = st_metas s /\ st_areas (seq_st s) = st_areas s /\ st_regions (seq_st s) = st_regions s /\
st_brk (seq_st s) = st_brk s /\ st_usage (seq_st s) = st_usage s /\ st_active (seq_st s) = st_active s /\
st_bounces (seq_st s) = st_bounces s /\ st_mmap_counter (seq_st s) = st_mmap_counter s /\
st_init_done (seq_st s) = st_init_done s /\ st_free_meta_head (seq_st s) = st_free_meta_head s /\
st_avail_meta_areas (seq_st s) = st_avail_meta_areas s.
Proof. intros s. unfold seq_st. destruct (st_seq s =? 255); repeat split; reflexivity. Qed.
Lemma Inv_ab_st : forall X R U s sc, Inv X R U s -> Inv X R U (ab_st sc s).
Proof.
intros X R U s sc HI. pose proof (account_bounce_spec X R U s sc (fun r => Inv X R U (snd r)) HI ltac:(intros s' H _; exact H)) as T.
rewrite account_bounce_eq in T. exact T.
Qed.
Lemma Inv_seq_st : forall X R U s, Inv X R U s -> Inv X R U (seq_st s).
Proof.
intros X R U s HI. pose proof (step_seq_spec X R U s (fun r => Inv X R U (snd r)) HI ltac:(intros s' H _; exact H)) as T.
rewrite step_seq_eq in T. exact T.
Qed.
Lemma chunk_byte0 : forall E ss ms i j r c (w : N) v,
st_ok src0segs E ss ms -> nth_error (ss_mem ss) i = Some r -> nth_error (r_chunks r) j = Some c -> c_val c = CVal w v -> (0 < w)%N ->
mbyte src0segs (ms_mem ms) (base_val E (r_base r) + c_off c) = Some (byte_of_word (sv_denot E v) 0).
Proof.
intros E ss ms i j r c w v HS Hr Hc Hv Hw. destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hok & _) & _).
rewrite Forall_forall in Hok. specialize (Hok r (nth_error_In _ _ Hr)). destruct Hok as (_ & _ & _ & Hch).
rewrite Forall_forall in Hch. specialize (Hch c (nth_error_In _ _ Hc) 0). unfold c_len in Hch. rewrite Hv in Hch. cbn [cv_len cbyte] in Hch.
destruct (Hch ltac:(lia)) as (b & Hb1 & Hb2). injection Hb1 as <-. rewrite Z.add_0_r in Hb2. exact Hb2.
Qed.
Lemma chunk_bytek : forall E ss ms i j r c (w : N) v k,
st_ok src0segs E ss ms -> nth_error (ss_mem ss) i = Some r -> nth_error (r_chunks r) j = Some c -> c_val c = CVal w v -> 0 <= k < Z.of_N w ->
mbyte src0segs (ms_mem ms) (base_val E (r_base r) + c_off c + k) = Some (byte_of_word (sv_denot E v) k).
Proof.
intros E ss ms i j r c w v k HS Hr Hc Hv Hk. destruct HS as (_ & _ & _ & _ & _ & _ & _ & (_ & Hok & _) & _).
rewrite Forall_forall in Hok. specialize (Hok r (nth_error_In _ _ Hr)). destruct Hok as (_ & _ & _ & Hch).
rewrite Forall_forall in Hch. specialize (Hch c (nth_error_In _ _ Hc) k). unfold c_len in Hch. rewrite Hv in Hch. cbn [cv_len cbyte] in Hch.
destruct (Hch Hk) as (b & Hb1 & Hb2). injection Hb1 as <-. exact Hb2.
Qed.
Lemma byte_of_word_zero : forall k, byte_of_word (Z_to_bv 64 0) k = Z_to_bv 8 0.
Proof. intros k. unfold byte_of_word. rewrite lit64_small by lia. rewrite Z.shiftr_0_l. reflexivity. Qed.
Lemma byte_of_word0 : forall v, 0 <= v < 2 ^ 64 -> byte_of_word (Z_to_bv 64 v) 0 = Z_to_bv 8 (v mod 256).
Proof.
intros v Hv. unfold byte_of_word. rewrite lit64_small by lia. rewrite Z.mul_0_r, Z.shiftr_0_r.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma le_byte_1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r, (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.
Section f.
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
Local Notation csn := (cs L A sc g j1 j2).
Local Notation E00 := (E0 regs csn).
Local Notation WSn := (WS regs).
Let agree_cs' := agree_cs L A regs sc g j1 j2.
Let sv_cs' := sv_cs L A regs sc g j1 j2.
Let agree_reg' := agree_reg L A regs sc g j1 j2.
Let cs_facts' := cs_facts X U L A regs mem md sc HI Hsc MID g j1 j2.
Let pre_facts' := pre_facts regs mem stk PRE.
Let nu : Z := cs L A sc g j1 j2 35.
Definition ctx_off (c : mcell) : Z := match mc_loc c with LCtx o => o | _ => 0 end.
Lemma midrep_ctx : forall X' L1 A1 A2 m1 m2 md1 (W : Z -> Prop),
Inv X' None U A1 -> Xclean X' A1 -> ama_ok A1 -> midrep B L1 A1 m1 md1 ->
st_metas A2 = st_metas A1 -> st_areas A2 = st_areas A1 -> st_regions A2 = st_regions A1 -> st_brk A2 = st_brk A1 ->
(forall x, W x \/ ~ W x) -> (forall x, W x -> WSn x \/ CTX <= x < CTX + CTX_SIZE) ->
(forall x, 0 <= x < 2 ^ 64 -> ~ W x -> m2 (Z_to_bv 64 x) = m1 (Z_to_bv 64 x)) ->
(forall c, In c (ctx_cells A2) -> (In c (ctx_cells A1) /\ forall k, (k < mc_w c)%nat -> ~ W (CTX + ctx_off c + Z.of_nat k)) \/ cell_mem B L1 m2 c) ->
midrep B L1 A2 m2 md1.
Proof.
intros X1 L1 A1 A2 m1 m2 md1 W HI1 XC1 AMA1 MID1 EM EA ER EB Wdec Wsub FR CELLS.
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts' as (_ & _ & P3 & _).
pose proof (inv_areas HI1) as (NDA & Hareas & _). pose proof (mid_syms _ _ _ _ _ MID1) as SO.
assert (CTXhi : CTX + CTX_SIZE <= alloc_ceiling) by (pose proof (so_ctx_hi _ SO) as Y; exact Y).
assert (LOWc : forall x, W x -> alloc_ceiling <= x \/ CTX <= x < CTX + CTX_SIZE) by (intros x Hx; destruct (Wsub x Hx) as [Hw|Hc]; [left; unfold WS, ASF in *; lia | right; exact Hc]).
assert (UM : used_metas A2 = used_metas A1) by (unfold used_metas; rewrite EM; reflexivity).
assert (NDA2 : List.NoDup (st_areas A2)) by (rewrite EA; exact NDA).
assert (RO : forall k, region_of A2 k = region_of A1 k) by (intros k; unfold region_of; rewrite ER; reflexivity).
assert (MR' : memrep B L1 A2 m2).
{ refine (memrep_xfer B X1 None U L1 L1 A1 A2 m1 m2 md1 HI1 XC1 AMA1 MID1 UM [] _ _ NDA2 _ _ eq_refl eq_refl _ W Wdec FR _ [] _ _ _ _ _ _ _ _ _).
- rewrite app_nil_r. exact EA.
- intros p q l H. discriminate.
- intros k rg H Hl Hk. rewrite RO in H. exact H.
- intros k rg H _ _. rewrite RO. exact H.
- intros; reflexivity.
- intros x k rg Hx Hk Hl Hkd Hin. pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID1) k rg Hk Hl) as (_ & _ & Phi & Pimg).
destruct (LOWc x Hx) as [Hlo|Hc]; [lia|]. apply (Pimg x Hin). apply (so_ctx_img _ SO). change (ms_ctx B) with CTX. exact Hc.
- intros x a Hx Ha Hin. exfalso. destruct (areas_off_img B X1 None U L1 A1 m1 md1 HI1 MID1 a x Ha Hin) as [NI Rx].
destruct (LOWc x Hx) as [Hlo|Hc]; [lia|]. apply NI. apply (so_ctx_img _ SO). change (ms_ctx B) with CTX. exact Hc.
- intros x a Hx Ha Hin. exfalso. destruct (areas_off_img B X1 None U L1 A1 m1 md1 HI1 MID1 a x Ha Hin) as [NI Rx].
destruct (LOWc x Hx) as [Hlo|Hc]; [lia|]. apply NI. apply (so_ctx_img _ SO). change (ms_ctx B) with CTX. exact Hc.
- intros q [].
- intros q [].
- intros a k Ha Hk _. unfold MT. rewrite EM. reflexivity.
- intros p H. discriminate.
- intros p c H. discriminate.
- intros p x H. discriminate.
- intros c Hc. destruct (CELLS c Hc) as [[Hc1 HW]|Hm]; [left | right; exact Hm]. split; [exact Hc1|].
intros k Hk. destruct (In_ctx_cells A1 c Hc1) as (off & El & _). change (ms_ctx B) with CTX. unfold ctx_off in HW. rewrite El in HW |- *. exact (HW k Hk). }
pose proof (YN2i.ledger_same B L1 A1 md1 (mid_ledger _ _ _ _ _ MID1) (mid_ledgerx _ _ _ _ _ MID1) A2 md1 ER EB eq_refl eq_refl eq_refl) as [LG2 LX2].
split.
- exact SO.
- exact MR'.
- eapply (tail_geom_xfer B X1 None U L1 L1 A1 A2 m1 md1 HI1 XC1 MID1); [exact UM | intros k rg H _ _; rewrite RO; exact H | reflexivity | intros; reflexivity].
- apply (YN2d.statics_ok_ext B A1 0 m1); [| exact (mid_statics _ _ _ _ _ MID1)]. intros x Hx.
pose proof (so_img_hi _ SO x (so_statics_img _ SO x Hx)) as Hhi. apply FR; [lia|]. intros Hw.
destruct (LOWc x Hw) as [Hlo|Hc]; [lia|]. exact (src0_SNC x Hx Hc).
- exact LG2.
- exact LX2.
- apply (YN2d.layout_ok_same L1 A1 A2 (mid_layout _ _ _ _ _ MID1) ER). unfold footprint. rewrite EA, ER. f_equal. f_equal.
apply YN2c.flat_map_ext_in. intros k _. rewrite RO. reflexivity.
- exact (mid_ctx _ _ _ _ _ MID1).
- exact (mid_sec _ _ _ _ _ MID1).
- exact (mid_md _ _ _ _ _ MID1).
Qed.
Lemma ctx_byte_gen : forall L1 A1 m1 md1 off v, midrep B L1 A1 m1 md1 -> In (MCell (LCtx off) 1 (VZ v)) (ctx_cells A1) -> 0 <= v <= 255 ->
mbyte src0segs m1 (CTX + off) = Some (Z_to_bv 8 v).
Proof.
intros L1 A1 m1 md1 off v MID1 Hin Hv.
pose proof (memrep_cell B L1 A1 m1 _ (mid_mem _ _ _ _ _ MID1) ltac:(unfold image; apply in_app_iff; left; exact Hin)) as C.
unfold cell_mem in C. cbn [mc_loc mc_w mc_val loc_addr sval_num] in C. rewrite (mid_ctx _ _ _ _ _ MID1) in C. change (ms_ctx B) with CTX in C.
specialize (C 0%nat ltac:(lia)). cbn [Z.of_nat] in C. rewrite Z.add_0_r, le_byte_1 in C by lia. exact C.
Qed.
Lemma In_bounces_cell : forall s k, (k < 32)%nat -> In (MCell (LCtx (CTX_bounces + Z.of_nat k)) 1 (VZ (nth k (st_bounces s) 0))) (ctx_cells s).
Proof. intros s k Hk. unfold ctx_cells. rewrite !in_app_iff. right. right. right. right. apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia]. Qed.
Lemma In_useq_cell : forall s k, (k < 32)%nat -> In (MCell (LCtx (CTX_unmap_seq + Z.of_nat k)) 1 (VZ (nth k (st_unmap_seq s) 0))) (ctx_cells s).
Proof. intros s k Hk. unfold ctx_cells. rewrite !in_app_iff. right. right. right. left. apply in_map_iff. exists k. split; [reflexivity | apply in_seq; lia]. Qed.
Lemma In_seq_cell : forall s, In (MCell (LCtx CTX_seq) 1 (VZ (st_seq s))) (ctx_cells s).
Proof. intros s. unfold ctx_cells. rewrite !in_app_iff. left. inlist. Qed.
Section MA.
Variables (m : sptr) (s1 : astate) (L1 : layout) (mem1 : word -> option byte) (md1 : Model).
Hypothesis HI1 : Inv (m :: X) None U s1.
Hypothesis RX1 : rawX X s1.
Hypothesis Mm : MT s1 m = Some MRaw \/ MT s1 m = Some (MFree None None).
Hypothesis MID1 : midrep B L1 s1 mem1 md1.
Hypothesis AMA1 : ama_ok s1.
Hypothesis BND1 : bounded s1.
Variable E : env.
Hypothesis HA : env_agree 40 E00 E.
Hypothesis E40 : ew E 40 = Z_to_bv 64 (ptr_addr L1 m).
Hypothesis E56 : ew E 56 = Z_to_bv 64 (usage_of s1 sc).
Hypothesis E61 : ew E 61 = Z_to_bv 64 (initial_cnt sc (usage_of s1 sc)).
Hypothesis E62 : ew E 62 = Z_to_bv 64 (16 * nu * initial_cnt sc (usage_of s1 sc)).
Let Mh1 : m_halted md1 = None := proj1 (mid_md _ _ _ _ _ MID1).
Let Mlz1 : m_vm_lazy md1 = [] := proj1 (proj2 (mid_md _ _ _ _ _ MID1)).
Lemma XC1 : Xclean (m :: X) s1.
Proof.
intros x am [<-|Hx] Hu; [destruct Mm as [Mq|Mq]; rewrite Mq in Hu; discriminate|]. destruct (RX1 x Hx) as [Mq|Mq]; rewrite Mq in Hu; discriminate.
Qed.
Let k0 : Z := sc - 7.
Let bnc : Z := znth k0 (st_bounces s1).
Let usq : Z := znth k0 (st_unmap_seq s1).
Let seq : Z := st_seq s1.
Let s2 : astate := ab_st sc s1.
Let s3 : astate := seq_st s2.
Let nosm : Z := if is_bouncing s1 sc then 1 else 0.
Let Eb : env := ewset (ewset (ewset E 64 (Z_to_bv 64 bnc)) 65 (Z_to_bv 64 usq)) 66 (Z_to_bv 64 seq).
Definition W0 (x : Z) : Prop := WSn x \/ (7 <= sc <= 38 /\ x = LOCK + 881 + sc) \/ x = LOCK + 920.
Definition W1 (x : Z) : Prop := W0 x \/ LOCK + 856 <= x < LOCK + 888.
Local Notation FRW := (YN1d.FRM mem1).
Definition CWA (W : Z -> Prop) (E' : env) (ss : sstate) (c : config) : Prop :=
exists ms, c = mkCfg ms md1 /\ st_ok src0segs E' ss ms /\ FRW W (ms_mem ms).
Lemma ctx_facts : 0 <= bnc <= 255 /\ 0 <= usq <= 255 /\ 0 <= seq <= 255 /\
(7 <= sc <= 38 -> bnc = nth (Z.to_nat k0) (st_bounces s1) 0 /\ usq = nth (Z.to_nat k0) (st_unmap_seq s1) 0 /\ (Z.to_nat k0 < 32)%nat).
Proof.
pose proof (inv_ctx HI1) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & _).
subst bnc usq seq k0. unfold znth. split; [| split; [| split; [exact C8 | intros Hr; repeat split; lia]]].
- destruct (Nat.lt_ge_cases (Z.to_nat (sc - 7)) (length (st_bounces s1))) as [Hl|Hl]; [apply C7; apply nth_In; exact Hl | rewrite nth_overflow by exact Hl; lia].
- destruct (Nat.lt_ge_cases (Z.to_nat (sc - 7)) (length (st_unmap_seq s1))) as [Hl|Hl]; [apply C6; apply nth_In; exact Hl | rewrite nth_overflow by exact Hl; lia].
Qed.
Lemma Eb_facts : env_agree 64 E Eb /\ ew Eb 64 = Z_to_bv 64 bnc /\ ew Eb 65 = Z_to_bv 64 usq /\ ew Eb 66 = Z_to_bv 64 seq /\
env_agree 40 E00 Eb /\ ew Eb 10 = Z_to_bv 64 sc /\ ew Eb 33 = Z_to_bv 64 (csn 33).
Proof.
assert (AG : env_agree 64 E Eb) by (split; [intros k Hk; subst Eb; rewrite !ew_ewset_other by lia; reflexivity | reflexivity]).
assert (AG' : env_agree 40 E00 Eb) by (eapply env_agree_trans; [exact HA | eapply env_agree_le; [| exact AG]; lia]).
split; [exact AG|]. split; [subst Eb; rewrite !ew_ewset_other, ew_ewset_same by lia; reflexivity|].
split; [subst Eb; rewrite ew_ewset_other, ew_ewset_same by lia; reflexivity|]. split; [subst Eb; apply ew_ewset_same|]. split; [exact AG'|].
split; [rewrite (agree_reg' _ 10 AG') by lia; exact R10 | exact (agree_cs' _ 33 AG' ltac:(lia))].
Qed.
Definition SKA : list (option nat * Z * Z) := [(Some 2%nat, -ASF, 0); (Some 10%nat, LOCK + 881, LOCK + 882); (None, LOCK + 920, LOCK + 921)].
Definition SKo : list (option nat * Z * Z) := [(Some 2%nat, -ASF, 0); (None, LOCK + 920, LOCK + 921)].
Definition SKB : list (option nat * Z * Z) := [(None, LOCK + 856, LOCK + 888); (Some 2%nat, -ASF, 0); (None, LOCK + 920, LOCK + 921)].
Lemma win_stack : forall E' x, env_agree 40 E00 E' -> base_val E' (Some 2%nat) + - ASF <= x < base_val E' (Some 2%nat) + 0 -> WSn x.
Proof.
intros E' x HA' Hx. unfold WS. cbn [base_val] in Hx. rewrite (agree_reg' E' 2 HA' ltac:(lia)) in Hx.
replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) in Hx by (apply bv_eq; reflexivity). lia.
Qed.
Lemma SKA_W0 : forall E', env_agree 40 E00 E' -> ew E' 10 = Z_to_bv 64 sc -> 7 <= sc <= 38 ->
forall b lo hi x, In (b, lo, hi) SKA -> base_val E' b + lo <= x < base_val E' b + hi -> W0 x.
Proof.
intros E' HA' E10 Hr b lo hi x Hin Hx. unfold SKA in Hin.
destruct Hin as [H|[H|[H|[]]]]; injection H as <- <- <-.
- left. exact (win_stack E' x HA' Hx).
- right. left. cbn [base_val] in Hx. rewrite E10, lit64_small in Hx by lia. lia.
- right. right. cbn [base_val] in Hx. lia.
Qed.
Lemma SKo_W0 : forall E', env_agree 40 E00 E' ->
forall b lo hi x, In (b, lo, hi) SKo -> base_val E' b + lo <= x < base_val E' b + hi -> W0 x.
Proof.
intros E' HA' b lo hi x Hin Hx. unfold SKo in Hin.
destruct Hin as [H|[H|[]]]; injection H as <- <- <-.
- left. exact (win_stack E' x HA' Hx).
- right. right. cbn [base_val] in Hx. lia.
Qed.
Lemma SKB_W1 : forall E', env_agree 40 E00 E' ->
forall b lo hi x, In (b, lo, hi) SKB -> base_val E' b + lo <= x < base_val E' b + hi -> W1 x.
Proof.
intros E' HA' b lo hi x Hin Hx. unfold SKB in Hin.
destruct Hin as [H|[H|[H|[]]]]; injection H as <- <- <-.
- right. cbn [base_val] in Hx. lia.
- left. left. exact (win_stack E' x HA' Hx).
- left. right. right. cbn [base_val] in Hx. lia.
Qed.
Lemma cwa_run : forall (W : Z -> Prop) sk E' S ss ss' st (Q : config -> Prop),
sym_run_toN src0segs src0tbl FUEL S ss = (ss', st) -> match st with RS_ecall => False | _ => True end ->
wsub (ss_mem ss) sk = true ->
(forall b lo hi x, In (b, lo, hi) sk -> base_val E' b + lo <= x < base_val E' b + hi -> W x) ->
(forall ms', st_ok src0segs E' ss' ms' -> FRW W (ms_mem ms') -> SR src0segs (mkCfg ms' md1) Q) ->
forall cfg, CWA W E' ss cfg -> SR src0segs cfg Q.
Proof.
intros W sk E' S ss ss' st Q RUN NE WSB HSK K cfg (ms & -> & HS & HF).
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL S E' ss ss' st); [exact Mh1 | exact Mlz1 | exact HS | exact RUN |].
intros ms' HS' Hfr. apply K; [destruct st; first [exact HS' | destruct NE]|].
eapply (FRM_run regs mem1 W E'); [exact HF | exact Hfr | exact WSB | exact HSK].
Qed.
Lemma sk_ma1 : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_ma1) =
[(Some 33%nat, 472, 480); (Some 2%nat, -ASF, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56)]
/\ ss_mem ss_mo1 = ss_mem ss_ma1 /\ ss_mem ss_ma0 = ss_mem ss_ma1.
Proof. vm_compute. repeat split; reflexivity. Qed.
Ltac solve_disj Hr :=
cbn [In] in Hr;
repeat (destruct Hr as [Hr|Hr]; [apply (f_equal (fun t => match t with (b, lo, hi) => (b, lo, hi) end)) in Hr; cbn in Hr; injection Hr as <- <- <-; cbn [base_val] |]);
try (destruct Hr).
Lemma station_SB : 7 <= sc <= 38 -> forall ms, st_ok src0segs E ss_ma1 ms -> YN1d.FRM mem1 WSn (ms_mem ms) -> st_ok src0segs Eb ss_SB ms.
Proof.
intros Hr ms HS HF. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
destruct cs_facts' as (C33 & C33m & _). destruct Eb_facts as (AG & E64 & E65 & E66 & AG' & E10 & E33).
destruct ctx_facts as (Bb & Bu & Bs & BK). destruct (BK Hr) as (Ebnc & Eusq & K32).
pose proof (so_ctx_hi _ (mid_syms _ _ _ _ _ MID1)) as CH. change (ms_ctx B) with CTX in CH.
assert (NW : forall x, CTX <= x < CTX + CTX_SIZE -> ~ WSn x) by (intros x Hx Hw; unfold WS, CTX_SIZE in *; lia).
assert (HS0 : st_ok src0segs Eb ss_ma1 ms) by (eapply (st_ok_agree src0segs 64 E Eb); [exact HS | exact AG | vm_compute; reflexivity]).
assert (B10 : bv_unsigned (ew Eb 10) = sc) by (rewrite E10; apply lit64_small; lia).
assert (B33 : bv_unsigned (ew Eb 33) = csn 33) by (rewrite E33; apply lit64_small; lits; lia).
assert (B2 : bv_unsigned (ew Eb 2) = sp) by (rewrite (agree_reg' Eb 2 AG') by lia; reflexivity).
assert (HS1 : st_ok src0segs Eb (mkSS (ss_pc ss_ma1) (ss_regs ss_ma1) (R_seqb :: ss_mem ss_ma1) (ss_resv ss_ma1) (ss_facts ss_ma1)) ms).
{ apply (st_ok_add_region src0segs Eb _ ms R_seqb HS0); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_seqb]; [lits; lia | lits; lia | |].
+ intros o Ho. rewrite Z.add_0_l. apply (ctxw L1 s1 mem1 md1 MID1). lits. lia.
+ apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_cval src0segs Eb (ms_mem ms) 0 (LOCK + 920) 1 _ seq); [apply den_off0; exact E66 | lia |].
intros k Hk. destruct k; [| lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Z.add_0_l. rewrite le_byte_1 by lia.
rewrite (mbyte_ext1 mem1) by (apply HF; [lits; lia | apply NW; unfold CTX_SIZE; lits; lia]).
replace (LOCK + 920) with (CTX + CTX_seq) by (unfold CTX_seq; lits; lia). exact (ctx_byte_gen L1 s1 mem1 md1 _ _ MID1 (In_seq_cell s1) Bs).
- apply Forall_forall. intros r Hr'. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite (proj1 sk_ma1) in Hr'.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_seqb]. solve_disj Hr'; rewrite ?B33, ?B2; cbn [base_val]; lits; lia. }
assert (HS2 : st_ok src0segs Eb (mkSS (ss_pc ss_ma1) (ss_regs ss_ma1) (R_usq :: R_seqb :: ss_mem ss_ma1) (ss_resv ss_ma1) (ss_facts ss_ma1)) ms).
{ apply (st_ok_add_region src0segs Eb _ ms R_usq HS1); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_usq base_val]; rewrite B10; [lits; lia | lits; lia | intros o Ho; lia |].
apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_cval src0segs Eb (ms_mem ms) sc (LOCK + 849) 1 _ usq); [apply den_off0; exact E65 | lia |].
intros k Hk. destruct k; [| lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite le_byte_1 by lia.
rewrite (mbyte_ext1 mem1) by (apply HF; [lits; lia | apply NW; unfold CTX_SIZE; lits; lia]).
replace (sc + (LOCK + 849)) with (CTX + (CTX_unmap_seq + Z.of_nat (Z.to_nat k0))) by (unfold CTX_unmap_seq; subst k0; lits; lia).
rewrite Eusq. exact (ctx_byte_gen L1 s1 mem1 md1 _ _ MID1 (In_useq_cell s1 _ K32) ltac:(rewrite <- Eusq; exact Bu)).
- apply Forall_forall. intros r Hr'. cbn [ss_mem] in Hr'. destruct Hr' as [<-|Hr'].
+ unfold extent_disjoint. cbn [r_base r_lo r_hi R_usq R_seqb base_val]. rewrite B10. lits. lia.
+ apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite (proj1 sk_ma1) in Hr'.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_usq base_val]. rewrite B10. solve_disj Hr'; rewrite ?B33, ?B2; cbn [base_val]; lits; lia. }
assert (HS3 : st_ok src0segs Eb (mkSS (ss_pc ss_ma1) (ss_regs ss_ma1) (R_bnc :: R_usq :: R_seqb :: ss_mem ss_ma1) (ss_resv ss_ma1) (ss_facts ss_ma1)) ms).
{ apply (st_ok_add_region src0segs Eb _ ms R_bnc HS2); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_bnc base_val]; rewrite B10; [lits; lia | lits; lia | |].
+ intros o Ho. apply (ctxw L1 s1 mem1 md1 MID1). lits. lia.
+ apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_cval src0segs Eb (ms_mem ms) sc (LOCK + 881) 1 _ bnc); [apply den_off0; exact E64 | lia |].
intros k Hk. destruct k; [| lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite le_byte_1 by lia.
rewrite (mbyte_ext1 mem1) by (apply HF; [lits; lia | apply NW; unfold CTX_SIZE; lits; lia]).
replace (sc + (LOCK + 881)) with (CTX + (CTX_bounces + Z.of_nat (Z.to_nat k0))) by (unfold CTX_bounces; subst k0; lits; lia).
rewrite Ebnc. exact (ctx_byte_gen L1 s1 mem1 md1 _ _ MID1 (In_bounces_cell s1 _ K32) ltac:(rewrite <- Ebnc; exact Bb)).
- apply Forall_forall. intros r Hr'. cbn [ss_mem] in Hr'. destruct Hr' as [<-|[<-|Hr']].
+ unfold extent_disjoint. cbn [r_base r_lo r_hi R_usq R_bnc base_val]. rewrite B10. lits. lia.
+ unfold extent_disjoint. cbn [r_base r_lo r_hi R_bnc R_seqb base_val]. rewrite B10. lits. lia.
+ apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite (proj1 sk_ma1) in Hr'.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_bnc base_val]. rewrite B10. solve_disj Hr'; rewrite ?B33, ?B2; cbn [base_val]; lits; lia. }
apply (st_ok_add_fact src0segs Eb _ ms 66 F_byte) in HS3. 2:{ unfold afact_ok, F_byte. cbn [af_lo af_hi af_al2]. rewrite E66, lit64_small by lia. split; [lia|]. split; [| lia]. change (2 ^ 0) with 1. apply Z.mod_1_r. }
apply (st_ok_add_fact src0segs Eb _ ms 65 F_byte) in HS3. 2:{ unfold afact_ok, F_byte. cbn [af_lo af_hi af_al2]. rewrite E65, lit64_small by lia. split; [lia|]. split; [| lia]. change (2 ^ 0) with 1. apply Z.mod_1_r. }
apply (st_ok_add_fact src0segs Eb _ ms 64 F_byte) in HS3. 2:{ unfold afact_ok, F_byte. cbn [af_lo af_hi af_al2]. rewrite E64, lit64_small by lia. split; [lia|]. split; [| lia]. change (2 ^ 0) with 1. apply Z.mod_1_r. }
exact HS3.
Qed.
Lemma station_SO : forall ms, st_ok src0segs E ss_mo1 ms -> YN1d.FRM mem1 WSn (ms_mem ms) -> st_ok src0segs Eb ss_SO ms.
Proof.
intros ms HS HF. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
destruct cs_facts' as (C33 & C33m & _). destruct Eb_facts as (AG & E64 & E65 & E66 & AG' & E10 & E33). destruct ctx_facts as (Bb & Bu & Bs & BK).
pose proof (so_ctx_hi _ (mid_syms _ _ _ _ _ MID1)) as CH. change (ms_ctx B) with CTX in CH.
assert (NW : forall x, CTX <= x < CTX + CTX_SIZE -> ~ WSn x) by (intros x Hx Hw; unfold WS, CTX_SIZE in *; lia).
assert (HS0 : st_ok src0segs Eb ss_mo1 ms) by (eapply (st_ok_agree src0segs 64 E Eb); [exact HS | exact AG | vm_compute; reflexivity]).
assert (B33 : bv_unsigned (ew Eb 33) = csn 33) by (rewrite E33; apply lit64_small; lits; lia).
assert (B2 : bv_unsigned (ew Eb 2) = sp) by (rewrite (agree_reg' Eb 2 AG') by lia; reflexivity).
assert (HS1 : st_ok src0segs Eb (mkSS (ss_pc ss_mo1) (ss_regs ss_mo1) (R_seqb :: ss_mem ss_mo1) (ss_resv ss_mo1) (ss_facts ss_mo1)) ms).
{ apply (st_ok_add_region src0segs Eb _ ms R_seqb HS0); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_seqb]; [lits; lia | lits; lia | |].
+ intros o Ho. rewrite Z.add_0_l. apply (ctxw L1 s1 mem1 md1 MID1). lits. lia.
+ apply Forall_cons; [| apply Forall_nil]. apply (chunk_ok_cval src0segs Eb (ms_mem ms) 0 (LOCK + 920) 1 _ seq); [apply den_off0; exact E66 | lia |].
intros k Hk. destruct k; [| lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Z.add_0_l. rewrite le_byte_1 by lia.
rewrite (mbyte_ext1 mem1) by (apply HF; [lits; lia | apply NW; unfold CTX_SIZE; lits; lia]).
replace (LOCK + 920) with (CTX + CTX_seq) by (unfold CTX_seq; lits; lia). exact (ctx_byte_gen L1 s1 mem1 md1 _ _ MID1 (In_seq_cell s1) Bs).
- rewrite (proj1 (proj2 sk_ma1)). apply Forall_forall. intros r Hr'. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite (proj1 sk_ma1) in Hr'.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_seqb]. solve_disj Hr'; rewrite ?B33, ?B2; cbn [base_val]; lits; lia. }
apply (st_ok_add_fact src0segs Eb _ ms 66 F_byte) in HS1. 2:{ unfold afact_ok, F_byte. cbn [af_lo af_hi af_al2]. rewrite E66, lit64_small by lia. split; [lia|]. split; [| lia]. change (2 ^ 0) with 1. apply Z.mod_1_r. }
exact HS1.
Qed.
Definition BNC (mm : word -> option byte) : Prop :=
7 <= sc <= 38 -> mbyte src0segs mm (LOCK + 881 + sc) = Some (Z_to_bv 8 (znth k0 (st_bounces s2))).
Definition M0post (c : config) : Prop :=
exists E2 ms, c = mkCfg ms md1 /\ st_ok src0segs E2 ss_M0 ms /\ env_agree 67 Eb E2 /\ ew E2 67 = Z_to_bv 64 nosm /\ FRW W0 (ms_mem ms) /\ BNC (ms_mem ms).
Lemma nosm_range : 0 <= nosm <= 1. Proof. subst nosm. destruct (is_bouncing s1 sc); lia. Qed.
Lemma nosm_in : 7 <= sc <= 38 -> nosm = (if bnc <? 100 then 0 else 1).
Proof.
intros Hr. subst nosm bnc k0. unfold is_bouncing, bounce_idx.
replace ((7 <=? sc) && (sc <? 39)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
destruct (znth (sc - 7) (st_bounces s1) <? 100) eqn:Y; [apply Z.ltb_lt in Y | apply Z.ltb_ge in Y];
[replace (100 <=? _) with false by (symmetry; apply Z.leb_gt; lia) | replace (100 <=? _) with true by (symmetry; apply Z.leb_le; lia)]; reflexivity.
Qed.
Lemma nosm_out : ~ 7 <= sc <= 38 -> nosm = 0 /\ s2 = s1.
Proof.
intros Hr. subst nosm s2. unfold is_bouncing, ab_st, bounce_idx.
replace ((7 <=? sc) && (sc <? 39)) with false; [split; reflexivity|].
symmetry. destruct (7 <=? sc) eqn:Y1; [apply Z.leb_le in Y1 | reflexivity]. cbn [andb]. apply Z.ltb_ge. lia.
Qed.
Lemma s2_in : 7 <= sc <= 38 ->
s2 = (if negb (usq =? 0) && (seq - usq <? 10) then set_bounces (zset k0 (if bnc + 1 <? 100 then bnc + 1 else 150) (st_bounces s1)) s1 else s1).
Proof.
intros Hr. subst s2 usq seq bnc k0. unfold ab_st, bounce_idx.
replace ((7 <=? sc) && (sc <? 39)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity.
Qed.
Definition m0_check2 (ss : sstate) : bool := m0_check ss && facts_subb (ss_facts ss_ma0) (ss_facts ss).
Lemma to_M0 : forall ss ms, m0_check2 ss = true -> st_ok src0segs Eb ss ms ->
sv_denot Eb (sr_get (ss_regs ss) 13) = Z_to_bv 64 nosm -> FRW W0 (ms_mem ms) -> BNC (ms_mem ms) -> M0post (mkCfg ms md1).
Proof.
intros ss ms CK HS D13 HF HB. pose proof nosm_range as NR. destruct Eb_facts as (AG & E64 & E65 & E66 & AG' & E10 & E33). destruct ctx_facts as (Bb & Bu & Bs & BK).
unfold m0_check2, m0_check in CK. apply andb_prop in CK as [CK FS]. apply andb_prop in CK as [AT MG].
assert (NZ : forallb (fun r : reg => negb (bv_eqb r 0)) M0_JUNK = true) by (vm_compute; reflexivity).
destruct (junk_regs_ok src0segs M0_JUNK 67 Eb ss ms HS AT NZ) as (E2 & HA2 & HS2).
assert (R13 : sr_get (ss_regs (junk_regs M0_JUNK 67 ss)) 13 = SOff 67 0).
{ unfold M0_JUNK. cbn [junk_regs ss_regs]. rewrite !sr_get_set_other by (intros H; discriminate). apply sr_get_set_same. reflexivity. }
assert (E67 : ew E2 67 = Z_to_bv 64 nosm).
{ pose proof (st_ok_regs_ok _ E2 _ ms HS2 13%bv) as X1. pose proof (st_ok_regs_ok _ Eb _ ms HS 13%bv) as X2. rewrite R13 in X1. rewrite D13 in X2.
cbn [sv_denot] in X1. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in X1. rewrite <- X1. exact X2. }
destruct HA2 as [Y D2].
assert (HFM : facts_ok E2 facts_M0).
{ destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HF0). pose proof (facts_subb_sound Eb _ _ FS HF0) as HF1.
assert (AT0 : facts_atoms_lt 64 (ss_facts ss_ma0) = true) by (vm_compute; reflexivity).
assert (AG2 : env_agree 64 Eb E2) by (split; [intros k Hk; apply Y; lia | exact D2]).
pose proof (facts_ok_agree 64 Eb E2 (ss_facts ss_ma0) AG2 AT0 HF1) as (Y1 & Y2 & Y3).
unfold facts_M0. split; [| split; [exact Y2 | exact I]]. cbn [f_atoms atoms_ok]. split; [| split; [| exact Y1]].
- unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E67, lit64_small by lia. split; [lia|]. split; [| lia]. change (2 ^ 0) with 1. apply Z.mod_1_r.
- unfold afact_ok, F_byte. cbn [af_lo af_hi af_al2]. rewrite (Y 66%nat) by lia. rewrite E66, lit64_small by lia. split; [lia|]. split; [| lia]. change (2 ^ 0) with 1. apply Z.mod_1_r. }
exists E2, ms. split; [reflexivity|]. split.
{ exact (st_ok_merge src0segs E2 ss_M0 (setfacts facts_M0 (junk_regs M0_JUNK 67 ss)) ms (st_ok_setfacts src0segs E2 _ ms facts_M0 HS2 HFM) MG). }
split; [exact (conj Y D2)|]. split; [exact E67|]. split; [exact HF | exact HB].
Qed.
Lemma m0_checks2 : m0_check2 ss_B_T = true /\ m0_check2 ss_B_FT = true /\ m0_check2 ss_B_FFT = true /\ m0_check2 ss_B_FFF = true /\ m0_check2 ss_O_ = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma wsubsA : wsub (ss_mem ss_SB) SKA = true /\ wsub (ss_mem ss_B_) SKA = true /\ wsub (ss_mem ss_B_F) SKA = true /\ wsub (ss_mem ss_B_FF) SKA = true /\
wsub (ss_mem ss_SO) SKo = true /\ wsub (ss_mem ss_ma0) SKo = true /\ wsub (ss_mem (add_cond ss_g4 C_mm)) SKo = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma den_nosm : 7 <= sc <= 38 -> sv_denot Eb (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 64 0) (SLit 100)) (SLit 1)) = Z_to_bv 64 nosm.
Proof.
intros Hr. destruct Eb_facts as (AG & E64 & _). destruct ctx_facts as (Bb & _). rewrite (nosm_in Hr).
apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E64, alu64_xor, alu64_sltu. rewrite (lit64_small bnc) by lia.
rewrite Z.add_0_r, (lit64_small bnc), (lit64_small 100), (lit64_small 1) by lia. unfold sltu.
destruct (bnc <? 100); rewrite lit64_small by lia; reflexivity.
Qed.
Lemma bt_diff : forall (b : bool),
branch_taken BC_LT (sv_denot Eb (SLit 9)) (sv_denot Eb (SAlu ALU_ADD (SMd M_MUL (SOff 65 0) (SLit (-1))) (SOff 66 0))) = b ->
if b then ~ seq - usq < 10 else seq - usq < 10.
Proof.
intros b H. destruct Eb_facts as (AG & E64 & E65 & E66 & _). destruct ctx_facts as (Bb & Bu & Bs & _).
rewrite branch_lt, den_lit, lit64_small in H by lia. cbn [sv_denot] in H. rewrite E65, E66, alu64_add, mul64_unsigned in H.
rewrite (lit64_small usq), (lit64_small seq) in H by lia. rewrite !Z.add_0_r, (lit64_small usq), (lit64_small seq) in H by lia.
rewrite (lit64_unsigned (-1)) in H. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) in H.
assert (EQ : s64 (add64 (mul64 usq (2 ^ 64 - 1)) seq) = seq - usq).
{ unfold add64, mul64. rewrite Zplus_mod_idemp_l.
replace (usq * (2 ^ 64 - 1) + seq) with ((seq - usq) + usq * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
unfold s64. destruct (Z_lt_le_dec (seq - usq) 0).
- rewrite <- (Z_mod_plus_full (seq - usq) 1). rewrite (Z.mod_small) by lia. replace (seq - usq + 1 * 2 ^ 64 <? 2 ^ 63) with false by (symmetry; apply Z.ltb_ge; lia). lia.
- rewrite Z.mod_small by lia. replace (seq - usq <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
rewrite EQ in H. unfold s64 in H. replace (9 <? 2 ^ 63) with true in H by reflexivity.
destruct b; [destruct (9 <? seq - usq) eqn:Z9; [apply Z.ltb_lt in Z9; lia | discriminate] | destruct (9 <? seq - usq) eqn:Z9; [discriminate | apply Z.ltb_ge in Z9; lia]].
Qed.
Lemma bt_useq : forall (b : bool), branch_taken BC_EQ (sv_denot Eb (SOff 65 0)) (sv_denot Eb (SLit 0)) = b -> if b then usq = 0 else usq <> 0.
Proof.
intros b H. destruct Eb_facts as (AG & E64 & E65 & _). destruct ctx_facts as (_ & Bu & _).
rewrite (den_off0 Eb 65 usq E65), den_lit, branch_eq, !lit64_small in H by lia.
destruct b; [apply Z.eqb_eq in H; exact H | apply Z.eqb_neq in H; exact H].
Qed.
Lemma bt_b99 : forall (b : bool), branch_taken BC_LTU (sv_denot Eb (SOff 64 0)) (sv_denot Eb (SLit 99)) = b -> if b then bnc < 99 else 99 <= bnc.
Proof.
intros b H. destruct Eb_facts as (AG & E64 & _). destruct ctx_facts as (Bb & _).
rewrite (den_off0 Eb 64 bnc E64), den_lit, branch_ltu, !lit64_small in H by lia.
destruct b; [apply Z.ltb_lt in H; exact H | apply Z.ltb_ge in H; exact H].
Qed.
Lemma bnc_of_leaf : forall ss ms v bv, 7 <= sc <= 38 -> st_ok src0segs Eb ss ms ->
nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 10%nat) (LOCK + 881) (LOCK + 882) (LOCK + 881) (LOCK + 882) [mkChunk (LOCK + 881) (CVal 1 v)]) ->
sv_denot Eb v = Z_to_bv 64 bv -> 0 <= bv < 2 ^ 64 -> bv mod 256 = znth k0 (st_bounces s2) -> BNC (ms_mem ms).
Proof.
intros ss ms v bv Hr HS Hnth Hv Hbv Hm _. destruct Eb_facts as (AG & E64 & E65 & E66 & AG' & E10 & _).
pose proof (chunk_byte0 Eb ss ms 0 0 _ _ 1 v HS Hnth eq_refl eq_refl ltac:(lia)) as Y. cbn [r_base c_off base_val] in Y.
rewrite E10, (lit64_small sc) in Y by lia. replace (LOCK + 881 + sc) with (sc + (LOCK + 881)) by lia. rewrite Y, Hv, byte_of_word0 by lia. rewrite Hm. reflexivity.
Qed.
Lemma reach_M0 : forall c, G4post L A regs sc g j1 j2 m s1 L1 mem1 md1 false c ->
(exists E' ms, c = mkCfg ms md1 /\ st_ok src0segs E' (add_cond ss_g4 C_mm) ms /\ E' = E /\ YN1d.FRM mem1 WSn (ms_mem ms)) ->
SR src0segs c M0post.
Proof.
intros c _ (E' & ms & -> & HS & -> & HF). pose proof (proj1 alloc_ceiling_val) as AC.
destruct Eb_facts as (AG & E64 & E65 & E66 & AG' & E10 & E33). destruct ctx_facts as (Bb & Bu & Bs & BK).
pose proof wsubsA as (W1' & W2 & W3 & W4 & W5 & W6 & W7). pose proof m0_checks2 as (K1 & K2 & K3 & K4 & K5).
pose proof leafA_vals as (V1 & V2 & V3 & V4 & V5).
assert (E10' : ew E 10 = Z_to_bv 64 sc) by (rewrite (agree_reg' E 10 HA) by lia; exact R10).
assert (W8 : wsub (ss_mem (add_cond ss_g4 C_mm)) SKS = true) by (vm_compute; reflexivity).
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E _ ss_ma0); [exact Mh1 | exact Mlz1 | exact HS | apply run_mm |].
intros ms0 HS0 Hfr0.
assert (HF0 : YN1d.FRM mem1 WSn (ms_mem ms0)).
{ eapply (FRM_run regs mem1 WSn E); [exact HF | exact Hfr0 | exact W8 |]. intros b lo hi x Hin Hx. unfold SKS in Hin.
destruct Hin as [H|[]]; injection H as <- <- <-. exact (win_stack E x HA Hx). }
assert (B2len : length (st_bounces s1) = 32%nat) by (pose proof (inv_ctx HI1) as (_ & _ & _ & C4 & _); exact C4).
apply (SR_sym_branch src0segs E ss_ma0 ms0 md1 _ BC_LTU (SLit 31) (SOff 10 (-7)) HS0).
-
intros Hb HSb.
assert (Hr : ~ 7 <= sc <= 38).
{ rewrite branch_ltu, den_lit, lit64_small in Hb by lia. cbn [sv_denot] in Hb. rewrite E10', (lit64_small sc), lit64_unsigned in Hb by lia.
apply Z.ltb_lt in Hb. intros Hr. rewrite Z.mod_small in Hb by lia. lia. }
destruct (nosm_out Hr) as [N0 S21].
assert (C0 : CWA WSn E (add_cond ss_ma0 C_rout) (mkCfg ms0 md1)) by (exists ms0; split; [reflexivity|]; split; [exact HSb | exact HF0]).
revert C0. apply (cwa_run WSn SKS E PS_M0 _ _ _ _ grun_rout I W8); [intros b lo hi x Hin Hx; unfold SKS in Hin; destruct Hin as [H|[]]; injection H as <- <- <-; exact (win_stack E x HA Hx) |].
intros ms1 HS1 HF1. pose proof (station_SO ms1 HS1 HF1) as HS2.
assert (C1 : CWA W0 Eb ss_SO (mkCfg ms1 md1)) by (exists ms1; split; [reflexivity|]; split; [exact HS2 | intros x Hx Hw; apply HF1; [exact Hx | intros Hw'; apply Hw; left; exact Hw']]).
revert C1. apply (cwa_run W0 SKo Eb PS_M0 _ _ _ _ grun_O_ I W5 (SKo_W0 Eb AG')).
intros ms2 HS3 HF3. apply SR_ret. apply (to_M0 ss_O_ ms2 K5 HS3); [rewrite V5, N0; apply den_lit | exact HF3 | intros Hr'; exfalso; exact (Hr Hr')].
-
intros Hb HSb.
assert (Hr : 7 <= sc <= 38).
{ rewrite branch_ltu, den_lit, lit64_small in Hb by lia. cbn [sv_denot] in Hb. rewrite E10', (lit64_small sc), lit64_unsigned in Hb by lia.
apply Z.ltb_ge in Hb. destruct (Z_lt_le_dec sc 7) as [Hl|Hl]; [| rewrite Z.mod_small in Hb by lia; lia].
exfalso. replace ((sc + -7) mod 2 ^ 64) with (sc - 7 + 2 ^ 64) in Hb by (symmetry; rewrite <- (Z_mod_plus_full (sc + -7) 1); apply Z.mod_small; lia). lia. }
destruct (BK Hr) as (Ebnc & Eusq & K32). pose proof (s2_in Hr) as S2. pose proof (den_nosm Hr) as DN.
assert (C0 : CWA WSn E (add_cond ss_ma0 C_rin) (mkCfg ms0 md1)) by (exists ms0; split; [reflexivity|]; split; [exact HSb | exact HF0]).
revert C0. apply (cwa_run WSn SKS E PS_M0 _ _ _ _ grun_rin I W8); [intros b lo hi x Hin Hx; unfold SKS in Hin; destruct Hin as [H|[]]; injection H as <- <- <-; exact (win_stack E x HA Hx) |].
intros ms1 HS1 HF1. pose proof (station_SB Hr ms1 HS1 HF1) as HS2.
assert (C1 : CWA W0 Eb ss_SB (mkCfg ms1 md1)) by (exists ms1; split; [reflexivity|]; split; [exact HS2 | intros x Hx Hw; apply HF1; [exact Hx | intros Hw'; apply Hw; left; exact Hw']]).
revert C1. pose proof (SKA_W0 Eb AG' E10 Hr) as CV.
apply (cwa_run W0 SKA Eb PS_M0 _ _ _ _ grun_B_ I W1' CV). intros ms2 HS3 HF3.
apply (SR_sym_branch src0segs Eb ss_B_ ms2 md1 _ BC_EQ (SOff 65 0) (SLit 0) HS3).
+
intros Hb1 HSb1. pose proof (bt_useq true Hb1) as U0. cbv iota in U0.
assert (C2 : CWA W0 Eb (add_cond ss_B_ (mkAC BC_EQ (SOff 65 0) (SLit 0))) (mkCfg ms2 md1)) by (exists ms2; split; [reflexivity|]; split; [exact HSb1 | exact HF3]).
revert C2. apply (cwa_run W0 SKA Eb PS_M0 _ _ _ _ grun_B_T I W2 CV). intros ms3 HS4 HF4. apply SR_ret.
assert (N1 : nth_error (ss_mem ss_B_T) 0 = Some (YP09.mkRegion (Some 10%nat) (LOCK + 881) (LOCK + 882) (LOCK + 881) (LOCK + 882) [mkChunk (LOCK + 881) (CVal 1 (SOff 64 0))])) by (vm_compute; reflexivity).
apply (to_M0 ss_B_T ms3 K1 HS4); [change (sr_get (ss_regs ss_B_T) 13) with (fst (leafA ss_B_T)); rewrite V1; exact DN | exact HF4 |].
apply (bnc_of_leaf ss_B_T ms3 (SOff 64 0) bnc Hr HS4 N1 (den_off0 _ _ _ E64) ltac:(lia)).
rewrite S2, U0. cbn [Z.eqb negb andb]. subst bnc. apply Z.mod_small. lia.
+ intros Hb1 HSb1. pose proof (bt_useq false Hb1) as U0. cbv iota in U0.
assert (C2 : CWA W0 Eb (add_cond ss_B_ (mkAC (neg_bc BC_EQ) (SOff 65 0) (SLit 0))) (mkCfg ms2 md1)) by (exists ms2; split; [reflexivity|]; split; [exact HSb1 | exact HF3]).
revert C2. apply (cwa_run W0 SKA Eb PS_M0 _ _ _ _ grun_B_F I W2 CV). intros ms3 HS4 HF4.
apply (SR_sym_branch src0segs Eb ss_B_F ms3 md1 _ BC_LT (SLit 9) (SAlu ALU_ADD (SMd M_MUL (SOff 65 0) (SLit (-1))) (SOff 66 0)) HS4).
*
intros Hb2 HSb2. pose proof (bt_diff true Hb2) as D0. cbv iota in D0.
assert (C3 : CWA W0 Eb (add_cond ss_B_F (mkAC BC_LT (SLit 9) (SAlu ALU_ADD (SMd M_MUL (SOff 65 0) (SLit (-1))) (SOff 66 0)))) (mkCfg ms3 md1)) by (exists ms3; split; [reflexivity|]; split; [exact HSb2 | exact HF4]).
revert C3. apply (cwa_run W0 SKA Eb PS_M0 _ _ _ _ grun_B_FT I W3 CV). intros ms4 HS5 HF5. apply SR_ret.
assert (N1 : nth_error (ss_mem ss_B_FT) 0 = Some (YP09.mkRegion (Some 10%nat) (LOCK + 881) (LOCK + 882) (LOCK + 881) (LOCK + 882) [mkChunk (LOCK + 881) (CVal 1 (SOff 64 0))])) by (vm_compute; reflexivity).
apply (to_M0 ss_B_FT ms4 K2 HS5); [change (sr_get (ss_regs ss_B_FT) 13) with (fst (leafA ss_B_FT)); rewrite V2; exact DN | exact HF5 |].
apply (bnc_of_leaf ss_B_FT ms4 (SOff 64 0) bnc Hr HS5 N1 (den_off0 _ _ _ E64) ltac:(lia)).
rewrite S2. replace (seq - usq <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. subst bnc. apply Z.mod_small. lia.
* intros Hb2 HSb2. pose proof (bt_diff false Hb2) as D0. cbv iota in D0.
assert (C3 : CWA W0 Eb (add_cond ss_B_F (mkAC (neg_bc BC_LT) (SLit 9) (SAlu ALU_ADD (SMd M_MUL (SOff 65 0) (SLit (-1))) (SOff 66 0)))) (mkCfg ms3 md1)) by (exists ms3; split; [reflexivity|]; split; [exact HSb2 | exact HF4]).
revert C3. apply (cwa_run W0 SKA Eb PS_M0 _ _ _ _ grun_B_FF I W3 CV). intros ms4 HS5 HF5.
assert (CND : negb (usq =? 0) && (seq - usq <? 10) = true) by (apply andb_true_intro; split; [apply negb_true_iff; apply Z.eqb_neq; exact U0 | apply Z.ltb_lt; exact D0]).
apply (SR_sym_branch src0segs Eb ss_B_FF ms4 md1 _ BC_LTU (SOff 64 0) (SLit 99) HS5).
--
intros Hb3 HSb3. pose proof (bt_b99 true Hb3) as G0. cbv iota in G0.
assert (C4 : CWA W0 Eb (add_cond ss_B_FF (mkAC BC_LTU (SOff 64 0) (SLit 99))) (mkCfg ms4 md1)) by (exists ms4; split; [reflexivity|]; split; [exact HSb3 | exact HF5]).
revert C4. apply (cwa_run W0 SKA Eb PS_M0 _ _ _ _ grun_B_FFT I W4 CV). intros ms5 HS6 HF6. apply SR_ret.
assert (N1 : nth_error (ss_mem ss_B_FFT) 0 = Some (YP09.mkRegion (Some 10%nat) (LOCK + 881) (LOCK + 882) (LOCK + 881) (LOCK + 882) [mkChunk (LOCK + 881) (CVal 1 (SOff 64 1))])) by (vm_compute; reflexivity).
apply (to_M0 ss_B_FFT ms5 K3 HS6); [change (sr_get (ss_regs ss_B_FFT) 13) with (fst (leafA ss_B_FFT)); rewrite V3; exact DN | exact HF6 |].
assert (D641 : sv_denot Eb (SOff 64 1) = Z_to_bv 64 (bnc + 1)) by (cbn [sv_denot]; rewrite E64, lit64_small by lia; reflexivity).
apply (bnc_of_leaf ss_B_FFT ms5 (SOff 64 1) (bnc + 1) Hr HS6 N1 D641 ltac:(lia)).
rewrite S2, CND. cbn [st_bounces set_bounces]. rewrite znth_zset, Z.eqb_refl, B2len by lia.
replace (k0 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb]. replace (bnc + 1 <? 100) with true by (symmetry; apply Z.ltb_lt; lia). apply Z.mod_small. lia.
-- intros Hb3 HSb3. pose proof (bt_b99 false Hb3) as G0. cbv iota in G0.
assert (C4 : CWA W0 Eb (add_cond ss_B_FF (mkAC (neg_bc BC_LTU) (SOff 64 0) (SLit 99))) (mkCfg ms4 md1)) by (exists ms4; split; [reflexivity|]; split; [exact HSb3 | exact HF5]).
revert C4. apply (cwa_run W0 SKA Eb PS_M0 _ _ _ _ grun_B_FFF I W4 CV). intros ms5 HS6 HF6. apply SR_ret.
assert (N1 : nth_error (ss_mem ss_B_FFF) 0 = Some (YP09.mkRegion (Some 10%nat) (LOCK + 881) (LOCK + 882) (LOCK + 881) (LOCK + 882) [mkChunk (LOCK + 881) (CVal 1 (SLit 150))])) by (vm_compute; reflexivity).
apply (to_M0 ss_B_FFF ms5 K4 HS6); [change (sr_get (ss_regs ss_B_FFF) 13) with (fst (leafA ss_B_FFF)); rewrite V4; exact DN | exact HF6 |].
apply (bnc_of_leaf ss_B_FFF ms5 (SLit 150) 150 Hr HS6 N1 (den_lit _ _) ltac:(lia)).
rewrite S2, CND. cbn [st_bounces set_bounces]. rewrite znth_zset, Z.eqb_refl, B2len by lia.
replace (k0 <? Z.of_nat 32) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb]. replace (bnc + 1 <? 100) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Definition FRc (mm : word -> option byte) : Prop :=
forall x, 0 <= x < 2 ^ 64 -> ~ WSn x -> ~ (CTX <= x < CTX + CTX_SIZE) -> mm (Z_to_bv 64 x) = mem1 (Z_to_bv 64 x).
Definition M1post (c : config) : Prop :=
exists E3 ms, c = mkCfg ms md1 /\ st_ok src0segs E3 ss_M1 ms /\ env_agree 67 Eb E3 /\ ew E3 67 = Z_to_bv 64 nosm /\
midrep B L1 s3 (ms_mem ms) md1 /\ FRc (ms_mem ms).
Lemma s2_shape : exists b, s2 = set_bounces b s1 /\ length b = 32%nat /\ (forall u, In u b -> 0 <= u <= 255) /\
(forall k, (7 <= sc <= 38 -> k <> Z.to_nat k0) -> nth k b 0 = nth k (st_bounces s1) 0).
Proof.
pose proof (inv_ctx HI1) as (_ & _ & _ & C4 & _ & _ & C7 & _). destruct ctx_facts as (Bb & Bu & Bs & BK).
destruct (Z_le_dec 7 sc) as [H7|H7]; [destruct (Z_le_dec sc 38) as [H38|H38]|].
- rewrite (s2_in ltac:(lia)). destruct (negb (usq =? 0) && (seq - usq <? 10)).
+ eexists. split; [reflexivity|]. split; [unfold zset; rewrite length_zupd; exact C4|]. split.
* intros u Hu. unfold zset in Hu. apply In_zupd_inv in Hu as [->|Hu]; [| exact (C7 u Hu)]. destruct (bnc + 1 <? 100) eqn:Y; [apply Z.ltb_lt in Y; lia | lia].
* intros k Hk. unfold zset. rewrite nth_zupd. replace (Nat.eqb k (Z.to_nat k0)) with false by (symmetry; apply Nat.eqb_neq; apply Hk; lia). reflexivity.
+ exists (st_bounces s1). split; [destruct s1; reflexivity|]. split; [exact C4|]. split; [exact C7 | intros; reflexivity].
- exists (st_bounces s1). destruct (nosm_out ltac:(lia)) as [_ ->]. split; [destruct s1; reflexivity|]. split; [exact C4|]. split; [exact C7 | intros; reflexivity].
- exists (st_bounces s1). destruct (nosm_out ltac:(lia)) as [_ ->]. split; [destruct s1; reflexivity|]. split; [exact C4|]. split; [exact C7 | intros; reflexivity].
Qed.
Lemma s3_shape : s3 = set_seq (if seq =? 255 then 1 else seq + 1) (set_unmap_seq (if seq =? 255 then repeat 0 32%nat else st_unmap_seq s1) s2).
Proof.
subst s3 seq. unfold seq_st. replace (st_seq s2) with (st_seq s1) by (symmetry; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (ab_st_fields sc s1))))))))).
replace (st_unmap_seq s1) with (st_unmap_seq s2) by (exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (ab_st_fields sc s1)))))))))).
destruct (st_seq s1 =? 255); [reflexivity | destruct s2; reflexivity].
Qed.
Lemma cells_s3 : forall (W : Z -> Prop) mm,
(forall x, W x -> WSn x \/ (7 <= sc <= 38 /\ x = LOCK + 881 + sc) \/ x = LOCK + 920 \/ (seq = 255 /\ LOCK + 856 <= x < LOCK + 888)) ->
BNC mm ->
mbyte src0segs mm (LOCK + 920) = Some (Z_to_bv 8 (st_seq s3)) ->
(seq = 255 -> forall i, 0 <= i < 32 -> mbyte src0segs mm (LOCK + 856 + i) = Some (Z_to_bv 8 0)) ->
forall c, In c (ctx_cells s3) -> (In c (ctx_cells s1) /\ forall k, (k < mc_w c)%nat -> ~ W (CTX + ctx_off c + Z.of_nat k)) \/ cell_mem B L1 mm c.
Proof.
intros W mm HW HB HSQ HUQ c Hc. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (_ & _ & P3 & _).
pose proof (so_ctx_hi _ (mid_syms _ _ _ _ _ MID1)) as CH. change (ms_ctx B) with CTX in CH.
pose proof (mid_ctx _ _ _ _ _ MID1) as LC. change (ms_ctx B) with CTX in LC.
destruct s2_shape as (b & Es2 & Lb & Rb & Ob). pose proof s3_shape as Es3. rewrite Es2 in Es3.
set (q := if seq =? 255 then 1 else seq + 1) in Es3. set (u := if seq =? 255 then repeat 0 32%nat else st_unmap_seq s1) in Es3.
assert (NWo : forall off k, 0 <= off -> 0 <= k -> (off + k < 848 \/ 920 <= off) -> off + k < CTX_SIZE -> ~ W (CTX + off + k)).
{ intros off k Ho Hk0 Hr Hhi HWx. destruct (HW _ HWx) as [Hw|[[Hsc1 Hx]|[Hx|[Hs Hx]]]]; unfold WS, CTX_SIZE in *; lits; lia. }
destruct ctx_facts as (_ & _ & Bs & _).
rewrite Es3 in Hc. destruct (YN2c.In_ctx_cells_cases 0 _ c Hc) as [H13 | [(k & Hk & ->) | [(k & Hk & ->) | [(k & Hk & ->) | (k & Hk & ->)]]]];
cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta st_avail_meta_count st_avail_meta_area_count st_meta_alloc_shift
st_area_head st_area_tail st_avail_meta_areas st_seq st_brk st_active st_usage st_unmap_seq st_bounces set_seq set_unmap_seq set_bounces] in *.
-
cbn [In] in H13.
destruct H13 as [E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[E1|[]]]]]]]]]]]]]]; rewrite <- E1;
first [ solve [ left; split; [ unfold ctx_cells; apply in_app_iff; left; inlist
| unfold ctx_off; cbn [mc_loc mc_w]; intros k Hk1; apply NWo;
unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count, CTX_avail_meta_area_count,
CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas, CTX_seq, CTX_brk, CTX_SIZE; lia ] ]
| right ].
unfold cell_mem. cbn [mc_loc mc_w mc_val loc_addr sval_num]. rewrite LC. change (ms_segs B) with src0segs. intros k Hk1. destruct k; [| lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
replace (CTX + CTX_seq) with (LOCK + 920) by (unfold CTX_seq; lits; lia). rewrite Es3 in HSQ. cbn [st_seq set_seq] in HSQ. rewrite HSQ. f_equal. f_equal.
symmetry. apply le_byte_1. subst q. destruct (seq =? 255) eqn:Yq; [| apply Z.eqb_neq in Yq]; lia.
-   left. split; [unfold ctx_cells; rewrite !in_app_iff; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
unfold ctx_off. cbn [mc_loc mc_w]. intros j Hj. apply NWo; unfold CTX_active, CTX_SIZE; lia.
-   left. split; [unfold ctx_cells; rewrite !in_app_iff; right; right; left; apply in_map_iff; exists k; split; [reflexivity | apply in_seq; lia]|].
unfold ctx_off. cbn [mc_loc mc_w]. intros j Hj. apply NWo; unfold CTX_usage, CTX_SIZE; lia.
-
destruct (Z.eq_dec seq 255) as [Hs|Hs].
+ right. unfold cell_mem. cbn [mc_loc mc_w mc_val loc_addr sval_num]. rewrite LC. change (ms_segs B) with src0segs. intros j Hj. destruct j; [| lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
replace (CTX + (CTX_unmap_seq + Z.of_nat k)) with (LOCK + 856 + Z.of_nat k) by (unfold CTX_unmap_seq; lits; lia).
rewrite (HUQ Hs) by lia. subst u. replace (seq =? 255) with true by (symmetry; apply Z.eqb_eq; exact Hs).
rewrite nth_repeat. reflexivity.
+ left. subst u. replace (seq =? 255) with false by (symmetry; apply Z.eqb_neq; exact Hs).
split; [exact (In_useq_cell s1 k Hk)|]. unfold ctx_off. cbn [mc_loc mc_w]. intros j Hj HWx.
destruct (HW _ HWx) as [Hw|[[Hsc1 Hx]|[Hx|[Hs1 Hx]]]]; unfold WS, CTX_unmap_seq in *; lits; lia.
-
destruct (decide (7 <= sc <= 38 /\ k = Z.to_nat k0)) as [[Hr ->]|Hno].
+ right. unfold cell_mem. cbn [mc_loc mc_w mc_val loc_addr sval_num]. rewrite LC. change (ms_segs B) with src0segs. intros j Hj. destruct j; [| lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
replace (CTX + (CTX_bounces + Z.of_nat (Z.to_nat k0))) with (LOCK + 881 + sc) by (assert (Ek0 : k0 = sc - 7) by reflexivity; unfold CTX_bounces; rewrite Ek0; lits; lia).
rewrite (HB Hr). rewrite Es2. cbn [st_bounces set_bounces]. unfold znth. f_equal. f_equal. symmetry. apply le_byte_1.
destruct ctx_facts as (_ & _ & _ & BK). destruct (BK Hr) as (_ & _ & K32).
pose proof (Rb _ (@nth_In Z (Z.to_nat k0) b 0 ltac:(rewrite Lb; exact K32))) as Rk. lia.
+ left. rewrite (Ob k) by (intros Hr He; apply Hno; split; [exact Hr | exact He]).
split; [exact (In_bounces_cell s1 k Hk)|]. unfold ctx_off. cbn [mc_loc mc_w]. intros j Hj HWx.
destruct (HW _ HWx) as [Hw|[[Hsc1 Hx]|[Hx|[Hs1 Hx]]]]; unfold WS, CTX_bounces in *; lits; lia.
Qed.
Lemma BNC_keep : forall E' rs sk mm mm', BNC mm -> frame_of E' rs mm mm' -> wsub rs sk = true ->
(forall b lo hi, In (b, lo, hi) sk -> 7 <= sc <= 38 -> ~ base_val E' b + lo <= LOCK + 881 + sc < base_val E' b + hi) -> BNC mm'.
Proof.
intros E' rs sk mm mm' HB Hfr Hs Hsk Hr. rewrite <- (HB Hr). apply mbyte_ext1. apply (frame_of_at E' rs mm mm' _ Hfr); [lits; lia|].
intros Hw. destruct (in_wrange_wsub regs E' rs sk _ Hs Hw) as (b & lo & hi & Hin & Hx). exact (Hsk b lo hi Hin Hr Hx).
Qed.
Lemma wsubsM : wsub (ss_mem ss_M0) SKo = true /\ wsub (ss_mem (add_cond ss_m0a C_sne)) SKo = true /\ wsub (ss_mem (add_cond ss_m0a C_s255)) SKo = true /\
wsub (ss_mem ss_SU) SKB = true /\ m1_check ss_mA = true /\ m1_check ss_mB = true /\
nth_error (ss_mem ss_mA) 0 = Some (YP09.mkRegion None (LOCK + 920) (LOCK + 921) (LOCK + 920) (LOCK + 921) [mkChunk (LOCK + 920) (CVal 1 (SOff 66 1))]) /\
nth_error (ss_mem ss_mB) 1 = Some (YP09.mkRegion None (LOCK + 920) (LOCK + 921) (LOCK + 920) (LOCK + 921) [mkChunk (LOCK + 920) (CVal 1 (SLit 1))]) /\
nth_error (ss_mem ss_mB) 0 = Some (YP09.mkRegion None (LOCK + 856) (LOCK + 888) (LOCK + 856) (LOCK + 888)
[mkChunk (LOCK + 880) (CVal 8 (SLit 0)); mkChunk (LOCK + 872) (CVal 8 (SLit 0)); mkChunk (LOCK + 864) (CVal 8 (SLit 0)); mkChunk (LOCK + 856) (CVal 8 (SLit 0))]) /\
ss_mem ss_mB0 = ss_mem ss_M0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma sk_M0 : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_M0) =
[(None, LOCK + 920, LOCK + 921); (Some 33%nat, 472, 480); (Some 2%nat, -ASF, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56)].
Proof. vm_compute. reflexivity. Qed.
Lemma to_M1 : forall (W : Z -> Prop) E2 ss ms, m1_check ss = true -> st_ok src0segs E2 ss ms -> env_agree 67 Eb E2 -> ew E2 67 = Z_to_bv 64 nosm ->
facts_ok E2 facts_M0 -> (forall x, W x \/ ~ W x) ->
(forall x, W x -> WSn x \/ (7 <= sc <= 38 /\ x = LOCK + 881 + sc) \/ x = LOCK + 920 \/ (seq = 255 /\ LOCK + 856 <= x < LOCK + 888)) ->
FRW W (ms_mem ms) -> BNC (ms_mem ms) ->
mbyte src0segs (ms_mem ms) (LOCK + 920) = Some (Z_to_bv 8 (st_seq s3)) ->
(seq = 255 -> forall i, 0 <= i < 32 -> mbyte src0segs (ms_mem ms) (LOCK + 856 + i) = Some (Z_to_bv 8 0)) ->
M1post (mkCfg ms md1).
Proof.
intros W E2 ss ms CK HS AG2 E67 HFM Wdec HW HF HB HSQ HUQ. pose proof nosm_range as NR. pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (_ & _ & P3 & _).
unfold m1_check in CK. apply andb_prop in CK as [AT MG].
assert (NZ : forallb (fun r : reg => negb (bv_eqb r 0)) M1_JUNK = true) by (vm_compute; reflexivity).
destruct (junk_regs_ok src0segs M1_JUNK 72 E2 ss ms HS AT NZ) as (E3 & [Y D3] & HS3).
assert (AG3 : env_agree 72 E2 E3) by (split; [exact Y | exact D3]).
assert (HFM3 : facts_ok E3 facts_M0).
{ eapply (facts_ok_agree 72 E2 E3); [exact AG3 | vm_compute; reflexivity | exact HFM]. }
exists E3, ms. split; [reflexivity|]. split.
{ exact (st_ok_merge src0segs E3 ss_M1 (setfacts facts_M0 (junk_regs M1_JUNK 72 ss)) ms (st_ok_setfacts src0segs E3 _ ms facts_M0 HS3 HFM3) MG). }
split; [eapply env_agree_trans; [exact AG2 | eapply env_agree_le; [| exact AG3]; lia]|].
split; [rewrite (Y 67%nat) by lia; exact E67|]. split.
- destruct s2_shape as (b & Es2 & _). pose proof s3_shape as Es3. rewrite Es2 in Es3.
apply (midrep_ctx (m :: X) L1 s1 s3 mem1 (ms_mem ms) md1 W HI1 XC1 AMA1 MID1);
[rewrite Es3; reflexivity | rewrite Es3; reflexivity | rewrite Es3; reflexivity | rewrite Es3; reflexivity | | | exact HF | exact (cells_s3 W (ms_mem ms) HW HB HSQ HUQ)].
+ exact Wdec.
+ intros x Hx. destruct (HW x Hx) as [Hw|[[_ ->]|[->|[_ Hx']]]]; [left; exact Hw | right | right | right]; unfold CTX_SIZE; lits; lia.
- intros x Hx Hnw Hnc. apply HF; [exact Hx|]. intros HWx. destruct (HW x HWx) as [Hw|[[_ ->]|[->|[_ Hx']]]]; [exact (Hnw Hw) | | |]; apply Hnc; unfold CTX_SIZE; lits; lia.
Qed.
Lemma reach_M1 : forall c, M0post c -> SR src0segs c M1post.
Proof.
intros c (E2 & ms & -> & HS & AG2 & E67 & HF & HB). pose proof (proj1 alloc_ceiling_val) as AC. destruct pre_facts' as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
destruct Eb_facts as (AG & E64 & E65 & E66 & AG' & E10 & E33). destruct ctx_facts as (Bb & Bu & Bs & BK). destruct cs_facts' as (C33 & C33m & _).
pose proof wsubsM as (W1' & W2 & W3 & W4 & K1 & K2 & NA & NB1 & NB0 & EM0).
destruct AG2 as [Y D2].
assert (AG2' : env_agree 40 E00 E2) by (eapply env_agree_trans; [exact AG' | split; [intros k Hk; apply Y; lia | exact D2]]).
assert (E66' : ew E2 66 = Z_to_bv 64 seq) by (rewrite (Y 66%nat) by lia; exact E66).
assert (HFM : facts_ok E2 facts_M0) by (destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & H9); exact H9).
assert (SKo_bnc : forall E', env_agree 40 E00 E' -> forall b lo hi, In (b, lo, hi) SKo -> 7 <= sc <= 38 -> ~ base_val E' b + lo <= LOCK + 881 + sc < base_val E' b + hi).
{ intros E' HA' b lo hi Hin Hr Hx. unfold SKo in Hin. destruct Hin as [H|[H|[]]]; injection H as <- <- <-.
- pose proof (win_stack E' _ HA' Hx) as Hw. unfold WS in Hw. lits. lia.
- cbn [base_val] in Hx. lia. }
assert (SKB_bnc : forall E', env_agree 40 E00 E' -> forall b lo hi, In (b, lo, hi) SKB -> 7 <= sc <= 38 -> ~ base_val E' b + lo <= LOCK + 881 + sc < base_val E' b + hi).
{ intros E' HA' b lo hi Hin Hr Hx. unfold SKB in Hin. destruct Hin as [H|[H|[H|[]]]]; injection H as <- <- <-.
- cbn [base_val] in Hx. lia.
- pose proof (win_stack E' _ HA' Hx) as Hw. unfold WS in Hw. lits. lia.
- cbn [base_val] in Hx. lia. }
assert (W0dec : forall x, W0 x \/ ~ W0 x) by (intros x; unfold W0, WS; lia).
assert (W1dec : forall x, W1 x \/ ~ W1 x) by (intros x; unfold W1, W0, WS; lia).
assert (W0sub : forall x, W0 x -> WSn x \/ (7 <= sc <= 38 /\ x = LOCK + 881 + sc) \/ x = LOCK + 920 \/ (seq = 255 /\ LOCK + 856 <= x < LOCK + 888)) by (intros x Hx; unfold W0 in Hx; tauto).
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL PS_M1 E2 ss_M0 ss_m0a); [exact Mh1 | exact Mlz1 | exact HS | apply grun_M0 |].
intros ms0 HS0 Hfr0.
pose proof (FRM_run regs mem1 W0 E2 _ _ _ _ HF Hfr0 W1' (SKo_W0 E2 AG2')) as HF0.
pose proof (BNC_keep E2 _ _ _ _ HB Hfr0 W1' (SKo_bnc E2 AG2')) as HB0.
apply (SR_sym_branch src0segs E2 ss_m0a ms0 md1 _ BC_NE (SOff 66 0) (SLit 255) HS0).
-
intros Hb HSb.
assert (Hs : seq <> 255).
{ rewrite (den_off0 E2 66 seq E66'), den_lit, branch_ne, !lit64_small in Hb by lia. intros Hs. rewrite Hs, Z.eqb_refl in Hb. discriminate. }
change (add_cond ss_m0a (mkAC BC_NE (SOff 66 0) (SLit 255))) with (add_cond ss_m0a C_sne) in HSb.
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL PS_M1 E2 _ ss_mA); [exact Mh1 | exact Mlz1 | exact HSb | apply grun_mA |].
intros msA HSA HfrA.
pose proof (FRM_run regs mem1 W0 E2 _ _ _ _ HF0 HfrA W2 (SKo_W0 E2 AG2')) as HFA.
pose proof (BNC_keep E2 _ _ _ _ HB0 HfrA W2 (SKo_bnc E2 AG2')) as HBA.
apply SR_ret. apply (to_M1 W0 E2 ss_mA msA K1 HSA (conj Y D2) E67 HFM W0dec W0sub HFA HBA).
+ pose proof (chunk_byte0 E2 ss_mA msA 0 0 _ _ 1 (SOff 66 1) HSA NA eq_refl eq_refl ltac:(lia)) as Q. cbn [r_base c_off base_val] in Q. rewrite Z.add_0_l in Q.
rewrite Q. cbn [sv_denot]. rewrite E66', (lit64_small seq), byte_of_word0 by lia. f_equal. f_equal.
rewrite s3_shape. cbn [st_seq set_seq]. replace (seq =? 255) with false by (symmetry; apply Z.eqb_neq; exact Hs). apply Z.mod_small. lia.
+ intros Hs'. exfalso. exact (Hs Hs').
-
intros Hb HSb.
assert (Hs : seq = 255).
{ rewrite (den_off0 E2 66 seq E66'), den_lit, branch_ne, !lit64_small in Hb by lia. destruct (seq =? 255) eqn:Q; [apply Z.eqb_eq in Q; exact Q | discriminate]. }
change (add_cond ss_m0a (mkAC (neg_bc BC_NE) (SOff 66 0) (SLit 255))) with (add_cond ss_m0a C_s255) in HSb.
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL PS_M1 E2 _ ss_mB0); [exact Mh1 | exact Mlz1 | exact HSb | apply grun_mB0 |].
intros msB0 HSB0 HfrB0.
pose proof (FRM_run regs mem1 W0 E2 _ _ _ _ HF0 HfrB0 W3 (SKo_W0 E2 AG2')) as HFB0.
pose proof (BNC_keep E2 _ _ _ _ HB0 HfrB0 W3 (SKo_bnc E2 AG2')) as HBB0.
assert (HSU : st_ok src0segs E2 ss_SU msB0).
{ apply (st_ok_add_region src0segs E2 _ msB0 R_ublk HSB0); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_ublk]; [lits; lia | lits; lia | | apply Forall_nil].
intros o Ho. rewrite Z.add_0_l. apply (ctxw L1 s1 mem1 md1 MID1). lits. lia.
- rewrite EM0. apply Forall_forall. intros r Hr'. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite sk_M0 in Hr'.
assert (B33 : bv_unsigned (ew E2 33) = csn 33) by (rewrite (agree_cs' E2 33 AG2') by lia; apply lit64_small; lits; lia).
assert (B2 : bv_unsigned (ew E2 2) = sp) by (rewrite (agree_reg' E2 2 AG2') by lia; reflexivity).
unfold extent_disjoint. cbn [r_base r_lo r_hi R_ublk]. solve_disj Hr'; rewrite ?B33, ?B2; cbn [base_val]; lits; lia. }
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL PS_M1 E2 ss_SU ss_mB); [exact Mh1 | exact Mlz1 | exact HSU | apply grun_mB |].
intros msB HSB HfrB.
assert (HFB : FRW W1 (ms_mem msB)).
{ eapply (FRM_run regs mem1 W1 E2); [intros x Hx Hnn; apply HFB0; [exact Hx | intros Hw; apply Hnn; left; exact Hw] | exact HfrB | exact W4 | exact (SKB_W1 E2 AG2')]. }
pose proof (BNC_keep E2 _ _ _ _ HBB0 HfrB W4 (SKB_bnc E2 AG2')) as HBB.
apply SR_ret. apply (to_M1 W1 E2 ss_mB msB K2 HSB (conj Y D2) E67 HFM W1dec).
+ intros x Hx. unfold W1 in Hx. destruct Hx as [Hx|Hx]; [exact (W0sub x Hx) | right; right; right; split; [exact Hs | exact Hx]].
+ exact HFB.
+ exact HBB.
+ pose proof (chunk_byte0 E2 ss_mB msB 1 0 _ _ 1 (SLit 1) HSB NB1 eq_refl eq_refl ltac:(lia)) as Q. cbn [r_base c_off base_val] in Q. rewrite Z.add_0_l in Q.
rewrite Q. rewrite den_lit, byte_of_word0 by lia. f_equal. f_equal.
rewrite s3_shape. cbn [st_seq set_seq]. replace (seq =? 255) with true by (symmetry; apply Z.eqb_eq; exact Hs). reflexivity.
+ intros _ i Hi.
assert (Q : forall j k, (j < 4)%nat -> 0 <= k < 8 -> mbyte src0segs (ms_mem msB) (LOCK + 880 - 8 * Z.of_nat j + k) = Some (Z_to_bv 8 0)).
{ intros j k Hj Hk.
destruct j as [|[|[|[|j]]]]; [| | | | lia];
[ pose proof (chunk_bytek E2 ss_mB msB 0 0 _ _ 8 (SLit 0) k HSB NB0 eq_refl eq_refl ltac:(lia)) as Q
| pose proof (chunk_bytek E2 ss_mB msB 0 1 _ _ 8 (SLit 0) k HSB NB0 eq_refl eq_refl ltac:(lia)) as Q
| pose proof (chunk_bytek E2 ss_mB msB 0 2 _ _ 8 (SLit 0) k HSB NB0 eq_refl eq_refl ltac:(lia)) as Q
| pose proof (chunk_bytek E2 ss_mB msB 0 3 _ _ 8 (SLit 0) k HSB NB0 eq_refl eq_refl ltac:(lia)) as Q ];
cbn [r_base c_off base_val Z.of_nat] in Q; rewrite den_lit, byte_of_word_zero in Q; rewrite <- Q; f_equal; lia. }
replace (LOCK + 856 + i) with (LOCK + 880 - 8 * Z.of_nat (Z.to_nat (3 - i / 8)) + (i mod 8)).
2:{ rewrite Z2Nat.id by (pose proof (Z.div_pos i 8); pose proof (Z.div_lt_upper_bound i 8 4); lia). pose proof (Z_div_mod_eq_full i 8). lia. }
apply Q; [| apply Z.mod_pos_bound; lia]. pose proof (Z.div_pos i 8 ltac:(lia) ltac:(lia)). assert (i / 8 < 4) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
End MA.
End f.
End e.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
