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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02 YN3b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0h YO0w YO0s YO0x YO0z YO10 YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0c YO0b YN01 YN03 YN02
YN2b YN2e YN0g YN0d YN0c
YN2j YN2h YN2n YN2i YN2k YN2m YN2l
YN0j YN0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM01.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation B := src0_msyms.
Ltac inlist := cbn; repeat (first [left; reflexivity | right]).
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma brkst_cases : forall b : brkst, b = BrkNever \/ b = BrkDead \/ exists r p, b = BrkCur r p.
Proof. intros [| |r p]; [left | right; left | right; right; exists r, p]; reflexivity. Qed.
Lemma fixed_models_shape : forall a n m, m_vm_lazy m = [] -> m_vm_materialized m = [] ->
(mmap_fixed_model a n m = with_vmmaps (m_vmmaps (mmap_fixed_model a n m)) m /\
(m_halted (mmap_fixed_model a n m) = m_halted m /\ m_vm_lazy (mmap_fixed_model a n m) = [] /\ m_vm_materialized (mmap_fixed_model a n m) = [])) /\
(mmap_fixed_destroyed_model a n m = with_vmmaps (m_vmmaps (mmap_fixed_destroyed_model a n m)) m /\
(m_halted (mmap_fixed_destroyed_model a n m) = m_halted m /\ m_vm_lazy (mmap_fixed_destroyed_model a n m) = [] /\ m_vm_materialized (mmap_fixed_destroyed_model a n m) = [])).
Proof.
intros a n m Hl Hm. destruct m as [fd [vm lazy mat] io fs proc lim tm sg sc]. cbn in Hl, Hm. subst.
repeat split; reflexivity.
Qed.
Lemma B_segs : ms_segs B = src0segs. Proof. reflexivity. Qed.
Lemma B_ctx : ms_ctx B = CTX. Proof. reflexivity. Qed.
Lemma B_errno : errno_addr B = ERRNO. Proof. reflexivity. Qed.
Lemma B_tp : ms_tp B = TP. Proof. reflexivity. Qed.
Lemma B_am : pc_alloc_meta (ms_pcs B) = src0_A_alloc_meta. Proof. reflexivity. Qed.
Lemma AMS_eq : AM_STACK = AMS. Proof. reflexivity. Qed.
Lemma src0_img_range : forall a, in_img B a -> 0x10000 <= a < 0x51000.
Proof. intros a Ha. apply in_img_img1 in Ha. unfold in_img1 in Ha. lia. Qed.
Lemma src0_rwseg_img : forall x, 0x1e000 <= x < 0x51000 -> in_img B x.
Proof. intros x Hx. apply in_img1_img. unfold in_img1. lia. Qed.
Lemma src0_ENC : forall x, errno_addr B <= x < errno_addr B + 4 -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE).
Proof. intros x. rewrite B_errno, B_ctx. unfold ERRNO, CTX, CTX_SIZE, src0_tp, src0_D_malloc_context. lia. Qed.
Lemma src0_ENS : forall x, errno_addr B <= x < errno_addr B + 4 -> ~ static_owned B x.
Proof.
intros x. rewrite B_errno. unfold static_owned. cbn. unfold ERRNO, src0_tp, src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard,
src0_D_stack_chk_guard, src0_D_debruijn32, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab. lia.
Qed.
Lemma src0_ERRIMG : forall x, errno_addr B <= x < errno_addr B + 4 -> in_img B x.
Proof. intros x. rewrite B_errno. unfold ERRNO, src0_tp. intros Hx. apply src0_rwseg_img. lia. Qed.
Lemma src0_SNC : forall x, static_owned B x -> ~ (ms_ctx B <= x < ms_ctx B + CTX_SIZE).
Proof.
intros x. rewrite B_ctx. unfold static_owned. cbn. unfold CTX, CTX_SIZE, src0_D_malloc_context, src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard,
src0_D_stack_chk_guard, src0_D_debruijn32, src0_D_size_classes, src0_D_small_cnt_tab, src0_D_med_cnt_tab. lia.
Qed.
Lemma hd_error_In {T} : forall (l : list T) x, hd_error l = Some x -> In x l.
Proof. intros [|y l] x H; cbn in H; [discriminate | injection H as ->; left; reflexivity]. Qed.
Lemma fetch_ret : fetch_word src0segs (Z_to_bv 64 PC_RET) = Some (0x00008067%bv : bv 32).
Proof. rewrite <- (Z_to_bv_bv_unsigned 32 (0x00008067%bv : bv 32)). apply src0tbl_ok. vm_compute. reflexivity. Qed.
Lemma decode_ret : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma SR_final_ret : forall E ss ms mdl Q,
st_ok src0segs E ss ms -> ss_resv ss = None -> ss_pc ss = PC_RET ->
sr_get (ss_regs ss) 1 = SOff 1 0 -> YK0s.ret_ok (ew E 1) ->
m_halted mdl = None -> m_vm_lazy mdl = [] ->
Q (mkCfg (mkst (ms_regs ms) (ew E 1) (ms_mem ms) (seg_rom src0segs)) mdl) ->
SR src0segs (mkCfg ms mdl) Q.
Proof.
intros E ss ms mdl Q HS Hrv Hpc Hra Hret Hh Hlz HQ.
pose proof (st_ok_reg src0segs E ss ms 1 HS) as R1. rewrite Hra in R1. cbn [sv_denot] in R1.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned in R1.
rewrite (st_ok_mkst src0segs E ss ms HS Hrv). rewrite Hpc.
eapply SR_step; [exact Hh | exact Hlz | reflexivity | |].
- eapply step_jalr_x0; [apply fetch_ret | reflexivity | apply decode_ret | exact R1].
- cbn [ms_regs ms_mem mkst]. change (bv_signed (0%bv : bv 12)) with 0. unfold YK0s.ret_ok in Hret. rewrite Hret.
apply SR_ret. exact HQ.
Qed.
Section AM.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z).
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Hypothesis HI : Inv X R U A.
Hypothesis XC : Xclean X A.
Hypothesis AMA : ama_ok A.
Hypothesis BND : bounded A.
Hypothesis MID : midrep B L A mem md.
Hypothesis PRE : callee_pre B regs mem AM_STACK.
Variables (g av ar : Z).
Hypothesis Hg : word_mem src0segs mem GUARD g.
Hypothesis AUXV : st_init_done A = false ->
word_mem src0segs mem (LIBC + 8) av /\
(forall k, (k < 10)%nat -> word_mem src0segs mem (av + 16 * Z.of_nat k) (nth k AUXV_TYPES 0)) /\
word_mem src0segs mem (av + 16 * 8 + 8) ar /\
word_mem src0segs mem (ar + 8) (ly_sec L) /\
4096 <= av /\ av + 160 <= 2 ^ 63 /\ 4096 <= ar /\ ar + 16 <= 2 ^ 63 /\
bv_unsigned (getr regs 2) <= av /\ bv_unsigned (getr regs 2) <= ar.
Let sp : Z := bv_unsigned (getr regs 2).
Let A0 : astate := set_init_done true A.
Definition lnkv (f : option mslot -> sval) : Z :=
match st_free_meta_head A with Some m => sval_num L (f (MT A m)) | None => 0 end.
Definition cx (n : nat) : Z :=
match n with
| 32%nat => g
| 33%nat => onum L (st_free_meta_head A)
| 34%nat => lnkv lnk_next
| 35%nat => lnkv lnk_prev
| 36%nat => sval_num L (amv A)
| 37%nat => st_avail_meta_count A
| 38%nat => st_avail_meta_area_count A
| 39%nat => st_meta_alloc_shift A
| 40%nat => onum L (st_area_head A)
| 41%nat => onum L (st_area_tail A)
| 42%nat => sval_num L (amav A)
| 43%nat => sval_num L (brkv A)
| 44%nat => av
| 45%nat => ar
| 0%nat => ly_sec L
| _ => 0
end.
Let E00 : env := E0 regs cx.
Definition FRM (W : Z -> Prop) (m : word -> option byte) : Prop :=
forall x, 0 <= x < 2 ^ 64 -> ~ W x -> m (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Lemma FRM_mono : forall (W W' : Z -> Prop) m, FRM W m -> (forall x, W x -> W' x) -> FRM W' m.
Proof. intros W W' m H HW x Hx Hn. apply H; [exact Hx|]. intros HWx. apply Hn, HW, HWx. Qed.
Definition at_st (ss : sstate) (W : Z -> Prop) (mdl : Model) (c : config) : Prop :=
exists E ms, c = mkCfg ms mdl /\ st_ok src0segs E ss ms /\ env_agree 46 E00 E /\ FRM W (ms_mem ms).
Let SO : syms_ok B := mid_syms _ _ _ _ _ MID.
Let MR : memrep B L A mem := mid_mem _ _ _ _ _ MID.
Lemma pre_facts : YK0s.ret_ok (getr regs 1) /\ sp mod 16 = 0 /\ alloc_ceiling + AMS <= sp /\ sp < 2 ^ 63 /\
(forall a, sp - AMS <= a < sp -> writable_at src0segs mem a) /\ getr regs 4 = Z_to_bv 64 TP /\
(forall a, ERRNO <= a < ERRNO + 4 -> writable_at src0segs mem a).
Proof.
pose proof PRE as (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold spZ in *. fold sp in H2, H3, H4, H5.
rewrite AMS_eq in *. rewrite B_tp in H6. rewrite B_errno in H7. repeat (split; [assumption|]). exact H7.
Qed.
Lemma In_ctx_image : forall c, In c (ctx_cells A) -> In c (image A).
Proof. intros c Hc. unfold image. apply in_app_iff. left. exact Hc. Qed.
Lemma ctx_word : forall off v, In (MCell (LCtx off) 8 v) (ctx_cells A) -> (forall z, v <> VLo5 z) ->
word_mem src0segs mem (CTX + off) (sval_num L v).
Proof.
intros off v Hin Hv. pose proof (memrep_cell B L A mem _ MR (In_ctx_image _ Hin)) as C.
unfold cell_mem in C. cbn [mc_loc mc_w mc_val loc_addr] in C. rewrite (mid_ctx _ _ _ _ _ MID), B_ctx in C.
destruct v as [z|p|z|]; try exact C. exfalso. exact (Hv z eq_refl).
Qed.
Lemma ctx13 : forall k c, nth_error (ctx_cells A) k = Some c -> (k < 13)%nat -> In c (ctx_cells A).
Proof. intros k c H _. exact (nth_error_In _ _ H). Qed.
Lemma entry_words :
word_mem src0segs mem CTX (if st_init_done A then ly_sec L else 0)   /\
(forall k, (k < 4)%nat -> mbyte src0segs mem (CTX + 8 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (if st_init_done A then 1 else 0) 4 k))) /\
word_mem src0segs mem (CTX + 16) (cx 33) /\ word_mem src0segs mem (CTX + 24) (cx 36) /\
word_mem src0segs mem (CTX + 32) (cx 37) /\ word_mem src0segs mem (CTX + 40) (cx 38) /\
word_mem src0segs mem (CTX + 48) (cx 39) /\ word_mem src0segs mem (CTX + 56) (cx 40) /\
word_mem src0segs mem (CTX + 64) (cx 41) /\ word_mem src0segs mem (CTX + 72) (cx 42) /\
word_mem src0segs mem (CTX + 920) (cx 43).
Proof.
assert (W : forall k off v, nth_error (ctx_cells A) k = Some (MCell (LCtx off) 8 v) -> (forall z, v <> VLo5 z) ->
word_mem src0segs mem (CTX + off) (sval_num L v)).
{ intros k off v Hk Hv. apply ctx_word; [exact (nth_error_In _ _ Hk) | exact Hv]. }
split.
{ assert (E1 : sval_num L (if st_init_done A then VSec else VZ 0) = (if st_init_done A then ly_sec L else 0)).
{ destruct (st_init_done A); reflexivity. }
rewrite <- E1. replace CTX with (CTX + 0) at 1 by lia.
apply (W 0%nat); [reflexivity | destruct (st_init_done A); discriminate]. }
split.
{ pose proof (memrep_cell B L A mem _ MR (In_ctx_image _ (nth_error_In (ctx_cells A) 1 eq_refl))) as C.
unfold cell_mem in C. cbn [mc_loc mc_w mc_val loc_addr sval_num] in C. rewrite (mid_ctx _ _ _ _ _ MID), B_ctx in C.
unfold CTX_init_done in C. exact C. }
unfold cx.
split; [rewrite <- sval_num_optr; apply (W 3%nat); [reflexivity | destruct (st_free_meta_head A); discriminate] |].
split; [apply (W 4%nat (CTX_avail_meta) (amv A)); [reflexivity | unfold amv; destruct (st_areas A); discriminate] |].
split; [apply (W 5%nat _ (VZ _)); [reflexivity | discriminate] |].
split; [apply (W 6%nat _ (VZ _)); [reflexivity | discriminate] |].
split; [apply (W 7%nat _ (VZ _)); [reflexivity | discriminate] |].
split; [rewrite <- sval_num_optr; apply (W 8%nat); [reflexivity | destruct (st_area_head A); discriminate] |].
split; [rewrite <- sval_num_optr; apply (W 9%nat); [reflexivity | destruct (st_area_tail A); discriminate] |].
split; [apply (W 10%nat CTX_avail_meta_areas (amav A)); [reflexivity | unfold amav; destruct (_ && _); discriminate] |].
apply (W 12%nat CTX_brk (brkv A)); [reflexivity | unfold brkv; destruct (st_brk A); discriminate].
Qed.
Lemma ctxw : forall m x, CTX <= x < CTX + 928 -> writable_at src0segs m x.
Proof. intros m x Hx. pose proof (so_ctx_rw B SO m x) as [W _]; [rewrite B_ctx; unfold CTX_SIZE; exact Hx | rewrite B_segs in W; exact W]. Qed.
Lemma sh_range : 0 <= st_meta_alloc_shift A <= 40.
Proof. destruct BND as (_ & B2 & _). exact B2. Qed.
Let ms0 := mkst regs (Z_to_bv 64 src0_A_alloc_meta) mem (seg_rom src0segs).
Lemma st_entry1 : st_init_done A = true -> st_ok src0segs E00 ss_am1 ms0.
Proof.
intros Ei. pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
pose proof entry_words as (C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C920). rewrite Ei in C8, C0.
pose proof (mid_statics _ _ _ _ _ MID) as ST.
apply (st_ok_am1 regs mem cx); try assumption.
- split; [exact P3 | split; [exact P4 | exact P2]].
- pose proof (st_got _ _ ST) as G. rewrite B_segs in G. exact G.
- pose proof (st_pagesize _ _ ST) as G. rewrite B_segs in G. exact G.
- apply ctxw.
- exact sh_range.
Qed.
Lemma st_entry0 : st_init_done A = false -> st_ok src0segs E00 ss_am0 ms0.
Proof.
intros Ei. pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
pose proof entry_words as (C0 & C8 & C16 & C24 & C32 & C40 & C48 & C56 & C64 & C72 & C920). rewrite Ei in C8, C0.
pose proof (mid_statics _ _ _ _ _ MID) as ST.
destruct (AUXV Ei) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
apply (st_ok_am0 regs mem cx); try assumption.
- split; [exact P3 | split; [exact P4 | exact P2]].
- pose proof (st_got _ _ ST) as G. rewrite B_segs in G. exact G.
- pose proof (st_pagesize _ _ ST) as G. rewrite B_segs in G. exact G.
- apply ctxw.
- exact sh_range.
- cbn [cx]. lia.
Qed.
Definition triple_eqb (a b : option nat * Z * Z) : bool :=
match a, b with
| (ba, loa, hia), (bb, lob, hib) => obase_eqb' ba bb && Z.eqb loa lob && Z.eqb hia hib
end.
Lemma triple_eqb_eq : forall a b, triple_eqb a b = true -> a = b.
Proof.
intros [[ba loa] hia] [[bb lob] hib] H. cbn in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst.
destruct ba as [x|], bb as [y|]; cbn in H1; try discriminate; [apply Nat.eqb_eq in H1; subst|]; reflexivity.
Qed.
Definition wsub (rs : smem) (l : list (option nat * Z * Z)) : bool :=
forallb (fun e => match e with (_, lo, hi) => (hi <=? lo) || existsb (triple_eqb e) l end) (wskel rs).
Lemma in_wrange_wsub : forall E rs l x,
wsub rs l = true -> in_wrange E rs x ->
exists b lo hi, In (b, lo, hi) l /\ base_val E b + lo <= x < base_val E b + hi.
Proof.
intros E rs l x Hs Hw. destruct (in_wrange_wskel E rs x Hw) as (b & lo & hi & Hin & Hx).
unfold wsub in Hs. pose proof (proj1 (forallb_forall _ _) Hs _ Hin) as H. cbn beta iota in H.
apply orb_prop in H as [H|H]; [apply Z.leb_le in H; lia|].
apply existsb_exists in H as (e & He & Heq). apply triple_eqb_eq in Heq. subst e. exists b, lo, hi. auto.
Qed.
Definition SK0 : list (option nat * Z * Z) :=
[(Some 2%nat, -AMS, 0); (None, CTX, CTX + 12); (None, CTX + 16, CTX + 80); (None, CTX + 920, CTX + 928); (None, ERRNO, ERRNO + 4)].
Lemma W0_of_SK0 : forall E b lo hi x,
ew E 2 = getr regs 2 -> In (b, lo, hi) SK0 -> base_val E b + lo <= x < base_val E b + hi -> WF0 B sp x.
Proof.
intros E b lo hi x HE2 Hin Hx. unfold SK0 in Hin. cbn [In] in Hin.
unfold WF0, am_scratch, ctxW. rewrite B_errno, B_ctx, AMS_eq.
destruct Hin as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <- <-; cbn [base_val] in Hx; rewrite ?HE2 in Hx; fold sp in Hx; unfold AMS in *; lia.
Qed.
Lemma FRM_run : forall (W : Z -> Prop) E rs m m' l,
FRM W m -> frame_of E rs m m' -> wsub rs l = true ->
(forall b lo hi x, In (b, lo, hi) l -> base_val E b + lo <= x < base_val E b + hi -> W x) ->
FRM W m'.
Proof.
intros W E rs m m' l HF Hfr Hs HW x Hx Hn. rewrite <- (HF x Hx Hn). apply (frame_of_at E rs m m' x Hfr Hx).
intros Hw. destruct (in_wrange_wsub E rs l x Hs Hw) as (b & lo & hi & Hin & Hbx). exact (Hn (HW b lo hi x Hin Hbx)).
Qed.
Lemma FRM0 : FRM (WF0 B sp) mem.
Proof. intros x _ _. reflexivity. Qed.
Lemma agree_reg2 : forall E, env_agree 46 E00 E -> ew E 2 = getr regs 2.
Proof. intros E [H _]. rewrite (H 2%nat) by lia. reflexivity. Qed.
Hypothesis Hh : m_halted md = None.
Hypothesis Hlz : m_vm_lazy md = [].
Lemma wsub_am1 : wsub (ss_mem ss_am1) SK0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wsub_am0 : wsub (ss_mem ss_am0) SK0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wsub_i2 : wsub (ss_mem ss_i2) SK0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma reach_A2_1 : st_init_done A = true -> SR src0segs (mkCfg ms0 md) (at_st ss_A2 (WF0 B sp) md).
Proof.
intros Ei. pose proof (st_entry1 Ei) as HS.
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL PC_A2 E00 ss_am1 ss_a2x RS_running); [exact Hh | exact Hlz | exact HS | apply run_am1 |].
intros ms1 HS1 HF1.
assert (AT : ss_atoms_lt 57 ss_a2x = true) by (vm_compute; reflexivity).
assert (NZ : forallb (fun r : reg => negb (bv_eqb r 0)) A2_JUNK = true) by (vm_compute; reflexivity).
destruct (junk_regs_ok src0segs A2_JUNK 57 E00 ss_a2x ms1 HS1 AT NZ) as (E1 & HA1 & HS2).
pose proof (st_ok_merge src0segs E1 ss_A2 (junk_regs A2_JUNK 57 ss_a2x) ms1 HS2 merge_a2x) as HS3.
apply SR_ret. exists E1, ms1. split; [reflexivity|]. split; [exact HS3|]. split; [eapply env_agree_le; [| exact HA1]; lia|].
eapply (FRM_run _ E00); [apply FRM0 | exact HF1 | apply wsub_am1 | intros b lo hi x Hin Hx; apply (W0_of_SK0 E00 b lo hi x eq_refl Hin Hx)].
Qed.
Lemma reach_A2_0 : st_init_done A = false -> SR src0segs (mkCfg ms0 md) (at_st ss_A2 (WF0 B sp) md).
Proof.
intros Ei. pose proof (st_entry0 Ei) as HS. pose proof (proj1 alloc_ceiling_val) as AC.
pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7). unfold AMS in P3, P5.
destruct (AUXV Ei) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10). fold sp in X9, X10.
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL src0_A_memcpy E00 ss_am0 ss_i1 RS_running); [exact Hh | exact Hlz | exact HS | apply run_am0 |].
intros ms1 HS1 HF1.
rewrite (st_ok_mkst src0segs E00 ss_i1 ms1 HS1 eq_refl). rewrite ss_i1_pc.
set (bs := map (fun k => Z_to_bv 8 (le_byte (ly_sec L) 8 k)) (seq 0 8)).
assert (Lbs : length bs = 8%nat) by reflexivity.
pose proof (mid_sec _ _ _ _ _ MID) as SECR.
assert (D0 : sv_denot E00 (SOff 0 0) = Z_to_bv 64 (ly_sec L)).
{ cbn [sv_denot]. unfold E00. cbn [ew E0 cx]. rewrite u64_of_Z, Z.add_0_r by lia. reflexivity. }
assert (BW : forall i, 0 <= i < 8 -> byte_of_word (Z_to_bv 64 (ly_sec L)) i = Z_to_bv 8 (le_byte (ly_sec L) 8 (Z.to_nat i))).
{ intros i Hi. unfold byte_of_word, le_byte. rewrite u64_of_Z by lia.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite (Z.mod_small (ly_sec L) (2 ^ 64)) by lia. rewrite Z2Nat.id by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity. }
assert (NB : forall k, (k < 8)%nat -> nth_error bs k = Some (Z_to_bv 8 (le_byte (ly_sec L) 8 k))).
{ intros k Hk. subst bs. do 8 (destruct k as [|k]; [reflexivity|]). lia. }
assert (R10 : getr (ms_regs ms1) 10 = Z_to_bv 64 (sp - 64)).
{ rewrite (st_ok_reg src0segs E00 ss_i1 ms1 10 HS1). change (sr_get (ss_regs ss_i1) 10) with (SOff 2 (-64)). cbn [sv_denot]. subst E00. cbn [ew E0]. f_equal. }
assert (R11 : getr (ms_regs ms1) 11 = Z_to_bv 64 (ar + 8)).
{ rewrite (st_ok_reg src0segs E00 ss_i1 ms1 11 HS1). change (sr_get (ss_regs ss_i1) 11) with (SOff 45 8). cbn [sv_denot]. subst E00.
rewrite (E0_cx regs cx 45 ltac:(lia)). cbn [cx]. rewrite u64_of_Z by lia. reflexivity. }
assert (R12 : getr (ms_regs ms1) 12 = Z_to_bv 64 8).
{ rewrite (st_ok_reg src0segs E00 ss_i1 ms1 12 HS1). reflexivity. }
assert (R1 : getr (ms_regs ms1) 1 = Z_to_bv 64 PC_MCRET).
{ rewrite (st_ok_reg src0segs E00 ss_i1 ms1 1 HS1). reflexivity. }
assert (SRC : rdn src0segs (ms_mem ms1) (Z_to_bv 64 (ar + 8)) (length bs) = Some bs).
{ apply rdn_mbytes. split; [reflexivity|]. intros i Hi. rewrite Lbs in Hi.
assert (FRi : ms_mem ms1 (Z_to_bv 64 (ar + 8 + Z.of_nat i)) = mem (Z_to_bv 64 (ar + 8 + Z.of_nat i))).
{ apply (frame_of_at E00 (ss_mem ss_am0) mem (ms_mem ms1) _ HF1); [lia|].
intros Hw. destruct (in_wrange_wsub E00 _ SK0 _ wsub_am0 Hw) as (b & lo & hi & Hin & Hx).
unfold SK0 in Hin. cbn [In] in Hin.
destruct Hin as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <- <-; subst E00; cbn [base_val ew E0] in Hx; fold sp in Hx;
unfold AMS, CTX, ERRNO, src0_D_malloc_context, src0_tp in *; lia. }
transitivity (mbyte src0segs mem (ar + 8 + Z.of_nat i)).
{ unfold mbyte. rewrite FRi. reflexivity. }
rewrite (X4 i) by lia. symmetry. apply NB. exact Hi. }
pose proof (st_ok_mem_ok src0segs E00 ss_i1 ms1 HS1) as HM1.
destruct (swrite_sound src0segs E00 (ms_mem ms1) (ss_mem ss_i1) (Some 2%nat) (-64) (CVal 8 (SOff 0 0)) bs mem_i2 HM1) as [STOK HM2].
{ rewrite Lbs. change (Z.of_nat 8) with 8. apply store_i1. }
{ rewrite Lbs. lia. }
{ rewrite Lbs. reflexivity. }
{ intros i Hi. rewrite Lbs in Hi. change (Z.of_nat 8) with 8 in Hi. cbn [cbyte]. rewrite D0, BW by lia.
rewrite (NB (Z.to_nat i)) by lia. reflexivity. }
assert (EB : base_val E00 (Some 2%nat) + -64 = sp - 64) by (subst E00; cbn [base_val ew E0]; fold sp; lia).
rewrite EB in STOK, HM2.
destruct (src0_memcpy bs (Z_to_bv 64 (sp - 64)) (Z_to_bv 64 (ar + 8)) (Z_to_bv 64 8) (ms_mem ms1) (seg_rom src0segs) (ms_regs ms1)
R10 R11 R12 eq_refl SRC) as (regs' & Hms & H10' & Hpres).
{ exact STOK. }
{ rewrite Lbs. change (Z.of_nat 8) with 8. rewrite u64_of_Z by lia. lia. }
{ rewrite Lbs. change (Z.of_nat 8) with 8. rewrite u64_of_Z by lia. lia. }
{ rewrite Lbs. change (Z.of_nat 8) with 8. rewrite !u64_of_Z by lia. left. lia. }
eapply SR_msteps; [exact Hh | exact Hlz | exact Hms |].
rewrite R1. replace (v_jalr (Z_to_bv 64 PC_MCRET) 0) with (Z_to_bv 64 PC_MCRET) by (symmetry; apply ret_ok_even; reflexivity).
assert (HS1' : st_ok src0segs E00 ss_i1' (mkst (ms_regs ms1) (Z_to_bv 64 PC_MCRET) (wbytes (ms_mem ms1) (Z_to_bv 64 (sp - 64)) bs) (seg_rom src0segs))).
{ destruct HS1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
unfold st_ok, ss_i1', setpc, setmem, mkst; cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem ss_pc ss_regs ss_mem ss_resv ss_facts].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact S7|]. split; [exact HM2 | exact S9]. }
assert (AT : ss_atoms_lt 46 ss_i1' = true) by (vm_compute; reflexivity).
assert (NZ : forallb (fun r : reg => negb (bv_eqb r 0)) MC_JUNK = true) by (vm_compute; reflexivity).
destruct (st_ok_clobber src0segs MC_JUNK 46 E00 ss_i1' (ms_regs ms1) regs' (Z_to_bv 64 PC_MCRET) _ (seg_rom src0segs) HS1' AT NZ) as (E1 & HA1 & HS2).
{ intros r Hr. apply Hpres; intros ->; apply Hr; cbn; tauto. }
change (junk_regs MC_JUNK 46 ss_i1') with ss_i2 in HS2.
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL PC_A2 E1 ss_i2 ss_a2y RS_running); [exact Hh | exact Hlz | exact HS2 | apply run_i2 |].
intros ms3 HS3 HF3.
assert (AT3 : ss_atoms_lt 57 ss_a2y = true) by (vm_compute; reflexivity).
assert (NZ3 : forallb (fun r : reg => negb (bv_eqb r 0)) A2_JUNK = true) by (vm_compute; reflexivity).
destruct (junk_regs_ok src0segs A2_JUNK 57 E1 ss_a2y ms3 HS3 AT3 NZ3) as (E2 & HA2 & HS4).
pose proof (st_ok_merge src0segs E2 ss_A2 (junk_regs A2_JUNK 57 ss_a2y) ms3 HS4 merge_a2y) as HS5.
apply SR_ret. exists E2, ms3. split; [reflexivity|]. split; [exact HS5|]. split.
{ eapply env_agree_trans; [exact HA1 | eapply env_agree_le; [| exact HA2]; lia]. }
assert (F1 : FRM (WF0 B sp) (ms_mem ms1)).
{ eapply (FRM_run _ E00); [apply FRM0 | exact HF1 | apply wsub_am0 | intros b lo hi x Hin Hx; apply (W0_of_SK0 E00 b lo hi x eq_refl Hin Hx)]. }
assert (F2 : FRM (WF0 B sp) (wbytes (ms_mem ms1) (Z_to_bv 64 (sp - 64)) bs)).
{ intros x Hx Hn. rewrite <- (F1 x Hx Hn). apply wbytes_other; [lia | rewrite Lbs; change (Z.of_nat 8) with 8; lia | exact Hx |].
rewrite Lbs; change (Z.of_nat 8) with 8. intros Hin. apply Hn. unfold WF0, am_scratch. left. left. rewrite AMS_eq. fold sp. unfold AMS. lia. }
eapply (FRM_run _ E1); [apply F2 | exact HF3 | apply wsub_i2 |].
intros b lo hi x Hin Hx. apply (W0_of_SK0 E1 b lo hi x (agree_reg2 E1 HA1) Hin Hx).
Qed.
Lemma reach_A2 : SR src0segs (mkCfg ms0 md) (at_st ss_A2 (WF0 B sp) md).
Proof. generalize reach_A2_1 reach_A2_0. intros H1 H0. destruct (st_init_done A); [apply H1 | apply H0]; reflexivity. Qed.
Lemma word_of_chunk : forall E ss ms i r a sv v,
st_ok src0segs E ss ms -> nth_error (ss_mem ss) i = Some r -> r_base r = None ->
In (mkChunk a (CVal 8 sv)) (r_chunks r) -> sv_denot E sv = Z_to_bv 64 v ->
word_mem src0segs (ms_mem ms) a v.
Proof.
intros E ss ms i r a sv v HS Hi Hb Hin Hv.
pose proof (st_ok_chunk src0segs E ss ms i r _ HS Hi Hin) as C. rewrite Hb in C. cbn [base_val] in C.
replace a with (0 + a) by lia. eapply word_mem_of_chunk; [exact C | exact Hv].
Qed.
Lemma word_of_chunk_at : forall E ss ms i r n off sv v,
st_ok src0segs E ss ms -> nth_error (ss_mem ss) i = Some r -> r_base r = Some n ->
In (mkChunk off (CVal 8 sv)) (r_chunks r) -> sv_denot E sv = Z_to_bv 64 v ->
word_mem src0segs (ms_mem ms) (bv_unsigned (ew E n) + off) v.
Proof.
intros E ss ms i r n off sv v HS Hi Hb Hin Hv.
pose proof (st_ok_chunk src0segs E ss ms i r _ HS Hi Hin) as C. rewrite Hb in C. cbn [base_val] in C.
eapply word_mem_of_chunk; [exact C | exact Hv].
Qed.
Lemma w4_of_chunk : forall E ss ms i r a sv v,
st_ok src0segs E ss ms -> nth_error (ss_mem ss) i = Some r -> r_base r = None ->
In (mkChunk a (CVal 4 sv)) (r_chunks r) -> sv_denot E sv = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
forall k, (k < 4)%nat -> mbyte src0segs (ms_mem ms) (a + Z.of_nat k) = Some (Z_to_bv 8 (le_byte v 4 k)).
Proof.
intros E ss ms i r a sv v HS Hi Hb Hin Hv Hr k Hk.
pose proof (st_ok_chunk src0segs E ss ms i r _ HS Hi Hin) as C. rewrite Hb in C. cbn [base_val] in C.
replace a with (0 + a) by lia. apply (chunk_bytes_cval_exact src0segs E _ 0 a 4 sv v C Hv Hr k Hk).
Qed.
Lemma zeros_of_chunk_at : forall E ss ms i r n off len,
st_ok src0segs E ss ms -> nth_error (ss_mem ss) i = Some r -> r_base r = Some n ->
In (mkChunk off (CZero len)) (r_chunks r) ->
forall j, 0 <= j < len -> mbyte src0segs (ms_mem ms) (bv_unsigned (ew E n) + off + j) = Some (Z_to_bv 8 0).
Proof.
intros E ss ms i r n off len HS Hi Hb Hin j Hj.
pose proof (st_ok_chunk src0segs E ss ms i r _ HS Hi Hin) as C. rewrite Hb in C. cbn [base_val] in C.
exact (chunk_bytes_czero src0segs E _ _ off len C j Hj).
Qed.
Lemma zword_of_chunk_at : forall E ss ms i r n off,
st_ok src0segs E ss ms -> nth_error (ss_mem ss) i = Some r -> r_base r = Some n ->
In (mkChunk off (CVal 8 (SLit 0))) (r_chunks r) ->
forall j, 0 <= j < 8 -> mbyte src0segs (ms_mem ms) (bv_unsigned (ew E n) + off + j) = Some (Z_to_bv 8 0).
Proof.
intros E ss ms i r n off HS Hi Hb Hin j Hj.
pose proof (word_of_chunk_at E ss ms i r n off (SLit 0) 0 HS Hi Hb Hin eq_refl) as W.
replace j with (Z.of_nat (Z.to_nat j)) by lia. rewrite (W (Z.to_nat j)) by lia. rewrite YN03.le_byte_0. reflexivity.
Qed.
Lemma writable_of_region : forall E ss ms i r x,
st_ok src0segs E ss ms -> nth_error (ss_mem ss) i = Some r ->
base_val E (r_base r) + r_wlo r <= x < base_val E (r_base r) + r_whi r ->
writable_at src0segs (ms_mem ms) x.
Proof.
intros E ss ms i r x HS Hi Hx.
replace x with (base_val E (r_base r) + (x - base_val E (r_base r))) by lia.
apply (st_ok_writable src0segs E ss ms i r _ HS Hi). lia.
Qed.
Definition cs_regs : list nat := [2; 3; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition final_regs_check (ss : sstate) : bool :=
forallb (fun k => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat k))) (SOff k 0)) cs_regs
&& sv_eqb (sr_get (ss_regs ss) 4) (SLit TP) && sv_eqb (sr_get (ss_regs ss) 1) (SOff 1 0)
&& Z.eqb (ss_pc ss) PC_RET && match ss_resv ss with None => true | _ => false end.
Lemma final_regs : forall E ss ms,
final_regs_check ss = true -> st_ok src0segs E ss ms -> env_agree 46 E00 E ->
regs_preserved regs (ms_regs ms) /\ ew E 1 = getr regs 1 /\ sr_get (ss_regs ss) 1 = SOff 1 0 /\ ss_pc ss = PC_RET /\ ss_resv ss = None.
Proof.
intros E ss ms Hc HS [HA _]. pose proof pre_facts as (_ & _ & _ & _ & _ & P6 & _).
unfold final_regs_check in Hc. apply andb_prop in Hc as [Hc Hrv]. apply andb_prop in Hc as [Hc Hpc]. apply andb_prop in Hc as [Hc H1]. apply andb_prop in Hc as [Hc H4].
apply Z.eqb_eq in Hpc. apply sv_eqb_eq in H1. apply sv_eqb_eq in H4. rewrite forallb_forall in Hc.
assert (EW : forall k, (1 <= k <= 31)%nat -> ew E k = getr regs (Z_to_bv 5 (Z.of_nat k))).
{ intros k Hk. rewrite (HA k) by lia. subst E00. apply E0_reg. exact Hk. }
split; [| split; [exact (EW 1%nat ltac:(lia)) | split; [exact H1 | split; [exact Hpc | destruct (ss_resv ss); [discriminate | reflexivity]]]]].
intros r Hr. rewrite (st_ok_reg src0segs _ ss ms _ HS).
assert (CASE : r = 4 \/ exists k, In k cs_regs /\ r = Z.of_nat k).
{ unfold callee_saved in Hr. unfold cs_regs.
destruct Hr as [->|[->|[->|[->|[->|Hr]]]]]; [right; exists 2%nat | right; exists 3%nat | left; reflexivity | right; exists 8%nat | right; exists 9%nat |];
try (split; [cbn; tauto | reflexivity]).
right. exists (Z.to_nat r). split; [|lia].
assert (H : (18 <= Z.to_nat r <= 27)%nat) by lia. revert H. generalize (Z.to_nat r) as m. intros m H.
do 18 (destruct m as [|m]; [lia|]). do 10 (destruct m as [|m]; [cbn; tauto|]). lia. }
destruct CASE as [-> | (k & Hk & ->)].
- replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite H4. cbn [sv_denot]. symmetry. exact P6.
- specialize (Hc k Hk). apply sv_eqb_eq in Hc. rewrite Hc. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
apply EW. unfold cs_regs in Hk. cbn [In] in Hk. lia.
Qed.
Lemma reg_off : forall E ss ms (r : reg) n d,
st_ok src0segs E ss ms -> sr_get (ss_regs ss) r = SOff n d -> getr (ms_regs ms) r = Z_to_bv 64 (bv_unsigned (ew E n) + d).
Proof. intros E ss ms r n d HS Hr. rewrite (st_ok_reg src0segs _ ss ms r HS), Hr. reflexivity. Qed.
Lemma scratch_writable : forall E ss ms i j rstk,
st_ok src0segs E ss ms -> env_agree 46 E00 E ->
nth_error (ss_mem ss) i = Some rstk -> r_base rstk = Some 2%nat -> r_wlo rstk = - AMS -> r_whi rstk = 0 ->
nth_error (ss_mem ss) j = Some R_errno ->
forall a, call_scratch B sp AM_STACK a -> writable_at src0segs (ms_mem ms) a.
Proof.
intros E ss ms i j rstk HS HA Hi Hb Hlo Hhi Hj a Ha. rewrite AMS_eq in Ha. unfold call_scratch in Ha. rewrite B_errno in Ha.
destruct Ha as [Ha|Ha].
- apply (writable_of_region E ss ms i rstk a HS Hi). rewrite Hb, Hlo, Hhi. cbn [base_val]. rewrite (agree_reg2 E HA). fold sp. lia.
- apply (writable_of_region E ss ms j R_errno a HS Hj). cbn. lia.
Qed.
Definition scratch_skel (ss : sstate) (i j : nat) : bool :=
match nth_error (ss_mem ss) i, nth_error (ss_mem ss) j with
| Some rstk, Some rerr =>
obase_eqb' (r_base rstk) (Some 2%nat) && Z.eqb (r_wlo rstk) (- AMS) && Z.eqb (r_whi rstk) 0 &&
obase_eqb' (r_base rerr) None && Z.eqb (r_wlo rerr) ERRNO && Z.eqb (r_whi rerr) (ERRNO + 4)
| _, _ => false
end.
Lemma scratch_writable' : forall E ss ms i j,
st_ok src0segs E ss ms -> env_agree 46 E00 E -> scratch_skel ss i j = true ->
forall a, call_scratch B sp AM_STACK a -> writable_at src0segs (ms_mem ms) a.
Proof.
intros E ss ms i j HS HA Hk a Ha. unfold scratch_skel in Hk.
destruct (nth_error (ss_mem ss) i) as [rstk|] eqn:Hi; [|discriminate]. destruct (nth_error (ss_mem ss) j) as [rerr|] eqn:Hj; [|discriminate].
repeat (apply andb_prop in Hk as [Hk ?]).
apply Z.eqb_eq in H. apply Z.eqb_eq in H0. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3.
rewrite AMS_eq in Ha. unfold call_scratch in Ha. rewrite B_errno in Ha.
destruct Ha as [Ha|Ha].
- apply (writable_of_region E ss ms i rstk a HS Hi). destruct (r_base rstk) as [[|[|[|n]]]|]; try discriminate. rewrite H3, H2. cbn [base_val]. rewrite (agree_reg2 E HA). fold sp. lia.
- apply (writable_of_region E ss ms j rerr a HS Hj). destruct (r_base rerr); [discriminate|]. rewrite H0, H. cbn [base_val]. lia.
Qed.
Definition POST (r : option sptr * astate) (c' : config) : Prop :=
exists L' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom src0segs)) md' /\
callee_post B L A regs mem md AM_STACK L' (snd r) regs' mem' md' /\ ama_ok (snd r) /\ bounded (snd r) /\
getr regs' 10 = Z_to_bv 64 (match fst r with None => 0 | Some m => ptr_addr L' m end) /\
(match fst r with Some m => ptr_addr L' m <> 0 | None => True end).
Definition Qspec (r : option sptr * astate) : Prop :=
match fst r with
| None => Inv X R U (snd r)
| Some m => Inv (m :: X) R U (snd r) /\ memb m X = false /\ In m (keys (snd r))
end.
Lemma alloc_meta_Qspec : itok (alloc_meta A) Qspec.
Proof.
apply (alloc_meta_spec X R U A Qspec HI).
- intros s' HI' _ _ _. exact HI'.
- intros m s' HI' Hm Hk _ _ _ _. cbn. auto.
Qed.
Lemma sv_off : forall E n d v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n d) = Z_to_bv 64 (v + d).
Proof.
intros E n d v H. cbn [sv_denot]. rewrite H. apply Z_to_bv64_eq_mod.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma sv_off0 : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. rewrite (sv_off E n 0 v H). f_equal. lia. Qed.
Lemma agree_cx : forall E n, env_agree 46 E00 E -> (32 <= n < 46)%nat -> ew E n = Z_to_bv 64 (cx n).
Proof. intros E n [HA _] Hn. rewrite (HA n) by lia. subst E00. apply E0_cx. lia. Qed.
Lemma agree_sec : forall E k, env_agree k E00 E -> (0 < k)%nat -> ew E 0 = Z_to_bv 64 (ly_sec L).
Proof. intros E k [HA _] Hk. rewrite (HA 0%nat) by lia. reflexivity. Qed.
Lemma sv_sec : forall E k, env_agree k E00 E -> (0 < k)%nat -> sv_denot E (SOff 0 0) = Z_to_bv 64 (ly_sec L).
Proof. intros E k HA Hk. apply sv_off0. exact (agree_sec E k HA Hk). Qed.
Lemma with_vmmaps_self : forall mdl, m_vm_lazy mdl = [] -> m_vm_materialized mdl = [] -> mdl = with_vmmaps (m_vmmaps mdl) mdl.
Proof.
intros [fd [maps lazy mat] io fs proc lim tm] Hl Hm. unfold with_vmmaps, m_vmmaps, m_vm_lazy, m_vm_materialized in *.
cbn in *. subst. reflexivity.
Qed.
Lemma apart_by_img : forall a n lo hi, 0 < n -> lo < hi ->
(forall x, lo <= x < hi -> in_img B x) -> (forall x, a <= x < a + n -> ~ in_img B x) -> a + n <= lo \/ hi <= a.
Proof.
intros a n lo hi Hn Hlh Himg Hno.
destruct (Z_lt_le_dec lo (a + n)); [|left; lia]. destruct (Z_lt_le_dec a hi); [|right; lia]. exfalso.
destruct (Z_le_gt_dec a lo).
- apply (Hno lo); [lia|]. apply Himg. lia.
- apply (Hno a); [lia|]. apply Himg. lia.
Qed.
Lemma md_facts : m_halted md = None /\ m_vm_lazy md = [] /\ m_vm_materialized md = [].
Proof. exact (mid_md _ _ _ _ _ MID). Qed.
Section w.
Hypothesis Efh : st_free_meta_head A = None.
Hypothesis Hamc : 0 < st_avail_meta_count A.
Let m := st_avail_meta A.
Let A' := take_st A0.
Lemma wsub_A2 : wsub (ss_mem ss_A2) SK0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wsub_fh0 : wsub (ss_mem (add_cond ss_fh C_fh0)) SK0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wsub_amc1 : wsub (ss_mem (add_cond ss_amc C_amc1)) SK0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma wsub_c2 : wsub (ss_mem ss_c2) ((Some 36%nat, 0, 16) :: SK0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cE_checks : final_regs_check ss_cE = true. Proof. vm_compute. reflexivity. Qed.
Lemma m_facts : st_areas A <> [] /\ In (last (st_areas A) (SP 0%nat 0)) (st_areas A) /\
(forall x, ptr_addr L m <= x < ptr_addr L m + 16 ->
ptr_addr L (last (st_areas A) (SP 0%nat 0)) <= x < ptr_addr L (last (st_areas A) (SP 0%nat 0)) + PGSZ) /\
cx 36 = ptr_addr L m /\ 0 < st_avail_meta_count A <= METAS_PER_AREA.
Proof.
destruct (C_facts X R U A HI Hamc) as (Hfresh & HI' & Hne & (k & Hk & Em) & Hlast).
split; [exact Hne|]. split; [exact Hlast|]. split; [| split].
- intros x Hx. unfold m in Hx. rewrite Em in Hx. unfold slot_of in Hx. rewrite ptr_addr_padd in Hx.
unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia.
- cbn [cx]. unfold amv. destruct (st_areas A); [exfalso; exact (Hne eq_refl) | reflexivity].
- pose proof (inv_keys HI) as (_ & _ & _ & _ & Hc). lia.
Qed.
Theorem path_C : forall c, at_st ss_A2 (WF0 B sp) md c -> SR src0segs c (POST (Some m, A')).
Proof.
intros c (E & ms1 & -> & HS1 & HA & HF1).
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7). unfold AMS in P3, P5.
pose proof md_facts as (Mh & Mlz & Mmat).
pose proof m_facts as (Hne & Hlast & INPAGE & E36v & Hamc').
pose proof (areas_off_img B X R U L A mem md HI MID) as OFF.
assert (E33 : ew E 33 = Z_to_bv 64 0) by (rewrite (agree_cx E 33 HA) by lia; cbn [cx]; rewrite Efh; reflexivity).
assert (E37 : ew E 37 = Z_to_bv 64 (st_avail_meta_count A)) by (rewrite (agree_cx E 37 HA) by lia; reflexivity).
assert (E36 : ew E 36 = Z_to_bv 64 (ptr_addr L m)) by (rewrite (agree_cx E 36 HA) by lia; rewrite E36v; reflexivity).
assert (AMr : 4096 <= ptr_addr L m /\ ptr_addr L m + 16 <= alloc_ceiling).
{ destruct (OFF _ (ptr_addr L m) Hlast (INPAGE (ptr_addr L m) ltac:(lia))) as [_ R1].
destruct (OFF _ (ptr_addr L m + 15) Hlast (INPAGE (ptr_addr L m + 15) ltac:(lia))) as [_ R2]. lia. }
assert (U36 : bv_unsigned (ew E 36) = ptr_addr L m) by (rewrite E36; apply u64_of_Z; lia).
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E ss_A2 ss_fh); [exact Mh | exact Mlz | exact HS1 | apply run_A2 |].
intros ms2 HS2 HF2.
apply (st_ok_add_cond src0segs E ss_fh ms2 BC_EQ (SOff 33 0) (SLit 0)) in HS2.
2:{ rewrite (sv_off E 33 0 0 E33). reflexivity. }
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E (add_cond ss_fh C_fh0) ss_amc); [exact Mh | exact Mlz | exact HS2 | apply run_fh0 |].
intros ms3 HS3 HF3.
apply (st_ok_add_cond src0segs E ss_amc ms3 BC_NE (SOff 37 0) (SLit 0)) in HS3.
2:{ rewrite (sv_off E 37 0 _ E37). cbn [sv_denot]. rewrite branch_ne, !u64_of_Z by (unfold METAS_PER_AREA in *; lia).
apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E (add_cond ss_amc C_amc1) ss_c1); [exact Mh | exact Mlz | exact HS3 | apply run_amc1 |].
intros ms4 HS4 HF4.
assert (F4 : FRM (WF0 B sp) (ms_mem ms4)).
{ eapply (FRM_run _ E); [| exact HF4 | apply wsub_amc1 | intros b lo hi x Hin Hx; apply (W0_of_SK0 E b lo hi x (agree_reg2 E HA) Hin Hx)].
eapply (FRM_run _ E); [| exact HF3 | apply wsub_fh0 | intros b lo hi x Hin Hx; apply (W0_of_SK0 E b lo hi x (agree_reg2 E HA) Hin Hx)].
eapply (FRM_run _ E); [exact HF1 | exact HF2 | apply wsub_A2 | intros b lo hi x Hin Hx; apply (W0_of_SK0 E b lo hi x (agree_reg2 E HA) Hin Hx)]. }
assert (NW : forall x, ptr_addr L m <= x < ptr_addr L m + 16 -> ~ WF0 B sp x).
{ intros x Hx [Hs|Hc].
- exact (scratch_not_area B X R U L A mem md HI MID src0_ERRIMG sp x _ ltac:(rewrite AMS_eq; unfold AMS; lia) Hs Hlast (INPAGE x Hx)).
- exact (ctxW_not_area B X R U L A mem md HI MID x _ Hc Hlast (INPAGE x Hx)). }
assert (PRES : forall x, ptr_addr L m <= x < ptr_addr L m + 16 -> present (ms_mem ms4) x).
{ intros x Hx. pose proof (mid_mem _ _ _ _ _ MID) as (_ & _ & FT).
assert (Hin : In (LMem (last (st_areas A) (SP 0%nat 0)), PGSZ) (footprint A)).
{ right. apply in_app_iff. left. apply in_map_iff. eexists. split; [reflexivity | exact Hlast]. }
pose proof (proj1 (Forall_forall _ _) FT _ Hin) as FO. cbn [foot_ok fst snd] in FO.
destruct (FO x) as [b Hb]; [change (loc_addr L (LMem ?a)) with (ptr_addr L a); apply INPAGE; exact Hx|].
exists b. rewrite (F4 x ltac:(lia) (NW x Hx)). exact Hb. }
assert (HS4' : st_ok src0segs E ss_c2 ms4).
{ apply (st_ok_add_region src0segs E ss_c1 ms4 R_am HS4); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_am]; rewrite ?U36; [lia | lia | | apply Forall_nil].
intros o Ho. apply present_writable. apply PRES. lia.
- assert (SK : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_c1) =
[(Some 2%nat, -AMS, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56);
(None, CTX, CTX + 12); (None, CTX + 16, CTX + 80); (None, CTX + 920, CTX + 928); (None, ERRNO, ERRNO + 4)]) by (vm_compute; reflexivity).
assert (IMG : forall lo hi, 0x1e000 <= lo -> hi <= 0x51000 -> lo < hi -> ptr_addr L m + 16 <= lo \/ hi <= ptr_addr L m).
{ intros lo hi Hlo Hhi Hlh. apply (apart_by_img (ptr_addr L m) 16 lo hi); [lia | exact Hlh | |].
- intros x Hx. apply src0_rwseg_img. lia.
- intros x Hx. destruct (OFF _ x Hlast (INPAGE x Hx)) as [NI _]. exact NI. }
apply Forall_forall. intros r Hr. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr. rewrite SK in Hr.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_am base_val]. rewrite U36.
cbn [In] in Hr. destruct Hr as [H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]];
apply (f_equal (fun t => match t with (b, lo, hi) => (b, lo, hi) end)) in H; cbn in H;
injection H as <- <- <-; cbn [base_val]; rewrite ?(agree_reg2 E HA); fold sp;
unfold AMS, GOT, GUARD, LIBC, CTX, ERRNO, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_libc, src0_D_malloc_context, src0_tp;
rewrite ?Z.add_0_l, ?Z.add_0_r; first [lia | apply IMG; lia]. }
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E ss_c2 ss_cE); [exact Mh | exact Mlz | exact HS4' | apply run_c2 |].
intros ms5 HS5 HF5.
destruct (final_regs E ss_cE ms5 cE_checks HS5 HA) as (PRS & E1 & Hra & Hpc & Hrv).
apply (SR_final_ret E ss_cE ms5 md _ HS5 Hrv Hpc Hra); [rewrite E1; exact P1 | exact Mh | exact Mlz |].
assert (F5 : FRM (WC B L A sp) (ms_mem ms5)).
{ eapply (FRM_run _ E); [eapply FRM_mono; [exact F4 | intros x [Hx|Hx]; [left | right; left]; exact Hx] | exact HF5 | apply wsub_c2 |].
intros b lo hi x [Hin|Hin] Hx.
- injection Hin as <- <- <-. cbn [base_val] in Hx. rewrite U36 in Hx. right. right. unfold m in Hx. lia.
- destruct (W0_of_SK0 E b lo hi x (agree_reg2 E HA) Hin Hx) as [Hw|Hw]; [left | right; left]; exact Hw. }
assert (MEM5 : nth_error (ss_mem ss_cE) 0 = Some (YP09.mkRegion (Some 36%nat) 0 16 0 16 [mkChunk 0 (CVal 8 (SLit 0)); mkChunk 8 (CVal 8 (SLit 0))]) /\
nth_error (ss_mem ss_cE) 5 = Some (R_ctxA true) /\
nth_error (ss_mem ss_cE) 6 = Some (YP09.mkRegion None (CTX + 16) (CTX + 80) (CTX + 16) (CTX + 80)
[mkChunk (CTX + 32) (CVal 8 (SOff 37 (-1))); mkChunk (CTX + 24) (CVal 8 (SOff 36 40));
mkChunk (CTX + 16) (CVal 8 (SOff 33 0)); mkChunk (CTX + 40) (CVal 8 (SOff 38 0));
mkChunk (CTX + 48) (CVal 8 (SOff 39 0)); mkChunk (CTX + 56) (CVal 8 (SOff 40 0));
mkChunk (CTX + 64) (CVal 8 (SOff 41 0)); mkChunk (CTX + 72) (CVal 8 (SOff 42 0))]) /\
nth_error (ss_mem ss_cE) 7 = Some R_ctxC /\
nth_error (ss_mem ss_cE) 1 = Some (YP09.mkRegion (Some 2%nat) (-AMS) 0 (-AMS) 0
[mkChunk (-56) (CVal 8 (SOff 32 0)); mkChunk (-48) (CVal 8 (SOff 20 0)); mkChunk (-40) (CVal 8 (SOff 19 0));
mkChunk (-32) (CVal 8 (SOff 18 0)); mkChunk (-24) (CVal 8 (SOff 9 0)); mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-8) (CVal 8 (SOff 1 0))]) /\
nth_error (ss_mem ss_cE) 8 = Some R_errno /\ sr_get (ss_regs ss_cE) 10 = SOff 36 0).
{ vm_compute. repeat split; reflexivity. }
destruct MEM5 as (M0 & M5 & M6 & M7 & M1 & M8 & R10).
destruct (post_C B X R U L A mem md HI XC AMA BND MID src0_ENC src0_ENS src0_ERRIMG src0_SNC Hamc sp (ms_mem ms5) md) as (MID' & AMA' & BND' & NZ & NM);
[rewrite AMS_eq; unfold AMS; lia | exact F5 | | | | reflexivity | reflexivity | reflexivity | reflexivity |].
-
change (ctx11 B L (ms_mem ms5) (take_st (set_init_done true A))) with (ctx11 B L (ms_mem ms5) A').
assert (Famv : amv A' = VP (padd m META_SIZE)).
{ unfold amv. change (st_areas A') with (st_areas A). destruct (st_areas A); [exfalso; exact (Hne eq_refl) | reflexivity]. }
assert (Famav : amav A' = amav A) by reflexivity.
unfold ctx11. rewrite Famv, Famav. change (st_init_done A') with true. change (st_free_meta_head A') with (st_free_meta_head A). rewrite Efh.
change (st_avail_meta_count A') with (st_avail_meta_count A - 1). change (st_avail_meta_area_count A') with (st_avail_meta_area_count A).
change (st_meta_alloc_shift A') with (st_meta_alloc_shift A). change (st_area_head A') with (st_area_head A).
change (st_area_tail A') with (st_area_tail A). change (brkv A') with (brkv A).
cbn [sval_num onum]. change (loc_addr L (LMem (padd m META_SIZE))) with (ptr_addr L (padd m META_SIZE)). rewrite ptr_addr_padd.
Ltac cw HS M sv := apply (word_of_chunk _ _ _ _ _ _ sv _ HS M eq_refl); [cbn; tauto |].
split; [cw HS5 M5 (SOff 0 0); exact (sv_sec E _ HA ltac:(lia))|].
split; [intros kk Hkk; apply (w4_of_chunk E ss_cE ms5 5 _ (CTX + 8) (SLit 1) 1 HS5 M5 eq_refl); [cbn; tauto | reflexivity | lia | exact Hkk] |].
split; [cw HS5 M6 (SOff 33 0); rewrite (sv_off E 33 0 0 E33); reflexivity|].
split; [cw HS5 M6 (SOff 36 40); rewrite (sv_off E 36 40 _ E36); unfold META_SIZE; reflexivity|].
split; [cw HS5 M6 (SOff 37 (-1)); rewrite (sv_off E 37 (-1) _ E37); f_equal; lia|].
split; [cw HS5 M6 (SOff 38 0); rewrite (sv_off E 38 0 _ (agree_cx E 38 HA ltac:(lia))); f_equal; cbn [cx]; lia|].
split; [cw HS5 M6 (SOff 39 0); rewrite (sv_off E 39 0 _ (agree_cx E 39 HA ltac:(lia))); f_equal; cbn [cx]; lia|].
split; [cw HS5 M6 (SOff 40 0); rewrite (sv_off E 40 0 _ (agree_cx E 40 HA ltac:(lia))); f_equal; cbn [cx]; lia|].
split; [cw HS5 M6 (SOff 41 0); rewrite (sv_off E 41 0 _ (agree_cx E 41 HA ltac:(lia))); f_equal; cbn [cx]; lia|].
split; [cw HS5 M6 (SOff 42 0); rewrite (sv_off E 42 0 _ (agree_cx E 42 HA ltac:(lia))); f_equal; cbn [cx]; lia|].
cw HS5 M7 (SOff 43 0); rewrite (sv_off E 43 0 _ (agree_cx E 43 HA ltac:(lia))); f_equal; cbn [cx]; lia.
-   intros k Hk. fold m. change (ms_segs B) with src0segs. destruct (Nat.lt_ge_cases k 8).
+ rewrite <- U36. replace (bv_unsigned (ew E 36) + Z.of_nat k) with (bv_unsigned (ew E 36) + 0 + Z.of_nat k) by lia.
apply (zword_of_chunk_at E ss_cE ms5 0 _ 36%nat 0 HS5 M0 eq_refl); [cbn; tauto | lia].
+ rewrite <- U36. replace (bv_unsigned (ew E 36) + Z.of_nat k) with (bv_unsigned (ew E 36) + 8 + (Z.of_nat k - 8)) by lia.
apply (zword_of_chunk_at E ss_cE ms5 0 _ 36%nat 8 HS5 M0 eq_refl); [cbn; tauto | lia].
-   intros x Hx. fold m in Hx. apply writable_off_img_present; [lia | | apply (writable_of_region E ss_cE ms5 0 _ x HS5 M0); cbn [r_base r_wlo r_whi base_val]; rewrite U36; lia].
intros Hi. destruct (OFF _ x Hlast (INPAGE x Hx)) as [NI _]. exact (NI (in_img1_img x Hi)).
-
exists L, (ms_regs ms5), (ms_mem ms5), md. cbn [fst snd].
split; [rewrite E1; reflexivity|].
split; [| split; [exact AMA' | split; [exact BND' | split; [| exact NZ]]]].
+ split; [exact MID'|]. split; [apply layout_le_refl|]. split; [exact PRS|]. split; [exists (m_vmmaps md); apply with_vmmaps_self; assumption|]. split.
* intros x Hx Nc Nn Ns. apply (F5 x Hx). intros [Hs|[Hc|Hm]].
-- apply Ns. unfold spZ. fold sp. exact Hs.
-- apply Nc. rewrite B_ctx. unfold ctxW in Hc. rewrite B_ctx in Hc. unfold CTX_SIZE. lia.
-- exact (Nn (NM x Hm)).
* rewrite B_segs. unfold spZ. fold sp. apply (scratch_writable E ss_cE ms5 1 8 _ HS5 HA M1 eq_refl eq_refl eq_refl M8).
+ rewrite (reg_off E ss_cE ms5 10 36 0 HS5 R10). rewrite U36. f_equal. lia.
Qed.
End w.
Lemma key_page : forall q, In q (keys A) -> exists a k, In a (st_areas A) /\ 0 <= k < METAS_PER_AREA /\ q = slot_of a k /\
ptr_addr L q = ptr_addr L a + AREA_HDR + META_SIZE * k /\
(forall x, ptr_addr L q <= x < ptr_addr L q + META_SIZE -> ptr_addr L a <= x < ptr_addr L a + PGSZ).
Proof.
intros q Hq. pose proof (inv_keys HI) as (_ & KP & _ & _ & Kc). destruct (KP q Hq) as (a & k & Ha & Hk & ->).
assert (Hk' : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk; destruct (sptr_eqb a _); lia).
exists a, k. split; [exact Ha|]. split; [exact Hk'|]. split; [reflexivity|]. unfold slot_of. rewrite ptr_addr_padd.
split; [lia|]. intros x Hx. unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia.
Qed.
Lemma keys_apart : forall p q, In p (keys A) -> In q (keys A) -> p <> q ->
ptr_addr L p + META_SIZE <= ptr_addr L q \/ ptr_addr L q + META_SIZE <= ptr_addr L p.
Proof.
intros p q Hp Hq Hne.
destruct (key_page p Hp) as (a & k & Ha & Hk & Ep & Ap & Pp). destruct (key_page q Hq) as (a' & k' & Ha' & Hk' & Eq & Aq & Pq).
destruct (sptr_eq_dec a a') as [<-|Hna].
- assert (k <> k') by (intros <-; apply Hne; rewrite Ep, Eq; reflexivity). unfold META_SIZE in *. nia.
- pose proof (areas_pages_disjoint B L A mem md MID a a' Ha Ha' Hna) as D.
pose proof (Pp (ptr_addr L p) ltac:(unfold META_SIZE; lia)). pose proof (Pq (ptr_addr L q) ltac:(unfold META_SIZE; lia)).
unfold META_SIZE, AREA_HDR, METAS_PER_AREA, PGSZ in *. lia.
Qed.
Lemma key_cells : forall q, In q (keys A) ->
word_mem src0segs mem (ptr_addr L q) (sval_num L (lnk_prev (MT A q))) /\
word_mem src0segs mem (ptr_addr L q + 8) (sval_num L (lnk_next (MT A q))).
Proof.
intros q Hq. destruct (key_page q Hq) as (a & k & Ha & Hk & Eq & _ & _).
assert (IMG : forall c, In c (meta_slot_cells q (MT A q)) -> In c (image A)).
{ intros c Hc. unfold image. rewrite !in_app_iff. right. left. rewrite Eq in Hc. exact (slot_cells_in_areas A (st_areas A) a k c Ha Hk Hc). }
assert (C2 : In (MCell (LMem (padd q META_prev)) 8 (lnk_prev (MT A q))) (meta_slot_cells q (MT A q)) /\
In (MCell (LMem (padd q META_next)) 8 (lnk_next (MT A q))) (meta_slot_cells q (MT A q))).
{ unfold lnk_prev, lnk_next. destruct (MT A q) as [[pr nx| |am]|]; cbn; auto. }
destruct C2 as [C1 C2].
assert (NV : forall x z, lnk_prev x <> VLo5 z /\ lnk_next x <> VLo5 z).
{ intros [[pr nx| |am]|] z; cbn; split; try discriminate.
- destruct pr; discriminate. - destruct nx; discriminate.
- destruct (am_prev am); discriminate. - destruct (am_next am); discriminate. }
split.
- pose proof (memrep_cell B L A mem _ MR (IMG _ C1)) as C. unfold cell_mem in C. cbn [mc_loc mc_w mc_val] in C.
change (loc_addr L (LMem (padd q META_prev))) with (ptr_addr L (padd q META_prev)) in C. rewrite ptr_addr_padd in C. unfold META_prev in C. rewrite Z.add_0_r in C.
destruct (lnk_prev (MT A q)) as [z|p'|z|] eqn:El; try exact C. exfalso. exact (proj1 (NV (MT A q) z) El).
- pose proof (memrep_cell B L A mem _ MR (IMG _ C2)) as C. unfold cell_mem in C. cbn [mc_loc mc_w mc_val] in C.
change (loc_addr L (LMem (padd q META_next))) with (ptr_addr L (padd q META_next)) in C. rewrite ptr_addr_padd in C. unfold META_next in C.
destruct (lnk_next (MT A q)) as [z|p'|z|] eqn:El; try exact C. exfalso. exact (proj2 (NV (MT A q) z) El).
Qed.
Lemma key_range : forall q x, In q (keys A) -> ptr_addr L q <= x < ptr_addr L q + META_SIZE ->
~ in_img B x /\ 4096 <= x < alloc_ceiling /\ ~ WF0 B sp x /\ present mem x.
Proof.
intros q x Hq Hx. destruct (key_page q Hq) as (a & k & Ha & Hk & Eq & _ & Pg). specialize (Pg x Hx).
pose proof (areas_off_img B X R U L A mem md HI MID a x Ha Pg) as [NI Rx].
split; [exact NI|]. split; [exact Rx|]. split.
- intros [Hs|Hc].
+ exact (scratch_not_area B X R U L A mem md HI MID src0_ERRIMG sp x a ltac:(rewrite AMS_eq; unfold AMS; pose proof pre_facts; unfold AMS in *; lia) Hs Ha Pg).
+ exact (ctxW_not_area B X R U L A mem md HI MID x a Hc Ha Pg).
- pose proof (mid_mem _ _ _ _ _ MID) as (_ & _ & FT).
assert (Hin : In (LMem a, PGSZ) (footprint A)) by (right; apply in_app_iff; left; apply in_map_iff; eexists; split; [reflexivity | exact Ha]).
pose proof (proj1 (Forall_forall _ _) FT _ Hin) as FO. cbn [foot_ok fst snd] in FO. apply FO. exact Pg.
Qed.
Lemma SK0_apart : forall E a n r,
ew E 2 = getr regs 2 -> 0 < n -> (forall x, a <= x < a + n -> ~ in_img B x /\ 4096 <= x < alloc_ceiling) ->
In (r_base r, r_lo r, r_hi r)
[(Some 2%nat, -AMS, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56);
(None, CTX, CTX + 12); (None, CTX + 16, CTX + 80); (None, CTX + 920, CTX + 928); (None, ERRNO, ERRNO + 4)] ->
a + n <= base_val E (r_base r) + r_lo r \/ base_val E (r_base r) + r_hi r <= a.
Proof.
intros E a n r HE2 Hn Hoff Hin. pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts as (_ & _ & P3 & _). unfold AMS in P3.
assert (IMG : forall lo hi, 0x1e000 <= lo -> hi <= 0x51000 -> lo < hi -> a + n <= lo \/ hi <= a).
{ intros lo hi Hlo Hhi Hlh. apply (apart_by_img a n lo hi Hn Hlh); [intros x Hx; apply src0_rwseg_img; lia | intros x Hx; exact (proj1 (Hoff x Hx))]. }
destruct (Hoff a ltac:(lia)) as [_ Ra]. destruct (Hoff (a + n - 1) ltac:(lia)) as [_ Rb].
cbn [In] in Hin. destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]];
apply (f_equal (fun t => match t with (b, lo, hi) => (b, lo, hi) end)) in H; cbn in H; injection H as E1 E2 E3;
rewrite <- E1, <- E2, <- E3; cbn [base_val]; rewrite ?HE2; fold sp;
unfold AMS, GOT, GUARD, LIBC, CTX, ERRNO, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_libc, src0_D_malloc_context, src0_tp;
rewrite ?Z.add_0_l, ?Z.add_0_r; first [lia | apply IMG; lia].
Qed.
Lemma wsub_SK0 : wsub (ss_mem ss_A2) SK0 = true /\ wsub (ss_mem (add_cond ss_fh C_fh0)) SK0 = true /\ wsub (ss_mem (add_cond ss_fh C_fh1)) SK0 = true /\
wsub (ss_mem (add_cond ss_amc C_amc1)) SK0 = true /\ wsub (ss_mem (add_cond ss_amc C_amc0)) SK0 = true /\
wsub (ss_mem (add_cond ss_aac C_aac0)) SK0 = true /\ wsub (ss_mem ss_r0) SK0 = true /\
wsub (ss_mem (add_cond ss_b0 C_bd)) SK0 = true /\ wsub (ss_mem (add_cond ss_b0 C_nbd)) SK0 = true /\
wsub (ss_mem (add_cond ss_b1 C_bn)) SK0 = true /\ wsub (ss_mem (add_cond ss_b1 C_bc)) SK0 = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma FRM_run0 : forall (W : Z -> Prop) E rs m m',
(forall x, WF0 B sp x -> W x) -> env_agree 46 E00 E ->
FRM W m -> frame_of E rs m m' -> wsub rs SK0 = true -> FRM W m'.
Proof.
intros W E rs m m' HW HA HF Hfr Hs. eapply (FRM_run W E); [exact HF | exact Hfr | exact Hs |].
intros b lo hi x Hin Hx. apply HW. exact (W0_of_SK0 E b lo hi x (agree_reg2 E HA) Hin Hx).
Qed.
Lemma reach_fh : forall c, at_st ss_A2 (WF0 B sp) md c -> SR src0segs c (at_st ss_fh (WF0 B sp) md).
Proof.
intros c (E & ms1 & -> & HS1 & HA & HF1). pose proof md_facts as (Mh & Mlz & Mmat).
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E ss_A2 ss_fh); [exact Mh | exact Mlz | exact HS1 | apply run_A2 |].
intros ms2 HS2 HF2. apply SR_ret. exists E, ms2. split; [reflexivity|]. split; [exact HS2|]. split; [exact HA|].
eapply FRM_run0; [intros x Hx; exact Hx | exact HA | exact HF1 | exact HF2 | apply (proj1 wsub_SK0)].
Qed.
Lemma reach_amc : forall c, st_free_meta_head A = None -> at_st ss_fh (WF0 B sp) md c -> SR src0segs c (at_st ss_amc (WF0 B sp) md).
Proof.
intros c Efh (E & ms1 & -> & HS1 & HA & HF1). pose proof md_facts as (Mh & Mlz & Mmat).
assert (E33 : ew E 33 = Z_to_bv 64 0) by (rewrite (agree_cx E 33 HA) by lia; cbn [cx]; rewrite Efh; reflexivity).
apply (st_ok_add_cond src0segs E ss_fh ms1 BC_EQ (SOff 33 0) (SLit 0)) in HS1; [| rewrite (sv_off E 33 0 0 E33); reflexivity].
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E (add_cond ss_fh C_fh0) ss_amc); [exact Mh | exact Mlz | exact HS1 | apply run_fh0 |].
intros ms2 HS2 HF2. apply SR_ret. exists E, ms2. split; [reflexivity|]. split; [exact HS2|]. split; [exact HA|].
eapply FRM_run0; [intros x Hx; exact Hx | exact HA | exact HF1 | exact HF2 | apply (proj1 (proj2 wsub_SK0))].
Qed.
Lemma amc_range : 0 <= st_avail_meta_count A <= METAS_PER_AREA.
Proof. pose proof (inv_keys HI) as (_ & _ & _ & _ & Hc). exact Hc. Qed.
Lemma reach_aac : forall c, st_avail_meta_count A = 0 -> at_st ss_amc (WF0 B sp) md c -> SR src0segs c (at_st ss_aac (WF0 B sp) md).
Proof.
intros c Eamc (E & ms1 & -> & HS1 & HA & HF1). pose proof md_facts as (Mh & Mlz & Mmat).
assert (E37 : ew E 37 = Z_to_bv 64 0) by (rewrite (agree_cx E 37 HA) by lia; cbn [cx]; rewrite Eamc; reflexivity).
apply (st_ok_add_cond src0segs E ss_amc ms1 BC_EQ (SOff 37 0) (SLit 0)) in HS1; [| rewrite (sv_off E 37 0 0 E37); reflexivity].
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E (add_cond ss_amc C_amc0) ss_aac); [exact Mh | exact Mlz | exact HS1 | apply run_amc0 |].
intros ms2 HS2 HF2. apply SR_ret. exists E, ms2. split; [reflexivity|]. split; [exact HS2|]. split; [exact HA|].
eapply FRM_run0; [intros x Hx; exact Hx | exact HA | exact HF1 | exact HF2 | apply (proj1 (proj2 (proj2 (proj2 (proj2 wsub_SK0)))))].
Qed.
Lemma ctx11_intro : forall E ss ms s L' iA iB iC rA rB rC (v16 v24 v32 v40 v48 v56 v64 v72 v920 : sv),
st_ok src0segs E ss ms -> sv_denot E (SOff 0 0) = Z_to_bv 64 (ly_sec L')   -> st_init_done s = true ->
nth_error (ss_mem ss) iA = Some rA -> r_base rA = None ->
In (mkChunk CTX (CVal 8 (SOff 0 0))) (r_chunks rA) -> In (mkChunk (CTX + 8) (CVal 4 (SLit 1))) (r_chunks rA) ->
nth_error (ss_mem ss) iB = Some rB -> r_base rB = None ->
In (mkChunk (CTX + 16) (CVal 8 v16)) (r_chunks rB) -> sv_denot E v16 = Z_to_bv 64 (onum L' (st_free_meta_head s)) ->
In (mkChunk (CTX + 24) (CVal 8 v24)) (r_chunks rB) -> sv_denot E v24 = Z_to_bv 64 (sval_num L' (amv s)) ->
In (mkChunk (CTX + 32) (CVal 8 v32)) (r_chunks rB) -> sv_denot E v32 = Z_to_bv 64 (st_avail_meta_count s) ->
In (mkChunk (CTX + 40) (CVal 8 v40)) (r_chunks rB) -> sv_denot E v40 = Z_to_bv 64 (st_avail_meta_area_count s) ->
In (mkChunk (CTX + 48) (CVal 8 v48)) (r_chunks rB) -> sv_denot E v48 = Z_to_bv 64 (st_meta_alloc_shift s) ->
In (mkChunk (CTX + 56) (CVal 8 v56)) (r_chunks rB) -> sv_denot E v56 = Z_to_bv 64 (onum L' (st_area_head s)) ->
In (mkChunk (CTX + 64) (CVal 8 v64)) (r_chunks rB) -> sv_denot E v64 = Z_to_bv 64 (onum L' (st_area_tail s)) ->
In (mkChunk (CTX + 72) (CVal 8 v72)) (r_chunks rB) -> sv_denot E v72 = Z_to_bv 64 (sval_num L' (amav s)) ->
nth_error (ss_mem ss) iC = Some rC -> r_base rC = None ->
In (mkChunk (CTX + 920) (CVal 8 v920)) (r_chunks rC) -> sv_denot E v920 = Z_to_bv 64 (sval_num L' (brkv s)) ->
ctx11 B L' (ms_mem ms) s.
Proof.
intros E ss ms s L' iA iB iC rA rB rC v16 v24 v32 v40 v48 v56 v64 v72 v920 HS Hsec Hinit MA BA CA0 CA8 MB BB
C16 D16 C24 D24 C32 D32 C40 D40 C48 D48 C56 D56 C64 D64 C72 D72 MC BC C920 D920.
unfold ctx11. rewrite Hinit. cbn [sval_num].
split; [exact (word_of_chunk E ss ms iA rA CTX (SOff 0 0) (ly_sec L') HS MA BA CA0 Hsec) |].
split; [intros k Hk; exact (w4_of_chunk E ss ms iA rA (CTX + 8) (SLit 1) 1 HS MA BA CA8 eq_refl ltac:(lia) k Hk) |].
split; [exact (word_of_chunk E ss ms iB rB _ _ _ HS MB BB C16 D16) |].
split; [exact (word_of_chunk E ss ms iB rB _ _ _ HS MB BB C24 D24) |].
split; [exact (word_of_chunk E ss ms iB rB _ _ _ HS MB BB C32 D32) |].
split; [exact (word_of_chunk E ss ms iB rB _ _ _ HS MB BB C40 D40) |].
split; [exact (word_of_chunk E ss ms iB rB _ _ _ HS MB BB C48 D48) |].
split; [exact (word_of_chunk E ss ms iB rB _ _ _ HS MB BB C56 D56) |].
split; [exact (word_of_chunk E ss ms iB rB _ _ _ HS MB BB C64 D64) |].
split; [exact (word_of_chunk E ss ms iB rB _ _ _ HS MB BB C72 D72) |].
exact (word_of_chunk E ss ms iC rC _ _ _ HS MC BC C920 D920).
Qed.
Lemma sv_cx : forall E n, env_agree 46 E00 E -> (32 <= n < 46)%nat -> sv_denot E (SOff n 0) = Z_to_bv 64 (cx n).
Proof. intros E n HA Hn. rewrite (sv_off E n 0 (cx n) (agree_cx E n HA Hn)). f_equal. lia. Qed.
Let HI0 : Inv X R U A0 := Inv_set_init_done X R U A HI.
Lemma onum_hd : forall (l : list sptr) d, l <> [] -> onum L (match l with [] => None | y :: _ => Some y end) = ptr_addr L (hd d l).
Proof. intros [|y l] d H; [exfalso; exact (H eq_refl) | reflexivity]. Qed.
Lemma QsD_cases : forall m l q, In q (QsD m l) -> q = m \/ q = hd m l \/ q = last l m.
Proof.
intros m l q Hq. unfold QsD in Hq. destruct Hq as [<-|Hq]; [left; reflexivity|].
destruct l as [|y l]; [destruct Hq|]. cbn [In] in Hq. destruct Hq as [<-|[<-|[]]]; [right; left | right; right]; reflexivity.
Qed.
Lemma QsD_In : forall m l, l <> [] -> In (hd m l) (QsD m l) /\ In (last l m) (QsD m l).
Proof. intros m [|y l] H; [exfalso; exact (H eq_refl)|]. unfold QsD. cbn [In]. split; [right; left | right; right; left]; reflexivity. Qed.
Section b0.
Variables (m0 : sptr) (rest : list sptr) (A1 : astate).
Hypothesis Efh : st_free_meta_head A = Some m0.
Hypothesis RING : ring_ok (flinks X A0) (Some m0) (m0 :: rest).
Hypothesis MTm : MT A0 m0 = Some (MFree (Some (last rest m0)) (Some (hd m0 rest))).
Hypothesis MEMS : forall q, In q (m0 :: rest) -> exists qp qn, MT A0 q = Some (MFree qp qn) /\ memb q X = false.
Hypothesis DP : deq_post A0 m0 rest (MFree (Some (last rest m0)) (Some (hd m0 rest))) (tt, A1).
Let nx := hd m0 rest.
Let pr := last rest m0.
Lemma d_keys : In m0 (keys A) /\ In nx (keys A) /\ In pr (keys A) /\ List.NoDup (m0 :: rest) /\
cx 33 = ptr_addr L m0 /\ cx 34 = ptr_addr L nx /\ cx 35 = ptr_addr L pr /\
(rest <> [] -> nx <> m0 /\ pr <> m0 /\ In nx rest /\ In pr rest).
Proof.
pose proof (D_facts X A m0 rest A1 RING MEMS DP) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_& QK & ND).
assert (Knx : In nx (m0 :: rest)) by (unfold nx; destruct rest; [left; reflexivity | right; left; reflexivity]).
assert (Kpr : In pr (m0 :: rest)) by (unfold pr; destruct rest as [|y r]; [left; reflexivity | right; apply In_last; discriminate]).
split; [apply QK; left; reflexivity|]. split; [apply QK; exact Knx|]. split; [apply QK; exact Kpr|]. split; [exact ND|].
cbn [cx]. rewrite Efh. unfold lnkv. rewrite Efh. change (MT A m0) with (MT A0 m0). rewrite MTm. cbn [lnk_next lnk_prev optr sval_num onum].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
intros Hne. inversion ND; subst.
assert (Inx : In nx rest) by (unfold nx; destruct rest; [exfalso; exact (Hne eq_refl) | left; reflexivity]).
assert (Ipr : In pr rest) by (unfold pr; apply In_last; exact Hne).
repeat split; try assumption; intros E1; rewrite E1 in *; contradiction.
Qed.
Lemma wsub_d0 : wsub (ss_mem ss_d0) ((Some 33%nat, 0, 16) :: SK0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wsub_d1m : wsub (ss_mem (add_cond ss_d1 C_nxm)) ((Some 33%nat, 0, 16) :: SK0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wsub_d2 : wsub (ss_mem ss_d2) ((Some 35%nat, 8, 16) :: (Some 34%nat, 0, 8) :: (Some 33%nat, 0, 16) :: SK0) = true. Proof. vm_compute. reflexivity. Qed.
Lemma d_checks : final_regs_check ss_d1E = true /\ final_regs_check ss_d2E = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma sk_fh1 : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem (add_cond ss_fh C_fh1)) =
[(Some 2%nat, -AMS, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56);
(None, CTX, CTX + 12); (None, CTX + 16, CTX + 80); (None, CTX + 920, CTX + 928); (None, ERRNO, ERRNO + 4)].
Proof. vm_compute. reflexivity. Qed.
Lemma sk_d1 : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem (add_cond ss_d1 C_nxo)) =
(Some 33%nat, 0, 16) :: [(Some 2%nat, -AMS, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56);
(None, CTX, CTX + 12); (None, CTX + 16, CTX + 80); (None, CTX + 920, CTX + 928); (None, ERRNO, ERRNO + 4)].
Proof. vm_compute. reflexivity. Qed.
Definition WDm (x : Z) : Prop :=
WF0 B sp x \/ (ptr_addr L m0 <= x < ptr_addr L m0 + 16) \/ (ptr_addr L nx <= x < ptr_addr L nx + 8) \/ (ptr_addr L pr + 8 <= x < ptr_addr L pr + 16).
Lemma WDm_WD : forall x, WDm x -> WD B L m0 rest sp x.
Proof.
intros x [[H|H]|[H|[H|H]]]; [left; exact H | right; left; exact H | right; right..].
- exists m0. split; [left; reflexivity | exact H].
- exists nx. split; [| lia]. unfold QsD, nx. destruct rest; [left; reflexivity | right; left; reflexivity].
- exists pr. split; [| lia]. unfold QsD, pr. destruct rest; [left; reflexivity | right; right; left; reflexivity].
Qed.
Theorem path_D : forall c, at_st ss_fh (WF0 B sp) md c -> SR src0segs c (POST (Some m0, A1)).
Proof.
intros c (E & ms1 & -> & HS1 & HA & HF1).
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7). unfold AMS in P3, P5.
pose proof md_facts as (Mh & Mlz & Mmat).
pose proof d_keys as (Km0 & Knx & Kpr & ND & E33v & E34v & E35v & Hrest).
pose proof (D_facts X A m0 rest A1 RING MEMS DP) as (EAr & ERg & EBk & EK & Ein & Eam & Eamc & Eaac & Esh & Ehd & Etl & Eama & Efh' & CR & QK & _).
assert (E33 : ew E 33 = Z_to_bv 64 (ptr_addr L m0)) by (rewrite (agree_cx E 33 HA) by lia; rewrite E33v; reflexivity).
assert (E34 : ew E 34 = Z_to_bv 64 (ptr_addr L nx)) by (rewrite (agree_cx E 34 HA) by lia; rewrite E34v; reflexivity).
assert (E35 : ew E 35 = Z_to_bv 64 (ptr_addr L pr)) by (rewrite (agree_cx E 35 HA) by lia; rewrite E35v; reflexivity).
pose proof (fun x Hx => key_range m0 x Km0 Hx) as Rm0. pose proof (fun x Hx => key_range nx x Knx Hx) as Rnx. pose proof (fun x Hx => key_range pr x Kpr Hx) as Rpr.
assert (C40 : META_SIZE = 40) by reflexivity.
assert (U33 : bv_unsigned (ew E 33) = ptr_addr L m0) by (rewrite E33; apply u64_of_Z; destruct (Rm0 (ptr_addr L m0) ltac:(lia)); lia).
assert (U34 : bv_unsigned (ew E 34) = ptr_addr L nx) by (rewrite E34; apply u64_of_Z; destruct (Rnx (ptr_addr L nx) ltac:(lia)); lia).
assert (U35 : bv_unsigned (ew E 35) = ptr_addr L pr) by (rewrite E35; apply u64_of_Z; destruct (Rpr (ptr_addr L pr) ltac:(lia)); lia).
destruct (key_cells m0 Km0) as [CPm CNm]. change (MT A m0) with (MT A0 m0) in CPm, CNm. rewrite MTm in CPm, CNm. cbn [lnk_prev lnk_next optr sval_num] in CPm, CNm.
destruct (Rm0 (ptr_addr L m0) ltac:(lia)) as (_ & Rg0 & _). destruct (Rnx (ptr_addr L nx) ltac:(lia)) as (_ & Rgn & _). destruct (Rpr (ptr_addr L pr) ltac:(lia)) as (_ & Rgp & _).
apply (st_ok_add_cond src0segs E ss_fh ms1 BC_NE (SOff 33 0) (SLit 0)) in HS1.
2:{ rewrite (sv_off E 33 0 _ E33). cbn [sv_denot]. rewrite branch_ne. destruct (Rm0 (ptr_addr L m0) ltac:(lia)) as (_ & Rg & _).
rewrite !u64_of_Z by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
assert (HS1' : st_ok src0segs E ss_d0 ms1).
{ apply (st_ok_add_region src0segs E (add_cond ss_fh C_fh1) ms1 R_fh HS1); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_fh]; rewrite ?U33; [lia | lia | |].
+ intros o Ho. apply present_writable. destruct (Rm0 (ptr_addr L m0 + o) ltac:(lia)) as (_ & Rg & NW & PR).
destruct PR as [b Hb]. exists b. rewrite (HF1 (ptr_addr L m0 + o) ltac:(lia) NW). exact Hb.
+ apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
* apply (chunk_ok_word src0segs E _ _ 0 (SOff 35 0) (ptr_addr L pr)); [rewrite (sv_off E 35 0 _ E35); f_equal; lia|].
intros k Hk. destruct (Rm0 (ptr_addr L m0 + Z.of_nat k) ltac:(lia)) as (_ & Rg & NW & _). unfold mbyte. rewrite Z.add_0_r. rewrite (HF1 (ptr_addr L m0 + Z.of_nat k) ltac:(lia) NW).
apply CPm. exact Hk.
* apply (chunk_ok_word src0segs E _ _ 8 (SOff 34 0) (ptr_addr L nx)); [rewrite (sv_off E 34 0 _ E34); f_equal; lia|].
intros k Hk. destruct (Rm0 (ptr_addr L m0 + 8 + Z.of_nat k) ltac:(lia)) as (_ & Rg & NW & _). unfold mbyte. rewrite (HF1 (ptr_addr L m0 + 8 + Z.of_nat k) ltac:(lia) NW).
apply CNm. exact Hk.
- apply Forall_forall. intros r Hr. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr. rewrite sk_fh1 in Hr.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_fh]. change (base_val E (Some 33%nat)) with (bv_unsigned (ew E 33)). rewrite U33, Z.add_0_r.
apply (SK0_apart E (ptr_addr L m0) 16 r (agree_reg2 E HA) ltac:(lia)); [| exact Hr].
intros x Hx. destruct (Rm0 x ltac:(lia)) as (NI & Rg & _). exact (conj NI Rg). }
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E ss_d0 ss_d1); [exact Mh | exact Mlz | exact HS1' | apply run_d0 |].
intros ms2 HS2 HF2.
assert (F2 : FRM (fun x => WF0 B sp x \/ ptr_addr L m0 <= x < ptr_addr L m0 + 16) (ms_mem ms2)).
{ eapply (FRM_run _ E); [eapply FRM_mono; [exact HF1 | intros x Hx; left; exact Hx] | exact HF2 | apply wsub_d0 |].
intros b lo hi x [Hin|Hin] Hx; [| left; exact (W0_of_SK0 E b lo hi x (agree_reg2 E HA) Hin Hx)].
injection Hin as <- <- <-. cbn [base_val] in Hx. rewrite U33 in Hx. right. lia. }
destruct (nil_or_not rest) as [Er | Hne].
-
assert (Enx : nx = m0) by (unfold nx; rewrite Er; reflexivity).
apply (st_ok_add_cond src0segs E ss_d1 ms2 BC_EQ (SOff 34 0) (SOff 33 0)) in HS2.
2:{ rewrite (sv_off E 34 0 _ E34), (sv_off E 33 0 _ E33), Enx. rewrite branch_eq. apply Z.eqb_refl. }
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E (add_cond ss_d1 C_nxm) ss_d1E); [exact Mh | exact Mlz | exact HS2 | apply run_d1m |].
intros ms3 HS3 HF3.
destruct (final_regs E ss_d1E ms3 (proj1 d_checks) HS3 HA) as (PRS & E1 & Hra & Hpc & Hrv).
apply (SR_final_ret E ss_d1E ms3 md _ HS3 Hrv Hpc Hra); [rewrite E1; exact P1 | exact Mh | exact Mlz |].
assert (F3 : FRM WDm (ms_mem ms3)).
{ eapply (FRM_run _ E); [eapply FRM_mono; [exact F2 | intros x [Hx|Hx]; [left; exact Hx | right; left; exact Hx]] | exact HF3 | apply wsub_d1m |].
intros b lo hi x [Hin|Hin] Hx; [| left; exact (W0_of_SK0 E b lo hi x (agree_reg2 E HA) Hin Hx)].
injection Hin as <- <- <-. cbn [base_val] in Hx. rewrite U33 in Hx. right. left. lia. }
assert (MEM : nth_error (ss_mem ss_d1E) 0 = Some (YP09.mkRegion (Some 33%nat) 0 16 0 16 [mkChunk 0 (CVal 8 (SLit 0)); mkChunk 8 (CVal 8 (SLit 0))]) /\
nth_error (ss_mem ss_d1E) 5 = Some (R_ctxA true) /\
nth_error (ss_mem ss_d1E) 6 = Some (YP09.mkRegion None (CTX + 16) (CTX + 80) (CTX + 16) (CTX + 80)
[mkChunk (CTX + 16) (CVal 8 (SLit 0)); mkChunk (CTX + 24) (CVal 8 (SOff 36 0));
mkChunk (CTX + 32) (CVal 8 (SOff 37 0)); mkChunk (CTX + 40) (CVal 8 (SOff 38 0));
mkChunk (CTX + 48) (CVal 8 (SOff 39 0)); mkChunk (CTX + 56) (CVal 8 (SOff 40 0));
mkChunk (CTX + 64) (CVal 8 (SOff 41 0)); mkChunk (CTX + 72) (CVal 8 (SOff 42 0))]) /\
nth_error (ss_mem ss_d1E) 7 = Some R_ctxC /\
nth_error (ss_mem ss_d1E) 1 = Some (YP09.mkRegion (Some 2%nat) (-AMS) 0 (-AMS) 0
[mkChunk (-56) (CVal 8 (SOff 32 0)); mkChunk (-48) (CVal 8 (SOff 20 0)); mkChunk (-40) (CVal 8 (SOff 19 0));
mkChunk (-32) (CVal 8 (SOff 18 0)); mkChunk (-24) (CVal 8 (SOff 9 0)); mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-8) (CVal 8 (SOff 1 0))]) /\
nth_error (ss_mem ss_d1E) 8 = Some R_errno /\ sr_get (ss_regs ss_d1E) 10 = SOff 33 0).
{ vm_compute. repeat split; reflexivity. }
destruct MEM as (M0 & M5 & M6 & M7 & M1 & M8 & R10).
destruct (post_D_core B X R U L A mem md HI XC AMA BND MID src0_ENC src0_ENS src0_ERRIMG src0_SNC m0 rest A1 RING MEMS DP sp (ms_mem ms3) md)
as (MID' & AMA' & BND' & NZ & NM);
[rewrite AMS_eq; unfold AMS; lia | intros x Hx Hn; apply (F3 x Hx); intros W; exact (Hn (WDm_WD x W)) | | | | reflexivity | reflexivity | reflexivity | reflexivity |].
+ eapply (ctx11_intro E ss_d1E ms3 A1 L 5 6 7); [exact HS3 | (eapply sv_sec; [eassumption | lia]) | exact Ein | exact M5 | reflexivity | inlist | inlist | exact M6 | reflexivity | inlist | | inlist | | inlist | | inlist | | inlist | | inlist | | inlist | | inlist | | exact M7 | reflexivity | inlist |].
* rewrite Efh', Er. reflexivity.
* rewrite (sv_cx E 36 HA ltac:(lia)). cbn [cx]. unfold amv. rewrite EAr, Eam. reflexivity.
* rewrite (sv_cx E 37 HA ltac:(lia)). cbn [cx]. rewrite Eamc. reflexivity.
* rewrite (sv_cx E 38 HA ltac:(lia)). cbn [cx]. rewrite Eaac. reflexivity.
* rewrite (sv_cx E 39 HA ltac:(lia)). cbn [cx]. rewrite Esh. reflexivity.
* rewrite (sv_cx E 40 HA ltac:(lia)). cbn [cx]. rewrite Ehd. reflexivity.
* rewrite (sv_cx E 41 HA ltac:(lia)). cbn [cx]. rewrite Etl. reflexivity.
* rewrite (sv_cx E 42 HA ltac:(lia)). cbn [cx]. unfold amav. rewrite EAr, Eama, Eaac. reflexivity.
* rewrite (sv_cx E 43 HA ltac:(lia)). cbn [cx]. unfold brkv. rewrite EBk. reflexivity.
+
intros q Hq. unfold QsD in Hq. rewrite Er in Hq. destruct Hq as [<-|[]].
destruct DP as (_ & _ & _ & S4 & _). cbn [snd] in S4. rewrite S4. cbn [with_links lnk_prev lnk_next optr].
split; unfold cell_mem; cbn [mc_loc mc_w mc_val sval_num]; intros j Hj; rewrite YN03.le_byte_0.
* change (loc_addr L (LMem (padd m0 META_prev))) with (ptr_addr L (padd m0 META_prev)). rewrite ptr_addr_padd. unfold META_prev.
rewrite <- U33. replace (bv_unsigned (ew E 33) + 0 + Z.of_nat j) with (bv_unsigned (ew E 33) + 0 + Z.of_nat j) by lia.
apply (zword_of_chunk_at E ss_d1E ms3 0 _ 33%nat 0 HS3 M0 eq_refl); [inlist | lia].
* change (loc_addr L (LMem (padd m0 META_next))) with (ptr_addr L (padd m0 META_next)). rewrite ptr_addr_padd. unfold META_next.
rewrite <- U33. apply (zword_of_chunk_at E ss_d1E ms3 0 _ 33%nat 8 HS3 M0 eq_refl); [inlist | lia].
+
intros x q Hq Hx. unfold QsD in Hq. rewrite Er in Hq. destruct Hq as [<-|[]].
apply writable_off_img_present; [destruct (Rm0 x ltac:(lia)); lia | | apply (writable_of_region E ss_d1E ms3 0 _ x HS3 M0); cbn [r_base r_wlo r_whi base_val]; rewrite U33; lia].
intros Hi. destruct (Rm0 x ltac:(lia)) as [NI _]. exact (NI (in_img1_img x Hi)).
+
exists L, (ms_regs ms3), (ms_mem ms3), md. cbn [fst snd].
split; [rewrite E1; reflexivity|].
split; [| split; [exact AMA' | split; [exact BND' | split; [| exact NZ]]]].
* split; [exact MID'|]. split; [apply layout_le_refl|]. split; [exact PRS|]. split; [exists (m_vmmaps md); apply with_vmmaps_self; assumption|]. split.
-- intros x Hx Nc Nn Ns. apply (F3 x Hx). intros [[Hs|Hc]|[Hm|[Hm|Hm]]].
** apply Ns. unfold spZ. fold sp. exact Hs.
** apply Nc. rewrite B_ctx. unfold ctxW in Hc. rewrite B_ctx in Hc. unfold CTX_SIZE. lia.
** exact (Nn (NM x m0 ltac:(left; reflexivity) Hm)).
** rewrite Enx in Hm. exact (Nn (NM x m0 ltac:(left; reflexivity) ltac:(lia))).
** unfold pr in Hm. rewrite Er in Hm. cbn [last] in Hm. exact (Nn (NM x m0 ltac:(left; reflexivity) ltac:(lia))).
-- rewrite B_segs. unfold spZ. fold sp. apply (scratch_writable E ss_d1E ms3 1 8 _ HS3 HA M1 eq_refl eq_refl eq_refl M8).
* rewrite (reg_off E ss_d1E ms3 10 33 0 HS3 R10). rewrite U33. f_equal. lia.
-
destruct (Hrest Hne) as (Nnx & Npr & Inx & Ipr).
pose proof (keys_apart nx m0 Knx Km0 Nnx) as APn. pose proof (keys_apart pr m0 Kpr Km0 Npr) as APp.
assert (APnp : nx = pr \/ ptr_addr L nx + META_SIZE <= ptr_addr L pr \/ ptr_addr L pr + META_SIZE <= ptr_addr L nx).
{ destruct (sptr_eq_dec nx pr) as [Heq|Hneq]; [left; exact Heq | right; exact (keys_apart nx pr Knx Kpr Hneq)]. }
apply (st_ok_add_cond src0segs E ss_d1 ms2 BC_NE (SOff 34 0) (SOff 33 0)) in HS2.
2:{ rewrite (sv_off E 34 0 _ E34), (sv_off E 33 0 _ E33). rewrite branch_ne, !u64_of_Z by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
assert (HS2a : st_ok src0segs E (addR R_nx (add_cond ss_d1 C_nxo)) ms2).
{ apply (st_ok_add_region src0segs E (add_cond ss_d1 C_nxo) ms2 R_nx HS2); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_nx]; rewrite ?U34; [lia | lia | | apply Forall_nil].
intros o Ho. apply present_writable. destruct (Rnx (ptr_addr L nx + o) ltac:(lia)) as (_ & Rg & NW & [b Hb]).
exists b. rewrite (F2 (ptr_addr L nx + o) ltac:(lia)); [exact Hb|]. intros [W|W]; [exact (NW W) | lia].
- apply Forall_forall. intros r Hr. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr. rewrite sk_d1 in Hr.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_nx]. change (base_val E (Some 34%nat)) with (bv_unsigned (ew E 34)). rewrite U34, Z.add_0_r.
destruct Hr as [Hr|Hr].
+ apply (f_equal (fun t => match t with (b, lo, hi) => (b, lo, hi) end)) in Hr; cbn in Hr; injection Hr as E1 E2 E3.
rewrite <- E1, <- E2, <- E3. change (base_val E (Some 33%nat)) with (bv_unsigned (ew E 33)). rewrite U33. lia.
+ apply (SK0_apart E (ptr_addr L nx) 8 r (agree_reg2 E HA) ltac:(lia)); [| exact Hr].
intros x Hx. destruct (Rnx x ltac:(lia)) as (NI & Rg & _). exact (conj NI Rg). }
assert (HS2b : st_ok src0segs E ss_d2 ms2).
{ apply (st_ok_add_region src0segs E (addR R_nx (add_cond ss_d1 C_nxo)) ms2 R_pr HS2a); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_pr]; rewrite ?U35; [lia | lia | | apply Forall_nil].
intros o Ho. apply present_writable. destruct (Rpr (ptr_addr L pr + o) ltac:(lia)) as (_ & Rg & NW & [b Hb]).
exists b. rewrite (F2 (ptr_addr L pr + o) ltac:(lia)); [exact Hb|]. intros [W|W]; [exact (NW W) | lia].
- change (ss_mem (addR R_nx (add_cond ss_d1 C_nxo))) with (R_nx :: ss_mem (add_cond ss_d1 C_nxo)).
apply Forall_cons.
+ unfold extent_disjoint. cbn [r_base r_lo r_hi R_nx R_pr base_val]. rewrite U34, U35. destruct APnp as [Enp|D]; [rewrite Enp; lia | lia].
+ apply Forall_forall. intros r Hr. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr. rewrite sk_d1 in Hr.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_pr]. change (base_val E (Some 35%nat)) with (bv_unsigned (ew E 35)). rewrite U35.
destruct Hr as [Hr|Hr].
* apply (f_equal (fun t => match t with (b, lo, hi) => (b, lo, hi) end)) in Hr; cbn in Hr; injection Hr as E1 E2 E3.
rewrite <- E1, <- E2, <- E3. change (base_val E (Some 33%nat)) with (bv_unsigned (ew E 33)). rewrite U33. lia.
* destruct (SK0_apart E (ptr_addr L pr + 8) 8 r (agree_reg2 E HA) ltac:(lia)) as [D|D]; [| exact Hr | lia | lia].
intros x Hx. destruct (Rpr x ltac:(lia)) as (NI & Rg & _). exact (conj NI Rg). }
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E ss_d2 ss_d2E); [exact Mh | exact Mlz | exact HS2b | apply run_d2 |].
intros ms3 HS3 HF3.
destruct (final_regs E ss_d2E ms3 (proj2 d_checks) HS3 HA) as (PRS & E1 & Hra & Hpc & Hrv).
apply (SR_final_ret E ss_d2E ms3 md _ HS3 Hrv Hpc Hra); [rewrite E1; exact P1 | exact Mh | exact Mlz |].
assert (F3 : FRM WDm (ms_mem ms3)).
{ eapply (FRM_run _ E); [eapply FRM_mono; [exact F2 | intros x [Hx|Hx]; [left; exact Hx | right; left; exact Hx]] | exact HF3 | apply wsub_d2 |].
intros b lo hi x [Hin|[Hin|[Hin|Hin]]] Hx; [| | | left; exact (W0_of_SK0 E b lo hi x (agree_reg2 E HA) Hin Hx)];
injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U33, ?U34, ?U35 in Hx; unfold WDm; lia. }
assert (MEM : nth_error (ss_mem ss_d2E) 2 = Some (YP09.mkRegion (Some 33%nat) 0 16 0 16 [mkChunk 0 (CVal 8 (SLit 0)); mkChunk 8 (CVal 8 (SLit 0))]) /\
nth_error (ss_mem ss_d2E) 1 = Some (YP09.mkRegion (Some 34%nat) 0 8 0 8 [mkChunk 0 (CVal 8 (SOff 35 0))]) /\
nth_error (ss_mem ss_d2E) 0 = Some (YP09.mkRegion (Some 35%nat) 8 16 8 16 [mkChunk 8 (CVal 8 (SOff 34 0))]) /\
nth_error (ss_mem ss_d2E) 7 = Some (R_ctxA true) /\
nth_error (ss_mem ss_d2E) 8 = Some (YP09.mkRegion None (CTX + 16) (CTX + 80) (CTX + 16) (CTX + 80)
[mkChunk (CTX + 16) (CVal 8 (SOff 34 0)); mkChunk (CTX + 24) (CVal 8 (SOff 36 0));
mkChunk (CTX + 32) (CVal 8 (SOff 37 0)); mkChunk (CTX + 40) (CVal 8 (SOff 38 0));
mkChunk (CTX + 48) (CVal 8 (SOff 39 0)); mkChunk (CTX + 56) (CVal 8 (SOff 40 0));
mkChunk (CTX + 64) (CVal 8 (SOff 41 0)); mkChunk (CTX + 72) (CVal 8 (SOff 42 0))]) /\
nth_error (ss_mem ss_d2E) 9 = Some R_ctxC /\
nth_error (ss_mem ss_d2E) 3 = Some (YP09.mkRegion (Some 2%nat) (-AMS) 0 (-AMS) 0
[mkChunk (-56) (CVal 8 (SOff 32 0)); mkChunk (-48) (CVal 8 (SOff 20 0)); mkChunk (-40) (CVal 8 (SOff 19 0));
mkChunk (-32) (CVal 8 (SOff 18 0)); mkChunk (-24) (CVal 8 (SOff 9 0)); mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-8) (CVal 8 (SOff 1 0))]) /\
nth_error (ss_mem ss_d2E) 10 = Some R_errno /\ sr_get (ss_regs ss_d2E) 10 = SOff 33 0).
{ vm_compute. repeat split; reflexivity. }
destruct MEM as (Mfh & Mnx & Mpr & M5 & M6 & M7 & M1 & M8 & R10).
assert (Wm0p : word_mem src0segs (ms_mem ms3) (ptr_addr L m0) 0).
{ rewrite <- U33. replace (bv_unsigned (ew E 33)) with (bv_unsigned (ew E 33) + 0) by lia. exact (word_of_chunk_at E ss_d2E ms3 2 _ 33%nat 0 (SLit 0) 0 HS3 Mfh eq_refl ltac:(inlist) eq_refl). }
assert (Wm0n : word_mem src0segs (ms_mem ms3) (ptr_addr L m0 + 8) 0).
{ rewrite <- U33. exact (word_of_chunk_at E ss_d2E ms3 2 _ 33%nat 8 (SLit 0) 0 HS3 Mfh eq_refl ltac:(inlist) eq_refl). }
assert (Wnxp : word_mem src0segs (ms_mem ms3) (ptr_addr L nx) (ptr_addr L pr)).
{ rewrite <- U34. replace (bv_unsigned (ew E 34)) with (bv_unsigned (ew E 34) + 0) by lia.
exact (word_of_chunk_at E ss_d2E ms3 1 _ 34%nat 0 (SOff 35 0) _ HS3 Mnx eq_refl ltac:(inlist) (sv_off0 E 35 _ E35)). }
assert (Wprn : word_mem src0segs (ms_mem ms3) (ptr_addr L pr + 8) (ptr_addr L nx)).
{ rewrite <- U35. exact (word_of_chunk_at E ss_d2E ms3 0 _ 35%nat 8 (SOff 34 0) _ HS3 Mpr eq_refl ltac:(inlist) (sv_off0 E 34 _ E34)). }
assert (OLD : forall q a v, In q (keys A) -> word_mem src0segs mem a v -> (forall x, a <= x < a + 8 -> ptr_addr L q <= x < ptr_addr L q + META_SIZE /\ ~ WDm x) ->
word_mem src0segs (ms_mem ms3) a v).
{ intros q a v Hq Hw Hr k Hk. destruct (Hr (a + Z.of_nat k) ltac:(lia)) as [Hx NW]. destruct (key_range q _ Hq Hx) as (_ & Rg & _).
unfold mbyte. rewrite (F3 (a + Z.of_nat k) ltac:(lia) NW). apply Hw. exact Hk. }
destruct (post_D_core B X R U L A mem md HI XC AMA BND MID src0_ENC src0_ENS src0_ERRIMG src0_SNC m0 rest A1 RING MEMS DP sp (ms_mem ms3) md)
as (MID' & AMA' & BND' & NZ & NM);
[rewrite AMS_eq; unfold AMS; lia | intros x Hx Hn; apply (F3 x Hx); intros W; exact (Hn (WDm_WD x W)) | | | | reflexivity | reflexivity | reflexivity | reflexivity |].
+ eapply (ctx11_intro E ss_d2E ms3 A1 L 7 8 9); [exact HS3 | (eapply sv_sec; [eassumption | lia]) | exact Ein | exact M5 | reflexivity | inlist | inlist | exact M6 | reflexivity | inlist | | inlist | | inlist | | inlist | | inlist | | inlist | | inlist | | inlist | | exact M7 | reflexivity | inlist |].
* rewrite Efh', (onum_hd rest m0 Hne). exact (sv_off0 E 34 _ E34).
* rewrite (sv_cx E 36 HA ltac:(lia)). cbn [cx]. unfold amv. rewrite EAr, Eam. reflexivity.
* rewrite (sv_cx E 37 HA ltac:(lia)). cbn [cx]. rewrite Eamc. reflexivity.
* rewrite (sv_cx E 38 HA ltac:(lia)). cbn [cx]. rewrite Eaac. reflexivity.
* rewrite (sv_cx E 39 HA ltac:(lia)). cbn [cx]. rewrite Esh. reflexivity.
* rewrite (sv_cx E 40 HA ltac:(lia)). cbn [cx]. rewrite Ehd. reflexivity.
* rewrite (sv_cx E 41 HA ltac:(lia)). cbn [cx]. rewrite Etl. reflexivity.
* rewrite (sv_cx E 42 HA ltac:(lia)). cbn [cx]. unfold amav. rewrite EAr, Eama, Eaac. reflexivity.
* rewrite (sv_cx E 43 HA ltac:(lia)). cbn [cx]. unfold brkv. rewrite EBk. reflexivity.
+
destruct DP as (_ & _ & _ & S4 & S5 & S6). cbn [snd] in S4, S5, S6.
assert (LNK : forall q, In q rest -> exists qp qn, MT A0 q = Some (MFree qp qn) /\
MT A1 q = Some (MFree (if sptr_eqb q nx then Some pr else qp) (if sptr_eqb q pr then Some nx else qn))).
{ intros q Hq. destruct (MEMS q (or_intror Hq)) as (qp & qn & Mq & _). exists qp, qn. split; [exact Mq|].
rewrite (S6 q _ Hq Mq). cbn [with_links links_of fst snd]. reflexivity. }
assert (CELL : forall q o v, word_mem src0segs (ms_mem ms3) (ptr_addr L q + o) (sval_num L v) -> (forall z, v <> VLo5 z) ->
cell_mem B L (ms_mem ms3) (MCell (LMem (padd q o)) 8 v)).
{ intros q o v Hw Hv. unfold cell_mem. cbn [mc_loc mc_w mc_val]. change (loc_addr L (LMem (padd q o))) with (ptr_addr L (padd q o)). rewrite ptr_addr_padd.
destruct v as [z|p'|z|]; try exact Hw. exfalso. exact (Hv z eq_refl). }
assert (C0 : META_prev = 0) by reflexivity. assert (C8 : META_next = 8) by reflexivity.
intros q Hq. apply QsD_cases in Hq. fold nx pr in Hq.
destruct Hq as [->|[->| ->]].
* rewrite S4. cbn [with_links lnk_prev lnk_next optr]. split.
-- apply (CELL m0 META_prev (VZ 0)); [rewrite C0, Z.add_0_r; exact Wm0p | discriminate].
-- apply (CELL m0 META_next (VZ 0)); [rewrite C8; exact Wm0n | discriminate].
* destruct (LNK nx Inx) as (qp & qn & Mq & M1q). rewrite M1q. rewrite sptr_eqb_refl. cbn [lnk_prev lnk_next optr]. split.
-- apply (CELL nx META_prev (VP pr)); [rewrite C0, Z.add_0_r; exact Wnxp | discriminate].
-- destruct (sptr_eqb nx pr) eqn:Enp.
++ apply sptr_eqb_eq in Enp. apply (CELL nx META_next (VP nx)); [rewrite C8 | discriminate].
cbn [sval_num]. rewrite Enp at 1. exact Wprn.
++ assert (Hnp : nx <> pr) by (intros Heq; rewrite Heq, sptr_eqb_refl in Enp; discriminate).
apply (CELL nx META_next (optr qn)); [rewrite C8 | destruct qn; discriminate].
destruct (key_cells nx Knx) as [_ CN]. change (MT A nx) with (MT A0 nx) in CN. rewrite Mq in CN. cbn [lnk_next] in CN.
apply (OLD nx _ _ Knx CN). intros x Hx. split; [lia|]. intros [W|[W|[W|W]]]; [| lia | lia | destruct APnp as [?|[?|?]]; [exact (Hnp H) | lia | lia]].
destruct (Rnx x ltac:(lia)) as (_ & _ & NW & _). exact (NW W).
* destruct (LNK pr Ipr) as (qp & qn & Mq & M1q). rewrite M1q. rewrite (sptr_eqb_refl pr). cbn [lnk_prev lnk_next optr]. split.
-- destruct (sptr_eqb pr nx) eqn:Epn.
++ apply sptr_eqb_eq in Epn. apply (CELL pr META_prev (VP pr)); [rewrite C0, Z.add_0_r | discriminate].
cbn [sval_num]. rewrite Epn at 1. exact Wnxp.
++ assert (Hpn : pr <> nx) by (intros Heq; rewrite Heq, sptr_eqb_refl in Epn; discriminate).
apply (CELL pr META_prev (optr qp)); [rewrite C0, Z.add_0_r | destruct qp; discriminate].
destruct (key_cells pr Kpr) as [CP _]. change (MT A pr) with (MT A0 pr) in CP. rewrite Mq in CP. cbn [lnk_prev] in CP.
apply (OLD pr _ _ Kpr CP). intros x Hx. split; [lia|]. intros [W|[W|[W|W]]]; [| lia | destruct APnp as [?|[?|?]]; [exact (Hpn (eq_sym H)) | lia | lia] | lia].
destruct (Rpr x ltac:(lia)) as (_ & _ & NW & _). exact (NW W).
-- apply (CELL pr META_next (VP nx)); [rewrite C8; exact Wprn | discriminate].
+
assert (PRS3 : forall q x, In q (keys A) -> ptr_addr L q <= x < ptr_addr L q + 16 -> present (ms_mem ms3) x).
{ intros q x Hq Hx. destruct (key_range q x Hq ltac:(lia)) as (NI & Rg & NW & [b Hb]).
assert (DEC : WDm x \/ ~ WDm x) by (unfold WDm, WF0, am_scratch, ctxW; lia).
destruct DEC as [W|W].
- apply writable_off_img_present; [lia | intros Hi; exact (NI (in_img1_img x Hi)) |].
destruct W as [W|[W|[W|W]]]; [exact (False_ind _ (NW W)) | | |].
+ apply (writable_of_region E ss_d2E ms3 2 _ x HS3 Mfh). cbn [r_base r_wlo r_whi base_val]. rewrite U33. lia.
+ apply (writable_of_region E ss_d2E ms3 1 _ x HS3 Mnx). cbn [r_base r_wlo r_whi base_val]. rewrite U34. lia.
+ apply (writable_of_region E ss_d2E ms3 0 _ x HS3 Mpr). cbn [r_base r_wlo r_whi base_val]. rewrite U35. lia.
- exists b. rewrite (F3 x ltac:(lia) W). exact Hb. }
intros x q Hq Hx. apply QsD_cases in Hq. fold nx pr in Hq.
destruct Hq as [->|[->| ->]]; [exact (PRS3 m0 x Km0 Hx) | exact (PRS3 nx x Knx Hx) | exact (PRS3 pr x Kpr Hx)].
+
exists L, (ms_regs ms3), (ms_mem ms3), md. cbn [fst snd].
split; [rewrite E1; reflexivity|].
split; [| split; [exact AMA' | split; [exact BND' | split; [| exact NZ]]]].
* split; [exact MID'|]. split; [apply layout_le_refl|]. split; [exact PRS|]. split; [exists (m_vmmaps md); apply with_vmmaps_self; assumption|]. split.
-- intros x Hx Nc Nn Ns. apply (F3 x Hx). intros [[Hs|Hc]|[Hm|[Hm|Hm]]].
** apply Ns. unfold spZ. fold sp. exact Hs.
** apply Nc. rewrite B_ctx. unfold ctxW in Hc. rewrite B_ctx in Hc. unfold CTX_SIZE. lia.
** exact (Nn (NM x m0 ltac:(left; reflexivity) Hm)).
** exact (Nn (NM x nx (proj1 (QsD_In m0 rest Hne)) ltac:(lia))).
** exact (Nn (NM x pr (proj2 (QsD_In m0 rest Hne)) ltac:(lia))).
-- rewrite B_segs. unfold spZ. fold sp. apply (scratch_writable E ss_d2E ms3 3 10 _ HS3 HA M1 eq_refl eq_refl eq_refl M8).
* rewrite (reg_off E ss_d2E ms3 10 33 0 HS3 R10). rewrite U33. f_equal. lia.
Qed.
End b0.
Lemma agree_step : forall k k' E1 E2 E3, env_agree k E1 E2 -> env_agree k' E2 E3 -> (k <= k')%nat -> env_agree k E1 E3.
Proof. intros k k' E1 E2 E3 H1 H2 Hk. eapply env_agree_trans; [exact H1 | eapply env_agree_le; [exact Hk | exact H2]]. Qed.
Definition absO_check (ss : sstate) (v40 v48 v920 : sv) : bool :=
ss_atoms_lt 95 ss && ss_atoms_lt 96 (absO1 ss) && ss_atoms_lt 108 (absO2 ss) && ss_atoms_lt 109 (absO3 ss) && ss_atoms_lt 110 (absO4 ss)
&& chunk_is (absO2 ss) 5 (CTX + 40) (CVal 8 v40) && chunk_is (absO3 ss) 5 (CTX + 48) (CVal 8 v48) && chunk_is (absO4 ss) 6 (CTX + 920) (CVal 8 v920)
&& sv_atoms_lt 95 v40 && sv_atoms_lt 95 v48 && sv_atoms_lt 95 v920
&& regions_wf (ss_mem (absO3 ss)) && regions_wf (ss_mem (absO4 ss)) && regions_wf (ss_mem (absO5 ss))
&& mergeb ss_O' (setfacts facts_O (absO5 ss)).
Lemma to_O : forall ss E ms v40 v48 v920 (V92 V93 V94 Pv : Z),
absO_check ss v40 v48 v920 = true ->
st_ok src0segs E ss ms -> env_agree 46 E00 E ->
getr (ms_regs ms) 9 = Z_to_bv 64 Pv -> 4096 <= Pv <= alloc_ceiling - 4096 -> Pv mod 4096 = 0 ->
sv_denot E v40 = Z_to_bv 64 V92 -> sv_denot E v48 = Z_to_bv 64 V93 -> sv_denot E v920 = Z_to_bv 64 V94 ->
ew E 37 = Z_to_bv 64 0 -> ew E 33 = Z_to_bv 64 0 ->
exists E', st_ok src0segs E' ss_O' ms /\ env_agree 46 E00 E' /\ env_agree 95 E E' /\
ew E' 95 = Z_to_bv 64 Pv /\ ew E' 108 = Z_to_bv 64 V92 /\ ew E' 109 = Z_to_bv 64 V93 /\ ew E' 110 = Z_to_bv 64 V94.
Proof.
intros ss E ms v40 v48 v920 V92 V93 V94 Pv CK HS HA R9 HPv HPal D40 D48 D920 E37 E33.
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7). unfold AMS in P3, P5.
unfold absO_check in CK. do 14 (apply andb_prop in CK as [CK ?]).
rename H into MG, H0 into WF5, H1 into WF4, H2 into WF3, H3 into AV920, H4 into AV48, H5 into AV40, H6 into CI920, H7 into CI48, H8 into CI40,
H9 into AT4, H10 into AT3, H11 into AT2, H12 into AT1.
assert (NZ1 : forallb (fun r : reg => negb (bv_eqb r 0)) [9%bv] = true) by (vm_compute; reflexivity).
assert (NZ2 : forallb (fun r : reg => negb (bv_eqb r 0)) O_JUNK = true) by (vm_compute; reflexivity).
destruct (junk_regs_ok src0segs [9%bv] 95 E ss ms HS CK NZ1) as (E1 & HA1 & HS1).
assert (E1_79 : ew E1 95 = Z_to_bv 64 Pv).
{ pose proof (st_ok_reg src0segs E1 _ ms 9 HS1) as RR. rewrite R9 in RR.
assert (SG : sr_get (ss_regs (junk_regs [9%bv] 95 ss)) 9 = SOff 95 0).
{ clear. destruct ss as [pc0 sr sfr rs rv G]. cbn [junk_regs ss_regs ss_pc ss_fregs ss_mem ss_resv ss_facts].
do 9 (destruct sr as [|? sr]; [vm_compute; reflexivity|]). destruct sr; vm_compute; reflexivity. }
rewrite SG in RR. cbn [sv_denot] in RR. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in RR. symmetry. exact RR. }
destruct (junk_regs_ok src0segs O_JUNK 96 E1 (absO1 ss) ms HS1 AT1 NZ2) as (E2 & HA2 & HS2).
destruct (st_ok_abs_chunk src0segs 108 E2 (absO2 ss) ms 5 (CTX + 40) 8 v40 HS2 AT2 CI40 (sv_atoms_lt_mono 95 108 _ ltac:(lia) AV40) WF3) as [HS3 HA3].
set (E3 := ewset E2 108 (sv_denot E2 v40)) in *.
destruct (st_ok_abs_chunk src0segs 109 E3 (absO3 ss) ms 5 (CTX + 48) 8 v48 HS3 AT3 CI48 (sv_atoms_lt_mono 95 109 _ ltac:(lia) AV48) WF4) as [HS4 HA4].
set (E4 := ewset E3 109 (sv_denot E3 v48)) in *.
destruct (st_ok_abs_chunk src0segs 110 E4 (absO4 ss) ms 6 (CTX + 920) 8 v920 HS4 AT4 CI920 (sv_atoms_lt_mono 95 110 _ ltac:(lia) AV920) WF5) as [HS5 HA5].
set (E5 := ewset E4 110 (sv_denot E4 v920)) in *.
assert (HA15 : env_agree 95 E E5).
{ apply (agree_step 95 96 _ _ _ HA1); [| lia]. apply (agree_step 96 108 _ _ _ HA2); [| lia]. apply (agree_step 108 109 _ _ _ HA3); [| lia]. apply (agree_step 109 110 _ _ _ HA4); [exact HA5 | lia]. }
assert (HA05 : env_agree 46 E00 E5) by (apply (agree_step 46 95 _ _ _ HA HA15); lia).
assert (E5_79 : ew E5 95 = Z_to_bv 64 Pv).
{ rewrite <- E1_79. destruct HA2 as [X2 _]. destruct HA3 as [X3 _]. destruct HA4 as [X4 _]. destruct HA5 as [X5 _].
rewrite (X5 95%nat), (X4 95%nat), (X3 95%nat), (X2 95%nat) by lia. reflexivity. }
assert (E5_92 : ew E5 108 = Z_to_bv 64 V92).
{ destruct HA4 as [X4 _]. destruct HA5 as [X5 _]. rewrite (X5 108%nat), (X4 108%nat) by lia. unfold E3. cbn [ew ewset]. rewrite Nat.eqb_refl.
rewrite <- D40. apply (sv_denot_agree 95); [| exact AV40]. apply (agree_step 95 96 _ _ _ HA1 HA2). lia. }
assert (E5_93 : ew E5 109 = Z_to_bv 64 V93).
{ destruct HA5 as [X5 _]. rewrite (X5 109%nat) by lia. unfold E4. cbn [ew ewset]. rewrite Nat.eqb_refl.
rewrite <- D48. apply (sv_denot_agree 95); [| exact AV48].
apply (agree_step 95 96 _ _ _ HA1); [| lia]. apply (agree_step 96 108 _ _ _ HA2 HA3). lia. }
assert (E5_94 : ew E5 110 = Z_to_bv 64 V94).
{ unfold E5. cbn [ew ewset]. rewrite Nat.eqb_refl. rewrite <- D920. apply (sv_denot_agree 95); [| exact AV920].
apply (agree_step 95 96 _ _ _ HA1); [| lia]. apply (agree_step 96 108 _ _ _ HA2); [| lia]. apply (agree_step 108 109 _ _ _ HA3 HA4). lia. }
assert (HF : facts_ok E5 facts_O).
{ pose proof sh_range as SH. destruct HA05 as [X05 _].
unfold facts_O, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok, acond_ok, F_pg, F_sp, F_sh, C_amc0, C_fh0; cbn [af_lo af_hi af_al2 ac_c ac_a ac_b].
rewrite E5_79, (X05 2%nat), (X05 39%nat) by lia. subst E00. rewrite (E0_reg regs cx 2 ltac:(lia)), (E0_cx regs cx 39 ltac:(lia)). cbn [cx].
replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity). fold sp.
rewrite !u64_of_Z by lia. change (2 ^ 12) with 4096. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold AMS.
repeat split; try lia.
- rewrite (sv_off0 E5 37 0); [reflexivity|]. destruct HA15 as [X15 _]. rewrite (X15 37%nat) by lia. exact E37.
- rewrite (sv_off0 E5 33 0); [reflexivity|]. destruct HA15 as [X15 _]. rewrite (X15 33%nat) by lia. exact E33. }
pose proof (st_ok_setfacts src0segs E5 (absO5 ss) ms facts_O HS5 HF) as HS6.
pose proof (st_ok_merge src0segs E5 ss_O' (setfacts facts_O (absO5 ss)) ms HS6 MG) as HS7.
exists E5. split; [exact HS7|]. split; [exact HA05|]. split; [exact HA15|]. split; [exact E5_79|]. split; [exact E5_92|]. split; [exact E5_93 | exact E5_94].
Qed.
Section c0.
Variables (s3 : astate) (p : sptr) (L' : layout) (md3 : Model) (Kr : Z -> Prop).
Hypothesis OC : open_ctx B L A md s3 p L' md3 Kr.
Hypothesis Efh : st_free_meta_head A = None.
Let A' := take_st (open_st p s3).
Let m := padd p AREA_HDR.
Let P := ptr_addr L' p.
Lemma wsub_O : wsub (ss_mem ss_O) ((Some 95%nat, 0, 4096) :: SK0) = true /\ wsub (ss_mem (add_cond ss_o1 C_tl0)) ((Some 95%nat, 0, 4096) :: SK0) = true /\
wsub (ss_mem ss_o2) ((Some 41%nat, 8, 16) :: (Some 95%nat, 0, 4096) :: SK0) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma o_checks : final_regs_check ss_oE0 = true /\ final_regs_check ss_oE1 = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma sk_O' : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_O') =
[(Some 2%nat, -AMS, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56);
(None, CTX, CTX + 12); (None, CTX + 16, CTX + 80); (None, CTX + 920, CTX + 928); (None, ERRNO, ERRNO + 4)].
Proof. vm_compute. reflexivity. Qed.
Lemma sk_o1 : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem (add_cond ss_o1 C_tl1)) =
(Some 95%nat, 0, 4096) :: [(Some 2%nat, -AMS, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56);
(None, CTX, CTX + 12); (None, CTX + 16, CTX + 80); (None, CTX + 920, CTX + 928); (None, ERRNO, ERRNO + 4)].
Proof. vm_compute. reflexivity. Qed.
Definition page_region : YP09.region :=
YP09.mkRegion (Some 95%nat) 0 4096 0 4096
[mkChunk 24 (CVal 8 (SLit 0)); mkChunk 32 (CVal 8 (SLit 0)); mkChunk 16 (CVal 4 (SLit 101)); mkChunk 0 (CVal 8 (SOff 0 0));
mkChunk 8 (CZero 8); mkChunk 20 (CZero 4); mkChunk 40 (CZero 4056)].
Lemma page_bytes : forall E ss ms i,
st_ok src0segs E ss ms -> nth_error (ss_mem ss) i = Some page_region -> ew E 95 = Z_to_bv 64 P -> 0 <= P -> P + 4096 <= 2 ^ 64 ->
sv_denot E (SOff 0 0) = Z_to_bv 64 (ly_sec L)   ->
forall j, 0 <= j < PGSZ -> mbyte src0segs (ms_mem ms) (P + j) = Some (Z_to_bv 8 (pagebyte (ly_sec L) j)).
Proof.
intros E ss ms i HS Hi E79 HP0 HP1 DSEC j Hj. assert (U79 : bv_unsigned (ew E 95) = P) by (rewrite E79; apply u64_of_Z; lia).
pose proof (mid_sec _ _ _ _ _ MID) as SECR.
pose proof (st_ok_region src0segs E ss ms i page_region HS Hi) as (_ & _ & _ & CH). cbn [r_base base_val r_chunks page_region] in CH. rewrite U79 in CH.
pose proof (Forall_inv CH) as C24. apply Forall_inv_tail in CH.
pose proof (Forall_inv CH) as C32. apply Forall_inv_tail in CH.
pose proof (Forall_inv CH) as C16. apply Forall_inv_tail in CH.
pose proof (Forall_inv CH) as C0. apply Forall_inv_tail in CH.
pose proof (Forall_inv CH) as C8. apply Forall_inv_tail in CH.
pose proof (Forall_inv CH) as C20. apply Forall_inv_tail in CH.
pose proof (Forall_inv CH) as C40. clear CH.
assert (ZW : forall off k, chunk_ok src0segs E (ms_mem ms) P (mkChunk off (CVal 8 (SLit 0))) -> 0 <= k < 8 ->
mbyte src0segs (ms_mem ms) (P + off + k) = Some (Z_to_bv 8 0)).
{ intros off k Hc Hk. replace k with (Z.of_nat (Z.to_nat k)) by lia.
rewrite (chunk_bytes_cval_exact src0segs E _ P off 8 (SLit 0) 0 Hc eq_refl ltac:(lia) (Z.to_nat k) ltac:(lia)). rewrite YN03.le_byte_0. reflexivity. }
unfold pagebyte. unfold PGSZ in Hj.
destruct (Z_lt_le_dec j 16) as [A16|A16]; [| destruct (Z_lt_le_dec j 20) as [A20|A20]].
- replace ((16 <=? j) && (j <? 20)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
destruct (Z_lt_le_dec j 8).
+   replace (j <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
replace (P + j) with (P + 0 + Z.of_nat (Z.to_nat j)) by lia.
rewrite (chunk_bytes_cval_exact src0segs E _ P 0 8 (SOff 0 0) (ly_sec L) C0 DSEC ltac:(lia) (Z.to_nat j) ltac:(lia)). reflexivity.
+ replace (j <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
replace (P + j) with (P + 8 + (j - 8)) by lia. apply (chunk_bytes_czero src0segs E _ P 8 8 C8). lia.
- replace (j <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
replace ((16 <=? j) && (j <? 20)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
replace (P + j) with (P + 16 + Z.of_nat (Z.to_nat (j - 16))) by lia.
rewrite (chunk_bytes_cval_exact src0segs E _ P 16 4 (SLit 101) METAS_PER_AREA C16 eq_refl ltac:(unfold METAS_PER_AREA; lia) (Z.to_nat (j - 16)) ltac:(lia)).
reflexivity.
- replace (j <? 8) with false by (symmetry; apply Z.ltb_ge; lia).
replace ((16 <=? j) && (j <? 20)) with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
destruct (Z_lt_le_dec j 24); [| destruct (Z_lt_le_dec j 32); [| destruct (Z_lt_le_dec j 40)]].
+ replace (P + j) with (P + 20 + (j - 20)) by lia. apply (chunk_bytes_czero src0segs E _ P 20 4 C20). lia.
+ replace (P + j) with (P + 24 + (j - 24)) by lia. apply (ZW 24 (j - 24) C24). lia.
+ replace (P + j) with (P + 32 + (j - 32)) by lia. apply (ZW 32 (j - 32) C32). lia.
+ replace (P + j) with (P + 40 + (j - 40)) by lia. apply (chunk_bytes_czero src0segs E _ P 40 4056 C40). lia.
Qed.
Theorem leaf_O : forall E ms W,
st_ok src0segs E ss_O' ms -> env_agree 46 E00 E ->
ew E 95 = Z_to_bv 64 P -> ew E 108 = Z_to_bv 64 (st_avail_meta_area_count s3) ->
ew E 109 = Z_to_bv 64 (st_meta_alloc_shift s3) -> ew E 110 = Z_to_bv 64 (sval_num L' (brkv s3)) ->
(forall i, 0 <= i < PGSZ -> ms_mem ms (Z_to_bv 64 (P + i)) = Some (Z_to_bv 8 0)) ->
FRM W (ms_mem ms) -> (forall x, W x -> WO B L A p L' Kr sp x) -> (forall x, WF0 B sp x -> W x) ->
(st_areas A <> [] -> forall x, ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 8 <= x < ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 16 -> ~ W x) ->
SR src0segs (mkCfg ms md3) (fun c' => Qspec (Some m, A') -> POST (Some m, A') c').
Proof.
intros E ms W HS HA E79 E92 E93 E94 PZ HF HW HW0 TLm.
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7). unfold AMS in P3, P5.
pose proof (oc_MD3 _ _ _ _ _ _ _ _ _ OC) as (Mh3 & Mlz3 & Mmat3).
pose proof (open_page_range B L A md s3 p L' md3 Kr OC) as (Pg1 & Pg2 & Pg3 & Pg4). fold P in Pg1, Pg2, Pg3, Pg4.
assert (PG4 : PGSZ = 4096) by reflexivity.
assert (U79 : bv_unsigned (ew E 95) = P) by (rewrite E79; apply u64_of_Z; lia).
assert (E41 : ew E 41 = Z_to_bv 64 (onum L (st_area_tail A))) by (rewrite (agree_cx E 41 HA) by lia; reflexivity).
assert (HS1 : st_ok src0segs E ss_O ms).
{ apply (st_ok_add_region src0segs E ss_O' ms R_page HS); [reflexivity | |].
- apply (zregion_ok src0segs E (ms_mem ms) 95 0 4096); rewrite ?U79; [lia | lia | lia |]. intros x Hx. replace x with (P + (x - P)) by lia. apply PZ. lia.
- apply Forall_forall. intros r Hr. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr. rewrite sk_O' in Hr.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_page zregion]. change (base_val E (Some 95%nat)) with (bv_unsigned (ew E 95)). rewrite U79, Z.add_0_r.
apply (SK0_apart E P 4096 r (agree_reg2 E HA) ltac:(lia)); [| exact Hr]. intros x Hx. split; [apply Pg3; lia | lia]. }
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E ss_O ss_o1); [exact Mh3 | exact Mlz3 | exact HS1 | apply run_O |].
intros ms2 HS2 HF2.
assert (W2def : forall x, (W x \/ P <= x < P + 4096) -> WO B L A p L' Kr sp x).
{ intros x [Hx|Hx]; [exact (HW x Hx)|]. right. right. right. left. fold P. unfold PGSZ. exact Hx. }
assert (F2 : FRM (fun x => W x \/ P <= x < P + 4096) (ms_mem ms2)).
{ eapply (FRM_run _ E); [eapply FRM_mono; [exact HF | intros x Hx; left; exact Hx] | exact HF2 | apply (proj1 wsub_O) |].
intros b lo hi x [Hin|Hin] Hx; [| left; apply HW0; exact (W0_of_SK0 E b lo hi x (agree_reg2 E HA) Hin Hx)].
injection Hin as <- <- <-. cbn [base_val] in Hx. rewrite U79 in Hx. right. lia. }
pose proof (O_fields X R U L A HI s3 p L' (oc_areas _ _ _ _ _ _ _ _ _ OC) (oc_metas _ _ _ _ _ _ _ _ _ OC) (oc_init _ _ _ _ _ _ _ _ _ OC)
(oc_rest _ _ _ _ _ _ _ _ _ OC) (oc_hd _ _ _ _ _ _ _ _ _ OC) (oc_fh _ _ _ _ _ _ _ _ _ OC) (oc_LEN3 _ _ _ _ _ _ _ _ _ OC)
(oc_Lctx _ _ _ _ _ _ _ _ _ OC) (oc_Lreg _ _ _ _ _ _ _ _ _ OC) (oc_Pfresh _ _ _ _ _ _ _ _ _ OC))
as (EAr & ERg & EBk & Ein & Eam & Eamc & Eaac & Esh & Ehd & Etl & Eama & Efh' & CR & _ & _).
fold A' in EAr, ERg, EBk, Ein, Eam, Eamc, Eaac, Esh, Ehd, Etl, Eama, Efh', CR.
assert (Lsec' : ly_sec L' = ly_sec L) by exact (oc_Lsec _ _ _ _ _ _ _ _ _ OC).
assert (Famv : sval_num L' (amv A') = P + 64).
{ unfold amv. rewrite EAr, Eam. destruct (st_areas A ++ [p]) eqn:Enil; [destruct (st_areas A); discriminate|].
cbn [sval_num]. unfold m. change (ptr_addr L' (padd (padd p AREA_HDR) META_SIZE) = P + 64). rewrite !ptr_addr_padd. unfold P, AREA_HDR, META_SIZE. lia. }
assert (Famav : sval_num L' (amav A') = P + 4096).
{ unfold amav. rewrite EAr, Eama. destruct (st_areas A ++ [p]) eqn:Enil; [destruct (st_areas A); discriminate|]. cbn [andb sval_num].
change (ptr_addr L' (padd p 4096) = P + 4096). rewrite ptr_addr_padd. reflexivity. }
assert (Fbrk : brkv A' = brkv s3) by (unfold brkv; rewrite EBk; reflexivity).
assert (FIN : forall ss ms5 iP iA iB iC rB rstk istk ierr (W5 : Z -> Prop),
st_ok src0segs E ss ms5 -> final_regs_check ss = true ->
FRM W5 (ms_mem ms5) -> (forall x, W5 x -> WO B L A p L' Kr sp x) ->
nth_error (ss_mem ss) iP = Some page_region ->
nth_error (ss_mem ss) iA = Some (R_ctxA true) -> nth_error (ss_mem ss) iB = Some rB -> r_base rB = None -> nth_error (ss_mem ss) iC = Some (YP09.mkRegion None (CTX + 920) (CTX + 928) (CTX + 920) (CTX + 928) [mkChunk (CTX + 920) (CVal 8 (SOff 110 0))]) ->
In (mkChunk (CTX + 16) (CVal 8 (SOff 33 0))) (r_chunks rB) -> In (mkChunk (CTX + 24) (CVal 8 (SOff 95 64))) (r_chunks rB) ->
In (mkChunk (CTX + 32) (CVal 8 (SLit 100))) (r_chunks rB) -> In (mkChunk (CTX + 40) (CVal 8 (SOff 108 (-1)))) (r_chunks rB) ->
In (mkChunk (CTX + 48) (CVal 8 (SOff 109 0))) (r_chunks rB) -> In (mkChunk (CTX + 64) (CVal 8 (SOff 95 0))) (r_chunks rB) ->
In (mkChunk (CTX + 72) (CVal 8 (SOff 95 4096))) (r_chunks rB) ->
(exists v56, In (mkChunk (CTX + 56) (CVal 8 v56)) (r_chunks rB) /\ sv_denot E v56 = Z_to_bv 64 (onum L' (st_area_head A'))) ->
nth_error (ss_mem ss) istk = Some rstk -> r_base rstk = Some 2%nat -> r_wlo rstk = - AMS -> r_whi rstk = 0 -> nth_error (ss_mem ss) ierr = Some R_errno ->
sr_get (ss_regs ss) 10 = SOff 95 24 ->
(st_areas A <> [] -> forall k, (k < 8)%nat ->
mbyte src0segs (ms_mem ms5) (ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 8 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte P 8 k))) ->
(st_areas A <> [] -> forall x, ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 8 <= x < ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 16 -> present (ms_mem ms5) x) ->
SR src0segs (mkCfg ms5 md3) (fun c' => Qspec (Some m, A') -> POST (Some m, A') c')).
{ intros ss ms5 iP iA iB iC rB rstk istk ierr W5 HS5 CK F5 HW5 MP MA MB BB MC C16 C24 C32 C40 C48 C64 C72 (v56 & C56 & D56) Mstk Bstk Lstk Hstk Merr R10 NXT NXTP.
destruct (final_regs E ss ms5 CK HS5 HA) as (PRS & E1 & Hra & Hpc & Hrv).
apply (SR_final_ret E ss ms5 md3 _ HS5 Hrv Hpc Hra); [rewrite E1; exact P1 | exact Mh3 | exact Mlz3 |].
intros [HI' _]. cbn [fst snd] in HI'. fold A' in HI'.
destruct (post_open_ctx B X R U L A mem md HI XC AMA BND MID src0_ENC src0_ENS src0_ERRIMG src0_SNC s3 p L' md3 Kr OC HI' sp (ms_mem ms5))
as (MID' & AMA' & BND' & NZ & NMp & NMn);
[rewrite AMS_eq; unfold AMS; lia | intros x Hx Hn; apply (F5 x Hx); intros Wx; exact (Hn (HW5 x Wx)) | | | | | |].
- eapply (ctx11_intro E ss ms5 A' L' iA iB iC); [exact HS5 | (rewrite Lsec'; eapply sv_sec; [eassumption | lia]) | exact Ein | exact MA | reflexivity | cbn; tauto | cbn; tauto | exact MB | exact BB
| exact C16 | | exact C24 | | exact C32 | | exact C40 | | exact C48 | | exact C56 | exact D56 | exact C64 | | exact C72 | | exact MC | reflexivity | cbn; tauto |].
+ rewrite Efh', Efh. rewrite (sv_cx E 33 HA ltac:(lia)). cbn [cx]. rewrite Efh. reflexivity.
+ rewrite Famv. exact (sv_off E 95 64 _ E79).
+ rewrite Eamc. reflexivity.
+ rewrite Eaac. exact (sv_off E 108 (-1) _ E92).
+ rewrite Esh. exact (sv_off0 E 109 _ E93).
+ rewrite Etl. cbn [onum]. fold P. exact (sv_off0 E 95 _ E79).
+ rewrite Famav. exact (sv_off E 95 4096 _ E79).
+ rewrite Fbrk. exact (sv_off0 E 110 _ E94).
- rewrite B_segs. exact NXT.
- exact NXTP.
- rewrite B_segs. apply (page_bytes E ss ms5 iP HS5 MP E79); [lia | lia | eapply sv_sec; [eassumption | lia]].
- intros x Hx. fold P in Hx. apply writable_off_img_present; [lia | intros Hi; exact (Pg3 x Hx (in_img1_img x Hi)) |].
apply (writable_of_region E ss ms5 iP page_region x HS5 MP). cbn [r_base r_wlo r_whi base_val page_region]. rewrite U79. lia.
- exists L', (ms_regs ms5), (ms_mem ms5), md3. cbn [fst snd]. fold A'.
split; [rewrite E1; reflexivity|].
split; [| split; [exact AMA' | split; [exact BND' | split; [| exact NZ]]]].
+ split; [exact MID'|]. split; [exact (oc_layout _ _ _ _ _ _ _ _ _ OC)|]. split; [exact PRS|]. split; [exact (oc_md _ _ _ _ _ _ _ _ _ OC)|]. split.
* intros x Hx Nc Nn Ns. apply (F5 x Hx). intros Wx. destruct (HW5 x Wx) as [Hs|[Hc|[[Hne Ht]|[Hp|Hk]]]].
-- apply Ns. unfold spZ. fold sp. exact Hs.
-- apply Nc. rewrite B_ctx. unfold ctxW in Hc. rewrite B_ctx in Hc. unfold CTX_SIZE. lia.
-- exact (Nn (NMn Hne x Ht)).
-- exact (Nn (NMp x Hp)).
-- exact (Nn (oc_Kr_nonmap _ _ _ _ _ _ _ _ _ OC x Hk)).
* rewrite B_segs. unfold spZ. fold sp. apply (scratch_writable E ss ms5 istk ierr rstk HS5 HA Mstk Bstk Lstk Hstk Merr).
+ rewrite (reg_off E ss ms5 10 95 24 HS5 R10). rewrite U79. unfold m. rewrite ptr_addr_padd. reflexivity. }
destruct (nil_or_not (st_areas A)) as [EA0 | Hne].
-
assert (Etl0 : st_area_tail A = None).
{ pose proof (inv_areas HI) as (_ & _ & _ & Htl & _). rewrite Htl, EA0. reflexivity. }
apply (st_ok_add_cond src0segs E ss_o1 ms2 BC_EQ (SOff 41 0) (SLit 0)) in HS2.
2:{ rewrite (sv_off0 E 41 _ E41), Etl0. reflexivity. }
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E (add_cond ss_o1 C_tl0) ss_oE0); [exact Mh3 | exact Mlz3 | exact HS2 | apply run_tl0 |].
intros ms3 HS3 HF3.
assert (F3 : FRM (fun x => W x \/ P <= x < P + 4096) (ms_mem ms3)).
{ eapply (FRM_run _ E); [exact F2 | exact HF3 | apply (proj1 (proj2 wsub_O)) |].
intros b lo hi x [Hin|Hin] Hx; [| left; apply HW0; exact (W0_of_SK0 E b lo hi x (agree_reg2 E HA) Hin Hx)].
injection Hin as <- <- <-. cbn [base_val] in Hx. rewrite U79 in Hx. right. lia. }
assert (MEM : nth_error (ss_mem ss_oE0) 0 = Some page_region /\ nth_error (ss_mem ss_oE0) 5 = Some (R_ctxA true) /\
nth_error (ss_mem ss_oE0) 6 = Some (YP09.mkRegion None (CTX + 16) (CTX + 80) (CTX + 16) (CTX + 80)
[mkChunk (CTX + 32) (CVal 8 (SLit 100)); mkChunk (CTX + 24) (CVal 8 (SOff 95 64)); mkChunk (CTX + 64) (CVal 8 (SOff 95 0));
mkChunk (CTX + 56) (CVal 8 (SOff 95 0)); mkChunk (CTX + 72) (CVal 8 (SOff 95 4096)); mkChunk (CTX + 40) (CVal 8 (SOff 108 (-1)));
mkChunk (CTX + 16) (CVal 8 (SOff 33 0)); mkChunk (CTX + 48) (CVal 8 (SOff 109 0))]) /\
nth_error (ss_mem ss_oE0) 7 = Some (YP09.mkRegion None (CTX + 920) (CTX + 928) (CTX + 920) (CTX + 928) [mkChunk (CTX + 920) (CVal 8 (SOff 110 0))]) /\
nth_error (ss_mem ss_oE0) 1 = Some (YP09.mkRegion (Some 2%nat) (-AMS) 0 (-AMS) 0
[mkChunk (-56) (CVal 8 (SOff 32 0)); mkChunk (-48) (CVal 8 (SOff 20 0)); mkChunk (-40) (CVal 8 (SOff 19 0));
mkChunk (-32) (CVal 8 (SOff 18 0)); mkChunk (-24) (CVal 8 (SOff 9 0)); mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-8) (CVal 8 (SOff 1 0))]) /\
nth_error (ss_mem ss_oE0) 8 = Some R_errno /\ sr_get (ss_regs ss_oE0) 10 = SOff 95 24).
{ vm_compute. repeat split; reflexivity. }
destruct MEM as (MP & MA & MB & MC & Mstk & Merr & R10).
eapply (FIN ss_oE0 ms3 0%nat 5%nat 6%nat 7%nat _ _ 1%nat 8%nat _ HS3 (proj1 o_checks) F3 W2def MP MA MB eq_refl MC);
[cbn; tauto | cbn; tauto | cbn; tauto | cbn; tauto | cbn; tauto | cbn; tauto | cbn; tauto | | exact Mstk | reflexivity | reflexivity | reflexivity | exact Merr | exact R10 | | ].
+ exists (SOff 95 0). split; [cbn; tauto|]. rewrite Ehd. rewrite (proj2 (area_head_none X R U A HI) EA0). cbn [onum]. fold P. exact (sv_off0 E 95 _ E79).
+ intros Hne'. exfalso. exact (Hne' EA0).
+ intros Hne'. exfalso. exact (Hne' EA0).
-
destruct (last_area_facts B X R U L A mem md HI MID Hne) as (Hlast & Etl1 & OFFl & PRl).
set (tl := last (st_areas A) (SP 0%nat 0)) in *.
assert (U41 : bv_unsigned (ew E 41) = ptr_addr L tl).
{ rewrite E41, Etl1. cbn [onum]. apply u64_of_Z. destruct (OFFl (ptr_addr L tl) ltac:(unfold PGSZ; lia)) as [_ R1]. lia. }
apply (st_ok_add_cond src0segs E ss_o1 ms2 BC_NE (SOff 41 0) (SLit 0)) in HS2.
2:{ rewrite (sv_off0 E 41 _ E41), Etl1. cbn [onum sv_denot]. rewrite branch_ne. destruct (OFFl (ptr_addr L tl) ltac:(unfold PGSZ; lia)) as [_ R1].
rewrite !u64_of_Z by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
assert (HS2' : st_ok src0segs E ss_o2 ms2).
{ apply (st_ok_add_region src0segs E (add_cond ss_o1 C_tl1) ms2 R_tl HS2); [reflexivity | |].
- apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val R_tl]; rewrite ?U41;
[destruct (OFFl (ptr_addr L tl) ltac:(unfold PGSZ; lia)); lia | destruct (OFFl (ptr_addr L tl + 15) ltac:(unfold PGSZ; lia)); lia | | apply Forall_nil].
intros o Ho. apply present_writable. destruct (PRl (ptr_addr L tl + o) ltac:(unfold PGSZ; lia)) as [b Hb]. exists b.
rewrite (F2 (ptr_addr L tl + o)); [exact Hb | destruct (OFFl (ptr_addr L tl + o) ltac:(unfold PGSZ; lia)); lia |].
intros [Wx|Wx].
+ exact (TLm Hne (ptr_addr L tl + o) ltac:(lia) Wx).
+ pose proof (oc_Pfresh _ _ _ _ _ _ _ _ _ OC (LMem tl, PGSZ) ltac:(right; apply in_app_iff; left; apply in_map_iff; exists tl; auto)) as D.
unfold ranges_disjoint, crange in D. cbn [fst snd] in D. change (loc_addr L (LMem tl)) with (ptr_addr L tl) in D. fold P in D. unfold PGSZ in *. lia.
- apply Forall_forall. intros r Hr. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr. rewrite sk_o1 in Hr.
unfold extent_disjoint. cbn [r_base r_lo r_hi R_tl]. change (base_val E (Some 41%nat)) with (bv_unsigned (ew E 41)). rewrite U41.
destruct Hr as [Hr|Hr].
+ apply (f_equal (fun t => match t with (b, lo, hi) => (b, lo, hi) end)) in Hr; cbn in Hr; injection Hr as E1 E2 E3.
rewrite <- E1, <- E2, <- E3. change (base_val E (Some 95%nat)) with (bv_unsigned (ew E 95)). rewrite U79.
pose proof (oc_Pfresh _ _ _ _ _ _ _ _ _ OC (LMem tl, PGSZ) ltac:(right; apply in_app_iff; left; apply in_map_iff; exists tl; auto)) as D.
unfold ranges_disjoint, crange in D. cbn [fst snd] in D. change (loc_addr L (LMem tl)) with (ptr_addr L tl) in D. fold P in D. unfold PGSZ in *. lia.
+ destruct (SK0_apart E (ptr_addr L tl + 8) 8 r (agree_reg2 E HA) ltac:(lia)) as [D|D]; [| exact Hr | lia | lia].
intros x Hx. exact (OFFl x ltac:(unfold PGSZ; lia)). }
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E ss_o2 ss_oE1); [exact Mh3 | exact Mlz3 | exact HS2' | apply run_o2 |].
intros ms3 HS3 HF3.
set (W3 := fun x => (W x \/ P <= x < P + 4096) \/ ptr_addr L tl + 8 <= x < ptr_addr L tl + 16).
assert (F3 : FRM W3 (ms_mem ms3)).
{ eapply (FRM_run _ E); [eapply FRM_mono; [exact F2 | intros x Hx; left; exact Hx] | exact HF3 | apply (proj2 (proj2 wsub_O)) |].
intros b lo hi x [Hin|[Hin|Hin]] Hx; [| | left; left; apply HW0; exact (W0_of_SK0 E b lo hi x (agree_reg2 E HA) Hin Hx)];
injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U41, ?U79 in Hx; unfold W3; lia. }
assert (W3def : forall x, W3 x -> WO B L A p L' Kr sp x).
{ intros x [Hx|Hx]; [exact (W2def x Hx)|]. right. right. left. split; [exact Hne | exact Hx]. }
assert (MEM : nth_error (ss_mem ss_oE1) 1 = Some page_region /\ nth_error (ss_mem ss_oE1) 6 = Some (R_ctxA true) /\
nth_error (ss_mem ss_oE1) 7 = Some (YP09.mkRegion None (CTX + 16) (CTX + 80) (CTX + 16) (CTX + 80)
[mkChunk (CTX + 32) (CVal 8 (SLit 100)); mkChunk (CTX + 24) (CVal 8 (SOff 95 64)); mkChunk (CTX + 64) (CVal 8 (SOff 95 0));
mkChunk (CTX + 72) (CVal 8 (SOff 95 4096)); mkChunk (CTX + 40) (CVal 8 (SOff 108 (-1)));
mkChunk (CTX + 16) (CVal 8 (SOff 33 0)); mkChunk (CTX + 48) (CVal 8 (SOff 109 0)); mkChunk (CTX + 56) (CVal 8 (SOff 40 0))]) /\
nth_error (ss_mem ss_oE1) 8 = Some (YP09.mkRegion None (CTX + 920) (CTX + 928) (CTX + 920) (CTX + 928) [mkChunk (CTX + 920) (CVal 8 (SOff 110 0))]) /\
nth_error (ss_mem ss_oE1) 2 = Some (YP09.mkRegion (Some 2%nat) (-AMS) 0 (-AMS) 0
[mkChunk (-56) (CVal 8 (SOff 32 0)); mkChunk (-48) (CVal 8 (SOff 20 0)); mkChunk (-40) (CVal 8 (SOff 19 0));
mkChunk (-32) (CVal 8 (SOff 18 0)); mkChunk (-24) (CVal 8 (SOff 9 0)); mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-8) (CVal 8 (SOff 1 0))]) /\
nth_error (ss_mem ss_oE1) 9 = Some R_errno /\ sr_get (ss_regs ss_oE1) 10 = SOff 95 24 /\
nth_error (ss_mem ss_oE1) 0 = Some (YP09.mkRegion (Some 41%nat) 8 16 8 16 [mkChunk 8 (CVal 8 (SOff 95 0))])).
{ vm_compute. repeat split; reflexivity. }
destruct MEM as (MP & MA & MB & MC & Mstk & Merr & R10 & Mtl).
eapply (FIN ss_oE1 ms3 1%nat 6%nat 7%nat 8%nat _ _ 2%nat 9%nat W3 HS3 (proj2 o_checks) F3 W3def MP MA MB eq_refl MC);
[cbn; tauto | cbn; tauto | cbn; tauto | cbn; tauto | cbn; tauto | cbn; tauto | cbn; tauto | | exact Mstk | reflexivity | reflexivity | reflexivity | exact Merr | exact R10 | | ].
+ exists (SOff 40 0). split; [cbn; tauto|]. rewrite Ehd.
pose proof (inv_areas HI) as (_ & _ & Hhd & _).
destruct (st_area_head A) as [h|] eqn:Eh.
* rewrite (sv_cx E 40 HA ltac:(lia)). cbn [cx]. rewrite Eh. cbn [onum].
assert (Hha : In h (st_areas A)).
{ apply hd_error_In. symmetry. exact Hhd. }
rewrite (area_addr_old X R U L L' A HI (oc_Lctx _ _ _ _ _ _ _ _ _ OC) (oc_Lreg _ _ _ _ _ _ _ _ _ OC) h Hha). reflexivity.
* exfalso. apply Hne. apply (proj1 (area_head_none X R U A HI)). exact Eh.
+ intros _ k Hk. rewrite <- U41.
exact (word_of_chunk_at E ss_oE1 ms3 0 _ 41%nat 8 (SOff 95 0) _ HS3 Mtl eq_refl ltac:(cbn; tauto) (sv_off0 E 95 _ E79) k Hk).
+ intros _ x Hx. apply writable_off_img_present; [destruct (OFFl x ltac:(unfold PGSZ; lia)); lia | intros Hi; exact (proj1 (OFFl x ltac:(unfold PGSZ; lia)) (in_img1_img x Hi)) |].
apply (writable_of_region E ss_oE1 ms3 0 _ x HS3 Mtl). cbn [r_base r_wlo r_whi base_val]. rewrite U41. lia.
Qed.
End c0.
Definition regs_table_F (ss : sstate) : bool :=
final_regs_check ss && sv_eqb (sr_get (ss_regs ss) 10) (SLit 0).
Lemma mprotect_budget : forall Ly mdl a n A1,
ledger_ok B Ly A1 mdl -> ledger_x Ly A1 mdl -> m_vm_lazy mdl = [] -> m_vm_materialized mdl = [] ->
live_bytes A1 + 4096 <= MG_LIVE -> mprotect_budget_ok mdl a n = true.
Proof.
intros Ly mdl a n A1 LG' LX' ML MM HL. unfold mprotect_budget_ok, vm_backing_within_limit. apply Z.leb_le.
pose proof (vm_backing_used_le_maps (mprotect_model_next mdl a n)) as VB.
unfold mprotect_model_next in VB |- *. rewrite m_vm_lazy_with, m_vm_materialized_with, m_vmmaps_with in VB. specialize (VB ML MM).
rewrite m_vmmaps_with. cbn [vm_maps vm_limit] in VB |- *.
pose proof (lx_lb _ _ _ LX'). pose proof (lg_limit _ _ _ _ LG'). unfold MG_LIVE, SRC_LIM_MIN in *. lia.
Qed.
Lemma WF0_where : forall x, WF0 B sp x -> in_img B x \/ sp - AMS <= x < sp.
Proof.
intros x Hx. unfold WF0, am_scratch, ctxW in Hx. rewrite B_errno, B_ctx, AMS_eq in Hx.
destruct Hx as [[Hs|He]|Hc]; [right; exact Hs | left; apply src0_rwseg_img; unfold ERRNO, src0_tp in He; lia
| left; apply src0_rwseg_img; unfold CTX, src0_D_malloc_context in Hc; lia].
Qed.
Lemma PZ_run : forall E rs m m' Pg,
env_agree 46 E00 E -> frame_of E rs m m' -> wsub rs SK0 = true ->
(forall x, Pg <= x < Pg + 4096 -> ~ in_img B x) -> Pg + 4096 <= alloc_ceiling -> 0 <= Pg ->
(forall i, 0 <= i < PGSZ -> m (Z_to_bv 64 (Pg + i)) = Some (Z_to_bv 8 0)) ->
(forall i, 0 <= i < PGSZ -> m' (Z_to_bv 64 (Pg + i)) = Some (Z_to_bv 8 0)).
Proof.
intros E rs m m' Pg HA Hfr Hs Himg Hhi Hlo PZ i Hi. pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts as (_ & _ & P3 & _). unfold AMS in P3.
unfold PGSZ in Hi. rewrite <- (PZ i ltac:(unfold PGSZ; lia)). apply (frame_of_at E rs m m' (Pg + i) Hfr ltac:(lia)).
intros Hw. destruct (in_wrange_wsub E rs SK0 (Pg + i) Hs Hw) as (b & lo & hi & Hin & Hx).
destruct (WF0_where (Pg + i) (W0_of_SK0 E b lo hi (Pg + i) (agree_reg2 E HA) Hin Hx)) as [H|H]; [exact (Himg (Pg + i) ltac:(lia) H) | unfold AMS in H; lia].
Qed.
Lemma zeros_frame_n : forall (W : Z -> Prop) m Pg ln,
FRM W m -> 0 <= Pg -> 0 < ln < 2 ^ 64 -> Pg + ln <= 2 ^ 64 ->
FRM (fun x => W x \/ Pg <= x < Pg + ln) (apply_zeros m [(Z_to_bv 64 Pg, Z_to_bv 64 ln)]) /\
(forall i, 0 <= i < ln -> apply_zeros m [(Z_to_bv 64 Pg, Z_to_bv 64 ln)] (Z_to_bv 64 (Pg + i)) = Some (Z_to_bv 8 0)).
Proof.
intros W m Pg ln HF Hlo Hln Hhi. split.
- intros x Hx Hn. rewrite (apply_zeros1_at m Pg ln x) by lia.
replace ((Pg <=? x) && (x <? Pg + ln)) with false.
+ apply (HF x Hx). intros Hw. apply Hn. left. exact Hw.
+ symmetry. apply andb_false_iff. destruct (Z_lt_le_dec x Pg); [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge].
destruct (Z_lt_le_dec x (Pg + ln)); [exfalso; apply Hn; right; lia | lia].
- intros i Hi. rewrite (apply_zeros1_at m Pg ln (Pg + i)) by lia.
replace ((Pg <=? Pg + i) && (Pg + i <? Pg + ln)) with true; [reflexivity|]. symmetry. apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma zeros_frame : forall (W : Z -> Prop) m Pg,
FRM W m -> 0 <= Pg -> Pg + 4096 <= 2 ^ 64 ->
FRM (fun x => W x \/ Pg <= x < Pg + 4096) (apply_zeros m [(Z_to_bv 64 Pg, Z_to_bv 64 4096)]) /\
(forall i, 0 <= i < PGSZ -> apply_zeros m [(Z_to_bv 64 Pg, Z_to_bv 64 4096)] (Z_to_bv 64 (Pg + i)) = Some (Z_to_bv 8 0)).
Proof. intros W m Pg HF Hlo Hhi. exact (zeros_frame_n W m Pg 4096 HF Hlo ltac:(lia) Hhi). Qed.
Lemma last_next_not_W : forall s3 p L' md3 Kr, open_ctx B L A md s3 p L' md3 Kr ->
st_areas A <> [] -> forall x,
ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 8 <= x < ptr_addr L (last (st_areas A) (SP 0%nat 0)) + 16 ->
~ (WF0 B sp x \/ ptr_addr L' p <= x < ptr_addr L' p + 4096 \/ Kr x).
Proof.
intros s3 p L' md3 Kr OC Hne x Hx [Hw|[Hw|Hw]]; pose proof pre_facts as (_ & _ & P3 & _); unfold AMS in P3.
- destruct (last_area_facts B X R U L A mem md HI MID Hne) as (_ & _ & Hoff & _).
destruct (Hoff x ltac:(unfold PGSZ; lia)) as [Ni Nc]. destruct (WF0_where x Hw) as [H|H]; [exact (Ni H) | unfold AMS in H; lia].
- assert (Hin : In (LMem (last (st_areas A) (SP 0%nat 0)), PGSZ) (footprint A)).
{ right. apply in_app_iff. left. apply in_map_iff. exists (last (st_areas A) (SP 0%nat 0)). split; [reflexivity | apply In_last; exact Hne]. }
pose proof (oc_Pfresh _ _ _ _ _ _ _ _ _ OC _ Hin) as D. unfold ranges_disjoint, crange in D. cbn [fst snd] in D.
change (loc_addr L (LMem (last (st_areas A) (SP 0%nat 0)))) with (ptr_addr L (last (st_areas A) (SP 0%nat 0))) in D. unfold PGSZ in D. lia.
- exact (oc_Kr_area _ _ _ _ _ _ _ _ _ OC x (last (st_areas A) (SP 0%nat 0)) Hw (In_last (st_areas A) (SP 0%nat 0) Hne) ltac:(unfold PGSZ; lia)).
Qed.
Lemma brk_keep_id : forall req mdl, m_vm_lazy mdl = [] -> m_vm_materialized mdl = [] ->
brk_model req (vm_brk (m_vmmaps mdl)) mdl = mdl.
Proof.
intros req mdl Hl Hm. rewrite brk_model_keep.
transitivity (with_vmmaps (m_vmmaps mdl) mdl); [| symmetry; apply with_vmmaps_self; assumption].
f_equal. destruct (m_vmmaps mdl); reflexivity.
Qed.
Definition absV_check (two : bool) (ss : sstate) : bool :=
ss_atoms_lt 74 ss &&
(if two then chunk_is (absV1 ss) 6 (CTX + 920) (CVal 8 (SOff 43 0)) && regions_wf (ss_mem (absV2 ss)) && mergeb ss_V (setfacts facts_V (absV2 ss))
else mergeb ss_V (setfacts facts_V (absV1 ss))).
Lemma to_V : forall two ss E ms,
absV_check two ss = true -> st_ok src0segs E ss ms -> env_agree 46 E00 E ->
(two = true -> ew E 43 = Z_to_bv 64 (2 ^ 64 - 1)) ->
ew E 38 = Z_to_bv 64 0 -> ew E 37 = Z_to_bv 64 0 -> ew E 33 = Z_to_bv 64 0 ->
exists E', st_ok src0segs E' ss_V ms /\ env_agree 46 E00 E' /\ env_agree 74 E E'.
Proof.
intros two ss E ms CK HS HA E43 E38 E37 E33.
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7). unfold AMS in P3, P5.
unfold absV_check in CK. apply andb_prop in CK as [AT CK].
assert (NZ : forallb (fun r : reg => negb (bv_eqb r 0)) V_JUNK = true) by (vm_compute; reflexivity).
destruct (junk_regs_ok src0segs V_JUNK 74 E ss ms HS AT NZ) as (E1 & HA1 & HS1).
change (junk_regs V_JUNK 74 ss) with (absV1 ss) in HS1.
assert (HA01 : env_agree 46 E00 E1) by (apply (agree_step 46 74 _ _ _ HA HA1); lia).
assert (HF : facts_ok E1 facts_V).
{ pose proof sh_range as SH. destruct HA01 as [X01 _]. destruct HA1 as [X1 _].
unfold facts_V, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok, acond_ok, F_sp, F_sh, C_aac0, C_amc0, C_fh0; cbn [af_lo af_hi af_al2 ac_c ac_a ac_b].
rewrite (X01 2%nat), (X01 39%nat) by lia. subst E00. rewrite (E0_reg regs cx 2 ltac:(lia)), (E0_cx regs cx 39 ltac:(lia)). cbn [cx].
replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : reg) by (apply bv_eq; reflexivity). fold sp.
rewrite !u64_of_Z by lia. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold AMS.
repeat split; try lia.
- rewrite (sv_off0 E1 38 0); [reflexivity|]. rewrite (X1 38%nat) by lia. exact E38.
- rewrite (sv_off0 E1 37 0); [reflexivity|]. rewrite (X1 37%nat) by lia. exact E37.
- rewrite (sv_off0 E1 33 0); [reflexivity|]. rewrite (X1 33%nat) by lia. exact E33. }
exists E1. split; [| split; [exact HA01 | exact HA1]].
destruct two.
- apply andb_prop in CK as [CK MG]. apply andb_prop in CK as [CI WF].
assert (HS2 : st_ok src0segs E1 (absV2 ss) ms).
{ apply (st_ok_upd_chunk src0segs E1 (absV1 ss) ms 6 (CTX + 920) 8 (SOff 43 0) (SLit (2 ^ 64 - 1)) HS1 (chunk_is_sound _ _ _ _ CI)); [| exact WF].
rewrite (sv_off0 E1 43 (2 ^ 64 - 1)); [reflexivity|]. destruct HA1 as [X1 _]. rewrite (X1 43%nat) by lia. exact (E43 eq_refl). }
exact (st_ok_merge src0segs E1 ss_V (setfacts facts_V (absV2 ss)) ms (st_ok_setfacts src0segs E1 (absV2 ss) ms facts_V HS2 HF) MG).
- exact (st_ok_merge src0segs E1 ss_V (setfacts facts_V (absV1 ss)) ms (st_ok_setfacts src0segs E1 (absV1 ss) ms facts_V HS1 HF) CK).
Qed.
Section d0.
Hypothesis Efh : st_free_meta_head A = None.
Hypothesis Eamc : st_avail_meta_count A = 0.
Hypothesis Haac : 0 < st_avail_meta_area_count A.
Let p := st_avail_meta_areas A.
Let P := ptr_addr L p.
Let OC := open_R B X R U L A mem md HI BND MID Haac.
Lemma wsub_R : wsub (ss_mem ss_r0) SK0 = true /\ wsub (ss_mem ss_rK) SK0 = true.
Proof. vm_compute. split; reflexivity. Qed.
Lemma sk_rK : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_rK) =
[(Some 2%nat, -AMS, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56);
(None, CTX, CTX + 12); (None, CTX + 16, CTX + 80); (None, CTX + 920, CTX + 928); (None, ERRNO, ERRNO + 4)].
Proof. vm_compute. reflexivity. Qed.
Lemma rF_checks : final_regs_check ss_rFE = true /\ absO_check ss_oR (SOff 38 0) (SOff 39 0) (SOff 43 0) = true.
Proof. vm_compute. split; reflexivity. Qed.
Lemma R_facts : exists r o len rw, p = SP r o /\ region_of A r = Some (YO0i.mkRegion RkMetaRes len rw true) /\
o mod PGSZ = 0 /\ PGSZ <= o /\ o + PGSZ * st_avail_meta_area_count A = len /\ (forall x, In x rw -> x < o) /\
P = ly_reg L r + o /\ 8192 <= P /\ P + PGSZ <= alloc_ceiling /\ P mod PGSZ = 0 /\ cx 42 = P /\
(forall x, P <= x < P + PGSZ -> ~ in_img B x) /\ ly_reg L r + len <= alloc_ceiling.
Proof.
destruct (resv_facts X R U A HI Haac) as (r & o & len & rw & Ep & Hr & Ho1 & Ho2 & Ho3 & Hrw).
pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID) r _ Hr eq_refl) as (Pal & Plo & Phi & Pimg). cbn [rg_len] in Phi, Pimg.
exists r, o, len, rw. assert (EP : P = ly_reg L r + o) by (unfold P, p; rewrite Ep; reflexivity).
split; [exact Ep|]. split; [exact Hr|]. split; [exact Ho1|]. split; [exact Ho2|]. split; [exact Ho3|]. split; [exact Hrw|]. split; [exact EP|].
unfold PGSZ in *. split; [lia|]. split; [nia|]. split; [rewrite EP, Z.add_mod, Pal, Ho1 by lia; reflexivity|].
split; [cbn [cx]; unfold amav; rewrite (proj2 (Z.eqb_neq (st_avail_meta_area_count A) 0) ltac:(lia)), andb_false_r; reflexivity|].
split; [| lia]. intros x Hx. apply Pimg. nia.
Qed.
Theorem path_R : forall c (K : Z -> itree astate (option sptr * astate)),
at_st ss_aac (WF0 B sp) md c ->
K 0 = IRet (None, A0) ->
(forall z, z <> 0 -> K z = IRet (Some (padd p AREA_HDR), take_st (open_st p (sR A)))) ->
SR src0segs c (fun c1 => knode src0segs c1 (KMprotect p) A0 (fun z c2 => mreal src0segs c2 (K z) (fun r c' => Qspec r -> POST r c'))).
Proof.
intros c K (E & ms & -> & HS & HA & HF) K0 K1.
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7). unfold AMS in P3, P5.
pose proof md_facts as (Mh & Mlz & Mmat).
destruct R_facts as (r & o & len & rw & Ep & Hr & Ho1 & Ho2 & Ho3 & Hrw & EP & HP1 & HP2 & HP3 & E42v & Pimg & Phi).
assert (PG4 : PGSZ = 4096) by reflexivity.
assert (E38 : ew E 38 = Z_to_bv 64 (st_avail_meta_area_count A)) by (rewrite (agree_cx E 38 HA) by lia; reflexivity).
assert (E42 : ew E 42 = Z_to_bv 64 P) by (rewrite (agree_cx E 42 HA) by lia; rewrite E42v; reflexivity).
assert (U42 : bv_unsigned (ew E 42) = P) by (rewrite E42; apply u64_of_Z; lia).
apply (st_ok_add_cond src0segs E ss_aac ms BC_NE (SOff 38 0) (SLit 0)) in HS.
2:{ rewrite (sv_off0 E 38 _ E38). cbn [sv_denot]. rewrite branch_ne.
assert (st_avail_meta_area_count A < 2 ^ 64) by (unfold PGSZ in *; lia).
rewrite !u64_of_Z by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
apply (st_ok_add_fact src0segs E _ ms 42 F_pg) in HS.
2:{ unfold afact_ok, F_pg. cbn [af_lo af_hi af_al2]. rewrite U42. change (2 ^ 12) with 4096. unfold PGSZ in *. lia. }
change (add_atom (add_cond ss_aac C_aac1) 42 F_pg) with ss_r0 in HS.
eapply (SR_run_ecall src0segs src0tbl src0tbl_ok FUEL E ss_r0 ss_rK); [exact Mh | exact Mlz | exact HS | apply run_r0 |].
intros ms1 HS1 HF1.
assert (F1 : FRM (WF0 B sp) (ms_mem ms1)) by (eapply FRM_run0; [intros x Hx; exact Hx | exact HA | exact HF | exact HF1 | apply (proj1 wsub_R)]).
destruct (st_ok_ecall_shape src0segs E ss_rK ms1 HS1 eq_refl) as (regs1 & mem1 & Hms & Hregs & Hmem & HG).
rewrite Hms. rewrite Hms in F1. cbn [ms_mem pend_at] in F1. rewrite ss_rK_pc.
assert (R10 : getr regs1 10 = Z_to_bv 64 P) by (rewrite (Hregs 10%bv); exact (sv_off0 E 42 _ E42)).
apply SR_ret.
apply (knode_mprotect src0segs regs1 (Z_to_bv 64 (src0_A_mprotect + 0x30)) mem1 (seg_rom src0segs) md A0 p).
- exact Mh. - exact Mlz.
- rewrite (Hregs 17%bv). reflexivity.
- rewrite R10, u64_of_Z by lia. unfold page_size. rewrite <- PG4. exact HP3.
- rewrite (Hregs 11%bv). reflexivity.
- rewrite R10, u64_of_Z by lia. unfold two_pow_64. lia.
- rewrite (Hregs 12%bv). reflexivity.
- rewrite R10, EP. change (Z_to_bv 64 4096) with (w64 PGSZ).
exact (proj1 (lg_noaccess _ _ _ _ (mid_ledger _ _ _ _ _ MID) r _ o Hr eq_refl eq_refl ltac:(lia) ltac:(cbn [rg_len]; nia) Ho1 ltac:(cbn [rg_rw]; intros Hin; pose proof (Hrw o Hin); lia))).
- rewrite R10, EP. change (Z_to_bv 64 4096) with (w64 PGSZ).
exact (proj2 (lg_noaccess _ _ _ _ (mid_ledger _ _ _ _ _ MID) r _ o Hr eq_refl eq_refl ltac:(lia) ltac:(cbn [rg_len]; nia) Ho1 ltac:(cbn [rg_rw]; intros Hin; pose proof (Hrw o Hin); lia))).
-
intros e He. rewrite K0. cbn [mreal].
assert (Ee : errno_ret e = Z_to_bv 64 (2 ^ 64 - 12)).
{ destruct He as [<-|[]]. unfold errno_ret. apply bv_eq. reflexivity. }
pose proof (st_ok_resume_sv src0segs E ss_rK regs1 mem1 (SLit (2 ^ 64 - 12)) (errno_ret e) Hregs Hmem HG ltac:(rewrite Ee; reflexivity)) as HS2.
change (resume ss_rK (SLit (2 ^ 64 - 12)) (ss_mem ss_rK) (ss_facts ss_rK)) with ss_rF in HS2. rewrite ss_rK_pc in HS2.
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E ss_rF ss_rFE); [exact Mh | exact Mlz | exact HS2 | apply run_rF |].
intros ms3 HS3 HF3. cbn [ms_mem mkst] in HF3.
assert (F3 : FRM (WF0 B sp) (ms_mem ms3)) by (eapply FRM_run0; [intros x Hx; exact Hx | exact HA | exact F1 | exact HF3 | apply (proj2 wsub_R)]).
destruct (final_regs E ss_rFE ms3 (proj1 rF_checks) HS3 HA) as (PRS & E1 & Hra & Hpc & Hrv).
apply (SR_final_ret E ss_rFE ms3 md _ HS3 Hrv Hpc Hra); [rewrite E1; exact P1 | exact Mh | exact Mlz |].
intros _.
assert (MEM : nth_error (ss_mem ss_rFE) 4 = Some (R_ctxA true) /\
nth_error (ss_mem ss_rFE) 5 = Some (YP09.mkRegion None (CTX + 16) (CTX + 80) (CTX + 16) (CTX + 80)
[mkChunk (CTX + 16) (CVal 8 (SOff 33 0)); mkChunk (CTX + 24) (CVal 8 (SOff 36 0));
mkChunk (CTX + 32) (CVal 8 (SOff 37 0)); mkChunk (CTX + 40) (CVal 8 (SOff 38 0));
mkChunk (CTX + 48) (CVal 8 (SOff 39 0)); mkChunk (CTX + 56) (CVal 8 (SOff 40 0));
mkChunk (CTX + 64) (CVal 8 (SOff 41 0)); mkChunk (CTX + 72) (CVal 8 (SOff 42 0))]) /\
nth_error (ss_mem ss_rFE) 6 = Some R_ctxC /\
scratch_skel ss_rFE 0 7 = true /\ sr_get (ss_regs ss_rFE) 10 = SLit 0).
{ vm_compute. repeat split; reflexivity. }
destruct MEM as (MA & MB & MC & SKL & R10').
destruct (post_fail0 B X R U L A mem md HI XC AMA BND MID src0_ENC src0_ENS src0_ERRIMG src0_SNC A0
eq_refl eq_refl eq_refl (or_introl eq_refl) ltac:(repeat split; reflexivity) eq_refl eq_refl
sp (ms_mem ms3) md) as (MID' & AMA' & BND');
[rewrite AMS_eq; unfold AMS; lia | exact F3 | | reflexivity | reflexivity | reflexivity | reflexivity |].
+ eapply (ctx11_intro E ss_rFE ms3 A0 L 4 5 6); [exact HS3 | (eapply sv_sec; [eassumption | lia]) | reflexivity | exact MA | reflexivity | cbn; tauto | cbn; tauto | exact MB | reflexivity
| cbn; tauto | | cbn; tauto | | cbn; tauto | | cbn; tauto | | cbn; tauto | | cbn; tauto | | cbn; tauto | | cbn; tauto | | exact MC | reflexivity | cbn; tauto |].
* exact (sv_cx E 33 HA ltac:(lia)).
* rewrite (sv_cx E 36 HA ltac:(lia)). reflexivity.
* rewrite (sv_cx E 37 HA ltac:(lia)). reflexivity.
* rewrite (sv_cx E 38 HA ltac:(lia)). reflexivity.
* rewrite (sv_cx E 39 HA ltac:(lia)). reflexivity.
* rewrite (sv_cx E 40 HA ltac:(lia)). reflexivity.
* rewrite (sv_cx E 41 HA ltac:(lia)). reflexivity.
* rewrite (sv_cx E 42 HA ltac:(lia)). reflexivity.
* rewrite (sv_cx E 43 HA ltac:(lia)). reflexivity.
+ exists L, (ms_regs ms3), (ms_mem ms3), md. cbn [fst snd].
split; [rewrite E1; reflexivity|].
split; [| split; [exact AMA' | split; [exact BND' | split; [| exact I]]]].
* split; [exact MID'|]. split; [apply layout_le_refl|]. split; [exact PRS|]. split; [exists (m_vmmaps md); apply with_vmmaps_self; assumption|]. split.
-- intros x Hx Nc Nn Ns. apply (F3 x Hx). intros [Hs|Hc].
** apply Ns. unfold spZ. fold sp. exact Hs.
** apply Nc. rewrite B_ctx. unfold ctxW in Hc. rewrite B_ctx in Hc. unfold CTX_SIZE. lia.
-- rewrite B_segs. unfold spZ. fold sp. exact (scratch_writable' E ss_rFE ms3 0 7 HS3 HA SKL).
* rewrite (st_ok_reg src0segs _ ss_rFE ms3 10 HS3), R10'. reflexivity.
-
intros GB. rewrite (K1 1 ltac:(lia)). cbn [mreal]. rewrite R10.
assert (Pfacts : forall x, P <= x < P + 4096 -> ~ in_img B x /\ 4096 <= x < alloc_ceiling) by (intros x Hx; split; [apply Pimg; unfold PGSZ; lia | unfold PGSZ in HP2; lia]).
assert (Hmem2 : mem_ok src0segs E (apply_zeros mem1 [(Z_to_bv 64 P, Z_to_bv 64 4096)]) (ss_mem ss_rK)).
{ apply (mem_ok_zeros_outside src0segs E mem1 (ss_mem ss_rK) P 4096 Hmem); [lia | lia | lia |].
intros r' Hr'. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite sk_rK in Hr'.
destruct (SK0_apart E P 4096 r' (agree_reg2 E HA) ltac:(lia) Pfacts Hr') as [H|H]; [right; exact H | left; exact H]. }
pose proof (st_ok_resume_sv src0segs E ss_rK regs1 _ (SLit 0) (Z_to_bv 64 0) Hregs Hmem2 HG eq_refl) as HS2.
change (resume ss_rK (SLit 0) (ss_mem ss_rK) (ss_facts ss_rK)) with ss_rO in HS2. rewrite ss_rK_pc in HS2.
assert (EMD : mprotect_model (Z_to_bv 64 P) (Z_to_bv 64 4096) md = mdR L A md) by reflexivity.
rewrite EMD. pose proof (oc_MD3 _ _ _ _ _ _ _ _ _ OC) as (Mh3 & Mlz3 & Mmat3).
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL PC_O E ss_rO ss_oR RS_running); [exact Mh3 | exact Mlz3 | exact HS2 | apply run_rO |].
intros ms2 HS3 HF3. cbn [ms_mem mkst] in HF3.
destruct (zeros_frame (WF0 B sp) mem1 P F1 ltac:(lia) ltac:(lia)) as [F2 PZ2].
set (W := fun x => WF0 B sp x \/ P <= x < P + 4096) in F2.
assert (wsub_rO : wsub (ss_mem ss_rO) SK0 = true) by exact (proj2 wsub_R).
assert (F3 : FRM W (ms_mem ms2)) by (eapply FRM_run0; [intros x Hx; left; exact Hx | exact HA | exact F2 | exact HF3 | exact wsub_rO]).
assert (PZ3 : forall i, 0 <= i < PGSZ -> ms_mem ms2 (Z_to_bv 64 (P + i)) = Some (Z_to_bv 8 0)).
{ apply (PZ_run E (ss_mem ss_rO) _ _ P HA HF3 wsub_rO); [intros x Hx; apply Pimg; unfold PGSZ; lia | unfold PGSZ in HP2; lia | lia | exact PZ2]. }
assert (R9 : getr (ms_regs ms2) 9 = Z_to_bv 64 P) by (rewrite (st_ok_reg src0segs E ss_oR ms2 9 HS3); exact (sv_off0 E 42 _ E42)).
assert (E37 : ew E 37 = Z_to_bv 64 0) by (rewrite (agree_cx E 37 HA) by lia; cbn [cx]; rewrite Eamc; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 0) by (rewrite (agree_cx E 33 HA) by lia; cbn [cx]; rewrite Efh; reflexivity).
assert (HPv : 4096 <= P <= alloc_ceiling - 4096) by (unfold PGSZ in HP2; lia).
assert (HPal : P mod 4096 = 0) by (unfold PGSZ in HP3; exact HP3).
destruct (to_O ss_oR E ms2 (SOff 38 0) (SOff 39 0) (SOff 43 0) (st_avail_meta_area_count A) (st_meta_alloc_shift A) (sval_num L (brkv A)) P
(proj2 rF_checks) HS3 HA R9 HPv HPal
(sv_cx E 38 HA ltac:(lia)) (sv_cx E 39 HA ltac:(lia)) (sv_cx E 43 HA ltac:(lia)) E37 E33)
as (E' & HS4 & HA' & HA79 & E79 & E92 & E93 & E94).
apply (leaf_O (sR A) p L (mdR L A md) (fun _ => False) OC Efh E' ms2 W HS4 HA').
+ exact E79.
+ exact E92.
+ exact E93.
+ exact E94.
+ exact PZ3.
+ exact F3.
+ intros x [[Hx|Hx]|Hx]; [left; exact Hx | right; left; exact Hx | right; right; right; left; unfold PGSZ; exact Hx].
+ intros x Hx. left. exact Hx.
+ intros Hne x Hx Wx. apply (last_next_not_W (sR A) p L (mdR L A md) (fun _ => False) OC Hne x Hx).
destruct Wx as [Hw|Hw]; [left; exact Hw | right; left; exact Hw].
-
intros (_ & Hlive & _). apply (mprotect_budget L md _ _ A (mid_ledger _ _ _ _ _ MID) (mid_ledgerx _ _ _ _ _ MID) Mlz Mmat).
unfold req_len in Hlive. change (live_bytes A0) with (live_bytes A) in Hlive. unfold PGSZ in Hlive. lia.
Qed.
End d0.
Section f0.
Variables (rb : nat) (pages : Z).
Hypothesis Efh : st_free_meta_head A = None.
Hypothesis Eamc : st_avail_meta_count A = 0.
Hypothesis Eaac : st_avail_meta_area_count A = 0.
Hypothesis Hbk : st_brk A = BrkCur rb pages.
Let p := SP rb (PGSZ * pages).
Let b := vm_brk (m_vmmaps md).
Lemma wsub_BC : wsub (ss_mem ss_cG) SK0 = true /\ wsub (ss_mem ss_cR) SK0 = true /\ wsub (ss_mem ss_cGG) SK0 = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma sk_cG : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_cG) =
[(Some 2%nat, -AMS, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56);
(None, CTX, CTX + 12); (None, CTX + 16, CTX + 80); (None, CTX + 920, CTX + 928); (None, ERRNO, ERRNO + 4)].
Proof. vm_compute. reflexivity. Qed.
Lemma bc_checks : absO_check ss_oC (SLit 1) (SOff 39 0) (SOff 43 4096) = true /\ absV_check false ss_vBC = true.
Proof. vm_compute. split; reflexivity. Qed.
Lemma BC_facts : exists rw, region_of A rb = Some (YO0i.mkRegion RkBrk (PGSZ * pages) rw true) /\ 2 <= pages /\
bv_unsigned b = ly_reg L rb + PGSZ * pages /\ ly_reg L rb = ly_brk0 L /\ cx 43 = bv_unsigned b /\ ptr_addr L p = bv_unsigned b /\
ly_reg L rb mod PGSZ = 0 /\ 4096 <= ly_reg L rb /\ ly_reg L rb + PGSZ * pages <= alloc_ceiling /\
bv_unsigned (vm_start_brk (m_vmmaps md)) <= ly_brk0 L.
Proof.
destruct (brk_facts B X R U L A mem md HI MID rb pages Hbk) as (rw & Hr & Hp2 & Hb & Hr0).
pose proof (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID) rb _ Hr eq_refl) as (Pal & Plo & Phi & Pimg). cbn [rg_len] in Phi, Pimg.
pose proof (lg_brk0 _ _ _ _ (mid_ledger _ _ _ _ _ MID)) as (B1 & B2 & B3 & B4 & B5).
exists rw. split; [exact Hr|]. split; [exact Hp2|]. split; [exact Hb|]. split; [exact Hr0|]. unfold b, p in *. unfold PGSZ in *.
split; [cbn [cx]; unfold brkv; rewrite Hbk; cbn [sval_num]; unfold ptr_addr; cbn [loc_addr]; unfold PGSZ; lia|].
split; [unfold ptr_addr; cbn [loc_addr]; lia|]. auto.
Qed.
Theorem path_BC : forall c (K : Z -> itree astate (option sptr * astate)),
at_st (add_cond ss_b1 C_bc) (WF0 B sp) md c ->
(forall c2, at_st ss_V (WF0 B sp) md c2 -> mreal src0segs c2 (K 0) (fun r c' => Qspec r -> POST r c')) ->
(forall z, z <> 0 -> K z = IRet (Some (padd p AREA_HDR), take_st (open_st p (sBC A rb pages)))) ->
SR src0segs c (fun c1 => knode src0segs c1 (KBrkGrow 1) A0 (fun z c2 => mreal src0segs c2 (K z) (fun r c' => Qspec r -> POST r c'))).
Proof.
intros c K (E & ms & -> & HS & HA & HF) K0 K1.
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7). unfold AMS in P3, P5.
pose proof md_facts as (Mh & Mlz & Mmat).
destruct BC_facts as (rw & Hr & Hp2 & Hb & Hr0 & E43v & EP & Pal & Plo & Phi & Bst).
assert (PG4 : PGSZ = 4096) by reflexivity. pose proof (u64_range b) as Ub.
assert (E43 : ew E 43 = Z_to_bv 64 (bv_unsigned b)) by (rewrite (agree_cx E 43 HA) by lia; rewrite E43v; reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 0) by (rewrite (agree_cx E 38 HA) by lia; cbn [cx]; rewrite Eaac; reflexivity).
assert (E37 : ew E 37 = Z_to_bv 64 0) by (rewrite (agree_cx E 37 HA) by lia; cbn [cx]; rewrite Eamc; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 0) by (rewrite (agree_cx E 33 HA) by lia; cbn [cx]; rewrite Efh; reflexivity).
eapply (SR_run_ecall src0segs src0tbl src0tbl_ok FUEL E (add_cond ss_b1 C_bc) ss_cG); [exact Mh | exact Mlz | exact HS | apply run_bc |].
intros ms1 HS1 HF1.
assert (F1 : FRM (WF0 B sp) (ms_mem ms1)).
{ eapply FRM_run0; [intros x Hx; exact Hx | exact HA | exact HF | exact HF1 | exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 wsub_SK0))))))))))]. }
destruct (st_ok_ecall_shape src0segs E ss_cG ms1 HS1 eq_refl) as (regs1 & mem1 & Hms & Hregs & Hmem & HG).
rewrite Hms. rewrite Hms in F1. cbn [ms_mem pend_at] in F1.
assert (R10 : getr regs1 10 = Z_to_bv 64 (bv_unsigned b + 4096)) by (rewrite (Hregs 10%bv); exact (sv_off E 43 4096 _ E43)).
assert (U10 : bv_unsigned (getr regs1 10) = bv_unsigned b + 4096) by (rewrite R10; apply u64_of_Z; lia).
apply SR_ret.
apply (knode_brk_grow src0segs regs1 (Z_to_bv 64 (ss_pc ss_cG)) mem1 (seg_rom src0segs) md A0 1).
- exact Mh. - exact Mlz.
- rewrite (Hregs 17%bv). reflexivity.
- fold b. rewrite U10. unfold PGSZ. lia.
- lia.
- fold b. lia.
- fold b. unfold page_size. rewrite Hb, <- PG4, Z.add_mod, Pal, Z.mul_comm, Z_mod_mult by lia. reflexivity.
- fold b. lia.
-
fold b. rewrite (brk_keep_id (getr regs1 10) md Mlz Mmat).
pose proof (st_ok_resume_sv src0segs E ss_cG regs1 mem1 (SOff 43 0) b Hregs Hmem HG ltac:(rewrite (sv_off0 E 43 _ E43); apply Z_to_bv_bv_unsigned)) as HS2.
change (resume ss_cG (SOff 43 0) (ss_mem ss_cG) (ss_facts ss_cG)) with ss_cR in HS2.
apply (mreal_SR_pre src0segs (K 0) _ _ (at_st ss_V (WF0 B sp) md)); [| exact K0].
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL PC_V E ss_cR ss_vBC RS_running); [exact Mh | exact Mlz | exact HS2 | apply run_cR |].
intros ms2 HS3 HF3. cbn [ms_mem mkst] in HF3.
assert (F3 : FRM (WF0 B sp) (ms_mem ms2)) by (eapply FRM_run0; [intros x Hx; exact Hx | exact HA | exact F1 | exact HF3 | exact (proj1 (proj2 wsub_BC))]).
destruct (to_V false ss_vBC E ms2 (proj2 bc_checks) HS3 HA ltac:(discriminate) E38 E37 E33) as (E' & HS4 & HA' & _).
apply SR_ret. exists E', ms2. split; [reflexivity|]. split; [exact HS4|]. split; [exact HA' | exact F3].
-
intros G. rewrite (K1 1 ltac:(lia)). cbn [mreal].
assert (Hreq0 : getr regs1 10 <> Z_to_bv 64 0) by (intros E0'; rewrite E0' in U10; change (bv_unsigned (Z_to_bv 64 0)) with 0 in U10; lia).
assert (HPal : bv_unsigned b mod 4096 = 0) by (rewrite Hb, <- PG4, Z.add_mod, Pal, Z.mul_comm, Z_mod_mult by lia; reflexivity).
fold b in G |- *.
rewrite (brk_grow_ok_unfold md (getr regs1 10) PGSZ Hreq0 ltac:(fold b; lia) ltac:(fold b; unfold page_size; exact HPal) ltac:(fold b; rewrite U10; reflexivity) ltac:(unfold PGSZ; lia) eq_refl) in G.
apply andb_prop in G as [G _]. apply andb_prop in G as [Gtop Gfree2]. apply Z.leb_le in Gtop. fold b in Gtop, Gfree2.
assert (Gfree : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) b (Z_to_bv 64 PGSZ) = true).
{ eapply region_free_prefix; [| exact Gfree2]. vm_compute. discriminate. }
assert (Gceil : bv_unsigned b + PGSZ <= alloc_ceiling).
{ apply (YM05.grant_below_ceil _ _ (lg_ceil _ _ _ _ (mid_ledger _ _ _ _ _ MID))); [| exact Gtop].
unfold PGSZ. rewrite Z.add_mod, HPal by lia. reflexivity. }
set (md' := brk_model (getr regs1 10) (getr regs1 10) md).
assert (MD' : md' = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps md)) ((b, Z_to_bv 64 PGSZ) :: vm_maps (m_vmmaps md)) (vm_noaccess (m_vmmaps md))
(vm_start_brk (m_vmmaps md)) (Z_to_bv 64 (bv_unsigned b + PGSZ)) (vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md))) md).
{ unfold md'. rewrite (brk_model_grow (getr regs1 10) md PGSZ Hreq0 ltac:(fold b; lia) ltac:(fold b; rewrite U10; reflexivity) ltac:(unfold PGSZ; lia)). fold b. rewrite R10. reflexivity. }
pose proof (open_BC B X R U L A mem md HI BND MID rb pages md' Hbk Gceil Gfree MD') as OC.
pose proof (oc_MD3 _ _ _ _ _ _ _ _ _ OC) as (Mh3 & Mlz3 & Mmat3).
assert (Pfacts : forall x, bv_unsigned b <= x < bv_unsigned b + 4096 -> ~ in_img B x /\ 4096 <= x < alloc_ceiling).
{ intros x Hx. split; [| unfold PGSZ in Gceil; lia]. intros Hi.
exact (fresh_img B L A md (mid_ledger _ _ _ _ _ MID) b PGSZ ltac:(unfold PGSZ; lia) ltac:(lia) ltac:(unfold PGSZ in *; lia) Gfree x Hi ltac:(unfold PGSZ; lia)). }
assert (Hmem2 : mem_ok src0segs E (apply_zeros mem1 [(Z_to_bv 64 (bv_unsigned b), Z_to_bv 64 4096)]) (ss_mem ss_cG)).
{ apply (mem_ok_zeros_outside src0segs E mem1 (ss_mem ss_cG) (bv_unsigned b) 4096 Hmem); [lia | lia | lia |].
intros r' Hr'. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite sk_cG in Hr'.
destruct (SK0_apart E (bv_unsigned b) 4096 r' (agree_reg2 E HA) ltac:(lia) Pfacts Hr') as [H|H]; [right; exact H | left; exact H]. }
replace (apply_zeros mem1 [(b, Z_to_bv 64 (PGSZ * 1))]) with (apply_zeros mem1 [(Z_to_bv 64 (bv_unsigned b), Z_to_bv 64 4096)])
by (rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof (st_ok_resume_sv src0segs E ss_cG regs1 _ (SOff 43 4096) (getr regs1 10) Hregs Hmem2 HG ltac:(rewrite R10; exact (sv_off E 43 4096 _ E43))) as HS2.
change (resume ss_cG (SOff 43 4096) (ss_mem ss_cG) (ss_facts ss_cG)) with ss_cGG in HS2.
change (brk_model (getr regs1 10) (getr regs1 10) md) with md'.
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL PC_O E ss_cGG ss_oC RS_running); [exact Mh3 | exact Mlz3 | exact HS2 | apply run_cGG |].
intros ms2 HS3 HF3. cbn [ms_mem mkst] in HF3.
destruct (zeros_frame (WF0 B sp) mem1 (bv_unsigned b) F1 ltac:(lia) ltac:(lia)) as [F2 PZ2].
set (W := fun x => WF0 B sp x \/ bv_unsigned b <= x < bv_unsigned b + 4096) in F2.
assert (F3 : FRM W (ms_mem ms2)) by (eapply FRM_run0; [intros x Hx; left; exact Hx | exact HA | exact F2 | exact HF3 | exact (proj2 (proj2 wsub_BC))]).
assert (PZ3 : forall i, 0 <= i < PGSZ -> ms_mem ms2 (Z_to_bv 64 (bv_unsigned b + i)) = Some (Z_to_bv 8 0)).
{ apply (PZ_run E (ss_mem ss_cGG) _ _ (bv_unsigned b) HA HF3 (proj2 (proj2 wsub_BC))); [intros x Hx; exact (proj1 (Pfacts x Hx)) | unfold PGSZ in Gceil; lia | lia | exact PZ2]. }
assert (R9 : getr (ms_regs ms2) 9 = Z_to_bv 64 (bv_unsigned b)) by (rewrite (st_ok_reg src0segs E ss_oC ms2 9 HS3); exact (sv_off0 E 43 _ E43)).
destruct (to_O ss_oC E ms2 (SLit 1) (SOff 39 0) (SOff 43 4096) 1 (st_meta_alloc_shift A) (bv_unsigned b + 4096) (bv_unsigned b)
(proj1 bc_checks) HS3 HA R9 ltac:(unfold PGSZ in Gceil; lia) HPal
eq_refl (sv_cx E 39 HA ltac:(lia)) (sv_off E 43 4096 _ E43) E37 E33) as (E' & HS4 & HA' & HA79 & E79 & E92 & E93 & E94).
apply (leaf_O (sBC A rb pages) p L md' (fun _ => False) OC Efh E' ms2 W HS4 HA').
+ rewrite EP. exact E79.
+ exact E92.
+ exact E93.
+ rewrite E94. f_equal. unfold brkv. change (st_brk (sBC A rb pages)) with (BrkCur rb (pages + 1)). cbn [sval_num]. unfold ptr_addr. cbn [loc_addr]. unfold PGSZ in *. lia.
+ intros i Hi. rewrite EP. exact (PZ3 i Hi).
+ exact F3.
+ intros x [[Hx|Hx]|Hx]; [left; exact Hx | right; left; exact Hx | right; right; right; left; rewrite EP; unfold PGSZ; exact Hx].
+ intros x Hx. left. exact Hx.
+ intros Hne x Hx Wx. apply (last_next_not_W (sBC A rb pages) p L md' (fun _ => False) OC Hne x Hx).
destruct Wx as [Hw|Hw]; [left; exact Hw | right; left; rewrite EP; exact Hw].
-
intros (Hn & _ & _). exfalso. change (st_brk A0) with (st_brk A) in Hn. rewrite Hbk in Hn. discriminate.
Qed.
End f0.
Lemma old_ptrs : forall L', ly_ctx L' = ly_ctx L -> (forall r, (r < length (st_regions A))%nat -> ly_reg L' r = ly_reg L r) ->
sval_num L' (amv A) = sval_num L (amv A) /\ onum L' (st_area_head A) = onum L (st_area_head A) /\
onum L' (st_area_tail A) = onum L (st_area_tail A).
Proof.
intros L' Lctx Lreg. pose proof (inv_areas HI) as (_ & _ & Hhd & Htl & _). destruct (inv_keys HI) as (_ & _ & _ & K4 & _).
pose proof (fun a Ha => area_addr_old X R U L L' A HI Lctx Lreg a Ha) as AO.
destruct (nil_or_not (st_areas A)) as [EA|NE].
- unfold amv. rewrite Hhd, Htl, EA. cbn. auto.
- assert (Hl : In (last (st_areas A) (SP 0%nat 0)) (st_areas A)) by (apply In_last; exact NE).
split; [| split].
+ unfold amv. rewrite (K4 NE). set (q := last (st_areas A) (SP 0%nat 0)) in *. clearbody q.
destruct (st_areas A) as [|a0 l] eqn:EA; [exfalso; exact (NE eq_refl)|]. cbn [sval_num].
change (loc_addr L' (LMem (padd q (AREA_HDR + META_SIZE * (METAS_PER_AREA - st_avail_meta_count A))))) with (ptr_addr L' (padd q (AREA_HDR + META_SIZE * (METAS_PER_AREA - st_avail_meta_count A)))).
change (loc_addr L (LMem (padd q (AREA_HDR + META_SIZE * (METAS_PER_AREA - st_avail_meta_count A))))) with (ptr_addr L (padd q (AREA_HDR + META_SIZE * (METAS_PER_AREA - st_avail_meta_count A)))).
rewrite !ptr_addr_padd, (AO q Hl). reflexivity.
+ rewrite Hhd. destruct (st_areas A) as [|a0 l] eqn:EA; [exfalso; exact (NE eq_refl)|]. cbn [hd_error onum].
change (loc_addr L' (LMem a0)) with (ptr_addr L' a0). change (loc_addr L (LMem a0)) with (ptr_addr L a0).
rewrite (AO a0 ltac:(left; reflexivity)). reflexivity.
+ rewrite Htl, (match_last (st_areas A) (SP 0%nat 0) NE). cbn [onum]. apply AO. exact Hl.
Qed.
Let NN : forall k rg, region_of A k = Some rg -> 0 <= rg_len rg := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (inv_areas HI)))))))).
Lemma resv_grant_exists : forall Xs ln, like_A0 A Xs -> mgrant Xs (KMmapNone ln) ->
exists a, place_ok (Z_to_bv 64 0) md a (page_round ln) = true.
Proof.
intros Xs ln LXs (Hpos & Hlive & Hsl & Hreq). pose proof LXs as (ER & _).
pose proof (mid_ledger _ _ _ _ _ MID) as G. pose proof (mid_ledgerx _ _ _ _ _ MID) as LX.
unfold req_len in Hpos, Hlive, Hreq. unfold MG_LIVE, MG_SLOTS, MG_REQ in *.
assert (ELB : live_bytes Xs = live_bytes A) by (unfold live_bytes; rewrite ER; reflexivity).
assert (ENS : nslots Xs = nslots A) by (unfold nslots; rewrite ER; reflexivity).
rewrite ELB in Hlive. rewrite ENS in Hsl. pose proof (live_bytes_nonneg' A NN) as Hlb.
destruct src0_reserved_small as [RS RL]. pose proof src0_reserved_bytes as RB.
destruct (region_free_exists28_std (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (page_round ln)) as (a & Ha1 & Ha2 & Ha3 & Ha4).
- lia.
- rewrite length_app. rewrite (lg_reserved _ _ _ _ G). pose proof (lg_count _ _ _ _ G). change (ms_segs B) with src0segs. lia.
- rewrite ivs_bytes_app, (lg_reserved _ _ _ _ G). change (ms_segs B) with src0segs.
rewrite (ivs_bytes_live_bytes (vm_maps (m_vmmaps md))). pose proof (lx_lb _ _ _ LX). lia.
- exists a. unfold place_ok.
rewrite (proj2 (Z.eqb_eq _ _) Ha1), (proj2 (Z.ltb_lt 0 _)) by lia.
pose proof (YM05.ceil_le_top _ (lg_ceil _ _ _ _ G)) as Htop.
assert (Ha3' : bv_unsigned a + page_round ln <= alloc_top (m_vmmaps md)) by lia.
rewrite (proj2 (Z.leb_le _ _) Ha3'), Ha4. reflexivity.
Qed.
Lemma denot_n2 : forall E shv, ew E 39 = Z_to_bv 64 shv -> 0 <= shv <= 40 ->
sv_denot E (SAlu ALU_SLL (SLit 2) (SOff 39 0)) = Z_to_bv 64 (Z.shiftl 2 shv) /\ 2 <= Z.shiftl 2 shv <= 2199023255552 /\ Z.shiftl 2 shv mod 2 = 0.
Proof.
intros E shv E39 Hsh.
assert (Hv : Z.shiftl 2 shv = 2 ^ shv * 2) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
assert (H1 : 2 ^ 0 <= 2 ^ shv) by (apply Z.pow_le_mono_r; lia).
assert (H2 : 2 ^ shv <= 2 ^ 40) by (apply Z.pow_le_mono_r; lia).
change (2 ^ 0) with 1 in H1. change (2 ^ 40) with 1099511627776 in H2.
split; [| split; [lia | rewrite Hv; apply Z_mod_mult]].
apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E39, alu64_sll. rewrite (lit64_small 2) by lia. rewrite (lit64_small shv) by lia.
rewrite Z.add_0_r, (lit64_small shv) by lia. rewrite (Z.mod_small shv 64) by lia. rewrite (lit64_small (Z.shiftl 2 shv)) by lia. rewrite sll64_small by lia. lia.
Qed.
Section g0.
Variable Xs : astate.
Hypothesis LXs : like_A0 A Xs.
Hypothesis BDx : st_brk Xs = BrkDead.
Hypothesis Efh : st_free_meta_head A = None.
Hypothesis Eamc : st_avail_meta_count A = 0.
Hypothesis Eaac : st_avail_meta_area_count A = 0.
Let sh := st_meta_alloc_shift A.
Let n2 := Z.shiftl 2 sh.
Let len := n2 * PGSZ.
Let NX := length (st_regions Xs).
Let p := SP NX PGSZ.
Lemma wsub_Vs : wsub (ss_mem ss_V) SK0 = true /\ wsub (ss_mem ss_v1') SK0 = true /\ wsub (ss_mem ss_v2') SK0 = true /\
wsub (ss_mem ss_vF1) SK0 = true /\ wsub (ss_mem ss_vG) SK0 = true /\ wsub (ss_mem (add_cond ss_vG1 C_vok)) SK0 = true /\
wsub (ss_mem ss_vF2) SK0 = true /\ wsub (ss_mem ss_vO) SK0 = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma sk_vK : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_vK) =
[(Some 2%nat, -AMS, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56);
(None, CTX, CTX + 12); (None, CTX + 16, CTX + 80); (None, CTX + 920, CTX + 928); (None, ERRNO, ERRNO + 4)] /\
map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_vK2) =
[(Some 2%nat, -AMS, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56);
(None, CTX, CTX + 12); (None, CTX + 16, CTX + 80); (None, CTX + 920, CTX + 928); (None, ERRNO, ERRNO + 4)].
Proof. vm_compute. split; reflexivity. Qed.
Lemma v_checks : ss_atoms_lt 77 ss_v1 = true /\ ss_atoms_lt 78 ss_v2 = true /\ ss_atoms_lt 79 ss_vK = true /\
final_regs_check ss_vF1E = true /\ final_regs_check ss_vF2E = true /\
absO_check ss_oV (SMd M_MUL (SOff 77 (-1)) (SLit 1)) (SOff 39 1) (SLit (2 ^ 64 - 1)) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma v_regs : sr_get (ss_regs (junk_regs [9%bv] 77 ss_v1)) 9 = SOff 77 0 /\ sr_get (ss_regs ss_v1) 9 = SAlu ALU_SLL (SLit 2) (SOff 39 0) /\
sr_get (ss_regs (junk_regs [11%bv] 78 ss_v2)) 11 = SOff 78 0 /\ sr_get (ss_regs ss_v2) 11 = SMd M_MUL (SOff 77 0) (SLit 4096).
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition R_ctxBV : YP09.region :=
YP09.mkRegion None (CTX + 16) (CTX + 80) (CTX + 16) (CTX + 80)
[mkChunk (CTX + 72) (CVal 8 (SOff 79 4096)); mkChunk (CTX + 48) (CVal 8 (SOff 39 1));
mkChunk (CTX + 40) (CVal 8 (SMd M_MUL (SOff 77 (-1)) (SLit 1))); mkChunk (CTX + 16) (CVal 8 (SOff 33 0));
mkChunk (CTX + 24) (CVal 8 (SOff 36 0)); mkChunk (CTX + 32) (CVal 8 (SOff 37 0));
mkChunk (CTX + 56) (CVal 8 (SOff 40 0)); mkChunk (CTX + 64) (CVal 8 (SOff 41 0))].
Definition R_brkdead : YP09.region :=
YP09.mkRegion None (CTX + 920) (CTX + 928) (CTX + 920) (CTX + 928) [mkChunk (CTX + 920) (CVal 8 (SLit (2 ^ 64 - 1)))].
Lemma vF_mem : (nth_error (ss_mem ss_vF1E) 4 = Some (R_ctxA true) /\ nth_error (ss_mem ss_vF1E) 5 = Some R_ctxB /\
nth_error (ss_mem ss_vF1E) 6 = Some R_brkdead /\ scratch_skel ss_vF1E 0 7 = true /\ sr_get (ss_regs ss_vF1E) 10 = SLit 0) /\
(nth_error (ss_mem ss_vF2E) 4 = Some (R_ctxA true) /\ nth_error (ss_mem ss_vF2E) 5 = Some R_ctxBV /\
nth_error (ss_mem ss_vF2E) 6 = Some R_brkdead /\ scratch_skel ss_vF2E 0 7 = true /\ sr_get (ss_regs ss_vF2E) 10 = SLit 0).
Proof. vm_compute. repeat split; reflexivity. Qed.
Theorem path_V : forall c (K : Z -> itree astate (option sptr * astate)),
at_st ss_V (WF0 B sp) md c ->
K 0 = IRet (None, Xs) ->
(forall z, z <> 0 -> exists K2, K z = IAsk (KMprotect p) (resv_st Xs) K2 /\
K2 0 = IRet (None, resv_st Xs) /\
(forall z2, z2 <> 0 -> K2 z2 = IRet (Some (padd p AREA_HDR), take_st (open_st p (sV Xs))))) ->
SR src0segs c (fun c1 => knode src0segs c1 (KMmapNone len) Xs (fun z c2 => mreal src0segs c2 (K z) (fun r c' => Qspec r -> POST r c'))).
Proof.
intros c K (E & ms & -> & HS & HA & HF) K0 K1.
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7). unfold AMS in P3, P5.
pose proof md_facts as (Mh & Mlz & Mmat). assert (PG4 : PGSZ = 4096) by reflexivity.
pose proof LXs as (ER & EAr & EMt & EB & Ein & CR & Efh' & Eam & Eamc' & Eaac' & Esh & Ehd & Etl & Eama).
pose proof sh_range as SH. change (st_meta_alloc_shift A) with sh in SH.
assert (E39 : ew E 39 = Z_to_bv 64 sh) by (rewrite (agree_cx E 39 HA) by lia; reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 0) by (rewrite (agree_cx E 38 HA) by lia; cbn [cx]; rewrite Eaac; reflexivity).
assert (E37 : ew E 37 = Z_to_bv 64 0) by (rewrite (agree_cx E 37 HA) by lia; cbn [cx]; rewrite Eamc; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 0) by (rewrite (agree_cx E 33 HA) by lia; cbn [cx]; rewrite Efh; reflexivity).
destruct (denot_n2 E sh E39 SH) as (Dn2 & Hn2 & Hn2e). change (Z.shiftl 2 sh) with n2 in Dn2, Hn2, Hn2e.
assert (Hlen : len = n2 * 4096) by reflexivity.
pose proof v_regs as (SG9 & SG9' & SG11 & SG11').
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL (src0_A_alloc_meta + 0x1c4) E ss_V ss_v1 RS_running); [exact Mh | exact Mlz | exact HS | apply run_V |].
intros ms1 HS1 HF1.
assert (F1 : FRM (WF0 B sp) (ms_mem ms1)) by (eapply FRM_run0; [intros x Hx; exact Hx | exact HA | exact HF | exact HF1 | exact (proj1 wsub_Vs)]).
assert (NZ9 : forallb (fun r : reg => negb (bv_eqb r 0)) [9%bv] = true) by (vm_compute; reflexivity).
destruct (junk_regs_ok src0segs [9%bv] 77 E ss_v1 ms1 HS1 (proj1 v_checks) NZ9) as (E1 & HA1 & HS2).
assert (E1_77 : ew E1 77 = Z_to_bv 64 n2).
{ pose proof (st_ok_reg src0segs E1 _ ms1 9 HS2) as RR. rewrite SG9 in RR. cbn [sv_denot] in RR. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in RR.
rewrite <- RR, (st_ok_reg src0segs E _ ms1 9 HS1), SG9'. exact Dn2. }
apply (st_ok_add_fact src0segs E1 _ ms1 77 F_n2) in HS2.
2:{ unfold afact_ok, F_n2. cbn [af_lo af_hi af_al2]. rewrite E1_77, (u64_of_Z n2) by lia. change (2 ^ 1) with 2. change (2 ^ 41) with 2199023255552. repeat split; lia. }
change (add_atom (junk_regs [9%bv] 77 ss_v1) 77 F_n2) with ss_v1' in HS2.
assert (HA01 : env_agree 46 E00 E1) by (apply (agree_step 46 77 _ _ _ HA HA1); lia).
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL (src0_A_alloc_meta + 0x1c8) E1 ss_v1' ss_v2 RS_running); [exact Mh | exact Mlz | exact HS2 | apply run_v1' |].
intros ms2 HS3 HF3.
assert (F2 : FRM (WF0 B sp) (ms_mem ms2)) by (eapply FRM_run0; [intros x Hx; exact Hx | exact HA01 | exact F1 | exact HF3 | exact (proj1 (proj2 wsub_Vs))]).
assert (NZ11 : forallb (fun r : reg => negb (bv_eqb r 0)) [11%bv] = true) by (vm_compute; reflexivity).
destruct (junk_regs_ok src0segs [11%bv] 78 E1 ss_v2 ms2 HS3 (proj1 (proj2 v_checks)) NZ11) as (E2 & HA2 & HS4).
assert (E2_78 : ew E2 78 = Z_to_bv 64 len).
{ pose proof (st_ok_reg src0segs E2 _ ms2 11 HS4) as RR. rewrite SG11 in RR. cbn [sv_denot] in RR. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in RR.
rewrite <- RR, (st_ok_reg src0segs E1 _ ms2 11 HS3), SG11'.
apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite E1_77, mul64_unsigned. rewrite (lit64_small n2) by lia. rewrite Z.add_0_r, (lit64_small n2) by lia.
rewrite (lit64_small 4096) by lia. rewrite (lit64_small len) by lia. rewrite mul64_small by lia. lia. }
apply (st_ok_add_fact src0segs E2 _ ms2 78 F_nl) in HS4.
2:{ unfold afact_ok, F_nl. cbn [af_lo af_hi af_al2]. rewrite E2_78, (u64_of_Z len) by lia. change (2 ^ 12) with 4096. change (2 ^ 53) with 9007199254740992.
split; [lia|]. rewrite Hlen. split; [apply Z_mod_mult | lia]. }
change (add_atom (junk_regs [11%bv] 78 ss_v2) 78 F_nl) with ss_v2' in HS4.
assert (HA02 : env_agree 46 E00 E2) by (apply (agree_step 46 78 _ _ _ HA01 HA2); lia).
assert (E2_77 : ew E2 77 = Z_to_bv 64 n2) by (destruct HA2 as [X2 _]; rewrite (X2 77%nat) by lia; exact E1_77).
eapply (SR_run_ecall src0segs src0tbl src0tbl_ok FUEL E2 ss_v2' ss_vK); [exact Mh | exact Mlz | exact HS4 | apply run_v2' |].
intros ms3 HS5 HF5.
assert (F3 : FRM (WF0 B sp) (ms_mem ms3)) by (eapply FRM_run0; [intros x Hx; exact Hx | exact HA02 | exact F2 | exact HF5 | exact (proj1 (proj2 (proj2 wsub_Vs)))]).
destruct (st_ok_ecall_shape src0segs E2 ss_vK ms3 HS5 eq_refl) as (regs3 & mem3 & Hms & Hregs & Hmem & HG).
rewrite Hms. rewrite Hms in F3. cbn [ms_mem pend_at] in F3. rewrite ss_vK_pc.
apply SR_ret.
apply (knode_mmap_none src0segs regs3 (Z_to_bv 64 (src0_A_mmap + 0xc4)) mem3 (seg_rom src0segs) md Xs len).
- exact Mh. - exact Mlz.
- rewrite (Hregs 17%bv). reflexivity.
- rewrite (Hregs 11%bv). exact (sv_off0 E2 78 _ E2_78).
- lia.
- rewrite (Hregs 12%bv). reflexivity.
- rewrite (Hregs 13%bv). reflexivity.
- rewrite (Hregs 14%bv). apply bv_eq. vm_compute. reflexivity.
- rewrite (Hregs 15%bv). reflexivity.
-
intros e He. rewrite K0. cbn [mreal].
assert (Ee : errno_ret e = Z_to_bv 64 (2 ^ 64 - 12)) by (destruct He as [<-|[]]; unfold errno_ret; apply bv_eq; reflexivity).
pose proof (st_ok_resume_sv src0segs E2 ss_vK regs3 mem3 (SLit (2 ^ 64 - 12)) (errno_ret e) Hregs Hmem HG ltac:(rewrite Ee; reflexivity)) as HS6.
change (resume ss_vK (SLit (2 ^ 64 - 12)) (ss_mem ss_vK) (ss_facts ss_vK)) with ss_vF1 in HS6. rewrite ss_vK_pc in HS6.
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E2 ss_vF1 ss_vF1E); [exact Mh | exact Mlz | exact HS6 | apply run_vF1 |].
intros ms4 HS7 HF7. cbn [ms_mem mkst] in HF7.
assert (F4 : FRM (WF0 B sp) (ms_mem ms4)) by (eapply FRM_run0; [intros x Hx; exact Hx | exact HA02 | exact F3 | exact HF7 | exact (proj1 (proj2 (proj2 (proj2 wsub_Vs))))]).
destruct (final_regs E2 ss_vF1E ms4 (proj1 (proj2 (proj2 (proj2 v_checks)))) HS7 HA02) as (PRS & E1' & Hra & Hpc & Hrv).
apply (SR_final_ret E2 ss_vF1E ms4 md _ HS7 Hrv Hpc Hra); [rewrite E1'; exact P1 | exact Mh | exact Mlz |].
intros _. destruct (proj1 vF_mem) as (MA & MB & MC & SKL & R10').
destruct (old_ptrs L eq_refl ltac:(intros; reflexivity)) as (O36 & O40 & O41).
destruct (post_fail0 B X R U L A mem md HI XC AMA BND MID src0_ENC src0_ENS src0_ERRIMG src0_SNC Xs
ER EAr EMt EB CR Esh Eama sp (ms_mem ms4) md) as (MID' & AMA' & BND');
[rewrite AMS_eq; unfold AMS; lia | exact F4 | | reflexivity | reflexivity | reflexivity | reflexivity |].
+ eapply (ctx11_intro E2 ss_vF1E ms4 Xs L 4 5 6); [exact HS7 | (eapply sv_sec; [eassumption | lia]) | exact Ein | exact MA | reflexivity | cbn; tauto | cbn; tauto | exact MB | reflexivity
| cbn; tauto | | cbn; tauto | | cbn; tauto | | cbn; tauto | | cbn; tauto | | cbn; tauto | | cbn; tauto | | cbn; tauto | | exact MC | reflexivity | cbn; tauto |].
* rewrite Efh'. exact (sv_cx E2 33 HA02 ltac:(lia)).
* unfold amv. rewrite EAr, Eam. exact (sv_cx E2 36 HA02 ltac:(lia)).
* rewrite Eamc'. exact (sv_cx E2 37 HA02 ltac:(lia)).
* rewrite Eaac'. exact (sv_cx E2 38 HA02 ltac:(lia)).
* rewrite Esh. exact (sv_cx E2 39 HA02 ltac:(lia)).
* rewrite Ehd. exact (sv_cx E2 40 HA02 ltac:(lia)).
* rewrite Etl. exact (sv_cx E2 41 HA02 ltac:(lia)).
* unfold amav. rewrite EAr, Eaac', Eama. exact (sv_cx E2 42 HA02 ltac:(lia)).
* unfold brkv. rewrite BDx. cbn [sval_num sv_denot]. apply bv_eq. vm_compute. reflexivity.
+ exists L, (ms_regs ms4), (ms_mem ms4), md. cbn [fst snd].
split; [rewrite E1'; reflexivity|].
split; [| split; [exact AMA' | split; [exact BND' | split; [| exact I]]]].
* split; [exact MID'|]. split; [apply layout_le_refl|]. split; [exact PRS|]. split; [exists (m_vmmaps md); apply with_vmmaps_self; assumption|]. split.
-- intros x Hx Nc Nn Ns. apply (F4 x Hx). intros [Hs|Hc].
** apply Ns. unfold spZ. fold sp. exact Hs.
** apply Nc. rewrite B_ctx. unfold ctxW in Hc. rewrite B_ctx in Hc. unfold CTX_SIZE. lia.
-- rewrite B_segs. unfold spZ. fold sp. exact (scratch_writable' E2 ss_vF1E ms4 0 7 HS7 HA02 SKL).
* rewrite (st_ok_reg src0segs _ ss_vF1E ms4 10 HS7), R10'. reflexivity.
-
intros a PL. destruct (K1 1 ltac:(lia)) as (K2 & EK & K20 & K21). rewrite EK. cbn [mreal].
assert (PR : page_round len = len).
{ unfold page_round. rewrite Hlen. change PGSZ with 4096. replace (n2 * 4096 + 4096 - 1) with (4095 + n2 * 4096) by lia.
rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
rewrite PR in PL |- *. rewrite (Hregs 10%bv) in PL. change (sv_denot E2 (sr_get (ss_regs ss_vK) 10)) with (Z_to_bv 64 0) in PL.
pose proof (len_facts B L A mem md BND MID a PL) as (_ & _ & Hceil & Ha0 & Hal & RF & Hsh40). change (Z.shiftl 2 (st_meta_alloc_shift A) * PGSZ) with len in Hceil, RF.
pose proof (u64_range a) as Ua.
assert (Hal' : bv_unsigned a mod 4096 = 0) by (unfold PGSZ in Hal; exact Hal).
assert (Ha4096 : 4096 <= bv_unsigned a).
{ destruct (Z_lt_le_dec (bv_unsigned a) 4096); [| lia]. rewrite Z.mod_small in Hal' by lia. lia. }
assert (Pfacts : forall x, bv_unsigned a <= x < bv_unsigned a + len -> ~ in_img B x /\ 4096 <= x < alloc_ceiling).
{ intros x Hx. split; [| lia]. intros Hi. exact (fresh_img B L A md (mid_ledger _ _ _ _ _ MID) a len ltac:(lia) Ha0 ltac:(lia) RF x Hi Hx). }
assert (Hmem4 : mem_ok src0segs E2 (apply_unmaps mem3 [(Z_to_bv 64 (bv_unsigned a), Z_to_bv 64 len)]) (ss_mem ss_vK)).
{ apply (mem_ok_unmap src0segs E2 mem3 (ss_mem ss_vK) (bv_unsigned a) len Hmem); [lia | lia | lia |].
intros r' Hr'. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite (proj1 sk_vK) in Hr'.
destruct (SK0_apart E2 (bv_unsigned a) len r' (agree_reg2 E2 HA02) ltac:(lia) Pfacts Hr') as [H|H]; [right; exact H | left; exact H]. }
replace (apply_unmaps mem3 [(a, Z_to_bv 64 len)]) with (apply_unmaps mem3 [(Z_to_bv 64 (bv_unsigned a), Z_to_bv 64 len)])
by (rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof (st_ok_resume_atom src0segs 79 F_pg E2 ss_vK regs3 _ a Hregs Hmem4 HG (proj1 (proj2 (proj2 v_checks)))
ltac:(unfold F_pg; cbn [af_lo af_hi]; lia) ltac:(unfold F_pg; cbn [af_al2]; lia) ltac:(unfold F_pg; cbn [af_al2]; change (2 ^ 12) with 4096; exact Hal')) as HS6.
change (resume ss_vK (SOff 79 0) (ss_mem ss_vK) (mkFacts ((79%nat, F_pg) :: f_atoms (ss_facts ss_vK)) (f_conds (ss_facts ss_vK)) (f_alias (ss_facts ss_vK)))) with ss_vG in HS6.
rewrite ss_vK_pc in HS6.
set (E3 := ewset E2 79 a) in HS6.
assert (HA23 : env_agree 79 E2 E3) by (apply env_agree_ewset).
assert (HA03 : env_agree 46 E00 E3) by (apply (agree_step 46 79 _ _ _ HA02 HA23); lia).
assert (E3_73 : ew E3 79 = Z_to_bv 64 (bv_unsigned a)) by (unfold E3; rewrite ew_ewset_same; symmetry; apply Z_to_bv_bv_unsigned).
assert (U73 : bv_unsigned (ew E3 79) = bv_unsigned a) by (rewrite E3_73; apply u64_of_Z; lia).
assert (E3_77 : ew E3 77 = Z_to_bv 64 n2) by (destruct HA23 as [X3 _]; rewrite <- E2_77; apply X3; lia).
assert (E3_39 : ew E3 39 = Z_to_bv 64 sh) by (rewrite (agree_cx E3 39 HA03) by lia; reflexivity).
set (md1 := mmap_none_model a (Z_to_bv 64 len) md).
assert (MD1 : m_halted md1 = None /\ m_vm_lazy md1 = [] /\ m_vm_materialized md1 = []).
{ unfold md1, mmap_none_model. rewrite m_halted_with, m_vm_lazy_with, m_vm_materialized_with. auto. }
destruct MD1 as (Mh1 & Mlz1 & Mmat1).
set (W := fun x => WF0 B sp x \/ bv_unsigned a <= x < bv_unsigned a + len).
assert (F4 : FRM W (apply_unmaps mem3 [(Z_to_bv 64 (bv_unsigned a), Z_to_bv 64 len)])).
{ intros x Hx Hn. rewrite apply_unmaps1_out; [apply (F3 x Hx); intros Hw; apply Hn; left; exact Hw|].
rewrite !u64_of_Z by lia. destruct (Z_lt_le_dec x (bv_unsigned a)); [left; lia|]. right.
destruct (Z_lt_le_dec x (bv_unsigned a + len)); [exfalso; apply Hn; right; lia | lia]. }
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E3 ss_vG ss_vG1); [exact Mh1 | exact Mlz1 | exact HS6 | apply run_vG |].
intros ms5 HS8 HF8. cbn [ms_mem mkst] in HF8.
assert (F5 : FRM W (ms_mem ms5)) by (eapply FRM_run0; [intros x Hx; left; exact Hx | exact HA03 | exact F4 | exact HF8 | exact (proj1 (proj2 (proj2 (proj2 (proj2 wsub_Vs)))))]).
apply (st_ok_add_cond src0segs E3 ss_vG1 ms5 BC_NE (ac_a C_vok) (SLit 0)) in HS8.
2:{ cbn [ac_a C_vok sv_denot]. rewrite branch_ne. apply Bool.negb_true_iff. apply Z.eqb_neq.
rewrite alu64_or, alu64_xor_allones by (vm_compute; reflexivity). rewrite (lit64_small 0) by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, U73, Z.lor_0_l.
unfold not64. intros H0.
assert (HL : Z.lnot (bv_unsigned a) = - bv_unsigned a - 1) by (unfold Z.lnot; lia).
rewrite HL in H0. replace (- bv_unsigned a - 1) with (2 ^ 64 - bv_unsigned a - 1 + (-1) * 2 ^ 64) in H0 by lia.
rewrite Z_mod_plus_full, Z.mod_small in H0 by lia. lia. }
change (add_cond ss_vG1 (mkAC BC_NE (ac_a C_vok) (SLit 0))) with (add_cond ss_vG1 C_vok) in HS8.
eapply (SR_run_ecall src0segs src0tbl src0tbl_ok FUEL E3 (add_cond ss_vG1 C_vok) ss_vK2); [exact Mh1 | exact Mlz1 | exact HS8 | apply run_vG1 |].
intros ms6 HS9 HF9.
assert (F6 : FRM W (ms_mem ms6)) by (eapply FRM_run0; [intros x Hx; left; exact Hx | exact HA03 | exact F5 | exact HF9 | exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 wsub_Vs))))))]).
destruct (st_ok_ecall_shape src0segs E3 ss_vK2 ms6 HS9 eq_refl) as (regs6 & mem6 & Hms6 & Hregs6 & Hmem6 & HG6).
rewrite Hms6. rewrite Hms6 in F6. cbn [ms_mem pend_at] in F6. rewrite ss_vK2_pc.
assert (R10 : getr regs6 10 = Z_to_bv 64 (bv_unsigned a + 4096)) by (rewrite (Hregs6 10%bv); exact (sv_off E3 79 4096 _ E3_73)).
assert (U10 : bv_unsigned (getr regs6 10) = bv_unsigned a + 4096) by (rewrite R10; apply u64_of_Z; lia).
assert (Ulen : bv_unsigned (Z_to_bv 64 len) = len) by (apply u64_of_Z; lia).
apply SR_ret.
apply (knode_mprotect src0segs regs6 (Z_to_bv 64 (src0_A_mprotect + 0x30)) mem6 (seg_rom src0segs) md1 (resv_st Xs) p).
+ exact Mh1. + exact Mlz1.
+ rewrite (Hregs6 17%bv). reflexivity.
+ rewrite U10. unfold page_size. replace (bv_unsigned a + 4096) with (bv_unsigned a + 1 * 4096) by lia. rewrite Z_mod_plus_full. exact Hal'.
+ rewrite (Hregs6 11%bv). reflexivity.
+ rewrite U10. unfold two_pow_64. lia.
+ rewrite (Hregs6 12%bv). reflexivity.
+ unfold md1, mmap_none_model. rewrite m_vmmaps_with. cbn [vm_noaccess]. apply map_contains_head; rewrite U10, ?Ulen; [lia|]. change (bv_unsigned (Z_to_bv 64 4096)) with 4096. lia.
+ unfold md1, mmap_none_model. rewrite m_vmmaps_with. cbn [vm_maps]. apply map_contains_head; rewrite U10, ?Ulen; [lia|]. change (bv_unsigned (Z_to_bv 64 4096)) with 4096. lia.
+
intros e He. rewrite K20. cbn [mreal].
assert (Ee : errno_ret e = Z_to_bv 64 (2 ^ 64 - 12)) by (destruct He as [<-|[]]; unfold errno_ret; apply bv_eq; reflexivity).
pose proof (st_ok_resume_sv src0segs E3 ss_vK2 regs6 mem6 (SLit (2 ^ 64 - 12)) (errno_ret e) Hregs6 Hmem6 HG6 ltac:(rewrite Ee; reflexivity)) as HS10.
change (resume ss_vK2 (SLit (2 ^ 64 - 12)) (ss_mem ss_vK2) (ss_facts ss_vK2)) with ss_vF2 in HS10. rewrite ss_vK2_pc in HS10.
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E3 ss_vF2 ss_vF2E); [exact Mh1 | exact Mlz1 | exact HS10 | apply run_vF2 |].
intros ms7 HS11 HF11. cbn [ms_mem mkst] in HF11.
assert (F7 : FRM W (ms_mem ms7)) by (eapply FRM_run0; [intros x Hx; left; exact Hx | exact HA03 | exact F6 | exact HF11 | exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 wsub_Vs)))))))]).
destruct (final_regs E3 ss_vF2E ms7 (proj1 (proj2 (proj2 (proj2 (proj2 v_checks))))) HS11 HA03) as (PRS & E1' & Hra & Hpc & Hrv).
apply (SR_final_ret E3 ss_vF2E ms7 md1 _ HS11 Hrv Hpc Hra); [rewrite E1'; exact P1 | exact Mh1 | exact Mlz1 |].
intros _. destruct (proj2 vF_mem) as (MA & MB & MC & SKL & R10').
set (L' := Lset L A (bv_unsigned a)).
assert (L'reg : forall r, (r < length (st_regions A))%nat -> ly_reg L' r = ly_reg L r) by (intros r Hr; unfold L'; apply Lset_lt; exact Hr).
destruct (old_ptrs L' eq_refl L'reg) as (O36 & O40 & O41).
destruct (post_resv_fail B X R U L A mem md HI XC AMA BND MID src0_ENC src0_ENS src0_ERRIMG src0_SNC Xs a md1 LXs PL
(conj eq_refl (conj Mh1 (conj Mlz1 Mmat1))) sp (ms_mem ms7)) as (MID' & AMA' & BND' & LE' & NM);
[rewrite AMS_eq; unfold AMS; lia | intros x Hx Hn; apply (F7 x Hx); intros [[Hw|Hw]|Hw]; apply Hn; [left; exact Hw | right; left; exact Hw | right; right; exact Hw] | |].
* fold L'. eapply (ctx11_intro E3 ss_vF2E ms7 (resv_st Xs) L' 4 5 6); [exact HS11 | (eapply sv_sec; [eassumption | lia]) | exact Ein | exact MA | reflexivity | cbn; tauto | cbn; tauto | exact MB | reflexivity
| cbn; tauto | | cbn; tauto | | cbn; tauto | | cbn; tauto | | cbn; tauto | | cbn; tauto | | cbn; tauto | | cbn; tauto | | exact MC | reflexivity | cbn; tauto |].
-- change (st_free_meta_head (resv_st Xs)) with (st_free_meta_head Xs). rewrite Efh', Efh. rewrite (sv_cx E3 33 HA03 ltac:(lia)). cbn [cx]. rewrite Efh. reflexivity.
-- unfold amv. change (st_areas (resv_st Xs)) with (st_areas Xs). change (st_avail_meta (resv_st Xs)) with (st_avail_meta Xs). rewrite EAr, Eam.
change (match st_areas A with [] => VZ 0 | _ :: _ => VP (st_avail_meta A) end) with (amv A). rewrite O36. exact (sv_cx E3 36 HA03 ltac:(lia)).
-- change (st_avail_meta_count (resv_st Xs)) with (st_avail_meta_count Xs). rewrite Eamc'. exact (sv_cx E3 37 HA03 ltac:(lia)).
-- change (st_avail_meta_area_count (resv_st Xs)) with (Z.shiftl 2 (st_meta_alloc_shift Xs) - 1). rewrite Esh. change (Z.shiftl 2 (st_meta_alloc_shift A)) with n2.
apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite mul64_unsigned, E3_77. rewrite (lit64_small n2) by lia. replace (n2 + -1) with (n2 - 1) by lia.
rewrite (lit64_small (n2 - 1)) by lia. rewrite (lit64_small 1) by lia. rewrite mul64_small by lia. lia.
-- change (st_meta_alloc_shift (resv_st Xs)) with (st_meta_alloc_shift Xs + 1). rewrite Esh. exact (sv_off E3 39 1 _ E3_39).
-- change (st_area_head (resv_st Xs)) with (st_area_head Xs). rewrite Ehd, O40. exact (sv_cx E3 40 HA03 ltac:(lia)).
-- change (st_area_tail (resv_st Xs)) with (st_area_tail Xs). rewrite Etl, O41. exact (sv_cx E3 41 HA03 ltac:(lia)).
-- unfold amav. change (st_avail_meta_area_count (resv_st Xs)) with (Z.shiftl 2 (st_meta_alloc_shift Xs) - 1). rewrite Esh. change (Z.shiftl 2 (st_meta_alloc_shift A)) with n2.
replace (n2 - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite andb_false_r.
change (st_avail_meta_areas (resv_st Xs)) with (SP (length (st_regions Xs)) PGSZ). cbn [sval_num]. unfold ptr_addr. cbn [loc_addr].
unfold L', Lset. cbn [ly_reg]. rewrite ER, Nat.eqb_refl. exact (sv_off E3 79 4096 _ E3_73).
-- unfold brkv. change (st_brk (resv_st Xs)) with (st_brk Xs). rewrite BDx. cbn [sval_num sv_denot]. apply bv_eq. vm_compute. reflexivity.
* exists L', (ms_regs ms7), (ms_mem ms7), md1. cbn [fst snd].
split; [rewrite E1'; reflexivity|].
split; [| split; [exact AMA' | split; [exact BND' | split; [| exact I]]]].
-- split; [exact MID'|]. split; [exact LE'|]. split; [exact PRS|]. split; [exists (m_vmmaps md1); unfold md1, mmap_none_model; rewrite m_vmmaps_with; reflexivity|]. split.
++ intros x Hx Nc Nn Ns. apply (F7 x Hx). intros [[Hs|Hc]|Hr].
** apply Ns. unfold spZ. fold sp. exact Hs.
** apply Nc. rewrite B_ctx. unfold ctxW in Hc. rewrite B_ctx in Hc. unfold CTX_SIZE. lia.
** exact (Nn (NM x Hr)).
++ rewrite B_segs. unfold spZ. fold sp. exact (scratch_writable' E3 ss_vF2E ms7 0 7 HS11 HA03 SKL).
-- rewrite (st_ok_reg src0segs _ ss_vF2E ms7 10 HS11), R10'. reflexivity.
+
intros GB. rewrite (K21 1 ltac:(lia)). cbn [mreal]. rewrite R10.
set (Pg := bv_unsigned a + 4096).
assert (Pgfacts : forall x, Pg <= x < Pg + 4096 -> ~ in_img B x /\ 4096 <= x < alloc_ceiling) by (intros x Hx; apply Pfacts; unfold Pg in Hx; lia).
assert (Hmem7 : mem_ok src0segs E3 (apply_zeros mem6 [(Z_to_bv 64 Pg, Z_to_bv 64 4096)]) (ss_mem ss_vK2)).
{ apply (mem_ok_zeros_outside src0segs E3 mem6 (ss_mem ss_vK2) Pg 4096 Hmem6); [lia | lia | lia |].
intros r' Hr'. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite (proj2 sk_vK) in Hr'.
destruct (SK0_apart E3 Pg 4096 r' (agree_reg2 E3 HA03) ltac:(lia) Pgfacts Hr') as [H|H]; [right; exact H | left; exact H]. }
pose proof (st_ok_resume_sv src0segs E3 ss_vK2 regs6 _ (SLit 0) (Z_to_bv 64 0) Hregs6 Hmem7 HG6 eq_refl) as HS10.
change (resume ss_vK2 (SLit 0) (ss_mem ss_vK2) (ss_facts ss_vK2)) with ss_vO in HS10. rewrite ss_vK2_pc in HS10.
pose proof (open_V B X R U L A mem md HI BND MID Xs a LXs PL) as OC.
assert (EMD : mprotect_model (Z_to_bv 64 Pg) (Z_to_bv 64 4096) md1 = mdV A md a) by reflexivity.
rewrite EMD. pose proof (oc_MD3 _ _ _ _ _ _ _ _ _ OC) as (Mh3 & Mlz3 & Mmat3).
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL PC_O E3 ss_vO ss_oV RS_running); [exact Mh3 | exact Mlz3 | exact HS10 | apply run_vO |].
intros ms7 HS11 HF11. cbn [ms_mem mkst] in HF11.
destruct (zeros_frame W mem6 Pg F6 ltac:(lia) ltac:(lia)) as [F7 PZ7].
set (W' := fun x => W x \/ Pg <= x < Pg + 4096) in F7.
assert (F8 : FRM W' (ms_mem ms7)) by (eapply FRM_run0; [intros x Hx; left; left; exact Hx | exact HA03 | exact F7 | exact HF11 | exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 wsub_Vs)))))))]).
assert (PZ8 : forall i, 0 <= i < PGSZ -> ms_mem ms7 (Z_to_bv 64 (Pg + i)) = Some (Z_to_bv 8 0)).
{ apply (PZ_run E3 (ss_mem ss_vO) _ _ Pg HA03 HF11 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 wsub_Vs)))))))); [intros x Hx; exact (proj1 (Pgfacts x Hx)) | lia | lia | exact PZ7]. }
assert (R9 : getr (ms_regs ms7) 9 = Z_to_bv 64 Pg) by (rewrite (st_ok_reg src0segs E3 ss_oV ms7 9 HS11); exact (sv_off E3 79 4096 _ E3_73)).
assert (E3_37 : ew E3 37 = Z_to_bv 64 0) by (rewrite (agree_cx E3 37 HA03) by lia; cbn [cx]; rewrite Eamc; reflexivity).
assert (E3_33 : ew E3 33 = Z_to_bv 64 0) by (rewrite (agree_cx E3 33 HA03) by lia; cbn [cx]; rewrite Efh; reflexivity).
assert (HPal : Pg mod 4096 = 0) by (unfold Pg; replace (bv_unsigned a + 4096) with (bv_unsigned a + 1 * 4096) by lia; rewrite Z_mod_plus_full; exact Hal').
assert (D40 : sv_denot E3 (SMd M_MUL (SOff 77 (-1)) (SLit 1)) = Z_to_bv 64 (n2 - 1)).
{ apply (proj2 (word_eq _ _)). cbn [sv_denot]. rewrite mul64_unsigned, E3_77. rewrite (lit64_small n2) by lia. replace (n2 + -1) with (n2 - 1) by lia.
rewrite (lit64_small (n2 - 1)) by lia. rewrite (lit64_small 1) by lia. rewrite mul64_small by lia. lia. }
destruct (to_O ss_oV E3 ms7 (SMd M_MUL (SOff 77 (-1)) (SLit 1)) (SOff 39 1) (SLit (2 ^ 64 - 1)) (n2 - 1) (sh + 1) (2 ^ 64 - 1) Pg
(proj2 (proj2 (proj2 (proj2 (proj2 v_checks))))) HS11 HA03 R9 ltac:(lia) HPal
D40 (sv_off E3 39 1 _ E3_39) eq_refl E3_37 E3_33) as (E' & HS12 & HA' & HA79 & E79 & E92 & E93 & E94).
set (L' := Lset L A (bv_unsigned a)).
assert (EP : ptr_addr L' p = Pg).
{ unfold p, ptr_addr. cbn [loc_addr]. unfold L', Lset. cbn [ly_reg]. unfold NX. rewrite ER, Nat.eqb_refl. unfold Pg, PGSZ. reflexivity. }
apply (leaf_O (sV Xs) p L' (mdV A md a) (fun x => bv_unsigned a <= x < bv_unsigned a + len) OC Efh E' ms7 W' HS12 HA').
* rewrite EP. exact E79.
* rewrite E92. f_equal. change (st_avail_meta_area_count (sV Xs)) with (Z.shiftl 2 (st_meta_alloc_shift Xs) - 1). rewrite Esh. reflexivity.
* rewrite E93. f_equal. change (st_meta_alloc_shift (sV Xs)) with (st_meta_alloc_shift Xs + 1). rewrite Esh. reflexivity.
* rewrite E94. unfold brkv. change (st_brk (sV Xs)) with (st_brk Xs). rewrite BDx. cbn [sval_num]. apply bv_eq. vm_compute. reflexivity.
* intros i Hi. rewrite EP. exact (PZ8 i Hi).
* exact F8.
* intros x [[[Hx|Hx]|Hx]|Hx]; [left; exact Hx | right; left; exact Hx | right; right; right; right; exact Hx | right; right; right; left; rewrite EP; unfold PGSZ; exact Hx].
* intros x Hx. left. left. exact Hx.
* intros Hne x Hx Wx. apply (last_next_not_W (sV Xs) p L' (mdV A md a) (fun x => bv_unsigned a <= x < bv_unsigned a + len) OC Hne x Hx).
destruct Wx as [[Hw|Hw]|Hw]; [left; exact Hw | right; right; exact Hw | right; left; rewrite EP; exact Hw].
+
intros (_ & Hlive & _). destruct (ledger_V1 B X R U L A mem md HI BND MID Xs a LXs PL) as [LG1 LX1].
apply (mprotect_budget (Lset L A (bv_unsigned a)) md1 _ _ (resv_st Xs) LG1 LX1 Mlz1 Mmat1).
unfold req_len, PGSZ in Hlive. lia.
-
intros Hm. rewrite (Hregs 10%bv). change (sv_denot E2 (sr_get (ss_regs ss_vK) 10)) with (Z_to_bv 64 0).
exact (resv_grant_exists Xs len LXs Hm).
Qed.
End g0.
Section h0.
Hypothesis Efh : st_free_meta_head A = None.
Hypothesis Eamc : st_avail_meta_count A = 0.
Hypothesis Eaac : st_avail_meta_area_count A = 0.
Hypothesis Hbk : st_brk A = BrkNever.
Let b := vm_brk (m_vmmaps md).
Let p := SP (length (st_regions A)) PGSZ.
Let L' := Lset L A (bv_unsigned b).
Lemma wsub_BN : wsub (ss_mem ss_nQ1) SK0 = true /\ wsub (ss_mem ss_nR) SK0 = true /\ wsub (ss_mem ss_nGG) SK0 = true /\
wsub (ss_mem (resume_ ss_nK3 (SLit (2 ^ 64 - 12)) (ss_mem ss_nK3))) SK0 = true /\ wsub (ss_mem (add_cond ss_g1 C_gok1)) SK0 = true /\
wsub (ss_mem (resume_ ss_nK3 (SOff 72 0) (ss_mem ss_nK3))) SK0 = true /\ wsub (ss_mem (add_cond ss_g2 C_gok2)) SK0 = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma sk_BN : map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_nG) =
[(Some 2%nat, -AMS, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56);
(None, CTX, CTX + 12); (None, CTX + 16, CTX + 80); (None, CTX + 920, CTX + 928); (None, ERRNO, ERRNO + 4)] /\
map (fun r => (r_base r, r_lo r, r_hi r)) (ss_mem ss_nK3) =
[(Some 2%nat, -AMS, 0); (None, GOT, GOT + 8); (None, GUARD, GUARD + 8); (None, LIBC + 48, LIBC + 56);
(None, CTX, CTX + 12); (None, CTX + 16, CTX + 80); (None, CTX + 920, CTX + 928); (None, ERRNO, ERRNO + 4)].
Proof. vm_compute. split; reflexivity. Qed.
Lemma bn_checks : ss_atoms_lt 72 ss_nQ = true /\ absV_check false ss_vBN = true /\
absO_check ss_oN1 (SLit 1) (SOff 39 0) (SOff 72 8192) = true /\ absO_check ss_oN2 (SLit 1) (SOff 39 0) (SOff 72 8192) = true /\
sr_get (ss_regs ss_oN1) 9 = SOff 72 4096 /\ sr_get (ss_regs ss_oN2) 9 = SOff 72 4096.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma BN_facts : bv_unsigned b = ly_brk0 L /\ ly_brk0 L mod PGSZ = 0 /\ 4096 <= ly_brk0 L /\ ly_brk0 L + 2 * PGSZ <= alloc_ceiling /\
bv_unsigned (vm_start_brk (m_vmmaps md)) <= ly_brk0 L /\ reserved_top (segments_reserved src0segs) <= ly_brk0 L /\ cx 43 = 0 /\
ptr_addr L' p = bv_unsigned b + PGSZ.
Proof.
pose proof (lg_brk _ _ _ _ (mid_ledger _ _ _ _ _ MID)) as HB. rewrite Hbk in HB.
pose proof (lg_brk0 _ _ _ _ (mid_ledger _ _ _ _ _ MID)) as (B1 & B2 & B3 & B4 & B5).
split; [exact HB|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|].
split; [cbn [cx]; unfold brkv; rewrite Hbk; reflexivity|].
unfold p, ptr_addr. cbn [loc_addr]. unfold L', Lset. cbn [ly_reg]. rewrite Nat.eqb_refl. reflexivity.
Qed.
Lemma bn_leaf : forall E2 ss ms4 md3,
bv_unsigned b + 2 * PGSZ <= alloc_ceiling ->
region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) b (Z_to_bv 64 (2 * PGSZ)) = true ->
(vm_maps (m_vmmaps md3) = (b, w64 (2 * PGSZ)) :: vm_maps (m_vmmaps md) \/
vm_maps (m_vmmaps md3) = (w64 (bv_unsigned b + PGSZ), w64 PGSZ) :: vm_maps (m_vmmaps md)) ->
(forall lo n, 0 < bv_unsigned n ->
(bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + 2 * PGSZ <= bv_unsigned lo) ->
map_contains (vm_noaccess (m_vmmaps md)) lo n = true -> map_contains (vm_noaccess (m_vmmaps md3)) lo n = true) ->
(forall e, In e (vm_noaccess (m_vmmaps md3)) ->
(exists e0, In e0 (vm_noaccess (m_vmmaps md)) /\ iv_lo e0 <= iv_lo e /\ iv_lo e + iv_len e <= iv_lo e0 + iv_len e0) \/
(exists E, In E (vm_maps (m_vmmaps md3)) /\ iv_lo E <= iv_lo e /\ iv_lo e + iv_len e <= iv_lo E + iv_len E /\
bv_unsigned b <= iv_lo E /\ iv_lo E + iv_len E <= bv_unsigned b + 2 * PGSZ)) ->
vm_reserved (m_vmmaps md3) = vm_reserved (m_vmmaps md) -> vm_start_brk (m_vmmaps md3) = vm_start_brk (m_vmmaps md) ->
bv_unsigned (vm_brk (m_vmmaps md3)) = bv_unsigned b + 2 * PGSZ -> vm_limit (m_vmmaps md3) = vm_limit (m_vmmaps md) ->
alloc_top (m_vmmaps md3) = alloc_top (m_vmmaps md)   ->
m_halted md3 = None /\ m_vm_lazy md3 = [] /\ m_vm_materialized md3 = [] -> (exists vm', md3 = with_vmmaps vm' md) ->
absO_check ss (SLit 1) (SOff 39 0) (SOff 72 8192) = true -> sr_get (ss_regs ss) 9 = SOff 72 4096 ->
st_ok src0segs E2 ss ms4 -> env_agree 46 E00 E2 -> ew E2 72 = Z_to_bv 64 (bv_unsigned b) ->
FRM (fun x => WF0 B sp x \/ bv_unsigned b <= x < bv_unsigned b + 8192) (ms_mem ms4) ->
(forall i, 0 <= i < PGSZ -> ms_mem ms4 (Z_to_bv 64 (bv_unsigned b + 4096 + i)) = Some (Z_to_bv 8 0)) ->
SR src0segs (mkCfg ms4 md3) (fun c' => Qspec (Some (padd p AREA_HDR), take_st (open_st p (sBN A))) ->
POST (Some (padd p AREA_HDR), take_st (open_st p (sBN A))) c').
Proof.
intros E2 ss ms4 md3 Gceil Gfree VM3 VN3 VNX3 VR3 VS3 VB3 VL3 VT3 MD3 MDW3 CK SG9 HS HA2 E72 F4 PZ4.
pose proof (proj1 alloc_ceiling_val) as AC. pose proof (u64_range b) as Ub.
destruct BN_facts as (Hb & B1 & B2 & B3 & B4 & B5 & E43v & EP).
pose proof (open_BN B X R U L A mem md HI BND MID md3 Hbk Gfree VM3 VN3 VNX3 VR3 VS3 VB3 VL3 VT3 MD3 MDW3) as OC. fold L' in OC.
assert (E2_37 : ew E2 37 = Z_to_bv 64 0) by (rewrite (agree_cx E2 37 HA2) by lia; cbn [cx]; rewrite Eamc; reflexivity).
assert (E2_33 : ew E2 33 = Z_to_bv 64 0) by (rewrite (agree_cx E2 33 HA2) by lia; cbn [cx]; rewrite Efh; reflexivity).
assert (R9 : getr (ms_regs ms4) 9 = Z_to_bv 64 (bv_unsigned b + 4096)) by (rewrite (st_ok_reg src0segs E2 ss ms4 9 HS), SG9; exact (sv_off E2 72 4096 _ E72)).
assert (HPal : (bv_unsigned b + 4096) mod 4096 = 0).
{ replace (bv_unsigned b + 4096) with (bv_unsigned b + 1 * 4096) by lia. rewrite Z_mod_plus_full, Hb. unfold PGSZ in B1. exact B1. }
destruct (to_O ss E2 ms4 (SLit 1) (SOff 39 0) (SOff 72 8192) 1 (st_meta_alloc_shift A) (bv_unsigned b + 8192) (bv_unsigned b + 4096)
CK HS HA2 R9 ltac:(unfold PGSZ in Gceil; lia) HPal eq_refl (sv_cx E2 39 HA2 ltac:(lia)) (sv_off E2 72 8192 _ E72) E2_37 E2_33)
as (E' & HS5 & HA' & _ & E95 & E108 & E109 & E110).
apply (leaf_O (sBN A) p L' md3 (fun x => bv_unsigned b <= x < bv_unsigned b + 2 * PGSZ) OC Efh E' ms4 (fun x => WF0 B sp x \/ bv_unsigned b <= x < bv_unsigned b + 8192) HS5 HA').
- rewrite EP. exact E95.
- exact E108.
- exact E109.
- rewrite E110. f_equal. unfold brkv. change (st_brk (sBN A)) with (BrkCur (length (st_regions A)) 2). cbn [sval_num].
unfold ptr_addr. cbn [loc_addr]. unfold L', Lset. cbn [ly_reg]. rewrite Nat.eqb_refl. unfold PGSZ. lia.
- intros i Hi. rewrite EP. exact (PZ4 i Hi).
- exact F4.
- intros x [[Hx|Hx]|Hx]; [left; exact Hx | right; left; exact Hx | right; right; right; right; unfold PGSZ; exact Hx].
- intros x Hx. left. exact Hx.
- intros Hne x Hx Wx. apply (last_next_not_W (sBN A) p L' md3 _ OC Hne x Hx). destruct Wx as [Hw|Hw]; [left; exact Hw | right; right; unfold PGSZ; exact Hw].
Qed.
Theorem path_BN : forall c (K0 : Z -> itree astate (option sptr * astate)),
at_st (add_cond ss_b1 C_bn) (WF0 B sp) md c ->
(forall z0, exists K1, K0 z0 = IAsk (KBrkGrow 2) A0 K1 /\
(forall c2, at_st ss_V (WF0 B sp) md c2 -> mreal src0segs c2 (K1 0) (fun r c' => Qspec r -> POST r c')) /\
(forall z1, z1 <> 0 -> exists K3, K1 z1 = IAsk KGuard (sBN A) K3 /\
forall z3, K3 z3 = IRet (Some (padd p AREA_HDR), take_st (open_st p (sBN A))))) ->
SR src0segs c (fun c1 => knode src0segs c1 KBrkQuery A0 (fun z c2 => mreal src0segs c2 (K0 z) (fun r c' => Qspec r -> POST r c'))).
Proof.
intros c K0 (E & ms & -> & HS & HA & HF) HK.
pose proof (proj1 alloc_ceiling_val) as AC. pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7). unfold AMS in P3, P5.
pose proof md_facts as (Mh & Mlz & Mmat). assert (PG4 : PGSZ = 4096) by reflexivity.
destruct BN_facts as (Hb & B1 & B2 & B3 & B4 & B5 & E43v & EP). pose proof (u64_range b) as Ub. unfold PGSZ in B1, B3.
assert (E38 : ew E 38 = Z_to_bv 64 0) by (rewrite (agree_cx E 38 HA) by lia; cbn [cx]; rewrite Eaac; reflexivity).
assert (E37 : ew E 37 = Z_to_bv 64 0) by (rewrite (agree_cx E 37 HA) by lia; cbn [cx]; rewrite Eamc; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 0) by (rewrite (agree_cx E 33 HA) by lia; cbn [cx]; rewrite Efh; reflexivity).
eapply (SR_run_ecall src0segs src0tbl src0tbl_ok FUEL E (add_cond ss_b1 C_bn) ss_nQ); [exact Mh | exact Mlz | exact HS | apply run_bn |].
intros ms1 HS1 HF1.
assert (F1 : FRM (WF0 B sp) (ms_mem ms1)).
{ eapply FRM_run0; [intros x Hx; exact Hx | exact HA | exact HF | exact HF1 | exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj1 (conj (proj2 wsub_SK0) I)))))))))))]. }
destruct (st_ok_ecall_shape src0segs E ss_nQ ms1 HS1 eq_refl) as (regs1 & mem1 & Hms & Hregs & Hmem & HG).
rewrite Hms. rewrite Hms in F1. cbn [ms_mem pend_at] in F1. rewrite ss_nQ_pc.
apply SR_ret.
apply (knode_brk_query src0segs regs1 (Z_to_bv 64 (src0_A_alloc_meta + 0x144)) mem1 (seg_rom src0segs) md A0).
- exact Mh. - exact Mlz.
- rewrite (Hregs 17%bv). reflexivity.
- rewrite (Hregs 10%bv). reflexivity.
- rewrite (brk_keep_id (Z_to_bv 64 0) md Mlz Mmat). fold b.
destruct (HK 1) as (K1 & EK1 & K10 & K11). rewrite EK1. cbn [mreal].
pose proof (st_ok_resume_atom src0segs 72 F_pg E ss_nQ regs1 mem1 b Hregs Hmem HG (proj1 bn_checks)
ltac:(unfold F_pg; cbn [af_lo af_hi]; lia) ltac:(unfold F_pg; cbn [af_al2]; lia)
ltac:(unfold F_pg; cbn [af_al2]; change (2 ^ 12) with 4096; rewrite Hb; exact B1)) as HS2.
change (resume ss_nQ (SOff 72 0) (ss_mem ss_nQ) (mkFacts ((72%nat, F_pg) :: f_atoms (ss_facts ss_nQ)) (f_conds (ss_facts ss_nQ)) (f_alias (ss_facts ss_nQ)))) with ss_nQ1 in HS2.
rewrite ss_nQ_pc in HS2.
set (E1 := ewset E 72 b) in HS2.
assert (HA0x : env_agree 72 E E1) by (apply env_agree_ewset).
assert (HA01 : env_agree 46 E00 E1) by (apply (agree_step 46 72 _ _ _ HA HA0x); lia).
assert (E1_72 : ew E1 72 = Z_to_bv 64 (bv_unsigned b)) by (unfold E1; rewrite ew_ewset_same; symmetry; apply Z_to_bv_bv_unsigned).
assert (E1_38 : ew E1 38 = Z_to_bv 64 0) by (rewrite (agree_cx E1 38 HA01) by lia; cbn [cx]; rewrite Eaac; reflexivity).
assert (E1_37 : ew E1 37 = Z_to_bv 64 0) by (rewrite (agree_cx E1 37 HA01) by lia; cbn [cx]; rewrite Eamc; reflexivity).
assert (E1_33 : ew E1 33 = Z_to_bv 64 0) by (rewrite (agree_cx E1 33 HA01) by lia; cbn [cx]; rewrite Efh; reflexivity).
eapply (SR_run_ecall src0segs src0tbl src0tbl_ok FUEL E1 ss_nQ1 ss_nG); [exact Mh | exact Mlz | exact HS2 | apply run_nQ1 |].
intros ms2 HS3 HF3. cbn [ms_mem mkst] in HF3.
assert (F2 : FRM (WF0 B sp) (ms_mem ms2)) by (eapply FRM_run0; [intros x Hx; exact Hx | exact HA01 | exact F1 | exact HF3 | exact (proj1 wsub_BN)]).
destruct (st_ok_ecall_shape src0segs E1 ss_nG ms2 HS3 eq_refl) as (regs2 & mem2 & Hms2 & Hregs2 & Hmem2 & HG2).
rewrite Hms2. rewrite Hms2 in F2. cbn [ms_mem pend_at] in F2. rewrite ss_nG_pc.
assert (R10 : getr regs2 10 = Z_to_bv 64 (bv_unsigned b + 8192)) by (rewrite (Hregs2 10%bv); exact (sv_off E1 72 8192 _ E1_72)).
assert (U10 : bv_unsigned (getr regs2 10) = bv_unsigned b + 8192) by (rewrite R10; apply u64_of_Z; lia).
apply SR_ret.
apply (knode_brk_grow src0segs regs2 (Z_to_bv 64 (src0_A_alloc_meta + 0x168)) mem2 (seg_rom src0segs) md A0 2).
+ exact Mh. + exact Mlz.
+ rewrite (Hregs2 17%bv). reflexivity.
+ fold b. rewrite U10. unfold PGSZ. lia.
+ lia.
+ fold b. lia.
+ fold b. unfold page_size. rewrite Hb. exact B1.
+ fold b. lia.
+
rewrite (brk_keep_id (getr regs2 10) md Mlz Mmat). fold b.
pose proof (st_ok_resume_sv src0segs E1 ss_nG regs2 mem2 (SOff 72 0) b Hregs2 Hmem2 HG2 ltac:(rewrite (sv_off0 E1 72 _ E1_72); apply Z_to_bv_bv_unsigned)) as HS4.
change (resume ss_nG (SOff 72 0) (ss_mem ss_nG) (ss_facts ss_nG)) with ss_nR in HS4. rewrite ss_nG_pc in HS4.
apply (mreal_SR_pre src0segs (K1 0) _ _ (at_st ss_V (WF0 B sp) md)); [| exact K10].
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL PC_V E1 ss_nR ss_vBN RS_running); [exact Mh | exact Mlz | exact HS4 | apply run_nR |].
intros ms3 HS5 HF5. cbn [ms_mem mkst] in HF5.
assert (F3 : FRM (WF0 B sp) (ms_mem ms3)) by (eapply FRM_run0; [intros x Hx; exact Hx | exact HA01 | exact F2 | exact HF5 | exact (proj1 (proj2 wsub_BN))]).
destruct (to_V false ss_vBN E1 ms3 (proj1 (proj2 bn_checks)) HS5 HA01 ltac:(discriminate) E1_38 E1_37 E1_33) as (E' & HS6 & HA' & _).
apply SR_ret. exists E', ms3. split; [reflexivity|]. split; [exact HS6|]. split; [exact HA' | exact F3].
+
intros G. destruct (K11 1 ltac:(lia)) as (K3 & EK3 & K3r). rewrite EK3. cbn [mreal].
assert (Hreq0 : getr regs2 10 <> Z_to_bv 64 0) by (intros E0'; rewrite E0' in U10; change (bv_unsigned (Z_to_bv 64 0)) with 0 in U10; lia).
fold b in G |- *.
rewrite (brk_grow_ok_unfold md (getr regs2 10) (2 * PGSZ) Hreq0 ltac:(fold b; lia) ltac:(fold b; unfold page_size; rewrite Hb; exact B1) ltac:(fold b; rewrite U10; reflexivity) ltac:(unfold PGSZ; lia) eq_refl) in G.
apply andb_prop in G as [G _]. apply andb_prop in G as [Gtop Gfree2]. apply Z.leb_le in Gtop. fold b in Gtop, Gfree2.
assert (Gfree : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) b (Z_to_bv 64 (2 * PGSZ)) = true).
{ eapply region_free_prefix; [| exact Gfree2]. vm_compute. discriminate. }
assert (Gceil : bv_unsigned b + 2 * PGSZ <= alloc_ceiling).
{ assert (HPal2 : bv_unsigned b mod 4096 = 0) by (rewrite Hb; exact B1).
apply (YM05.grant_below_ceil _ _ (lg_ceil _ _ _ _ (mid_ledger _ _ _ _ _ MID))); [| exact Gtop].
unfold PGSZ. rewrite Z.add_mod, HPal2 by lia. reflexivity. }
set (md2 := brk_model (getr regs2 10) (getr regs2 10) md).
assert (MD2 : md2 = with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps md)) ((b, Z_to_bv 64 (2 * PGSZ)) :: vm_maps (m_vmmaps md)) (vm_noaccess (m_vmmaps md))
(vm_start_brk (m_vmmaps md)) (getr regs2 10) (vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md))) md).
{ unfold md2. rewrite (brk_model_grow (getr regs2 10) md (2 * PGSZ) Hreq0 ltac:(fold b; lia) ltac:(fold b; rewrite U10; reflexivity) ltac:(unfold PGSZ; lia)). reflexivity. }
assert (Mh2 : m_halted md2 = None) by (rewrite MD2, m_halted_with; exact Mh).
assert (Mlz2 : m_vm_lazy md2 = []) by (rewrite MD2, m_vm_lazy_with; exact Mlz).
assert (Mmat2 : m_vm_materialized md2 = []) by (rewrite MD2, m_vm_materialized_with; exact Mmat).
assert (VM2 : m_vmmaps md2 = mkVmMapsFull (vm_reserved (m_vmmaps md)) ((b, Z_to_bv 64 (2 * PGSZ)) :: vm_maps (m_vmmaps md)) (vm_noaccess (m_vmmaps md))
(vm_start_brk (m_vmmaps md)) (getr regs2 10) (vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md))) by (rewrite MD2, m_vmmaps_with; reflexivity).
unfold PGSZ in Gceil.
assert (Pfacts : forall x, bv_unsigned b <= x < bv_unsigned b + 8192 -> ~ in_img B x /\ 4096 <= x < alloc_ceiling).
{ intros x Hx. split; [| lia]. intros Hi.
exact (fresh_img B L A md (mid_ledger _ _ _ _ _ MID) b (2 * PGSZ) ltac:(unfold PGSZ; lia) ltac:(lia) ltac:(unfold PGSZ; lia) Gfree x Hi ltac:(unfold PGSZ; lia)). }
assert (Hmem4 : mem_ok src0segs E1 (apply_zeros mem2 [(Z_to_bv 64 (bv_unsigned b), Z_to_bv 64 8192)]) (ss_mem ss_nG)).
{ apply (mem_ok_zeros_outside src0segs E1 mem2 (ss_mem ss_nG) (bv_unsigned b) 8192 Hmem2); [lia | lia | lia |].
intros r' Hr'. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite (proj1 sk_BN) in Hr'.
destruct (SK0_apart E1 (bv_unsigned b) 8192 r' (agree_reg2 E1 HA01) ltac:(lia) Pfacts Hr') as [H|H]; [right; exact H | left; exact H]. }
replace (apply_zeros mem2 [(b, Z_to_bv 64 (PGSZ * 2))]) with (apply_zeros mem2 [(Z_to_bv 64 (bv_unsigned b), Z_to_bv 64 8192)]) by (rewrite Z_to_bv_bv_unsigned; reflexivity).
pose proof (st_ok_resume_sv src0segs E1 ss_nG regs2 _ (SOff 72 8192) (getr regs2 10) Hregs2 Hmem4 HG2 ltac:(rewrite R10; exact (sv_off E1 72 8192 _ E1_72))) as HS4.
change (resume ss_nG (SOff 72 8192) (ss_mem ss_nG) (ss_facts ss_nG)) with ss_nGG in HS4. rewrite ss_nG_pc in HS4.
change (brk_model (getr regs2 10) (getr regs2 10) md) with md2.
destruct (zeros_frame_n (WF0 B sp) mem2 (bv_unsigned b) 8192 F2 ltac:(lia) ltac:(lia) ltac:(lia)) as [F4 PZ4].
set (W := fun x => WF0 B sp x \/ bv_unsigned b <= x < bv_unsigned b + 8192) in F4.
assert (PZ4' : forall i, 0 <= i < PGSZ -> apply_zeros mem2 [(Z_to_bv 64 (bv_unsigned b), Z_to_bv 64 8192)] (Z_to_bv 64 (bv_unsigned b + 4096 + i)) = Some (Z_to_bv 8 0)).
{ intros i Hi. unfold PGSZ in Hi. replace (bv_unsigned b + 4096 + i) with (bv_unsigned b + (4096 + i)) by lia. apply PZ4. lia. }
eapply (SR_run_ecall src0segs src0tbl src0tbl_ok FUEL E1 ss_nGG ss_nK3); [exact Mh2 | exact Mlz2 | exact HS4 | apply run_nGG |].
intros ms3 HS5 HF5. cbn [ms_mem mkst] in HF5.
assert (F5 : FRM W (ms_mem ms3)) by (eapply FRM_run0; [intros x Hx; left; exact Hx | exact HA01 | exact F4 | exact HF5 | exact (proj1 (proj2 (proj2 wsub_BN)))]).
assert (PZ5 : forall i, 0 <= i < PGSZ -> ms_mem ms3 (Z_to_bv 64 (bv_unsigned b + 4096 + i)) = Some (Z_to_bv 8 0)).
{ apply (PZ_run E1 (ss_mem ss_nGG) _ _ (bv_unsigned b + 4096) HA01 HF5 (proj1 (proj2 (proj2 wsub_BN)))); [intros x Hx; apply Pfacts; lia | lia | lia | exact PZ4']. }
destruct (st_ok_ecall_shape src0segs E1 ss_nK3 ms3 HS5 eq_refl) as (regs3 & mem3 & Hms3 & Hregs3 & Hmem3 & HG3).
rewrite Hms3. rewrite Hms3 in F5, PZ5. cbn [ms_mem pend_at] in F5, PZ5. rewrite ss_nK3_pc.
assert (R10' : getr regs3 10 = Z_to_bv 64 (bv_unsigned b)) by (rewrite (Hregs3 10%bv); exact (sv_off0 E1 72 _ E1_72)).
assert (U10' : bv_unsigned (getr regs3 10) = bv_unsigned b) by (rewrite R10'; apply u64_of_Z; lia).
assert (R11' : getr regs3 11 = Z_to_bv 64 4096) by (rewrite (Hregs3 11%bv); reflexivity).
assert (MAPS : forall e, In e (vm_maps (m_vmmaps md)) -> 0 < iv_len e /\ (iv_lo e + iv_len e <= bv_unsigned b \/ bv_unsigned b + 4096 <= iv_lo e)).
{ intros e He. pose proof (lx_maps _ _ _ (mid_ledgerx _ _ _ _ _ MID) e He) as [Hl _]. split; [exact Hl|].
pose proof (fresh_entry L A md (mid_ledgerx _ _ _ _ _ MID) b (2 * PGSZ) ltac:(unfold PGSZ; lia) ltac:(lia) ltac:(unfold PGSZ; lia) Gfree e He) as D.
unfold ranges_disjoint in D. cbn [fst snd] in D. unfold PGSZ in D. lia. }
apply SR_ret.
apply (knode_guard src0segs regs3 (Z_to_bv 64 (src0_A_mmap + 0xc4)) mem3 (seg_rom src0segs) md2 (sBN A)).
* exact Mh2. * exact Mlz2.
* rewrite (Hregs3 17%bv). reflexivity.
* exact R11'.
* rewrite (Hregs3 12%bv). reflexivity.
* rewrite (Hregs3 13%bv). reflexivity.
* rewrite (Hregs3 14%bv). apply bv_eq. vm_compute. reflexivity.
* rewrite (Hregs3 15%bv). reflexivity.
* rewrite U10'. unfold page_size. rewrite Hb. exact B1.
* rewrite U10'. lia.
*   rewrite U10', VM2. unfold alloc_top in Gtop |- *. cbn [vm_init_sp]. unfold PGSZ in Gtop. lia.
* rewrite VM2. cbn [vm_reserved]. rewrite (lg_reserved _ _ _ _ (mid_ledger _ _ _ _ _ MID)). apply region_free_above_top. rewrite U10', Hb. exact B5.
* rewrite VM2. cbn [vm_maps]. apply map_contains_head; rewrite U10'; [lia|]. rewrite (u64_of_Z (2 * PGSZ)) by (unfold PGSZ; lia).
change (bv_unsigned (Z_to_bv 64 4096)) with 4096. unfold PGSZ. lia.
*
assert (KEPT : forall mem4 md3,
(vm_maps (m_vmmaps md3) = (b, w64 (2 * PGSZ)) :: vm_maps (m_vmmaps md) \/
vm_maps (m_vmmaps md3) = (w64 (bv_unsigned b + PGSZ), w64 PGSZ) :: vm_maps (m_vmmaps md)) ->
(forall lo n, 0 < bv_unsigned n ->
(bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + 2 * PGSZ <= bv_unsigned lo) ->
map_contains (vm_noaccess (m_vmmaps md)) lo n = true -> map_contains (vm_noaccess (m_vmmaps md3)) lo n = true) ->
(forall e, In e (vm_noaccess (m_vmmaps md3)) ->
(exists e0, In e0 (vm_noaccess (m_vmmaps md)) /\ iv_lo e0 <= iv_lo e /\ iv_lo e + iv_len e <= iv_lo e0 + iv_len e0) \/
(exists E, In E (vm_maps (m_vmmaps md3)) /\ iv_lo E <= iv_lo e /\ iv_lo e + iv_len e <= iv_lo E + iv_len E /\
bv_unsigned b <= iv_lo E /\ iv_lo E + iv_len E <= bv_unsigned b + 2 * PGSZ)) ->
vm_reserved (m_vmmaps md3) = vm_reserved (m_vmmaps md) -> vm_start_brk (m_vmmaps md3) = vm_start_brk (m_vmmaps md) ->
bv_unsigned (vm_brk (m_vmmaps md3)) = bv_unsigned b + 2 * PGSZ -> vm_limit (m_vmmaps md3) = vm_limit (m_vmmaps md) ->
alloc_top (m_vmmaps md3) = alloc_top (m_vmmaps md)   ->
m_halted md3 = None /\ m_vm_lazy md3 = [] /\ m_vm_materialized md3 = [] -> (exists vm', md3 = with_vmmaps vm' md) ->
mem_ok src0segs E1 mem4 (ss_mem ss_nK3) -> FRM W mem4 ->
(forall i, 0 <= i < PGSZ -> mem4 (Z_to_bv 64 (bv_unsigned b + 4096 + i)) = Some (Z_to_bv 8 0)) ->
forall rv ssg Cg ssO,
sv_denot E1 rv = (match rv with SOff _ _ => b | _ => Z_to_bv 64 (2 ^ 64 - 12) end) ->
sym_runN src0segs src0tbl FUEL (resume_ ss_nK3 rv (ss_mem ss_nK3)) = (ssg, RS_stopped (SR_branch BC_NE (ac_a Cg) (SLit 0))) ->
ac_c Cg = BC_NE -> ac_b Cg = SLit 0 ->
branch_taken BC_NE (sv_denot E1 (ac_a Cg)) (sv_denot E1 (SLit 0)) = true ->
wsub (ss_mem (resume_ ss_nK3 rv (ss_mem ss_nK3))) SK0 = true -> wsub (ss_mem (add_cond ssg Cg)) SK0 = true ->
sym_run_toN src0segs src0tbl FUEL PC_O (add_cond ssg Cg) = (ssO, RS_running) ->
absO_check ssO (SLit 1) (SOff 39 0) (SOff 72 8192) = true -> sr_get (ss_regs ssO) 9 = SOff 72 4096 ->
SR src0segs (mkCfg (mkst (regupd regs3 10 (sv_denot E1 rv)) (v_addi (Z_to_bv 64 (src0_A_mmap + 0xc4)) 4) mem4 (seg_rom src0segs)) md3)
(fun c' => Qspec (Some (padd p AREA_HDR), take_st (open_st p (sBN A))) -> POST (Some (padd p AREA_HDR), take_st (open_st p (sBN A))) c')).
{ intros mem4 md3 VM3 VN3 VNX3 VR3 VS3 VB3 VL3 VT3 MD3 MDW3 Hmem4' F6 PZ6 rv ssg Cg ssO Hrv RUN1 HCc HCb BT W1 W2 RUN2 CK SG9.
destruct MD3 as (Mh3 & Mlz3 & Mmat3).
pose proof (st_ok_resume_sv src0segs E1 ss_nK3 regs3 mem4 rv (sv_denot E1 rv) Hregs3 Hmem4' HG3 eq_refl) as HS6.
change (resume ss_nK3 rv (ss_mem ss_nK3) (ss_facts ss_nK3)) with (resume_ ss_nK3 rv (ss_mem ss_nK3)) in HS6. rewrite ss_nK3_pc in HS6.
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E1 _ ssg); [exact Mh3 | exact Mlz3 | exact HS6 | exact RUN1 |].
intros ms4 HS7 HF7. cbn [ms_mem mkst] in HF7.
assert (F7 : FRM W (ms_mem ms4)) by (eapply FRM_run0; [intros x Hx; left; exact Hx | exact HA01 | exact F6 | exact HF7 | exact W1]).
assert (PZ7 : forall i, 0 <= i < PGSZ -> ms_mem ms4 (Z_to_bv 64 (bv_unsigned b + 4096 + i)) = Some (Z_to_bv 8 0)).
{ apply (PZ_run E1 _ _ _ (bv_unsigned b + 4096) HA01 HF7 W1); [intros x Hx; apply Pfacts; lia | lia | lia | exact PZ6]. }
apply (st_ok_add_cond src0segs E1 ssg ms4 BC_NE (ac_a Cg) (SLit 0)) in HS7; [| exact BT].
replace (add_cond ssg (mkAC BC_NE (ac_a Cg) (SLit 0))) with (add_cond ssg Cg) in HS7 by (destruct Cg; cbn in HCc, HCb; subst; reflexivity).
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL PC_O E1 (add_cond ssg Cg) ssO RS_running); [exact Mh3 | exact Mlz3 | exact HS7 | exact RUN2 |].
intros ms5 HS8 HF8.
assert (F8 : FRM W (ms_mem ms5)) by (eapply FRM_run0; [intros x Hx; left; exact Hx | exact HA01 | exact F7 | exact HF8 | exact W2]).
assert (PZ8 : forall i, 0 <= i < PGSZ -> ms_mem ms5 (Z_to_bv 64 (bv_unsigned b + 4096 + i)) = Some (Z_to_bv 8 0)).
{ apply (PZ_run E1 _ _ _ (bv_unsigned b + 4096) HA01 HF8 W2); [intros x Hx; apply Pfacts; lia | lia | lia | exact PZ7]. }
exact (bn_leaf E1 ssO ms5 md3 ltac:(unfold PGSZ; lia) Gfree VM3 VN3 VNX3 VR3 VS3 VB3 VL3 VT3 (conj Mh3 (conj Mlz3 Mmat3)) MDW3 CK SG9 HS8 HA01 E1_72 F8 PZ8). }
assert (BT1 : branch_taken BC_NE (sv_denot E1 (ac_a C_gok1)) (sv_denot E1 (SLit 0)) = true).
{ cbn [ac_a C_gok1 sv_denot]. rewrite branch_ne. apply Bool.negb_true_iff. apply Z.eqb_neq. rewrite alu64_or, E1_72.
rewrite (lit64_small (bv_unsigned b)) by lia. rewrite Z.add_0_r, (lit64_small (bv_unsigned b)), (lit64_small 11), (lit64_small 0) by lia.
intros H0. apply Z.lor_eq_0_iff in H0. lia. }
assert (BT2 : branch_taken BC_NE (sv_denot E1 (ac_a C_gok2)) (sv_denot E1 (SLit 0)) = true).
{ cbn [ac_a C_gok2 sv_denot]. rewrite branch_ne. apply Bool.negb_true_iff. apply Z.eqb_neq. rewrite alu64_or, E1_72.
rewrite (lit64_small (bv_unsigned b)) by lia. rewrite Z.add_0_r, (lit64_small (bv_unsigned b)), (lit64_small 0) by lia.
intros H0. apply Z.lor_eq_0_iff in H0. lia. }
assert (VB2 : bv_unsigned (vm_brk (m_vmmaps md2)) = bv_unsigned b + 2 * PGSZ) by (rewrite VM2; cbn [vm_brk]; rewrite U10; reflexivity).
assert (MDW2 : exists vm', md2 = with_vmmaps vm' md) by (eexists; exact MD2).
assert (E4096 : bv_unsigned (Z_to_bv 64 4096) = 4096) by reflexivity.
intros [[e He] | [[] | [e He]]]; rewrite (K3r 1); cbn [mreal fixed_nx proj1_sig].
--
assert (Ee : errno_ret e = Z_to_bv 64 (2 ^ 64 - 12)) by (destruct He as [<-|[]]; unfold errno_ret; apply bv_eq; reflexivity).
rewrite Ee.
refine (KEPT mem3 md2 _ _ _ _ _ VB2 _ _ (conj Mh2 (conj Mlz2 Mmat2)) MDW2
Hmem3 F5 PZ5 (SLit (2 ^ 64 - 12)) ss_g1 C_gok1 ss_oN1 eq_refl run_g1 eq_refl eq_refl BT1
(proj1 (proj2 (proj2 (proj2 wsub_BN)))) (proj1 (proj2 (proj2 (proj2 (proj2 wsub_BN))))) run_g1'
(proj1 (proj2 (proj2 bn_checks))) (proj1 (proj2 (proj2 (proj2 (proj2 bn_checks))))));
[left; rewrite VM2; reflexivity | rewrite VM2; cbn [vm_noaccess]; intros lo n _ _ Hc; exact Hc
| rewrite VM2; cbn [vm_noaccess]; intros e2 He2; left; exists e2; split; [exact He2 | lia]
| rewrite VM2; reflexivity | rewrite VM2; reflexivity | rewrite VM2; reflexivity | rewrite VM2; reflexivity].
--
rewrite R11'. change (page_round_up (Z_to_bv 64 4096)) with (Z_to_bv 64 4096).
destruct (fixed_models_shape (getr regs3 10) (Z_to_bv 64 4096) md2 Mlz2 Mmat2) as [(SH & MD3) _].
set (md3 := mmap_fixed_model (getr regs3 10) (Z_to_bv 64 4096) md2) in *.
assert (VM3 : m_vmmaps md3 = mkVmMapsFull (vm_reserved (m_vmmaps md)) ((b, Z_to_bv 64 (2 * PGSZ)) :: vm_maps (m_vmmaps md))
((getr regs3 10, Z_to_bv 64 4096) :: maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned b) (bv_unsigned b + 4096))
(vm_start_brk (m_vmmaps md)) (getr regs2 10) (vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md))).
{ unfold md3. rewrite mmap_fixed_model_vmmaps, VM2. cbn. rewrite U10', E4096. reflexivity. }
assert (Hmem4' : mem_ok src0segs E1 (apply_unmaps mem3 [(Z_to_bv 64 (bv_unsigned b), Z_to_bv 64 4096)]) (ss_mem ss_nK3)).
{ apply (mem_ok_unmap src0segs E1 mem3 (ss_mem ss_nK3) (bv_unsigned b) 4096 Hmem3); [lia | lia | lia |].
intros r' Hr'. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite (proj2 sk_BN) in Hr'.
destruct (SK0_apart E1 (bv_unsigned b) 4096 r' (agree_reg2 E1 HA01) ltac:(lia) ltac:(intros x Hx; apply Pfacts; lia) Hr') as [H|H]; [right; exact H | left; exact H]. }
replace (apply_unmaps mem3 [(getr regs3 10, Z_to_bv 64 4096)]) with (apply_unmaps mem3 [(Z_to_bv 64 (bv_unsigned b), Z_to_bv 64 4096)]) by (rewrite R10'; reflexivity).
replace (getr regs3 10) with (sv_denot E1 (SOff 72 0)) at 1 by (rewrite R10'; exact (sv_off0 E1 72 _ E1_72)).
destruct MD3 as (Mh3 & Mlz3 & Mmat3). rewrite Mh2 in Mh3.
refine (KEPT _ md3 _ _ _ _ _ _ _ _ (conj Mh3 (conj Mlz3 Mmat3)) _ Hmem4' _ _ (SOff 72 0) ss_g2 C_gok2 ss_oN2 ltac:(rewrite (sv_off0 E1 72 _ E1_72); apply Z_to_bv_bv_unsigned) run_g2 eq_refl eq_refl BT2
(proj1 (proj2 (proj2 (proj2 (proj2 (proj2 wsub_BN)))))) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 wsub_BN)))))) run_g2'
(proj1 (proj2 (proj2 (proj2 bn_checks)))) (proj2 (proj2 (proj2 (proj2 (proj2 bn_checks))))));
[ left; rewrite VM3; reflexivity
| rewrite VM3; cbn [vm_noaccess]; intros lo n Hn Hd Hc; apply map_contains_cons'; apply map_contains_subtract; [lia | exact Hc | exact Hn | unfold PGSZ in Hd; lia]
| rewrite VM3; cbn [vm_noaccess vm_maps]; intros e2 [<- | He2];
[ right; exists (b, Z_to_bv 64 (2 * PGSZ)); split; [left; reflexivity|];
unfold iv_lo, iv_len; cbn [fst snd]; rewrite U10', E4096, (u64_of_Z (2 * PGSZ)) by (unfold PGSZ; lia); unfold PGSZ; lia
| left; eapply In_maps_subtract_sub; [| exact He2]; lia ]
| rewrite VM3; reflexivity | rewrite VM3; reflexivity | rewrite VM3; cbn [vm_brk]; rewrite U10; reflexivity | rewrite VM3; reflexivity | rewrite VM3; reflexivity
| rewrite SH, MD2, with_vmmaps_twice'; eexists; reflexivity | | ].
** intros x Hx Hn. rewrite apply_unmaps1_out; [exact (F5 x Hx Hn)|]. rewrite !u64_of_Z by lia.
destruct (Z_lt_le_dec x (bv_unsigned b)); [left; lia|]. right. destruct (Z_lt_le_dec x (bv_unsigned b + 4096)); [exfalso; apply Hn; right; lia | lia].
** intros i Hi. unfold PGSZ in Hi. rewrite apply_unmaps1_out; [exact (PZ5 i ltac:(unfold PGSZ; lia))|]. rewrite !u64_of_Z by lia. right. lia.
--
assert (Ee : errno_ret e = Z_to_bv 64 (2 ^ 64 - 12)) by (destruct He as [<-|[]]; unfold errno_ret; apply bv_eq; reflexivity).
rewrite Ee, R11'. change (page_round_up (Z_to_bv 64 4096)) with (Z_to_bv 64 4096).
destruct (fixed_models_shape (getr regs3 10) (Z_to_bv 64 4096) md2 Mlz2 Mmat2) as [_ (SH & MD3)].
set (md3 := mmap_fixed_destroyed_model (getr regs3 10) (Z_to_bv 64 4096) md2) in *.
assert (VM3 : m_vmmaps md3 = mkVmMapsFull (vm_reserved (m_vmmaps md))
((Z_to_bv 64 (bv_unsigned b + 4096), Z_to_bv 64 4096) :: vm_maps (m_vmmaps md))
(maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned b) (bv_unsigned b + 4096))
(vm_start_brk (m_vmmaps md)) (getr regs2 10) (vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md))).
{ unfold md3. rewrite mmap_fixed_destroyed_model_vmmaps, VM2. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp]. rewrite U10', E4096.
cbn [maps_subtract]. rewrite (length_iv_subtract_prefix b (Z_to_bv 64 (2 * PGSZ)) (bv_unsigned b) (bv_unsigned b + 4096) eq_refl ltac:(lia) ltac:(rewrite (u64_of_Z (2 * PGSZ)) by (unfold PGSZ; lia); unfold PGSZ; lia)).
rewrite (u64_of_Z (2 * PGSZ)) by (unfold PGSZ; lia). rewrite (length_maps_subtract_keep (vm_maps (m_vmmaps md)) (bv_unsigned b) (bv_unsigned b + 4096) ltac:(lia) MAPS).
cbn [app]. replace (bv_unsigned b + 2 * PGSZ - (bv_unsigned b + 4096)) with 4096 by (unfold PGSZ; lia). reflexivity. }
assert (Hmem4' : mem_ok src0segs E1 (apply_unmaps mem3 [(Z_to_bv 64 (bv_unsigned b), Z_to_bv 64 4096)]) (ss_mem ss_nK3)).
{ apply (mem_ok_unmap src0segs E1 mem3 (ss_mem ss_nK3) (bv_unsigned b) 4096 Hmem3); [lia | lia | lia |].
intros r' Hr'. apply (in_map (fun r => (r_base r, r_lo r, r_hi r))) in Hr'. rewrite (proj2 sk_BN) in Hr'.
destruct (SK0_apart E1 (bv_unsigned b) 4096 r' (agree_reg2 E1 HA01) ltac:(lia) ltac:(intros x Hx; apply Pfacts; lia) Hr') as [H|H]; [right; exact H | left; exact H]. }
replace (apply_unmaps mem3 [(getr regs3 10, Z_to_bv 64 4096)]) with (apply_unmaps mem3 [(Z_to_bv 64 (bv_unsigned b), Z_to_bv 64 4096)]) by (rewrite R10'; reflexivity).
destruct MD3 as (Mh3 & Mlz3 & Mmat3). rewrite Mh2 in Mh3.
refine (KEPT _ md3 _ _ _ _ _ _ _ _ (conj Mh3 (conj Mlz3 Mmat3)) _ Hmem4' _ _ (SLit (2 ^ 64 - 12)) ss_g1 C_gok1 ss_oN1 eq_refl run_g1 eq_refl eq_refl BT1
(proj1 (proj2 (proj2 (proj2 wsub_BN)))) (proj1 (proj2 (proj2 (proj2 (proj2 wsub_BN))))) run_g1'
(proj1 (proj2 (proj2 bn_checks))) (proj1 (proj2 (proj2 (proj2 (proj2 bn_checks))))));
[ right; rewrite VM3; reflexivity
| rewrite VM3; cbn [vm_noaccess]; intros lo n Hn Hd Hc; apply map_contains_subtract; [lia | exact Hc | exact Hn | unfold PGSZ in Hd; lia]
| rewrite VM3; cbn [vm_noaccess]; intros e2 He2; left; eapply In_maps_subtract_sub; [| exact He2]; lia
| rewrite VM3; reflexivity | rewrite VM3; reflexivity | rewrite VM3; cbn [vm_brk]; rewrite U10; reflexivity | rewrite VM3; reflexivity | rewrite VM3; reflexivity
| rewrite SH, MD2, with_vmmaps_twice'; eexists; reflexivity | | ].
** intros x Hx Hn. rewrite apply_unmaps1_out; [exact (F5 x Hx Hn)|]. rewrite !u64_of_Z by lia.
destruct (Z_lt_le_dec x (bv_unsigned b)); [left; lia|]. right. destruct (Z_lt_le_dec x (bv_unsigned b + 4096)); [exfalso; apply Hn; right; lia | lia].
** intros i Hi. unfold PGSZ in Hi. rewrite apply_unmaps1_out; [exact (PZ5 i ltac:(unfold PGSZ; lia))|]. rewrite !u64_of_Z by lia. right. lia.
+
intros (_ & Hrg & _). change (st_regions A0) with (st_regions A) in Hrg. fold b.
rewrite (brk_grow_ok_unfold md (getr regs2 10) (2 * PGSZ) ltac:(intros E0'; rewrite E0' in U10; change (bv_unsigned (Z_to_bv 64 0)) with 0 in U10; lia)
ltac:(fold b; lia) ltac:(fold b; unfold page_size; rewrite Hb; exact B1) ltac:(fold b; rewrite U10; reflexivity) ltac:(unfold PGSZ; lia) eq_refl).
fold b. apply andb_true_intro. split; [apply andb_true_intro; split|].
* apply Z.leb_le.
pose proof (YM05.ceil_le_top _ (lg_ceil _ _ _ _ (mid_ledger _ _ _ _ _ MID))) as Htop.
pose proof (lg_brk0 _ _ _ _ (mid_ledger _ _ _ _ _ MID)) as (_ & _ & B3' & _ & _). unfold PGSZ in B3' |- *. lia.
* rewrite region_free_app. apply andb_true_intro. split.
-- rewrite (lg_reserved _ _ _ _ (mid_ledger _ _ _ _ _ MID)). apply region_free_above_top. rewrite Hb. exact B5.
-- pose proof (lg_count _ _ _ _ (mid_ledger _ _ _ _ _ MID)) as CNT. unfold nslots in CNT. rewrite Hrg in CNT. cbn in CNT.
destruct (vm_maps (m_vmmaps md)); [reflexivity | cbn in CNT; lia].
* apply Z.leb_le. pose proof (lg_backing _ _ _ _ (mid_ledger _ _ _ _ _ MID)) as BK. pose proof (lg_limit _ _ _ _ (mid_ledger _ _ _ _ _ MID)) as LM.
unfold live_bytes in BK. rewrite Hrg in BK. cbn in BK. unfold SRC_LIM_MIN, PGSZ in *. lia.
Qed.
End h0.
Lemma bd_checks : absV_check true ss_vBD = true.
Proof. vm_compute. reflexivity. Qed.
Lemma reach_b0 : forall c, st_avail_meta_area_count A = 0 -> at_st ss_aac (WF0 B sp) md c -> SR src0segs c (at_st ss_b0 (WF0 B sp) md).
Proof.
intros c Eaac (E & ms & -> & HS & HA & HF). pose proof md_facts as (Mh & Mlz & _).
apply (st_ok_add_cond src0segs E ss_aac ms BC_EQ (SOff 38 0) (SLit 0)) in HS.
2:{ rewrite (sv_cx E 38 HA ltac:(lia)). cbn [cx sv_denot]. rewrite Eaac, branch_eq. reflexivity. }
change (add_cond ss_aac (mkAC BC_EQ (SOff 38 0) (SLit 0))) with (add_cond ss_aac C_aac0) in HS.
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E _ ss_b0); [exact Mh | exact Mlz | exact HS | apply run_aac0 |].
intros ms1 HS1 HF1. apply SR_ret. exists E, ms1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HA|].
eapply FRM_run0; [intros x Hx; exact Hx | exact HA | exact HF | exact HF1 | exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 wsub_SK0))))))].
Qed.
Lemma reach_V_BD : forall c, st_brk A = BrkDead -> st_free_meta_head A = None -> st_avail_meta_count A = 0 -> st_avail_meta_area_count A = 0 ->
at_st ss_b0 (WF0 B sp) md c -> SR src0segs c (at_st ss_V (WF0 B sp) md).
Proof.
intros c Hbk Efh Eamc Eaac (E & ms & -> & HS & HA & HF). pose proof md_facts as (Mh & Mlz & _).
assert (E43 : ew E 43 = Z_to_bv 64 (2 ^ 64 - 1)).
{ rewrite (agree_cx E 43 HA) by lia. cbn [cx]. unfold brkv. rewrite Hbk. cbn [sval_num]. apply bv_eq. reflexivity. }
assert (E38 : ew E 38 = Z_to_bv 64 0) by (rewrite (agree_cx E 38 HA) by lia; cbn [cx]; rewrite Eaac; reflexivity).
assert (E37 : ew E 37 = Z_to_bv 64 0) by (rewrite (agree_cx E 37 HA) by lia; cbn [cx]; rewrite Eamc; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 0) by (rewrite (agree_cx E 33 HA) by lia; cbn [cx]; rewrite Efh; reflexivity).
apply (st_ok_add_cond src0segs E ss_b0 ms BC_EQ (SOff 43 0) (SLit (2 ^ 64 - 1))) in HS.
2:{ rewrite (sv_off0 E 43 _ E43). rewrite branch_eq. apply Z.eqb_refl. }
change (add_cond ss_b0 (mkAC BC_EQ (SOff 43 0) (SLit (2 ^ 64 - 1)))) with (add_cond ss_b0 C_bd) in HS.
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL PC_V E _ ss_vBD RS_running); [exact Mh | exact Mlz | exact HS | apply run_bd |].
intros ms1 HS1 HF1.
assert (F1 : FRM (WF0 B sp) (ms_mem ms1)).
{ eapply FRM_run0; [intros x Hx; exact Hx | exact HA | exact HF | exact HF1 | exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 wsub_SK0))))))))]. }
destruct (to_V true ss_vBD E ms1 bd_checks HS1 HA (fun _ => E43) E38 E37 E33) as (E' & HS2 & HA' & _).
apply SR_ret. exists E', ms1. split; [reflexivity|]. split; [exact HS2|]. split; [exact HA' | exact F1].
Qed.
Lemma reach_b1 : forall c, cx 43 <> 2 ^ 64 - 1 -> 0 <= cx 43 < 2 ^ 64 -> at_st ss_b0 (WF0 B sp) md c -> SR src0segs c (at_st ss_b1 (WF0 B sp) md).
Proof.
intros c H43 R43 (E & ms & -> & HS & HA & HF). pose proof md_facts as (Mh & Mlz & _).
apply (st_ok_add_cond_neg src0segs E ss_b0 ms BC_EQ (SOff 43 0) (SLit (2 ^ 64 - 1))) in HS.
2:{ rewrite (sv_cx E 43 HA ltac:(lia)). cbn [sv_denot]. rewrite branch_eq. rewrite !u64_of_Z by lia. apply Z.eqb_neq. exact H43. }
change (add_cond ss_b0 (mkAC (neg_bc BC_EQ) (SOff 43 0) (SLit (2 ^ 64 - 1)))) with (add_cond ss_b0 C_nbd) in HS.
eapply (SR_run_stop src0segs src0tbl src0tbl_ok FUEL E _ ss_b1); [exact Mh | exact Mlz | exact HS | apply run_nbd |].
intros ms1 HS1 HF1. apply SR_ret. exists E, ms1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HA|].
eapply FRM_run0; [intros x Hx; exact Hx | exact HA | exact HF | exact HF1 | exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 wsub_SK0)))))))))].
Qed.
Lemma at_b1_cond : forall c (cnd : acond) bc, ac_a cnd = SOff 43 0 -> ac_b cnd = SLit 0 -> ac_c cnd = bc ->
(forall E, env_agree 46 E00 E -> branch_taken bc (sv_denot E (SOff 43 0)) (sv_denot E (SLit 0)) = true) ->
at_st ss_b1 (WF0 B sp) md c -> at_st (add_cond ss_b1 cnd) (WF0 B sp) md c.
Proof.
intros c cnd bc Ha Hb Hc BT (E & ms & -> & HS & HA & HF). exists E, ms. split; [reflexivity|]. split; [| split; [exact HA | exact HF]].
destruct cnd as [cc ca cb]. cbn in Ha, Hb, Hc. subst. apply st_ok_add_cond; [exact HS | exact (BT E HA)].
Qed.
Theorem alloc_meta_AM : mreal src0segs (mkCfg ms0 md) (alloc_meta A) (fun r c' => Qspec r -> POST r c').
Proof.
pose proof (proj1 alloc_ceiling_val) as AC. pose proof (inv_ctx HI) as CT.
assert (AAC0 : 0 <= st_avail_meta_area_count A) by (destruct CT as (_&_&_&_&_&_&_&_&_&_&C11&_); exact C11).
rewrite alloc_meta_tree. change (set_init_done true A) with A0.
destruct (st_free_meta_head A) as [m|] eqn:Efh.
-
destruct (deq_shape X R U A0 m HI0 Efh) as (rest & s1 & RING & MTm & MEMS & Edq & DP).
change (st_free_meta_head A0) with (st_free_meta_head A) in DP.
change (dequeue HFreeMeta m A0) with (dequeue HFreeMeta m (set_init_done true A)) in Edq.
change (set_init_done true A) with A0 in Edq. rewrite Edq. cbn [ibind snd mreal].
eapply SR_bind; [exact reach_A2|]. intros c1 H1. eapply SR_bind; [exact (reach_fh c1 H1)|]. intros c2 H2.
eapply SR_mono; [exact (path_D m rest s1 Efh RING MTm MEMS DP c2 H2) | intros c' H' _; exact H'].
- destruct (0 <? st_avail_meta_count A) eqn:Hamc.
+
apply Z.ltb_lt in Hamc. cbn [mreal].
eapply SR_bind; [exact reach_A2|]. intros c1 H1.
eapply SR_mono; [exact (path_C Efh Hamc c1 H1) | intros c' H' _; exact H'].
+ apply Z.ltb_ge in Hamc. pose proof amc_range as AR. assert (Eamc : st_avail_meta_count A = 0) by lia. clear Hamc AR.
assert (REACH : SR src0segs (mkCfg ms0 md) (at_st ss_aac (WF0 B sp) md)).
{ eapply SR_bind; [exact reach_A2|]. intros c1 H1. eapply SR_bind; [exact (reach_fh c1 H1)|]. intros c2 H2.
eapply SR_bind; [exact (reach_amc c2 Efh H2)|]. intros c3 H3. exact (reach_aac c3 Eamc H3). }
destruct (Z.eq_dec (st_avail_meta_area_count A) 0) as [Eaac|Haac].
* assert (REACH0 : SR src0segs (mkCfg ms0 md) (at_st ss_b0 (WF0 B sp) md)).
{ eapply SR_bind; [exact REACH|]. intros c1 H1. exact (reach_b0 c1 Eaac H1). }
destruct (brkst_cases (st_brk A)) as [Hbk | [Hbk | (rb & pages & Hbk)]].
--
destruct (am_area_BN A0 Eaac Hbk) as (k0 & Ek0 & Hk0). rewrite Ek0. cbn [ibind mreal].
eapply SR_bind; [exact REACH0|]. intros c1 H1.
eapply SR_bind; [apply (reach_b1 c1); [cbn [cx]; unfold brkv; rewrite Hbk; cbn; lia | cbn [cx]; unfold brkv; rewrite Hbk; cbn; lia | exact H1]|]. intros c2 H2.
apply (path_BN Efh Eamc Eaac Hbk c2 (fun z => ibind (k0 z) am_after_area)).
++ apply (at_b1_cond c2 C_bn BC_EQ eq_refl eq_refl eq_refl); [| exact H2].
intros E HA. rewrite (sv_cx E 43 HA ltac:(lia)). cbn [cx sv_denot]. unfold brkv. rewrite Hbk. cbn [sval_num]. rewrite branch_eq. reflexivity.
++ intros z0. destruct (Hk0 z0) as (k1 & Ek1 & Hk10 & Hk11). exists (fun z => ibind (k1 z) am_after_area).
split; [rewrite Ek1; reflexivity|]. split.
** intros c3 H3. rewrite Hk10. destruct (am_resv_tree (set_brk BrkDead A0) Eaac) as (k & Ek & Hk0' & Hk1'). rewrite Ek. cbn [ibind mreal].
apply (path_V (set_brk BrkDead A0) (like_A0_dead A) eq_refl Efh Eamc Eaac c3 (fun z => ibind (k z) am_after_area) H3).
+++ rewrite Hk0'. reflexivity.
+++ intros z Hz. destruct (Hk1' z Hz) as (k2 & Ek2 & Hk2). exists (fun z2 => ibind (k2 z2) am_after_area).
split; [rewrite Ek2; reflexivity|]. split; [rewrite Hk2; reflexivity|]. intros z2 Hz2. rewrite Hk2, (proj2 (Z.eqb_neq _ _) Hz2). cbn [ibind am_after_area negb].
rewrite (sV_open (set_brk BrkDead A0)). reflexivity.
** intros z1 Hz1. destruct (Hk11 z1 Hz1) as (k3 & Ek3 & Hk3). exists (fun z => ibind (k3 z) am_after_area).
split; [rewrite Ek3; reflexivity|]. intros z3. rewrite Hk3. cbn [ibind am_after_area negb]. reflexivity.
--
rewrite (am_area_BD A0 Eaac Hbk). destruct (am_resv_tree A0 Eaac) as (k & Ek & Hk0' & Hk1'). rewrite Ek. cbn [ibind mreal].
eapply SR_bind; [exact REACH0|]. intros c1 H1. eapply SR_bind; [exact (reach_V_BD c1 Hbk Efh Eamc Eaac H1)|]. intros c2 H2.
apply (path_V A0 (like_A0_A0 A) Hbk Efh Eamc Eaac c2 (fun z => ibind (k z) am_after_area) H2).
++ rewrite Hk0'. reflexivity.
++ intros z Hz. destruct (Hk1' z Hz) as (k2 & Ek2 & Hk2). exists (fun z2 => ibind (k2 z2) am_after_area).
split; [rewrite Ek2; reflexivity|]. split; [rewrite Hk2; reflexivity|]. intros z2 Hz2. rewrite Hk2, (proj2 (Z.eqb_neq _ _) Hz2). cbn [ibind am_after_area negb].
rewrite (sV_open A0). reflexivity.
--
destruct (am_area_BC A0 rb pages Eaac Hbk) as (k1 & Ek1 & Hk10 & Hk11). rewrite Ek1. cbn [ibind mreal].
destruct (BC_facts rb pages Hbk) as (rw & Hr & Hp2 & Hb & Hr0 & E43v & EP & Pal & Plo & Phi & Bst).
pose proof (u64_range (vm_brk (m_vmmaps md))) as Ub.
eapply SR_bind; [exact REACH0|]. intros c1 H1.
eapply SR_bind; [apply (reach_b1 c1); [rewrite E43v; unfold PGSZ in *; lia | rewrite E43v; lia | exact H1]|]. intros c2 H2.
apply (path_BC rb pages Efh Eamc Eaac Hbk c2 (fun z => ibind (k1 z) am_after_area)).
++ apply (at_b1_cond c2 C_bc BC_NE eq_refl eq_refl eq_refl); [| exact H2].
intros E HA. rewrite (sv_cx E 43 HA ltac:(lia)), E43v. cbn [sv_denot]. rewrite branch_ne, !u64_of_Z by lia. apply Bool.negb_true_iff. apply Z.eqb_neq. unfold PGSZ in *. lia.
++ intros c3 H3. rewrite Hk10. destruct (am_resv_tree (set_brk BrkDead A0) Eaac) as (k & Ek & Hk0' & Hk1'). rewrite Ek. cbn [ibind mreal].
apply (path_V (set_brk BrkDead A0) (like_A0_dead A) eq_refl Efh Eamc Eaac c3 (fun z => ibind (k z) am_after_area) H3).
** rewrite Hk0'. reflexivity.
** intros z Hz. destruct (Hk1' z Hz) as (k2 & Ek2 & Hk2). exists (fun z2 => ibind (k2 z2) am_after_area).
split; [rewrite Ek2; reflexivity|]. split; [rewrite Hk2; reflexivity|]. intros z2 Hz2. rewrite Hk2, (proj2 (Z.eqb_neq _ _) Hz2). cbn [ibind am_after_area negb].
rewrite (sV_open (set_brk BrkDead A0)). reflexivity.
++ intros z Hz. rewrite (Hk11 z Hz). cbn [ibind am_after_area negb]. reflexivity.
*
destruct (am_area_R A0 Haac) as (k & Ek & Hk). rewrite Ek. cbn [ibind mreal].
eapply SR_bind; [exact REACH|]. intros c1 H1.
apply (path_R Efh Eamc ltac:(lia) c1 (fun z => ibind (k z) am_after_area) H1).
-- rewrite Hk. reflexivity.
-- intros z Hz. rewrite Hk, (proj2 (Z.eqb_neq _ _) Hz). cbn [ibind am_after_area negb]. change (openR_st A0) with (open_st (st_avail_meta_areas A) (sR A)). reflexivity.
Qed.
End AM.
Theorem src0_alloc_meta : alloc_meta_hyp src0_msyms.
Proof.
intros X R U L A regs mem md HI XC AMA BND MID AUXP PRE.
pose proof (mid_md _ _ _ _ _ MID) as (Mh & Mlz & Mmat).
destruct (st_guard _ _ (mid_statics _ _ _ _ _ MID)) as [g Hg].
assert (AUX : exists av ar, st_init_done A = false ->
word_mem src0segs mem (LIBC + 8) av /\
(forall k, (k < 10)%nat -> word_mem src0segs mem (av + 16 * Z.of_nat k) (nth k AUXV_TYPES 0)) /\
word_mem src0segs mem (av + 16 * 8 + 8) ar /\
word_mem src0segs mem (ar + 8) (ly_sec L) /\
4096 <= av /\ av + 160 <= 2 ^ 63 /\ 4096 <= ar /\ ar + 16 <= 2 ^ 63 /\
bv_unsigned (getr regs 2) <= av /\ bv_unsigned (getr regs 2) <= ar).
{ destruct (st_init_done A) eqn:Ei.
- exists 0, 0. intros; discriminate.
- destruct (AUXP eq_refl) as (av & ar & Hx). exists av, ar. intros _. exact Hx. }
destruct AUX as (av & ar & AUXV).
pose proof (alloc_meta_AM X R U L A regs mem md HI XC AMA BND MID PRE g av ar Hg AUXV Mh Mlz) as M.
pose proof (mreal_itok _ _ _ _ _ M (alloc_meta_Qspec X R U A HI)) as M2.
eapply mreal_mono; [| exact M2]. intros r c' [HP HQ]. exact (HP HQ).
Qed.
End u.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
