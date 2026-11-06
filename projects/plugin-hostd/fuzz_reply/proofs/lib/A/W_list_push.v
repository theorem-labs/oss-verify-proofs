(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of fuzz_reply's list_push, in the form of the cgif walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8v.v (allocator call sites) and lib/A/ACbk.v (entry and return). *)
(* list_push(l, s, n) at 0x85090 (fuzz_reply.c:130-151).  When the list is full it grows the vector with
   realloc (8 entries, then doubling); it copies the n source bytes into a fresh malloc'd block of n + 1 bytes
   with __asan_memcpy, NUL-terminates it and appends (block, n) to the vector.  The list struct lies in the
   program global g_s (in G); its shadow checks pass by azs.  The walk runs to the malloc call (0x8515c) on both
   paths and hands over to the second segment, TAIL (W_list_push_tail.v lp_tail_stmt, proved by W_lp_tail.v
   pb_lp_tail).  The growth path (lp_grow_seg) calls realloc(v, 16 * s9) through ARE (arealloc_cf_rule,
   W_journal.v, the GUIDE section 3.1 allocator parameter); its forced-success post (4096 <= res) refutes the
   NULL arm (0x8525c, __asan_handle_no_return; abort).  pb_list_push_g (Section g) is the G-generic form
   (W_contract.v lp_spec_g) with TAIL discharged by pb_lp_tail, which takes AMA (amalloc_cf_rule) and AMEMCPY
   (Reusable/YG0d.v aintrin_realizes OCpy).
   The walk is pb_list_push_x / pb_list_push_g_x (Sections c / g), over any allocator relation ARx with its laws
   (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)), stated as W_contract_x.lp_spec_x / lp_spec_g_x, with
   ARE in its caller-context form (arealloc_cf_rule_c_x at CTX; the realloc call hands the rule the chain [], so its
   trace is the singleton [list_push + 0xac], HCTX_lp_realloc) and TAIL as W_list_push_tail.lp_tail_stmt_x.
   pb_list_push and pb_list_push_g (Sections cAR / gAR) are their corollaries at ARx := ARi0, PST := [].
   The room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record) and C3: the Sections take the room record RP; lp_spec_x's live bytes
   are C3's peak over list_push's trace (lp_peak_grow / lp_peak_nogrow give each call's own premise), its room budget
   3 (grow) or 1 (lp_rk_eq) is spent as realloc's 2 and the tail's 1, and its peak-form counts give each call's count
   premise (lp_cnt_at at S; at the tail after realloc, S's counts plus the new vector, the old one gone). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d YI00 YN0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_frame W_list_push_tail W_lp_tail.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_contract_x W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_list_push : Z := AF_fr_list_push.
Definition A_list_pushP : Z := BASE + A_list_push.
(* ---- the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record) and C3's peak premise: list_push's room budget, live bytes, counts ---- *)
(* lp_spec_x's room budget Z.to_nat (lp_cost MT_rk ..): 3 when the vector grows (realloc, then malloc), else 1 *)
Lemma lp_rk_eq : forall l n, Z.to_nat (lp_cost MT_rk l n) = ((if lp_grow l then 2 else 0) + 1)%nat.
Proof. intros l n. unfold lp_cost. destruct (lp_grow l); reflexivity. Qed.
(* C3's peak premise (lp_spec_x: blocks_bytes S + tr_peak (lp_tr l n) <= LIVE_MAX), when the list has room: the one
   request is the text's block *)
Lemma lp_peak_nogrow : forall bb l n, lp_grow l = false -> 0 <= n ->
  bb + tr_peak (lp_tr l n) <= LIVE_MAX -> bb + (n + 1) <= LIVE_MAX.
Proof.
  intros bb l n Hg Hn. revert Hg. unfold lp_tr, lp_grow, ListTr.list_push_tra.
  destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [E|E]; [intros Hg; discriminate Hg|].
  intros _ H. cbv beta iota in H; cbn [app tr_peak fold_right] in H. lia.
Qed.
(* ... and when the vector grows: realloc's own premise at the entry, and the tail malloc's at the state after it (the
   new vector counted, the old one, if any, gone) *)
Lemma lp_peak_grow : forall bb l n, lp_grow l = true -> 0 <= n ->
  bb + tr_peak (lp_tr l n) <= LIVE_MAX ->
  bb + lp_vbytes l <= LIVE_MAX /\
  bb - (if hl_cap l =? 0 then 0 else AREC * hl_cap l) + lp_vbytes l + (n + 1) <= LIVE_MAX.
Proof.
  intros bb l n Hg Hn. revert Hg. unfold lp_tr, lp_grow, lp_vbytes, ListTr.list_push_tra, grow_cap, AREC.
  destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [E|E]; [|intros Hg; discriminate Hg].
  intros _. destruct (Z.eqb_spec (hl_cap l) 0) as [E0|E0]; intros H; cbv beta iota in H |- *;
    cbn [app tr_peak fold_right] in H; split; lia.
Qed.
(* the count premise of one allocator call (cnt_ok) from a spec's peak form: the peak is not negative *)
Lemma lp_cnt_at : forall RP0 pk l, cnt_ok_pk RP0 pk l -> cnt_ok RP0 l.
Proof.
  intros RP0 pk l H. unfold cnt_ok.
  apply (cnt_ok_pk_mono RP0 pk (fun _ => 0%nat) l l); [intros Pq; cbv beta; lia | exact H].
Qed.
(* ---- THE GENERIC WALK (route (b), step 3): list_push over any allocator relation ARx with its laws ---- *)
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): the room invariant and the live counts, as W_contract_x.v Section w2 *)
Variable RP : roomp.
Hypothesis MLAW : ameter_laws MT.
Variable MMAX : Z.
(* the request bound of the allocator rules; at most 2 ^ 30, so that 2 * cap stays inside slliw's 32 bits *)
Hypothesis HMMAX : 2 ^ 29 < MMAX <= 2 ^ 30.
Variable G : list (Z * Z).
Hypothesis HG : gx_ok SEGS B G.
(* G misses errno and the runtime's two static cells the walk reads (the GOT slot of the shadow base and the
   cell); at PB_fr this is a vm_compute over G *)
Hypothesis HGR : gx_rt B G.
Lemma GX_RT : forall a, inG G a -> ~ (VAL (A_OBJ 0) <= a < VAL (A_OBJ 0) + 8) /\ ~ (VAL (A_OBJ 32) <= a < VAL (A_OBJ 32) + 8).
Proof. intros a Ha. exact (proj2 (HGR a Ha)). Qed.
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the allocator rules' caller-context table (W_journal.v Section hc); the realloc call hands the rule the chain []
   (s0 holds LA + 8, an image address), so its trace is the singleton [its return address 0x8513c = list_push + 0xac] *)
Variable CTX : list (list Z).
Hypothesis ARE : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX (SIGMA WS_realloc).
Hypothesis HCTX_lp_realloc : In [BASE + AF_fr_list_push + 0xac] CTX.
(* the second segment, from the malloc call to the return (A/W_lp_tail.v, pb_lp_tail_x) *)
Hypothesis TAIL : lp_tail_stmt_x B PST ARx MT RP G.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run_x_x B PST ARx LAWS G HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Definition Bx : sv := SOff 35 0.
Definition LP_FRAME : Z := 96.
Definition lp_lregion : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 16 0 16
[YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 4 (SOff 33 0)); YP09.mkChunk 12 (CVal 4 (SOff 34 0))].
Definition lp_regions : smem := [ stack_region LP_FRAME; got_regionP; bcell_regionP 35; lp_lregion ].
Definition lp_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 0x10000 0x5fb000 0);
(33%nat, mkAF 0 (2 ^ 30 - 1) 0); (34%nat, mkAF 0 (2 ^ 30 - 1) 0); (35%nat, mkAF SB SB 0) ] [] [].
Definition ss_lp : sstate := mkSS A_list_push sr_atoms lp_regions None lp_facts.
Definition lp_SH : list shent := [ mkSHE 10 0 16 ].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition lp_extra (v n c : Z) : list word := map (Z_to_bv 64) [v; n; c; SB].
Lemma inG_img : forall a, inG G a -> 0x10000 <= a < 0x5fb000.
Proof. intros a Ha. exact (pa_img_range a (proj1 (HG a Ha))). Qed.
Lemma lp_entry : forall W ly S Hp regs mem md ch LA (l : hlist) lines,
afn_pre_x SEGS B ARx LP_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 LA ->
alist_at B ly S W mem LA l lines ->
(forall a, LA <= a < LA + 16 -> inG G a) -> azs B LA 16 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (lp_extra (hl_v l) (hl_n l) (hl_cap l)))) ss_lp
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_list_pushP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx lp_SH (Eimg (Ereg regs (lp_extra (hl_v l) (hl_n l) (hl_cap l)))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch LA l lines HPRE H10 HL HGL HZ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LP_STK = 96 + 16384) by reflexivity.
pose proof HL as (Mv & Mn & Mc & HwL & Hnc & Hvec & _).
pose proof (inG_img LA (HGL LA ltac:(lia))) as HLA0. pose proof (inG_img (LA + 15) (HGL (LA + 15) ltac:(lia))) as HLA1.
pose proof (GX_RT LA (HGL LA ltac:(lia))) as [HR0 HR1]. pose proof (GX_RT (LA + 15) (HGL (LA + 15) ltac:(lia))) as [HR2 HR3].
assert (Rn0 : 0 <= hl_n l) by (unfold hl_n; lia).
assert (Rv : 0 <= hl_v l < 2 ^ 64) by (destruct Hvec as [[_ ->] | (Hc0 & Hin & _)]; [lia|];
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & H4096 & Hceilv & _);
  unfold req_size, AREC in Hceilv; destruct (16 * hl_cap l =? 0); lia).
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (lp_extra (hl_v l) (hl_n l) (hl_cap l)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (hl_cap l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E273 : ew E (A_OBJ 32) = Z_to_bv 64 (VAL (A_OBJ 32))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
split.
- unfold ss_lp, A_list_pushP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold lp_regions, lp_lregion, stack_region, got_regionP, bcell_regionP, LP_FRAME.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
[cbn [sv_denot]; rewrite E273, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 32)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 32)) 0 8 Bx SB);
[cbn [sv_denot Bx]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat LA E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HwL; lia|].
constructor; [|constructor; [|constructor; [|constructor]]].
-- apply (chunk_ok_val SEGS E _ LA 0 8 _ (hl_v l)); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
   rewrite Z.add_0_r. exact Mv.
-- apply (chunk_ok_val SEGS E _ LA 8 4 _ (hl_n l)); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mn].
-- apply (chunk_ok_val SEGS E _ LA 12 4 _ (hl_cap l)); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mc].
+ apply pairwise_disjoint_of_extents. unfold lp_regions, lp_lregion, stack_region, got_regionP, bcell_regionP, extent_of_region, LP_FRAME.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat LA E10) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia). cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
assert (HR4 : ~ (LA <= VAL (A_OBJ 0) < LA + 16)) by (intros Hc; destruct (GX_RT _ (HGL _ Hc)) as [X _]; apply X; lia).
assert (HR5 : ~ (LA <= VAL (A_OBJ 32) < LA + 16)) by (intros Hc; destruct (GX_RT _ (HGL _ Hc)) as [_ X]; apply X; lia).
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR HLA0 HLA1 HR0 HR1 HR2 HR3 HR4 HR5. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [lp_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 Hnc HLA0 Rn0. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, lp_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E Bx 10 LA 16 LA 0 16).
+ exact (azs_range_addressable_x B ARx LAWS ly S Hp W mem md LA 16 HAR HZ).
+ unfold U, Bx. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ lia.
+ intros x Hx. unfold SHADOW_OFF in *. lia.
Qed.
Lemma lp_blks_in : forall ly S W mem LA l lines, alist_at B ly S W mem LA l lines ->
forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
intros ly S W mem LA l lines HL b Hb. destruct HL as (_ & _ & _ & _ & _ & H6 & _ & _ & H9).
unfold alist_blks in Hb. apply in_app_iff in Hb as [Hb|Hb].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<-|[]].
  destruct H6 as [(Hc & _) | (_ & Hin & _)]; [apply Z.eqb_neq in Ec; lia | exact Hin].
- apply in_map_iff in Hb as (r & <- & Hr). rewrite Forall_forall in H9. exact (proj1 (H9 r Hr)).
Qed.
Lemma lp_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH. unfold text_rec.
rewrite length_app, !Mem.length_le8. cbn [length]. lia.
Qed.
(* the bytes a list's predicate reads outside its struct lie in its blocks *)
Lemma lp_fp_blk : forall ly S W mem LA l lines, alist_at B ly S W mem LA l lines ->
forall r a, In r (alist_fp LA l) -> fst r <= a < snd r -> ~ (LA <= a < LA + 16) ->
exists b, In b (ablocks B ly S) /\ fst b <= a < fst b + req_size (snd b).
Proof.
intros ly S W mem LA l lines HL r a Hr Ha Hn. pose proof HL as (_ & _ & _ & _ & Hnc & H6 & _ & _ & H9).
unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [cbn in Ha; lia|]. apply in_app_iff in Hr as [Hr|Hr].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hr|]. destruct Hr as [<-|[]].
  destruct H6 as [(Hc & _) | (Hc0 & Hin & Hj & _)]; [apply Z.eqb_neq in Ec; lia|].
  exists (hl_v l, AREC * hl_cap l). split; [exact Hin|]. unfold gfp in Ha. cbn [fst snd] in *.
  unfold bzs in Ha. rewrite length_map, length_app, lp_concat_len in Ha. unfold req_size, AREC, hl_n in *.
  destruct (16 * hl_cap l =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia|].
  lia.
- apply in_map_iff in Hr as (t & <- & Ht). rewrite Forall_forall in H9. destruct (H9 t Ht) as (Hin & _).
  exists (fst t, Z.of_nat (length (snd t)) + 1). split; [exact Hin|]. unfold gfp in Ha. cbn [fst snd] in *.
  unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha. unfold req_size.
  destruct (Z.of_nat (length (snd t)) + 1 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | lia].
Qed.
Lemma lp_inG_not_owned : forall ly S Hp (W : world SEGS) m md a, ARx ly S Hp W m md -> inG G a -> ~ aowned B ly S a.
Proof.
intros ly S Hp W m md a HAR Ha Ho.
exact (proj1 (proj2 (HG a Ha)) (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W m md a HAR (proj1 (HG a Ha))) Ho)).
Qed.
(* errno's four bytes are image bytes outside the list struct (gx_rt keeps errno out of G) *)
Lemma lp_errno_out : forall LA a, (forall b, LA <= b < LA + 16 -> inG G b) -> as_errno B <= a < as_errno B + 4 ->
0x10000 <= a < 0x5fb000 /\ ~ (LA <= a < LA + 16).
Proof.
intros LA a HGL Ha. pose proof (pal_env B TL) as (_ & HeImg & _).
split; [exact (pa_img_range a (HeImg a Ha))|].
intros Hc. exact (proj1 (HGR a (HGL a Hc)) Ha).
Qed.
(* ---- the growth arm (N = CAP): realloc, the stores of v and cap, to the malloc call ---- *)
(* the realloc call returns to 0x8513c = list_push + 0xac *)
Definition A_lp_rret : Z := AF_fr_list_push + 0xac.
Lemma lp_sll : forall a s, 0 <= s < 64 -> 0 <= a -> a * 2 ^ s < 2 ^ 64 ->
alu64 ALU_SLL (Z_to_bv 64 a) (Z_to_bv 64 s) = Z_to_bv 64 (a * 2 ^ s).
Proof.
intros a s Hs Ha Hr. rewrite zalu64_sound. f_equal. unfold zalu64. cbn [zalu_raw].
assert (Hl : Z.land (zcanon s) 63 = s).
{ unfold zcanon, M64. rewrite (Z.mod_small s) by lia. change 63 with (Z.ones 6). rewrite Z.land_ones by lia.
  apply Z.mod_small. change (2 ^ 6) with 64. lia. }
rewrite Hl. unfold zcanon, M64. rewrite (Z.mod_small a) by lia. rewrite Z.shiftl_mul_pow2 by lia.
assert (0 <= a * 2 ^ s) by (apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]).
apply Z.mod_small. lia.
Qed.
(* the blocks of an allocator state are pairwise disjoint, so no block occurs twice *)
Lemma lp_nodup : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S Hp W mem md HAR.
assert (HN : Forall (fun b => 0 <= snd b) (ablocks B ly S)).
{ rewrite Forall_forall. intros [p n] Hb. cbn [snd]. exact (BLKN ly S Hp W mem md p n HAR Hb). }
assert (HP : ablocks B ly S = [] \/ pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S))).
{ destruct (ablocks B ly S) as [|[p0 n0] L] eqn:EL; [left; reflexivity|right].
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p0 n0 HAR ltac:(rewrite EL; left; reflexivity)) as (_ & _ & _ & _ & _ & HP).
  rewrite EL in HP. exact HP. }
clear HAR. revert HN HP. generalize (ablocks B ly S) as L0. intros L0.
induction L0 as [|b L IH]; intros HN HP; [constructor|].
destruct HP as [HP|HP]; [discriminate|]. apply Forall_cons_iff in HN as [Hb HN].
cbn [map pairwise] in HP. destruct HP as [HF HP]. constructor.
- intros Hin. assert (Hd : zdisjoint (fst b, req_size (snd b)) (fst b, req_size (snd b))).
  { first [rewrite Forall_forall in HF; apply HF | apply HF]. apply (in_map (fun b => (fst b, req_size (snd b))) L b Hin). }
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. revert Hd Hb. clear. unfold req_size.
  destruct (Z.eqb_spec (snd b) 0); intros; lia.
- apply IH; [exact HN | right; exact HP].
Qed.
Lemma lp_bzs_map : forall jz : list Z, Forall (fun b => 0 <= b < 256) jz -> bzs (map (Z_to_bv 8) jz) = jz.
Proof.
induction jz as [|b jz IH]; intros HF; [reflexivity|]. apply Forall_cons_iff in HF as [Hb HF].
unfold bzs in *. cbn [map]. rewrite (IH HF). f_equal. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. apply Z.mod_small. exact Hb.
Qed.
Lemma lp_present_of : forall H (m : word -> option byte) a, apresent H m a -> YO0d.present (mrestrict H m) a.
Proof. intros H m a [Hh [b Hb]]. exists b. unfold mrestrict. rewrite Hh. exact Hb. Qed.
(* What holds at the realloc call of the growth arm (0x85138, the jal to the realloc trampoline), in values:
   the list is still l (full: N = CAP), s9 = grow_cap N CAP, a0 = v, a1 = 16 * s9, s10 the shadow address of
   LA; the frame holds the caller's ra and s0 .. s10.  The live bytes are lp_spec_x's (C3's peak over list_push's
   trace); the room budget is lp_spec_x's at a growing list (realloc 2, then the tail's malloc 1) and the counts are
   lp_spec_x's peak form, all at the entry's allocator state S (the walk to the call allocates nothing). *)
Definition lp_rcall_pre (W : world SEGS) ly S (Hp : list Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(LA SRC : Z) (l : hlist) (lines : bool) (x : list byte) (q k : Z)
(regsc : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (kr : nat) : Prop :=
let n := Z.of_nat (length x) in
ajournal_gx_x SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly S Hp W memc mdc 0 /\
(exists ch, afn_pre_x SEGS B ARx LP_STK ly S Hp W regs mem md ch) /\
(forall a, LA <= a < LA + 16 -> inG G a) /\ azs B LA 16 /\
alist_at B ly S W memc LA l lines /\ hl_n l = hl_cap l /\ lp_vbytes l < MMAX /\
blocks_bytes S + tr_peak (lp_tr l n) <= LIVE_MAX /\ n < 2 ^ 16 /\
In (q, k) (ablocks B ly S) /\ q <> hl_v l /\ q <= SRC /\ SRC + n <= q + req_size k /\
garr8 SEGS (mrestrict (w_H W) memc) SRC (bzs x) /\
(lines = true -> ~ In (Z_to_bv 8 0) x /\ n <= APARTIAL) /\ (lines = false -> (1 <= length x)%nat) /\
mo_ok MT S (lp_cost MT l n) /\
rp_RM RP S (3 + kr)%nat /\ cnt_ok_pk RP (lp_peak l n) (ablocks B ly S) /\
getr regsc 1 = Z_to_bv 64 (BASE + A_lp_rret) /\ getr regsc 2 = Z_to_bv 64 (spZ regs - 96) /\
getr regsc 3 = getr regs 3 /\ getr regsc 4 = getr regs 4 /\ getr regsc 27 = getr regs 27 /\
getr regsc 8 = w64 (LA + 8) /\ getr regsc 9 = w64 n /\ getr regsc 18 = w64 LA /\ getr regsc 19 = w64 SRC /\
getr regsc 20 = w64 (LA + 12) /\ getr regsc 21 = w64 SB /\
getr regsc 22 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 8)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 23 = alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3) /\
getr regsc 24 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 12)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 25 = w64 (grow_cap (hl_n l) (hl_cap l)) /\
getr regsc 26 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 10 = w64 (hl_v l) /\ getr regsc 11 = w64 (lp_vbytes l) /\
Forall (fun p => val_mem SEGS (mrestrict (w_H W) memc) (spZ regs - 96 + fst p) 8
  (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) lp_saved /\
apres_kept B W mem W memc /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W) memc (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
(* the state seated at the realloc's return: registers are atoms except s4 = LA + 12 and the shadow addresses
   s8 / s10 of LA + 12 / LA (atom 18 = LA, 21 = SB, 10 = the new vector, 9 = n); the list struct with its n field
   (atom 32); no frame (the segment does not touch it) *)
Definition lpr_lregion : YP09.region := YP09.mkRegion (Some 18%nat) 0 16 0 16 [YP09.mkChunk 8 (CVal 4 (SOff 32 0))].
Definition lpr_regs : list sv :=
sr_set (sr_set (sr_set sr_atoms 20%bv (SOff 18 12))
24%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 12) (SLit 3)) (SOff 21 0)))
26%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 21 0)).
Definition lpr_facts : facts :=
mkFacts [ (9%nat, mkAF 0 (2 ^ 16) 0); (10%nat, mkAF 4096 0x7fffff800000 4); (18%nat, mkAF 0x10000 0x5fb000 0);
(21%nat, mkAF SB SB 0) ] [] [].
Definition ss_lpr : sstate := mkSS A_lp_rret lpr_regs [lpr_lregion] None lpr_facts.
Definition lpr_SH : list shent := [ mkSHE 18 0 16 ].
Lemma lp_grow_seg : forall W ly S Hp regs mem md LA SRC l lines x q k regsc memc mdc kr,
lp_rcall_pre W ly S Hp regs mem md LA SRC l lines x q k regsc memc mdc kr ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA WS_realloc)) memc (seg_rom SEGS)) mdc)
(lp_post_x B PST ARx MT RP G regs ly S Hp W mem md LA l lines x kr).
Proof.
intros W ly S Hp regs mem md LA SRC l lines x q k regsc memc mdc kr HPRE.
destruct HPRE as (HJ & (ch & HAF) & HGL & HZ & HLc & Heq & Hvb & Hlive & Hx16 & Hq & Hqv & HqS & HqE & HSRC &
Hlin1 & Hlin2 & HMOK & HRM & HCNT & R1 & R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 &
R10 & R11 & HSAVED & HAPK & HERRC).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (ajournal_gx_AR_x SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly S Hp W memc mdc 0 HJ) as HARc.
pose proof HAF as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LP_STK = 96 + 16384) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
pose proof HLc as (Mv & Mn & Mc & HwL & Hnc & Hvec & HND & HVR & HRECS).
pose proof (proj1 (Forall_forall _ _) HRECS) as HRECS'.
assert (Rn0 : 0 <= hl_n l) by (unfold hl_n; lia).
assert (Hgr : lp_grow l = true) by (unfold lp_grow; rewrite Heq; apply Z.eqb_refl).
assert (Hgc : grow_cap (hl_n l) (hl_cap l) = if hl_cap l =? 0 then 8 else 2 * hl_cap l)
by (unfold grow_cap; rewrite Heq, Z.eqb_refl; reflexivity).
assert (Hvb16 : lp_vbytes l = 16 * grow_cap (hl_n l) (hl_cap l)) by reflexivity.
assert (Hgb : hl_cap l < grow_cap (hl_n l) (hl_cap l) /\ 16 * grow_cap (hl_n l) (hl_cap l) < 2 ^ 30)
by (rewrite Hgc in *; destruct (Z.eqb_spec (hl_cap l) 0); lia).
(* C3's peak: realloc's live bytes at S, and the tail malloc's after it *)
destruct (lp_peak_grow (blocks_bytes S) l (Z.of_nat (length x)) Hgr ltac:(lia) Hlive) as [Hlv1 Hlv2].
pose proof (inG_img LA (HGL LA ltac:(lia))) as HLA0. pose proof (inG_img (LA + 15) (HGL (LA + 15) ltac:(lia))) as HLA1.
assert (Usp : spZ regsc = spZ regs - 96) by (unfold spZ; rewrite R2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (Hv64 : 0 <= hl_v l < 2 ^ 64) by (destruct Hvec as [[_ ->] | (Hc0 & Hin & _)]; [lia|];
  destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hin) as (_ & H4096 & Hceilv & _);
  unfold req_size, AREC in Hceilv; destruct (16 * hl_cap l =? 0) eqn:Ez; [apply Z.eqb_eq in Ez|]; lia).
destruct HJ as (HSTK0 & HXO0 & (memS & HJi & HAG) & HOUT0). rewrite !Z.add_0_r in HJi.
(* realloc(v, 16 * s9) *)
eapply SRr_bind.
{ eapply (ARE W regsc memc LP_STK (spZ regs) (lp_FP l) ly S Hp W memS md [] ly S Hp mdc 0 (hl_v l) (AREC * hl_cap l)
    (lp_vbytes l) (-96) _ [] (1 + kr)%nat HJi).
  - destruct Hvec as [[_ ->] | (_ & Hin & _)]; [left; reflexivity | right; exact Hin].
  - exact R10.
  - exact R11.
  - lia.
  - lia.
  - exact (lp_cnt_at RP _ _ HCNT).
  - rewrite Usp. lia.
  - reflexivity.
  - lia.
  - lia.
  - eapply aj_stack_room_x with (o := -96); [exact HJi | rewrite Usp; lia | lia].
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [unfold A_lp_rret, AF_fr_list_push; lia | reflexivity].
  - apply (achain_chain_pre ly _ (spZ regs - 96) (LA + 8) [] regsc).
    + apply achain_low. lia.
    + rewrite Usp. lia.
    + unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + unfold raZ. rewrite R1. rewrite unsigned_lit_small by (unfold A_lp_rret, AF_fr_list_push; lia).
      unfold A_lp_rret, AF_fr_list_push. lia.
  - cbn [spine]. replace (raZ regsc) with (BASE + AF_fr_list_push + 0xac); [exact HCTX_lp_realloc|].
    unfold raZ. rewrite R1, unsigned_lit_small by (unfold A_lp_rret, AF_fr_list_push; lia).
    unfold A_lp_rret. lia.
  - exact HRM.
  - intros Hp0 Hin i Hi. unfold lp_FP. destruct (Z.eqb_spec (hl_cap l) 0) as [E0|E0].
    + destruct Hvec as [[_ Hv0] | (Hc & _)]; [exact (False_ind _ (Hp0 Hv0)) | lia].
    + exists (hl_v l, hl_v l + AREC * hl_cap l). split; [left; reflexivity|]. cbn [fst snd].
      unfold req_size, AREC in Hi. destruct (16 * hl_cap l =? 0) eqn:Ez; [apply Z.eqb_eq in Ez|]; unfold AREC; lia.
  - apply (mok_station MT S S (lp_cost MT l (Z.of_nat (length x))) 0 _ MLAW HMOK (mle_start MT S MLAW)).
    + pose proof (mo_free_nonneg MT MLAW). pose proof (mo_malloc_nonneg MT MLAW (lp_vbytes l) ltac:(lia)). lia.
    + unfold lp_cost. rewrite Hgr. pose proof (mo_malloc_nonneg MT MLAW (Z.of_nat (length x) + 1) ltac:(lia)). lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & -> & HJ2i & HP2 & Hres & Hfr2 & H4096 & Hp0 & Hpn &
Hcpy & Hkept2 & Hmle2 & HRM2 & Herr2 & Hpres2).
(* ---- after realloc: res (atom 10) is the new vector; the old one went ---- *)
pose proof (proj1 HJ2i) as HAR2.
assert (HPM : exists L, Permutation (ablocks B ly2 S2) ((res, lp_vbytes l) :: L) /\
  (forall b, In b (ablocks B ly S) -> b <> (hl_v l, AREC * hl_cap l) -> In b L) /\
  (forall rest, Permutation (ablocks B ly S) ((if hl_cap l =? 0 then [] else [(hl_v l, AREC * hl_cap l)]) ++ rest) ->
    Permutation L rest) /\
  bsum L + (if hl_cap l =? 0 then 0 else AREC * hl_cap l) = bsum (ablocks B ly S) /\
  (forall Pq, (acnt Pq L <= acnt Pq (ablocks B ly S))%nat)).
{ destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0].
  - assert (Hv0 : hl_v l = 0) by (destruct Hvec as [[_ Hv0] | (Hc & _)]; [exact Hv0 | lia]).
    exists (ablocks B ly S). split; [exact (Hp0 Hv0)|]. split; [intros b Hb _; exact Hb|].
    split; [intros rest Hpr; exact Hpr|]. split; [cbv beta iota; lia | intros Pq; lia].
  - destruct Hvec as [[Hc _] | (_ & Hin & _)]; [lia|].
    assert (Hv0 : hl_v l <> 0)
    by (destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hin) as (_ & H4096v & _); lia).
    destruct (Hpn Hv0) as (l1 & l2 & El & Hpq).
    exists (l1 ++ l2). split; [exact Hpq|]. split.
    + intros b Hb Hne. rewrite El in Hb. apply in_app_or in Hb as [Hb | [Hb | Hb]];
      [apply in_or_app; left; exact Hb | exfalso; apply Hne; symmetry; exact Hb | apply in_or_app; right; exact Hb].
    + split.
      * intros rest Hpr. rewrite El in Hpr.
        exact (Permutation_app_inv l1 l2 [] rest (hl_v l, AREC * hl_cap l) Hpr).
      * split; [rewrite El, !bsum_app, bsum_cons; cbn [snd]; cbv beta iota; unfold AREC; lia|].
        intros Pq. rewrite El. apply acnt_del_le. }
destruct HPM as (L & HPL & HinL & HpermL & HbsL & HcL).
assert (HND2 : List.NoDup ((res, lp_vbytes l) :: L)) by exact (Permutation_NoDup HPL (lp_nodup ly2 S2 Hp2 W2 mem2 md2 HAR2)).
apply NoDup_cons_iff in HND2 as [HnotL HNDL].
assert (Hvin2 : In (res, lp_vbytes l) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPL)); left; reflexivity).
assert (HL2 : forall b, In b L -> In b (ablocks B ly2 S2)) by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPL)); right; exact Hb).
assert (DL : forall b m, In (b, m) L -> b + req_size m <= res \/ res + req_size (lp_vbytes l) <= b).
{ intros b m Hb. assert (Hne : (b, m) <> (res, lp_vbytes l)) by (intros He; rewrite He in Hb; exact (HnotL Hb)).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m res (lp_vbytes l) HAR2 (HL2 _ Hb) Hvin2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd. }
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hvin2) as (Hr16 & Hr4096 & Hrceil & Hrapp & Hrpres & _).
assert (Hreqv : req_size (lp_vbytes l) = lp_vbytes l) by (unfold req_size; destruct (Z.eqb_spec (lp_vbytes l) 0); lia).
rewrite Hreqv in Hrceil, Hrapp, Hrpres, DL.
destruct Hkept2 as (KA1 & KA2 & KA3 & KA4 & KA5 & KA6).
(* a byte of an old block other than the old vector is the byte at the call *)
assert (KB : forall b m a, In (b, m) (ablocks B ly S) -> (b, m) <> (hl_v l, AREC * hl_cap l) -> b <= a < b + req_size m ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
{ intros b m a Hb Hne Ha. pose proof (DL b m (HinL _ Hb Hne)) as D1.
  assert (D2 : hl_v l <> 0 -> b + req_size m <= hl_v l \/ hl_v l + req_size (AREC * hl_cap l) <= b).
  { intros Hv0. destruct Hvec as [[_ Hv] | (_ & Hin & _)]; [exfalso; exact (Hv0 Hv)|].
    pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W memc mdc b m _ _ HARc Hb Hin Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd. }
  replace a with (b + (a - b)) by lia. apply (KA2 b m (a - b) Hb); [lia|]. cbv beta.
  intros [Hx | (Hv0 & Hx)]; [lia | specialize (D2 Hv0); lia]. }
(* the list struct's bytes are image bytes: kept, and still writable *)
assert (KL : forall a, LA <= a < LA + 16 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
{ intros a Ha. apply KA3; [exact (proj1 (HG a (HGL a Ha))) | exact (proj1 (proj2 (HG a (HGL a Ha)))) | exact (proj1 (HGR a (HGL a Ha)))]. }
assert (WL2 : forall o, 0 <= o < 16 -> writable_at SEGS (mrestrict (w_H W2) mem2) (LA + o)).
{ intros o Ho. assert (Ha : LA <= LA + o < LA + 16) by lia.
  apply (lpt_writable_img W W2 memc mem2 (LA + o)); [exact (proj1 (HG _ (HGL _ Ha))) | | exact (HwL o Ho)].
  intros Hpa. apply Hpres2; [exact (proj1 (HG _ (HGL _ Ha)))
  | exact (lp_inG_not_owned ly S Hp W _ _ (LA + o) HARc (HGL _ Ha))
  | exact (lp_inG_not_owned ly2 S2 Hp2 W2 mem2 md2 (LA + o) HAR2 (HGL _ Ha))
  | exact (proj1 (HGR _ (HGL _ Ha)))
  | | exact Hpa].
  intros [Hb | (Hv0 & Hb)].
  - apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res _ (LA + o) HAR2 Hvin2); [rewrite Hreqv; lia|].
    exact (proj1 (HG _ (HGL _ Ha))).
  - destruct Hvec as [[_ Hv] | (_ & Hin & _)]; [exact (Hv0 Hv)|].
    exact (blk_img_x SEGS B ARx LAWS ly S Hp W memc mdc _ _ (LA + o) HARc Hin Hb (proj1 (HG _ (HGL _ Ha)))). }
assert (MN2 : val_mem SEGS (mrestrict (w_H W2) mem2) (LA + 8) 4 (hl_n l)).
{ apply (val_mem_kept SEGS (w_H W) (w_H W2) memc mem2); [|exact Mn]. intros k0 Hk0. apply KL. cbn in Hk0. lia. }
(* ---- the state at the realloc's return ---- *)
remember (Eimg (Ereg regs2 [Z_to_bv 64 (hl_n l)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EA : forall i, (i < 32)%nat -> ew E i = getr regs2 (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew]. destruct (Nat.ltb_spec i 32); [reflexivity | lia]. }
assert (PS : forall i, (i < 32)%nat -> acallee_saved (Z.of_nat i) -> ew E i = getr regsc (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi Hs. rewrite (EA i Hi). exact (HP2 (Z.of_nat i) Hs). }
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs - 96)) by exact (eq_trans (PS 2%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R2).
assert (E3 : ew E 3 = getr regs 3) by exact (eq_trans (PS 3%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R3).
assert (E4 : ew E 4 = getr regs 4) by exact (eq_trans (PS 4%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R4).
assert (E8 : ew E 8 = w64 (LA + 8)) by exact (eq_trans (PS 8%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R8).
assert (E9 : ew E 9 = w64 (Z.of_nat (length x))) by exact (eq_trans (PS 9%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R9).
assert (E10 : ew E 10 = w64 res) by exact (eq_trans (EA 10%nat ltac:(lia)) Hres).
assert (E18 : ew E 18 = w64 LA) by exact (eq_trans (PS 18%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R18).
assert (E19 : ew E 19 = w64 SRC) by exact (eq_trans (PS 19%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R19).
assert (E21 : ew E 21 = w64 SB) by exact (eq_trans (PS 21%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R21).
assert (E22 : ew E 22 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 8)) (Z_to_bv 64 3)) (Z_to_bv 64 SB))
by exact (eq_trans (PS 22%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R22).
assert (E23 : ew E 23 = alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3))
by exact (eq_trans (PS 23%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R23).
assert (E25 : ew E 25 = w64 (grow_cap (hl_n l) (hl_cap l)))
by exact (eq_trans (PS 25%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R25).
assert (E27 : ew E 27 = getr regs 27) by exact (eq_trans (PS 27%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R27).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_n l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (P20 : getr regs2 20 = w64 (LA + 12)) by exact (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) R20).
assert (P24 : getr regs2 24 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 12)) (Z_to_bv 64 3)) (Z_to_bv 64 SB))
by exact (eq_trans (HP2 24 ltac:(unfold acallee_saved; lia)) R24).
assert (P26 : getr regs2 26 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3)) (Z_to_bv 64 SB))
by exact (eq_trans (HP2 26 ltac:(unfold acallee_saved; lia)) R26).
assert (U18 : bv_unsigned (ew E 18) = LA) by (rewrite E18; apply unsigned_lit_small; lia).
assert (Usp2 : bv_unsigned (ew E 2) = spZ regs - 96) by (rewrite E2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (HS : st_ok_pi SEGS VAL E ss_lpr (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + A_lp_rret)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_lpr. apply pa_entry_st_ok_full.
  - unfold lpr_regs. repeat apply lpt_regs_ok_set; [subst E; apply regs_ok_Eimg_Ereg| ..].
    all: cbn [sv_denot]; rewrite ?E18, ?E21; unfold w64; rewrite ?unsigned_lit_small by (unfold SB; lia); rewrite ?Z.add_0_r;
    first [rewrite P20 | rewrite P24 | rewrite P26]; reflexivity.
  - vm_compute. reflexivity.
  - unfold lpr_lregion. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB 18%nat LA E18) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply WL2; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ LA 8 4 _ (hl_n l)); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact MN2].
  - apply pairwise_disjoint_of_extents. unfold lpr_lregion. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [lpr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E10, E18, E21. unfold w64. rewrite !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite Hr16.
    repeat match goal with |- _ /\ _ => split end; unfold SB; lia. }
assert (SHOK : sh_ok SEGS lpt_Bx lpr_SH E (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, lpr_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E lpt_Bx 18 LA 16 LA 0 16).
  + exact (azs_range_addressable_x B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 LA 16 HAR2 HZ).
  + unfold U, lpt_Bx. cbn [sv_denot]. rewrite E21, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E18, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros y Hy. unfold SHADOW_OFF in *. lia. }
assert (HJ2 : ajournal_gx_x SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 (0 + 3)).
{ apply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 (0 + 3) memS);
  [lia | lia | rewrite !Z.add_0_r; exact HJ2i | exact HAG | apply out_none]. }
clear HE.
(* R: beqz (refuted by 4096 <= res), the shadow checks, l->v = res, l->cap = s9, a0 = n + 1, to the malloc call *)
paj_run_to_tok_x RUNTO HS HJ2 SHOK lpt_Bspan A_lp_mcall.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?ew_ewset_other in Ha by lia.
  rewrite U18 in Ha. apply HGL. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?mm _) _ => rename mm into msf end.
rename HFr into HFrR, HG0 into HGrR.
pmkst HS.
prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
prreg HS (9%bv : bv 5) F9. prreg HS (10%bv : bv 5) F10. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19.
prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
prreg HS (24%bv : bv 5) F24. prreg HS (27%bv : bv 5) F27.
(* ---- the memory at the malloc call ---- *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => set (Ef := Ev) in HS end.
assert (UF : forall m, (m < 64)%nat -> ew Ef m = ew E m) by (intros m Hm; subst Ef; rewrite ?ew_ewset_other by lia; reflexivity).
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RL. cbn [ms_mem restrict] in RL.
assert (UFL : bv_unsigned (ew Ef 18) = LA) by (rewrite UF by lia; exact U18).
assert (VL0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 0) (N.to_nat 8) res).
{ eapply (field_of_region Ef _ 18 LA); [exact RL | exact UFL | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF by lia. rewrite E10. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VL8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 8) (N.to_nat 4) (hl_n l)).
{ eapply (field_of_region Ef _ 18 LA); [exact RL | exact UFL | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF by lia. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VL12 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 12) (N.to_nat 4) (grow_cap (hl_n l) (hl_cap l))).
{ eapply (field_of_region Ef _ 18 LA); [exact RL | exact UFL | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF by lia. rewrite E25. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
rewrite Z.add_0_r in VL0.
assert (HAWR : awr W2 (ms_mem msf) LA 16).
{ intros i Hi. destruct RL as (_ & _ & RLw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw.
  rewrite UFL in RLw. exact (RLw i Hi). }
(* off the list struct the run wrote nothing *)
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha H1. apply (aview_kept_out _ _ (w_H W2) mem2 (ms_mem msf) HFrR a Ha). apply lpt_not_wrange.
  lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
  repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U18; lia. }
(* the vector: the copied records, then the rest of the new block as junk *)
assert (HPJ : forall a, res + 16 * hl_cap l <= a < res + 16 * hl_cap l + Z.of_nat (Z.to_nat (16 * (grow_cap (hl_n l) (hl_cap l) - hl_cap l))) ->
  YO0d.present (mrestrict (w_H W2) (ms_mem msf)) a).
{ intros a Ha. apply lp_present_of. apply (apresent_grows _ _ _ a HGrR). apply (proj1 (Hrpres a ltac:(rewrite Hvb16; lia))). }
destruct (garr8_of_present SEGS (mrestrict (w_H W2) (ms_mem msf)) (res + 16 * hl_cap l)
  (Z.to_nat (16 * (grow_cap (hl_n l) (hl_cap l) - hl_cap l))) HPJ) as (jz & Hjl & Hjg).
assert (HjF : Forall (fun b => 0 <= b < 256) jz).
{ apply Forall_forall. intros b Hb. apply (In_nth _ _ 0) in Hb as (j & Hj & <-). exact (proj2 (Hjg j Hj)). }
assert (GV : garr8 SEGS (arm W2 (ms_mem msf)) res (bzs (concat (map text_rec (hl_recs l)) ++ map (Z_to_bv 8) jz))).
{ unfold bzs, arm. rewrite map_app. apply garr8_app. split.
  - destruct Hvec as [[Hc0 Hv0] | (Hc0 & Hin & Hjk & Hgv)].
    + assert (Hr0 : hl_recs l = []) by (apply length_zero_iff_nil; unfold hl_n in *; lia).
      rewrite Hr0. cbn [map concat]. apply garr8_nil.
    + assert (Hj0 : hl_junk l = []) by (apply length_zero_iff_nil; unfold AREC, hl_n in *; lia).
      rewrite Hj0, app_nil_r in Hgv. unfold arm in Hgv.
      apply (lpt_garr8_moved (w_H W) (w_H W2) memc (ms_mem msf) (hl_v l) res); [|exact Hgv].
      intros j Hj. rewrite length_map, lp_concat_len in Hj.
      assert (Hv0 : hl_v l <> 0) by (destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hin) as (_ & H4096v & _); lia).
      rewrite KR.
      * apply (Hcpy Hv0 j). unfold AREC, hl_n in *. lia.
      * unfold hl_n in *. lia.
      * intros HLa. apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res _ (res + j) HAR2 Hvin2); [rewrite Hreqv; unfold AREC, hl_n in *; lia|].
        exact (proj1 (HG _ (HGL _ HLa))).
  - rewrite length_map, lp_concat_len.
    replace (res + Z.of_nat (16 * length (hl_recs l))) with (res + 16 * hl_cap l) by (unfold hl_n in *; lia).
    change (map bz (map (Z_to_bv 8) jz)) with (bzs (map (Z_to_bv 8) jz)). rewrite (lp_bzs_map jz HjF). exact Hjg. }
(* the texts: their blocks stay, untouched *)
assert (RECS : Forall (fun r => In (fst r, Z.of_nat (length (snd r)) + 1) (ablocks B ly2 S2) /\
  garr8 SEGS (arm W2 (ms_mem msf)) (fst r) (bzs (snd r ++ [Z_to_bv 8 0])) /\
  (lines = true -> ~ In (Z_to_bv 8 0) (snd r) /\ Z.of_nat (length (snd r)) <= APARTIAL) /\
  (lines = false -> (1 <= length (snd r))%nat)) (hl_recs l)).
{ apply Forall_forall. intros r Hr. destruct (HRECS' r Hr) as (Hb & Hg & Hl1 & Hl2).
  assert (Hne : (fst r, Z.of_nat (length (snd r)) + 1) <> (hl_v l, AREC * hl_cap l)).
  { intros He. injection He as He1 _. apply HVR. rewrite <- He1. apply in_map. exact Hr. }
  split; [exact (HL2 _ (HinL _ Hb Hne))|]. split; [|split; assumption].
  assert (Hreqr : req_size (Z.of_nat (length (snd r)) + 1) = Z.of_nat (length (snd r)) + 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (snd r)) + 1) 0); lia).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hb) as (_ & H4096r & Hce & _). rewrite Hreqr in Hce.
  unfold arm in *. apply (lpt_garr8_kept (w_H W) (w_H W2) memc (ms_mem msf)); [|exact Hg].
  intros j Hj. unfold bzs in Hj. rewrite length_map, length_app in Hj. cbn [length] in Hj.
  rewrite KR; [apply (KB _ _ _ Hb Hne); rewrite Hreqr; lia | lia |].
  intros HLa. exact (blk_img_x SEGS B ARx LAWS ly S Hp W memc mdc _ _ (fst r + j) HARc Hb ltac:(rewrite Hreqr; lia) (proj1 (HG _ (HGL _ HLa)))). }
assert (HNR : ~ In res (map fst (hl_recs l))).
{ intros Hin. apply in_map_iff in Hin as (r & Hrr & Hr). destruct (HRECS' r Hr) as (Hb & _).
  assert (Hne : (fst r, Z.of_nat (length (snd r)) + 1) <> (hl_v l, AREC * hl_cap l)).
  { intros He. injection He as He1 _. apply HVR. rewrite <- He1. apply in_map. exact Hr. }
  pose proof (DL _ _ (HinL _ Hb Hne)) as D. rewrite Hrr in D. revert D. clear - Hvb16 Hgb Hnc Rn0. unfold req_size.
  destruct (Z.eqb_spec (Z.of_nat (length (snd r)) + 1) 0); intros; lia. }
assert (HLC : alist_at B ly2 S2 W2 (ms_mem msf) LA (HL res (grow_cap (hl_n l) (hl_cap l)) (hl_recs l) (map (Z_to_bv 8) jz)) lines).
{ unfold alist_at. cbn [hl_v hl_cap hl_recs hl_junk].
  split; [exact VL0|]. split; [exact VL8|]. split; [exact VL12|]. split; [exact HAWR|].
  split; [unfold hl_n in *; cbn [hl_recs]; lia|].
  split; [right; split; [lia|]; split; [exact Hvin2|]; split;
    [rewrite length_map, Hjl, Z2Nat.id by lia; unfold AREC, hl_n in *; cbn [hl_recs]; lia | exact GV]|].
  split; [exact HND|]. split; [exact HNR | exact RECS]. }
(* ---- the malloc call: the second segment (W_lp_tail.v) ---- *)
eapply (TAIL W ly S Hp regs mem md LA SRC l lines x q k W2 ly2 S2 Hp2 (ms_regs msf) (ms_mem msf) _ (0 + 3)
  (HL res (grow_cap (hl_n l) (hl_cap l)) (hl_recs l) (map (Z_to_bv 8) jz)) kr).
- apply HL2, HinL; [exact Hq | intros He; injection He as He1 _; exact (Hqv He1)].
- cbn [hl_v]. intros Hqr.
  assert (Hne : (q, k) <> (hl_v l, AREC * hl_cap l)) by (intros He; injection He as He1 _; exact (Hqv He1)).
  pose proof (BLKN ly S Hp W memc mdc q k HARc Hq) as Hk0.
  pose proof (DL _ _ (HinL _ Hq Hne)) as D. rewrite Hqr in D. revert D. clear - Hvb16 Hgb Hnc Rn0 Hk0. unfold req_size.
  destruct (Z.eqb_spec k 0); intros; lia.
- exact HqS.
- exact HqE.
- unfold lp_tail_pre_x. cbv zeta. cbn [hl_v hl_cap hl_recs hl_junk]. rewrite Hgr. cbn [andb negb app].
  split; [exact HJ2|]. split; [exists ch; exact HAF|]. split; [exact HGL|]. split; [exact HZ|].
  split; [exact HLC|]. split; [reflexivity|]. split; [reflexivity|].
  split; [change (hl_n l < grow_cap (hl_n l) (hl_cap l)); lia|].
  split; [intros Hf; discriminate|].
  split; [intros _ Hin; apply HnotL; apply HinL; [exact Hin | intros He; injection He as _ He2; unfold lp_vbytes, AREC in He2; lia]|].
  split; [intros rest Hpr; eapply Permutation_trans; [exact HPL|]; apply perm_skip; apply HpermL;
    revert Hpr; destruct (hl_cap l =? 0); intros Hpr; exact Hpr|].
  split; [exact Hfr2|]. split; [exact Hmle2|]. split; [exact HMOK|].
  (* the room round: realloc's post leaves the tail's budget; the counts at S2 are S's plus the new vector, within
     lp_spec_x's peak (the old vector, if any, is gone) *)
  split; [exact HRM2|].
  split.
  { unfold cnt_ok. apply (cnt_ok_pk_mono RP (lp_peak l (Z.of_nat (length x))) (fun _ => 0%nat) (ablocks B ly S) (ablocks B ly2 S2));
      [|exact HCNT].
    intros Pq. unfold lp_peak. cbv beta. rewrite (acnt_perm Pq _ _ HPL), acnt_cons. cbn [snd]. rewrite Hgr, andb_true_r.
    specialize (HcL Pq). lia. }
  split; [rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HPL), bsum_cons; cbn [snd];
    rewrite (blocks_bytes_bsum B ly S) in Hlv2; lia|].
  split; [exact Hx16|].
  split.
  { unfold arm in *. apply (lpt_garr8_kept (w_H W) (w_H W2) memc (ms_mem msf) SRC (bzs x)); [|exact HSRC].
    intros j Hj. unfold bzs in Hj. rewrite length_map in Hj.
    assert (Hne : (q, k) <> (hl_v l, AREC * hl_cap l)) by (intros He; injection He as He1 _; exact (Hqv He1)).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hq) as (_ & Hq4096 & Hqce & _).
    rewrite KR; [apply (KB q k (SRC + j) Hq Hne); lia | lia |].
    intros HLa. exact (blk_img_x SEGS B ARx LAWS ly S Hp W memc mdc q k (SRC + j) HARc Hq ltac:(lia) (proj1 (HG _ (HGL _ HLa)))). }
  split; [exact Hlin1|]. split; [exact Hlin2|].
  split; [rewrite F2, E2; reflexivity|].
  split; [rewrite F3, E3; reflexivity|]. split; [rewrite F4, E4; reflexivity|]. split; [rewrite F27, E27; reflexivity|].
  split; [rewrite F8, E8; reflexivity|]. split; [rewrite F9, E9; reflexivity|]. split; [rewrite F18, E18; reflexivity|].
  split; [rewrite F19, E19; reflexivity|].
  split; [rewrite F20, E18; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split; [rewrite F21, E21; reflexivity|]. split; [rewrite F22, E22; reflexivity|]. split; [rewrite F23, E23; reflexivity|].
  split; [rewrite F24, E18, E21; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split; [rewrite F10, E9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split.
  { apply Forall_forall. intros p Hpp. rewrite Forall_forall in HSAVED.
    apply (val_mem_kept SEGS (w_H W) (w_H W2) memc (ms_mem msf)); [|exact (HSAVED p Hpp)].
    assert (Hfp : 0 <= fst p <= 88)
    by (unfold lp_saved in Hpp; cbn [In] in Hpp; repeat destruct Hpp as [<- | Hpp]; try destruct Hpp; cbn [fst]; lia).
    intros k0 Hk0. cbn in Hk0. rewrite KR by lia. apply KA1; lia. }
  split.
  2: { intros i Hi. destruct (lp_errno_out LA (as_errno B + i) HGL ltac:(clear - Hi; lia)) as [HeR HeL].
       rewrite KR by (clear - HeR HeL; lia). rewrite (Herr2 i Hi). exact (HERRC i Hi). }
  intros a Hi Hno Herr Hpa.
  assert (Hnot : forall ly0 S0 Hq0 (W0 : world SEGS) m0 md0, ARx ly0 S0 Hq0 W0 m0 md0 -> ~ aowned B ly0 S0 a)
  by (intros ly0 S0 Hq0 W0 m0 md0 HA Ho; apply Hno; exact (proj1 (alx_owned_image _ _ _ LAWS ly0 S0 Hq0 W0 m0 md0 a HA Hi) Ho)).
  apply (apresent_grows _ _ _ a HGrR).
  apply (Hpres2 a Hi (Hnot _ _ _ _ _ _ HARc) (Hnot _ _ _ _ _ _ HAR2) Herr); [|exact (HAPK a Hi Hno Herr Hpa)].
  intros [Hb | (Hv0 & Hb)].
  + exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res _ a HAR2 Hvin2 Hb Hi).
  + destruct Hvec as [[_ Hv] | (_ & Hin & _)]; [exact (Hv0 Hv)|].
    exact (blk_img_x SEGS B ARx LAWS ly S Hp W memc mdc _ _ a HARc Hin Hb Hi).
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0, 3, 4): the walk at a world relation R, stated as W_contract_xR.lp_spec_xR
   (journal ajournal_gx_xR R, step relation SRrG SEGS R, post lp_post_xR R).  The runs are the G runs
   (W_journal_x.paj_run_x_xG / paj_run_to_x_xG), the branches W_kit.paj_branch_xR.  The realloc call goes through the
   realloc rule at R (arealloc_cf_rule_c_xR at CTX): its call-boundary premise RO at the call memory comes from the call
   state's ARx (RO_ARx; part 3c removed its memnorm premise), its hull admission HA from the meter fact at the call
   (HA_call).  The second segment is TAIL_R (W_list_push_tail.lp_tail_stmt_xR, proved by W_lp_tail.pb_lp_tail_xR).
   lp_grow_seg keeps its strict proof; pb_list_push_x below is pb_list_push_xR at R := wle.  lp_rcall_pre_wle below
   checks that lp_rcall_pre is lp_rcall_pre_xR at wle. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Variable HA : alayout -> astate -> bvmap 5 word -> list (Z * Z * Z) -> Z -> Z -> Prop.
Hypothesis HA_call : forall lyc Sc regsT ch p n, mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HA lyc Sc regsT ch p n.
Hypothesis ARE_R : arealloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO HA CTX R (SIGMA WS_realloc).
Hypothesis TAIL_R : lp_tail_stmt_xR B PST ARx MT RP G R.
Let RUNG := paj_run_x_xG B PST ARx LAWS R G HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG 0 [].
Let BRG := paj_branch_xR (PI := PI) (R := R).
(* :325 lp_rcall_pre *)
Definition lp_rcall_pre_xR (W : world SEGS) ly S (Hp : list Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
(LA SRC : Z) (l : hlist) (lines : bool) (x : list byte) (q k : Z)
(regsc : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (kr : nat) : Prop :=
let n := Z.of_nat (length x) in
ajournal_gx_xR SEGS B PST ARx R G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly S Hp W memc mdc 0 /\
(exists ch, afn_pre_x SEGS B ARx LP_STK ly S Hp W regs mem md ch) /\
(forall a, LA <= a < LA + 16 -> inG G a) /\ azs B LA 16 /\
alist_at B ly S W memc LA l lines /\ hl_n l = hl_cap l /\ lp_vbytes l < MMAX /\
blocks_bytes S + tr_peak (lp_tr l n) <= LIVE_MAX /\ n < 2 ^ 16 /\
In (q, k) (ablocks B ly S) /\ q <> hl_v l /\ q <= SRC /\ SRC + n <= q + req_size k /\
garr8 SEGS (mrestrict (w_H W) memc) SRC (bzs x) /\
(lines = true -> ~ In (Z_to_bv 8 0) x /\ n <= APARTIAL) /\ (lines = false -> (1 <= length x)%nat) /\
mo_ok MT S (lp_cost MT l n) /\
rp_RM RP S (3 + kr)%nat /\ cnt_ok_pk RP (lp_peak l n) (ablocks B ly S) /\
getr regsc 1 = Z_to_bv 64 (BASE + A_lp_rret) /\ getr regsc 2 = Z_to_bv 64 (spZ regs - 96) /\
getr regsc 3 = getr regs 3 /\ getr regsc 4 = getr regs 4 /\ getr regsc 27 = getr regs 27 /\
getr regsc 8 = w64 (LA + 8) /\ getr regsc 9 = w64 n /\ getr regsc 18 = w64 LA /\ getr regsc 19 = w64 SRC /\
getr regsc 20 = w64 (LA + 12) /\ getr regsc 21 = w64 SB /\
getr regsc 22 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 8)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 23 = alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3) /\
getr regsc 24 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 12)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 25 = w64 (grow_cap (hl_n l) (hl_cap l)) /\
getr regsc 26 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
getr regsc 10 = w64 (hl_v l) /\ getr regsc 11 = w64 (lp_vbytes l) /\
Forall (fun p => val_mem SEGS (mrestrict (w_H W) memc) (spZ regs - 96 + fst p) 8
  (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) lp_saved /\
apres_kept B W mem W memc /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W) memc (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i)).
(* :366 lp_grow_seg *)
Lemma lp_grow_seg_xR : forall W ly S Hp regs mem md LA SRC l lines x q k regsc memc mdc kr,
lp_rcall_pre_xR W ly S Hp regs mem md LA SRC l lines x q k regsc memc mdc kr ->
SRrG SEGS R W (mkCfg (mkst regsc (Z_to_bv 64 (SIGMA WS_realloc)) memc (seg_rom SEGS)) mdc)
(lp_post_xR B PST ARx R MT RP G regs ly S Hp W mem md LA l lines x kr).
Proof.
intros W ly S Hp regs mem md LA SRC l lines x q k regsc memc mdc kr HPRE.
destruct HPRE as (HJ & (ch & HAF) & HGL & HZ & HLc & Heq & Hvb & Hlive & Hx16 & Hq & Hqv & HqS & HqE & HSRC &
Hlin1 & Hlin2 & HMOK & HRM & HCNT & R1 & R2 & R3 & R4 & R27 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 &
R10 & R11 & HSAVED & HAPK & HERRC).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly S Hp W memc mdc 0 HJ) as HARc.
pose proof HAF as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LP_STK = 96 + 16384) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
pose proof HLc as (Mv & Mn & Mc & HwL & Hnc & Hvec & HND & HVR & HRECS).
pose proof (proj1 (Forall_forall _ _) HRECS) as HRECS'.
assert (Rn0 : 0 <= hl_n l) by (unfold hl_n; lia).
assert (Hgr : lp_grow l = true) by (unfold lp_grow; rewrite Heq; apply Z.eqb_refl).
assert (Hgc : grow_cap (hl_n l) (hl_cap l) = if hl_cap l =? 0 then 8 else 2 * hl_cap l)
by (unfold grow_cap; rewrite Heq, Z.eqb_refl; reflexivity).
assert (Hvb16 : lp_vbytes l = 16 * grow_cap (hl_n l) (hl_cap l)) by reflexivity.
assert (Hgb : hl_cap l < grow_cap (hl_n l) (hl_cap l) /\ 16 * grow_cap (hl_n l) (hl_cap l) < 2 ^ 30)
by (rewrite Hgc in *; destruct (Z.eqb_spec (hl_cap l) 0); lia).
(* C3's peak: realloc's live bytes at S, and the tail malloc's after it *)
destruct (lp_peak_grow (blocks_bytes S) l (Z.of_nat (length x)) Hgr ltac:(lia) Hlive) as [Hlv1 Hlv2].
pose proof (inG_img LA (HGL LA ltac:(lia))) as HLA0. pose proof (inG_img (LA + 15) (HGL (LA + 15) ltac:(lia))) as HLA1.
assert (Usp : spZ regsc = spZ regs - 96) by (unfold spZ; rewrite R2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (Hv64 : 0 <= hl_v l < 2 ^ 64) by (destruct Hvec as [[_ ->] | (Hc0 & Hin & _)]; [lia|];
  destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hin) as (_ & H4096 & Hceilv & _);
  unfold req_size, AREC in Hceilv; destruct (16 * hl_cap l =? 0) eqn:Ez; [apply Z.eqb_eq in Ez|]; lia).
destruct HJ as (HSTK0 & HXO0 & (memS & HJi & HAG) & HOUT0). rewrite !Z.add_0_r in HJi.
(* the realloc rule's call-boundary premise at the call memory, from the call state's ARx, and its hull admission
   from the meter fact at the call *)
pose proof (RO_ARx _ _ _ _ _ _ (proj1 HJi)) as HRO.
assert (HMOKc : mo_ok MT S (mo_malloc MT (lp_vbytes l) + mo_free MT)).
{ apply (mok_station MT S S (lp_cost MT l (Z.of_nat (length x))) 0 _ MLAW HMOK (mle_start MT S MLAW)).
  + pose proof (mo_free_nonneg MT MLAW). pose proof (mo_malloc_nonneg MT MLAW (lp_vbytes l) ltac:(lia)). lia.
  + unfold lp_cost. rewrite Hgr. pose proof (mo_malloc_nonneg MT MLAW (Z.of_nat (length x) + 1) ltac:(lia)). lia. }
(* realloc(v, 16 * s9) *)
eapply (SRrG_bind SEGS R R_trans).
{ eapply (ARE_R W regsc memc LP_STK (spZ regs) (lp_FP l) ly S Hp W memS md [] ly S Hp mdc 0 (hl_v l) (AREC * hl_cap l)
    (lp_vbytes l) (-96) _ [] (1 + kr)%nat HJi).
  - destruct Hvec as [[_ ->] | (_ & Hin & _)]; [left; reflexivity | right; exact Hin].
  - exact R10.
  - exact R11.
  - lia.
  - lia.
  - exact (lp_cnt_at RP _ _ HCNT).
  - rewrite Usp. lia.
  - reflexivity.
  - lia.
  - lia.
  - eapply aj_stack_room_xR with (o := -96); [exact HJi | rewrite Usp; lia | lia].
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [unfold A_lp_rret, AF_fr_list_push; lia | reflexivity].
  - apply (achain_chain_pre ly _ (spZ regs - 96) (LA + 8) [] regsc).
    + apply achain_low. lia.
    + rewrite Usp. lia.
    + unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + unfold raZ. rewrite R1. rewrite unsigned_lit_small by (unfold A_lp_rret, AF_fr_list_push; lia).
      unfold A_lp_rret, AF_fr_list_push. lia.
  - exact HRO.
  - apply HA_call. exact HMOKc.
  - cbn [spine]. replace (raZ regsc) with (BASE + AF_fr_list_push + 0xac); [exact HCTX_lp_realloc|].
    unfold raZ. rewrite R1, unsigned_lit_small by (unfold A_lp_rret, AF_fr_list_push; lia).
    unfold A_lp_rret. lia.
  - exact HRM.
  - intros Hp0 Hin i Hi. unfold lp_FP. destruct (Z.eqb_spec (hl_cap l) 0) as [E0|E0].
    + destruct Hvec as [[_ Hv0] | (Hc & _)]; [exact (False_ind _ (Hp0 Hv0)) | lia].
    + exists (hl_v l, hl_v l + AREC * hl_cap l). split; [left; reflexivity|]. cbn [fst snd].
      unfold req_size, AREC in Hi. destruct (16 * hl_cap l =? 0) eqn:Ez; [apply Z.eqb_eq in Ez|]; unfold AREC; lia.
  - exact HMOKc. }
cbv beta. intros W2 c2 HRw2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & res & -> & HJ2i & HP2 & Hres & Hfr2 & H4096 & Hp0 & Hpn &
Hcpy & Hkept2 & Hmle2 & HRM2 & Herr2 & Hpres2).
(* ---- after realloc: res (atom 10) is the new vector; the old one went ---- *)
pose proof (proj1 HJ2i) as HAR2.
assert (HPM : exists L, Permutation (ablocks B ly2 S2) ((res, lp_vbytes l) :: L) /\
  (forall b, In b (ablocks B ly S) -> b <> (hl_v l, AREC * hl_cap l) -> In b L) /\
  (forall rest, Permutation (ablocks B ly S) ((if hl_cap l =? 0 then [] else [(hl_v l, AREC * hl_cap l)]) ++ rest) ->
    Permutation L rest) /\
  bsum L + (if hl_cap l =? 0 then 0 else AREC * hl_cap l) = bsum (ablocks B ly S) /\
  (forall Pq, (acnt Pq L <= acnt Pq (ablocks B ly S))%nat)).
{ destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0].
  - assert (Hv0 : hl_v l = 0) by (destruct Hvec as [[_ Hv0] | (Hc & _)]; [exact Hv0 | lia]).
    exists (ablocks B ly S). split; [exact (Hp0 Hv0)|]. split; [intros b Hb _; exact Hb|].
    split; [intros rest Hpr; exact Hpr|]. split; [cbv beta iota; lia | intros Pq; lia].
  - destruct Hvec as [[Hc _] | (_ & Hin & _)]; [lia|].
    assert (Hv0 : hl_v l <> 0)
    by (destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hin) as (_ & H4096v & _); lia).
    destruct (Hpn Hv0) as (l1 & l2 & El & Hpq).
    exists (l1 ++ l2). split; [exact Hpq|]. split.
    + intros b Hb Hne. rewrite El in Hb. apply in_app_or in Hb as [Hb | [Hb | Hb]];
      [apply in_or_app; left; exact Hb | exfalso; apply Hne; symmetry; exact Hb | apply in_or_app; right; exact Hb].
    + split.
      * intros rest Hpr. rewrite El in Hpr.
        exact (Permutation_app_inv l1 l2 [] rest (hl_v l, AREC * hl_cap l) Hpr).
      * split; [rewrite El, !bsum_app, bsum_cons; cbn [snd]; cbv beta iota; unfold AREC; lia|].
        intros Pq. rewrite El. apply acnt_del_le. }
destruct HPM as (L & HPL & HinL & HpermL & HbsL & HcL).
assert (HND2 : List.NoDup ((res, lp_vbytes l) :: L)) by exact (Permutation_NoDup HPL (lp_nodup ly2 S2 Hp2 W2 mem2 md2 HAR2)).
apply NoDup_cons_iff in HND2 as [HnotL HNDL].
assert (Hvin2 : In (res, lp_vbytes l) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPL)); left; reflexivity).
assert (HL2 : forall b, In b L -> In b (ablocks B ly2 S2)) by (intros b Hb; apply (Permutation_in _ (Permutation_sym HPL)); right; exact Hb).
assert (DL : forall b m, In (b, m) L -> b + req_size m <= res \/ res + req_size (lp_vbytes l) <= b).
{ intros b m Hb. assert (Hne : (b, m) <> (res, lp_vbytes l)) by (intros He; rewrite He in Hb; exact (HnotL Hb)).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b m res (lp_vbytes l) HAR2 (HL2 _ Hb) Hvin2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd. }
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hvin2) as (Hr16 & Hr4096 & Hrceil & Hrapp & Hrpres & _).
assert (Hreqv : req_size (lp_vbytes l) = lp_vbytes l) by (unfold req_size; destruct (Z.eqb_spec (lp_vbytes l) 0); lia).
rewrite Hreqv in Hrceil, Hrapp, Hrpres, DL.
destruct Hkept2 as (KA1 & KA2 & KA3 & KA4 & KA5 & KA6).
(* a byte of an old block other than the old vector is the byte at the call *)
assert (KB : forall b m a, In (b, m) (ablocks B ly S) -> (b, m) <> (hl_v l, AREC * hl_cap l) -> b <= a < b + req_size m ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
{ intros b m a Hb Hne Ha. pose proof (DL b m (HinL _ Hb Hne)) as D1.
  assert (D2 : hl_v l <> 0 -> b + req_size m <= hl_v l \/ hl_v l + req_size (AREC * hl_cap l) <= b).
  { intros Hv0. destruct Hvec as [[_ Hv] | (_ & Hin & _)]; [exfalso; exact (Hv0 Hv)|].
    pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W memc mdc b m _ _ HARc Hb Hin Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd. }
  replace a with (b + (a - b)) by lia. apply (KA2 b m (a - b) Hb); [lia|]. cbv beta.
  intros [Hx | (Hv0 & Hx)]; [lia | specialize (D2 Hv0); lia]. }
(* the list struct's bytes are image bytes: kept, and still writable *)
assert (KL : forall a, LA <= a < LA + 16 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
{ intros a Ha. apply KA3; [exact (proj1 (HG a (HGL a Ha))) | exact (proj1 (proj2 (HG a (HGL a Ha)))) | exact (proj1 (HGR a (HGL a Ha)))]. }
assert (WL2 : forall o, 0 <= o < 16 -> writable_at SEGS (mrestrict (w_H W2) mem2) (LA + o)).
{ intros o Ho. assert (Ha : LA <= LA + o < LA + 16) by lia.
  apply (lpt_writable_img W W2 memc mem2 (LA + o)); [exact (proj1 (HG _ (HGL _ Ha))) | | exact (HwL o Ho)].
  intros Hpa. apply Hpres2; [exact (proj1 (HG _ (HGL _ Ha)))
  | exact (lp_inG_not_owned ly S Hp W _ _ (LA + o) HARc (HGL _ Ha))
  | exact (lp_inG_not_owned ly2 S2 Hp2 W2 mem2 md2 (LA + o) HAR2 (HGL _ Ha))
  | exact (proj1 (HGR _ (HGL _ Ha)))
  | | exact Hpa].
  intros [Hb | (Hv0 & Hb)].
  - apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res _ (LA + o) HAR2 Hvin2); [rewrite Hreqv; lia|].
    exact (proj1 (HG _ (HGL _ Ha))).
  - destruct Hvec as [[_ Hv] | (_ & Hin & _)]; [exact (Hv0 Hv)|].
    exact (blk_img_x SEGS B ARx LAWS ly S Hp W memc mdc _ _ (LA + o) HARc Hin Hb (proj1 (HG _ (HGL _ Ha)))). }
assert (MN2 : val_mem SEGS (mrestrict (w_H W2) mem2) (LA + 8) 4 (hl_n l)).
{ apply (val_mem_kept SEGS (w_H W) (w_H W2) memc mem2); [|exact Mn]. intros k0 Hk0. apply KL. cbn in Hk0. lia. }
(* ---- the state at the realloc's return ---- *)
remember (Eimg (Ereg regs2 [Z_to_bv 64 (hl_n l)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EA : forall i, (i < 32)%nat -> ew E i = getr regs2 (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew]. destruct (Nat.ltb_spec i 32); [reflexivity | lia]. }
assert (PS : forall i, (i < 32)%nat -> acallee_saved (Z.of_nat i) -> ew E i = getr regsc (Z_to_bv 5 (Z.of_nat i))).
{ intros i Hi Hs. rewrite (EA i Hi). exact (HP2 (Z.of_nat i) Hs). }
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs - 96)) by exact (eq_trans (PS 2%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R2).
assert (E3 : ew E 3 = getr regs 3) by exact (eq_trans (PS 3%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R3).
assert (E4 : ew E 4 = getr regs 4) by exact (eq_trans (PS 4%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R4).
assert (E8 : ew E 8 = w64 (LA + 8)) by exact (eq_trans (PS 8%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R8).
assert (E9 : ew E 9 = w64 (Z.of_nat (length x))) by exact (eq_trans (PS 9%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R9).
assert (E10 : ew E 10 = w64 res) by exact (eq_trans (EA 10%nat ltac:(lia)) Hres).
assert (E18 : ew E 18 = w64 LA) by exact (eq_trans (PS 18%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R18).
assert (E19 : ew E 19 = w64 SRC) by exact (eq_trans (PS 19%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R19).
assert (E21 : ew E 21 = w64 SB) by exact (eq_trans (PS 21%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R21).
assert (E22 : ew E 22 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 8)) (Z_to_bv 64 3)) (Z_to_bv 64 SB))
by exact (eq_trans (PS 22%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R22).
assert (E23 : ew E 23 = alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3))
by exact (eq_trans (PS 23%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R23).
assert (E25 : ew E 25 = w64 (grow_cap (hl_n l) (hl_cap l)))
by exact (eq_trans (PS 25%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R25).
assert (E27 : ew E 27 = getr regs 27) by exact (eq_trans (PS 27%nat ltac:(lia) ltac:(unfold acallee_saved; lia)) R27).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_n l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (P20 : getr regs2 20 = w64 (LA + 12)) by exact (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) R20).
assert (P24 : getr regs2 24 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (LA + 12)) (Z_to_bv 64 3)) (Z_to_bv 64 SB))
by exact (eq_trans (HP2 24 ltac:(unfold acallee_saved; lia)) R24).
assert (P26 : getr regs2 26 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 LA) (Z_to_bv 64 3)) (Z_to_bv 64 SB))
by exact (eq_trans (HP2 26 ltac:(unfold acallee_saved; lia)) R26).
assert (U18 : bv_unsigned (ew E 18) = LA) by (rewrite E18; apply unsigned_lit_small; lia).
assert (Usp2 : bv_unsigned (ew E 2) = spZ regs - 96) by (rewrite E2; apply unsigned_lit_small; unfold spZ in *; lia).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (HS : st_ok_pi SEGS VAL E ss_lpr (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + A_lp_rret)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_lpr. apply pa_entry_st_ok_full.
  - unfold lpr_regs. repeat apply lpt_regs_ok_set; [subst E; apply regs_ok_Eimg_Ereg| ..].
    all: cbn [sv_denot]; rewrite ?E18, ?E21; unfold w64; rewrite ?unsigned_lit_small by (unfold SB; lia); rewrite ?Z.add_0_r;
    first [rewrite P20 | rewrite P24 | rewrite P26]; reflexivity.
  - vm_compute. reflexivity.
  - unfold lpr_lregion. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (VB 18%nat LA E18) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply WL2; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ LA 8 4 _ (hl_n l)); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact MN2].
  - apply pairwise_disjoint_of_extents. unfold lpr_lregion. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [lpr_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E9, E10, E18, E21. unfold w64. rewrite !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite Hr16.
    repeat match goal with |- _ /\ _ => split end; unfold SB; lia. }
assert (SHOK : sh_ok SEGS lpt_Bx lpr_SH E (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, lpr_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 E lpt_Bx 18 LA 16 LA 0 16).
  + exact (azs_range_addressable_x B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 LA 16 HAR2 HZ).
  + unfold U, lpt_Bx. cbn [sv_denot]. rewrite E21, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E18, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros y Hy. unfold SHADOW_OFF in *. lia. }
assert (HJ2 : ajournal_gx_xR SEGS B PST ARx R G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 (0 + 3)).
{ apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 (0 + 3) memS);
  [lia | lia | rewrite !Z.add_0_r; exact HJ2i | exact HAG | apply out_none]. }
clear HE.
(* R: beqz (refuted by 4096 <= res), the shadow checks, l->v = res, l->cap = s9, a0 = n + 1, to the malloc call *)
paj_run_to_tok_xR RUNTOG HS HJ2 SHOK lpt_Bspan A_lp_mcall.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?ew_ewset_other in Ha by lia.
  rewrite U18 in Ha. apply HGL. lia. }
lazymatch goal with |- SRrG _ _ _ (mkCfg ?mm _) _ => rename mm into msf end.
rename HFr into HFrR, HG0 into HGrR.
pmkst HS.
prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
prreg HS (9%bv : bv 5) F9. prreg HS (10%bv : bv 5) F10. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19.
prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
prreg HS (24%bv : bv 5) F24. prreg HS (27%bv : bv 5) F27.
(* ---- the memory at the malloc call ---- *)
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => set (Ef := Ev) in HS end.
assert (UF : forall m, (m < 64)%nat -> ew Ef m = ew E m) by (intros m Hm; subst Ef; rewrite ?ew_ewset_other by lia; reflexivity).
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RL. cbn [ms_mem restrict] in RL.
assert (UFL : bv_unsigned (ew Ef 18) = LA) by (rewrite UF by lia; exact U18).
assert (VL0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 0) (N.to_nat 8) res).
{ eapply (field_of_region Ef _ 18 LA); [exact RL | exact UFL | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF by lia. rewrite E10. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VL8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 8) (N.to_nat 4) (hl_n l)).
{ eapply (field_of_region Ef _ 18 LA); [exact RL | exact UFL | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF by lia. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (VL12 : val_mem SEGS (mrestrict (w_H W2) (ms_mem msf)) (LA + 12) (N.to_nat 4) (grow_cap (hl_n l) (hl_cap l))).
{ eapply (field_of_region Ef _ 18 LA); [exact RL | exact UFL | cbn [In]; repeat first [left; reflexivity | right] | | zside | zside].
  cbn [sv_denot]. rewrite UF by lia. rewrite E25. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
rewrite Z.add_0_r in VL0.
assert (HAWR : awr W2 (ms_mem msf) LA 16).
{ intros i Hi. destruct RL as (_ & _ & RLw & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RLw.
  rewrite UFL in RLw. exact (RLw i Hi). }
(* off the list struct the run wrote nothing *)
assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) (ms_mem msf) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha H1. apply (aview_kept_out _ _ (w_H W2) mem2 (ms_mem msf) HFrR a Ha). apply lpt_not_wrange.
  lazymatch goal with |- Forall _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' end.
  repeat constructor; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?U18; lia. }
(* the vector: the copied records, then the rest of the new block as junk *)
assert (HPJ : forall a, res + 16 * hl_cap l <= a < res + 16 * hl_cap l + Z.of_nat (Z.to_nat (16 * (grow_cap (hl_n l) (hl_cap l) - hl_cap l))) ->
  YO0d.present (mrestrict (w_H W2) (ms_mem msf)) a).
{ intros a Ha. apply lp_present_of. apply (apresent_grows _ _ _ a HGrR). apply (proj1 (Hrpres a ltac:(rewrite Hvb16; lia))). }
destruct (garr8_of_present SEGS (mrestrict (w_H W2) (ms_mem msf)) (res + 16 * hl_cap l)
  (Z.to_nat (16 * (grow_cap (hl_n l) (hl_cap l) - hl_cap l))) HPJ) as (jz & Hjl & Hjg).
assert (HjF : Forall (fun b => 0 <= b < 256) jz).
{ apply Forall_forall. intros b Hb. apply (In_nth _ _ 0) in Hb as (j & Hj & <-). exact (proj2 (Hjg j Hj)). }
assert (GV : garr8 SEGS (arm W2 (ms_mem msf)) res (bzs (concat (map text_rec (hl_recs l)) ++ map (Z_to_bv 8) jz))).
{ unfold bzs, arm. rewrite map_app. apply garr8_app. split.
  - destruct Hvec as [[Hc0 Hv0] | (Hc0 & Hin & Hjk & Hgv)].
    + assert (Hr0 : hl_recs l = []) by (apply length_zero_iff_nil; unfold hl_n in *; lia).
      rewrite Hr0. cbn [map concat]. apply garr8_nil.
    + assert (Hj0 : hl_junk l = []) by (apply length_zero_iff_nil; unfold AREC, hl_n in *; lia).
      rewrite Hj0, app_nil_r in Hgv. unfold arm in Hgv.
      apply (lpt_garr8_moved (w_H W) (w_H W2) memc (ms_mem msf) (hl_v l) res); [|exact Hgv].
      intros j Hj. rewrite length_map, lp_concat_len in Hj.
      assert (Hv0 : hl_v l <> 0) by (destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hin) as (_ & H4096v & _); lia).
      rewrite KR.
      * apply (Hcpy Hv0 j). unfold AREC, hl_n in *. lia.
      * unfold hl_n in *. lia.
      * intros HLa. apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res _ (res + j) HAR2 Hvin2); [rewrite Hreqv; unfold AREC, hl_n in *; lia|].
        exact (proj1 (HG _ (HGL _ HLa))).
  - rewrite length_map, lp_concat_len.
    replace (res + Z.of_nat (16 * length (hl_recs l))) with (res + 16 * hl_cap l) by (unfold hl_n in *; lia).
    change (map bz (map (Z_to_bv 8) jz)) with (bzs (map (Z_to_bv 8) jz)). rewrite (lp_bzs_map jz HjF). exact Hjg. }
(* the texts: their blocks stay, untouched *)
assert (RECS : Forall (fun r => In (fst r, Z.of_nat (length (snd r)) + 1) (ablocks B ly2 S2) /\
  garr8 SEGS (arm W2 (ms_mem msf)) (fst r) (bzs (snd r ++ [Z_to_bv 8 0])) /\
  (lines = true -> ~ In (Z_to_bv 8 0) (snd r) /\ Z.of_nat (length (snd r)) <= APARTIAL) /\
  (lines = false -> (1 <= length (snd r))%nat)) (hl_recs l)).
{ apply Forall_forall. intros r Hr. destruct (HRECS' r Hr) as (Hb & Hg & Hl1 & Hl2).
  assert (Hne : (fst r, Z.of_nat (length (snd r)) + 1) <> (hl_v l, AREC * hl_cap l)).
  { intros He. injection He as He1 _. apply HVR. rewrite <- He1. apply in_map. exact Hr. }
  split; [exact (HL2 _ (HinL _ Hb Hne))|]. split; [|split; assumption].
  assert (Hreqr : req_size (Z.of_nat (length (snd r)) + 1) = Z.of_nat (length (snd r)) + 1)
  by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (snd r)) + 1) 0); lia).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hb) as (_ & H4096r & Hce & _). rewrite Hreqr in Hce.
  unfold arm in *. apply (lpt_garr8_kept (w_H W) (w_H W2) memc (ms_mem msf)); [|exact Hg].
  intros j Hj. unfold bzs in Hj. rewrite length_map, length_app in Hj. cbn [length] in Hj.
  rewrite KR; [apply (KB _ _ _ Hb Hne); rewrite Hreqr; lia | lia |].
  intros HLa. exact (blk_img_x SEGS B ARx LAWS ly S Hp W memc mdc _ _ (fst r + j) HARc Hb ltac:(rewrite Hreqr; lia) (proj1 (HG _ (HGL _ HLa)))). }
assert (HNR : ~ In res (map fst (hl_recs l))).
{ intros Hin. apply in_map_iff in Hin as (r & Hrr & Hr). destruct (HRECS' r Hr) as (Hb & _).
  assert (Hne : (fst r, Z.of_nat (length (snd r)) + 1) <> (hl_v l, AREC * hl_cap l)).
  { intros He. injection He as He1 _. apply HVR. rewrite <- He1. apply in_map. exact Hr. }
  pose proof (DL _ _ (HinL _ Hb Hne)) as D. rewrite Hrr in D. revert D. clear - Hvb16 Hgb Hnc Rn0. unfold req_size.
  destruct (Z.eqb_spec (Z.of_nat (length (snd r)) + 1) 0); intros; lia. }
assert (HLC : alist_at B ly2 S2 W2 (ms_mem msf) LA (HL res (grow_cap (hl_n l) (hl_cap l)) (hl_recs l) (map (Z_to_bv 8) jz)) lines).
{ unfold alist_at. cbn [hl_v hl_cap hl_recs hl_junk].
  split; [exact VL0|]. split; [exact VL8|]. split; [exact VL12|]. split; [exact HAWR|].
  split; [unfold hl_n in *; cbn [hl_recs]; lia|].
  split; [right; split; [lia|]; split; [exact Hvin2|]; split;
    [rewrite length_map, Hjl, Z2Nat.id by lia; unfold AREC, hl_n in *; cbn [hl_recs]; lia | exact GV]|].
  split; [exact HND|]. split; [exact HNR | exact RECS]. }
(* ---- the malloc call: the second segment (W_lp_tail.v) ---- *)
eapply (TAIL_R W ly S Hp regs mem md LA SRC l lines x q k W2 ly2 S2 Hp2 (ms_regs msf) (ms_mem msf) _ (0 + 3)
  (HL res (grow_cap (hl_n l) (hl_cap l)) (hl_recs l) (map (Z_to_bv 8) jz)) kr).
- apply HL2, HinL; [exact Hq | intros He; injection He as He1 _; exact (Hqv He1)].
- cbn [hl_v]. intros Hqr.
  assert (Hne : (q, k) <> (hl_v l, AREC * hl_cap l)) by (intros He; injection He as He1 _; exact (Hqv He1)).
  pose proof (BLKN ly S Hp W memc mdc q k HARc Hq) as Hk0.
  pose proof (DL _ _ (HinL _ Hq Hne)) as D. rewrite Hqr in D. revert D. clear - Hvb16 Hgb Hnc Rn0 Hk0. unfold req_size.
  destruct (Z.eqb_spec k 0); intros; lia.
- exact HqS.
- exact HqE.
- unfold lp_tail_pre_xR. cbv zeta. cbn [hl_v hl_cap hl_recs hl_junk]. rewrite Hgr. cbn [andb negb app].
  split; [exact HJ2|]. split; [exists ch; exact HAF|]. split; [exact HGL|]. split; [exact HZ|].
  split; [exact HLC|]. split; [reflexivity|]. split; [reflexivity|].
  split; [change (hl_n l < grow_cap (hl_n l) (hl_cap l)); lia|].
  split; [intros Hf; discriminate|].
  split; [intros _ Hin; apply HnotL; apply HinL; [exact Hin | intros He; injection He as _ He2; unfold lp_vbytes, AREC in He2; lia]|].
  split; [intros rest Hpr; eapply Permutation_trans; [exact HPL|]; apply perm_skip; apply HpermL;
    revert Hpr; destruct (hl_cap l =? 0); intros Hpr; exact Hpr|].
  split; [exact Hfr2|]. split; [exact Hmle2|]. split; [exact HMOK|].
  (* the room round: realloc's post leaves the tail's budget; the counts at S2 are S's plus the new vector, within
     lp_spec_x's peak (the old vector, if any, is gone) *)
  split; [exact HRM2|].
  split.
  { unfold cnt_ok. apply (cnt_ok_pk_mono RP (lp_peak l (Z.of_nat (length x))) (fun _ => 0%nat) (ablocks B ly S) (ablocks B ly2 S2));
      [|exact HCNT].
    intros Pq. unfold lp_peak. cbv beta. rewrite (acnt_perm Pq _ _ HPL), acnt_cons. cbn [snd]. rewrite Hgr, andb_true_r.
    specialize (HcL Pq). lia. }
  split; [rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HPL), bsum_cons; cbn [snd];
    rewrite (blocks_bytes_bsum B ly S) in Hlv2; lia|].
  split; [exact Hx16|].
  split.
  { unfold arm in *. apply (lpt_garr8_kept (w_H W) (w_H W2) memc (ms_mem msf) SRC (bzs x)); [|exact HSRC].
    intros j Hj. unfold bzs in Hj. rewrite length_map in Hj.
    assert (Hne : (q, k) <> (hl_v l, AREC * hl_cap l)) by (intros He; injection He as He1 _; exact (Hqv He1)).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W memc mdc _ _ HARc Hq) as (_ & Hq4096 & Hqce & _).
    rewrite KR; [apply (KB q k (SRC + j) Hq Hne); lia | lia |].
    intros HLa. exact (blk_img_x SEGS B ARx LAWS ly S Hp W memc mdc q k (SRC + j) HARc Hq ltac:(lia) (proj1 (HG _ (HGL _ HLa)))). }
  split; [exact Hlin1|]. split; [exact Hlin2|].
  split; [rewrite F2, E2; reflexivity|].
  split; [rewrite F3, E3; reflexivity|]. split; [rewrite F4, E4; reflexivity|]. split; [rewrite F27, E27; reflexivity|].
  split; [rewrite F8, E8; reflexivity|]. split; [rewrite F9, E9; reflexivity|]. split; [rewrite F18, E18; reflexivity|].
  split; [rewrite F19, E19; reflexivity|].
  split; [rewrite F20, E18; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split; [rewrite F21, E21; reflexivity|]. split; [rewrite F22, E22; reflexivity|]. split; [rewrite F23, E23; reflexivity|].
  split; [rewrite F24, E18, E21; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split; [rewrite F10, E9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
  split.
  { apply Forall_forall. intros p Hpp. rewrite Forall_forall in HSAVED.
    apply (val_mem_kept SEGS (w_H W) (w_H W2) memc (ms_mem msf)); [|exact (HSAVED p Hpp)].
    assert (Hfp : 0 <= fst p <= 88)
    by (unfold lp_saved in Hpp; cbn [In] in Hpp; repeat destruct Hpp as [<- | Hpp]; try destruct Hpp; cbn [fst]; lia).
    intros k0 Hk0. cbn in Hk0. rewrite KR by lia. apply KA1; lia. }
  split.
  2: { intros i Hi. destruct (lp_errno_out LA (as_errno B + i) HGL ltac:(clear - Hi; lia)) as [HeR HeL].
       rewrite KR by (clear - HeR HeL; lia). rewrite (Herr2 i Hi). exact (HERRC i Hi). }
  intros a Hi Hno Herr Hpa.
  assert (Hnot : forall ly0 S0 Hq0 (W0 : world SEGS) m0 md0, ARx ly0 S0 Hq0 W0 m0 md0 -> ~ aowned B ly0 S0 a)
  by (intros ly0 S0 Hq0 W0 m0 md0 HAx Ho; apply Hno; exact (proj1 (alx_owned_image _ _ _ LAWS ly0 S0 Hq0 W0 m0 md0 a HAx Hi) Ho)).
  apply (apresent_grows _ _ _ a HGrR).
  apply (Hpres2 a Hi (Hnot _ _ _ _ _ _ HARc) (Hnot _ _ _ _ _ _ HAR2) Herr); [|exact (HAPK a Hi Hno Herr Hpa)].
  intros [Hb | (Hv0 & Hb)].
  + exact (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 res _ a HAR2 Hvin2 Hb Hi).
  + destruct Hvec as [[_ Hv] | (_ & Hin & _)]; [exact (Hv0 Hv)|].
    exact (blk_img_x SEGS B ARx LAWS ly S Hp W memc mdc _ _ a HARc Hin Hb Hi).
Qed.
(* :723 pb_list_push_x *)
Theorem pb_list_push_xR : lp_spec_xR B PST ARx R MT RP G MMAX A_list_pushP.
Proof.
intros W ly S Hp regs mem md ch LA SRC l lines x q k HPRE H10 H11 H12 HAL8 HL HGL HZ Hcap25 Hx16 Hlive Hq Hqv Hq1 Hq2 Hsrc
Hlines1 Hlines2 HMOK kr HRM HCNT.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (lp_entry W ly S Hp regs mem md ch LA l lines HPRE H10 HL HGL HZ) as [HS SHOK].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : LP_STK = 96 + 16384) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HL as (Mv & Mn & Mc & HwL & Hnc & Hvec & HND & HVR & HRECS).
assert (Rn0 : 0 <= hl_n l) by (unfold hl_n; lia).
assert (Rv : 0 <= hl_v l < 2 ^ 64) by (destruct Hvec as [[_ ->] | (Hc0 & Hin & _)]; [lia|];
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & H4096 & Hceilv & _);
  unfold req_size, AREC in Hceilv; destruct (16 * hl_cap l =? 0) eqn:Ez; [apply Z.eqb_eq in Ez|]; lia).
assert (HJ : ajournal_gx_xR SEGS B PST ARx R G 0 [] LP_STK (spZ regs) (lp_FP l) ly S Hp W mem md [] ly S Hp W mem md 0).
{ apply (ajournal_gx_init_xR SEGS B PST ARx R_refl G 0 [] LP_STK (lp_FP l) ly S Hp W regs mem md ch HPRE); [lia | reflexivity | lia | intros a Ha; lia]. }
remember (Eimg (Ereg regs (lp_extra (hl_v l) (hl_n l) (hl_cap l)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 SRC) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 (Z.of_nat (length x))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E32 : ew E 32 = Z_to_bv 64 (hl_v l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (hl_n l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (hl_cap l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (lp_extra (hl_v l) (hl_n l) (hl_cap l))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 A_list_pushP) with (Z_to_bv 64 A_list_pushP). unfold A_list_pushP, A_list_push.
paj_run_tok_xR RUNG HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons_awr0; [awr_ok_tac; exact Usp|].
  apply awr_ok_x_cons_awr0; [awr_ok_tac|].
  apply awr_ok_x_cons_awr0; [awr_ok_tac|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?ew_ewset_other in Ha by lia.
  rewrite E10, unsigned_lit_small in Ha by (pose proof (inG_img LA (HGL LA ltac:(lia))); lia). apply HGL. lia. }
psrr_branch_tok RUNG BRG HS SHOK Bspan.
-
(* the list has room: N < CAP; straight to the malloc call *)
assert (Hlt : hl_n l < hl_cap l).
{ rewrite branch_ne_U in Hc. rewrite (U_atom _ 33 (hl_n l)), (U_atom _ 34 (hl_cap l)) in Hc;
  [| rewrite !ew_ewset_other by lia; exact E34 | lia | rewrite !ew_ewset_other by lia; exact E33 | lia].
  apply Bool.negb_true_iff, Z.eqb_neq in Hc. lia. }
paj_run_to_tok_xR RUNTOG HS HJ SHOK Bspan (A_lp_mcall).
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons_awr0; [awr_ok_tac; rewrite ?ew_ewset_other by lia; exact Usp|].
  apply awr_ok_x_cons_awr0; [awr_ok_tac|].
  apply awr_ok_x_cons_awr0; [awr_ok_tac|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?ew_ewset_other in Ha by lia.
  rewrite E10, unsigned_lit_small in Ha by (pose proof (inG_img LA (HGL LA ltac:(lia))); lia). apply HGL. lia. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (10%bv : bv 5) Q10.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (27%bv : bv 5) Q27.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
assert (HLAr : 0x10000 <= LA /\ LA + 16 <= 0x5fb000)
by (pose proof (inG_img LA (HGL LA ltac:(lia))); pose proof (inG_img (LA + 15) (HGL (LA + 15) ltac:(lia))); lia).
assert (E27 : ew E 27 = getr regs 27) by (rewrite (proj1 HAE 27%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 27 27%bv eq_refl)).
(* the chunks of the frame and of the list region, read back at the call *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv (restrict _ ?msv) =>
  assert (CK : forall i r c, nth_error (ss_mem ssv) i = Some r -> In c (YP09.r_chunks r) ->
    YP09.chunk_ok SEGS Ev (mrestrict (w_H W) (ms_mem msv)) (base_val Ev (YP09.r_base r)) c)
  by (intros i r c Hi0 Hc0; exact (st_ok_chunk SEGS Ev (abs_ss VAL ssv) (restrict (w_H W) msv) i r c HS Hi0 Hc0)) end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv (restrict _ ?msv) =>
  lazymatch eval vm_compute in (nth_error (ss_mem ssv) 0) with Some ?r0 =>
    assert (CK0 : forall c, In c (YP09.r_chunks r0) ->
      YP09.chunk_ok SEGS Ev (mrestrict (w_H W) (ms_mem msv)) (base_val Ev (Some 2%nat)) c)
    by (intros c Hc0; exact (CK 0%nat r0 c ltac:(vm_compute; reflexivity) Hc0)) end;
  lazymatch eval vm_compute in (nth_error (ss_mem ssv) 3) with Some ?r3 =>
    assert (CK3 : forall c, In c (YP09.r_chunks r3) ->
      YP09.chunk_ok SEGS Ev (mrestrict (w_H W) (ms_mem msv)) (base_val Ev (Some 10%nat)) c)
    by (intros c Hc0; exact (CK 3%nat r3 c ltac:(vm_compute; reflexivity) Hc0)) end end.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv (restrict _ ?msv) =>
  assert (EV2 : base_val Ev (Some 2%nat) = spZ regs)
    by (cbn [base_val]; rewrite ?ew_ewset_other by (clear; discriminate); exact Usp);
  assert (EV10 : base_val Ev (Some 10%nat) = LA)
    by (cbn [base_val]; rewrite ?ew_ewset_other by (clear; discriminate); rewrite E10;
        apply unsigned_lit_small; clear - HLAr; lia);
  assert (EVr : forall r, (r < 32)%nat -> ew Ev r = ew E r)
    by (intros r Hr; rewrite ?ew_ewset_other by (clear - Hr; lia); reflexivity);
  assert (EVx : forall r, (32 <= r < 36)%nat -> ew Ev r = ew E r)
    by (intros r Hr; rewrite ?ew_ewset_other by (clear - Hr; lia); reflexivity);
  (* the frame holds the caller's ra and s0 .. s10 *)
  assert (SAVED : Forall (fun p => val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) (spZ regs - 96 + fst p) 8
    (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) lp_saved);
  [ unfold lp_saved; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    lazymatch goal with |- val_mem _ _ (spZ regs - 96 + ?o) 8 (bv_unsigned (getr regs (Z_to_bv 5 ?r))) =>
      let c := eval vm_compute in (o - 96) in
      let rn := eval vm_compute in (Z.to_nat r) in
      replace (spZ regs - 96 + o) with (base_val Ev (Some 2%nat) + c) by (rewrite EV2; clear; lia);
      apply (val_of_chunk_ok SEGS Ev _ _ c 8 (SOff rn 0));
      [ exact (CK0 (YP09.mkChunk c (CVal 8 (SOff rn 0))) ltac:(clear; cbn; tauto))
      | cbn [sv_denot]; rewrite Z.add_0_r, EVr by (clear; cbv; lia);
        rewrite (proj1 HAE rn ltac:(clear; cbv; lia)), (ew_Ereg_nat regs _ rn (Z_to_bv 5 r) ltac:(vm_compute; reflexivity));
        reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR; change (bv_modulus 64) with (2 ^ 64) in HR;
        change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - HR; lia
      | clear; vm_compute; discriminate ] end |];
  assert (MV' : val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) LA 8 (hl_v l));
  [ replace LA with (base_val Ev (Some 10%nat) + 0) by (rewrite EV10; ring);
    apply (val_of_chunk_ok SEGS Ev _ _ 0 8 (SOff 32 0));
    [ exact (CK3 (YP09.mkChunk 0 (CVal 8 (SOff 32 0))) ltac:(clear; cbn; tauto))
    | cbn [sv_denot]; rewrite Z.add_0_r, EVx by (clear; cbv; lia); rewrite E32, unsigned_lit_small by (clear - Rv; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Rv; lia | clear; vm_compute; discriminate ] |];
  assert (MN' : val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) (LA + 8) 4 (hl_n l));
  [ replace (LA + 8) with (base_val Ev (Some 10%nat) + 8) by (rewrite EV10; ring);
    apply (val_of_chunk_ok SEGS Ev _ _ 8 4 (SOff 33 0));
    [ exact (CK3 (YP09.mkChunk 8 (CVal 4 (SOff 33 0))) ltac:(clear; cbn; tauto))
    | cbn [sv_denot]; rewrite Z.add_0_r, EVx by (clear; cbv; lia); rewrite E33, unsigned_lit_small by (clear - Hnc Rn0; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); clear - Hnc Rn0; lia | clear; vm_compute; discriminate ] |];
  assert (MC' : val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) (LA + 12) 4 (hl_cap l));
  [ replace (LA + 12) with (base_val Ev (Some 10%nat) + 12) by (rewrite EV10; ring);
    apply (val_of_chunk_ok SEGS Ev _ _ 12 4 (SOff 34 0));
    [ exact (CK3 (YP09.mkChunk 12 (CVal 4 (SOff 34 0))) ltac:(clear; cbn; tauto))
    | cbn [sv_denot]; rewrite Z.add_0_r, EVx by (clear; cbv; lia); rewrite E34, unsigned_lit_small by (clear - Hnc Rn0; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); clear - Hnc Rn0; lia | clear; vm_compute; discriminate ] |];
  idtac
end.
(* heap and low bytes off the image were not written by the two runs *)
assert (KEEP : forall a, 0 <= a < alloc_ceiling -> (a + 1 <= 0x10000 \/ 0x5fb000 <= a \/ ~ (LA <= a < LA + 16)) ->
  mrestrict (w_H W) (ms_mem ms0) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)).
{ intros a Ha Hoi.
  lazymatch type of HFr0 with frame_of ?Ev0 ?rs0 _ _ => let r0 := eval vm_compute in rs0 in change rs0 with r0 in HFr0 end.
  lazymatch type of HFr with frame_of ?Ev1 ?rs1 _ _ => let r1 := eval vm_compute in rs1 in change rs1 with r1 in HFr end.
  rewrite HFr0, HFr; [reflexivity | |];
  rewrite unsigned_lit_small by (clear - Ha C1; unfold alloc_ceiling in *; lia);
  intros (r & Hin & Hr); cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]); try destruct Hin;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?ew_ewset_other in Hr by (clear; discriminate);
  try rewrite Usp in Hr; try (rewrite E10, unsigned_lit_small in Hr by (clear - HLAr; lia));
  clear - Hr Hoi Ha Hceil Hslo Hstk0 HLAr WS C1; unfold LP_STK, ASTACK in *; lia. }
(* the list as it is at the call: the same as at entry *)
assert (HLc : alist_at B ly S W (ms_mem ms0) LA l lines).
{ apply (alist_at_kept B ly S W mem ly S W (ms_mem ms0) LA l lines HL); [|exact (lp_blks_in ly S W mem LA l lines HL)].
  intros r Hr a Ha.
  assert (HWg : writable_at SEGS (mrestrict (w_H W) mem) a -> writable_at SEGS (mrestrict (w_H W) (ms_mem ms0)) a)
  by (intros Hw;
      lazymatch goal with Hb : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
        eapply writable_at_grows; [exact Hb|] end;
      eapply writable_at_grows; [exact HG0 | exact Hw]).
  destruct (Z.le_gt_cases LA a) as [Hlo | Hlo]; [destruct (Z.lt_ge_cases a (LA + 16)) as [Hhi | Hhi]|].
  - (* the struct: its three fields hold the same values, and it stays writable *)
    split; [| intros _; apply HWg; replace a with (LA + (a - LA)) by ring; apply HwL; clear - Hlo Hhi; lia].
    unfold aview. f_equal. unfold arm in Mv, Mn, Mc.
    destruct (Z.lt_ge_cases a (LA + 8)) as [Hz8 | Hz8]; [|destruct (Z.lt_ge_cases a (LA + 12)) as [Hz12 | Hz12]].
    + replace a with (LA + (a - LA)) by ring.
      exact (val_mem_agree SEGS _ _ LA 8 (hl_v l) Mv MV' (a - LA) ltac:(clear - Hlo Hz8; cbn; lia)).
    + replace a with ((LA + 8) + (a - (LA + 8))) by ring.
      exact (val_mem_agree SEGS _ _ (LA + 8) 4 (hl_n l) Mn MN' (a - (LA + 8)) ltac:(clear - Hz8 Hz12; cbn; lia)).
    + replace a with ((LA + 12) + (a - (LA + 12))) by ring.
      exact (val_mem_agree SEGS _ _ (LA + 12) 4 (hl_cap l) Mc MC' (a - (LA + 12)) ltac:(clear - Hz12 Hhi; cbn; lia)).
  - destruct (lp_fp_blk ly S W mem LA l lines HL r a Hr Ha ltac:(clear - Hhi; lia)) as ([p nb] & Hb & Hab).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p nb HAR Hb) as (_ & H4096 & Hceilb & _).
    pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ p nb HAR Hb) as Hoff. unfold off_img in Hoff. cbn [fst snd] in Hab.
    assert (Hk : mrestrict (w_H W) (ms_mem ms0) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
    by (apply KEEP; clear - Hab H4096 Hceilb Hoff; lia).
    split; [apply aview_eq_of; exact Hk | intros Hw; exact (writable_at_eq SEGS _ _ a Hk Hw)].
  - destruct (lp_fp_blk ly S W mem LA l lines HL r a Hr Ha ltac:(clear - Hlo; lia)) as ([p nb] & Hb & Hab).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p nb HAR Hb) as (_ & H4096 & Hceilb & _).
    pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ p nb HAR Hb) as Hoff. unfold off_img in Hoff. cbn [fst snd] in Hab.
    assert (Hk : mrestrict (w_H W) (ms_mem ms0) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
    by (apply KEEP; clear - Hab H4096 Hceilb Hoff; lia).
    split; [apply aview_eq_of; exact Hk | intros Hw; exact (writable_at_eq SEGS _ _ a Hk Hw)]. }
assert (Hng : lp_grow l = false) by (unfold lp_grow; apply Z.eqb_neq; clear - Hlt; lia).
assert (HSRC : garr8 SEGS (mrestrict (w_H W) (ms_mem ms0)) SRC (bzs x)).
{ destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md q k HAR Hq) as (_ & H4096 & Hceilq & _).
  pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ q k HAR Hq) as Hoff. unfold off_img in Hoff.
  apply (akept_garr8 W mem W (ms_mem ms0)); [|exact Hsrc].
  intros a Ha. unfold bzs in Ha. rewrite length_map in Ha.
  assert (Hk : mrestrict (w_H W) (ms_mem ms0) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
  by (apply KEEP; clear - Ha Hq1 Hq2 H4096 Hceilq Hoff; lia).
  split; [apply aview_eq_of; exact Hk | intros Hw; exact (writable_at_eq SEGS _ _ a Hk Hw)]. }
eapply (TAIL_R W ly S Hp regs mem md LA SRC l lines x q k W ly S Hp (ms_regs ms0) (ms_mem ms0) _ 0 l kr Hq Hqv Hq1 Hq2).
unfold lp_tail_pre_xR. cbv zeta. rewrite Hng. cbn [andb negb app].
split; [exact HJ|]. split; [exists ch; exact HPRE|]. split; [exact HGL|]. split; [exact HZ|].
split; [exact HLc|]. split; [reflexivity|].
split; [unfold grow_cap; destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [Heq|_]; [clear - Hlt Heq; lia | reflexivity]|].
split; [unfold grow_cap; destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [Heq|_]; [clear - Hlt Heq; lia | clear - Hlt; lia]|].
split; [intros _; reflexivity|]. split; [intros Hg; discriminate|].
split; [intros rest Hpr; exact Hpr|]. split; [reflexivity|]. split; [exact (mle_start MT S MLAW)|].
split; [exact HMOK|].
(* the room round: the list has room, so the tail's malloc is list_push's only call, at the entry's state S *)
split; [rewrite lp_rk_eq, Hng in HRM; exact HRM|]. split; [exact (lp_cnt_at RP _ _ HCNT)|].
split; [pose proof (lp_peak_nogrow (blocks_bytes S) l (Z.of_nat (length x)) Hng ltac:(lia) Hlive); lia|].
split; [exact Hx16|].
split; [exact HSRC|]. split; [exact Hlines1|]. split; [exact Hlines2|].
split; [rewrite Q2, Usp; f_equal; clear; ring|].
split; [rewrite Q3, E3; reflexivity|]. split; [rewrite Q4, E4; reflexivity|]. split; [rewrite Q27, E27; reflexivity|].
split; [rewrite Q8, E10, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
split; [rewrite Q9, E12; reflexivity|]. split; [rewrite Q18, E10; reflexivity|]. split; [rewrite Q19, E11; reflexivity|].
split; [rewrite Q20, E10, unsigned_lit_small by (clear - HLAr; lia); reflexivity|]. split; [rewrite Q21, E35; reflexivity|].
split; [rewrite Q22, E10, E35, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
split; [rewrite Q23, E10; reflexivity|].
split; [rewrite Q24, E10, E35, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
split; [rewrite Q10, E12, unsigned_lit_small by (clear - Hx16; lia); reflexivity|].
split; [exact SAVED|].
split.
2: { intros i Hi. destruct (lp_errno_out LA (as_errno B + i) HGL ltac:(clear - Hi; lia)) as [HeR HeL].
     apply aview_eq_of. apply KEEP; [clear - HeR C1; lia | right; right; exact HeL]. }
intros a _ _ _ Hpa.
lazymatch goal with Hb : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
  apply (apresent_grows _ _ _ a Hb) end.
exact (apresent_grows _ _ _ a HG0 Hpa).
-
(* the list is full: N = CAP; the vector grows with realloc *)
assert (Heq : hl_n l = hl_cap l).
{ rewrite branch_ne_U in Hc. rewrite (U_atom _ 33 (hl_n l)), (U_atom _ 34 (hl_cap l)) in Hc;
  [| rewrite !ew_ewset_other by lia; exact E34 | lia | rewrite !ew_ewset_other by lia; exact E33 | lia].
  apply Bool.negb_false_iff, Z.eqb_eq in Hc. lia. }
(* the room round: lp_spec_x's budget at a growing list is 3 (realloc, then the tail's malloc) *)
assert (HRM3 : rp_RM RP S (3 + kr)%nat).
{ assert (Hgr : lp_grow l = true) by (unfold lp_grow; rewrite Heq; apply Z.eqb_refl).
  rewrite lp_rk_eq, Hgr in HRM. exact HRM. }
paj_run_tok_xR RUNG HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end.
  apply awr_ok_x_cons_awr0; [awr_ok_tac; rewrite ?ew_ewset_other by lia; exact Usp|].
  apply awr_ok_x_cons_awr0; [awr_ok_tac|].
  apply awr_ok_x_cons_awr0; [awr_ok_tac|].
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite ?ew_ewset_other in Ha by lia.
  rewrite E10, unsigned_lit_small in Ha by (pose proof (inG_img LA (HGL LA ltac:(lia))); lia). apply HGL. lia. }
(* bnez a0 at 0x85114: CAP <> 0 (s9 := 2 CAP, slliw) or CAP = 0 (s9 := 8); both reach the realloc call *)
psrr_branch_tok RUNG BRG HS SHOK Bspan.
all: paj_run_tok_xR RUNG HS HJ SHOK Bspan.
all: try (lazymatch goal with |- awr_ok_x _ ?rs _ _ _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
  apply awr_ok_x_cons_awr0; [awr_ok_tac; rewrite ?ew_ewset_other by lia; exact Usp|];
  apply awr_ok_x_cons_awr0; [awr_ok_tac|];
  apply awr_ok_x_cons_awr0; [awr_ok_tac|];
  apply awr_ok_x_cons_g; [|apply awr_ok_x_nil];
  intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?ew_ewset_other in Ha by lia;
  rewrite E10, unsigned_lit_small in Ha by (pose proof (inG_img LA (HGL LA ltac:(lia))); lia); apply HGL; lia).
(* s9 and a1 = s9 << 4, per arm *)
all: prreg HS (25%bv : bv 5) Q25.
all: prreg HS (11%bv : bv 5) Q11.
1: assert (R25 : getr (ms_regs ms1) 25 = w64 (grow_cap (hl_n l) (hl_cap l)) /\ getr (ms_regs ms1) 11 = w64 (lp_vbytes l)).
1: { assert (Hn0 : hl_n l <> 0).
     { rewrite branch_ne_U in Hc0. rewrite (U_atom _ 33 (hl_n l)) in Hc0 by first [rewrite !ew_ewset_other by lia; exact E33 | lia].
       rewrite U_lit in Hc0 by lia. apply Bool.negb_true_iff, Z.eqb_neq in Hc0. exact Hc0. }
     unfold lp_vbytes, grow_cap, AREC. rewrite Heq, Z.eqb_refl. destruct (Z.eqb_spec (hl_cap l) 0) as [E0|E0]; [lia|].
     rewrite Q25, Q11, E33. unfold w64. rewrite !lp_sll by lia. split; f_equal; lia. }
2: assert (R25 : getr (ms_regs ms1) 25 = w64 (grow_cap (hl_n l) (hl_cap l)) /\ getr (ms_regs ms1) 11 = w64 (lp_vbytes l)).
2: { assert (Hc00 : hl_cap l = 0).
     { rewrite branch_ne_U in Hc0. rewrite (U_atom _ 33 (hl_n l)) in Hc0 by first [rewrite !ew_ewset_other by lia; exact E33 | lia].
       rewrite U_lit in Hc0 by lia. apply Bool.negb_false_iff, Z.eqb_eq in Hc0. lia. }
     unfold lp_vbytes, grow_cap, AREC. rewrite Heq, Z.eqb_refl, Hc00. cbn [Z.eqb]. rewrite Q25, Q11. split; reflexivity. }
(* the rest is the same in both arms *)
all: pmkst HS.
all: prreg HS (1%bv : bv 5) Q1.
all: prreg HS (2%bv : bv 5) Q2.
all: prreg HS (3%bv : bv 5) Q3.
all: prreg HS (4%bv : bv 5) Q4.
all: prreg HS (8%bv : bv 5) Q8.
all: prreg HS (9%bv : bv 5) Q9.
all: prreg HS (10%bv : bv 5) Q10.
all: prreg HS (18%bv : bv 5) Q18.
all: prreg HS (19%bv : bv 5) Q19.
all: prreg HS (20%bv : bv 5) Q20.
all: prreg HS (21%bv : bv 5) Q21.
all: prreg HS (22%bv : bv 5) Q22.
all: prreg HS (23%bv : bv 5) Q23.
all: prreg HS (24%bv : bv 5) Q24.
all: prreg HS (26%bv : bv 5) Q26.
all: prreg HS (27%bv : bv 5) Q27.
all: assert (HLAr : 0x10000 <= LA /\ LA + 16 <= 0x5fb000)
  by (pose proof (inG_img LA (HGL LA ltac:(lia))); pose proof (inG_img (LA + 15) (HGL (LA + 15) ltac:(lia))); lia).
all: assert (E27 : ew E 27 = getr regs 27) by (rewrite (proj1 HAE 27%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 27 27%bv eq_refl)).
all: lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
  assert (CK : forall i r c, nth_error (ss_mem ssv) i = Some r -> In c (YP09.r_chunks r) ->
    YP09.chunk_ok SEGS Ev (mrestrict (w_H W) (ms_mem msv)) (base_val Ev (YP09.r_base r)) c)
  by (intros i r c Hi1 Hc1; exact (st_ok_chunk SEGS Ev ssv (restrict (w_H W) msv) i r c HS Hi1 Hc1)) end.
all: lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
  lazymatch eval vm_compute in (nth_error (ss_mem ssv) 0) with Some ?r0 =>
    assert (CK0 : forall c, In c (YP09.r_chunks r0) ->
      YP09.chunk_ok SEGS Ev (mrestrict (w_H W) (ms_mem msv)) (base_val Ev (Some 2%nat)) c)
    by (intros c Hc1; exact (CK 0%nat r0 c ltac:(vm_compute; reflexivity) Hc1)) end;
  lazymatch eval vm_compute in (nth_error (ss_mem ssv) 3) with Some ?r3 =>
    assert (CK3 : forall c, In c (YP09.r_chunks r3) ->
      YP09.chunk_ok SEGS Ev (mrestrict (w_H W) (ms_mem msv)) (base_val Ev (Some 10%nat)) c)
    by (intros c Hc1; exact (CK 3%nat r3 c ltac:(vm_compute; reflexivity) Hc1)) end end.
all: lazymatch type of HS with st_ok _ ?Ev ?ssv (restrict _ ?msv) =>
  assert (EV2 : base_val Ev (Some 2%nat) = spZ regs)
    by (cbn [base_val]; rewrite ?ew_ewset_other by (clear; discriminate); exact Usp);
  assert (EV10 : base_val Ev (Some 10%nat) = LA)
    by (cbn [base_val]; rewrite ?ew_ewset_other by (clear; discriminate); rewrite E10;
        apply unsigned_lit_small; clear - HLAr; lia);
  assert (EVr : forall r, (r < 32)%nat -> ew Ev r = ew E r)
    by (intros r Hr; rewrite ?ew_ewset_other by (clear - Hr; lia); reflexivity);
  assert (EVx : forall r, (32 <= r < 36)%nat -> ew Ev r = ew E r)
    by (intros r Hr; rewrite ?ew_ewset_other by (clear - Hr; lia); reflexivity);
  assert (SAVED : Forall (fun p => val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) (spZ regs - 96 + fst p) 8
    (bv_unsigned (getr regs (Z_to_bv 5 (snd p))))) lp_saved);
  [ unfold lp_saved; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    lazymatch goal with |- val_mem _ _ (spZ ?rg - 96 + ?o) 8 (bv_unsigned (getr ?rg (Z_to_bv 5 ?r))) =>
      let c := eval vm_compute in (o - 96) in
      let rn := eval vm_compute in (Z.to_nat r) in
      replace (spZ rg - 96 + o) with (base_val Ev (Some 2%nat) + c) by (rewrite EV2; clear; lia);
      apply (val_of_chunk_ok SEGS Ev _ _ c 8 (SOff rn 0));
      [ exact (CK0 (YP09.mkChunk c (CVal 8 (SOff rn 0))) ltac:(clear; cbn; tauto))
      | cbn [sv_denot]; rewrite Z.add_0_r, EVr by (clear; cbv; lia);
        rewrite (proj1 HAE rn ltac:(clear; cbv; lia)), (ew_Ereg_nat regs _ rn (Z_to_bv 5 r) ltac:(vm_compute; reflexivity));
        reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR; change (bv_modulus 64) with (2 ^ 64) in HR;
        change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - HR; lia
      | clear; vm_compute; discriminate ] end |];
  assert (MV' : val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) LA 8 (hl_v l));
  [ replace LA with (base_val Ev (Some 10%nat) + 0) by (rewrite EV10; ring);
    apply (val_of_chunk_ok SEGS Ev _ _ 0 8 (SOff 32 0));
    [ exact (CK3 (YP09.mkChunk 0 (CVal 8 (SOff 32 0))) ltac:(clear; cbn; tauto))
    | cbn [sv_denot]; rewrite Z.add_0_r, EVx by (clear; cbv; lia); rewrite E32, unsigned_lit_small by (clear - Rv; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Rv; lia | clear; vm_compute; discriminate ] |];
  assert (MN' : val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) (LA + 8) 4 (hl_n l));
  [ replace (LA + 8) with (base_val Ev (Some 10%nat) + 8) by (rewrite EV10; ring);
    apply (val_of_chunk_ok SEGS Ev _ _ 8 4 (SOff 33 0));
    [ exact (CK3 (YP09.mkChunk 8 (CVal 4 (SOff 33 0))) ltac:(clear; cbn; tauto))
    | cbn [sv_denot]; rewrite Z.add_0_r, EVx by (clear; cbv; lia); rewrite E33, unsigned_lit_small by (clear - Hnc Rn0; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); clear - Hnc Rn0; lia | clear; vm_compute; discriminate ] |];
  assert (MC' : val_mem SEGS (mrestrict (w_H W) (ms_mem msv)) (LA + 12) 4 (hl_cap l));
  [ replace (LA + 12) with (base_val Ev (Some 10%nat) + 12) by (rewrite EV10; ring);
    apply (val_of_chunk_ok SEGS Ev _ _ 12 4 (SOff 34 0));
    [ exact (CK3 (YP09.mkChunk 12 (CVal 4 (SOff 34 0))) ltac:(clear; cbn; tauto))
    | cbn [sv_denot]; rewrite Z.add_0_r, EVx by (clear; cbv; lia); rewrite E34, unsigned_lit_small by (clear - Hnc Rn0; lia); reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); clear - Hnc Rn0; lia | clear; vm_compute; discriminate ] |];
  idtac
end.
(* the three runs wrote only the frame and the list struct *)
all: assert (HGT : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms1)))
  by exact (mem_grows_trans _ _ _ HG0 (mem_grows_trans _ _ _ HG1 HG2)).
all: assert (KEEP : forall a, 0 <= a < alloc_ceiling -> (a + 1 <= 0x10000 \/ 0x5fb000 <= a \/ ~ (LA <= a < LA + 16)) ->
  mrestrict (w_H W) (ms_mem ms1) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
  by (intros a Ha Hoi;
  lazymatch type of HFr1 with frame_of ?Ev0 ?rs0 _ _ => let r0 := eval vm_compute in rs0 in change rs0 with r0 in HFr1 end;
  lazymatch type of HFr0 with frame_of ?Ev0 ?rs0 _ _ => let r0 := eval vm_compute in rs0 in change rs0 with r0 in HFr0 end;
  lazymatch type of HFr with frame_of ?Ev1 ?rs1 _ _ => let r1 := eval vm_compute in rs1 in change rs1 with r1 in HFr end;
  rewrite HFr1, HFr0, HFr; [reflexivity | | |];
  rewrite unsigned_lit_small by (clear - Ha C1; unfold alloc_ceiling in *; lia);
  intros (r & Hin & Hr); cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]); try destruct Hin;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?ew_ewset_other in Hr by (clear; discriminate);
  try rewrite Usp in Hr; try (rewrite E10, unsigned_lit_small in Hr by (clear - HLAr; lia));
  clear - Hr Hoi Ha Hceil Hslo Hstk0 HLAr WS C1; unfold LP_STK, ASTACK in *; lia).
(* the list as it is at the realloc call: the same as at entry *)
all: assert (HLc : alist_at B ly S W (ms_mem ms1) LA l lines)
  by (apply (alist_at_kept B ly S W mem ly S W (ms_mem ms1) LA l lines HL); [|exact (lp_blks_in ly S W mem LA l lines HL)];
  intros r Hr a Ha;
  assert (HWg : writable_at SEGS (mrestrict (w_H W) mem) a -> writable_at SEGS (mrestrict (w_H W) (ms_mem ms1)) a)
    by (intros Hw; eapply writable_at_grows; [exact HGT | exact Hw]);
  destruct (Z.le_gt_cases LA a) as [Hlo | Hlo]; [destruct (Z.lt_ge_cases a (LA + 16)) as [Hhi | Hhi]|];
  [ split; [| intros _; apply HWg; replace a with (LA + (a - LA)) by ring; apply HwL; clear - Hlo Hhi; lia];
    unfold aview; f_equal; unfold arm in Mv, Mn, Mc;
    destruct (Z.lt_ge_cases a (LA + 8)) as [Hz8 | Hz8]; [|destruct (Z.lt_ge_cases a (LA + 12)) as [Hz12 | Hz12]];
    [ replace a with (LA + (a - LA)) by ring;
      exact (val_mem_agree SEGS _ _ LA 8 (hl_v l) Mv MV' (a - LA) ltac:(clear - Hlo Hz8; cbn; lia))
    | replace a with ((LA + 8) + (a - (LA + 8))) by ring;
      exact (val_mem_agree SEGS _ _ (LA + 8) 4 (hl_n l) Mn MN' (a - (LA + 8)) ltac:(clear - Hz8 Hz12; cbn; lia))
    | replace a with ((LA + 12) + (a - (LA + 12))) by ring;
      exact (val_mem_agree SEGS _ _ (LA + 12) 4 (hl_cap l) Mc MC' (a - (LA + 12)) ltac:(clear - Hz12 Hhi; cbn; lia)) ]
  | destruct (lp_fp_blk ly S W mem LA l lines HL r a Hr Ha ltac:(clear - Hhi; lia)) as ([p nb] & Hb & Hab);
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p nb HAR Hb) as (_ & H4096 & Hceilb & _);
    pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ p nb HAR Hb) as Hoff; unfold off_img in Hoff; cbn [fst snd] in Hab;
    assert (Hk : mrestrict (w_H W) (ms_mem ms1) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
      by (apply KEEP; clear - Hab H4096 Hceilb Hoff; lia);
    split; [apply aview_eq_of; exact Hk | intros Hw; exact (writable_at_eq SEGS _ _ a Hk Hw)]
  | destruct (lp_fp_blk ly S W mem LA l lines HL r a Hr Ha ltac:(clear - Hlo; lia)) as ([p nb] & Hb & Hab);
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p nb HAR Hb) as (_ & H4096 & Hceilb & _);
    pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ p nb HAR Hb) as Hoff; unfold off_img in Hoff; cbn [fst snd] in Hab;
    assert (Hk : mrestrict (w_H W) (ms_mem ms1) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
      by (apply KEEP; clear - Hab H4096 Hceilb Hoff; lia);
    split; [apply aview_eq_of; exact Hk | intros Hw; exact (writable_at_eq SEGS _ _ a Hk Hw)] ]).
all: assert (HSRC : garr8 SEGS (mrestrict (w_H W) (ms_mem ms1)) SRC (bzs x))
  by (destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md q k HAR Hq) as (_ & H4096 & Hceilq & _);
  pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN _ _ _ _ _ _ q k HAR Hq) as Hoff; unfold off_img in Hoff;
  apply (akept_garr8 W mem W (ms_mem ms1)); [|exact Hsrc];
  intros a Ha; unfold bzs in Ha; rewrite length_map in Ha;
  assert (Hk : mrestrict (w_H W) (ms_mem ms1) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
    by (apply KEEP; clear - Ha Hq1 Hq2 H4096 Hceilq Hoff; lia);
  split; [apply aview_eq_of; exact Hk | intros Hw; exact (writable_at_eq SEGS _ _ a Hk Hw)]).
(* the realloc call: the growth segment *)
all: eapply (lp_grow_seg_xR W ly S Hp regs mem md LA SRC l lines x q k (ms_regs ms1) (ms_mem ms1) _ kr).
all: unfold lp_rcall_pre_xR; cbv zeta.
all: split; [exact HJ|].
all: split; [exists ch; exact HPRE|].
all: split; [exact HGL|].
all: split; [exact HZ|].
all: split; [exact HLc|].
all: split; [exact Heq|].
all: split; [apply Hcap25; unfold lp_grow; rewrite Heq; apply Z.eqb_refl|].
all: split; [exact Hlive|].
all: split; [exact Hx16|].
all: split; [exact Hq|].
all: split; [exact Hqv|].
all: split; [exact Hq1|].
all: split; [exact Hq2|].
all: split; [exact HSRC|].
all: split; [exact Hlines1|].
all: split; [exact Hlines2|].
all: split; [exact HMOK|].
all: split; [exact HRM3|].
all: split; [exact HCNT|].
all: split; [rewrite Q1; reflexivity|].
all: split; [rewrite Q2, Usp; f_equal; clear; ring|].
all: split; [rewrite Q3, E3; reflexivity|].
all: split; [rewrite Q4, E4; reflexivity|].
all: split; [rewrite Q27, E27; reflexivity|].
all: split; [rewrite Q8, E10, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
all: split; [rewrite Q9, E12; reflexivity|].
all: split; [rewrite Q18, E10; reflexivity|].
all: split; [rewrite Q19, E11; reflexivity|].
all: split; [rewrite Q20, E10, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
all: split; [rewrite Q21, E35; reflexivity|].
all: split; [rewrite Q22, E10, E35, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
all: split; [rewrite Q23, E10; reflexivity|].
all: split; [rewrite Q24, E10, E35, unsigned_lit_small by (clear - HLAr; lia); reflexivity|].
all: split; [exact (proj1 R25)|].
all: split; [rewrite Q26, E10, E35; reflexivity|].
all: split; [rewrite Q10, E32; reflexivity|].
all: split; [exact (proj2 R25)|].
all: split; [exact SAVED|].
all: split; [intros a _ _ _ Hpa; exact (apresent_grows _ _ _ a HGT Hpa)|].
all: intros i Hi; destruct (lp_errno_out LA (as_errno B + i) HGL ltac:(clear - Hi; lia)) as [HeR HeL];
  apply aview_eq_of; apply KEEP; [clear - HeR C1; lia | right; right; exact HeL].
Qed.
End wR.
Lemma lp_rcall_pre_wle : lp_rcall_pre = lp_rcall_pre_xR (@wle SEGS). Proof. reflexivity. Qed.
(* pb_list_push_xR at R := wle: the laws of wle, RO := True, HA := True, the realloc rule at R from the strict ARE by
   W_journal_x.v arealloc_cf_rule_c_xR_of_x, and TAIL_R at wle is the strict TAIL *)
Theorem pb_list_push_x : lp_spec_x B PST ARx MT RP G MMAX A_list_pushP.
Proof.
eapply (pb_list_push_xR (@wle SEGS)) with (RO := fun _ => True) (HA := fun _ _ _ _ _ _ => True);
  first [ exact TAIL | intros ? ? H; exact H | intros ?; apply wle_refl
        | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2]
        | exact (fun _ _ _ _ _ _ _ => I) | (apply arealloc_cf_rule_c_xR_of_x; exact ARE) ].
Qed.
End c.
(* list_push's G-generic form (W_contract_x.v lp_spec_g_x): the Section hypotheses on G are lp_spec_g_x's premises
   gx_ok / gx_rt; the second segment TAIL is W_lp_tail.v's pb_lp_tail_x; the allocator rules stay hypotheses, each at
   its own caller-context table with its closed trace fact (the instance proves each rule at its own table, and a _c
   rule at a larger table is stronger): realloc at CTX_R, malloc at CTX_M. *)
Section g.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
(* the room round: lp_spec_g_x passes RP through (W_contract_x.v Section w2g) *)
Variable RP : roomp.
Hypothesis MLAW : ameter_laws MT.
Variable MMAX : Z.
Hypothesis HMMAX : 2 ^ 29 < MMAX <= 2 ^ 30.
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Variable CTX_R : list (list Z).
Hypothesis ARE : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_lp_realloc : In [BASE + AF_fr_list_push + 0xac] CTX_R.
Variable CTX_M : list (list Z).
Hypothesis AMA : amalloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_M.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis HCTX_lp_malloc : In [BASE + AF_fr_list_push + 0xd0] CTX_M.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0, 4): list_push's G-generic form at a world relation R (W_contract_xR.lp_spec_g_xR):
   pb_list_push_xR with TAIL_R discharged by W_lp_tail.pb_lp_tail_xR; the realloc rule at R at CTX_R, the malloc rule at
   R at CTX_M, their call-boundary premise from RO_ARx and realloc's hull admission from HA_call;
   __asan_memcpy stays the strict AMEMCPY.  pb_list_push_g_x keeps its strict proof. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Variable HA : alayout -> astate -> bvmap 5 word -> list (Z * Z * Z) -> Z -> Z -> Prop.
Hypothesis HA_call : forall lyc Sc regsT ch p n, mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HA lyc Sc regsT ch p n.
Hypothesis ARE_R : arealloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO HA CTX_R R (SIGMA WS_realloc).
Hypothesis AMA_R : amalloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO CTX_M R.
(* :1183 pb_list_push_g_x *)
Theorem pb_list_push_g_xR : lp_spec_g_xR B PST ARx R MT RP MMAX (BASE + AF_fr_list_push).
Proof.
intros G HG HGR.
change (BASE + AF_fr_list_push) with A_list_pushP.
assert (HM29 : 2 ^ 29 < MMAX) by lia.
eapply pb_list_push_xR with (CTX := CTX_R) (R := R) (RO := RO) (HA := HA); try eassumption.
eapply pb_lp_tail_xR with (CTX := CTX_M) (R := R) (RO := RO); eassumption.
Qed.
End wR.
Theorem pb_list_push_g_x : lp_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_list_push).
Proof.
intros G HG HGR.
change (BASE + AF_fr_list_push) with A_list_pushP.
assert (HM29 : 2 ^ 29 < MMAX) by lia.
eapply pb_list_push_x with (CTX := CTX_R); try eassumption.
eapply pb_lp_tail_x with (CTX := CTX_M); eassumption.
Qed.
End g.

(* ---- THE AR STATEMENTS, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_list_push's and pb_list_push_g's
   statements are the AR walk's, byte-identical, now corollaries of pb_list_push_x / pb_list_push_g_x at
   ARx := ARi0 (cgif's AR with the head set empty), PST := [].  Their Sections take LX0 (the laws at ARi0, a Theorem Labs lane's
   rulings (a) and HP0) in place of LAWS, and the allocator rules in their caller-context forms (W_journal.v Section
   hc; pb_list_push at its realloc table CTX, pb_list_push_g at CTX_R for realloc and CTX_M for malloc) with the
   closed trace facts HCTX_lp_realloc / HCTX_lp_malloc in place of arealloc_cf_rule /
   amalloc_cf_rule.  TAIL keeps its AR form.  The bridges: W_contract_x.lp_spec_x_AR0 / lp_spec_g_x_AR0,
   W_list_push_tail.lp_tail_stmt_x_of_AR0, W_journal_x.arealloc_cf_rule_c_x_of_AR0 / amalloc_cf_rule_c_x_of_AR0 /
   ARi0_hp0, W_sites_x.aintrin_realizes_x_of_AR0, W_kit_x.AR_imgc / AR_blkn. ---- *)
Section cAR.
Variable B : asyms.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Variable MMAX : Z.
Hypothesis HMMAX : 2 ^ 29 < MMAX <= 2 ^ 30.
Variable G : list (Z * Z).
Hypothesis HG : gx_ok SEGS B G.
Hypothesis HGR : gx_rt B G.
Variable CTX : list (list Z).
Hypothesis ARE : arealloc_cf_rule_c SEGS B MT MMAX CTX (SIGMA WS_realloc).
Hypothesis HCTX_lp_realloc : In [BASE + AF_fr_list_push + 0xac] CTX.
Hypothesis TAIL : lp_tail_stmt B MT G.
Theorem pb_list_push : lp_spec B MT G MMAX A_list_pushP.
Proof.
apply lp_spec_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (IMGC : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly))
  by (intros ly S Hp W mem md H; destruct H as [HAR _]; exact (AR_imgc B ly S Hp W mem md HAR)).
assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
  by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin)).
pose proof (arealloc_cf_rule_c_x_of_AR0 SEGS B MT MMAX CTX (SIGMA WS_realloc) ARE) as AREx.
pose proof (lp_tail_stmt_x_of_AR0 B MT G TAIL) as TAILx.
eapply pb_list_push_x; eassumption.
Qed.
End cAR.
Section gAR.
Variable B : asyms.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Variable MMAX : Z.
Hypothesis HMMAX : 2 ^ 29 < MMAX <= 2 ^ 30.
Variable CTX_R : list (list Z).
Hypothesis ARE : arealloc_cf_rule_c SEGS B MT MMAX CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_lp_realloc : In [BASE + AF_fr_list_push + 0xac] CTX_R.
Variable CTX_M : list (list Z).
Hypothesis AMA : amalloc_cf_rule_c SEGS B MT MMAX CTX_M.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA WS_asan_memcpy).
Hypothesis HCTX_lp_malloc : In [BASE + AF_fr_list_push + 0xd0] CTX_M.
Theorem pb_list_push_g : lp_spec_g B MT MMAX (BASE + AF_fr_list_push).
Proof.
apply lp_spec_g_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (IMGC : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly))
  by (intros ly S Hp W mem md H; destruct H as [HAR _]; exact (AR_imgc B ly S Hp W mem md HAR)).
assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
  by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin)).
pose proof (arealloc_cf_rule_c_x_of_AR0 SEGS B MT MMAX CTX_R (SIGMA WS_realloc) ARE) as AREx.
pose proof (amalloc_cf_rule_c_x_of_AR0 SEGS B MT MMAX CTX_M AMA) as AMAx.
pose proof (aintrin_realizes_x_of_AR0 SEGS B OCpy (SIGMA WS_asan_memcpy) AMEMCPY) as AMEMCPYx.
eapply (pb_list_push_g_x B [] (ARi0 SEGS B) LX0 HP0 TL MT RP_AR MLAW MMAX HMMAX IMGC BLKN CTX_R AREx HCTX_lp_realloc
  CTX_M AMAx AMEMCPYx HCTX_lp_malloc).
Qed.
End gAR.
End b.
End a.
