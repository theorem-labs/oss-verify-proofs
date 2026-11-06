(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/cgif/cgif_file_fuzzer/lib/YFg5cf.v (commit 3cae605a900a, file sha256 7b433b3baae0) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; cgif's image-instance names kept where preset's B' instance carries them (AGif2cgif, AImg_cgif), CfImg_cgif -> CfImg_B, cgif's image rows mapped to preset's (YGcfImgcgif.* -> CfImgB / PresetImgRefillB / PresetImgRowsB, *cgif -> *preset); its 4 image numerals moved by symbol from cgif_file_fuzzer.asan-ubsan (pin 1c29845fe605, unstripped twin of the same build) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal, jump-table offsets, derived counts and list indices by the same stage map), 0 list indices re-picked, and 0 addresses named in comments; facts preset already states are cited, not restated; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10-30 (lane F1 of the generic cf instance layer; integrator
   ReallocPrimary): the RELATION half of proofs/cgif/cgif_file_fuzzer/lib/YFg5.v at c5 30a1993588f (Enqueue's HIT
   arm: a new batch from a non-empty class-24 cache), ported from cgif's AR / enq_pre to the cf instance's ARX_cf /
   enq_pre_cf, as YFg4cf.v ported YFg4.v.  Kept, with these changes only: the Section's call premise is
   YGcfInstEnq.enq_pre_cf at YGcfInstBase.ARX_cf B IOK Hp; Hci reads Wf_cf (wrc_cache); HI (:99) / NBG (YFfqcf.v:331, read here through q_hit_facts) read YFf2cf.HIGH /
   YFf2cf.nb_geom (kFreeArrayOffset for 2 ^ 31); WIN_dec reads 1 <= cnt from l <> [] (not from cache_vals); HTSD is a
   lemma (amc_tsd); FINQH becomes FINQH_cf, whose conclusion is EnqGbase.enq_leaf_g0 at ARX_cf (the call post the cf
   instance's EnqIfaceHit.ih_post states), through YFf2cf.enq_fin_ARmcf_x (its ARmcf part, :493), ALedger_same_cf, ahs_transfer_cf and Wf_cf
   of the end state from YGcfInstEnqG.enq_hit_wf_cf.
   ALSO PORTED (below, :108-:318): of the walk half, the E0 equations (:122-:136), the readers q_* (:137-:181: cell readers, cache_vals,
   last_facts, hit_facts, u_facts, q_facts), REG0_ok .. SEED_ok (as *_cf, :190-:291) and FH_ok (as FH_ok_cf, :293); fh_Hnn (YFgq.v:126,
   1 <= nn <= kQuarantineMax) is YFfqcf.u_facts_cf's 1 <= nn and enq_pre_cf's guard (HNM, :119; :310).  NOT HERE: tfib_enqueue_hit_arm / tfib_enqueue_hit; the unit's walk YFh4.segQH takes FH_ok_cf (AU/YGcfInstEnqMisspreset.v:354-356).
   IMAGE-SPECIFIC (cgif_file's image, TfibSyms): each unit relocates this file to its own image (preset A' / B':
   A11; reply A / B: lane W), as A/AFf0cf.v was.
   rule 24: no function proved (kind: relational transport of the allocator relation over Enqueue's hit arm). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(* The cgif image instances first, as DGif1.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a YB1w YFeq YFew YFex YFfu YFf2 YFfq YFfp YFgq YFh4 YFfl.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0qcf YG0scf YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstEnq YGcfInstEnqG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import YGcfInstF1Wpreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YFf2cf. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require EnqGbase CLenq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YFfqcf.
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* YFg4.v:27, copied (YFg4 is cgif's instance file). *)
Lemma same_io_wvb_cf : forall l p md, same_io md (with_vm_backing l p md). Proof. intros. repeat split; reflexivity. Qed.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section h.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (IOK : Z -> Prop) (Hp : list Z) (inst : Z).
Variables (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : chunk).
Hypothesis ENQ : enq_pre_cf B (ARX_cf B IOK Hp) inst ly X W regs mem md k.
Hypothesis HNB : need_new_batch (st_qthread X) = true.
Variable l : list Z.
Hypothesis Hl : pc_chunks (cache X kBatchClass) = l.
Hypothesis Hlne : l <> [].
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation H0 := (w_H W).
Local Notation rd0 := (aview tfibsegs (w_H W) mem).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation q := (st_qthread X).
Local Notation u := (sptr_addr B ly (ck_user k)).
Local Notation nn := (ck_n k).
Definition cnt : Z := Z.of_nat (length l).
Definition coff : Z := last l 0.
Lemma HAR : ARcf tfibsegs B ly X Hp W mem md. Proof. destruct ENQ as ((_ & H & _) & _). exact H. Qed.
Lemma M : ARmcf B ly X Hp rd0. Proof. exact (proj1 HAR). Qed.
Let WF : Wf_cf (as_universe B) X := amc_wf B ly X Hp rd0 M.
Let LO : layout_ok ly := amc_layout B ly X Hp rd0 M.
Lemma Hk : In k (st_chunks X). Proof. destruct ENQ as (_ & _ & _ & Hk & _). exact Hk. Qed.
Lemma Hst : ck_state k = CQuarantined. Proof. destruct ENQ as (_ & _ & _ & _ & Hst & _). exact Hst. Qed.
Lemma Hnq : ~ In (ck_beg k) (map ck_beg (q_items X)). Proof. destruct ENQ as (_ & _ & _ & _ & _ & Hnq & _). exact Hnq. Qed.
Lemma Hci : st_cache_inited X = true.
Proof.
pose proof (wfc_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as C. unfold wf_class_cf in C.
pose proof (wrc_cache _ _ _ _ _ _ C) as WC.
destruct (st_cache_inited X) eqn:E; [reflexivity|]. exfalso. apply Hlne. rewrite <- Hl, WC. reflexivity.
Qed.
Lemma cnt_pos : 1 <= cnt.
Proof. unfold cnt. destruct l as [|x t]; [congruence|]. cbn [length]. lia. Qed.
Local Notation QSZv := (YFgq.QSZv q).
Local Notation QFv := (YFgq.QFv ly q).
Local Notation QLv := (YFgq.QLv ly q).
Local Notation QBv := (YFgq.QBv q).
Local Notation CPv := (YFgq.CPv coff).
Local Notation NBv := (YFgq.NBv ly coff).
Local Notation CSLv := (YFgq.CSLv ly cnt).
Lemma HSP : ly_stk_lo ly + QSTACK <= sp0 <= ly_stk_hi ly.
Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _). unfold spZ, CLenq.QSTACK_G, QSTACK in *. unfold sp0. lia. Qed.
Lemma IMG : img_cover ly.
Proof. pose proof HAR as (_ & LED & _). exact (IMG_COVER_preset ly X md LED). Qed.
Lemma HTSD : ly_tsd ly = TFIB_TSD. Proof. rewrite (amc_tsd B ly X Hp rd0 M). exact (ts_tsd _ TB). Qed.
Lemma HI : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\
ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
ly_prim ly <= NBv /\ NBv + kBatchBytes <= SB + kSpaceSize /\
(forall lb initr, rev (qc_list q) = lb :: initr -> ly_prim ly <= QLv /\ QLv + kBatchBytes <= SB + kSpaceSize).
Proof.
pose proof (YFf2cf.HIGH B ly X rd0 Hp M Hci l Hl Hlne sp0 HSP IMG) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
unfold YFgq.NBv, coff. splits; try lia; try exact A3. exact A11.
Qed.
(* ---------------------------------------------------------------------------------------------------------------- *)
(* The walk's free hypotheses at cf (a prior worker, 2026-10-30; for a Theorem Labs lane's Enqueue hit arm): B3's YFgq.free_hyps
   (YFgq.v:114-139) from enq_pre_cf, as YFg5.v:247-405 proves them at cgif's enq_pre.  The memory readers and the
   size / list facts are YFfqcf.v's (its section g at sp0 / HSP / IMG / Hk / HQL / HNB, its section h at l); the
   region, pair, fact and seed checks are YFg5.v's scripts with these changes only: the call premise is enq_pre_cf (its
   stack window CLenq.QSTACK_G = QSTACK = 1088), fh_Hnn reads the call's guard ck_n k <= kQuarantineMax
   (enq_pre_cf's last conjunct) beside YFfqcf.u_facts_cf's 1 <= nn, and fh_hit's offset bound is kFreeArrayOffset
   (YFfqcf.hit_facts_cf, from YFf2cf.nb_geom).
   rule 24: no function proved (kind: the walk record's premises at the cf instance). *)
Lemma HQL : qloose X.
Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQ & _). exact HQ. Qed.
Lemma HNM : nn <= kQuarantineMax.
Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HN & _). exact HN. Qed.
Local Notation jst := (YFfqcf.jst ly W mem).
Local Notation E0 := (YFgq.E0 ly regs u nn q cnt coff jst).
Lemma qE2 : ew E0 2 = getr regs 2. Proof. exact (YFgq.E2 ly regs u nn q cnt coff jst). Qed.
Lemma qEqT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma qEqSB : ew E0 33 = w64 SB. Proof. reflexivity. Qed.
Lemma qEqU : ew E0 34 = w64 u. Proof. reflexivity. Qed.
Lemma qEqN : ew E0 35 = w64 nn. Proof. reflexivity. Qed.
Lemma qEqQSZ : ew E0 36 = w64 QSZv. Proof. reflexivity. Qed.
Lemma qEqQF : ew E0 37 = w64 QFv. Proof. reflexivity. Qed.
Lemma qEqQL : ew E0 38 = w64 QLv. Proof. reflexivity. Qed.
Lemma qEqQB : ew E0 39 = w64 QBv. Proof. reflexivity. Qed.
Lemma qEqCNT : ew E0 40 = w64 cnt. Proof. reflexivity. Qed.
Lemma qEqCP : ew E0 41 = w64 CPv. Proof. reflexivity. Qed.
Lemma qEqJST : ew E0 42 = w64 jst. Proof. reflexivity. Qed.
Lemma qEqNB : ew E0 43 = w64 NBv. Proof. reflexivity. Qed.
Lemma qEqCSL : ew E0 44 = w64 CSLv. Proof. reflexivity. Qed.
(* YFfqcf's readers at this Section's state *)
Lemma q_root_vals : val_mem tfibsegs m0 (T + t_qc) 8 QSZv /\ val_mem tfibsegs m0 (T + t_qc + 8) 8 QFv /\
  val_mem tfibsegs m0 (T + t_qc + 16) 8 QLv /\ val_mem tfibsegs m0 (T + t_qc + 24) 8 QBv.
Proof. exact (YFfqcf.root_vals B ly X W mem Hp M). Qed.
Lemma q_jst_val : val_mem tfibsegs m0 (T + t_cache_stats + 16) 8 jst /\ 0 <= jst < 2 ^ 64.
Proof. exact (YFfqcf.jst_val B ly X W mem sp0 Hp M HSP). Qed.
Lemma q_u_zone : zone3 (u - 16) (nn + 16).
Proof. exact (YFfqcf.u_zone B ly X W mem k Hp M IMG Hk). Qed.
Lemma q_u_facts : 4096 + 16 <= u /\ u + nn <= ASAN_CEIL /\ u mod 16 = 0 /\ 1 <= nn.
Proof. exact (YFfqcf.u_facts_cf B ly X W mem k Hp M Hk). Qed.
Lemma q_q_facts : 0 <= QBv /\ QBv + nn + kBatchBytes <= 2 ^ 48 /\ QSZv < 2 ^ 40 /\ 0 <= QFv < ASAN_CEIL.
Proof. exact (YFfqcf.q_facts_cf B ly X W mem sp0 k Hp M HSP Hk HQL). Qed.
Lemma q_last_facts : forall lb initr, rev (qc_list q) = lb :: initr ->
  ly_prim ly <= QLv /\ QLv + kBatchBytes <= SB + kSpaceSize /\ QLv mod 8192 = 0 /\
  val_mem tfibsegs m0 (QLv + 16) 8 kBatchSlots /\ (forall a, QLv <= a < QLv + 8 -> apresent H0 mem a) /\
  In lb (all_batches X) /\ QLv = SB + b_self lb.
Proof. exact (YFfqcf.last_facts B ly X W mem sp0 Hp M HSP HNB). Qed.
Lemma q_cache_vals : val_mem tfibsegs m0 (T + t_cache + 1920) 4 cnt /\ val_mem tfibsegs m0 (T + t_cache + 1928) 8 8192 /\
  val_mem tfibsegs m0 CSLv 4 CPv /\ 0 <= cnt <= 16 /\ 1 <= cnt.
Proof. exact (YFfqcf.cache_vals B ly X W mem Hp M l Hl Hlne). Qed.
Lemma q_hit_facts : 0 <= coff /\ coff + kBatchBytes <= kFreeArrayOffset /\ coff mod 16 = 0 /\ ly_prim ly <= NBv /\
  NBv + kBatchBytes <= SB + kSpaceSize /\ NBv mod 8192 = 0 /\
  (forall a, NBv <= a < NBv + 32 -> apresent H0 mem a) /\
  (forall lb initr, rev (qc_list q) = lb :: initr -> NBv + kBatchBytes <= QLv \/ QLv + kBatchBytes <= NBv).
Proof. exact (YFfqcf.hit_facts_cf B ly X W mem sp0 Hp M HSP IMG HNB l Hl Hlne). Qed.
Lemma q_cell_sym : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. exact (YFfqcf.cell_sym B TB ly X W mem Hp M). Qed.
Lemma q_cell_lit : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfibsegs m0 a w x.
Proof. exact (YFfqcf.cell_lit B TB ly X W mem Hp M). Qed.
Lemma q_chunk_lit : forall a (w : BinNums.N) x, val_mem tfibsegs m0 a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  YP09.chunk_ok tfibsegs E0 m0 0 (YP09.mkChunk a (CVal w (SLit x))).
Proof. exact (YFfqcf.chunk_lit W mem E0). Qed.
Lemma q_chunk_atom : forall base a (w : BinNums.N) k0 d x, ew E0 k0 = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
  val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SOff k0 d))).
Proof. exact (YFfqcf.chunk_atom W mem E0). Qed.
Lemma q_val_mem_writable : forall a (w : nat) v o, val_mem tfibsegs m0 a w v -> a <= o < a + Z.of_nat w -> off_img o -> writable_at tfibsegs m0 o.
Proof. exact (YFfqcf.val_mem_writable W mem). Qed.
Lemma q_stack_pres : forall a, sp0 - QSTACK <= a < sp0 -> apresent (w_H W) mem a.
Proof.
destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _). unfold spZ in HPRES. fold sp0 in HPRES.
intros a Ha. apply HPRES. unfold CLenq.QSTACK_G, QSTACK in *. lia.
Qed.
Lemma q_sp_al : sp0 mod 16 = 0.
Proof. destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & Hal & _). unfold spZ in Hal. exact Hal. Qed.
Ltac q_offw := first [ lia | apply off_img_high; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END, kHighMemBeg in *; ceil; unfold ASAN_CEIL in *; lia
| apply (zone3_off_img _ _ _ (proj1 (proj2 (proj2 HI)))); unfold kThreadObjSize, t_qc, t_cache, t_cache_stats, YFgq.CSLv in *; lia ].
Local Ltac q_reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac q_r8 := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Local Ltac q_r4 := change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia.
Local Ltac q_lit_region :=
q_reg_intro; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
repeat (apply Forall_cons; [apply q_chunk_lit; [apply q_cell_lit; vm_compute; reflexivity | cbn; lia | cbn; lia] |]); apply Forall_nil.
Lemma REG0_ok_cf : Forall (region_ok tfibsegs E0 m0) YFgq.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hN1 & hN2 & _). pose proof HSP as [S1 S2].
pose proof q_root_vals as (V1 & V2 & V3 & V4). pose proof q_cache_vals as (C1 & C2 & C3 & C4 & C5). pose proof q_jst_val as [J1 J1R].
pose proof q_q_facts as (Qa & Qb & Qc & Qd). assert (Qc0 : 0 <= QSZv) by (unfold YFgq.QSZv; clear; lia).
assert (QLR : 0 <= QLv < ASAN_CEIL).
{ unfold YFgq.QLv. destruct (rev (qc_list q)) as [|lb initr] eqn:Hrev; [ceil; unfold ASAN_CEIL; lia|].
pose proof (q_last_facts lb initr Hrev) as (L1 & L2 & _). unfold YFgq.QLv in L1, L2. rewrite Hrev in L1, L2. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kBatchBytes, kSpaceSize, kHighMemBeg, ASAN_CEIL, kPrimResvSize in hP1, hP2, hSP1, hSP2, L1, L2. ceil; unfold ASAN_CEIL. lia. }
pose proof q_u_facts as (Ua & Ub & Uc & Ud).
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, QSTACK in hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, hN1, hN2, S1, S2, QLR, Qb, Qd, Ua, Ub.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof q_stack_pres as HPRES.
unfold YFgq.REG0, YFgq.R_ROOT, YFgq.R_CNT, YFgq.R_JST, flit4, flit8, fatom8.
apply Forall_cons.
{   apply (region_ok_stack tfibsegs E0 m0 2 sp0 (- 64)); [rewrite qE2; reflexivity | lia | lia |].
intros a Ha. apply apresent_writable; [unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END in *; lia | apply HPRES; clear -Ha; unfold QSTACK in *; lia]. }
apply Forall_cons. {   q_reg_intro. rewrite qEqT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_qc in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 88); [apply (q_val_mem_writable _ _ _ _ V1) | destruct (Z_lt_le_dec o 96); [apply (q_val_mem_writable _ _ _ _ V2) | destruct (Z_lt_le_dec o 104); [apply (q_val_mem_writable _ _ _ _ V3) | apply (q_val_mem_writable _ _ _ _ V4)]]];
cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; q_offw. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (q_chunk_atom _ _ 8 36%nat 0 QSZv); [rewrite Z.sub_0_r; reflexivity | lia | exact V1 | q_r8 | cbn; lia].
- apply (q_chunk_atom _ _ 8 37%nat 0 QFv); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V2 | lia] | q_r8 | cbn; lia].
- apply (q_chunk_atom _ _ 8 38%nat 0 QLv); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V3 | lia] | q_r8 | cbn; lia].
- apply (q_chunk_atom _ _ 8 39%nat 0 QBv); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V4 | lia] | q_r8 | cbn; lia]. }
apply Forall_cons. {   q_reg_intro. rewrite qEqT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_cache in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (q_val_mem_writable _ _ _ _ C1); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; q_offw. }
apply Forall_cons; [|apply Forall_nil]. apply (q_chunk_atom _ _ 4 40%nat 0 cnt); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact C1 | lia] | q_r4 | cbn; lia]. }
apply Forall_cons. {   q_reg_intro. rewrite qEqT. unfold w64. rewrite unsigned_lit_small by lia. unfold t_cache_stats in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (q_val_mem_writable _ _ _ _ J1); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, TFIB_IMG_END; q_offw. }
apply Forall_cons; [|apply Forall_nil]. apply (q_chunk_atom _ _ 8 42%nat 0 jst); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact J1 | lia] | q_r8 | cbn; lia]. }
apply Forall_cons. {   q_reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (q_chunk_atom 0 _ 8 33%nat 0 SB); [rewrite Z.sub_0_r; reflexivity | lia | | q_r8 | cbn; lia].
rewrite Z.add_0_l. replace YImgCellsB.B_INSTANCE_OFF_20_CELL with (aeval B ly (AInst o_space)) by (cbn; rewrite (ts_inst B TB); reflexivity).
replace SB with (aeval B ly (ASp 0)) by (cbn; lia). apply q_cell_sym. vm_compute. reflexivity. }
do 3 (apply Forall_cons; [q_lit_region|]). apply Forall_nil.
Qed.
Lemma PAIRS_ok_cf : pairwise_disjoint E0 YFgq.REG0.
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _). pose proof HSP as [S1 S2].
pose proof (YFf2cf.SX B ly X rd0 Hp M l 2 8 _ _ eq_refl eq_refl ltac:(lia)) as DTS. unfold zdisjoint in DTS. cbn [fst snd] in DTS.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
apply pairwise_disjoint_of_extents. unfold YFgq.REG0, YFgq.R_ROOT, YFgq.R_CNT, YFgq.R_JST, flit4, flit8, fatom8, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite qE2, qEqT. unfold w64. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, QSTACK in *.
fold sp0. rewrite !unsigned_lit_small by lia.
unfold t_qc, t_cache, t_cache_stats. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg in hT1.
repeat split; first [clear hT1; lia | clear - hT1 CR0; lia].
Qed.
Lemma FACTS_ok_cf : atoms_ok E0 (f_atoms YFgq.FFQ).
Proof.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hN1 & hN2 & _). pose proof HSP as [S1 S2].
pose proof q_sp_al as Hal.
pose proof q_u_facts as (U1 & U2 & U3 & U4). pose proof HNM as U5. pose proof q_q_facts as (Qa & Qb & Qc & Qd).
pose proof q_cache_vals as (_ & _ & _ & C4 & C5). pose proof q_jst_val as [_ JR].
pose proof q_hit_facts as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof (lo_space_al ly LO) as SAL. pose proof (lo_T_al ly LO) as TAL. unfold page_aligned in TAL.
assert (QLR : 0 <= QLv < ASAN_CEIL /\ QLv mod 8192 = 0).
{ unfold YFgq.QLv. destruct (rev (qc_list q)) as [|lb initr] eqn:Hrev; [ceil; unfold ASAN_CEIL; split; [lia | reflexivity]|].
pose proof (q_last_facts lb initr Hrev) as (L1 & L2 & L3 & _). unfold YFgq.QLv in L1, L2, L3. rewrite Hrev in L1, L2, L3. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kBatchBytes, kSpaceSize, kHighMemBeg, ASAN_CEIL, kPrimResvSize in hP1, hP2, hSP1, hSP2, L1, L2. ceil; unfold ASAN_CEIL. split; [lia | exact L3]. }
destruct QLR as [QLR QLA].
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, QSTACK in hP1, hP2, hT1, hT2, hS1, hS2, hSP1, hSP2, hN1, hN2, S1, S2, U1, U2, QLR, F2, F4, F5, Qb, Qd.
assert (E2' : ew E0 2 = w64 sp0) by (rewrite qE2; unfold sp0, w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (AF : forall k0 Xv lo hi al, ew E0 k0 = w64 Xv -> 0 <= Xv < 2 ^ 64 -> lo <= Xv <= hi -> Xv mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k0 (mkAF lo hi al)).
{ clear. intros k0 Xv lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
cbn [YFgq.FFQ f_atoms atoms_ok]. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, QSTACK.
split. { apply (AF 2%nat sp0); [exact E2'| | | |]. all: clear - CR0 Usp S1 S2 hS1 hS2 Hal; first [lia | change (2 ^ 4) with 16; exact Hal]. }
split. { apply (AF 32%nat T); [exact qEqT| | | |]. all: clear - CR0 hT1 hT2 TAL; first [lia | exact TAL]. }
split. { apply (AF 33%nat SB); [exact qEqSB| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 SAL; first [lia | exact SAL]. }
split. { apply (AF 34%nat u); [exact qEqU| | | |]. all: clear - CR0 U1 U2 U3 U4; first [lia | change (2 ^ 4) with 16; exact U3]. }
split. { apply (AF 35%nat nn); [exact qEqN| | | |]. all: clear - CR0 U4 U5; unfold kQuarantineMax in U5; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 36%nat QSZv); [exact qEqQSZ| | | |]. all: clear - CR0 Qc; unfold YFgq.QSZv in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 37%nat QFv); [exact qEqQF| | | |]. all: clear - CR0 Qd; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 38%nat QLv); [exact qEqQL| | | |]. all: clear - CR0 QLR QLA; first [lia | change (2 ^ 13) with 8192; exact QLA]. }
split. { apply (AF 39%nat QBv); [exact qEqQB| | | |]. all: clear - CR0 Qa Qb U4; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 40%nat cnt); [exact qEqCNT| | | |]. all: clear - CR0 C4; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 41%nat CPv); [exact qEqCP| | | |]. all: clear - CR0 F1 F2 F3; unfold YFgq.CPv, kFreeArrayOffset in *;
  first [pose proof (Z.div_pos coff 16); pose proof (Z.div_lt_upper_bound coff 16 (2 ^ 28)); lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 42%nat jst); [exact qEqJST| | | |]. all: clear - CR0 JR; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 43%nat NBv); [exact qEqNB| | | |]. all: clear - CR0 F4 F5 F6 hP1 hP2 hSP1 hSP2; first [lia | change (2 ^ 13) with 8192; exact F6]. }
split; [|exact I]. { apply (AF 44%nat CSLv); [exact qEqCSL| | | |]. all: clear - CR0 C4 C5 hT1 hT2 TAL; unfold YFgq.CSLv, t_cache in *;
first [lia | change (2 ^ 2) with 4; apply Z.mod_divide in TAL as [c Hc]; [|lia]; rewrite Hc; apply Z.mod_divide; [lia|]; exists (1024 * c + 536 + (cnt - 1)); lia]. }
Qed.
Lemma SEED_ok_cf : st_ok tfibsegs E0 YFgq.SS0 (restrict (w_H W) (mkst regs (w64 0x36b60) mem (seg_rom tfibsegs))).
Proof.
destruct ENQ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htp & Ha0 & Ha1 & Ha3 & Ha4 & _). rewrite (ts_tp _ TB) in Htp.
pose proof q_u_facts as (U1 & U2 & U3 & U4). pose proof HI as (hP1 & hP2 & hT1 & hT2 & _). ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize in hT1, hT2, U1, U2.
rewrite restrict_mkst_fx. unfold YFgq.SS0, YFgq.SR0, sr_set. cbn [bv_eqb]. unfold YFgq.E0, w64. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros XX; discriminate | cbn [sv_denot]; exact Htp] | intros XX; discriminate |] | intros XX; discriminate |] | intros XX; discriminate |] | intros XX; discriminate |].
+ cbn [sv_denot]. fold (YFgq.E0 ly regs u nn q cnt coff jst). rewrite qEqT, Ha0. unfold w64. rewrite Zbv_add_unsigned. reflexivity.
+ cbn [sv_denot]. fold (YFgq.E0 ly regs u nn q cnt coff jst). rewrite qEqT, Ha1. unfold w64. rewrite Zbv_add_unsigned. reflexivity.
+ cbn [sv_denot]. fold (YFgq.E0 ly regs u nn q cnt coff jst). rewrite qEqU, Ha3. unfold w64, kChunkHeaderSize. rewrite Zbv_add_unsigned. reflexivity.
+ cbn [sv_denot]. fold (YFgq.E0 ly regs u nn q cnt coff jst). rewrite qEqN, Ha4. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. exact REG0_ok_cf.
- exact PAIRS_ok_cf.
- split; [exact FACTS_ok_cf | split; exact I].
Qed.
(* The hit arm's walk record at cf. *)
Theorem FH_ok_cf : YFgq.free_hyps W ly regs mem u nn q cnt coff jst.
Proof.
pose proof ENQ as ENQ'. destruct ENQ' as (_ & _ & _ & _ & _ & _ & Hra & Hra4 & _ & _ & _ & _ & _ & Htp & _).
unfold raZ in Hra4.
pose proof q_u_facts as (U1 & U2 & U3 & U4). pose proof q_q_facts as QF. pose proof q_cache_vals as (C1 & C2 & C3 & C4 & C5).
pose proof q_jst_val as [_ JR].
pose proof q_hit_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
constructor.
- exact LO.
- rewrite (ts_tp _ TB) in Htp. exact Htp.
- exact Hra.
- exact Hra4.
- exact HSP.
- exact q_sp_al.
- exact q_stack_pres.
- split; [exact q_u_zone | exact U3].
- exact IMG.
- split; [exact U4 | exact HNM].
- exact QF.
- exact HNB.
- intros lb initr Hrev. pose proof (q_last_facts lb initr Hrev) as (L1 & L2 & L3 & L4 & L5 & _). splits; assumption.
- exact C4.
- intros _. splits; assumption.
- exact JR.
- exact SEED_ok_cf.
Qed.
Local Notation WINq := (YFgq.WIN ly regs q cnt coff).
Local Notation S' := (YFf2cf.S' X k l).
Lemma GEO_cf :
(ly_prim ly + kPrimResvSize <= T \/ T + kThreadObjSize <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_C ly \/ ly_C ly + 256 <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_D ly \/ ly_D ly + 4096 <= ly_prim ly) /\
(ly_prim ly + kPrimResvSize <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_prim ly) /\
(T + kThreadObjSize <= ly_C ly \/ ly_C ly + 256 <= T) /\
(T + kThreadObjSize <= ly_D ly \/ ly_D ly + 4096 <= T) /\
(T + kThreadObjSize <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= T) /\
(ly_C ly + 256 <= ly_D ly \/ ly_D ly + 4096 <= ly_C ly) /\
(ly_C ly + 256 <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_C ly) /\
(ly_D ly + 4096 <= ly_stk_lo ly \/ ly_stk_lo ly + (ly_stk_hi ly - ly_stk_lo ly) <= ly_D ly) /\
(4096 <= ly_C ly /\ ly_C ly + 256 <= ASAN_CEIL) /\ (4096 <= ly_D ly /\ ly_D ly + 4096 <= ASAN_CEIL).
Proof.
pose proof (Forall_nth_f _ _ 6 _ (lo_app ly LO) eq_refl) as IC. pose proof (Forall_nth_f _ _ 7 _ (lo_app ly LO) eq_refl) as ID.
cbn beta in IC, ID. cbn [fst snd] in IC, ID. unfold in_app in IC, ID.
assert (C12 : 4096 <= ly_C ly /\ ly_C ly + 256 <= ASAN_CEIL) by (clear - IC; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia).
assert (D12 : 4096 <= ly_D ly /\ ly_D ly + 4096 <= ASAN_CEIL) by (clear - ID; ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia). clear IC ID.
pose proof (lo_disj ly LO) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _ & DT & _ & _ & _ & DC & DD & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PC DP]. apply Forall_cons_iff in DP as [PD DP]. apply Forall_cons_iff in DP as [PSTK _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TC DT].
apply Forall_cons_iff in DT as [TD DT]. apply Forall_cons_iff in DT as [TSTK _].
apply Forall_cons_iff in DC as [CD DC]. apply Forall_cons_iff in DC as [CSTK _]. apply Forall_cons_iff in DD as [DSTK _].
destruct C12 as [C1 C2]. destruct D12 as [D1 D2].
clear - PT PC PD PSTK TC TD TSTK CD CSTK DSTK C1 C2 D1 D2.
unfold zdisjoint in *. cbn [fst snd] in *. repeat match goal with G : _ /\ _ |- _ => destruct G as [? ?] end. splits; assumption.
Qed.
Lemma WIN_zone : forall a, WINq a -> (sp0 - 64 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize).
Proof.
intros a Hw. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & hSP1 & hSP2 & hN1 & hN2 & HL).
unfold YFgq.WIN, YFgq.WINT, YFgq.WINA in Hw. fold sp0 in Hw.
destruct Hw as [Hw|[Hw|[[_ Hw]|[Hq Hw]]]].
- left. exact Hw.
- right; left. clear - Hw. unfold t_qc, t_cache, t_cache_stats, kThreadObjSize in *. lia.
- right; right. clear - Hw hN1 hN2 hSP2. unfold kBatchBytes, kSpaceSize, kPrimResvSize in *. lia.
- right; right. destruct (rev (qc_list q)) as [|lb initr] eqn:Hrev.
+ exfalso. apply Hq. rewrite <- (rev_involutive (qc_list q)), Hrev. reflexivity.
+ pose proof (HL lb initr eq_refl) as [L1 L2]. unfold YFgq.QLv in Hw, L1, L2. rewrite Hrev in Hw, L1, L2.
clear - Hw L1 L2 hSP2. unfold kBatchBytes, kSpaceSize, kPrimResvSize in *. lia.
Qed.
Lemma WIN_dec : forall a, WINq a \/ ~ WINq a.
Proof.
intros a. assert (EM : forall lo hi, (lo <= a < hi) \/ ~ (lo <= a < hi)) by (intros; lia).
pose proof cnt_pos as C5.
assert (LQ : qc_list q = [] \/ qc_list q <> []) by (destruct (qc_list q); [left; reflexivity | right; discriminate]).
unfold YFgq.WIN, YFgq.WINT, YFgq.WINA. fold sp0.
destruct (EM (sp0 - 64) sp0) as [C|C0]; [left; left; exact C|].
destruct (EM (T + t_qc) (T + t_qc + 32)) as [C|C1]; [left; right; left; left; exact C|].
destruct (EM (T + t_cache + 1920) (T + t_cache + 1924)) as [C|C2]; [left; right; left; right; left; exact C|].
destruct (EM (T + t_cache_stats + 16) (T + t_cache_stats + 24)) as [C|C3]; [left; right; left; right; right; exact C|].
destruct (EM NBv (NBv + 32)) as [C|C4]; [left; right; right; left; split; [exact C5 | exact C]|].
destruct LQ as [LQ|LQ].
- right. intros [X0|[[X1|[X2|X3]]|[[_ X4]|[X5 _]]]]; [exact (C0 X0) | exact (C1 X1) | exact (C2 X2) | exact (C3 X3) | exact (C4 X4) | exact (X5 LQ)].
- destruct (EM QLv (QLv + 8)) as [C|C6]; [left; right; right; right; split; [exact LQ | exact C]|].
right. intros [X0|[[X1|[X2|X3]]|[[_ X4]|[_ X5]]]]; [exact (C0 X0) | exact (C1 X1) | exact (C2 X2) | exact (C3 X3) | exact (C4 X4) | exact (C6 X5)].
Qed.
Definition low_okq (a w : Z) : bool :=
((TFIB_IMG_LO <=? a) && (a + w <=? TFIB_IMG_END)) || ((SHADOW_OFF + TFIB_IMG_LO / 8 <=? a) && (a + w <=? SHADOW_OFF + TFIB_IMG_END / 8)).
Definition const_loc_okq (c : acell) : bool :=
let w := Z.max 1 (Z.of_nat (c_w c)) in
match c_at c with
| ANum a => low_okq a w
| AT o => (0 <=? o) && (o + w <=? 80)
| AC o => (0 <=? o) && (o + w <=? 256)
| AD o => (0 <=? o) && (o + w <=? 4096)
| ATsd o => low_okq (TFIB_TSD + o) w
| ATp o => low_okq (TFIB_TP + o) w
| AInst o => low_okq (TFIB_INST + o) w
| _ => false
end.
Lemma Tfib_const_locq : forallb const_loc_okq (Tfib_const ly) = true.
Proof. clear. vm_compute. reflexivity. Qed.
Lemma CONST_OUT : Forall (fun c => forall i, 0 <= i < Z.max 1 (Z.of_nat (c_w c)) -> ~ WINq (aeval B ly (c_at c) + i) /\ 0 <= aeval B ly (c_at c) + i < 2 ^ 64) (as_const B ly).
Proof.
rewrite (ts_const _ TB). apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) Tfib_const_locq c Hc) as K. unfold const_loc_okq in K.
pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _). pose proof HSP as [S1 S2].
pose proof GEO_cf as (G_PT & G_PC & G_PD & G_PS & G_TC & G_TD & G_TS & G_CD & G_CS & G_DS & [C1 C2] & [D1 D2]).
assert (ZN : forall a, ~ ((sp0 - 64 <= a < sp0) \/ (T + 80 <= a < T + kThreadObjSize) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize)) -> ~ WINq a).
{ intros a Hn Hw. exact (Hn (WIN_zone a Hw)). }
assert (LOW : forall a, low_okq a (Z.max 1 (Z.of_nat (c_w c))) = true -> ~ WINq (a + i) /\ 0 <= a + i < 2 ^ 64).
{ intros a L. unfold low_okq in L.
split; [apply ZN|]; clear - L Hi hP1 hT1 hS1 S1; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, QSTACK, kThreadObjSize in *;
change (65536 / 8) with 8192 in *; change (6295552 / 8) with 786944 in *; lia. }
destruct (c_at c); try discriminate K; cbn [aeval].
- apply LOW, K.
- split; [apply ZN|]; clear - K Hi hT1 hT2 S1 S2 G_PT G_TS; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *; lia.
- split; [apply ZN|]; clear - K Hi C1 C2 S1 S2 G_PC G_TC G_CS; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *; lia.
- rewrite HTSD. apply LOW, K.
- rewrite (ts_inst _ TB). apply LOW, K.
- rewrite (ts_tp _ TB). apply LOW, K.
- split; [apply ZN|]; clear - K Hi D1 D2 S1 S2 G_PD G_TD G_DS; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *; lia.
Qed.
Lemma val_mem_aview : forall H m a (w : nat) v kk, val_mem tfibsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfibsegs H m (a + Z.of_nat kk) = Some (YG0f.le_byte v w kk).
Proof.
clear. intros H m a w v kk Hv Hk. unfold aview. rewrite (Hv kk Hk). cbn [option_map]. change (YG0f.le_byte v w kk) with (YO0f.le_byte v w kk). f_equal. apply unsigned_lit_small8.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
(* YFg5.FINQH at the cf relation: the hit arm's walk post gives the call post the cf instance's ih_post states. *)
Lemma FINQH_cf : forall W' c', YFh4.at_RETQ W ly regs mem md u nn q cnt coff W' c' ->
EnqGbase.enq_leaf_g0 tfibsegs B (ARX_cf B IOK Hp) (aowned B) inst ly X W regs mem md k (tt, S') W' c'.
Proof.
intros W' c' HR.
pose proof ENQ as ENQ'.
destruct ENQ' as ((Hinst & HAR' & XSM) & BR & TICK & Hk' & Hst' & Hnq' & Hra & Hra4 & Hal & Hlo & Hhi & HPRES & Hgp & Htp & Ha0 & Ha1 & Ha3 & Ha4 & HQL' & HNM & _).
destruct HAR' as (M' & LED & BUD & MW & HSH). unfold spZ in *. fold sp0 in Hal, Hlo, Hhi, HPRES.
destruct HR as (-> & regs' & mem' & mat & -> & CS & MEQ' & PRESW & VALS). cbv zeta in VALS.
destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & VL).
set (rd := aview tfibsegs (w_H W) mem) in *. set (rd' := aview tfibsegs (w_H W) mem').
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
pose proof HSP as HSP'. pose proof cnt_pos as C5.
assert (ENB : NBv = SB + (region_off kBatchClass + last l 0)) by (unfold YFgq.NBv, coff; lia).
assert (WD : forall a, WINq a -> YFf2cf.D ly X l sp0 a).
{ intros a Hw. unfold YFf2cf.D, YFf2cf.DT, YFf2cf.DN, YFf2cf.DL, YFf2cf.DS.
unfold YFgq.WIN, YFgq.WINT, YFgq.WINA in Hw. fold sp0 in Hw. rewrite ENB in Hw.
destruct Hw as [Hw|[Hw|[[_ Hw]|[Hq Hw]]]].
- do 3 right. clear - Hw. unfold QSTACK. lia.
- left. exact Hw.
- right; left. exact Hw.
- right; right; left. split; [exact Hq|]. unfold YFf2cf.QLv. unfold YFgq.QLv in Hw. exact Hw. }
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YFf2cf.D ly X l sp0 a -> rd' a = rd a).
{ intros a Ha ND. subst rd rd'. apply aview_same. apply (MEQ' (Z_to_bv 64 a)). rewrite unsigned_lit_small by exact Ha. intros X'. exact (ND (WD a X')). }
assert (VIS : forall a, rd a <> None -> rd' a <> None).
{ intros a Hv HN. subst rd rd'. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
destruct (w_H W x) eqn:Hx; [exact (Hv HN)|].
destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (mem' x); discriminate|].
destruct (mem' x) as [|] eqn:E'; [discriminate|]. clear HN.
destruct (mem x) as [b0|] eqn:E0; [clear Hv | exact (Hv eq_refl)].
set (a' := bv_unsigned x). assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
destruct (WIN_dec a') as [C|C].
- destruct (PRESW a' C) as [_ [bb Hb]]. unfold w64 in Hb. rewrite Ex in Hb. congruence.
- rewrite (MEQ' x C) in E'. congruence. }
assert (HSK : forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)).
{ intros a Hb Hx. assert (Ha : kLowShadowBeg <= a < kHighShadowEnd) by (clear - Hb; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; lia). clear Hb.
unfold w64 in *. set (x := Z_to_bv 64 a) in *.
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha; unfold kLowShadowBeg, kHighShadowEnd in Ha; lia).
assert (Ux : bv_unsigned x = a) by (subst x; apply unsigned_lit_small; exact Ha').
destruct (WIN_dec a) as [C|C].
- exfalso. destruct (PRESW a C) as [Hh _]. unfold w64 in Hh. fold x in Hh. rewrite Hx in Hh. discriminate.
- apply (MEQ' x). rewrite Ux. exact C. }
assert (VM : forall a a' (w : nat) v v', val_mem tfibsegs (mrestrict (w_H W) mem') a w v -> a = a' -> v = v' ->
forall i, (i < w)%nat -> rd' (a' + Z.of_nat i) = Some (YG0f.le_byte v' w i)).
{ intros a a' w v v' Hv <- <- i Hi. subst rd'. exact (val_mem_aview _ _ _ _ _ i Hv Hi). }
assert (NEW_qs : forall i, (i < 8)%nat -> rd' (T + t_qc + Z.of_nat i) = Some (YG0f.le_byte (Z.of_nat (length (qc_list q)) + 1) 8 i)).
{ apply (VM _ _ 8%nat _ _ V1); [reflexivity | unfold YFgq.QSZv; reflexivity]. }
assert (NEW_qf : forall i, (i < 8)%nat -> rd' (T + t_qc + 8 + Z.of_nat i) =
Some (YG0f.le_byte (match qc_list q with [] => SB + (region_off kBatchClass + last l 0) | b0 :: _ => SB + b_self b0 end) 8 i)).
{ apply (VM _ _ 8%nat _ _ V2); [reflexivity|]. unfold YFh4.QF', YFgq.QFv. rewrite ENB. destruct (qc_list q); reflexivity. }
assert (NEW_ql : forall i, (i < 8)%nat -> rd' (T + t_qc + 16 + Z.of_nat i) = Some (YG0f.le_byte (SB + (region_off kBatchClass + last l 0)) 8 i)).
{ apply (VM _ _ 8%nat _ _ V3); [reflexivity | exact ENB]. }
assert (NEW_qb : forall i, (i < 8)%nat -> rd' (T + t_qc + 24 + Z.of_nat i) = Some (YG0f.le_byte (qc_bytes q + nn + kBatchBytes) 8 i)).
{ apply (VM _ _ 8%nat _ _ V4); [reflexivity | unfold YFgq.QBv; reflexivity]. }
assert (NEW_cnt : forall i, (i < 4)%nat -> rd' (T + t_cache + 1920 + Z.of_nat i) = Some (YG0f.le_byte (Z.of_nat (length l) - 1) 4 i)).
{ apply (VM _ _ 4%nat _ _ V5); [reflexivity | unfold cnt; reflexivity]. }
assert (NEW_n0 : forall i, (i < 8)%nat -> rd' (SB + (region_off kBatchClass + last l 0) + Z.of_nat i) = Some (YG0f.le_byte 0 8 i)).
{ apply (VM _ _ 8%nat _ _ V6); [exact ENB | reflexivity]. }
assert (NEW_n8 : forall i, (i < 8)%nat -> rd' (SB + (region_off kBatchClass + last l 0) + 8 + Z.of_nat i) = Some (YG0f.le_byte (nn + kBatchBytes) 8 i)).
{ apply (VM _ _ 8%nat _ _ V7); [rewrite ENB; reflexivity | reflexivity]. }
assert (NEW_n16 : forall i, (i < 8)%nat -> rd' (SB + (region_off kBatchClass + last l 0) + 16 + Z.of_nat i) = Some (YG0f.le_byte 1 8 i)).
{ apply (VM _ _ 8%nat _ _ V8); [rewrite ENB; reflexivity | reflexivity]. }
assert (NEW_n24 : forall i, (i < 8)%nat -> rd' (SB + (region_off kBatchClass + last l 0) + 24 + Z.of_nat i) = Some (YG0f.le_byte (u - 16) 8 i)).
{ apply (VM _ _ 8%nat _ _ V9); [rewrite ENB; reflexivity | reflexivity]. }
assert (NEW_lnext : forall lb initr, rev (qc_list q) = lb :: initr ->
forall i, (i < 8)%nat -> rd' (SB + b_self lb + Z.of_nat i) = Some (YG0f.le_byte (SB + (region_off kBatchClass + last l 0)) 8 i)).
{ intros lb initr Hrev. apply (VM _ _ 8%nat _ _ (VL lb initr Hrev)); [| exact ENB]. unfold YFgq.QLv. rewrite Hrev. reflexivity. }
assert (CONST' : Forall (cell_holds B ly rd') (as_const B ly)).
{ apply Forall_forall. intros c Hc. eapply (cell_holds_agree B ly rd); [exact (proj1 (Forall_forall _ _) (amc_const B ly X Hp _ M') c Hc)|].
intros i Hi. subst rd rd'. destruct (proj1 (Forall_forall _ _) CONST_OUT c Hc i Hi) as [X1 X2]. apply aview_same.
apply (MEQ' (Z_to_bv 64 _)). rewrite unsigned_lit_small by exact X2. exact X1. }
pose proof (enq_hit_wf_cf B Hp (ARX_cf B IOK Hp) (ARX_cf_ARcf B IOK Hp) inst ly X W regs mem md k l ENQ HNB Hl Hlne) as HWS'.
pose proof (YFf2cf.enq_fin_ARmcf_x B TB ly X rd rd' Hp M' k Hk Hci l Hl Hlne sp0 HSP' IMG AG VIS
NEW_qs NEW_qf NEW_ql NEW_qb NEW_cnt NEW_n0 NEW_n8 NEW_n16 NEW_n24 NEW_lnext CONST' HWS') as (MF & _ & _).
exists regs', mem', (with_vm_backing (m_vm_lazy md) mat md), (Some (region_off kBatchClass + last l 0)). split.
{ unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split.
2:{ split; [reflexivity|]. split; [exact HNB|]. split; [reflexivity|]. split; reflexivity. }
split; [|split; [apply layout_le_refl | split; [apply wle_refl | split; [|split; [|split]]]]].
- split; [exact Hinst|]. split; [|exact XSM].
split; [exact MF | split; [|split; [|split]]].
+ eapply ALedger_same_cf; [exact (YFf2cf.ALedger_cf_S' ly X k l tfibsegs md LED) | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
+ destruct BUD as (BUD & PIN & CLS). split; [|split; [exact (YFf2cf.asecA_S' ly X k l _ PIN) | exact CLS]].
eapply Z.le_trans; [exact BUD|]. rewrite <- (YFf2cf.abudget_cf_S' X k l). apply Z.le_refl.
+ eapply amwf_same; [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW].
+ eapply (ahs_transfer_cf tfibsegs B ly X Hp _ (w_H W) mem mem' (al_img_env_cf tfibsegs ly X md LO LED) M' HSH VIS HSK).
* intros a _ C. exact C.
*   reflexivity.
*
intros g Hg Hga HF _. pose proof (shadow_addr_band_rw g Hga) as SBg. apply AG; [clear - SBg; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg; lia|].
pose proof HI as (hP1 & _ & hT1 & _ & hS1 & _ & _ & _ & hN1 & _ & hL).
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in SBg. unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kThreadObjSize in hP1, hT1, hS1.
unfold YFf2cf.D, YFf2cf.DT, YFf2cf.DN, YFf2cf.DL, YFf2cf.DS. change (st_qthread X) with q. intros [Y|[Y|[[Hq Y]|Y]]].
-- clear - Y SBg hT1. unfold t_qc, t_cache, t_cache_stats in Y. lia.
-- rewrite <- ENB in Y. clear - Y SBg hP1 hN1. lia.
-- destruct (rev (qc_list q)) as [|lb initr] eqn:Hrev; [exfalso; apply Hq; rewrite <- (rev_involutive (qc_list q)), Hrev; reflexivity|].
destruct (hL lb initr eq_refl) as [L1 _]. unfold YFgq.QLv in L1. unfold YFf2cf.QLv in Y. rewrite Hrev in L1, Y.
clear - Y SBg hP1 L1. lia.
-- clear - Y SBg hS1 HSP'. unfold QSTACK in *. lia.
- intros r Hr'. apply CS. unfold acallee_saved in Hr'.
assert (R : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
clear - R. unfold CALLEE_SAVED.
repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; subst r; cbn [In]; repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]).
- apply same_io_wvb_cf.
- intros a Ha NO NO' NS NE. apply AG; [exact Ha|]. intros HD.
destruct (YFf2cf.D_owned_cf B ly X rd Hp M' k Hci l Hl Hlne sp0 HSP' a (proj1 Ha) HD) as [O|O]; [exact (NO O) | apply NS; unfold ascratch, spZ; left; unfold CLenq.QSTACK_G; exact O].
- intros a Ha. unfold spZ in Ha. fold sp0 in Ha. unfold CLenq.QSTACK_G in Ha. destruct (Z_lt_le_dec a (sp0 - 64)) as [Hb|Hb].
+ apply (apresent_same (w_H W) mem); [|apply HPRES; unfold CLenq.QSTACK_G; lia]. apply MEQ'. pose proof HI as (hP1 & hP2 & hT1 & hT2 & hS1 & hS2 & _).
assert (Ha' : 0 <= a < 2 ^ 64) by (clear - Ha Usp HSP' hS1; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, QSTACK, kHighMemBeg in *; lia). rewrite unsigned_lit_small by exact Ha'.
intros Hw. pose proof (WIN_zone a Hw) as Z3. pose proof GEO_cf as (G_PT & _ & _ & G_PS & _ & _ & G_TS & _).
clear - Z3 Ha Hb G_PT G_PS G_TS HSP' hT1 hT2 hP1 hP2. ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kPrimResvSize, QSTACK in *. lia.
+ apply PRESW. unfold YFgq.WIN. left. fold sp0. lia.
Qed.
End h.
End f.
