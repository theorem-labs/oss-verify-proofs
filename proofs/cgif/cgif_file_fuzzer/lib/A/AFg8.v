(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j YP0n YK0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA05.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG06 YG03 YG0f YG0v YG0n YG0d YG0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0j YG0o YG0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AFeq AFew AFeu AFf3 AFf4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFfn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFgv.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac numconst_hi := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kPtrArrayResv, kLowMemEnd, kPage, t_stats, A_ALLOCATOR, TFIB_INST, SHADOW_OFF, kHighShadowBeg, kHighShadowEnd in *;
unfold AFf4.own, AFf4.qi, AFf4.lst, AFf4.MAP, AFf4.LEN, AFf4.idx, AFf4.nA, AFf4.lastr, AFf4.arr in *.
Definition X2 (X1 : astate) (r : nat) (i : nat) (sm : secmap) : astate :=
set_sec_arr (removelast (lupd (st_sec_arr X1) i (last (st_sec_arr X1) r)))
(set_secs (lupd (st_secs X1) r (mkSec (sm_len sm) (sm_size sm) false)) X1).
Lemma recycle_chunk_sec : forall k X r o sm i,
mem_chunk k (st_chunks X) = true -> ck_beg k = PSec r o ->
nth_error (st_secs X) r = Some sm -> index_of (st_sec_arr X) r 0%nat = Some i -> needs_remap (sm_len sm) = false ->
recycle_chunk k X = IAsk (KMunmapSec r (sm_len sm)) (AFf3.X1 X k) (fun _ => IRet (tt, X2 (AFf3.X1 X k) r i sm)).
Proof.
intros k X r o sm i Hm Hb Hsm Hi NR. unfold recycle_chunk, bind, get. cbn [ibind]. rewrite Hm. unfold mcheck, ret, put. cbn [ibind].
rewrite Hb. unfold sec_dealloc, bind, get. cbn [ibind st_secs st_sec_arr set_chunks AFf3.X1].
replace (st_secs (set_chunks (del_chunk (st_chunks X) (PSec r o)) X)) with (st_secs X) by (destruct X; reflexivity).
replace (st_sec_arr (set_chunks (del_chunk (st_chunks X) (PSec r o)) X)) with (st_sec_arr X) by (destruct X; reflexivity).
rewrite Hsm, Hi, NR. unfold ret, askz, modify. cbn [ibind]. unfold X2, AFf3.X1. rewrite Hb.
replace (st_sec_arr (set_chunks (del_chunk (st_chunks X) (PSec r o)) X)) with (st_sec_arr X) by (destruct X; reflexivity).
replace (st_secs (set_chunks (del_chunk (st_chunks X) (PSec r o)) X)) with (st_secs X) by (destruct X; reflexivity).
reflexivity.
Qed.
Lemma page_round_up_Z_aligned : forall n, 0 <= n -> n mod 4096 = 0 -> page_round_up_Z n = n.
Proof. intros n Hn Hm. unfold page_round_up_Z, page_size. apply Z.mod_divide in Hm as [q Hq]; [|lia]. subst n. rewrite <- (Z.mul_comm 4096 q).
replace (4096 * q + 4096 - 1) with (q * 4096 + 4095) by lia. rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia. Qed.
Section e.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (r : nat) (o : Z) (sm : secmap) (i : nat).
Hypothesis PRE : rcc_pre B ly X k cbp W regs mem md.
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Hypothesis Hidx : index_of (st_sec_arr X) r 0%nat = Some i.
Hypothesis SMALL : needs_remap (sm_len sm) = false.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Let sp0 : Z := bv_unsigned (getr regs 2).
Local Notation T := (ly_T ly).
Definition LEN : Z := sm_len sm.
Definition MAP : Z := ly_sec ly r.
Definition nA : Z := Z.of_nat (length (st_sec_arr X)).
Definition idx : Z := Z.of_nat i.
Definition qi : Z := ly_Q ly + 8 * idx.
Definition lst : Z := ly_sec ly (last (st_sec_arr X) r).
Definition own : bool := idx =? nA - 1.
Definition vra : Z := bv_unsigned (getr regs 1).
Definition vs0 : Z := bv_unsigned (getr regs 8).
Definition vs1 : Z := bv_unsigned (getr regs 9).
Definition vs2 : Z := bv_unsigned (getr regs 18).
Definition X1 : astate := AFf3.X1 X k.
Definition X2v : astate := X2 X1 r i sm.
Definition iv : Z * Z := (MAP, MAP + LEN).
Definition W2 : world tfibsegs := wrefund tfibsegs W iv.
Lemma M : AR tfibsegs B ly X W mem md. Proof. exact (proj1 PRE). Qed.
Lemma Hk : In k (st_chunks X). Proof. exact (proj1 (proj2 (proj2 PRE))). Qed.
Lemma IMG : img_cover ly.
Proof. exact (img_cover_of_ledger ly X md (proj1 (proj2 (proj1 PRE)))). Qed.
Lemma KFACTS : o = kPage /\ sm_live sm = true /\ LEN = sec_map_size (ck_req k) /\ 0 <= ck_req k < MALLOC_MAX /\ from_primary (ck_req k) = false /\
In (MAP, LEN) (sec_extents ly X).
Proof.
pose proof M as (AM & _). pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ (am_wf B ly X _ AM)) k Hk) as [Hn CK].
rewrite Hb in CK. destruct CK as (P1 & P2 & sm' & Q1 & Q2 & Q3 & Q4). rewrite Hsm in Q1. injection Q1 as <-.
unfold LEN. repeat split; try assumption; try lia.
unfold sec_extents. apply in_flat_map. exists k. split; [exact Hk|]. rewrite Hb. left. unfold MAP. rewrite Q4. reflexivity.
Qed.
Lemma LEN_facts : 8192 <= LEN < 2 ^ 29 /\ LEN mod 4096 = 0.
Proof.
pose proof KFACTS as (_ & _ & E & Hn & FP & _). rewrite E. unfold sec_map_size, needed_size. rewrite FP.
unfold from_primary in FP. apply Z.leb_gt in FP.
pose proof (round_up_ge (needed_primary (ck_req k) + rz_size (ck_req k)) kPage ltac:(unfold kPage; lia)) as [R1 R2].
pose proof (needed_primary_bounds (ck_req k) ltac:(lia)) as (N1 & N2 & N3). pose proof (rz_size_bounds (ck_req k)) as [RZ _].
unfold kMaxSize, kPage, MALLOC_MAX in *. split; [lia|].
rewrite Z.add_mod, R2, Z.mod_same by lia. reflexivity.
Qed.
Lemma MAP_facts : zone3 MAP LEN /\ MAP + LEN <= ASAN_CEIL /\ MAP mod 4096 = 0 /\
In (MAP, MAP + LEN) (w_A W) /\ In (w64 MAP, w64 LEN) (vm_maps (m_vmmaps md)) /\ amwf md.
Proof.
pose proof M as (AM & AL & AB & MW & _). pose proof KFACTS as (_ & _ & _ & _ & _ & IN).
pose proof (AFf4.ZSEC B ly X _ AM IMG _ IN) as (H1 & PA & H2). cbn [fst snd] in PA, H1, H2. unfold page_aligned in PA.
split; [exact H1|]. split; [exact H2|]. split; [exact PA|]. split; [exact (proj1 (proj2 AB _ IN))|]. split; [exact (al_sec _ _ _ _ AL _ IN) | exact MW].
Qed.
Lemma HULL_fact : In (shull (MAP, LEN)) (w_A W).
Proof. pose proof M as (_ & _ & AB & _). pose proof KFACTS as (_ & _ & _ & _ & _ & IN). exact (proj2 (proj2 AB _ IN)). Qed.
Definition WPRE (a : Z) : Prop :=
(sp0 - GDEPTH <= a < sp0) \/ (A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 684) \/ (T + t_stats + 40 <= a < T + t_stats + 56).
Definition LINKD (regsD : bvmap 5 word) (memD : word -> option byte) : Prop :=
getr regsD 2 = getr regs 2 /\ (forall r' : bv 5, In r' AFgv.SREGS -> getr regsD r' = getr regs r') /\
(forall x : word, ~ WPRE (bv_unsigned x) -> memD x = mem x) /\
(forall a, T + t_stats + 40 <= a < T + t_stats + 56 -> apresent (w_H W) memD a).
Definition POSTMUN (W' : world tfibsegs) (c' : config) : Prop :=
exists regsD memD, LINKD regsD memD /\ AFgv.at_MUN W ly regsD memD md MAP LEN idx nA qi lst vra vs0 vs1 vs2 own W' c'.
Hypothesis WALK : SRr tfibsegs W (cfg_at tfibsegs A_RChunk regs mem md) POSTMUN.
Lemma val_mem_aview : forall H m a (w : nat) v kk, val_mem tfibsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfibsegs H m (a + Z.of_nat kk) = Some (YG0f.le_byte v w kk).
Proof.
clear. intros H m a w v kk Hv Hk'. unfold aview. rewrite (Hv kk Hk'). cbn [option_map]. change (YG0f.le_byte v w kk) with (YO0f.le_byte v w kk). f_equal. apply unsigned_lit_small8.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma val_mem_vis : forall H m a (w : nat) v b, val_mem tfibsegs (mrestrict H m) a w v -> a <= b < a + Z.of_nat w -> aview tfibsegs H m b <> None.
Proof.
clear. intros H m a w v b Hv Hb. replace b with (a + Z.of_nat (Z.to_nat (b - a))) by lia. rewrite (val_mem_aview H m a w v _ Hv) by lia. discriminate.
Qed.
Lemma apresent_vis : forall H m a, 0 <= a < 2 ^ 64 -> apresent H m a -> aview tfibsegs H m a <> None.
Proof. clear. intros H m a Ha [Hh [b Hb]]. unfold aview, mbyte, mrestrict, w64 in *. rewrite Hh, Hb. discriminate. Qed.
Lemma aview_hidden_none : forall (W0 : world tfibsegs) m a, w_H W0 (Z_to_bv 64 a) = true -> aview tfibsegs (w_H W0) m a = None.
Proof.
clear. intros W0 m a Hh. unfold aview, mbyte, mrestrict. rewrite Hh. unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
rewrite (w_Hoff W0 _ Hh). reflexivity.
Qed.
Lemma same_io_wvb' : forall l p md0, same_io md0 (with_vm_backing l p md0). Proof. clear. intros. repeat split; reflexivity. Qed.
Lemma X2v_eq : X2v = AFf4.X2 X k r sm i.
Proof. clear. unfold X2v, X2, X1, AFf4.X2, AFf4.arr', AFf4.arr, AFf4.lastr, AFf3.X1. destruct X; reflexivity. Qed.
Definition FINAL (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
(forall r' : bv 5, In r' AFgv.SREGS -> getr regs' r' = getr regs r') /\
getr regs' 2 = getr regs 2 /\ getr regs' 8 = w64 vs0 /\ getr regs' 9 = w64 vs1 /\ getr regs' 18 = w64 vs2 /\
(forall x : word, ~ AFf4.D B ly X k r i sp0 (bv_unsigned x) -> mem' x = mem x) /\
(forall x : word, SHAv MAP <= bv_unsigned x < SHAv MAP + CNTv LEN -> mem' x = Some (Z_to_bv 8 0)) /\
(forall a, sp0 - KSTACK <= a < sp0 -> apresent (w_H W) mem' a) /\
(forall a, (T + t_stats + 40 <= a < T + t_stats + 56) \/ (T + t_stats + 88 <= a < T + t_stats + 104) -> apresent (w_H W) mem' a) /\
(forall a, qi <= a < qi + 8 -> apresent (w_H W) mem' a) /\
let mr := mrestrict (w_H W) mem' in
val_mem tfibsegs mr (A_ALLOCATOR + 680) 4 0 /\
val_mem tfibsegs mr (A_ALLOCATOR + 120) 8 (nA - 1) /\
val_mem tfibsegs mr (A_ALLOCATOR + 128) 1 0 /\
(exists v, val_mem tfibsegs mr (A_ALLOCATOR + 144) 8 v) /\ (exists v, val_mem tfibsegs mr (A_ALLOCATOR + 152) 8 v) /\
(exists v, val_mem tfibsegs mr (A_ALLOCATOR + 704) 8 v) /\ (exists v, val_mem tfibsegs mr (A_ALLOCATOR + 712) 8 v) /\
val_mem tfibsegs mr qi 8 lst /\
(own = false -> val_mem tfibsegs mr (lst + 24) 8 idx /\ forall a, lst + 24 <= a < lst + 32 -> apresent (w_H W) mem' a).
Theorem FIN_core : forall regs' mem' md1 mat, FINAL regs' mem' ->
ALedger tfibsegs ly X md1 -> amwf md1 -> same_io md md1 -> In (w64 MAP, w64 LEN) (vm_maps (m_vmmaps md1)) ->
let mdM := munmap_model (w64 MAP) (w64 LEN) md1 in
rcc_leaf B ly X k W regs mem md (tt, X2v) W2 (mkCfg (mkst regs' (w64 vra) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy mdM) mat mdM)).
Proof.
intros regs' mem' md1 mat HF LED1 MW1 IO1 INV1 mdM.
pose proof PRE as PRE'. destruct PRE' as (HAR & Hci & _ & Hst & Hni & Hra & Hra4 & Hal & Hlo & Hcb1 & Hcb2 & Hcb3 & HPRES & HPRC & HVC & Hgp & Htp & Ha0 & Ha1).
destruct HAR as (M' & LED & BUD & MW & HSH). unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hcb1, HPRES.
pose proof MAP_facts as (P1 & P2 & P3 & INA & INV & _). pose proof LEN_facts as [L1 L2]. pose proof KFACTS as (Ho & _ & ELEN & _ & FP & INE).
destruct HF as (CS & CSP & C8 & C9 & C18 & AGm & SHD' & PRS & PRSJ & PRSQ & VALS). cbv zeta in VALS.
destruct VALS as (VMU & VNS & VSRT & [v1 V1] & [v2 V2] & [v3 V3] & [v4 V4] & VQI & VOWN).
set (rd := aview tfibsegs (w_H W) mem) in *. set (rd' := aview tfibsegs (w_H W) mem').
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (HSP' : ly_stk_lo ly + KSTACK <= sp0 <= ly_stk_hi ly) by (split; [exact Hlo | clear - Hcb1 Hcb2; lia]).
assert (EI : A_ALLOCATOR = as_inst B) by (rewrite (ts_inst _ TB); reflexivity).
pose proof (AFf4.geom B ly X rd M' k r o Hk Hb IMG) as GEOM. cbv zeta in GEOM. fold MAP in GEOM.
assert (ELEN' : sec_map_size (ck_req k) = LEN) by (symmetry; exact ELEN).
pose proof (AFf4.HIGH B TB ly X rd M' IMG) as HI. pose proof HI as (_ & _ & hQ1 & hQ2 & hT1 & hT2 & _ & _ & _ & _ & _ & _ & _ & _ & hS1 & hS2 & _ & _ & hI1 & hI2 & hCE & hEI). unfold zone3, zone3cases in hT1.
pose proof GEOM as (GZ & GM2 & GM3 & GM4 & _). pose proof GZ as (GM1 & _ & _).
pose proof (AFf4.ARR B ly X rd M' r i Hi) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
destruct (AFf4.LST B ly X rd M' k r o sm i Hk Hb Hsm Hi IMG) as (y2 & Hy2 & Ey2 & CI2 & Q1 & Q2 & Q3 & Q4 & Q5).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ AFf4.D B ly X k r i sp0 a -> rd' a = rd a).
{ intros a Ha ND. subst rd rd'. apply aview_same. apply AGm. rewrite unsigned_lit_small by exact Ha. exact ND. }
assert (Ddec : forall a, AFf4.D B ly X k r i sp0 a \/ ~ AFf4.D B ly X k r i sp0 a) by (intros a; apply Classical_Prop.classic).
assert (VIS : forall a, 0 <= a < 2 ^ 64 -> rd a <> None -> ~ AFf4.DM ly k r a -> rd' a <> None).
{ intros a Ha Hv NM. destruct (Ddec a) as [HD|ND]; [| rewrite (AG a Ha ND); exact Hv].
assert (NH : w_H W (Z_to_bv 64 a) = false) by (subst rd; destruct (w_H W (Z_to_bv 64 a)) eqn:Hh; [exfalso; exact (Hv (aview_hidden_none W mem a Hh)) | reflexivity]).
subst rd'.
unfold AFf4.D, AFf4.DS, AFf4.DI, AFf4.DJ, AFf4.DQ, AFf4.DL, AFf4.DH in HD.
unfold AFf4.own, AFf4.qi, AFf4.lst, AFf4.MAP, AFf4.LEN, AFf4.idx, AFf4.nA, AFf4.lastr, AFf4.arr in HD.
rewrite ELEN', <- EI in HD. fold MAP qi lst idx nA own in HD.
destruct HD as [Y|[Y|[Y|[Y|[[Yo Y]|[Y|Y]]]]]].
-   apply apresent_vis; [exact Ha | apply PRS; exact Y].
-
destruct Y as [Y|[Y|[Y|Y]]].
+ eapply val_mem_vis; [exact VMU | cbn; lia].
+ destruct (Z_lt_le_dec a (A_ALLOCATOR + 128)); [eapply val_mem_vis; [exact VNS | cbn; lia] | eapply val_mem_vis; [exact VSRT | cbn; lia]].
+ destruct (Z_lt_le_dec a (A_ALLOCATOR + 152)); [eapply val_mem_vis; [exact V1 | cbn; lia] | eapply val_mem_vis; [exact V2 | cbn; lia]].
+ destruct (Z_lt_le_dec a (A_ALLOCATOR + 712)); [eapply val_mem_vis; [exact V3 | cbn; lia] | eapply val_mem_vis; [exact V4 | cbn; lia]].
-   apply apresent_vis; [exact Ha | apply PRSJ; exact Y].
- apply apresent_vis; [exact Ha | apply PRSQ; exact Y].
- apply apresent_vis; [exact Ha | apply (proj2 (VOWN Yo)); exact Y].
-   unfold aview, mbyte, mrestrict. rewrite NH. rewrite (SHD' (Z_to_bv 64 a)); [discriminate|].
unfold SHAv, CNTv. rewrite unsigned_lit_small by exact Ha. unfold shadow_addr in Y. exact Y.
- exfalso. exact (NM Y). }
assert (VM : forall a a' (w : nat) v v', val_mem tfibsegs (mrestrict (w_H W) mem') a w v -> a = a' -> v = v' ->
forall kk, (kk < w)%nat -> rd' (a' + Z.of_nat kk) = Some (YG0f.le_byte v' w kk)).
{ intros a a' w v v' Hv <- <- kk Hk'. subst rd'. exact (val_mem_aview _ _ _ _ _ kk Hv Hk'). }
assert (MUT' : forall j, 0 <= j < 4 -> rd' (as_inst B + 680 + j) = Some 0).
{ intros j Hj. replace (as_inst B + 680 + j) with (A_ALLOCATOR + 680 + Z.of_nat (Z.to_nat j)) by (rewrite EI; lia).
rewrite (VM _ _ 4%nat _ _ VMU eq_refl eq_refl (Z.to_nat j)) by lia. rewrite AFf4.le_byte_0. reflexivity. }
assert (NS' : forall kk, (kk < 8)%nat -> rd' (as_inst B + 120 + Z.of_nat kk) = Some (YG0f.le_byte (nA - 1) 8 kk)).
{ apply (VM _ _ 8%nat _ _ VNS); [rewrite EI; reflexivity | reflexivity]. }
assert (QI' : forall kk, (kk < 8)%nat -> rd' (qi + Z.of_nat kk) = Some (YG0f.le_byte lst 8 kk)).
{ apply (VM _ _ 8%nat _ _ VQI); reflexivity. }
assert (LST' : own = false -> forall kk, (kk < 8)%nat -> rd' (lst + 24 + Z.of_nat kk) = Some (YG0f.le_byte idx 8 kk)).
{ intros Hown. apply (VM _ _ 8%nat _ _ (proj1 (VOWN Hown))); reflexivity. }
pose proof (AFf4.rs_fin_ARm B TB ly X rd rd' M' k r o sm i Hk Hst Hb Hni Hci Hsm Hi sp0 HSP' IMG AG VIS MUT' NS' QI' LST' HTSD) as MF.
pose proof (am_layout B ly X rd M') as LO'. pose proof (am_wf B ly X rd M') as WFX.
destruct (in_split _ _ INV1) as (l1 & l2 & EVM).
assert (MWM : amwf mdM) by (exact (munmap_amwf md1 (w64 MAP, w64 LEN) l1 l2 MW1 EVM)).
assert (HS2 : ahs B ly (AFf4.X2 X k r sm i) (w_H W) mem').
{ apply (AFf4.ahs_X2 B TB ly X rd M' k r o sm i Hk Hst Hb Hsm Hi sp0 HSP' IMG (w_H W) mem mem' HSH).
- intros a Ha ND. apply AGm. unfold w64. rewrite unsigned_lit_small by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia). exact ND.
- intros a Hd. apply SHD'. unfold SHAv, CNTv. unfold AFf4.DH, AFf4.MAP, AFf4.LEN, shadow_addr in Hd. rewrite ELEN' in Hd. fold MAP in Hd.
unfold w64. rewrite unsigned_lit_small by (clear - Hd GEOM L1; numconst_hi; unfold MAP, LEN in *; lia). exact Hd. }
rewrite X2v_eq. exists regs', mem', (with_vm_backing (m_vm_lazy mdM) mat mdM). cbn [fst snd].
split; [unfold cfg_at, raZ, vra; reflexivity|].
split.
2:{ split; [|exact (AFf4.X2_cinit X k r sm i Hci)].
intros a Ha (c' & Hc' & Hr) NK. unfold W2. rewrite wrefund_H. apply AG; [exact Ha|]. intros HD.
pose proof (region_in_prim ly c' LO' Hc') as (R1 & R2 & _).
pose proof (wf_classes _ _ _ _ _ WFX c' Hc') as CL'. pose proof (wr_alloc _ _ _ _ _ _ CL') as AL1.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X c' WFX Hc') as MB. unfold kUserMapSize, EV_MAX in MB.
exact (proj2 (AFf4.ok_prim B TB ly X rd M' k r o sm i Hk Hb Hsm Hi sp0 HSP' IMG a ltac:(clear - Hr AL1 MB R1 R2; lia)) HD). }
split; [|split; [apply layout_le_refl | split; [apply wrefund_wle | split; [|split; [|split]]]]].
-
split; [exact MF | split; [|split; [|split; [eapply amwf_same; [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MWM] | exact HS2]]]].
+
destruct (AFf4.sec_extents_split B ly X rd M' k r o sm i Hk Hb) as (E1 & E2 & EX & EX2).
pose proof (ALedger_munmap tfibsegs (as_universe B) 0 0 0 ly X (AFf4.X2 X k r sm i) md1 (AFf4.MAP ly r, AFf4.LEN k) E1 E2
LO' WFX (am_placed B ly X rd M') MW1 LED1 EX EX2 (fun c _ => AFf4.reg' X k r sm i c)
(AFf4.prim_committed' X k r sm i) (AFf4.X2_nev X k r sm i) (AFf4.X2_sec_res X k r sm i)) as LM.
cbv zeta in LM. destruct LM as (LED2 & _ & _). cbn [fst snd] in LED2. unfold AFf4.MAP, AFf4.LEN in LED2. rewrite ELEN' in LED2. fold MAP mdM in LED2.
eapply ALedger_same; [exact LED2 | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
+
destruct BUD as [BUD PIN]. split.
* unfold W2. rewrite wrefund_A. rewrite (AFf4.abudget' B ly X rd M' k r o sm i Hk Hb Hsm  ). unfold AFf4.LEN. rewrite ELEN'.
pose proof (A_bytes_refund iv (w_A W) (w_Awf W) INA) as AB. unfold iv in AB. cbn [fst snd] in AB. unfold iv. clear - AB BUD. lia.
* unfold W2, iv. rewrite wrefund_A. rewrite ELEN. exact (AFf4.asecA_X2 B ly X rd M' k r o sm i Hk Hb IMG _ PIN).
-
intros rr Hr'. unfold acallee_saved in Hr'.
destruct (Z.eq_dec rr 2) as [->|N2]; [exact CSP|].
destruct (Z.eq_dec rr 8) as [->|N8]; [etransitivity; [exact C8 | unfold vs0, w64; apply Z_to_bv_bv_unsigned]|].
destruct (Z.eq_dec rr 9) as [->|N9]; [etransitivity; [exact C9 | unfold vs1, w64; apply Z_to_bv_bv_unsigned]|].
destruct (Z.eq_dec rr 18) as [->|N18]; [etransitivity; [exact C18 | unfold vs2, w64; apply Z_to_bv_bv_unsigned]|].
assert (R : rr = 3 \/ rr = 4 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
assert (Hin : In (Z_to_bv 5 rr) AFgv.SREGS).
{ clear - R. unfold AFgv.SREGS. repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; subst rr; cbn [In];
repeat (first [left; apply bv_eq; vm_compute; reflexivity | right]). }
exact (CS _ Hin).
-
pose proof (same_io_munmap (w64 MAP) (w64 LEN) md1) as IO2. pose proof (same_io_wvb' (m_vm_lazy mdM) mat mdM) as IO3.
fold mdM in IO2. clear - IO1 IO2 IO3. unfold same_io in *.
destruct IO1 as (I1 & I2 & I3 & I4). destruct IO2 as (J1 & J2 & J3 & J4). destruct IO3 as (K1 & K2 & K3 & K4). repeat split; congruence.
-
intros a Ha NO NO' NS NE. unfold W2. rewrite wrefund_H. apply AG; [exact Ha|]. intros HD.
destruct (AFf4.D_owned B TB ly X rd M' k r o sm i Hk Hst Hb Hsm Hi sp0 HSP' IMG a (proj1 Ha) HD) as [O|O]; [exact (NO O) | apply NS; unfold ascratch, spZ; left; exact O].
-
intros a Ha. unfold spZ in Ha. fold sp0 in Ha. unfold W2. rewrite wrefund_H. apply PRS. exact Ha.
Qed.
Theorem FIN : forall regsD memD mat1 W' c', LINKD regsD memD ->
AFgv.at_RET W ly regsD memD MAP LEN idx nA qi lst vra vs0 vs1 vs2 own (munmap_model (w64 MAP) (w64 LEN) (with_vm_backing (m_vm_lazy md) mat1 md)) W' c' ->
rcc_leaf B ly X k W regs mem md (tt, X2v) W2 c'.
Proof.
intros regsD memD mat1 W' c' (LSP & LSR & LMEM & LPRES) HR.
pose proof PRE as PRE'. destruct PRE' as (HAR & Hci & _ & Hst & Hni & Hra & Hra4 & Hal & Hlo & Hcb1 & Hcb2 & Hcb3 & HPRES & HPRC & HVC & Hgp & Htp & Ha0 & Ha1).
destruct HAR as (M' & LED & BUD & MW & HSH). unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hcb1, HPRES.
pose proof MAP_facts as (P1 & P2 & P3 & INA & INV & _). pose proof LEN_facts as [L1 L2]. pose proof KFACTS as (Ho & _ & ELEN & _ & FP & INE).
destruct HR as (-> & regs' & mem' & mat & -> & CS & CSP & C8 & C9 & C18 & MEQ' & SHD' & PRS & PRS2 & VALS). cbv zeta in VALS.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
set (rd := aview tfibsegs (w_H W) mem) in *.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (HSP' : ly_stk_lo ly + KSTACK <= sp0 <= ly_stk_hi ly) by (split; [exact Hlo | clear - Hcb1 Hcb2; lia]).
assert (EI : A_ALLOCATOR = as_inst B) by (rewrite (ts_inst _ TB); reflexivity).
assert (SPD : bv_unsigned (getr regsD 2) = sp0) by (rewrite LSP; reflexivity).
pose proof (AFf4.geom B ly X rd M' k r o Hk Hb IMG) as GEOM. cbv zeta in GEOM. fold MAP in GEOM.
assert (ELEN' : sec_map_size (ck_req k) = LEN) by (symmetry; exact ELEN).
pose proof (AFf4.HIGH B TB ly X rd M' IMG) as HI. pose proof HI as (_ & _ & hQ1 & hQ2 & hT1 & hT2 & _ & _ & _ & _ & _ & _ & _ & _ & hS1 & hS2 & _ & _ & hI1 & hI2 & hCE & hEI). unfold zone3, zone3cases in hT1.
pose proof GEOM as (GZ & GM2 & GM3 & GM4 & _). pose proof GZ as (GM1 & _ & _).
pose proof (AFf4.ARR B ly X rd M' r i Hi) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
destruct (AFf4.LST B ly X rd M' k r o sm i Hk Hb Hsm Hi IMG) as (y2 & Hy2 & Ey2 & CI2 & Q1 & Q2 & Q3 & Q4 & Q5).
pose proof (AFf4.SX B ly X rd M' 1 2 _ _ eq_refl eq_refl ltac:(lia)) as DQT. pose proof (AFf4.SECX B ly X rd M' _ 2 _ CI2 eq_refl) as DLT.
pose proof (AFf4.MAPX B ly X rd M' k r o sm Hk Hb Hsm 2 _ eq_refl) as DMT. unfold zdisjoint in DQT, DLT, DMT. cbn [fst snd] in DQT, DLT, DMT.
assert (WD : forall a, 0 <= a < 2 ^ 64 -> (WPRE a \/ AFgv.WIN3 ly regsD MAP LEN qi lst a) -> AFf4.D B ly X k r i sp0 a).
{ intros a Ha HW. unfold AFf4.D, AFf4.DS, AFf4.DI, AFf4.DJ, AFf4.DQ, AFf4.DL, AFf4.DH, AFf4.DM.
unfold AFf4.own, AFf4.qi, AFf4.lst, AFf4.MAP, AFf4.LEN, AFf4.idx, AFf4.nA, AFf4.lastr, AFf4.arr.
rewrite ELEN'. fold MAP. rewrite <- EI. unfold shadow_addr.
unfold WPRE, AFgv.WIN3, AFgv.WIN2, AFgv.WIN, AFgv.WINS, AFgv.WINM, SHAv, CNTv, GDEPTH in HW. rewrite SPD in HW.
unfold own, qi, lst, idx, nA in *.
destruct (Z.eqb_spec (Z.of_nat i) (Z.of_nat (length (st_sec_arr X)) - 1)) as [EO|NEO].
-
assert (LR : last (st_sec_arr X) r = r) by (apply A8; unfold AFf4.own, AFf4.idx, AFf4.nA, AFf4.arr; apply Z.eqb_eq; exact EO).
rewrite LR in HW. fold MAP in HW. unfold KSTACK.
lazymatch goal with |- ?A \/ ?Bq \/ ?C \/ ?Dq \/ (_ /\ _) \/ ?G =>
enough (G' : A \/ Bq \/ C \/ Dq \/ G) by (destruct G' as [?|[?|[?|[?|?]]]]; [left | right; left | do 2 right; left | do 3 right; left | do 5 right]; assumption) end.
clear - HW L1 Ha. lia.
- unfold KSTACK.
lazymatch goal with |- ?A \/ ?Bq \/ ?C \/ ?Dq \/ (_ /\ ?F) \/ ?G =>
enough (G' : A \/ Bq \/ C \/ Dq \/ F \/ G) by (destruct G' as [?|[?|[?|[?|[?|?]]]]]; [left | right; left | do 2 right; left | do 3 right; left | do 4 right; left; split; [reflexivity | assumption] | do 5 right]; assumption) end.
clear - HW L1 Ha. lia. }
apply (FIN_core regs' mem' md1 mat).
- split; [intros r' Hr'; rewrite (CS _ Hr'); exact (LSR _ Hr')|].
split; [etransitivity; [exact CSP | exact LSP]|]. split; [exact C8|]. split; [exact C9|]. split; [exact C18|].
split. {
intros x ND. rewrite (MEQ' x) by (intros HW; apply ND; apply WD; [apply u64_range | right; exact HW]).
apply LMEM. intros HW. apply ND. apply WD; [apply u64_range | left; exact HW]. }
split. { intros x Hx. apply SHD'. unfold AFgv.WINS. exact Hx. }
split. {
intros a Y. destruct (Z_lt_le_dec a (sp0 - GDEPTH)) as [LOW|HIGH'].
+ assert (Ha : 0 <= a < 2 ^ 64) by (clear - Y Usp HSP' hS1 hS2; unfold KSTACK in *; numconst_hi; lia).
apply (apresent_same (w_H W) mem); [|apply HPRES; exact Y].
rewrite (MEQ' (Z_to_bv 64 a)) by (unfold AFgv.WIN3, AFgv.WIN2, AFgv.WIN, AFgv.WINS, AFgv.WINM, SHAv, CNTv; rewrite unsigned_lit_small by exact Ha; rewrite SPD;
clear - Y LOW HSP' hS1 hCE hT2 hQ2 GM2 GM4 A4 A5 Q2 Q4 L1 ELEN'; unfold own, qi, lst, idx, nA, MAP, LEN, GDEPTH, KSTACK in *; numconst_hi; lia).
apply LMEM. unfold WPRE. rewrite unsigned_lit_small by exact Ha. clear - Y LOW HSP' hS1 hCE hT2 hEI; unfold GDEPTH, KSTACK in *; numconst_hi; lia.
+ apply PRS. rewrite SPD. unfold GDEPTH in *. lia. }
split. {
intros a [Y|Y].
+ assert (Ha : 0 <= a < 2 ^ 64) by (clear - Y hT1; numconst_hi; lia).
apply (apresent_same (w_H W) memD); [|exact (LPRES a Y)].
rewrite (MEQ' (Z_to_bv 64 a)) by (unfold AFgv.WIN3, AFgv.WIN2, AFgv.WIN, AFgv.WINS, AFgv.WINM, SHAv, CNTv; rewrite unsigned_lit_small by exact Ha; rewrite SPD;
clear - Y HSP' hT1 hCE GM1 GM2 GM4 A4 A5 Q4 L1 ELEN' DQT DLT DMT; unfold own, qi, lst, idx, nA, MAP, LEN, GDEPTH, KSTACK in *; numconst_hi; lia).
reflexivity.
+ apply PRS2. right. exact Y. }
split. { intros a Y. apply PRS2. left. exact Y. }
exact VALS.
- eapply ALedger_same; [exact LED | apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
- apply (amwf_same md md1); [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | exact MW].
- apply same_io_wvb'.
- subst md1. rewrite m_vmmaps_wvb. exact INV.
Qed.
Theorem plumbing : amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (rcc_leaf B ly X k W regs mem md).
Proof.
pose proof MAP_facts as (P1 & P2 & P3 & INA & INV & MW). pose proof LEN_facts as [L1 L2].
rewrite (recycle_chunk_sec k X r o sm i (proj2 (mem_chunk_spec _ _) Hk) Hb Hsm Hidx SMALL). cbn [amreal].
eapply SRr_bind; [exact WALK|]. intros W1 c1 _ (regsD & memD & LNK & HM).
destruct HM as (-> & regs1 & mem1 & mat1 & -> & H17 & H10 & H11 & INNER). cbv zeta in INNER.
apply SRr_use_AI. cbn [cfg_model]. intros HAI. apply SRr_ret.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
set (c2 := mkCfg (mkst (regupd regs1 10 (w64 0)) (w64 0x6417c) (unfill (w64 MAP) (w64 LEN) mem1) (seg_rom tfibsegs)) (munmap_model (w64 MAP) (w64 LEN) md1)).
assert (UM : bv_unsigned (w64 MAP) = MAP) by (unfold w64; apply unsigned_lit_small; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
assert (UL : bv_unsigned (w64 LEN) = LEN) by (unfold w64; apply unsigned_lit_small; lia).
assert (MW1 : amwf md1) by (apply (amwf_same md md1); [subst md1; apply m_vmmaps_wvb | subst md1; apply m_vm_lazy_wvb | exact MW]).
assert (INV1 : In (w64 MAP, w64 LEN) (vm_maps (m_vmmaps md1))) by (subst md1; rewrite m_vmmaps_wvb; exact INV).
destruct (in_split _ _ INV1) as (l1 & l2 & EVM).
exists unit, (fun _ => c2), (fun _ => 1), (fun _ => false), tt.
split.
{ pose proof (munmap_node tfibsegs regs1 (w64 0x64178) mem1 (seg_rom tfibsegs) md1 (w64 MAP) LEN (AI_halted _ _ _ _ HAI) H17 H10
ltac:(rewrite UM; unfold page_size; exact P3) H11 ltac:(lia)
ltac:(rewrite UM, (page_round_up_Z_aligned LEN) by lia; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, two_pow_64, TASK_SIZE, kHighMemBeg, ASAN_CEIL in *; lia)
ltac:(rewrite (page_round_up_Z_aligned LEN) by lia; exact (map_has_In _ _ _ INV1))) as ND.
cbv zeta in ND. rewrite (page_round_up_Z_aligned LEN) in ND by lia. exact ND. }
split. { intros [] _. cbn [cfg_model]. exact (munmap_AI tfibsegs (w_H W) (w_A W) md1 (w64 MAP, w64 LEN) l1 l2 HAI MW1 EVM ltac:(cbn [fst]; rewrite UM; unfold page_size; exact P3)
ltac:(cbn [fst snd]; rewrite UM, UL; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)). }
split. { intros []. cbn [aok]. reflexivity. }
split; [reflexivity|]. split; [reflexivity|]. split; [intros [] _; reflexivity|].   split; [intros [] XX; discriminate XX|].
intros [] _. cbn [amreal].
eapply SRr_bind; [exact INNER|]. intros W3 c3 _ HR. pose proof HR as (-> & regs' & mem' & mat' & Ec3 & _).
apply SRr_use_AI. intros HAI3. rewrite Ec3 in HAI3 |- *. cbn [cfg_model] in HAI3.
apply (SRr_world_le tfibsegs W W2).
{ apply wrefund_wle. }
{ intros _. cbn [cfg_model]. apply AI_refund_gen; [exact HAI3|]. intros p Hp. rewrite m_vm_lazy_wvb in Hp. unfold iv. cbn [fst snd].
pose proof (munmap_lazy_out (w64 MAP) (w64 LEN) md1 p ltac:(destruct MW1 as [(_ & _ & W3l & _) _]; intros q Hq; exact (W3l q Hq))
ltac:(rewrite UM, UL; ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) Hp) as NL. rewrite UM, UL in NL. exact NL. }
apply SRr_ret. rewrite <- Ec3. exact (FIN regsD memD mat1 W c3 LNK HR).
Qed.
End e.
End d.
