(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g YQ0k YK0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o YA05.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG06 YG03 YG0h YG10 YG0u YG0d YG0y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0l YG0v YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF0q YF0o YF0x YF0y YF1h YF2q.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Ltac numconst_hi := ceil; unfold zone3, zone3cases, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kPtrArrayResv, kLowMemEnd, kPage, t_stats, A_ALLOCATOR, TFX_INST, SHADOW_OFF, kHighShadowBeg, kHighShadowEnd in *;
unfold YF0y.own, YF0y.qi, YF0y.lst, YF0y.MAP, YF0y.LEN, YF0y.idx, YF0y.nA, YF0y.lastr, YF0y.arr in *.
Definition X2 (X1 : astate) (r : nat) (i : nat) (sm : secmap) : astate :=
set_sec_arr (removelast (lupd (st_sec_arr X1) i (last (st_sec_arr X1) r)))
(set_secs (lupd (st_secs X1) r (mkSec (sm_len sm) (sm_size sm) false)) X1).
Lemma recycle_chunk_sec : forall k X r o sm i,
mem_chunk k (st_chunks X) = true -> ck_beg k = PSec r o ->
nth_error (st_secs X) r = Some sm -> index_of (st_sec_arr X) r 0%nat = Some i -> needs_remap (sm_len sm) = false ->
recycle_chunk k X = IAsk (KMunmapSec r (sm_len sm)) (YF0x.X1 X k) (fun _ => IRet (tt, X2 (YF0x.X1 X k) r i sm)).
Proof.
intros k X r o sm i Hm Hb Hsm Hi NR. unfold recycle_chunk, bind, get. cbn [ibind]. rewrite Hm. unfold mcheck, ret, put. cbn [ibind].
rewrite Hb. unfold sec_dealloc, bind, get. cbn [ibind st_secs st_sec_arr set_chunks YF0x.X1].
replace (st_secs (set_chunks (del_chunk (st_chunks X) (PSec r o)) X)) with (st_secs X) by (img_try (destruct X; img_refl)).
replace (st_sec_arr (set_chunks (del_chunk (st_chunks X) (PSec r o)) X)) with (st_sec_arr X) by (img_try (destruct X; img_refl)).
rewrite Hsm, Hi, NR. unfold ret, askz, modify. cbn [ibind]. unfold X2, YF0x.X1. rewrite Hb.
replace (st_sec_arr (set_chunks (del_chunk (st_chunks X) (PSec r o)) X)) with (st_sec_arr X) by (img_try (destruct X; img_refl)).
replace (st_secs (set_chunks (del_chunk (st_chunks X) (PSec r o)) X)) with (st_secs X) by (img_try (destruct X; img_refl)).
img_refl.
Qed.
Lemma page_round_up_Z_aligned : forall n, 0 <= n -> n mod 4096 = 0 -> page_round_up_Z n = n.
Proof. intros n Hn Hm. unfold page_round_up_Z, page_size. apply Z.mod_divide in Hm as [q Hq]; [|img_lia]. (subst n; cbv beta). rewrite <- (Z.mul_comm 4096 q).
replace (4096 * q + 4096 - 1) with (q * 4096 + 4095) by img_lia. rewrite Z.div_add_l by img_lia. img_change (4095 / 4096) with 0. img_lia. Qed.
Section e. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (r : nat) (o : Z) (sm : secmap) (i : nat).
Hypothesis PRE : rcc_pre B ly X k cbp W regs mem md.
Hypothesis Hb : ck_beg k = PSec r o.
Hypothesis Hsm : nth_error (st_secs X) r = Some sm.
Hypothesis Hi : nth_error (st_sec_arr X) i = Some r.
Hypothesis Hidx : index_of (st_sec_arr X) r 0%nat = Some i.
Hypothesis SMALL : needs_remap (sm_len sm) = false.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
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
Definition X1 : astate := YF0x.X1 X k.
Definition X2v : astate := X2 X1 r i sm.
Definition iv : Z * Z := (MAP, MAP + LEN).
Definition W2 : world tfxsegs := wrefund tfxsegs W iv.
Lemma M : AR tfxsegs B ly X W mem md. Proof. img_exact (proj1 PRE). Qed.
Lemma Hk : In k (st_chunks X). Proof. img_exact (proj1 (proj2 (proj2 PRE))). Qed.
Lemma IMG : img_cover ly.
Proof. img_exact (img_cover_of_ledger ly X md (proj1 (proj2 (proj1 PRE)))). Qed.
Lemma KFACTS : o = kPage /\ sm_live sm = true /\ LEN = sec_map_size (ck_req k) /\ 0 <= ck_req k < MALLOC_MAX /\ from_primary (ck_req k) = false /\
In (MAP, LEN) (sec_extents ly X).
Proof.
pose proof M as (AM & _). pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ (am_wf B ly X _ AM)) k Hk) as [Hn CK].
rewrite Hb in CK. destruct CK as (P1 & P2 & sm' & Q1 & Q2 & Q3 & Q4). rewrite Hsm in Q1. injection Q1 as <-.
unfold LEN. repeat split; try assumption; try img_lia.
unfold sec_extents. img_apply in_flat_map. exists k. split; [img_try (img_exact Hk)|]. rewrite Hb. left. unfold MAP. rewrite Q4. img_refl.
Qed.
Lemma LEN_facts : 8192 <= LEN < 2 ^ 29 /\ LEN mod 4096 = 0.
Proof.
pose proof KFACTS as (_ & _ & E & Hn & FP & _). rewrite E. unfold sec_map_size, needed_size. rewrite FP.
unfold from_primary in FP. apply Z.leb_gt in FP.
pose proof (round_up_ge (needed_primary (ck_req k) + rz_size (ck_req k)) kPage ltac:(img_try (unfold kPage; img_lia))) as [R1 R2].
pose proof (needed_primary_bounds (ck_req k) ltac:(img_lia)) as (N1 & N2 & N3). pose proof (rz_size_bounds (ck_req k)) as [RZ _].
unfold kMaxSize, kPage, MALLOC_MAX in *. split; [img_lia|].
rewrite Z.add_mod, R2, Z.mod_same by img_lia. img_refl.
Qed.
Lemma MAP_facts : zone3 MAP LEN /\ MAP + LEN <= ASAN_CEIL /\ MAP mod 4096 = 0 /\
In (MAP, MAP + LEN) (w_A W) /\ In (w64 MAP, w64 LEN) (vm_maps (m_vmmaps md)) /\ amwf md.
Proof.
pose proof M as (AM & AL & AB & MW & _). pose proof KFACTS as (_ & _ & _ & _ & _ & IN).
pose proof (YF0y.ZSEC B ly X _ AM IMG _ IN) as (H1 & PA & H2). cbn [fst snd] in PA, H1, H2. unfold page_aligned in PA.
split; [img_try (img_exact H1)|]. split; [img_try (img_exact H2)|]. split; [img_try (img_exact PA)|]. split; [img_try (img_exact (proj1 (proj2 AB _ IN)))|]. split; [img_try (img_exact (al_sec _ _ _ _ AL _ IN)) | img_try (img_exact MW)].
Qed.

Definition WPRE (a : Z) : Prop :=
(sp0 - GDEPTH <= a < sp0) \/ (A_ALLOCATOR + 680 <= a < A_ALLOCATOR + 684) \/ (T + t_stats + 40 <= a < T + t_stats + 56).
Definition LINKD (regsD : bvmap 5 word) (memD : word -> option byte) : Prop :=
getr regsD 2 = getr regs 2 /\ (forall r' : bv 5, In r' YF2q.SREGS -> getr regsD r' = getr regs r') /\
(forall x : word, ~ WPRE (bv_unsigned x) -> memD x = mem x) /\
(forall a, T + t_stats + 40 <= a < T + t_stats + 56 -> apresent (w_H W) memD a).
Definition POSTMUN (W' : world tfxsegs) (c' : config) : Prop :=
exists regsD memD, LINKD regsD memD /\ YF2q.at_MUN W ly regsD memD md MAP LEN idx nA qi lst vra vs0 vs1 vs2 own W' c'.
Hypothesis WALK : SRr tfxsegs W (cfg_at tfxsegs A_RChunk regs mem md) POSTMUN.
Lemma val_mem_aview : forall H m a (w : nat) v kk, val_mem tfxsegs (mrestrict H m) a w v -> (kk < w)%nat ->
aview tfxsegs H m (a + Z.of_nat kk) = Some (YG0h.le_byte v w kk).
Proof.
clear. intros H m a w v kk Hv Hk'. unfold aview. rewrite (Hv kk Hk'). cbn [option_map]. img_change (YG0h.le_byte v w kk) with (YP0g.le_byte v w kk). f_equal. img_apply unsigned_lit_small8.
unfold YP0g.le_byte. img_apply Z.mod_pos_bound. img_lia.
Qed.
Lemma val_mem_vis : forall H m a (w : nat) v b, val_mem tfxsegs (mrestrict H m) a w v -> a <= b < a + Z.of_nat w -> aview tfxsegs H m b <> None.
Proof.
clear. intros H m a w v b Hv Hb. replace b with (a + Z.of_nat (Z.to_nat (b - a))) by img_lia. rewrite (val_mem_aview H m a w v _ Hv) by img_lia. discriminate.
Qed.
Lemma apresent_vis : forall H m a, 0 <= a < 2 ^ 64 -> apresent H m a -> aview tfxsegs H m a <> None.
Proof. clear. intros H m a Ha [Hh [b Hb]]. unfold aview, mbyte, mrestrict, w64 in *. rewrite Hh, Hb. discriminate. Qed.
Lemma aview_hidden_none : forall (W0 : world tfxsegs) m a, w_H W0 (Z_to_bv 64 a) = true -> aview tfxsegs (w_H W0) m a = None.
Proof.
clear. intros W0 m a Hh. unfold aview, mbyte, mrestrict. rewrite Hh. unfold seg_rom, memory_read. img_change (Z.of_N 1) with 1.
rewrite (w_Hoff W0 _ Hh). img_refl.
Qed.
Lemma same_io_wvb' : forall l p md0, same_io md0 (with_vm_backing l p md0). Proof. clear. intros. repeat split; img_refl. Qed.
Lemma X2v_eq : X2v = YF0y.X2 X k r sm i.
Proof. clear. unfold X2v, X2, X1, YF0y.X2, YF0y.arr', YF0y.arr, YF0y.lastr, YF0x.X1. destruct X; img_refl. Qed.
Definition FINAL (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
(forall r' : bv 5, In r' YF2q.SREGS -> getr regs' r' = getr regs r') /\
getr regs' 2 = getr regs 2 /\ getr regs' 8 = w64 vs0 /\ getr regs' 9 = w64 vs1 /\ getr regs' 18 = w64 vs2 /\
(forall x : word, ~ YF0y.D B ly X k r i sp0 (bv_unsigned x) -> mem' x = mem x) /\
(forall x : word, SHAv MAP <= bv_unsigned x < SHAv MAP + CNTv LEN -> mem' x = Some (Z_to_bv 8 0)) /\
(forall a, sp0 - KSTACK <= a < sp0 -> apresent (w_H W) mem' a) /\
(forall a, (T + t_stats + 40 <= a < T + t_stats + 56) \/ (T + t_stats + 88 <= a < T + t_stats + 104) -> apresent (w_H W) mem' a) /\
(forall a, qi <= a < qi + 8 -> apresent (w_H W) mem' a) /\
let mr := mrestrict (w_H W) mem' in
val_mem tfxsegs mr (A_ALLOCATOR + 680) 4 0 /\
val_mem tfxsegs mr (A_ALLOCATOR + 120) 8 (nA - 1) /\
val_mem tfxsegs mr (A_ALLOCATOR + 128) 1 0 /\
(exists v, val_mem tfxsegs mr (A_ALLOCATOR + 144) 8 v) /\ (exists v, val_mem tfxsegs mr (A_ALLOCATOR + 152) 8 v) /\
(exists v, val_mem tfxsegs mr (A_ALLOCATOR + 704) 8 v) /\ (exists v, val_mem tfxsegs mr (A_ALLOCATOR + 712) 8 v) /\
val_mem tfxsegs mr qi 8 lst /\
(own = false -> val_mem tfxsegs mr (lst + 24) 8 idx /\ forall a, lst + 24 <= a < lst + 32 -> apresent (w_H W) mem' a).
Theorem FIN_core : forall regs' mem' md1 mat, FINAL regs' mem' ->
ALedger tfxsegs ly X md1 -> amwf md1 -> same_io md md1 -> In (w64 MAP, w64 LEN) (vm_maps (m_vmmaps md1)) ->
let mdM := munmap_model (w64 MAP) (w64 LEN) md1 in
rcc_leaf B ly X k W regs mem md (tt, X2v) W2 (mkCfg (mkst regs' (w64 vra) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy mdM) mat mdM)).
Proof.
intros regs' mem' md1 mat HF LED1 MW1 IO1 INV1 mdM.
pose proof PRE as PRE'. destruct PRE' as (HAR & Hci & _ & Hst & Hni & Hra & Hra4 & Hal & Hlo & Hcb1 & Hcb2 & Hcb3 & HPRES & HPRC & HVC & Hgp & Htp & Ha0 & Ha1).
destruct HAR as (M' & LED & BUD & MW & HSH). unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hcb1, HPRES.
pose proof MAP_facts as (P1 & P2 & P3 & INA & INV & _). pose proof LEN_facts as [L1 L2]. pose proof KFACTS as (Ho & _ & ELEN & _ & FP & INE).
destruct HF as (CS & CSP & C8 & C9 & C18 & AGm & SHD' & PRS & PRSJ & PRSQ & VALS). cbv zeta in VALS.
destruct VALS as (VMU & VNS & VSRT & [v1 V1] & [v2 V2] & [v3 V3] & [v4 V4] & VQI & VOWN).
set (rd := aview tfxsegs (w_H W) mem) in *. set (rd' := aview tfxsegs (w_H W) mem').
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
assert (HSP' : ly_stk_lo ly + KSTACK <= sp0 <= ly_stk_hi ly) by (img_try (split; [img_try (img_exact Hlo) | img_try (clear - Hcb1 Hcb2; img_lia)])).
assert (EI : A_ALLOCATOR = as_inst B) by (img_try (rewrite (ts_inst _ TB); img_refl)).
pose proof (YF0y.geom B ly X rd M' k r o Hk Hb IMG) as GEOM. cbv zeta in GEOM. fold MAP in GEOM.
assert (ELEN' : sec_map_size (ck_req k) = LEN) by (img_try (symmetry; img_exact ELEN)).
pose proof (YF0y.HIGH B TB ly X rd M' IMG) as HI. pose proof HI as (_ & _ & hQ1 & hQ2 & hT1 & hT2 & _ & _ & _ & _ & _ & _ & _ & _ & hS1 & hS2 & _ & _ & hI1 & hI2 & hCE & hEI). unfold zone3, zone3cases in hT1.
pose proof GEOM as (GZ & GM2 & GM3 & GM4 & _). pose proof GZ as (GM1 & _ & _).
pose proof (YF0y.ARR B ly X rd M' r i Hi) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
destruct (YF0y.LST B ly X rd M' k r o sm i Hk Hb Hsm Hi IMG) as (y2 & Hy2 & Ey2 & CI2 & Q1 & Q2 & Q3 & Q4 & Q5).
assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ YF0y.D B ly X k r i sp0 a -> rd' a = rd a).
{ intros a Ha ND. (subst rd rd'; cbv beta). img_apply aview_same. img_apply AGm. rewrite unsigned_lit_small by img_exact Ha. img_exact ND. }
assert (Ddec : forall a, YF0y.D B ly X k r i sp0 a \/ ~ YF0y.D B ly X k r i sp0 a) by (img_try (intros a; img_apply Classical_Prop.classic)).
assert (VIS : forall a, 0 <= a < 2 ^ 64 -> rd a <> None -> ~ YF0y.DM ly k r a -> rd' a <> None).
{ intros a Ha Hv NM. destruct (Ddec a) as [HD|ND]; [| img_try (rewrite (AG a Ha ND); img_exact Hv)].
assert (NH : w_H W (Z_to_bv 64 a) = false) by (img_try ((subst rd; cbv beta); destruct (w_H W (Z_to_bv 64 a)) eqn:Hh; [img_try (exfalso; img_exact (Hv (aview_hidden_none W mem a Hh))) | img_refl])).
(subst rd'; cbv beta).
unfold YF0y.D, YF0y.DS, YF0y.DI, YF0y.DJ, YF0y.DQ, YF0y.DL, YF0y.DH in HD.
unfold YF0y.own, YF0y.qi, YF0y.lst, YF0y.MAP, YF0y.LEN, YF0y.idx, YF0y.nA, YF0y.lastr, YF0y.arr in HD.
rewrite ELEN', <- EI in HD. fold MAP qi lst idx nA own in HD.
destruct HD as [Y|[Y|[Y|[Y|[[Yo Y]|[Y|Y]]]]]].
-   img_apply apresent_vis; [img_try (img_exact Ha) | img_try (img_apply PRS; img_exact Y)].
-
destruct Y as [Y|[Y|[Y|Y]]].
+ eapply val_mem_vis; [img_try (img_exact VMU) | img_try (cbn; img_lia)].
+ destruct (Z_lt_le_dec a (A_ALLOCATOR + 128)); [img_try (eapply val_mem_vis; [img_exact VNS | cbn; img_lia]) | img_try (eapply val_mem_vis; [img_exact VSRT | cbn; img_lia])].
+ destruct (Z_lt_le_dec a (A_ALLOCATOR + 152)); [img_try (eapply val_mem_vis; [img_exact V1 | cbn; img_lia]) | img_try (eapply val_mem_vis; [img_exact V2 | cbn; img_lia])].
+ destruct (Z_lt_le_dec a (A_ALLOCATOR + 712)); [img_try (eapply val_mem_vis; [img_exact V3 | cbn; img_lia]) | img_try (eapply val_mem_vis; [img_exact V4 | cbn; img_lia])].
-   img_apply apresent_vis; [img_try (img_exact Ha) | img_try (img_apply PRSJ; img_exact Y)].
- img_apply apresent_vis; [img_try (img_exact Ha) | img_try (img_apply PRSQ; img_exact Y)].
- img_apply apresent_vis; [img_try (img_exact Ha) | img_try (img_apply (proj2 (VOWN Yo)); img_exact Y)].
-   unfold aview, mbyte, mrestrict. rewrite NH. rewrite (SHD' (Z_to_bv 64 a)); [img_try (discriminate)|].
unfold SHAv, CNTv. rewrite unsigned_lit_small by img_exact Ha. unfold shadow_addr in Y. img_exact Y.
- exfalso. img_exact (NM Y). }
assert (VM : forall a a' (w : nat) v v', val_mem tfxsegs (mrestrict (w_H W) mem') a w v -> a = a' -> v = v' ->
forall kk, (kk < w)%nat -> rd' (a' + Z.of_nat kk) = Some (YG0h.le_byte v' w kk)).
{ intros a a' w v v' Hv <- <- kk Hk'. (subst rd'; cbv beta). img_exact (val_mem_aview _ _ _ _ _ kk Hv Hk'). }
assert (MUT' : forall j, 0 <= j < 4 -> rd' (as_inst B + 680 + j) = Some 0).
{ intros j Hj. replace (as_inst B + 680 + j) with (A_ALLOCATOR + 680 + Z.of_nat (Z.to_nat j)) by (img_try (rewrite EI; img_lia)).
rewrite (VM _ _ 4%nat _ _ VMU eq_refl eq_refl (Z.to_nat j)) by img_lia. rewrite YF0y.le_byte_0. img_refl. }
assert (NS' : forall kk, (kk < 8)%nat -> rd' (as_inst B + 120 + Z.of_nat kk) = Some (YG0h.le_byte (nA - 1) 8 kk)).
{ img_apply (VM _ _ 8%nat _ _ VNS); [img_try (rewrite EI; img_refl) | img_refl]. }
assert (QI' : forall kk, (kk < 8)%nat -> rd' (qi + Z.of_nat kk) = Some (YG0h.le_byte lst 8 kk)).
{ img_apply (VM _ _ 8%nat _ _ VQI); img_refl. }
assert (LST' : own = false -> forall kk, (kk < 8)%nat -> rd' (lst + 24 + Z.of_nat kk) = Some (YG0h.le_byte idx 8 kk)).
{ intros Hown. img_apply (VM _ _ 8%nat _ _ (proj1 (VOWN Hown))); img_refl. }
pose proof (YF0y.rs_fin_ARm B TB ly X rd rd' M' k r o sm i Hk Hst Hb Hni Hci Hsm Hi sp0 HSP' IMG AG VIS MUT' NS' QI' LST' HTSD) as MF.
pose proof (am_layout B ly X rd M') as LO'. pose proof (am_wf B ly X rd M') as WFX.
destruct (in_split _ _ INV1) as (l1 & l2 & EVM).
assert (MWM : amwf mdM) by (img_try (img_exact (munmap_amwf md1 (w64 MAP, w64 LEN) l1 l2 MW1 EVM))).
assert (HS2 : ahs B ly (YF0y.X2 X k r sm i) (w_H W) mem').
{ img_apply (YF0y.ahs_X2 B TB ly X rd M' k r o sm i Hk Hst Hb Hsm Hi sp0 HSP' IMG (w_H W) mem mem' HSH).
- intros a Ha ND. img_apply AGm. unfold w64. rewrite unsigned_lit_small by (img_try (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; img_lia)). img_exact ND.
- intros a Hd. img_apply SHD'. unfold SHAv, CNTv. unfold YF0y.DH, YF0y.MAP, YF0y.LEN, shadow_addr in Hd. rewrite ELEN' in Hd. fold MAP in Hd.
unfold w64. rewrite unsigned_lit_small by (img_try (clear - Hd GEOM L1; numconst_hi; unfold MAP, LEN in *; img_lia)). img_exact Hd. }
rewrite X2v_eq. exists regs', mem', (with_vm_backing (m_vm_lazy mdM) mat mdM). cbn [fst snd].
split; [img_try (unfold cfg_at, raZ, vra; img_refl)|].
split.
2:{ split; [|img_try (img_exact (YF0y.X2_cinit X k r sm i Hci))].
intros a Ha (c' & Hc' & Hr) NK. unfold W2. rewrite wrefund_H. img_apply AG; [img_try (img_exact Ha)|]. intros HD.
pose proof (region_in_prim ly c' LO' Hc') as (R1 & R2 & _).
pose proof (wf_classes _ _ _ _ _ WFX c' Hc') as CL'. pose proof (wr_alloc _ _ _ _ _ _ CL') as AL1.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X c' WFX Hc') as MB. unfold kUserMapSize, EV_MAX in MB.
img_exact (proj2 (YF0y.ok_prim B TB ly X rd M' k r o sm i Hk Hb Hsm Hi sp0 HSP' IMG a ltac:(img_try (clear - Hr AL1 MB R1 R2; img_lia))) HD). }
split; [|img_try (split; [img_apply layout_le_refl | split; [img_apply wrefund_wle | split; [|split; [|split]]]])].
-
split; [img_try (img_exact MF) | img_try (split; [|split; [|split; [eapply amwf_same; [img_apply m_vmmaps_wvb | img_apply m_vm_lazy_wvb | img_exact MWM] | img_exact HS2]]])].
+
destruct (YF0y.sec_extents_split B ly X rd M' k r o sm i Hk Hb) as (E1 & E2 & EX & EX2).
pose proof (ALedger_munmap tfxsegs (as_universe B) 0 0 0 ly X (YF0y.X2 X k r sm i) md1 (YF0y.MAP ly r, YF0y.LEN k) E1 E2
LO' WFX (am_placed B ly X rd M') MW1 LED1 EX EX2 (fun c _ => YF0y.reg' X k r sm i c)
(YF0y.prim_committed' X k r sm i) (YF0y.X2_nev X k r sm i) (YF0y.X2_sec_res X k r sm i)) as LM.
cbv zeta in LM. destruct LM as (LED2 & _ & _). cbn [fst snd] in LED2. unfold YF0y.MAP, YF0y.LEN in LED2. rewrite ELEN' in LED2. fold MAP mdM in LED2.
eapply ALedger_same; [img_try (img_exact LED2) | img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_apply eager_used_wvb)].
+
destruct BUD as [BUD PIN]. split.
* unfold W2. rewrite wrefund_A. rewrite (YF0y.abudget' B ly X rd M' k r o sm i Hk Hb Hsm  ). unfold YF0y.LEN. rewrite ELEN'.
pose proof (A_bytes_refund iv (w_A W) (w_Awf W) INA) as AB. unfold iv in AB. cbn [fst snd] in AB. unfold iv. clear - AB BUD. img_lia.
* unfold W2, iv. rewrite wrefund_A. rewrite ELEN. img_exact (YF0y.asecA_X2 B ly X rd M' k r o sm i Hk Hb IMG _ PIN).
-
intros rr Hr'. unfold acallee_saved in Hr'.
destruct (Z.eq_dec rr 2) as [->|N2]; [img_try (img_exact CSP)|].
destruct (Z.eq_dec rr 8) as [->|N8]; [img_try (etransitivity; [img_exact C8 | unfold vs0, w64; img_apply Z_to_bv_bv_unsigned])|].
destruct (Z.eq_dec rr 9) as [->|N9]; [img_try (etransitivity; [img_exact C9 | unfold vs1, w64; img_apply Z_to_bv_bv_unsigned])|].
destruct (Z.eq_dec rr 18) as [->|N18]; [img_try (etransitivity; [img_exact C18 | unfold vs2, w64; img_apply Z_to_bv_bv_unsigned])|].
assert (R : rr = 3 \/ rr = 4 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by img_lia.
assert (Hin : In (Z_to_bv 5 rr) YF2q.SREGS).
{ clear - R. unfold YF2q.SREGS. repeat match goal with R : _ \/ _ |- _ => destruct R as [R|R] end; (subst rr; cbv beta); cbn [In];
repeat (first [left; img_apply bv_eq; (img_case; vm_compute); img_refl | right]). }
img_exact (CS _ Hin).
-
pose proof (same_io_munmap (w64 MAP) (w64 LEN) md1) as IO2. pose proof (same_io_wvb' (m_vm_lazy mdM) mat mdM) as IO3.
fold mdM in IO2. clear - IO1 IO2 IO3. unfold same_io in *.
destruct IO1 as (I1 & I2 & I3 & I4). destruct IO2 as (J1 & J2 & J3 & J4). destruct IO3 as (K1 & K2 & K3 & K4). repeat split; congruence.
-
intros a Ha NO NO' NS NE. unfold W2. rewrite wrefund_H. img_apply AG; [img_try (img_exact Ha)|]. intros HD.
destruct (YF0y.D_owned B TB ly X rd M' k r o sm i Hk Hst Hb Hsm Hi sp0 HSP' IMG a (proj1 Ha) HD) as [O|O]; [img_try (img_exact (NO O)) | img_try (img_apply NS; unfold ascratch, spZ; left; img_exact O)].
-
intros a Ha. unfold spZ in Ha. fold sp0 in Ha. unfold W2. rewrite wrefund_H. img_apply PRS. img_exact Ha.
Qed.
Theorem FIN : forall regsD memD mat1 W' c', LINKD regsD memD ->
YF2q.at_RET W ly regsD memD MAP LEN idx nA qi lst vra vs0 vs1 vs2 own (munmap_model (w64 MAP) (w64 LEN) (with_vm_backing (m_vm_lazy md) mat1 md)) W' c' ->
rcc_leaf B ly X k W regs mem md (tt, X2v) W2 c'.
Proof.
intros regsD memD mat1 W' c' (LSP & LSR & LMEM & LPRES) HR.
pose proof PRE as PRE'. destruct PRE' as (HAR & Hci & _ & Hst & Hni & Hra & Hra4 & Hal & Hlo & Hcb1 & Hcb2 & Hcb3 & HPRES & HPRC & HVC & Hgp & Htp & Ha0 & Ha1).
destruct HAR as (M' & LED & BUD & MW & HSH). unfold spZ, raZ in *. fold sp0 in Hal, Hlo, Hcb1, HPRES.
pose proof MAP_facts as (P1 & P2 & P3 & INA & INV & _). pose proof LEN_facts as [L1 L2]. pose proof KFACTS as (Ho & _ & ELEN & _ & FP & INE).
destruct HR as (-> & regs' & mem' & mat & -> & CS & CSP & C8 & C9 & C18 & MEQ' & SHD' & PRS & PRS2 & VALS). cbv zeta in VALS.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
set (rd := aview tfxsegs (w_H W) mem) in *.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (img_try (unfold sp0; img_apply u64_range)).
assert (HSP' : ly_stk_lo ly + KSTACK <= sp0 <= ly_stk_hi ly) by (img_try (split; [img_try (img_exact Hlo) | img_try (clear - Hcb1 Hcb2; img_lia)])).
assert (EI : A_ALLOCATOR = as_inst B) by (img_try (rewrite (ts_inst _ TB); img_refl)).
assert (SPD : bv_unsigned (getr regsD 2) = sp0) by (img_try (rewrite LSP; img_refl)).
pose proof (YF0y.geom B ly X rd M' k r o Hk Hb IMG) as GEOM. cbv zeta in GEOM. fold MAP in GEOM.
assert (ELEN' : sec_map_size (ck_req k) = LEN) by (img_try (symmetry; img_exact ELEN)).
pose proof (YF0y.HIGH B TB ly X rd M' IMG) as HI. pose proof HI as (_ & _ & hQ1 & hQ2 & hT1 & hT2 & _ & _ & _ & _ & _ & _ & _ & _ & hS1 & hS2 & _ & _ & hI1 & hI2 & hCE & hEI). unfold zone3, zone3cases in hT1.
pose proof GEOM as (GZ & GM2 & GM3 & GM4 & _). pose proof GZ as (GM1 & _ & _).
pose proof (YF0y.ARR B ly X rd M' r i Hi) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
destruct (YF0y.LST B ly X rd M' k r o sm i Hk Hb Hsm Hi IMG) as (y2 & Hy2 & Ey2 & CI2 & Q1 & Q2 & Q3 & Q4 & Q5).
pose proof (YF0y.SX B ly X rd M' 1 2 _ _ eq_refl eq_refl ltac:(img_lia)) as DQT. pose proof (YF0y.SECX B ly X rd M' _ 2 _ CI2 eq_refl) as DLT.
pose proof (YF0y.MAPX B ly X rd M' k r o sm Hk Hb Hsm 2 _ eq_refl) as DMT. unfold zdisjoint in DQT, DLT, DMT. cbn [fst snd] in DQT, DLT, DMT.
assert (WD : forall a, 0 <= a < 2 ^ 64 -> (WPRE a \/ YF2q.WIN3 ly regsD MAP LEN qi lst a) -> YF0y.D B ly X k r i sp0 a).
{ intros a Ha HW. unfold YF0y.D, YF0y.DS, YF0y.DI, YF0y.DJ, YF0y.DQ, YF0y.DL, YF0y.DH, YF0y.DM.
unfold YF0y.own, YF0y.qi, YF0y.lst, YF0y.MAP, YF0y.LEN, YF0y.idx, YF0y.nA, YF0y.lastr, YF0y.arr.
rewrite ELEN'. fold MAP. rewrite <- EI. unfold shadow_addr.
unfold WPRE, YF2q.WIN3, YF2q.WIN2, YF2q.WIN, YF2q.WINS, YF2q.WINM, SHAv, CNTv, GDEPTH in HW. rewrite SPD in HW.
unfold own, qi, lst, idx, nA in *.
destruct (Z.eqb_spec (Z.of_nat i) (Z.of_nat (length (st_sec_arr X)) - 1)) as [EO|NEO].
-
assert (LR : last (st_sec_arr X) r = r) by (img_try (img_apply A8; unfold YF0y.own, YF0y.idx, YF0y.nA, YF0y.arr; img_apply Z.eqb_eq; img_exact EO)).
rewrite LR in HW. fold MAP in HW. unfold KSTACK.
lazymatch goal with |- ?A \/ ?Bq \/ ?C \/ ?Dq \/ (_ /\ _) \/ ?G =>
enough (G' : A \/ Bq \/ C \/ Dq \/ G) by (img_try (destruct G' as [?|[?|[?|[?|?]]]]; [img_try (left) | img_try (right; left) | img_try (do 2 right; left) | img_try (do 3 right; left) | img_try (do 5 right)]; assumption)) end.
clear - HW L1 Ha. img_lia.
- unfold KSTACK.
lazymatch goal with |- ?A \/ ?Bq \/ ?C \/ ?Dq \/ (_ /\ ?F) \/ ?G =>
enough (G' : A \/ Bq \/ C \/ Dq \/ F \/ G) by (img_try (destruct G' as [?|[?|[?|[?|[?|?]]]]]; [img_try (left) | img_try (right; left) | img_try (do 2 right; left) | img_try (do 3 right; left) | img_try (do 4 right; left; split; [img_refl | assumption]) | img_try (do 5 right)]; assumption)) end.
clear - HW L1 Ha. img_lia. }
img_apply (FIN_core regs' mem' md1 mat).
- split; [img_try (intros r' Hr'; rewrite (CS _ Hr'); img_exact (LSR _ Hr'))|].
split; [img_try (etransitivity; [img_exact CSP | img_exact LSP])|]. split; [img_try (img_exact C8)|]. split; [img_try (img_exact C9)|]. split; [img_try (img_exact C18)|].
split. {
intros x ND. rewrite (MEQ' x) by (img_try (intros HW; img_apply ND; img_apply WD; [img_try (img_apply u64_range) | img_try (right; img_exact HW)])).
img_apply LMEM. intros HW. img_apply ND. img_apply WD; [img_try (img_apply u64_range) | img_try (left; img_exact HW)]. }
split. { intros x Hx. img_apply SHD'. unfold YF2q.WINS. img_exact Hx. }
split. {
intros a Y. destruct (Z_lt_le_dec a (sp0 - GDEPTH)) as [LOW|HIGH'].
+ assert (Ha : 0 <= a < 2 ^ 64) by (img_try (clear - Y Usp HSP' hS1 hS2; unfold KSTACK in *; numconst_hi; img_lia)).
img_apply (apresent_same (w_H W) mem); [|img_try (img_apply HPRES; img_exact Y)].
rewrite (MEQ' (Z_to_bv 64 a)) by (img_try (unfold YF2q.WIN3, YF2q.WIN2, YF2q.WIN, YF2q.WINS, YF2q.WINM, SHAv, CNTv; rewrite unsigned_lit_small by img_exact Ha; rewrite SPD;
clear - Y LOW HSP' hS1 hCE hT2 hQ2 GM2 GM4 A4 A5 Q2 Q4 L1 ELEN'; unfold own, qi, lst, idx, nA, MAP, LEN, GDEPTH, KSTACK in *; numconst_hi; img_lia)).
img_apply LMEM. unfold WPRE. rewrite unsigned_lit_small by img_exact Ha. clear - Y LOW HSP' hS1 hCE hT2 hEI; unfold GDEPTH, KSTACK in *; numconst_hi; img_lia.
+ img_apply PRS. rewrite SPD. unfold GDEPTH in *. img_lia. }
split. {
intros a [Y|Y].
+ assert (Ha : 0 <= a < 2 ^ 64) by (img_try (clear - Y hT1; numconst_hi; img_lia)).
img_apply (apresent_same (w_H W) memD); [|img_try (img_exact (LPRES a Y))].
rewrite (MEQ' (Z_to_bv 64 a)) by (img_try (unfold YF2q.WIN3, YF2q.WIN2, YF2q.WIN, YF2q.WINS, YF2q.WINM, SHAv, CNTv; rewrite unsigned_lit_small by img_exact Ha; rewrite SPD;
clear - Y HSP' hT1 hCE GM1 GM2 GM4 A4 A5 Q4 L1 ELEN' DQT DLT DMT; unfold own, qi, lst, idx, nA, MAP, LEN, GDEPTH, KSTACK in *; numconst_hi; img_lia)).
img_refl.
+ img_apply PRS2. right. img_exact Y. }
split. { intros a Y. img_apply PRS2. left. img_exact Y. }
img_exact VALS.
- eapply ALedger_same; [img_try (img_exact LED) | img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_apply eager_used_wvb)].
- img_apply (amwf_same md md1); [img_try (img_apply m_vmmaps_wvb) | img_try (img_apply m_vm_lazy_wvb) | img_try (img_exact MW)].
- img_apply same_io_wvb'.
- (subst md1; cbv beta). rewrite m_vmmaps_wvb. img_exact INV.
Qed.
Theorem plumbing : amreal tfxsegs (recycle_chunk k X) W (cfg_at tfxsegs A_RChunk regs mem md) (rcc_leaf B ly X k W regs mem md).
Proof.
pose proof MAP_facts as (P1 & P2 & P3 & INA & INV & MW). pose proof LEN_facts as [L1 L2].
rewrite (recycle_chunk_sec k X r o sm i (proj2 (mem_chunk_spec _ _) Hk) Hb Hsm Hidx SMALL). cbn [amreal].
eapply SRr_bind; [img_try (img_exact WALK)|]. intros W1 c1 _ (regsD & memD & LNK & HM).
destruct HM as (-> & regs1 & mem1 & mat1 & -> & H17 & H10 & H11 & INNER). cbv zeta in INNER.
img_apply SRr_use_AI. cbn [cfg_model]. intros HAI. img_apply SRr_ret.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
set (c2 := mkCfg (mkst (regupd regs1 10 (w64 0)) (w64 (0x64c98 + D_2c4)) (unfill (w64 MAP) (w64 LEN) mem1) (seg_rom tfxsegs)) (munmap_model (w64 MAP) (w64 LEN) md1)).
assert (UM : bv_unsigned (w64 MAP) = MAP) by (img_try (unfold w64; img_apply unsigned_lit_small; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; img_lia)).
assert (UL : bv_unsigned (w64 LEN) = LEN) by (img_try (unfold w64; img_apply unsigned_lit_small; img_lia)).
assert (MW1 : amwf md1) by (img_try (img_apply (amwf_same md md1); [img_try ((subst md1; cbv beta); img_apply m_vmmaps_wvb) | img_try ((subst md1; cbv beta); img_apply m_vm_lazy_wvb) | img_try (img_exact MW)])).
assert (INV1 : In (w64 MAP, w64 LEN) (vm_maps (m_vmmaps md1))) by (img_try ((subst md1; cbv beta); rewrite m_vmmaps_wvb; img_exact INV)).
destruct (in_split _ _ INV1) as (l1 & l2 & EVM).
exists unit, (fun _ => c2), (fun _ => 1), (fun _ => false), tt.
split.
{ pose proof (munmap_node tfxsegs regs1 (w64 (0x64c94 + D_2c4)) mem1 (seg_rom tfxsegs) md1 (w64 MAP) LEN (AI_halted _ _ _ _ HAI) H17 H10
ltac:(img_try (rewrite UM; unfold page_size; img_exact P3)) H11 ltac:(img_lia)
ltac:(img_try (rewrite UM, (page_round_up_Z_aligned LEN) by img_lia; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, two_pow_64, TASK_SIZE, kHighMemBeg, ASAN_CEIL in *; img_lia))
ltac:(img_try (rewrite (page_round_up_Z_aligned LEN) by img_lia; img_exact (map_has_In _ _ _ INV1)))) as ND.
cbv zeta in ND. rewrite (page_round_up_Z_aligned LEN) in ND by img_lia. img_exact ND. }
split. { intros [] _. cbn [cfg_model]. img_exact (munmap_AI tfxsegs (w_H W) (w_A W) md1 (w64 MAP, w64 LEN) l1 l2 HAI MW1 EVM ltac:(img_try (cbn [fst]; rewrite UM; unfold page_size; img_exact P3))
ltac:(img_try (cbn [fst snd]; rewrite UM, UL; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; img_lia))). }
split. { intros []. cbn [aok]. img_refl. }
split; [img_refl|]. split; [img_refl|]. split; [img_try (intros XX; discriminate XX)|]. split; [img_try (intros [] XX; discriminate XX)|].
split; [img_try (intros [] [XX|XX]; [discriminate XX | exfalso; exact (XX eq_refl)])|].
intros [] _. cbn [Z.eqb Pos.eqb]. cbn [amreal].
eapply SRr_bind; [img_try (img_exact INNER)|]. intros W3 c3 _ HR. pose proof HR as (-> & regs' & mem' & mat' & Ec3 & _).
img_apply SRr_use_AI. intros HAI3. rewrite Ec3 in HAI3 |- *. cbn [cfg_model] in HAI3.
img_apply (SRr_world_le tfxsegs W W2).
{ img_apply wrefund_wle. }
{ intros _. cbn [cfg_model]. img_apply AI_refund_gen; [img_try (img_exact HAI3)|]. intros p Hp. rewrite m_vm_lazy_wvb in Hp. unfold iv. cbn [fst snd].
pose proof (munmap_lazy_out (w64 MAP) (w64 LEN) md1 p ltac:(img_try (destruct MW1 as [(_ & _ & W3l & _) _]; intros q Hq; img_exact (W3l q Hq)))
ltac:(img_try (rewrite UM, UL; ceil; unfold zone3, TFX_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; img_lia)) Hp) as NL. rewrite UM, UL in NL. img_exact NL. }
img_apply SRr_ret. rewrite <- Ec3. img_exact (FIN regsD memD mat1 W c3 LNK HR).
Qed.
End e.
End d.
