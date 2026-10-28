(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA StepF.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import ASecFacts AImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP ARepKit ARepFrame
AKit AKit2 AModelFacts AFreeModel AFreeModelR AFreeRep AFreeGeo AFreeRead ARefill_iface
F_apoison F_aalloc_s F_aalloc1 F_afree_tail F_afree_icpt F_aenqueueR F_afree_tailR F_afree_icptR F_afree_arep.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma ablocks_xbusy : forall L st st' X X' LB, x_busy X' = x_busy X -> a_live st' = a_live st -> ablocks L st X LB -> ablocks L st' X' LB.
Proof. intros L st st' X X' LB E EL AB. eapply ablocks_same; [exact AB| exact E| exact EL]. Qed.
Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Notation AHQ := (AHQ DI ASEC AFK).
Hypothesis HL : ahole_laws AHQ.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
/\ (snd iv <= 0x9f0f0 \/ 0x9f1b0 <= fst iv)
/\ (snd iv <= 0xa3680 \/ 0x1246b0 <= fst iv)
/\ (snd iv <= 0x131f08 \/ 0x131f0c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Definition AHQm (Q1 : qconc) : aholes := mkAHoles (fun L s X m => AQUAR_at L s X Q1 m) ASEC (ADEPOT DI) AFK.
#[using="HL"] Lemma AHQm_laws : forall Q1, ahole_laws (AHQm Q1).
Proof.
intros Q1. destruct HL as [HQF HSF HDF HFF HFB].
constructor; cbn [ah_quar ah_sec ah_depot ah_fake AHQm F_afree_arep.AHQ] in *; try assumption.
intros L st st' X X' m m' W AQ MU WM UT QS. exact (AQUAR_frame_at L st st' X X' Q1 m m' W AQ MU WM UT QS).
Qed.
Definition mid_stmt : Prop :=
forall (L : alayout) (RNG : footprint) (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (c k n b1 ctx A lo lst nx bsz : Z)
(hs : list word) (tr : list Z) (l1 l2 : list xbusy),
let st1 := set_live (delete p (a_live st)) st in
let X1 := xquar X c k n b1 ctx l1 l2 in
let Q1 := mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q) in
alayout_ok L -> arng L RNG st -> AREP AHQ L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
x_busy X = l1 ++ bfreed p c k n b1 ctx :: l2 -> In (HB p A n) LB -> 1 <= n ->
ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
forall ms1,
free_to_refill_post DI L full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n b1 ctx lo lst nx bsz hs tr m ms1 ->
AREP (AHQm Q1) L st1 X1 (ms_mem ms1)
/\ ablocks L st1 X1 (lb_remove p LB) /\ AFK L (lb_remove p LB) (ms_mem ms1)
/\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m (ms_mem ms1).
Definition store_freeR_stmt : Prop :=
forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : amem) (s : astate) (LB : list ablock) (X : aconc) (Q : qconc) (c k n b1 ctx lo k24 : Z)
(l1 l2 : list xbusy) (stj : word) (chunks : list word),
let ch := CPrim c n in
let sq := st_enq s ch in
let ek := ek_of L s X Q n k24 stj chunks in
let g := g_of L s Q (ek_delta ek n) in
alayout_ok L -> arng L RNG s -> AREP (AHQm Q) L s X m -> ablocks L s X LB -> AFK L LB m ->
x_busy X = l1 ++ bquar c k n b1 ctx :: l2 -> 1 <= n ->
(exists pend, q_pend Q = (c, k) :: pend) ->
enq_is_app s = false ->
nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls s K_BATCH_CLASS) - 1)) = Some k24 ->
busy_of X K_BATCH_CLASS k24 = None -> 0 <= k24 < ndist s K_BATCH_CLASS ->
~ In k24 (map qb_slot (q_loc Q ++ q_glob Q)) ->
junk_at m (abatch_addr L k24) 8192 -> fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa ->
a_cinit s = true -> 0 < c_count (get_cls s K_BATCH_CLASS) ->
(Q_CACHE < a_qloc_bytes sq -> a_qglob_bytes sq + a_qloc_bytes sq <= Q_MAX) ->
ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc s))) (qlast L (q_loc Q)) n (fhm L c k n) m ->
dk_pre ek g RNG (al_t L) (qlast L (q_loc Q)) (fhm L c k n) (a_qloc_bytes s + ek_delta ek n) m ->
ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
forall ms',
free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n
(Z.of_nat (length (a_qloc s))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes s) b1 ctx lo m ms' ->
exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ aheap_pres CI LB (bv_unsigned sp) m m'
/\ AHEAP_P AHQ L RNG (st_after sq) LB m'.
Hypothesis MID : mid_stmt.
Hypothesis STORE_R : store_freeR_stmt.
Hypothesis REFILL : forall Q1, refill_stmt (AHQm Q1).
#[using="Type"] Lemma busy_slot_range' : forall L st X b, awf L st X -> In b (x_busy X) ->
1 <= xb_class b < K_NUM_CLASSES /\ 0 <= xb_slot b < ndist st (xb_class b).
Proof.
intros L st X b WF Hb. pose proof WF as WF0. destruct WF0 as (_ & _ & _ & _ & _ & PERC & _ & BUSY & _).
destruct (BUSY b Hb) as [HC _]. split; [exact HC|].
destruct (PERC (xb_class b) HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RANGE).
apply RANGE. apply in_or_app. right. apply in_or_app. right. unfold busy_slots. apply in_map. apply List.filter_In.
split; [exact Hb| apply Z.eqb_refl].
Qed.
#[using="CI_OK CI_OK2"] Lemma aheap_pres_refill : forall L st X LB (sp : word) (sE lo : Z) m m',
alayout_ok L -> awf L st X -> ablocks L st X LB ->
munch (arefill_W L st K_BATCH_CLASS sE) m m' -> wmono asegs m m' ->
ATOP <= lo -> lo <= sE - 1536 -> sE <= bv_unsigned sp ->
aheap_pres CI LB (bv_unsigned sp) m m'.
Proof.
intros L st X LB sp sE lo m m' ALO WF BL MU WM CEIL LO SLE a Ha CL.
split; [| intros Hw; apply WM; exact Hw].
apply MU. rewrite wa_unsigned by exact Ha.
pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_space L ALO) as (SP1 & SP2 & _).
pose proof (ao_res L ALO) as RES. pose proof (ao_fake L ALO) as FKO. unfold aobj in RES, FKO. pose proof (ao_space L ALO) as RSP.
pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1, TL4, RES, FKO.
pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_res L ALO) as D_t_res. unfold adisj in D_t_f, D_f_res, D_t_res.
pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & _).
destruct (PERC K_BATCH_CLASS (K24)) as (A24a & A24b & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof (slot_geo L st X K_BATCH_CLASS 0 ALO WF (K24)) as SG0.
Local Ltac2 Set LiaHints.tbl := fun () => "00e0?1183713683.54  12658827346.22 12658827346.28 12658827346.30 12658827346.33 12658827346.35 14420195635.10 15574476147.13323857893116.23 23859989372.42 26128101929.22 26128101929.28 26128101929.30 26128101929.33 26128101929.35 26466751818.15 2685960337.20  26958991508.20 31685377474.22 31685377474.28 31685377474.30 31685377474.33 31685377474.35 33194120991.20 34710718778.22 34710718778.28 34710718778.30 34710718778.33 34710718778.35 35746654875.20 37903709739.7  40461571878.10 40463821211.5  425966277.22   425966277.28   425966277.30   425966277.33   425966277.35   42656430687.4  46542661272.20 53238998938.2  54758582002.15 56848492733.20 61587208202.22 61587208202.28 61587208202.30 61587208202.33 61587208202.35 63771665232.55 63970516581.13 63970516581.14 66151427842.16 8129703265.1   00000100J00^01701b02I02]04304R05A05I05Y05o06K06a06n07207607J07Z08008O09009<09T09b0:00:U0;60;H0;Q0;c0;l0<>0<D0<R0<d0=:0=A0=O0=T0=c0=n0>E0>P0>c0?L0@70@80@E0@V0@f0@gSS2ST3SLE2LO4CEIL3SP24ER24S1R2Q33SP14ER244A24aS1R3FIT3SL53SP14ER244A24aS1R2K12K33FKO7D_f_res3RES3RSP3SP14ER244A24aS1R3Gs43Gs52SF2Cr3RES3RSP3SP14ER244A24aS2RS2P23Ac13Ac24A24aS3TL13RES3FKO3RHI5D_t_f7D_f_res7D_t_res3SAL3SLO4ER242RM2Hx1H2H02H93H293H303H313H323H33S1R2Q33SP14ER244A24a1H2H02H42H5S1D1R2K33RSP4ER244A24a2RM3MM81H2H02H42H52H93H14S2ST3SLES1R2Q32LO4CEIL1HS1R3FIT2P62LO4CEIL3SP2S1R2K33FKO3RES2LO4CEIL3TL21HS1R3Gs33Gs42SF2LO4CEILS3SP21H2H02H4S2B1S2B2S2ST3SLE2LO4CEIL3TL2S1R2Q12Q32Q73TL4S1R3FIT2P52BT3SP14ER24S1R2K12K33FKO5D_t_f3RES3RHI3TL1S1R3Gs23Gs43Gs52SF2Ct3RES3RHI3TL1S2B33SP13ERIS2ST3SLE2LO4CEIL3SP23ERIS1R2Q33SP13ERIS1R3FIT2P63ERIS1R2K12K33FKO7D_f_res3RES3RSP3SP13ERIS1R3Gs43Gs52SF2Cr3RES3RSP3SP13ERIS2B33SP14ER244A24aS2P24A24aS2ST1H1R2K12K33FKOS1R2Q12Q3S2ST3SLE2LO4CEIL1HS1R2Q7S1R3FIT2P53SP1S1R2K13FKO3RES3RHIS1R3Gs23Gs52SF3RES3RHIS2RS2P1S2B32LO4CEIL1HS3Gs5S3SP14A24a1H2H0S2B22B33TL1S2ST3SLE2LO4CEIL4W6HI1HS1R2Q34W6LOS1R3FIT2P53SP14W6HIS1R2K12K33FKO5D_t_f3RES3RHI3TL14W6LO4W6HIS1R3Gs23Gs43Gs52SF2Ct3RES3RHI3TL14W6LO4W6HISS2ST3SP24ER24S1D1R2K13RSP4ER24S3MU81H2H02H42RMS".
assert (ERI : aregion_info L K_BATCH_CLASS = al_space_beg L + 137438953472 + 3072) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE, K_BATCH_CLASS; lia).
assert (ER24 : aregion L K_BATCH_CLASS = al_space_beg L + 24 * 4294967296) by (unfold aregion, K_REGION, K_BATCH_CLASS; lia).
pose proof (aregion_mod L K_BATCH_CLASS SAL) as RM.
assert (MM8 : c_mapped_user (get_cls st K_BATCH_CLASS) mod 8 = 0).
{ destruct (PERC K_BATCH_CLASS (K24)) as (_ & _ & _ & MU8 & _). generalize MU8; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia. }
assert (W6B : 0x2008fff7000 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
/\ shad (aregion L K_BATCH_CLASS) + shlen K_REGION = shad (aregion L K_BATCH_CLASS + K_REGION)
/\ shad (aregion L K_BATCH_CLASS + K_REGION) <= 0x10007fff8000).
{ split; [| split; [symmetry; apply shad_add_shlen; generalize RM; clear; intros; Z.div_mod_to_equations; lia|]];
rewrite !shad_div; unfold ASHOFF, K_REGION; rewrite ER24; generalize SP1 SP2 A24a A24b; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF;
change (2^37) with 137438953472; change (2^32) with 4294967296; intros; Z.div_mod_to_equations; lia. }
destruct W6B as (W6LO & W6E & W6HI). rewrite W6E.
unfold AIMG_HI, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
eapply (disjoint_outside _ a 1); [| clear; lia].
cbn [disjoint_from fst snd]. unfold AINSTANCE.
destruct CL as [ST | [CIa | [BLK | SH]]].
- generalize ST SLE LO CEIL TL1 TL2 SP1 SP2 ERI ER24 A24a A24b W6LO W6HI; clear; intros; repeat split; lia.
-
destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q7. cbn [fst snd] in *. unfold AINSTANCE, AIMG_HI in *.
generalize R Q1 Q3 Q7 SLE LO CEIL TL1 TL2 TL4 SP1 SP2 RHI ERI ER24 A24a A24b W6LO W6HI; clear; intros; repeat split; lia.
-
destruct BLK as ([[q|cls] A' n'] & Hin & R); cbn [ab_addr ab_size] in R.
+ destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
* destruct (busy_slot_range' L st X b WF Hb) as [HCb HKb].
pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
unfold xb_user, xb_alloc in Ub. subst A' n'.
pose proof (slot_geo L st X (xb_class b) (xb_slot b) ALO WF HCb HKb) as (_ & _ & _ & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
pose proof (slot_sep_objects L st X (xb_class b) (xb_slot b) ALO WF HCb HKb) as (BT & _).
assert (SL5 : aslot_addr L (xb_class b) (xb_slot b) + size_of_class (xb_class b) <= aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS)
\/ aregion L K_BATCH_CLASS + 4294967296 <= aslot_addr L (xb_class b) (xb_slot b)).
{ destruct (PERC (xb_class b) HCb) as (Ac1 & Ac2 & _).
destruct (Z.lt_trichotomy (xb_class b) K_BATCH_CLASS) as [LT|[E24|GT]].
- left. pose proof (regions_sep L (xb_class b) K_BATCH_CLASS LT) as RS. generalize RS P2 P3 Ac1 Ac2 A24a A24b. clear. unfold K_REGION. change (2^32) with 4294967296. intros. lia.
- left. generalize P2 P3 A24a A24b. rewrite E24. clear. intros. lia.
- right. pose proof (regions_sep L K_BATCH_CLASS (xb_class b) GT) as RS. generalize RS P1. clear. unfold K_REGION. change (2^32) with 4294967296. intros. lia. }
unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
generalize R FIT P5 P6 P7 P8 BT SL5 SLE LO CEIL TL1 TL2 SP1 SP2 ERI ER24 A24a A24b W6LO W6HI; clear; intros; repeat split; lia.
*
cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
unfold ablk, KLS, AIMG_HI in Gs2.
generalize R Gs2 Gs3 Gs4 Gs5 SF Ct Cr RES RHI RSP SLE LO CEIL TL1 TL2 SP1 SP2 ERI ER24 A24a A24b W6LO W6HI; clear; intros; repeat split; lia.
+ destruct (proj1 (proj2 BL) cls A' n' Hin) as (K1 & K2 & K3).
generalize R K1 K2 K3 FKO D_t_f D_f_res RES RHI RSP SLE LO CEIL TL1 TL2 SP1 SP2 ERI ER24 A24a A24b W6LO W6HI; clear; intros; repeat split; lia.
-
destruct SH as (a' & Ha' & ->).
assert (SHI' : forall x, 0 <= x < 2^47 -> 0x7fff8000 <= shad x /\ shad x + 1 <= 0x10007fff8000) by (intros x Hx; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
destruct Ha' as [ST | [CIa | FK]].
+
atop_facts.
assert (B1 : shad (aregion L K_BATCH_CLASS + 4294967296) <= shad a') by (apply shad_mono; generalize ST SLE LO CEIL SP2 ER24; clear; intros; lia).
destruct (SHI' a' ltac:(generalize ST SLE LO CEIL; clear; intros; lia)) as [B2 B3].
generalize B1 B2 B3 TL1 SP1 ERI ER24 A24a SLE LO CEIL W6LO; clear; intros; repeat split; lia.
+ destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3 & _). cbn [fst snd] in *. unfold AIMG_HI in *.
assert (B1 : shad a' + 1 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))).
{ rewrite !shad_div. generalize R Q3 SP1 ER24 A24a; clear; intros; Z.div_mod_to_equations; lia. }
destruct (SHI' a' ltac:(generalize R Q1 Q3; clear; intros; lia)) as [B2 B3].
generalize B1 B2 B3 TL1 SP1 ERI ER24 A24a SLE LO CEIL W6LO; clear; intros; repeat split; lia.
+ destruct FK as (cls & FA & sz & Hin & R). destruct (proj1 (proj2 BL) cls FA sz Hin) as (K1 & K2 & K3).
assert (B1 : shad a' + 1 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
\/ shad (aregion L K_BATCH_CLASS + 4294967296) <= shad a').
{ destruct D_f_res as [D|D].
- left. rewrite !shad_div. generalize D R K1 K3 RSP ER24 A24a RM MM8; clear; intros; Z.div_mod_to_equations; lia.
- right. apply shad_mono. generalize D R K1 K3 RSP RES SP2 ER24; clear; intros; lia. }
destruct (SHI' a' ltac:(generalize R K1 K3 FKO; clear; intros; lia)) as [B2 B3].
generalize B1 B2 B3 TL1 SP1 ERI ER24 A24a SLE LO CEIL W6LO; clear; intros; repeat split; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="HL CI_OK CI_OK2 MID STORE_R REFILL"] Theorem afree_refill : forall (L : alayout) (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (c : Z),
(a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
enq_is_app st = false -> c_count (get_cls st K_BATCH_CLASS) = 0 ->
(Q_CACHE < a_qloc_bytes st + (n + 8192) -> a_qglob_bytes st + (a_qloc_bytes st + (n + 8192)) <= Q_MAX) ->
AHEAP_P AHQ L RNG st LB m -> In (HB p A n) LB ->
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
tp = Z_to_bv 64 ATP ->
a0 = Z_to_bv 64 A ->
aunw m L RNG lo AFREE_PC sp s0 ra tr ->
bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
bv_unsigned sp mod 16 = 0 ->
rng RNG lo (bv_unsigned sp - lo) ->
implS asegs RNG (aembed ATOP (afree st (Some p)))
(epostF (afree_post CI (AHEAP_P AHQ) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
intros until c. intros LIVE N1 EA CNT0 NOREC AH HIN MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
{ destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
destruct UNWX as (trt & FUNW & TRU).
set (st1 := set_live (delete p (a_live st)) st).
destruct AH as (ALO & ARNG & [X [AR BL]] & HFK).
pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & HRT2 & AVL & RT3).
cbn [ah_quar ah_sec ah_depot F_afree_arep.AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].
pose proof BL as BL0. destruct BL0 as (BH & _).
pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVEB & FRESH & UNIQ).
destruct (BH p A n HIN) as [(y & Hy & Sy & Uy & Ny)|(mb & msz & Lp & _)]; [| exfalso; rewrite LIVE in Lp; discriminate].
destruct (BUSY y Hy) as [CLy My]. rewrite Sy in My. destruct My as (_ & _ & _ & _ & _ & M5). rewrite LIVE in M5.
injection M5 as Cy Ny'. clear Ny'.
destruct (in_split _ _ Hy) as (l1 & l2 & XB).
destruct y as [yc yk yn yst yb1 yctx]. cbn in Sy, Uy, Ny, Cy, CLy. subst yst yn yc.
rename yk into k. rename yb1 into b1. rename yctx into ctx.
change ({| xb_class := c; xb_slot := k; xb_n := n; xb_st := BLive p; xb_b1 := b1; xb_ctx := ctx |}) with (bfreed p c k n b1 ctx) in XB.
unfold xb_user, xb_alloc in Uy. cbn [xb_class xb_slot xb_n] in Uy.
destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as (_ & N0 & FIT0 & B10 & AT0 & CTX0).
pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (HM16 & UB16 & ABUB & ABHM & HLO & UBS & ABCE & HHI & N65 & NQM & ABLO & RUP & RUP8 & S8).
pose proof (slot_sep_objects L st X c k ALO WF HC KR) as (DT & DC & DN & DSO & DF).
destruct (slot_rng L st X c k ALO WF HC KR RNG ARNG) as [RSL RSS].
pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDT & RCLS & RPA & RSECS & RPSH).
pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (SE & G2 & GE & G0 & GFS & SHLO & SHHI & _).
pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.
pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).
set (AB := aslot_addr L c k) in *. set (UB := AB + rz_size n) in *.
Local Ltac2 Set LiaHints.tbl := fun () => "02S0?10317641044.55 1047820382.55  11745168637.34 1176603551.55  1183713683.391 12079996060.1  12132607597.8  12315131949.87 1241734689.2   13031118019.87 13212736933.87 13339528318.24 13339528318.26 13339528318.37 13911963429.9  13913996220.3  14082025517.87 14330016302.87 14623762917.87 15261595693.87 156175311.55   15887217069.87 16329056878.87 1685717371.0   17004507337.0  17986879152.6  19033156465.55 19180513865.0  19289104452.55 19512710711.87 19529692878.34 20615423388.1  22298099863.87 2355938998.239 23592147986.55 23594146463.3  2389686922.368 24215381656.55 24491041186.3  25075438297.87 25174793952.4  25285276718.87 25786868973.87 25911213742.87 26508081303.6  27240989092.2  28286778042.12 28290036197.87 29810849779.27729810849779.49929810849779.55 30069777748.6  30543647586.87 30719730331.45130873323561.0  31027678055.55 31716486433.23031732222821.87 31876270974.87 32263333265.87 32289360468.24 32289360468.26 32289360468.37 32613601186.87 33669152803.9  33669186341.17 34498998706.87 36078469081.56 3620815406.87  3711592090.9   3713784609.55  37291296152.87 37415255660.56 37801351095.87 37864197951.9  38242491404.9  38931646788.87 3918647937.1   39346223692.2  39668881180.1  40910236855.87 42064432165.87 42093861872.34 42516103219.0  42531779165.87 42596913235.27742596913235.49942596913235.55 42781866378.34 43078836633.0  43886324944.9  44437157366.1  4588927050.6   4595006784.277 46485083121.29 46489507895.87 4671481253.87  46768195959.87 47429192258.87 48152420000.9  49131994466.87 49715208489.0  5007213918.87  50913041728.55 5099596343.87  52432642853.87 53463547985.55 53512866218.27553733023829.87 54040317349.87 5414831378.17  54466317674.53 54969794426.55 55483203454.24 55483203454.26 55483203454.37 56023370143.42356375006430.27856851783752.1  57148469895.24 57148469895.26 57148469895.37 58143615587.17 58457718618.34 58462618912.4  58512664418.87 58520610802.55 58524739064.2  60244011164.1  61662043918.36161662043918.9  61995864802.87 62689745923.87 62894365541.87 6289768185.87  63368325748.2  63374621462.42163459279349.87 63771665232.39263798280914.11 64324852998.11 6507725776.55  65504523926.41965976979734.56 66115153114.24 66115153114.26 66115153114.37 66151427713.18 66151427842.16 66151427842.21 66260016006.4046637867901.87  6742910577.34  6859907429.9   6963065448.5   7088077112.191 7313457419.24  7313457419.26  7313457419.37  7349454695.7   8327838599.87  85311973.87    9532457909.12  00000600;00G00O00h00i01201;01?02O02]03203D03i03m04104:04@04O04X04a04j05005105205705D05E05I05V06006107E07N07V07^08708808<08Q08Z08`08i08o09609:09O09^09k0:M0:N0:U0:V0;20;30;@0;A0;P0;V0<o0=?0=K0=n0=o0>00>10>20><0>B0>H0>N0>[0>c0?00?:0?;0@O0@P0@T0@U0BX0Bf0CC0CD0D?0DK0Dl0Dm0EE0EF0EG0EH0EI0ER0F60FC0FQ0F^0HH0HP0HQ0HR0H_0H`0Hm0I<0ID0IM0I\0Ij0J90JO0JW0Jk0K70KF0K_0L80L90LL0LU0La0Lg0ME0MO0MP0MU0MZ0M[0NJ0NY0NZ0PP0P^0RU0RV0Ro0S=0SV0S_0Sh0T:0TS0U70U;0UI0U`0Um0V90VG0W@0WI0WT0W[0Wg0Wh0X60X:0XA0XF0XS0Xb0Y3S4STK1S3CL2S4SHLO2SE2G2S2N13NQMS3LSJ3LCH4LSJ14LTB15NEXTrSS3HLO3EHMS3SP13ERIS2G0S3TL24TL1u3SP14ER244A24a3FKO3DTO7D_d_res5D_t_d3RES3RHI3RSP1H2H02H42H52H93H103H39S4TL4u3FKO3RESS2H12LO4CEIL3SP24ER24S2H23SP14ER244A24aS2H12H22H34TL1u3SP14ER244A24a3SL53UBSS2LOS2LOS3SP13ERIS4W6LOS3SP14ER244A24aS3SP13ERIS4ABCE2S8S3SP13ERIS4W6LOSSS3BOTS2LO3BOT4STK3SS2S8S2LO4CEIL3H39S2LO4CEIL4SHHI2SE2GE3GFS1HSS3TL24TL1u3SP13ERI4ER244A24b3FKO3DTO7D_d_res5D_t_d3RES3RHI3RSP1H2H02H42H52H93H103H39S3LSJ3LCHS3LLB2NCS3LLB2NCS3LSJ3LCH4LSJ14LTB15NEXTrSS2HiS3FKO5D_t_f3RES5D_t_dS5NOREC1HS4W6LOS3SP13ERIS4W6LOS2RS2G1S2HjS2RS3G2'3Ac13Ac24A24aS3SP14ER244A24aS3LSJ3GFS3LCHS3LSJ3GFS3LCH4LTB15NEXTr4LSJr4LCHrFS1D3RSPSS2N13LSJ3LCH4LTB15NEXTr4LSJrSS4ABCE2S83EHMSS3SP14ER244A24aS4W6LOS4TL1u3SP14ER244A24a3FKO3DTO7D_f_res5D_t_f7D_d_res5D_t_d3RES3RHI3RSP1H2H03H143H153H193H20S2H12LO4CEIL3TL2S2H12H24TL4uS2H12H22H34TL1u3SP14ER243DT'2G73UBSSSSSS4ABHM3EHMS4W6LOS4ABUBS4ABUBS3FKO3RES3SHFS2S83EHMS2LO4CEIL3H39S3G2'4A24aSS4TL1u3SP14ER243FKO3DTO7D_f_res5D_t_f7D_d_res5D_t_d3RES3RHI1H2H03H143H153H193H203H34SS2HjSS2LO4CEIL3TL24TL1u4TL4u4ER244A24b3FKO3DTO7D_f_res5D_t_f7D_d_res5D_t_d3RES3RHI3RSP1H2H02H42H52H93H103H343H393SP13SHF3H143H153H193H20S4TL4u3FKO3RESS4TL1u4SHLO4SHHI2SE2GE3GFS2G2SS2LO4CEIL3TL24TL1u3FKO3DTO7D_d_res5D_t_d3RES1H2H02H42H53H39S3LSJ2G23LCHS3LSJ2G23LCH4LTB15NEXTr4LSJr4LCHrFS3SP13ERI4SHHI2SE2GE3GFSSSSSS3LSJ3LCHS3SP13SP24A24a1H2H02H42H52H93H103H14S2LO4CEIL3H39S4TL4u3FKO3RESS2LO4CEIL3H39S3TL24TL1u3SP13SP24ER244A24a3FKO3DTO7D_f_res5D_t_f7D_d_res5D_t_d3RES3RHI3RSP1H2H02H42H52H93H103H143H153H39S3RUP2N1SSS3FKO3RES3DTOFS2LO4CEIL3H39S3SP14ER244A24aS3N652NCS3LSJ3LCHS3SP14ER244A24aS4TL4u3FKO3RESS3RUP4RUP82N11HS2N14HM163HLO3RUP4RUP8S4STK31HS2H12LO4CEIL3SP23ERIS2H23SP13ERIS2H23ERI2G63UBSS3LSJ3LCH4LTB15NEXTr4LSJrS3LSJ3SLO3HLO3LCH2B02B11HSS2H12LO4CEIL4W6HI1HS2H24W6LOS2H14W6HI2G7S4ABUBS3SP14ER244A24a4SHHI2SE2GE3GFSS6NORECr1HSS3LLBS3LLBSS3BOT2LO3LSJ3SLO3HLO4SP473LCH4LSJ14LTB15NEXTr1HS3BOT2LO4SP471HSS4TL1u3SP13SP24ER244A24b3FKO3DTO7D_f_res5D_t_f7D_d_res5D_t_d3RES3RHI3RSP3SHF1H2H02H42H52H93H103H143H153H193H203H343H39S4TL4u3FKO3RESS4TL1u4TL4u3SP13ERI4ER244A24b3FKO3DTO7D_f_res5D_t_f7D_d_res5D_t_d3RES3RHI3RSP1H2H02H42H52H93H103H343SHF3H143H153H193H20SS3LSJ3LCH4LTB15NEXTr4LSJrS4TL4u3FKO3RESS3LSJ3LCH4LSJ14LTB15NEXTrS3HLO3HHIS3HLO3HHIS4STK14STK24STK31HS3LSJ3LCH4LTB15NEXTr4LSJrS1Y2N14HM163HLO4ABHM2S83RUP4RUP83TL3S2H1S2H22LO4CEIL1HS2H22LO4CEIL3SP22G63UBSS3FKO1H2H02H4S2RM1H2H02H4S4UB161H2H02H4S3LSJ3SLO3HLO4ABLO2S83LCH4LTB15NEXTr3S163G2'2G33SPR2Hj2HiS3SP13ERIS3SL62SE2G2S1D3UBSS1D3RSP4A24aSS2H12LO4CEIL1HS2H1S2H12G7S3EHMS2LO4CEIL3H39S3SP14ER244A24aS3DT23EHM2S84ABUB".
assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; lia).
pose proof RT as RT0.
destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
& PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
destruct (CACHES K_BATCH_CLASS (K24)) as [tail (CR & CH & LCH)].
replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR by (unfold acache_addr, K_BATCH_CLASS; lia).
rewrite CNT0 in CR.
destruct (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC))))))
as (HDR & [uw HUW] & UJR & LH & SHA & SHU & SHR).
fold AB in HDR, HUW, UJR, LH, SHA, SHU, SHR. fold UB in HDR, HUW, UJR, LH, SHU, SHR.
pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GCQ ABG] & (FL & IAS & IAM) & CP & NUM).
destruct NUM as (NB1 & NB2 & NF & NC & NM).
pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.
pose proof (read_last AHQ L st X Q m RNG (BLive p) c k n b1 ctx l1 l2 ALO ARNG AR AQ XB ltac:(discriminate) EA) as (FULL & DTL & DHL & DNL & DSL & LST64).
cbv zeta in FULL.
set (full := match a_qloc st with [] => false | _ :: _ => true end) in *.
set (lst := qlast L (q_loc Q)) in *.
set (bsz := b_size (List.last (a_qloc st) dummy_batch)) in *.
set (hs := map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb)))) in *.
assert (FULL' : if full then 0 < Z.of_nat (length (a_qloc st)) /\ rw_cells asegs m lst [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
/\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
else Z.of_nat (length (a_qloc st)) = 0 /\ lst = 0).
{ destruct full; [| exact FULL]. destruct FULL as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _). repeat (split; [assumption|]). exact F7. }
rewrite (afree_refill_eq st p (CPrim c n) LIVE ltac:(cbn [chunk_size]; exact NQM) EA CNT0). fold st1.
idtac "CHECKPOINT-A".
assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
{ intros q Hq. pose proof (bslot_geo L st X ALO WF (qb_slot q) (bslot_range L st X Q WF CP q Hq)) as (B0 & B1 & _). atop_facts. lia. }
assert (LF64 : 0 <= qfirst L (q_loc Q) < 2^64).
{ destruct (qfirst_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
assert (CEIL : ATOP <= lo) by (generalize BOT STK3; clear; intros; lia).
unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE in *.
box DT. box DC. box DN. box DSO. box DF. box CL5. box DL7. box DL8. box DL9. box DL10. box DTL. box DHL. box DNL. box DSL.
eapply implF_evtF.
{ eapply (free_to_refill_spec DI L (q_ia Q) full RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
(al_t L) (al_ctx L) (fhm L c k n) n b1 ctx lo (al_top L) (al_bot L)
(Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) lst (a_qloc_bytes st) 0 bsz uw _ _ sj hs (block_shadow_bytes n) trt).
all: rewrite ?EHM.
all: try lazymatch goal with
| |- stk _ _ _ _ => first [exact ST | exact IAS]
| |- ablk _ (_ + 16 + rup _ 8) => first [assumption | unfold ablk; right; generalize HLO HHI; try generalize EHM; clear; unfold fhm; intros; lia]
| |- mem_inv _ _ => exact MI
| |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
| |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
| |- ADEPOT _ _ _ => exact HD
| |- afree_unw _ _ _ _ _ _ => exact FUNW
| |- In _ _ => exact TRU
| |- u64arr _ _ _ _ => exact STATS
| |- if _ then _ else _ => exact FULL'
| |- _ = true -> _ => exact IAM
| |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HDR
| |- rw_cells _ _ (shad _) _ => eapply rw_cells_addr_eq; [exact SHU| f_equal; lia]
| |- rw_cells _ _ (_ + 80) _ => exact QC
| |- rw_cells _ _ (_ + 2128) _ => exact CR
| |- rw_cells _ _ (_ - 16 + 16) [C8 _] => eapply rw_cells_addr_eq; [exact HUW| lia]
end.
all: try lazymatch goal with
| |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
| |- rw_cells _ _ _ _ => assumption
| |- @eq word _ _ => first [exact TP | rewrite Ha0, <- Uy; subst AB UB; apply Z_to_bv_eqm; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia] | reflexivity]
| |- _ \/ _ => first [unboxed DT | unboxed DC | unboxed DN | unboxed DSO | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10
| unboxed DTL | unboxed DHL | unboxed DNL | unboxed DSL
| ub DT; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DC; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DN; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DSO; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DTL; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DHL; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DNL; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DSL; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia)
| ub DT; lia | ub DC; lia | ub DN; lia | ub DSO; lia | ub DTL; lia | ub DHL; lia | ub DNL; lia | ub DSL; lia]
| |- rng _ (shad _) _ => replace (UB - 16 + 16) with UB by (clear; lia); eapply rng_sub; [exact RSS| rewrite SE; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]| rewrite SE, GE; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]]
| |- rng _ _ _ => first [assumption | eapply rng_sub; [exact RSL| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia)| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia)] | eapply rng_sub; [exact RCTX| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia)| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia)] | eapply rng_sub; [exact RSL| lia| lia] | eapply rng_sub; [exact RCTX| lia| lia] | solve_rng]
end.
all: try assumption.
all: unfold AIMG_HI, Q_MAX, Q_CACHE, Q_BATCH_BYTES, UDEPTH in *.
all: try (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia).
all: match goal with |- ?G => idtac "REMF" G end. }
cbv beta. intros ms1 PTR.
pose proof (MID L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p c k n b1 ctx A lo lst 0 bsz hs trt l1 l2
ALO ARNG AR AQ BL HFK XB HIN N1 CEIL LO ms1) as MIDI.
rewrite EHM in MIDI. specialize (MIDI PTR). destruct MIDI as (ARm & BLm & FKm & HPm).
unfold free_to_refill_post in PTR.
destruct PTR as (id & t0a & t1a & t2a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & sj1 & tb1 & junk2 & j0
& -> & MUf & WMf & MIf & STf & IDR & HD1 & FC1 & SH1 & STATS1 & LSJ1 & UW1 & FL1 & IAS1 & IAM1 & SS1 & TB1 & LTB1 & FRS1 & FRP1 & FRE1 & LBS1 & DEP1).
cbn [ms_mem MS] in ARm, FKm, HPm.
idtac "CHECKPOINT-B".
set (Q1 := mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q)) in *.
set (X1 := xquar X c k n b1 ctx l1 l2) in *.
eapply (REFILL Q1 _ (KB (CPrim c n)) _ L RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 st1 X1 K_BATCH_CLASS lo).
all: try lazymatch goal with
| |- alayout_ok _ => exact ALO
| |- arng _ _ _ =>
apply (arng_st L RNG st st1); [intros; reflexivity| reflexivity| apply (sec_chunks_free st p c n); [exact LIVE| reflexivity| apply Permutation_refl]| exact ARNG]
| |- AREP _ _ _ _ _ => exact ARm
| |- mem_inv _ _ => exact MIf
| |- stk _ _ _ _ => rewrite unsigned_lit by (first [clear -SP47 LO BOT STK3; lia | lia]); exact STf
| |- @eq word _ _ => first [exact TP | reflexivity | unfold acache_addr, K_BATCH_CLASS; apply Z_to_bv_eqm; first [clear; lia | lia] | unfold AINSTANCE; reflexivity]
| |- _ <= K_BATCH_CLASS < _ => exact (K24)
| |- c_count _ = 0 => exact CNT0
| |- _ <= _ => first [exact CEIL | rewrite ?unsigned_lit by (first [clear -SP47 LO BOT STK3; lia | lia]); first [clear -SP47 LO BOT STK3; lia | lia]]
| |- rng _ _ _ => rewrite unsigned_lit by (first [clear -SP47 LO BOT STK3; lia | lia]); eapply rng_sub; [exact RSTK| first [clear -SP47 LO BOT STK3; lia | lia]| first [clear -SP47 LO BOT STK3; lia | lia]]
end.
all: match goal with |- forall _ _ _ _, refill_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => idtac | |- ?G => idtac "REMR" G end.
intros st_r X' RNG' ms' RR. unfold refill_ret in RR.
destruct RR as (FPLE & t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m' & -> & MUr & WMr & MIr & STr & ARr & ARNGr
& CINr & CNTr & MAXr & XBr & XCr & LIVEr & NEXTr & QLr & QBr & QGr & QGBr & NSECr & NRESr & GCr).
rewrite ?unsigned_lit in MUr by lia. rewrite ?unsigned_lit in STr by lia.
idtac "CHECKPOINT-C".
assert (EAr : enq_is_app st_r = false) by (unfold enq_is_app; rewrite QLr; exact EA).
pose proof (enq_new_core (CPrim c n) st_r) as (_ & NG1 & NG2 & _ & NL1 & NL2 & _). cbn [chunk_size] in NL1, NL2.
assert (ENr : st_enq st_r (CPrim c n) = enq_new st_r (CPrim c n)).
{ unfold st_enq. destruct (enq_app st_r (CPrim c n)) as [s'|] eqn:E; [| reflexivity]. exfalso.
assert (EA1 : enq_is_app st_r = true) by (apply (proj2 (enq_is_app_spec st_r (CPrim c n))); eexists; exact E). congruence. }
assert (NORECr : Q_CACHE < a_qloc_bytes (st_enq st_r (CPrim c n)) -> a_qglob_bytes (st_enq st_r (CPrim c n)) + a_qloc_bytes (st_enq st_r (CPrim c n)) <= Q_MAX).
{ rewrite ENr, NG2, NL2, QBr, QGBr. change (a_qloc_bytes st1) with (a_qloc_bytes st). change (a_qglob_bytes st1) with (a_qglob_bytes st).
unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES. generalize NOREC; clear; intros; lia. }
rewrite (KB_apop_eq st_r (CPrim c n) EAr NORECr).
apply implS_ret.
replace (ret_pc (Z_to_bv 64 0x368a0)) with (Z_to_bv 64 0x368a0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
pose proof (slot_geo L st X c k ALO WF HC KR) as (S16 & SM16 & AL16 & G1 & G2' & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8). fold AB in AL16, G1, G2', G5, G6, G7, G8.
pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
pose proof (ad_t_res L ALO) as D_t_res. unfold adisj in D_t_res.
pose proof (ao_res L ALO) as RES. unfold aobj in RES. pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in RES. pose proof (ao_space L ALO) as RSP.
destruct (PERC K_BATCH_CLASS (K24)) as (A24a & A24b & _).
assert (ERI : aregion_info L K_BATCH_CLASS = al_space_beg L + 137438953472 + 3072) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE, K_BATCH_CLASS; lia).
assert (ER24 : aregion L K_BATCH_CLASS = al_space_beg L + 24 * 4294967296) by (unfold aregion, K_REGION, K_BATCH_CLASS; lia).
assert (SLW5 : AB + size_of_class c <= aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS) \/ aregion L K_BATCH_CLASS + K_REGION <= AB).
{ destruct (PERC c HC) as (Ac1 & Ac2 & _).
destruct (Z.lt_trichotomy c K_BATCH_CLASS) as [LT|[E24|GT]].
- left. pose proof (regions_sep L c K_BATCH_CLASS LT) as RS. generalize RS G2' G3 Ac1 Ac2 A24a A24b. clear. unfold K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296. intros. lia.
- left. generalize G2' G3 A24a A24b. rewrite E24. clear. intros. lia.
- right. pose proof (regions_sep L K_BATCH_CLASS c GT) as RS. generalize RS G1. clear. intros. lia. }
assert (UB8 : UB mod 8 = 0) by (generalize UB16; clear; intros; Z.div_mod_to_equations; lia).
assert (SLW6 : shad UB + shlen (rup n 8) <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
\/ shad (aregion L K_BATCH_CLASS) + shlen K_REGION <= shad AB).
{ pose proof (aregion_mod L K_BATCH_CLASS SAL) as RM. destruct SLW5 as [D|D].
- left. apply shad_sep; [| exact UB8]. generalize D UBS; clear; intros; lia.
- right. apply shad_sep; [exact D| generalize RM; clear; intros; Z.div_mod_to_equations; lia]. }
assert (W6B : 2199023255552 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
/\ shad (aregion L K_BATCH_CLASS) + shlen K_REGION <= 17594333495296).
{ rewrite !shad_div, shlen_div. unfold ASHOFF, K_REGION. rewrite ER24. generalize SP1 SP2 A24a A24b. clear. unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF. change (2^37) with 137438953472. change (2^32) with 4294967296. change (2^41) with 2199023255552. intros. Z.div_mod_to_equations. lia. }
destruct W6B as [W6LO W6HI].
word_range sp SPR.
change (get_cls st1 K_BATCH_CLASS) with (get_cls st K_BATCH_CLASS) in MUr.
lazymatch type of MUr with munch ?W _ _ =>
assert (KHI : forall Ad sz, bv_unsigned sp + -2272 <= Ad -> 0 <= sz -> disjoint_from W Ad sz);
[ intros Ad sz H1 H2; cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION;
generalize H1 H2 LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |];
assert (KIM : forall Ad sz, 0xa3680 <= Ad -> Ad + sz <= 0x131f10 -> 0 <= sz -> disjoint_from W Ad sz);
[ intros Ad sz H1 H2 H3; cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION;
generalize H1 H2 H3 LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |];
assert (KCH : forall Ad sz, AB <= Ad -> Ad + sz <= UB + rup n 8 -> 0 <= sz -> disjoint_from W Ad sz);
[ intros Ad sz H1 H2 H3; cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION;
pose proof DT as DT'; unbox DT'; pose proof SLW5 as SL5;
generalize H1 H2 H3 LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR DT' SL5 G6 G7 UBS ABUB; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |];
assert (KSH : disjoint_from W (shad UB) (shlen (rup n 8)));
[ cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION; pose proof SLW6 as SL6;
generalize LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR SL6 SHLO SHHI SE GE GFS G0 G2; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |]
end.
rewrite EHM in HD1, FC1, SH1.
eapply (cells_frame _ m1 m') in HD1; [| exact MUr | exact WMr | apply KCH; cbn [cells_size csize Nat.add]; generalize ABUB RUP N1; clear; intros; lia].
eapply (cells_frame _ m1 m') in FC1; [| exact MUr | exact WMr | apply KCH; cbn [cells_size csize Nat.add]; generalize ABUB RUP RUP8 N1; clear; intros; Z.div_mod_to_equations; lia].
eapply (cells_frame _ m1 m') in SH1; [| exact MUr | exact WMr | replace (UB - 16 + 16) with UB by (clear; lia); match goal with |- disjoint_from _ _ ?z => replace z with (shlen (rup n 8)) by (cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id; [reflexivity| generalize G0; clear; intros; lia]) end; exact KSH].
clear STATS1 LSJ1 UW1.
eapply (cells_frame _ m1 m') in FL1; [| exact MUr | exact WMr | apply KIM; cbn [cells_size csize Nat.add]; clear; lia].
eapply (stk_transport_disjoint _ _ m1 m') in IAS1; [| exact MUr | exact WMr | apply KIM; clear; lia].
eapply (cells_frame _ m1 m') in SS1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
eapply (u64arr_frame _ m1 m') in TB1; [| exact MUr | exact WMr | apply KHI; rewrite ?LTB1; clear; cbn; lia].
eapply (cells_frame _ m1 m') in FRS1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
eapply (cells_frame _ m1 m') in FRP1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
eapply (cells_frame _ m1 m') in FRE1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xa3688 + 8 * j) (le8 (Z_to_bv 64 0))).
{ intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
intros i Hi. apply MUr. rewrite length_le8 in Hi. rewrite wa_unsigned by lia.
eapply disjoint_outside; [apply (KIM (0xa3688 + 8 * j) 8); generalize Hj; clear; intros; lia| generalize Hi; clear; intros; lia]. }
clear IAM1.
idtac "CHECKPOINT-C2".
pose proof ARr as AR0. destruct AR0 as (WFr & RTr & INSTr & THRr & CLSr & HQr & HSr & HDr & HROr & HRT2r & AVLr).
cbn [ah_quar ah_sec ah_depot AHQm] in HQr, HSr, HDr.
assert (XB' : x_busy X' = l1 ++ bany BQuar c k n b1 ctx :: l2) by (rewrite XBr; reflexivity).
destruct THRr as (T0r & T40r & CACHESr & CSTATSr & [sjr [STATSr LSJr]] & UNWr).
destruct (junk_split m' (al_t L + 2768) 16 16 CSTATSr ltac:(lia) ltac:(lia)) as [CSa CSb].
destruct (junk_split m' (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
destruct (c8_of_junk m' _ CS8) as [stj' STSr].
assert (POSr : 0 < c_count (get_cls st_r K_BATCH_CLASS)) by (rewrite CNTr; exact MAXr).
destruct (read_ek_new (AHQm Q1) L st_r X' Q1 m' RNG' BQuar c k n b1 ctx l1 l2 ALO ARNGr ARr HQr XB' ltac:(discriminate) stj' EAr POSr STSr)
as (k24 & chunks & EK & ES & ED & EB & NK & NB & KK & NIB & JK & FSH & CIN & _ & EKE).
pose proof HQr as AQr. destruct AQr as ([QKr MXr] & [QCr ABLr] & [GCQr ABGr] & (FLr & IASr & IAMr) & CPr & NUMr).
destruct (read_dk (AHQm Q1) L st_r X' Q1 m' RNG' BQuar c k n b1 ctx l1 l2 ALO ARNGr ARr HQr XB' ltac:(discriminate)
(abatch_addr L k24) (n + 8192) (ek_of L st_r X' Q1 n k24 stj' chunks) ltac:(lia)
ltac:(right; exists k24; split; [reflexivity|]; split; [exact KK| exact NIB])
ltac:(rewrite ENr, NG2, NL2 in NORECr; generalize NORECr; clear; unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES; intros; lia) EB) as (DK & DS & GL & GLST).
set (ek := ek_of L st_r X' Q1 n k24 stj' chunks) in *.
set (g := g_of L st_r Q1 (n + 8192)) in *.
idtac "CHECKPOINT-D".
destruct (any_range L st_r X' BQuar c k n b1 ctx l1 l2 XB' WFr) as [HCr KRr].
destruct (slot_rng L st_r X' c k ALO WFr HCr KRr RNG' ARNGr) as [RSLr RSSr]. fold AB in RSLr, RSSr.
pose proof ARNGr as AG0. destruct AG0 as (RIMGr & RT4r & RCTXr & RNOr & RSTOr & _).
pose proof (rng_fp_le _ _ _ _ FPLE RSTK) as RSTKr.
assert (BLr : ablocks L st_r X' (lb_remove p LB)) by (apply (ablocks_xbusy L (set_live (delete p (a_live st)) st) st_r X1); [exact XBr | exact LIVEr | exact BLm]).
pose proof (ao_fake L ALO) as FKO. unfold aobj in FKO. pose proof (ao_dtls L ALO) as DTO. unfold aobj in DTO.
unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in FKO, DTO.
pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
assert (FKr : AFK L (lb_remove p LB) m').
{ eapply (hf_frame _ HL L (lb_remove p LB) m1 m'); [exact FKm | exact MUr | exact WMr |].
unfold fake_untouched. unfold AINSTANCE, K_REGION.
assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
\/ shad (aregion L K_BATCH_CLASS) + shlen K_REGION <= shad (al_fake L))).
{ destruct D_f_res as [D|D].
- left. apply shad_sep; [| generalize FKO; clear; intros; Z.div_mod_to_equations; lia]. rewrite ER24. generalize D RSP A24a; clear; intros; lia.
- right. apply shad_sep; [| pose proof (aregion_mod L K_BATCH_CLASS SAL) as RM; generalize RM; clear; intros; Z.div_mod_to_equations; lia].
rewrite ER24. unfold K_REGION. generalize D RSP RES; clear; atop_facts; intros; lia. }
unfold K_REGION in SHF.
repeat (apply Forall_cons; [cbn [fst snd];
generalize LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR FKO DTO D_f_res D_t_f D_d_res D_t_d RES RHI RSP SHF; clear;
unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296;
rewrite ?shad_div, ?shlen_div; unfold ASHOFF; intros; Z.div_mod_to_equations; repeat split; lia |]).
apply Forall_nil. }
clear D_f_res D_t_f D_d_res D_t_d D_t_res.
idtac "CHECKPOINT-D2".
rewrite <- EHM in HD1, FC1, SH1.
pose proof EK as EK0. pose proof ES as ES0. pose proof DK as DK0.
rewrite EKE in EK, ES, DK. cbn [ek_pre] in EK.
destruct EK as (FULLr & SBr & CRr & CHr & LCHr & CNTr' & NTHr & IXSr & STSr' & HBr & BJr & SBPr & B0r & BL1r & DTBr & DTLr & DBLr & DHBr & DHLr & RBr).
box DTBr. box DTLr. box DBLr. box DHBr. box DHLr.
pose proof ES as ES1. cbn [ek_seps] in ES1. destruct ES1 as (SB1r & SB2r & SB3r & SLr).
assert (DHL24 : fhm L c k n + 24 <= qlast L (q_loc Q1) \/ qlast L (q_loc Q1) + 8192 <= fhm L c k n).
{ destruct (a_qloc st_r); [destruct FULLr as [_ E0]; rewrite E0; right; generalize HLO EHM; clear; intros; lia | exact (proj1 (SLr eq_refl))]. }
box SB1r. box DHL24.
assert (NBr : 0 <= Z.of_nat (length (a_qloc st_r)) < 2^62) by (rewrite QLr; change (a_qloc st1) with (a_qloc st); generalize LLB NC; clear; unfold Q_BATCH_BYTES; intros; lia).
assert (QB0r : 0 <= a_qloc_bytes st_r) by (rewrite QBr; change (a_qloc_bytes st1) with (a_qloc_bytes st); generalize LLB; clear; unfold Q_BATCH_BYTES; intros; lia).
eapply evtF_mono.
{ lazymatch type of EKE with _ = EkNew ?fu ?nx ?bs ?cn ?mx ?cz ?sj0 ?ix ?chs ?sb ?bb ?hs0 =>
eapply (free_from_refill_spec DI L fu g RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m'
(al_t L) (fhm L c k n) n b1 ctx lo (Z.of_nat (length (a_qloc st_r))) (qfirst L (q_loc Q1)) (qlast L (q_loc Q1)) (a_qloc_bytes st_r)
nx bs cn sb id bb mx cz sj0 ix sjr tb1 chs hs0 junk2 j0 trt)
end.
all: try lazymatch goal with
| |- stk _ _ _ _ => first [exact STr | exact IAS1]
| |- ablk _ (_ + 16 + rup _ 8) => first [assumption | unfold ablk; right; generalize HLO HHI; try generalize EHM; clear; unfold fhm; intros; lia]
| |- mem_inv _ _ => exact MIr
| |- ADEPOT _ _ _ => exact HDr
| |- u64arr _ _ (_ + 2800) _ => exact STATSr
| |- u64arr _ _ _ _ => first [exact TB1 | exact CHr]
| |- if _ then _ else _ => exact FULLr
| |- forall j, _ -> bytes_at _ _ _ _ => exact IAM2
| |- ek_seps _ _ _ _ => exact ES
| |- dk_pre _ _ _ _ _ _ _ _ => exact DK
| |- dk_seps _ _ _ => exact DS
| |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
| |- rw_cells _ _ (shad _) _ => exact SH1
| |- rw_cells _ _ (aq_tcache _) _ => exact QCr
| |- rw_cells _ _ (_ + 80) _ => exact QCr
| |- rw_cells _ _ (_ + 2128) _ => exact CRr
| |- rw_cells _ _ (_ + 2784) _ => exact STSr'
| |- rw_cells _ _ (_ + 3168) _ => exact UNWr
| |- rw_cells _ _ (_ + -72) _ => exact FRS1
| |- rw_cells _ _ (_ + -2128) _ => exact SS1
| |- rw_cells _ _ (_ + -2208) _ => exact FRP1
| |- rw_cells _ _ (_ + -2272) _ => exact FRE1
| |- rw_cells _ _ (fhm _ _ _ _ + 16) _ => exact FC1
| |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact QKr
| |- nth_error _ _ = _ => exact NTHr
| |- @eq Z _ _ => exact HBr
| |- ex _ => exact BJr
| |- _ + 24 <= al_t _ \/ _ => pose proof DT as DT2; unbox DT2; generalize DT2 EHM S8 ABUB RUP N1; clear; intros; lia
| |- _ \/ _ => first [unboxed DTBr | unboxed DTLr | unboxed DBLr | unboxed SB1r | unboxed DHL24 | unboxed DT | unboxed DL7 | unboxed DL8]
| |- rng _ (shad _) _ => replace (fhm L c k n + 16) with UB by (generalize EHM; clear; intros; lia); eapply rng_sub; [exact RSSr| rewrite SE; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]| rewrite SE, GE; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]]
| |- rng _ (fhm _ _ _ _) _ => eapply rng_sub; [exact RSLr| first [generalize EHM; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]| first [generalize EHM; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]]
| |- rng _ _ _ => first [assumption | eapply rng_sub; [exact RSTKr| first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]| first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]]]
end.
all: try assumption.
all: try (unfold Q_MAX, Q_BATCH_BYTES; rewrite ?QLr, ?QBr; change (a_qloc st1) with (a_qloc st); change (a_qloc_bytes st1) with (a_qloc_bytes st);
generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM UBS S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 DL1 DL2 DL3 DL4 DL5 DL6
B10 LLB NC NM LF64 LST64 RA4 IDR EHM; clear; intros; lia).
all: match goal with |- ?G => idtac "REMT" G end. }
cbv beta. intros msf PF.
idtac "CHECKPOINT-E".
rewrite <- EKE in PF.
pose proof ARm as ARm0. destruct ARm0 as [WFm _].
assert (DK1 : dk_pre ek (g_of L st_r Q1 (ek_delta ek n)) RNG' (al_t L) (qlast L (q_loc Q1)) (fhm L c k n) (a_qloc_bytes st_r + ek_delta ek n) m') by (rewrite ED; exact DK0).
assert (PF1 : free_fast_post DI L ek (g_of L st_r Q1 (ek_delta ek n)) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n
(Z.of_nat (length (a_qloc st_r))) (qfirst L (q_loc Q1)) (qlast L (q_loc Q1)) (a_qloc_bytes st_r) b1 ctx lo m' msf) by (rewrite ED; exact PF).
pose proof (STORE_R L RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m' st_r (lb_remove p LB) X' Q1 c k n b1 ctx lo k24 l1 l2 stj' chunks
ALO ARNGr ARr BLr FKr XB' N1 (ex_intro _ (q_pend Q) eq_refl) EAr NK NB KK NIB JK FSH CIN POSr NORECr EK0 DK1 CEIL LO msf PF1)
as (t0f & t1f & t2f & a0f & a1f & a2f & a3f & a4f & a5f & a6f & a7f & t3f & t4f & t5f & t6f & mf & -> & MIf2 & STf2 & HPf & AHf).
unfold afree_post. split; [exact FPLE|].
exists t0f, t1f, t2f, a0f, a1f, a2f, a3f, a4f, a5f, a6f, a7f, t3f, t4f, t5f, t6f, mf.
split; [reflexivity|]. split; [exact MIf2|]. split; [exact STf2|]. split; [| exact AHf].
eapply aheap_pres_trans; [exact HPm|]. eapply aheap_pres_trans; [| exact HPf].
eapply (aheap_pres_refill L st1 X1 (lb_remove p LB) sp (bv_unsigned sp + -2272) lo m1 m');
[exact ALO | exact WFm | exact BLm | exact MUr | exact WMr | exact CEIL | generalize LO; clear; intros; lia | clear; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
