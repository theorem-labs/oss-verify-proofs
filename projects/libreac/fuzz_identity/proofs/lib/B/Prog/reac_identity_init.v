(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:198-200;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:132-134. *)
(* reac_identity_init of fuzz_identity.asan-ubsan (build B), at BASE + AF_reac_identity_init = 0x83a84: the
   contract and its walk. It mirrors lib/A/Prog/reac_identity_init.v
   line for line. reac_identity_init writes 38 bytes of its caller's frame, so it is stated in
   cgif's caller-journal form (IdentBCJ.v: tdst_ok, twr_ok, tcj_kept).
   Measured on the B listing:
   9 slots as in A; 0x83a84 `addi sp,sp,-16` is a 16-byte frame; 0x83a8c `beqz a0` (a0 = 0 goes to the return)
   is decided by the pointer fact of a0; 0x83a98 calls IB___asan_memset (0x51d5c) with a0 = pI, a1 = 0,
   a2 = 38 and returns to BASE + 0x3328; it needs ESTACK under sp. No UBSan check in this function.
   The B differences from A: the listing (identb_listing, IB___asan_memset, PL_identb) and the memset return
   offset 0x3328 (A: 0x31e4). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import YC45.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import YC85 IdentBFrame IdentBCJ.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition REAC_IDENTITY_INIT_STK : Z := 16 + ESTACK.
Definition IDENT_SIZE : Z := 38.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation SIGMA := (pa_sigma).
#[local] Notation BASE := (pa_val A_TEXT).
Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA IB___asan_memset).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).

Definition treac_identity_init_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (pI : Z) : world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
(forall i, 0 <= i < IDENT_SIZE -> aview SEGS (w_H W2) mem2 (pI + i) = Some 0) /\
tcj_kept B REAC_IDENTITY_INIT_STK lyc Sc W memc W2 mem2 (spZ regs) (fun a => pI <= a < pI + IDENT_SIZE).

Definition treac_identity_init_spec (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (pI : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 pI ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_IDENTITY_INIT_STK -> spZ regs <= sp0 ->
tdst_ok B lyc Sc pI IDENT_SIZE ->
twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) pI IDENT_SIZE ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF pI IDENT_SIZE ->
shadow_hull_vis (aview SEGS (w_H W) memc) pI IDENT_SIZE ->
SRr SEGS W (cfg_at SEGS a regs memc mdc)
(treac_identity_init_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs pI).

Definition init_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, PTR 0)] [] [].
Definition ss_init : sstate := mkSS AF_reac_identity_init sr_atoms [stack_region 16] None init_facts.

Theorem pb_reac_identity_init : treac_identity_init_spec (BASE + AF_reac_identity_init).
Proof.
unfold treac_identity_init_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pI
HJc Hra0 Hgp Htp G10 Hal16 Hwlo Hwhi HDST HWR HRA HHULL.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : REAC_IDENTITY_INIT_STK = 4112) by reflexivity.
assert (HSZ : IDENT_SIZE = 38) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HJc as (HARc & Hlyc & _ & _ & _ & Hfrsc & _ & _ & F1c & F2c & F3c & F4c & _ & Hpresc & HST & _).
destruct HST as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (Hsplo : alloc_ceiling + REAC_IDENTITY_INIT_STK <= spZ regs) by lia.
assert (Hsphi : spZ regs <= 2 ^ 47) by lia.
assert (Hom : (spZ regs - 16 - sp0) mod 16 = 0).
{ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D0. pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D1.
rewrite Hsp0al, Z.add_0_r in D0. rewrite Hal16, Z.add_0_r in D1.
replace (spZ regs - 16 - sp0) with ((spZ regs / 16 - 1 - sp0 / 16) * 16) by lia. apply Z_mod_mult. }
assert (HLOC : forall a, pI <= a < pI + IDENT_SIZE ->
4096 <= a < alloc_ceiling /\ (a < kLowShadowBeg \/ kHighMemBeg <= a) /\ ~ in_img SEGS a).
{ intros a Ha. destruct (HDST a Ha) as [(b & m & Hin & Hr) | (cid & pos & Hin & Hr)].
- destruct (al_blocks SEGS B LAWS lyc Sc W memc mdc b m HARc Hin) as (_ & H4096 & Hce & Happ & _).
pose proof (blk_off_imgP _ _ _ _ _ _ b m HARc Hin) as Himg.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
split; [lia|]. split; [unfold kLowShadowBeg, kHighMemBeg; lia|].
intros Hi. pose proof (pa_img_range a Hi). lia.
- unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HARc Hin) as (H4096 & Hce & Happ).
pose proof (frm_off_imgP B lyc Sc W memc mdc cid pos HARc Hin) as Himg.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
split; [lia|]. split; [unfold kLowShadowBeg, kHighMemBeg; lia|].
intros Hi. pose proof (pa_img_range a Hi). lia. }
destruct (HLOC pI ltac:(lia)) as (HpI0 & HpIz & _).
destruct (HLOC (pI + 37) ltac:(lia)) as (HpI1 & HpIz1 & _).
assert (HAMR : amem_range pI IDENT_SIZE).
{ unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, IDENT_SIZE in *. lia. }
remember (Eimg (Ereg regs (@nil word))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (AGE : env_agree 32 (Ereg regs (@nil word)) E)
by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER : regs_ok E sr_atoms regs) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (E1 : ew E 1 = getr regs 1) by (exact (EE 1%nat 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (exact (EE 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (E10 : ew E 10 = Z_to_bv 64 pI) by (rewrite (EE 10%nat 10%bv eq_refl); exact G10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE.
assert (HS : st_ok_pi SEGS VAL E ss_init
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_identity_init)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_init. apply pa_entry_st_ok_full.
- exact ER.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil. unfold region_ok, stack_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpresc. lia.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- unfold init_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
split; [|split; exact I]. split; [|split; [|exact I]].
+ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp. change (2 ^ 4) with 16.
split; [lia|]. split; [exact Hal16 | lia].
+ unfold afact_ok, PTR. cbn [af_lo af_hi af_al2]. rewrite E10, unsigned_lit_small by lia.
rewrite Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity | lia]. }
unfold cfg_at. change (w64 (BASE + AF_reac_identity_init)) with (Z_to_bv 64 (BASE + AF_reac_identity_init)).
paj_run_shc RUNP RUNC HS HJc.
{ eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
[reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo stack_region]; lia
| cbn [YP09.r_whi stack_region]; lia | apply awr_ok_nil]. }
pose proof HF as HF1. pose proof HFr as HFr1. pose proof HG as HG1.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ intros a Ha Hw.
apply (kept_of_frame E (ss_mem ss_init) (w_H W) memc (ms_mem ms)
(fun x => spZ regs - 16 <= x < spZ regs) HFr1); [| exact Ha | exact Hw].
intros bb wlo whi aa Hin Hr. unfold ss_init in Hin.
cbn [ss_mem windows map stack_region YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
destruct Hin as [Eq | []]. injection Eq as <- <- <-.
cbn [base_val] in Hr. rewrite Usp in Hr. lia. }
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA IB___asan_memset) AMEMSET W (ms_regs msX) (ms_mem msX)
STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k pI 0 IDENT_SIZE (spZ regs - 16 - sp0) (Z_to_bv 64 (BASE + 0x3328)) HJc) end.
- rewrite Ra0, E10. reflexivity.
- rewrite Ra1. reflexivity.
- rewrite Ra2. reflexivity.
- unfold IDENT_SIZE. lia.
- lia.
- lia.
- unfold spZ at 1. rewrite Rsp, Usp, unsigned_lit_small by lia. lia.
- exact Hom.
- lia.
- lia.
- rewrite Rgp. exact E3.
- rewrite Rtp. exact E4.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros x Hx. destruct (HWR x Hx) as (Hw & _ & _ & _). destruct (HLOC x Hx) as (Hb & _ & _).
split; [exact Hw | lia].
- exact HAMR.
- eapply (range_addressable_kept_win (aview SEGS (w_H W) memc) _ (spZ regs - 16) (spZ regs) pI IDENT_SIZE); [| | lia | unfold IDENT_SIZE; lia | exact HRA].
+ intros s Hs Hns. apply KEEP1; lia.
+ unfold kHighShadowEnd in *. lia.
- intros _. eapply (shadow_hull_vis_kept_win (aview SEGS (w_H W) memc) _ (spZ regs - 16) (spZ regs) pI IDENT_SIZE);
[| | lia | unfold IDENT_SIZE; lia | unfold IDENT_SIZE; lia | exact HHULL].
+ intros s Hs Hns. apply KEEP1; lia.
+ unfold kHighShadowEnd in *. lia.
- exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff & Hfr2 & Hpres2).
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp.
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
eapply (region_kept_aview E (w_H W) _ mem2 2%nat (spZ regs)); [exact Usp | | exact Hpres2];
intros aa Haa; apply Hfr2; unfold IDENT_SIZE, ESTACK in *; lia
| specialize (HS2 HQ); clear HQ ] end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
pose proof (img_env_havoc_hi E 512%nat (map (getr regs2) CLOB) HEI ltac:(cbv; lia)) as HEI2.
clear HF HFr HG.
paj_run_sh RUNP HS HJ2.
{ eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
[reflexivity | try (rewrite ew_havoc_old by lia); rewrite Usp; lia
| cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha Hw.
apply (kept_of_frame _ _ (w_H W) mem2 (ms_mem ms0)
(fun x => spZ regs - 16 <= x < spZ regs) HFr); [| exact Ha | exact Hw].
intros bb wlo whi aa Hin Hr.
cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
destruct Hin as [Eq | []]. injection Eq as <- <- <-.
cbn [base_val] in Hr. try (rewrite ew_havoc_old in Hr by lia). rewrite Usp in Hr. lia. }
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - REAC_IDENTITY_INIT_STK <= a < spZ regs) ->
~ (pI <= a < pI + IDENT_SIZE) -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
{ intros a Ha Hw Hp. rewrite (KEEP2 a Ha ltac:(lia)).
rewrite (Hfr2 a Ha Hp ltac:(unfold IDENT_SIZE, ESTACK in *; lia)). apply KEEP1; lia. }
assert (HPRES : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms0) a).
{ intros a Hp. eapply apresent_grows; [exact HG|]. apply Hpres2. eapply apresent_grows; [exact HG1 | exact Hp]. }
prreg HS (1%bv : bv 5) R1.
try (rewrite ew_havoc_old in R1 by lia). rewrite E1 in R1.
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbn [ms_regs ms_mem].
unfold treac_identity_init_post.
exists lyc, Sc. eexists. eexists. eexists.
split; [rewrite R1; unfold YK0s.ret_ok in Hra0; rewrite Hra0; reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|].
split.
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (@nil word) HS); [| vm_compute; reflexivity].
split; [intros n Hn; rewrite ew_havoc_old by lia; exact (proj1 AGE n Hn)
| cbn [havoc ed]; exact (proj2 AGE)]. }
split; [reflexivity|].
split; [apply Permutation_refl|].
split.
{ intros i Hi. rewrite (KEEP2 (pI + i) ltac:(lia) ltac:(lia)). rewrite (Heff i ltac:(lia)). reflexivity. }
unfold tcj_kept. cbn beta.
split.
{ intros a Ha Hw Hp. apply KEEP; [lia | lia | exact Hp]. }
split.
{ intros b m i Hin Hi Hp.
destruct (al_blocks SEGS B LAWS lyc Sc W memc mdc b m HARc Hin) as (_ & H4096 & Hce & _ & _).
apply KEEP; [lia | lia | exact Hp]. }
split.
{ intros a Hi Hns He. pose proof (Hsegs a Hi) as Hlow. pose proof (pa_img_range a Hi) as Hrng.
apply KEEP; [lia | unfold kLowMemEnd in Hlow; lia|].
intros Hp. exact (proj2 (proj2 (HLOC a Hp)) Hi). }
split.
{ intros cid pos a Hin Hr Hp.
destruct (frame_zone SEGS B LAWS lyc Sc W memc mdc cid pos a HARc Hin Hr) as (Hz & _).
apply KEEP; [| lia | exact Hp].
destruct Hr as [Hr | Hr]; unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr;
pose proof (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HARc Hin) as (Hf0 & Hfc & _);
pose proof (fs_frame_bytes_nonneg cid) as Hfb;
[lia | pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hsb; unfold kLowMemEnd in *; lia]. }
split.
{ intros a Ha Hw Hp. eapply apresent_grows; [exact HG|]. apply Hpres2.
eapply apresent_grows; [exact HG1 | exact Hp]. }
{ pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
intros a Ha. apply Hpres3. lia. }
Qed.
End c.
End b.
End a.
