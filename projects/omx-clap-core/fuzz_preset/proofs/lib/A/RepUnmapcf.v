(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/RepUnmapcf.v (commit eb934de95d13, blob 4afb9b9a7b85) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 16 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d YK02 YK0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j YP0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YFfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AFk7 AFgv.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition A_UOD : Z := 0x66b08.
Definition UOD_STK : Z := 48.
Definition uSTK : YP09.region := YP09.mkRegion (Some 2%nat) (- UOD_STK) 0 (- UOD_STK) 0 [].
Definition uGOT : YP09.region := YP09.mkRegion None 0xa2000 (0xa2000 + 8) 0 0 [YP09.mkChunk 0xa2000 (CVal 8 (SLit 0x13c9e8))].
Definition uLIM : YP09.region := YP09.mkRegion None 0x13ca78 (0x13ca78 + 8) 0 0 [YP09.mkChunk 0x13ca78 (CVal 8 (SLit 0))].
Definition uFN : facts := mkFacts [ (2%nat, mkAF (TFIB_IMG_END + UOD_STK) (2 ^ 64 - 1) 4) ] [] [].
Definition uFU : facts :=
mkFacts [ (2%nat, mkAF (TFIB_IMG_END + UOD_STK) (2 ^ 64 - 1) 4); (10%nat, mkAF 1 (2 ^ 64 - 1) 0); (11%nat, mkAF 1 (2 ^ 64 - 1) 0) ] [] [].
Definition SS_N : sstate := mkSS A_UOD sr_atoms [uSTK] None uFN.
Definition SS_U : sstate := mkSS A_UOD sr_atoms [uSTK; uGOT; uLIM] None uFU.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].

Local Ltac uod_frame HF BV2 spv K :=
lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
let rs' := eval vm_compute in rs in
assert (K : forall x : word, ~ (spv - UOD_STK <= bv_unsigned x < spv) -> m' x = m x)
by (let x := fresh "x" in let Hx := fresh "Hx" in let r := fresh "r" in let Hr := fresh "Hr" in
    intros x Hx; apply (frame_of_outside E rs m m' x HF); intros r Hr;
    change rs with rs' in Hr; cbn [In] in Hr;
    repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; rewrite ?BV2; unfold UOD_STK in *; lia|]);
    destruct Hr);
clear HF
end.

Local Ltac rrege HS r Hr :=
lazymatch type of HS with
| st_ok_ecall ?segs ?E ?ss (restrict ?H ?ms) =>
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
let v := eval cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in (sv_denot E e) in
let v := simp_off0 v in
let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
assert (Hr : getr rg r = v)
by (refine (eq_trans (st_ok_ecall_restrict_reg H E ss ms r HS) _);
change (sv_denot E e = v);
cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity)
end.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma uod_fr_trans : forall (P : word -> Prop) (m0 m1 m2 : word -> option byte),
(forall x, P x -> m1 x = m0 x) -> (forall x, P x -> m2 x = m1 x) -> forall x, P x -> m2 x = m0 x.
Proof. intros P m0 m1 m2 H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.
Lemma uod_apresent_bv : forall (H : word -> bool) (m : word -> option byte) a,
apresent H m a <-> apresent H m (bv_unsigned (Z_to_bv 64 a)).
Proof. intros H m a. unfold apresent. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma uod_apresent_post : forall (H : word -> bool) (mem mem' : word -> option byte) (lo hi : Z),
(forall x : word, ~ (lo <= bv_unsigned x < hi) -> mem' x = mem x) ->
(forall a, lo <= a < hi -> 0 <= a < 2 ^ 64 -> apresent H mem' a) ->
forall a, apresent H mem a -> apresent H mem' a.
Proof.
intros H mem mem' lo hi FR WIN a HP. apply (proj2 (uod_apresent_bv H mem' a)). apply (proj1 (uod_apresent_bv H mem a)) in HP.
pose proof (u64_range (Z_to_bv 64 a)) as Ua. set (a' := bv_unsigned (Z_to_bv 64 a)) in *.
destruct (Z_lt_le_dec a' lo) as [L|L]; [|destruct (Z_lt_le_dec a' hi) as [L2|L2]].
- apply (apresent_same H mem); [apply FR; rewrite unsigned_lit_small by lia; lia | exact HP].
- apply WIN; lia.
- apply (apresent_same H mem); [apply FR; rewrite unsigned_lit_small by lia; lia | exact HP].
Qed.

Lemma uod_win : forall (W : world tfibsegs) (E : env) ss ms (r : YP09.region) (sp : Z),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> nth_error (ss_mem ss) 0 = Some r ->
YP09.r_base r = Some 2%nat -> YP09.r_wlo r = - UOD_STK -> YP09.r_whi r = 0 ->
bv_unsigned (ew E 2) = sp -> TFIB_IMG_END <= sp - UOD_STK ->
forall a, sp - UOD_STK <= a < sp -> 0 <= a < 2 ^ 64 -> apresent (w_H W) (ms_mem ms) a.
Proof.
intros W E ss ms r sp HS Hn Hb Hlo Hhi BV2 Hsp a Ha Ha'. apply (st_ok_window_apresent (w_H W) E ss ms 0 r a HS Hn).
- rewrite Hb, Hlo, Hhi. cbn [base_val]. rewrite BV2. lia.
- lia.
Qed.
Lemma uod_map_has_In : forall (l : list (word * word)) a n, map_has l a n = true -> In (a, n) l.
Proof.
intros l a n H. unfold map_has in H. apply existsb_exists in H as ([a' n'] & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [Ha Hn]. apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hn. subst. exact Hin.
Qed.
Lemma uod_same_io : forall l1 l2 (mat1 mat : list word) (a n : word) md,
same_io md (with_vm_backing l2 mat (munmap_model a n (with_vm_backing l1 mat1 md))).
Proof.
intros l1 l2 mat1 mat a n md. pose proof (same_io_munmap a n (with_vm_backing l1 mat1 md)) as IO. hnf in IO. hnf.
destruct IO as (I1 & I2 & I3 & I4). split; [exact I1|]. split; [exact I2|]. split; [exact I3 | exact I4].
Qed.

Local Ltac uod_nop_fin HS Hwx W E0 E1 BV2 Hsp Hra regs sp FR :=
eapply (SRr_ret_at tfibsegs tfibtbl_rtM tfibtbl_rtM_ok Hwx W E0); [exact HS | reflexivity | vm_compute; reflexivity |];
let mat' := fresh "mat" in intros mat'; split; [reflexivity|];
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) =>
let Q1 := fresh "Q1" in rreg HS (1%bv : bv 5) Q1; rewrite E1 in Q1;
exists (ms_regs msx), (ms_mem msx), mat';
split; [rewrite Q1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|];
split; [apply (regs_preserved_of_st_ok tfibsegs E0 _ _ regs [] HS); [apply env_agree_refl | vm_compute; reflexivity]|];
split; [exact FR|];
apply (uod_apresent_post _ _ _ _ _ FR);
eapply (uod_win W E0 _ _ _ sp HS); [reflexivity | reflexivity | reflexivity | reflexivity | exact BV2 | exact Hsp]
end.
Lemma unmapordie_nop : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model),
let sp := bv_unsigned (getr regs 2) in
(getr regs 10 = w64 0 \/ getr regs 11 = w64 0) ->
YK0s.ret_ok (getr regs 1) ->
sp mod 16 = 0 -> TFIB_IMG_END <= sp - UOD_STK -> (forall a, sp - UOD_STK <= a < sp -> apresent (w_H W) mem a) ->
SRr tfibsegs W (mkCfg (mkst regs (w64 A_UOD) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp - UOD_STK <= bv_unsigned x < sp) -> mem' x = mem x) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros W regs mem md. cbv zeta. intros H0 Hra Hal Hsp HPRES. pose proof Hwx_tfa as Hwx.
pose proof (u64_range (getr regs 2)) as Usp. set (sp := bv_unsigned (getr regs 2)) in *.
set (E0 := Ereg regs []).
assert (E1 : ew E0 1 = getr regs 1) by (exact (ew_Ereg_nat regs [] 1 1%bv eq_refl)).
assert (E10 : ew E0 10 = getr regs 10) by (exact (ew_Ereg_nat regs [] 10 10%bv eq_refl)).
assert (E11 : ew E0 11 = getr regs 11) by (exact (ew_Ereg_nat regs [] 11 11%bv eq_refl)).
assert (BV2 : bv_unsigned (ew E0 2) = sp) by (exact (f_equal bv_unsigned (ew_Ereg_nat regs [] 2 2%bv eq_refl))).
assert (BV2' : bv_unsigned (ew (Ereg regs []) 2) = sp) by exact BV2.
assert (HS : st_ok tfibsegs E0 SS_N (restrict (w_H W) (mkst regs (w64 A_UOD) mem (seg_rom tfibsegs)))).
{ unfold SS_N, A_UOD, w64. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. unfold uSTK. apply Forall_cons; [|apply Forall_nil].
apply (region_ok_stack tfibsegs E0 _ 2 sp (- UOD_STK)); [exact BV2 | unfold UOD_STK, TFIB_IMG_END in *; lia | lia |].
intros a Ha. apply apresent_writable; [unfold UOD_STK in *; lia | apply HPRES; exact Ha].
- apply pairwise_disjoint_of_extents. unfold uSTK, extent_of_region. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; exact I]. cbn [uFN f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite ?BV2, ?BV2'.
unfold UOD_STK, TFIB_IMG_END in *. change (2 ^ 4) with 16. repeat split; lia. }
srr_run_sh tfibtbl_rtM_ok HS. clear HFr. uod_frame HF BV2 sp FR.
srr_branch_sh tfibtbl_rtM_ok HS.
- srr_run_sh tfibtbl_rtM_ok HS. clear HFr. uod_frame HF BV2 sp K.
  pose proof (uod_fr_trans _ _ _ _ FR K) as FR'. clear FR K. rename FR' into FR.
  uod_nop_fin HS Hwx W E0 E1 BV2 Hsp Hra regs sp FR.
- srr_run_sh tfibtbl_rtM_ok HS. clear HFr. uod_frame HF BV2 sp K.
  pose proof (uod_fr_trans _ _ _ _ FR K) as FR'. clear FR K. rename FR' into FR.
  srr_branch_sh tfibtbl_rtM_ok HS.
  + srr_run_sh tfibtbl_rtM_ok HS. clear HFr. uod_frame HF BV2 sp K.
    pose proof (uod_fr_trans _ _ _ _ FR K) as FR'. clear FR K. rename FR' into FR.
    uod_nop_fin HS Hwx W E0 E1 BV2 Hsp Hra regs sp FR.
  + exfalso. rewrite branch_eq_U in Hc, Hc0. unfold U in Hc, Hc0. cbn [sv_denot] in Hc, Hc0.
    rewrite E10 in Hc. rewrite E11 in Hc0.
    destruct H0 as [Z0|Z0]; [revert Hc | revert Hc0]; rewrite Z0; vm_compute; intros X; discriminate X.
Qed.
Lemma unmapordie_unmap : forall (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (ad n : Z),
let sp := bv_unsigned (getr regs 2) in let N := page_round_up_Z n in
getr regs 10 = w64 ad -> getr regs 11 = w64 n -> 0 < ad -> 0 < n -> ad mod 4096 = 0 ->
(ad + N <= TFIB_IMG_LO \/ TFIB_IMG_END <= ad) -> ad + N <= TASK_SIZE ->
map_has (vm_maps (m_vmmaps md)) (w64 ad) (w64 N) = true -> amwf md ->
YK0s.ret_ok (getr regs 1) ->
sp mod 16 = 0 -> TFIB_IMG_END <= sp - UOD_STK -> (forall a, sp - UOD_STK <= a < sp -> apresent (w_H W) mem a) ->
ad + N <= sp - UOD_STK \/ sp <= ad ->
val_mem tfibsegs (mrestrict (w_H W) mem) 0xa2000 8 0x13c9e8 -> val_mem tfibsegs (mrestrict (w_H W) mem) 0x13ca78 8 0 ->
SRr tfibsegs W (mkCfg (mkst regs (w64 A_UOD) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists regs' mem' mat1 mat,
let md1 := munmap_model (w64 ad) (w64 N) (with_vm_backing (m_vm_lazy md) mat1 md) in
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md1) mat md1) /\
regs_preserved regs regs' /\
(forall x : word, ~ (sp - UOD_STK <= bv_unsigned x < sp) -> ~ (ad <= bv_unsigned x < ad + N) -> mem' x = mem x) /\
(forall x : word, ad <= bv_unsigned x < ad + N -> mem' x = None) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (ad <= a < ad + N) -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
same_io md (cfg_model c') /\ amwf (cfg_model c')).
Proof.
intros W regs mem md ad n. cbv zeta. intros R10 R11 Had0 Hn Hal Had Hnw Hhas MW Hra Hspal Hsp HPRES Hdisj VG VL.
pose proof Hwx_tfa as Hwx. assert (HT : TASK_SIZE = 2 ^ 47) by reflexivity.
pose proof (u64_range (getr regs 2)) as Usp. set (sp := bv_unsigned (getr regs 2)) in *.
pose proof (page_round_up_Z_bounds n ltac:(lia)) as NB. set (N := page_round_up_Z n) in *. unfold page_size in NB.
assert (RA : 0 < ad /\ ad + N <= 2 ^ 47) by (rewrite HT in Hnw; lia).
set (E0 := Ereg regs []).
assert (E1 : ew E0 1 = getr regs 1) by (exact (ew_Ereg_nat regs [] 1 1%bv eq_refl)).
assert (E10 : ew E0 10 = getr regs 10) by (exact (ew_Ereg_nat regs [] 10 10%bv eq_refl)).
assert (E11 : ew E0 11 = getr regs 11) by (exact (ew_Ereg_nat regs [] 11 11%bv eq_refl)).
assert (BV2 : bv_unsigned (ew E0 2) = sp) by (exact (f_equal bv_unsigned (ew_Ereg_nat regs [] 2 2%bv eq_refl))).
assert (BV2' : bv_unsigned (ew (Ereg regs []) 2) = sp) by exact BV2.
assert (UA : bv_unsigned (w64 ad) = ad) by (unfold w64; apply unsigned_lit_small; lia).
assert (UNn : bv_unsigned (w64 n) = n) by (unfold w64; apply unsigned_lit_small; lia).
assert (UN : bv_unsigned (w64 N) = N) by (unfold w64; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E0 10) = ad) by (rewrite E10, R10; exact UA).
assert (U11 : bv_unsigned (ew E0 11) = n) by (rewrite E11, R11; exact UNn).
assert (U10' : bv_unsigned (ew (Ereg regs []) 10) = ad) by exact U10.
assert (U11' : bv_unsigned (ew (Ereg regs []) 11) = n) by exact U11.
assert (HS : st_ok tfibsegs E0 SS_U (restrict (w_H W) (mkst regs (w64 A_UOD) mem (seg_rom tfibsegs)))).
{ unfold SS_U, A_UOD, w64. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- cbn [ms_mem mkst]. unfold uSTK, uGOT, uLIM.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ apply (region_ok_stack tfibsegs E0 _ 2 sp (- UOD_STK)); [exact BV2 | unfold UOD_STK, TFIB_IMG_END in *; lia | lia |].
intros a Ha. apply apresent_writable; [unfold UOD_STK in *; lia | apply HPRES; exact Ha].
+ reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VG].
+ reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VL].
- apply pairwise_disjoint_of_extents. unfold uSTK, uGOT, uLIM, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite ?BV2, ?BV2'. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold UOD_STK, TFIB_IMG_END in *. repeat split; lia.
- split; [|split; exact I]. cbn [uFU f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. change (Ereg regs []) with E0.
rewrite BV2, U10, U11. unfold UOD_STK, TFIB_IMG_END in *. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
repeat split; first [lia | apply Z.mod_1_r]. }

srr_run_sh tfibtbl_rtM_ok HS. clear HFr. uod_frame HF BV2 sp FR1.
lazymatch goal with |- SRr _ _ (mkCfg ?msx (with_vm_backing _ ?mt _)) _ => rename msx into msE; rename mt into mat1 end.
pose proof (st_ok_ecall_full_shape (w_H W) E0 _ msE HS eq_refl) as SHP. cbn [ss_pc] in SHP.
rrege HS (17%bv : bv 5) Q17. rrege HS (10%bv : bv 5) Q10. rrege HS (11%bv : bv 5) Q11.
rewrite E10, R10 in Q10.
rewrite E11, R11 in Q11.
lazymatch type of HS with st_ok_ecall _ _ ?ssM _ =>
assert (KEPT : Forall (region_kept tfibsegs E0 (mrestrict (w_H W) (ms_mem msE)) (mrestrict (w_H W) (unfill (w64 ad) (w64 N) (ms_mem msE)))) (ss_mem ssM)) end.
{ apply Forall_forall. intros r Hr. apply region_kept_ext. intros z Hz. revert Hz.
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hr end.
cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?BV2; intros Hz;
apply mrestrict_unfill_out; [unfold UOD_STK, TFIB_IMG_END in *; lia | rewrite UA, UN; unfold UOD_STK, TFIB_IMG_END, TFIB_IMG_LO in *; lia] |]).
destruct Hr. }
pose proof (st_node_cont (w_H W) E0 _ msE (SLit 0) 0 0x652cc (unfill (w64 ad) (w64 N) (ms_mem msE)) HS eq_refl eq_refl ltac:(vm_compute; reflexivity) KEPT) as HS2.
clear KEPT.

rewrite SHP at 1. apply SRr_use_AI. intros HAI. cbn [cfg_model] in HAI.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
assert (MW1 : amwf md1) by (apply (amwf_same md md1); [subst md1; apply m_vmmaps_wvb | subst md1; apply m_vm_lazy_wvb | exact MW]).
assert (INV1 : In (w64 ad, w64 N) (vm_maps (m_vmmaps md1))) by (subst md1; rewrite m_vmmaps_wvb; exact (uod_map_has_In _ _ _ Hhas)).
destruct (in_split _ _ INV1) as (l1 & l2 & EVM).
apply (SRr_node tfibsegs W _ unit (fun _ => mkCfg (mkst (regupd (ms_regs msE) 10%bv (Z_to_bv 64 0)) (v_addi (Z_to_bv 64 0x652c8) 4)
  (unfill (w64 ad) (w64 N) (ms_mem msE)) (seg_rom tfibsegs)) (munmap_model (w64 ad) (w64 N) md1)) tt).
{ exact (munmap_node tfibsegs (ms_regs msE) (Z_to_bv 64 0x652c8) (ms_mem msE) (seg_rom tfibsegs) md1 (w64 ad) n (AI_halted _ _ _ _ HAI)
  Q17 Q10 ltac:(rewrite UA; exact Hal) Q11 Hn ltac:(rewrite UA; exact Hnw) ltac:(subst md1; rewrite m_vmmaps_wvb; exact Hhas)). }
{ intros [] HA. cbn [cfg_model] in HA |- *.
  exact (munmap_AI tfibsegs (w_H W) (w_A W) md1 (w64 ad, w64 N) l1 l2 HA MW1 EVM ltac:(cbn [fst]; rewrite UA; exact Hal)
    ltac:(cbn [fst snd]; rewrite UA, UN; lia)). }
intros []. clear HS. rename HS2 into HS.
change (v_addi (Z_to_bv 64 0x652c8) 4) with (Z_to_bv 64 0x652cc).

srr_run_sh tfibtbl_rtM_ok HS. clear HFr. uod_frame HF BV2 sp FR2.
eapply (SRr_ret_at tfibsegs tfibtbl_rtM tfibtbl_rtM_ok Hwx W E0); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite ?wvb_collapse. split; [reflexivity|].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msR end.
rreg HS (1%bv : bv 5) Q1. rewrite E1 in Q1.
exists (ms_regs msR), (ms_mem msR), mat1, mat'. cbv zeta.
split. { rewrite Q1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split. { apply (regs_preserved_of_st_ok tfibsegs E0 _ _ regs [] HS); [apply env_agree_refl | vm_compute; reflexivity]. }
split. { intros x H1 H2. rewrite (FR2 x H1). rewrite unfill_out by (rewrite UA, UN; lia). exact (FR1 x H1). }
split. { intros x Hx. assert (Hs : ~ (sp - UOD_STK <= bv_unsigned x < sp)) by (clear - Hx Hdisj; unfold UOD_STK in *; lia).
  rewrite (FR2 x Hs). unfold unfill. rewrite UA, UN.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
split. { intros a Ua Hh HP.
  assert (OUT : ~ (sp - UOD_STK <= a < sp) -> ms_mem msR (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros Ho. rewrite (FR2 (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; lia).
    rewrite unfill_out by (rewrite UA, UN, unsigned_lit_small by lia; lia). apply FR1. rewrite unsigned_lit_small by lia; lia. }
  destruct (Z_lt_le_dec a (sp - UOD_STK)) as [L|L]; [|destruct (Z_lt_le_dec a sp) as [L2|L2]].
  - apply (apresent_same (w_H W) mem); [apply OUT; lia | exact HP].
  - eapply (uod_win W E0 _ _ _ sp HS); [reflexivity | reflexivity | reflexivity | reflexivity | exact BV2 | exact Hsp | lia | lia].
  - apply (apresent_same (w_H W) mem); [apply OUT; lia | exact HP]. }
split. { cbn [cfg_model]. apply uod_same_io. }
cbn [cfg_model]. apply (amwf_same (munmap_model (w64 ad) (w64 N) md1)); [apply m_vmmaps_wvb | apply m_vm_lazy_wvb |].
exact (munmap_amwf md1 (w64 ad, w64 N) l1 l2 MW1 EVM).
Qed.
End a.
