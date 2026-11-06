(* LLVMFuzzerTestOneInput 0x8091c (fuzz_manifest.c:306, u = fuzz_copy (uri, un, 1, 0, 0)), segment 0x809e0 (FMW_llvmfP.v
   LF_P2) .. 0x80a24 (LF_P3): u = malloc (un + 1) (`beqz a0` is dead: u >= 4096), s1 := u, memcpy (u, uri, un) when
   un > 0 (__asan_memcpy 0x51a68), then the shadow check of u + un and `sb zero, 0(u + un)`; at 0x80a24 the block u holds
   ub and a NUL. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YCbp YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YC85.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0l ACej FMPstat AE2k ACfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_llvmf0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_crtB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_llvmfP FMW_llvmfD.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- 0x80a0c: a0 := u + un (atom 32, by the alias), the shadow check of the byte at a0 (s5 = the shadow base),
   sb zero, 0(a0) into the 1-byte writable region at atom 32 ---- *)
Definition LF3_A : Z := 0x80a0c.
Definition lf3_blk : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition ss_lf3 : sstate :=
  mkSS LF3_A sr_atoms [lf3_blk] None
    (mkFacts [(32%nat, mkAF 4096 (2 ^ 47 - 16) 0); (21%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] []
       [(SAlu ALU_ADD (SOff 9 0) (SOff 8 0), SOff 32 0)]).
Definition LF3_Bx : sv := SOff 21 0.
Definition LF3_SH : list shent := [mkSHE 32 0 1].

(* ---- pure facts ---- *)
Lemma s3_req : forall m, 0 < m -> req_size m = m.
Proof. intros m Hm. unfold req_size. destruct (Z.eqb_spec m 0); lia. Qed.

Section X. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Hypothesis FB : FmB B.
Hypothesis UNIV : fm_univ B.
Hypothesis AMALLOC : amalloc04_rule tfibsegs B ameter_triv.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy FM_asan_memcpy.
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* ---- blocks ---- *)
(* the block malloc appends is not among the blocks before it *)
Lemma s3_app_new : forall ly S (W : world tfibsegs) mem md l b n,
  AR tfibsegs B ly S W mem md -> ablocks B ly S = l ++ [(b, n)] -> 0 < n -> ~ In (b, n) l.
Proof.
intros ly S W mem md l b n HAR Hbl Hn Hx. apply in_split in Hx as (l1 & l2 & El). subst l.
assert (Hd : zdisjoint (block_rng (b, n)) (block_rng (b, n))).
{ apply (sep_blocks_pos tfibsegs B (AR_laws_ok tfibsegs B) ly S W mem md (b, n) (b, n) l1 l2 [] HAR).
  rewrite Hbl, <- app_assoc. reflexivity. }
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite (s3_req n Hn) in Hd. lia.
Qed.
(* the entry blocks are apart from u *)
Lemma s3_sep : forall cx ly S (W : world tfibsegs) mem md u,
  AR tfibsegs B ly S W mem md ->
  Permutation (ablocks B ly S) ((u, lx_un cx + 1) :: ablocks B (lx_ly cx) (lx_S cx)) ->
  ~ In (u, lx_un cx + 1) (ablocks B (lx_ly cx) (lx_S cx)) ->
  forall b m, In (b, m) (ablocks B (lx_ly cx) (lx_S cx)) -> b + req_size m <= u \/ u + lx_un cx + 1 <= b.
Proof.
intros cx ly S W mem md u HAR HP Hnew b m Hin.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (Hu : In (u, lx_un cx + 1) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
assert (Hb : In (b, m) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); right; exact Hin).
assert (Hne : (b, m) <> (u, lx_un cx + 1)) by (intros Heq; apply Hnew; rewrite <- Heq; exact Hin).
pose proof (sep_blocks tfibsegs B LAWS ly S W mem md b m u (lx_un cx + 1) HAR Hb Hu Hne) as Hd.
pose proof (Zle_0_nat (length (lx_ub cx))) as H0. fold (lx_un cx) in H0.
rewrite (s3_req (lx_un cx + 1)) in Hd by lia.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the facts the segment carries over a step that changes memory only in u's block (below alloc_ceiling) and in the
   stack below the frame (above alloc_ceiling), at an unchanged world *)
Lemma s3_carry : forall cx ly S (W : world tfibsegs) m m' md u,
  lf_base B cx -> AR tfibsegs B ly S W m' md ->
  Permutation (ablocks B ly S) ((u, lx_un cx + 1) :: ablocks B (lx_ly cx) (lx_S cx)) ->
  ~ In (u, lx_un cx + 1) (ablocks B (lx_ly cx) (lx_S cx)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (u <= a < u + lx_un cx + 1) -> ~ (alloc_ceiling <= a < lx_sp0 cx - LF_FRAME) ->
     aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  lf_frame cx W m -> lf_inkept cx W m -> arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) m) ->
  lf_glob2 cx W m ->
  lf_frame cx W m' /\ lf_inkept cx W m' /\ arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) m') /\
  lf_glob2 cx W m'.
Proof.
intros cx ly S W m m' md u HB HAR HP Hnew HV HFR HIK HRO HG.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _).
pose proof HB as (HAP & _ & _ & _ & Hblk & _).
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
assert (FS : LLVMF_STK = 32768) by reflexivity.
assert (Hin_u : In (u, lx_un cx + 1) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_u) as (_ & Hu4 & Huc & _).
pose proof (Zle_0_nat (length (lx_ub cx))) as Hun0. fold (lx_un cx) in Hun0.
rewrite (s3_req (lx_un cx + 1)) in Huc by lia.
pose proof (s3_sep cx ly S W m' md u HAR HP Hnew) as Due.
unfold lx_sp0, LF_FRAME in *.
(* a low byte outside u's block *)
assert (HL : forall a, 0 <= a < alloc_ceiling -> ~ (u <= a < u + lx_un cx + 1) ->
  aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) by (intros a Ha Hn; apply HV; [lia | exact Hn | lia]).
(* an image byte is in no block *)
assert (HI : forall a, in_img tfibsegs a -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a).
{ intros a Hi. pose proof (fm_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. apply HL; [lia|].
  intros Ha. apply (blk_img tfibsegs B LAWS ly S W m' md u (lx_un cx + 1) a HAR Hin_u); [|exact Hi].
  rewrite (s3_req (lx_un cx + 1)) by lia. lia. }
split.
{ apply (lf_frame_kept cx W W m m'); [|exact HFR]. intros a Ha. unfold lx_sp0, LF_FRAME in *.
  apply HV; [lia | lia | lia]. }
split.
{ intros i Hi. rewrite <- (HIK i Hi). destruct (Z.eqb_spec (lx_n cx) 0) as [E0|E0]; [lia|].
  destruct Hblk as [(Hn0 & _) | (Hn & Hpin)]; [lia|].
  pose proof (Permutation_in _ (Permutation_sym HP) (in_cons _ _ _ Hpin)) as Hpin'.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpin') as (_ & Hp4 & Hpc & _).
  rewrite (s3_req (lx_n cx)) in Hpc by lia.
  pose proof (Due _ _ Hpin) as Hd. rewrite (s3_req (lx_n cx)) in Hd by lia.
  apply HL; lia. }
split.
{ intros a Ha Ho He. rewrite (HI a (roP_img a Ha)). exact (HRO a Ha Ho He). }
apply (crt_glob_img W W m m'); [|exact HG]. intros a Ha. exact (HI a (pstat_img a Ha)).
Qed.

(* bytes read back at another address (a copy) *)
Lemma s3_mbyte_of_aview2 : forall (H H' : word -> bool) (m m' : word -> option byte) a a',
  aview tfibsegs H' m' a' = aview tfibsegs H m a -> mbyte tfibsegs (mrestrict H' m') a' = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H H' m m' a a' E. unfold aview in E. cbv beta in E.
destruct (mbyte tfibsegs (mrestrict H' m') a') as [b'|]; destruct (mbyte tfibsegs (mrestrict H m) a) as [b|];
  cbn [option_map] in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma s3_garr8_shift : forall (W W' : world tfibsegs) m m' x d l, garr8 tfibsegs (rdW W m) x l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> aview tfibsegs (w_H W') m' (d + i) = aview tfibsegs (w_H W) m (x + i)) ->
  garr8 tfibsegs (rdW W' m') d l.
Proof.
intros W W' m m' x d l Hg HV j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros k0 Hk0. assert (k0 = 0%nat) as -> by lia.
specialize (Hv 0%nat ltac:(lia)). rewrite <- Hv.
replace (d + Z.of_nat j + Z.of_nat 0) with (d + Z.of_nat j) by lia.
replace (x + Z.of_nat j + Z.of_nat 0) with (x + Z.of_nat j) by lia.
apply s3_mbyte_of_aview2. apply HV. lia.
Qed.
Lemma s3_garr8_vis : forall (W : world tfibsegs) m p l a, garr8 tfibsegs (rdW W m) p l -> p <= a < p + Z.of_nat (length l) ->
  aview tfibsegs (w_H W) m a <> None.
Proof.
intros W m p l a Hg Ha.
destruct (Hg (Z.to_nat (a - p)) ltac:(lia)) as (Hv & _).
specialize (Hv 0%nat ltac:(lia)).
rewrite Z2Nat.id in Hv by lia. replace (p + (a - p) + Z.of_nat 0) with a in Hv by lia.
unfold aview. cbv beta. rewrite Hv. cbn [option_map]. discriminate.
Qed.

(* the resume state at 0x80a0c *)
Lemma lf3_entry : forall (W : world tfibsegs) mem regs u n,
  getr regs 21 = w64 FMW_SB -> 4096 <= u + n <= 2 ^ 47 - 16 ->
  getr regs 8 = w64 n -> getr regs 9 = w64 u -> 0 <= n -> 0 <= u ->
  writable_at tfibsegs (rdW W mem) (u + n) ->
  st_ok tfibsegs (Ereg regs [Z_to_bv 64 (u + n)]) ss_lf3
    (restrict (w_H W) (mkst regs (Z_to_bv 64 LF3_A) mem (seg_rom tfibsegs))).
Proof.
intros W mem regs u n R21 Hun R8 R9 Hn Hu Hw.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Ereg regs [Z_to_bv 64 (u + n)]).
assert (E8 : ew E 8 = Z_to_bv 64 n) by (unfold E; rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 u) by (unfold E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 (u + n)) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
assert (U32 : bv_unsigned (ew E 32) = u + n) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF) by (rewrite E21; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
unfold ss_lf3. apply (entry_st_ok_full tfibsegs); change (Ereg regs [Z_to_bv 64 (u + n)]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lf3_blk. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
  split; [lia|]. split; [lia|]. split; [intros o Ho; replace (u + n + o) with (u + n) by lia; exact Hw|].
  apply Forall_nil.
- apply pairwise_disjoint_of_extents. unfold lf3_blk, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U32, U21. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
  + cbn [f_alias alias_ok]. split; [|exact I]. apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 9 u E9) by lia. rewrite (U_atom E 8 n E8) by lia. rewrite (U_atom E 32 (u + n) E32) by lia.
    apply zcanon_id. unfold M64. lia.
Qed.

(* ---- 0x80a0c .. 0x80a24: the shadow check of u + un and the NUL store. The byte is addressable (SHOK: the 1-byte
   range at u + un inside u's block, range_addressable_of_block), so the tok run takes `bnez a1` (0x80a1c) only to the
   slow path 0x80b08, where `blt a2, a1` goes back to 0x80a20; `jal __asan_report_store1` (0x80b10) is refuted. ---- *)
Lemma lf3_tail : forall cx ly S W regs mem md k u,
  lf_base B cx -> lf_core B cx ly S W regs mem md k -> 0 <= k <= EV_check_no_overread + 1 ->
  Permutation (ablocks B ly S) ((u, lx_un cx + 1) :: ablocks B (lx_ly cx) (lx_S cx)) ->
  ~ In (u, lx_un cx + 1) (ablocks B (lx_ly cx) (lx_S cx)) ->
  lf_glob2 cx W mem -> lx_tn cx <= MANIFEST_MAX -> bytes_at tfibsegs W mem u (lx_ub cx) ->
  getr regs 8 = w64 (lx_un cx) -> getr regs 9 = w64 u -> getr regs 18 = w64 (lx_text cx) ->
  getr regs 19 = w64 (lx_tn cx) ->
  (forall ly' S' W' regs' mem' md' k' u', lf_P3 B cx ly' S' W' regs' mem' md' k' u' ->
     SRr tfibsegs W' (cfg_at tfibsegs LF_P3 regs' mem' md') (lf_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs LF3_A regs mem md) (lf_post B cx).
Proof.
intros cx ly S W regs mem md k u HB HC Hk Hperm Hnew HGl Htn Hbu R8 R9 R18 R19 K3.
pose proof HB as (HAP & _ & _ & _ & Hblk & _).
pose proof HC as (HJ & HFR & Hsp & HKX & R21 & HIK & HRO).
unfold lf_J in HJ.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : LLVMF_STK = 32768) by reflexivity.
pose proof (lx_ranges B cx HB) as (Rk & Rs6 & Rsk & Rn & _ & _ & _ & _ & Run & Rtn & Rub).
pose proof HJ as (HAR & _).
unfold lx_sp0, LF_FRAME in *.
assert (Hin : In (u, lx_un cx + 1) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (Hrq : req_size (lx_un cx + 1) = lx_un cx + 1) by (apply s3_req; lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hu4 & Huc & Happ & Hupres & _).
rewrite Hrq in Huc, Happ, Hupres.
assert (Hw : writable_at tfibsegs (rdW W mem) (u + lx_un cx))
  by (apply (apresent_writable tfibsegs); exact (proj1 (Hupres (u + lx_un cx) ltac:(lia)))).
pose proof (lf3_entry W mem regs u (lx_un cx) R21 ltac:(lia) R8 R9 ltac:(lia) ltac:(lia) Hw) as HS.
set (E := Ereg regs [Z_to_bv 64 (u + lx_un cx)]) in HS.
assert (E32 : bv_unsigned (ew E 32) = u + lx_un cx)
  by (unfold E; rewrite (ew_Ereg_extra regs _ 0); cbn [nth]; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok tfibsegs LF3_Bx LF3_SH E (rdW W (ms_mem (mkst regs (Z_to_bv 64 LF3_A) mem (seg_rom tfibsegs))))).
{ constructor; [|constructor]. cbn [ms_mem].
  apply (shent_ok_of_range tfibsegs (w_H W) mem E LF3_Bx 32 u (lx_un cx + 1) (u + lx_un cx) 0 1).
  - apply (range_addressable_of_block tfibsegs B LAWS ly S W mem md u (lx_un cx + 1) u _ HAR Hin); lia.
  - unfold LF3_Bx. apply U_atom; [unfold E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21 | unfold SHADOW_OFF; lia].
  - apply U_atom; [unfold E; exact (ew_Ereg_extra regs _ 0) | lia].
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app in Happ.
    unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
unfold cfg_at. change (w64 LF3_A) with (Z_to_bv 64 LF3_A).
change mem with (ms_mem (mkst regs (Z_to_bv 64 LF3_A) mem (seg_rom tfibsegs))) in HJ.
aj_run_to_tok fmw_tbl_llvmf_ok HS HJ SHOK fmw_Bspan LF_P3.
{ unfold ss_lf3. cbn [ss_mem].
  eapply awr_ok_cons_gen with (k := 32%nat) (b := u + lx_un cx); [reflexivity | exact E32 | | apply awr_ok_nil].
  intros a Ha. cbn [lf3_blk YP09.r_wlo YP09.r_whi] in Ha.
  left; right; right; left. exists u, (lx_un cx + 1). split; [exact Hin|]. split; [exact Hnew|]. rewrite Hrq. lia. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
lazymatch type of HS with st_ok _ ?Ex _ _ => set (E1 := Ex) in HS, SHOK end.
assert (AG : forall n, (n < 33)%nat -> ew E1 n = ew E n)
  by (intros n Hn; unfold E1; rewrite ?ew_ewset_other by lia; reflexivity).
(* the run changed memory only at u + un *)
assert (HV : forall a, 0 <= a < 2 ^ 64 -> a <> u + lx_un cx ->
  aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hne. apply (aview_eq_of tfibsegs).
  match goal with H : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => apply H end.
  rewrite unsigned_lit_small by lia. unfold ss_lf3. cbn [ss_mem]. intros (r & [<-|[]] & Hr).
  cbn [lf3_blk YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E32 in Hr. lia. }
pose proof HJ as (HARF & _).
destruct (s3_carry cx ly S W mem (ms_mem ms1) _ u HB HARF Hperm Hnew) as (HFRF & HIKF & HROF & HGF).
{ intros a Ha Hn1 Hn2. apply HV; [exact Ha | lia]. }
{ exact HFR. }
{ exact HIK. }
{ exact HRO. }
{ exact HGl. }
(* the NUL at u + un, from the final region *)
pose proof (fmw_region_nth _ _ _ 0 _ HS eq_refl) as HR. cbn [ms_mem restrict] in HR.
pose proof (fmw_field E1 (rdW W (ms_mem ms1)) 32 (u + lx_un cx) [YP09.mkChunk 0 (CVal 1 (SLit 0))] 0 1 0 1 0 1%N
  (SLit 0) 0 HR ltac:(rewrite (AG 32%nat ltac:(lia)); exact E32) ltac:(left; reflexivity) eq_refl ltac:(cbn; lia)
  ltac:(cbn; lia)) as V0.
assert (HuF : cstr_ok tfibsegs W (ms_mem ms1) u (lx_ub cx)).
{ apply (lf_cstr_ok_of_blk B ly S W (ms_mem ms1) _ u (lx_un cx + 1) u (lx_ub cx) HARF Hin ltac:(lia) ltac:(unfold lx_un in *; lia)).
  split; [|exact (lf_cut_nz (lx_uw cx))].
  apply (garr8_app tfibsegs). split.
  - apply (s3_garr8_shift W W mem (ms_mem ms1) u u (lx_ub cx) Hbu). intros i Hi. apply HV; [lia|]. unfold lx_un in *. lia.
  - intros j Hj. cbn [length] in Hj. assert (j = 0%nat) as -> by lia. cbn [nth]. split; [|lia].
    unfold lx_un in V0. exact V0. }
(* the registers at 0x80a24 *)
lazymatch type of HS with st_ok _ _ ?ss _ =>
  assert (QF : forall (r : bv 5) n, sr_get (ss_regs ss) r = SOff n 0 -> (n < 33)%nat -> getr (ms_regs ms1) r = ew E n)
    by (intros r n Hr Hn; rewrite (st_ok_restrict_reg tfibsegs _ _ _ ms1 r HS), Hr, fmw_SOff0; apply AG; exact Hn);
  assert (KA : atoms_kept ss lf_X = true) by (vm_compute; reflexivity) end.
pose proof (QF 2%bv 2%nat ltac:(vm_compute; reflexivity) ltac:(lia)) as F2.
pose proof (QF 8%bv 8%nat ltac:(vm_compute; reflexivity) ltac:(lia)) as F8.
pose proof (QF 9%bv 9%nat ltac:(vm_compute; reflexivity) ltac:(lia)) as F9.
pose proof (QF 18%bv 18%nat ltac:(vm_compute; reflexivity) ltac:(lia)) as F18.
pose proof (QF 19%bv 19%nat ltac:(vm_compute; reflexivity) ltac:(lia)) as F19.
pose proof (QF 21%bv 21%nat ltac:(vm_compute; reflexivity) ltac:(lia)) as F21.
unfold E in F2, F8, F9, F18, F19, F21.
rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl) in F2. rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl) in F8.
rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl) in F9. rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl) in F18.
rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl) in F19. rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl) in F21.
assert (HKF : kept_from (lx_regs cx) (ms_regs ms1) lf_X).
{ intros r Hc HX. destruct (acs_bv r Hc) as [Eu _].
  assert (Hr32 : 0 <= r < 32) by (unfold acallee_saved in Hc; lia).
  rewrite (QF _ (Z.to_nat r) (atoms_kept_get _ lf_X r KA Hc HX) ltac:(lia)).
  unfold E. rewrite (ew_Ereg_nat regs _ (Z.to_nat r) (Z_to_bv 5 r)) by (rewrite Eu; lia).
  exact (HKX r Hc HX). }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E1 _ ms1 HS eq_refl). cbn [ss_pc].
change (mkCfg (mkst (ms_regs ms1) (Z_to_bv 64 LF_P3) (ms_mem ms1) (seg_rom tfibsegs)) ?mm)
  with (cfg_at tfibsegs LF_P3 (ms_regs ms1) (ms_mem ms1) mm).
apply (K3 ly S W (ms_regs ms1) (ms_mem ms1) _ k u).
unfold lf_P3, lf_core, lf_J.
split.
{ split; [exact HJ|]. split; [exact HFRF|].
  split; [unfold lx_sp0, LF_FRAME; unfold spZ at 1; rewrite F2; fold (spZ regs); lia|].
  split; [exact HKF|]. split; [rewrite F21; exact R21|]. split; [exact HIKF | exact HROF]. }
split; [exact Hk|]. split; [exact Hperm|]. split; [exact HGF|]. split; [exact Htn|].
split; [exact HuF|].
split; [rewrite F8; exact R8|]. split; [rewrite F9; exact R9|]. split; [rewrite F18; exact R18 | rewrite F19; exact R19].
Qed.

(* ---- 0x809f0 .. 0x80a0c: `beqz a0` (dead), s1 := u, memcpy (u, uri, un) when un > 0 ---- *)
Lemma lf3_mid : forall cx ly S W regs mem md k u,
  lf_base B cx -> lf_core B cx ly S W regs mem md k -> 0 <= k <= EV_check_no_overread + 1 ->
  Permutation (ablocks B ly S) ((u, lx_un cx + 1) :: ablocks B (lx_ly cx) (lx_S cx)) ->
  ~ In (u, lx_un cx + 1) (ablocks B (lx_ly cx) (lx_S cx)) ->
  lf_glob2 cx W mem -> lx_tn cx <= MANIFEST_MAX ->
  getr regs 8 = w64 (lx_un cx) -> getr regs 10 = w64 u -> getr regs 18 = w64 (lx_text cx) ->
  getr regs 19 = w64 (lx_tn cx) -> getr regs 20 = w64 (lx_uri cx) ->
  (forall ly' S' W' regs' mem' md' k' u', lf_P3 B cx ly' S' W' regs' mem' md' k' u' ->
     SRr tfibsegs W' (cfg_at tfibsegs LF_P3 regs' mem' md') (lf_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs 0x809f0 regs mem md) (lf_post B cx).
Proof.
intros cx ly S W regs mem md k u HB HC Hk Hperm Hnew HGl Htn R8 R10 R18 R19 R20 K3.
pose proof HB as (HAP & _ & _ & _ & Hblk & _).
pose proof HAP as (HAR0 & _ & _ & Hgp & Htp & _ & _ & _ & _).
pose proof HC as (HJ & HFR & Hsp & HKX & R21 & HIK & HRO).
unfold lf_J in HJ.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
pose proof (lx_ranges B cx HB) as (Rk & Rs6 & Rsk & Rn & _ & _ & _ & _ & Run & Rtn & Rub).
assert (FS : LLVMF_STK = 32768) by reflexivity.
pose proof HJ as (HAR & _).
unfold lx_sp0, LF_FRAME in *.
assert (Hin_u : In (u, lx_un cx + 1) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_u) as (_ & Hu4 & Huc & _).
rewrite (s3_req (lx_un cx + 1)) in Huc by lia.
pose proof (s3_sep cx ly S W mem md u HAR Hperm Hnew) as Due.
assert (Hpin : 0 < lx_n cx -> In (lx_p cx, lx_n cx) (ablocks B ly S)).
{ intros Hn. destruct Hblk as [(Hn0 & _) | (_ & Hpe)]; [lia|].
  exact (Permutation_in _ (Permutation_sym Hperm) (in_cons _ _ _ Hpe)). }
assert (Hinb : forall i, 0 <= i < lx_n cx -> 0 <= lx_p cx + i < alloc_ceiling).
{ intros i Hi. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (Hpin ltac:(lia))) as (_ & Hp4 & Hpc & _).
  rewrite (s3_req (lx_n cx)) in Hpc by lia. lia. }
pose proof (fmw_resume_nr W regs [] mem 0x809f0) as HS.
unfold cfg_at. change (w64 0x809f0) with (Z_to_bv 64 0x809f0).
assert (U10 : U (Ereg regs []) (SOff 10 0) = u)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact R10 | lia]).
assert (U8 : U (Ereg regs []) (SOff 8 0) = lx_un cx)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs [] 8 8%bv eq_refl); exact R8 | lia]).
assert (UZ : U (Ereg regs []) (SLit 0) = 0) by (apply U_lit; lia).
(* 0x809f0: beqz a0 (u >= 4096) *)
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0); [exact HS | intros Hb _ | intros _ HS1].
{ exfalso. rewrite branch_eq_U, U10, UZ in Hb. apply Z.eqb_eq in Hb. lia. }
clear HS.
aj_run fmw_tbl_llvmf_ok HS1 HJ.
{ apply awr_ok_nil. }
lazymatch type of HS1 with context [restrict _ ?m] => rename m into ms1 end.
(* 0x809f8: beqz s0 *)
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 8 0) (b := SLit 0); [exact HS1 | intros Hb HS2 | intros Hb HS2];
  rewrite branch_eq_U, U8, UZ in Hb; clear HS1.
- (* un = 0: on to 0x80a0c *)
  apply Z.eqb_eq in Hb.
  aj_run_to fmw_tbl_llvmf_ok HS2 HJ LF3_A.
  { apply awr_ok_nil. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
  crt_sb_nil.
  match goal with H : same_below mem (ms_mem ms2) _ |- _ => rename H into SB end.
  assert (SBc : same_below mem (ms_mem ms2) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB); lia).
  pose proof (fmw_reg_atom _ regs [] _ ms2 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q2.
  pose proof (fmw_reg_atom _ regs [] _ ms2 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q8.
  pose proof (fmw_reg_atom _ regs [] _ ms2 9%bv 10%bv 10 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q9.
  pose proof (fmw_reg_atom _ regs [] _ ms2 18%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q18.
  pose proof (fmw_reg_atom _ regs [] _ ms2 19%bv 19%bv 19 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q19.
  pose proof (fmw_reg_atom _ regs [] _ ms2 21%bv 21%bv 21 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q21.
  assert (Eub : lx_ub cx = []) by (apply length_zero_iff_nil; unfold lx_un in Hb; lia).
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms2 HS2 eq_refl). cbn [ss_pc].
  change (mkCfg (mkst (ms_regs ms2) (Z_to_bv 64 LF3_A) (ms_mem ms2) (seg_rom tfibsegs)) ?mm)
    with (cfg_at tfibsegs LF3_A (ms_regs ms2) (ms_mem ms2) mm).
  apply (lf3_tail cx ly S W (ms_regs ms2) (ms_mem ms2) _ k u HB).
  + split; [exact HJ|].
    split; [apply (lf_frame_below cx W mem (ms_mem ms2) SB); [unfold lx_sp0, LF_FRAME; lia | unfold lx_sp0; lia | exact HFR]|].
    split; [unfold lx_sp0, LF_FRAME; unfold spZ at 1; rewrite Q2; fold (spZ regs); lia|].
    split; [exact (kept_step (w_H W) (lx_regs cx) regs [] _ ms2 (ms_regs ms2) lf_X HKX HS2 ltac:(vm_compute; reflexivity)
                     (fun r _ => eq_refl))|].
    split; [rewrite Q21; exact R21|].
    split; [intros i Hi; rewrite <- (HIK i Hi); apply (aview_below (w_H W) mem (ms_mem ms2) alloc_ceiling _ SBc);
            exact (Hinb i Hi)|].
    exact (arodata_below B W mem (ms_mem ms2) SBc HRO).
  + exact Hk.
  + exact Hperm.
  + exact Hnew.
  + exact (fm_glob_below W mem (ms_mem ms2) _ _ _ _ SBc HGl).
  + exact Htn.
  + rewrite Eub. apply garr8_nil.
  + rewrite Q8. exact R8.
  + rewrite Q9. exact R10.
  + rewrite Q18. exact R18.
  + rewrite Q19. exact R19.
  + exact K3.
- (* un > 0: memcpy (u, uri, un) *)
  apply Z.eqb_neq in Hb.
  assert (Hun1 : 1 <= lx_un cx) by lia.
  aj_run_to fmw_tbl_llvmf_ok HS2 HJ 0x51a68.
  { apply awr_ok_nil. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
  crt_sb_nil.
  match goal with H : same_below mem (ms_mem ms2) _ |- _ => rename H into SB end.
  assert (SBc : same_below mem (ms_mem ms2) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB); lia).
  pose proof (fmw_reg_lit _ (Ereg regs []) _ ms2 1%bv 0x80a0c HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as Q1.
  pose proof (fmw_reg_atom _ regs [] _ ms2 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q2.
  pose proof (fmw_reg_atom _ regs [] _ ms2 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q3.
  pose proof (fmw_reg_atom _ regs [] _ ms2 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q4.
  pose proof (fmw_reg_atom _ regs [] _ ms2 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q8.
  pose proof (fmw_reg_atom _ regs [] _ ms2 9%bv 10%bv 10 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q9.
  pose proof (fmw_reg_atom _ regs [] _ ms2 10%bv 10%bv 10 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q10.
  pose proof (fmw_reg_atom _ regs [] _ ms2 11%bv 20%bv 20 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q11.
  pose proof (fmw_reg_atom _ regs [] _ ms2 12%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q12.
  pose proof (fmw_reg_atom _ regs [] _ ms2 18%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q18.
  pose proof (fmw_reg_atom _ regs [] _ ms2 19%bv 19%bv 19 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q19.
  pose proof (fmw_reg_atom _ regs [] _ ms2 21%bv 21%bv 21 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q21.
  assert (Hsp2 : spZ (ms_regs ms2) = spZ (lx_regs cx) + -64) by (unfold spZ at 1; rewrite Q2; fold (spZ regs); lia).
  assert (Hgp2 : getr (ms_regs ms2) 3 = w64 (as_gp B))
    by (rewrite Q3, (kept_get _ _ _ 3%bv HKX ltac:(fmw_cs_side) ltac:(fmw_notin)); exact Hgp).
  assert (Htp2 : getr (ms_regs ms2) 4 = w64 (as_tp B))
    by (rewrite Q4, (kept_get _ _ _ 4%bv HKX ltac:(fmw_cs_side) ltac:(fmw_notin)); exact Htp).
  pose proof HJ as (HAR2 & _).
  assert (HIK2 : lf_inkept cx W (ms_mem ms2)).
  { intros i Hi. rewrite <- (HIK i Hi). apply (aview_below (w_H W) mem (ms_mem ms2) alloc_ceiling _ SBc). exact (Hinb i Hi). }
  destruct (lf_src_rd B cx ly S W (ms_mem ms2) _ HB HAR2 HIK2 Hpin) as (Hsrc & _ & _ & _ & _ & _ & Huri & _).
  pose proof Hsrc as (Hbu & Hx4 & Hxc & Hxam & Hxra & Hxhv).
  fold (lx_un cx) in Hxc, Hxam, Hxra, Hxhv.
  destruct (Huri ltac:(lia)) as (Hxp & Hxpn).
  assert (Hpe : In (lx_p cx, lx_n cx) (ablocks B (lx_ly cx) (lx_S cx)))
    by (destruct Hblk as [(Hn0 & _) | (_ & Hpe)]; [lia | exact Hpe]).
  pose proof (Due _ _ Hpe) as Hdx. rewrite (s3_req (lx_n cx)) in Hdx by lia.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms2 HS2 eq_refl). cbn [ss_pc].
  change (Z_to_bv 64 0x51a68) with (Z_to_bv 64 FM_asan_memcpy).
  eapply SRr_bind.
  { apply (YC85.aj_intrin_atS tfibsegs B LAWS HSL OCpy FM_asan_memcpy AICPY W (ms_regs ms2) (ms_mem ms2) LLVMF_STK
      (spZ (lx_regs cx)) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx) [] ly S _ k
      u (lx_uri cx) (lx_un cx) (-64) (Z_to_bv 64 0x80a0c)).
    - exact HJ.
    - rewrite Q10. exact R10.
    - rewrite Q11. exact R20.
    - rewrite Q12. exact R8.
    - lia.
    - lia.
    - lia.
    - exact Hsp2.
    - reflexivity.
    - lia.
    - unfold ESTACK. lia.
    - exact Hgp2.
    - exact Htp2.
    - exact Q1.
    - apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
    - intros a Ha. split.
      + right; right; left. exists u, (lx_un cx + 1). split; [exact Hin_u|]. split; [exact Hnew|].
        rewrite (s3_req (lx_un cx + 1)) by lia. lia.
      + unfold ESTACK. lia.
    - apply (amem_range_of_block tfibsegs B LAWS ly S W (ms_mem ms2) _ u (lx_un cx + 1) u (lx_un cx) HAR2 Hin_u);
        [lia | rewrite (s3_req (lx_un cx + 1)) by lia; lia].
    - apply (range_addressable_of_block tfibsegs B LAWS ly S W (ms_mem ms2) _ u (lx_un cx + 1) u (lx_un cx) HAR2 Hin_u);
        [lia | rewrite (s3_req (lx_un cx + 1)) by lia; lia].
    - intros _. apply (shadow_hull_vis_of_block tfibsegs B LAWS ly S W (ms_mem ms2) _ u (lx_un cx + 1) u (lx_un cx) HAR2 Hin_u);
        [lia | rewrite (s3_req (lx_un cx + 1)) by lia; lia | lia].
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split; [|rewrite Hsp2; unfold ESTACK; lia].
        apply (s3_garr8_vis W (ms_mem ms2) (lx_uri cx) (lx_ub cx) a Hbu). fold (lx_un cx). lia. }
      split; [lia|]. split; [exact Hxam|]. split; [exact Hxra | exact Hxhv]. }
  intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & H10' & Heff & Hfr & Hpres3 & _).
  change (forall i, 0 <= i < lx_un cx ->
    aview tfibsegs (w_H W) mem3 (u + i) = aview tfibsegs (w_H W) (ms_mem ms2) (lx_uri cx + i)) in Heff.
  pose proof HJ3 as (HAR3 & _).
  destruct (s3_carry cx ly S W (ms_mem ms2) mem3 _ u HB HAR3 Hperm Hnew) as (HFR3 & HIK3 & HRO3 & HG3).
  { intros a Ha Hn1 Hn2. unfold lx_sp0, LF_FRAME in Hn2. apply Hfr; [exact Ha | lia | unfold ESTACK; lia]. }
  { apply (lf_frame_below cx W mem (ms_mem ms2) SB); [unfold lx_sp0, LF_FRAME; lia | unfold lx_sp0; lia | exact HFR]. }
  { exact HIK2. }
  { exact (arodata_below B W mem (ms_mem ms2) SBc HRO). }
  { exact (fm_glob_below W mem (ms_mem ms2) _ _ _ _ SBc HGl). }
  assert (P2 : getr regs3 2 = getr (ms_regs ms2) 2) by exact (fmw_pres _ _ 2%bv HP3 ltac:(fmw_cs_side)).
  assert (P8 : getr regs3 8 = getr (ms_regs ms2) 8) by exact (fmw_pres _ _ 8%bv HP3 ltac:(fmw_cs_side)).
  assert (P9 : getr regs3 9 = getr (ms_regs ms2) 9) by exact (fmw_pres _ _ 9%bv HP3 ltac:(fmw_cs_side)).
  assert (P18 : getr regs3 18 = getr (ms_regs ms2) 18) by exact (fmw_pres _ _ 18%bv HP3 ltac:(fmw_cs_side)).
  assert (P19 : getr regs3 19 = getr (ms_regs ms2) 19) by exact (fmw_pres _ _ 19%bv HP3 ltac:(fmw_cs_side)).
  assert (P21 : getr regs3 21 = getr (ms_regs ms2) 21) by exact (fmw_pres _ _ 21%bv HP3 ltac:(fmw_cs_side)).
  change (mkCfg (mkst regs3 (Z_to_bv 64 0x80a0c) mem3 (seg_rom tfibsegs)) md3) with (cfg_at tfibsegs LF3_A regs3 mem3 md3).
  apply (lf3_tail cx ly S W regs3 mem3 md3 k u HB).
  + split; [exact HJ3|]. split; [exact HFR3|].
    split; [unfold lx_sp0, LF_FRAME; unfold spZ at 1; rewrite P2; fold (spZ (ms_regs ms2)); lia|].
    split; [exact (kept_step (w_H W) (lx_regs cx) regs [] _ ms2 regs3 lf_X HKX HS2 ltac:(vm_compute; reflexivity) HP3)|].
    split; [rewrite P21, Q21; exact R21|]. split; [exact HIK3 | exact HRO3].
  + exact Hk.
  + exact Hperm.
  + exact Hnew.
  + exact HG3.
  + exact Htn.
  + apply (s3_garr8_shift W W (ms_mem ms2) mem3 (lx_uri cx) u (lx_ub cx) Hbu).
    intros i Hi. fold (lx_un cx) in Hi. exact (Heff i Hi).
  + rewrite P8, Q8. exact R8.
  + rewrite P9, Q9. exact R10.
  + rewrite P18, Q18. exact R18.
  + rewrite P19, Q19. exact R19.
  + exact K3.
Qed.

(* ---- 0x809e0 .. 0x809f0: u = malloc (un + 1) ---- *)
Lemma lf_seg3 : forall cx ly S W regs mem md k, lf_base B cx -> lf_P2 B cx ly S W regs mem md k ->
  (forall ly' S' W' regs' mem' md' k' u, lf_P3 B cx ly' S' W' regs' mem' md' k' u ->
     SRr tfibsegs W' (cfg_at tfibsegs LF_P3 regs' mem' md') (lf_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs LF_P2 regs mem md) (lf_post B cx).
Proof.
intros cx ly S W regs mem md k HB HP2 K3.
pose proof HB as (HAP & Hra & H10 & H11 & Hcase & Hgarr & Hfrs & Hev & Hbb & HRO0 & HG0 & Hc0 & Hc1 & Hlv).
pose proof HAP as (HAR0 & Hra' & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
destruct HP2 as ((HJ & HFR & Hsp & HKf & H21 & HIN & HRO) & Hk & Hperm & HGl & Htn & R8 & R18 & R19 & R20).
unfold lf_J, lx_sp0, LF_FRAME in *.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : LLVMF_STK = 32768) by reflexivity.
assert (FE : EV_check_no_overread + 1 < EV_LLVMF) by (vm_compute; reflexivity).
pose proof (lx_ranges B cx HB) as (Hk255 & Hs6 & Hsk & Hn26 & Hn0 & Hnp & Hluw & Hltw & Hun & Htn' & Hub255).
assert (Hun255 : lx_un cx <= 255) by (unfold lx_un; lia).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _).
pose proof (fmw_resume_nr W regs [] mem LF_P2) as HS.
unfold cfg_at. change (w64 LF_P2) with (Z_to_bv 64 LF_P2).
aj_run_to fmw_tbl_llvmf_ok HS HJ 0x52dbc.
{ apply awr_ok_nil. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms2 end.
crt_sb_nil.
match goal with H : same_below mem (ms_mem ms2) _ |- _ => rename H into SB1 end.
assert (SB1c : same_below mem (ms_mem ms2) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB1); lia).
pose proof (fmw_reg_lit _ (Ereg regs []) _ ms2 1%bv 0x809f0 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as Q1.
pose proof (fmw_reg_atom _ regs [] _ ms2 2%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl) as Q2.
pose proof (fmw_reg_atom _ regs [] _ ms2 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as Q3.
pose proof (fmw_reg_atom _ regs [] _ ms2 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as Q4.
pose proof (fmw_reg_atom _ regs [] _ ms2 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as Q8.
pose proof (fmw_reg_atom _ regs [] _ ms2 18%bv 18%bv 18 HS ltac:(vm_compute; reflexivity) eq_refl) as Q18.
pose proof (fmw_reg_atom _ regs [] _ ms2 19%bv 19%bv 19 HS ltac:(vm_compute; reflexivity) eq_refl) as Q19.
pose proof (fmw_reg_atom _ regs [] _ ms2 20%bv 20%bv 20 HS ltac:(vm_compute; reflexivity) eq_refl) as Q20.
pose proof (fmw_reg_atom _ regs [] _ ms2 21%bv 21%bv 21 HS ltac:(vm_compute; reflexivity) eq_refl) as Q21.
assert (E8 : ew (Ereg regs []) 8 = Z_to_bv 64 (lx_un cx)) by (rewrite (ew_Ereg_nat regs [] 8 8%bv eq_refl); exact R8).
(* a0 = un + 1 + (un + 1 == 0) = un + 1 *)
assert (Q10 : getr (ms_regs ms2) 10 = w64 (lx_un cx + 1)).
{ eapply (crt_reg_U _ _ _ ms2 10%bv); [exact HS | vm_compute; reflexivity |].
  rewrite !U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off _ 8 (lx_un cx) 1 E8) by lia. rewrite U_SLit.
  change (zcanon 1) with 1. destruct (Z.ltb_spec (lx_un cx + 1) 1); [lia|].
  rewrite (zcanon_id 0) by (unfold M64; lia). rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
assert (Hsp2 : spZ (ms_regs ms2) = spZ (lx_regs cx) + -64) by (unfold spZ at 1; rewrite Q2; fold (spZ regs); lia).
assert (Hgp2 : getr (ms_regs ms2) 3 = w64 (as_gp B))
  by (rewrite Q3, (kept_get _ _ _ 3%bv HKf ltac:(fmw_cs_side) ltac:(fmw_notin)); exact Hgp).
assert (Htp2 : getr (ms_regs ms2) 4 = w64 (as_tp B))
  by (rewrite Q4, (kept_get _ _ _ 4%bv HKf ltac:(fmw_cs_side) ltac:(fmw_notin)); exact Htp).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms2 HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 0x52dbc) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite (fb_code B FB); reflexivity).
eapply SRr_bind.
{ apply (YC85.amalloc04_sub tfibsegs B LAWS HSL ameter_triv AMALLOC W (ms_regs ms2) (ms_mem ms2)
    LLVMF_STK (spZ (lx_regs cx)) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx) [] ly S _ k
    (lx_un cx + 1) (-64) (Z_to_bv 64 0x809f0) []).
  - exact HJ.
  - exact Q10.
  - unfold MALLOC_MAX. lia.
  - rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ Hperm), <- (blocks_bytes_bsum B (lx_ly cx) (lx_S cx)).
    unfold LIVE_LIB, LIVE_MAX in *. lia.
  - exact Hsp2.
  - reflexivity.
  - lia.
  - unfold ASTACK. lia.
  - exact Hgp2.
  - exact Htp2.
  - exact Q1.
  - apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - first [ lia | (unfold EV_LLVMF, EV_check_no_overread, EV_check_reject_clean_starved, EV_check_round_trip, EV_names,
                     EV_MAX in *; lia) ].
  - apply (achain_chain_pre ly _ (spZ (ms_regs ms2)) (lx_un cx) [] (ms_regs ms2)).
    + apply achain_low. lia.
    + lia.
    + unfold s0Z. rewrite Q8, R8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - apply UNIV. rewrite call_trace_nil, (fb_code B FB).
    assert (RA : raZ (ms_regs ms2) = 0x809f0) by (unfold raZ; rewrite Q1; apply unsigned_lit_small; lia).
    rewrite RA. apply memZL_In. vm_compute. reflexivity.
  - exact I. }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & u & -> & HJ2 & HPr & H10r & _ & Hu4 & Hbl & HK & _ & HJs).
(* back at 0x809f0 *)
destruct HK as (KK1 & _ & KK3 & _).
pose proof HJ2 as (HAR2 & _).
assert (Hnew0 : ~ In (u, lx_un cx + 1) (ablocks B ly S))
  by exact (s3_app_new ly2 S2 W2 mem2 _ _ u (lx_un cx + 1) HAR2 Hbl ltac:(lia)).
assert (Hnew : ~ In (u, lx_un cx + 1) (ablocks B (lx_ly cx) (lx_S cx)))
  by (intros Hi; apply Hnew0; exact (Permutation_in _ (Permutation_sym Hperm) Hi)).
assert (Hperm2 : Permutation (ablocks B ly2 S2) ((u, lx_un cx + 1) :: ablocks B (lx_ly cx) (lx_S cx))).
{ rewrite Hbl. eapply Permutation_trans; [apply Permutation_sym, Permutation_cons_append|]. apply perm_skip. exact Hperm. }
assert (Hinc : forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2))
  by (intros x Hx; rewrite Hbl; apply in_or_app; left; exact Hx).
pose proof HJs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2s & _).
assert (HFR2 : lf_frame cx W2 mem2).
{ apply (lf_frame_kept cx W W2 (ms_mem ms2) mem2).
  - intros a Ha. unfold lx_sp0, LF_FRAME in Ha. apply KK1; [lia | unfold ASTACK; lia].
  - apply (lf_frame_below cx W mem (ms_mem ms2) SB1); [unfold lx_sp0, LF_FRAME; lia | unfold lx_sp0; lia | exact HFR]. }
assert (HIK2 : lf_inkept cx W2 mem2).
{ intros i Hi. rewrite <- (HIN i Hi).
  destruct Hcase as [(Hn0' & _) | (Hn & Hpin)]; [lia|].
  pose proof (Permutation_in _ (Permutation_sym Hperm) Hpin) as Hpin'.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpin') as (_ & Hp4 & Hpc & _).
  rewrite (s3_req (lx_n cx)) in Hpc by lia.
  rewrite (F2s (lx_p cx) (lx_n cx) i Hpin' (Hinc _ Hpin') ltac:(rewrite s3_req by lia; lia) (inFP_nil _)).
  apply (aview_below (w_H W) mem (ms_mem ms2) alloc_ceiling _ SB1c). lia. }
assert (HRO2 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W2) mem2))
  by exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJs nil_closed nil_not_roP (arodata_below B W mem (ms_mem ms2) SB1c HRO)).
assert (HG2 : lf_glob2 cx W2 mem2).
{ unfold lf_glob2 in *. apply (crt_glob_img W W2 (ms_mem ms2) mem2).
  - intros a Ha. destruct (fb_pstat B FB a Ha) as [N1 N2]. exact (KK3 a (pstat_img a Ha) N1 N2).
  - exact (fm_glob_below W mem (ms_mem ms2) _ _ _ _ SB1c HGl). }
assert (P2 : getr regs2 2 = getr (ms_regs ms2) 2) by exact (fmw_pres _ _ 2%bv HPr ltac:(fmw_cs_side)).
assert (P8 : getr regs2 8 = getr (ms_regs ms2) 8) by exact (fmw_pres _ _ 8%bv HPr ltac:(fmw_cs_side)).
assert (P18 : getr regs2 18 = getr (ms_regs ms2) 18) by exact (fmw_pres _ _ 18%bv HPr ltac:(fmw_cs_side)).
assert (P19 : getr regs2 19 = getr (ms_regs ms2) 19) by exact (fmw_pres _ _ 19%bv HPr ltac:(fmw_cs_side)).
assert (P20 : getr regs2 20 = getr (ms_regs ms2) 20) by exact (fmw_pres _ _ 20%bv HPr ltac:(fmw_cs_side)).
assert (P21 : getr regs2 21 = getr (ms_regs ms2) 21) by exact (fmw_pres _ _ 21%bv HPr ltac:(fmw_cs_side)).
assert (HKX2 : kept_from (lx_regs cx) regs2 lf_X)
  by exact (kept_step (w_H W) (lx_regs cx) regs [] _ ms2 regs2 lf_X HKf HS ltac:(vm_compute; reflexivity) HPr).
change (mkCfg (mkst regs2 (Z_to_bv 64 0x809f0) mem2 (seg_rom tfibsegs)) md2) with (cfg_at tfibsegs 0x809f0 regs2 mem2 md2).
apply (lf3_mid cx ly2 S2 W2 regs2 mem2 md2 (k + 1) u HB).
- split; [exact HJ2|]. split; [exact HFR2|].
  split; [unfold lx_sp0, LF_FRAME, spZ at 1; rewrite P2; fold (spZ (ms_regs ms2)); lia|].
  split; [exact HKX2|]. split; [rewrite P21, Q21; exact H21|]. split; [exact HIK2 | exact HRO2].
- lia.
- exact Hperm2.
- exact Hnew.
- exact HG2.
- exact Htn.
- rewrite P8, Q8. exact R8.
- exact H10r.
- rewrite P18, Q18. exact R18.
- rewrite P19, Q19. exact R19.
- rewrite P20, Q20. exact R20.
- exact K3.
Qed.
End X.
