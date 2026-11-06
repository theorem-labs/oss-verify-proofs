(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_llvmfS4.v at a working branch 79d8c0f1b8f, re-walked on B's
   instructions (fuzz_manifest.asan-ubsan objdump, B 0x80ac0 .. 0x80b0c and the shadow slow path 0x80bc8 .. 0x80bd0).
   Same statements as A, re-keyed to B's cuts (LF_P3 0x80ac0, LF_P4 0x80b0c). B adds two UBSan pointer-overflow guards
   whose taken side is the shared trap block L+0x224 = 0x80ba0 (`unimp`): 0x80ae4 `not a0, s4` + 0x80ae8
   `bltu a0, s3, 0x80ba0` (t + tn wraps) and 0x80b00 `li a1, -1` + 0x80b08 `beq a0, a1, 0x80ba0` (t + tn = 2^64 - 1).
   s4_tail proves both not taken inline with B5's class lemmas (lib/B/FMTrapB.v, a working branch c89f3cdf72d;
   (internal path) rows 54 and 55): 0x80ae8 K2 fmt_not_ltu_not, 0x80b08 K1 fmt_eq_not, each from
   t + tn <= 2^47 - 16 in a cleared lemma; s4_mid kills `beqz a0, 0x80ba4` (0x80ac8, __asan_handle_no_return; abort; the
   second `unimp` at 0x80bac) from t >= 4096. So no path of this segment reaches 0x80ba0 or 0x80bac.
   Imports per the B core rule (a Theorem Labs lane, core c22f1ae4253). *)
(* LLVMFuzzerTestOneInput 0x8097c (fuzz_manifest.c:293-321), segment 0x80ac0 .. 0x80b0c (and the slow path of its shadow
   check, 0x80bc8 .. 0x80bd0): t = malloc (tn + 1) (`beqz a0` is dead: t >= 4096), s4 := t, memcpy (t, text, tn) when
   tn > 0 (__asan_memcpy 0x51ac8), the guard on t + tn, then the shadow check of t + tn, `sb zero, 0(t + tn)` and the guard
   t + tn <> -1; at 0x80b0c (LF_P4) the block t holds tb and a NUL, and u still holds ub and its NUL. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YF0l YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YE2k YCfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_llvmf0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_llvmfP FMW_llvmfD.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMTrapB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- pure facts ---- *)
Lemma s4_zdisj_sym : forall a b, zdisjoint a b -> zdisjoint b a.
Proof. intros a b H. unfold zdisjoint in *. lia. Qed.
Lemma s4_pairwise_perm : forall (l l' : list (Z * Z)), Permutation l l' ->
  pairwise zdisjoint l -> pairwise zdisjoint l'.
Proof.
intros l l' H. induction H as [| x l1 l2 H IH | x y l | l1 l2 l3 H1 IH1 H2 IH2]; intros P; cbn [pairwise] in *.
- exact P.
- destruct P as [HF P]. split; [|exact (IH P)].
  apply Forall_forall. intros z Hz.
  exact (proj1 (Forall_forall _ _) HF z (Permutation_in z (Permutation_sym H) Hz)).
- destruct P as [HFy [HFx Pl]].
  inversion HFy as [|a0 l0 Hyx HFyl]; subst.
  split; [constructor; [exact (s4_zdisj_sym y x Hyx) | exact HFx] | split; [exact HFyl | exact Pl]].
- exact (IH2 (IH1 P)).
Qed.
Lemma s4_req : forall m, 0 < m -> req_size m = m.
Proof. intros m Hm. unfold req_size. destruct (Z.eqb_spec m 0); lia. Qed.

(* ---- 0x80ae4: a0 := not t, the guard 0x80ae8; a0 := t + tn (atom 32, by the alias), the shadow check of the byte at a0
   (s5 = the shadow base), a1 := -1, sb zero, 0(a0) into the 1-byte writable region at atom 32 (a Theorem Labs lane's recipe,
   FMW_llvmfS3.v), the guard 0x80b08 ---- *)
Definition LF4_A : Z := 0x80ae4.
Definition lf4_blk : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition ss_lf4 : sstate :=
  mkSS LF4_A sr_atoms [lf4_blk] None
    (mkFacts [(32%nat, mkAF 4096 (2 ^ 47 - 16) 0); (21%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] []
       [(SAlu ALU_ADD (SOff 20 0) (SOff 19 0), SOff 32 0)]).
Definition LF4_Bx : sv := SOff 21 0.
Definition LF4_SH : list shent := [mkSHE 32 0 1].

(* ---- the facts that refute the two UBSan guards (B5's classes, lib/B/FMTrapB.v at a working branch c89f3cdf72d;
   FM-B-TRAPS.md rows 54, 55), each in a cleared context ---- *)
(* 0x80ae8 `bltu (not t), tn, 0x80ba0`, class K2 (fmt_not_ltu_not): t + tn < 2^64 *)
Lemma s4_g1 : forall E p n vp vn, ew E p = Z_to_bv 64 vp -> ew E n = Z_to_bv 64 vn -> 0 <= vp -> 0 <= vn ->
  vp + vn <= 2 ^ 47 - 16 -> U E (SOff p 0) + U E (SOff n 0) < 2 ^ 64.
Proof. intros E p n vp vn Hp Hn Hp0 Hn0 H. rewrite (U_atom E p vp Hp), (U_atom E n vn Hn) by lia. lia. Qed.
(* 0x80b08 `beq (t + tn), -1, 0x80ba0`, class K1 (fmt_eq_not): t + tn <> 2^64 - 1 *)
Lemma s4_g2 : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v <= 2 ^ 47 - 16 -> zcanon k = 2 ^ 64 - 1 ->
  U E (SOff n 0) <> U E (SLit k).
Proof. intros E n v k Hn Hv Hk. rewrite (U_atom E n v Hn) by lia. rewrite U_SLit, Hk. lia. Qed.
(* a run from a state whose one region is t's NUL byte (atom 32) writes only inside t's new block *)
Ltac s4_awr Ex32 Hin_t Hnew Hrq tt sz :=
  lazymatch goal with |- context [ss_mem ?s] =>
    let rs := eval vm_compute in (ss_mem s) in change (ss_mem s) with rs end;
  eapply awr_ok_cons_gen with (k := 32%nat); [reflexivity | exact Ex32 | | apply awr_ok_nil];
  let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; left; right; right; left;
  exists tt, sz; split; [exact Hin_t|]; split; [exact Hnew|]; rewrite Hrq; lia.
(* an address a <> t + tn is outside that region's window (the goal of a run's frame_of) *)
Ltac s4_notin Ex32 :=
  rewrite unsigned_lit_small by lia;
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end;
  destruct Hin as [<-|[]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite Ex32 in Hr; lia.

Section X. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Hypothesis FB : FmB B.
Hypothesis UNIV : fm_univ B.
Hypothesis AMALLOC : amalloc04_rule tfibsegs B ameter_triv.
Hypothesis AICPY : aintrin_realizes tfibsegs B OCpy FM_asan_memcpy.
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* the blocks of a state, listed in any order, are pairwise apart *)
Lemma s4_perm_sep : forall ly S (W : world tfibsegs) mem md l,
  AR tfibsegs B ly S W mem md -> Permutation (ablocks B ly S) l ->
  pairwise zdisjoint (map (fun b : Z * Z => (fst b, req_size (snd b))) l).
Proof.
intros ly S W mem md l HAR HP.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
exact (s4_pairwise_perm _ _ (Permutation_map _ HP) Hp).
Qed.
(* the walk's blocks at P4: t, u and the entry blocks, apart *)
Lemma s4_sep : forall cx ly S (W : world tfibsegs) mem md t u,
  AR tfibsegs B ly S W mem md ->
  Permutation (ablocks B ly S) ((t, lx_tn cx + 1) :: (u, lx_un cx + 1) :: ablocks B (lx_ly cx) (lx_S cx)) ->
  (u + lx_un cx + 1 <= t \/ t + lx_tn cx + 1 <= u) /\
  (forall b m, In (b, m) (ablocks B (lx_ly cx) (lx_S cx)) -> b + req_size m <= t \/ t + lx_tn cx + 1 <= b) /\
  (forall b m, In (b, m) (ablocks B (lx_ly cx) (lx_S cx)) -> b + req_size m <= u \/ u + lx_un cx + 1 <= b).
Proof.
intros cx ly S W mem md t u HAR HP.
pose proof (s4_perm_sep ly S W mem md _ HAR HP) as Hp.
pose proof (lx_tn_nonneg := Zle_0_nat (length (lx_tb cx))).
pose proof (lx_un_nonneg := Zle_0_nat (length (lx_ub cx))).
fold (lx_tn cx) in lx_tn_nonneg. fold (lx_un cx) in lx_un_nonneg.
cbn [map pairwise fst snd] in Hp. destruct Hp as [HFt [HFu _]].
inversion HFt as [|a0 l0 Htu HFt']; subst.
rewrite (s4_req (lx_tn cx + 1)) in Htu, HFt' by lia. rewrite (s4_req (lx_un cx + 1)) in Htu, HFu by lia.
unfold zdisjoint in Htu. cbn [fst snd] in Htu.
split; [lia|].
split.
- intros b m Hin. pose proof (proj1 (Forall_forall _ _) HFt' (b, req_size m)
    (in_map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) _ (b, m) Hin)) as H.
  unfold zdisjoint in H. cbn [fst snd] in H. lia.
- intros b m Hin. pose proof (proj1 (Forall_forall _ _) HFu (b, req_size m)
    (in_map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) _ (b, m) Hin)) as H.
  unfold zdisjoint in H. cbn [fst snd] in H. lia.
Qed.

(* fm's statics ride through any step that keeps their bytes *)
Lemma s4_glob_img : forall (W W' : world tfibsegs) m m' live peak cnt fail,
  (forall a, inFP FM_PSTAT_FP a -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  fm_glob tfibsegs W m live peak cnt fail -> fm_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' live peak cnt fail HK (G1 & G2 & G3 & G4 & R).
assert (VK : forall g v, In (g, g + 8) FM_PSTAT_FP ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W') m') g 8 v).
{ intros g v Hg Hv. eapply (val_mem_kept tfibsegs); [|exact Hv]. intros k Hk. apply HK.
  apply (inFP_FM_PSTAT_FP g Hg). cbn in Hk. lia. }
unfold fm_glob, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply VK; [cbv [FM_PSTAT_FP In]; repeat (first [left; reflexivity | right]) | exact G1]|].
split; [apply VK; [cbv [FM_PSTAT_FP In]; repeat (first [left; reflexivity | right]) | exact G2]|].
split; [apply VK; [cbv [FM_PSTAT_FP In]; repeat (first [left; reflexivity | right]) | exact G3]|].
split; [apply VK; [cbv [FM_PSTAT_FP In]; repeat (first [left; reflexivity | right]) | exact G4]|].
exact R.
Qed.

(* a register the run left as the computed value v, U E v = z *)
Lemma s4_reg_U : forall (H : word -> bool) E ss ms (r : bv 5) v z,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = v -> U E v = z -> getr (ms_regs ms) r = w64 z.
Proof.
intros H E ss ms r v z HS Hr Hz. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. unfold w64. rewrite <- Hz.
unfold U. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* the facts the segment carries over a step that changes memory only in t's block (below alloc_ceiling) and in the
   stack below the frame (above alloc_ceiling), at an unchanged world *)
Lemma s4_carry : forall cx ly S (W : world tfibsegs) m m' md t u,
  lf_base B cx -> AR tfibsegs B ly S W m' md ->
  Permutation (ablocks B ly S) ((t, lx_tn cx + 1) :: (u, lx_un cx + 1) :: ablocks B (lx_ly cx) (lx_S cx)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (t <= a < t + lx_tn cx + 1) -> ~ (alloc_ceiling <= a < lx_sp0 cx - LF_FRAME) ->
     aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  lf_frame cx W m -> lf_inkept cx W m -> arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) m) ->
  lf_glob2 cx W m -> cstr_ok tfibsegs W m u (lx_ub cx) ->
  lf_frame cx W m' /\ lf_inkept cx W m' /\ arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) m') /\
  lf_glob2 cx W m' /\ cstr_ok tfibsegs W m' u (lx_ub cx).
Proof.
intros cx ly S W m m' md t u HB HAR HP HV HFR HIK HRO HG Hu.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _).
pose proof HB as (HAP & _ & _ & _ & Hblk & _).
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
assert (FS : LLVMF_STK = 32768) by reflexivity.
assert (Hin_t : In (t, lx_tn cx + 1) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
assert (Hin_u : In (u, lx_un cx + 1) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_t) as (_ & Ht4 & Htc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_u) as (_ & Hu4 & Huc & _).
pose proof (Zle_0_nat (length (lx_tb cx))) as Htn0. fold (lx_tn cx) in Htn0.
pose proof (Zle_0_nat (length (lx_ub cx))) as Hun0. fold (lx_un cx) in Hun0.
rewrite (s4_req (lx_tn cx + 1)) in Htc by lia. rewrite (s4_req (lx_un cx + 1)) in Huc by lia.
destruct (s4_sep cx ly S W m' md t u HAR HP) as (Dtu & Dte & Due).
unfold lx_sp0, LF_FRAME in *.
(* a low byte outside t's block *)
assert (HL : forall a, 0 <= a < alloc_ceiling -> ~ (t <= a < t + lx_tn cx + 1) ->
  aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) by (intros a Ha Hn; apply HV; [lia | exact Hn | lia]).
(* an image byte is in no block *)
assert (HI : forall a, in_img tfibsegs a -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a).
{ intros a Hi. pose proof (fm_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. apply HL; [lia|].
  intros Ha. apply (blk_img tfibsegs B LAWS ly S W m' md t (lx_tn cx + 1) a HAR Hin_t); [|exact Hi].
  rewrite (s4_req (lx_tn cx + 1)) by lia. lia. }
split.
{ apply (lf_frame_kept cx W W m m'); [|exact HFR]. intros a Ha. unfold lx_sp0, LF_FRAME in *.
  apply HV; [lia | lia | lia]. }
split.
{ intros i Hi. rewrite <- (HIK i Hi). destruct (Z.eqb_spec (lx_n cx) 0) as [E0|E0]; [lia|].
  destruct Hblk as [(Hn0 & _) | (Hn & Hpin)]; [lia|].
  pose proof (Permutation_in _ (Permutation_sym HP) (in_cons _ _ _ (in_cons _ _ _ Hpin))) as Hpin'.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpin') as (_ & Hp4 & Hpc & _).
  rewrite (s4_req (lx_n cx)) in Hpc by lia.
  pose proof (Dte _ _ Hpin) as Hd. rewrite (s4_req (lx_n cx)) in Hd by lia.
  apply HL; lia. }
split.
{ intros a Ha Ho He. rewrite (HI a (roP_img a Ha)). exact (HRO a Ha Ho He). }
split.
{ apply (s4_glob_img W W m m'); [|exact HG]. intros a Ha. exact (HI a (pstat_img a Ha)). }
apply (lf_cstr_ok_view B ly S W W m m' md u (lx_un cx + 1) u (lx_ub cx) HAR Hin_u ltac:(lia) ltac:(unfold lx_un in *; lia)).
- intros a Ha. unfold lx_un in *. apply HL; lia.
- exact Hu.
Qed.

(* bytes read back at another address (a copy) *)
Lemma s4_mbyte_of_aview2 : forall (H H' : word -> bool) (m m' : word -> option byte) a a',
  aview tfibsegs H' m' a' = aview tfibsegs H m a -> mbyte tfibsegs (mrestrict H' m') a' = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H H' m m' a a' E. unfold aview in E. cbv beta in E.
destruct (mbyte tfibsegs (mrestrict H' m') a') as [b'|]; destruct (mbyte tfibsegs (mrestrict H m) a) as [b|];
  cbn [option_map] in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma s4_garr8_shift : forall (W W' : world tfibsegs) m m' x d l, garr8 tfibsegs (rdW W m) x l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> aview tfibsegs (w_H W') m' (d + i) = aview tfibsegs (w_H W) m (x + i)) ->
  garr8 tfibsegs (rdW W' m') d l.
Proof.
intros W W' m m' x d l Hg HV j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
intros k0 Hk0. assert (k0 = 0%nat) as -> by lia.
specialize (Hv 0%nat ltac:(lia)). rewrite <- Hv.
replace (d + Z.of_nat j + Z.of_nat 0) with (d + Z.of_nat j) by lia.
replace (x + Z.of_nat j + Z.of_nat 0) with (x + Z.of_nat j) by lia.
apply s4_mbyte_of_aview2. apply HV. lia.
Qed.
Lemma s4_garr8_vis : forall (W : world tfibsegs) m p l a, garr8 tfibsegs (rdW W m) p l -> p <= a < p + Z.of_nat (length l) ->
  aview tfibsegs (w_H W) m a <> None.
Proof.
intros W m p l a Hg Ha.
destruct (Hg (Z.to_nat (a - p)) ltac:(lia)) as (Hv & _).
specialize (Hv 0%nat ltac:(lia)).
rewrite Z2Nat.id in Hv by lia. replace (p + (a - p) + Z.of_nat 0) with a in Hv by lia.
unfold aview. cbv beta. rewrite Hv. cbn [option_map]. discriminate.
Qed.

(* every frame of a run with no regions in context as same_below (2 ^ 64), chained *)
Ltac s4_sb_nil :=
  repeat match goal with
  | HF : frame_of ?E ?rs ?m1 ?m2 |- _ =>
      lazymatch m1 with mrestrict _ _ => fail | _ => idtac end;
      let H := fresh "SB" in
      assert (H : same_below m1 m2 (2 ^ 64)) by (apply (frame_nil_same E); exact HF); clear HF
  end;
  repeat match goal with
  | H1 : same_below ?a ?b (2 ^ 64), H2 : same_below ?b ?c (2 ^ 64) |- _ =>
      let H := fresh "SB" in pose proof (same_below_trans a b c (2 ^ 64) H1 H2) as H; clear H1 H2
  end.

(* the resume state at 0x80ae4 *)
Lemma s4_entry : forall (W : world tfibsegs) mem regs t n,
  getr regs 21 = w64 FMW_SB -> 4096 <= t + n <= 2 ^ 47 - 16 ->
  getr regs 19 = w64 n -> getr regs 20 = w64 t -> 0 <= n -> 0 <= t ->
  writable_at tfibsegs (rdW W mem) (t + n) ->
  st_ok tfibsegs (Ereg regs [Z_to_bv 64 (t + n)]) ss_lf4
    (restrict (w_H W) (mkst regs (Z_to_bv 64 LF4_A) mem (seg_rom tfibsegs))).
Proof.
intros W mem regs t n R21 Htn R19 R20 Hn Ht Hw.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Ereg regs [Z_to_bv 64 (t + n)]).
assert (E19 : ew E 19 = Z_to_bv 64 n) by (unfold E; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = Z_to_bv 64 t) by (unfold E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = Z_to_bv 64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 (t + n)) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
assert (U32 : bv_unsigned (ew E 32) = t + n) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF) by (rewrite E21; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
unfold ss_lf4. apply (entry_st_ok_full tfibsegs); change (Ereg regs [Z_to_bv 64 (t + n)]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold lf4_blk. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
  split; [lia|]. split; [lia|]. split; [intros o Ho; replace (t + n + o) with (t + n) by lia; exact Hw|].
  apply Forall_nil.
- apply pairwise_disjoint_of_extents. unfold lf4_blk, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I|]].
  + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U32, U21. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
  + cbn [f_alias alias_ok]. split; [|exact I]. apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 20 t E20) by lia. rewrite (U_atom E 19 n E19) by lia. rewrite (U_atom E 32 (t + n) E32) by lia.
    apply zcanon_id. unfold M64. lia.
Qed.

(* ---- 0x80ae4 .. 0x80b0c: the guard 0x80ae8, the shadow check of t + tn, the NUL store, the guard 0x80b08 ---- *)
Lemma s4_tail : forall cx ly S W regs mem md k u t,
  lf_base B cx -> lf_core B cx ly S W regs mem md k -> 0 <= k <= EV_check_no_overread + 2 ->
  Permutation (ablocks B ly S) ((t, lx_tn cx + 1) :: (u, lx_un cx + 1) :: ablocks B (lx_ly cx) (lx_S cx)) ->
  lf_glob2 cx W mem -> lx_tn cx <= MANIFEST_MAX -> cstr_ok tfibsegs W mem u (lx_ub cx) ->
  bytes_at tfibsegs W mem t (lx_tb cx) ->
  getr regs 8 = w64 (lx_un cx) -> getr regs 9 = w64 u -> getr regs 19 = w64 (lx_tn cx) -> getr regs 20 = w64 t ->
  (forall ly' S' W' regs' mem' md' k' t', lf_P4 B cx ly' S' W' regs' mem' md' k' u t' ->
     SRr tfibsegs W' (cfg_at tfibsegs LF_P4 regs' mem' md') (lf_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs 0x80ae4 regs mem md) (lf_post B cx).
Proof.
intros cx ly S W regs mem md k u t HB HC Hk Hperm HGl Htn Hu Hbt R8 R9 R19 R20 K4.
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
assert (Hin_t : In (t, lx_tn cx + 1) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (s4_sep cx ly S W mem md t u HAR Hperm) as (Dtu & Dte & Due).
assert (Hrq : req_size (lx_tn cx + 1) = lx_tn cx + 1) by (apply s4_req; lia).
assert (Hnew : ~ In (t, lx_tn cx + 1) (ablocks B (lx_ly cx) (lx_S cx))).
{ intros Hi. pose proof (Dte _ _ Hi) as Hd. rewrite Hrq in Hd. lia. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_t) as (_ & Ht4 & Htc & Happ & Htpres & _).
rewrite Hrq in Htc, Happ, Htpres.
assert (Hpin : 0 < lx_n cx -> In (lx_p cx, lx_n cx) (ablocks B ly S)).
{ intros Hn. destruct Hblk as [(Hn0 & _) | (_ & Hpe)]; [lia|].
  exact (Permutation_in _ (Permutation_sym Hperm) (in_cons _ _ _ (in_cons _ _ _ Hpe))). }
destruct (lf_src_rd B cx ly S W mem md HB HAR HIK Hpin) as (_ & _ & _ & Hnz & _).
assert (Hw : writable_at tfibsegs (rdW W mem) (t + lx_tn cx))
  by (apply (apresent_writable tfibsegs); exact (proj1 (Htpres (t + lx_tn cx) ltac:(lia)))).
pose proof (s4_entry W mem regs t (lx_tn cx) R21 ltac:(lia) R19 R20 ltac:(lia) ltac:(lia) Hw) as HS.
set (E := Ereg regs [Z_to_bv 64 (t + lx_tn cx)]) in HS.
assert (E32 : bv_unsigned (ew E 32) = t + lx_tn cx)
  by (unfold E; rewrite (ew_Ereg_extra regs _ 0); cbn [nth]; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok tfibsegs LF4_Bx LF4_SH E (rdW W (ms_mem (mkst regs (Z_to_bv 64 LF4_A) mem (seg_rom tfibsegs))))).
{ constructor; [|constructor]. cbn [ms_mem].
  apply (shent_ok_of_range tfibsegs (w_H W) mem E LF4_Bx 32 t (lx_tn cx + 1) (t + lx_tn cx) 0 1).
  - apply (range_addressable_of_block tfibsegs B LAWS ly S W mem md t (lx_tn cx + 1) t _ HAR Hin_t); lia.
  - unfold LF4_Bx. apply U_atom; [unfold E; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21 | unfold SHADOW_OFF; lia].
  - apply U_atom; [unfold E; exact (ew_Ereg_extra regs _ 0) | lia].
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app in Happ.
    unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
(* the atoms the guards read, and their ranges *)
assert (E19 : ew E 19 = Z_to_bv 64 (lx_tn cx)) by (unfold E; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = Z_to_bv 64 t) by (unfold E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact R20).
assert (E32z : ew E 32 = Z_to_bv 64 (t + lx_tn cx)) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
assert (R_tn : 0 <= t + lx_tn cx <= 2 ^ 47 - 16) by lia.
assert (R_t0 : 0 <= t) by lia.
assert (R_n0 : 0 <= lx_tn cx) by lia.
unfold cfg_at. change (w64 0x80ae4) with (Z_to_bv 64 LF4_A).
change mem with (ms_mem (mkst regs (Z_to_bv 64 LF4_A) mem (seg_rom tfibsegs))) in HJ.
(* run 1: 0x80ae4 `not a0, s4`, up to the guard *)
aj_run_to_tok fmw_tbl_llvmf_ok HS HJ SHOK fmw_Bspan 0x80ae8.
{ s4_awr E32 Hin_t Hnew Hrq t (lx_tn cx + 1). }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
lazymatch goal with H : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ms1)) |- _ => rename H into FR1 end.
lazymatch type of HS with st_ok _ ?Ex _ _ => set (E1 := Ex) in HS, SHOK end.
assert (AG1 : forall n, (n < 33)%nat -> ew E1 n = ew E n)
  by (intros n Hn; unfold E1; rewrite ?ew_ewset_other by lia; reflexivity).
assert (E1_19 : ew E1 19 = Z_to_bv 64 (lx_tn cx)) by (rewrite AG1 by lia; exact E19).
assert (E1_20 : ew E1 20 = Z_to_bv 64 t) by (rewrite AG1 by lia; exact E20).
assert (E1_32 : bv_unsigned (ew E1 32) = t + lx_tn cx) by (rewrite AG1 by lia; exact E32).
(* 0x80ae8 `bltu a0, s3, 0x80ba0` (unimp), a0 = not t, s3 = tn: not taken *)
lazymatch type of HS with st_ok _ _ ?ss _ =>
  let va := eval vm_compute in (sr_get (ss_regs ss) 10%bv) in
  let vb := eval vm_compute in (sr_get (ss_regs ss) 19%bv) in
  idtac "S4G1:" va vb;
  eapply SRr_sym_branch with (c := BC_LTU) (a := va) (b := vb); [exact HS | intros Hb _ | intros _ HS2; clear HS] end.
{ (* the trap arm, class K2: t + tn < 2^64 *)
  exfalso. rewrite (fmt_not_ltu_not E1 (SOff 20 0) (SOff 19 0)
    (s4_g1 E1 20 19 t (lx_tn cx) E1_20 E1_19 R_t0 R_n0 (proj2 R_tn))) in Hb. discriminate Hb. }
(* run 2: a0 := t + tn, the shadow check (slow path 0x80bc8 .. 0x80bd0), a1 := -1, sb zero, 0(a0), up to the guard *)
aj_run_to_tok fmw_tbl_llvmf_ok HS2 HJ SHOK fmw_Bspan 0x80b08.
{ s4_awr E1_32 Hin_t Hnew Hrq t (lx_tn cx + 1). }
lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
lazymatch goal with H : frame_of _ _ (mrestrict _ (ms_mem ms1)) (mrestrict _ (ms_mem ms2)) |- _ => rename H into FR2 end.
lazymatch type of HS2 with st_ok _ ?Ex _ _ => set (E2 := Ex) in HS2, SHOK end.
assert (AG2 : forall n, (n < 33)%nat -> ew E2 n = ew E n)
  by (intros n Hn; unfold E2; rewrite ?ew_ewset_other by lia; first [reflexivity | apply AG1; exact Hn]).
assert (E2_32 : ew E2 32 = Z_to_bv 64 (t + lx_tn cx)) by (rewrite AG2 by lia; exact E32z).
assert (E2_32u : bv_unsigned (ew E2 32) = t + lx_tn cx) by (rewrite AG2 by lia; exact E32).
(* 0x80b08 `beq a0, a1, 0x80ba0` (unimp), a0 = t + tn, a1 = -1: not taken *)
lazymatch type of HS2 with st_ok _ _ ?ss _ =>
  let va := eval vm_compute in (sr_get (ss_regs ss) 10%bv) in
  let vb := eval vm_compute in (sr_get (ss_regs ss) 11%bv) in
  idtac "S4G2:" va vb;
  eapply SRr_sym_branch with (c := BC_EQ) (a := va) (b := vb); [exact HS2 | intros Hb _ | intros _ HS3; clear HS2] end.
{ (* the trap arm, class K1: t + tn <> 2^64 - 1 *)
  exfalso. lazymatch type of Hb with context [sv_denot _ (SLit ?k)] =>
    rewrite (fmt_eq_not E2 (SOff 32 0) (SLit k) (s4_g2 E2 32 (t + lx_tn cx) k E2_32 R_tn ltac:(vm_compute; reflexivity)))
      in Hb end.
  discriminate Hb. }
(* run 3: on to 0x80b0c (LF_P4) *)
aj_run_to_tok fmw_tbl_llvmf_ok HS3 HJ SHOK fmw_Bspan LF_P4.
{ s4_awr E2_32u Hin_t Hnew Hrq t (lx_tn cx + 1). }
lazymatch type of HS3 with context [restrict _ ?m] => rename m into msF end.
lazymatch goal with H : frame_of _ _ (mrestrict _ (ms_mem ms2)) (mrestrict _ (ms_mem msF)) |- _ => rename H into FR3 end.
rename HS3 into HS.
lazymatch type of HS with st_ok _ _ ?ss _ => let r := eval vm_compute in ss in idtac "S4SS:" r end.
lazymatch type of HS with st_ok _ ?Ex _ _ => set (EF := Ex) in HS, SHOK end.
assert (AG : forall n, (n < 33)%nat -> ew EF n = ew E n)
  by (intros n Hn; unfold EF; rewrite ?ew_ewset_other by lia; apply AG2; exact Hn).
(* the three runs changed memory only at t + tn *)
assert (HV : forall a, 0 <= a < 2 ^ 64 -> a <> t + lx_tn cx ->
  aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) mem a).
{ intros a Ha Hne.
  transitivity (aview tfibsegs (w_H W) (ms_mem ms2) a).
  { apply (aview_eq_of tfibsegs). apply FR3. s4_notin E2_32u. }
  transitivity (aview tfibsegs (w_H W) (ms_mem ms1) a).
  { apply (aview_eq_of tfibsegs). apply FR2. s4_notin E1_32. }
  apply (aview_eq_of tfibsegs). apply FR1. s4_notin E32. }
pose proof HJ as (HARF & _).
destruct (s4_carry cx ly S W mem (ms_mem msF) _ t u HB HARF Hperm) as (HFRF & HIKF & HROF & HGF & HuF).
{ intros a Ha Hn1 Hn2. apply HV; [exact Ha | lia]. }
{ exact HFR. }
{ exact HIK. }
{ exact HRO. }
{ exact HGl. }
{ exact Hu. }
(* the NUL at t + tn, from the final region *)
lazymatch type of HS with st_ok _ _ ?ss _ =>
  assert (HR : region_ok tfibsegs EF (rdW W (ms_mem msF))
                 (YP09.mkRegion (Some 32%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]))
    by exact (fmw_region_nth EF ss (restrict (w_H W) msF) 0
               (YP09.mkRegion (Some 32%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) HS ltac:(vm_compute; reflexivity)) end.
pose proof (fmw_field EF (rdW W (ms_mem msF)) 32 (t + lx_tn cx) [YP09.mkChunk 0 (CVal 1 (SLit 0))] 0 1 0 1 0 1%N
  (SLit 0) 0 HR ltac:(rewrite (AG 32%nat ltac:(lia)); exact E32) ltac:(left; reflexivity) eq_refl ltac:(lia) ltac:(lia)) as V0.
assert (HtF : cstr_ok tfibsegs W (ms_mem msF) t (lx_tb cx)).
{ apply (lf_cstr_ok_of_blk B ly S W (ms_mem msF) _ t (lx_tn cx + 1) t (lx_tb cx) HARF Hin_t ltac:(lia) ltac:(unfold lx_tn in *; lia)).
  split; [|exact Hnz].
  apply (garr8_app tfibsegs). split.
  - apply (s4_garr8_shift W W mem (ms_mem msF) t t (lx_tb cx) Hbt). intros i Hi. unfold lx_tn in *. apply HV; lia.
  - intros j Hj. cbn [length] in Hj. assert (j = 0%nat) as -> by lia. cbn [nth]. split; [|lia].
    unfold lx_tn in V0. exact V0. }
(* the registers at 0x80b0c *)
lazymatch type of HS with st_ok _ _ ?ss _ =>
  assert (QF : forall (r : bv 5) n, sr_get (ss_regs ss) r = SOff n 0 -> (n < 33)%nat -> getr (ms_regs msF) r = ew E n)
    by (intros r n Hr Hn; rewrite (st_ok_restrict_reg tfibsegs _ _ _ msF r HS), Hr, fmw_SOff0; apply AG; exact Hn) end.
pose proof (QF 2%bv 2%nat ltac:(vm_compute; reflexivity) ltac:(lia)) as F2.
pose proof (QF 8%bv 8%nat ltac:(vm_compute; reflexivity) ltac:(lia)) as F8.
pose proof (QF 9%bv 9%nat ltac:(vm_compute; reflexivity) ltac:(lia)) as F9.
pose proof (QF 20%bv 20%nat ltac:(vm_compute; reflexivity) ltac:(lia)) as F20.
pose proof (QF 21%bv 21%nat ltac:(vm_compute; reflexivity) ltac:(lia)) as F21.
unfold E in F2, F8, F9, F20, F21.
rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl) in F2. rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl) in F8.
rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl) in F9. rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl) in F20.
rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl) in F21.
assert (HKF : kept_from (lx_regs cx) (ms_regs msF) lf_X).
{ (* the closed check first: vm_compute never sees an evar *)
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    assert (AK : atoms_kept ss lf_X = true) by (vm_compute; reflexivity) end.
  intros r Hc HX. destruct (acs_bv r Hc) as [Eu _].
  assert (Hr32 : 0 <= r < 32) by (unfold acallee_saved in Hc; lia).
  rewrite (QF _ (Z.to_nat r) (atoms_kept_get _ lf_X r AK Hc HX) ltac:(lia)).
  unfold E. rewrite (ew_Ereg_nat regs _ (Z.to_nat r) (Z_to_bv 5 r)) by (rewrite Eu; lia).
  exact (HKX r Hc HX). }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ msF HS eq_refl). cbn [ss_pc].
change (mkCfg (mkst (ms_regs msF) (Z_to_bv 64 0x80b0c) (ms_mem msF) (seg_rom tfibsegs)) ?mm)
  with (cfg_at tfibsegs LF_P4 (ms_regs msF) (ms_mem msF) mm).
apply (K4 ly S W (ms_regs msF) (ms_mem msF) _ k t).
unfold lf_P4, lf_core, lf_J.
split.
{ split; [exact HJ|]. split; [exact HFRF|].
  split; [unfold lx_sp0, LF_FRAME; unfold spZ at 1; rewrite F2; fold (spZ regs); lia|].
  split; [exact HKF|]. split; [rewrite F21; exact R21|]. split; [exact HIKF | exact HROF]. }
split; [exact Hk|]. split; [exact Hperm|]. split; [exact HGF|]. split; [exact Htn|].
split; [exact HuF|]. split; [exact HtF|].
split; [rewrite F8; exact R8|]. split; [rewrite F9; exact R9 | rewrite F20; exact R20].
Qed.

(* ---- 0x80ac8 .. 0x80ae4: `beqz a0` (dead), s4 := t, memcpy (t, text, tn) when tn > 0 ---- *)
Lemma s4_mid : forall cx ly S W regs mem md k u t,
  lf_base B cx -> lf_core B cx ly S W regs mem md k -> 0 <= k <= EV_check_no_overread + 2 ->
  Permutation (ablocks B ly S) ((t, lx_tn cx + 1) :: (u, lx_un cx + 1) :: ablocks B (lx_ly cx) (lx_S cx)) ->
  lf_glob2 cx W mem -> lx_tn cx <= MANIFEST_MAX -> cstr_ok tfibsegs W mem u (lx_ub cx) ->
  getr regs 8 = w64 (lx_un cx) -> getr regs 9 = w64 u -> getr regs 10 = w64 t ->
  getr regs 18 = w64 (lx_text cx) -> getr regs 19 = w64 (lx_tn cx) ->
  (forall ly' S' W' regs' mem' md' k' t', lf_P4 B cx ly' S' W' regs' mem' md' k' u t' ->
     SRr tfibsegs W' (cfg_at tfibsegs LF_P4 regs' mem' md') (lf_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs 0x80ac8 regs mem md) (lf_post B cx).
Proof.
intros cx ly S W regs mem md k u t HB HC Hk Hperm HGl Htn Hu R8 R9 R10 R18 R19 K4.
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
assert (Hin_t : In (t, lx_tn cx + 1) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_t) as (_ & Ht4 & Htc & _).
rewrite (s4_req (lx_tn cx + 1)) in Htc by lia.
destruct (s4_sep cx ly S W mem md t u HAR Hperm) as (Dtu & Dte & Due).
assert (Hnew : ~ In (t, lx_tn cx + 1) (ablocks B (lx_ly cx) (lx_S cx))).
{ intros Hi. pose proof (Dte _ _ Hi) as Hd. rewrite (s4_req (lx_tn cx + 1)) in Hd by lia. lia. }
assert (Hpin : 0 < lx_n cx -> In (lx_p cx, lx_n cx) (ablocks B ly S)).
{ intros Hn. destruct Hblk as [(Hn0 & _) | (_ & Hpe)]; [lia|].
  exact (Permutation_in _ (Permutation_sym Hperm) (in_cons _ _ _ (in_cons _ _ _ Hpe))). }
assert (Hinb : forall i, 0 <= i < lx_n cx -> 0 <= lx_p cx + i < alloc_ceiling).
{ intros i Hi. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (Hpin ltac:(lia))) as (_ & Hp4 & Hpc & _).
  rewrite (s4_req (lx_n cx)) in Hpc by lia. lia. }
pose proof (fmw_resume_nr W regs [] mem 0x80ac8) as HS.
unfold cfg_at. change (w64 0x80ac8) with (Z_to_bv 64 0x80ac8).
assert (U10 : U (Ereg regs []) (SOff 10 0) = t)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs [] 10 10%bv eq_refl); exact R10 | lia]).
assert (U19 : U (Ereg regs []) (SOff 19 0) = lx_tn cx)
  by (apply U_atom; [rewrite (ew_Ereg_nat regs [] 19 19%bv eq_refl); exact R19 | lia]).
assert (UZ : U (Ereg regs []) (SLit 0) = 0) by (apply U_lit; lia).
(* 0x80ac8: beqz a0, 0x80ba4 (__asan_handle_no_return; abort; unimp 0x80bac): not taken, t >= 4096 *)
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0); [exact HS | intros Hb _ | intros _ HS1].
{ exfalso. rewrite branch_eq_U, U10, UZ in Hb. apply Z.eqb_eq in Hb. lia. }
clear HS.
aj_run fmw_tbl_llvmf_ok HS1 HJ.
{ apply awr_ok_nil. }
lazymatch type of HS1 with context [restrict _ ?m] => rename m into ms1 end.
(* 0x80ad0: beqz s3 *)
eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 19 0) (b := SLit 0); [exact HS1 | intros Hb HS2 | intros Hb HS2];
  rewrite branch_eq_U, U19, UZ in Hb; clear HS1.
- (* tn = 0: on to 0x80ae4 *)
  apply Z.eqb_eq in Hb.
  aj_run_to fmw_tbl_llvmf_ok HS2 HJ 0x80ae4.
  { apply awr_ok_nil. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
  s4_sb_nil.
  match goal with H : same_below mem (ms_mem ms2) _ |- _ => rename H into SB end.
  assert (SBc : same_below mem (ms_mem ms2) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB); lia).
  pose proof (fmw_reg_atom _ regs [] _ ms2 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q2.
  pose proof (fmw_reg_atom _ regs [] _ ms2 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q8.
  pose proof (fmw_reg_atom _ regs [] _ ms2 9%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q9.
  pose proof (fmw_reg_atom _ regs [] _ ms2 19%bv 19%bv 19 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q19.
  pose proof (fmw_reg_atom _ regs [] _ ms2 20%bv 10%bv 10 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q20.
  pose proof (fmw_reg_atom _ regs [] _ ms2 21%bv 21%bv 21 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q21.
  assert (Etb : lx_tb cx = []) by (apply length_zero_iff_nil; unfold lx_tn in Hb; lia).
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms2 HS2 eq_refl). cbn [ss_pc].
  change (mkCfg (mkst (ms_regs ms2) (Z_to_bv 64 0x80ae4) (ms_mem ms2) (seg_rom tfibsegs)) ?mm)
    with (cfg_at tfibsegs 0x80ae4 (ms_regs ms2) (ms_mem ms2) mm).
  apply (s4_tail cx ly S W (ms_regs ms2) (ms_mem ms2) _ k u t HB).
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
  + exact (fm_glob_below W mem (ms_mem ms2) _ _ _ _ SBc HGl).
  + exact Htn.
  + exact (cstr_ok_below W mem (ms_mem ms2) u (lx_ub cx) SBc Hu).
  + rewrite Etb. apply garr8_nil.
  + rewrite Q8. exact R8.
  + rewrite Q9. exact R9.
  + rewrite Q19. exact R19.
  + rewrite Q20. exact R10.
  + exact K4.
- (* tn > 0: memcpy (t, text, tn) *)
  apply Z.eqb_neq in Hb.
  assert (Htn1 : 1 <= lx_tn cx) by lia.
  aj_run_to fmw_tbl_llvmf_ok HS2 HJ 0x51ac8.
  { apply awr_ok_nil. }
  lazymatch type of HS2 with context [restrict _ ?m] => rename m into ms2 end.
  s4_sb_nil.
  match goal with H : same_below mem (ms_mem ms2) _ |- _ => rename H into SB end.
  assert (SBc : same_below mem (ms_mem ms2) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB); lia).
  pose proof (fmw_reg_lit _ (Ereg regs []) _ ms2 1%bv 0x80ae4 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)) as Q1.
  pose proof (fmw_reg_atom _ regs [] _ ms2 2%bv 2%bv 2 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q2.
  pose proof (fmw_reg_atom _ regs [] _ ms2 3%bv 3%bv 3 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q3.
  pose proof (fmw_reg_atom _ regs [] _ ms2 4%bv 4%bv 4 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q4.
  pose proof (fmw_reg_atom _ regs [] _ ms2 8%bv 8%bv 8 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q8.
  pose proof (fmw_reg_atom _ regs [] _ ms2 9%bv 9%bv 9 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q9.
  pose proof (fmw_reg_atom _ regs [] _ ms2 10%bv 10%bv 10 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q10.
  pose proof (fmw_reg_atom _ regs [] _ ms2 11%bv 18%bv 18 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q11.
  pose proof (fmw_reg_atom _ regs [] _ ms2 12%bv 19%bv 19 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q12.
  pose proof (fmw_reg_atom _ regs [] _ ms2 19%bv 19%bv 19 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q19.
  pose proof (fmw_reg_atom _ regs [] _ ms2 20%bv 10%bv 10 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q20.
  pose proof (fmw_reg_atom _ regs [] _ ms2 21%bv 21%bv 21 HS2 ltac:(vm_compute; reflexivity) eq_refl) as Q21.
  assert (Hsp2 : spZ (ms_regs ms2) = spZ (lx_regs cx) + -64) by (unfold spZ at 1; rewrite Q2; fold (spZ regs); lia).
  assert (Hgp2 : getr (ms_regs ms2) 3 = w64 (as_gp B))
    by (rewrite Q3, (kept_get _ _ _ 3%bv HKX ltac:(fmw_cs_side) ltac:(fmw_notin)); exact Hgp).
  assert (Htp2 : getr (ms_regs ms2) 4 = w64 (as_tp B))
    by (rewrite Q4, (kept_get _ _ _ 4%bv HKX ltac:(fmw_cs_side) ltac:(fmw_notin)); exact Htp).
  pose proof HJ as (HAR2 & _).
  assert (HIK2 : lf_inkept cx W (ms_mem ms2)).
  { intros i Hi. rewrite <- (HIK i Hi). apply (aview_below (w_H W) mem (ms_mem ms2) alloc_ceiling _ SBc). exact (Hinb i Hi). }
  destruct (lf_src_rd B cx ly S W (ms_mem ms2) _ HB HAR2 HIK2 Hpin) as (_ & Hsrc & _ & Hnz & _ & _ & _ & Htext).
  pose proof Hsrc as (Hbt & Hx4 & Hxc & Hxam & Hxra & Hxhv).
  fold (lx_tn cx) in Hxc, Hxam, Hxra, Hxhv.
  destruct (Htext ltac:(lia)) as (Hxp & Hxpn).
  assert (Hpe : In (lx_p cx, lx_n cx) (ablocks B (lx_ly cx) (lx_S cx)))
    by (destruct Hblk as [(Hn0 & _) | (_ & Hpe)]; [lia | exact Hpe]).
  pose proof (Dte _ _ Hpe) as Hdx. rewrite (s4_req (lx_n cx)) in Hdx by lia.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms2 HS2 eq_refl). cbn [ss_pc].
  change (Z_to_bv 64 0x51ac8) with (Z_to_bv 64 FM_asan_memcpy).
  eapply SRr_bind.
  { apply (YC85.aj_intrin_atS tfibsegs B LAWS HSL OCpy FM_asan_memcpy AICPY W (ms_regs ms2) (ms_mem ms2) LLVMF_STK
      (spZ (lx_regs cx)) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx) [] ly S _ k
      t (lx_text cx) (lx_tn cx) (-64) (Z_to_bv 64 0x80ae4)).
    - exact HJ.
    - rewrite Q10. exact R10.
    - rewrite Q11. exact R18.
    - rewrite Q12. exact R19.
    - unfold MANIFEST_MAX in Htn. lia.
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
      + right; right; left. exists t, (lx_tn cx + 1). split; [exact Hin_t|]. split; [exact Hnew|].
        rewrite (s4_req (lx_tn cx + 1)) by lia. lia.
      + unfold ESTACK. lia.
    - apply (amem_range_of_block tfibsegs B LAWS ly S W (ms_mem ms2) _ t (lx_tn cx + 1) t (lx_tn cx) HAR2 Hin_t);
        [lia | rewrite (s4_req (lx_tn cx + 1)) by lia; lia].
    - apply (range_addressable_of_block tfibsegs B LAWS ly S W (ms_mem ms2) _ t (lx_tn cx + 1) t (lx_tn cx) HAR2 Hin_t);
        [lia | rewrite (s4_req (lx_tn cx + 1)) by lia; lia].
    - intros _. apply (shadow_hull_vis_of_block tfibsegs B LAWS ly S W (ms_mem ms2) _ t (lx_tn cx + 1) t (lx_tn cx) HAR2 Hin_t);
        [lia | rewrite (s4_req (lx_tn cx + 1)) by lia; lia | lia].
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split; [|rewrite Hsp2; unfold ESTACK; lia].
        apply (s4_garr8_vis W (ms_mem ms2) (lx_text cx) (lx_tb cx) a Hbt). fold (lx_tn cx). lia. }
      split; [lia|]. split; [exact Hxam|]. split; [exact Hxra | exact Hxhv]. }
  intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & H10' & Heff & Hfr & Hpres3 & _).
  change (forall i, 0 <= i < lx_tn cx ->
    aview tfibsegs (w_H W) mem3 (t + i) = aview tfibsegs (w_H W) (ms_mem ms2) (lx_text cx + i)) in Heff.
  pose proof HJ3 as (HAR3 & _).
  destruct (s4_carry cx ly S W (ms_mem ms2) mem3 _ t u HB HAR3 Hperm) as (HFR3 & HIK3 & HRO3 & HG3 & Hu3).
  { intros a Ha Hn1 Hn2. unfold lx_sp0, LF_FRAME in Hn2. apply Hfr; [exact Ha | lia | unfold ESTACK; lia]. }
  { apply (lf_frame_below cx W mem (ms_mem ms2) SB); [unfold lx_sp0, LF_FRAME; lia | unfold lx_sp0; lia | exact HFR]. }
  { exact HIK2. }
  { exact (arodata_below B W mem (ms_mem ms2) SBc HRO). }
  { exact (fm_glob_below W mem (ms_mem ms2) _ _ _ _ SBc HGl). }
  { exact (cstr_ok_below W mem (ms_mem ms2) u (lx_ub cx) SBc Hu). }
  assert (P2 : getr regs3 2 = getr (ms_regs ms2) 2) by exact (fmw_pres _ _ 2%bv HP3 ltac:(fmw_cs_side)).
  assert (P8 : getr regs3 8 = getr (ms_regs ms2) 8) by exact (fmw_pres _ _ 8%bv HP3 ltac:(fmw_cs_side)).
  assert (P9 : getr regs3 9 = getr (ms_regs ms2) 9) by exact (fmw_pres _ _ 9%bv HP3 ltac:(fmw_cs_side)).
  assert (P19 : getr regs3 19 = getr (ms_regs ms2) 19) by exact (fmw_pres _ _ 19%bv HP3 ltac:(fmw_cs_side)).
  assert (P20 : getr regs3 20 = getr (ms_regs ms2) 20) by exact (fmw_pres _ _ 20%bv HP3 ltac:(fmw_cs_side)).
  assert (P21 : getr regs3 21 = getr (ms_regs ms2) 21) by exact (fmw_pres _ _ 21%bv HP3 ltac:(fmw_cs_side)).
  change (mkCfg (mkst regs3 (Z_to_bv 64 0x80ae4) mem3 (seg_rom tfibsegs)) md3) with (cfg_at tfibsegs 0x80ae4 regs3 mem3 md3).
  apply (s4_tail cx ly S W regs3 mem3 md3 k u t HB).
  + split; [exact HJ3|]. split; [exact HFR3|].
    split; [unfold lx_sp0, LF_FRAME; unfold spZ at 1; rewrite P2; fold (spZ (ms_regs ms2)); lia|].
    split; [exact (kept_step (w_H W) (lx_regs cx) regs [] _ ms2 regs3 lf_X HKX HS2 ltac:(vm_compute; reflexivity) HP3)|].
    split; [rewrite P21, Q21; exact R21|]. split; [exact HIK3 | exact HRO3].
  + exact Hk.
  + exact Hperm.
  + exact HG3.
  + exact Htn.
  + exact Hu3.
  + apply (s4_garr8_shift W W (ms_mem ms2) mem3 (lx_text cx) t (lx_tb cx) Hbt).
    intros i Hi. fold (lx_tn cx) in Hi. exact (Heff i Hi).
  + rewrite P8, Q8. exact R8.
  + rewrite P9, Q9. exact R9.
  + rewrite P19, Q19. exact R19.
  + rewrite P20, Q20. exact R10.
  + exact K4.
Qed.

(* ---- 0x80ac0 .. 0x80ac8: t = malloc (tn + 1) ---- *)
Lemma lf_seg4 : forall cx ly S W regs mem md k u, lf_base B cx -> lf_P3 B cx ly S W regs mem md k u ->
  (forall ly' S' W' regs' mem' md' k' t, lf_P4 B cx ly' S' W' regs' mem' md' k' u t ->
     SRr tfibsegs W' (cfg_at tfibsegs LF_P4 regs' mem' md') (lf_post B cx)) ->
  SRr tfibsegs W (cfg_at tfibsegs LF_P3 regs mem md) (lf_post B cx).
Proof.
intros cx ly S W regs mem md k u HB HP3 K4.
pose proof HB as (HAP & _ & _ & _ & Hblk & _ & _ & Hev & Hbb & _ & _ & _ & _ & _).
pose proof HAP as (HAR0 & _ & _ & Hgp & Htp & _ & _ & _ & _).
destruct HP3 as (HC & Hk & Hperm & HGl & Htn & Hu & R8 & R9 & R18 & R19).
pose proof HC as (HJ & HFR & Hsp & HKX & R21 & HIK & HRO).
unfold lf_J in HJ.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof fm_segs_low as HSL. pose proof fm_wx as HWX.
pose proof (fmw_sp B _ _ _ _ _ _ _ _ HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
pose proof (lx_ranges B cx HB) as (Rk & Rs6 & Rsk & Rn & _ & _ & _ & _ & Run & Rtn & Rub).
assert (FE : EV_check_no_overread + 2 < EV_LLVMF) by (vm_compute; reflexivity).
assert (FS : LLVMF_STK = 32768) by reflexivity.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _).
unfold lx_sp0, LF_FRAME in *.
pose proof (fmw_resume_nr W regs [] mem LF_P3) as HS.
unfold cfg_at. change (w64 LF_P3) with (Z_to_bv 64 LF_P3).
aj_run_to fmw_tbl_llvmf_ok HS HJ 0x52e1c.
{ apply awr_ok_nil. }
lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
assert (SB1 : same_below mem (ms_mem ms1) (2 ^ 64))
  by (match goal with H : frame_of _ _ mem (ms_mem ms1) |- _ => exact (frame_nil_same _ mem (ms_mem ms1) H) end).
assert (SB1c : same_below mem (ms_mem ms1) alloc_ceiling) by (apply (same_below_mono _ _ _ _ SB1); lia).
pose proof (fmw_reg_lit _ (Ereg regs []) _ ms1 1%bv 0x80ac8 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as Q1.
pose proof (fmw_reg_atom _ regs [] _ ms1 2%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl) as Q2.
pose proof (fmw_reg_atom _ regs [] _ ms1 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as Q3.
pose proof (fmw_reg_atom _ regs [] _ ms1 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as Q4.
pose proof (fmw_reg_atom _ regs [] _ ms1 8%bv 8%bv 8 HS ltac:(vm_compute; reflexivity) eq_refl) as Q8.
pose proof (fmw_reg_atom _ regs [] _ ms1 9%bv 9%bv 9 HS ltac:(vm_compute; reflexivity) eq_refl) as Q9.
pose proof (fmw_reg_atom _ regs [] _ ms1 18%bv 18%bv 18 HS ltac:(vm_compute; reflexivity) eq_refl) as Q18.
pose proof (fmw_reg_atom _ regs [] _ ms1 19%bv 19%bv 19 HS ltac:(vm_compute; reflexivity) eq_refl) as Q19.
pose proof (fmw_reg_atom _ regs [] _ ms1 21%bv 21%bv 21 HS ltac:(vm_compute; reflexivity) eq_refl) as Q21.
assert (Q10 : getr (ms_regs ms1) 10 = w64 (lx_tn cx + 1)).
{ eapply (s4_reg_U _ _ _ ms1 10%bv); [exact HS | vm_compute; reflexivity |].
  apply (U_atom_off _ 19 (lx_tn cx) 1); [rewrite (ew_Ereg_nat regs [] 19 19%bv eq_refl); exact R19 | lia | lia]. }
assert (Hsp1 : spZ (ms_regs ms1) = spZ (lx_regs cx) + -64) by (unfold spZ at 1; rewrite Q2; fold (spZ regs); lia).
assert (Hgp1 : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite Q3, (kept_get _ _ _ 3%bv HKX ltac:(fmw_cs_side) ltac:(fmw_notin)); exact Hgp).
assert (Htp1 : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite Q4, (kept_get _ _ _ 4%bv HKX ltac:(fmw_cs_side) ltac:(fmw_notin)); exact Htp).
assert (Hun : 0 <= lx_un cx <= 255) by lia.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms1 HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 0x52e1c) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite (fb_code B FB); reflexivity).
eapply SRr_bind.
{ apply (YC85.amalloc04_sub tfibsegs B LAWS HSL ameter_triv AMALLOC W (ms_regs ms1) (ms_mem ms1) LLVMF_STK
    (spZ (lx_regs cx)) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx) [] ly S _ k
    (lx_tn cx + 1) (-64) (Z_to_bv 64 0x80ac8) []).
  - exact HJ.
  - exact Q10.
  - unfold MANIFEST_MAX in Htn. unfold MALLOC_MAX. lia.
  - rewrite (blocks_bytes_bsum B ly S), (bsum_perm _ _ Hperm), bsum_cons, <- (blocks_bytes_bsum B (lx_ly cx) (lx_S cx)).
    cbn [snd]. unfold LIVE_LIB, LIVE_MAX, MANIFEST_MAX in *. lia.
  - exact Hsp1.
  - reflexivity.
  - lia.
  - unfold ASTACK. lia.
  - exact Hgp1.
  - exact Htp1.
  - exact Q1.
  - apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - lia.
  - apply (achain_chain_pre ly _ (spZ (ms_regs ms1)) (lx_un cx) [] (ms_regs ms1)).
    + apply achain_low. lia.
    + lia.
    + unfold s0Z. rewrite Q8, R8. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - apply UNIV. rewrite call_trace_nil, (fb_code B FB).
    assert (RA : raZ (ms_regs ms1) = 0x80ac8) by (unfold raZ; rewrite Q1; apply unsigned_lit_small; lia).
    rewrite RA. apply memZL_In. vm_compute. reflexivity.
  - exact I. }
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & t & -> & HJ2 & HP2 & H10r & _ & Ht4 & Hbl & HK & _ & HJs).
(* back at 0x80ac8 *)
destruct HK as (KK1 & _ & KK3 & _).
assert (Hperm2 : Permutation (ablocks B ly2 S2) ((t, lx_tn cx + 1) :: (u, lx_un cx + 1) :: ablocks B (lx_ly cx) (lx_S cx))).
{ rewrite Hbl. eapply Permutation_trans; [apply Permutation_sym, Permutation_cons_append|]. apply perm_skip. exact Hperm. }
assert (Hinc : forall x, In x (ablocks B ly S) -> In x (ablocks B ly2 S2))
  by (intros x Hx; rewrite Hbl; apply in_or_app; left; exact Hx).
pose proof HJs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2s & _).
assert (Hin_u : In (u, lx_un cx + 1) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin_u) as (_ & Hu4 & Huc & _).
rewrite (s4_req (lx_un cx + 1)) in Huc by lia.
assert (HFR2 : lf_frame cx W2 mem2).
{ apply (lf_frame_kept cx W W2 (ms_mem ms1) mem2).
  - intros a Ha. unfold lx_sp0, LF_FRAME in Ha. apply KK1; [lia | unfold ASTACK; lia].
  - apply (lf_frame_below cx W mem (ms_mem ms1) SB1); [unfold lx_sp0, LF_FRAME; lia | unfold lx_sp0; lia | exact HFR]. }
assert (HIK2 : lf_inkept cx W2 mem2).
{ intros i Hi. rewrite <- (HIK i Hi).
  destruct Hblk as [(Hn0 & _) | (Hn & Hpin)]; [lia|].
  pose proof (Permutation_in _ (Permutation_sym Hperm) (in_cons _ _ _ Hpin)) as Hpin'.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpin') as (_ & Hp4 & Hpc & _).
  rewrite (s4_req (lx_n cx)) in Hpc by lia.
  rewrite (F2s (lx_p cx) (lx_n cx) i Hpin' (Hinc _ Hpin') ltac:(rewrite s4_req by lia; lia) (inFP_nil _)).
  apply (aview_below (w_H W) mem (ms_mem ms1) alloc_ceiling _ SB1c). lia. }
assert (HRO2 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W2) mem2))
  by exact (arodata_kept B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJs nil_closed nil_not_roP (arodata_below B W mem (ms_mem ms1) SB1c HRO)).
assert (HG2 : lf_glob2 cx W2 mem2).
{ unfold lf_glob2 in *. apply (s4_glob_img W W2 (ms_mem ms1) mem2).
  - intros a Ha. destruct (fb_pstat B FB a Ha) as [N1 N2]. exact (KK3 a (pstat_img a Ha) N1 N2).
  - exact (fm_glob_below W mem (ms_mem ms1) _ _ _ _ SB1c HGl). }
assert (Hu2 : cstr_ok tfibsegs W2 mem2 u (lx_ub cx)).
{ apply (cstr_ok_kept_blk B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u (lx_ub cx) u (lx_un cx + 1) HJs Hin_u (Hinc _ Hin_u)).
  - lia.
  - unfold lx_un. lia.
  - intros a _ Ha. exact (inFP_nil a Ha).
  - exact (cstr_ok_below W mem (ms_mem ms1) u (lx_ub cx) SB1c Hu). }
assert (P2 : getr regs2 2 = getr (ms_regs ms1) 2) by exact (fmw_pres _ _ 2%bv HP2 ltac:(fmw_cs_side)).
assert (P8 : getr regs2 8 = getr (ms_regs ms1) 8) by exact (fmw_pres _ _ 8%bv HP2 ltac:(fmw_cs_side)).
assert (P9 : getr regs2 9 = getr (ms_regs ms1) 9) by exact (fmw_pres _ _ 9%bv HP2 ltac:(fmw_cs_side)).
assert (P18 : getr regs2 18 = getr (ms_regs ms1) 18) by exact (fmw_pres _ _ 18%bv HP2 ltac:(fmw_cs_side)).
assert (P19 : getr regs2 19 = getr (ms_regs ms1) 19) by exact (fmw_pres _ _ 19%bv HP2 ltac:(fmw_cs_side)).
assert (P21 : getr regs2 21 = getr (ms_regs ms1) 21) by exact (fmw_pres _ _ 21%bv HP2 ltac:(fmw_cs_side)).
assert (HKX2 : kept_from (lx_regs cx) regs2 lf_X)
  by exact (kept_step (w_H W) (lx_regs cx) regs [] _ ms1 regs2 lf_X HKX HS ltac:(vm_compute; reflexivity) HP2).
change (mkCfg (mkst regs2 (Z_to_bv 64 0x80ac8) mem2 (seg_rom tfibsegs)) md2) with (cfg_at tfibsegs 0x80ac8 regs2 mem2 md2).
apply (s4_mid cx ly2 S2 W2 regs2 mem2 md2 (k + 1) u t HB).
- split; [exact HJ2|]. split; [exact HFR2|].
  split; [unfold lx_sp0, LF_FRAME, spZ at 1; rewrite P2; fold (spZ (ms_regs ms1)); lia|].
  split; [exact HKX2|]. split; [rewrite P21, Q21; exact R21|]. split; [exact HIK2 | exact HRO2].
- lia.
- exact Hperm2.
- exact HG2.
- exact Htn.
- exact Hu2.
- rewrite P8, Q8. exact R8.
- rewrite P9, Q9. exact R9.
- exact H10r.
- rewrite P18, Q18. exact R18.
- rewrite P19, Q19. exact R19.
- exact K4.
Qed.
End X.
