(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module paths and module names changed; 211 of its 274 lines of code are new or changed and 1310 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_g3kit.v on a working branch e2e59892bef: relocated A->B by symbol (b_reloc.py, revcheck rc 0 vs pin ca61e5c9eabc0050). *)
(* G3's walk kit for lv2_locate_manifest_names / _readings at fm.asan addresses: image facts, the registers a symbolic
   state keeps, and the transfer of memory facts (C strings, statics, the relro view) across a step that leaves every
   byte below alloc_ceiling unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma g3_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Lemma g3_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
unfold tfibsegs, AsanUbsan.M.loaded_segments in Hin. cbn in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hr; lia.
Qed.

Section h. Context {fx : YK11.FPState}.
Variable segs : list Segment.
(* registers a symbolic state keeps as their entry atom equal the entry registers *)
Lemma g3_regs_of_st_ok : forall E ss ms regs0 extra (L : list (bv 5)),
  st_ok segs E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) L = true ->
  forall r, In r L -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms regs0 extra L HS [HA _] Hcs r Hr.
pose proof (proj1 (forallb_forall _ _) Hcs _ Hr) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
rewrite (st_ok_reg segs E ss ms _ HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite HA. 2:{ pose proof (u5_range r). lia. }
rewrite ew_Ereg_reg, Z_to_bv_bv_unsigned. reflexivity.
Qed.
End h.

(* the callee-saved registers other than sp *)
Definition G3_KEPT : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma g3_aregs : forall regs0 regs2 : bvmap 5 word,
  (forall r, In r G3_KEPT -> getr regs2 r = getr regs0 r) -> getr regs2 2 = getr regs0 2 ->
  aregs_preserved regs0 regs2.
Proof.
intros regs0 regs2 HK H2 r Hr.
assert (Hr0 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold acallee_saved in Hr; lia).
clear Hr.
destruct Hr0 as [-> | Hr0]; [exact H2|].
apply HK. cbv [G3_KEPT In].
repeat (destruct Hr0 as [-> | Hr0]; [repeat (first [left; apply bv_eq; reflexivity | right]) |]).
subst r. repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.

Lemma g3_aregs_keep : forall regs0 regs1 : bvmap 5 word,
  aregs_preserved regs0 regs1 -> forall r, In r G3_KEPT -> getr regs1 r = getr regs0 r.
Proof.
intros regs0 regs1 HP r Hr. pose proof (HP (bv_unsigned r)) as H. rewrite Z_to_bv_bv_unsigned in H. apply H.
cbv [G3_KEPT In] in Hr.
repeat (destruct Hr as [<- | Hr];
  [ match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in
      change (bv_unsigned x) with v end; unfold acallee_saved; lia |]).
destruct Hr.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the journal composition with image footprints (statics in FM_PSTAT_FP): ajournal_sub with the third FP1 case
   `inFP FP a /\ in_img segs a` (YCbq.v:725-731, FP-keyed journal, Reloc/JournalFP) *)
Definition g3_ajsub_img (B : asyms) : Prop :=
  forall STK sp0 FP ly S (W : world tfibsegs) mem md own lyc Sc Wc memc mdc k STK1 sp1 FP1 nf ly2 S2 W2 mem2 md2 k1,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc Wc memc mdc nf ly2 S2 W2 mem2 md2 k1 ->
  sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
  (forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a \/ (inFP FP a /\ in_img tfibsegs a)) ->
  ajournal tfibsegs B STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 mem2 md2 (k + k1).
Lemma g3_ajsub_img_ok : forall B, g3_ajsub_img B.
Proof. intros B. exact (ajournal_sub tfibsegs B (AR_laws_ok tfibsegs B) g3_segs_low). Qed.

(* fuzz/alloc.c's statics are image bytes (load segment 3, 0x9b9a0..0x5f6950 in the ELF) *)
Lemma g3_pstat_img : forall a, inFP FM_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha).
set (f := fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))).
let v := eval vm_compute in (option_map f (nth_error tfibsegs 3)) in
assert (E3 : option_map f (nth_error tfibsegs 3) = v) by (vm_compute; reflexivity).
destruct (nth_error tfibsegs 3) as [sg|] eqn:E; [|discriminate E3].
cbn [option_map] in E3. unfold f in E3. injection E3 as Hb Hz.
exists sg. split; [exact (nth_error_In _ 3 E)|]. rewrite Hb, Hz.
cbv [FM_PSTAT_FP G_FAIL G_LIVE G_PEAK G_COUNT In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; lia.
Qed.

(* a frame equation of a run: aview is unchanged outside the run's write windows *)
Lemma g3_aview_frame : forall E rs H (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros E rs H m m' HF a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* the view below alloc_ceiling is unchanged (from one world and memory to another) *)
Definition g3_low_kept (W W' : world tfibsegs) (mem mem' : word -> option byte) : Prop :=
  forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a.

Lemma g3_val_mem_kept : forall (W W' : world tfibsegs) mem mem' a n v,
  val_mem tfibsegs (rdW W mem) a n v ->
  (forall i, 0 <= i < Z.of_nat n -> aview tfibsegs (w_H W') mem' (a + i) = aview tfibsegs (w_H W) mem (a + i)) ->
  val_mem tfibsegs (rdW W' mem') a n v.
Proof.
intros W W' mem mem' a n v Hv Heq k Hk.
rewrite (mbyte_of_aview tfibsegs _ _ _ _ _ (Heq (Z.of_nat k) ltac:(lia))). exact (Hv k Hk).
Qed.

Lemma g3_garr8_kept : forall (W W' : world tfibsegs) mem mem' a l,
  garr8 tfibsegs (rdW W mem) a l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> aview tfibsegs (w_H W') mem' (a + i) = aview tfibsegs (w_H W) mem (a + i)) ->
  garr8 tfibsegs (rdW W' mem') a l.
Proof.
intros W W' mem mem' a l Hg Heq j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (g3_val_mem_kept W W' mem mem'); [exact Hv|]. intros i Hi. cbn in Hi.
replace (a + Z.of_nat j + i) with (a + (Z.of_nat j + i)) by lia. apply Heq. lia.
Qed.

Lemma g3_shadow_low : forall x, 0 <= x < alloc_ceiling -> 0 <= shadow_addr x < alloc_ceiling.
Proof.
intros x Hx. pose proof asan_consts as (C1 & _). unfold shadow_addr, SHADOW_OFF.
split; [pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)); lia|].
assert (x / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (alloc_ceiling / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma g3_hull_low : forall x, 0 <= x < alloc_ceiling ->
  0 <= shadow_addr x / 8 * 8 /\ shadow_addr x / 8 * 8 + 8 <= alloc_ceiling.
Proof.
intros x Hx. pose proof (g3_shadow_low x Hx) as [S1 S2]. pose proof asan_consts as (C1 & _).
pose proof (Z.mul_div_le (shadow_addr x) 8 ltac:(lia)).
pose proof (Z.div_pos (shadow_addr x) 8 ltac:(lia) ltac:(lia)).
assert (shadow_addr x + 8 <= alloc_ceiling).
{ unfold shadow_addr, SHADOW_OFF in *.
  assert (x / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
  assert (alloc_ceiling / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia). lia. }
lia.
Qed.

Lemma g3_cstr_ok_kept : forall (W W' : world tfibsegs) mem mem' p l,
  cstr_ok tfibsegs W mem p l -> g3_low_kept W W' mem mem' -> cstr_ok tfibsegs W' mem' p l.
Proof.
intros W W' mem mem' p l ((Hg & Hnz) & H4 & Hc & H40 & Ham & Hra & Hhv & Htl) HK.
pose proof asan_consts as (C1 & _).
split; [split; [|exact Hnz]|].
{ apply (g3_garr8_kept W W' mem mem'); [exact Hg|]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  apply HK. lia. }
split; [exact H4|]. split; [exact Hc|]. split; [exact H40|]. split; [exact Ham|]. split.
{ intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr. fold (shadow_addr x). rewrite HK; [exact Hs|]. apply g3_shadow_low. lia. }
split.
{ intros s Hs. rewrite HK; [apply Hhv; exact Hs|].
  match type of Hs with shadow_addr ?x / 8 * 8 <= _ < shadow_addr ?y / 8 * 8 + 8 =>
    pose proof (g3_hull_low x ltac:(lia)) as S1; pose proof (g3_hull_low y ltac:(lia)) as S2 end.
  lia. }
intros a Ha. rewrite HK; [apply Htl; exact Ha|].
pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)). lia.
Qed.

Lemma g3_fm_glob_kept : forall (W W' : world tfibsegs) mem mem' live peak cnt fail,
  fm_glob tfibsegs W mem live peak cnt fail -> g3_low_kept W W' mem mem' ->
  fm_glob tfibsegs W' mem' live peak cnt fail.
Proof.
intros W W' mem mem' live peak cnt fail (GL & GP & GC & GF & R) HK. pose proof asan_consts as (C1 & _).
unfold fm_glob. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply (g3_val_mem_kept W W' mem mem'); [exact GL | intros i Hi; apply HK; cbn in Hi; lia]|].
split; [apply (g3_val_mem_kept W W' mem mem'); [exact GP | intros i Hi; apply HK; cbn in Hi; lia]|].
split; [apply (g3_val_mem_kept W W' mem mem'); [exact GC | intros i Hi; apply HK; cbn in Hi; lia]|].
split; [apply (g3_val_mem_kept W W' mem mem'); [exact GF | intros i Hi; apply HK; cbn in Hi; lia]|].
exact R.
Qed.

Lemma g3_in_roP_low : forall a, in_roP tfibsegs FM_RLO FM_RHI a -> 0 <= a < kLowMemEnd.
Proof.
intros a [(s & Hs & _ & Hr) | Hr].
- apply g3_segs_low. exists s. split; [exact Hs | exact Hr].
- unfold FM_RLO, FM_RHI, kLowMemEnd in *. lia.
Qed.

Lemma g3_arodata_kept : forall B (W W' : world tfibsegs) mem mem',
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) mem) -> g3_low_kept W W' mem mem' ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W') mem').
Proof.
intros B W W' mem mem' HR HK a Hro Ho He. pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof (g3_in_roP_low a Hro) as Hl. rewrite HK by lia. exact (HR a Hro Ho He).
Qed.

(* a region's value chunk gives the value it holds *)
Lemma g3_st_ok_region_nth : forall E ss ms i r,
  st_ok tfibsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok tfibsegs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok tfibsegs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.

Lemma g3_field_of_region : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem tfibsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok tfibsegs E m b od w e v Hck He Hv Hw).
Qed.
End k.

(* ---- calls into the runtime and the shadow of the stack (the same steps as G4's FMW_lib.v aj_ro_at and G6's
   FMW_kit.v stk_sh0_of_AR, restated here so G3's files build on their own) ---- *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

(* a call at sp0 + o to a runtime routine whose contract has FMH_Rt's rt_post_ro form: the caller's journal holds after
   the call, unchanged (the routine writes only its own stack window, inside the caller's) *)
Lemma g3_aj_ro_at : forall pc STKr (R : Z -> Prop),
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK <= STKr -> STKr - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (ecall_pre_k tfibsegs B STKr lyc Sc W regsT memT mdc ->
   SRr tfibsegs W (cfg_at tfibsegs pc regsT memT mdc) (rt_post_ro tfibsegs B STKr lyc Sc W regsT memT mdc R)) ->
  SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom tfibsegs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : Z),
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
       ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - STKr <= a < sp0 + o) ->
          aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc STKr R W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
  HJ Hsp' Hal Hneg Hes Hbud Hgp Htp Hra Hraw HC.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as HE4 by reflexivity.
assert (HPRE : ecall_pre tfibsegs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o);
    try eassumption; [lia|]. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HPK : ecall_pre_k tfibsegs B STKr lyc Sc W regsT memT mdc).
{ split; [exact HPRE|]. split; [rewrite Eslo; lia|]. split; [rewrite Eslo, Hsp'; lia|].
  intros a Ha. apply Hpres. rewrite Hsp' in Ha. lia. }
eapply SRr_mono; [exact (HC HPK)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hv & HR & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write tfibsegs B LAWS g3_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => sp0 + o - STKr <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; unfold awr_byte; left; unfold awr_byte0; left; lia.
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hv|]. split; [exact HR|]. split; [exact Hfr | exact Hpres2].
Qed.

(* the zero shadow of the stack, from AR alone (ARm am_zshadow over zero_shadow_ranges, YG0n.v:187-190, 217) *)
Lemma g3_stk_sh0_of_AR : forall ly S (W : world tfibsegs) mem md lo hi,
  AR tfibsegs B ly S W mem md -> ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly ->
  stk_sh0 tfibsegs W mem lo hi.
Proof.
intros ly S W mem md lo hi (M & _) Hlo Hhi a Ha.
pose proof (am_layout B ly S _ M) as HLY. pose proof (lo_top ly HLY) as (_ & _ & _ & _ & Hpl & Hph & _).
pose proof (am_zshadow B ly S _ M) as HZ. unfold zshadow_ok, zero_shadow_ranges in HZ.
apply Forall_inv in HZ. cbn [fst snd] in HZ. unfold zero_shadow in HZ.
unfold page_aligned in Hpl, Hph.
set (l0 := ly_stk_lo ly) in *. set (h0 := ly_stk_hi ly) in *.
assert (E : shadow_addr a = shadow_of_addr SHADOW_OFF l0 + (a / 8 - l0 / 8)).
{ unfold shadow_addr, shadow_of_addr. lia. }
rewrite E. apply HZ.
pose proof (Z.div_mod l0 4096 ltac:(lia)) as D0. pose proof (Z.div_mod h0 4096 ltac:(lia)) as D1.
rewrite Hpl, Z.add_0_r in D0. rewrite Hph, Z.add_0_r in D1.
assert (Q0 : l0 / 8 = 512 * (l0 / 4096)) by (rewrite D0 at 1; replace (4096 * (l0 / 4096)) with ((512 * (l0 / 4096)) * 8) by lia; apply Z.div_mul; lia).
assert (Q1 : (h0 - l0) / 8 = 512 * (h0 / 4096) - 512 * (l0 / 4096)).
{ rewrite D0 at 1. rewrite D1 at 1. replace (4096 * (h0 / 4096) - 4096 * (l0 / 4096)) with ((512 * (h0 / 4096) - 512 * (l0 / 4096)) * 8) by lia.
  apply Z.div_mul. lia. }
rewrite Q1. split.
- apply Zle_minus_le_0. apply Z.div_le_mono; lia.
- assert (a / 8 < 512 * (h0 / 4096)) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
End r.

(* what the prologue needs of B: the shadow-base cells are fm's (TfibLib's tl_got_shadow / tl_shadow_cell, A/ACeg.v:28-29
   relocated: GOT 0x99c98 -> __asan_shadow_memory_dynamic_address 0xa2078 -> 0x7fff8000, fm-fn-measure.md 2) *)
Definition g3_cells (B : asyms) : Prop := as_got_shadow B = 0x99c98 /\ as_shadow_cell B = 0xa2078.

(* cstr_kept is closed under suffixes (FMH_Fn.v cstr_kept, hdesign cce35be4cf7 / 7d12534e1ca) *)
Lemma g3_cstr_kept_suffix : forall B ly S p l k, cstr_kept B ly S p l -> (k <= length l)%nat ->
  cstr_kept B ly S (p + Z.of_nat k) (skipn k l).
Proof.
intros B ly S p l k [(b & m & Hin & Hb & Hm) | (p0 & l0 & k0 & H0 & Hk0 & -> & ->)] Hk.
- left. exists b, m. split; [exact Hin|]. rewrite length_skipn. lia.
- right. rewrite length_skipn in Hk. exists p0, l0, (k0 + k)%nat. split; [exact H0|]. rewrite skipn_skipn.
  split; [lia|]. split; [lia|]. f_equal. lia.
Qed.
