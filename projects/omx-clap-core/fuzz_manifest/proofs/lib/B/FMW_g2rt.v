(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050, unstripped twin b9568e38145a) of lib/A/FMW_g2rt.v at a working branch
   6397116ac79 (= a working branch 0d38fb8ac64, unchanged to 433b7106168). Its code states no image numeral (b_reloc.py
   ad735a6c849a4c62 over mapAB.json 1fe25eab6729e252 finds 0 rows; the code here equals its output except that A's import
   order is kept): its image facts are vm_compute / case analyses over B's tfibsegs (lib.ReusableB YB1v) and FMH_Base's B
   values. Imports by the image-B core's rule (a working branch 305d8b1527f, coreab/REUSABLEB-LIST.txt): lib.A AB1v
   -> lib.ReusableB YB1v (listed); every lib.Reusable module, YCbq included, stays lib.Reusable; fm's own files from
   lib.B; FMupoison shared from lib.A. *)
(* G2 (name_char, has_prefixed) helpers: fm image facts, a journal step for a runtime call in FMH_Rt's rt_post_ro form
   (after the donor's aj_bcmp_at, lib/Reusable/YCbq.v:2060), and the frame of a walk (bytes outside one stack window
   unchanged), which carries fm_glob across a function that writes no static. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI04 YN3v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- fm.asan-ubsan image facts (the donor's A/ACeg.v:61-72, restated on fm's tfibsegs) ---- *)
Lemma g2_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma g2_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr). unfold kLowMemEnd.
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
(map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H.
repeat (destruct H as [H|H]; [injection H as <- <-; lia|]). destruct H.
Qed.
Lemma g2_ret_ok_lit : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> YK0s.ret_ok (Z_to_bv 64 z).
Proof. intros z Hz He. apply YK0s.ret_ok_even. rewrite unsigned_lit_small by lia. exact He. Qed.
(* fm's relro window [FM_RLO, FM_RHI) = [0x99738, 0x9a990) lies in fm.asan-ubsan's third loadable segment
   (PT_LOAD 2: 0x99700 .. 0x9b000, measured on the pin and its unstripped twin) *)
Lemma g2_relro_img : forall a, FM_RLO <= a < FM_RHI -> in_img tfibsegs a.
Proof.
intros a Ha. unfold FM_RLO, FM_RHI in Ha. unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) =>
  let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end.
lia.
Qed.

(* reading the engine's symbolic values back as Z: everything the has_prefixed walk builds is an atom sum *)
Lemma U_atom_mod : forall E n k x, ew E n = Z_to_bv 64 x -> U E (SOff n k) = (x + k) mod 2 ^ 64.
Proof.
intros E n k x H. rewrite U_SOff, H, Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma U_add2 : forall E a b, U E (SAlu ALU_ADD a b) = (U E a + U E b) mod 2 ^ 64.
Proof. intros E a b. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64. reflexivity. Qed.
Lemma U_mul2 : forall E a b, U E (SMd M_MUL a b) = (U E a * U E b) mod 2 ^ 64.
Proof. intros E a b. rewrite U_SMd. cbn [zmd_raw]. unfold zcanon, M64. reflexivity. Qed.
Lemma U_lit : forall E z, U E (SLit z) = z mod 2 ^ 64.
Proof. intros E z. rewrite U_SLit. unfold zcanon, M64. reflexivity. Qed.
Lemma branch_lt_small : forall E a b,
  U E a < 2 ^ 63 -> U E b < 2 ^ 63 -> branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (U E a <? U E b).
Proof.
intros E a b Ha Hb. cbn [branch_taken]. unfold bv_lts, U in *.
rewrite !YK11.bv_signed_small by lia. reflexivity.
Qed.
Lemma branch_ge_small : forall E a b,
  U E a < 2 ^ 63 -> U E b < 2 ^ 63 -> branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (U E a <? U E b).
Proof.
intros E a b Ha Hb. cbn [branch_taken]. unfold bv_lts, U in *.
rewrite !YK11.bv_signed_small by lia. reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* bytes outside [lo, hi) read the same *)
Definition gframe (W : world segs) (lo hi : Z) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview segs (w_H W) m' a = aview segs (w_H W) m a.
Lemma gframe_refl : forall W lo hi m, gframe W lo hi m m.
Proof. intros W lo hi m a _ _. reflexivity. Qed.
Lemma gframe_trans : forall W lo hi lo1 hi1 lo2 hi2 m1 m2 m3,
  gframe W lo1 hi1 m1 m2 -> gframe W lo2 hi2 m2 m3 -> lo <= lo1 -> hi1 <= hi -> lo <= lo2 -> hi2 <= hi ->
  gframe W lo hi m1 m3.
Proof. intros W lo hi lo1 hi1 lo2 hi2 m1 m2 m3 H1 H2 L1 L2 L3 L4 a Ha Hn. rewrite H2, H1 by lia. reflexivity. Qed.
Lemma gframe_widen : forall W lo hi lo' hi' m m',
  gframe W lo' hi' m m' -> lo <= lo' -> hi' <= hi -> gframe W lo hi m m'.
Proof. intros W lo hi lo' hi' m m' H L1 L2 a Ha Hn. apply H; lia. Qed.
Lemma gframe_seq : forall W lo hi m1 m2 m3,
  gframe W lo hi m1 m2 -> gframe W lo hi m2 m3 -> gframe W lo hi m1 m3.
Proof. intros W lo hi m1 m2 m3 H1 H2 a Ha Hn. rewrite H2, H1 by lia. reflexivity. Qed.
Lemma gframe_of_frame : forall W E rs n wlo whi spv lo hi m m',
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  forallb (fun t => win_eqb t (Some n, wlo, whi) || (snd t <=? snd (fst t))) (windows rs) = true ->
  bv_unsigned (ew E n) = spv -> lo <= spv + wlo -> spv + whi <= hi ->
  gframe W lo hi m m'.
Proof.
intros W E rs n wlo whi spv lo hi m m' HF Hw Hn L1 L2 a Ha Hna.
unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. intros Hin.
pose proof (in_wrange_single_b E rs a n wlo whi spv Hw Hn Hin). lia.
Qed.
Lemma val_mem_gframe : forall W lo hi m m' p n v,
  gframe W lo hi m m' -> 0 <= p -> p + Z.of_nat n <= lo -> p + Z.of_nat n <= 2 ^ 64 ->
  val_mem segs (mrestrict (w_H W) m) p n v -> val_mem segs (mrestrict (w_H W) m') p n v.
Proof.
intros W lo hi m m' p n v HG Hp Hpn Hp64 Hv k Hk. rewrite <- (Hv k Hk). apply (mbyte_of_aview segs).
apply HG; lia.
Qed.
Lemma val_mem_gframe_hi : forall W lo hi m m' p n v,
  gframe W lo hi m m' -> hi <= p -> 0 <= p -> p + Z.of_nat n <= 2 ^ 64 ->
  val_mem segs (mrestrict (w_H W) m) p n v -> val_mem segs (mrestrict (w_H W) m') p n v.
Proof.
intros W lo hi m m' p n v HG Hhi Hp Hp64 Hv k Hk. rewrite <- (Hv k Hk). apply (mbyte_of_aview segs).
apply HG; lia.
Qed.

Lemma fm_glob_gframe : forall W lo hi m m' live peak cnt fail,
  gframe W lo hi m m' -> alloc_ceiling <= lo ->
  fm_glob segs W m live peak cnt fail -> fm_glob segs W m' live peak cnt fail.
Proof.
intros W lo hi m m' live peak cnt fail HG Hlo (V1 & V2 & V3 & V4 & R).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold YG0f.ASAN_CEIL in CR.
unfold fm_glob. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply (val_mem_gframe W lo hi m); [exact HG | lia | cbn; lia | cbn; lia | exact V1]|].
split; [apply (val_mem_gframe W lo hi m); [exact HG | lia | cbn; lia | cbn; lia | exact V2]|].
split; [apply (val_mem_gframe W lo hi m); [exact HG | lia | cbn; lia | cbn; lia | exact V3]|].
split; [apply (val_mem_gframe W lo hi m); [exact HG | lia | cbn; lia | cbn; lia | exact V4]|].
exact R.
Qed.
(* a C string lives below alloc_ceiling, so a walk that writes only its stack frame keeps it (shadow bytes too:
   SHADOW_OFF + a / 8 < alloc_ceiling for every a below the ceiling) *)
Lemma cstr_ok_gframe : forall W lo hi m m' p l,
  gframe W lo hi m m' -> alloc_ceiling <= lo -> cstr_ok segs W m p l -> cstr_ok segs W m' p l.
Proof.
intros W lo hi m m' p l HG Hlo ((Hg & Hnz) & H4096 & Hceil & H32 & Ham & Hra & Hhull & Htail).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR. unfold YG0f.ASAN_CEIL in CR.
assert (HSH : forall a, 0 <= a < alloc_ceiling -> shadow_addr a < lo).
{ intros a Ha. unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_le_mono a alloc_ceiling 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). cbn. lia. }
assert (HV : forall a, 0 <= a < alloc_ceiling -> aview segs (w_H W) m' a = aview segs (w_H W) m a)
  by (intros a Ha; apply HG; lia).
assert (HVs : forall a, 0 <= a < alloc_ceiling -> aview segs (w_H W) m' (shadow_addr a) = aview segs (w_H W) m (shadow_addr a)).
{ intros a Ha. apply HG; [unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia));
    pose proof (Z.div_le_mono a alloc_ceiling 8 ltac:(lia) ltac:(lia)); cbn; lia | pose proof (HSH a Ha); lia]. }
split; [split; [|exact Hnz]|].
- intros j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
  intros kk Hk. rewrite <- (Hv kk Hk). apply (mbyte_of_aview segs). apply HV.
  cbn [Z.of_nat] in *. assert (Z.of_nat j < Z.of_nat (length (l ++ [0]))) by lia.
  rewrite length_app in *. cbn [length] in *. lia.
- split; [exact H4096|]. split; [exact Hceil|]. split; [exact H32|]. split; [exact Ham|].
  split.
  { intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    unfold shadow_of_addr in *. change (SHADOW_OFF + x / 8) with (shadow_addr x) in *.
    rewrite HVs; [exact Hs | lia]. }
  split.
  { intros s Hs. rewrite HV; [exact (Hhull s Hs)|].
    unfold shadow_addr, SHADOW_OFF in Hs.
    pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (p + Z.of_nat (length l) + 1 - 1) alloc_ceiling 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (p + Z.of_nat (length l) + 1 - 1) 8 ltac:(lia) ltac:(lia)). cbn in *. lia. }
  intros a Ha. rewrite HV; [exact (Htail a Ha)|].
  pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)). lia.
Qed.
(* the relro/rom view rides through a journal (the donor's A/ACeg.v:49 arodata_ok_journal, over arodata_okP) *)
Lemma arodata_journal : forall RLO RHI STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  (forall a, fp_spares FP a) -> (forall a, ~ inFP FP a) -> (forall a, RLO <= a < RHI -> in_img segs a) ->
  arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
  arodata_okP segs RLO RHI B (aview segs (w_H W') mem').
Proof.
intros RLO RHI STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ Hfp HnF Himg HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | apply HnF | apply Hfp].
destruct Hro as [(s & Hs & _ & Hr) | Hin]; [exists s; split; [exact Hs | exact Hr] | exact (Himg a Hin)].
Qed.

(* a contract in FMH_Rt's rt_post_roU form, used with no user-poisoned range, is one in rt_post_ro form *)
Lemma rt_post_ro_of_roU : forall STK ly S W regs mem md (R : Z -> Prop) W' c',
  rt_post_roU segs B STK ly S [] W regs mem md R W' c' -> rt_post_ro segs B STK ly S W regs mem md R W' c'.
Proof.
intros STK ly S W regs mem md R W' c' (-> & regs' & mem' & md' & v & Hc & HAR & _ & HP & HSBM & H10 & Hv & HR & Hfr & Hpres).
rewrite unpoison_nil in HAR.
split; [reflexivity|]. exists regs', mem', md', v.
split; [exact Hc|]. split; [exact HAR|]. split; [exact HP|]. split; [exact HSBM|].
split; [exact H10|]. split; [exact Hv|]. split; [exact HR|]. split; [exact Hfr | exact Hpres].
Qed.

(* a call to a runtime routine whose contract has FMH_Rt's rt_post_ro form, inside a journal walk *)
Lemma aj_rt_ro : forall (STKr pc : Z) (R : Z -> Prop)
  W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
  ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK <= STKr -> STKr - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (ecall_pre_k segs B STKr lyc Sc W regsT memT mdc ->
     SRr segs W (cfg_at segs pc regsT memT mdc) (rt_post_ro segs B STKr lyc Sc W regsT memT mdc R)) ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : Z),
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v /\
       gframe W (sp0 + o - STKr) (sp0 + o) memT mem2 /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros STKr pc R W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw
  HJ Hsp' Hal Hneg Hes Hbud Hgp Htp Hra Hraw HC.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption; [zlia|].
  rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HPK : ecall_pre_k segs B STKr lyc Sc W regsT memT mdc).
{ split; [exact HPRE|]. split; [rewrite Eslo; exact Hceil|]. split; [rewrite Eslo, Hsp'; zlia|].
  intros a Ha. apply Hpres. rewrite Hsp' in Ha. zlia. }
eapply SRr_mono; [exact (HC HPK)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hv & HR & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => sp0 + o - STKr <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; left; zlia.
  - exact HAR2.
  - reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hv|]. split; [exact HR|].
split; [intros a Ha Hna; exact (Hfr a Ha Hna) | exact Hpres2].
Qed.
End a.
