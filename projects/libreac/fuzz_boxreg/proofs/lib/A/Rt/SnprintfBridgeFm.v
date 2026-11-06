(* libreac/fuzz_boxreg: the image-generic bridge from a Theorem Labs lane's shared snprintf statement, at ANY format family, to
   boxreg's R2 call-level contract (lib/A/Rt/SnprintfDef.v asnprintf_realizes and lib/B/Rt/SnprintfDefB.v
   absnprintf_realizes, abd0df80365). Rule 24: no function is proved here. No image content: every name is over a
   Section's segs and B; the instances are lib/A/Rt/SnprintfBridgeFmA.v (TfibB of fuzz_boxreg.asan, a Theorem Labs lane's FF_fm)
   and lib/B/Rt/SnprintfBridgeFmB.v (fuzz_boxreg.asan-ubsan), and lib/B/Rt/SnprintfBridgeB.v proves its
   boxb_absnprintf_of_shared here.
   Why it exists: lib/A/Rt/SnprintfBridge.v box_asnprintf_of_shared takes the family pf_family (fun p => p = Ps) and a
   constant list whose bytes are no owned static (snp_cr_not_owned). A Theorem Labs lane's proved snprintf (lib/A/Rt/FMsnprintfFmI.v
   fm_snprintf_gxa_AR) has the family FF_fm (FMsnprintfFmI.v:32-37) and the constant list fm_cr = the image's
   non-writable segments, which holds owned statics (the read-only globals' right redzones, e.g. (0x20ce1, 0x1f)), so
   snp_cr_not_owned is false for it. And the R2 contracts of the two images differ in one constant, the format bound
   P2 (f + 3 <= 0x99b40 on A, <= 0x99f60 on B: each image's GOT canary slot), so neither contract converts to the other.
   - snp_fm_realizes hi: the R2 contract text with the P2 bound as hi; at hi = 0x99b40 it is asnprintf_realizes
     (asnprintf_of_snp_fm), at hi = 0x99f60 absnprintf_realizes (both by conversion: the B text is the A text with
     B names for ASN_FMT, asn_word_end, asn_rom_kept).
   - snp_fm_of_shared: the shared statement at a family FF -> snp_fm_realizes hi. It is box_asnprintf_of_shared's
     proof (its lemmas and steps: destination facts, constants and canary cells apart from the window and the written
     part, canary words, writable-globals range, K = 2 * ESTACK, no stack slot) with two premises in place of its
     family and its owned-static condition:
     (1) snp_ff_entry FF hi: FF holds for the format "%s" at f and one %s argument x whenever 0x10000 <= f,
         f + 3 <= hi and amem_range x (|s| + 8), i.e. the contract's R2 premises P1, P2, P3 (P3 also gives
         pf_arg_asan's amem_range x (|s| + 1)). pf_family (fun p => p = Ps) meets it at every hi (snp_ff_entry_ps);
         FF_fm at its own bound (SnprintfBridgeFmA.v / SnprintfBridgeFmB.v);
     (2) snp_cv_kept cr: consts_view cr in every AR state whose read-only image is kept (asn_rom_kept, the contract's
         premise). snp_cr_not_owned and snp_cr_not_errno give it (snp_cv_kept_of_not_owned, SnprintfBridge.v
         snp_consts_view); for fm_cr the instances take fm's route (FMsnprintfCr.v fm_cr_consts_view). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import FMsnprintfPf FMsnprintfShared FMsnprintfSx.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require Import SnprintfDef SnprintfBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require FMupoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* amem_range holds for every shorter range at the same start. *)
Lemma snp_amem_le : forall p n n', n' <= n -> amem_range p n -> amem_range p n'.
Proof. intros p n n' Hle H. unfold amem_range in *. lia. Qed.
(* A family takes boxreg's call: the format "%s" at f and one %s argument x, under the contract's R2 premises
   0x10000 <= f, f + 3 <= hi and amem_range x (|s| + 8); the argument words after x are any. *)
Definition snp_ff_entry (FF : fmt_fam) (hi : Z) : Prop :=
forall rd rs f x ws (s : list Z), fmt_at rd rs f [37; 115] -> pf_arg_asan rd rs x (APtr s) ->
0x10000 <= f -> f + 3 <= hi -> amem_range x (Z.of_nat (length s) + 8) -> FF rd rs f (x :: ws) s.
(* boxreg's own family, pf_family (fun p => p = Ps), takes the call at every bound. *)
Lemma snp_ff_entry_ps : forall hi, snp_ff_entry (pf_family (fun p => p = Ps)) hi.
Proof.
intros hi rd rs f x ws s Hf Ha _ _ _.
exists [37; 115], [Ps], [APtr s].
split; [exact Hf|]. split; [reflexivity|]. split; [constructor; [reflexivity | constructor]|].
split; [split; [exact Ha | destruct ws; exact I]|].
split; [cbn [pf_text option_map]; rewrite app_nil_r; reflexivity | exact I].
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
(* lib/A/Rt/SnprintfDef.v asnprintf_realizes (R2, abd0df80365) verbatim, with the bound 0x99b40 of P2 as hi. *)
Definition snp_fm_realizes (hi pc : Z) : Prop :=
forall ly S W regs mem md d n f x (s : list Z) p m,
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f -> getr regs 13 = w64 x ->
1 <= n < 2 ^ 31 ->
In (p, m) (ablocks B ly S) -> p <= d -> d + n <= p + m ->
(forall a, d <= a < d + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
(forall i, 0 <= i < 3 -> aview segs (w_H W) mem (f + i) = Some (nth (Z.to_nat i) ASN_FMT 0)) ->
0 < f -> amem_range f 3 ->
0x10000 <= f -> f + 3 <= hi ->
(forall a, f <= a < f + 3 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) -> (f + 3 <= d \/ d + n <= f) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF f 3 -> shadow_hull_vis (aview segs (w_H W) mem) f 3 ->
Forall (fun c => 0 < c < 256) s -> Z.of_nat (length s) + 8 < 2 ^ 31 -> 0 < x ->
(forall i, 0 <= i <= Z.of_nat (length s) -> aview segs (w_H W) mem (x + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0)) ->
(forall a, x + Z.of_nat (length s) < a < asn_word_end x (Z.of_nat (length s)) -> aview segs (w_H W) mem a <> None) ->
amem_range x (Z.of_nat (length s) + 8) ->
(forall a, x <= a < asn_word_end x (Z.of_nat (length s)) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
(asn_word_end x (Z.of_nat (length s)) <= d \/ d + n <= x) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length s) + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) x (Z.of_nat (length s) + 1) ->
asn_rom_kept segs B W mem ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length s)) /\
(forall i, 0 <= i < Z.of_nat (length (asn_out n s)) ->
aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (asn_out n s) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + Z.of_nat (length (asn_out n s))) ->
~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Lemma asnprintf_of_snp_fm : forall pc, snp_fm_realizes 0x99b40 pc -> asnprintf_realizes segs B pc.
Proof. intros pc H. exact H. Qed.
(* In every AR state whose read-only image is kept, the constants cr read as the image's bytes. *)
Definition snp_cv_kept (cr : list (Z * Z)) : Prop :=
forall ly S (W : world segs) mem md, AR segs B ly S W mem md -> asn_rom_kept segs B W mem -> consts_view segs W mem cr.
(* A constant list with no owned static and no errno byte reads through asn_rom_kept alone. *)
Lemma snp_cv_kept_of_not_owned : forall cr,
snp_cr_rom segs cr -> snp_cr_not_owned B cr -> snp_cr_not_errno B cr -> snp_cv_kept cr.
Proof.
intros cr Hcr Hno Hne ly S W mem md _ Hrk. exact (snp_consts_view segs B cr W mem Hcr Hno Hne Hrk).
Qed.
(* ---- the bridge ---- *)
Theorem snp_fm_of_shared : forall FF hi gc gv img_lo img_hi cr pc,
AR_laws segs B -> snp_ff_entry FF hi ->
snp_cr_rom segs cr -> snp_cv_kept cr ->
snp_img_word segs gc -> snp_img_word segs gv -> snp_canary_ar segs B gc gv -> snp_img_range segs img_lo img_hi ->
sh_asnprintf_realizes segs B FF (2 * ESTACK) gc gv img_lo img_hi cr pc ->
snp_fm_realizes hi pc.
Proof.
intros FF hi gc gv img_lo img_hi cr pc LAWS HFE Hcr Hcv Hgc Hgv Hcan Himg HSH.
intros ly S W regs mem md d n f x s p m HPRE HK Hwin Ha0 Ha1 Ha2 Ha3 Hn Hin Hpd Hdn Hdwin
  Hfb Hf0 Hfm Hflo Hfhi Hfwin Hfd Hfra Hfsh Hsb Hsl Hx0 Hsx Htail Hxm8 Hxwin Hxd Hxra Hxsh Hrk Hfrm.
pose proof HPRE as (HAR & _ & _ & Hslo & Hshi & _).
assert (EK : 2 * ESTACK = 8192) by reflexivity.
assert (EE : ESTACK = 4096) by reflexivity.
pose proof (snp_sn_len_bounds n s ltac:(lia)) as Hw0.
set (w := sn_len (n - 1) s) in *.
assert (Hw : 1 <= w <= n) by lia.
assert (Hm : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (Hdw : d + w <= p + req_size m) by lia.
assert (Hdwin1 : forall a, d <= a < d + w -> ~ (spZ regs - ESTACK <= a < spZ regs)).
{ intros a Ha Hc. apply (Hdwin a); lia. }
destruct (snp_dest_facts segs B ly S W regs mem md p m d w LAWS HAR Hin Hpd Hdw ltac:(lia) Hdwin1)
  as (Hd0 & Hd63 & Hdok & Hdam8 & Hdra & Hdsh).
assert (HZG : zdisjoint (d, w) (img_lo, img_hi - img_lo))
  by exact (snp_dest_zd_img segs B ly S W mem md p m d w img_lo img_hi LAWS HAR Hin Hpd ltac:(lia) ltac:(lia) Himg).
destruct (Hcan ly S W mem md HAR) as [Hgcv [cval Hcval]].
pose proof Hgc as (Hgc0 & Hgc8 & _). pose proof Hgv as (Hgv0 & Hgv8 & _).
(* the constants *)
assert (HCV : consts_view segs W mem cr) by exact (Hcv ly S W mem md HAR Hrk).
assert (HCB : Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr).
{ eapply Forall_impl; [|exact (proj1 Hcr)]. intros r (_ & H1 & H2). split; assumption. }
assert (HCD : Forall (fun r => Forall (zdisjoint r) (snp_out (2 * ESTACK) (spZ regs) d w)) cr)
  by exact (snp_cr_apart segs B cr ly S W mem md (2 * ESTACK) (spZ regs) p m d w LAWS HAR Hcr ltac:(lia) HK Hshi Hin
    Hpd Hdw ltac:(lia)).
(* the canary cells *)
assert (HGC : Forall (zdisjoint (gc, 8)) (snp_out (2 * ESTACK) (spZ regs) d w)).
{ apply (snp_img_apart segs B ly S W mem md (2 * ESTACK) (spZ regs) p m d w gc 8 LAWS HAR ltac:(lia) HK Hshi Hin Hpd
    Hdw ltac:(lia) ltac:(lia)).
  exact (snp_img_word_img segs gc Hgc). }
assert (HGV : Forall (zdisjoint (gv, 8)) (snp_out (2 * ESTACK) (spZ regs) d w)).
{ apply (snp_img_apart segs B ly S W mem md (2 * ESTACK) (spZ regs) p m d w gv 8 LAWS HAR ltac:(lia) HK Hshi Hin Hpd
    Hdw ltac:(lia) ltac:(lia)).
  exact (snp_img_word_img segs gv Hgv). }
(* the arguments: a3 .. a7, no stack slot *)
assert (Hxm : amem_range x (Z.of_nat (length s) + 1))
  by exact (snp_amem_le x (Z.of_nat (length s) + 8) (Z.of_nat (length s) + 1) ltac:(lia) Hxm8).
assert (Ha3' : argZ regs 3 = x).
{ unfold argZ. assert (E : getr regs (Z_to_bv 5 (10 + 3)) = getr regs 13) by (f_equal; apply bv_eq; reflexivity).
  rewrite E, Ha3. unfold w64. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
  change (bv_modulus 64) with (2 ^ 64). unfold amem_range, kHighMemEnd, kLowMemEnd, kHighMemBeg in Hxm. lia. }
assert (Hva : va_words regs (aview segs (w_H W) mem) (spZ regs) [] (map (argZ regs) [3; 4; 5; 6; 7] ++ [])).
{ split; [reflexivity|]. intros i Hi. cbn [length] in Hi. lia. }
assert (Hsp8 : spZ regs + 8 * Z.of_nat (length ([] : list Z)) <= 2 ^ 47).
{ apply (va_slots_below_47_nil segs B ly S [] W regs mem md). apply FMupoison.ecall_preU_nil. exact HPRE. }
assert (Hspd : Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length ([] : list Z)))) (snp_out (2 * ESTACK) (spZ regs) d w)).
{ cbn [length Z.of_nat]. unfold snp_out. constructor; [|constructor; [|constructor]].
  - unfold zdisjoint; cbn [fst snd]. lia.
  - unfold zdisjoint; cbn [fst snd].
    destruct (Z_le_gt_dec (spZ regs) d) as [E1|E1]; [left; lia|]. right.
    destruct (Z_le_gt_dec (d + w) (spZ regs)) as [E2|E2]; [exact E2|].
    exfalso. apply (Hdwin (spZ regs - 1)); lia. }
(* the format family, from the R2 premises *)
assert (HFF : FF (aview segs (w_H W) mem) (snp_out (2 * ESTACK) (spZ regs) d w) f
  (map (argZ regs) [3; 4; 5; 6; 7] ++ []) s).
{ cbn [map app]. rewrite Ha3'. apply HFE; [| | exact Hflo | exact Hfhi | exact Hxm8].
  - unfold fmt_at. change (Z.of_nat (length [37; 115]) + 1) with 3.
    split; [exact Hf0|]. split.
    { intros i Hi. change (Z.of_nat (length [37; 115])) with 2 in Hi. exact (Hfb i ltac:(lia)). }
    split.
    { unfold snp_out. constructor; [|constructor; [|constructor]].
      - apply snp_zd_of_pts; [lia | lia |]. intros z Hz1 Hz2. apply (Hfwin z Hz1). lia.
      - unfold zdisjoint; cbn [fst snd]. lia. }
    split; [exact Hfm|]. split; [exact Hfra | exact Hfsh].
  - cbn [pf_arg_asan].
    assert (HE : str_end x s = asn_word_end x (Z.of_nat (length s))) by reflexivity.
    pose proof (Z.mod_pos_bound (x + Z.of_nat (length s)) 8 ltac:(lia)) as Hmod.
    split; [exact Hsb|]. split; [exact Hx0|]. split; [exact Hsl|]. split; [exact Hsx|].
    split; [rewrite HE; exact Htail|].
    split.
    { rewrite HE. unfold snp_out. constructor; [|constructor; [|constructor]].
      - apply snp_zd_of_pts; [unfold asn_word_end; lia | lia |]. intros z Hz1 Hz2.
        apply (Hxwin z); lia.
      - unfold zdisjoint; cbn [fst snd]. lia. }
    split; [exact Hxm|]. split; [exact Hxra | exact Hxsh]. }
(* the destination's pairwise disjointness *)
assert (HPW : pairwise zdisjoint (snp_out (2 * ESTACK) (spZ regs) d w)).
{ unfold snp_out. cbn [pairwise]. split; [|split; [constructor | exact I]]. constructor; [|constructor].
  apply snp_zd_of_pts; [lia | lia |]. intros z Hz1 Hz2. apply (Hdwin z); lia. }
assert (HTl : Z.of_nat (length s) < 2 ^ 31 - 1) by lia.
eapply SRr_mono.
{ exact (HSH ly S W regs mem md d n f [] (map (argZ regs) [3; 4; 5; 6; 7] ++ []) s cval
    HPRE HK Hwin Ha0 Ha1 Ha2 HCV HCB HCD Hgcv Hcval Hgc0 Hgc8 Hgv0 Hgv8 HGC HGV Hva Hsp8 Hspd HFF Hn HTl Hd0 Hd63 HPW
    Hdok Hdam8 Hdra Hdsh HZG Hfrm). }
intros W' c' _ HQ. exact HQ.
Qed.
End c.
End b.
