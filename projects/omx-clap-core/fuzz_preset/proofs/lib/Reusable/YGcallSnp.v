(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31 (the world relation R): aj_snprintf_at_xromR is the call-site rule over a
   journal at a reflexive and transitive world relation R (binders first; the call keeps the world, so no law of R is
   read); aj_snprintf_at_xrom keeps its statement and is the instance at wle. *)
(* Theorem Labs, 2026-10: the snprintf RUNTIME ROW and its CALL-SITE RULE, GENERIC over the allocator invariant ARx
   of YCbqG.v (Section Variables segs B PST ARx rlo rhi), beside YGcallMx.v's strcmp / strlen rows. No allocator
   instance, no image class, no address and no ledger is named here. TEXT FOR ANNOUNCEMENT (c-omx-alloc, owner ruling
   c-omx-hpreset 10:53Z step 5a; revised by c-omx-alloc 2026-10-29: read-only premise arodata_okP, memnorm keep):
   c-libc-stdio proves it from its restated chain; h-mani-a8's po_snprintf_cf is discharged by instantiating it at
   ARx := ARcf segs B (YGcallSnpCk.v asnprintf_cf_of_xrom, which needs the read-only bridge named there).

   1. THE TEXT asnprintf_realizes_xrom rlo rhi FF K gc gv img_lo img_hi cr pc = port-fm's shared snprintf top over
      ecall_pre_x: FMsnprintfSharedCf.v:32-67 sh_asnprintf_realizes_cf (origin/cold/port-fm-rtprintf-param
      0ddf65fd8cc, here by path; header line 1) with
      - ecall_pre_cf segs B -> ecall_pre_x segs B ARx (FCiface.v:42-48; = ecall_pre_cf at ARx := ARcf segs B),
      - ARcf segs B -> ARx in the post, the ghost set Hp threaded UNCHANGED (snprintf allocates nothing and moves no
        poison window: a Theorem Labs lane's measurement, the internal file preset-snprintf-U.md sections 3.2 and 4),
      - the per-call rom_view -> arodata_okP segs rlo rhi B (aview segs (w_H W) mem): the _xro form of
        h-pre-b3's ExvB_StrcmpRo.v:59 / ExwB_StrlenRo.v (origin/cold/h-pre-b3-exword-b 2038bfaedb4e; c-libc-stdio's
        ruling 11:46Z: rom_view does not follow from ARcf + arodata_okP at image B),
      - the post gains the memnorm KEEP (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem') as its LAST
        conjunct (the m-form; YGcallMxmn.v's convention, over YAkMemnorm, not YAjMemnorm).
      Everything else is the shared top's text as it stands: the destination's amem_range d (w + 8) (port-fm
      00daeaf3796, "the destination's 8-byte slack": musl vfprintf's pf_rng asks app_mem (D + i + 7)), the format
      family FF (preset: a8's FF_preset, pieces literal / %c / %04x, CfSnprintfPreset.v:33-41), the stack window K,
      the stack-protector cells gc -> gv -> cval, the image range [img_lo, img_hi) the destination avoids, the
      read-only ranges cr (consts_view), the argument words va_words (a3..a7, then xs on the caller's stack), the
      written part w = sn_len (n - 1) T, the entry rounding mode 0. The post: the float state fx' keeps every f
      register but f10 and frm = 0 (the shared top's float clause); ARx at the SAME (ly, S, Hp, W); a0 = |T|; the
      destination bytes sn_bytes (n - 1) T through aview; nothing else changes outside the destination and the window
      K; presence grows; the memnorm keep.
      asnprintf_realizes_xro is the same text without the keep; asnprintf_realizes_xrom_forget gives it. Names follow
      YGcallMxmn.v (c-omx-alloc 2026-10-29): _xro = the arodata_okP form, _xrom = the arodata_okP form with the keep.
      Hull: the text bounds no block's tail. The one "+ 8" is amem_range's application-memory slack past the
      destination (a range bound, not a granule past an aligned block).
   0. in_roP / arodata_okP: NOT defined here. They are the leaf lib/Spec/PresetRodata.v (blob 4eb7e95e7e93, by path
      from commit 1bba49fd7ac5), Required, so the text's read-only premise is
      PresetRodata.arodata_okP: one home (the lib/Spec/PresetRodataCheck.v checks the re-exporters with constr_eq).
      The leaf is LiaTwx2-free but NOT override-free (a Theorem Labs lane's measured probe, 2026-10-29: `Print Ltac lia` after
      Requiring the leaf alone prints the YM05 / YM03 body, "Redefined by: YM05 YM03"), and this file already carries
      that override, so the leaf buys one home only, not a stock lia.
   2. THE RULE aj_snprintf_at_xrom (Section l): aj_strcmp_at_x's derivation (YGcallMx.v:506-566) at this text. The call's
      ecall_pre_x is proved inline from the journal as YCbq.v:1913 ecall_pre_at proves cgif's; the destination's
      dest_ok from awr_byte (awr_byte_present_x, YGcallMx.v:193) and the window disjointness; the journal is kept at the
      call's state by ajournal_x_after_write (YCbqG.v:393) over the destination and the window K, with the float
      state existential as in apost_base_xF (YCbqG.v:224-231). The keep is the LAST conclusion conjunct in
      IMPLICATION form (YAkMemnorm.memnorm segs memT -> YAkMemnorm.memnorm segs mem2), with no memnorm premise.
   3. asnprintf_realizes_xrom_conj (Section cj): YGcallMx.v:574-612's shape (a text at ARx holds at ARx /\ P).

   This file's Require closure holds no lib/Lib file and no LiaTwx2 `Ltac lia ::=` (it Requires neither PRH_Base, nor
   YAjMemnorm, nor any lib/Lib file; lib/Spec/PresetRodata.v Requires only Stdlib, BvBase / MemImageType and YK11 /
   YG0f / YG0n).

   Numerals: 10, 11, 12 (RISC-V registers, WORD), 1, 3, 4 (registers, WORD); 5 and 7 (the frm field of fcsr, WORD);
   1 in n - 1 (DERIVED: the cookie count); 8 (rdword width / destination slack, LENGTH);
   16 (stack alignment, LENGTH); 2 ^ 31, 2 ^ 47, 2 ^ 63, 2 ^ 64 (LENGTH bounds of the shared top). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FMsnprintfPf FMsnprintfShared.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetRodata.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section snp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variables rlo rhi : Z.
Local Abbreviation AJ := (ajournal_x (SK := SK) segs B PST ARx).

(* ---------------------------------------------------------------------------- *)
(* 1. The text.                                                                   *)
(* port-fm's FMsnprintfSharedCf.v:32-67 (0ddf65fd8cc) over ecall_pre_x / ARx; Hp unchanged through the call; the
   read-only premise arodata_okP (the _xro form); the memnorm keep as the last post conjunct. *)
Definition asnprintf_realizes_xrom (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S Hp W regs mem md d n f (xs ws T : list Z) cval,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f ->
consts_view segs W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (fun r => Forall (zdisjoint r) (snp_out K (spZ regs) d (sn_len (n - 1) T))) cr ->
rdword (aview segs (w_H W) mem) gc = Some gv -> rdword (aview segs (w_H W) mem) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
Forall (zdisjoint (gv, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
va_words regs (aview segs (w_H W) mem) (spZ regs) xs ws ->
spZ regs + 8 * Z.of_nat (length xs) <= 2 ^ 47 ->
Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length xs))) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
FF (aview segs (w_H W) mem) (snp_out K (spZ regs) d (sn_len (n - 1) T)) f ws T ->
1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + sn_len (n - 1) T <= 2 ^ 63 ->
pairwise zdisjoint (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
dest_ok segs B ly S W regs mem d (sn_len (n - 1) T) -> amem_range d (sn_len (n - 1) T + 8) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d (sn_len (n - 1) T) ->
shadow_hull_vis (aview segs (w_H W) mem) d (sn_len (n - 1) T) ->
(* dest_off_globals *) zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo) ->
(* frm0_entry *) Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')).

(* the same text without the memnorm keep *)
Definition asnprintf_realizes_xro (FF : fmt_fam) (K gc gv img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
forall ly S Hp W regs mem md d n f (xs ws T : list Z) cval,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + K <= spZ regs ->
(forall a, spZ regs - K <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 d -> getr regs 11 = w64 n -> getr regs 12 = w64 f ->
consts_view segs W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (fun r => Forall (zdisjoint r) (snp_out K (spZ regs) d (sn_len (n - 1) T))) cr ->
rdword (aview segs (w_H W) mem) gc = Some gv -> rdword (aview segs (w_H W) mem) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
Forall (zdisjoint (gv, 8)) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
va_words regs (aview segs (w_H W) mem) (spZ regs) xs ws ->
spZ regs + 8 * Z.of_nat (length xs) <= 2 ^ 47 ->
Forall (zdisjoint (spZ regs, 8 * Z.of_nat (length xs))) (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
FF (aview segs (w_H W) mem) (snp_out K (spZ regs) d (sn_len (n - 1) T)) f ws T ->
1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + sn_len (n - 1) T <= 2 ^ 63 ->
pairwise zdisjoint (snp_out K (spZ regs) d (sn_len (n - 1) T)) ->
dest_ok segs B ly S W regs mem d (sn_len (n - 1) T) -> amem_range d (sn_len (n - 1) T + 8) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d (sn_len (n - 1) T) ->
shadow_hull_vis (aview segs (w_H W) mem) d (sn_len (n - 1) T) ->
(* dest_off_globals *) zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo) ->
(* frm0_entry *) Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) ->
~ (spZ regs - K <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* forgetting the keep gives the plain text *)
Lemma asnprintf_realizes_xrom_forget : forall FF K gc gv img_lo img_hi cr pc,
asnprintf_realizes_xrom FF K gc gv img_lo img_hi cr pc -> asnprintf_realizes_xro FF K gc gv img_lo img_hi cr pc.
Proof.
intros FF K gc gv img_lo img_hi cr pc AS ly S Hp W regs mem md d n f xs ws T cval HPRE. intros.
eapply SRr_mono; [apply (AS ly S Hp W regs mem md d n f xs ws T cval HPRE); assumption |].
cbv beta. intros W' c' _ (-> & fx' & regs' & mem' & md' & Hc & Hf1 & Hf2 & HAR' & HP & Hsame & Hres & Hbytes & Hfr & Hpres' & _).
split; [reflexivity|]. exists fx', regs', mem', md'.
exact (conj Hc (conj Hf1 (conj Hf2 (conj HAR' (conj HP (conj Hsame (conj Hres (conj Hbytes (conj Hfr Hpres'))))))))).
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The call-site rule.                                                         *)
Section l.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* aj_snprintf_at_xrom over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_snprintf_at_xrom is its case R := wle *)
Lemma aj_snprintf_at_xromR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall FF K gc gv img_lo img_hi cr pc, asnprintf_realizes_xrom FF K gc gv img_lo img_hi cr pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d n f (xs ws T : list Z) cval (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 n -> getr regsT 12 = w64 f ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK <= K -> K - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
consts_view segs W memT cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (fun r => Forall (zdisjoint r) (snp_out K (sp0 + o) d (sn_len (n - 1) T))) cr ->
rdword (aview segs (w_H W) memT) gc = Some gv -> rdword (aview segs (w_H W) memT) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (snp_out K (sp0 + o) d (sn_len (n - 1) T)) ->
Forall (zdisjoint (gv, 8)) (snp_out K (sp0 + o) d (sn_len (n - 1) T)) ->
va_words regsT (aview segs (w_H W) memT) (sp0 + o) xs ws ->
sp0 + o + 8 * Z.of_nat (length xs) <= 2 ^ 47 ->
Forall (zdisjoint (sp0 + o, 8 * Z.of_nat (length xs))) (snp_out K (sp0 + o) d (sn_len (n - 1) T)) ->
FF (aview segs (w_H W) memT) (snp_out K (sp0 + o) d (sn_len (n - 1) T)) f ws T ->
1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + sn_len (n - 1) T <= 2 ^ 63 ->
pairwise zdisjoint (snp_out K (sp0 + o) d (sn_len (n - 1) T)) ->
(forall a, d <= a < d + sn_len (n - 1) T -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
amem_range d (sn_len (n - 1) T + 8) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d (sn_len (n - 1) T) ->
shadow_hull_vis (aview segs (w_H W) memT) d (sn_len (n - 1) T) ->
zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo) ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP segs rlo rhi B (aview segs (w_H W) memT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fx' : YK11.FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom segs)) md2 /\
(forall kr : bv 5, bv_unsigned kr <> 10 -> Sem.reg_get (@fp_regs fx') kr = Sem.reg_get (@fp_regs fx) kr) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem2 (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) -> ~ (sp0 + o - K <= a < sp0 + o) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
(YAkMemnorm.memnorm segs memT -> YAkMemnorm.memnorm segs mem2)).
Proof.
intros R R_refl R_trans FF K gc gv img_lo img_hi cr pc AS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d n f xs ws T cval o raw
HJ Ha0 Ha1 Ha2 Hsp' Hal Hneg HKE HKS Hgp Htp Hra Hraw Hcv Hcrb Hcrd Hgc Hgv Hgc0 Hgc8 Hgv0 Hgv8 Hgcd Hgvd
Hva Hxs Hxsd HFF Hn HT Hd0 Hdw Hpw Hdest Hamr Hrad Hhull Himg Hfrm Hro.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hwle. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
(* the call's ecall_pre_x, as cgif's ecall_pre_at (YCbq.v:1913) *)
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [rewrite Hsp', Z.add_mod, Hal16, Hal by zlia; reflexivity|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
assert (HloK : ly_stk_lo lyc + K <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (HpresK : forall a, spZ regsT - K <= a < spZ regsT -> apresent (w_H W) memT a)
by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
(* the destination misses the window K, hence the ESTACK window (ESTACK <= K) *)
assert (Hdk : zdisjoint (sp0 + o - K, K) (d, sn_len (n - 1) T)).
{ pose proof Hpw as Hpw'. unfold snp_out in Hpw'. cbn [pairwise] in Hpw'. destruct Hpw' as [Hpw1 _].
  exact (Forall_inv Hpw1). }
unfold zdisjoint in Hdk. cbn [fst snd] in Hdk.
assert (HDEST : dest_ok segs B lyc Sc W regsT memT d (sn_len (n - 1) T)).
{ intros a Ha.
  destruct (awr_byte_present_xR segs B PST ARx LAWS R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k a HJ (Hdest a Ha))
    as [Hpa Hno].
  split; [apply apresent_writable; exact Hpa|]. split; [exact Hno|]. rewrite Hsp'. zlia. }
eapply SRr_mono.
{ exact (AS lyc Sc Hpc W regsT memT mdc d n f xs ws T cval HPRE HloK HpresK Ha0 Ha1 Ha2 Hcv Hcrb
  ltac:(rewrite Hsp'; exact Hcrd) Hgc Hgv Hgc0 Hgc8 Hgv0 Hgv8
  ltac:(rewrite Hsp'; exact Hgcd) ltac:(rewrite Hsp'; exact Hgvd)
  ltac:(rewrite Hsp'; exact Hva) ltac:(rewrite Hsp'; exact Hxs) ltac:(rewrite Hsp'; exact Hxsd)
  ltac:(rewrite Hsp'; exact HFF) Hn HT Hd0 Hdw ltac:(rewrite Hsp'; exact Hpw) HDEST Hamr Hrad Hhull Himg Hfrm Hro). }
cbv beta. intros W2 c2 _
  (-> & fx' & regs2 & mem2 & md2 & -> & Hfl & Hfrm' & HAR2 & HP & Hsame & Hres & Hbytes & Hfr & Hpres2 & Hmn).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists fx', regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact Hfl|]. split; [exact Hfrm'|].
split.
{ eapply (ajournal_x_after_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k
    mem2 md2 (fun a => (d <= a < d + sn_len (n - 1) T) \/ (sp0 + o - K <= a < sp0 + o)) Sc Hpc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (Hdest a Ha) | left; zlia].
  - exact HAR2.
  - reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. - reflexivity. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hbytes|]. split; [exact Hfr|].
split; [exact Hpres2 | exact Hmn].
Qed.

(* aj_strcmp_at_x's shape (YGcallMx.v:506) at the snprintf text: a0 = d (the destination, every written byte one the
   journal may write), a1 = n, a2 = f (the format, with the argument words ws), the call's stack window K inside the
   journal's budget; the call returns a0 = |T| with the destination holding sn_bytes (n - 1) T, keeps the journal at
   the call's state, writes only the destination and its window K, leaves a float state fx' that keeps every f
   register but f10 and the rounding mode 0, and keeps memnorm (the implication, last). *)
Lemma aj_snprintf_at_xrom : forall FF K gc gv img_lo img_hi cr pc, asnprintf_realizes_xrom FF K gc gv img_lo img_hi cr pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d n f (xs ws T : list Z) cval (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 n -> getr regsT 12 = w64 f ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK <= K -> K - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
consts_view segs W memT cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
Forall (fun r => Forall (zdisjoint r) (snp_out K (sp0 + o) d (sn_len (n - 1) T))) cr ->
rdword (aview segs (w_H W) memT) gc = Some gv -> rdword (aview segs (w_H W) memT) gv = Some cval ->
0 <= gc -> gc + 8 <= 2 ^ 63 -> 0 <= gv -> gv + 8 <= 2 ^ 63 ->
Forall (zdisjoint (gc, 8)) (snp_out K (sp0 + o) d (sn_len (n - 1) T)) ->
Forall (zdisjoint (gv, 8)) (snp_out K (sp0 + o) d (sn_len (n - 1) T)) ->
va_words regsT (aview segs (w_H W) memT) (sp0 + o) xs ws ->
sp0 + o + 8 * Z.of_nat (length xs) <= 2 ^ 47 ->
Forall (zdisjoint (sp0 + o, 8 * Z.of_nat (length xs))) (snp_out K (sp0 + o) d (sn_len (n - 1) T)) ->
FF (aview segs (w_H W) memT) (snp_out K (sp0 + o) d (sn_len (n - 1) T)) f ws T ->
1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 -> 0 < d -> d + sn_len (n - 1) T <= 2 ^ 63 ->
pairwise zdisjoint (snp_out K (sp0 + o) d (sn_len (n - 1) T)) ->
(forall a, d <= a < d + sn_len (n - 1) T -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
amem_range d (sn_len (n - 1) T + 8) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d (sn_len (n - 1) T) ->
shadow_hull_vis (aview segs (w_H W) memT) d (sn_len (n - 1) T) ->
zdisjoint (d, sn_len (n - 1) T) (img_lo, img_hi - img_lo) ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
arodata_okP segs rlo rhi B (aview segs (w_H W) memT) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fx' : YK11.FPState) regs2 mem2 md2,
c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom segs)) md2 /\
(forall kr : bv 5, bv_unsigned kr <> 10 -> Sem.reg_get (@fp_regs fx') kr = Sem.reg_get (@fp_regs fx) kr) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (Z.of_nat (length T)) /\
(forall i, 0 <= i < sn_len (n - 1) T -> aview segs (w_H W) mem2 (d + i) = Some (nth (Z.to_nat i) (sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sn_len (n - 1) T) -> ~ (sp0 + o - K <= a < sp0 + o) ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
(YAkMemnorm.memnorm segs memT -> YAkMemnorm.memnorm segs mem2)).
Proof. exact (aj_snprintf_at_xromR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
End l.
End snp.

(* ---------------------------------------------------------------------------- *)
(* 3. The text at ARx holds at ARx /\ P for any P on (ly, S): the call keeps ly and S (YGcallMx.v:571-612's shape).  *)
Section cj. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variables rlo rhi : Z.
Variable P : alayout -> astate -> Prop.
Local Abbreviation ARP := (fun ly S Hp W mem md => ARx ly S Hp W mem md /\ P ly S).

Lemma asnprintf_realizes_xrom_conj : forall FF K gc gv img_lo img_hi cr pc,
asnprintf_realizes_xrom segs B ARx rlo rhi FF K gc gv img_lo img_hi cr pc ->
asnprintf_realizes_xrom segs B ARP rlo rhi FF K gc gv img_lo img_hi cr pc.
Proof.
intros FF K gc gv img_lo img_hi cr pc AS ly S Hp W regs mem md d n f xs ws T cval [[HAR HPl] Hrest]. intros.
eapply SRr_mono; [apply (AS ly S Hp W regs mem md d n f xs ws T cval (conj HAR Hrest)); assumption |].
cbv beta. intros W' c' _ (-> & fx' & regs' & mem' & md' & Hc & Hf1 & Hf2 & HAR' & Hrest').
split; [reflexivity|]. exists fx', regs', mem', md'. split; [exact Hc|]. split; [exact Hf1|]. split; [exact Hf2|].
split; [split; [exact HAR' | exact HPl] | exact Hrest'].
Qed.
End cj.
