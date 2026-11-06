(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the two CHECKS of YGcallSnp.v's snprintf row asnprintf_realizes_xrom. Image-free: no address,
   no image class instance.

   (a) asnprintf_cf_of_xrom: at ARx := ARcf segs B the text IMPLIES port-fm's cf twin sh_asnprintf_realizes_cf
       (FMsnprintfSharedCf.v:32-67, blob 878a56df57de, by path from origin/cold/port-fm-rtprintf-param 0ddf65fd8cc),
       at every format family, window, canary cells, image range, read-only ranges and pc, GIVEN THE READ-ONLY BRIDGE
       snp_ro_bridge rlo rhi. h-mani-a8's field aa_snprintf_cf (YGcfNames.v:443 / :469 at a8439a761af0) at preset's
       instance pa_snprintf_cf (CfApiPreset.v:90-93 there) states the earlier twin (blob d9695b89e004), whose
       destination premise is amem_range8 d w; amem8_of_amem_range8 (FMsnprintfSharedCf.v:71) turns that premise into
       this twin's amem_range d (w + 8). Direction: text -> twin only. Two things differ, in the twin's favour or the
       text's:
       - the read-only premise: the text asks arodata_okP segs rlo rhi B (aview ..), the twin gives rom_view. The
         implication needs rom_view -> arodata_okP (snp_ro_bridge, with ARcf at hand), the CONVERSE of the bridge
         c-libc-stdio delivers (arodata_okP + const cells -> rom_view, which serves proving the text from a rom_view
         chain, not this check). rom_view covers the non-writable segments only, so it gives arodata_okP on them
         and says nothing of [rlo, rhi): snp_ro_bridge_nil proves the bridge when rhi <= rlo, and
         asnprintf_cf_of_xrom_nil is check (a) with no hypothesis at an empty relro range. For a non-empty relro range
         the bridge is an image fact ARcf does not carry (the relro bytes off the owned statics and errno read as the
         image's): OWED by the text's instance owner, or the twin restated in the _xro form;
       - the post's memnorm keep, which the twin does not state (forgotten).
       Every other premise, the destination's amem_range d (w + 8) included, and the rest of the post are the same
       terms.
   (b) The stand-in h-hpreset-7 uses today, PRW_S7bKit.asnprintf_esc_realizes_x (origin/cold/h-hpreset-7-walk-S7B
       7ffbb0405d3, PRW_S7bKit.v:58-100), copied VERBATIM below as snp_esc_realizes_x with the one image name
       STK_RT_PRINTF (PRH_Base.v:165, = 4 * ESTACK) made the parameter Kp: at Kp := STK_RT_PRINTF the copy and the
       stand-in are the same term (`reflexivity`, scratch build against 7ffbb0405d3's file, 2026-10-29). The stand-in
       does NOT follow from the text:
       - its post keeps the WHOLE float state (c' = cfg_at .. at the caller's fx); the text's post (the shared top's)
         gives some fx' that keeps every f register but f10, and frm = 0;
       - it lacks premises the text needs (the list in snp_esc_realizes_xrom's comment; the read-only one is the text's
         arodata_okP).
       snp_esc_realizes_xrom is the stand-in with exactly those changes plus the text's memnorm keep as the last post
       conjunct, and snp_esc_of_xrom proves it from the text at
       FF_esc lo hi, which is a8's FF_preset (CfSnprintfPreset.v:33-41, blob 29945739be86) with its two image bounds
       (cf_img_lo, cf_got_stack_chk_guard) made the parameters lo, hi: FF_preset = FF_esc (@cf_img_lo CfImg_A)
       (@cf_got_stack_chk_guard CfImg_A) by `reflexivity` (scratch build at a8439a761af0, 2026-10-29). The consumers
       re-point to snp_esc_realizes_xrom and discharge it with one citation of snp_esc_of_xrom (side conditions K <= Kp
       and ESTACK <= Kp; snp_K_A = 8160 by `reflexivity` at a8439a761af0, STK_RT_PRINTF = 16384).

   Numerals: 92 37 99 117 48 52 120 (WORD: the format bytes, PRW_S7bKit.v:59-60); 8 (LENGTH: the escape buffer size,
   and the canary cell width); 16 (LENGTH: the destination 8 plus the text's 8-byte slack; the hex base); 10, 11, 12,
   13 (registers, WORD); 2 (DERIVED: printf_common's runs), 256, 2 ^ 31, 2 ^ 32, 2 ^ 47, 2 ^ 63, 2 ^ 64 (WORD / LENGTH
   ranges); 3 4 5 6 7 (registers a3..a7, WORD); 5 and 7 (the frm field, WORD). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YP03 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
FMsnprintfPf FMsnprintfShared FMsnprintfSharedCf YGcallSnp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0s YO0f YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetRodata.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------------- *)
(* (a) At ARcf the text implies port-fm's cf twin.                                 *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable segs : list Segment.
Variable B : asyms.

(* THE READ-ONLY BRIDGE check (a) needs: from the twin's rom_view to the text's arodata_okP, at an ARcf state *)
Definition snp_ro_bridge (rlo rhi : Z) : Prop :=
  forall ly S Hp W mem md, ARcf segs B ly S Hp W mem md -> rom_view segs W mem ->
  arodata_okP segs rlo rhi B (aview segs (w_H W) mem).

(* at an empty relro range rom_view gives arodata_okP outright (in_roP's segment disjunct is in_rom) *)
Lemma snp_ro_bridge_nil : forall rlo rhi, rhi <= rlo -> snp_ro_bridge rlo rhi.
Proof.
intros rlo rhi Hr ly S Hp W mem md _ Hrom a [Hseg | Hrel] _ _; [exact (Hrom a Hseg) | lia].
Qed.

Lemma asnprintf_cf_of_xrom : forall rlo rhi FF K gc gv img_lo img_hi cr pc,
snp_ro_bridge rlo rhi ->
asnprintf_realizes_xrom segs B (ARcf segs B) rlo rhi FF K gc gv img_lo img_hi cr pc ->
sh_asnprintf_realizes_cf segs B FF K gc gv img_lo img_hi cr pc.
Proof.
intros rlo rhi FF K gc gv img_lo img_hi cr pc BR AS ly S Hp W regs mem md d n f xs ws T cval
HPRE Hlo Hpres Ha0 Ha1 Ha2 Hcv Hcrb Hcrd Hgc Hgv Hgc0 Hgc8 Hgv0 Hgv8 Hgcd Hgvd Hva Hxs Hxsd HFF Hn HT Hd0 Hdw Hpw
Hdest Hamr Hrad Hhull Himg Hfrm Hrom.
eapply SRr_mono.
{ exact (AS ly S Hp W regs mem md d n f xs ws T cval HPRE Hlo Hpres Ha0 Ha1 Ha2 Hcv Hcrb Hcrd Hgc Hgv Hgc0 Hgc8 Hgv0 Hgv8
  Hgcd Hgvd Hva Hxs Hxsd HFF Hn HT Hd0 Hdw Hpw Hdest Hamr Hrad Hhull Himg Hfrm
  (BR ly S Hp W mem md (proj1 HPRE) Hrom)). }
cbv beta. intros W' c' _ (-> & fx' & regs' & mem' & md' & Hc & Hf1 & Hf2 & HAR' & HP & Hsame & Hres & Hbytes & Hfr & Hpres' & _).
split; [reflexivity|]. exists fx', regs', mem', md'.
exact (conj Hc (conj Hf1 (conj Hf2 (conj HAR' (conj HP (conj Hsame (conj Hres (conj Hbytes (conj Hfr Hpres'))))))))).
Qed.

(* check (a) with no hypothesis, at an empty relro range *)
Lemma asnprintf_cf_of_xrom_nil : forall rlo rhi FF K gc gv img_lo img_hi cr pc, rhi <= rlo ->
asnprintf_realizes_xrom segs B (ARcf segs B) rlo rhi FF K gc gv img_lo img_hi cr pc ->
sh_asnprintf_realizes_cf segs B FF K gc gv img_lo img_hi cr pc.
Proof.
intros rlo rhi FF K gc gv img_lo img_hi cr pc Hr. apply asnprintf_cf_of_xrom. exact (snp_ro_bridge_nil rlo rhi Hr).
Qed.
End a.

(* ---------------------------------------------------------------------------- *)
(* (b) h-hpreset-7's stand-in, and what the text gives in its place.               *)
(* a8's FF_preset (CfSnprintfPreset.v:33-41) with its image bounds as parameters *)
Definition pf_esc_piece (p : pf_piece) : Prop :=
  match p with PLit _ | Pc | Px04 => True | _ => False end.
Definition FF_esc (lo hi : Z) : fmt_fam := fun rd rs f ws T =>
  exists (fmt : list Z) (ps : list pf_piece) (args : list pf_arg),
    fmt_at rd rs f fmt /\ pf_parse fmt = Some ps /\ Forall pf_esc_piece ps /\ pf_args_asan rd rs ws args /\
    pf_text ps args = Some T /\ pf_prec_pos ps args /\
    lo <= f /\ f + Z.of_nat (length fmt) + 1 <= hi /\ fmt <> [].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* PRW_S7bKit.v:59-77, verbatim (names prefixed snp_) *)
Definition snp_esc_fmt_c : list Z := [92; 37; 99].
Definition snp_esc_fmt_x : list Z := [92; 117; 37; 48; 52; 120].
Definition snp_esc_render (fmt : list Z) (c : Z) : list Z :=
  if list_eq_dec Z.eq_dec fmt snp_esc_fmt_c then [92; c]
  else [92; 117; 48; 48; WriterSpec.hexd (c / 16); WriterSpec.hexd (c mod 16)].
Definition snp_printf_runs : nat := 2.
Definition snp_printf_common_ok (W : world segs) (mem : word -> option byte) (f : Z) (fmt : list Z) : Prop :=
  garr8 segs (rdW W mem) f (fmt ++ [0]) /\ 0 < f /\ f + Z.of_nat (length fmt) + 1 <= 2 ^ 63 /\
  amem_range f (Z.of_nat (length fmt) + 1) /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF f (Z.of_nat (length fmt) + 1) /\
  shadow_hull_vis (aview segs (w_H W) mem) f (Z.of_nat (length fmt) + 1).

(* PRW_S7bKit.v:79-100, verbatim but STK_RT_PRINTF -> Kp *)
Definition snp_esc_realizes_x (Kp gcan can pc : Z) : Prop :=
  forall ly S Hp W regs mem md d f fmt c,
  ecall_pre_x segs B ARx ly S Hp W regs mem md ->
  ly_stk_lo ly + Kp <= spZ regs ->
  (forall a, spZ regs - Kp <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 d -> getr regs 11 = w64 8 -> getr regs 12 = w64 f -> getr regs 13 = w64 c ->
  (fmt = snp_esc_fmt_c \/ fmt = snp_esc_fmt_x) -> 0 <= c < 256 ->
  (forall k, (k < snp_printf_runs)%nat -> snp_printf_common_ok W mem f fmt) ->
  (exists cval, val_mem segs (rdW W mem) gcan 8 can /\ val_mem segs (rdW W mem) can 8 cval) ->
  0 < d -> d + 8 <= 2 ^ 63 -> amem_range d 8 ->
  (forall a, d <= a < d + 8 -> writable_at segs (rdW W mem) a /\ ~ aowned B ly S a /\
     ~ (spZ regs - Kp <= a < spZ regs)) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF d 8 -> shadow_hull_vis (aview segs (w_H W) mem) d 8 ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at segs (raZ regs) regs' mem' md' /\
       ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 (Z.of_nat (length (snp_esc_render fmt c))) /\
       garr8 segs (rdW W mem') d (snp_esc_render fmt c ++ [0]) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + Z.of_nat (length (snp_esc_render fmt c)) + 1) ->
          ~ (spZ regs - Kp <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* THE STAND-IN AS THE TEXT GIVES IT: snp_esc_realizes_x with
   - the post's float state existential: fx' keeps every f register but f10 and frm = 0 (the text's post);
   - the post's memnorm keep (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem') as its last conjunct;
   - seventeen added premises, each one the text asks and the stand-in does not state:
     arodata_okP segs rlo rhi B (aview ..) (the text's read-only premise); consts_view of the read-only ranges cr,
     their bounds and their disjointness from the window and the 8-byte buffer; the canary cells' bounds
     (0 <= gcan, gcan + 8 <= 2 ^ 63, 0 <= can, can + 8 <= 2 ^ 63) and their disjointness from the window and the
     buffer; the format's disjointness from the window and the buffer and its image bounds lo <= f,
     f + |fmt| + 1 <= hi (FF_preset's); spZ regs <= 2 ^ 47 (the text's argument-slot bound at xs = []);
     amem_range d 16 (the text's amem_range d (w + 8), w <= 8); the buffer off the image range [img_lo, img_hi);
     rounding mode 0 at entry.
   Each window disjointness is stated against the stand-in's own window Kp and the whole buffer (d, 8). *)
Definition snp_esc_realizes_xrom (Kp rlo rhi lo hi gcan can img_lo img_hi : Z) (cr : list (Z * Z)) (pc : Z) : Prop :=
  forall ly S Hp W regs mem md d f fmt c,
  ecall_pre_x segs B ARx ly S Hp W regs mem md ->
  ly_stk_lo ly + Kp <= spZ regs ->
  (forall a, spZ regs - Kp <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 10 = w64 d -> getr regs 11 = w64 8 -> getr regs 12 = w64 f -> getr regs 13 = w64 c ->
  (fmt = snp_esc_fmt_c \/ fmt = snp_esc_fmt_x) -> 0 <= c < 256 ->
  (forall k, (k < snp_printf_runs)%nat -> snp_printf_common_ok W mem f fmt) ->
  (exists cval, val_mem segs (rdW W mem) gcan 8 can /\ val_mem segs (rdW W mem) can 8 cval) ->
  0 < d -> d + 8 <= 2 ^ 63 -> amem_range d 8 ->
  (forall a, d <= a < d + 8 -> writable_at segs (rdW W mem) a /\ ~ aowned B ly S a /\
     ~ (spZ regs - Kp <= a < spZ regs)) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF d 8 -> shadow_hull_vis (aview segs (w_H W) mem) d 8 ->
  (* the added premises *)
  arodata_okP segs rlo rhi B (aview segs (w_H W) mem) ->
  consts_view segs W mem cr -> Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) cr ->
  Forall (fun r => Forall (zdisjoint r) (snp_out Kp (spZ regs) d 8)) cr ->
  0 <= gcan -> gcan + 8 <= 2 ^ 63 -> 0 <= can -> can + 8 <= 2 ^ 63 ->
  Forall (zdisjoint (gcan, 8)) (snp_out Kp (spZ regs) d 8) ->
  Forall (zdisjoint (can, 8)) (snp_out Kp (spZ regs) d 8) ->
  Forall (zdisjoint (f, Z.of_nat (length fmt) + 1)) (snp_out Kp (spZ regs) d 8) ->
  lo <= f -> f + Z.of_nat (length fmt) + 1 <= hi ->
  spZ regs <= 2 ^ 47 ->
  amem_range d 16 ->
  zdisjoint (d, 8) (img_lo, img_hi - img_lo) ->
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  SRr segs W (cfg_at segs pc regs mem md)
    (fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
       c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
       (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
       Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
       ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
       getr regs' 10 = w64 (Z.of_nat (length (snp_esc_render fmt c))) /\
       garr8 segs (rdW W mem') d (snp_esc_render fmt c ++ [0]) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + Z.of_nat (length (snp_esc_render fmt c)) + 1) ->
          ~ (spZ regs - Kp <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
       (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
       (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')).

(* -- the byte facts the bridge needs -- *)
Lemma snp_rdword_of_val_mem : forall (H : word -> bool) mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> rdword (aview segs H mem) a = Some (v mod 2 ^ 64).
Proof.
intros H mem a v Hv. set (u := v mod 2 ^ 64).
assert (Hu : 0 <= u < 2 ^ 64) by (unfold u; apply Z.mod_pos_bound; lia).
assert (Bk : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (YG0f.le_byte u 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  unfold u, YO0f.le_byte, YG0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite !Z.mod_mod by lia. reflexivity. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
f_equal. apply YG0s.le_bytes8. exact Hu.
Qed.

Lemma snp_aview_of_garr8 : forall (H : word -> bool) mem p l j, garr8 segs (mrestrict H mem) p l -> (j < length l)%nat ->
  aview segs H mem (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H mem p l j Hg Hj. destruct (Hg j Hj) as [Hv Hr].
specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite !(Z.mod_small (nth j l 0) 256) by lia. reflexivity.
Qed.

Lemma snp_garr8_of_aview : forall (H : word -> bool) mem p l,
  (forall j, (j < length l)%nat -> aview segs H mem (p + Z.of_nat j) = Some (nth j l 0)) ->
  garr8 segs (mrestrict H mem) p l.
Proof.
intros H mem p l Hv j Hj. specialize (Hv j Hj). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (p + Z.of_nat j)) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in Hv. injection Hv as Hv.
assert (Hr : 0 <= nth j l 0 < 256).
{ rewrite <- Hv. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R. }
split; [|exact Hr].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, Eb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite !(Z.mod_small (nth j l 0) 256) by lia. exact Hv.
Qed.

(* -- the two formats: parse, pieces, text -- *)
Lemma snp_esc_text : forall fmt c, (fmt = snp_esc_fmt_c \/ fmt = snp_esc_fmt_x) -> 0 <= c < 256 ->
  exists ps, pf_parse fmt = Some ps /\ Forall pf_esc_piece ps /\ pf_text ps [AInt c] = Some (snp_esc_render fmt c) /\
  pf_prec_pos ps [AInt c].
Proof.
intros fmt c [-> | ->] Hc.
- exists [PLit 92; Pc]. split; [reflexivity|]. split; [repeat constructor|]. split; [|exact I].
  unfold snp_esc_render. destruct (list_eq_dec Z.eq_dec snp_esc_fmt_c snp_esc_fmt_c) as [_|Hn]; [|exfalso; exact (Hn eq_refl)].
  cbn [pf_text option_map]. rewrite Z.mod_small by lia. reflexivity.
- exists [PLit 92; PLit 117; Px04]. split; [reflexivity|]. split; [repeat constructor|]. split; [|exact I].
  unfold snp_esc_render. destruct (list_eq_dec Z.eq_dec snp_esc_fmt_x snp_esc_fmt_c) as [He|_]; [discriminate He|].
  cbn [pf_text option_map]. rewrite app_nil_r.
  change (pf_hex4 c) with (repeat 48 (4 - length (pf_hexs 8 (c mod 2 ^ 32) [])) ++ pf_hexs 8 (c mod 2 ^ 32) []).
  rewrite (Z.mod_small c (2 ^ 32)) by lia.
  destruct (Z_lt_le_dec c 16) as [Hlt|Hge].
  + assert (Eh : pf_hexs 8 c [] = [pf_hexd c]).
    { change (pf_hexs 8 c []) with (if c <? 16 then [pf_hexd c] else pf_hexs 7 (c / 16) [pf_hexd (c mod 16)]).
      rewrite (proj2 (Z.ltb_lt c 16) Hlt). reflexivity. }
    rewrite Eh, (Z.div_small c 16), (Z.mod_small c 16) by lia. reflexivity.
  + assert (H16 : c / 16 < 16) by (apply Z.div_lt_upper_bound; lia).
    assert (Eh : pf_hexs 8 c [] = [pf_hexd (c / 16); pf_hexd (c mod 16)]).
    { change (pf_hexs 8 c []) with (if c <? 16 then [pf_hexd c] else pf_hexs 7 (c / 16) [pf_hexd (c mod 16)]).
      rewrite (proj2 (Z.ltb_ge c 16) Hge).
      change (pf_hexs 7 (c / 16) [pf_hexd (c mod 16)]) with
        (if c / 16 <? 16 then [pf_hexd (c / 16); pf_hexd (c mod 16)]
         else pf_hexs 6 (c / 16 / 16) [pf_hexd (c / 16 mod 16); pf_hexd (c mod 16)]).
      rewrite (proj2 (Z.ltb_lt (c / 16) 16) H16). reflexivity. }
    rewrite Eh. reflexivity.
Qed.

(* -- windows and the buffer -- *)
Lemma snp_out_Forall : forall (P : Z * Z -> Prop) K sp d n, Forall P (snp_out K sp d n) <-> P (sp - K, K) /\ P (d, n).
Proof.
intros P K sp d n. unfold snp_out. split.
- intros H. split; [exact (Forall_inv H) | exact (Forall_inv (Forall_inv_tail H))].
- intros [H1 H2]. constructor; [exact H1 | constructor; [exact H2 | constructor]].
Qed.

Lemma snp_out_shrink : forall r K Kp sp d n, K <= Kp -> n <= 8 ->
  Forall (zdisjoint r) (snp_out Kp sp d 8) -> Forall (zdisjoint r) (snp_out K sp d n).
Proof.
intros r K Kp sp d n HK Hn H. apply snp_out_Forall in H as [H1 H2]. apply snp_out_Forall.
unfold zdisjoint in *. cbn [fst snd] in *. split; lia.
Qed.

(* the stand-in's buffer premise keeps all of (d, 8) out of its window (sp - Kp, Kp) *)
Lemma snp_buf_off_window : forall (P : Z -> Prop) sp Kp d, 0 < Kp ->
  (forall a, d <= a < d + 8 -> P a /\ ~ (sp - Kp <= a < sp)) -> d + 8 <= sp - Kp \/ sp <= d.
Proof.
intros P sp Kp d HK H. destruct (Z_lt_le_dec d sp) as [Hlt|Hge]; [left|right; exact Hge].
destruct (Z_le_gt_dec (d + 8) (sp - Kp)) as [Hle|Hgt]; [exact Hle|]. exfalso.
destruct (H (Z.max d (sp - Kp)) ltac:(lia)) as [_ Hn]. apply Hn. lia.
Qed.

(* (b) the bridge: the text at FF_esc gives the stand-in as the text states it *)
Lemma snp_esc_of_xrom : forall rlo rhi lo hi K Kp gcan can img_lo img_hi cr pc,
  K <= Kp -> ESTACK <= Kp ->
  asnprintf_realizes_xrom segs B ARx rlo rhi (FF_esc lo hi) K gcan can img_lo img_hi cr pc ->
  snp_esc_realizes_xrom Kp rlo rhi lo hi gcan can img_lo img_hi cr pc.
Proof.
intros rlo rhi lo hi K Kp gcan can img_lo img_hi cr pc HKK HEK AS ly S Hp W regs mem md d f fmt c
HPRE Hlo Hpres Ha0 Ha1 Ha2 Ha3 Hfmt Hc Hpco Hcan Hd0 Hd8 Hamr Hdest Hrad Hhull
Hrom Hcv Hcrb Hcrd Hgc0 Hgc8 Hcn0 Hcn8 Hgcd Hcnd Hfd Hlof Hfhi Hsp47 Ham16 Himg Hfrm.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct Hcan as (cval & Hv1 & Hv2).
destruct (Hpco 0%nat ltac:(unfold snp_printf_runs; lia)) as (Hgar & Hf0 & Hf63 & Hfam & Hfra & Hfhv).
destruct (snp_esc_text fmt c Hfmt Hc) as (ps & Hps & Hpk & Htext & Hpp).
assert (Hne : fmt <> []) by (destruct Hfmt as [-> | ->]; discriminate).
assert (HTl : (1 <= length (snp_esc_render fmt c) <= 6)%nat)
  by (unfold snp_esc_render; destruct (list_eq_dec Z.eq_dec fmt snp_esc_fmt_c); cbn [length]; lia).
set (T := snp_esc_render fmt c) in *.
assert (Hsb : sn_bytes (8 - 1) T = T ++ [0]).
{ unfold sn_bytes. rewrite firstn_all2; [reflexivity|]. change (Z.to_nat (8 - 1)) with 7%nat. lia. }
assert (Hsl : sn_len (8 - 1) T = Z.of_nat (length T) + 1).
{ unfold sn_len. rewrite Hsb, length_app. cbn [length]. lia. }
assert (Hbw := snp_buf_off_window (fun a => writable_at segs (rdW W mem) a /\ ~ aowned B ly S a) (spZ regs) Kp d
  ltac:(lia) (fun a Ha => conj (conj (proj1 (Hdest a Ha)) (proj1 (proj2 (Hdest a Ha)))) (proj2 (proj2 (Hdest a Ha))))).
assert (E3 : argZ regs 3 = c).
{ unfold argZ. assert (Er : getr regs (Z_to_bv 5 (10 + 3)) = getr regs 13) by (f_equal; apply bv_eq; reflexivity).
  rewrite Er, Ha3. unfold w64. apply unsigned_lit_small. lia. }
assert (Hgv : rdword (aview segs (w_H W) mem) gcan = Some can).
{ pose proof (snp_rdword_of_val_mem _ _ _ _ Hv1) as R. rewrite Z.mod_small in R by lia. exact R. }
assert (Hsh : forall r, Forall (zdisjoint r) (snp_out Kp (spZ regs) d 8) ->
  Forall (zdisjoint r) (snp_out K (spZ regs) d (sn_len (8 - 1) T))).
{ intros r Hr. apply (snp_out_shrink r K Kp); [exact HKK | rewrite Hsl; lia | exact Hr]. }
eapply SRr_mono.
{ apply (AS ly S Hp W regs mem md d 8 f [] (map (argZ regs) [3; 4; 5; 6; 7] ++ []) T (cval mod 2 ^ 64) HPRE).
  - (* the window K *) lia.
  - intros a Ha. apply Hpres. lia.
  - exact Ha0.
  - exact Ha1.
  - exact Ha2.
  - exact Hcv.
  - exact Hcrb.
  - eapply Forall_impl; [|exact Hcrd]. intros r Hr. exact (Hsh r Hr).
  - exact Hgv.
  - exact (snp_rdword_of_val_mem _ _ _ _ Hv2).
  - exact Hgc0.
  - exact Hgc8.
  - exact Hcn0.
  - exact Hcn8.
  - exact (Hsh _ Hgcd).
  - exact (Hsh _ Hcnd).
  - (* va_words at xs = [] *) split; [reflexivity|]. intros i Hi. cbn [length] in Hi. lia.
  - cbn [length Z.of_nat]. lia.
  - apply snp_out_Forall. unfold zdisjoint. cbn [fst snd length Z.of_nat]. rewrite Hsl. split; lia.
  - (* the format family *)
    exists fmt, ps, [AInt c].
    split.
    { split; [exact Hf0|]. split.
      { intros i Hi. pose proof (snp_aview_of_garr8 (w_H W) mem f (fmt ++ [0]) (Z.to_nat i) Hgar
          ltac:(rewrite length_app; cbn [length]; lia)) as R.
        rewrite Z2Nat.id in R by lia. exact R. }
      split; [exact (Hsh _ Hfd)|]. split; [exact Hfam|]. split; [exact Hfra | exact Hfhv]. }
    split; [exact Hps|]. split; [exact Hpk|].
    split.
    { cbn [map app pf_args_asan]. split; [|exact I]. cbn [pf_arg_asan]. rewrite E3. split; [lia | reflexivity]. }
    split; [exact Htext|]. split; [exact Hpp|]. split; [exact Hlof|]. split; [exact Hfhi | exact Hne].
  - lia.
  - lia.
  - exact Hd0.
  - rewrite Hsl. lia.
  - (* the destination misses the window K *)
    unfold snp_out. cbn [pairwise]. split; [|split; [constructor | exact I]].
    constructor; [|constructor]. unfold zdisjoint. cbn [fst snd]. rewrite Hsl. lia.
  - (* dest_ok *)
    intros a Ha. rewrite Hsl in Ha. destruct (Hdest a ltac:(lia)) as (Hw & Hno & Hn).
    split; [exact Hw|]. split; [exact Hno|]. intros Hin. apply Hn. lia.
  - unfold amem_range in *. rewrite Hsl. lia.
  - unfold range_addressable in *. intros x Hx. apply Hrad. rewrite Hsl in Hx. lia.
  - unfold shadow_hull_vis in *. intros s Hs. apply Hhull. rewrite Hsl in Hs. unfold shadow_addr in *.
    assert (D1 : (d + (Z.of_nat (length T) + 1) - 1) / 8 <= (d + 8 - 1) / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : (SHADOW_OFF + (d + (Z.of_nat (length T) + 1) - 1) / 8) / 8 <= (SHADOW_OFF + (d + 8 - 1) / 8) / 8)
      by (apply Z.div_le_mono; lia).
    lia.
  - unfold zdisjoint in *. cbn [fst snd] in *. rewrite Hsl. lia.
  - exact Hfrm.
  - exact Hrom. }
cbv beta. intros W' c' _
  (-> & fx' & regs' & mem' & md' & -> & Hf1 & Hf2 & HAR' & HP & Hsame & Hres & Hbytes & Hfr & Hpres' & Hmn).
split; [reflexivity|]. exists fx', regs', mem', md'.
split; [reflexivity|]. split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HAR'|]. split; [exact HP|].
split; [exact Hsame|]. split; [exact Hres|].
split.
{ apply snp_garr8_of_aview. intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  specialize (Hbytes (Z.of_nat j) ltac:(rewrite Hsl; lia)). rewrite Nat2Z.id, Hsb in Hbytes. exact Hbytes. }
split; [|split; [exact Hpres' | exact Hmn]].
intros a Ha Hna Hnk. apply Hfr; [exact Ha | rewrite Hsl; lia | lia].
Qed.
End b.
