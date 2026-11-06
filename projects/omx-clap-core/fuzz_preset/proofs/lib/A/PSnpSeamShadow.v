(* Step 2 of the evt -> SRr seam at musl vfprintf: the ASAN SHADOW.

   The harness states ASan facts over its reader `aview tfibsegs H mem` (YG0n.v:18):
   `range_addressable rd SHADOW_OFF p n` (YG0v.v:33) asks, for each byte x of [p, p + n), a shadow byte
   s at `shadow_of_addr SHADOW_OFF x = SHADOW_OFF + x / 8` with `saddr_ok x s` (YG0v.v:29), and
   `amem_range p n` (YG0d.v:317) puts the range in low or high application memory.
   GXA states them over the CJ store (lib/CJ/RL/GXA/AsanFacts.v): `addr_byte`, `addressable`,
   `pf_rng`, `shadow_rw`, with the shadow byte at `a / 8 + ASAN_K` read SIGNED (`shadow_ok`).

   The two readers are the same function (FMgxaSeamBase.aview_mrd), the two shadow maps are the same
   map (ASAN_K = SHADOW_OFF), and a shadow byte the harness accepts is below 8, where the signed and
   unsigned readings agree (byte_signed_small).  So each harness fact becomes the GXA fact over
   `cjstore H mem` with no new premise, except pf_rng: GXA reads up to 7 bytes past each byte of the
   range (`app_mem (p + i + 7)`) and the byte just past it (`end_in_app`), which `amem_range p (n + 8)`
   gives.

   The musl prefix (GXA's musl_prefix_addressable, AsanFacts.v:82): the nine image bytes at
   `sym 0x1029e` = 0x10b74 (RT_IImgA.v:36) lie in fm.asan's first zero-shadow range
   (0x10000, 0x20f40 - 0x10000) (AF0m.v:551), which AR's am_zshadow (YG0n.v:218) covers whenever that
   range is in `as_zero_shadow B` (TfibSyms' ts_zsh gives it).  musl_prefix_of_AR states it for AR;
   musl_prefix_of_ARU states it for ARU (lib/A/FMupoison.v:32), the form the shared contract's
   ecall_preU carries: a user-poisoned shadow byte is the shadow of a live block's granule, and no
   live block meets the image (AR_client_img_law, YG0d.v:490). *)
(* Modified by Theorem Labs, 2026-10: c-libc-stdio's copy for fuzz_preset image A (L3-V2, the GXA seam over ARx, helper H2; parent c-libc-stdio 15:0xZ, split scratch/vfp/SEAM-SPLIT.txt) of proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxaSeamShadow.v at origin/cold/port-fm-rtprintf-param 3e35620c52e: module paths fuzz_manifest -> fuzz_preset; the image record RT_IImgA.A_img -> preset's rebuilt-pin lib/CJ/RL/I/IImgA.v N_img_asan (c-libc-str f697dea427f); lib/A/FMupoison -> removed (its aview_vis_byte, FMupoison.v:71, copied here). R7 / R9 numerals (preset A, d83eb25d, literals proved by vm_compute or from Tfib_zero_shadow): the first segment [0x10000, 0x31000) (fm [0x10000, 0x30000)); GXA's musl prefix @sym N_img_asan 0x1029e = 0x10b74 (fm 0x10b4c); the first zero-shadow range (0x10000, 0x20f40 - 0x10000), A/AF0m.v Tfib_zero_shadow's head (IMG_LO, 0x20f40 - IMG_LO) with IMG_LO = 0x10000 (fm (0x10000, 0x20d00 - 0x10000)). R4 / R5 / R8: Section Sh takes ARx and alx_zshadow; prefix_ra_of_AR -> prefix_ra_of_ARx and musl_prefix_of_AR / musl_prefix_of_ARU -> musl_prefix_of_ARx, over ARx at Hp, from alx_zshadow (the U case and its al_client_img premise vanish with unpoison). Runtime-option cells (c-omx-hpreset 15:22Z): this file holds no walk and reads no option cell. The sentences above name fm's files. *)
(* Modified by Theorem Labs, 2026-10: moved to the #102 pins, image A' (fuzz_preset.asan 1be0f53d, unstripped bff8519b), from the old-pin donor origin/cold/c-libc-stdio-presetsnp-vfp ac1750cac8be: every code numeral by symbol + offset by c-asan's alreloc of record (frame/alreloc.py.frozen-c4338d099cfb8025, --src omx-clap-core/fuzz_preset --src-pin d83eb25d --assume-source; the chain's code is equal old -> #102); kept as written: the IImg record keys (fm addresses), the instruction words and the segment sizes; audited by port_addr_check 0767e70e074a (only the record keys flag). Per-numeral table: c-libc-stdio scratch/p102/reloc/A/PSnpSeamShadow.v.reloc.tsv. Comment numerals are as written (sentences above that name preset A's addresses describe the old pin). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YG0q YA0n YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA Require AsanFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.I Require Import IImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PSnpSeamBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqG.
Import ListNotations.
Local Open Scope Z_scope.

(* preset A's first segment is [0x10000, 0x31000) *)
Lemma in_img_seg0 : forall a, 0x10000 <= a < 0x31000 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img.
assert (P : nth_error (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs) 0
            = Some (65536, 135168)) by (vm_compute; reflexivity).
destruct tfibsegs as [|s1 rest]; [discriminate|].
cbn [map nth_error] in P. injection P as P1 P2.
exists s1. split; [left; reflexivity|]. lia.
Qed.

(* GXA's musl prefix symbol on preset A *)
Lemma sym_musl_prefix : @sym N_img_asan 0x1029e = 0x10b74.
Proof. vm_compute. reflexivity. Qed.

Section Sh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Hypothesis alx_zshadow : YCbqG.ARx_zshadow_law tfibsegs B ARx.

(* ---- one shadow byte ---- *)
Lemma byte_signed_small : forall b : byte, bv_unsigned b < 8 -> bv_signed b = bv_unsigned b.
Proof.
intros b Hb. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
unfold bv_signed, bv_swrap, bv_wrap.
change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256.
Z.div_mod_to_equations. lia.
Qed.

Lemma shadow_ok_of_saddr_ok : forall (b : byte) a,
  saddr_ok a (bv_unsigned b) -> @AsanFacts.shadow_ok a (bv_signed b).
Proof.
intros b a Hs. assert (H8 : bv_unsigned b < 8) by (destruct Hs as [H0|[_ H1]]; lia).
rewrite (byte_signed_small b H8). unfold AsanFacts.shadow_ok.
destruct Hs as [H0|[H1 H2]]; [left; exact H0 | right; lia].
Qed.

(* ---- application memory ---- *)
Lemma app_mem_of_amem_range : forall p n a,
  amem_range p n -> 0 <= p -> p <= a -> a < p + n -> @AsanFacts.app_mem a.
Proof.
intros p n a Hr Hp Hpa Ha. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hr.
unfold AsanFacts.app_mem, AsanFacts.LOWMEM_END, AsanFacts.HIGHMEM_BEG, AsanFacts.APPMEM_END. lia.
Qed.

(* ---- addressable bytes and ranges ---- *)
Lemma addr_byte_of_view : forall H mem a,
  0 <= a -> @AsanFacts.app_mem a ->
  (exists s, aview tfibsegs H mem (shadow_of_addr SHADOW_OFF a) = Some s /\ saddr_ok a s) ->
  @AsanFacts.addr_byte N_img_asan (cjstore H mem) a.
Proof.
intros H mem a _ Happ (s & Hs & Hok).
split; [exact Happ|].
assert (Hsa : shadow_of_addr SHADOW_OFF a = AsanFacts.shadow_addr a)
  by (unfold shadow_of_addr, SHADOW_OFF, AsanFacts.shadow_addr, AsanFacts.ASAN_K; lia).
rewrite Hsa, aview_mrd in Hs.
match type of Hs with option_map _ ?X = _ => destruct X as [b|] eqn:Eb end; cbn in Hs; [|discriminate].
injection Hs as <-.
exists b. split; [exact Eb | exact (shadow_ok_of_saddr_ok b a Hok)].
Qed.

Lemma addressable_of_view : forall H mem p n,
  0 <= p -> 0 <= n -> amem_range p n ->
  range_addressable (aview tfibsegs H mem) SHADOW_OFF p n ->
  @AsanFacts.addressable N_img_asan (cjstore H mem) p n.
Proof.
intros H mem p n Hp Hn Hr HRA.
split; [exact Hp|]. split; [exact Hn|]. split.
- unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hr. unfold AsanFacts.APPMEM_END. lia.
- intros i Hi. apply addr_byte_of_view; [lia | | apply HRA; lia].
  exact (app_mem_of_amem_range p n (p + i) Hr Hp ltac:(lia) ltac:(lia)).
Qed.

Lemma pf_rng_of_view : forall H mem p n,
  0 <= p -> 0 <= n -> n <= 2 ^ 40 -> amem_range p (n + 8) ->
  range_addressable (aview tfibsegs H mem) SHADOW_OFF p n ->
  @AsanFacts.pf_rng N_img_asan (cjstore H mem) p n.
Proof.
intros H mem p n Hp Hn Hn40 Hr HRA.
assert (Hr0 : amem_range p n) by (unfold amem_range in *; lia).
unfold AsanFacts.pf_rng, AsanFacts.end_in_app.
split; [exact Hn40|]. split; [exact (addressable_of_view H mem p n Hp Hn Hr0 HRA)|]. split.
- right. exact (app_mem_of_amem_range p (n + 8) (p + n) Hr Hp ltac:(lia) ltac:(lia)).
- intros i Hi. exact (app_mem_of_amem_range p (n + 8) (p + i + 7) Hr Hp ltac:(lia) ltac:(lia)).
Qed.

(* ---- the shadow is mapped, writable and readable ---- *)
(* fm's lib/A/FMupoison.v:71 aview_vis_byte (FMupoison is not ported, R3), copied over its segs argument *)
Lemma aview_vis_byte : forall segs H (m : word -> option byte) a b, H (Z_to_bv 64 a) = false -> m (Z_to_bv 64 a) = Some b ->
  aview segs H m a = Some (bv_unsigned b).
Proof. intros segs H m a b E M. unfold aview, mbyte, mrestrict. rewrite E, M. reflexivity. Qed.

Lemma shadow_rw_of_view : forall H mem,
  (forall a, @AsanFacts.in_shadow a -> apresent H mem a) ->
  @AsanFacts.shadow_rw N_img_asan (cjstore H mem).
Proof.
intros H mem HP a Ha. destruct (HP a Ha) as (Hh & b & Hb).
pose proof (aview_vis_byte tfibsegs H mem a b Hh Hb) as Hv.
pose proof (mrd_of_view H mem a (bv_unsigned b) Hv) as Hm. rewrite byte_roundtrip in Hm.
assert (E : cjstore H mem (Mem.wa a) = Some b).
{ unfold cjstore, mrestrict, Mem.wa. rewrite Hh. exact Hb. }
split; [|exists b; exact Hm].
unfold wview. rewrite E. discriminate.
Qed.

(* ---- GXA's musl prefix ---- *)
(* the nine bytes at sym 0x1029e are addressable once their shadow reads as the harness accepts *)
Lemma musl_prefix_of_ra : forall H mem,
  range_addressable (aview tfibsegs H mem) SHADOW_OFF 0x10b74 9 ->
  @AsanFacts.musl_prefix_addressable N_img_asan (cjstore H mem).
Proof.
intros H mem HRA. unfold AsanFacts.musl_prefix_addressable. rewrite sym_musl_prefix.
apply pf_rng_of_view; [lia | lia | lia | | exact HRA].
unfold amem_range, kLowMemEnd. lia.
Qed.

(* the one fact about B the prefix needs: preset A's first zero-shadow range is B's *)
Lemma zsh_rodata_of_tfib : TfibSyms B -> In (0x10000, 0x20f60 - 0x10000) (as_zero_shadow B).
Proof. intros HB. rewrite (ts_zsh B HB). unfold Tfib_zero_shadow, YImgTop.IMG_LO. apply in_eq. Qed.

Lemma prefix_ra_of_ARx : forall ly S Hp W mem md,
  In (0x10000, 0x20f60 - 0x10000) (as_zero_shadow B) -> ARx ly S Hp W mem md ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF 0x10b74 9.
Proof.
intros ly S Hp W mem md HIn HAR.
pose proof (alx_zshadow ly S Hp W mem md (0x10000, 0x20f60 - 0x10000) HAR
  ltac:(unfold zero_shadow_ranges; right; exact HIn)) as HZ0.
cbn [fst snd] in HZ0.
apply (range_addressable_sub _ _ 0x10000 (0x20f60 - 0x10000)); [| lia | lia].
apply zero_shadow_range; [reflexivity | reflexivity | exact HZ0].
Qed.

(* fm's musl_prefix_of_AR and musl_prefix_of_ARU are one lemma over ARx: ARx holds of mem itself (no unpoison), so
   fm's ARU detour (al_client_img: a user-poisoned shadow byte is a live block's) has no counterpart *)
Lemma musl_prefix_of_ARx : forall ly S Hp W mem md,
  In (0x10000, 0x20f60 - 0x10000) (as_zero_shadow B) -> ARx ly S Hp W mem md ->
  @AsanFacts.musl_prefix_addressable N_img_asan (cjstore (w_H W) mem).
Proof.
intros ly S Hp W mem md HIn HAR. apply musl_prefix_of_ra.
exact (prefix_ra_of_ARx ly S Hp W mem md HIn HAR).
Qed.

End Sh.
