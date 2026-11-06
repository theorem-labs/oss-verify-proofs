(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8c.v:168-170
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC85.v:371-373 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8a.v:360-365 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:341-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/put_dec.v, with its module paths and module names changed; 726 of its 801 lines of code are new or changed and 3265 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import McConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YO0f.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model.
Import ListNotations.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC4b YC85 YC88 DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JsonScalarBase JsonScalarStr JsonScalarLit JsonScalarNum1 JsonScalarNum2 JsonScalarNumEnt.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import StrlenDef MemchrDef.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
Section h.
Variable B : asyms.
Hypothesis GLOBS : globs_marked SEGS B disco_globs.
Hypothesis IMGV : img_shadow_vis SEGS B.
Hypothesis ROU : disco_ro_unowned B.
Definition TJSON_SCALAR_STK : Z := 128 + 2 * ESTACK.
Definition tjson_scalar_str (W : world SEGS) (mem : word -> option byte) (a : Z) (s : list Z) : Prop :=
  Forall (fun c => 0 < c < 256) s /\
  garr8 SEGS (mrestrict (w_H W) mem) a (s ++ [0]) /\
  0 < a /\ a + Z.of_nat (length s) + 1 <= 2 ^ 63 /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\
  amem_range a (Z.of_nat (length s) + 1) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a (Z.of_nat (length s) + 1) /\
  shadow_hull_vis (aview SEGS (w_H W) mem) a (Z.of_nat (length s) + 1) /\
  (forall x, a + Z.of_nat (length s) < x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
     aview SEGS (w_H W) mem x <> None) /\
  (forall x, a <= x < a + Z.of_nat (length s) + 1 -> in_img SEGS x).
Definition tjson_scalar_img (W : world SEGS) (mem : word -> option byte) : Prop :=
  exists t1 t2 t3 : Z,
  VAL (A_OBJ 20) mod 8 = 0 /\ (forall x, VAL (A_OBJ 20) <= x < VAL (A_OBJ 20) + 24 -> in_img SEGS x) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 20)) 24 /\
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 20)) 8 t1 /\
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 20) + 8) 8 t2 /\
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 20) + 16) 8 t3 /\
  tjson_scalar_str W mem t1 [116; 114; 117; 101] /\
  tjson_scalar_str W mem t2 [102; 97; 108; 115; 101] /\
  tjson_scalar_str W mem t3 [110; 117; 108; 108] /\
  tjson_scalar_str W mem (VAL (A_OBJ 19)) [34; 92; 47; 98; 102; 110; 114; 116; 117].
Definition tjson_rom_bytes (a : Z) (l : list Z) : Prop :=
  forall k, (k < length l)%nat -> seg_rom SEGS (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (nth k l 0)).
Definition tjson_rom_word (a w : Z) : Prop :=
  forall k, (k < 8)%nat -> seg_rom SEGS (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte w 8 k)).
Definition tjson_scalar_rostr (a : Z) (s : list Z) : Prop :=
  Forall (fun c => 0 < c < 256) s /\
  In (a, Z.of_nat (length s) + 1) disco_globs /\
  (forall x, a <= x < a + Z.of_nat (length s) + 1 -> in_img SEGS x /\ in_roP SEGS pa_relro_lo pa_relro_hi x) /\
  tjson_rom_bytes a (s ++ [0]) /\
  (forall x, a + Z.of_nat (length s) < x < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
     seg_rom SEGS (Z_to_bv 64 x) <> None).
Definition tjson_scalar_roimg : Prop :=
  exists t1 t2 t3 : Z,
  In (VAL (A_OBJ 20), 24) disco_globs /\ VAL (A_OBJ 20) mod 8 = 0 /\
  (forall x, VAL (A_OBJ 20) <= x < VAL (A_OBJ 20) + 24 -> in_img SEGS x /\ in_roP SEGS pa_relro_lo pa_relro_hi x) /\
  tjson_rom_word (VAL (A_OBJ 20)) t1 /\ tjson_rom_word (VAL (A_OBJ 20) + 8) t2 /\ tjson_rom_word (VAL (A_OBJ 20) + 16) t3 /\
  tjson_scalar_rostr t1 [116; 114; 117; 101] /\
  tjson_scalar_rostr t2 [102; 97; 108; 115; 101] /\
  tjson_scalar_rostr t3 [110; 117; 108; 108] /\
  tjson_scalar_rostr (VAL (A_OBJ 19)) [34; 92; 47; 98; 102; 110; 114; 116; 117].
Definition tjson_scalar_kept (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (W2 : world SEGS) (mem2 : word -> option byte) (sp v : Z) (E : Z -> Prop) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp - TJSON_SCALAR_STK <= a < sp) -> ~ E a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
     aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - TJSON_SCALAR_STK <= a < sp) -> apresent (w_H W) memc a ->
     apresent (w_H W2) mem2 a) /\
  (forall a, sp - TJSON_SCALAR_STK <= a < sp -> apresent (w_H W2) mem2 a).
Definition tjson_scalar_post (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (b i v : Z) (BS : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
    match jscalar (map bv_unsigned BS) i with
    | Some (e, kd, s, l) =>
        getr regs2 10 = w64 e /\
        val_mem SEGS (mrestrict (w_H W2) mem2) v 8 (b + s) /\
        val_mem SEGS (mrestrict (w_H W2) mem2) (v + 8) 8 l /\
        val_mem SEGS (mrestrict (w_H W2) mem2) (v + 16) 4 kd /\
        tjson_scalar_kept lyc Sc W memc W2 mem2 (spZ regs) v (fun a => v <= a < v + 20)
    | None =>
        getr regs2 10 = w64 0 /\
        tjson_scalar_kept lyc Sc W memc W2 mem2 (spZ regs) v (fun _ => False)
    end.
Definition tjson_scalar_spec : Prop :=
  forall (fq : YK11.FPState) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (b i n v : Z) (BS : list byte) ch,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W memc ->
  tjson_scalar_roimg ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 b -> getr regs 11 = w64 i -> getr regs 12 = w64 n -> getr regs 13 = w64 v ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z (regupd regs 8 (Z_to_bv 64 0))) ch ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TJSON_SCALAR_STK -> spZ regs <= sp0 ->
  0 <= i < 2 ^ 64 -> Z.of_nat (length BS) = n -> b + n <= 2 ^ 64 ->
  (i < n ->
     garr8 SEGS (mrestrict (w_H W) memc) b (map bv_unsigned BS) /\
     0 < b /\ b + n <= 2 ^ 63 /\ amem_range b n /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF b n /\
     shadow_hull_vis (aview SEGS (w_H W) memc) b n /\
     (b + n <= spZ regs - TJSON_SCALAR_STK \/ spZ regs <= b) /\ off_img b n /\ (b + n <= v \/ v + 20 <= b)) ->
  0 < v -> v mod 8 = 0 -> v + 20 <= 2 ^ 63 -> amem_range v 20 ->
  (spZ regs <= v \/ v + 20 <= spZ regs - TJSON_SCALAR_STK) ->
  off_img v 20 ->
  (forall a, v <= a < v + 20 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
     apresent (w_H W) memc a) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF v 20 ->
  shadow_hull_vis (aview SEGS (w_H W) memc) v 20 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_json_scalar) regs memc mdc)
    (tjson_scalar_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b i v BS).
Local Set Default Proof Using "All".
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ASTRLEN : forall fq : YK11.FPState,
  astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (@pa_sigma _ disco_listing PI DS___interceptor_trampoline_strlen).
Hypothesis AMEMCHR : forall fq : YK11.FPState,
  amemchr_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (@pa_sigma _ disco_listing PI DS___interceptor_trampoline_memchr).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (@pa_sigma _ disco_listing PI DS___interceptor_trampoline_bcmp).
Section J.
Context {fq : YK11.FPState} {STK sp0 : Z} {FP : list (Z * Z)} {ly : alayout} {S : astate} {W0 : world SEGS}
  {mem0 : word -> option byte} {md0 : Model} {own : list (Z * Z)} {lyc : alayout} {Sc : astate} {W : world SEGS}
  {memc : word -> option byte} {k : Z} {regs0 : bvmap 5 word} {b i n v : Z} {BS : list byte} {mdc : Model}.
Context `{JHI : @JH rc SK PI B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs0 b i n v BS mdc}.
Let HJ0 : ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k := jh_HJ0.
Let Hvimg : off_img v 20 := jh_Hvimg.
Let Hsp16 : spZ regs0 mod 16 = 0 := jh_Hsp16.
Let HspSTK : sp0 - STK <= spZ regs0 - TJSON_SCALAR_STK := jh_HspSTK.
Let Hsp0 : spZ regs0 <= sp0 := jh_Hsp0.
Let Hv0 : 0 < v := jh_Hv0.
Let Hv8 : v mod 8 = 0 := jh_Hv8.
Let Hv63 : v + 20 <= 2 ^ 63 := jh_Hv63.
Let Hvw : spZ regs0 <= v \/ v + 20 <= spZ regs0 - TJSON_SCALAR_STK := jh_Hvw.
Let Hra : YK0s.ret_ok (getr regs0 1) := jh_Hra.
Let RUN := paj_run (fx := fq) B LAWS.
Let RUNTO := paj_run_to (fx := fq) B LAWS.
Let BR := paj_branch (fx := fq) (PI := PI).
Let HLn : Z.of_nat (length BS) = n := jh_HLn.
Let HBS : garr8 SEGS (mrestrict (w_H W) memc) b BZ := jh_HBS.
Let Hb0 : 0 < b := jh_Hb0.
Let Hbam : amem_range b n := jh_Hbam.
Let Hbw : b + n <= spZ regs0 - TJSON_SCALAR_STK \/ spZ regs0 <= b := jh_Hbw.
Let Hvam : amem_range v 20 := jh_Hvam.
Let Hvra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF v 20 := jh_Hvra.
Let Hvaw : forall a, v <= a < v + 20 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
  apresent (w_H W) memc a := jh_Hvaw.
Let Hbv : b + n <= v \/ v + 20 <= b := jh_Hbv.
Let Hbra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF b n := jh_Hbra.
Hypothesis Htimg : tjson_scalar_img W memc.
Hypothesis Hcv : consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W memc.
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Htp : getr regs0 4 = w64 (as_tp B).
Hypothesis Hboff : off_img b n.
Let HBgot := pal_got_shadow B TL.
Let HBcell := pal_cell B TL.
Let JQ := tjson_scalar_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs0 b i v BS.
Let RET := paj_ret_at (fx := fq) (PL := PL_disco) (PI := PI).
Let HTSK : TJSON_SCALAR_STK = 128 + 2 * ESTACK := eq_refl.
Lemma jkept : forall M2 (Ez : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs0 - TJSON_SCALAR_STK <= a < spZ regs0) -> ~ Ez a ->
     aview SEGS (w_H W) M2 a = aview SEGS (w_H W) memc a) ->
  (forall a, in_img SEGS a -> ~ Ez a) ->
  JPRES M2 -> (forall a, spZ regs0 - TJSON_SCALAR_STK <= a < spZ regs0 -> apresent (w_H W) M2 a) ->
  tjson_scalar_kept lyc Sc W memc W M2 (spZ regs0) v Ez.
Proof.
intros M2 Ez HK Himg HPR Hwin.
pose proof jwin_lo as Hlo. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ0) as HAR0.
assert (Hsp64 : spZ regs0 < 2 ^ 64) by (unfold spZ; pose proof (bv_unsigned_in_range 64 (getr regs0 2)) as Hr;
  change (bv_modulus 64) with (2 ^ 64) in Hr; lia).
unfold tjson_scalar_kept. split; [exact HK|]. split.
{ intros p m t Hin Ht HE. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc p m HAR0 Hin) as (_ & H4096 & Hc & _).
  apply HK; [lia | lia | exact HE]. }
split.
{ intros a Hi _ _. pose proof (pa_segs_low a Hi) as Ha. apply HK; [lia | lia | exact (Himg a Hi)]. }
split.
{ intros cid pos a Hin Hz HE. destruct (frames_bounds _ _ LAWS lyc Sc W memc mdc cid pos HAR0 Hin) as (H1 & H2 & _).
  unfold in_zr, frame_rng, shadow_addr, SHADOW_OFF in Hz. cbn [fst snd] in Hz.
  pose proof (fs_frame_bytes_nonneg cid). apply HK; [ | | exact HE]; Z.div_mod_to_equations; lia. }
split; [intros a _ _ Ha; exact (HPR a Ha) | exact Hwin].
Qed.
Lemma js_epi : JEPI_K JQ.
Proof.
unfold JEPI_K. intros R M md r HJ H2 H3 H4 H10 Hr HSL HPR HRES.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
assert (Usp : bv_unsigned (getr R 2) = spZ regs0 - 128) by (rewrite H2; unfold w64; rewrite unsigned_lit_small; lia).
set (E := Eimg (Ereg R JX)).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (E2 : ew E 2 = getr R 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat R JX 2 2%bv eq_refl)).
assert (HS : st_ok_pi SEGS VAL E (mkSS JS_EPI sr_atoms [jframe] None jG_epi)
  (restrict (w_H W) (mkst R (Z_to_bv 64 (BASE + JS_EPI)) M (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. apply jframe_ok.
    + rewrite E2. exact Usp.
    + intros t Ht. subst E. apply jE_extra. exact Ht.
    + exact HSL.
    + intros a Ha. apply Hpres. lia.
    + lia.
    + lia.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [jG_epi f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, Usp. unfold JSP_LO, JSP_HI. change (2 ^ 4) with 16.
    assert (Hsp'16 : (spZ regs0 - 128) mod 16 = 0) by (rewrite Zminus_mod, Hsp16; reflexivity).
    repeat split; try lia; exact Hsp'16. }
assert (SHOK : sh_ok SEGS (SOff 9 0) [] E (mrestrict (w_H W) M)) by apply Forall_nil.
paj_run_tok RUN HS HJ SHOK JBspan.
- cbn [ss_mem]. eapply (awr_ok_cons_stack_off E jframe [] STK sp0 FP _ _ lyc own 2%nat (spZ regs0 - 128 - sp0));
  [reflexivity | rewrite E2, Usp; lia | cbn; lia | cbn; lia | apply awr_ok_nil].
- eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat2.
  assert (EX : forall t, (t < 13)%nat -> ew E (32 + t) = getr regs0 (Z_to_bv 5 (snd (nth t JSAVED (0, 0)))))
    by (intros t Ht; subst E; apply jE_extra; exact Ht).
  assert (E3 : ew E 3 = getr R 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat R JX 3 3%bv eq_refl)).
  assert (E4 : ew E 4 = getr R 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat R JX 4 4%bv eq_refl)).
  assert (E10 : ew E 10 = getr R 10) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat R JX 10 10%bv eq_refl)).
  pose proof (EX 0%nat ltac:(lia)) as X0. pose proof (EX 1%nat ltac:(lia)) as X1. pose proof (EX 2%nat ltac:(lia)) as X2.
  pose proof (EX 3%nat ltac:(lia)) as X3. pose proof (EX 4%nat ltac:(lia)) as X4. pose proof (EX 5%nat ltac:(lia)) as X5.
  pose proof (EX 6%nat ltac:(lia)) as X6. pose proof (EX 7%nat ltac:(lia)) as X7. pose proof (EX 8%nat ltac:(lia)) as X8.
  pose proof (EX 9%nat ltac:(lia)) as X9. pose proof (EX 10%nat ltac:(lia)) as X10. pose proof (EX 11%nat ltac:(lia)) as X11.
  pose proof (EX 12%nat ltac:(lia)) as X12.
  unfold JSAVED in X0, X1, X2, X3, X4, X5, X6, X7, X8, X9, X10, X11, X12.
  cbn [Nat.add nth snd] in X0, X1, X2, X3, X4, X5, X6, X7, X8, X9, X10, X11, X12.
  prreg HS (Z_to_bv 5 1) Q1. prreg HS (Z_to_bv 5 10) Q10.
  assert (Hpc : v_jalr (getr (ms_regs ms) 1) 0 = getr regs0 1).
  { change (getr (ms_regs ms) 1) with (getr (ms_regs ms) (Z_to_bv 5 1)). rewrite Q1, X0. exact Hra. }
  assert (HKF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs0 - 128 <= a < spZ regs0) ->
    aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) M a).
  { intros a Ha Hn. apply (aview_eq_of SEGS). apply HFr. rewrite unsigned_lit_small by lia.
    intros (rg & Hin & Hrg). cbn [ss_mem In] in Hin. destruct Hin as [<-|[]].
    cbn [jframe YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg. rewrite E2, Usp in Hrg. lia. }
  assert (HPR2 : JPRES (ms_mem ms)) by (intros a Ha; apply (apresent_grows _ _ _ _ HG); apply HPR; exact Ha).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  assert (Hwin2 : forall a, spZ regs0 - TJSON_SCALAR_STK <= a < spZ regs0 -> apresent (w_H W) (ms_mem ms) a)
    by (intros a Ha; apply Hpres2; lia).
  assert (Himg : forall a, in_img SEGS a -> ~ (v <= a < v + 20)).
  { intros a Ha. pose proof (pa_img_range a Ha). unfold off_img in Hvimg. lia. }
  rewrite Hpc. unfold JQ, tjson_scalar_post.
  do 5 eexists. split; [reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
  split.
  { intros rr Hrr. unfold acallee_saved in Hrr.
    assert (C : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/
      rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    repeat (destruct C as [-> | C]; [
      lazymatch goal with |- getr _ (Z_to_bv 5 ?q) = _ =>
        let Hq := fresh "Hq" in prreg HS (Z_to_bv 5 q) Hq; rewrite Hq end;
      rewrite ?E2, ?Usp, ?E3, ?E4, ?H3, ?H4, ?X1, ?X2, ?X3, ?X4, ?X5, ?X6, ?X7, ?X8, ?X9, ?X10, ?X11, ?X12;
      try reflexivity;
      replace (spZ regs0 - 128 + 128) with (spZ regs0) by lia; unfold spZ; rewrite Z_to_bv_bv_unsigned; reflexivity |]).
    subst rr. prreg HS (Z_to_bv 5 27) Hq. rewrite Hq, X12. reflexivity. }
  split; [reflexivity|]. split; [reflexivity|].
  unfold JRES in HRES. destruct (jscalar (map bv_unsigned BS) i) as [[[[e kd] s] l]|] eqn:Hjs.
  + destruct HRES as (-> & Hv1 & Hv2 & Hv3 & HKV).
    split; [change (getr (ms_regs ms) 10) with (getr (ms_regs ms) (Z_to_bv 5 10)); rewrite Q10, E10, H10; reflexivity|].
    split; [apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) M); [intros x Hx; apply HKF; lia | exact Hv1]|].
    split; [apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) M); [intros x Hx; apply HKF; lia | exact Hv2]|].
    split; [apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) M); [intros x Hx; apply HKF; lia | exact Hv3]|].
    apply jkept; [ | exact Himg | exact HPR2 | exact Hwin2].
    intros a Ha Hw Hv. rewrite HKF by lia. apply HKV; assumption.
  + destruct HRES as (-> & HK).
    split; [change (getr (ms_regs ms) 10) with (getr (ms_regs ms) (Z_to_bv 5 10)); rewrite Q10, E10, H10; reflexivity|].
    apply jkept; [ | intros a _ []; exact I | exact HPR2 | exact Hwin2].
    intros a Ha Hw _. rewrite HKF by lia. apply HK; assumption.
Qed.
Definition jent_x : list word := map (Z_to_bv 64) [SHADOW_OFF; b + i; jbyte BZ i].
Definition jbreg : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition jent_rs : smem := [stack_region 128; got_regionP; bcell_regionP 32; jbreg].
Definition jent_G : facts := mkFacts [(2%nat, mkAF (JSP_LO + 128) (JSP_HI + 128) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
  (33%nat, mkAF 1 (0x7fffffffffff - 1) 0); (34%nat, mkAF 0 255 0)] [] [(SAlu ALU_ADD (SOff 10 0) (SOff 11 0), SOff 33 0)].
Lemma jent_low : forall (q : nat) (r : bv 5), (q < 32)%nat -> Z.of_nat q = bv_unsigned r ->
  ew (Eimg (Ereg regs0 jent_x)) q = getr regs0 r.
Proof. intros q r Hq Hr. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr. Qed.
Definition jwin_ok0 (r : YP09.region) : bool :=
  (YP09.r_whi r <=? YP09.r_wlo r) ||
  (match YP09.r_base r with Some 2%nat => true | _ => false end && (-128 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 0)).
Lemma jwin_ent : forall Eh rs, forallb jwin_ok0 rs = true -> bv_unsigned (ew Eh 2) = spZ regs0 ->
  forall a, in_wrange Eh rs a -> spZ regs0 - TJSON_SCALAR_STK <= a < spZ regs0.
Proof.
intros Eh rs Hok H2 a (r & Hin & Ha). rewrite forallb_forall in Hok. specialize (Hok r Hin).
unfold jwin_ok0 in Hok. assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
destruct (YP09.r_whi r <=? YP09.r_wlo r) eqn:Hw; [apply Z.leb_le in Hw; lia|]. cbn [orb] in Hok.
destruct (YP09.r_base r) as [[|[|[|nb]]]|]; cbn in Hok; try discriminate.
apply andb_prop in Hok as [H0 H1]. apply Z.leb_le in H0, H1. cbn [base_val] in Ha. rewrite H2 in Ha. lia.
Qed.
Lemma jawr_ent : forall Eh rs, forallb jwin_ok0 rs = true -> bv_unsigned (ew Eh 2) = spZ regs0 ->
  awr_ok Eh rs STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own.
Proof. intros Eh rs Hok H2 a Ha. pose proof (jwin_ent Eh rs Hok H2 a Ha). left. lia. Qed.
Lemma jkeep_ent : forall Eh rs M M', forallb jwin_ok0 rs = true -> bv_unsigned (ew Eh 2) = spZ regs0 ->
  frame_of Eh rs (mrestrict (w_H W) M) (mrestrict (w_H W) M') -> JKEEP M -> JKEEP M'.
Proof. intros Eh rs M M' Hok H2 HF HK. exact (jkeep_of Eh rs M M' HF (jwin_ent Eh rs Hok H2) HK). Qed.
Lemma jobl_ent : forall Eh (M : word -> option byte), JKEEP M ->
  bv_unsigned (ew Eh 32) = SHADOW_OFF -> bv_unsigned (ew Eh 33) = b + i -> 0 <= i < n ->
  range_addressable (rd_of SEGS (mrestrict (w_H W) M)) (U Eh (SOff 32 0)) (U Eh (SOff 33 0)) 1.
Proof.
intros Eh M HK H32 H33 Hin. pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite !U_SOff, H32, H33, !zcanon_id by (unfold M64, SHADOW_OFF; lia). rewrite !Z.add_0_r.
change (rd_of SEGS (mrestrict (w_H W) M)) with (aview SEGS (w_H W) M).
apply (range_addressable_kept_win (aview SEGS (w_H W) memc) (aview SEGS (w_H W) M) (spZ regs0 - TJSON_SCALAR_STK) (spZ regs0));
  [intros s Hs Hn; apply HK; assumption | lia | lia | lia |].
apply (range_addressable_sub _ _ b n); [exact Hbra | lia | lia].
Qed.
Lemma jslots_ent : forall Eh ss ms cs,
  st_ok_pi SEGS VAL Eh ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 2%nat) (-128) 0 (-128) 0 cs) ->
  (forall t, (t < 13)%nat ->
     In (YP09.mkChunk (fst (nth t JSAVED (0, 0)) - 128) (CVal 8 (SOff (Z.to_nat (snd (nth t JSAVED (0, 0)))) 0))) cs) ->
  bv_unsigned (ew Eh 2) = spZ regs0 ->
  (forall t, (t < 13)%nat -> ew Eh (Z.to_nat (snd (nth t JSAVED (0, 0)))) = getr regs0 (Z_to_bv 5 (snd (nth t JSAVED (0, 0))))) ->
  JSLOTS (ms_mem ms).
Proof.
intros Eh ss ms cs HS Hn Hin H2 HX t Ht.
pose proof (st_ok_pi_region_nth Eh ss _ 0 _ HS Hn) as HR. cbn [ms_mem restrict] in HR.
pose proof (field_of_region Eh _ 2 _ cs (-128) 0 (-128) 0 _ 8 (SOff (Z.to_nat (snd (nth t JSAVED (0, 0)))) 0)
  (bv_unsigned (getr regs0 (Z_to_bv 5 (snd (nth t JSAVED (0, 0)))))) HR H2 (Hin t Ht)
  ltac:(cbn [sv_denot]; rewrite HX by exact Ht; rewrite Z.add_0_r; reflexivity)
  (bv_unsigned_in_range 64 _) ltac:(do 13 (destruct t as [|t]; [cbn; lia|]); lia)) as Hv.
replace (spZ regs0 + (fst (nth t JSAVED (0, 0)) - 128)) with (spZ regs0 - 128 + fst (nth t JSAVED (0, 0))) in Hv by lia.
exact Hv.
Qed.
Lemma jent_X : forall t, (t < 13)%nat ->
  ew (Eimg (Ereg regs0 jent_x)) (Z.to_nat (snd (nth t JSAVED (0, 0)))) = getr regs0 (Z_to_bv 5 (snd (nth t JSAVED (0, 0)))).
Proof. intros t Ht. apply jent_low; do 13 (destruct t as [|t]; [cbn; first [lia | reflexivity] |]); lia. Qed.
Lemma jsc_str : 0 <= i < n -> jbyte BZ i = 34 -> jscalar BZ i = jstr BZ i (i + 1) (length BZ).
Proof.
intros Hin H34. pose proof jlen_BZ as HL. unfold jscalar. rewrite HL, (proj2 (Z.leb_gt _ _)) by lia.
rewrite H34. reflexivity.
Qed.
Lemma jsc_str_short : 0 <= i < n -> jbyte BZ i = 34 -> n <= i + 1 -> jscalar BZ i = None.
Proof.
intros Hin H34 Hn. rewrite (jsc_str Hin H34). pose proof jlen_BZ as HL.
destruct (length BZ) as [|f]; [reflexivity|]. cbn [jstr]. rewrite HL, (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.
Let Hs13' : jsstr_ok W memc (VAL (A_OBJ 19)) [34; 92; 47; 98; 102; 110; 114; 116; 117].
Proof. destruct Htimg as (t1 & t2 & t3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.
Lemma jsh_addr : forall x y : word, bv_unsigned x = b + i -> bv_unsigned y = SHADOW_OFF -> 0 <= i < n ->
  alu64 ALU_ADD (alu64 ALU_SRL x (Z_to_bv 64 3)) y = w64 (SHADOW_OFF + (b + i) / 8).
Proof.
intros x y Hx Hy Hin. pose proof jb_hi as Hbhi. apply bv_eq.
rewrite !alu64_unsigned. cbn [zalu_raw]. rewrite Hx, Hy. rewrite (unsigned_lit_small 3) by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd : 0 <= (b + i) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (bv_wrap_small 64 ((b + i) / 8)) by (unfold bv_modulus; cbn [Z.of_N]; lia).
unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
rewrite Z.add_comm. apply bv_wrap_small. unfold bv_modulus, SHADOW_OFF. cbn [Z.of_N]. lia.
Qed.
Lemma js_entry : js_lit_spec -> forall Q, JEPI_K Q ->
  getr regs0 10 = w64 b -> getr regs0 11 = w64 i -> getr regs0 12 = w64 n -> getr regs0 13 = w64 v -> 0 <= i < n ->
  SRr SEGS W (mkCfg (mkst regs0 (Z_to_bv 64 (BASE + AF_json_scalar)) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros HLIT Q HQ H10 H11 H12 H13 Hin.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HJ0 as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as HcellR.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as HgotR.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR.
set (E := Eimg (Ereg regs0 jent_x)).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (E2 : ew E 2 = getr regs0 2) by (apply jent_low; [lia | reflexivity]).
assert (E10 : ew E 10 = getr regs0 10) by (apply jent_low; [lia | reflexivity]).
assert (E11 : ew E 11 = getr regs0 11) by (apply jent_low; [lia | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs0 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (b + i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs0 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (jbyte BZ i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs0 _ 2)).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E307 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0) by (rewrite E2; reflexivity).
assert (VB : forall nn vv, ew E nn = Z_to_bv 64 vv -> 0 <= vv < 2 ^ 64 -> base_val E (Some nn) = vv).
{ intros nn vv Hn Hv'. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv'. }
destruct (jbyte_mem memc i ltac:(intros a _ _; reflexivity) Hin) as [Hbi Hbir].
assert (U10 : bv_unsigned (ew E 10) = b) by (rewrite E10, H10; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = i) by (rewrite E11, H11; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = b + i) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS AF_json_scalar sr_atoms jent_rs None jent_G)
  (restrict (w_H W) (mkst regs0 (Z_to_bv 64 (BASE + AF_json_scalar)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold jent_rs, jbreg, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
      [cbn [sv_denot]; rewrite E307, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 66)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    + rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) E307) by (pose proof (pa_val_range (A_OBJ 66)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    + rewrite (VB 33%nat (b + i) E33) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      refine (chunk_ok_val SEGS E _ _ 0 1 (SOff 34 0) (jbyte BZ i) _ _ _ _);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r; rewrite unsigned_lit_small by lia; reflexivity
      | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia | rewrite Z.add_0_r; exact Hbi].
  - apply pairwise_disjoint_of_extents. unfold jent_rs, jbreg, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) E307) by (pose proof (pa_val_range (A_OBJ 66)); lia).
    rewrite (VB 33%nat (b + i) E33) by lia.
    cbn [base_val]. rewrite Usp. pose proof (pal_got_cell B TL) as HgcD. pose proof Hboff as Hbo.
    unfold off_img in Hbo. try (unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hbo).
    pose proof alloc_ceiling_val as Hcl.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; [exact I|]].
    + cbn [jent_G f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E32, E33, E34, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      unfold JSP_LO, JSP_HI. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SHADOW_OFF. repeat match goal with |- _ /\ _ => split end; try lia; exact Hsp16.
    + cbn [jent_G f_alias alias_ok]. split; [|exact I].
      apply (jalias_add _ _ _ _ _ _ _ _ _ U10 U11 U33). f_equal; lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H W) (ms_mem (mkst regs0 (Z_to_bv 64 (BASE + AF_json_scalar)) memc (seg_rom SEGS))))) by apply Forall_nil.
pose proof HJ0 as HJ.
assert (MEQ : JKEEP (ms_mem (mkst regs0 (Z_to_bv 64 (BASE + AF_json_scalar)) memc (seg_rom SEGS)))) by (intros a _ _; reflexivity).
assert (PRS : JPRES (ms_mem (mkst regs0 (Z_to_bv 64 (BASE + AF_json_scalar)) memc (seg_rom SEGS)))) by (intros a Ha; exact Ha).
assert (E3 : ew E 3 = getr regs0 3) by (apply jent_low; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs0 4) by (apply jent_low; [lia | reflexivity]).
assert (E12 : ew E 12 = getr regs0 12) by (apply jent_low; [lia | reflexivity]).
assert (E13 : ew E 13 = getr regs0 13) by (apply jent_low; [lia | reflexivity]).
assert (U12 : bv_unsigned (ew E 12) = n) by (rewrite E12, H12; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew E 13) = v) by (rewrite E13, H13; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U34 : bv_unsigned (ew E 34) = jbyte BZ i) by (rewrite E34; apply unsigned_lit_small; lia).
assert (EA19 : ew E (A_OBJ 19) = Z_to_bv 64 (VAL (A_OBJ 19))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
set (E0 := E) in *.
set (Ec0 := E0) in HS, SHOK, HEI.
assert (AG : forall kk, (kk < 512)%nat -> ew Ec0 kk = ew E0 kk) by (intros; reflexivity).
clearbody Ec0.
let rec go T :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ecur ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK JBspan T;
  [ lazymatch goal with
    | |- range_addressable _ (U _ (SOff 32 0)) (U _ (SOff 33 0)) 1 =>
      cbn [ms_mem mkst]; apply (jobl_ent _ _ MEQ); [rewrite AG by lia; exact U32 | rewrite AG by lia; exact U33 | lia]
    | |- awr_ok _ _ _ _ _ _ _ _ _ => apply jawr_ent; [vm_compute; reflexivity | rewrite AG by lia; exact Usp]
    end ..
  | jpost Ecur ]
  end
with jpost Ecur :=
  lazymatch goal with HFr : frame_of ?Eh ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), MEQ : JKEEP ?m1 |- _ =>
    let MEQ2 := fresh "MEQ" in
    pose proof (jkeep_ent Eh rs m1 m2 ltac:(vm_compute; reflexivity) ltac:(rewrite AG by lia; exact Usp) HFr MEQ) as MEQ2;
    clear MEQ; rename MEQ2 into MEQ
  end;
  lazymatch goal with HG : mem_grows (mrestrict _ ?m1) (mrestrict _ ?m2), PRS : JPRES ?m1 |- _ =>
    let PRS2 := fresh "PRS" in pose proof (jpres_of m1 m2 HG PRS) as PRS2; clear PRS; rename PRS2 into PRS
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ _ |- _ => jrebase En Ecur
  end;
  lazymatch goal with
  | HS : st_ok_pi _ _ _ ?ss _ |- _ =>
    let pc := eval vm_compute in (ss_pc ss) in
    lazymatch pc with
    | 12740 => jexit_epi
    | 12140 => jexit_str
    | 12564 => jexit_lit
    | 12044 => psrr_branch_tok RUN BR HS SHOK JBspan;
               [jconv Hc; first [exfalso; lia | go JS_EPI] | jconv Hc; first [exfalso; lia | go JS_LIT]]
    | 12104 => psrr_branch_tok RUN BR HS SHOK JBspan;
               [jconv Hc; first [exfalso; lia | go JS_LIT] | jconv Hc; first [exfalso; lia | go JS_STR]]
    | 12112 => psrr_branch_tok RUN BR HS SHOK JBspan;
               [jconv Hc; first [exfalso; lia | go JS_EPI] | jconv Hc; first [exfalso; lia | go JS_STR]]
    end
  end
with jrebase En Ecur :=
  tryif constr_eq En Ecur then idtac else
  (let E2 := fresh "Ec" in set (E2 := En) in *;
   let AG2 := fresh "AG" in
   assert (AG2 : forall kk, (kk < 512)%nat -> ew E2 kk = ew E0 kk)
     by (intros kk Hkk; subst E2; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; apply AG; exact Hkk);
   clear AG; rename AG2 into AG)
with jrgE HS :=
  lazymatch goal with |- getr _ ?r = _ =>
    let Q := fresh "Q" in prreg HS r Q; rewrite Q; clear Q; rewrite ?AG by lia;
    first [ reflexivity
          | rewrite ?E3, ?E4; reflexivity
          | rewrite ?E10, ?E12, ?E13, ?EA19; assumption
          | rewrite EA19; reflexivity
          | apply jsh_addr; [exact U33 | exact U32 | lia]
          | apply bv_eq; rewrite ?Usp, ?U10, ?U11, ?U12, ?U13, ?U32, ?U33, ?U34; unfold w64; rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia); lia
          | unfold w64; f_equal; rewrite ?Usp, ?U10, ?U11, ?U12, ?U13, ?U32, ?U33, ?U34; lia ]
  end
with jinv HS :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec _ (restrict _ ?msx) |- _ =>
  split; [exact HJ|]; split;
  [ apply (jslots_ent Ec _ msx _ HS eq_refl);
    [ let t := fresh in let Ht := fresh in intros t Ht; do 13 (destruct t as [|t]; [cbn; tauto|]); lia
    | rewrite AG by lia; exact Usp
    | let t := fresh in let Ht := fresh in intros t Ht; rewrite AG by (do 13 (destruct t as [|t]; [cbn; lia|]); lia); apply jent_X; exact Ht ]
  | split; [exact MEQ|]; split; [exact PRS|]; repeat split; jrgE HS ]
  end
with jexit_epi :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec _ (restrict _ ?msx) |- _ =>
  pmkst HS;
  apply (HQ (ms_regs msx) (ms_mem msx) _ 0 HJ);
  [ jrgE HS | jrgE HS | jrgE HS | jrgE HS | lia
  | apply (jslots_ent Ec _ msx _ HS eq_refl);
    [ let t := fresh in let Ht := fresh in intros t Ht; do 13 (destruct t as [|t]; [cbn; tauto|]); lia
    | rewrite AG by lia; exact Usp
    | let t := fresh in let Ht := fresh in intros t Ht; rewrite AG by (do 13 (destruct t as [|t]; [cbn; lia|]); lia); apply jent_X; exact Ht ]
  | exact PRS
  | unfold JRES; change (map bv_unsigned BS) with BZ; rewrite jsc_str_short by lia; split; [reflexivity | exact MEQ] ]
  end
with jexit_str :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec _ (restrict _ ?msx) |- _ =>
  pmkst HS;
  apply (str_loop AMEMCHR Hs13' Hcv Hgp Htp Q HQ (Z.to_nat (n - (i + 1))) (ms_regs msx) (ms_mem msx) _ (i + 1) (length BZ));
  [ lia | jinv HS | jrgE HS | jrgE HS | jrgE HS | jrgE HS | jrgE HS | jrgE HS | jrgE HS | jrgE HS | jrgE HS
  | lia | lia | pose proof jlen_BZ as HL; unfold jlen in HL; lia | apply jsc_str; [lia | assumption] ]
  end
with jexit_lit :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec _ (restrict _ ?msx) |- _ =>
  pmkst HS;
  apply (HLIT Q HQ (ms_regs msx) (ms_mem msx) _);
  [ jinv HS | jrgE HS | jrgE HS | jrgE HS | jrgE HS | lia | assumption ]
  end in
go JS_EPI.
Qed.
Lemma js_short : forall Q, JEPI_K Q -> forall nr,
  getr regs0 11 = w64 i -> getr regs0 12 = w64 nr -> 0 <= nr <= i -> i < 2 ^ 64 -> jscalar BZ i = None ->
  SRr SEGS W (mkCfg (mkst regs0 (Z_to_bv 64 (BASE + AF_json_scalar)) memc (seg_rom SEGS)) mdc) Q.
Proof.
intros Q HQ nr H11 H12 Hnr Hi64 Hnone.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HJ0 as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
assert (Hes : ESTACK = 4096) by reflexivity.
set (E := Eimg (Ereg regs0 jent_x)).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (E2 : ew E 2 = getr regs0 2) by (apply jent_low; [lia | reflexivity]).
assert (E3 : ew E 3 = getr regs0 3) by (apply jent_low; [lia | reflexivity]).
assert (E4 : ew E 4 = getr regs0 4) by (apply jent_low; [lia | reflexivity]).
assert (E11 : ew E 11 = getr regs0 11) by (apply jent_low; [lia | reflexivity]).
assert (E12 : ew E 12 = getr regs0 12) by (apply jent_low; [lia | reflexivity]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0) by (rewrite E2; reflexivity).
assert (U11 : bv_unsigned (ew E 11) = i) by (rewrite E11, H11; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E 12) = nr) by (rewrite E12, H12; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS AF_json_scalar sr_atoms [stack_region 128] None
  (mkFacts [(2%nat, mkAF (JSP_LO + 128) (JSP_HI + 128) 4)] [] []))
  (restrict (w_H W) (mkst regs0 (Z_to_bv 64 (BASE + AF_json_scalar)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. unfold JSP_LO, JSP_HI. change (2 ^ 4) with 16.
    split; [|exact I]. repeat split; try lia; exact Hsp16. }
assert (SHOK : sh_ok SEGS (SOff 9 0) [] E (mrestrict (w_H W) (ms_mem (mkst regs0 (Z_to_bv 64 (BASE + AF_json_scalar)) memc (seg_rom SEGS))))) by apply Forall_nil.
pose proof HJ0 as HJ.
assert (MEQ : JKEEP (ms_mem (mkst regs0 (Z_to_bv 64 (BASE + AF_json_scalar)) memc (seg_rom SEGS)))) by (intros a _ _; reflexivity).
assert (PRS : JPRES (ms_mem (mkst regs0 (Z_to_bv 64 (BASE + AF_json_scalar)) memc (seg_rom SEGS)))) by (intros a Ha; exact Ha).
set (E0 := E) in *.
set (Ec0 := E0) in HS, SHOK, HEI.
assert (AG : forall kk, (kk < 512)%nat -> ew Ec0 kk = ew E0 kk) by (intros; reflexivity).
clearbody Ec0.
let rec go T :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ecur ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK JBspan T;
  [ lazymatch goal with
    | |- awr_ok _ _ _ _ _ _ _ _ _ => apply jawr_ent; [vm_compute; reflexivity | rewrite AG by lia; exact Usp]
    end ..
  | jpost Ecur ]
  end
with jpost Ecur :=
  lazymatch goal with HFr : frame_of ?Eh ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), MEQ : JKEEP ?m1 |- _ =>
    let MEQ2 := fresh "MEQ" in
    pose proof (jkeep_ent Eh rs m1 m2 ltac:(vm_compute; reflexivity) ltac:(rewrite AG by lia; exact Usp) HFr MEQ) as MEQ2;
    clear MEQ; rename MEQ2 into MEQ
  end;
  lazymatch goal with HG : mem_grows (mrestrict _ ?m1) (mrestrict _ ?m2), PRS : JPRES ?m1 |- _ =>
    let PRS2 := fresh "PRS" in pose proof (jpres_of m1 m2 HG PRS) as PRS2; clear PRS; rename PRS2 into PRS
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ _ |- _ => jrebase En Ecur
  end;
  lazymatch goal with
  | HS : st_ok_pi _ _ _ ?ss _ |- _ =>
    let pc := eval vm_compute in (ss_pc ss) in
    lazymatch pc with
    | 12740 => jexit_epi
    | 12044 => psrr_branch_tok RUN BR HS SHOK JBspan;
               [jconv Hc; first [exfalso; lia | go JS_EPI] | jconv Hc; first [exfalso; lia | go JS_EPI]]
    end
  end
with jrebase En Ecur :=
  tryif constr_eq En Ecur then idtac else
  (let E2 := fresh "Ec" in set (E2 := En) in *;
   let AG2 := fresh "AG" in
   assert (AG2 : forall kk, (kk < 512)%nat -> ew E2 kk = ew E0 kk)
     by (intros kk Hkk; subst E2; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; apply AG; exact Hkk);
   clear AG; rename AG2 into AG)
with jrgE HS :=
  lazymatch goal with |- getr _ ?r = _ =>
    let Q := fresh "Q" in prreg HS r Q; rewrite Q; clear Q; rewrite ?AG by lia;
    first [ reflexivity
          | rewrite ?E3, ?E4; reflexivity
          | apply bv_eq; rewrite ?Usp; unfold w64; rewrite unsigned_lit_small by lia; lia
          | unfold w64; f_equal; rewrite ?Usp; lia ]
  end
with jexit_epi :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec _ (restrict _ ?msx) |- _ =>
  pmkst HS;
  apply (HQ (ms_regs msx) (ms_mem msx) _ 0 HJ);
  [ jrgE HS | jrgE HS | jrgE HS | jrgE HS | lia
  | apply (jslots_ent Ec _ msx _ HS eq_refl);
    [ let t := fresh in let Ht := fresh in intros t Ht; do 13 (destruct t as [|t]; [cbn; tauto|]); lia
    | rewrite AG by lia; exact Usp
    | let t := fresh in let Ht := fresh in intros t Ht; rewrite AG by (do 13 (destruct t as [|t]; [cbn; lia|]); lia); apply jent_X; exact Ht ]
  | exact PRS
  | unfold JRES; change (map bv_unsigned BS) with BZ; rewrite Hnone; split; [reflexivity | exact MEQ] ]
  end in
go JS_EPI.
Qed.
End J.
Lemma disco_globs_bnd : forall q sz, In (q, sz) disco_globs -> 0x20000 <= q /\ q + sz <= 0xa0700 /\ 1 <= sz.
Proof.
intros q sz H. unfold disco_globs in H.
repeat (destruct H as [H|H]; [injection H as <- <-; lia|]). destruct H.
Qed.
Lemma tjson_ro_mbyte : forall (W : world SEGS) mem lo sz x (bt : byte),
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> ro_unowned B lo sz ->
  in_roP SEGS pa_relro_lo pa_relro_hi x -> lo <= x < lo + sz -> seg_rom SEGS (Z_to_bv 64 x) = Some bt ->
  mbyte SEGS (mrestrict (w_H W) mem) x = Some bt.
Proof.
intros W mem lo sz x bt HR HU Hro Hx Hs.
pose proof (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ lo sz x HR Hro HU Hx) as Hv. rewrite Hs in Hv.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict (w_H W) mem) x) as [b0|] eqn:E0; cbn in Hv; [|discriminate Hv].
injection Hv as Hv. f_equal. apply bv_eq. exact Hv.
Qed.
Lemma tjson_le_byte1 : forall c, 0 <= c < 256 -> YO0f.le_byte c 1 0 = c.
Proof.
intros c Hc. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small c 256) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma tjson_ro_unowned_of : forall q sz, In (q, sz) disco_globs -> ro_unowned B q sz.
Proof. intros q sz H. apply (disco_ro_unowned_at B q sz ROU). unfold disco_ro_ranges. apply in_or_app. left. exact H. Qed.
Section ro. Context {fx : YK11.FPState}.
Lemma tjson_str_of_ro : forall ly S (W : world SEGS) mem md a s,
  AR SEGS B ly S W mem md -> arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  tjson_scalar_rostr a s -> tjson_scalar_str W mem a s.
Proof.
intros ly S W mem md a s HAR HR (HF & HIn & HIR & HB & HT).
pose proof (disco_globs_bnd _ _ HIn) as (Q1 & Q2 & Q3).
pose proof (tjson_ro_unowned_of _ _ HIn) as HU.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hc : forall j, (j < length (s ++ [0%Z]))%nat -> 0 <= nth j (s ++ [0]) 0 < 256).
{ intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  destruct (Nat.lt_ge_cases j (length s)) as [Hl|Hl].
  - rewrite app_nth1 by exact Hl. pose proof (proj1 (Forall_forall _ _) HF (nth j s 0) (nth_In s 0 Hl)) as Hq. cbv beta in Hq. lia.
  - rewrite app_nth2 by exact Hl. replace (j - length s)%nat with 0%nat by lia. cbn. lia. }
split; [exact HF|]. split.
{ intros j Hj. split; [|exact (Hc j Hj)]. intros k0 Hk. assert (k0 = 0%nat) as -> by lia.
  cbn [Z.of_nat]. rewrite Z.add_0_r.
  rewrite length_app in Hj. cbn [length] in Hj.
  apply (tjson_ro_mbyte W mem a (Z.of_nat (length s) + 1)); [exact HR | exact HU | apply HIR; lia | lia |].
  rewrite (HB j) by (rewrite length_app; cbn [length]; lia).
  rewrite (tjson_le_byte1 (nth j (s ++ [0]) 0)) by (apply Hc; rewrite length_app; cbn [length]; lia). reflexivity. }
split; [lia|]. split; [lia|]. split; [lia|].
split; [unfold amem_range; left; lia|].
split; [apply (ro_usable_glob SEGS B disco_globs ly S W mem md a (Z.of_nat (length s) + 1) a (Z.of_nat (length s) + 1) GLOBS HIn HAR); lia|].
split; [apply (ro_hull SEGS B ly S W mem md a (Z.of_nat (length s) + 1) IMGV HAR); unfold YImgTop.IMG_LO, YImgTop.IMG_TOP; lia|].
split.
- intros x Hx. unfold aview, mbyte. destruct (mrestrict (w_H W) mem (Z_to_bv 64 x)); [discriminate|].
  destruct (seg_rom SEGS (Z_to_bv 64 x)) eqn:E0; [discriminate|]. exfalso. exact (HT x Hx E0).
- intros x Hx. exact (proj1 (HIR x Hx)).
Qed.
Lemma tjson_img_of_ro : forall ly S (W : world SEGS) mem md,
  AR SEGS B ly S W mem md -> arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  tjson_scalar_roimg -> tjson_scalar_img W mem.
Proof.
intros ly S W mem md HAR HR (t1 & t2 & t3 & HIn & H8 & HIR & W1 & W2 & W3 & S1 & S2 & S3 & S4).
pose proof (disco_globs_bnd _ _ HIn) as (Q1 & Q2 & Q3).
pose proof (tjson_ro_unowned_of _ _ HIn) as HU.
assert (VW : forall o t, 0 <= o -> o + 8 <= 24 -> tjson_rom_word (VAL (A_OBJ 20) + o) t ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 20) + o) 8 t).
{ intros o t Ho Ho8 Hw k0 Hk. apply (tjson_ro_mbyte W mem (VAL (A_OBJ 20)) 24); [exact HR | exact HU | apply HIR; lia | lia | exact (Hw k0 Hk)]. }
exists t1, t2, t3. split; [exact H8|]. split; [intros x Hx; exact (proj1 (HIR x Hx))|].
split; [apply (ro_usable_glob SEGS B disco_globs ly S W mem md (VAL (A_OBJ 20)) 24 (VAL (A_OBJ 20)) 24 GLOBS HIn HAR); lia|].
split; [rewrite <- (Z.add_0_r (VAL (A_OBJ 20))) at 1; apply VW; [lia | lia | rewrite Z.add_0_r; exact W1]|].
split; [apply VW; [lia | lia | exact W2]|]. split; [apply VW; [lia | lia | exact W3]|].
split; [exact (tjson_str_of_ro ly S W mem md _ _ HAR HR S1)|].
split; [exact (tjson_str_of_ro ly S W mem md _ _ HAR HR S2)|].
split; [exact (tjson_str_of_ro ly S W mem md _ _ HAR HR S3)|].
exact (tjson_str_of_ro ly S W mem md _ _ HAR HR S4).
Qed.
End ro.
Lemma jpost_none : forall fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b1 b2 i v BS1 BS2 W2 c2,
  jscalar (map bv_unsigned BS1) i = None -> jscalar (map bv_unsigned BS2) i = None ->
  tjson_scalar_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b1 i v BS1 W2 c2 ->
  tjson_scalar_post fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b2 i v BS2 W2 c2.
Proof.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b1 b2 i v BS1 BS2 W2 c2 H1 H2
  (ly2 & S2 & regs2 & mem2 & md2 & Hc & HJ & HP & HF & HB & HM).
exists ly2, S2, regs2, mem2, md2. rewrite H1 in HM. rewrite H2. tauto.
Qed.
Theorem pb_json_scalar : tjson_scalar_spec.
Proof.
unfold tjson_scalar_spec.
intros fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b i n v BS ch
  HJ0 Haro Hcv Hroimg Hra Hra4 Hgp Htp H10 H11 H12 H13 Hch Hsp16 HspSTK Hsp0 Hi HLn Hbn Hbf
  Hv0 Hv8 Hv63 Hvam Hvw Hvimg Hvaw Hvra Hvhull.
pose proof (tjson_img_of_ro (fx := fq) lyc Sc W memc mdc (proj1 HJ0) Haro Hroimg) as Himg.
unfold cfg_at. change (w64 (BASE + AF_json_scalar)) with (Z_to_bv 64 (BASE + AF_json_scalar)).
destruct (Z_lt_ge_dec i n) as [Hin | Hin].
- destruct (Hbf Hin) as (HBS & Hb0 & Hb63 & Hbam & Hbra & Hbhull & Hbw & Hboff & Hbv).
  assert (JHI : @JH _ _ _ B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b i n v BS mdc)
    by (constructor; assumption).
  pose proof Himg as (t1 & t2 & t3 & HL8 & HLimg & HLra & HLv1 & HLv2 & HLv3 & HS1 & HS2 & HS3 & HS13).
  pose proof (js_C_store (JHI := JHI)) as CST.
  pose proof (js_L_d3 (JHI := JHI) CST) as LD3.
  pose proof (js_C_exp (JHI := JHI) LD3 CST) as CEX.
  pose proof (js_L_d2 (JHI := JHI) CEX CST) as LD2.
  pose proof (js_C_frac (JHI := JHI) LD2 CEX) as CFR.
  pose proof (js_L_d1 (JHI := JHI) CFR CST) as LD1.
  pose proof (js_nument (JHI := JHI) LD1 CFR) as NUM.
  pose proof (js_lit ASTRLEN ABCMP (JHI := JHI) HL8 HLimg HLra HLv1 HLv2 HLv3 HS1 HS2 HS3 Hcv Hgp Htp Hboff Hbhull NUM) as LIT.
  exact (js_entry (JHI := JHI) Himg Hcv Hgp Htp Hboff LIT _ (js_epi (JHI := JHI) Himg Hcv Hgp Htp Hboff) H10 H11 H12 H13 ltac:(lia)).
- assert (JHIf : @JH _ _ _ B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs v i 0 v [] mdc).
  { pose proof Hvam as Hva. unfold amem_range in Hva.
    constructor; try assumption.
    - reflexivity.
    - intros t Ht. cbn in Ht. lia.
    - unfold amem_range. lia.
    - unfold TJSON_SCALAR_STK in *. lia.
    - lia.
    - apply range_addressable_nil. lia. }
  assert (Hboff : off_img v 0) by (unfold off_img in *; lia).
  assert (Hnr : jscalar (map bv_unsigned BS) i = None).
  { unfold jscalar, jlen. rewrite length_map, HLn, (proj2 (Z.leb_le n i)) by lia. reflexivity. }
  assert (Hnf : jscalar (map bv_unsigned (@nil byte)) i = None).
  { unfold jscalar. replace (jlen (map bv_unsigned (@nil byte))) with 0 by reflexivity.
    rewrite (proj2 (Z.leb_le 0 i)) by lia. reflexivity. }
  eapply SRr_mono.
  { exact (js_short (JHI := JHIf) Himg Hcv Hgp Htp Hboff _ (js_epi (JHI := JHIf) Himg Hcv Hgp Htp Hboff) n H11 H12
      ltac:(lia) ltac:(lia) Hnf). }
  intros W2 c2 _ HP. exact (jpost_none fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs v b i v [] BS W2 c2 Hnf Hnr HP).
Qed.
End h.
End f.
End d.
