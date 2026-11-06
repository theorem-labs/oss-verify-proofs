(* Non-vacuity controls for disco's shared printf route at disco's three conversions Pd, Px02, Pllu (G9 rows
   R9-A-RT_pf_ctl / R9-Y-RT_pf_ctl). Written for fuzz_disco (a Theorem Labs lane's ruling b, 16:26Z), not relocated: the twin of
   fm's lib/A/RT_pf_ctl.v (a working branch 0ddf65fd8cc), whose %c / %04x controls do not apply here
   (disco has neither conversion, and pf_disco_piece Pc / Px04 are False).
   The family these controls make non-vacuous is disco's FF_disco disco_fmt_lo disco_fmt_hi (lib/Rt/SnFF.v:236) at
   PK = pf_disco_piece, the format family of disco's snprintf instance lib/A/FMsnprintfDiscoR1.v / lib/B/FMsnprintfDiscoR1.v
   (rows R9-A-instance / R9-Y-instance).
   The three formats are disco's own call sites. Their bytes and .rodata addresses were read with pyelftools from the
   pinned fuzz_disco asan / asan-ubsan images (sha256 5e39150d... / cee6f04a...); they
   are the same in both images and equal rows 1-3 of provenance/evidence/g9-gxa/gates/call-sites.tsv:
   - Pd:   fuzz_disco.c:621 snprintf(width, 24, "%dx%d", e->decl_in, e->decl_out), 25 64 78 25 64 00 at 0x20fe0;
   - Px02: fuzz_disco.c:592 "%02x:%02x:%02x:%02x:%02x:%02x" (the six mac bytes), 29 bytes + NUL at 0x20f80;
   - Pllu: fuzz_disco.c:641 snprintf(age, 24, "%llu", age_ns / 1000000), 25 6c 6c 75 00 at 0x21040 (disco's own %llu
     site; reac_disco.c:415, provenance/evidence/g9-gxa/gates/call-sites.tsv row 12, is the other one). No format here is synthetic.
   Shape as fm's file: a witness memory ctl_rd that reads the format and its NUL, reads 0 (addressable) on the whole
   shadow band [SHADOW_OFF, kHighMemBeg) and nothing else; rs = []; parse lemmas; text lemmas; the memberships; the
   bites. fm's CTL_F = 65536 (0x10000) is NOT kept: it lies below disco_fmt_lo = 0x102e0, so FF_disco's range conjunct
   fails there. ctl_rd takes the format's address instead, and each control sits at its site's real address.
   For each format with its arguments (any 32-bit ints for %d / %02x, any word for %llu):
   (1) FF_disco lo hi at every range [lo, hi) that holds the format, and at disco_fmt_lo / disco_fmt_hi
       (lib/A/Rt/SnprintfConsts.v:11-12);
   (2) RT_pf_sh.FF_pcomK pf_disco_piece (printf_common's family at disco's pieces; lib/A/RT_pf_sh.v:266, row
       R9-A-RT_pf_sh-delta, a working branch e246dd3a70d, from fm 0ddf65fd8cc
       RT_pf_sh.v:263). Its f + |fmt| + 1 <= TFIB_IMG_END is at disco's TFIB_IMG_END = YImgTop.IMG_TOP = 0x5fe000
       (fm's file has 0x5f7000);
   (3) pf_family_ro pf_disco_piece lo hi, from (1) by SnFF.FF_disco_ro;
   (4) the bite: fm's narrower piece predicate pf_fm_piece refuses the format's parse (the shape of a Theorem Labs lane's probe
       site1_not_fm, not landed).
   Prior controls, cited, not Required (neither is on a branch this base can merge; both are at fm's widened
   predicates, not at pf_disco_piece / FF_disco):
   - %dx%d: a Theorem Labs lane's FMpfArmPdCtl (fm 0ddf65fd8cc lib/A/FMpfArmPdCtl.v:110-227: ctl_parse, ctl_text, ctl_fmt_at,
     ctl_in_pcomK / ctl_in_route at pf_fm_pc_d, ctl_f = 0x20fe0); its disco row R9-A-FMpfArmPdCtl (a Theorem Labs lane,
     a working branch 990c3a3a8c1) holds notes only. ctl_d_parse / ctl_d_text below
     restate its ctl_parse / ctl_text at disco's names.
   - site 1's %02x: a Theorem Labs lane's controls (a working branch 6dbf2ed755a = fm 0ddf65fd8cc
     lib/A/RT_pf_02x.v:49-80 disco_mac_parse / disco_mac_render at pf_pc_02x, and lib/A/FMgxaSeam02x.v:65-106
     disco_mac02_* at pk_02x); rows R9-*-RT_pf_02x / R9-*-FMgxaSeam02x, not relocated. The mac de:ad:be:ef:00:01 of
     ctl_02x_text_mac is theirs.
   - %llu: fm 0ddf65fd8cc lib/A/RT_pf_llu.v:38-94 places "%llu" at 0x10000, below disco_fmt_lo, so it cannot serve here.
   Image: NOT neutral (measured, a Theorem Labs lane 16:5xZ: Print Libraries of a throwaway file that Requires this one, dgb
   probe on T0 dc724fb4daf). It loads the A image images.Asan and the lib/A image modules AF0x (TFIB_IMG_END, used by
   (2)), AF0l, AF0m, AB1v, AB1q, RT_pf_sh, Rt/SnprintfConsts (disco_fmt_lo / disco_fmt_hi) and, through it,
   Prog/DiscoImg, DiscoPa, PaRun, PaShadow; the closure's other lib/A files, Bz/A/I_pcxgram, Bz/BvWfKernel and FMpfStep,
   are image-neutral (one copy for both images). The Y image has its own copy, lib/B/RT_pf_ctl.v (row R9-Y-RT_pf_ctl),
   built on lib/Reusable/YF0x and lib/Y/Rt/SnprintfConsts; do not Require this file from a Y file. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0f YG0d YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import PfFacts SnShared SnFF.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AF0x.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require RT_pf_sh.
Import ListNotations.
Local Open Scope Z_scope.

Module RTS := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.RT_pf_sh.

(* ---- the witness memory ---- *)
Definition ctl_rd (f : Z) (fmt : list Z) : reader := fun a =>
  if (f <=? a) && (a <=? f + Z.of_nat (length fmt))
  then Some (nth (Z.to_nat (a - f)) (fmt ++ [0]) 0)
  else if (SHADOW_OFF <=? a) && (a <? kHighMemBeg) then Some 0 else None.

Lemma ctl_rd_fmt : forall f fmt i, 0 <= i <= Z.of_nat (length fmt) ->
  ctl_rd f fmt (f + i) = Some (nth (Z.to_nat i) (fmt ++ [0]) 0).
Proof.
intros f fmt i Hi. unfold ctl_rd.
assert (E : (f <=? f + i) && (f + i <=? f + Z.of_nat (length fmt)) = true).
{ apply andb_true_intro. split; apply Z.leb_le; lia. }
rewrite E. replace (f + i - f) with i by lia. reflexivity.
Qed.

Lemma ctl_rd_shadow : forall f fmt a, f + Z.of_nat (length fmt) < SHADOW_OFF -> SHADOW_OFF <= a < kHighMemBeg ->
  ctl_rd f fmt a = Some 0.
Proof.
intros f fmt a Hf Ha. unfold ctl_rd.
assert (E : (f <=? a) && (a <=? f + Z.of_nat (length fmt)) = false).
{ apply andb_false_intro2. apply Z.leb_gt. lia. }
rewrite E.
assert (E' : (SHADOW_OFF <=? a) && (a <? kHighMemBeg) = true).
{ apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite E'. reflexivity.
Qed.

(* the format at f is an fmt_at member (no written region) whenever it lies in the low application memory *)
Lemma ctl_fmt_at : forall f fmt, 0 < f -> f + Z.of_nat (length fmt) + 1 <= kLowMemEnd - 1 ->
  fmt_at (ctl_rd f fmt) [] f fmt.
Proof.
intros f fmt Hf Hl. unfold fmt_at.
assert (Hs : f + Z.of_nat (length fmt) < SHADOW_OFF) by (unfold SHADOW_OFF, kLowMemEnd in *; lia).
refine (conj Hf (conj (ctl_rd_fmt f fmt) (conj (Forall_nil _) (conj _ (conj _ _))))).
- unfold amem_range. left. lia.
- intros x Hx. exists 0. split; [|left; reflexivity].
  apply ctl_rd_shadow; [exact Hs|].
  unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg in *.
  assert (0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia.
- intros s Hsr. rewrite (ctl_rd_shadow f fmt s Hs); [discriminate|].
  unfold shadow_addr, SHADOW_OFF, kHighMemBeg in *. Z.div_mod_to_equations. lia.
Qed.

(* disco's TFIB_IMG_END (AF0x.v:27, YImgTop.IMG_TOP); fm's file has TFIB_IMG_END = 0x5f7000 here *)
Lemma ctl_img_end : TFIB_IMG_END = 0x5fe000.
Proof. vm_compute. reflexivity. Qed.

(* ---- the arguments: 32-bit ints (%d, %02x) and their words ---- *)
Lemma ctl_args_int : forall rd rs vs, Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) vs ->
  pf_args_asan rd rs vs (map AInt vs).
Proof. intros rd rs vs H. induction H as [|v vs Hv _ IH]; [exact I | exact (conj (conj Hv eq_refl) IH)]. Qed.

Lemma ctl_slack_int : forall vs, pf_args_slack vs (map AInt vs).
Proof. induction vs as [|v vs IH]; [exact I | exact IH]. Qed.

Lemma ctl_amem_int : forall vs, pf_args_amem vs (map AInt vs).
Proof. induction vs as [|v vs IH]; [exact I | exact IH]. Qed.

Lemma ctl_amem_int_sh : forall vs, RTS.pf_args_amem vs (map AInt vs).
Proof. induction vs as [|v vs IH]; [exact I | exact IH]. Qed.

(* ---- the three formats as read from .rodata, their parses and their texts ---- *)
Definition F_d : Z := 0x20fe0.
Definition FMT_d : list Z := [37; 100; 120; 37; 100].
Definition PS_d : list pf_piece := [Pd; PLit 120; Pd].

Definition F_02x : Z := 0x20f80.
Definition FMT_02x : list Z :=
  [37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 58;
   37; 48; 50; 120].
Definition PS_02x : list pf_piece :=
  [Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02; PLit 58; Px02].
Definition TXT_02x (v1 v2 v3 v4 v5 v6 : Z) : list Z :=
  pf_hex2 v1 ++ 58 :: pf_hex2 v2 ++ 58 :: pf_hex2 v3 ++ 58 :: pf_hex2 v4 ++ 58 :: pf_hex2 v5 ++ 58 :: pf_hex2 v6.

Definition F_llu : Z := 0x21040.
Definition FMT_llu : list Z := [37; 108; 108; 117].
Definition PS_llu : list pf_piece := [Pllu].

Lemma ctl_d_len : Z.of_nat (length FMT_d) = 5. Proof. reflexivity. Qed.
Lemma ctl_02x_len : Z.of_nat (length FMT_02x) = 29. Proof. reflexivity. Qed.
Lemma ctl_llu_len : Z.of_nat (length FMT_llu) = 4. Proof. reflexivity. Qed.

Lemma ctl_d_parse : pf_parse FMT_d = Some PS_d. Proof. reflexivity. Qed.
Lemma ctl_02x_parse : pf_parse FMT_02x = Some PS_02x. Proof. reflexivity. Qed.
Lemma ctl_llu_parse : pf_parse FMT_llu = Some PS_llu. Proof. reflexivity. Qed.

Lemma ctl_d_pk : Forall pf_disco_piece PS_d. Proof. repeat constructor. Qed.
Lemma ctl_02x_pk : Forall pf_disco_piece PS_02x. Proof. repeat constructor. Qed.
Lemma ctl_llu_pk : Forall pf_disco_piece PS_llu. Proof. repeat constructor. Qed.

(* the texts depend on every argument *)
Lemma ctl_d_text : forall v1 v2, pf_text PS_d (map AInt [v1; v2]) = Some (pf_dec v1 ++ 120 :: pf_dec v2).
Proof. intros v1 v2. cbn [pf_text PS_d map option_map]. rewrite app_nil_r. reflexivity. Qed.

Lemma ctl_02x_text : forall v1 v2 v3 v4 v5 v6,
  pf_text PS_02x (map AInt [v1; v2; v3; v4; v5; v6]) = Some (TXT_02x v1 v2 v3 v4 v5 v6).
Proof. intros v1 v2 v3 v4 v5 v6. cbn [pf_text PS_02x map option_map]. rewrite app_nil_r. reflexivity. Qed.

Lemma ctl_llu_text : forall u, pf_text PS_llu [AU64 u] = Some (pf_udec u).
Proof. intros u. cbn [pf_text PS_llu option_map]. rewrite app_nil_r. reflexivity. Qed.

(* three concrete renderings: "16x9"; the mac de:ad:be:ef:00:01; an age of 1500 ms *)
Example ctl_d_text_16x9 : pf_text PS_d (map AInt [16; 9]) = Some [49; 54; 120; 57].
Proof. vm_compute. reflexivity. Qed.

Example ctl_02x_text_mac : pf_text PS_02x (map AInt [0xde; 0xad; 0xbe; 0xef; 0x00; 0x01]) =
  Some [100; 101; 58; 97; 100; 58; 98; 101; 58; 101; 102; 58; 48; 48; 58; 48; 49].
Proof. vm_compute. reflexivity. Qed.

Example ctl_llu_text_1500 : pf_text PS_llu [AU64 1500] = Some [49; 53; 48; 48].
Proof. vm_compute. reflexivity. Qed.

(* ---- (1) FF_disco: every range [lo, hi) holding the format, and disco_fmt_lo / disco_fmt_hi ---- *)
Theorem ctl_d_disco : forall lo hi v1 v2, lo <= F_d -> F_d + 6 <= hi ->
  Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) [v1; v2] ->
  FF_disco lo hi (ctl_rd F_d FMT_d) [] F_d [v1; v2] (pf_dec v1 ++ 120 :: pf_dec v2).
Proof.
intros lo hi v1 v2 Hlo Hhi Hv. exists FMT_d, PS_d, (map AInt [v1; v2]).
split; [apply ctl_fmt_at; rewrite ?ctl_d_len; unfold F_d, kLowMemEnd; lia|].
split; [exact ctl_d_parse|].
split; [exact ctl_d_pk|].
split; [exact (ctl_args_int _ _ _ Hv)|].
split; [exact (ctl_d_text v1 v2)|].
split; [exact I|].
split; [exact Hlo|].
split; [rewrite ctl_d_len; lia|].
split; [exact (ctl_slack_int _)|].
split; [discriminate|].
exact (ctl_amem_int _).
Qed.

Theorem ctl_02x_disco : forall lo hi v1 v2 v3 v4 v5 v6, lo <= F_02x -> F_02x + 30 <= hi ->
  Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) [v1; v2; v3; v4; v5; v6] ->
  FF_disco lo hi (ctl_rd F_02x FMT_02x) [] F_02x [v1; v2; v3; v4; v5; v6] (TXT_02x v1 v2 v3 v4 v5 v6).
Proof.
intros lo hi v1 v2 v3 v4 v5 v6 Hlo Hhi Hv. exists FMT_02x, PS_02x, (map AInt [v1; v2; v3; v4; v5; v6]).
split; [apply ctl_fmt_at; rewrite ?ctl_02x_len; unfold F_02x, kLowMemEnd; lia|].
split; [exact ctl_02x_parse|].
split; [exact ctl_02x_pk|].
split; [exact (ctl_args_int _ _ _ Hv)|].
split; [exact (ctl_02x_text v1 v2 v3 v4 v5 v6)|].
split; [exact I|].
split; [exact Hlo|].
split; [rewrite ctl_02x_len; lia|].
split; [exact (ctl_slack_int _)|].
split; [discriminate|].
exact (ctl_amem_int _).
Qed.

Theorem ctl_llu_disco : forall lo hi u, lo <= F_llu -> F_llu + 5 <= hi ->
  FF_disco lo hi (ctl_rd F_llu FMT_llu) [] F_llu [u] (pf_udec u).
Proof.
intros lo hi u Hlo Hhi. exists FMT_llu, PS_llu, [AU64 u].
split; [apply ctl_fmt_at; rewrite ?ctl_llu_len; unfold F_llu, kLowMemEnd; lia|].
split; [exact ctl_llu_parse|].
split; [exact ctl_llu_pk|].
split; [exact (conj eq_refl I)|].
split; [exact (ctl_llu_text u)|].
split; [exact I|].
split; [exact Hlo|].
split; [rewrite ctl_llu_len; lia|].
split; [exact I|].
split; [discriminate|].
exact I.
Qed.

Corollary ctl_d_disco_A : forall v1 v2, Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) [v1; v2] ->
  FF_disco disco_fmt_lo disco_fmt_hi (ctl_rd F_d FMT_d) [] F_d [v1; v2] (pf_dec v1 ++ 120 :: pf_dec v2).
Proof. intros v1 v2 Hv. apply ctl_d_disco; [unfold disco_fmt_lo, F_d; lia | unfold disco_fmt_hi, F_d; lia | exact Hv]. Qed.

Corollary ctl_02x_disco_A : forall v1 v2 v3 v4 v5 v6,
  Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) [v1; v2; v3; v4; v5; v6] ->
  FF_disco disco_fmt_lo disco_fmt_hi (ctl_rd F_02x FMT_02x) [] F_02x [v1; v2; v3; v4; v5; v6]
    (TXT_02x v1 v2 v3 v4 v5 v6).
Proof.
intros v1 v2 v3 v4 v5 v6 Hv.
apply ctl_02x_disco; [unfold disco_fmt_lo, F_02x; lia | unfold disco_fmt_hi, F_02x; lia | exact Hv].
Qed.

Corollary ctl_llu_disco_A : forall u,
  FF_disco disco_fmt_lo disco_fmt_hi (ctl_rd F_llu FMT_llu) [] F_llu [u] (pf_udec u).
Proof. intros u. apply ctl_llu_disco; [unfold disco_fmt_lo, F_llu; lia | unfold disco_fmt_hi, F_llu; lia]. Qed.

(* the three concrete instances: "16x9", the mac, an age of 1500 ms *)
Example ctl_d_disco_16x9 :
  FF_disco disco_fmt_lo disco_fmt_hi (ctl_rd F_d FMT_d) [] F_d [16; 9] [49; 54; 120; 57].
Proof. exact (ctl_d_disco_A 16 9 ltac:(repeat constructor; lia)). Qed.

Example ctl_02x_disco_mac :
  FF_disco disco_fmt_lo disco_fmt_hi (ctl_rd F_02x FMT_02x) [] F_02x [0xde; 0xad; 0xbe; 0xef; 0x00; 0x01]
    [100; 101; 58; 97; 100; 58; 98; 101; 58; 101; 102; 58; 48; 48; 58; 48; 49].
Proof. exact (ctl_02x_disco_A 0xde 0xad 0xbe 0xef 0x00 0x01 ltac:(repeat constructor; lia)). Qed.

Example ctl_llu_disco_1500 :
  FF_disco disco_fmt_lo disco_fmt_hi (ctl_rd F_llu FMT_llu) [] F_llu [1500] [49; 53; 48; 48].
Proof. exact (ctl_llu_disco_A 1500). Qed.

(* ---- (2) printf_common's family FF_pcomK at disco's pieces (RT_pf_sh.v:266) ---- *)
Theorem ctl_d_pcomK : forall v1 v2, Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) [v1; v2] ->
  RTS.FF_pcomK pf_disco_piece (ctl_rd F_d FMT_d) [] F_d [v1; v2] (pf_dec v1 ++ 120 :: pf_dec v2).
Proof.
intros v1 v2 Hv. unfold RTS.FF_pcomK. exists FMT_d, PS_d, (map AInt [v1; v2]).
split; [apply ctl_fmt_at; rewrite ?ctl_d_len; unfold F_d, kLowMemEnd; lia|].
split; [discriminate|].
split; [rewrite ctl_d_len, ctl_img_end; unfold F_d; lia|].
split; [exact ctl_d_parse|].
split; [exact ctl_d_pk|].
split; [exact (ctl_args_int _ _ _ Hv)|].
split; [exact (ctl_amem_int_sh _)|].
split; [exact (ctl_d_text v1 v2)|].
exact I.
Qed.

Theorem ctl_02x_pcomK : forall v1 v2 v3 v4 v5 v6, Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) [v1; v2; v3; v4; v5; v6] ->
  RTS.FF_pcomK pf_disco_piece (ctl_rd F_02x FMT_02x) [] F_02x [v1; v2; v3; v4; v5; v6] (TXT_02x v1 v2 v3 v4 v5 v6).
Proof.
intros v1 v2 v3 v4 v5 v6 Hv. unfold RTS.FF_pcomK. exists FMT_02x, PS_02x, (map AInt [v1; v2; v3; v4; v5; v6]).
split; [apply ctl_fmt_at; rewrite ?ctl_02x_len; unfold F_02x, kLowMemEnd; lia|].
split; [discriminate|].
split; [rewrite ctl_02x_len, ctl_img_end; unfold F_02x; lia|].
split; [exact ctl_02x_parse|].
split; [exact ctl_02x_pk|].
split; [exact (ctl_args_int _ _ _ Hv)|].
split; [exact (ctl_amem_int_sh _)|].
split; [exact (ctl_02x_text v1 v2 v3 v4 v5 v6)|].
exact I.
Qed.

Theorem ctl_llu_pcomK : forall u,
  RTS.FF_pcomK pf_disco_piece (ctl_rd F_llu FMT_llu) [] F_llu [u] (pf_udec u).
Proof.
intros u. unfold RTS.FF_pcomK. exists FMT_llu, PS_llu, [AU64 u].
split; [apply ctl_fmt_at; rewrite ?ctl_llu_len; unfold F_llu, kLowMemEnd; lia|].
split; [discriminate|].
split; [rewrite ctl_llu_len, ctl_img_end; unfold F_llu; lia|].
split; [exact ctl_llu_parse|].
split; [exact ctl_llu_pk|].
split; [exact (conj eq_refl I)|].
split; [exact I|].
split; [exact (ctl_llu_text u)|].
exact I.
Qed.

(* ---- (3) pf_family_ro pf_disco_piece lo hi, from (1) ---- *)
Corollary ctl_d_ro : forall lo hi v1 v2, lo <= F_d -> F_d + 6 <= hi ->
  Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) [v1; v2] ->
  pf_family_ro pf_disco_piece lo hi (ctl_rd F_d FMT_d) [] F_d [v1; v2] (pf_dec v1 ++ 120 :: pf_dec v2).
Proof. intros lo hi v1 v2 Hlo Hhi Hv. exact (FF_disco_ro lo hi _ _ _ _ _ (ctl_d_disco lo hi v1 v2 Hlo Hhi Hv)). Qed.

Corollary ctl_02x_ro : forall lo hi v1 v2 v3 v4 v5 v6, lo <= F_02x -> F_02x + 30 <= hi ->
  Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) [v1; v2; v3; v4; v5; v6] ->
  pf_family_ro pf_disco_piece lo hi (ctl_rd F_02x FMT_02x) [] F_02x [v1; v2; v3; v4; v5; v6]
    (TXT_02x v1 v2 v3 v4 v5 v6).
Proof.
intros lo hi v1 v2 v3 v4 v5 v6 Hlo Hhi Hv.
exact (FF_disco_ro lo hi _ _ _ _ _ (ctl_02x_disco lo hi v1 v2 v3 v4 v5 v6 Hlo Hhi Hv)).
Qed.

Corollary ctl_llu_ro : forall lo hi u, lo <= F_llu -> F_llu + 5 <= hi ->
  pf_family_ro pf_disco_piece lo hi (ctl_rd F_llu FMT_llu) [] F_llu [u] (pf_udec u).
Proof. intros lo hi u Hlo Hhi. exact (FF_disco_ro lo hi _ _ _ _ _ (ctl_llu_disco lo hi u Hlo Hhi)). Qed.

(* ---- (4) the controls bite: fm's piece predicate pf_fm_piece (literals, %s, %.*s) refuses each format's parse ---- *)
Lemma ctl_d_not_fm : forall ps, pf_parse FMT_d = Some ps -> ~ Forall pf_fm_piece ps.
Proof.
intros ps H. rewrite ctl_d_parse in H. injection H as <-. unfold PS_d. intros HF.
inversion HF as [|p l Hp _]. exact Hp.
Qed.

Lemma ctl_02x_not_fm : forall ps, pf_parse FMT_02x = Some ps -> ~ Forall pf_fm_piece ps.
Proof.
intros ps H. rewrite ctl_02x_parse in H. injection H as <-. unfold PS_02x. intros HF.
inversion HF as [|p l Hp _]. exact Hp.
Qed.

Lemma ctl_llu_not_fm : forall ps, pf_parse FMT_llu = Some ps -> ~ Forall pf_fm_piece ps.
Proof.
intros ps H. rewrite ctl_llu_parse in H. injection H as <-. unfold PS_llu. intros HF.
inversion HF as [|p l Hp _]. exact Hp.
Qed.
