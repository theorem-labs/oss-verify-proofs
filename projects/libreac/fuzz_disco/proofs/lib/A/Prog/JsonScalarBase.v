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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/JsonScalar.v; 515 of its 610 lines of code are new or changed and 706 lines of the source are left out. *)
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
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC4b YC85 YC88 DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Default Proof Using "All".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Notation TJSON_SCALAR_STK := (128 + 2 * ESTACK) (only parsing).
Ltac jnorm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
Ltac jpin HS r z Hr :=
  let H := fresh "HSp" in
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 r) z HS Hr eq_refl) as H; clear HS; rename H into HS; jnorm HS.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
Definition JS_EPI : Z := 0x31c4.
Definition JSAVED : list (Z * Z) :=
  [(120, 1); (112, 8); (104, 9); (96, 18); (88, 19); (80, 20); (72, 21); (64, 22); (56, 23); (48, 24); (40, 25); (32, 26); (24, 27)].
Definition jframe_chunks : list YP09.chunk :=
  [YP09.mkChunk 120 (CVal 8 (SOff 32 0)); YP09.mkChunk 112 (CVal 8 (SOff 33 0)); YP09.mkChunk 104 (CVal 8 (SOff 34 0));
   YP09.mkChunk 96 (CVal 8 (SOff 35 0)); YP09.mkChunk 88 (CVal 8 (SOff 36 0)); YP09.mkChunk 80 (CVal 8 (SOff 37 0));
   YP09.mkChunk 72 (CVal 8 (SOff 38 0)); YP09.mkChunk 64 (CVal 8 (SOff 39 0)); YP09.mkChunk 56 (CVal 8 (SOff 40 0));
   YP09.mkChunk 48 (CVal 8 (SOff 41 0)); YP09.mkChunk 40 (CVal 8 (SOff 42 0)); YP09.mkChunk 32 (CVal 8 (SOff 43 0));
   YP09.mkChunk 24 (CVal 8 (SOff 44 0))].
Definition jframe : YP09.region := YP09.mkRegion (Some 2%nat) 0 128 0 128 jframe_chunks.
Definition JSP_LO : Z := 0x7fff7f800000.
Definition JSP_HI : Z := 0x7fffffffff80.
Definition JBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition jG_epi : facts := mkFacts [(2%nat, mkAF JSP_LO JSP_HI 4)] [] [].
Class JH (B : asyms) (fq : YK11.FPState) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world SEGS)
  (memc : word -> option byte) (k : Z) (regs0 : bvmap 5 word) (b i n v : Z) (BS : list byte) (mdc : Model) : Prop := {
  jh_LAWS : AR_laws SEGS B;
  jh_HJ0 : ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k;
  jh_Hvimg : off_img v 20;
  jh_Hsp16 : spZ regs0 mod 16 = 0;
  jh_HspSTK : sp0 - STK <= spZ regs0 - TJSON_SCALAR_STK;
  jh_Hsp0 : spZ regs0 <= sp0;
  jh_Hv0 : 0 < v;
  jh_Hv8 : v mod 8 = 0;
  jh_Hv63 : v + 20 <= 2 ^ 63;
  jh_Hvw : spZ regs0 <= v \/ v + 20 <= spZ regs0 - TJSON_SCALAR_STK;
  jh_Hra : YK0s.ret_ok (getr regs0 1);
  jh_HLn : Z.of_nat (length BS) = n;
  jh_HBS : garr8 SEGS (mrestrict (w_H W) memc) b (map bv_unsigned BS);
  jh_Hb0 : 0 < b;
  jh_Hbam : amem_range b n;
  jh_Hbw : b + n <= spZ regs0 - TJSON_SCALAR_STK \/ spZ regs0 <= b;
  jh_Hvam : amem_range v 20;
  jh_Hvra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF v 20;
  jh_Hvaw : forall a, v <= a < v + 20 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
    apresent (w_H W) memc a;
  jh_Hbv : b + n <= v \/ v + 20 <= b;
  jh_Hbra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF b n
}.
Section h.
Context {B : asyms}.
Section J.
Context {fq : YK11.FPState} {STK sp0 : Z} {FP : list (Z * Z)} {ly : alayout} {S : astate} {W0 : world SEGS}
  {mem0 : word -> option byte} {md0 : Model} {own : list (Z * Z)} {lyc : alayout} {Sc : astate} {W : world SEGS}
  {memc : word -> option byte} {k : Z} {regs0 : bvmap 5 word} {b i n v : Z} {BS : list byte} {mdc : Model}.
Context `{JHI : JH (fq := fq) B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs0 b i n v BS mdc}.
Let LAWS : AR_laws SEGS B := jh_LAWS.
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
Definition JX : list word := (fun _ => map (fun p => getr regs0 (Z_to_bv 5 (snd p))) JSAVED) JHI.
Definition JSLOTS (M : word -> option byte) : Prop := (fun _ =>
  forall t, (t < 13)%nat -> val_mem SEGS (mrestrict (w_H W) M) (spZ regs0 - 128 + fst (nth t JSAVED (0, 0))) 8
    (bv_unsigned (getr regs0 (Z_to_bv 5 (snd (nth t JSAVED (0, 0))))))) JHI.
Definition JKEEP (M : word -> option byte) : Prop := (fun _ =>
  forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs0 - TJSON_SCALAR_STK <= a < spZ regs0) ->
    aview SEGS (w_H W) M a = aview SEGS (w_H W) memc a) JHI.
Definition JKEEPV (M : word -> option byte) : Prop := (fun _ =>
  forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs0 - TJSON_SCALAR_STK <= a < spZ regs0) -> ~ (v <= a < v + 20) ->
    aview SEGS (w_H W) M a = aview SEGS (w_H W) memc a) JHI.
Definition JPRES (M : word -> option byte) : Prop := (fun _ =>
  forall a, apresent (w_H W) memc a -> apresent (w_H W) M a) JHI.
Definition JRES (M : word -> option byte) (r : Z) : Prop :=
  match jscalar (map bv_unsigned BS) i with
  | Some (e, kd, s, l) =>
      r = e /\ val_mem SEGS (mrestrict (w_H W) M) v 8 (b + s) /\ val_mem SEGS (mrestrict (w_H W) M) (v + 8) 8 l /\
      val_mem SEGS (mrestrict (w_H W) M) (v + 16) 4 kd /\ JKEEPV M
  | None => r = 0 /\ JKEEP M
  end.
Lemma jframe_ok : forall E M,
  bv_unsigned (ew E 2) = spZ regs0 - 128 ->
  (forall t, (t < 13)%nat -> ew E (32 + t) = getr regs0 (Z_to_bv 5 (snd (nth t JSAVED (0, 0))))) ->
  JSLOTS M -> (forall a, spZ regs0 - 128 <= a < spZ regs0 -> apresent (w_H W) M a) ->
  0 <= spZ regs0 - 128 -> spZ regs0 <= 2 ^ 64 ->
  region_ok SEGS E (mrestrict (w_H W) M) jframe.
Proof.
intros E M H2 HX HSL HP Hlo Hhi.
unfold region_ok, jframe. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite H2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable SEGS). apply HP. lia. }
unfold jframe_chunks.
repeat match goal with |- Forall _ [] => apply Forall_nil | |- Forall _ (_ :: _) => apply Forall_cons end.
all: lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal _ (SOff ?nn _))) =>
  let t := eval compute in (nn - 32)%nat in
  pose proof (HX t ltac:(lia)) as Ht; pose proof (HSL t ltac:(lia)) as Hv; unfold JSAVED in Ht, Hv;
  cbn [nth fst snd Nat.add] in Ht, Hv;
  refine (chunk_ok_val SEGS E _ _ _ 8 _ _ _ _ _ Hv);
  [ cbn [sv_denot]; rewrite Ht, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | apply bv_unsigned_in_range
  | lia ]
end.
Qed.
Lemma jwin_lo : alloc_ceiling <= spZ regs0 - TJSON_SCALAR_STK.
Proof.
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & _). lia.
Qed.
Lemma jE_extra : forall R t, (t < 13)%nat ->
  ew (Eimg (Ereg R JX)) (32 + t) = getr regs0 (Z_to_bv 5 (snd (nth t JSAVED (0, 0)))).
Proof.
intros R t Ht. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
do 13 (destruct t as [|t]; [reflexivity|]). lia.
Qed.
Definition JINV (R : bvmap 5 word) (M : word -> option byte) (md : Model) : Prop :=
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W M md k /\ JSLOTS M /\ JKEEP M /\ JPRES M /\
  getr R 2 = w64 (spZ regs0 - 128) /\ getr R 3 = getr regs0 3 /\ getr R 4 = getr regs0 4 /\
  getr R 9 = w64 SHADOW_OFF /\ getr R 19 = w64 n /\ getr R 20 = w64 b.
Definition BZ : list Z := (fun _ => map bv_unsigned BS) JHI.
Definition JXB (j : Z) (la : nat) : list word :=
  JX ++ Z_to_bv 64 (b + j) :: map (fun t => Z_to_bv 64 (jbyte BZ (j + Z.of_nat t))) (seq 0 la).
Definition JE (R : bvmap 5 word) (j : Z) (la : nat) : env := Eimg (Ereg R (JXB j la)).
Lemma JX_len : length JX = 13%nat.
Proof. reflexivity. Qed.
Lemma jE_low : forall R j la (q : nat) (r : bv 5), (q < 32)%nat -> Z.of_nat q = bv_unsigned r -> ew (JE R j la) q = getr R r.
Proof. intros R j la q r Hq Hr. unfold JE. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr. Qed.
Lemma jE_X : forall R j la t, (t < 13)%nat -> ew (JE R j la) (32 + t) = getr regs0 (Z_to_bv 5 (snd (nth t JSAVED (0, 0)))).
Proof.
intros R j la t Ht. unfold JE. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. unfold JXB.
rewrite app_nth1 by (rewrite JX_len; exact Ht).
do 13 (destruct t as [|t]; [reflexivity|]). lia.
Qed.
Lemma jE_P : forall R j la, ew (JE R j la) 45 = Z_to_bv 64 (b + j).
Proof.
intros R j la. unfold JE. rewrite Eimg_low by (unfold A_TEXT; lia). change 45%nat with (32 + 13)%nat. rewrite ew_Ereg_extra.
unfold JXB. rewrite app_nth2 by (rewrite JX_len; lia). rewrite JX_len. reflexivity.
Qed.
Lemma jE_C : forall R j la t, (la <= 8)%nat -> (t < la)%nat -> ew (JE R j la) (46 + t) = Z_to_bv 64 (jbyte BZ (j + Z.of_nat t)).
Proof.
intros R j la t Hla Ht. unfold JE. rewrite Eimg_low by (unfold A_TEXT; lia). replace (46 + t)%nat with (32 + (14 + t))%nat by lia.
rewrite ew_Ereg_extra. unfold JXB. rewrite app_nth2 by (rewrite JX_len; lia). rewrite JX_len.
replace (14 + t - 13)%nat with (Datatypes.S t) by lia. cbn [nth].
set (f := fun t0 : nat => Z_to_bv 64 (jbyte BZ (j + Z.of_nat t0))).
rewrite (nth_indep _ _ (f 0%nat)) by (rewrite length_map, length_seq; exact Ht).
rewrite map_nth, seq_nth by exact Ht. reflexivity.
Qed.
Definition jbytes (la : nat) : YP09.region :=
  YP09.mkRegion (Some 45%nat) 0 (Z.of_nat la) 0 0 (map (fun t => YP09.mkChunk (Z.of_nat t) (CVal 1 (SOff (46 + t) 0))) (seq 0 la)).
Definition jatoms (la : nat) : list (nat * afact) :=
  (2%nat, mkAF JSP_LO JSP_HI 4) :: (9%nat, mkAF SHADOW_OFF SHADOW_OFF 0) :: (45%nat, mkAF 1 (0x7fffffffffff - Z.of_nat la) 0) ::
  map (fun t => ((46 + t)%nat, mkAF 0 255 0)) (seq 0 la).
Lemma atoms_ok_bytes : forall E la s, (forall t, (s <= t < s + la)%nat -> afact_ok E (46 + t) (mkAF 0 255 0)) ->
  atoms_ok E (map (fun t => ((46 + t)%nat, mkAF 0 255 0)) (seq s la)).
Proof.
intros E la. induction la as [|la IH]; intros s H; cbn [seq map atoms_ok]; [exact I|].
split; [apply H; lia | apply IH; intros t Ht; apply H; lia].
Qed.
Lemma regions_wf_jbytes : forall la, region_wf (jbytes la) = true.
Proof.
intros la. unfold region_wf, jbytes. cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
apply andb_true_intro. split; [apply andb_true_intro; split; [apply Z.leb_le; lia | reflexivity]|].
apply forallb_forall. intros c Hc. apply in_map_iff in Hc as (t & <- & Ht). apply in_seq in Ht.
unfold chunk_inside, c_len, cv_len. cbn [YP09.r_lo YP09.r_hi YP09.c_off YP09.c_val].
apply andb_true_intro. split; [apply andb_true_intro; split|]; apply Z.leb_le; lia.
Qed.
Let HLn : Z.of_nat (length BS) = n := jh_HLn.
Let HBS : garr8 SEGS (mrestrict (w_H W) memc) b BZ := jh_HBS.
Let Hb0 : 0 < b := jh_Hb0.
Let Hbam : amem_range b n := jh_Hbam.
Let Hbw : b + n <= spZ regs0 - TJSON_SCALAR_STK \/ spZ regs0 <= b := jh_Hbw.
Lemma jb_hi : b + n <= 0x7fffffffffff.
Proof. pose proof asan_consts as (_ & _ & C3 & C4 & C5). unfold amem_range in Hbam. lia. Qed.
Lemma jsp_hi : spZ regs0 <= 2 ^ 47.
Proof.
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & _ & _ & Hshi & H47 & _). lia.
Qed.
Lemma jbyte_mem : forall M t, JKEEP M -> 0 <= t < n ->
  val_mem SEGS (mrestrict (w_H W) M) (b + t) 1 (jbyte BZ t) /\ 0 <= jbyte BZ t < 256.
Proof.
intros M t HK Ht. pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & _).
assert (HBZ : length BZ = length BS) by (unfold BZ; apply length_map).
destruct (HBS (Z.to_nat t) ltac:(lia)) as [Hv Hr].
rewrite Z2Nat.id in Hv by lia. unfold jbyte. split; [|exact Hr].
apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) memc M); [|exact Hv].
intros x Hx. unfold JKEEP in HK. apply HK; lia.
Qed.
Lemma jstate : forall R M md pc j (la : nat) al,
  JINV R M md -> 0 <= j -> j + Z.of_nat la <= n -> (la <= 8)%nat ->
  alias_ok (JE R j la) al ->
  st_ok_pi SEGS VAL (JE R j la) (mkSS pc sr_atoms [jframe; jbytes la] None (mkFacts (jatoms la) [] al))
    (restrict (w_H W) (mkst R (Z_to_bv 64 (BASE + pc)) M (seg_rom SEGS))).
Proof.
intros R M md pc j la al (HJ & HSL & HK & HPR & H2 & H3 & H4 & H9 & H19 & H20) Hj Hjla Hla Hal.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
assert (Usp : bv_unsigned (getr R 2) = spZ regs0 - 128) by (rewrite H2; unfold w64; rewrite unsigned_lit_small; lia).
assert (E2 : ew (JE R j la) 2 = getr R 2) by (apply jE_low; [lia | reflexivity]).
assert (E9 : ew (JE R j la) 9 = getr R 9) by (apply jE_low; [lia | reflexivity]).
assert (UP : bv_unsigned (ew (JE R j la) 45) = b + j) by (rewrite jE_P; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- cbn [regions_wf]. rewrite regions_wf_jbytes. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply jframe_ok; [rewrite E2; exact Usp | intros t Ht; apply jE_X; exact Ht | exact HSL | intros a Ha; apply Hpres; lia | lia | lia].
  + unfold region_ok, jbytes. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UP.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (t & <- & Ht). apply in_seq in Ht.
    destruct (jbyte_mem M (j + Z.of_nat t) HK ltac:(lia)) as [Hv Hr].
    refine (chunk_ok_val SEGS (JE R j la) _ _ _ 1 _ (jbyte BZ (j + Z.of_nat t)) _ _ _ _).
    * cbn [sv_denot]. rewrite jE_C by lia. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
    * change (2 ^ (8 * Z.of_N 1)) with 256. lia.
    * cbn. lia.
    * replace (b + j + Z.of_nat t) with (b + (j + Z.of_nat t)) by lia. exact Hv.
- cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I]|split; [exact I | exact I]].
  unfold extent_disjoint, jframe, jbytes. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, Usp, UP. lia.
- split; [|split; [exact I | exact Hal]]. unfold jatoms. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  assert (Hsp'16 : (spZ regs0 - 128) mod 16 = 0) by (rewrite Zminus_mod, Hsp16; reflexivity).
  rewrite E2, Usp, E9, H9, UP. unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
  unfold JSP_LO, JSP_HI, SHADOW_OFF. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  split; [repeat split; try lia; exact Hsp'16|]. split; [repeat split; lia|]. split; [repeat split; lia|].
  apply atoms_ok_bytes. intros t Ht. unfold afact_ok. cbn [af_lo af_hi af_al2].
  destruct (jbyte_mem M (j + Z.of_nat t) HK ltac:(lia)) as [_ Hr].
  rewrite jE_C by lia. rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.
Lemma jalias_add : forall E (nb nr np : nat) c d xb xr xp,
  bv_unsigned (ew E nb) = xb -> bv_unsigned (ew E nr) = xr -> bv_unsigned (ew E np) = xp ->
  (xp + d) mod 2 ^ 64 = (xb + xr + c) mod 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff nb 0) (SOff nr c)) = sv_denot E (SOff np d).
Proof.
intros E nb nr np c d xb xr xp Hb Hr Hp Hm. rewrite !denot_lit_U. f_equal.
rewrite U_SAlu, !U_SOff. cbn [zalu_raw]. unfold zcanon, M64. rewrite Hb, Hr, Hp, Z.add_0_r.
rewrite <- Zplus_mod. rewrite Hm. f_equal. lia.
Qed.
Lemma jU_reg : forall R j la (q : nat) (r : bv 5) z, (q < 32)%nat -> Z.of_nat q = bv_unsigned r ->
  getr R r = w64 z -> 0 <= z < 2 ^ 64 -> bv_unsigned (ew (JE R j la) q) = z.
Proof. intros R j la q r z Hq Hr Hz Hz2. rewrite (jE_low R j la q r Hq Hr), Hz. unfold w64. apply unsigned_lit_small. exact Hz2. Qed.
Lemma jslots_of : forall E ss ms (idx : nat) cs,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) idx = Some (YP09.mkRegion (Some 2%nat) 0 128 0 128 cs) ->
  incl jframe_chunks cs ->
  bv_unsigned (ew E 2) = spZ regs0 - 128 ->
  (forall t, (t < 13)%nat -> ew E (32 + t) = getr regs0 (Z_to_bv 5 (snd (nth t JSAVED (0, 0))))) ->
  JSLOTS (ms_mem ms).
Proof.
intros E ss ms idx cs HS Hn Hinc H2 HX t Ht.
pose proof (st_ok_pi_region_nth E ss _ idx _ HS Hn) as HR. cbn [ms_mem restrict] in HR.
assert (Hc : In (nth t jframe_chunks (YP09.mkChunk 0 (CZero 0))) cs) by (apply Hinc; apply nth_In; cbn; lia).
assert (Hnc : nth t jframe_chunks (YP09.mkChunk 0 (CZero 0)) =
  YP09.mkChunk (fst (nth t JSAVED (0, 0))) (CVal 8 (SOff (32 + t) 0))) by (do 13 (destruct t as [|t]; [reflexivity|]); lia).
rewrite Hnc in Hc.
exact (field_of_region E _ 2 _ cs 0 128 0 128 _ 8 (SOff (32 + t) 0)
  (bv_unsigned (getr regs0 (Z_to_bv 5 (snd (nth t JSAVED (0, 0)))))) HR H2 Hc
  ltac:(cbn [sv_denot]; rewrite HX by exact Ht; rewrite Z.add_0_r; reflexivity)
  (bv_unsigned_in_range 64 _) ltac:(cbn; lia)).
Qed.
Let Hvam : amem_range v 20 := jh_Hvam.
Let Hvra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF v 20 := jh_Hvra.
Let Hvaw : forall a, v <= a < v + 20 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
  apresent (w_H W) memc a := jh_Hvaw.
Let Hbv : b + n <= v \/ v + 20 <= b := jh_Hbv.
Definition vreg (nv : nat) : YP09.region := YP09.mkRegion (Some nv) 0 20 0 20 [].
Definition JVHI : Z := 0x7fffffffffeb.
Lemma jvstate : forall R M md pc j (nv : nat) (rv : bv 5) al,
  JINV R M md -> 0 <= j <= n -> (nv < 32)%nat -> Z.of_nat nv = bv_unsigned rv -> getr R rv = w64 v ->
  alias_ok (JE R j 0) al ->
  st_ok_pi SEGS VAL (JE R j 0) (mkSS pc sr_atoms [vreg nv; jframe; jbytes 0] None
    (mkFacts ((nv, mkAF 1 JVHI 3) :: jatoms 0) [] al))
    (restrict (w_H W) (mkst R (Z_to_bv 64 (BASE + pc)) M (seg_rom SEGS))).
Proof.
intros R M md pc j nv rv al HI Hj Hnv Hrv Hv Hal.
pose proof (jstate R M md pc j 0 al HI ltac:(lia) ltac:(lia) ltac:(lia) Hal) as HS.
destruct HI as (HJ & HSL & HK & HPR & H2 & _).
pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
assert (Hvhi : v + 20 <= 0x7fffffffffff) by (unfold amem_range in Hvam; lia).
assert (UV : bv_unsigned (ew (JE R j 0) nv) = v) by (apply (jU_reg R j 0 nv rv); [exact Hnv | exact Hrv | exact Hv | lia]).
assert (Usp : bv_unsigned (ew (JE R j 0) 2) = spZ regs0 - 128).
{ rewrite (jE_low R j 0 2 2%bv) by (lia || reflexivity). rewrite H2. unfold w64. apply unsigned_lit_small. lia. }
assert (UP : bv_unsigned (ew (JE R j 0) 45) = b + j) by (rewrite jE_P; apply unsigned_lit_small; lia).
apply (st_ok_pi_add_fact _ _ _ nv (mkAF 1 JVHI 3)) in HS.
2:{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite UV. unfold JVHI. change (2 ^ 3) with 8. split; [lia|]. split; [exact Hv8 | lia]. }
apply (st_ok_pi_add_region _ _ _ (vreg nv)) in HS.
- jnorm HS. exact HS.
- reflexivity.
- unfold region_ok, vreg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UV.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). apply HPR. apply Hvaw. lia.
- cbn [ss_mem add_atom all_disjoint]. unfold extent_disjoint, vreg, jframe, jbytes.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UV, Usp, UP. split; [lia|]. split; [lia | exact I].
Qed.
Lemma jvshok : forall R M md j (nv : nat) (rv : bv 5),
  JINV R M md -> 0 <= j <= n -> (nv < 32)%nat -> Z.of_nat nv = bv_unsigned rv -> getr R rv = w64 v ->
  sh_ok SEGS (SOff 9 0) [mkSHE nv 0 20] (JE R j 0) (mrestrict (w_H W) M).
Proof.
intros R M md j nv rv HI Hj Hnv Hrv Hv. destruct HI as (HJ & HSL & HK & HPR & H2 & H3 & H4 & H9 & _).
pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hvhi : v + 20 <= 0x7fffffffffff) by (unfold amem_range in Hvam; lia).
constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) M (JE R j 0) (SOff 9 0) nv v 20 v 0 20).
- apply (range_addressable_kept_win (aview SEGS (w_H W) memc) (aview SEGS (w_H W) M) (spZ regs0 - TJSON_SCALAR_STK) (spZ regs0));
  [intros s Hs Hn; apply HK; assumption | lia | lia | lia | exact Hvra].
- unfold U. cbn [sv_denot]. rewrite (jE_low R j 0 9 9%bv) by (lia || reflexivity). rewrite H9, Z.add_0_r.
  unfold w64. rewrite Z_to_bv_bv_unsigned. apply unsigned_lit_small. unfold SHADOW_OFF; lia.
- unfold U. cbn [sv_denot]. rewrite (jE_low R j 0 nv rv Hnv Hrv), Hv, Z.add_0_r.
  unfold w64. rewrite Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia.
- lia.
- lia.
- intros x Hx. unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma jdenot_sub : forall E (na nb : nat) xa xb, bv_unsigned (ew E na) = xa -> bv_unsigned (ew E nb) = xb -> 0 <= xa - xb < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff na 0) (SMd M_MUL (SOff nb 0) (SLit (-1)))) = Z_to_bv 64 (xa - xb).
Proof.
intros E na nb xa xb Ha Hb Hr. rewrite denot_lit_U. f_equal. rewrite U_SAlu, U_SMd, !U_SOff, U_SLit. cbn [zalu_raw zmd_raw].
unfold zcanon, M64. rewrite Ha, Hb, !Z.add_0_r. rewrite <- Zmult_mod, <- Zplus_mod. rewrite Z.mod_small by lia. lia.
Qed.
Lemma jdenot_soff : forall E (na : nat) xa c, bv_unsigned (ew E na) = xa -> sv_denot E (SOff na c) = Z_to_bv 64 (xa + c).
Proof. intros E na xa c Ha. cbn [sv_denot]. rewrite Ha. reflexivity. Qed.
Lemma jkeepv_of : forall E rs M M',
  frame_of E rs (mrestrict (w_H W) M) (mrestrict (w_H W) M') ->
  (forall a, in_wrange E rs a -> (spZ regs0 - TJSON_SCALAR_STK <= a < spZ regs0) \/ (v <= a < v + 20)) ->
  JKEEP M -> JKEEPV M'.
Proof.
intros E rs M M' HF Hw HK a Ha Hn Hv. rewrite <- (HK a Ha Hn). apply (aview_eq_of SEGS). apply HF.
rewrite unsigned_lit_small by lia. intros Hin. destruct (Hw a Hin); tauto.
Qed.
Lemma jkeep_of : forall E rs M M',
  frame_of E rs (mrestrict (w_H W) M) (mrestrict (w_H W) M') ->
  (forall a, in_wrange E rs a -> spZ regs0 - TJSON_SCALAR_STK <= a < spZ regs0) ->
  JKEEP M -> JKEEP M'.
Proof.
intros E rs M M' HF Hw HK a Ha Hn. rewrite <- (HK a Ha Hn). apply (aview_eq_of SEGS). apply HF.
rewrite unsigned_lit_small by lia. intros Hin. exact (Hn (Hw a Hin)).
Qed.
Lemma jpres_of : forall M M', mem_grows (mrestrict (w_H W) M) (mrestrict (w_H W) M') -> JPRES M -> JPRES M'.
Proof. intros M M' HG HP a Ha. apply (apresent_grows _ _ _ _ HG). apply HP. exact Ha. Qed.
Lemma jbrute : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true -> forall c, 0 <= c < 256 -> P c = true.
Proof.
intros P H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat c). split; [lia | apply in_seq; lia].
Qed.
Lemma Lbr_dig : forall E (nn : nat) c, bv_unsigned (ew E nn) = c -> 0 <= c < 256 ->
  branch_taken BC_LTU (sv_denot E (SLit 18446744073709551605)) (sv_denot E (SOff nn (-58))) = jdigit c.
Proof.
intros E nn c Hc Hr. rewrite branch_ltu_U, U_SLit, U_SOff, Hc.
pose proof (jbrute (fun c => Bool.eqb (zcanon 18446744073709551605 <? zcanon (c + -58)) (jdigit c)) ltac:(vm_compute; reflexivity) c Hr) as X.
apply Bool.eqb_prop in X. exact X.
Qed.
Lemma Lbr_hex : forall E (nn : nat) c, bv_unsigned (ew E nn) = c -> 0 <= c < 256 -> jdigit c = false ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff nn 0) (SLit 223)) (SLit (-71)))) (sv_denot E (SLit 18446744073709551610))
  = negb (jhexd c).
Proof.
intros E nn c Hc Hr Hd. rewrite branch_ltu_U, !U_SAlu, U_SOff, !U_SLit, Hc. cbn [zalu_raw].
pose proof (jbrute (fun c => jdigit c || Bool.eqb (zcanon (zcanon (Z.land (zcanon (c + 0)) (zcanon 223)) + zcanon (-71)) <? zcanon 18446744073709551610) (negb (jhexd c)))
  ltac:(vm_compute; reflexivity) c Hr) as X.
cbv beta in X. rewrite Hd in X. cbn [orb] in X. apply Bool.eqb_prop in X. exact X.
Qed.
Lemma Lbr_eq_lit : forall E (nn : nat) x z, bv_unsigned (ew E nn) = x -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff nn 0)) (sv_denot E (SLit z)) = (x =? z).
Proof.
intros E nn x z Hx Hz. rewrite branch_eq_U, U_SOff, U_SLit, Hx, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 (ew E nn)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
rewrite !zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Lemma Lbr_ne_lit : forall E (nn : nat) x z, bv_unsigned (ew E nn) = x -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff nn 0)) (sv_denot E (SLit z)) = negb (x =? z).
Proof.
intros E nn x z Hx Hz. rewrite branch_ne_U, U_SOff, U_SLit, Hx, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 (ew E nn)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
rewrite !zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Lemma Lbr_ltu_lit : forall E (nn : nat) x z, bv_unsigned (ew E nn) = x -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SOff nn 0)) (sv_denot E (SLit z)) = (x <? z).
Proof.
intros E nn x z Hx Hz. rewrite branch_ltu_U, U_SOff, U_SLit, Hx, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 (ew E nn)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
rewrite !zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Lemma Lbr_geu_off : forall E (na nb : nat) xa xb c, bv_unsigned (ew E na) = xa -> bv_unsigned (ew E nb) = xb ->
  0 <= xa + c < 2 ^ 64 ->
  branch_taken BC_GEU (sv_denot E (SOff na c)) (sv_denot E (SOff nb 0)) = negb (xa + c <? xb).
Proof.
intros E na nb xa xb c Ha Hb Hr. rewrite branch_geu_U, !U_SOff, Ha, Hb, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 (ew E nb)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
rewrite !zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Lemma Lbr_ltu_sub : forall E (na nb : nat) xa xb c z, bv_unsigned (ew E na) = xa -> bv_unsigned (ew E nb) = xb ->
  0 <= xa - (xb + c) < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD (SOff na 0) (SMd M_MUL (SOff nb c) (SLit (-1))))) (sv_denot E (SLit z))
  = (xa - (xb + c) <? z).
Proof.
intros E na nb xa xb c z Ha Hb Hr Hz. rewrite branch_ltu_U, U_SAlu, U_SMd, !U_SOff, !U_SLit, Ha, Hb. cbn [zalu_raw zmd_raw].
rewrite (zcanon_id z) by (unfold M64; lia). f_equal. unfold zcanon, M64. rewrite Z.add_0_r, <- Zmult_mod, <- Zplus_mod.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma Lbr_ltu_sub2 : forall E (na nb : nat) xa xb d z, bv_unsigned (ew E na) = xa -> bv_unsigned (ew E nb) = xb ->
  0 <= xb - xa + d < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff na 0) (SLit (-1))) (SLit d)) (SOff nb 0))) (sv_denot E (SLit z))
  = (xb - xa + d <? z).
Proof.
intros E na nb xa xb d z Ha Hb Hr Hz. rewrite branch_ltu_U, !U_SAlu, U_SMd, !U_SOff, !U_SLit, Ha, Hb. cbn [zalu_raw zmd_raw].
rewrite (zcanon_id z) by (unfold M64; lia). f_equal. unfold zcanon, M64. rewrite !Z.add_0_r.
rewrite <- (Zmult_mod xa (-1)), <- (Zplus_mod (xa * -1) d), <- (Zplus_mod (xa * -1 + d) xb). rewrite Z.mod_small by lia. lia.
Qed.
Lemma Lbr_eq0 : forall E (nn : nat) (w : word), ew E nn = w ->
  (branch_taken BC_EQ (sv_denot E (SOff nn 0)) (sv_denot E (SLit 0)) = true <-> w = w64 0).
Proof.
intros E nn w Hw. rewrite branch_eq_U, U_SOff, U_SLit, Hw, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 w) as R. change (bv_modulus 64) with (2 ^ 64) in R.
rewrite !zcanon_id by (unfold M64; lia). rewrite Z.eqb_eq. unfold w64. split; intros H.
- apply bv_eq. rewrite H, unsigned_lit_small by lia. reflexivity.
- rewrite H. apply unsigned_lit_small. lia.
Qed.
Lemma jlen_BZ : jlen BZ = n.
Proof. unfold jlen, BZ. cbv beta. rewrite length_map. exact HLn. Qed.
Definition jwin_ok (r : YP09.region) : bool :=
  (YP09.r_whi r <=? YP09.r_wlo r) ||
  (match YP09.r_base r with Some 2%nat => true | _ => false end && (0 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 128)).
Lemma jwin_std : forall Eh rs, forallb jwin_ok rs = true -> bv_unsigned (ew Eh 2) = spZ regs0 - 128 ->
  forall a, in_wrange Eh rs a -> spZ regs0 - TJSON_SCALAR_STK <= a < spZ regs0.
Proof.
intros Eh rs Hok H2 a (r & Hin & Ha). rewrite forallb_forall in Hok. specialize (Hok r Hin).
unfold jwin_ok in Hok. assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
destruct (YP09.r_whi r <=? YP09.r_wlo r) eqn:Hw; [apply Z.leb_le in Hw; lia|]. cbn [orb] in Hok.
destruct (YP09.r_base r) as [[|[|[|nb]]]|]; cbn in Hok; try discriminate.
apply andb_prop in Hok as [H0 H1]. apply Z.leb_le in H0, H1. cbn [base_val] in Ha. rewrite H2 in Ha. lia.
Qed.
Lemma jawr_std : forall Eh rs, forallb jwin_ok rs = true -> bv_unsigned (ew Eh 2) = spZ regs0 - 128 ->
  awr_ok Eh rs STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own.
Proof.
intros Eh rs Hok H2 a Ha. pose proof (jwin_std Eh rs Hok H2 a Ha). left. lia.
Qed.
Lemma jkeep_run : forall Eh rs M M', forallb jwin_ok rs = true -> bv_unsigned (ew Eh 2) = spZ regs0 - 128 ->
  frame_of Eh rs (mrestrict (w_H W) M) (mrestrict (w_H W) M') -> JKEEP M -> JKEEP M'.
Proof. intros Eh rs M M' Hok H2 HF HK. exact (jkeep_of Eh rs M M' HF (jwin_std Eh rs Hok H2) HK). Qed.
Lemma jkeep_call : forall (memT mem2 : word -> option byte), JKEEP memT ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs0 - 128 - ESTACK <= a < spZ regs0 - 128) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) -> JKEEP mem2.
Proof.
intros memT mem2 HK Hf a Ha Hn. assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity. rewrite Hf by lia. apply HK; assumption.
Qed.
Let Hbra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF b n := jh_Hbra.
Lemma jobl : forall Eh (M : word -> option byte) j0 t, JKEEP M ->
  bv_unsigned (ew Eh 9) = SHADOW_OFF -> bv_unsigned (ew Eh 45) = b + j0 -> 0 <= j0 -> 0 <= t -> j0 + t < n ->
  range_addressable (rd_of SEGS (mrestrict (w_H W) M)) (U Eh (SOff 9 0)) (U Eh (SOff 45 t)) 1.
Proof.
intros Eh M j0 t HK H9 H45 Hj0 Ht Hjt. pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite !U_SOff, H9, H45, !zcanon_id by (unfold M64, SHADOW_OFF; lia). rewrite Z.add_0_r.
change (rd_of SEGS (mrestrict (w_H W) M)) with (aview SEGS (w_H W) M).
apply (range_addressable_kept_win (aview SEGS (w_H W) memc) (aview SEGS (w_H W) M) (spZ regs0 - TJSON_SCALAR_STK) (spZ regs0));
  [intros s Hs Hn; apply HK; assumption | lia | lia | lia |].
apply (range_addressable_sub _ _ b n); [exact Hbra | lia | lia].
Qed.
Lemma jkept_region : forall Eh (memT mem2 : word -> option byte) (nb : nat) base lo hi wlo whi cs,
  bv_unsigned (ew Eh nb) = base ->
  (forall a, base + lo <= a < base + hi -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs0 - 128 - ESTACK <= a < spZ regs0 - 128)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs0 - 128 - ESTACK <= a < spZ regs0 - 128) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) ->
  (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
  region_kept SEGS Eh (mrestrict (w_H W) memT) (mrestrict (w_H W) mem2) (YP09.mkRegion (Some nb) lo hi wlo whi cs).
Proof.
intros Eh memT mem2 nb base lo hi wlo whi cs Hb Hin Hf Hp.
apply (region_kept_aview Eh (w_H W) memT mem2 nb base lo hi wlo whi cs Hb); [|exact Hp].
intros a Ha. destruct (Hin a Ha). apply Hf; assumption.
Qed.
Lemma jesc_true : forall c, ~ (jesc c = false /\ c <> 0) -> c <> 0 -> jesc c = true.
Proof. intros c H1 H2. destruct (jesc c) eqn:E; [reflexivity|]. exfalso. apply H1. split; [reflexivity | exact H2]. Qed.
Definition JEPI_K Q : Prop := forall R M md r,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W M md k ->
  getr R 2 = w64 (spZ regs0 - 128) -> getr R 3 = getr regs0 3 -> getr R 4 = getr regs0 4 ->
  getr R 10 = w64 r -> 0 <= r < 2 ^ 64 ->
  JSLOTS M -> JPRES M -> JRES M r ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + JS_EPI)) M (seg_rom SEGS)) md) Q.
Definition JNPRE (R : bvmap 5 word) (M : word -> option byte) (md : Model) : Prop :=
  JINV R M md /\ getr R 18 = w64 (b + i) /\ getr R 15 = w64 i /\ getr R 16 = w64 v.
Definition jtail (j2 : Z) : option jtok :=
  match jexp BZ j2 with Some j3 => Some (j3, 2, i, j3 - i) | None => None end.
Definition jtail1 (j1 : Z) : option jtok :=
  match jfrac BZ j1 with Some j2 => jtail j2 | None => None end.
Definition JS_LD1 : Z := 0x3414.
Definition JS_CFRAC : Z := 0x3270.
Definition JS_LD2 : Z := 0x32c0.
Definition JS_CEXP : Z := 0x3354.
Definition JS_LD3 : Z := 0x33d8.
Definition JS_CST : Z := 0x3454.
Definition JM10 : Z := 18446744073709551606.
Definition js_C_store_spec : Prop := forall Q, JEPI_K Q -> forall R M md j3,
  JNPRE R M md -> getr R 10 = w64 j3 -> 0 <= i <= j3 -> j3 <= n ->
  jscalar BZ i = Some (j3, 2, i, j3 - i) ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + JS_CST)) M (seg_rom SEGS)) md) Q.
Definition js_L_d3_spec : Prop := forall Q, JEPI_K Q -> forall R M md j f,
  JNPRE R M md -> getr R 12 = w64 j -> getr R 11 = w64 JM10 -> 0 <= i <= j -> j < n -> n - j < Z.of_nat f ->
  jscalar BZ i = Some (jdigits BZ j f, 2, i, jdigits BZ j f - i) ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + JS_LD3)) M (seg_rom SEGS)) md) Q.
Definition js_C_exp_spec : Prop := forall Q, JEPI_K Q -> forall R M md j2,
  JNPRE R M md -> getr R 10 = w64 j2 -> 0 <= i <= j2 -> j2 <= n ->
  jscalar BZ i = jtail j2 ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + JS_CEXP)) M (seg_rom SEGS)) md) Q.
Definition js_L_d2_spec : Prop := forall Q, JEPI_K Q -> forall R M md j f,
  JNPRE R M md -> getr R 10 = w64 j -> getr R 12 = w64 JM10 -> 0 <= i <= j -> j < n -> n - j < Z.of_nat f ->
  jscalar BZ i = jtail (jdigits BZ j f) ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + JS_LD2)) M (seg_rom SEGS)) md) Q.
Definition js_C_frac_spec : Prop := forall Q, JEPI_K Q -> forall R M md j1,
  JNPRE R M md -> getr R 10 = w64 j1 -> 0 <= i <= j1 -> j1 <= n ->
  jscalar BZ i = jtail1 j1 ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + JS_CFRAC)) M (seg_rom SEGS)) md) Q.
Definition js_L_d1_spec : Prop := forall Q, JEPI_K Q -> forall R M md j f,
  JNPRE R M md -> getr R 10 = w64 j -> getr R 12 = w64 JM10 -> 0 <= i <= j -> j < n -> n - j < Z.of_nat f ->
  jscalar BZ i = jtail1 (jdigits BZ j f) ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + JS_LD1)) M (seg_rom SEGS)) md) Q.
Definition js_C_store_stmt : Prop := js_C_store_spec.
Definition js_L_d3_stmt : Prop := js_C_store_spec -> js_L_d3_spec.
Definition js_C_exp_stmt : Prop := js_L_d3_spec -> js_C_store_spec -> js_C_exp_spec.
Definition js_L_d2_stmt : Prop := js_C_exp_spec -> js_C_store_spec -> js_L_d2_spec.
Definition js_C_frac_stmt : Prop := js_L_d2_spec -> js_C_exp_spec -> js_C_frac_spec.
Definition js_L_d1_stmt : Prop := js_C_frac_spec -> js_C_store_spec -> js_L_d1_spec.
Definition JS_NUMENT : Z := 0x3178.
Definition JSLOTS2 (M : word -> option byte) : Prop := (fun _ =>
  val_mem SEGS (mrestrict (w_H W) M) (spZ regs0 - 128 + 8) 8 v /\
  val_mem SEGS (mrestrict (w_H W) M) (spZ regs0 - 128 + 16) 8 i) JHI.
Definition js_nument_spec : Prop := forall Q, JEPI_K Q -> forall R M md,
  JINV R M md -> JSLOTS2 M -> getr R 18 = w64 (b + i) -> getr R 8 = w64 (SHADOW_OFF + (b + i) / 8) ->
  0 <= i < n -> jscalar BZ i = jnum BZ i ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + JS_NUMENT)) M (seg_rom SEGS)) md) Q.
Definition js_nument_stmt : Prop := js_L_d1_spec -> js_C_frac_spec -> js_nument_spec.
End J.
End h.
End f.
End d.
Ltac jconv Hc :=
  let jU := idtac; lazymatch goal with AGx : forall kk, (kk < 512)%nat -> ew _ kk = ew _ kk |- _ => first [eassumption | rewrite AGx by lia; eassumption] end in
  let jR := idtac; first [lia | lazymatch goal with Hz : forall t, _ -> 0 <= jbyte _ t < 256 |- _ => apply Hz; lia end] in
  lazymatch type of Hc with
  | branch_taken BC_EQ (sv_denot ?Ex (SOff ?nn 0)) (sv_denot _ (SLit 0)) = ?bb =>
    lazymatch goal with
    | MW : ew Ex nn = ?w, HRm : (?w = w64 0 <-> ?P) |- _ =>
      lazymatch bb with
      | true => let Hm := fresh "Hm" in pose proof (proj1 HRm (proj1 (Lbr_eq0 Ex nn w MW) Hc)) as Hm; destruct Hm
      | false => let Hm := fresh "Hm" in
        assert (Hm : ~ P) by (let X := fresh in intros X; apply (proj2 HRm) in X; apply (proj2 (Lbr_eq0 Ex nn w MW)) in X;
          rewrite X in Hc; discriminate Hc)
      end; clear Hc
    | _ => rewrite (Lbr_eq_lit Ex nn _ 0 ltac:(jU) ltac:(lia)) in Hc
    end
  | branch_taken BC_EQ (sv_denot ?Ex (SOff ?nn 0)) (sv_denot _ (SLit ?z)) = _ =>
    rewrite (Lbr_eq_lit Ex nn _ z ltac:(jU) ltac:(lia)) in Hc
  | branch_taken BC_NE (sv_denot ?Ex (SOff ?nn 0)) (sv_denot _ (SLit ?z)) = _ =>
    rewrite (Lbr_ne_lit Ex nn _ z ltac:(jU) ltac:(lia)) in Hc
  | branch_taken BC_LTU (sv_denot ?Ex (SOff ?nn 0)) (sv_denot _ (SLit ?z)) = _ =>
    rewrite (Lbr_ltu_lit Ex nn _ z ltac:(jU) ltac:(lia)) in Hc
  | branch_taken BC_GEU (sv_denot ?Ex (SOff ?na ?c)) (sv_denot _ (SOff ?nb 0)) = _ =>
    rewrite (Lbr_geu_off Ex na nb _ _ c ltac:(jU) ltac:(jU) ltac:(lia)) in Hc
  | branch_taken BC_LTU (sv_denot ?Ex (SAlu ALU_ADD (SOff ?na 0) (SMd M_MUL (SOff ?nb ?c) (SLit (-1))))) (sv_denot _ (SLit ?z)) = _ =>
    rewrite (Lbr_ltu_sub Ex na nb _ _ c z ltac:(jU) ltac:(jU) ltac:(lia) ltac:(lia)) in Hc
  | branch_taken BC_LTU (sv_denot ?Ex (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff ?na 0) (SLit (-1))) (SLit ?d)) (SOff ?nb 0))) (sv_denot _ (SLit ?z)) = _ =>
    rewrite (Lbr_ltu_sub2 Ex na nb _ _ d z ltac:(jU) ltac:(jU) ltac:(lia) ltac:(lia)) in Hc
  | branch_taken BC_LTU (sv_denot ?Ex (SLit 18446744073709551605)) (sv_denot _ (SOff ?nn (-58))) = _ =>
    rewrite (Lbr_dig Ex nn _ ltac:(jU) ltac:(jR)) in Hc
  | branch_taken BC_LTU (sv_denot ?Ex (SAlu ALU_ADD (SAlu ALU_AND (SOff ?nn 0) (SLit 223)) (SLit (-71)))) (sv_denot _ (SLit 18446744073709551610)) = _ =>
    rewrite (Lbr_hex Ex nn _ ltac:(jU) ltac:(jR) ltac:(assumption)) in Hc
  end;
  try (rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in Hc);
  try (rewrite ?Z.eqb_eq, ?Z.eqb_neq, ?Z.ltb_lt, ?Z.ltb_ge in Hc);
  try (let BF := fresh "BF" in rename Hc into BF);
  repeat match goal with
  | H1 : ~ (jesc ?x = false /\ ?x <> 0), H2 : ?x <> 0 |- _ => pose proof (jesc_true x H1 H2); clear H1
  end.
