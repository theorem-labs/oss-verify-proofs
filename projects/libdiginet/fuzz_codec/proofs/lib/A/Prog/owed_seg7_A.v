(* owed_seg7 at image A 0x8438c (84 instructions, real frame 16, no call): it walks the 29 entries of the
   glyph table at 0x9d6e0 (a character and a pointer to its segment string) and folds the segment string of
   the entry that matches the character in a0.
   The walk carries the table's bytes and the strings' bytes as regions of the image's own bytes, and
   their shadow bytes as regions based at the shadow-offset atom (lib/A/Prog/CPgWalkImg.v). With those,
   every instrumented check of this function is decided by the run itself: no token, no obligation
   (measured: the run reaches the first undecided branch at 0x843e0 with 0 obligations and 0 tokens).
   The 29 entries are unrolled: the table is read at a constant address in each of them, so the run
   decides every address of the table and of the strings, and the only undecided branches are the two
   tests of the entry's character against a0 (the second one only for an entry whose character is a
   letter other than H and h). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm AF0m.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CodecRo CodecGlobs CPgWalk CPgWalkImg CPgWalkRo CPgChkC.
(* Required, not Imported: lib/Spec/DgnLib.v has a name st_ok of its own *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.libdiginet.fuzz_codec.images Require Import Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition A_OWED_SEG7 : Z := 0x8438c.
(* the 27 distinct segment strings the glyph table points at, each with its size including the 0
   (rows of lib/A/Prog/CodecGlobs.v CODEC_GLOBS; the pointers are the table's own, read from the image) *)
Definition SEG7_STRS : list (Z * Z) :=
  [(0x20fe0, 1); (0x21000, 7); (0x21020, 3); (0x21040, 6); (0x21060, 6); (0x21080, 5); (0x210a0, 6);
   (0x210c0, 7); (0x210e0, 4); (0x21100, 8); (0x21120, 7); (0x21140, 7); (0x21160, 6); (0x21180, 5);
   (0x211a0, 6); (0x211c0, 6); (0x211e0, 5); (0x21200, 6); (0x21220, 5); (0x21240, 5); (0x21260, 4);
   (0x21280, 5); (0x212a0, 6); (0x212c0, 3); (0x212e0, 6); (0x21300, 6); (0x21320, 2)].
Definition SEG7_TBL : list (Z * Z) := (CA_GLYPH, 464) :: SEG7_STRS.
(* The four regions of the table: the glyph table's own bytes and their shadow bytes, and the bytes of
   the 27 strings and their shadow bytes. The strings lie in one span with guard bytes between them, so
   one region holds all of them, with a chunk per string: a region's chunks need not cover it. *)
Definition SEG7_STR_LO : Z := 0x20fe0.
Definition SEG7_STR_HI : Z := 0x21322.
Definition seg7_str_img : YP09.region :=
  YP09.mkRegion None SEG7_STR_LO SEG7_STR_HI 0 0
    (map (fun r => YP09.mkChunk (fst r) (CImg (snd r))) SEG7_STRS).
(* the granules of that span: 0x20fe0 / 8 .. 0x21322 / 8 *)
Definition SEG7_STR_SLO : Z := 0x41fc.
Definition SEG7_STR_SHI : Z := 0x4265.
Definition seg7_str_shadow : YP09.region :=
  YP09.mkRegion (Some 32%nat) SEG7_STR_SLO SEG7_STR_SHI 0 0
    (map (fun r => YP09.mkChunk (fst r / 8) (CVal 1 (SLit (snd r mod 8)))) SEG7_STRS).
Definition seg7_rs : smem :=
  [cpg_img_region CA_GLYPH 464; cpg_shadow_region CA_GLYPH 464; seg7_str_img; seg7_str_shadow].
Definition seg7_af : list (nat * afact) := [(10%nat, mkAF 0 255 0)].
Definition ss_seg7 : sstate :=
  mkSS A_OWED_SEG7 sr_atoms (cw_regs 16 ++ seg7_rs) None (mkFacts (cw_atoms ++ seg7_af) [] []).

(* ================================ the model side ================================
   The characters and the segment strings of the table, and the machine's own test of an entry's
   character g against the character c in a0: the two tests the run leaves undecided, with the two
   concrete tests of g the run decides itself. The text of seg7_hit and of the three lemmas below is the
   plain walk's (lib/Prog/owed_seg7.v on the plain and ubsan branch), with the plain image's test in the
   form image A states it. *)
Definition g_chr : list Z := Eval vm_compute in map fst glyph.
Definition g_str : list (list Z) := Eval vm_compute in map snd glyph.
Definition seg7_hit (g c : Z) : bool :=
  (c =? g) || (negb (Z.lor g 32 =? 104) && ((Z.land g 223 - 65) mod 256 <=? 25)
               && (Z.land (Z.lxor c g) 223 =? 0)).
Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).
Lemma seg7_hit_check :
  forallb (fun g => forallb (fun c => Bool.eqb (seg7_hit g c) (glyph_match g c)) (zseq 256)) g_chr = true.
Proof. vm_compute. reflexivity. Qed.
Lemma seg7_hit_ok : forall g c, In g g_chr -> 0 <= c < 256 -> seg7_hit g c = glyph_match g c.
Proof.
intros g c Hg Hc. pose proof (proj1 (forallb_forall _ _) seg7_hit_check g Hg) as H. cbn beta in H.
assert (Hin : In c (zseq 256)).
{ unfold zseq. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. }
pose proof (proj1 (forallb_forall _ _) H c Hin) as H'. cbn beta in H'. apply Bool.eqb_prop in H'. exact H'.
Qed.
(* an entry's test is met only by the entry's character and, for a letter, by its other case *)
Lemma seg7_fold_check :
  forallb (fun g => forallb (fun c => implb (Z.land (Z.lxor c g) 223 =? 0) ((c =? g) || (c =? Z.lxor g 32)))
                            (zseq 256)) g_chr = true.
Proof. vm_compute. reflexivity. Qed.
Lemma seg7_fold_val : forall g c, In g g_chr -> 0 <= c < 256 -> Z.land (Z.lxor c g) 223 = 0 ->
  c = g \/ c = Z.lxor g 32.
Proof.
intros g c Hg Hc H. pose proof (proj1 (forallb_forall _ _) seg7_fold_check g Hg) as HA. cbn beta in HA.
assert (Hin : In c (zseq 256)).
{ unfold zseq. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. }
pose proof (proj1 (forallb_forall _ _) HA c Hin) as H'. cbn beta in H'.
rewrite (proj2 (Z.eqb_eq _ _) H) in H'. cbn [implb] in H'.
apply orb_prop in H' as [H'|H']; [left | right]; apply Z.eqb_eq; exact H'.
Qed.


(* a fact lia must not see: the walk's accumulated tests c <> g would make every lia of a later run
   split on each of them (a 2^k search); they are kept under this name until the last leaf *)
Definition s7_hold (P : Prop) : Prop := P.
Lemma s7_hide : forall P : Prop, P -> s7_hold P.
Proof. intros P H. exact H. Qed.

(* the engine's value of the case-folding test (c xor g) & 223 *)
Lemma seg7_U_fold : forall E n cv g, ew E n = Z_to_bv 64 cv -> 0 <= cv < 256 -> 0 <= g < 256 ->
  U E (SAlu ALU_AND (SAlu ALU_XOR (SOff n 0) (SLit g)) (SLit 223)) = Z.land (Z.lxor cv g) 223.
Proof.
intros E n cv g Hn Hc Hg. rewrite U_and_lit by lia. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n cv Hn ltac:(lia)), (U_lit E g ltac:(lia)).
apply zcanon_id. unfold M64. apply Z_lxor_range; lia.
Qed.
(* membership of a concrete character in the table *)
Ltac seg7_in_chr := unfold g_chr; cbn [In]; repeat (first [left; reflexivity | right]).
(* no entry matches: the walk returns -1 *)
Lemma seg7_go_miss : forall gs c, (forall p, In p gs -> glyph_match (fst p) c = false) ->
  owed_seg7_go gs c = -1.
Proof.
induction gs as [|[g s] gs IH]; intros c H; cbn [owed_seg7_go]; [reflexivity|].
pose proof (H (g, s) (or_introl eq_refl)) as Hg. cbn [fst] in Hg. rewrite Hg.
apply IH. intros p Hp. apply H. right. exact Hp.
Qed.

(* every run of the engine leaves the model as with_vm_backing (m_vm_lazy md) mat md, which holds the
   previous model twice; srr_norm_model collapses it in the goal only, so the journal's copy would
   double with each run. This collapses it everywhere after each run. *)
Ltac s7_norm := repeat (rewrite wvb_collapse in * ).

(* no entry of the table matches c: owed_seg7 returns -1 *)
Lemma seg7_miss_all : forall c, 0 <= c < 256 ->
  c <> 48 ->
  c <> 49 ->
  c <> 50 ->
  c <> 51 ->
  c <> 52 ->
  c <> 53 ->
  c <> 54 ->
  c <> 55 ->
  c <> 56 ->
  c <> 57 ->
  c <> 65 ->
  c <> 98 ->
  c <> 67 ->
  c <> 100 ->
  c <> 69 ->
  c <> 70 ->
  c <> 72 ->
  c <> 104 ->
  c <> 74 ->
  c <> 76 ->
  c <> 111 ->
  c <> 80 ->
  c <> 114 ->
  c <> 83 ->
  c <> 85 ->
  c <> 89 ->
  c <> 90 ->
  c <> 45 ->
  c <> 32 ->
  Z.land (Z.lxor c 65) 223 <> 0 ->
  Z.land (Z.lxor c 98) 223 <> 0 ->
  Z.land (Z.lxor c 67) 223 <> 0 ->
  Z.land (Z.lxor c 100) 223 <> 0 ->
  Z.land (Z.lxor c 69) 223 <> 0 ->
  Z.land (Z.lxor c 70) 223 <> 0 ->
  Z.land (Z.lxor c 74) 223 <> 0 ->
  Z.land (Z.lxor c 76) 223 <> 0 ->
  Z.land (Z.lxor c 111) 223 <> 0 ->
  Z.land (Z.lxor c 80) 223 <> 0 ->
  Z.land (Z.lxor c 114) 223 <> 0 ->
  Z.land (Z.lxor c 83) 223 <> 0 ->
  Z.land (Z.lxor c 85) 223 <> 0 ->
  Z.land (Z.lxor c 89) 223 <> 0 ->
  Z.land (Z.lxor c 90) 223 <> 0 ->
  owed_seg7_spec c = -1.
Proof.
intros c Hc. intros. unfold owed_seg7_spec. apply seg7_go_miss. intros p Hp.
unfold glyph in Hp.
repeat (destruct Hp as [<- | Hp];
  [cbn [fst];
   lazymatch goal with |- glyph_match ?g _ = false =>
     rewrite <- (seg7_hit_ok g c ltac:(seg7_in_chr) Hc) end; unfold seg7_hit;
   apply orb_false_intro;
   [apply Z.eqb_neq; assumption
   | first [vm_compute; reflexivity | apply andb_false_intro2; apply Z.eqb_neq; assumption]] |]).
all: try (destruct Hp).
Qed.

(* ================================ the walk ================================ *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis HB : TfibSyms B.
(* the start-up certificate that the memory-checking runtime marked each registered global *)
Hypothesis HGLOB : globs_marked tfibsegs B CODEC_GLOBS.

(* the glyph table and the segment strings are bytes of the image, not of the runtime's own memory *)
Lemma seg7_rows_free : cpw_rows_free B SEG7_TBL.
Proof. apply (cpw_rows_free_of_off B SEG7_TBL HB). vm_compute. reflexivity. Qed.
Lemma seg7_row_free : forall q n a, In (q, n) SEG7_TBL -> q <= a < q + n ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros q n a Hin Ha.
pose proof (cpw_rows_free_In B SEG7_TBL q n (a - q) seg7_rows_free Hin ltac:(cbn [snd]; lia)) as H.
cbn [fst] in H. replace (q + (a - q)) with a in H by lia. exact H.
Qed.
(* the segment strings are in the image's first read-only part, the glyph table in the read window *)
Lemma seg7_in_ro : forall a, 0x20fe0 <= a < 0x21322 \/ CA_GLYPH <= a < CA_GLYPH + 464 ->
  in_roP tfibsegs CA_RLO CA_RHI a.
Proof.
intros a [Ha|Ha]; [left | right; unfold CA_RLO, CA_RHI, CA_GLYPH in *; lia].
exists Asan.Asan_segment_000. split; [left; reflexivity|]. split; [vm_compute; reflexivity|].
let b := eval vm_compute in (Z.of_N (seg_base Asan.Asan_segment_000)) in
let z := eval vm_compute in (Z.of_N (seg_size Asan.Asan_segment_000)) in
change (b <= a < b + z); lia.
Qed.
(* every row of the table lies in the read-only data, the image file holds it, and it is a row of the
   registered globals (so its shadow bytes are the start-up certificate's) *)
Lemma seg7_rows_ro : Forall (fun r => forall i, 0 <= i < snd r -> in_roP tfibsegs CA_RLO CA_RHI (fst r + i))
  SEG7_TBL.
Proof.
apply Forall_forall. intros r Hr i Hi. apply seg7_in_ro.
unfold SEG7_TBL, SEG7_STRS, CA_GLYPH in *.
repeat (destruct Hr as [<- | Hr]; [cbn [fst snd] in Hi |- *; lia|]). destruct Hr.
Qed.
Lemma seg7_rows_some : Forall (fun r => cpg_img_some (fst r) (snd r) = true) SEG7_TBL.
Proof.
unfold SEG7_TBL, SEG7_STRS. repeat (apply Forall_cons; [vm_compute; reflexivity|]). apply Forall_nil.
Qed.
Lemma seg7_rows_globs : Forall (fun r => In r CODEC_GLOBS) SEG7_TBL.
Proof.
unfold SEG7_TBL, SEG7_STRS.
repeat (apply Forall_cons; [apply globs_In_b; vm_compute; reflexivity|]). apply Forall_nil.
Qed.
Lemma seg7_rows_range : Forall (fun r => 0 < fst r /\ 0 < snd r /\ fst r + snd r <= 2 ^ 63) SEG7_TBL.
Proof.
unfold SEG7_TBL, SEG7_STRS, CA_GLYPH.
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
Qed.

Lemma seg7_entry_ok : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world tfibsegs) memc mdc k regs c,
cdc_entry tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_owed_seg7 ->
getr regs 10 = w64 c -> 0 <= c < 256 ->
arodata_okP tfibsegs CA_RLO CA_RHI B (aview tfibsegs (w_H W) memc) ->
st_ok tfibsegs (Ereg regs (cw_extra []))
  ss_seg7 (restrict (w_H W) (mkst regs (Z_to_bv 64 A_OWED_SEG7) memc (seg_rom tfibsegs))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c HE H10 Hc HRO.
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_owed_seg7 HE
  ltac:(unfold T_owed_seg7; lia)) as (Hceil & H47 & H46 & Hal & Hpres).
pose proof HE as ((HAR & _) & _).
unfold T_owed_seg7 in *.
set (E := Ereg regs (cw_extra [])).
assert (E2 : ew E 2 = getr regs 2) by (subst E; apply (cw_ew_reg regs [] 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E10 : ew E 10 = Z_to_bv 64 c)
  by (subst E; rewrite (cw_ew_reg regs [] 10 10%bv eq_refl); rewrite H10; reflexivity).
assert (U2 : bv_unsigned (ew (Ereg regs (cw_extra [])) 2) = spZ regs)
  by (rewrite (cw_ew_reg regs [] 2 2%bv eq_refl); reflexivity).
assert (U32 : bv_unsigned (ew (Ereg regs (cw_extra [])) 32) = SB)
  by (rewrite (cw_ew_SB regs []); apply unsigned_lit_small; unfold SB; lia).
assert (U10e : ew (Ereg regs (cw_extra [])) 10 = Z_to_bv 64 c)
  by (rewrite (cw_ew_reg regs [] 10 10%bv eq_refl); exact H10).
(* the four regions of the table: the glyph table, the strings, and the shadow bytes of each. The two
   chunk facts come from the one-row regions of lib/A/Prog/CPgWalkImg.v. *)
assert (HCHI : forall q n, In (q, n) SEG7_TBL ->
  YP09.chunk_ok tfibsegs E (mrestrict (w_H W) memc) 0 (YP09.mkChunk q (CImg n))).
{ intros q n Hin.
  pose proof (proj1 (Forall_forall _ _) seg7_rows_ro (q, n) Hin) as HRO1. cbn [fst snd] in HRO1.
  pose proof (proj1 (Forall_forall _ _) seg7_rows_some (q, n) Hin) as HS1. cbn [fst snd] in HS1.
  pose proof (proj1 (Forall_forall _ _) seg7_rows_range (q, n) Hin) as (Hq & Hn & Hqn).
  cbn [fst snd] in Hq, Hn, Hqn.
  assert (HR : region_ok tfibsegs E (mrestrict (w_H W) memc) (cpg_img_region q n)).
  { apply (cpg_img_region_ok B CA_RLO CA_RHI E W memc);
    [ exact HRO
    | intros a Ha; replace a with (q + (a - q)) by lia; apply HRO1; lia
    | intros a Ha; exact (proj1 (seg7_row_free q n a Hin Ha))
    | intros a Ha; exact (proj2 (seg7_row_free q n a Hin Ha))
    | exact HS1 | lia | lia | lia ]. }
  destruct HR as (_ & _ & _ & HF). unfold cpg_img_region in HF.
  cbn [YP09.r_chunks YP09.r_base base_val] in HF. inversion HF as [|x l HC _]. exact HC. }
assert (HCHS : forall q n, In (q, n) SEG7_TBL -> 0 < n <= 8 ->
  YP09.chunk_ok tfibsegs E (mrestrict (w_H W) memc) SB (YP09.mkChunk (q / 8) (CVal 1 (SLit (n mod 8))))).
{ intros q n Hin Hn8.
  pose proof (proj1 (Forall_forall _ _) seg7_rows_globs (q, n) Hin) as HG1.
  pose proof (proj1 (Forall_forall _ _) seg7_rows_range (q, n) Hin) as (Hq & Hn & Hqn).
  cbn [fst snd] in Hq, Hn, Hqn.
  assert (HR : region_ok tfibsegs E (mrestrict (w_H W) memc) (cpg_shadow_region q n)).
  { apply (cpg_shadow_region_ok B E W memc lyc Sc mdc CODEC_GLOBS);
    [exact HGLOB | exact HG1 | exact HAR | exact E32 | lia | lia]. }
  destruct HR as (_ & _ & _ & HF). unfold cpg_shadow_region in HF.
  cbn [YP09.r_chunks YP09.r_base base_val] in HF. rewrite E32 in HF.
  rewrite unsigned_lit_small in HF by (unfold SB; lia).
  assert (Hcase : n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8) by lia.
  destruct Hcase as [Hn1|[Hn1|[Hn1|[Hn1|[Hn1|[Hn1|[Hn1|Hn1]]]]]]]; subst n;
  cbn [cpg_sh_chunks] in HF; inversion HF as [|x l HC _];
  try (replace (q / 8 + 0) with (q / 8) in HC by lia); exact HC. }
assert (HRS : Forall (region_ok tfibsegs E (mrestrict (w_H W) memc)) seg7_rs).
{ unfold seg7_rs. repeat apply Forall_cons; try apply Forall_nil.
  - (* the glyph table's bytes *)
    apply (cpg_img_region_ok B CA_RLO CA_RHI E W memc);
    [ exact HRO
    | intros a Ha; replace a with (CA_GLYPH + (a - CA_GLYPH)) by lia;
      apply (proj1 (Forall_forall _ _) seg7_rows_ro (CA_GLYPH, 464) ltac:(left; reflexivity)); cbn [snd]; lia
    | intros a Ha; exact (proj1 (seg7_row_free CA_GLYPH 464 a ltac:(left; reflexivity) Ha))
    | intros a Ha; exact (proj2 (seg7_row_free CA_GLYPH 464 a ltac:(left; reflexivity) Ha))
    | vm_compute; reflexivity | unfold CA_GLYPH; lia | lia | unfold CA_GLYPH; lia ].
  - (* its shadow bytes *)
    apply (cpg_shadow_region_ok B E W memc lyc Sc mdc CODEC_GLOBS);
    [exact HGLOB | apply globs_In_b; vm_compute; reflexivity | exact HAR | exact E32
     | unfold CA_GLYPH; lia | unfold CA_GLYPH; lia].
  - (* the strings' bytes *)
    unfold seg7_str_img, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold SEG7_STR_LO; lia|]. split; [unfold SEG7_STR_HI; lia|].
    split; [intros o Ho; lia|].
    apply Forall_forall. intros ch Hch. apply in_map_iff in Hch as ((q, n) & <- & Hin). cbn [fst snd].
    apply HCHI. right. exact Hin.
  - (* the strings' shadow bytes *)
    unfold seg7_str_shadow, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32. rewrite unsigned_lit_small by (unfold SB; lia).
    split; [unfold SEG7_STR_SLO, SB; lia|].
    split; [unfold SEG7_STR_SHI, SB; lia|].
    split; [intros o Ho; lia|].
    apply Forall_forall. intros ch Hch. apply in_map_iff in Hch as ((q, n) & <- & Hin). cbn [fst snd].
    apply HCHS; [right; exact Hin|].
    unfold SEG7_STRS in Hin.
    repeat (destruct Hin as [E1 | Hin]; [injection E1 as <- <-; lia|]). destruct Hin. }
unfold ss_seg7.
apply (cw_entry B TL LAWS A_OWED_SEG7 16 [] seg7_rs seg7_af lyc Sc W regs memc mdc HAR
  ltac:(lia) ltac:(lia) Hal ltac:(intros a Ha; apply Hpres; lia)).
- vm_compute. reflexivity.
- exact HRS.
- apply pairwise_disjoint_of_extents.
  unfold seg7_rs, seg7_str_img, seg7_str_shadow, cw_regs, stack_region, got_region, bcell_region,
  cpg_img_region, cpg_shadow_region.
  cbv [extent_of_region map app zpairwise_disjoint zall_disjoint zdisj base_val
       YP09.r_base YP09.r_lo YP09.r_hi fst snd].
  rewrite !U2, !U32.
  unfold A_GOT_shadow, A_shadow_glob, CA_GLYPH, SEG7_STR_LO, SEG7_STR_HI, SEG7_STR_SLO, SEG7_STR_SHI, SB.
  change (644832 / 8) with 80604. change ((464 + 7) / 8) with 58.
  repeat split; first [exact I | lia].
- cbn [seg7_af atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U10e, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r.
  split; [split; [lia|]; split; [reflexivity | lia] | exact I].
Qed.

(* ================================ the run ================================ *)
Theorem owed_seg7_A_holds :
  cdc_owed_seg7_specX tfibsegs B MT CA_RLO CA_RHI CA_GLYPH CA_ROSTRS A_OWED_SEG7.
Proof using MTL TL LAWS ML HB HGLOB.
unfold cdc_owed_seg7_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c HE H10 Hc HIMG.
pose proof HE as HE0.
destruct HE as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
(* the run tactics take the newest journal; HJ stays the entry journal the leaf needs *)
pose proof HJ as HJRUN.
pose proof (seg7_entry_ok STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c HE0 H10 Hc
  (proj1 HIMG)) as HS.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
remember (Ereg regs (cw_extra [])) as E eqn:HEE.
assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E) by (subst E; apply env_agree_refl).
assert (E1 : ew E 1 = getr regs 1) by (subst E; apply (cw_ew_reg regs [] 1 1%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c)
  by (subst E; rewrite (cw_ew_reg regs [] 10 10%bv eq_refl); exact H10).
assert (B2 : bv_unsigned (ew E 2) = spZ regs)
  by (subst E; rewrite (cw_ew_reg regs [] 2 2%bv eq_refl); reflexivity).
clear HEE.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_owed_seg7 <= a < spZ regs) ->
  aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
unfold cfg_at. change (w64 A_OWED_SEG7) with (Z_to_bv 64 A_OWED_SEG7).
unfold T_owed_seg7 in *.
(* entry 0, the character 0x30 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb0.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 48 ltac:(lia)) in Hb0.
  apply Z.eqb_eq in Hb0.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 126 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 48 ltac:(lia)) in Hb0.
apply Z.eqb_neq in Hb0. apply s7_hide in Hb0.
(* entry 1, the character 0x31 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb1.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 49 ltac:(lia)) in Hb1.
  apply Z.eqb_eq in Hb1.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 48 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 49 ltac:(lia)) in Hb1.
apply Z.eqb_neq in Hb1. apply s7_hide in Hb1.
(* entry 2, the character 0x32 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb2.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 50 ltac:(lia)) in Hb2.
  apply Z.eqb_eq in Hb2.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 109 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 50 ltac:(lia)) in Hb2.
apply Z.eqb_neq in Hb2. apply s7_hide in Hb2.
(* entry 3, the character 0x33 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb3.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 51 ltac:(lia)) in Hb3.
  apply Z.eqb_eq in Hb3.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 121 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 51 ltac:(lia)) in Hb3.
apply Z.eqb_neq in Hb3. apply s7_hide in Hb3.
(* entry 4, the character 0x34 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb4.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 52 ltac:(lia)) in Hb4.
  apply Z.eqb_eq in Hb4.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 51 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 52 ltac:(lia)) in Hb4.
apply Z.eqb_neq in Hb4. apply s7_hide in Hb4.
(* entry 5, the character 0x35 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb5.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 53 ltac:(lia)) in Hb5.
  apply Z.eqb_eq in Hb5.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 91 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 53 ltac:(lia)) in Hb5.
apply Z.eqb_neq in Hb5. apply s7_hide in Hb5.
(* entry 6, the character 0x36 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb6.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 54 ltac:(lia)) in Hb6.
  apply Z.eqb_eq in Hb6.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 95 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 54 ltac:(lia)) in Hb6.
apply Z.eqb_neq in Hb6. apply s7_hide in Hb6.
(* entry 7, the character 0x37 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb7.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 55 ltac:(lia)) in Hb7.
  apply Z.eqb_eq in Hb7.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 112 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 55 ltac:(lia)) in Hb7.
apply Z.eqb_neq in Hb7. apply s7_hide in Hb7.
(* entry 8, the character 0x38 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb8.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 56 ltac:(lia)) in Hb8.
  apply Z.eqb_eq in Hb8.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 127 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 56 ltac:(lia)) in Hb8.
apply Z.eqb_neq in Hb8. apply s7_hide in Hb8.
(* entry 9, the character 0x39 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb9.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 57 ltac:(lia)) in Hb9.
  apply Z.eqb_eq in Hb9.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 123 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 57 ltac:(lia)) in Hb9.
apply Z.eqb_neq in Hb9. apply s7_hide in Hb9.
(* entry 10, the character 0x41 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb10.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 65 ltac:(lia)) in Hb10.
  apply Z.eqb_eq in Hb10.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 119 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 65 ltac:(lia)) in Hb10.
apply Z.eqb_neq in Hb10. apply s7_hide in Hb10.
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hf10.
{ rewrite branch_eq_U, (seg7_U_fold E 10 c 65 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf10.
  apply Z.eqb_eq in Hf10.
  destruct (seg7_fold_val 65 c ltac:(seg7_in_chr) Hc Hf10) as [Hx | Hx];
  [exfalso; unfold s7_hold in Hb10; exact (Hb10 Hx) |].
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 119 by (rewrite Hx; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (seg7_U_fold E 10 c 65 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf10.
apply Z.eqb_neq in Hf10. apply s7_hide in Hf10.
(* entry 11, the character 0x62 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb11.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 98 ltac:(lia)) in Hb11.
  apply Z.eqb_eq in Hb11.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 31 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 98 ltac:(lia)) in Hb11.
apply Z.eqb_neq in Hb11. apply s7_hide in Hb11.
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hf11.
{ rewrite branch_eq_U, (seg7_U_fold E 10 c 98 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf11.
  apply Z.eqb_eq in Hf11.
  destruct (seg7_fold_val 98 c ltac:(seg7_in_chr) Hc Hf11) as [Hx | Hx];
  [exfalso; unfold s7_hold in Hb11; exact (Hb11 Hx) |].
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 31 by (rewrite Hx; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (seg7_U_fold E 10 c 98 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf11.
apply Z.eqb_neq in Hf11. apply s7_hide in Hf11.
(* entry 12, the character 0x43 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb12.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 67 ltac:(lia)) in Hb12.
  apply Z.eqb_eq in Hb12.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 78 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 67 ltac:(lia)) in Hb12.
apply Z.eqb_neq in Hb12. apply s7_hide in Hb12.
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hf12.
{ rewrite branch_eq_U, (seg7_U_fold E 10 c 67 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf12.
  apply Z.eqb_eq in Hf12.
  destruct (seg7_fold_val 67 c ltac:(seg7_in_chr) Hc Hf12) as [Hx | Hx];
  [exfalso; unfold s7_hold in Hb12; exact (Hb12 Hx) |].
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 78 by (rewrite Hx; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (seg7_U_fold E 10 c 67 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf12.
apply Z.eqb_neq in Hf12. apply s7_hide in Hf12.
(* entry 13, the character 0x64 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb13.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 100 ltac:(lia)) in Hb13.
  apply Z.eqb_eq in Hb13.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 61 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 100 ltac:(lia)) in Hb13.
apply Z.eqb_neq in Hb13. apply s7_hide in Hb13.
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hf13.
{ rewrite branch_eq_U, (seg7_U_fold E 10 c 100 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf13.
  apply Z.eqb_eq in Hf13.
  destruct (seg7_fold_val 100 c ltac:(seg7_in_chr) Hc Hf13) as [Hx | Hx];
  [exfalso; unfold s7_hold in Hb13; exact (Hb13 Hx) |].
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 61 by (rewrite Hx; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (seg7_U_fold E 10 c 100 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf13.
apply Z.eqb_neq in Hf13. apply s7_hide in Hf13.
(* entry 14, the character 0x45 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb14.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 69 ltac:(lia)) in Hb14.
  apply Z.eqb_eq in Hb14.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 79 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 69 ltac:(lia)) in Hb14.
apply Z.eqb_neq in Hb14. apply s7_hide in Hb14.
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hf14.
{ rewrite branch_eq_U, (seg7_U_fold E 10 c 69 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf14.
  apply Z.eqb_eq in Hf14.
  destruct (seg7_fold_val 69 c ltac:(seg7_in_chr) Hc Hf14) as [Hx | Hx];
  [exfalso; unfold s7_hold in Hb14; exact (Hb14 Hx) |].
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 79 by (rewrite Hx; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (seg7_U_fold E 10 c 69 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf14.
apply Z.eqb_neq in Hf14. apply s7_hide in Hf14.
(* entry 15, the character 0x46 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb15.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 70 ltac:(lia)) in Hb15.
  apply Z.eqb_eq in Hb15.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 71 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 70 ltac:(lia)) in Hb15.
apply Z.eqb_neq in Hb15. apply s7_hide in Hb15.
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hf15.
{ rewrite branch_eq_U, (seg7_U_fold E 10 c 70 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf15.
  apply Z.eqb_eq in Hf15.
  destruct (seg7_fold_val 70 c ltac:(seg7_in_chr) Hc Hf15) as [Hx | Hx];
  [exfalso; unfold s7_hold in Hb15; exact (Hb15 Hx) |].
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 71 by (rewrite Hx; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (seg7_U_fold E 10 c 70 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf15.
apply Z.eqb_neq in Hf15. apply s7_hide in Hf15.
(* entry 16, the character 0x48 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb16.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 72 ltac:(lia)) in Hb16.
  apply Z.eqb_eq in Hb16.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 55 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 72 ltac:(lia)) in Hb16.
apply Z.eqb_neq in Hb16. apply s7_hide in Hb16.
(* entry 17, the character 0x68 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb17.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 104 ltac:(lia)) in Hb17.
  apply Z.eqb_eq in Hb17.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 23 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 104 ltac:(lia)) in Hb17.
apply Z.eqb_neq in Hb17. apply s7_hide in Hb17.
(* entry 18, the character 0x4a *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb18.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 74 ltac:(lia)) in Hb18.
  apply Z.eqb_eq in Hb18.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 60 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 74 ltac:(lia)) in Hb18.
apply Z.eqb_neq in Hb18. apply s7_hide in Hb18.
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hf18.
{ rewrite branch_eq_U, (seg7_U_fold E 10 c 74 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf18.
  apply Z.eqb_eq in Hf18.
  destruct (seg7_fold_val 74 c ltac:(seg7_in_chr) Hc Hf18) as [Hx | Hx];
  [exfalso; unfold s7_hold in Hb18; exact (Hb18 Hx) |].
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 60 by (rewrite Hx; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (seg7_U_fold E 10 c 74 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf18.
apply Z.eqb_neq in Hf18. apply s7_hide in Hf18.
(* entry 19, the character 0x4c *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb19.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 76 ltac:(lia)) in Hb19.
  apply Z.eqb_eq in Hb19.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 14 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 76 ltac:(lia)) in Hb19.
apply Z.eqb_neq in Hb19. apply s7_hide in Hb19.
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hf19.
{ rewrite branch_eq_U, (seg7_U_fold E 10 c 76 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf19.
  apply Z.eqb_eq in Hf19.
  destruct (seg7_fold_val 76 c ltac:(seg7_in_chr) Hc Hf19) as [Hx | Hx];
  [exfalso; unfold s7_hold in Hb19; exact (Hb19 Hx) |].
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 14 by (rewrite Hx; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (seg7_U_fold E 10 c 76 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf19.
apply Z.eqb_neq in Hf19. apply s7_hide in Hf19.
(* entry 20, the character 0x6f *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb20.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 111 ltac:(lia)) in Hb20.
  apply Z.eqb_eq in Hb20.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 29 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 111 ltac:(lia)) in Hb20.
apply Z.eqb_neq in Hb20. apply s7_hide in Hb20.
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hf20.
{ rewrite branch_eq_U, (seg7_U_fold E 10 c 111 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf20.
  apply Z.eqb_eq in Hf20.
  destruct (seg7_fold_val 111 c ltac:(seg7_in_chr) Hc Hf20) as [Hx | Hx];
  [exfalso; unfold s7_hold in Hb20; exact (Hb20 Hx) |].
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 29 by (rewrite Hx; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (seg7_U_fold E 10 c 111 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf20.
apply Z.eqb_neq in Hf20. apply s7_hide in Hf20.
(* entry 21, the character 0x50 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb21.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 80 ltac:(lia)) in Hb21.
  apply Z.eqb_eq in Hb21.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 103 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 80 ltac:(lia)) in Hb21.
apply Z.eqb_neq in Hb21. apply s7_hide in Hb21.
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hf21.
{ rewrite branch_eq_U, (seg7_U_fold E 10 c 80 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf21.
  apply Z.eqb_eq in Hf21.
  destruct (seg7_fold_val 80 c ltac:(seg7_in_chr) Hc Hf21) as [Hx | Hx];
  [exfalso; unfold s7_hold in Hb21; exact (Hb21 Hx) |].
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 103 by (rewrite Hx; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (seg7_U_fold E 10 c 80 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf21.
apply Z.eqb_neq in Hf21. apply s7_hide in Hf21.
(* entry 22, the character 0x72 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb22.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 114 ltac:(lia)) in Hb22.
  apply Z.eqb_eq in Hb22.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 5 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 114 ltac:(lia)) in Hb22.
apply Z.eqb_neq in Hb22. apply s7_hide in Hb22.
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hf22.
{ rewrite branch_eq_U, (seg7_U_fold E 10 c 114 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf22.
  apply Z.eqb_eq in Hf22.
  destruct (seg7_fold_val 114 c ltac:(seg7_in_chr) Hc Hf22) as [Hx | Hx];
  [exfalso; unfold s7_hold in Hb22; exact (Hb22 Hx) |].
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 5 by (rewrite Hx; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (seg7_U_fold E 10 c 114 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf22.
apply Z.eqb_neq in Hf22. apply s7_hide in Hf22.
(* entry 23, the character 0x53 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb23.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 83 ltac:(lia)) in Hb23.
  apply Z.eqb_eq in Hb23.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 91 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 83 ltac:(lia)) in Hb23.
apply Z.eqb_neq in Hb23. apply s7_hide in Hb23.
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hf23.
{ rewrite branch_eq_U, (seg7_U_fold E 10 c 83 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf23.
  apply Z.eqb_eq in Hf23.
  destruct (seg7_fold_val 83 c ltac:(seg7_in_chr) Hc Hf23) as [Hx | Hx];
  [exfalso; unfold s7_hold in Hb23; exact (Hb23 Hx) |].
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 91 by (rewrite Hx; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (seg7_U_fold E 10 c 83 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf23.
apply Z.eqb_neq in Hf23. apply s7_hide in Hf23.
(* entry 24, the character 0x55 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb24.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 85 ltac:(lia)) in Hb24.
  apply Z.eqb_eq in Hb24.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 62 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 85 ltac:(lia)) in Hb24.
apply Z.eqb_neq in Hb24. apply s7_hide in Hb24.
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hf24.
{ rewrite branch_eq_U, (seg7_U_fold E 10 c 85 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf24.
  apply Z.eqb_eq in Hf24.
  destruct (seg7_fold_val 85 c ltac:(seg7_in_chr) Hc Hf24) as [Hx | Hx];
  [exfalso; unfold s7_hold in Hb24; exact (Hb24 Hx) |].
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 62 by (rewrite Hx; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (seg7_U_fold E 10 c 85 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf24.
apply Z.eqb_neq in Hf24. apply s7_hide in Hf24.
(* entry 25, the character 0x59 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb25.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 89 ltac:(lia)) in Hb25.
  apply Z.eqb_eq in Hb25.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 59 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 89 ltac:(lia)) in Hb25.
apply Z.eqb_neq in Hb25. apply s7_hide in Hb25.
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hf25.
{ rewrite branch_eq_U, (seg7_U_fold E 10 c 89 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf25.
  apply Z.eqb_eq in Hf25.
  destruct (seg7_fold_val 89 c ltac:(seg7_in_chr) Hc Hf25) as [Hx | Hx];
  [exfalso; unfold s7_hold in Hb25; exact (Hb25 Hx) |].
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 59 by (rewrite Hx; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (seg7_U_fold E 10 c 89 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf25.
apply Z.eqb_neq in Hf25. apply s7_hide in Hf25.
(* entry 26, the character 0x5a *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb26.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 90 ltac:(lia)) in Hb26.
  apply Z.eqb_eq in Hb26.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 109 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 90 ltac:(lia)) in Hb26.
apply Z.eqb_neq in Hb26. apply s7_hide in Hb26.
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hf26.
{ rewrite branch_eq_U, (seg7_U_fold E 10 c 90 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf26.
  apply Z.eqb_eq in Hf26.
  destruct (seg7_fold_val 90 c ltac:(seg7_in_chr) Hc Hf26) as [Hx | Hx];
  [exfalso; unfold s7_hold in Hb26; exact (Hb26 Hx) |].
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 109 by (rewrite Hx; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (seg7_U_fold E 10 c 90 E10 Hc ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hf26.
apply Z.eqb_neq in Hf26. apply s7_hide in Hf26.
(* entry 27, the character 0x2d *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb27.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 45 ltac:(lia)) in Hb27.
  apply Z.eqb_eq in Hb27.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 1 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 45 ltac:(lia)) in Hb27.
apply Z.eqb_neq in Hb27. apply s7_hide in Hb27.
(* entry 28, the character 0x20 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_branch Hb28.
{ rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 32 ltac:(lia)) in Hb28.
  apply Z.eqb_eq in Hb28.
  cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
  cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
          ltac:(idtac; rewrite R10; cbn [sv_denot];
                replace (owed_seg7_spec c) with 0 by (subst c; vm_compute; reflexivity);
                reflexivity).
}
rewrite branch_eq_U, (U_atom E 10 c E10 ltac:(lia)), (U_lit E 32 ltac:(lia)) in Hb28.
apply Z.eqb_neq in Hb28. apply s7_hide in Hb28.
(* no entry matches: the function returns -1 *)
cw_run cw_awr_stk. cw_keep cw_kwr_stk. s7_norm.
cw_leaf ltac:(idtac; cw_kept HJ KE ltac:(intros ? []) ltac:(intros a Ha; left; exact Ha))
        ltac:(idtac; rewrite R10; cbn [sv_denot];
              replace (owed_seg7_spec c) with (-1) by
                (symmetry; unfold s7_hold in *; apply seg7_miss_all; assumption);
              apply Z_to_bv64_eq_mod; vm_compute; reflexivity).
Qed.

End c.
End b.
