(* rule 24: no function proved
   fuzz_preset, the crt102 walk: THE B' BINDING OF B, image B' (#102 pins: asan-ubsan d663f82d7f488d30, unstripped twin
   c90d4fa54d43160b). The B' port of lib/A/Prog/Crt102PALibCheck.v 405c59509186. The crt lane's B' contract takes the
   image facts below as generic Section hypotheses over a free `B : asyms`; this file WITNESSES them at the B' instance
   B := YD2l.TfibB (the B' image's generated asyms record), each stated in the hypothesis's own text with B := TfibB,
   PA := PI_prog_B, PST := prh_pst at prh_img_B. Every lemma is closed by vm_compute on a closed term or by citing
   PALibB; none is assumed.

   THE STAND-INS AND THEIR WITNESSES (texts: Crt102EntryB's Section f hypotheses, lib/B/Prog/Crt102EntryB.v
   27ad45449ff3 at commit 9179085e57d, :193 / :196 / :202; zs_aligned as
   lib/A/Prog/Crt102Top.v 0d349525589f :356 states it):
     PAL            : PALib (L := B_prog_listing) (PI := PA) B          crt102_PAL_TfibB, = PALibB.exvi_eh_palib (every
                                                                         field by vm_compute at TfibB, PALibB.v :58)
     pal_uar_img    : IMG_LO_B <= as_uar_cell B /\ as_uar_cell B + 4 <= IMG_TOP_B
                                                                         crt102_uar_img_TfibB, vm_compute
     pal_pst_static : forall a, Exists (in_zr a) PST -> ~ Exists (in_zr a) (as_owned_static B) /\
                      ~ (as_errno B <= a < as_errno B + 4)              crt102_pst_static_TfibB, from
                                                                         crt102_tfib_pst_static_B (every B with
                                                                         YF0m.TfibSyms B) at YD2l.TfibB_syms; its one
                                                                         computation runs over prh_pst
     zs_aligned     : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B)
                                                                         crt102_zs_aligned_TfibB, vm_compute
   pal_stack_malloc3 is Crt102AF0lCheckB.crt102_stack_malloc3_TfibB (the code record). img_shadow_vis_x is NOT witnessed
   here: it reads the allocator state ARx, which the contract keeps free.

   INPUTS OF RECORD (by path; blobs of the base commit 100c8e45583c unless named):
   - TAKEN BY PATH from the integration commit bedf6e890875 (image / generated files only; each one's base blob beside
     it): lib/B/PALibB.v 5baa19c890f7 (new on the lane), lib/Reusable/YD2l.v 0d0bc856b447 (base 4deb698ee695: the old
     pin's shadow / uar / GOT cells and junk; the integration's is the #102 B' record), lib/Reusable/YCej.v ae866e8addb2
     (base 9d858604e7c0: the old pin's traces, under which TfibB_syms' DRV_TRACES membership and PALibB's pal_env do not
     compute; the integration's is generated from image B').
   - read, not taken: listing lib/B/Listing_prog.v c97cc46b3e13, lib/B/PAImg_prog.v 15fab93fe702; records
     lib/Reusable/YF0l.v 4a405a3dba65, lib/Reusable/YF0m.v f82202ebccdf, lib/Reusable/YImgTop.v d2a97d3111ce;
     lib/B/PRH_ImgB.v 3216eca68342 (prh_img_B; the integration's c0678e5bddf3 differs only in its generator header).
   - contract / engine texts read, not taken: lib/A/PRH_Base.v ee2f5cd7ed35 (prh_pst, :542), lib/Reusable/YC1fP.v
     5a3e259a9c67 (PALib, :331), lib/Reusable/YP08.v 5d64fd5f9d0a (zallb), lib/Reusable/YG0n.v 7e71196e38f6 (in_zr).
   NUMERALS. ADDRESS: none typed (every address is a field of TfibB / YF0m, prh_pst of prh_img_B, or IMG_LO_B /
   IMG_TOP_B; the Eval lines print them). LENGTH: 4 (the uar flag's width; errno's width), 8 (the shadow granule).
   WORD: 0 (the residue mod 8). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
  YM05 YG00 YG01 YG0f YG0n YG0d YCbq YP0b YP08 YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
(* stdpp, through the LPS modules, shadows several list lemma names; the lemmas used here are Stdlib's *)
From Stdlib Require Import List.
Import ListNotations.
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.

(* which module each image name resolves to in this file's closure (printed into the build log) *)
Locate B_prog_listing.
Locate PI_prog_B.
Locate prh_img_B.
Locate YD2l.TfibB.

(* ---- image-free checkers and their soundness (written here, as A' S1ImgA's pst_allb, so that no A' image file is
   loaded into this B' file) ---- *)
(* f holds at every byte of every range of P *)
Definition crtb_allb (f : Z -> bool) (P : list (Z * Z)) : bool :=
  forallb (fun r => zallb f (fst r) (Z.to_nat (snd r))) P.

Lemma crtb_allb_sound : forall f P a, crtb_allb f P = true -> Exists (in_zr a) P -> f a = true.
Proof.
intros f P a H Ha. apply Exists_exists in Ha as (r & Hr & Ha). unfold crtb_allb in H.
rewrite forallb_forall in H. specialize (H r Hr). unfold in_zr in Ha.
apply (zallb_sound f (Z.to_nat (snd r)) (fst r) a H). rewrite Z2Nat.id by lia. lia.
Qed.

(* the byte a is outside the ranges l and outside [lo, lo + w) *)
Definition crtb_out_b (l : list (Z * Z)) (lo w a : Z) : bool :=
  negb (existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l) && negb ((lo <=? a) && (a <? lo + w)).

Lemma crtb_out_b_sound : forall l lo w a, crtb_out_b l lo w a = true -> ~ Exists (in_zr a) l /\ ~ (lo <= a < lo + w).
Proof.
intros l lo w a H. unfold crtb_out_b in H. apply andb_prop in H as [H1 H2].
apply negb_true_iff in H1. apply negb_true_iff in H2. split.
- intros HE. apply Exists_exists in HE as (r & Hr & Hin). unfold in_zr in Hin.
  assert (E : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) l = true).
  { apply existsb_exists. exists r. split; [exact Hr|].
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite E in H1. discriminate H1.
- intros Hr. assert (E : (lo <=? a) && (a <? lo + w) = true).
  { apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  rewrite E in H2. discriminate H2.
Qed.

(* ---- image B', the whole-program listing ---- *)
Section c. Context {rc : YM05.RunCeil}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation TB := (YD2l.TfibB).

(* PAL: PALibB's witness at the same instance, cited (PALibB.v 5baa19c890f7 :58) *)
Lemma crt102_PAL_TfibB : PALib (L := B_prog_listing) (PI := PA) TB.
Proof. exact PALibB.exvi_eh_palib. Qed.

(* pal_uar_img: the use-after-return flag cell of TfibB lies in B''s image bounds *)
Lemma crt102_uar_img_TfibB : IMG_LO_B <= as_uar_cell TB /\ as_uar_cell TB + 4 <= IMG_TOP_B.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* pal_pst_static: alloc.c's / the harness's statics (every prh_pst byte of prh_img_B) are neither a runtime-owned
   static nor an errno byte; first at every B with TfibSyms B (named projections ts_owned / ts_errno only), then at
   the record TfibB, whose TfibSyms is YD2l.TfibB_syms *)
Lemma crt102_pst_out_B : crtb_allb (crtb_out_b YF0m.Tfib_owned_static YF0m.TFIB_ERRNO 4) PST = true.
Proof. vm_compute. reflexivity. Qed.

Lemma crt102_tfib_pst_static_B : forall B, YF0m.TfibSyms B -> forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B HT a Ha. rewrite (YF0m.ts_owned B HT), (YF0m.ts_errno B HT).
exact (crtb_out_b_sound _ _ _ _ (crtb_allb_sound _ _ a crt102_pst_out_B Ha)).
Qed.

Lemma crt102_pst_static_TfibB : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static TB) /\ ~ (as_errno TB <= a < as_errno TB + 4).
Proof. exact (crt102_tfib_pst_static_B TB YD2l.TfibB_syms). Qed.

(* zs_aligned: every zero-shadow range of TfibB starts and ends 8-aligned *)
Lemma crt102_zs_aligned_TfibB : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow TB).
Proof.
apply Forall_forall. intros r Hr.
assert (Hb : forallb (fun r => (fst r mod 8 =? 0) && (snd r mod 8 =? 0)) (as_zero_shadow TB) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. specialize (Hb r Hr). apply andb_true_iff in Hb as [H1 H2].
split; apply Z.eqb_eq; assumption.
Qed.

(* the numbers, so the log shows them: the uar cell beside B''s image bounds, errno, the statics prh_pst names, and
   the count of TfibB's zero-shadow ranges *)
Eval vm_compute in ((IMG_LO_B, as_uar_cell TB, IMG_TOP_B), as_errno TB, PST, length (as_zero_shadow TB)).
End c.

Print Assumptions crt102_PAL_TfibB.
Print Assumptions crt102_uar_img_TfibB.
Print Assumptions crt102_tfib_pst_static_B.
Print Assumptions crt102_pst_static_TfibB.
Print Assumptions crt102_zs_aligned_TfibB.
