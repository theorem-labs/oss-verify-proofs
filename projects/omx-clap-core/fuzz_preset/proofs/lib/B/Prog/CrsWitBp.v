(* fuzz_preset, image B' (the #102 pins, asan-ubsan): INSTANCE WITNESSES of the three image premises of crs_seg_E_B
   (lib/B/Prog/CrsSeg_E_B.v, row E_B of the crcs walk) that PALibB does not cover: each lemma is the premise's text with
   B := YD2l.TfibB (the B' instance record PALibB's exvi_eh_palib is stated at) and PA := PI_prog_B, the statement the
   composition plugs in, closed by computation (the PALibB form, lib/B/PALibB.v blob 5baa19c890f7). B' twin of
   lib/A/Prog/CrsWitAp.v (a working branch 80467ffbd3ed).
     crs_wit_pal_uar_img_B'    = HX_pal_uar_img    : the use-after-return option cell lies in [pa_lo, pa_hi) of PI_prog_B
     crs_wit_pal_sm1_B'        = HX_pal_sm1        : the listing's __asan_stack_malloc_1 is the code record's class-1
                                                     frame-area entry
     crs_wit_pal_pst_static_B' = HX_pal_pst_static : alloc.c's statics (prh_pst at prh_img_B) are neither
                                                     runtime-owned statics nor errno
   rule 24: no function proved here (image facts only).
   INPUTS. The instance record lib/Reusable/YD2l.v blob 95803a8b9493, the listing instance lib/B/PAImg_prog.v blob
   15fab93fe702 (lib/B/Listing_prog.v blob c97cc46b3e13), the statics' places lib/B/PRH_ImgB.v blob 3216eca68342.
   Numerals: 4 (LENGTH: the use-after-return cell and errno are 4 bytes); 1 (the frame class). No ADDRESS literal:
   every address is read from the instance record, the listing or prh_img_B. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0f YG0n YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
(* the instance: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

(* two ranges do not meet *)
Definition cwb_disj (r o : Z * Z) : bool := (fst r + snd r <=? fst o) || (fst o + snd o <=? fst r).
Lemma cwb_disj_sound : forall r o a, cwb_disj r o = true -> in_zr a r -> ~ in_zr a o.
Proof.
intros [r1 r2] [o1 o2] a H Hr Ho. unfold cwb_disj, in_zr in *. cbn [fst snd] in *.
apply orb_true_iff in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Section w. Context {rc : YM05.RunCeil}.
#[local] Abbreviation TB := YD2l.TfibB.

(* HX_pal_uar_img at B' *)
Lemma crs_wit_pal_uar_img_B' :
  @pa_lo rc B_prog_listing (@PI_prog_B rc) <= as_uar_cell TB /\
  as_uar_cell TB + 4 <= @pa_hi rc B_prog_listing (@PI_prog_B rc).
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* HX_pal_sm1 at B' *)
Lemma crs_wit_pal_sm1_B' :
  @pa_sigma rc B_prog_listing (@PI_prog_B rc) AS___asan_stack_malloc_1 = pc_stack_malloc (as_code TB) 1.
Proof. vm_compute. reflexivity. Qed.

(* HX_pal_pst_static at B': every range of prh_pst misses every runtime-owned static range and errno's 4 bytes *)
Lemma crs_wit_pst_check_B :
  forallb (fun r => forallb (cwb_disj r) (as_owned_static TB) && cwb_disj r (as_errno TB, 4))
    (prh_pst (PI := prh_img_B)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crs_wit_pal_pst_static_B' : forall a, Exists (in_zr a) (prh_pst (PI := prh_img_B)) ->
  ~ Exists (in_zr a) (as_owned_static TB) /\ ~ (as_errno TB <= a < as_errno TB + 4).
Proof.
intros a Ha. apply Exists_exists in Ha as (r & Hr & Har).
pose proof (proj1 (forallb_forall _ _) crs_wit_pst_check_B r Hr) as Hc. apply andb_prop in Hc as [Ho He].
split.
- intros Hx. apply Exists_exists in Hx as (o & Ho' & Hao).
  exact (cwb_disj_sound r o a (proj1 (forallb_forall _ _) Ho o Ho') Har Hao).
- intros He'. exact (cwb_disj_sound r (as_errno TB, 4) a He Har He').
Qed.
End w.
