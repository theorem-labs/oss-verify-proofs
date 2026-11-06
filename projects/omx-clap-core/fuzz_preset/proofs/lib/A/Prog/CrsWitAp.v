(* fuzz_preset, image A' (the #102 pins): INSTANCE WITNESSES of the three image premises of crs_seg_E
   (lib/A/Prog/CrsSeg_E.v, row CR-E of the crcs walk) that PALibA does not cover (h-rw-man-5, 2026-10-29): each lemma
   is the premise's text with B := AD2l.TfibB and PA := PI_prog_A, the statement the composition plugs in, closed by
   computation (the PALibB form, origin/cold/h-rw-man-5-palib-core b597f50c7705 lib/B/PALibB.v blob 415450eb4ece).
     crs_wit_pal_uar_img_A'    = HX_pal_uar_img    : the use-after-return option cell lies in the image band
     crs_wit_pal_sm1_A'        = HX_pal_sm1        : the listing's __asan_stack_malloc_1 is the code record's class-1
                                                     frame-area entry
     crs_wit_pal_pst_static_A' = HX_pal_pst_static : alloc.c's statics (prh_pst) are neither runtime-owned statics
                                                     nor errno
   rule 24: no function proved here (image facts only).
   INPUTS. The instance record lib/A/AD2l.v blob eb321db7a357 (the same blob as RelocA, origin/cold/h-rw-pre-4-reloc102-a
   e36f036fc5ee; already on this branch's kit v2 base, so not re-taken), its code record lib/A/AF0m.v blob 97f423adf6eb,
   the listing instance lib/A/PAImg_prog.v blob 505a51ff7d08, the statics' places lib/A/PRH_Img.v (prh_img_A).
   Numerals: 4 (LENGTH: the use-after-return cell and errno are 4 bytes); 1 (the frame class). No ADDRESS literal:
   every address is read from the instance record, the listing or prh_img_A. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0f YG0n YP0b YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img Listing_prog PAImg_prog.
(* the instance: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

(* two ranges do not meet *)
Definition cw_disj (r o : Z * Z) : bool := (fst r + snd r <=? fst o) || (fst o + snd o <=? fst r).
Lemma cw_disj_sound : forall r o a, cw_disj r o = true -> in_zr a r -> ~ in_zr a o.
Proof.
intros [r1 r2] [o1 o2] a H Hr Ho. unfold cw_disj, in_zr in *. cbn [fst snd] in *.
apply orb_true_iff in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Section w. Context {rc : YM05.RunCeil}.
#[local] Abbreviation TA := AD2l.TfibB.

(* HX_pal_uar_img at A' *)
Lemma crs_wit_pal_uar_img_A' : IMG_LO <= as_uar_cell TA /\ as_uar_cell TA + 4 <= IMG_TOP.
Proof. split; apply Z.leb_le; vm_compute; reflexivity. Qed.

(* HX_pal_sm1 at A' *)
Lemma crs_wit_pal_sm1_A' :
  @pa_sigma rc A_prog_listing (@PI_prog_A rc) AS___asan_stack_malloc_1 = pc_stack_malloc (as_code TA) 1.
Proof. vm_compute. reflexivity. Qed.

(* HX_pal_pst_static at A': every range of prh_pst misses every runtime-owned static range and errno's 4 bytes *)
Lemma crs_wit_pst_check :
  forallb (fun r => forallb (cw_disj r) (as_owned_static TA) && cw_disj r (as_errno TA, 4))
    (prh_pst (PI := prh_img_A)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma crs_wit_pal_pst_static_A' : forall a, Exists (in_zr a) (prh_pst (PI := prh_img_A)) ->
  ~ Exists (in_zr a) (as_owned_static TA) /\ ~ (as_errno TA <= a < as_errno TA + 4).
Proof.
intros a Ha. apply Exists_exists in Ha as (r & Hr & Har).
pose proof (proj1 (forallb_forall _ _) crs_wit_pst_check r Hr) as Hc. apply andb_prop in Hc as [Ho He].
split.
- intros Hx. apply Exists_exists in Hx as (o & Ho' & Hao).
  exact (cw_disj_sound r o a (proj1 (forallb_forall _ _) Ho o Ho') Har Hao).
- intros He'. exact (cw_disj_sound r (as_errno TA, 4) a He Har He').
Qed.
End w.
