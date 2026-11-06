(* reac-pw/fuzz_link, PLAIN build: where malloc's block for link's memory FILE lies.

   malloc's `fresh_block` gives fmemopen a block f of 1304 bytes (MemFile.MF_BLOCK) with 4096 <= f and
   no byte of it in the image (`in_img src0_msyms`). `mf_place_of_fresh` turns that into memfile_c's
   `mf_place_ok f`: the block lies wholly below IMG_LO (0x10000) or wholly at or above IMG_TOP (0x97000).
   The reason: the image's reserved segments (`segments_reserved src0segs`, the list `in_img` reads)
   cover every address of [IMG_LO, IMG_TOP) without a gap, so a block that meets that range has a byte
   in the image. The cover is a boolean sweep over the segment list (`rsv_sweep`: from lo, take a
   reserved segment that holds lo and go on from its end, until lo reaches hi), proved sound
   (`rsv_sweep_sound`) and run on link's image by vm_compute (`rsv_cover`). On link's plain image the
   reserved segments are [0x10000, 0x12000), [0x12000, 0x20000), [0x20000, 0x21000) and
   [0x21000, 0x97000): the page-rounded PT_LOADs (R 0x10000+0x1eb4, RX 0x12eb4+0xc8fc, RW 0x207b0+0x850,
   RW 0x218f0+0x747f0) of the unstripped twin of the pin ebe34b259b9f. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require memfile_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YH00 YH02.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
Local Open Scope Z_scope.

(* the reserved segments of link's image, each as its first address and the address after it *)
Definition rsv_ivls : list (Z * Z) :=
  map (fun s : word * word => (bv_unsigned (fst s), bv_unsigned (fst s) + bv_unsigned (snd s)))
    (segments_reserved src0segs).

(* true when every address of [lo, hi) lies in a reserved segment, found by at most `fuel` steps *)
Fixpoint rsv_sweep (fuel : nat) (lo hi : Z) : bool :=
  (hi <=? lo) ||
  match fuel with
  | O => false
  | S n =>
      match find (fun iv : Z * Z => (fst iv <=? lo) && (lo <? snd iv)) rsv_ivls with
      | Some iv => rsv_sweep n (snd iv) hi
      | None => false
      end
  end.

Lemma rsv_sweep_sound : forall fuel lo hi a, rsv_sweep fuel lo hi = true -> lo <= a < hi ->
  exists s, In s (segments_reserved src0segs) /\
    bv_unsigned (fst s) <= a < bv_unsigned (fst s) + bv_unsigned (snd s).
Proof.
  induction fuel as [|n IH]; intros lo hi a H Ha; cbn [rsv_sweep] in H; apply orb_prop in H as [H|H].
  - apply Z.leb_le in H. lia.
  - discriminate H.
  - apply Z.leb_le in H. lia.
  - match type of H with context [find ?g ?l] => destruct (find g l) as [iv|] eqn:E end;
      [|discriminate H].
    apply find_some in E as [Hin Hc]. cbv beta in Hc. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    destruct (Z_lt_le_dec a (snd iv)) as [Hlt|Hge].
    + unfold rsv_ivls in Hin. apply in_map_iff in Hin as (s & Es & Hs).
      exists s. split; [exact Hs|]. subst iv. cbn [fst snd] in *. lia.
    + apply (IH (snd iv) hi a H). lia.
Qed.

(* link's image: the reserved segments cover [IMG_LO, IMG_TOP) (four steps; eight of fuel) *)
Lemma rsv_cover : rsv_sweep 8 memfile_c.IMG_LO memfile_c.IMG_TOP = true.
Proof. vm_compute. reflexivity. Qed.

Lemma img_range_in_img : forall a, memfile_c.IMG_LO <= a < memfile_c.IMG_TOP -> in_img src0_msyms a.
Proof.
  intros a Ha. destruct (rsv_sweep_sound 8 _ _ a rsv_cover Ha) as (s & Hs & Hsa). split.
  - intros E. change (ms_segs src0_msyms) with src0segs in E.
    pose proof Hs as Hs0. unfold segments_reserved in Hs0. rewrite E in Hs0. destruct Hs0.
  - exists s. split; [exact Hs | exact Hsa].
Qed.

Lemma mf_place_of_fresh : forall f, 4096 <= f -> (forall i, 0 <= i < MemFile.MF_BLOCK -> ~ in_img src0_msyms
(f + i)) -> memfile_c.mf_place_ok f.
Proof.
  intros f _ Hf. unfold memfile_c.mf_place_ok.
  destruct (Z_le_gt_dec (f + MemFile.MF_BLOCK) memfile_c.IMG_LO) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec memfile_c.IMG_TOP f) as [H'|H']; [right; exact H'|].
  exfalso. apply (Hf (Z.max f memfile_c.IMG_LO - f)).
  - unfold MemFile.MF_BLOCK, memfile_c.IMG_LO in *. lia.
  - replace (f + (Z.max f memfile_c.IMG_LO - f)) with (Z.max f memfile_c.IMG_LO) by lia.
    apply img_range_in_img. unfold MemFile.MF_BLOCK, memfile_c.IMG_LO, memfile_c.IMG_TOP in *. lia.
Qed.
