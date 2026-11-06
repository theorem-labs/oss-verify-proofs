(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgSatSeg.v at ea8335784b52 (item 12: in_roPb,
   img_bytes_ro_chk, img_val_ro_chk, img_static_chk and their soundness, rate_A_img_static, rate_A_static_of_facts,
   rate_A_static_full) for image B (fuzz_rate.asan-ubsan): the checkers run over image B's loaded segments
   (lib/AU/RtPgSatB.v segsB and its checkers), the record is RtPgImgB.rate_himg_B, the read-only range is image B's
   .data.rel.ro start .. .got end 0x9b9e0 .. 0x9ce68, and the bridge ends at lib/AU/RtPgSegB.v's rhb_static_law. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1 holds the same bytes here): the image side of
   RtPgCSpec.rt_static_of_img_facts at image B (rt_img_static over [IMG_LO, IMG_TOP) and the read-only range
   0x9b9e0 .. 0x9ce68), by computation over the loaded segments: each of the 46 strings is the image's bytes and NUL
   in a read-only segment, a registered global with room, 64 bytes inside the range; each of the 45 cells, each entry
   of closed_list, ordered, switch.table.check_code and reac_rate_refuse_code.codes is the image's value in a
   read-only segment or the read-only range. With it:
     rate_B_static_of_facts : at every AR state with the read-only data as in the image, image B's rt_img_facts
                              (RtPgSiteB.rate_B_img_facts) gives rt_seg_pre's globals, strings, cells and tables;
     rate_B_static_full     : with RtPgBase.rt_rom_pinned also rom_view, so RtPgSegB.rhb_static_law at image B's
                              segments and read-only range.
   proves no function (kind: statement text) *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YP09 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YO0f YG00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgSatB RtPgSiteB RtPgSegB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Definition in_roPb (segs : list Segment) (rlo rhi a : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
                     (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs || ((rlo <=? a) && (a <? rhi)).
Lemma in_roPb_ok : forall segs rlo rhi a, in_roPb segs rlo rhi a = true -> in_roP segs rlo rhi a.
Proof.
intros segs rlo rhi a H. unfold in_roPb in H. apply orb_true_iff in H. unfold in_roP. destruct H as [H|H].
- left. apply existsb_exists in H. destruct H as (sg & Hin & Hb). rewrite !andb_true_iff in Hb.
  destruct Hb as [[Hw H1] H2]. apply negb_true_iff in Hw. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists sg. split; [exact Hin|]. split; [exact Hw | lia].
- right. apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Definition img_bytes_ro_chk (rlo rhi a : Z) (l : list Z) : bool :=
  forallb (fun k => in_roPb segsB rlo rhi (a + Z.of_nat k) && oz_eqb (img_byte segsB (a + Z.of_nat k)) (nth k l 0))
    (seq 0 (length l)).
Lemma img_bytes_ro_chk_ok : forall rlo rhi a l, img_bytes_ro_chk rlo rhi a l = true -> rt_img_bytes segsB rlo rhi a l.
Proof.
intros rlo rhi a l Hc i Hi. unfold img_bytes_ro_chk in Hc. assert (Hk : (Z.to_nat i < length l)%nat) by lia.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
apply andb_true_iff in E. destruct E as [E1 E2]. split; [exact (in_roPb_ok _ _ _ _ E1)|].
exact (oz_eqb_ok _ _ E2).
Qed.
Definition img_val_ro_chk (rlo rhi a : Z) (n : nat) (v : Z) : bool :=
  img_val_chk segsB a n v && forallb (fun k => in_roPb segsB rlo rhi (a + Z.of_nat k)) (seq 0 n).
Lemma img_val_ro_chk_ok : forall rlo rhi a n v, img_val_ro_chk rlo rhi a n v = true -> rt_img_val segsB rlo rhi a n v.
Proof.
intros rlo rhi a n v Hc k Hk. unfold img_val_ro_chk in Hc. apply andb_true_iff in Hc. destruct Hc as [C1 C2].
split; [exact (in_roPb_ok _ _ _ _ (forallb_seq _ _ C2 _ Hk)) | exact (img_val_chk_ok segsB a n v C1 k Hk)].
Qed.
Definition img_static_chk (I : rt_himg) (lo hi rlo rhi : Z) : bool :=
  forallb (fun s => img_bytes_ro_chk rlo rhi (fst s) (snd s ++ [0]) &&
     forallb (fun b => (0 <? b) && (b <? 256)) (snd s) && (0 <? fst s) &&
     (fst s + Z.of_nat (length (snd s)) + 1 <=? 2 ^ 63) && img_chk segsB (fst s) (length (snd s) + 1) &&
     amem_rangeb (fst s) (Z.of_nat (length (snd s)) + 1) &&
     existsb (fun g => (fst g =? fst s) && (Z.of_nat (length (snd s)) + 1 <=? snd g)) (hi_globs I) &&
     (lo + 64 <=? fst s) && (fst s + Z.of_nat (length (snd s)) + 1 + 64 <=? hi)) (hi_strs I) &&
  forallb (fun c => img_val_ro_chk rlo rhi (fst c) 8 (snd c)) (hi_cells I) &&
  forallb (fun t => img_chk segsB (fst t) (4 * length (snd t)) && (fst t mod 4 =? 0) &&
     forallb (fun k => img_val_ro_chk rlo rhi (fst t + 4 * Z.of_nat k) 4 (nth k (snd t) 0)) (seq 0 (length (snd t))) &&
     existsb (fun g => (fst g =? fst t) && (4 * Z.of_nat (length (snd t)) <=? snd g)) (hi_globs I)) (hi_i32 I) &&
  forallb (fun t => img_chk segsB (fst t) (8 * length (snd t)) && (fst t mod 8 =? 0) &&
     forallb (fun v => (0 <=? v) && (v <? 2 ^ 64)) (snd t) &&
     forallb (fun k => img_val_ro_chk rlo rhi (fst t + 8 * Z.of_nat k) 8 (nth k (snd t) 0)) (seq 0 (length (snd t))) &&
     existsb (fun g => (fst g =? fst t) && (8 * Z.of_nat (length (snd t)) <=? snd g)) (hi_globs I)) (hi_u64 I).
Lemma img_static_chk_ok : forall I lo hi rlo rhi, img_static_chk I lo hi rlo rhi = true ->
  rt_img_static segsB I lo hi rlo rhi.
Proof.
intros I lo hi rlo rhi H. unfold img_static_chk in H. rewrite !andb_true_iff in H. destruct H as [[[HS HC] HI] HU].
rewrite forallb_forall in HS, HC, HI, HU.
unfold rt_img_static. split; [|split; [|split]]; apply Forall_forall.
- intros (a, s) Hin. specialize (HS (a, s) Hin). cbv beta in HS. cbn [fst snd] in HS |- *.
  rewrite !andb_true_iff in HS. destruct HS as [[[[[[[[H1 H2] H3] H4] H5] H6] H7] H8] H9].
  split; [exact (img_bytes_ro_chk_ok _ _ _ _ H1)|].
  split; [exact (bytes_range_ok _ H2)|].
  split; [apply Z.ltb_lt; exact H3|].
  split; [apply Z.leb_le; exact H4|].
  split; [intros i Hi; apply (img_chk_ok segsB a (length s + 1) H5); lia|].
  split; [exact (amem_rangeb_ok _ _ H6)|].
  split; [exact (rt_glob_of_b a _ (hi_globs I) H7)|].
  split; [apply Z.leb_le; exact H8 | apply Z.leb_le; exact H9].
- intros (c, v) Hin. specialize (HC (c, v) Hin). cbv beta in HC. cbn [fst snd] in HC |- *.
  exact (img_val_ro_chk_ok _ _ _ _ _ HC).
- intros (t, vs) Hin. specialize (HI (t, vs) Hin). cbv beta in HI. cbn [fst snd] in HI |- *.
  rewrite !andb_true_iff in HI. destruct HI as [[[T1 T2] T3] T4].
  split; [intros i Hi; apply (img_chk_ok segsB t (4 * length vs) T1); lia|].
  split; [apply Z.eqb_eq; exact T2|].
  split; [|exact (rt_glob_of_b t _ (hi_globs I) T4)].
  intros i Hi. assert (Hk : (Z.to_nat i < length vs)%nat) by lia.
  pose proof (forallb_seq _ _ T3 _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
  exact (img_val_ro_chk_ok _ _ _ _ _ E).
- intros (t, vs) Hin. specialize (HU (t, vs) Hin). cbv beta in HU. cbn [fst snd] in HU |- *.
  rewrite !andb_true_iff in HU. destruct HU as [[[[T1 T2] T3] T4] T5].
  split; [intros i Hi; apply (img_chk_ok segsB t (8 * length vs) T1); lia|].
  split; [apply Z.eqb_eq; exact T2|].
  split.
  { apply Forall_forall. intros v Hv. rewrite forallb_forall in T3. specialize (T3 v Hv). cbv beta in T3.
    apply andb_true_iff in T3. destruct T3 as [V1 V2]. apply Z.leb_le in V1. apply Z.ltb_lt in V2. lia. }
  split; [|exact (rt_glob_of_b t _ (hi_globs I) T5)].
  intros i Hi. assert (Hk : (Z.to_nat i < length vs)%nat) by lia.
  pose proof (forallb_seq _ _ T4 _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
  exact (img_val_ro_chk_ok _ _ _ _ _ E).
Qed.
Lemma rate_B_img_static_chk : img_static_chk rate_himg_B IMG_LO IMG_TOP 0x9b9e0 0x9ce68 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rate_B_img_static : rt_img_static segsB rate_himg_B IMG_LO IMG_TOP 0x9b9e0 0x9ce68.
Proof. exact (img_static_chk_ok _ _ _ _ _ rate_B_img_static_chk). Qed.
(* A control: with an empty read-only range the record is refused (its two tables in .data.rel.ro, a writable
   segment, switch.table.check_code 0x9bf40 and reac_rate_refuse_code.codes 0x9bf80, then lie in no read-only place). *)
Lemma rate_B_img_static_control : img_static_chk rate_himg_B IMG_LO IMG_TOP 0x9b9e0 0x9b9e0 = false.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions rate_B_img_static.

Section st. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma rate_B_static_of_facts : forall B : asyms, rate_B_img_facts segsB B ->
  forall ly S (W : world segsB) mem md, AR segsB B ly S W mem md ->
  arodata_okP segsB 0x9b9e0 0x9ce68 B (aview segsB (w_H W) mem) ->
  Forall (fun g => range_addressable (aview segsB (w_H W) mem) SHADOW_OFF (fst g) (snd g)) (hi_globs rate_himg_B) /\
  Forall (fun s => rt_cstr segsB (w_H W) mem (fst s) (snd s)) (hi_strs rate_himg_B) /\
  rt_ro_cells segsB (w_H W) mem (hi_cells rate_himg_B) /\
  Forall (fun t => rt_i32tab segsB (w_H W) mem (fst t) (snd t)) (hi_i32 rate_himg_B) /\
  Forall (fun t => rt_u64tab segsB (w_H W) mem (fst t) (snd t)) (hi_u64 rate_himg_B).
Proof.
intros B HF ly S W mem md HAR HA.
exact (rt_static_of_img_facts segsB B rate_himg_B IMG_LO IMG_TOP 0x9b9e0 0x9ce68 HF rate_B_img_static
  ly S W mem md HAR HA).
Qed.
(* With RtPgBase.rt_rom_pinned (the owned read-only bytes pinned as AR constant cells) also rom_view: the main walk's
   chaining law RtPgSegB.rhb_static_law at image B's segments and read-only range. *)
Lemma rate_B_static_full : forall B : asyms, rate_B_img_facts segsB B -> rt_rom_pinned segsB B ->
  rhb_static_law segsB B 0x9b9e0 0x9ce68.
Proof.
intros B HF HP ly S W mem md HAR HA.
destruct (rate_B_static_of_facts B HF ly S W mem md HAR HA) as (A1 & A2 & A3 & A4 & A5).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
exact (rt_rom_view_of segsB B 0x9b9e0 0x9ce68 ly S W mem md HP HAR HA).
Qed.
End st.
Print Assumptions rate_B_static_of_facts.
Print Assumptions rate_B_static_full.
