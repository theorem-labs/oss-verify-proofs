(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the static law of
   lib/AU/HPgHarn.v (hqu_static_law) holds for every symbol record B of lib/AU/YF0m.v's TfibSyms, at the image's
   loaded segments Img0U.rsegs and the read-only range [0x9c100, 0x9d4e8) (HPgLibU.RO_LO / RO_HI). So the whole-run
   chaining (lib/AU/HPgTop.v) does not have to assume it. The proof is image A's lib/A/HPgStatA.v (hq_static_A) over
   image B's tables (YF0m: the const cells, zero-shadow ranges, owned static ranges and the errno word
   TFIB_ERRNO 0x5d812c), image B's record (lib/AU/HPgImgB.v headamp_himg_B) and image B's segments; the checkers and
   their soundness lemmas are lib/A/HPgSat.v's and lib/A/HPgSatSeg.v's, used by name (no second copy).

   HOW. At any state AR accepts with the read-only data as in the image (arodata_okP), the view of memory agrees with
   one concrete partial reader hsb_rd0 built from YF0m's tables alone:
   - the bytes the const cells Tfib_const_abs ++ Tfib_const_shadow pin (AR's am_const, through ts_const), each with
     its cell's value;
   - 0 on the shadow of every range of Tfib_zero_shadow (AR's am_zshadow, through ts_zsh);
   - the image byte on every read-only byte (a non-writable segment, or [0x9c100, 0x9d4e8)) outside the owned static
     ranges Tfib_owned_static and the errno word TFIB_ERRNO (arodata_okP, through ts_owned and ts_errno).
   A byte of a loaded segment is readable at every memory (mbyte falls back to seg_rom). Each conjunct of the law is
   then a closed boolean check, computed on Img0U.rsegs:
   - the 43 registered globals of headamp_himg_B are addressable;
   - the 36 strings hold with their NUL, in the image, with addressable bytes, a readable shadow hull and a readable
     tail granule;
   - the 38 read-only cells hold their values;
   - the GOT word 0x9d478 reads 0x5f8210 (a const cell pins it) and the guard's eight bytes are image bytes (.bss);
   - every owned byte of a non-writable segment is pinned by a const cell with the image's byte, and the errno word
     lies in no non-writable segment; so every byte of a non-writable segment reads as the image's (rom_view).
   proves no function (kind: start-up facts) *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSat HPgSatSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgImgB HPgHarn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Img0U.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================== the reader of the tables ======================================== *)
(* The const cells with a number for address and value: Tfib_const ly without its layout-relative head. *)
Definition hsb_pins : list acell := Tfib_const_abs ++ Tfib_const_shadow.
Lemma hsb_pins_split : forall ly, Tfib_const ly = Tfib_const_sym ++ hsb_pins.
Proof. intros ly. unfold Tfib_const, hsb_pins. reflexivity. Qed.

(* The cell c pins the byte a, and the byte it pins there. *)
Definition hsb_pin_at (a : Z) (c : acell) : bool :=
  match c with
  | ACell (ANum z) w (AV (ANum _)) => (z <=? a) && (a <? z + Z.of_nat w)
  | _ => false
  end.
Definition hsb_pin_val (a : Z) (c : acell) : Z :=
  match c with
  | ACell (ANum z) w (AV (ANum v)) => YG0f.le_byte v w (Z.to_nat (a - z))
  | _ => 0
  end.

Definition hsb_in_zrb (a : Z) (r : Z * Z) : bool := (fst r <=? a) && (a <? fst r + snd r).
(* a is a shadow byte of the zero-shadow range r. *)
Definition hsb_zsh_at (a : Z) (r : Z * Z) : bool :=
  (shadow_of_addr SHADOW_OFF (fst r) <=? a) && (a <? shadow_of_addr SHADOW_OFF (fst r) + snd r / 8).
(* a is read-only data: in a non-writable segment of image B, or in [RO_LO, RO_HI). *)
Definition hsb_in_rob (a : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
    Img0U.rsegs || ((0x9c100 <=? a) && (a <? 0x9d4e8)).

Definition hsb_rd0 (a : Z) : option Z :=
  match find (hsb_pin_at a) hsb_pins with
  | Some c => Some (hsb_pin_val a c)
  | None =>
    if existsb (hsb_zsh_at a) Tfib_zero_shadow then Some 0
    else if hsb_in_rob a && negb (existsb (hsb_in_zrb a) Tfib_owned_static) &&
            negb ((TFIB_ERRNO <=? a) && (a <? TFIB_ERRNO + 4))
    then HPgSat.img_byte Img0U.rsegs a
    else None
  end.

(* ======================================== soundness of the reader ======================================== *)
Lemma hsb_pin_ok : forall (B : asyms) ly (rd : reader) c a,
  cell_holds B ly rd c -> hsb_pin_at a c = true -> rd a = Some (hsb_pin_val a c).
Proof.
intros B ly rd [ca w cv] a HC HP.
destruct ca; cbn in HP; try discriminate HP.
destruct cv as [e|m v]; cbn in HP; [|discriminate HP].
destruct e; cbn in HP; try discriminate HP.
apply andb_prop in HP as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
unfold cell_holds in HC. cbn [c_at c_w c_val aeval] in HC.
assert (Hk : (Z.to_nat (a - z) < w)%nat) by lia.
specialize (HC (Z.to_nat (a - z)) Hk). rewrite Z2Nat.id in HC by lia.
replace (z + (a - z)) with a in HC by ring.
cbn [hsb_pin_val]. exact HC.
Qed.

Lemma hsb_zsh_ok : forall (rd : reader) r a,
  zero_shadow rd SHADOW_OFF (fst r) (snd r) -> hsb_zsh_at a r = true -> rd a = Some 0.
Proof.
intros rd [lo len] a HZ Hz. unfold hsb_zsh_at in Hz. unfold zero_shadow in HZ. cbn [fst snd] in *.
set (b0 := shadow_of_addr SHADOW_OFF lo) in *.
apply andb_prop in Hz as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
specialize (HZ (a - b0)). replace (b0 + (a - b0)) with a in HZ by ring. apply HZ. lia.
Qed.

Lemma hsb_in_rob_ok : forall a, hsb_in_rob a = true -> in_roP Img0U.rsegs 0x9c100 0x9d4e8 a.
Proof.
intros a H. unfold hsb_in_rob in H. unfold in_roP. apply orb_true_iff in H as [H|H].
- left. apply existsb_exists in H as (s & Hs & Hb). cbv beta in Hb.
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists s. split; [exact Hs|]. split; [exact H0|]. lia.
- right. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma hsb_in_zrb_ok : forall a r, hsb_in_zrb a r = true -> in_zr a r.
Proof.
intros a r H. unfold hsb_in_zrb in H. unfold in_zr.
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma hsb_not_owned_ok : forall a l, negb (existsb (hsb_in_zrb a) l) = true -> ~ Exists (in_zr a) l.
Proof.
intros a l H HE. apply negb_true_iff in H. apply Exists_exists in HE as (r & Hr & Hz).
assert (X : existsb (hsb_in_zrb a) l = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. unfold in_zr in Hz. unfold hsb_in_zrb.
  apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite X in H. discriminate H.
Qed.

Lemma hsb_not_errno_ok : forall a e, negb ((e <=? a) && (a <? e + 4)) = true -> ~ (e <= a < e + 4).
Proof.
intros a e H [H1 H2]. apply negb_true_iff in H. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
rewrite H1, H2 in H. cbn in H. discriminate H.
Qed.

(* The reader of the tables is a part of the view of memory at every state AR accepts with the read-only data as in
   the image. *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

Lemma hsb_rd0_ext : forall B : asyms, TfibSyms B -> forall ly S (W : world Img0U.rsegs) mem md,
  AR Img0U.rsegs B ly S W mem md ->
  arodata_okP Img0U.rsegs 0x9c100 0x9d4e8 B (aview Img0U.rsegs (w_H W) mem) ->
  rd_ext hsb_rd0 (aview Img0U.rsegs (w_H W) mem).
Proof.
intros B TS ly S W mem md HAR HRO.
destruct HAR as (M & _).
set (rd := aview Img0U.rsegs (w_H W) mem) in *.
pose proof (am_const _ _ _ _ M) as HC. rewrite (ts_const B TS ly), (hsb_pins_split ly) in HC.
apply Forall_app in HC as [_ HC]. rewrite Forall_forall in HC.
pose proof (am_zshadow _ _ _ _ M) as HZ. unfold zshadow_ok, zero_shadow_ranges in HZ.
rewrite (ts_zsh B TS) in HZ. apply Forall_inv_tail in HZ. rewrite Forall_forall in HZ.
clear M.
intros a v H. unfold hsb_rd0 in H.
destruct (find (hsb_pin_at a) hsb_pins) as [c|] eqn:F.
- apply find_some in F as [Hin Hp]. injection H as <-.
  exact (hsb_pin_ok B ly rd c a (HC c Hin) Hp).
- destruct (existsb (hsb_zsh_at a) Tfib_zero_shadow) eqn:EZ.
  + injection H as <-. apply existsb_exists in EZ as (r & Hr & Hz).
    exact (hsb_zsh_ok rd r a (HZ r Hr) Hz).
  + destruct (hsb_in_rob a && negb (existsb (hsb_in_zrb a) Tfib_owned_static) &&
              negb ((TFIB_ERRNO <=? a) && (a <? TFIB_ERRNO + 4))) eqn:EC; [|discriminate H].
    apply andb_prop in EC as [EC E3]. apply andb_prop in EC as [E1 E2].
    assert (P1 : in_roP Img0U.rsegs 0x9c100 0x9d4e8 a) by exact (hsb_in_rob_ok a E1).
    assert (P2 : ~ Exists (in_zr a) (as_owned_static B))
      by (rewrite (ts_owned B TS); exact (hsb_not_owned_ok a _ E2)).
    assert (P3 : ~ (as_errno B <= a < as_errno B + 4))
      by (rewrite (ts_errno B TS); exact (hsb_not_errno_ok a _ E3)).
    rewrite (HRO a P1 P2 P3). exact H.
Qed.

End s.

(* ============================== checkers over a reader, and their soundness ============================== *)
Lemma hsb_hull_ext : forall (rd rd' : reader) x n, rd_ext rd rd' -> shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof.
intros rd rd' x n EXT HV s Hs. pose proof (HV s Hs) as Hn.
destruct (rd s) as [v|] eqn:E; [|contradiction].
rewrite (EXT s v E). discriminate.
Qed.

(* A byte of a loaded segment is readable at every memory: mbyte falls back to seg_rom. *)
Lemma hsb_aview_img : forall segs H mem a, HPgSat.is_someb (HPgSat.img_byte segs a) = true ->
  exists v, aview segs H mem a = Some v.
Proof.
intros segs H mem a Hs. unfold aview, mbyte.
destruct (mrestrict H mem (Z_to_bv 64 a)) as [b|]; [eexists; reflexivity|].
unfold HPgSat.img_byte in Hs. destruct (seg_rom segs (Z_to_bv 64 a)) as [b|]; [eexists; reflexivity | discriminate Hs].
Qed.

(* The string's tail granule: each byte after the NUL up to the granule's end is read by rd or is an image byte. *)
Definition hsb_tail_chk (segs : list Segment) (rd : reader) (e : Z) : bool :=
  forallb (fun k => HPgSat.is_someb (rd (e + 1 + Z.of_nat k)) || HPgSat.is_someb (HPgSat.img_byte segs (e + 1 + Z.of_nat k)))
    (seq 0 (Z.to_nat (7 - e mod 8))).
Lemma hsb_tail_chk_ok : forall segs H mem rd e,
  rd_ext rd (aview segs H mem) -> hsb_tail_chk segs rd e = true -> hd_str_tail (aview segs H mem) e.
Proof.
intros segs H mem rd e EXT Hc a Ha. unfold hsb_tail_chk in Hc.
pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as Hm.
assert (Hk : (Z.to_nat (a - e - 1) < Z.to_nat (7 - e mod 8))%nat) by lia.
pose proof (HPgSat.forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
replace (e + 1 + (a - e - 1)) with a in E by ring.
apply orb_true_iff in E as [E|E].
- destruct (rd a) as [v|] eqn:R; [|discriminate E]. rewrite (EXT a v R). discriminate.
- destruct (hsb_aview_img segs H mem a E) as [v Hv]. rewrite Hv. discriminate.
Qed.

(* HPgBase.hd_cstr, conjunct by conjunct, over a reader rd that is a part of the view of memory. *)
Definition hsb_cstr_chk (segs : list Segment) (rd : reader) (a : Z) (s : list Z) : bool :=
  HPgSat.bytes_chk rd a s &&
  HPgSat.oz_eqb (rd (a + Z.of_nat (length s))) 0 &&
  forallb (fun b => (0 <? b) && (b <? 256)) s &&
  (0 <? a) && (a + Z.of_nat (length s) + 1 <=? 2 ^ 63) &&
  HPgSat.img_chk segs a (S (length s)) &&
  HPgSat.amem_rangeb a (Z.of_nat (length s) + 8) &&
  HPgSat.ra_chk rd SHADOW_OFF a (S (length s)) &&
  HPgSat.hull_chk rd a (Z.of_nat (length s) + 1) &&
  hsb_tail_chk segs rd (a + Z.of_nat (length s)).
Lemma hsb_cstr_chk_ok : forall segs H mem rd a s,
  rd_ext rd (aview segs H mem) -> hsb_cstr_chk segs rd a s = true -> hd_cstr segs H mem a s.
Proof.
intros segs H mem rd a s EXT Hc. unfold hsb_cstr_chk in Hc. rewrite !andb_true_iff in Hc.
destruct Hc as [[[[[[[[[C1 C2] C3] C4] C5] C6] C7] C8] C9] C10].
pose proof EXT as EXT'. unfold rd_ext in EXT.
unfold hd_cstr.
split; [intros i Hi; apply EXT; exact (HPgSat.bytes_chk_ok _ _ _ C1 i Hi)|].
split; [apply EXT; exact (HPgSat.oz_eqb_ok _ _ C2)|].
split; [exact (HPgSat.bytes_range_ok _ C3)|].
split; [apply Z.ltb_lt; exact C4|].
split; [apply Z.leb_le; exact C5|].
split; [intros i Hi; apply (HPgSat.img_chk_ok _ _ _ C6); lia|].
split; [exact (HPgSat.amem_rangeb_ok _ _ C7)|].
split; [apply (range_addressable_ext rd); [exact EXT|]; apply (HPgSat.ra_chk_ok _ _ _ (S (length s))); [lia | exact C8]|].
split; [exact (hsb_hull_ext rd _ a _ EXT (HPgSat.hull_chk_ok _ _ _ C9))|].
exact (hsb_tail_chk_ok segs H mem rd _ EXT' C10).
Qed.

(* YI04.val_mem over a reader rd that is a part of the view of memory (val_mem reads YO0f.le_byte). *)
Definition hsb_val_chk (rd : reader) (a : Z) (n : nat) (v : Z) : bool :=
  forallb (fun k => HPgSat.oz_eqb (rd (a + Z.of_nat k)) (YO0f.le_byte v n k)) (seq 0 n).
Lemma hsb_val_chk_ok : forall segs H mem rd a n v,
  rd_ext rd (aview segs H mem) -> hsb_val_chk rd a n v = true -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem rd a n v EXT Hc. unfold rd_ext in EXT. unfold val_mem. intros k Hk. unfold hsb_val_chk in Hc.
pose proof (HPgSat.forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. apply HPgSat.oz_eqb_ok in E. apply EXT in E.
unfold aview in E.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|]; cbn [option_map] in E; [|discriminate E].
injection E as E. rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* rdword through a part of the view, and from eight readable bytes *)
Lemma hsb_rdword_ext : forall (rd rd' : reader) a v, rd_ext rd rd' -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof.
intros rd rd' a v EXT H. unfold rdword in *.
destruct (rd a) eqn:E0; [|discriminate H]. destruct (rd (a + 1)) eqn:E1; [|discriminate H].
destruct (rd (a + 2)) eqn:E2; [|discriminate H]. destruct (rd (a + 3)) eqn:E3; [|discriminate H].
destruct (rd (a + 4)) eqn:E4; [|discriminate H]. destruct (rd (a + 5)) eqn:E5; [|discriminate H].
destruct (rd (a + 6)) eqn:E6; [|discriminate H]. destruct (rd (a + 7)) eqn:E7; [|discriminate H].
rewrite (EXT _ _ E0), (EXT _ _ E1), (EXT _ _ E2), (EXT _ _ E3), (EXT _ _ E4), (EXT _ _ E5), (EXT _ _ E6), (EXT _ _ E7).
exact H.
Qed.
Lemma hsb_rdword_some : forall (rd : reader) a, (forall i, 0 <= i < 8 -> exists v, rd (a + i) = Some v) ->
  exists w, rdword rd a = Some w.
Proof.
intros rd a H.
destruct (H 0 ltac:(lia)) as [v0 E0]. rewrite Z.add_0_r in E0.
destruct (H 1 ltac:(lia)) as [v1 E1]. destruct (H 2 ltac:(lia)) as [v2 E2]. destruct (H 3 ltac:(lia)) as [v3 E3].
destruct (H 4 ltac:(lia)) as [v4 E4]. destruct (H 5 ltac:(lia)) as [v5 E5]. destruct (H 6 ltac:(lia)) as [v6 E6].
destruct (H 7 ltac:(lia)) as [v7 E7].
unfold rdword. rewrite E0, E1, E2, E3, E4, E5, E6, E7. eexists. reflexivity.
Qed.

(* Both readings are present and equal. *)
Definition hsb_opt_eqb (o1 o2 : option Z) : bool :=
  match o1, o2 with Some x, Some y => x =? y | _, _ => false end.
Lemma hsb_opt_eqb_ok : forall o1 o2, hsb_opt_eqb o1 o2 = true -> exists v, o1 = Some v /\ o2 = Some v.
Proof.
intros [x|] [y|] H; cbn [hsb_opt_eqb] in H; try discriminate H.
apply Z.eqb_eq in H. subst y. exists x. split; reflexivity.
Qed.

(* The bytes of the owned range r that lie in the segment sg: [hsb_lo r sg, hsb_hi r sg). *)
Definition hsb_lo (r : Z * Z) (sg : Segment) : Z := Z.max (fst r) (Z.of_N (seg_base sg)).
Definition hsb_hi (r : Z * Z) (sg : Segment) : Z := Z.min (fst r + snd r) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)).
(* Each owned byte of a non-writable segment reads, in hsb_rd0, as the image's byte (so a const cell pins it with that
   byte: the owned bytes are outside hsb_rd0's read-only branch). The writable segments are skipped by an `if`, not by
   `||`: vm_compute evaluates both arguments of orb, and owned ranges meet the writable segments in megabytes. *)
Definition hsb_rom_pin_chk : bool :=
  forallb (fun r => forallb (fun sg => if seg_writable sg then true else
    forallb (fun k => hsb_opt_eqb (hsb_rd0 (hsb_lo r sg + Z.of_nat k)) (HPgSat.img_byte Img0U.rsegs (hsb_lo r sg + Z.of_nat k)))
      (seq 0 (Z.to_nat (hsb_hi r sg - hsb_lo r sg)))) Img0U.rsegs) Tfib_owned_static.
Lemma hsb_rom_pin : hsb_rom_pin_chk = true ->
  forall r sg a, In r Tfib_owned_static -> In sg Img0U.rsegs -> seg_writable sg = false -> in_zr a r ->
  Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg) ->
  exists v, hsb_rd0 a = Some v /\ HPgSat.img_byte Img0U.rsegs a = Some v.
Proof.
intros Hc r sg a Hr Hsg Hw Hz Ha.
assert (L : hsb_lo r sg <= a < hsb_hi r sg) by (unfold in_zr in Hz; unfold hsb_lo, hsb_hi; lia).
clear Hz Ha.
unfold hsb_rom_pin_chk in Hc. rewrite forallb_forall in Hc.
specialize (Hc r Hr). cbv beta in Hc. rewrite forallb_forall in Hc. specialize (Hc sg Hsg). cbv beta in Hc.
rewrite Hw in Hc. cbv iota in Hc.
set (lo := hsb_lo r sg) in *. set (hi := hsb_hi r sg) in *.
assert (Hk : (Z.to_nat (a - lo) < Z.to_nat (hi - lo))%nat) by lia.
pose proof (HPgSat.forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
replace (lo + (a - lo)) with a in E by ring.
exact (hsb_opt_eqb_ok _ _ E).
Qed.

(* The errno word lies in no non-writable segment. *)
Definition hsb_errno_chk : bool :=
  forallb (fun sg => seg_writable sg || (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? TFIB_ERRNO) ||
    (TFIB_ERRNO + 4 <=? Z.of_N (seg_base sg))) Img0U.rsegs.
Lemma hsb_errno_rom : hsb_errno_chk = true ->
  forall sg a, In sg Img0U.rsegs -> seg_writable sg = false ->
  Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg) -> ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4).
Proof.
intros Hc sg a Hsg Hw Ha He. unfold hsb_errno_chk in Hc. rewrite forallb_forall in Hc.
specialize (Hc sg Hsg). cbv beta in Hc. rewrite Hw in Hc. cbn [orb] in Hc.
apply orb_true_iff in Hc as [Hc|Hc]; [apply Z.leb_le in Hc | apply Z.leb_le in Hc]; lia.
Qed.

(* ======================================== the closed checks ======================================== *)
(* 1. The registered globals (hi_globs: address, size) are addressable. *)
Lemma hsb_globs_chk : HPgSatSeg.ranges_chk hsb_rd0 (fun a => a) (hi_globs headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
(* 2. The strings. *)
Lemma hsb_strs_chk : forallb (fun c => hsb_cstr_chk Img0U.rsegs hsb_rd0 (fst c) (snd c)) (hi_strs headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
(* 3. The read-only cells. *)
Lemma hsb_cells_chk : forallb (fun c => hsb_val_chk hsb_rd0 (fst c) 8 (snd c)) (hi_cells headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
(* 4. The stack-guard pair: the GOT word reads the guard's address; the guard's eight bytes are image bytes. *)
Lemma hsb_got_chk : HPgSat.oz_eqb (rdword hsb_rd0 (hi_gotw headamp_himg_B)) (hi_guard headamp_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hsb_guard_img_chk :
  forallb (fun k => HPgSat.is_someb (HPgSat.img_byte Img0U.rsegs (hi_guard headamp_himg_B + Z.of_nat k))) (seq 0 8) = true.
Proof. vm_compute. reflexivity. Qed.
(* 5. The owned bytes of the non-writable segments are pinned with the image's bytes; the errno word is not in them. *)
Lemma hsb_rom_pin_chk_ok : hsb_rom_pin_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hsb_errno_chk_ok : hsb_errno_chk = true.
Proof. vm_compute. reflexivity. Qed.
(* The count of owned bytes in the non-writable segments that check 5 reads (YF0m's header: 1272 bytes pinned). *)
Lemma hsb_rom_pin_count :
  fold_right Z.add 0 (map (fun r => fold_right Z.add 0 (map (fun sg =>
    if seg_writable sg then 0 else Z.max 0 (hsb_hi r sg - hsb_lo r sg)) Img0U.rsegs)) Tfib_owned_static) = 1272.
Proof. vm_compute. reflexivity. Qed.

(* ======================================== the law ======================================== *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

Theorem hqu_static_B : forall B : asyms, TfibSyms B -> hqu_static_law Img0U.rsegs B 0x9c100 0x9d4e8.
Proof.
intros B TS ly S W mem md HAR HRO.
pose proof (hsb_rd0_ext B TS ly S W mem md HAR HRO) as EXT.
clear HAR.
split; [|split; [|split; [|split]]].
- pose proof (HPgSatSeg.ranges_chk_ok _ _ _ hsb_globs_chk) as F.
  eapply Forall_impl; [|exact F]. intros g Hg. cbv beta in Hg.
  exact (range_addressable_ext _ _ _ _ _ EXT Hg).
- apply Forall_forall. intros c Hc. apply (hsb_cstr_chk_ok Img0U.rsegs (w_H W) mem hsb_rd0); [exact EXT|].
  pose proof hsb_strs_chk as E. rewrite forallb_forall in E. exact (E c Hc).
- unfold hd_ro_cells. apply Forall_forall. intros c Hc.
  apply (hsb_val_chk_ok Img0U.rsegs (w_H W) mem hsb_rd0); [exact EXT|].
  pose proof hsb_cells_chk as E. rewrite forallb_forall in E. exact (E c Hc).
- unfold hd_guard_ok. split.
  + exact (hsb_rdword_ext hsb_rd0 _ _ _ EXT (HPgSat.oz_eqb_ok _ _ hsb_got_chk)).
  + apply hsb_rdword_some. intros i Hi. apply hsb_aview_img.
    assert (Hk : (Z.to_nat i < 8)%nat) by lia.
    pose proof (HPgSat.forallb_seq _ _ hsb_guard_img_chk _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia. exact E.
- intros a Ha. hnf in Ha. destruct Ha as (sg & Hsg & Hw & Hr).
  destruct (existsb (hsb_in_zrb a) Tfib_owned_static) eqn:EO.
  + apply existsb_exists in EO as (r & Hr' & Hz). apply hsb_in_zrb_ok in Hz.
    destruct (hsb_rom_pin hsb_rom_pin_chk_ok r sg a Hr' Hsg Hw Hz Hr) as (v & E1 & E2).
    rewrite (EXT a v E1). symmetry. exact E2.
  + apply (HRO a).
    * unfold in_roP. left. exists sg. split; [exact Hsg|]. split; [exact Hw | exact Hr].
    * rewrite (ts_owned B TS). apply hsb_not_owned_ok. rewrite EO. reflexivity.
    * rewrite (ts_errno B TS). exact (hsb_errno_rom hsb_errno_chk_ok sg a Hsg Hw Hr).
Qed.

End t.

Print Assumptions hqu_static_B.
