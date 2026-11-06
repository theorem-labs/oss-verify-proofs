(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgStatA.v at c9f9a5a10e3; the same law at image B
   (fuzz_role.asan-ubsan): image B's core tables (lib/AU/YF0m.v), segments (lib/AU/Img0.v), record (lib/AU/RPgImgA.v
   role_himg_B), checkers (lib/AU/RPgSat.v, RPgSatSeg.v) and read-only range 0x9a3c0 .. 0x9b7c8, and the law's
   instance at the closing's symbols lib/AU/YD2l.v TfibB and segments lib/AU/YB1v.v tfibsegs. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the static law of
   lib/AU/RPgHarn.v (rh_static_law) holds for every symbol record B of lib/AU/YF0m.v's TfibSyms, at the image's
   loaded segments Img0.rsegs and the read-only range [0x9a3c0, 0x9b7c8) (lib/AU/RPgLib.v RO_LO / RO_HI: .data.rel.ro
   start .. .got end). So the whole-run chaining does not have to assume it.

   HOW. At any state AR accepts with the read-only data as in the image (arodata_okP), the view of memory agrees with
   one concrete partial reader rsa_rd0 built from YF0m's tables alone:
   - the bytes the const cells Tfib_const_abs ++ Tfib_const_shadow pin (AR's am_const, through ts_const), each with
     its cell's value;
   - 0 on the shadow of every range of Tfib_zero_shadow (AR's am_zshadow, through ts_zsh);
   - the image byte on every read-only byte (a non-writable segment, or [0x9a3c0, 0x9b7c8)) outside the owned static
     ranges Tfib_owned_static and the errno word TFIB_ERRNO (arodata_okP, through ts_owned and ts_errno).
   Each conjunct of the law is then a closed boolean check on rsa_rd0, computed on Img0.rsegs:
   - the 49 registered globals of role_himg_B are addressable (lib/AU/RPgSat.v's ra_chk);
   - the 41 strings hold with their NUL, in the image, with addressable bytes and a readable shadow hull;
   - the 38 read-only cells hold their values;
   - every owned byte of a non-writable segment (1417 bytes, from the 57 of the 83 owned ranges that meet the
     read-only PT_LOADs) is pinned by a const cell with the image's byte, and the errno word lies in no non-writable
     segment; so every byte of a non-writable segment reads as the image's (rom_view).
   proves no function (kind: start-up facts) *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgImgA RPgHarn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgSat RPgSatSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Img0 YB1v YD2l RPgLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================== the reader of the tables ======================================== *)
(* The const cells with a number for address and value: Tfib_const ly without its layout-relative head. *)
Definition rsa_pins : list acell := Tfib_const_abs ++ Tfib_const_shadow.
Lemma rsa_pins_split : forall ly, Tfib_const ly = Tfib_const_sym ++ rsa_pins.
Proof. intros ly. unfold Tfib_const, rsa_pins. reflexivity. Qed.

(* The cell c pins the byte a, and the byte it pins there. *)
Definition rsa_pin_at (a : Z) (c : acell) : bool :=
  match c with
  | ACell (ANum z) w (AV (ANum _)) => (z <=? a) && (a <? z + Z.of_nat w)
  | _ => false
  end.
Definition rsa_pin_val (a : Z) (c : acell) : Z :=
  match c with
  | ACell (ANum z) w (AV (ANum v)) => YG0f.le_byte v w (Z.to_nat (a - z))
  | _ => 0
  end.

Definition rsa_in_zrb (a : Z) (r : Z * Z) : bool := (fst r <=? a) && (a <? fst r + snd r).
(* a is a shadow byte of the zero-shadow range r. *)
Definition rsa_zsh_at (a : Z) (r : Z * Z) : bool :=
  (shadow_of_addr SHADOW_OFF (fst r) <=? a) && (a <? shadow_of_addr SHADOW_OFF (fst r) + snd r / 8).
(* a is read-only data: in a non-writable segment of image B, or in [RO_LO, RO_HI). *)
Definition rsa_in_rob (a : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
    Img0.rsegs || ((0x9a3c0 <=? a) && (a <? 0x9b7c8)).

Definition rsa_rd0 (a : Z) : option Z :=
  match find (rsa_pin_at a) rsa_pins with
  | Some c => Some (rsa_pin_val a c)
  | None =>
    if existsb (rsa_zsh_at a) Tfib_zero_shadow then Some 0
    else if rsa_in_rob a && negb (existsb (rsa_in_zrb a) Tfib_owned_static) &&
            negb ((TFIB_ERRNO <=? a) && (a <? TFIB_ERRNO + 4))
    then RPgSat.img_byte Img0.rsegs a
    else None
  end.

(* ======================================== soundness of the reader ======================================== *)
Lemma rsa_pin_ok : forall (B : asyms) ly (rd : reader) c a,
  cell_holds B ly rd c -> rsa_pin_at a c = true -> rd a = Some (rsa_pin_val a c).
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
cbn [rsa_pin_val]. exact HC.
Qed.

Lemma rsa_zsh_ok : forall (rd : reader) r a,
  zero_shadow rd SHADOW_OFF (fst r) (snd r) -> rsa_zsh_at a r = true -> rd a = Some 0.
Proof.
intros rd [lo len] a HZ Hz. unfold rsa_zsh_at in Hz. unfold zero_shadow in HZ. cbn [fst snd] in *.
set (b0 := shadow_of_addr SHADOW_OFF lo) in *.
apply andb_prop in Hz as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
specialize (HZ (a - b0)). replace (b0 + (a - b0)) with a in HZ by ring. apply HZ. lia.
Qed.

Lemma rsa_in_rob_ok : forall a, rsa_in_rob a = true -> in_roP Img0.rsegs 0x9a3c0 0x9b7c8 a.
Proof.
intros a H. unfold rsa_in_rob in H. unfold in_roP. apply orb_true_iff in H as [H|H].
- left. apply existsb_exists in H as (s & Hs & Hb). cbv beta in Hb.
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists s. split; [exact Hs|]. split; [exact H0|]. lia.
- right. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma rsa_in_zrb_ok : forall a r, rsa_in_zrb a r = true -> in_zr a r.
Proof.
intros a r H. unfold rsa_in_zrb in H. unfold in_zr.
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma rsa_not_owned_ok : forall a l, negb (existsb (rsa_in_zrb a) l) = true -> ~ Exists (in_zr a) l.
Proof.
intros a l H HE. apply negb_true_iff in H. apply Exists_exists in HE as (r & Hr & Hz).
assert (X : existsb (rsa_in_zrb a) l = true).
{ apply existsb_exists. exists r. split; [exact Hr|]. unfold in_zr in Hz. unfold rsa_in_zrb.
  apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite X in H. discriminate H.
Qed.

Lemma rsa_not_errno_ok : forall a e, negb ((e <=? a) && (a <? e + 4)) = true -> ~ (e <= a < e + 4).
Proof.
intros a e H [H1 H2]. apply negb_true_iff in H. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
rewrite H1, H2 in H. cbn in H. discriminate H.
Qed.

(* The reader of the tables is a part of the view of memory at every state AR accepts with the read-only data as in
   the image. *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

Lemma rsa_rd0_ext : forall B : asyms, TfibSyms B -> forall ly S (W : world Img0.rsegs) mem md,
  AR Img0.rsegs B ly S W mem md ->
  arodata_okP Img0.rsegs 0x9a3c0 0x9b7c8 B (aview Img0.rsegs (w_H W) mem) ->
  rd_ext rsa_rd0 (aview Img0.rsegs (w_H W) mem).
Proof.
intros B TS ly S W mem md HAR HRO.
destruct HAR as (M & _).
set (rd := aview Img0.rsegs (w_H W) mem) in *.
pose proof (am_const _ _ _ _ M) as HC. rewrite (ts_const B TS ly), (rsa_pins_split ly) in HC.
apply Forall_app in HC as [_ HC]. rewrite Forall_forall in HC.
pose proof (am_zshadow _ _ _ _ M) as HZ. unfold zshadow_ok, zero_shadow_ranges in HZ.
rewrite (ts_zsh B TS) in HZ. apply Forall_inv_tail in HZ. rewrite Forall_forall in HZ.
clear M.
intros a v H. unfold rsa_rd0 in H.
destruct (find (rsa_pin_at a) rsa_pins) as [c|] eqn:F.
- apply find_some in F as [Hin Hp]. injection H as <-.
  exact (rsa_pin_ok B ly rd c a (HC c Hin) Hp).
- destruct (existsb (rsa_zsh_at a) Tfib_zero_shadow) eqn:EZ.
  + injection H as <-. apply existsb_exists in EZ as (r & Hr & Hz).
    exact (rsa_zsh_ok rd r a (HZ r Hr) Hz).
  + destruct (rsa_in_rob a && negb (existsb (rsa_in_zrb a) Tfib_owned_static) &&
              negb ((TFIB_ERRNO <=? a) && (a <? TFIB_ERRNO + 4))) eqn:EC; [|discriminate H].
    apply andb_prop in EC as [EC E3]. apply andb_prop in EC as [E1 E2].
    assert (P1 : in_roP Img0.rsegs 0x9a3c0 0x9b7c8 a) by exact (rsa_in_rob_ok a E1).
    assert (P2 : ~ Exists (in_zr a) (as_owned_static B))
      by (rewrite (ts_owned B TS); exact (rsa_not_owned_ok a _ E2)).
    assert (P3 : ~ (as_errno B <= a < as_errno B + 4))
      by (rewrite (ts_errno B TS); exact (rsa_not_errno_ok a _ E3)).
    rewrite (HRO a P1 P2 P3). exact H.
Qed.

End s.

(* ============================== checkers over a reader, and their soundness ============================== *)
Lemma rsa_hull_ext : forall (rd rd' : reader) x n, rd_ext rd rd' -> shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof.
intros rd rd' x n EXT HV s Hs. pose proof (HV s Hs) as Hn.
destruct (rd s) as [v|] eqn:E; [|contradiction].
rewrite (EXT s v E). discriminate.
Qed.

(* RPgBase.rl_cstr, conjunct by conjunct, over a reader rd that is a part of the view of memory. *)
Definition rsa_cstr_chk (segs : list Segment) (rd : reader) (a : Z) (s : list Z) : bool :=
  bytes_chk rd a s &&
  oz_eqb (rd (a + Z.of_nat (length s))) 0 &&
  forallb (fun b => (0 <? b) && (b <? 256)) s &&
  (0 <? a) && (a + Z.of_nat (length s) + 1 <=? 2 ^ 63) &&
  img_chk segs a (S (length s)) &&
  amem_rangeb a (Z.of_nat (length s) + 1) &&
  ra_chk rd SHADOW_OFF a (S (length s)) &&
  hull_chk rd a (Z.of_nat (length s) + 1).
Lemma rsa_cstr_chk_ok : forall segs H mem rd a s,
  rd_ext rd (aview segs H mem) -> rsa_cstr_chk segs rd a s = true -> rl_cstr segs H mem a s.
Proof.
intros segs H mem rd a s EXT Hc. unfold rd_ext in EXT. unfold rsa_cstr_chk in Hc. rewrite !andb_true_iff in Hc.
destruct Hc as [[[[[[[[C1 C2] C3] C4] C5] C6] C7] C8] C9].
unfold rl_cstr.
split; [intros i Hi; apply EXT; exact (bytes_chk_ok _ _ _ C1 i Hi)|].
split; [apply EXT; exact (oz_eqb_ok _ _ C2)|].
split; [exact (bytes_range_ok _ C3)|].
split; [apply Z.ltb_lt; exact C4|].
split; [apply Z.leb_le; exact C5|].
split; [intros i Hi; apply (img_chk_ok _ _ _ C6); lia|].
split; [exact (amem_rangeb_ok _ _ C7)|].
split; [apply (range_addressable_ext rd); [exact EXT|]; apply (ra_chk_ok _ _ _ (S (length s))); [lia | exact C8]|].
exact (rsa_hull_ext rd _ a _ EXT (hull_chk_ok _ _ _ C9)).
Qed.

(* YI04.val_mem over a reader rd that is a part of the view of memory (val_mem reads YO0f.le_byte). *)
Definition rsa_val_chk (rd : reader) (a : Z) (n : nat) (v : Z) : bool :=
  forallb (fun k => oz_eqb (rd (a + Z.of_nat k)) (YO0f.le_byte v n k)) (seq 0 n).
Lemma rsa_val_chk_ok : forall segs H mem rd a n v,
  rd_ext rd (aview segs H mem) -> rsa_val_chk rd a n v = true -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem rd a n v EXT Hc. unfold rd_ext in EXT. unfold val_mem. intros k Hk. unfold rsa_val_chk in Hc.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. apply oz_eqb_ok in E. apply EXT in E.
unfold aview in E.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|]; cbn [option_map] in E; [|discriminate E].
injection E as E. rewrite <- E, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* Both readings are present and equal. *)
Definition rsa_opt_eqb (o1 o2 : option Z) : bool :=
  match o1, o2 with Some x, Some y => x =? y | _, _ => false end.
Lemma rsa_opt_eqb_ok : forall o1 o2, rsa_opt_eqb o1 o2 = true -> exists v, o1 = Some v /\ o2 = Some v.
Proof.
intros [x|] [y|] H; cbn [rsa_opt_eqb] in H; try discriminate H.
apply Z.eqb_eq in H. subst y. exists x. split; reflexivity.
Qed.

(* The bytes of the owned range r that lie in the segment sg: [rsa_lo r sg, rsa_hi r sg). *)
Definition rsa_lo (r : Z * Z) (sg : Segment) : Z := Z.max (fst r) (Z.of_N (seg_base sg)).
Definition rsa_hi (r : Z * Z) (sg : Segment) : Z := Z.min (fst r + snd r) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)).
(* Each owned byte of a non-writable segment reads, in rsa_rd0, as the image's byte (so a const cell pins it with that
   byte: the owned bytes are outside rsa_rd0's read-only branch). The writable segments are skipped by an `if`, not by
   `||`: vm_compute evaluates both arguments of orb, and the owned range (0xa2ed0, ...) meets a writable segment in
   5.4 MB. *)
Definition rsa_rom_pin_chk : bool :=
  forallb (fun r => forallb (fun sg => if seg_writable sg then true else
    forallb (fun k => rsa_opt_eqb (rsa_rd0 (rsa_lo r sg + Z.of_nat k)) (RPgSat.img_byte Img0.rsegs (rsa_lo r sg + Z.of_nat k)))
      (seq 0 (Z.to_nat (rsa_hi r sg - rsa_lo r sg)))) Img0.rsegs) Tfib_owned_static.
Lemma rsa_rom_pin : rsa_rom_pin_chk = true ->
  forall r sg a, In r Tfib_owned_static -> In sg Img0.rsegs -> seg_writable sg = false -> in_zr a r ->
  Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg) ->
  exists v, rsa_rd0 a = Some v /\ RPgSat.img_byte Img0.rsegs a = Some v.
Proof.
intros Hc r sg a Hr Hsg Hw Hz Ha.
assert (L : rsa_lo r sg <= a < rsa_hi r sg) by (unfold in_zr in Hz; unfold rsa_lo, rsa_hi; lia).
clear Hz Ha.
unfold rsa_rom_pin_chk in Hc. rewrite forallb_forall in Hc.
specialize (Hc r Hr). cbv beta in Hc. rewrite forallb_forall in Hc. specialize (Hc sg Hsg). cbv beta in Hc.
rewrite Hw in Hc. cbv iota in Hc.
set (lo := rsa_lo r sg) in *. set (hi := rsa_hi r sg) in *.
assert (Hk : (Z.to_nat (a - lo) < Z.to_nat (hi - lo))%nat) by lia.
pose proof (forallb_seq _ _ Hc _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
replace (lo + (a - lo)) with a in E by ring.
exact (rsa_opt_eqb_ok _ _ E).
Qed.

(* The errno word lies in no non-writable segment. *)
Definition rsa_errno_chk : bool :=
  forallb (fun sg => seg_writable sg || (Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? TFIB_ERRNO) ||
    (TFIB_ERRNO + 4 <=? Z.of_N (seg_base sg))) Img0.rsegs.
Lemma rsa_errno_rom : rsa_errno_chk = true ->
  forall sg a, In sg Img0.rsegs -> seg_writable sg = false ->
  Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg) -> ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4).
Proof.
intros Hc sg a Hsg Hw Ha He. unfold rsa_errno_chk in Hc. rewrite forallb_forall in Hc.
specialize (Hc sg Hsg). cbv beta in Hc. rewrite Hw in Hc. cbn [orb] in Hc.
apply orb_true_iff in Hc as [Hc|Hc]; [apply Z.leb_le in Hc | apply Z.leb_le in Hc]; lia.
Qed.

(* ======================================== the closed checks ======================================== *)
(* 1. The 49 registered globals (hi_globs: address, size) are addressable. *)
Lemma rsa_globs_chk : ranges_chk rsa_rd0 (fun a => a) (hi_globs role_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
(* 2. The 41 strings. *)
Lemma rsa_strs_chk : forallb (fun c => rsa_cstr_chk Img0.rsegs rsa_rd0 (fst c) (snd c)) (hi_strs role_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
(* 3. The 38 read-only cells. *)
Lemma rsa_cells_chk : forallb (fun c => rsa_val_chk rsa_rd0 (fst c) 8 (snd c)) (hi_cells role_himg_B) = true.
Proof. vm_compute. reflexivity. Qed.
(* 4. The owned bytes of the non-writable segments are pinned with the image's bytes; the errno word is not in them. *)
Lemma rsa_rom_pin_chk_ok : rsa_rom_pin_chk = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rsa_errno_chk_ok : rsa_errno_chk = true.
Proof. vm_compute. reflexivity. Qed.
(* The count of owned bytes in the non-writable segments that check 4 reads. *)
Lemma rsa_rom_pin_count :
  fold_right Z.add 0 (map (fun r => fold_right Z.add 0 (map (fun sg =>
    if seg_writable sg then 0 else Z.max 0 (rsa_hi r sg - rsa_lo r sg)) Img0.rsegs)) Tfib_owned_static) = 1417.
Proof. vm_compute. reflexivity. Qed.

(* ======================================== the law ======================================== *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

Theorem rh_static_B : forall B : asyms, TfibSyms B -> rh_static_law Img0.rsegs B 0x9a3c0 0x9b7c8.
Proof.
intros B TS ly S W mem md HAR HRO.
pose proof (rsa_rd0_ext B TS ly S W mem md HAR HRO) as EXT.
clear HAR.
split; [|split; [|split]].
- pose proof (ranges_chk_ok _ _ _ rsa_globs_chk) as F.
  eapply Forall_impl; [|exact F]. intros g Hg. cbv beta in Hg.
  exact (range_addressable_ext _ _ _ _ _ EXT Hg).
- apply Forall_forall. intros c Hc. apply (rsa_cstr_chk_ok Img0.rsegs (w_H W) mem rsa_rd0); [exact EXT|].
  pose proof rsa_strs_chk as E. rewrite forallb_forall in E. exact (E c Hc).
- unfold rl_ro_cells. apply Forall_forall. intros c Hc.
  apply (rsa_val_chk_ok Img0.rsegs (w_H W) mem rsa_rd0); [exact EXT|].
  pose proof rsa_cells_chk as E. rewrite forallb_forall in E. exact (E c Hc).
- intros a Ha. hnf in Ha. destruct Ha as (sg & Hsg & Hw & Hr).
  destruct (existsb (rsa_in_zrb a) Tfib_owned_static) eqn:EO.
  + apply existsb_exists in EO as (r & Hr' & Hz). apply rsa_in_zrb_ok in Hz.
    destruct (rsa_rom_pin rsa_rom_pin_chk_ok r sg a Hr' Hsg Hw Hz Hr) as (v & E1 & E2).
    rewrite (EXT a v E1). symmetry. exact E2.
  + apply (HRO a).
    * unfold in_roP. left. exists sg. split; [exact Hsg|]. split; [exact Hw | exact Hr].
    * rewrite (ts_owned B TS). apply rsa_not_owned_ok. rewrite EO. reflexivity.
    * rewrite (ts_errno B TS). exact (rsa_errno_rom rsa_errno_chk_ok sg a Hsg Hw Hr).
Qed.

End t.

(* The read-only range lies in the image (its third PT_LOAD, [0x9a388, 0x9c000), holds .data.rel.ro and .got). *)
Lemma rh_relro_img : forall a, RPgLib.RO_LO <= a < RPgLib.RO_HI -> in_img Img0.rsegs a.
Proof.
intros a Ha. unfold RPgLib.RO_LO, RPgLib.RO_HI in Ha. apply in_imgb_ok. unfold in_imgb.
assert (E : existsb (fun sg => (Z.of_N (seg_base sg) <=? 0x9a3c0) &&
  (0x9b7c8 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) Img0.rsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in E as (sg & Hin & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
apply existsb_exists. exists sg. split; [exact Hin|]. cbv beta.
apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* The law at the closing's symbols and segments: lib/AU/YD2l.v TfibB (TfibB_syms) over lib/AU/YB1v.v tfibsegs (the
   same loaded segments as Img0.rsegs) and lib/AU/RPgLib.v's read-only range. *)
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Theorem rh_static_TfibB : rh_static_law YB1v.tfibsegs YD2l.TfibB RPgLib.RO_LO RPgLib.RO_HI.
Proof. exact (rh_static_B YD2l.TfibB YD2l.TfibB_syms). Qed.
End u.
