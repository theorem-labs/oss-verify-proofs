(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/PN102S2Help.v, with its module paths and module names changed; 154 of its 193 lines of code are new or changed and 567 lines of the source are left out. *)
(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): THE STATIC FACTS OF
   RPgCSpec.rl_seg_pre AT EVERY STATE THE MEMORY-CHECKING RUNTIME'S RELATION AR ACCEPTS. e01_static_law proves
   lib/A/RPgHarn.v rh_static_law at image A's loaded segments rsegs and the read-only range [0x9a120, 0x9b528): at
   every state AR accepts with the read-only data as in the image (arodata_okP), the 49 registered globals of
   RPgImgA.role_himg_A are addressable, its 41 strings satisfy rl_cstr, its read-only cells hold their values, and
   every byte of a read-only segment reads as the image's (rom_view). It takes four facts of the runtime's symbol
   record B:
   - e01_globs_marked: each registered global's shadow bytes are the runtime's (0 per full granule, size mod 8 on the
     last partial one);
   - e01_img_shadow_vis: every shadow byte of the image's range [IMG_LO, IMG_TOP) is mapped;
   - e01_rom_owned: the read-only bytes arodata_okP leaves out (owned by the runtime's static tables, or the errno
     cell) read as the image's;
   - e01_relro_unowned: the .data.rel.ro cells of hi_cells are neither owned nor the errno cell.
   The 41 strings and the 36 cells are checked on the image by one boolean checker each (e01_strs_chk,
   e01_cells_chk), proved by computation on the closed image and read through checker-soundness lemmas.
   proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk, the law the chaining takes at the two
   middle contracts' starts) *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YImgTop YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgSat RPgHarn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================== the four facts of B ======================================== *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* every registered global's shadow bytes: 0 per full granule, size mod 8 on the last partial one *)
Definition e01_globs_marked (B : asyms) : Prop :=
forall ly S (W : world rsegs) mem md q sz, In (q, sz) (hi_globs role_himg_A) -> AR rsegs B ly S W mem md ->
block_shadow (aview rsegs (w_H W) mem) SHADOW_OFF q sz.
(* every shadow byte of the image's range is mapped (the guard and gap granules the strings' 64-byte hulls reach) *)
Definition e01_img_shadow_vis (B : asyms) : Prop :=
forall ly S (W : world rsegs) mem md a, AR rsegs B ly S W mem md -> YImgTop.IMG_LO <= a < YImgTop.IMG_TOP ->
aview rsegs (w_H W) mem (shadow_addr a) <> None.
(* the read-only bytes arodata_okP leaves out (owned by the runtime's static tables, or the errno cell) read as
   the image's *)
Definition e01_rom_owned (B : asyms) : Prop :=
forall ly S (W : world rsegs) mem md a, AR rsegs B ly S W mem md -> in_rom rsegs a ->
(Exists (in_zr a) (as_owned_static B) \/ as_errno B <= a < as_errno B + 4) ->
aview rsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom rsegs (Z_to_bv 64 a)).
(* the .data.rel.ro cells of hi_cells are neither owned nor the errno cell *)
Definition e01_relro_unowned (B : asyms) : Prop :=
forall c i, In c (hi_cells role_himg_A) -> ~ in_rom rsegs (fst c) -> 0 <= i < 8 ->
~ Exists (in_zr (fst c + i)) (as_owned_static B) /\ ~ (as_errno B <= fst c + i < as_errno B + 4).
End b.

(* ======================================== checkers on the image ======================================== *)
(* a lies in a read-only loaded segment (YG0d.in_rom), as a boolean *)
Definition e01_romb (a : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
                     (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) rsegs.
Lemma e01_romb_ok : forall a, e01_romb a = true -> in_rom rsegs a.
Proof.
intros a H. unfold e01_romb in H. apply existsb_exists in H. destruct H as (sg & Hin & Hb).
cbv beta in Hb. rewrite !andb_true_iff in Hb. destruct Hb as [[Hw H1] H2]. apply negb_true_iff in Hw.
apply Z.leb_le in H1. apply Z.ltb_lt in H2.
exists sg. split; [exact Hin|]. split; [exact Hw | lia].
Qed.
Lemma e01_romb_false : forall a, e01_romb a = false -> ~ in_rom rsegs a.
Proof.
intros a H (sg & Hin & Hw & Hb). unfold e01_romb in H.
assert (E : existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
                     (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) rsegs = true).
{ apply existsb_exists. exists sg. split; [exact Hin|]. cbv beta. rewrite Hw. cbn [negb andb].
  apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite H in E. discriminate E.
Qed.

(* One string (a, s) of hi_strs: its bytes and the NUL are the image's, every one in a read-only segment; its bytes
   are in (0, 256); its bounds; it lies below kLowMemEnd; (a, len + 1) is a registered global of hi_globs; and it is
   64 bytes or more inside the image's range at both ends (so its shadow hull lies in the image's shadow). *)
Definition e01_str_chk (c : Z * list Z) : bool :=
  img_bytes_chk rsegs (fst c) (snd c ++ [0]) &&
  forallb (fun k => e01_romb (fst c + Z.of_nat k)) (seq 0 (S (length (snd c)))) &&
  forallb (fun b => (0 <? b) && (b <? 256)) (snd c) &&
  (0 <? fst c) && (fst c + Z.of_nat (length (snd c)) + 1 <=? 2 ^ 63) &&
  amem_rangeb (fst c) (Z.of_nat (length (snd c)) + 1) &&
  existsb (fun g => (fst g =? fst c) && (snd g =? Z.of_nat (length (snd c)) + 1)) (hi_globs role_himg_A) &&
  (YImgTop.IMG_LO + 64 <=? fst c) && (fst c + (Z.of_nat (length (snd c)) + 1) + 64 <=? YImgTop.IMG_TOP).
Lemma e01_strs_chk : forallb e01_str_chk (hi_strs role_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.

(* One cell (a, v) of hi_cells: its 8 bytes are v's in the image, and either all 8 lie in a read-only segment, or a
   is in no read-only segment and the 8 bytes lie in [0x9a120, 0x9b528). *)
Definition e01_cell_chk (c : Z * Z) : bool :=
  img_val_chk rsegs (fst c) 8 (snd c) &&
  (forallb (fun k => e01_romb (fst c + Z.of_nat k)) (seq 0 8) ||
   (negb (e01_romb (fst c)) && (0x9a120 <=? fst c) && (fst c + 8 <=? 0x9b528))).
Lemma e01_cells_chk : forallb e01_cell_chk (hi_cells role_himg_A) = true.
Proof. vm_compute. reflexivity. Qed.

(* ======================================== the law ======================================== *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma e01_rng_dec : forall lo a hi, {lo <= a < hi} + {~ (lo <= a < hi)}.
Proof.
intros lo a hi. destruct (Z_le_dec lo a); destruct (Z_lt_dec a hi); [left; lia | right; lia | right; lia | right; lia].
Qed.

(* rom_view: an owned byte or the errno cell from e01_rom_owned, every other read-only byte from arodata_okP. *)
Lemma e01_rom : forall B ly S (W : world rsegs) mem md,
  e01_rom_owned B -> AR rsegs B ly S W mem md -> arodata_okP rsegs 0x9a120 0x9b528 B (aview rsegs (w_H W) mem) ->
  rom_view rsegs W mem.
Proof.
intros B ly S W mem md HO HAR HRO a Ha.
destruct (@Exists_dec (Z * Z) (in_zr a) (as_owned_static B)
  (fun r : Z * Z => e01_rng_dec (fst r) a (fst r + snd r))) as [Hown|Hnown].
- exact (HO ly S W mem md a HAR Ha (or_introl Hown)).
- destruct (e01_rng_dec (as_errno B) a (as_errno B + 4)) as [He|Hne].
  + exact (HO ly S W mem md a HAR Ha (or_intror He)).
  + assert (Hr : in_roP rsegs 0x9a120 0x9b528 a) by (unfold in_roP; left; exact Ha).
    exact (HRO a Hr Hnown Hne).
Qed.

(* A byte that reads as the image's through aview is the image's byte through mbyte. *)
Lemma e01_mbyte_of_view : forall H mem a b,
  aview rsegs H mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom rsegs (Z_to_bv 64 a)) ->
  seg_rom rsegs (Z_to_bv 64 a) = Some b -> mbyte rsegs (mrestrict H mem) a = Some b.
Proof.
intros H mem a b E R. rewrite R in E. unfold aview in E.
destruct (mbyte rsegs (mrestrict H mem) a) as [b'|] eqn:M; cbn [option_map] in E; [|discriminate E].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* The shadow hull of [a, a + n) lies in the image's shadow when [a - 64, a + n + 64) lies in the image's range. *)
Lemma e01_hull : forall B ly S (W : world rsegs) mem md a n,
  e01_img_shadow_vis B -> AR rsegs B ly S W mem md -> 0 < n ->
  YImgTop.IMG_LO + 64 <= a -> a + n + 64 <= YImgTop.IMG_TOP ->
  shadow_hull_vis (aview rsegs (w_H W) mem) a n.
Proof.
intros B ly S W mem md a n HV HAR Hn Hlo Hhi s Hs.
unfold shadow_addr in Hs.
set (x := 8 * (s - SHADOW_OFF)).
assert (Hx : shadow_addr x = s).
{ unfold shadow_addr, x. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
assert (Hdlo : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_mod a 8 ltac:(lia)) as Ha8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ha8b.
pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)) as Hb8. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as Hb8b.
pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)) as Hc8b.
pose proof (Z.div_mod (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)) as Hd8b.
assert (Hxlo : YImgTop.IMG_LO <= x) by (unfold x; lia).
assert (Hxhi : x < YImgTop.IMG_TOP) by (unfold x; lia).
rewrite <- Hx. exact (HV ly S W mem md x HAR (conj Hxlo Hxhi)).
Qed.

(* A global of hi_globs is addressable over its size. *)
Lemma e01_glob_ra : forall B ly S (W : world rsegs) mem md q sz,
  e01_globs_marked B -> In (q, sz) (hi_globs role_himg_A) -> AR rsegs B ly S W mem md ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF q sz.
Proof.
intros B ly S W mem md q sz HG Hin HAR.
exact (block_shadow_range _ _ q sz q sz (HG ly S W mem md q sz Hin HAR) (Z.le_refl q) (Z.le_refl (q + sz))).
Qed.

(* One string of hi_strs, from its checker. *)
Lemma e01_cstr : forall B ly S (W : world rsegs) mem md c,
  e01_globs_marked B -> e01_img_shadow_vis B -> AR rsegs B ly S W mem md -> rom_view rsegs W mem ->
  e01_str_chk c = true -> rl_cstr rsegs (w_H W) mem (fst c) (snd c).
Proof.
intros B ly S W mem md [a s] HG HV HAR HROM Hc. cbn [fst snd] in Hc |- *.
unfold e01_str_chk in Hc. cbn [fst snd] in Hc. rewrite !andb_true_iff in Hc.
destruct Hc as [[[[[[[[C1 C2] C3] C4] C5] C6] C7] C8] C9].
(* each byte a + i, 0 <= i <= len, lies in a read-only segment and reads as the image's *)
assert (Hrom : forall i, 0 <= i <= Z.of_nat (length s) -> in_rom rsegs (a + i)).
{ intros i Hi. assert (Hk : (Z.to_nat i < Datatypes.S (length s))%nat) by lia.
  pose proof (forallb_seq _ _ C2 _ Hk) as E. cbv beta in E. rewrite Z2Nat.id in E by lia.
  exact (e01_romb_ok _ E). }
assert (Himg : forall i, 0 <= i < Z.of_nat (length s) + 1 ->
  img_byte rsegs (a + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0)).
{ intros i Hi. change (bytes_chk (img_byte rsegs) a (s ++ [0]) = true) in C1.
  apply (bytes_chk_ok _ _ _ C1). rewrite length_app. cbn [length]. lia. }
assert (Hview : forall i, 0 <= i <= Z.of_nat (length s) ->
  aview rsegs (w_H W) mem (a + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0)).
{ intros i Hi. rewrite (HROM (a + i) (Hrom i Hi)). exact (Himg i ltac:(lia)). }
unfold rl_cstr.
split.
{ intros i Hi. rewrite (Hview i ltac:(lia)). rewrite app_nth1 by lia. reflexivity. }
split.
{ rewrite (Hview (Z.of_nat (length s)) ltac:(lia)). rewrite Nat2Z.id, app_nth2 by lia. rewrite Nat.sub_diag.
  reflexivity. }
split; [exact (bytes_range_ok _ C3)|].
split; [apply Z.ltb_lt; exact C4|].
split; [apply Z.leb_le; exact C5|].
split.
{ intros i Hi. destruct (Hrom i Hi) as (sg & Hin & _ & Hb). exists sg. split; [exact Hin | exact Hb]. }
split; [exact (amem_rangeb_ok _ _ C6)|].
split.
{ apply existsb_exists in C7. destruct C7 as ([q sz] & Hin & Hg). cbn [fst snd] in Hg.
  apply andb_true_iff in Hg. destruct Hg as [Hq Hsz]. apply Z.eqb_eq in Hq. apply Z.eqb_eq in Hsz. subst q sz.
  exact (e01_glob_ra B ly S W mem md a (Z.of_nat (length s) + 1) HG Hin HAR). }
apply Z.leb_le in C8. apply Z.leb_le in C9.
exact (e01_hull B ly S W mem md a (Z.of_nat (length s) + 1) HV HAR ltac:(lia) C8 C9).
Qed.

(* One cell of hi_cells, from its checker. *)
Lemma e01_cell : forall B (W : world rsegs) mem c,
  e01_relro_unowned B -> arodata_okP rsegs 0x9a120 0x9b528 B (aview rsegs (w_H W) mem) -> rom_view rsegs W mem ->
  In c (hi_cells role_himg_A) -> e01_cell_chk c = true -> val_mem rsegs (mrestrict (w_H W) mem) (fst c) 8 (snd c).
Proof.
intros B W mem c HU HRO HROM Hin Hc. unfold e01_cell_chk in Hc.
apply andb_prop in Hc. destruct Hc as [Cv Cr].
intros k Hk. pose proof (img_val_chk_ok rsegs (fst c) 8 (snd c) Cv k Hk) as Hi.
apply (e01_mbyte_of_view (w_H W) mem (fst c + Z.of_nat k) _); [|exact Hi].
apply orb_true_iff in Cr. destruct Cr as [Cr|Cr].
- pose proof (forallb_seq _ _ Cr _ Hk) as E. cbv beta in E.
  exact (HROM _ (e01_romb_ok _ E)).
- rewrite !andb_true_iff in Cr. destruct Cr as [[Cn C1] C2].
  apply negb_true_iff in Cn. apply Z.leb_le in C1. apply Z.leb_le in C2.
  destruct (HU c (Z.of_nat k) Hin (e01_romb_false _ Cn) ltac:(lia)) as [Ho He].
  assert (Hr : in_roP rsegs 0x9a120 0x9b528 (fst c + Z.of_nat k)) by (unfold in_roP; right; lia).
  exact (HRO _ Hr Ho He).
Qed.

Theorem e01_static_law : forall B : asyms,
e01_globs_marked B -> e01_img_shadow_vis B -> e01_rom_owned B -> e01_relro_unowned B ->
rh_static_law rsegs B 0x9a120 0x9b528.
Proof.
intros B HG HV HO HU. unfold rh_static_law. intros ly S W mem md HAR HRO.
pose proof (e01_rom B ly S W mem md HO HAR HRO) as HROM.
split; [|split; [|split]].
- apply Forall_forall. intros [q sz] Hin. cbn [fst snd].
  exact (e01_glob_ra B ly S W mem md q sz HG Hin HAR).
- apply Forall_forall. intros c Hin.
  pose proof e01_strs_chk as E. rewrite forallb_forall in E.
  exact (e01_cstr B ly S W mem md c HG HV HAR HROM (E c Hin)).
- unfold rl_ro_cells. apply Forall_forall. intros c Hin.
  pose proof e01_cells_chk as E. rewrite forallb_forall in E.
  exact (e01_cell B W mem c HU HRO HROM Hin (E c Hin)).
- exact HROM.
Qed.
End c.
Print Assumptions e01_static_law.
