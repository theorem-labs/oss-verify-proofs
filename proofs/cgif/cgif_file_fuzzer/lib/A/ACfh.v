(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI00 YI04 YI09 YI08 YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w YI5z YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI17 YE00 YE01 YE02 YE03.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0a YC7x YC21.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACfn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACfm ACf5 AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Export YC5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variable B : asyms.
Lemma ajournal_fp_nil : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_mono; [|exact Hio]; intros Ho; exfalso; exact (sink_closed_nil Ho)|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
split; [intros p n i H1 H2 Hi _; apply (F2 p n i H1 H2 Hi); apply inFP_nil|].
split; [intros a Hi Hns He _; apply (F3 a Hi Hns He); apply fp_spares_closed; intros Ho; exact (sink_closed_nil Ho)|].
split; [intros cid pos a H1 H2 _; apply (F4 cid pos a H1 H2); apply inFP_nil|].
split; [intros p n i H1 H2 Hi; exfalso; exact (inFP_nil _ (Hgone p n i H1 H2 Hi))|].
split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.
End e.
Section f.
Variable segs : list Segment.
Lemma srz_enter : forall (W : world segs) (c : config) (T : TSet),
AI segs (w_H W) (w_A W) (cfg_model c) ->
SRr segs W c (fun W' c' => AI segs (w_H W') (w_A W') (cfg_model c') -> srealizes segs c' T) -> srealizes segs c T.
Proof. intros W c T HAI HS. apply (HS HAI T). intros W' c' _ HAI' HK. exact (HK HAI'). Qed.
End f.
Definition aff_tree (K : lleaf -> TSet) (fs : Fs.Fs) (P : list Z) : TSet :=
match ff_cfg P with
| None => ff_leaf K fs
| Some (g, loops, rest) =>
if g_opens g
then openat_shape fs (ff_unl K fs) (ff_unl K (Fs.fs_set fs sink_path (bytes (ff_content g loops rest))))
else ff_unl K fs
end.
Lemma ff_libk_aff_tree : forall pl fs K, ff_libk pl fs K = aff_tree K fs (zbytes pl).
Proof. intros. reflexivity. Qed.
Definition hdr_ngp (P : list Z) : Z := nth 12 P 0 + 256 * nth 13 P 0.
Lemma hdr5_bytes : forall P, (14 <= length P)%nat ->
hdr5 P = (false, (nth 0 P 0 + 256 * nth 1 P 0, nth 2 P 0 + 256 * nth 3 P 0,
nth 4 P 0 + 256 * nth 5 P 0 + 65536 * nth 6 P 0 + 16777216 * nth 7 P 0,
nth 8 P 0 + 256 * nth 9 P 0 + 65536 * nth 10 P 0 + 16777216 * nth 11 P 0,
nth 12 P 0 + 256 * nth 13 P 0), skipn 14 P).
Proof.
intros P HP. rewrite hdr5_ok by lia.
do 14 (destruct P as [|? P]; [cbn in HP; lia|]). cbn [firstn skipn nth]. rewrite !le_bytes_2, !le_bytes_4. reflexivity.
Qed.
Section h.
#[local] Abbreviation rd0 cx := (mrestrict (w_H (c_W cx)) (c_mem cx)).
Lemma val_mem1_inj : forall (m : word -> option byte) a u v,
val_mem tfibsegs m a 1 u -> val_mem tfibsegs m a 1 v -> 0 <= u < 256 -> 0 <= v < 256 -> u = v.
Proof.
intros m a u v Hu Hv Ru Rv.
specialize (Hu 0%nat ltac:(lia)). specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hu, Hv. rewrite Hu in Hv. injection Hv as E.
unfold YO0f.le_byte in E. change (8 * Z.of_nat 0) with 0 in E. change (2 ^ (8 * Z.of_nat 1)) with 256 in E.
rewrite !Z.shiftr_0_r, !(Z.mod_small u 256), !(Z.mod_small v 256) in E by lia.
change (bv_unsigned (Z_to_bv 8 u) = bv_unsigned (Z_to_bv 8 v)) in E.
rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 8) with 256 in E. rewrite !Z.mod_small in E by lia. exact E.
Qed.
Lemma PB_nth : forall cx pl (j : nat) b,
garr8 tfibsegs (rd0 cx) (c_p cx) (zbytes pl) -> PB cx (Z.of_nat j) b -> (j < length pl)%nat -> nth j (zbytes pl) 0 = b.
Proof.
intros cx pl j b HG [Rb Vb] Hj.
assert (Hj' : (j < length (zbytes pl))%nat) by (unfold zbytes; rewrite length_map; exact Hj).
destruct (HG j Hj') as [Hv Hr]. exact (val_mem1_inj _ _ _ _ Hv Vb Hr Rb).
Qed.
Lemma hdr_prov_hdr5 : forall cx pl attr gen w16 h16 ngp,
garr8 tfibsegs (rd0 cx) (c_p cx) (zbytes pl) -> hdr_prov cx attr gen w16 h16 ngp -> (14 <= length pl)%nat ->
hdr5 (zbytes pl) = (false, (w16, h16, attr mod 2 ^ 32, gen mod 2 ^ 32, ngp), skipn 14 (zbytes pl)).
Proof.
intros cx pl attr gen w16 h16 ngp HG (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & b8 & b9 & b10 & b11 & b12 & b13 &
P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & Ew & Eh & Ea & Eg & En) Hlen.
rewrite hdr5_bytes by (unfold zbytes; rewrite length_map; exact Hlen).
rewrite (PB_nth cx pl 0 b0 HG P0), (PB_nth cx pl 1 b1 HG P1), (PB_nth cx pl 2 b2 HG P2), (PB_nth cx pl 3 b3 HG P3),
(PB_nth cx pl 4 b4 HG P4), (PB_nth cx pl 5 b5 HG P5), (PB_nth cx pl 6 b6 HG P6), (PB_nth cx pl 7 b7 HG P7),
(PB_nth cx pl 8 b8 HG P8), (PB_nth cx pl 9 b9 HG P9), (PB_nth cx pl 10 b10 HG P10), (PB_nth cx pl 11 b11 HG P11),
(PB_nth cx pl 12 b12 HG P12), (PB_nth cx pl 13 b13 HG P13) by lia.
rewrite Ew, Eh, Ea, Eg, En. reflexivity.
Qed.
Lemma pal_prov_garr8 : forall cx pl pal ngp (m : word -> option byte),
garr8 tfibsegs (rd0 cx) (c_p cx) (zbytes pl) -> pal_prov cx pal ngp m -> 0 <= ngp -> 14 + 3 * ngp <= Z.of_nat (length pl) ->
garr8 tfibsegs m pal (firstn (Z.to_nat (3 * ngp)) (skipn 14 (zbytes pl))).
Proof.
intros cx pl pal ngp m HG Hpp Hngp Hlen j Hj.
assert (Hlz : length (zbytes pl) = length pl) by (unfold zbytes; apply length_map).
rewrite length_firstn, length_skipn, Hlz in Hj.
assert (Hj3 : (j < Z.to_nat (3 * ngp))%nat) by lia.
rewrite nth_firstn. rewrite (proj2 (Nat.ltb_lt _ _) Hj3). rewrite nth_skipn.
destruct (Hpp (Z.of_nat j) ltac:(lia)) as (b & HPB & Hv).
replace (14 + Z.of_nat j) with (Z.of_nat (14 + j)) in HPB by lia.
rewrite (PB_nth cx pl (14 + j) b HG HPB ltac:(lia)). split; [exact Hv | exact (proj1 HPB)].
Qed.
End h.
Section o.
Context {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Definition rt_leaf (cx : rtcx) (pl : list byte) (M : Z) (K : lleaf -> TSet) : Prop :=
forall (l : lleaf) (W' : world tfibsegs) (c' : config),
wle (c_W cx) W' -> AI tfibsegs (w_H W') (w_A W') (cfg_model c') ->
(exists ly' S' regs' mem' md' k,
c' = cfg_at tfibsegs RA_LLVMF regs' mem' md' /\
tfib_lib_post_x B MT XN_LIB (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx) M l ly' S' W' regs' mem' md' k) ->
srealizes tfibsegs c' (K l).
Definition rt_xbase (cx : rtcx) (pl : list byte) (aM : Z) (K : lleaf -> TSet) : Prop :=
c_n cx = Z.of_nat (length pl) /\
garr8 tfibsegs (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_p cx) (zbytes pl) /\
asink_none tfibsegs tfib_K (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_md cx) /\
fd_lookup (m_fds (c_md cx)) (alloc_fd (m_fds (c_md cx))) = None /\
Fs.fs_sorted (m_fs (c_md cx)) = true /\
ameta_inv tfibsegs tfib_K (c_ly cx) (mrestrict (w_H (c_W cx)) (c_mem cx)) aM /\
rt_leaf cx pl aM K /\
c_T cx = XN_LIB (c_n cx).
Lemma asink_none_imgv : forall (B : asyms), asink_img_laws tfibsegs B tfib_K ->
forall (W : world tfibsegs) (m m' : word -> option byte) (md md' : Model),
(forall a, in_img tfibsegs a -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
m_fds md' = m_fds md ->
asink_none tfibsegs tfib_K (mrestrict (w_H W) m) md -> asink_none tfibsegs tfib_K (mrestrict (w_H W) m') md'.
Proof.
intros B0 AIL W m m' md md' Hv Efd (Henv & Hhead & Hn).
assert (FR : forall a, aenv_addr tfib_K a -> mbyte tfibsegs (mrestrict (w_H W) m') a = mbyte tfibsegs (mrestrict (w_H W) m) a).
{ intros a Ha. apply (mbyte_of_aview tfibsegs). apply Hv. exact (proj1 (ail_env _ _ _ AIL a Ha)). }
split; [exact (astdio_env_frame tfibsegs tfib_K _ _ FR Henv)|]. split.
- eapply (val_mem_frame tfibsegs); [|exact Hhead]. intros x Hx. apply FR. unfold aenv_addr, ak_ofl_head, tfib_K in *. cbn in Hx |- *. lia.
- rewrite Efd. exact Hn.
Qed.
Lemma ajournal_closed_io : forall STK sp0 FP ly S (W : world tfibsegs) mem md own ly' S' W' mem' md' k,
~ YI16.sink_open_fp FP ->
ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k Hcl HJ. pose proof HJ as (_ & _ & _ & _ & Hos & _).
destruct (aos_step_closed FP md md' Hcl Hos) as (Efd & Efsys & _ & _).
unfold m_fds, m_fs. rewrite Efd, Efsys. split; reflexivity.
Qed.
Lemma ajournal_nil_io : forall STK sp0 ly S (W : world tfibsegs) mem md own ly' S' W' mem' md' k,
ajournal tfibsegs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof. intros until 0. intros HJ. exact (ajournal_closed_io _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sink_closed_nil HJ). Qed.
Definition rt_PX (cx : rtcx) (fs : Fs.Fs) : alayout -> list (Z * Z) -> world tfibsegs -> (word -> option byte) -> Model -> Prop :=
fun ly bl W m md => asink_none tfibsegs tfib_K (mrestrict (w_H W) m) md /\ m_fs md = fs /\ Fs.fs_sorted fs = true /\
Permutation bl (ablocks B (c_ly cx) (c_S cx)).
End o.
End d.
