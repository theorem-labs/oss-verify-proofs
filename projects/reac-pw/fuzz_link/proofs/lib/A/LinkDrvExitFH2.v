(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE3h.v, with its module paths changed, names TfibSyms -> BoxregSyms and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/AE3h.v, with its module paths and module names changed; 605 of its 757 lines of code are new or changed and 1572 lines of the source are left out. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m YA0e.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE2y AE20 AE7f AE22.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AE3e AE3f AE3g AE6g AE2p AE3i AE3h AE3m AE23 AE36 AE37.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AD2j AD2i AD1t AD20 AD1v AD2h AD2f AD1u AD1w AD1o AD1k.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AD1x AD28 AD1j AsanNoAR AD2l.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AE31 AD1y.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink AMemFile LinkExitFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import LinkDrvExitF LinkDrvExitFT LinkDrvExitFH.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* exf_head_tfa (LinkDrvExitF.v): the exit walk from A_EXIT 0x90688 to 0x9688c, where the open-file head has
   been read into s0 and, on link, is the memory FILE f. The phases are LinkDrvExitFH.v's hH_run1..hH_run5;
   the three intercepted calls are AE23.v's, at havoc bases 37 / 53 / 69, with their released contracts
   (AE36.v x1_realizes / x3_realizes, AE37.v x2_realizes_vals).

   The invariant across the walk is AE23.v's VX, taken over the atexit table and exit's lock only (exm2):
   the walk's regions leave the stdout and stderr FILE windows empty, so VX's frame clause keeps both FILEs,
   the open-file head and every other image cell the caller handed over. VX carries AR up to the module
   destructor 0x8864c; its post (x2_realizes_vals) keeps no AR, so the facts exf_mid needs after it are read
   at that call from AR (the memcpy interceptor's cells, the FILE's block and its shadow) and from the
   destructor's own writes (g_said's shadow reads 0), and carried by the destructor's frame and the frame of
   the last run to the state at 0x9688c. *)

Section q. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.

(* ---------- the bytes the walk may write besides the stack: the atexit table and exit's lock ---------- *)

Definition exm2 (a : Z) : Prop := (0x651c60 <= a < 0x651d90) \/ (0x651e80 <= a < 0x651e84).
Lemma exm2_img : forall a, exm2 a -> img_byte_ok tfibsegs a = true.
Proof.
intros a [H|H].
- exact (zallb_sound _ _ _ a exm_img_bytes_ok1 ltac:(lia)).
- exact (zallb_sound _ _ _ a exm_img_bytes_ok2 ltac:(lia)).
Qed.
Lemma exm2_dec : forall a, exm2 a \/ ~ exm2 a.
Proof. intros a. unfold exm2. lia. Qed.

Definition exw2_ok (t : option nat * Z * Z) : bool :=
band_winb t || win_eqb t (None, 0x651c60, 0x651d90) || win_eqb t (None, 0x651e80, 0x651e84) || (snd t <=? snd (fst t)).
Definition ex2_windows_ok (ss : sstate) : bool := forallb exw2_ok (windows (ss_mem ss)).
Lemma ex2_windows_sound : forall E ss sp0 a,
ex2_windows_ok ss = true -> bv_unsigned (ew E 2) = sp0 ->
in_wrange E (ss_mem ss) a -> vf_band sp0 a \/ exm2 a.
Proof.
intros E ss sp0 a Hb Hsp Hin.
destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr).
unfold ex2_windows_ok in Hb. rewrite forallb_forall in Hb. specialize (Hb _ Ht). unfold exw2_ok in Hb.
repeat (apply orb_prop in Hb as [Hb|Hb]).
- unfold band_winb in Hb. destruct b as [[|[|[|n]]]|]; try discriminate Hb.
  apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.leb_le in H2. subst lo.
  cbn [base_val] in Hr. rewrite Hsp in Hr. left. unfold vf_band. lia.
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. right. unfold exm2. lia.
- apply win_eqb_eq in Hb. injection Hb as -> -> ->. cbn [base_val] in Hr. right. unfold exm2. lia.
- cbn [fst snd] in Hb. apply Z.leb_le in Hb. lia.
Qed.

(* ---------- AE3h.v vf_icpt_xcall_noar over xret_realizes_noar_vals: the whole frame and the written values ---------- *)

Section c1.
Variable B : asyms.
Variable pcx : Z.
Variable XW : Z -> Prop.
Variable XV : Z -> Z.
Variable XPRE : world tfibsegs -> (word -> option byte) -> Prop.
Hypothesis XH : xret_realizes_noar_vals tfibsegs B pcx XW XV XPRE.
Lemma vf_icpt_xcall_noar_vals : forall (W : world tfibsegs) E ss ms md ly S (sp0 : Z) r0 rest k ra osp,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pcx -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 3 = w64 (as_gp B) -> ew E 4 = w64 (as_tp B) ->
ss_mem ss = r0 :: rest -> YP09.r_base r0 = Some 2%nat -> YP09.r_lo r0 = - VF_STK -> YP09.r_hi r0 = 0 ->
YP09.r_wlo r0 = - VF_STK -> YP09.r_whi r0 = 0 ->
sr_get (ss_regs ss) 1 = SLit ra -> sr_get (ss_regs ss) 2 = SOff 2 osp -> sr_get (ss_regs ss) 3 = SOff 3 0 -> sr_get (ss_regs ss) 4 = SOff 4 0 ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
no_cdata (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
mem_atoms_lt k (ss_mem (vf_after_icpt k ss ra osp 0 [])) = true ->
forallb (chunk_inside r0) (YP09.r_chunks r0) = true ->
osp mod 16 = 0 -> ESTACK - VF_STK <= osp -> osp <= 0 -> 4096 <= ra < 2 ^ 47 -> ra mod 4 = 0 ->
(forall r, In r rest -> exists bz, base_val E (YP09.r_base r) = bz /\ 0 <= bz + YP09.r_lo r /\ bz + YP09.r_hi r <= 2 ^ 43) ->
(forall r a, In r rest -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
(is_canary_region r = true \/ ~ aowned B ly S a) /\ ~ XW a) ->
(forall a, XW a -> ~ (sp0 - VF_STK <= a < sp0)) ->
(forall r a (m : word -> option byte), In r rest ->
base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> writable_at tfibsegs m a) ->
AR tfibsegs B ly S W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + VF_STK <= sp0 -> sp0 <= ly_stk_hi ly ->
(forall a, sp0 - VF_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
XPRE W (ms_mem ms) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2,
c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfibsegs (havoc E k (map (getr (ms_regs ms2)) CLOB)) (vf_after_icpt k ss ra osp 0 []) (restrict (w_H W) ms2) /\
aregs_preserved (ms_regs ms) (ms_regs ms2) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + osp - ESTACK <= a < sp0 + osp) -> ~ XW a ->
aview tfibsegs (w_H W) (ms_mem ms2) a = aview tfibsegs (w_H W) (ms_mem ms) a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ XW a -> apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a) /\
(forall a, XW a -> aview tfibsegs (w_H W) (ms_mem ms2) a = Some (XV a))).
Proof.
intros W E ss ms md ly S sp0 r0 rest k ra osp HS Hpc Hrv Usp E3 E4 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0
S1 S2 S3 S4 Hat Hwf2 Hnc2 Hma2 Hci0 Hal Hosp1 Hosp2 Hra Hra4 Hrest HrestX HXWb HrestW
HAR Hsp44 Hsp16 Hstk Htop Hpres HXP.
pose proof Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HVF : VF_STK = 9104) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & Lplo & Lphi & Lbeg).
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 ra) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 1 HS), S1; reflexivity).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 + osp)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 2 HS), S2. cbn [sv_denot]. rewrite Usp. reflexivity. }
assert (R3 : getr regsT 3 = w64 (as_gp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 3 HS), S3. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E3. }
assert (R4 : getr regsT 4 = w64 (as_tp B)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E _ _ 4 HS), S4. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E4. }
assert (HspT : spZ regsT = sp0 + osp).
{ change (spZ regsT) with (bv_unsigned (getr regsT 2)). rewrite R2. apply unsigned_lit_small. lia. }
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT.
pose proof XH as AM. unfold xret_realizes_noar_vals, cfg_at in AM.
rewrite Hshape.
eapply SRr_mono.
{ apply (AM ly S W regsT (ms_mem ms) md); [|exact HXP].
split; [exact HAR|]. split; [rewrite R1; apply YK0s.ret_ok_even; rewrite unsigned_lit_small by lia; lia |].
rewrite HspT. split; [rewrite Z.add_mod, Hsp16, Hal by lia; reflexivity|].
split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hpres; lia|]. split; [exact R3 | exact R4]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HP & Hsbm & Hfr & Hpres2 & Hval).
rewrite HspT in Hfr.
pose proof Hsbm as Hsbm'. unfold same_but_materialized in Hsbm'.
assert (Hraz : w64 (raZ regsT) = Z_to_bv 64 ra) by (unfold raZ, w64; rewrite R1, unsigned_lit_small by lia; reflexivity).
split; [reflexivity|]. exists (mkst regs2 (Z_to_bv 64 ra) mem2 (seg_rom tfibsegs)), (m_vm_materialized md2).
split; [rewrite <- Hsbm', Hraz; reflexivity|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
subst b0 lo0 hi0 wlo0 whi0.
unfold vf_after_icpt in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ss_mem lit_chunks app length Z.of_nat Z.add] in Hwf2, Hnc2, Hma2 |- *.
split; [|split; [exact HP | split; [|split]]].
- rewrite restrict_mkst_fx. cbn [ms_regs mkst].
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfibsegs k E ss regsT regs2 (Z_to_bv 64 pcx) ra
(mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2) rs [] CLOB HS Hat) as SPL end.
cbn [map app fst] in SPL. apply SPL; clear SPL.
+ vm_compute. reflexivity.
+ vm_compute. reflexivity.
+ reflexivity.
+ exact Hma2.
+ intros r Hr. destruct (not_clob_cases r Hr) as [-> | Hcs]; [rewrite !getr_zero; reflexivity|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP. exact Hcs.
+ constructor.
+ split; [exact Hwf2|]. split.
* constructor.
-- destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *. rewrite Usp in *.
split; [exact Hlo|]. split; [exact Hhi|]. split.
{ intros off Ho. apply AE2y.apresent_writable. apply Hpres2; [lia | intros Hx; apply (HXWb _ Hx); lia | apply Hpres; lia]. }
apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk].
apply andb_prop in Hk as [Hk1 _]. apply Z.leb_le in Hk1.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
cbn [YP09.r_lo YP09.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [exact Hb1|].
rewrite <- Hb2. apply AE2y.mbyte_of_aview. apply Hfr; [lia | lia | intros Hx; apply (HXWb _ Hx); lia].
-- apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
eapply (region_ok_transport tfibsegs E E); [exact Hokr | reflexivity | | | | ].
++ intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
cbn beta in Hncc. destruct (YP09.c_val c); [reflexivity | exact I | exact I | discriminate].
++ intros a Ha. apply AE2y.mbyte_of_aview. destruct (HrestX r a Hr Ha) as [_ Hx].
destruct (Hrest r Hr) as (bz & Hbz & Hrl & Hrh). rewrite Hbz in Ha. apply Hfr; [lia | lia | exact Hx].
++ intros a Ha _. apply (HrestW r a _ Hr Ha).
++ apply regions_wf_In with (r := r) in HwfT; [|right; exact Hr]. apply region_wf_facts in HwfT as (_ & _ & Hci). exact Hci.
* eapply pairwise_disjoint_extents; [|exact HpdT]. reflexivity.
- intros a Hr Hs Hx. apply Hfr; assumption.
- exact Hpres2.
- exact Hval.
Qed.
End c1.

(* ---------- the state at 0x9688c: the stack region and the cells read from it ---------- *)

Definition hH_r05 : YP09.region := Eval vm_compute in hd img_ro_region (ss_mem hH_st5).
Definition hH_rest5 : smem := Eval vm_compute in tl (ss_mem hH_st5).
Lemma hH_mem5 : ss_mem hH_st5 = hH_r05 :: hH_rest5.
Proof. vm_compute. reflexivity. Qed.

Lemma val_mem_of_rchunk : forall E (m : word -> option byte) r p b off (n : N) e v,
YP09.region_ok tfibsegs E m r -> YP09.r_base r = Some p -> In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
bv_unsigned (ew E p) = b -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem tfibsegs m (b + off) (N.to_nat n) v.
Proof.
intros E m r p b off n e v HR Hb Hin Hp He Hv Hn.
unfold YP09.region_ok in HR. cbv zeta in HR. destruct HR as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc.
rewrite Hb in Hc. cbn [base_val] in Hc. rewrite Hp in Hc.
exact (val_of_chunk_ok tfibsegs E m b off n e v Hc He Hv Hn).
Qed.

(* exf_consts at 0x9688c: every cell but stderr's three is a literal of the walk's last state; stderr's
   region has no chunks, so its three cells come from the caller *)
Lemma exf_cells_at5 : forall E (m : word -> option byte), mem_ok tfibsegs E m (ss_mem hH_st5) ->
val_mem tfibsegs m 0xa5fa8 8 0 -> val_mem tfibsegs m 0xa5fb0 8 0 -> val_mem tfibsegs m 0xa602c 4 0xffffffff ->
cells_are exf_consts m.
Proof.
intros E m HM H8 H16 H140. unfold cells_are. apply Forall_forall. intros [[a n] v] Hx.
unfold exf_consts in Hx. vm_compute in Hx.
repeat (destruct Hx as [Hq|Hx]; [injection Hq as <- <- <-;
  first [ (apply (xconst_sound E m (ss_mem hH_st5) _ _ _ HM); vm_compute; reflexivity)
        | exact H8 | exact H16 | exact H140 ] |]).
destruct Hx.
Qed.

(* ---------- numeric facts, each on a clean context ---------- *)

Definition dj (lo hi l h : Z) : bool := (hi <=? l) || (h <=? lo).
Lemma dj_sound : forall lo hi l h a, dj lo hi l h = true -> lo <= a < hi -> ~ (l <= a < h).
Proof. intros lo hi l h a H Ha. unfold dj in H. apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia. Qed.
(* a byte below b - VF_STK is under the stack band of any sp0 >= b *)
Lemma nvb : forall sp0 a b, b <= sp0 -> a < b - 9104 -> ~ vf_band sp0 a.
Proof. intros sp0 a b Hs Ha Hb. assert (HV : VF_STK = 9104) by reflexivity. unfold vf_band in Hb. lia. Qed.

(* an interval of the image below 0x654000, off the atexit table, exit's lock and the three image cells the
   intercepted calls write *)
Definition img_iv_ok (lo hi : Z) : bool :=
(0 <=? lo) && (hi <=? 0x654000) && dj lo hi 0x651c60 0x651d90 && dj lo hi 0x651e80 0x651e84 &&
dj lo hi 0xa6d80 0xa6d88 && dj lo hi 0xa7cf0 0xa7cf8 && dj lo hi 0xa6dd0 0xa6dd1.
Lemma img_iv_off : forall sp0 lo hi a, 2 ^ 44 <= sp0 -> img_iv_ok lo hi = true -> lo <= a < hi ->
0 <= a < 2 ^ 64 /\ ~ vf_band sp0 a /\ ~ exm2 a /\ ~ XW2 a /\ ~ XW3 a.
Proof.
intros sp0 lo hi a Hs Hc Ha. unfold img_iv_ok in Hc.
repeat (apply andb_prop in Hc as [Hc ?]). apply Z.leb_le in Hc.
match goal with H : (hi <=? 0x654000) = true |- _ => apply Z.leb_le in H end.
repeat match goal with H : dj lo hi _ _ = true |- _ => apply (dj_sound _ _ _ _ a) in H; [|exact Ha] end.
split; [lia|]. split; [apply (nvb sp0 a (2 ^ 44) Hs); lia|]. split; [unfold exm2; lia|].
split; [intros Hx; unfold XW2 in Hx; lia | unfold XW3; lia].
Qed.
Lemma FINV_IVS_iv : forallb (fun iv => img_iv_ok (fst iv) (snd iv)) FINV_IVS = true.
Proof. vm_compute. reflexivity. Qed.

Lemma high_off : forall a, 0x800be260 <= a -> ~ exm2 a /\ ~ XW2 a /\ ~ XW3 a.
Proof. intros a Ha. split; [unfold exm2; lia|]. split; [intros Hx; unfold XW2 in Hx; lia | unfold XW3; lia]. Qed.

Lemma icpt_off : forall sp0 a, 2 ^ 44 <= sp0 -> 0xa19c8 <= a < 0xab138 -> ~ (0xa6d80 <= a < 0xa6d88) ->
~ (0xa7cf0 <= a < 0xa7cf8) -> 0 <= a < 2 ^ 64 /\ ~ vf_band sp0 a /\ ~ exm2 a /\ ~ XW2 a.
Proof.
intros sp0 a Hs Ha H1 H2. split; [lia|]. split; [apply (nvb sp0 a (2 ^ 44) Hs); lia|].
split; [unfold exm2; lia | intros Hx; unfold XW2 in Hx; lia].
Qed.

(* g_said's shadow is written by the module destructor (XW2) *)
Lemma gsaid_shadow : forall sp0 x, 2 ^ 44 <= sp0 -> 0x62fee0 <= x < 0x62fee0 + 4096 ->
XW2 (shadow_of_addr SHADOW_OFF x) /\ 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\
~ vf_band sp0 (shadow_of_addr SHADOW_OFF x) /\ ~ exm2 (shadow_of_addr SHADOW_OFF x).
Proof.
intros sp0 x Hs Hx. unfold shadow_of_addr, SHADOW_OFF.
split; [unfold XW2; repeat (first [left; lia | right]) |].
split; [lia|]. split; [apply (nvb sp0 _ (2 ^ 44) Hs); lia | unfold exm2; lia].
Qed.
Lemma gsaid_hull : forall sp0 s, 2 ^ 44 <= sp0 ->
shadow_addr 0x62fee0 / 8 * 8 <= s < shadow_addr (0x62fee0 + 4096 - 1) / 8 * 8 + 8 ->
XW2 s /\ 0 <= s < 2 ^ 64 /\ ~ vf_band sp0 s /\ ~ exm2 s.
Proof.
intros sp0 s Hsp Hs. unfold shadow_addr, SHADOW_OFF in Hs.
split.
{ unfold XW2. destruct (Z_lt_le_dec s 0x800bdfdc) as [L|L]; repeat (first [left; lia | right]). }
split; [lia|]. split; [apply (nvb sp0 s (2 ^ 44) Hsp); lia | unfold exm2; lia].
Qed.

(* the FILE's block lies in application memory off the image, so off every byte the walk writes besides
   the stack, and so does its shadow *)
Lemma block_off : forall f a, in_app f AMF_BLOCK -> f <= a < f + AMF_BLOCK -> ~ in_img tfibsegs a ->
~ exm2 a /\ ~ XW2 a /\ ~ XW3 a.
Proof.
intros f a Happ Ha Hni.
assert (NI : ~ (0x10000 <= a < 0x654000))
  by (intros H; apply Hni; apply AD1y.in_img_hull; unfold pcap_img_end, YImgTop.IMG_TOP; lia).
unfold in_app, kLowShadowBeg, kHighMemBeg, AMF_BLOCK in *.
split; [unfold exm2; lia|]. split; [intros Hx; unfold XW2 in Hx; lia | unfold XW3; lia].
Qed.
Lemma bshadow_off : forall sp0 x, 2 ^ 46 <= sp0 -> 0 <= x < 2 ^ 47 -> ~ (0x10000 <= x < 0x654000) ->
0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64 /\ ~ vf_band sp0 (shadow_of_addr SHADOW_OFF x) /\
~ exm2 (shadow_of_addr SHADOW_OFF x) /\ ~ XW2 (shadow_of_addr SHADOW_OFF x).
Proof.
intros sp0 x Hs Hx NI. unfold shadow_of_addr, SHADOW_OFF.
split; [lia|]. split; [apply (nvb sp0 _ (2 ^ 46) Hs); lia|]. split; [unfold exm2; lia|].
intros Hw. unfold XW2 in Hw. lia.
Qed.
Lemma bhull_off : forall sp0 f s, 2 ^ 46 <= sp0 -> 0 <= f -> f + AMF_BLOCK <= 2 ^ 47 ->
(f + AMF_BLOCK <= 0x10000 \/ 0x654000 <= f) ->
shadow_addr f / 8 * 8 <= s < shadow_addr (f + AMF_BLOCK - 1) / 8 * 8 + 8 ->
0 <= s < 2 ^ 64 /\ ~ vf_band sp0 s /\ ~ exm2 s /\ ~ XW2 s.
Proof.
intros sp0 f s Hsp Hf Hf47 Hside Hs. unfold shadow_addr, SHADOW_OFF, AMF_BLOCK in *.
split; [lia|]. split; [apply (nvb sp0 s (2 ^ 46) Hsp); lia|]. split; [unfold exm2; lia|].
intros Hw. unfold XW2 in Hw. lia.
Qed.

Lemma amem_of_app : forall f, in_app f AMF_BLOCK -> amem_range f AMF_BLOCK.
Proof.
intros f Happ. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
unfold in_app, amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, AMF_BLOCK in *. lia.
Qed.

Lemma xr_vf : forall tp a, 0xa5fa0 <= a < 0xa6088 -> ex_cell_range tp a.
Proof. intros tp a Ha. unfold ex_cell_range, vf_file, F_STDERR, FILE_SZ. right. left. lia. Qed.
Lemma xr_vo : forall tp a, 0xa6090 <= a < 0xa6178 -> ex_cell_range tp a.
Proof. intros tp a Ha. unfold ex_cell_range, vo_file, F_STDOUT, FILE_SZ. left. lia. Qed.
Lemma xr_tid : forall tp a, tp - 168 <= a < tp - 164 -> ex_cell_range tp a.
Proof. intros tp a Ha. unfold ex_cell_range. repeat right. exact Ha. Qed.

Section t.
Variable B : asyms.
Hypothesis HB : PcapSyms B.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis XFR : xst_frame_tfa xst.

Local Ltac GEO := unfold STDOUT_BUFA, STDOUT_BSZ, F_STDOUT, F_STDERR, F_STDIN, FILE_SZ,
  A_GOT_canary, A_canary, OSP_X1, OSP_X23, XW1, XW2, XW3, TFIB_TPX, ESTACK in *; lia.

(* IMG_L clips the open-file range out, so the released route through IMG_L0 is closed on link: its head is
   the FILE, not 0. Every other cell is still an image cell of IMG_L, so read them from it directly. *)
Lemma exf_cells_of_img : forall E (m : word -> option byte),
mem_ok tfibsegs E m IMG_L -> cells_are exf_consts m.
Proof.
intros E m HM. unfold cells_are. apply Forall_forall. intros [[a n] v] Hx.
apply (xconst_sound E m IMG_L a n v HM).
unfold exf_consts in Hx. vm_compute in Hx.
repeat (destruct Hx as [Hq|Hx]; [injection Hq as <- <- <-; vm_compute; reflexivity|]). destruct Hx.
Qed.

(* an image range off the runtime's own static ranges is not owned *)
Lemma img_rng_not_owned : forall ly S (W : world tfibsegs) mem md lo hi a,
AR tfibsegs B ly S W mem md ->
forallb (fun r => (fst r + snd r <=? lo) || (hi <=? fst r))%bool Tfib_owned_static = true ->
lo <= a < hi -> hi <= 0x654000 -> 0x10000 <= lo -> ~ aowned B ly S a.
Proof.
intros ly S W mem md lo hi a HAR Hc Ha Hhi Hlo.
apply (tfib_low_not_owned B ly S W mem md a HAR);
  [unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END, pcap_img_end, YImgTop.IMG_TOP; lia|].
exact (tfib_not_owned_static B lo hi a HB Hc Ha).
Qed.

(* exf_head_tfa: the walk, and exf_mid read out of the state it arrives in *)
Theorem exf_head_ok : exf_head_tfa B xst.
Proof.
intros E' W regs mem md ly S usp fs code k f E0u [Ulo Uhi] U16 Htid8 Ha0 Hc02 Hsp R3 R4 HM Hpres
  HAI HAR HTOP Hnev HSO Hfds Hfs HFI Hblk.
pose proof (YG0q.AR_laws_ok tfibsegs B) as LAWS.
pose proof (x1_realizes B LAWS (cov0 B HB)) as X1.
pose proof (x3_realizes B LAWS (completed_free B HB)) as X3.
pose proof (x2_realizes_vals B HB mu0) as X2.
unfold sp_window_lo, sp_window_hi in Ulo, Uhi.
pose proof HTOP as (Htopw & Hslo & Hshi & HCT).
pose proof (YM05.ceil_le_top _ HCT) as CLE. pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
assert (HVF : VF_STK = 9104) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
assert (HTPX : as_tp B = TFIB_TPX) by (rewrite (ts_tp B HB); reflexivity).
pose proof (exf_cells_of_img E' _ HM) as HC.
pose proof (ex_ranges_free B) as XR.
repeat match type of XR with
| PcapSyms B -> _ => specialize (XR HB)
| AR_laws tfibsegs B -> _ => specialize (XR LAWS) end.
destruct (XR ly S W mem md HAR) as [HXown HBown]. clear XR.
assert (Ct : xatom_chk IMG_L (TFIB_TP - 168) 4 8 = true) by (vm_compute; reflexivity).
pose proof (xatom_sound E' _ IMG_L _ _ _ _ HM Ct eq_refl
  ltac:(change (2 ^ (8 * Z.of_N 4)) with 4294967296; lia)) as Htidc.
change (N.to_nat 4) with 4%nat in Htidc.
assert (Cg : xconst_chk IMG_L A_GOT_canary 8 A_canary = true) by (vm_compute; reflexivity).
assert (Cc : xatom_chk IMG_L A_canary 8 41 = true) by (vm_compute; reflexivity).
assert (Cw : xconst_chk IMG_L (F_STDERR + 40) 8 0 = true) by (vm_compute; reflexivity).
assert (Cb : xconst_chk IMG_L (F_STDERR + 56) 8 0 = true) by (vm_compute; reflexivity).
pose proof (xconst_sound E' _ IMG_L _ _ _ HM Cg) as Hgot.
pose proof (xconst_sound E' _ IMG_L _ _ _ HM Cw) as Hew1.
pose proof (xconst_sound E' _ IMG_L _ _ _ HM Cb) as Hew2.
pose proof (xatom_sound E' _ IMG_L _ _ _ _ HM Cc eq_refl
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (u64_range (ew E' 41)))) as Hcan.
change (N.to_nat 8) with 8%nat in Hgot, Hcan, Hew1, Hew2.
pose proof (amf_block_facts tfibsegs B LAWS ly S W mem md f HAR Hblk) as (F16 & F4k & Fceil & Fapp & Fby & _).
assert (Fh47 : f + AMF_BLOCK <= 2 ^ 47)
  by (unfold req_size, AMF_BLOCK in *; cbn in Fceil; unfold ASAN_CEIL in *; lia).
assert (Fbelow : f + AMF_BLOCK <= usp - 65536)
  by (unfold stack_max_size in CLE; lia).
pose proof (exf_file_head W mem f (proj1 HFI)) as Mofl.
assert (Rf : 0 <= f < 2 ^ 64) by (unfold AMF_BLOCK in Fh47; lia).
assert (Uw : sp_window_lo <= usp <= sp_window_hi) by (unfold sp_window_lo, sp_window_hi; lia).
assert (Cx1 : xconst_chk IMG_L 0x651c60 1 0 = true) by (vm_compute; reflexivity).
assert (Cx2 : xconst_chk IMG_L 0x651c68 4 2 = true) by (vm_compute; reflexivity).
assert (Cx3 : xconst_chk IMG_L 0x651c70 8 0x651c78 = true) by (vm_compute; reflexivity).
assert (Cx4 : xconst_chk IMG_L 0x651e80 4 0 = true) by (vm_compute; reflexivity).
pose proof (xconst_sound E' _ IMG_L _ _ _ HM Cx1) as Mx1.
pose proof (xconst_sound E' _ IMG_L _ _ _ HM Cx2) as Mx2.
pose proof (xconst_sound E' _ IMG_L _ _ _ HM Cx3) as Mx3.
pose proof (xconst_sound E' _ IMG_L _ _ _ HM Cx4) as Mx4.
cbn [N.to_nat] in Mx1, Mx2, Mx3, Mx4.
change TFIB_TP with TFIB_TPX in Htidc.
pose proof (exf_entryH W regs mem usp code f (bv_unsigned (ew E' 8)) (bv_unsigned (ew E' 41)) 0 STDOUT_BUFA
  Hsp U16 Uw
  ltac:(rewrite R4; reflexivity) Hpres HC
  Htidc ltac:(lia) Hgot Hcan (u64_range (ew E' 41)) Mofl Rf Mx1 Mx2 Mx3 Mx4) as HS0.
set (XS := fun a => aowned B ly S a \/ XW1 a \/ XW2 a \/ XW3 a).
assert (HFownM : forall a, exm2 a -> ~ aowned B ly S a).
{ intros a Ha. apply HXown. unfold exm2 in Ha. unfold ex_cell_range. destruct Ha as [H|H]; lia. }
assert (Hsp44 : 2 ^ 44 <= spZ regs) by (rewrite Hsp; lia).
assert (Hal16 : spZ regs mod 16 = 0) by (rewrite Hsp, <- Zminus_mod_idemp_l, U16; reflexivity).
assert (Hstk : ly_stk_lo ly + VF_STK <= spZ regs)
  by (rewrite Hsp, Hslo; unfold ASAN_CEIL, stack_max_size, VF_STK, ESTACK in *; lia).
assert (Htop : spZ regs <= ly_stk_hi ly) by (rewrite Hsp, Hshi; unfold kHighMemEnd; lia).
assert (Hband : forall a, vf_band (spZ regs) a -> apresent (w_H W) mem a)
  by (intros a Ha; unfold vf_band in Ha; rewrite Hsp in Ha; apply Hpres; lia).
assert (Usp0 : bv_unsigned (ew (exf_env regs (bv_unsigned (ew E' 8)) (bv_unsigned (ew E' 41)) STDOUT_BUFA 0 f code) 2) = spZ regs)
  by (unfold exf_env; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
set (E0 := exf_env regs (bv_unsigned (ew E' 8)) (bv_unsigned (ew E' 41)) STDOUT_BUFA 0 f code) in *.
assert (G3_0 : ew E0 3 = w64 (as_gp B))
  by (unfold E0, exf_env; rewrite (ew_Ereg_nat regs _ 3 3%bv eq_refl), R3, (ts_gp B HB); reflexivity).
assert (G4_0 : ew E0 4 = w64 (as_tp B))
  by (unfold E0, exf_env; rewrite (ew_Ereg_nat regs _ 4 4%bv eq_refl), R4, (ts_tp B HB); reflexivity).
assert (U4_0 : bv_unsigned (ew E0 4) = as_tp B)
  by (rewrite G4_0; apply unsigned_lit_small; rewrite HTPX; unfold TFIB_TPX; lia).
assert (A32_0 : bv_unsigned (ew E0 32) = bv_unsigned (ew E' 8))
  by (unfold E0, exf_env; rewrite (ew_Ereg_extra regs _ 0); apply unsigned_lit_small; lia).
assert (E10_0 : ew E0 10 = Z_to_bv 64 code)
  by (unfold E0, exf_env; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), Ha0; reflexivity).
assert (E33_0 : ew E0 33 = Z_to_bv 64 (bv_unsigned (ew E' 41)))
  by (unfold E0, exf_env; exact (ew_Ereg_extra regs _ 1)).
set (sp0 := spZ regs) in *.
pose proof (VX_init B ly S W sp0 mem md exm2 XS HAR Hband) as VX0.
unfold cfg_at. change (w64 A_EXIT) with (Z_to_bv 64 A_EXIT).
eapply SRr_bind; [exact (ex_phase W E0 ssf_H hH_st1 _ _ _ HS0 hH_run1)|]. cbv beta.
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). clear HS0.
assert (VX1 : VX B ly S W sp0 mem md exm2 XS (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm2 exm2_img exm2_dec HFownM XS Hstk Htop _ _ (ms_mem ms1) mat1 VX0) as VR.
  rewrite ?wvb_wvb in VR. apply VR.
  - intros x Hx1 Hx2. apply HF1. intros Hin.
    destruct (ex2_windows_sound E0 ssf_H sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw];
    [exact (Hx1 Hw) | exact (Hx2 Hw)].
  - intros x Hx1 Hx2. apply HFr1. intros Hin.
    destruct (ex2_windows_sound E0 ssf_H sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw];
    [exact (Hx1 Hw) | exact (Hx2 Hw)].
  - apply (vf_band_present W E0 hH_st1 ms1 sp0 HS1 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
clear VX0 HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs E0 hH_st1 _ BC_EQ (SLit 0) (SExt true 32 (SOff 32 0)) HS1
  ltac:(apply (beq0_sext32_false E0 32 (bv_unsigned (ew E' 8)) A32_0); lia)) as HS1c.
change (YP06.add_cond hH_st1 (mkAC (neg_bc BC_EQ) (SLit 0) (SExt true 32 (SOff 32 0)))) with hH_st1c in HS1c.
clear HS1.
eapply SRr_bind; [exact (ex_phase W E0 hH_st1c hH_st2 _ _ _ HS1c hH_run2)|]. cbv beta.
intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). clear HS1c.
assert (VX2 : VX B ly S W sp0 mem md exm2 XS (ms_mem ms2) (with_vm_backing (m_vm_lazy md) mat2 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm2 exm2_img exm2_dec HFownM XS Hstk Htop _ _ (ms_mem ms2) mat2 VX1) as VR.
  rewrite ?wvb_wvb in VR. apply VR.
  - intros x Hx1 Hx2. apply HF2. intros Hin.
    destruct (ex2_windows_sound E0 hH_st1c sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw];
    [exact (Hx1 Hw) | exact (Hx2 Hw)].
  - intros x Hx1 Hx2. apply HFr2. intros Hin.
    destruct (ex2_windows_sound E0 hH_st1c sp0 _ ltac:(vm_compute; reflexivity) Usp0 Hin) as [Hw|Hw];
    [exact (Hx1 Hw) | exact (Hx2 Hw)].
  - apply (vf_band_present W E0 hH_st2 ms2 sp0 HS2 ltac:(vm_compute; reflexivity) Usp0 ltac:(lia)). }
clear VX1 HF2 HFr2.
eapply SRr_bind; [exact
(vf_icpt_xcall B LAWS HB X1_PC XW1 XTRUE X1 W E0 hH_st2 ms2 _ ly S sp0 hH_r02 hH_rest2 37 X1_RA OSP_X1
HS2 eq_refl eq_refl Usp0 G3_0 G4_0 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_X1; lia) ltac:(unfold OSP_X1; lia) ltac:(unfold X1_RA; lia) ltac:(reflexivity)
(exf_hrest_ok E0 hH_rest2 (as_tp B) ltac:(vm_compute; reflexivity) U4_0
  ltac:(rewrite HTPX; unfold TFIB_TPX; lia) ltac:(rewrite HTPX; unfold TFIB_TPX; lia))
ltac:(intros r a Hr Ha; destruct (exf_hrest_range E0 hH_rest2 (as_tp B) ltac:(vm_compute; reflexivity) U4_0 r a Hr Ha)
  as [[HcanR Hcr]|Hcr];
[ split; [left; exact HcanR | unfold XW1; unfold A_GOT_canary in Hcr; GEO]
| split; [right; apply HXown; exact Hcr | unfold XW1; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO] ])
ltac:(intros a Hx; unfold XW1 in Hx; unfold vf_band; GEO)
(exf_hrest_w E0 hH_rest2 ltac:(vm_compute; reflexivity))
(proj1 VX2) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX2))) ltac:(exact I))|]. cbv beta.
intros W2' c2' _ (-> & ms2' & mat2' & -> & HS2' & HAR2' & HP2' & Hfr2' & Hpm2').
change (vf_after_icpt 37 hH_st2 X1_RA OSP_X1 0 []) with hH_af2 in HS2'.
assert (VX2' : VX B ly S W sp0 mem md exm2 XS (ms_mem ms2') (with_vm_backing (m_vm_lazy md) mat2' md)).
{ eapply (VX_splice B ly S W sp0 mem md exm2 XS Hstk Htop (ms_mem ms2) _ (ms_mem ms2') _
  (fun a => (sp0 + OSP_X1 - ESTACK <= a < sp0 + OSP_X1) \/ aowned B ly S a \/ XW1 a)).
  - exact VX2.
  - exact HAR2'.
  - rewrite <- (wvb_collapse (m_vm_lazy md) mat2' mat2 md). apply with_vm_backing_same.
  - intros a [Ha|[Ha|Ha]];
    [left; unfold vf_band, OSP_X1 in *; lia | right; right; unfold XS; tauto | right; right; unfold XS; tauto].
  - intros a Hr Hna. apply Hfr2'; [exact Hr | intros H'; apply Hna; left; exact H'
    | intros H'; apply Hna; right; left; exact H' | intros H'; apply Hna; right; right; exact H'].
  - intros a Hr Hba. apply Hpm2'; [exact Hr|]. destruct Hba as [Hb|Hns];
    [intros Hx; unfold XW1 in Hx; unfold vf_band in Hb; GEO | intros Hx; apply Hns; right; right; exact Hx]. }
remember (havoc E0 37 (map (getr (ms_regs ms2')) CLOB)) as E1 eqn:HE1.
assert (OLD1 : forall j, (j < 37)%nat -> ew E1 j = ew E0 j)
  by (intros j Hj; rewrite HE1; apply ew_havoc_old; exact Hj).
assert (Usp1 : bv_unsigned (ew E1 2) = sp0) by (rewrite OLD1 by (cbv; lia); exact Usp0).
assert (G3_1 : ew E1 3 = w64 (as_gp B)) by (rewrite OLD1 by (cbv; lia); exact G3_0).
assert (G4_1 : ew E1 4 = w64 (as_tp B)) by (rewrite OLD1 by (cbv; lia); exact G4_0).
assert (U4_1 : bv_unsigned (ew E1 4) = as_tp B) by (rewrite OLD1 by (cbv; lia); exact U4_0).
assert (A36_1 : ew E1 36 = Z_to_bv 64 f)
  by (rewrite OLD1 by (cbv; lia); unfold E0, exf_env; exact (ew_Ereg_extra regs _ 4)).
assert (E10_1 : ew E1 10 = Z_to_bv 64 code) by (rewrite OLD1 by (cbv; lia); exact E10_0).
assert (E33_1 : ew E1 33 = Z_to_bv 64 (bv_unsigned (ew E' 41))) by (rewrite OLD1 by (cbv; lia); exact E33_0).
clear HE1 HS2 VX2.
eapply SRr_bind; [exact (ex_phase W E1 hH_af2 hH_st3 _ _ _ HS2' hH_run3)|]. cbv beta.
intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). clear HS2'.
assert (VX3 : VX B ly S W sp0 mem md exm2 XS (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat3 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm2 exm2_img exm2_dec HFownM XS Hstk Htop _ _ (ms_mem ms3) mat3 VX2') as VR.
  rewrite ?wvb_wvb in VR. apply VR.
  - intros x Hx1 Hx2. apply HF3. intros Hin.
    destruct (ex2_windows_sound E1 hH_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw];
    [exact (Hx1 Hw) | exact (Hx2 Hw)].
  - intros x Hx1 Hx2. apply HFr3. intros Hin.
    destruct (ex2_windows_sound E1 hH_af2 sp0 _ ltac:(vm_compute; reflexivity) Usp1 Hin) as [Hw|Hw];
    [exact (Hx1 Hw) | exact (Hx2 Hw)].
  - apply (vf_band_present W E1 hH_st3 ms3 sp0 HS3 ltac:(vm_compute; reflexivity) Usp1 ltac:(lia)). }
clear VX2' HF3 HFr3.
pose proof HS3 as HSc3. destruct HSc3 as (_ & _ & _ & _ & _ & _ & _ & Hmem3 & _).
cbn [restrict ms_mem] in Hmem3.
assert (X3P : X3PRE W (ms_mem ms3)).
{ split; (eapply (val_mem_of_lit E1 (mrestrict (w_H W) (ms_mem ms3)) (ss_mem hH_st3) _ _ _ Hmem3);
  vm_compute; reflexivity). }
clear Hmem3.
eapply SRr_bind; [exact
(vf_icpt_xcall B LAWS HB X3_PC XW3 X3PRE X3 W E1 hH_st3 ms3 _ ly S sp0 hH_r03 hH_rest3 53 X23_RA OSP_X23
HS3 eq_refl eq_refl Usp1 G3_1 G4_1 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_X23; lia) ltac:(unfold OSP_X23; lia) ltac:(unfold X23_RA; lia) ltac:(reflexivity)
(exf_hrest_ok E1 hH_rest3 (as_tp B) ltac:(vm_compute; reflexivity) U4_1
  ltac:(rewrite HTPX; unfold TFIB_TPX; lia) ltac:(rewrite HTPX; unfold TFIB_TPX; lia))
ltac:(intros r a Hr Ha; destruct (exf_hrest_range E1 hH_rest3 (as_tp B) ltac:(vm_compute; reflexivity) U4_1 r a Hr Ha)
  as [[HcanR Hcr]|Hcr];
[ split; [left; exact HcanR | unfold XW3; unfold A_GOT_canary in Hcr; GEO]
| split; [right; apply HXown; exact Hcr | unfold XW3; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO] ])
ltac:(intros a Hx; unfold XW3 in Hx; unfold vf_band; GEO)
(exf_hrest_w E1 hH_rest3 ltac:(vm_compute; reflexivity))
(proj1 VX3) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX3))) ltac:(exact X3P))|]. cbv beta.
intros W3' c3' _ (-> & ms3' & mat3' & -> & HS3' & HAR3' & HP3' & Hfr3' & Hpm3').
change (vf_after_icpt 53 hH_st3 X23_RA OSP_X23 0 []) with hH_af3 in HS3'.
assert (VX3' : VX B ly S W sp0 mem md exm2 XS (ms_mem ms3') (with_vm_backing (m_vm_lazy md) mat3' md)).
{ eapply (VX_splice B ly S W sp0 mem md exm2 XS Hstk Htop (ms_mem ms3) _ (ms_mem ms3') _
  (fun a => (sp0 + OSP_X23 - ESTACK <= a < sp0 + OSP_X23) \/ aowned B ly S a \/ XW3 a)).
  - exact VX3.
  - exact HAR3'.
  - rewrite <- (wvb_collapse (m_vm_lazy md) mat3' mat3 md). apply with_vm_backing_same.
  - intros a [Ha|[Ha|Ha]];
    [left; unfold vf_band, OSP_X23 in *; lia | right; right; unfold XS; tauto | right; right; unfold XS; tauto].
  - intros a Hr Hna. apply Hfr3'; [exact Hr | intros H'; apply Hna; left; exact H'
    | intros H'; apply Hna; right; left; exact H' | intros H'; apply Hna; right; right; exact H'].
  - intros a Hr Hba. apply Hpm3'; [exact Hr|]. destruct Hba as [Hb|Hns];
    [intros Hx; unfold XW3 in Hx; unfold vf_band in Hb; GEO | intros Hx; apply Hns; right; right; exact Hx]. }
remember (havoc E1 53 (map (getr (ms_regs ms3')) CLOB)) as E2 eqn:HE2.
assert (OLD2 : forall j, (j < 53)%nat -> ew E2 j = ew E1 j)
  by (intros j Hj; rewrite HE2; apply ew_havoc_old; exact Hj).
assert (Usp2 : bv_unsigned (ew E2 2) = sp0) by (rewrite OLD2 by (cbv; lia); exact Usp1).
assert (G3_2 : ew E2 3 = w64 (as_gp B)) by (rewrite OLD2 by (cbv; lia); exact G3_1).
assert (G4_2 : ew E2 4 = w64 (as_tp B)) by (rewrite OLD2 by (cbv; lia); exact G4_1).
assert (U4_2 : bv_unsigned (ew E2 4) = as_tp B) by (rewrite OLD2 by (cbv; lia); exact U4_1).
assert (A36_2 : ew E2 36 = Z_to_bv 64 f) by (rewrite OLD2 by (cbv; lia); exact A36_1).
assert (E10_2 : ew E2 10 = Z_to_bv 64 code) by (rewrite OLD2 by (cbv; lia); exact E10_1).
assert (E33_2 : ew E2 33 = Z_to_bv 64 (bv_unsigned (ew E' 41))) by (rewrite OLD2 by (cbv; lia); exact E33_1).
clear HE2 HS3 VX3.
eapply SRr_bind; [exact (ex_phase W E2 hH_af3 hH_st4 _ _ _ HS3' hH_run4)|]. cbv beta.
intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). clear HS3'.
assert (VX4 : VX B ly S W sp0 mem md exm2 XS (ms_mem ms4) (with_vm_backing (m_vm_lazy md) mat4 md)).
{ pose proof (VX_run B LAWS ly S W sp0 mem md exm2 exm2_img exm2_dec HFownM XS Hstk Htop _ _ (ms_mem ms4) mat4 VX3') as VR.
  rewrite ?wvb_wvb in VR. apply VR.
  - intros x Hx1 Hx2. apply HF4. intros Hin.
    destruct (ex2_windows_sound E2 hH_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw];
    [exact (Hx1 Hw) | exact (Hx2 Hw)].
  - intros x Hx1 Hx2. apply HFr4. intros Hin.
    destruct (ex2_windows_sound E2 hH_af3 sp0 _ ltac:(vm_compute; reflexivity) Usp2 Hin) as [Hw|Hw];
    [exact (Hx1 Hw) | exact (Hx2 Hw)].
  - apply (vf_band_present W E2 hH_st4 ms4 sp0 HS4 ltac:(vm_compute; reflexivity) Usp2 ltac:(lia)). }
clear VX3' HF4 HFr4.
(* at the module destructor: what AR still gives, read before the call that ends it *)
pose proof VX4 as (HAR4 & _ & _ & Hfr4 & Hpm4).
pose proof (AE31.icpt_cells_of_AR B HB ly S (w_H W) (ms_mem ms4) (proj1 HAR4)) as HC4.
pose proof (amf_block_facts tfibsegs B LAWS ly S W (ms_mem ms4) _ f HAR4 Hblk) as (_ & _ & _ & _ & _ & Fsh4 & Fhull4).
eapply SRr_bind; [exact
(vf_icpt_xcall_noar_vals B X2_PC XW2 (fun _ => 0) XTRUE X2 W E2 hH_st4 ms4 _ ly S sp0 hH_r04 hH_rest4 69 X23_RA OSP_X23
HS4 eq_refl eq_refl Usp2 G3_2 G4_2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
eq_refl eq_refl eq_refl eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity)
ltac:(reflexivity) ltac:(unfold OSP_X23; lia) ltac:(unfold OSP_X23; lia) ltac:(unfold X23_RA; lia) ltac:(reflexivity)
(exf_hrest_ok E2 hH_rest4 (as_tp B) ltac:(vm_compute; reflexivity) U4_2
  ltac:(rewrite HTPX; unfold TFIB_TPX; lia) ltac:(rewrite HTPX; unfold TFIB_TPX; lia))
ltac:(intros r a Hr Ha; destruct (exf_hrest_range E2 hH_rest4 (as_tp B) ltac:(vm_compute; reflexivity) U4_2 r a Hr Ha)
  as [[HcanR Hcr]|Hcr];
[ split; [left; exact HcanR | unfold XW2; unfold A_GOT_canary in Hcr; GEO]
| split; [right; apply HXown; exact Hcr | unfold XW2; unfold ex_cell_range, vo_file, vf_file in Hcr; GEO] ])
ltac:(intros a Hx; unfold XW2 in Hx; unfold vf_band; GEO)
(exf_hrest_w E2 hH_rest4 ltac:(vm_compute; reflexivity))
(proj1 VX4) Hsp44 Hal16 Hstk Htop (proj1 (proj2 (proj2 VX4))) ltac:(exact I))|]. cbv beta.
intros W4' c4' _ (-> & ms4' & mat4' & -> & HS4' & HP4' & Hfr4' & Hpm4' & Hval4').
change (vf_after_icpt 69 hH_st4 X23_RA OSP_X23 0 []) with hH_af4 in HS4'.
remember (havoc E2 69 (map (getr (ms_regs ms4')) CLOB)) as E3 eqn:HE3.
assert (OLD3 : forall j, (j < 69)%nat -> ew E3 j = ew E2 j)
  by (intros j Hj; rewrite HE3; apply ew_havoc_old; exact Hj).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0) by (rewrite OLD3 by (cbv; lia); exact Usp2).
assert (G3_3 : ew E3 3 = w64 (as_gp B)) by (rewrite OLD3 by (cbv; lia); exact G3_2).
assert (G4_3 : ew E3 4 = w64 (as_tp B)) by (rewrite OLD3 by (cbv; lia); exact G4_2).
assert (A36_3 : ew E3 36 = Z_to_bv 64 f) by (rewrite OLD3 by (cbv; lia); exact A36_2).
assert (E10_3 : ew E3 10 = Z_to_bv 64 code) by (rewrite OLD3 by (cbv; lia); exact E10_2).
assert (E33_3 : ew E3 33 = Z_to_bv 64 (bv_unsigned (ew E' 41))) by (rewrite OLD3 by (cbv; lia); exact E33_2).
clear HE3 HS4 VX4.
eapply SRr_bind; [exact (ex_phase W E3 hH_af4 hH_st5 _ _ _ HS4' hH_run5)|]. cbv beta.
intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). clear HS4'.
(* ---- the frames from the caller's memory to the state at 0x9688c ---- *)
assert (F5 : forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ exm2 a ->
  aview tfibsegs (w_H W) (ms_mem ms5) a = aview tfibsegs (w_H W) (ms_mem ms4') a).
{ intros a Hr H1 H2. apply AE2y.aview_eq_of. apply HFr5. rewrite unsigned_lit_small by lia. intros Hin.
  destruct (ex2_windows_sound E3 hH_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin) as [Hw|Hw];
  [exact (H1 Hw) | exact (H2 Hw)]. }
assert (F4 : forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ exm2 a -> ~ XW2 a ->
  aview tfibsegs (w_H W) (ms_mem ms5) a = aview tfibsegs (w_H W) (ms_mem ms4) a).
{ intros a Hr H1 H2 H3. rewrite (F5 a Hr H1 H2). apply Hfr4'; [exact Hr | | exact H3].
  intros Hb. apply H1. unfold vf_band, OSP_X23 in *. lia. }
assert (F0 : forall a, 0 <= a < 2 ^ 64 -> ~ vf_band sp0 a -> ~ exm2 a -> ~ aowned B ly S a -> ~ XW2 a -> ~ XW3 a ->
  aview tfibsegs (w_H W) (ms_mem ms5) a = aview tfibsegs (w_H W) mem a).
{ intros a Hr H1 H2 H3 H4 H5. rewrite (F4 a Hr H1 H2 H4). apply Hfr4; [exact Hr | exact H1 | exact H2 |].
  unfold XS, XW1. intros [Hx|[Hx|[Hx|Hx]]]; [exact (H3 Hx) | exact Hx | exact (H4 Hx) | exact (H5 Hx)]. }
assert (P5 : forall a, 0 <= a < 2 ^ 64 -> ~ exm2 a -> ~ aowned B ly S a -> ~ XW2 a -> ~ XW3 a ->
  apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms5) a).
{ intros a Hr H2 H3 H4 H5 Hp.
  assert (CASE : vf_band sp0 a \/ ~ vf_band sp0 a) by (unfold vf_band; lia).
  destruct CASE as [Hb|Hout].
  - exact (vf_band_present W E3 hH_st5 ms5 sp0 HS5 ltac:(vm_compute; reflexivity) Usp3 ltac:(lia) a Hb).
  - assert (Hp4 : apresent (w_H W) (ms_mem ms4) a).
    { apply (Hpm4 a Hr H2); [|exact Hp]. unfold XS, XW1. intros [Hx|[Hx|[Hx|Hx]]]; [exact (H3 Hx) | exact Hx | exact (H4 Hx) | exact (H5 Hx)]. }
    destruct (Hpm4' a Hr H4 Hp4) as [Hh [b Hbb]]. split; [exact Hh|]. exists b.
    rewrite HF5; [exact Hbb|]. rewrite unsigned_lit_small by lia. intros Hin.
    destruct (ex2_windows_sound E3 hH_af4 sp0 _ ltac:(vm_compute; reflexivity) Usp3 Hin) as [Hw|Hw];
    [exact (Hout Hw) | exact (H2 Hw)]. }
(* ---- the FILE's block ---- *)
assert (NIb : forall x, f <= x < f + AMF_BLOCK -> ~ (0x10000 <= x < 0x654000)).
{ intros x Hx H. apply (proj2 (proj2 (Fby x Hx))). apply AD1y.in_img_hull. unfold pcap_img_end, YImgTop.IMG_TOP. lia. }
assert (BSIDE : f + AMF_BLOCK <= 0x10000 \/ 0x654000 <= f).
{ pose proof (NIb f ltac:(unfold AMF_BLOCK; lia)) as N1.
  pose proof (NIb (f + AMF_BLOCK - 1) ltac:(unfold AMF_BLOCK; lia)) as N2. unfold AMF_BLOCK in *. lia. }
assert (Fvb : forall a, f <= a < f + AMF_BLOCK -> ~ vf_band sp0 a)
  by (intros a Ha Hb; unfold vf_band in Hb; unfold ASAN_CEIL, stack_max_size, VF_STK in *; lia).
assert (Hsp46 : 2 ^ 46 <= sp0) by lia.
(* ---- reading the state at 0x9688c ---- *)
pose proof HS5 as HSc5.
destruct HSc5 as (_ & Hpc5 & _ & _ & _ & _ & Hregs5 & Hmem5 & _).
cbn [restrict ms_pc_val ms_regs ms_mem] in Hpc5, Hregs5, Hmem5.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E3 _ _ HS5 eq_refl) as Hsh5.
rreg HS5 (2%bv : bv 5) R2_5. rreg HS5 (3%bv : bv 5) R3_5. rreg HS5 (4%bv : bv 5) R4_5.
assert (HR5 : Forall (YP09.region_ok tfibsegs E3 (mrestrict (w_H W) (ms_mem ms5))) (hH_r05 :: hH_rest5)).
{ rewrite <- hH_mem5. destruct Hmem5 as (_ & Hrs & _). exact Hrs. }
pose proof (Forall_inv HR5) as Hr05.
assert (B05 : YP09.r_base hH_r05 = Some 2%nat) by (vm_compute; reflexivity).
apply SRr_ret. split; [reflexivity|].
exists (ms_regs ms5), (ms_mem ms5), (with_vm_backing (m_vm_lazy md) mat5 md),
  (bv_unsigned (ew E' 8)), (bv_unsigned (ew E' 41)), 0.
split; [unfold cfg_at; rewrite Hsh5 at 1; rewrite hH_pc5; reflexivity|].
split.
{ pose proof (Hregs5 8%bv) as HR8.
  match type of HR8 with
  | sv_denot _ ?x = _ => let x' := eval vm_compute in x in change x with x' in HR8
  | _ = sv_denot _ ?x => let x' := eval vm_compute in x in change x with x' in HR8
  end.
  cbn [sv_denot] in HR8. rewrite A36_3, Z.add_0_r, Z_to_bv_bv_unsigned in HR8.
  first [exact HR8 | symmetry; exact HR8]. }
unfold exf_mid.
split; [unfold spZ; rewrite R2_5, Usp3, unsigned_lit_small by lia; lia|].
split; [exact U16|]. split; [exact Uw|].
split; [rewrite R3_5; exact G3_3|].
split; [rewrite R4_5; exact G4_3|].
split; [exact HTPX|].
split.
{ intros a Ha. apply P5; [lia | exact (proj1 (high_off a ltac:(lia))) | | exact (proj1 (proj2 (high_off a ltac:(lia))))
  | exact (proj2 (proj2 (high_off a ltac:(lia)))) | exact (Hpres a Ha)].
  apply (al_stack _ _ LAWS ly S W mem md a HAR). rewrite Hslo, Hshi. unfold ASAN_CEIL, kHighMemEnd, stack_max_size in *. lia. }
split.
{ replace (usp - 80) with (sp0 + -32) by lia. change 8%nat with (N.to_nat 8).
  apply (val_mem_of_rchunk E3 _ hH_r05 2%nat sp0 (-32) 8 (SOff 10 0) code Hr05 B05).
  - unfold hH_r05. cbn [YP09.r_chunks In]. repeat (first [left; reflexivity | right]).
  - exact Usp3.
  - cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E10_3.
  - replace (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) by reflexivity. destruct Hc02; lia.
  - cbn. lia. }
split; [exact Hc02|].
split.
{ replace (usp - 72) with (sp0 + -24) by lia. change 8%nat with (N.to_nat 8).
  apply (val_mem_of_rchunk E3 _ hH_r05 2%nat sp0 (-24) 8 (SLit 593396) 0x90df4 Hr05 B05).
  - unfold hH_r05. cbn [YP09.r_chunks In]. repeat (first [left; reflexivity | right]).
  - exact Usp3.
  - reflexivity.
  - replace (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) by reflexivity. lia.
  - cbn. lia. }
split.
{ replace (usp - 56) with (sp0 + -8) by lia. change 8%nat with (N.to_nat 8).
  apply (val_mem_of_rchunk E3 _ hH_r05 2%nat sp0 (-8) 8 (SLit 591500) 0x9068c Hr05 B05).
  - unfold hH_r05. cbn [YP09.r_chunks In]. repeat (first [left; reflexivity | right]).
  - exact Usp3.
  - reflexivity.
  - replace (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) by reflexivity. lia.
  - cbn. lia. }
(* the stderr FILE, kept from the caller *)
assert (STDE : forall a, 0xa5fa0 <= a < 0xa6088 ->
  aview tfibsegs (w_H W) (ms_mem ms5) a = aview tfibsegs (w_H W) mem a).
{ intros a Ha. destruct (img_iv_off sp0 0xa5fa0 0xa6088 a Hsp44 eq_refl Ha) as (Z1 & Z2 & Z3 & Z4 & Z5).
  apply F0; try assumption. apply HXown. exact (xr_vf _ a Ha). }
split.
{ apply (exf_cells_at5 E3 _ Hmem5).
  - apply (val_mem_kept (w_H W) (w_H W) mem (ms_mem ms5)); [intros j Hj; cbn in Hj; apply STDE; lia|].
    exact (exf_cell _ 0xa5fa8 8%N 0 HC ltac:(vm_compute; reflexivity)).
  - apply (val_mem_kept (w_H W) (w_H W) mem (ms_mem ms5)); [intros j Hj; cbn in Hj; apply STDE; lia|].
    exact (exf_cell _ 0xa5fb0 8%N 0 HC ltac:(vm_compute; reflexivity)).
  - apply (val_mem_kept (w_H W) (w_H W) mem (ms_mem ms5)); [intros j Hj; cbn in Hj; apply STDE; lia|].
    exact (exf_cell _ 0xa602c 4%N 0xffffffff HC ltac:(vm_compute; reflexivity)). }
split.
{ apply (val_mem_kept (w_H W) (w_H W) mem (ms_mem ms5)); [|rewrite HTPX; exact Htidc].
  intros j Hj. cbn in Hj. rewrite HTPX. unfold TFIB_TPX.
  destruct (img_iv_off sp0 0x631b68 0x631b6c (0x631c10 - 168 + j) Hsp44 eq_refl ltac:(lia)) as (Z1 & Z2 & Z3 & Z4 & Z5).
  apply F0; try assumption. apply HXown. apply xr_tid. rewrite HTPX. unfold TFIB_TPX. lia. }
split; [lia|].
split; [exact (xconst_sound E3 _ (ss_mem hH_st5) A_GOT_canary 8 A_canary Hmem5 ltac:(vm_compute; reflexivity))|].
split.
{ exact (xatom_sound E3 _ (ss_mem hH_st5) A_canary 8 33 (bv_unsigned (ew E' 41)) Hmem5
    ltac:(vm_compute; reflexivity) ltac:(rewrite E33_3, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact (u64_range (ew E' 41)))). }
split; [exact (u64_range (ew E' 41))|].
split.
{ apply (val_mem_kept (w_H W) (w_H W) mem (ms_mem ms5)); [|exact Hew1].
  intros j Hj. cbn in Hj. apply STDE. unfold F_STDERR. lia. }
split.
{ apply (val_mem_kept (w_H W) (w_H W) mem (ms_mem ms5)); [|exact Hew2].
  intros j Hj. cbn in Hj. apply STDE. unfold F_STDERR. lia. }
split; [lia|].
(* stdout, kept from the caller *)
assert (STDO : forall a, (0xa6090 <= a < 0xa6178) \/ (0x652318 <= a < 0x652728) ->
  aview tfibsegs (w_H W) (ms_mem ms5) a = aview tfibsegs (w_H W) mem a).
{ intros a [Ha|Ha].
  - destruct (img_iv_off sp0 0xa6090 0xa6178 a Hsp44 eq_refl Ha) as (Z1 & Z2 & Z3 & Z4 & Z5).
    apply F0; try assumption. apply HXown. exact (xr_vo _ a Ha).
  - destruct (img_iv_off sp0 0x652318 0x652728 a Hsp44 eq_refl Ha) as (Z1 & Z2 & Z3 & Z4 & Z5).
    apply F0; try assumption.
    exact (img_rng_not_owned ly S W mem md 0x652318 0x652728 a HAR ltac:(vm_compute; reflexivity) Ha
      ltac:(lia) ltac:(lia)). }
split.
{ destruct HSO as [[Hk0 HSI] | [Hk1 HX]].
  - left. split; [exact Hk0|]. intros a Ha. rewrite STDO by (left; unfold STDOUT_LO, STDOUT_HI in Ha; lia).
    exact (HSI a Ha).
  - right. split; [exact Hk1|]. apply (XFR k (w_H W) (w_H W) mem (ms_mem ms5) HX).
    intros a Ha. apply STDO. unfold STDOUT_MUT, STDOUT_LO, STDOUT_HI, SOBUF_LO, SOBUF_HI in Ha. lia. }
split; [intros j; rewrite (proj1 (sbm_fds_fs md _ (with_vm_backing_same md mat5))); exact (Hfds j)|].
split; [rewrite (proj2 (sbm_fds_fs md _ (with_vm_backing_same md mat5))); exact Hfs|].
(* the open-file head and the FILE, kept from the caller *)
split.
{ assert (FIMG : forall a, finv_img a \/ in_kept [(f, AMF_BLOCK)] a ->
    aview tfibsegs (w_H W) (ms_mem ms5) a = aview tfibsegs (w_H W) mem a).
  { intros a [Ha|Ha].
    - destruct (finv_img_ivs a Ha) as (l & h & Hin & Hlh).
      pose proof (proj1 (forallb_forall _ _) FINV_IVS_iv (l, h) Hin) as Hok. cbn [fst snd] in Hok.
      destruct (img_iv_off sp0 l h a Hsp44 Hok Hlh) as (Z1 & Z2 & Z3 & Z4 & Z5).
      apply F0; try assumption.
      apply (tfib_low_not_owned B ly S W mem md a HAR).
      + pose proof (finv_img_range a Ha) as Rg. unfold AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END. lia.
      + exact (finv_img_not_owned B HB a Ha).
    - destruct Ha as (f' & Hin' & Hfa). destruct Hin' as [Hq|[]]. injection Hq as Hq'. subst f'.
      destruct (block_off f a Fapp Hfa (proj2 (proj2 (Fby a Hfa)))) as (Z3 & Z4 & Z5).
      apply F0; [unfold AMF_BLOCK in *; lia | exact (Fvb a Hfa) | exact Z3 | exact (proj1 (proj2 (Fby a Hfa)))
        | exact Z4 | exact Z5]. }
  exact (proj1 (finv_aview (w_H W) (w_H W) mem (ms_mem ms5) FIMG HFI)). }
split; [exact F4k|]. split; [exact F16|]. split; [exact Fh47|].
(* exf_noar: the facts mwrite's flush needs, read at the destructor and carried *)
split.
{ apply (icpt_cells_kept (w_H W) (w_H W) (ms_mem ms4) (ms_mem ms5)); [|exact HC4].
  intros a Ha H1 H2. destruct (icpt_off sp0 a Hsp44 Ha H1 H2) as (Z1 & Z2 & Z3 & Z4).
  exact (F4 a Z1 Z2 Z3 Z4). }
split.
{ intros x Hx. exists 0. split; [|left; reflexivity].
  destruct (gsaid_shadow sp0 x Hsp44 Hx) as (Z0 & Z1 & Z2 & Z3).
  rewrite (F5 _ Z1 Z2 Z3). exact (Hval4' _ Z0). }
split.
{ intros s Hs. destruct (gsaid_hull sp0 s Hsp44 Hs) as (Z0 & Z1 & Z2 & Z3).
  rewrite (F5 _ Z1 Z2 Z3), (Hval4' _ Z0). discriminate. }
split.
{ intros a Ha. destruct (block_off f a Fapp Ha (proj2 (proj2 (Fby a Ha)))) as (Z3 & Z4 & Z5).
  split; [|exact (proj2 (proj2 (Fby a Ha)))].
  apply P5; [unfold AMF_BLOCK in *; lia | exact Z3 | exact (proj1 (proj2 (Fby a Ha))) | exact Z4 | exact Z5
    | exact (proj1 (Fby a Ha))]. }
split; [exact (amem_of_app f Fapp)|].
split; [exact Fbelow|].
split.
{ apply (range_addressable_agree (aview tfibsegs (w_H W) (ms_mem ms4)));
    [|exact (block_shadow_range _ _ f AMF_BLOCK f AMF_BLOCK Fsh4 (Z.le_refl _) (Z.le_refl _))].
  intros x Hx. destruct (bshadow_off sp0 x Hsp46 ltac:(unfold AMF_BLOCK in *; lia) (NIb x Hx)) as (Z1 & Z2 & Z3 & Z4).
  exact (F4 _ Z1 Z2 Z3 Z4). }
{ apply (hull_kept (aview tfibsegs (w_H W) (ms_mem ms4))); [|exact Fhull4].
  intros s Hs. destruct (bhull_off sp0 f s Hsp46 ltac:(lia) Fh47 BSIDE Hs) as (Z1 & Z2 & Z3 & Z4).
  exact (F4 _ Z1 Z2 Z3 Z4). }
Qed.

End t.

(* at B = PcapB and the driver's stdout state AD1k.xst, as lib/A/AD2o.v takes it *)
Theorem exf_head_link : exf_head_tfa PcapB AD1k.xst.
Proof. exact (exf_head_ok PcapB PcapB_syms AD1k.xst tfib_xst_frame). Qed.

End q.

Print Assumptions exf_head_link.
