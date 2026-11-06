(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/PjStringCommon.v, with its module paths and module names changed; 334 of its 385 lines of code are new or changed and 285 lines of the source are left out. *)
(* fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30, unstripped twin c90d4fa54d43160b): padded's
   segment S4 (row PDB-S4 of the internal file FREE-PIECES-102.md), B' 0x830f0 -> 0x83118: the UBSan
   check of b + size and the call __asan_memset (b + size, fill, 16), from the cut PD_SET to the cut PD_EPI, where S6
   (pd_s6_stmt, row PDB-S6) takes over: pd_s4_of_s6 : pd_seat_stmt -> pd_s6_stmt -> pd_s4_stmt.
   rule 24: proves function padded (reuse search: the internal file REWALK-102-PLAN.md section D3: none exists) - this file proves one
   segment lemma of it (kind: segment lemma).
   INPUTS: the frozen interface lib/B/Prog/Padded102B.v (Padded102B.v (sha256 f44e9f62a63a; internal record); its
   Section d's Context lines, local notations and the runtime row AI_set (:174) are copied below); the listing
   lib/B/Listing_prog.v 8bcc2c9e7809 :1688-1694 (slots 1673-1679 of the whole-program listing = B' 0x830f0-0x83108:
   `not a0, s0`; `bltu a0, s2, 0x83138`; `add a0, s0, s2`; `li a2, 16`; `mv a1, s1`; PCall AS___asan_memset;
   `j 0x83118`); its PAListing instance PL_prog_B (lib/B/PAImg_prog.v 4392ab2c09ba :179; the image instance PI_prog_B
   is NOT used: the file stays over Section d's PA, as Padded102B.v does).
   THE WALK: the shared seat pd_seat_stmt at PD_SET; the runner to the bltu; its taken arm (the trap at PD_TRAP)
   refuted by pd4_ovf_false (Padded102B.v :142 pd_ovf_false with size <= 2 ^ 47 for size < 2 ^ 32: the cut bounds size
   by alloc_ceiling); the runner to the call; YGcallMxmn.v (2ca1815f60a8) :310 aj_intrin_at_xm OSet for __asan_memset (b + size,
   fill, 16) with the row AI_set; pd_base rebuilt at the return (pd4_base_kept: the memset writes
   [b + size, b + size + 16) and the callee's ESTACK window only); the shared seat at PD_RETS; the runner to PD_EPI;
   there pd_at_epi is rebuilt and the S6 premise applied.
   Numerals: 16 (LENGTH: FUZZ_PAD, fuzz.h; = the memset length; = cf_head at CfParams_preset, read by `change`);
   48 (LENGTH: the frame); 8 (LENGTH: word, granule); 256 (WORD: byte modulus); 2 ^ 44 / 2 ^ 46 / 2 ^ 47 (DERIVED:
   shadow and stack bounds); 4096 (DERIVED: ESTACK); 16432 (DERIVED: STK_padded at prh_img_B, by vm_compute).
   No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcallx YGcallcf YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG01cf YG00cf YG0ncf YG0dcf YG0sshcf YGcfRoomPre YG0lawscf YGcfApath.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Padded102B.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.
(* the image instance of PAImg_prog.v is never inferred here: every PA below is Section d's *)
#[local] Remove Hints PAImg_prog.PI_prog_B : typeclass_instances.

(* ---- pure arithmetic: no state ---- *)
Lemma pd4_req : forall z, 0 < z -> req_size z = z.
Proof. intros z Hz. unfold req_size. destruct (Z.eqb_spec z 0); lia. Qed.
(* the shadow of an address below 2 ^ 47, and the hull of a range below 2 ^ 47, lie in [kLowShadowBeg, kHighMemBeg),
   which no application range (in_app) meets *)
Lemma pd4_shadow_zone : forall x, 0 <= x < 2 ^ 47 -> kLowShadowBeg <= shadow_of_addr SHADOW_OFF x < kHighMemBeg.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma pd4_hull_zone : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> kLowShadowBeg <= s < kHighMemBeg.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr in Hs. unfold kLowShadowBeg, kHighMemBeg.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
assert (P3 : (x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as M2.
unfold SHADOW_OFF in *. lia.
Qed.
Section ar. Context {rc : YM05.RunCeil}.
Lemma pd4_app_zone : forall p len a, in_app p len -> p <= a < p + len -> a < kLowShadowBeg \/ kHighMemBeg <= a.
Proof. intros p len a Happ Ha. unfold in_app in Happ. lia. Qed.
End ar.
Lemma pd4_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
(* Padded102B.v pd_ovf_false with the size bound the cut gives (size <= 2 ^ 47 from b + size + 24 <= alloc_ceiling,
   where pd_ovf_false asks size < 2 ^ 32), the same proof *)
Lemma pd4_ovf_false : forall E (pa pn : nat) d n, ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n ->
  0 <= d <= 2 ^ 47 -> 0 <= n <= 2 ^ 47 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff pa 0) (SLit (-1)))) (sv_denot E (SOff pn 0)) = false.
Proof.
intros E pa pn d n Hd Hn Rd Rn. rewrite branch_ltu_U, pd_U_not, (U_atom E pa d Hd), (U_atom E pn n Hn) by lia.
apply Z.ltb_ge. lia.
Qed.
(* a0 = s0 + s2 at the call *)
Lemma pd4_sv_add : forall E (p q : nat) x y, ew E p = Z_to_bv 64 x -> ew E q = Z_to_bv 64 y ->
  0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff p 0) (SOff q 0)) = Z_to_bv 64 (x + y).
Proof.
intros E p q x y Hx Hy Rx Ry Rxy. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff p 0) (SOff q 0)))) with (U E (SAlu ALU_ADD (SOff p 0) (SOff q 0))).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E p x Hx), (U_atom E q y Hy) by lia.
rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
(* two readers that agree on 8 bytes read the same word there *)
Lemma pd4_rdword_ext : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
unfold rdword. rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma pd4_aregs_trans : forall r0 r1 r2, aregs_preserved r0 r1 -> aregs_preserved r1 r2 -> aregs_preserved r0 r2.
Proof. intros r0 r1 r2 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Existing Instance prh_img_B.
#[local] Notation CP := CfParams_preset.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation PL := PAImg_prog.PL_prog_B.
Variable B : asyms.
#[local] Notation ARc := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARc).
(* Padded102B.v :174, the runtime row this segment crosses, the Section hypothesis verbatim *)
Hypothesis AI_set : aintrin_realizes_xm SEGS B ARc OSet (SIGMA AS___asan_memset).

(* ---- views ---- *)
Lemma pd4_aview_ext : forall (H : word -> bool) (m m' : word -> option byte) a, (forall x, m' x = m x) ->
  aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.
Lemma pd4_apresent_ext : forall (H : word -> bool) (m m' : word -> option byte) a, (forall x, m' x = m x) ->
  apresent H m a -> apresent H m' a.
Proof. intros H m m' a E [H1 [c Hc]]. split; [exact H1|]. exists c. rewrite E. exact Hc. Qed.
(* YE7f.v :55 apresent_of_writable, at SEGS *)
Lemma pd4_apresent_of_writable : forall (H : word -> bool) (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> writable_at SEGS (mrestrict H m) a -> apresent H m a.
Proof.
intros H m a Ha Hn Hw. unfold apresent. unfold writable_at, wview, mrestrict in Hw.
rewrite unsigned_lit_small in Hw by lia. rewrite (find_segment_none SEGS a Hn) in Hw.
destruct (H (Z_to_bv 64 a)) eqn:E; try rewrite E in Hw; [exfalso; apply Hw; reflexivity|].
split; [reflexivity|]. destruct (m (Z_to_bv 64 a)) as [c|] eqn:Ec; [exists c; reflexivity|].
try rewrite Ec in Hw. exfalso. apply Hw. reflexivity.
Qed.
Lemma pd4_val_mem_kept : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
  (forall k, (k < n)%nat -> aview SEGS H' m' (a + Z.of_nat k) = aview SEGS H m (a + Z.of_nat k)) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v HA Hv k Hk. rewrite (prh_mbyte_of_aview H H' m m' _ (HA k Hk)). exact (Hv k Hk).
Qed.
Lemma pd4_val1_of_aview : forall (H : word -> bool) (m : word -> option byte) a v, 0 <= v < 256 ->
  aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv HA k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in HA. destruct (mbyte SEGS (mrestrict H m) a) as [c|] eqn:Ec; cbn [option_map] in HA; [|discriminate HA].
injection HA as Hc. f_equal. apply bv_eq. rewrite Hc.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !(Z.mod_small v 256) by lia.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia.
reflexivity.
Qed.
Lemma pd4_garr8_kept : forall (W : world SEGS) (m m' : word -> option byte) p l,
  (forall j, (j < length l)%nat -> aview SEGS (w_H W) m' (p + Z.of_nat j) = aview SEGS (w_H W) m (p + Z.of_nat j)) ->
  garr8 SEGS (mrestrict (w_H W) m) p l -> garr8 SEGS (mrestrict (w_H W) m') p l.
Proof.
intros W m m' p l HA H j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
apply (pd4_val_mem_kept (w_H W) (w_H W) m m' _ 1 _); [|exact Hv]. intros kk Hkk. assert (kk = 0%nat) by lia. subst kk.
cbn [Z.of_nat]. rewrite Z.add_0_r. exact (HA j Hj).
Qed.
Lemma pd4_ro_img : forall a, in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.
(* the frame region's write window is empty, so the runner's frame_of / awr_ok over it are trivial *)
Lemma pd4_frame_eq : forall E (m m' : word -> option byte), frame_of E [pd_frame] m m' -> forall x, m' x = m x.
Proof. intros E m m' HF x. apply HF. intros (r & Hr & Hw). destruct Hr as [<-|[]]. cbn in Hw. lia. Qed.

Ltac pd4_awr := let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
  intros a (r & Hr & Hw); cbn in Hr; destruct Hr as [<-|[]]; cbn in Hw; lia.

(* ---- the registers the cut carries survive any callee-saving change (x3 / x4 and x20..x27 are callee-saved) ---- *)
Lemma pd4_regsat_keep : forall D regs regs' b, pd_regsat D regs b -> aregs_preserved regs regs' ->
  pd_regsat D regs' b.
Proof.
intros D regs regs' b (R2 & R8 & R9 & R18 & R19 & R3 & R4 & R20) HP.
assert (K : forall r, acallee_saved r -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) by exact HP.
split; [rewrite <- R2; exact (K 2 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R8; exact (K 8 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R9; exact (K 9 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R18; exact (K 18 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R19; exact (K 19 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R3; exact (K 3 ltac:(unfold acallee_saved; lia))|].
split; [rewrite <- R4; exact (K 4 ltac:(unfold acallee_saved; lia))|].
intros r Hr. rewrite <- (R20 r Hr). apply K. unfold acallee_saved. lia.
Qed.

(* the allocator's laws at ARcf (AR_laws_ok_cf, YG0lawscf.v), at YGcallcf's bridge *)
Let LAWS_cf : AR_laws_cf (cp := CP) SEGS B := AR_laws_ok_cf (cp := CP) SEGS B.
Let LAWS : AR_laws_x SEGS B ARc (@cf_head CP) := AR_laws_x_xs (cp := CP) SEGS B LAWS_cf.

(* ---- pd_base survives a change of registers that keeps the callee-saved ones and a change of memory confined to a
   set C of bytes off the image, the data window, the shadow zone, the harness heads and the 48-byte frame ---- *)
Lemma pd4_base_kept : forall (PIMG : pd_img B) D ly S Hp W regs mem md k b ow regs' mem' md' (C : Z -> Prop),
  pd_base B D ly S Hp W regs mem md k b ow ->
  pd_J B D ly S Hp W mem' md' k -> pd_mn D mem' -> aregs_preserved regs regs' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ C a -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, in_img SEGS a -> ~ C a) ->
  (forall a, din_data D <= a < din_data D + pd_size D -> ~ C a) ->
  (forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ C a) ->
  (forall a kk i, In (a, kk) (din_Lam D) -> 0 <= i < 8 -> ~ C (a - 16 + i)) ->
  (forall a, pd_sp0 D - 48 <= a < pd_sp0 D -> ~ C a) ->
  pd_base B D ly S Hp W regs' mem' md' k b ow.
Proof.
intros PIMG D ly S Hp W regs mem md k b ow regs' mem' md' C HB HJ' Hmn' HPR HK Cimg Cdat Csh Chd Cfr.
destruct HB as (Hret & HJ & Hsaved & Hregs & Hgp & Htp & Hrod & Hmn & EHp & HLED & Hlive & Hsrc & Hhome & Hszb & Hhull).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hcl & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
assert (FSTK : @STK_padded prh_img_B = 16432) by (vm_compute; reflexivity). rewrite FSTK in Hslo.
assert (HKI : forall a, in_img SEGS a -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a).
{ intros a Ha. pose proof (Hsegs a Ha). apply HK; [unfold kLowMemEnd in *; lia | exact (Cimg a Ha)]. }
split; [exact Hret|]. split; [exact HJ'|].
split.
{ unfold pd_saved in *. rewrite Forall_forall in Hsaved |- *. intros [o r] Hin. rewrite <- (Hsaved _ Hin).
  cbn [fst snd]. apply pd4_rdword_ext. intros i Hi.
  assert (Ho : 8 <= o <= 40) by (cbn in Hin; destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E; intros; subst; lia).
  apply HK; [lia|]. apply Cfr. lia. }
split; [exact (pd4_regsat_keep D regs regs' b Hregs HPR)|].
split; [exact Hgp|]. split; [exact Htp|].
split.
{ intros a Hro Hn He. rewrite (HKI a (pd4_ro_img a Hro)). exact (Hrod a Hro Hn He). }
split; [exact Hmn'|]. split; [exact EHp|].
split.
{ apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W mem' (din_Lam D) _ _ _ _ _ _ HLED).
  - intros a Ha. apply HKI. exact (pdi_pst_ok _ PIMG a Ha).
  - intros a kk i Hin Hi. destruct (prh_ledger_hblock B ly S Hp W mem _ _ _ _ _ a kk _ _ HLED Hin) as (Hk0 & Hab & _).
    change (@cf_head CP) with 16 in *.
    destruct (alx_blocks SEGS B ARc LAWS ly S Hp W mem md (a - 16) (kk + 16) HAR Hab) as (_ & H4096 & Hc & _).
    rewrite pd4_req in Hc by lia. apply HK; [lia|]. exact (Chd a kk i Hin Hi).
  - intros a kk _ H. exact H.
  - apply Permutation_refl. }
split; [exact Hlive|].
split.
{ destruct Hsrc as (Hby & H4096 & Hsc & Hamr & HRAs & HHUs). set (n := Z.of_nat (length (din_x D))) in *.
  assert (En : n = pd_size D) by reflexivity.
  split; [|split; [exact H4096|split; [exact Hsc|split; [exact Hamr|split]]]].
  - unfold bytes_at in *. apply (pd4_garr8_kept W mem mem' _ _); [|exact Hby]. intros j Hj.
    apply HK; [lia|]. apply Cdat. lia.
  - eapply range_addressable_agree; [|exact HRAs]. intros x Hx.
    pose proof (pd4_shadow_zone x ltac:(lia)) as Z1.
    apply HK; [unfold kLowShadowBeg, kHighMemBeg in Z1; lia | exact (Csh _ Z1)].
  - intros Hn0 s Hs. pose proof (pd4_hull_zone (din_data D) n s ltac:(lia) Hn0 ltac:(lia) Hs) as Z1.
    rewrite HK; [exact (HHUs Hn0 s Hs) | unfold kLowShadowBeg, kHighMemBeg in Z1; lia | exact (Csh s Z1)]. }
split; [exact Hhome|]. split; [exact Hszb | exact Hhull].
Qed.


(* ======== THE SEGMENT ======== *)
Lemma pd_s4_of_s6 : pd_seat_stmt B -> pd_s6_stmt B -> pd_s4_stmt B.
Proof.
intros SEAT S6 PIMG D ly S Hp W regs mem md k b HSET.
pose proof HSET as (HB & Hok & HnHp & (Hapr & HAPART) & Hbx).
pose proof HB as (Hret & HJ & Hsaved & Hregs & Hgp & Htp & Hrod & Hmn & EHp & HLED & Hlive & Hsrc & Hhome & Hszb & Hhull).
unfold pd_J in HJ.
pose proof Hregs as (R2 & R8 & R9 & R18 & R19 & R3 & R4 & R2027).
pose proof Hok as (Hb0 & _ & H4096 & Hceil & Hnot & Hperm & HLamne & Hwr & HRA & HHU & Hrp).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hcl & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
assert (FSTK : @STK_padded prh_img_B = 16432) by (vm_compute; reflexivity). rewrite FSTK in Hslo.
assert (Hes : ESTACK = 4096) by reflexivity.
set (sz := pd_size D) in *. set (sp0 := pd_sp0 D) in *.
assert (Esz : sz = Z.of_nat (length (din_x D))) by reflexivity.
assert (Hsz : 0 <= sz) by lia.
(* the new block (b, size + 16) *)
assert (Hin_blk : In (b, sz + 16) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (alx_blocks SEGS B ARc LAWS ly S Hp W mem md b (sz + 16) HAR Hin_blk) as (_ & _ & Hbc & Happ & _).
rewrite (pd4_req (sz + 16)) in Hbc, Happ by lia.
assert (Hnew : ~ In (b, sz + 16) (ablocks B (din_ly D) (din_S D))) by (intros X; apply Hnot; exact (in_map fst _ _ X)).
assert (Hnoimg : forall a, b <= a < b + sz + 16 -> ~ in_img SEGS a).
{ intros a Ha. apply (blk_img_x SEGS B ARc LAWS ly S Hp W mem md b (sz + 16) a HAR Hin_blk). rewrite pd4_req by lia. lia. }
(* THE CHANGED SET of the call: the memset's 16 bytes and the callee's ESTACK window below the body sp *)
pose (C := fun a => (b + sz <= a < b + sz + 16) \/ (sp0 + -48 - ESTACK <= a < sp0 + -48)).
assert (CIMG : forall a, in_img SEGS a -> ~ C a).
{ intros a Ha [Hc|Hc]; [exact (Hnoimg a ltac:(lia) Ha) | pose proof (Hsegs a Ha); unfold kLowMemEnd in *; lia]. }
assert (CDAT : forall a, din_data D <= a < din_data D + pd_size D -> ~ C a).
{ intros a Ha [Hc|Hc]; destruct (HAPART a Ha) as [Ha1 Ha2]; [apply Ha2; lia | lia]. }
assert (CSH : forall a, kLowShadowBeg <= a < kHighMemBeg -> ~ C a).
{ intros a Ha [Hc|Hc]; [destruct (pd4_app_zone b (sz + 16) a Happ ltac:(lia)); lia | unfold kHighMemBeg in Ha; lia]. }
assert (CHD : forall a kk i, In (a, kk) (din_Lam D) -> 0 <= i < 8 -> ~ C (a - 16 + i)).
{ intros a kk i Hin Hi. destruct (prh_ledger_hblock B ly S Hp W mem _ _ _ _ _ a kk _ _ HLED Hin) as (Hk0 & Hab & _).
  change (@cf_head CP) with 16 in Hab.
  destruct (alx_blocks SEGS B ARc LAWS ly S Hp W mem md (a - 16) (kk + 16) HAR Hab) as (_ & _ & Hc' & _).
  rewrite pd4_req in Hc' by lia.
  assert (Hne : (a - 16, kk + 16) <> (b, sz + 16)).
  { intros X. injection X as X1 _. apply (HLamne a kk Hin). change (@cf_head CP) with 16. lia. }
  pose proof (sep_blocks_x SEGS B ARc LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hin_blk Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite !pd4_req in Hd by lia.
  intros [Hc|Hc]; lia. }
assert (CFR : forall a, pd_sp0 D - 48 <= a < pd_sp0 D -> ~ C a).
{ intros a Ha [Hc|Hc]; lia. }
(* ---- the seat at PD_SET ---- *)
destruct (SEAT PIMG D PD_SET ly S Hp W regs mem md k b (din_own D) HB ltac:(lia)) as (HS & SHOK & HEI & HAE).
lazymatch type of HS with st_ok_pi _ _ ?E0 _ _ => remember E0 as E eqn:HE end. clear HE.
assert (EW : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < 32)%nat -> ew E n = getr regs r)
  by (intros n r Hr Hn; rewrite (proj1 HAE n Hn); apply ew_Ereg_nat; exact Hr).
pose (P := fun m => YAkMemnorm.memnorm SEGS (din_mem D) -> YAkMemnorm.memnorm SEGS m).
pose (PLAW := srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) (din_mem D) (srr_inv_laws_memnorm_k SEGS)).
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing PL PA B PST ARc _ LAWS P PLAW).
pose (RUNTO := @paj_run_to_x_inv fx rc SK B_prog_listing PL PA B PST ARc _ LAWS P PLAW).
pose (BR := @paj_branch fx rc B_prog_listing PA).
assert (HPM : P mem) by exact Hmn.
(* ---- 0x830f0 `not a0, s0`, to the bltu ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PD_Bspan; [pd4_awr|].
pose proof (pd4_frame_eq _ _ _ HF) as K1. clear HF HFr HG. rename ms into ms1.
(* ---- 0x830f4 `bltu a0, s2, 0x83138`: the trap arm is refuted (b + size + 16 <= alloc_ceiling) ---- *)
psrr_branch_tok RUN BR HS SHOK PD_Bspan.
{ exfalso. rewrite (pd4_ovf_false E 8 18 b sz) in Hc; [discriminate Hc | | | |].
  - rewrite (EW 8%nat 8%bv eq_refl ltac:(lia)). exact R8.
  - rewrite (EW 18%nat 18%bv eq_refl ltac:(lia)). exact R18.
  - lia.
  - lia. }
(* ---- 0x830f8 .. 0x83104: a0 = b + size, a2 = 16, a1 = fill, the call ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PD_Bspan; [pd4_awr|].
pose proof (pd4_frame_eq _ _ _ HF) as K2. clear HF HFr HG. rename ms into ms2.
assert (KT : forall x, ms_mem ms2 x = mem x) by (intros x; rewrite K2; apply K1).
assert (Hpres12 : aregs_preserved regs (ms_regs ms2))
  by (eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS); [exact HAE | vm_compute; reflexivity]).
pmkst HS.
pose proof (st_ok_restrict_reg SEGS _ _ _ _ (10%bv : bv 5) HS) as Q10.
lazymatch type of Q10 with _ = sv_denot _ (sr_get (ss_regs ?ss) _) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) (10%bv : bv 5)) in change (sr_get (ss_regs ss) (10%bv : bv 5)) with e in Q10 end.
cbn [ms_regs restrict mkst] in Q10.
rewrite (pd4_sv_add E 8 18 b sz (eq_trans (EW 8%nat 8%bv eq_refl ltac:(lia)) R8) (eq_trans (EW 18%nat 18%bv eq_refl ltac:(lia)) R18) ltac:(lia) ltac:(lia) ltac:(lia)) in Q10.
prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
(* the call: YGcallMxmn.v :310 aj_intrin_at_xm OSet, d = b + size, x = fill, n = 16, the row AI_set *)
eapply SRr_bind.
{ eapply (aj_intrin_at_xm SEGS B PST ARc LAWS Hsegs OSet (SIGMA AS___asan_memset) AI_set W (ms_regs ms2) (ms_mem ms2)
    STK_padded sp0 [] (din_ly D) (din_S D) (din_Hp D) (din_W D) (din_mem D) (din_md D) [] ly S Hp _ k
    (b + sz) (din_fill D) 16 (-48) _ HJ).
  - exact Q10.
  - rewrite Q11, (EW 9%nat 9%bv eq_refl ltac:(lia)). exact R9.
  - exact Q12.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite Q2, (EW 2%nat 2%bv eq_refl ltac:(lia)), R2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - reflexivity.
  - lia.
  - rewrite FSTK, Hes. lia.
  - rewrite Q3, (EW 3%nat 3%bv eq_refl ltac:(lia)), R3. exact Hgp.
  - rewrite Q4, (EW 4%nat 4%bv eq_refl ltac:(lia)), R4. exact Htp.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - intros a Ha. split; [|rewrite Hes; lia].
    right; right; left. exists b, (sz + 16). split; [exact Hin_blk|]. split; [exact Hnew|]. rewrite pd4_req by lia. lia.
  - clear - Happ C1 Hsz. unfold amem_range, in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd in *. lia.
  - eapply range_addressable_agree; [|exact (range_addressable_sub _ _ b (sz + 16) (b + sz) 16 HRA ltac:(lia) ltac:(lia))].
    intros x Hx. apply pd4_aview_ext. exact KT.
  - intros _ s Hs. rewrite (pd4_aview_ext (w_H W) mem (ms_mem ms2) s KT).
    exact (pd4_hull_sub _ b (sz + 16) (b + sz) 16 HHU ltac:(lia) ltac:(lia) ltac:(lia) s Hs).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Hset & Hfr2 & Hpres2 & Hmn2).
cbv beta iota in Hset.
(* ---- what the call kept: every byte off C, the apresent bytes, the callee-saved registers, memnorm ---- *)
assert (K2C : forall a, 0 <= a < 2 ^ 64 -> ~ C a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha HnC. rewrite (Hfr2 a Ha); [| intros X; apply HnC; left; exact X | intros X; apply HnC; right; exact X].
  apply pd4_aview_ext. exact KT. }
assert (HPR2 : aregs_preserved regs regs2) by exact (pd4_aregs_trans _ _ _ Hpres12 HP2).
assert (HMN2 : pd_mn D mem2) by (intros H0; exact (Hmn2 (HPM H0))).
assert (HB2 : pd_base B D ly S Hp W regs2 mem2 md2 k b (din_own D))
  by exact (pd4_base_kept PIMG D ly S Hp W regs mem md k b (din_own D) regs2 mem2 md2 C HB HJ2 HMN2 HPR2 K2C CIMG CDAT CSH CHD CFR).
(* ---- the seat at PD_RETS (0x83108) ---- *)
destruct (SEAT PIMG D PD_RETS ly S Hp W regs2 mem2 md2 k b (din_own D) HB2 ltac:(lia)) as (HS3 & SHOK3 & HEI3 & HAE3).
lazymatch type of HS3 with st_ok_pi _ _ ?E0 _ _ => remember E0 as E3 eqn:HE3 end. clear HE3.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?pc _ _) _) _ =>
  replace pc with (Z_to_bv 64 (pd_pc PD_RETS)) by (unfold pd_pc, PD_OFF, PD_SLOT, PD_RETS; f_equal; cbn; lia) end.
(* ---- 0x83108 `j 0x83118`, to PD_EPI ---- *)
paj_run_to_tok_x_inv RUNTO HS3 HJ2 SHOK3 HMN2 PD_Bspan (pd_koff PD_EPI); [pd4_awr|].
pose proof (pd4_frame_eq _ _ _ HF) as K3. clear HF HFr HG. rename ms into ms4.
assert (Hpres3 : aregs_preserved regs2 (ms_regs ms4))
  by (eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs2 _ HS3); [exact HAE3 | vm_compute; reflexivity]).
pmkst HS3.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?pc _ _) _) _ =>
  replace pc with (Z_to_bv 64 (pd_pc PD_EPI)) by (unfold pd_pc, PD_OFF, PD_SLOT, PD_EPI; f_equal; cbn; lia) end.
(* ---- PD_EPI: pd_at_epi, then the S6 premise ---- *)
apply (S6 PIMG D ly S Hp W (ms_regs ms4) (ms_mem ms4) _ k b).
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ C a -> aview SEGS (w_H W) (ms_mem ms4) a = aview SEGS (w_H W) mem a).
{ intros a Ha HnC. rewrite (pd4_aview_ext (w_H W) mem2 (ms_mem ms4) a K3). exact (K2C a Ha HnC). }
assert (SET4 : forall i, 0 <= i < 16 -> aview SEGS (w_H W) (ms_mem ms4) (b + sz + i) = Some (din_fill D mod 256)).
{ intros i Hi. rewrite (pd4_aview_ext (w_H W) mem2 (ms_mem ms4) _ K3). exact (Hset i Hi). }
assert (APR4 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms4) a).
{ intros a Ha. apply (pd4_apresent_ext _ mem2 (ms_mem ms4) a K3). apply Hpres2.
  exact (pd4_apresent_ext _ mem (ms_mem ms2) a KT Ha). }
exists (din_own D). split.
{ apply (pd4_base_kept PIMG D ly S Hp W regs2 mem2 md2 k b (din_own D) (ms_regs ms4) (ms_mem ms4) _ (fun _ => False) HB2 HJ2 HMN2 Hpres3).
  - intros a _ _. exact (pd4_aview_ext (w_H W) mem2 (ms_mem ms4) a K3).
  - intros a _ H. exact H.
  - intros a _ H. exact H.
  - intros a _ H. exact H.
  - intros a kk i _ _ H. exact H.
  - intros a _ H. exact H. }
(* pd_at_epi's NULL-arm death (b = 0 -> pd_dead D) is vacuous on this arm: b <> 0 *)
split; [|intros Hbz; exfalso; exact (Hb0 Hbz)].
right. apply pd_okfull_of.
{ (* the block facts, at the final memory *)
  split; [exact Hb0|]. split; [reflexivity|]. split; [exact H4096|]. split; [exact Hceil|]. split; [exact Hnot|].
  split; [exact Hperm|]. split; [exact HLamne|].
  split.
  { intros a Ha. apply (apresent_writable SEGS). apply APR4.
    apply (pd4_apresent_of_writable _ _ a); [lia | exact (Hnoimg a Ha) | exact (Hwr a Ha)]. }
  split.
  { eapply range_addressable_agree; [|exact HRA]. intros x Hx.
    pose proof (pd4_shadow_zone x ltac:(lia)) as Z1.
    apply K4; [unfold kLowShadowBeg, kHighMemBeg in Z1; lia | exact (CSH _ Z1)]. }
  split.
  { intros s Hs. pose proof (pd4_hull_zone b (sz + 16) s ltac:(lia) ltac:(lia) ltac:(lia) Hs) as Z1.
    rewrite K4; [exact (HHU s Hs) | unfold kLowShadowBeg, kHighMemBeg in Z1; lia | exact (CSH s Z1)]. }
  exact Hrp. }
(* the bytes: x (kept from the cut) then 16 copies of fill mod 256 (the memset) *)
unfold bytes_at in *. intros j Hj. rewrite length_app, repeat_length in Hj.
destruct (Nat.lt_ge_cases j (length (din_x D))) as [Hjx|Hjx].
- rewrite app_nth1 by lia. destruct (Hbx j Hjx) as [Hv Hr]. split; [|exact Hr].
  apply (pd4_val_mem_kept (w_H W) (w_H W) mem (ms_mem ms4) _ 1 _); [|exact Hv]. intros kk Hkk.
  assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
  apply K4; [lia|]. intros [Hc0|Hc0]; lia.
- rewrite app_nth2 by lia.
  rewrite (nth_indep _ 0 (din_fill D mod 256)) by (rewrite repeat_length; lia). rewrite nth_repeat.
  split; [|apply Z.mod_pos_bound; lia].
  apply pd4_val1_of_aview; [apply Z.mod_pos_bound; lia|].
  replace (b + Z.of_nat j) with (b + sz + (Z.of_nat j - sz)) by lia. apply SET4. lia.
Qed.
End d.
