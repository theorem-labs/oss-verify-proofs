(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE2y.v, with its module paths and module names changed; 366 of its 406 lines of code are new or changed and 664 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Padded102B.v; 222 of its 274 lines of code are new or changed and 354 lines of the source are left out. *)
(* fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30, unstripped twin c90d4fa54d43160b): segment S5
   of the walk of padded (row PDB-S5): the NULL arm's g_own_ran_out store, from the cut PD_NULL to the
   cut PD_EPI.
   rule 24: proves function padded (reuse search: the internal file REWALK-102-PLAN.md section D3; proof-index padded: 0 named,
   0 by address, no released FUNCTION proof; second-agent check CONFIRM).
   INTERFACE (frozen, not edited): lib/B/Prog/Padded102B.v (sha256 c84199f45390; internal record).
   PROVES pd_s5_of : pd_seat_null_stmt -> pd_s6_stmt -> pd_s5_stmt (the seat and the epilogue as NAMED premises, no
   Section hypothesis), and the row's lemma pd_s5 : pd_s5_stmt by citing the interface's shared seat pd_seat_null
   (Padded102B.v Section d) and row PDB-S6's pd_s6 (lib/B/Prog/Padded102B_S6.v:71).
   THE CODE (listing lib/B/Listing_prog.v (sha256 416d90f8ab75; internal record) :1695-1697, slots PD_SLOT + 25 .. PD_SLOT + 27):
     PD_NULL      `auipc a0, 0x55b`      (PHi a0 39)
     PD_NULL + 4  `li a1, 1`
     PD_NULL + 8  `sb a1, -908(a0)`      (alias row (SOff (A_HI 39) (-908), SOff (A_OBJ 13) 0): the g_own_ran_out cell)
     falls through to PD_EPI.
   ONE symbolic run PD_NULL -> PD_EPI (paj_run_to_x_m_inv at P := pd_mn D) over the seat pd_ssn: no obligation, no
   fresh atom; the cell region ends holding the byte 1, the frame region is read-only. The run's journal is pd_J at
   the new memory; every other fact of the cut carries because the run's frame changes the memory at the one cell
   only (pd5_* below), and that cell is a program static apart from the read-only image (pdi_pst_rw), from the
   allocator's blocks (AR_client_img_law), from the frame (above alloc_ceiling), from the shadow (above SHADOW_OFF)
   and from errno (pdi_pst_errno, with errno's range from pdi_env's api_env).
   Numerals: 8 (LENGTH: a word, the shadow granule), 1 (LENGTH: the one-byte cell), 2 ^ 47 / 2 ^ 64 (WORD / stack
   bounds), 16 (cf_head at CfParams_preset, by computation), register numbers 2 .. 27 (WORD). No ADDRESS literal:
   the PrhImg fields are read by computation (pd5_pis). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomKeep YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoomPos PresetRun
  PresetReqAt PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc PRH_FnReader
  PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Padded102B Padded102B_S6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- state-free helpers ---- *)
(* a word read through a reader that agrees on its eight bytes *)
Lemma pd5_rdword_keep : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H.
assert (E0 : rd' a = rd a) by (pose proof (H 0 ltac:(lia)) as X; rewrite Z.add_0_r in X; exact X).
unfold rdword. rewrite E0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
(* a value read through memories that agree on its bytes *)
Lemma pd5_vm_keep : forall segs (m m' : word -> option byte) a n v,
  val_mem segs m a n v ->
  (forall k, (k < n)%nat -> mbyte segs m' (a + Z.of_nat k) = mbyte segs m (a + Z.of_nat k)) ->
  val_mem segs m' a n v.
Proof. intros segs m m' a n v Hv Hk k Hlt. rewrite (Hk k Hlt). exact (Hv k Hlt). Qed.
(* the shadow byte of an address below 2 ^ 47 lies in [SHADOW_OFF, 2 ^ 64) *)
Lemma pd5_shadow_rng : forall y, 0 <= y < 2 ^ 47 -> SHADOW_OFF <= shadow_of_addr SHADOW_OFF y < 2 ^ 64.
Proof.
intros y Hy. unfold shadow_of_addr.
pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)).
assert (y / 8 <= y) by (apply Z.div_le_upper_bound; lia).
unfold SHADOW_OFF. lia.
Qed.
(* every byte of the shadow hull of [x, x + n) lies in (SHADOW_OFF - 8, 2 ^ 64) when x + n <= 2 ^ 47 *)
Lemma pd5_hull_rng : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> SHADOW_OFF - 8 < s < 2 ^ 64.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as D1.
assert (D2 : (x + n - 1) / 8 <= x + n - 1) by (apply Z.div_le_upper_bound; lia).
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M2.
pose proof (Z.mul_div_le (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as M3.
unfold SHADOW_OFF in *. lia.
Qed.
(* membership of a register in a literal list (TxPut102B_END.v's tpe_inbv) *)
Ltac pd5_inbv := repeat (first [left; apply bv_eq; reflexivity | right]).
(* the image record's fields, as equations read off by computation (no number typed) *)
Ltac pd5_pi t := let v := eval vm_compute in t in let H := fresh "Hpi" in assert (H : t = v) by reflexivity.
Ltac pd5_pis :=
  pd5_pi (@pi_g_live prh_img_B); pd5_pi (@pi_gz_live prh_img_B);
  pd5_pi (@pi_g_peak prh_img_B); pd5_pi (@pi_gz_peak prh_img_B);
  pd5_pi (@pi_g_count prh_img_B); pd5_pi (@pi_gz_count prh_img_B);
  pd5_pi (@pi_g_fail prh_img_B); pd5_pi (@pi_gz_fail prh_img_B);
  pd5_pi (@pi_g_ran_out prh_img_B); pd5_pi (@pi_gz_ran_out prh_img_B);
  pd5_pi (@pi_g_own_ran_out prh_img_B); pd5_pi (@pi_gz_own_ran_out prh_img_B).

Section s5. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Existing Instance prh_img_B.
#[local] Notation CP := CfParams_preset.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).
Variable B : asyms.

(* the g_own_ran_out cell is a program static (the last row of prh_pst) *)
Lemma pd5_own_pst : forall a, pi_g_own_ran_out <= a < pi_g_own_ran_out + 1 -> Exists (in_zr a) PST.
Proof.
intros a Ha. unfold prh_pst. do 6 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
assert (Hw : Z.of_nat (@pi_gz_own_ran_out prh_img_B) = 1) by reflexivity. rewrite Hw. exact Ha.
Qed.

(* the g_most cell lies below the g_own_ran_out cell, so the NULL arm's one-byte store leaves it: by conversion on
   prh_img_B's two fields, no numeral typed here (8 is a LENGTH, pi_gz_most) *)
Lemma pd5_most_ne : forall k, (k < @pi_gz_most prh_img_B)%nat ->
  @pi_g_most prh_img_B + Z.of_nat k <> @pi_g_own_ran_out prh_img_B.
Proof.
intros k Hk.
assert (E1 : @pi_gz_most prh_img_B = 8%nat) by reflexivity.
assert (E2 : @pi_g_most prh_img_B + 8 <= @pi_g_own_ran_out prh_img_B) by (apply Z.leb_le; reflexivity).
lia.
Qed.

Lemma pd_s5_of : pd_seat_null_stmt (SK := SK) (PA := PA) B -> pd_s6_stmt (SK := SK) (PA := PA) B ->
  pd_s5_stmt (SK := SK) (PA := PA) B.
Proof.
unfold pd_seat_null_stmt, pd_s6_stmt, pd_s5_stmt.
intros SEAT S6 HIMG D ly S Hp W regs mem md k HAT.
destruct (SEAT HIMG D PD_NULL ly S Hp W regs mem md k (din_own D) (proj1 HAT)) as [HS SHOK].
pose proof HIMG as [Ibase Ientry Iown Iownimg Ialias Irw Ipstok Iowned Ierrno IMAL IENV IWR].
pose proof IENV as [[Erno0 Erno1] _]. unfold kLowMemEnd in Erno1.
destruct HAT as (HB & HNB & HDEAD).
destruct HNB as (HNBab & HNBpos & HNBerr & HNBex).
pose proof HB as (Hret & HJ & Hsaved & Hrs & Hgp & Htp & Hrod & Hmn & EHp & HL & Hroom & Hsrc & Hhome & Hsz & HHU).
unfold pd_J in HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (@YM05.alloc_ceiling_value rc) as [Cv _].
pose proof (@YM05.alloc_ceiling_lt rc) as Clt.
pd5_pis.
rewrite Iown in Iownimg. unfold IMG_LO_B, IMG_TOP_B in Iownimg.
assert (HPSTo : Exists (in_zr pi_g_own_ran_out) PST) by (apply pd5_own_pst; lia).
pose proof (Ipstok _ HPSTo) as HIo.
assert (NM : forall a, 0 <= a < 2 ^ 64 -> a <> pi_g_own_ran_out -> a mod 2 ^ 64 <> pi_g_own_ran_out)
  by (intros a Ha Hne; rewrite Z.mod_small by lia; exact Hne).
(* the seat's environment: the image's atoms, and the machine registers below 32 *)
lazymatch type of HS with st_ok_pi _ _ ?E0 _ _ =>
  assert (HEI : img_env VAL A_LIM E0) by (unfold pd_E; apply Eimg_env);
  assert (HAG : env_agree 32 (Ereg regs (map (getr (din_regs D)) [1%bv; 8%bv; 9%bv; 18%bv; 19%bv])) E0)
    by (unfold pd_E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
  set (E := E0) in *
end.
clearbody E.
assert (HVo : bv_unsigned (ew E (A_OBJ 13)) = pi_g_own_ran_out)
  by (rewrite (HEI (A_OBJ 13)) by (unfold A_OBJ, A_TEXT, A_LIM; lia); exact Iown).
pose proof HVo as HVo'.
let i := eval vm_compute in (A_OBJ 13) in change (A_OBJ 13) with i in HVo'.
(* the allocator's blocks are not image bytes, so not the cell *)
pose (LAWS := AR_laws_x_xs (cp := CP) SEGS B (AR_laws_ok_cf (cp := CP) SEGS B)).
assert (BNO : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  a mod 2 ^ 64 <> pi_g_own_ran_out).
{ intros p n a Hin Ha.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & H4 & Hc & _).
  rewrite Z.mod_small by lia. intros Ex.
  apply (blk_img_x SEGS B _ LAWS ly S Hp W mem md p n a HAR Hin Ha). rewrite Ex. exact HIo. }
(* the source window's bytes are not the cell: its home at the entry is a harness block, a read-only global or an
   allocator block of the entry, whose block list the NULL arm keeps *)
destruct Hsrc as (Hbx & Hd4 & Hdc & Ham & Hra & Hhu).
assert (DNO : forall a, din_data D <= a < din_data D + Z.of_nat (length (din_x D)) ->
  a mod 2 ^ 64 <> pi_g_own_ran_out).
{ intros a Ha. assert (Hpos : 0 < pd_size D) by (unfold pd_size; lia).
  pose proof (Hhome Hpos) as HH. unfold PRH_FnReader.prhReader_home, kept_at, kept_img, pd_size in HH.
  destruct HH as [[(b & m & HbL & Hb1 & Hb2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hbab & _ & Hb1 & Hb2)].
  - pose proof HL as (_ & _ & HHB & _). rewrite Forall_forall in HHB.
    destruct (HHB (b, m) HbL) as (Hm0 & Hbin & _). cbn [fst snd] in Hm0, Hbin.
    apply (BNO _ _ a Hbin). assert (Hcf : @cf_head CP = 16) by reflexivity. rewrite Hcf.
    unfold req_size. destruct (Z.eqb_spec (m + 16) 0); lia.
  - destruct (Hro a Ha) as (Hro' & _). apply NM; [lia|]. intros ->. exact (Irw _ HPSTo Hro').
  - destruct (Hro a Ha) as (Hro' & _). apply NM; [lia|]. intros ->. exact (Irw _ HPSTo Hro').
  - rewrite <- HNBab in Hbab. apply (BNO _ _ a Hbab).
    unfold req_size. destruct (Z.eqb_spec m 0); lia. }
(* THE RUN: PD_NULL -> PD_EPI, the memory invariant pd_mn D carried *)
assert (PSTOK : forall a, Exists (in_zr a) PST -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B))
  by (intros a Ha; exact (conj (Ipstok a Ha) (Iowned a Ha))).
pose (PLAW := srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) (din_mem D) (srr_inv_laws_memnorm_k SEGS)).
pose (RUNTO := @paj_run_to_x_m_inv fx rc SK B_prog_listing PL_pd_B PA B PST _ _ LAWS PSTOK _ PLAW).
paj_run_to_tok_x_inv RUNTO HS HJ SHOK Hmn PD_Bspan (pd_koff PD_EPI).
{ (* the one write window is the cell; the frame's is empty *)
  intros a (r & Hr & Ha). right. cbn [pd_ssn ss_mem In] in Hr.
  destruct Hr as [<-|[<-|[]]]; cbn [pd_own_region pd_frame YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [|lia].
  rewrite HVo in Ha. apply pd5_own_pst. lia. }
lazymatch type of HS with st_ok_pi _ _ _ ?ssq (restrict _ ?msq) =>
  pose proof (st_ok_pi_restrict_mkst _ _ ssq msq HS eq_refl) as Hshape;
  assert (Epc : BASE + ss_pc ssq = pd_pc PD_EPI)
    by (assert (Ek : ss_pc ssq = PD_OFF + PD_EPI) by reflexivity; rewrite Ek; unfold pd_pc; lia);
  rename msq into ms1
end.
(* the run changes the memory at the cell only *)
assert (KM : forall x : word, bv_unsigned x <> pi_g_own_ran_out ->
  mrestrict (w_H W) (ms_mem ms1) x = mrestrict (w_H W) mem x).
{ intros x Hx. apply HFr. intros (r & Hr & Ha). cbn [pd_ssn ss_mem In] in Hr.
  destruct Hr as [<-|[<-|[]]]; cbn [pd_own_region pd_frame YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
  [rewrite HVo in Ha; lia | lia]. }
assert (KMB : forall a, a mod 2 ^ 64 <> pi_g_own_ran_out ->
  mbyte SEGS (mrestrict (w_H W) (ms_mem ms1)) a = mbyte SEGS (mrestrict (w_H W) mem) a).
{ intros a Ha. unfold mbyte. rewrite KM; [reflexivity|].
  assert (Eu : bv_unsigned (Z_to_bv 64 a) = a mod 2 ^ 64) by (rewrite Z_to_bv_unsigned; reflexivity).
  rewrite Eu. exact Ha. }
assert (KA : forall a, a mod 2 ^ 64 <> pi_g_own_ran_out ->
  aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha. unfold aview. rewrite (KMB a Ha). reflexivity. }
(* the registers the run does not write *)
assert (KR : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
  getr (ms_regs ms1) r = getr regs r).
{ intros r Hr.
  exact (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv
    HS HAG ltac:(vm_compute; reflexivity) r Hr). }
(* the cell holds 1 *)
assert (HOWN1 : prh_own W (ms_mem ms1) 1).
{ split; [|right; reflexivity].
  pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & HMO & _).
  cbn [ms_mem restrict ss_mem abs_ss setpc] in HMO.
  apply Forall_inv in HMO. destruct HMO as (_ & _ & _ & HC).
  cbn [YP09.r_chunks YP09.r_base base_val] in HC. apply Forall_inv in HC.
  destruct (HC 0 ltac:(cbn; lia)) as (bt & Hcb & Hmb).
  cbn [cbyte YP09.c_val YP09.c_off] in Hcb, Hmb. injection Hcb as Hbt. subst bt.
  rewrite HVo' in Hmb.
  intros kk Hk. assert (Hk0 : kk = 0%nat) by lia. subst kk.
  replace (pi_g_own_ran_out + Z.of_nat 0) with (pi_g_own_ran_out + 0 + 0) by lia. rewrite Hmb.
  f_equal; unfold byte_of_word; cbn [sv_denot]; f_equal; vm_compute; reflexivity. }
(* hand off to S6 at PD_EPI with b = 0 *)
rewrite Hshape, Epc.
apply (S6 HIMG D ly S Hp W (ms_regs ms1) (ms_mem ms1) _ k 0).
exists 1. split.
{ split; [exact Hret|].
  split; [unfold pd_J; exact HJ|].
  split.
  { (* the five saved words, above alloc_ceiling *)
    unfold pd_saved in Hsaved |- *. rewrite Forall_forall in Hsaved |- *. intros p Hp0.
    rewrite <- (Hsaved p Hp0). apply pd5_rdword_keep. intros i Hi. apply KA.
    cbn [In] in Hp0. destruct Hp0 as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst]; apply NM; lia. }
  split.
  { destruct Hrs as (R2 & R8 & R9 & R18 & R19 & R3 & R4 & R20).
    split; [rewrite KR by pd5_inbv; exact R2|].
    split; [rewrite KR by pd5_inbv; exact R8|].
    split; [rewrite KR by pd5_inbv; exact R9|].
    split; [rewrite KR by pd5_inbv; exact R18|].
    split; [rewrite KR by pd5_inbv; exact R19|].
    split; [rewrite KR by pd5_inbv; exact R3|].
    split; [rewrite KR by pd5_inbv; exact R4|].
    intros r Hr. rewrite KR; [exact (R20 r Hr)|].
    assert (Hc : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hc as [-> | Hc]; [pd5_inbv |]). subst r. pd5_inbv. }
  split; [exact Hgp|]. split; [exact Htp|].
  split.
  { (* the read-only view: the cell is writable data (pdi_pst_rw) *)
    intros a Hro Hno Herr. rewrite KA; [exact (Hrod a Hro Hno Herr)|].
    assert (Hi : in_img SEGS a)
      by (destruct Hro as [(sg & Hin & _ & Hr) | Hr];
          [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]).
    pose proof (@pa_segs_low _ _ PA a Hi) as Hlo. unfold kLowMemEnd in Hlo.
    apply NM; [lia|]. intros ->. exact (Irw _ HPSTo Hro). }
  split; [exact Hmn|]. split; [exact EHp|].
  split.
  { (* the ledger: the other statics and the harness heads *)
    unfold prh_ledger in HL |- *. destruct HL as (HG0 & HND & HHB & HPerm).
    split; [|split; [exact HND|split; [|exact HPerm]]].
    - unfold prh_glob in HG0 |- *. destruct HG0 as (Glive & Gpeak & Gcnt & Gfail & Gran & Gmost & Gown & Gb).
      split; [|split; [|split; [|split; [|split; [|split; [|split; [exact HOWN1 | exact Gb]]]]]]].
      + eapply pd5_vm_keep; [exact Glive|]. intros kk Hk. apply KMB. apply NM; lia.
      + eapply pd5_vm_keep; [exact Gpeak|]. intros kk Hk. apply KMB. apply NM; lia.
      + eapply pd5_vm_keep; [exact Gcnt|]. intros kk Hk. apply KMB. apply NM; lia.
      + eapply pd5_vm_keep; [exact Gfail|]. intros kk Hk. apply KMB. apply NM; lia.
      + eapply pd5_vm_keep; [exact Gran|]. intros kk Hk. apply KMB. apply NM; lia.
      + (* the g_most cell: a static other than the own cell, so the store leaves it *)
        destruct Gmost as [Gv Gr]. split; [|exact Gr].
        eapply pd5_vm_keep; [exact Gv|]. intros kk Hk. apply KMB. pose proof (pd5_most_ne kk Hk) as Hne.
        assert (E2 : @pi_g_most prh_img_B + 8 <= @pi_g_own_ran_out prh_img_B) by (apply Z.leb_le; reflexivity).
        assert (E1 : @pi_gz_most prh_img_B = 8%nat) by reflexivity.
        refine (NM _ _ Hne).
        assert (E0 : 0 <= @pi_g_most prh_img_B) by (apply Z.leb_le; reflexivity).
        assert (E3 : @pi_g_own_ran_out prh_img_B < 2 ^ 64) by (apply Z.ltb_lt; reflexivity). lia.
    - eapply Forall_impl; [|exact HHB]. intros [a ka] (Hk0 & Hin & HinHp & Hal & Hv). cbn [fst snd] in *.
      split; [exact Hk0|]. split; [exact Hin|]. split; [exact HinHp|]. split; [exact Hal|].
      eapply pd5_vm_keep; [exact Hv|]. intros i Hi. apply KMB.
      apply (BNO _ _ _ Hin). assert (Hcf : @cf_head CP = 16) by reflexivity. rewrite Hcf.
      unfold req_size. destruct (Z.eqb_spec (ka + 16) 0); lia. }
  split; [exact Hroom|].
  split.
  { (* the source window, its shadow and its hull *)
    split.
    { unfold bytes_at, garr8 in Hbx |- *. intros j Hj. destruct (Hbx j Hj) as [Hv Hr]. split; [|exact Hr].
      eapply pd5_vm_keep; [exact Hv|]. intros i Hi. apply KMB. apply DNO. lia. }
    split; [exact Hd4|]. split; [exact Hdc|]. split; [exact Ham|]. split.
    { intros y Hy. rewrite KA; [exact (Hra y Hy)|].
      assert (HSO : pi_g_own_ran_out < SHADOW_OFF - 8) by (unfold SHADOW_OFF; lia).
      pose proof (pd5_shadow_rng y ltac:(lia)) as Hsy. apply NM; lia. }
    intros Hp0 s Hs. rewrite KA; [exact (Hhu Hp0 s Hs)|].
    assert (HSO : pi_g_own_ran_out < SHADOW_OFF - 8) by (unfold SHADOW_OFF; lia).
    pose proof (pd5_hull_rng (din_data D) (Z.of_nat (length (din_x D))) s ltac:(lia) Hp0 ltac:(lia) Hs) as Hsr.
    apply NM; lia. }
  split; [exact Hhome|]. split; [exact Hsz | exact HHU]. }
(* the kit's outcome clause needs the arm's death at a consumer position (pd_dead): carried from S1 unchanged *)
split; [|intros _; exact HDEAD].
(* the REFUSED arm with own' = 1; errno is apart from the cell (pdi_pst_errno) and does not wrap (pdi_env) *)
left. split; [reflexivity|]. split; [reflexivity|].
split; [exact HNBab|]. split; [exact HNBpos|]. split; [|exact HNBex].
intros kk Hk. rewrite KA; [exact (HNBerr kk Hk)|].
apply NM; [lia|]. intros Ex. apply (Ierrno _ HPSTo). lia.
Qed.

(* the row's lemma: the shared NULL seat (Padded102B.v pd_seat_null) and row PDB-S6's epilogue (Padded102B_S6.v pd_s6) *)
Lemma pd_s5 : pd_s5_stmt (SK := SK) (PA := PA) B.
Proof. exact (pd_s5_of (pd_seat_null (SK := SK) (PA := PA) B) (pd_s6 (SK := SK) (PA := PA) B)). Qed.

End s5.
