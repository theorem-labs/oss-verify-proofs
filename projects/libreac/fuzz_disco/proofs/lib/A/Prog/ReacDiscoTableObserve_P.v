(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 401 of its 437 lines of code are new or changed and 33 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI0m.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3u.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow DiscoSyms DiscoList DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase DiscoAddr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YI16 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve ReacDiscoTableObserve_C.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_observe_c reac_disco_table_observe.
Module DTC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.disco_table_c.
Module RDO := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac prraw HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
Definition R_hn : YP09.region := YP09.mkRegion (Some 10%nat) 384 400 0 0 [YP09.mkChunk 384 (CData 0 384 16)].
Definition pro_ss : sstate :=
  mkSS AF_reac_disco_table_observe sr_atoms [stack_region 96; got_regionP; bcell_regionP 32; R_hn] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 8 (2 ^ 47 - 401) 3); (32%nat, mkAF SB SB 0)] [] []).
Definition pro_Bx : sv := SOff 32 0.
Definition pro_SH : list shent := [mkSHE 10 0 400].
Definition pro_rs_ok (rs : smem) : bool :=
  forallb (fun r => (YP09.r_whi r <=? YP09.r_wlo r) ||
    (((match YP09.r_base r with Some n => Nat.eqb n 2 | None => false end) && (-96 <=? YP09.r_wlo r))
      && (YP09.r_whi r <=? 0))) rs.
Lemma pro_rs_win : forall E rs a sp, bv_unsigned (ew E 2) = sp -> pro_rs_ok rs = true -> in_wrange E rs a ->
  sp - 96 <= a < sp.
Proof.
intros E rs a sp H2 Hok (r & Hin & Ha). unfold pro_rs_ok in Hok. rewrite forallb_forall in Hok.
specialize (Hok r Hin). apply orb_true_iff in Hok as [Hok | Hok]; [apply Z.leb_le in Hok; lia|].
apply andb_prop in Hok as [Hok Hhi]. apply andb_prop in Hok as [Hb Hlo].
apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
revert Ha Hb. destruct (YP09.r_base r) as [n|]; intros Ha Hb; [|discriminate Hb].
apply Nat.eqb_eq in Hb. subst n. cbn [base_val] in Ha. rewrite H2 in Ha. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Definition pro_env (c : tctx) : env :=
  Eimg (mkEnv (ew (Ereg (tregs c) [Z_to_bv 64 SB])) (fun d => match d with 0%nat => tT c | _ => [] end)).
Lemma pro_env_reg : forall c n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (pro_env c) n = YK11.getr (tregs c) x.
Proof.
intros c n x Hn. unfold pro_env. pose proof (u5_range x) as Hx.
rewrite Eimg_low by (unfold A_TEXT; lia). cbn [ew]. exact (ew_Ereg_nat (tregs c) _ n x Hn).
Qed.
Lemma pro_env_sb : forall c, ew (pro_env c) 32 = Z_to_bv 64 SB.
Proof.
intros c. unfold pro_env. rewrite Eimg_low by (unfold A_TEXT; lia). cbn [ew].
exact (ew_Ereg_extra (tregs c) [Z_to_bv 64 SB] 0).
Qed.
Lemma pro_env_obj : forall c i, (A_TEXT <= A_OBJ i < A_LIM)%nat -> ew (pro_env c) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros c i Hi. unfold pro_env. apply Eimg_img. exact Hi. Qed.
Lemma pro_regs_ok : forall c, regs_ok (pro_env c) sr_atoms (tregs c).
Proof.
intros c. apply regs_ok_by_cases. intros z Hz. cbv [all_regs In] in Hz.
repeat (destruct Hz as [<-|Hz];
  [ lazymatch goal with |- _ = sv_denot ?E (sr_get ?sr ?q) =>
      let v := eval vm_compute in (sr_get sr q) in change (sr_get sr q) with v end;
    first
    [ reflexivity
    | lazymatch goal with |- YK11.getr _ ?q = sv_denot _ (SOff ?n 0) =>
        cbn [sv_denot]; rewrite (pro_env_reg c n q eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity end ]
  | ]).
destruct Hz.
Qed.
Lemma pro_dw : forall c E, ed E 0 = tT c -> 0 <= DTC.n_of (tT c) -> data_word E 0 384 4 = DTC.n_of (tT c).
Proof.
intros c E HE Hn.
assert (U : data_word E 0 384 4 = DTC.u_at (tT c) 384 4) by (unfold data_word, DTC.u_at, DTC.sub; rewrite HE; reflexivity).
rewrite U. pose proof (RDO.u32_range (tT c) 384) as R.
unfold DTC.n_of, DTC.s32_at in *. set (u := DTC.u_at (tT c) 384 4) in *.
unfold bv_swrap, bv_wrap in *. change (bv_half_modulus 32) with (2 ^ 31) in *. change (bv_modulus 32) with (2 ^ 32) in *.
pose proof (Z.div_mod (u + 2 ^ 31) (2 ^ 32) ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (u + 2 ^ 31) (2 ^ 32) ltac:(lia)) as M.
set (q := (u + 2 ^ 31) / 2 ^ 32) in *. set (r := (u + 2 ^ 31) mod 2 ^ 32) in *.
lia.
Qed.
Lemma pro_mbyte_out : forall E rs (m m' : word -> option byte) a sp, frame_of E rs m m' ->
  bv_unsigned (ew E 2) = sp -> pro_rs_ok rs = true -> 0 <= a < 2 ^ 64 -> ~ (sp - 96 <= a < sp) ->
  mbyte SEGS m' a = mbyte SEGS m a.
Proof.
intros E rs m m' a sp HF H2 Hok Ha Hout. apply (mbyte_of_frame_x SEGS E rs m m' a HF Ha).
intros r Hin Hr. apply Hout. apply (pro_rs_win E rs a sp H2 Hok). exists r. split; [exact Hin | exact Hr].
Qed.
Lemma pro_step2 : forall (H : word -> bool) E1 rs1 E2 rs2 (m0 m1 m2 : word -> option byte) sp,
  frame_of E1 rs1 (mrestrict H m0) (mrestrict H m1) -> frame_of E2 rs2 (mrestrict H m1) (mrestrict H m2) ->
  bv_unsigned (ew E1 2) = sp -> bv_unsigned (ew E2 2) = sp -> pro_rs_ok rs1 = true -> pro_rs_ok rs2 = true ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 96 <= a < sp) -> aview SEGS H m2 a = aview SEGS H m0 a.
Proof.
intros H E1 rs1 E2 rs2 m0 m1 m2 sp HF1 HF2 U1 U2 K1 K2 a Ha Hout. unfold aview. f_equal.
rewrite (pro_mbyte_out E2 rs2 _ _ a sp HF2 U2 K2 Ha Hout).
exact (pro_mbyte_out E1 rs1 _ _ a sp HF1 U1 K1 Ha Hout).
Qed.
Lemma pro_slot : forall E m lo hi wlo whi cs od (n : nat) (v : word) sp,
  YP09.region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 2) = sp -> In (YP09.mkChunk od (CVal 8 (SOff n 0))) cs -> ew E n = v ->
  val_mem SEGS m (sp + od) 8 (bv_unsigned v).
Proof.
intros E m lo hi wlo whi cs od n v sp (_ & _ & _ & Hcs) H2 Hc Hv.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite H2 in Hck.
change 8%nat with (N.to_nat 8). apply (val_of_chunk_ok SEGS E m sp od 8%N (SOff n 0) (bv_unsigned v) Hck).
- cbn [sv_denot]. rewrite Hv, Z.add_0_r; reflexivity.
- pose proof (bv_unsigned_in_range 64 v) as R. change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in R. exact R.
- cbn. lia.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Lemma pro_awr : forall c E rs, tpre B c -> bv_unsigned (ew E 2) = spZ (tregs c) -> pro_rs_ok rs = true ->
  awr_ok E rs (tSTK c) (tsp0 c) (tFP c) (ablocks B (tly c) (tS c)) (ablocks B (tlyc c) (tSc c)) (tlyc c) (town c).
Proof.
intros c E rs HP H2 Hok a Ha. pose proof (pro_rs_win E rs a _ H2 Hok Ha) as Wa.
pose proof (tp_wlo _ _ HP) as Hwlo. pose proof (tp_whi _ _ HP) as Hwhi.
assert (STK : REAC_DISCO_TABLE_OBSERVE_STK = 8288) by reflexivity. rewrite STK in Hwlo.
unfold awr_byte. left. lia.
Qed.
Lemma tobs_t_off_img : forall c, tpre B c -> forall a, tt c <= a < tt c + 400 -> a < IMG_LO \/ IMG_TOP <= a.
Proof.
intros c HP a Ha.
pose proof (tp_J _ _ HP) as HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hceil & Hslo & _) & _).
pose proof asan_consts as (C1 & _ & _ & _ & _).
pose proof HAR as (_ & HLG & _).
pose proof (pa_img_cover (tlyc c) (tSc c) (tmdc c) HLG) as [PC1 PC2].
destruct (proj1 (tp_tawr _ _ HP a Ha)) as [Hw | [[_ (b & n & Hin & Hb)] | [(b & n & Hin & _ & Hb) | (cid & pos & Hin & Hz)]]].
- right. unfold IMG_TOP. lia.
- destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR (or_introl (ex_intro _ b (ex_intro _ n (conj Hin Hb))))) as [Hni _].
  unfold in_zr in Hni. lia.
- destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR (or_introl (ex_intro _ b (ex_intro _ n (conj Hin Hb))))) as [Hni _].
  unfold in_zr in Hni. lia.
- assert (Hin' : In (cid, pos) (frames (tSc c))) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
  destruct Hz as [Hz | Hz]; unfold in_zr in Hz; cbn [fst snd] in Hz.
  + destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR
      (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hin' Hz)))))) as [Hni _].
    unfold in_zr in Hni. lia.
  + right. destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin') as (Hf4096 & _).
    pose proof (Z.div_pos (frame_addr (tlyc c) cid pos) 8 ltac:(lia) ltac:(lia)) as Hd.
    unfold shadow_addr, SHADOW_OFF, IMG_TOP in *. lia.
Qed.
Lemma tobs_hdr_off_img : forall c, tpre B c -> tt c + 400 <= IMG_LO \/ IMG_TOP <= tt c + 384.
Proof.
intros c HP. pose proof (tobs_t_off_img c HP) as H.
destruct (Z_lt_le_dec (tt c + 399) IMG_LO) as [Hl | Hl]; [left; lia | right].
pose proof (H (tt c + 399) ltac:(lia)) as H1.
pose proof (H (Z.max (tt c + 384) IMG_LO) ltac:(lia)) as H2.
unfold IMG_LO, IMG_TOP in *. lia.
Qed.
Lemma tobs_m_intro : forall c regs1 m1 md1,
  tpre B c ->
  ajournal SEGS B (tSTK c) (tsp0 c) (tFP c) (tly c) (tS c) (tW0 c) (tmem0 c) (tmd0 c) (town c)
    (tlyc c) (tSc c) (tW c) m1 md1 (tk c) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (tregs c) - 96 <= a < spZ (tregs c)) ->
     aview SEGS (w_H (tW c)) m1 a = aview SEGS (w_H (tW c)) (tmemc c) a) ->
  (forall a, apresent (w_H (tW c)) (tmemc c) a -> apresent (w_H (tW c)) m1 a) ->
  spZ regs1 = spZ (tregs c) - 96 ->
  YK11.getr regs1 3 = YK11.getr (tregs c) 3 -> YK11.getr regs1 4 = YK11.getr (tregs c) 4 ->
  YK11.getr regs1 27 = YK11.getr (tregs c) 27 ->
  YK11.getr regs1 8 = w64 (tt c) -> YK11.getr regs1 9 = w64 (tow c) -> YK11.getr regs1 20 = w64 (tnow c) ->
  YK11.getr regs1 21 = w64 (tt c + 384) -> YK11.getr regs1 22 = w64 SB ->
  YK11.getr regs1 24 = w64 (SB + (tt c + 384) / 8) ->
  tobs_frame c (mrestrict (w_H (tW c)) m1) (spZ regs1) ->
  tobs_m B c regs1 m1 md1 (tT c).
Proof.
intros c regs1 m1 md1 HP HJ2 Hstep Hgrow Hsp G3 G4 G27 G8 G9 G20 G21 G22 G24 HF.
pose proof (tp_J _ _ HP) as HJc. pose proof HJc as (HARc & _).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & (_ & _ & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (tp_wlo _ _ HP) as Hwlo. pose proof (tp_whi _ _ HP) as Hwhi.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t63 _ _ HP) as Ht63. pose proof (tp_tam _ _ HP) as Htam.
pose proof (tp_twin _ _ HP) as Htwin.
pose proof (tp_s0 _ _ HP) as Hs0. pose proof (tp_s63 _ _ HP) as Hs63. pose proof (tp_sam _ _ HP) as Hsam.
pose proof (tp_swin _ _ HP) as Hswin.
pose proof (tp_Gl _ _ HP) as HGl. pose proof (tp_Tl _ _ HP) as HTl.
assert (STK : REAC_DISCO_TABLE_OBSERVE_STK = 8288) by reflexivity. rewrite STK in Hwlo, Htwin, Hswin.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam, Hsam.
assert (Hwin : alloc_ceiling <= spZ (tregs c) - 8288) by lia.
assert (Hband : forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 ->
  aview SEGS (w_H (tW c)) m1 s = aview SEGS (w_H (tW c)) (tmemc c) s).
{ intros s0 Hs0'. apply Hstep; unfold SHADOW_OFF in *; lia. }
constructor.
- exact HJ2.
- exact Hsp.
- exact G3.
- exact G4.
- exact G27.
- exact G8.
- exact G9.
- exact G20.
- exact G21.
- exact G22.
- exact G24.
- exact HF.
- eapply garr8_aview_kept; [|exact (tp_T _ _ HP)]. intros x Hx. rewrite length_map, HTl in Hx.
  change (Z.of_nat 400) with 400 in Hx. apply Hstep; lia.
- exact HTl.
- eapply garr8_aview_kept; [|exact (tp_G _ _ HP)]. intros x Hx. rewrite length_map, HGl in Hx.
  change (Z.of_nat 24) with 24 in Hx. apply Hstep; lia.
- eapply ra_kept_band; [exact Hband | lia | lia | exact (tp_tra _ _ HP)].
- eapply ra_kept_band; [exact Hband | lia | lia | exact (tp_sra _ _ HP)].
- eapply hull_kept_band; [exact Hband | lia | lia | lia | exact (tp_thull _ _ HP)].
- eapply hull_kept_band; [exact Hband | lia | lia | lia | exact (tp_shull _ _ HP)].
- intros a Ha. apply Hgrow. exact (proj2 (tp_tawr _ _ HP a Ha)).
- intros a Ha. apply Hgrow. exact (tp_spres _ _ HP a Ha).
- unfold tobs_kept, treac_disco_table_observe_kept. rewrite STK.
  split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw Ht. apply Hstep; lia.
  + intros b m i Hb Hi Ht. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARc Hb) as (_ & Hb4096 & Hbceil & _).
    apply Hstep; lia.
  + intros a Himg Hno Herr. pose proof (pa_segs_low a Himg) as Hlow. rewrite C5 in Hlow. apply Hstep; lia.
  + intros cid pos a Hin Hz Ht. destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HARc Hin) as (Hf4096 & Hfceil & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfb.
    assert (Hfa : 0 <= a < alloc_ceiling \/ SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44).
    { destruct Hz as [Hz | Hz]; unfold in_zr, frame_rng, shadow_addr in Hz; cbn [fst snd] in Hz; [left; lia | right].
      pose proof (Z.div_pos (frame_addr (tlyc c) cid pos) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_pos (fs_frame_bytes cid) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.mul_div_le (frame_addr (tlyc c) cid pos) 8 ltac:(lia)).
      pose proof (Z.mul_div_le (fs_frame_bytes cid) 8 ltac:(lia)). unfold SHADOW_OFF in *. lia. }
    apply Hstep; unfold SHADOW_OFF in Hfa; lia.
  + intros a Ha Hw Hp. apply Hgrow. exact Hp.
  + intros a Ha. apply Hpres2. lia.
Qed.
Lemma seg_pro : forall c, SegLoop B c -> SegNew B c -> tpre B c ->
  SRr SEGS (tW c) (cfg_at SEGS (BASE + AF_reac_disco_table_observe) (tregs c) (tmemc c) (tmdc c)) (tpost B c).
Proof.
intros c HLoop HNew HP.
pose proof (tp_J _ _ HP) as HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (tp_wlo _ _ HP) as Hwlo. pose proof (tp_whi _ _ HP) as Hwhi. pose proof (tp_al _ _ HP) as Hal.
pose proof (tp_t0 _ _ HP) as Ht0. pose proof (tp_t8 _ _ HP) as Ht8. pose proof (tp_tam _ _ HP) as Htam.
pose proof (tp_twin _ _ HP) as Htwin. pose proof (tp_Tl _ _ HP) as HTl.
pose proof (tp_T1 _ _ HP) as HT1. unfold DTC.tbl_T1 in HT1.
assert (STK : REAC_DISCO_TABLE_OBSERVE_STK = 8288) by reflexivity. rewrite STK in Hwlo, Htwin.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam.
pose proof (tobs_hdr_off_img c HP) as Hhdr.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as HgotR.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as HcellR.
pose proof (pal_got_cell B TL) as HgcD. unfold IMG_LO, IMG_TOP in Hhdr, HgotR, HcellR.
pose proof (pa_val_range (A_OBJ 1)) as V1. pose proof (pa_val_range (A_OBJ 66)) as V66.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
assert (Hspr : 2 ^ 46 + 96 <= spZ (tregs c) <= 2 ^ 47) by lia.
pose proof (Z.div_mod (tt c) 8 ltac:(lia)) as Dt. rewrite Ht8, Z.add_0_r in Dt.
assert (Htr : 8 <= tt c <= 2 ^ 47 - 401) by lia.
set (E := pro_env c).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew E n = YK11.getr (tregs c) x)
  by (intros n x Hnx; subst E; apply pro_env_reg; exact Hnx).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply pro_env_sb).
assert (ED0 : ed E 0 = tT c) by reflexivity.
assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply pro_env_obj; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO66 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (subst E; apply pro_env_obj; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (HRO : regs_ok E sr_atoms (tregs c)) by (subst E; apply pro_regs_ok).
clearbody E.
assert (Usp : bv_unsigned (ew E 2) = spZ (tregs c)) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 (tt c)) by (rewrite (EE 10%nat 10%bv eq_refl); exact (tp_a0 _ _ HP)).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (B1 : base_val E (Some (A_OBJ 1)) = VAL (A_OBJ 1)) by (apply VB; [exact EO1 | lia]).
assert (B66 : base_val E (Some (A_OBJ 66)) = VAL (A_OBJ 66)) by (apply VB; [exact EO66 | lia]).
assert (B10 : base_val E (Some 10%nat) = tt c) by (apply VB; [exact E10 | lia]).
assert (B2 : base_val E (Some 2%nat) = spZ (tregs c)) by (cbn [base_val]; exact Usp).
assert (HS : st_ok_pi SEGS VAL E pro_ss (restrict (w_H (tW c))
  (YK11.mkst (tregs c) (Z_to_bv 64 (BASE + AF_reac_disco_table_observe)) (tmemc c) (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pro_ss. apply pa_entry_st_ok_full.
  - exact HRO.
  - vm_compute. reflexivity.
  - unfold stack_region, got_regionP, bcell_regionP, R_hn.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite B2. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply apresent_writable. apply Hpres. lia.
    + rewrite B1. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
      [ cbn [sv_denot]; rewrite EO66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | ].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    + rewrite B66. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 (SOff 32 0) SB);
      [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SB; lia | cbn; lia | ].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
    + rewrite B10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_cdata_garr8_s E _ (tt c) (tT c) 0 384 16); [exact (tp_T _ _ HP) | exact ED0 | lia | lia | lia | lia].
  - apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, R_hn, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B2, B1, B66, B10.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E32, !unsigned_lit_small by (unfold SB; lia).
    repeat split; try lia;
    first [ change (2 ^ 4) with 16; exact Hal
          | change (2 ^ 3) with 8; exact Ht8
          | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity ]. }
assert (UBx : U E pro_Bx = SHADOW_OFF) by (unfold pro_Bx; rewrite (U_atom E 32 SB E32) by (unfold SB; lia); reflexivity).
assert (U10 : U E (SOff 10 0) = tt c) by (apply U_atom; [exact E10 | lia]).
assert (SHOK : sh_ok SEGS pro_Bx pro_SH E (mrestrict (w_H (tW c)) (tmemc c))).
{ unfold sh_ok, pro_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H (tW c)) (tmemc c) E pro_Bx 10 (tt c) 400 (tt c) 0 400 (tp_tra _ _ HP) UBx U10); try lia.
  intros x Hx. rewrite ?Z.min_l, ?Z.max_r in Hx by lia. unfold SHADOW_OFF. lia. }
change (cfg_at SEGS (BASE + AF_reac_disco_table_observe) (tregs c) (tmemc c) (tmdc c)) with
  (mkCfg (YK11.mkst (tregs c) (Z_to_bv 64 (BASE + AF_reac_disco_table_observe)) (tmemc c) (YK11.seg_rom SEGS)) (tmdc c)).
paj_run_tok RUN HS HJ SHOK TBspan.
{ eapply pro_awr; [exact HP | exact Usp | vm_compute; reflexivity]. }
rename HFr into HFr1. rename HG into HG1. clear HF. rename ms into msA.
psrr_branch_tok RUN BR HS SHOK TBspan.
- cbn [sv_denot] in Hc. rewrite (pro_dw c) in Hc by (first [exact ED0 | lia]). rewrite sext32_small in Hc by lia.
  assert (Hn0 : DTC.n_of (tT c) = 0).
  { destruct (Z.eq_dec (DTC.n_of (tT c)) 0) as [Hz | Hz]; [exact Hz | exfalso].
    revert Hc Hz HT1. generalize (DTC.n_of (tT c)). intros n Hc' Hz' HT1'.
    assert (Hcs : n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8) by lia.
    destruct Hcs as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute in Hc'; discriminate Hc'. }
  paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x53f0.
  { eapply pro_awr; [exact HP | cbn [ewset ew Nat.eqb]; exact Usp | vm_compute; reflexivity]. }
  pose proof (pro_step2 (w_H (tW c)) _ _ _ _ _ _ _ (spZ (tregs c)) HFr1 HFr ltac:(cbn [ewset ew Nat.eqb]; exact Usp)
    ltac:(cbn [ewset ew Nat.eqb]; exact Usp) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as Hstep.
  pose proof (mem_grows_trans _ _ _ HG1 HG) as HGG.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (27%bv : bv 5) P27.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prraw HS (24%bv : bv 5) P24.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as Hreg0. cbn [ms_mem restrict] in Hreg0.
  assert (Hsp1 : spZ (ms_regs ms) = spZ (tregs c) - 96).
  { change (spZ (ms_regs ms)) with (bv_unsigned (YK11.getr (ms_regs ms) 2)). rewrite P2, Usp, unsigned_lit_small by lia; lia. }
  apply (HNew (ms_regs ms) (ms_mem ms) _ HP).
  + apply (tobs_m_intro c _ _ _ HP HJ Hstep (fun a Ha => apresent_grows _ _ _ a HGG Ha) Hsp1).
    * rewrite P3. exact (EE 3%nat 3%bv eq_refl).
    * rewrite P4. exact (EE 4%nat 4%bv eq_refl).
    * rewrite P27. exact (EE 27%nat 27%bv eq_refl).
    * rewrite P8, (EE 10%nat 10%bv eq_refl). exact (tp_a0 _ _ HP).
    * rewrite P9, (EE 12%nat 12%bv eq_refl). exact (tp_a2 _ _ HP).
    * rewrite P20, (EE 13%nat 13%bv eq_refl). exact (tp_a3 _ _ HP).
    * rewrite P21, E10, unsigned_lit_small by lia; reflexivity.
    * rewrite P22. exact E32.
    * rewrite P24. rewrite (denot_shx _ 10 32 384 (tt c) SB)
        by (first [cbn [ewset ew Nat.eqb]; first [exact E10 | exact E32] | unfold SB; lia | lia]); reflexivity.
    * rewrite Hsp1. unfold tobs_frame, TS.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      lazymatch goal with |- val_mem _ _ (_ + ?o) _ (bv_unsigned (YK11.getr _ (Z_to_bv 5 ?r))) =>
        let n := eval cbv in (Z.to_nat r) in
        let od := eval cbv in (o - 96) in
        replace (spZ (tregs c) - 96 + o) with (spZ (tregs c) + od) by lia;
        apply (pro_slot _ _ _ _ _ _ _ od n _ (spZ (tregs c)) Hreg0 ltac:(cbn [ewset ew Nat.eqb]; exact Usp));
        [ cbn [In]; repeat (first [left; reflexivity | right])
        | cbn [ewset ew Nat.eqb]; apply EE; reflexivity ] end.
  + rewrite P18, (EE 11%nat 11%bv eq_refl). exact (tp_a1 _ _ HP).
  + rewrite P23. rewrite (pro_dw c) by (first [exact ED0 | lia]). rewrite sext32_small by lia; reflexivity.
  + intros j Hj. exfalso. lia.
  + lia.
- cbn [sv_denot] in Hc. rewrite (pro_dw c) in Hc by (first [exact ED0 | lia]). rewrite sext32_small in Hc by lia.
  assert (Hn1 : 1 <= DTC.n_of (tT c)).
  { destruct (Z.eq_dec (DTC.n_of (tT c)) 0) as [Hz | Hz]; [exfalso | lia].
    rewrite Hz in Hc. vm_compute in Hc. discriminate Hc. }
  paj_run_to_tok RUNTO HS HJ SHOK TBspan 0x5128.
  { eapply pro_awr; [exact HP | cbn [ewset ew Nat.eqb]; exact Usp | vm_compute; reflexivity]. }
  pose proof (pro_step2 (w_H (tW c)) _ _ _ _ _ _ _ (spZ (tregs c)) HFr1 HFr ltac:(cbn [ewset ew Nat.eqb]; exact Usp)
    ltac:(cbn [ewset ew Nat.eqb]; exact Usp) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as Hstep.
  pose proof (mem_grows_trans _ _ _ HG1 HG) as HGG.
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (27%bv : bv 5) P27.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (20%bv : bv 5) P20.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
  prraw HS (24%bv : bv 5) P24.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as Hreg0. cbn [ms_mem restrict] in Hreg0.
  assert (Hsp1 : spZ (ms_regs ms) = spZ (tregs c) - 96).
  { change (spZ (ms_regs ms)) with (bv_unsigned (YK11.getr (ms_regs ms) 2)). rewrite P2, Usp, unsigned_lit_small by lia; lia. }
  apply (HLoop (ms_regs ms) (ms_mem ms) _ 0 HP).
  + apply (tobs_m_intro c _ _ _ HP HJ Hstep (fun a Ha => apresent_grows _ _ _ a HGG Ha) Hsp1).
    * rewrite P3. exact (EE 3%nat 3%bv eq_refl).
    * rewrite P4. exact (EE 4%nat 4%bv eq_refl).
    * rewrite P27. exact (EE 27%nat 27%bv eq_refl).
    * rewrite P8, (EE 10%nat 10%bv eq_refl). exact (tp_a0 _ _ HP).
    * rewrite P9, (EE 12%nat 12%bv eq_refl). exact (tp_a2 _ _ HP).
    * rewrite P20, (EE 13%nat 13%bv eq_refl). exact (tp_a3 _ _ HP).
    * rewrite P21, E10, unsigned_lit_small by lia; reflexivity.
    * rewrite P22. exact E32.
    * rewrite P24. rewrite (denot_shx _ 10 32 384 (tt c) SB)
        by (first [cbn [ewset ew Nat.eqb]; first [exact E10 | exact E32] | unfold SB; lia | lia]); reflexivity.
    * rewrite Hsp1. unfold tobs_frame, TS.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      lazymatch goal with |- val_mem _ _ (_ + ?o) _ (bv_unsigned (YK11.getr _ (Z_to_bv 5 ?r))) =>
        let n := eval cbv in (Z.to_nat r) in
        let od := eval cbv in (o - 96) in
        replace (spZ (tregs c) - 96 + o) with (spZ (tregs c) + od) by lia;
        apply (pro_slot _ _ _ _ _ _ _ od n _ (spZ (tregs c)) Hreg0 ltac:(cbn [ewset ew Nat.eqb]; exact Usp));
        [ cbn [In]; repeat (first [left; reflexivity | right])
        | cbn [ewset ew Nat.eqb]; apply EE; reflexivity ] end.
  + rewrite P18, (EE 11%nat 11%bv eq_refl). exact (tp_a1 _ _ HP).
  + rewrite P23. rewrite (pro_dw c) by (first [exact ED0 | lia]). rewrite sext32_small by lia; reflexivity.
  + rewrite P25; reflexivity.
  + rewrite P26. rewrite (pro_dw c) by (first [exact ED0 | lia]). rewrite ?sext32_small by lia.
    revert Hn1 HT1. generalize (DTC.n_of (tT c)). intros n Hn1' HT1'.
    assert (Hcs : n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8) by lia.
    destruct Hcs as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; apply bv_eq; vm_compute; reflexivity.
  + lia.
  + intros j' Hj'. exfalso. lia.
Qed.
End h.
End f.
End d.
