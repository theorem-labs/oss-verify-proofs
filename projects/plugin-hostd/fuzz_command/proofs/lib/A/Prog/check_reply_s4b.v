(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment 4b of check_reply's walk (fuzz_command.asan, 0x86d78): the refusal
   path from the return of snprintf at 0x86f9c to the strcmp call at 0x86fb8 (cr_s4b : CR_STRCMP_stmt ->
   CR_RSNP_stmt, lib/A/Prog/check_reply_m.v), after proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (a call step with
   cl_callS and jafter_call_keep_pi).

   The segment is stated at its section's FP state, and check_reply_s4.v uses it at the FP state the snprintf wrapper
   returns (the segment-lemma form): the walk seeds the mid-walk state at 0x86f9c
   (check_reply_sd.v cr_seed) with g_rec's fields as the only region, runs `mv a0,s5` to the call of
   rec_code_declared, takes the code's declared answer 1 (reply_okA), so the abort branch at 0x86fa4 is not taken,
   and runs over the inline check of g_rec.reply and the loads of the reply and the refusal to 0x86fb8. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaRun PaShadow PaStep CmdSyms
  CmdList CmdPa PaJournal CmdPaLib PaLibG PaLibH PaLibF PaDenot PaSB PaCall PaArt CmdBase CmdRep CmdObj CmdRo CmdZsh
  PaNoChain CmdRecBase CmdRecCells CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_reply_code_c check_reply_answer_c
  rec_code_declared_c rec_shape_of_c syntax_reply_matches_c check_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_reply_k check_reply_m check_reply_sd
  check_reply_t check_reply_s4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Context {RO : ro_below_ofl SEGS RLO RHI}.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis RCD : forall fx0 : YK11.FPState, @trec_code_declared_spec fx0 rc SK PI B MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis CMD_RO_AT : forall ly S W mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) mem) -> cmd_ro_ok (aview SEGS (w_H W) mem).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Theorem cr_s4b : CR_STRCMP_stmt B RLO RHI -> CR_RSNP_stmt B RLO RHI.
Proof.
intros STRCMP v lyc Sc Wc regs1 memc mdc pos CX MID RA Hneg R19 R21 HTXT LS.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (s4_nums B LAWS v CX) as (Hp4096 & Hp16 & Hphi & Hnr).
pose proof (cr_seed B RLO RHI LAWS v lyc Sc Wc regs1 memc mdc pos CR_RET_SNP false CX MID RA Hp4096 Hp16 Hphi Hnr) as HS0.
pose proof CX as (HPRE & Hfr7 & HROD & HGOT & HROK & HROI & HVO & HGRD & H10 & HREC & Hn1 & Hry & Hno0 & Hrepv & Htr
  & Hansv & Hta & Hw8 & Hspw & HWRA & Hww & Hnv & Hn & HN0 & HAOK & HRY & HFL & HERR & HEV & HWHI).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & HPerm & VFL & VSH & VSV & VREP & VSZ).
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & _).
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R22 & R24 & R25 & R20 & R26 & R27).
assert (HSTK : CHECK_REPLY_STK = 12464) by reflexivity.
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HARc Hfin) as (HFal & _ & _ & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HARc Hfin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in HFceil, HFapp.
set (F := frame_addr lyc 1 pos) in *.
unfold c_sp in *. set (sp0 := spZ (c_regs v)) in *.
assert (Esp : c_sp v = sp0) by reflexivity.
assert (Hsp0 : alloc_ceiling + 12464 <= sp0 <= 2 ^ 47) by lia.
assert (Hs1 : sp1_of sp0 = sp0 - 128 - sp0 mod 32 /\ (sp0 mod 32 = 0 \/ sp0 mod 32 = 16)).
{ unfold sp1_of. replace ((sp0 - 128) mod 32) with (sp0 mod 32)
    by (rewrite Zminus_mod; change (128 mod 32) with 0; rewrite Z.sub_0_r, Z.mod_mod by lia; reflexivity).
  split; [reflexivity|]. pose proof (Z.mod_pos_bound sp0 32 ltac:(lia)).
  pose proof (Z.div_mod sp0 32 ltac:(lia)). pose proof (Z.div_mod sp0 16 ltac:(lia)). lia. }
destruct Hs1 as [Hs1 Hs2].
assert (Hsp1 : alloc_ceiling + 12320 <= sp1_of sp0 /\ sp1_of sp0 + 128 <= sp0) by (rewrite Hs1; lia).
assert (Ho16 : (-128 - sp0 mod 32) mod 16 = 0) by (destruct Hs2 as [Em|Em]; rewrite Em; reflexivity).
assert (HFk : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32))
  by (rewrite HFk at 1; replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia; apply Z.div_mul; lia).
assert (HF8e : 8 * (F / 8) = F) by lia.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8lo.
pose proof (Z.div_le_upper_bound F 8 (2 ^ 47) ltac:(lia) ltac:(lia)) as HF8hi.
(* the environment at the seed *)
remember (crM regs1 v lyc pos) as E eqn:HE in HS0.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; unfold crM; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros; rewrite HE; apply crM_reg; assumption).
assert (EX : forall j, (j < 23)%nat -> ew E (32 + j) = nth j (crM_extra v lyc pos) (Z_to_bv 64 0)) by (intros; rewrite HE; apply crM_extra_nth; assumption).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 6%nat ltac:(lia)) as E38.
cbn [Nat.add nth crM_extra map app] in E32, E33, E34, E36, E38. fold F in E36, E38.
assert (U33u : bv_unsigned (ew E 33) = A_G_REC) by (rewrite E33; unfold A_G_REC; apply unsigned_lit_small; lia).
(* g_rec's fields are the only region the runs below read through the symbolic state *)
assert (HS : st_ok_pi SEGS VAL E (mkSS CR_RET_SNP sr_mid [cr_grecm] None cr_facts_mid)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + CR_RET_SNP)) memc (seg_rom SEGS)))).
{ exact (st_ok_pi_submem E (ss_mid CR_RET_SNP false) _ [cr_grecm] HS0
    (submem_drop _ _ _ (submem_keep _ _ _ _ (subregion_refl _) (submem_nil _))) eq_refl). }
clear HS0.
assert (SHOK1 : sh_ok SEGS crBx crSH_mid E (mrestrict (w_H Wc) memc)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H Wc) memc E crBx 33%nat A_G_REC 960 A_G_REC 928 944).
  - exact (cr_grec_addressable B LAWS HB lyc Sc Wc memc mdc A_G_REC 960 HARc ltac:(lia) ltac:(lia)).
  - unfold crBx. rewrite (U_atom E 32 SBc E32) by (unfold SBc; lia). reflexivity.
  - rewrite (U_atom E 33 0x5e3740 E33) by lia. reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold A_G_REC, SHADOW_OFF in *. lia. }
unfold cr_at.
(* 0x86f9c .. 0x86fa0: a0 = code, then the call of rec_code_declared *)
paj_run_tok RUN HS HJ SHOK1 crSpan.
{ awr_ok_tac. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdw := d) in *; clearbody mdw end.
(* the run wrote nothing: its region is read-only *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha.
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ memc) (mrestrict _ (ms_mem ms)) |- _ =>
  apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFx);
  [ intros b wlo whi x Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
  | exact Ha | intros [] ] end. }
(* the entry's saved registers and the call chain at this state *)
assert (KABOVE : forall a, sp0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW (c_W v) (c_mem v) a).
{ intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _). apply G1; [lia | lia | apply inFP_nil]. }
assert (VSV2 : forall j r, nth_error cr_saved_regs j = Some r ->
  val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr (c_regs v) (Z_to_bv 5 r)))).
{ intros j r Hjr.
  assert (Hj : (j < 12)%nat)
    by (change 12%nat with (length cr_saved_regs); apply (proj1 (nth_error_Some cr_saved_regs j));
        rewrite Hjr; discriminate).
  apply (s4_val_keep Wc Wc memc (ms_mem ms)); [|exact (VSV j r Hjr)].
  intros x Hx. apply KEEP2. lia. }
assert (Rra : rdword (rdW Wc (ms_mem ms)) (sp0 - 8) = Some (raZ (c_regs v))).
{ apply (rdword_of_val_mem SEGS (w_H Wc) (ms_mem ms)).
  - replace (sp0 - 8) with (sp0 - 8 - 8 * Z.of_nat 0) by lia.
    pose proof (VSV2 0%nat 1 eq_refl) as Hv.
    replace (Z_to_bv 5 1) with (1%bv : bv 5) in Hv by (apply bv_eq; reflexivity). exact Hv.
  - unfold raZ. pose proof (bv_unsigned_in_range 64 (getr (c_regs v) 1)).
    change (bv_modulus 64) with (2 ^ 64) in *. lia. }
assert (Rs0 : rdword (rdW Wc (ms_mem ms)) (sp0 - 16) = Some (s0Z (c_regs v))).
{ apply (rdword_of_val_mem SEGS (w_H Wc) (ms_mem ms)).
  - replace (sp0 - 16) with (sp0 - 8 - 8 * Z.of_nat 1) by lia.
    pose proof (VSV2 1%nat 8 eq_refl) as Hv.
    replace (Z_to_bv 5 8) with (8%bv : bv 5) in Hv by (apply bv_eq; reflexivity). exact Hv.
  - unfold s0Z. pose proof (bv_unsigned_in_range 64 (getr (c_regs v) 8)).
    change (bv_modulus 64) with (2 ^ 64) in *. lia. }
assert (Etop : ly_top lyc = ly_top (c_ly v))
  by (pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _); exact Et).
assert (Hm8 : sp0 mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 16); [exists 2; reflexivity|].
  apply Z.mod_divide; [lia | exact Hal16]. }
assert (HCHex : exists ch1, achain lyc (rdW Wc (ms_mem ms)) (sp0 + (-128 - sp0 mod 32)) sp0 ch1).
{ destruct (Z_lt_le_dec sp0 (ly_top lyc - 16)) as [Hlt | Hge].
  - exists ((sp0, raZ (c_regs v), s0Z (c_regs v)) :: c_ch v).
    apply (achain_push lyc (rdW (c_W v) (c_mem v)) (rdW Wc (ms_mem ms)) sp0 (s0Z (c_regs v)) (raZ (c_regs v)) (c_ch v)).
    + apply (achain_ly_top (c_ly v) lyc); [exact Etop | exact Hch].
    + rewrite Etop. lia.
    + intros a Ha. apply KABOVE. lia.
    + exact Rra.
    + exact Rs0.
    + exact Hra4.
    + lia.
    + exact Hm8.
    + exact Hlt.
    + lia.
  - exists []. left. split; [right; left; exact Hge | reflexivity]. }
destruct HCHex as (ch1 & HCH).
pose proof pa_base_lo as HBLO.
assert (HARm2 : AR SEGS B lyc Sc Wc (ms_mem ms) mdw) by exact (proj1 HJ).
assert (HROm2 : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms)))
  by (eapply (arodata_ok_journalP SEGS RLO RHI RELRO_IMG B); [exact HJ | intros a _; apply inFP_nil | exact HROD]).
assert (HROKm2 : cmd_ro_ok (rdW Wc (ms_mem ms))) by exact (CMD_RO_AT _ _ _ _ _ HARm2 HROm2).
assert (HEVb : st_nev Sc + EV_REC_CODE_DECLARED <= EV_MAX).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
  unfold EV_REC_CODE_DECLARED in *. unfold EV_CHECK_REPLY in HEV. lia. }
pmkst HS.
prreg HS (1%bv : bv 5) G1'. prreg HS (2%bv : bv 5) G2'. prreg HS (3%bv : bv 5) G3'.
prreg HS (4%bv : bv 5) G4'. prreg HS (8%bv : bv 5) G8'. prreg HS (10%bv : bv 5) G10'.
assert (Tsp2 : spZ (ms_regs ms) = sp0 + (-128 - sp0 mod 32)).
{ unfold spZ. rewrite G2', (EE 2%nat 2%bv eq_refl), R2.
  unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Gs0 : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite G8', (EE 8%nat 8%bv eq_refl), R8.
  unfold w64. apply unsigned_lit_small. lia. }
assert (Ga0 : getr (ms_regs ms) 10 = w64 (c_code v))
  by (rewrite G10', (EE 21%nat 21%bv eq_refl); exact R21).
assert (Ggp : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (rewrite G3', (EE 3%nat 3%bv eq_refl); exact R3).
assert (Gtp : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (rewrite G4', (EE 4%nat 4%bv eq_refl); exact R4).
assert (SIGP_rcd : SIGMA CS_rec_code_declared = BASE + AF_rec_code_declared)
  by (rewrite (SIGP CS_rec_code_declared) by (unfold cmd_prog_syms; repeat (first [left; reflexivity | right]));
      reflexivity).
rewrite SIGP_rcd.
(* 0x86fa0: rec_code_declared(code) *)
eapply SRr_bind.
{ apply (cl_callS B LAWS Wc (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_rec_code_declared))
    CHECK_REPLY_STK sp0 [] (c_ly v) (c_S v) (c_W v) (c_mem v) (c_md v) [(1, pos)] lyc Sc mdw 0
    REC_CODE_DECLARED_STK [] EV_REC_CODE_DECLARED (-128 - sp0 mod 32) (Z_to_bv 64 (BASE + CR_RET_RCD)) ch1
    (fun ly3 S3 W3 regs3 mem3 md3 => getr regs3 10 = w64 (if declared (c_code v) then 1 else 0) /\
       Permutation (ablocks B ly3 S3) (ablocks B lyc Sc) /\ ly3 = lyc /\ S3 = Sc)
    HJ Tsp2 Ho16 ltac:(lia) ltac:(unfold REC_CODE_DECLARED_STK; lia)
    ltac:(rewrite HSTK; unfold REC_CODE_DECLARED_STK; lia) Ggp Gtp G1'
    ltac:(apply ret_ok_codeptr_v; [unfold CR_RET_RCD; lia | reflexivity])
    ltac:(unfold CR_RET_RCD; rewrite unsigned_lit_small by lia; lia)).
  - rewrite Gs0. exact HCH.
  - intros HPRE1. eapply SRr_mono.
    + apply (RCD fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw (c_code v) ltac:(eapply afn_pre_na_of; exact HPRE1) HROm2 Ga0
        (s4_code_range (c_xr v)) HROKm2 HVO HEVb).
    + cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & Hc3 & HJc & HPr & HK).
      exists ly3, S3, regs3, mem3, md3. split; [rewrite Hc3, G1'; reflexivity|].
      split; [exact HJc|]. split; [exact HPr | exact HK].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc & HP3 & (Hdecl & Hperm3 & Ely3 & ES3)).
(* the code is declared, so the abort branch at 0x86fa4 is not taken *)
destruct HRY as (HRYn & _). destruct (HRYn Hneg) as (HDEC & HXR).
unfold c_code in Hdecl. rewrite HDEC in Hdecl.
(* back at 0x86fa4 with g_rec's fields kept *)
jafter_call_keep_pi HS 55%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS4.
lazymatch type of HS4 with ?t -> _ => assert (HRK2 : t); [|specialize (HS4 HRK2); clear HRK2] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
  rewrite U33u; intros a Ha; [|lia].
  apply (mbyte_of_aview SEGS).
  apply (aj_img_PG B LAWS HB IMG _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc).
  exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold A_G_REC in *; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS4.
set (E2 := havoc E 55 (map (getr regs3) CLOB)) in *.
assert (HEIb : img_env VAL A_LIM E2)
  by (unfold E2; apply img_env_havoc; [exact HEI | rewrite length_map; cbv; lia]).
assert (EH2 : forall nn, (nn < 55)%nat -> ew E2 nn = ew E nn) by (intros nn Hnn; unfold E2; apply ew_havoc_old; lia).
assert (A59 : ew E2 59 = getr regs3 10).
{ unfold E2. change 59%nat with (55 + 4)%nat.
  rewrite (ew_havoc_new E 55 _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbv; lia).
  cbn [nth map CLOB]. reflexivity. }
assert (SHOK2 : sh_ok SEGS crBx crSH_mid E2 (mrestrict (w_H W3) mem3)).
{ apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W3) mem3 E2 crBx 33%nat A_G_REC 960 A_G_REC 928 944).
  - exact (cr_grec_addressable B LAWS HB ly3 S3 W3 mem3 md3 A_G_REC 960 (proj1 HJ3) ltac:(lia) ltac:(lia)).
  - unfold crBx.
    rewrite (U_atom E2 32 SBc ltac:(rewrite EH2 by lia; exact E32)) by (unfold SBc; lia).
    reflexivity.
  - rewrite (U_atom E2 33 0x5e3740 ltac:(rewrite EH2 by lia; exact E33)) by lia. reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold A_G_REC, SHADOW_OFF in *. lia. }
psrr_branch_tok RUN BR HS4 SHOK2 crSpan.
- exfalso. rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. unfold U in Hc. apply bv_eq in Hc.
  cbn [sv_denot] in Hc. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc. rewrite A59, Hdecl in Hc.
  apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate.
- (* 0x86fa8 .. 0x86fb4: the inline check of g_rec.reply, the load of the reply and of the refusal *)
  paj_run_to_tok RUNTO HS4 HJ3 SHOK2 crSpan CR_STRCMP.
  { awr_ok_tac. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdx := d) in *; clearbody mdx end.
  (* the memory the callee and the runs kept *)
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> rdW W3 (ms_mem ms0) a = rdW W3 mem3 a).
  { intros a Ha.
    lazymatch goal with HFx : frame_of _ _ (mrestrict _ mem3) (mrestrict _ (ms_mem ms0)) |- _ =>
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFx);
    [ intros b wlo whi x Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
    | exact Ha | intros [] ] end. }
  assert (KFR : forall a, F <= a < F + 128 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 16 ->
    rdW W3 (ms_mem ms0) a = rdW Wc (ms_mem ms) a).
  { intros a Ha. rewrite (KEEP3 a ltac:(unfold SHADOW_OFF in *; lia)).
    pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G4 & _).
    apply (G4 1 pos a Hfin); [|apply inFP_nil].
    destruct Ha as [Ha | Ha]; [left | right]; unfold in_zr, frame_rng, shadow_addr; cbn [fst snd];
    change (fs_frame_bytes 1) with 128; change (128 / 8) with 16; fold F; unfold SHADOW_OFF in *; lia. }
  assert (KST : forall a, alloc_ceiling <= a < 2 ^ 64 ->
    ~ (sp0 + (-128 - sp0 mod 32) - REC_CODE_DECLARED_STK <= a < sp0 + (-128 - sp0 mod 32)) ->
    rdW W3 (ms_mem ms0) a = rdW Wc (ms_mem ms) a).
  { intros a Ha Hs. rewrite (KEEP3 a ltac:(lia)).
    pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
    apply G1; [lia | exact Hs | apply inFP_nil]. }
  assert (KPG : forall a, inFP cmd_PG a -> rdW W3 (ms_mem ms0) a = rdW Wc memc a).
  { intros a Ha.
    rewrite (aj_img_PG B LAWS HB IMG _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 a Ha).
    symmetry. exact (aj_img_PG B LAWS HB IMG _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 MID) a Ha). }
  (* the layout of the frame is the entry's *)
  assert (EFF : ly_F ly3 = ly_F lyc).
  { pose proof HJ3 as (_ & Hly3 & _). pose proof Hly3 as (_ & _ & _ & _ & _ & E3 & _).
    pose proof Hly as (_ & _ & _ & _ & _ & Ec & _). rewrite E3, Ec. reflexivity. }
  assert (EF3 : frame_addr ly3 1 pos = F) by (unfold F, frame_addr; rewrite EFF; reflexivity).
  assert (EFL3 : flag_addr ly3 1 pos = flag_addr lyc 1 pos) by (unfold flag_addr; rewrite EFF; reflexivity).
  (* the mid-walk invariant at the state before the strcmp call *)
  assert (MID3 : cr_mid B v ly3 S3 W3 (ms_mem ms0) mdx pos).
  { split; [change (0 + EV_REC_CODE_DECLARED) with 0 in HJ3; exact HJ3|].
    split; [apply (Permutation_trans Hperm3 HPerm)|].
    rewrite EF3, EFL3. split.
    { apply (s4_val_keep Wc W3 (ms_mem ms) (ms_mem ms0)); [intros x Hx; apply KFR; left; lia|].
      apply (s4_val_keep Wc Wc memc (ms_mem ms)); [|exact VFL].
      intros x Hx. apply KEEP2. lia. }
    split.
    { intros i Hi.
      apply (s4_val_keep Wc W3 (ms_mem ms) (ms_mem ms0)); [intros x Hx; apply KFR; right; lia|].
      apply (s4_val_keep Wc Wc memc (ms_mem ms)); [|exact (VSH i Hi)].
      intros x Hx. apply KEEP2. unfold SHADOW_OFF in *; lia. }
    split.
    { intros j r Hjr.
      assert (Hj : (j < 12)%nat)
        by (change 12%nat with (length cr_saved_regs); apply (proj1 (nth_error_Some cr_saved_regs j));
            rewrite Hjr; discriminate).
      apply (s4_val_keep Wc W3 (ms_mem ms) (ms_mem ms0)); [|exact (VSV2 j r Hjr)].
      intros x Hx. rewrite Esp in Hx. apply KST; [lia | unfold REC_CODE_DECLARED_STK; lia]. }
    split.
    { apply (s4_val_keep Wc W3 memc (ms_mem ms0)); [|exact VREP].
      intros x Hx. apply KPG. exists (A_G_REC, A_G_REC + 960).
      split; [left; reflexivity | cbn [fst snd]; unfold OFF_REPLY in *; lia]. }
    { apply (s4_val_keep Wc W3 memc (ms_mem ms0)); [|exact VSZ].
      intros x Hx. apply KPG. exists (A_G_REC, A_G_REC + 960).
      split; [left; reflexivity | cbn [fst snd]; unfold OFF_REPLY_SIZE in *; lia]. } }
  (* the refusal text the snprintf wrapper wrote *)
  assert (HTXT3 : abytes_atR (rdW W3 (ms_mem ms0)) (frame_addr ly3 1 pos + 32)
    (refusal_text (c_code v) ++ [Z_to_bv 8 0])).
  { rewrite EF3. apply (s4_bytes_keep Wc W3 (ms_mem ms) (ms_mem ms0)).
    - intros x Hx. apply KFR. left.
      pose proof (s4_text_len (c_code v)) as Hlt.
      rewrite (s4_refusal_len (c_code v)) in Hx. lia.
    - apply (s4_bytes_keep Wc Wc memc (ms_mem ms)); [|exact HTXT].
      intros x Hx. rewrite (s4_refusal_len (c_code v)) in Hx.
      pose proof (s4_text_len (c_code v)). apply KEEP2. lia. }
  pmkst HS4.
  prreg HS4 (2%bv : bv 5) K2. prreg HS4 (3%bv : bv 5) K3. prreg HS4 (4%bv : bv 5) K4.
  prreg HS4 (8%bv : bv 5) K8. prreg HS4 (9%bv : bv 5) K9. prreg HS4 (10%bv : bv 5) K10.
  prreg HS4 (11%bv : bv 5) K11. prreg HS4 (18%bv : bv 5) K18. prreg HS4 (19%bv : bv 5) K19.
  prreg HS4 (20%bv : bv 5) K20. prreg HS4 (21%bv : bv 5) K21. prreg HS4 (22%bv : bv 5) K22.
  prreg HS4 (23%bv : bv 5) K23. prreg HS4 (24%bv : bv 5) K24. prreg HS4 (25%bv : bv 5) K25.
  prreg HS4 (27%bv : bv 5) K27.
  assert (KK : forall nn (r : bv 5), (nn < 55)%nat -> Z.of_nat nn = bv_unsigned r -> ew E2 nn = getr regs1 r)
    by (intros nn r Hnn Hr; rewrite (EH2 nn ltac:(lia)); exact (EE nn r Hr)).
  assert (F32 : ew E2 32 = Z_to_bv 64 SBc) by (rewrite (EH2 32%nat ltac:(lia)); exact E32).
  assert (F33 : ew E2 33 = Z_to_bv 64 0x5e3740) by (rewrite (EH2 33%nat ltac:(lia)); exact E33).
  assert (F34 : ew E2 34 = Z_to_bv 64 (c_p v)) by (rewrite (EH2 34%nat ltac:(lia)); exact E34).
  assert (F36 : ew E2 36 = Z_to_bv 64 F) by (rewrite (EH2 36%nat ltac:(lia)); exact E36).
  assert (F38 : ew E2 38 = Z_to_bv 64 (SBc + F / 8)) by (rewrite (EH2 38%nat ltac:(lia)); exact E38).
  assert (K26 : getr (ms_regs ms0) 26 = w64 (SHADOW_OFF + (A_G_REC + OFF_REPLY) / 8)).
  { rewrite (st_ok_pi_restrict_reg (w_H W3) E2 _ _ (26%bv : bv 5) HS4).
    lazymatch goal with |- sv_denot _ (sr_get ?a ?rr) = _ =>
      let e := eval vm_compute in (sr_get a rr) in change (sr_get a rr) with e end.
    cbn [ms_regs restrict]. apply denot_s10; [exact F33 | exact F32]. }
  assert (RA3 : cr_regs_at B v ly3 pos (ms_regs ms0)).
  { unfold cr_regs_at. cbv zeta. rewrite EF3.
    split; [rewrite K2, (KK 2%nat 2%bv ltac:(lia) eq_refl); exact R2|].
    split; [rewrite K3, (KK 3%nat 3%bv ltac:(lia) eq_refl); exact R3|].
    split; [rewrite K4, (KK 4%nat 4%bv ltac:(lia) eq_refl); exact R4|].
    split; [rewrite K8, (KK 8%nat 8%bv ltac:(lia) eq_refl); exact R8|].
    split; [rewrite K9, (KK 2%nat 2%bv ltac:(lia) eq_refl); exact R2|].
    split; [rewrite K18, F36; reflexivity|].
    split; [rewrite K23, F36; reflexivity|].
    split; [rewrite K22, F38, SBc_SHADOW_OFF; reflexivity|].
    split; [rewrite K24, F32, SBc_SHADOW_OFF; reflexivity|].
    split; [rewrite K25, F33; reflexivity|].
    split; [rewrite K20, F33, unsigned_lit_small by lia; reflexivity|].
    split; [exact K26 | rewrite K27, (KK 27%nat 27%bv ltac:(lia) eq_refl); exact R27]. }
  assert (N19 : getr (ms_regs ms0) 19 = w64 (frame_addr ly3 1 pos + 32))
    by (rewrite EF3, K19, (KK 19%nat 19%bv ltac:(lia) eq_refl); exact R19).
  assert (N21 : getr (ms_regs ms0) 21 = w64 (c_code v))
    by (rewrite K21, (KK 21%nat 21%bv ltac:(lia) eq_refl); exact R21).
  assert (N10 : getr (ms_regs ms0) 10 = w64 (c_p v)) by (rewrite K10, F34; reflexivity).
  assert (N11 : getr (ms_regs ms0) 11 = w64 (frame_addr ly3 1 pos + 32))
    by (rewrite EF3, K11, (KK 19%nat 19%bv ltac:(lia) eq_refl); exact R19).
  exact (STRCMP v ly3 S3 W3 (ms_regs ms0) (ms_mem ms0) mdx pos CX MID3 RA3 Hneg N19 N21 N10 N11 HTXT3
    ltac:(rewrite Ely3, ES3; exact LS)).
Qed.
End e.
End f.
End d.
