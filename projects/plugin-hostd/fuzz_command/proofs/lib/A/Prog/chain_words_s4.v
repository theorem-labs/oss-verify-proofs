(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S4 of the walk of chain_words (0x8dfd4) on the ASan build of
   plugin-hostd/fuzz_command (interface chain_words_d.v): from the cut KD (0x8e264, every word parsed) through
   `lw a0,20(s1); addiw a2,s4,-2; mv a1,s6; jal sup_chain` (0x8e270, through cl_callS_wideF, PaFx.v: sup_chain's
   post is apost_baseF, so the call returns at some FP state fx1) and `j 0x8e280` (0x8e274) to the join KJ
   (0x8e280), taken at fx1. The jump runs at fx1, so it is the lemma cw4_jump of a section closed before cw_S4.
   The member array ids[0..ntok-2) is in this walk's own class-3
   frame (sup_chain's afobj arm); sup_chain writes g_rec, record.spill and the recorder's blocks, the walk's own
   footprint cw_FP. The helpers it shares with segment S5 are in chain_words_s5.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaSB PaCall PaCallRun PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import xstrdup_c arg_i_c hand_back_c answer_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import number_c sup_chain_c sup_resp_c chain_words_c chain_words_d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import chain_words_s5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Lemma cw4_val_mem_mod32 : forall (m : word -> option byte) a v, val_mem SEGS m a 4 v -> val_mem SEGS m a 4 (v mod 2 ^ 32).
Proof.
intros m a v Hv k Hk. rewrite (Hv k Hk). unfold YG0f.le_byte, YO0f.le_byte.
assert (E4 : 2 ^ (8 * Z.of_nat 4) = 2 ^ 32) by reflexivity. rewrite E4, Z.mod_mod by lia. reflexivity.
Qed.
(* lw of the 32-bit cell number wrote: the cell holds id mod 2^32, the load sign-extends it back to id *)
Lemma cw4_sext_mod : forall z, -2 ^ 31 <= z < 2 ^ 31 ->
  sext 64 (bv_extract 0 32 (Z_to_bv 64 (z mod 2 ^ 32))) = Z_to_bv 64 z.
Proof.
intros z Hz. rewrite <- (sext32_small z Hz).
change (bv_extract 0 32 (Z_to_bv 64 (z mod 2 ^ 32))) with (low32 (Z_to_bv 64 (z mod 2 ^ 32))).
change (bv_extract 0 32 (Z_to_bv 64 z)) with (low32 (Z_to_bv 64 z)).
rewrite !low32_lit. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). apply Z.mod_mod. lia.
Qed.
(* addiw a2,s4,-2 with s4 = ntok *)
Lemma cw4_addiw : forall n, 3 <= n <= 64 ->
  sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 n)) (low32 (Z_to_bv 64 (-2)))) = Z_to_bv 64 (n - 2).
Proof.
intros n Hn. rewrite zalu32_sound. unfold zalu32. rewrite Z_to_bv64_canon. f_equal.
cbn [zalu_raw]. unfold zu32, M32.
rewrite (Z.mod_small n (2 ^ 32)) by lia.
replace ((-2) mod 2 ^ 32) with (2 ^ 32 - 2) by reflexivity.
replace (n + (2 ^ 32 - 2)) with ((n - 2) + 1 * bv_modulus 32) by (change (bv_modulus 32) with (2 ^ 32); lia).
rewrite swrap_add_mod. apply swrap32_id. lia.
Qed.
(* the model's member list: one value per word, each a parsed number *)
Lemma cw4_numbers_m : forall ws vs, Verbs.numbers_m ws = Some vs ->
  length vs = length ws /\ Forall (fun v => -1000000 <= v <= 1000000) vs.
Proof.
induction ws as [|w ws IH]; intros vs H; cbn [Verbs.numbers_m] in H.
- injection H as <-. split; [reflexivity | constructor].
- destruct (Verbs.number_m w) as [v|] eqn:Ew; [|discriminate].
  destruct (Verbs.numbers_m ws) as [vs'|] eqn:Ews; [|discriminate].
  injection H as <-. destruct (IH vs' eq_refl) as [HL HF].
  split; [cbn [length]; rewrite HL; reflexivity | constructor; [exact (Verbs.number_m_range _ _ Ew) | exact HF]].
Qed.
(* the lengths behind LIVE_SUP_CHAIN and XM_SUP_CHAIN: the member list text, and the reply text sup_chain hands
   back (the shape "chain" declares, or resp of a declared refusal code) *)
Lemma cw4_concat_sp_length : forall r, Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) r ->
  (length (concat (map (fun j => SPACE :: dec j) r)) <= 12 * length r)%nat.
Proof.
induction r as [|j r IH]; intros HF; [cbn; lia|].
pose proof (Forall_inv HF) as Hj. pose proof (Forall_inv_tail HF) as Hr.
cbn [map concat]. rewrite length_app. cbn [length].
pose proof (dec_length j Hj). specialize (IH Hr). lia.
Qed.
Lemma cw4_dec_list_length : forall ids, Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids ->
  (length (dec_list ids) <= 12 * length ids)%nat.
Proof.
intros [|i r] HF; [cbn; lia|].
pose proof (Forall_inv HF) as Hi. pose proof (Forall_inv_tail HF) as Hr.
unfold dec_list. rewrite length_app. pose proof (dec_length i Hi). pose proof (cw4_concat_sp_length r Hr).
cbn [length]. lia.
Qed.
Lemma cw4_rec_record_rc : forall R fn A, r_refuse (rec_record R fn A) = r_refuse R /\ r_code (rec_record R fn A) = r_code R.
Proof. intros R fn A. unfold rec_record. destruct (Nat.ltb _ 16); split; reflexivity. Qed.
Lemma cw4_text_len : forall R id ids, (r_refuse R <> 0 -> declared (r_code R) = true) ->
  (length (snd (sup_chain_m R id ids)) <= 64)%nat.
Proof.
intros R id ids HR. unfold sup_chain_m, rec_stub, rec_answer.
rewrite (proj1 (cw4_rec_record_rc _ _ _)), (proj2 (cw4_rec_record_rc _ _ _)).
destruct (Z.eqb_spec (r_refuse R) 0) as [H0 | H0]; cbn [snd hand_back].
- apply Nat.leb_le. vm_compute. reflexivity.
- pose proof (declared_range _ (HR H0)) as Hc. pose proof (resp_length (r_code R) ltac:(lia)). lia.
Qed.
(* the live-byte bound: LIVE_SUP_CHAIN (sup_chain_c.v:64-66) within LIVE_CHAIN_WORDS (chain_words_c.v:68-70) *)
Lemma cw4_live : forall R id ids, -2 ^ 31 <= id < 2 ^ 31 -> Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids ->
  (length ids <= 62)%nat -> (r_refuse R <> 0 -> declared (r_code R) = true) ->
  LIVE_SUP_CHAIN R id ids <= LIVE_CHAIN_WORDS.
Proof.
intros R id ids Hid HF Hl HR.
pose proof (cw4_text_len R id ids HR) as Ht.
pose proof (dec_length id Hid) as Hd1.
pose proof (dec_length (Z.of_nat (length ids)) ltac:(lia)) as Hd2.
pose proof (cw4_dec_list_length ids HF) as Hd3.
unfold LIVE_SUP_CHAIN, LIVE_ARG_I, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP, LIVE_CHAIN_WORDS, CHAIN_WORDS_MALLOCS,
  CHAIN_WORDS_REQ.
lia.
Qed.
Lemma cw4_ev : forall R, 0 <= EV_SUP_CHAIN R <= EV_CHAIN_WORDS R.
Proof.
intros R. assert (H : 0 <= rec_spill_frees R) by (unfold rec_spill_frees; destruct (Nat.ltb _ 16); lia).
unfold EV_CHAIN_WORDS, EV_SUP_CHAIN, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_SUP_RESP, EV_XSTRDUP. lia.
Qed.
(* the meter: sup_chain's six mallocs of at most 8194 bytes, and its frees within EV_CHAIN_WORDS *)
Lemma cw4_xm : forall MT, ameter_laws MT -> forall R id ids, -2 ^ 31 <= id < 2 ^ 31 ->
  Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids -> (1 <= length ids <= 62)%nat ->
  (r_refuse R <> 0 -> declared (r_code R) = true) ->
  0 + XM_SUP_CHAIN MT R id ids <= XM_CHAIN_WORDS MT R.
Proof.
intros MT MTL R id ids Hid HF Hl HR.
pose proof (cw4_text_len R id ids HR) as Ht.
pose proof (dec_length id Hid) as Hd1.
pose proof (dec_length (Z.of_nat (length ids)) ltac:(lia)) as Hd2.
pose proof (cw4_dec_list_length ids HF) as Hd3.
pose proof (mo_malloc_mono MT MTL (12 * Z.of_nat (length ids) + 1) 8194 ltac:(lia)) as M1.
pose proof (mo_malloc_mono MT MTL (Z.of_nat (length (dec id)) + 1) 8194 ltac:(lia)) as M2.
pose proof (mo_malloc_mono MT MTL (Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1) 8194 ltac:(lia)) as M3.
pose proof (mo_malloc_mono MT MTL (Z.of_nat (length (dec_list ids)) + 1) 8194 ltac:(lia)) as M4.
pose proof (mo_malloc_mono MT MTL (Z.of_nat (length (snd (sup_chain_m R id ids))) + 1) 8194 ltac:(lia)) as M5.
pose proof (mo_free_nonneg MT MTL) as F.
pose proof (cw4_ev R) as HE.
assert (HE2 : rec_spill_frees R + 2 <= EV_CHAIN_WORDS R)
  by (unfold EV_CHAIN_WORDS, EV_SUP_CHAIN, EV_ARG_I, EV_ANSWER, EV_HAND_BACK, EV_SUP_RESP, EV_XSTRDUP in *; lia).
pose proof (Z.mul_le_mono_nonneg_r _ _ _ F HE2) as HM.
unfold XM_SUP_CHAIN, XM_ARG_I, XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP, XM_CHAIN_WORDS, CHAIN_WORDS_MALLOCS, CHAIN_WORDS_REQ.
lia.
Qed.
(* the shadow of ids[0..62): the cells frame/8 + 4 .. frame/8 + 36 *)
Lemma cw4_idx_bounds : forall d, 32 <= d < 288 -> 4 <= d / 8 < 36.
Proof. intros d Hd. split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia]. Qed.
Lemma cw4_sh_idx : forall F x, F mod 8 = 0 -> SHADOW_OFF + x / 8 = SB + F / 8 + (x - F) / 8.
Proof.
intros F x HF. rewrite <- SB_SHADOW_OFF.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF, Z.add_0_r in DF.
replace x with ((x - F) + (F / 8) * 8) at 1 by lia.
rewrite Z.div_add by lia. lia.
Qed.
(* the recorder statics of the walk's footprint are g_rec and record.spill, two of the program's statics *)
Lemma cw4_pg_cases : forall a, inFP CHAIN_WORDS_PG a ->
  (A_G_REC <= a < A_G_REC + 960) \/ (A_REC_SPILL <= a < A_REC_SPILL + 56).
Proof.
intros a Ha. unfold CHAIN_WORDS_PG, REC_SIZE, SC_SIZE in Ha.
apply inFP_cons in Ha as [Ha | Ha]; [left; exact Ha|].
apply inFP_cons in Ha as [Ha | Ha]; [right; exact Ha | destruct (inFP_nil a Ha)].
Qed.
Lemma cw4_pg_cmd : forall a, inFP CHAIN_WORDS_PG a -> inFP cmd_PG a.
Proof.
intros a Ha. apply cw4_pg_cases in Ha. unfold cmd_PG. destruct Ha as [Ha | Ha].
- apply inFP_cons. left. exact Ha.
- apply inFP_cons. right. apply inFP_cons. left. exact Ha.
Qed.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
(* the jump 0x8e274 `j 0x8e280` from sup_chain's return to the join KJ, at the ambient FP state: the cut facts
   carried over the run (the frame part through the registers it keeps, the post through the bytes it keeps) *)
Lemma cw4_jump : forall c ly4 S4 W4 regs4 mem4 md4,
  from_KJ B MT c -> INV_KJ B MT c ly4 S4 W4 regs4 mem4 md4 ->
  SRr SEGS W4 (mkCfg (mkst regs4 (Z_to_bv 64 (BASE + 32144)) mem4 (seg_rom SEGS)) md4) (cw_postB B MT c).
Proof.
intros c ly4 S4 W4 regs4 mem4 md4 HKJ (k & Hk & HFI4 & HQ4).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HFI4 as [HJ4 Hsp4 Hgp4 Htp4 Hs04 Hs14 Hs24 Hs34 Hs84 Hsaved4 Hflag4].
set (E5 := Eimg (Ereg regs4 [])).
assert (HEI5 : img_env VAL A_LIM E5) by (subst E5; apply Eimg_env).
assert (EE5 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E5 n = getr regs4 r)
  by (intros n r Hn; subst E5; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS5 : st_ok_pi SEGS VAL E5 (mkSS 32144 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W4) (mkst regs4 (Z_to_bv 64 (BASE + 32144)) mem4 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E5. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
paj_run_to_shc RUNTOP HS5 HJ4 CW_KJ.
{ apply awr_ok_nil. }
set (mdv5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody mdv5. clear mat.
prreg HS5 (2%bv : bv 5) R2. prreg HS5 (3%bv : bv 5) R3. prreg HS5 (4%bv : bv 5) R4. prreg HS5 (8%bv : bv 5) R8.
prreg HS5 (9%bv : bv 5) R9. prreg HS5 (10%bv : bv 5) R10. prreg HS5 (18%bv : bv 5) R18. prreg HS5 (19%bv : bv 5) R19.
prreg HS5 (24%bv : bv 5) R24.
pmkst HS5.
assert (UQ5 : forall a, rdW W4 (ms_mem ms) a = rdW W4 mem4 a)
  by exact (cw5_rd_frame_ro E5 [] (w_H W4) mem4 (ms_mem ms) (Forall_nil _) HFr).
assert (HFI5 : cw_fi B c k ly4 S4 W4 (ms_regs ms) (ms_mem ms) mdv5).
{ constructor.
  - exact HJ4.
  - rewrite R2, (EE5 2%nat 2%bv eq_refl). exact Hsp4.
  - rewrite R3, (EE5 3%nat 3%bv eq_refl). exact Hgp4.
  - rewrite R4, (EE5 4%nat 4%bv eq_refl). exact Htp4.
  - rewrite R8, (EE5 8%nat 8%bv eq_refl). exact Hs04.
  - rewrite R9, (EE5 9%nat 9%bv eq_refl). exact Hs14.
  - rewrite R18, (EE5 18%nat 18%bv eq_refl). exact Hs24.
  - rewrite R19, (EE5 19%nat 19%bv eq_refl). exact Hs34.
  - rewrite R24, (EE5 24%nat 24%bv eq_refl). exact Hs84.
  - intros j r Hj. rewrite (cw5_rdword_same _ _ _ UQ5). exact (Hsaved4 j r Hj).
  - rewrite (cw5_rdword_same _ _ _ UQ5). exact Hflag4. }
change (Z_to_bv 64 (BASE + 32156)) with (w64 (BASE + CW_KJ)).
apply (HKJ ly4 S4 W4 (ms_regs ms) (ms_mem ms) mdv5).
exists k. split; [exact Hk|]. split; [exact HFI5|].
unfold cw_Q in HQ4 |- *. cbv beta in HQ4 |- *.
destruct (VerbsRun.chain_run (x_R c) (tl (x_tks c))) as [R' x].
destruct HQ4 as (O' & p & n & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & REST).
exists O', p, n.
split; [exact (cw5_rec_repA_same B _ _ _ _ _ _ Q1 UQ5)|].
split; [rewrite R10, (EE5 10%nat 10%bv eq_refl); exact Q2|].
split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
split; [apply (cw5_astr_atR_agree _ _ _ _ (Z.of_nat (length x) + 1) Q6); [lia | intros kk _; apply UQ5]|].
split; [exact Q7 | exact REST].
Qed.
End e.
End f.
End d.
Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e2.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis SUP_CHAIN : forall fx0 : YK11.FPState, @tsup_chain_spec fx0 rc SK PI B MT.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis PROG_UNOWNED : cw_prog_unownedP B.
Hypothesis TRANSP : cw_transportP B MT RLO RHI.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
(* sup_chain returns at some FP state fx1 with fxrel fx fx1 (its post is apost_baseF): the jump and the join are
   taken at fx1, and the rest of the walk proves apost_base there, which srr_after_callF_base lifts *)
Lemma cw_S4 : cw_S4P B MT RLO RHI.
Proof.
intros c HFRM HPRE HKJ ly3 S3 W3 regs3 mem3 md3 ((HFI & HUN) & H20 & H22 & Hn3 & (id & vs & Hid & Hvs & Hidm & Hvsm)).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (cw5_stk B MT c HPRE) as (H16 & Hlo & Htop & H47 & Hra4).
destruct (cw_s1_facts c H16) as (H32 & Hs1r).
pose proof (cw5_STK) as HSTK.
pose proof (Verbs.number_m_range _ _ Hid) as Hidr.
pose proof (cp_ntokr _ _ _ _ _ HPRE) as Hntokr.
destruct (cw4_numbers_m _ _ Hvs) as (HLv & HFv).
assert (Hlen : Z.of_nat (length vs) = x_ntok c - 2).
{ rewrite HLv, length_skipn. pose proof (cp_ntok _ _ _ _ _ HPRE). lia. }
assert (HFv32 : Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) vs)
  by (eapply Forall_impl; [|exact HFv]; cbv beta; intros v Hv; lia).
(* the model: ntok >= 3 and every word parsed, so chain_run is sup_chain_m on id and the member values *)
assert (HRUN : VerbsRun.chain_run (x_R c) (tl (x_tks c)) = sup_chain_m (x_R c) id vs).
{ pose proof (cp_ntok _ _ _ _ _ HPRE) as HN. pose proof Hid as Hid'. pose proof Hvs as Hvs'.
  revert Hid' Hvs' HN. generalize (x_tks c) as tks. intros tks Hid' Hvs' HN.
  destruct tks as [|t0 [|t1 [|t2 rest]]]; cbn [length] in HN; try lia.
  cbn [tl nth skipn] in Hid', Hvs' |- *. unfold VerbsRun.chain_run, Verbs.chain_words_m. cbv beta iota.
  rewrite Hid', Hvs'. reflexivity. }
pose proof (cw4_live (x_R c) id vs ltac:(lia) HFv32 ltac:(lia) (cp_refuse _ _ _ _ _ HPRE)) as HLIVE.
pose proof (cw4_xm MT MTL (x_R c) id vs ltac:(lia) HFv32 ltac:(lia) (cp_refuse _ _ _ _ _ HPRE)) as HXM.
pose proof HFI as [HJ Hsp Hgp Htp Hs0 Hs1 Hs2 Hs3 Hs8 Hsaved Hflag].
set (E := Eimg (Ereg regs3 [Z_to_bv 64 (id mod 2 ^ 32)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (id mod 2 ^ 32))
  by (subst E; rewrite ?Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (U9 : bv_unsigned (ew E 9) = cw_s1 c)
  by (rewrite (EE 9%nat 9%bv eq_refl), Hs1; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (HS : st_ok_pi SEGS VAL E
  (mkSS CW_KD sr_atoms [YP09.mkRegion (Some 9%nat) 20 24 0 0 [YP09.mkChunk 20 (CVal 4 (SOff 32 0))]] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + CW_KD)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    pose proof (Z.mod_pos_bound id (2 ^ 32) ltac:(lia)) as Hmb.
    apply (chunk_ok_val SEGS E (mrestrict (w_H W3) mem3) (cw_s1 c) 20 4 (SOff 32 0) (id mod 2 ^ 32)).
    + cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
    + change (Z.of_N 4) with 4. lia.
    + exact (cw4_val_mem_mod32 _ _ _ (val_mem_of_rd32 SEGS (w_H W3) mem3 (cw_s1 c + 20) id Hidm)).
  - cbn. tauto.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
unfold cfg_at. change (w64 (BASE + CW_KD)) with (Z_to_bv 64 (BASE + CW_KD)).
(* 0x8e264 .. 0x8e270: a0 = id (the 32-bit cell number wrote), a2 = ntok - 2, a1 = ids, the call of sup_chain *)
paj_run_shc RUNP RUNC HS HJ.
{ apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
set (mdv := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdv. clear mat.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (24%bv : bv 5) Q24.
pmkst HS.
assert (UQ : forall a, rdW W3 (ms_mem ms) a = rdW W3 mem3 a).
{ refine (cw5_rd_frame_ro E _ (w_H W3) mem3 (ms_mem ms) _ HFr). cbn [ss_mem].
  apply Forall_cons; [cbn; lia | apply Forall_nil]. }
clear HF HFr HG.
(* the cut at the call: the frame part, the caller's objects (TRANSP), the frame chain *)
assert (HFI1 : cw_fi B c 0 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv).
{ constructor.
  - exact HJ.
  - rewrite Q2, (EE 2%nat 2%bv eq_refl). exact Hsp.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - rewrite Q8, (EE 8%nat 8%bv eq_refl). exact Hs0.
  - rewrite Q9, (EE 9%nat 9%bv eq_refl). exact Hs1.
  - rewrite Q18, (EE 18%nat 18%bv eq_refl). exact Hs2.
  - rewrite Q19, (EE 19%nat 19%bv eq_refl). exact Hs3.
  - rewrite Q24, (EE 24%nat 24%bv eq_refl). exact Hs8.
  - intros j r Hj. rewrite (cw5_rdword_same _ _ _ UQ). exact (Hsaved j r Hj).
  - rewrite (cw5_rdword_same _ _ _ UQ). exact Hflag. }
pose proof (cw5_un_same B MT c ly3 S3 W3 mem3 (ms_mem ms) HUN UQ) as HUN1.
destruct (TRANSP c 0 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv HPRE HFI1 HUN1)
  as (_ & _ & _ & HREC & HROD & HRO).
destruct (cw5_achain B MT c 0 ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv HPRE HFI1) as [ch1 Hch1].
pose proof HUN as [U1 U2 U3 Uperm Unev Ubb Umeter Uids].
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfr3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF & _).
assert (EFA : frame_addr ly3 3 (x_fpos c) = cw_F c) by (unfold cw_F, frame_addr; rewrite EF; reflexivity).
assert (Hin3 : In (3, x_fpos c) (frames S3)) by (rewrite Hfr3; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms) mdv 3 (x_fpos c) HAR3 Hin3) as (Hfa0 & Hfac & _).
destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms) mdv 3 (x_fpos c) HAR3 Hin3) as (Hf32 & _).
rewrite EFA in Hfa0, Hfac, Hf32. change (fs_frame_bytes 3) with 512 in Hfac.
assert (Hf8 : cw_F c mod 8 = 0)
  by exact (cw5_mod_of_div (cw_F c) 32 8 ltac:(lia) ltac:(exists 4; reflexivity) ltac:(lia) Hf32).
assert (Hf4 : cw_F c mod 4 = 0)
  by exact (cw5_mod_of_div (cw_F c) 32 4 ltac:(lia) ltac:(exists 8; reflexivity) ltac:(lia) Hf32).
(* the arguments: a0 = id, a1 = ids = frame + 32, a2 = ntok - 2 *)
assert (Q10' : getr (ms_regs ms) 10 = w64 id) by (rewrite Q10, E32; unfold w64; apply cw4_sext_mod; lia).
assert (Q11' : getr (ms_regs ms) 11 = w64 (cw_F c + 32)) by (rewrite Q11, (EE 22%nat 22%bv eq_refl); exact H22).
assert (Q12' : getr (ms_regs ms) 12 = w64 (Z.of_nat (length vs)))
  by (rewrite Q12, (EE 20%nat 20%bv eq_refl), H20, Hlen; unfold w64; apply cw4_addiw; lia).
assert (Qsp : spZ (ms_regs ms) = cw_sp0 c + (cw_s1 c - cw_sp0 c))
  by (unfold spZ; rewrite Q2, (EE 2%nat 2%bv eq_refl), Hsp; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hs0c : s0Z (ms_regs ms) = cw_sp0 c)
  by (unfold s0Z; rewrite Q8, (EE 8%nat 8%bv eq_refl), Hs0; unfold w64; rewrite unsigned_lit_small by lia; lia).
(* the member array: ids[0..ntok-2) in the walk's own class-3 frame, its shadow zero, its bytes the values *)
assert (HRA : range_addressable (rdW W3 (ms_mem ms)) SHADOW_OFF (cw_F c + 32) (4 * Z.of_nat (length vs))).
{ intros x Hx. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr. rewrite UQ, (cw4_sh_idx (cw_F c) x Hf8).
  apply Uids. apply cw4_idx_bounds. lia. }
assert (HAFOBJ : afobj SEGS B ly3 S3 W3 (ms_mem ms) (cw_F c + 32) (4 * Z.of_nat (length vs))).
{ split; [|split; [|exact HRA]].
  - exists 3, (x_fpos c). rewrite EFA. change (fs_frame_bytes 3) with 512.
    split; [exact Hin3|]. split; [lia|]. split; [exact Hf8|]. lia.
  - replace (cw_F c + 32) with (cw_F c + 4 * 8) by lia. rewrite Z_mod_plus_full. exact Hf8. }
assert (HVS3 : abytes_atR (rdW W3 (ms_mem ms)) (cw_F c + 32) (concat (map le32 vs))).
{ apply (cw5_abytes_atR_agree _ _ _ _ (Z.of_nat (length (concat (map le32 vs)))) Hvsm); [lia | intros k _; apply UQ]. }
(* sup_chain's footprint is the walk's: g_rec and record.spill (program statics in the image) and the recorder's
   blocks (live blocks of the cut) *)
assert (HAWR : forall a, inFP (cw_FP c) a ->
  awr_byte SEGS B CHAIN_WORDS_STK (cw_sp0 c) (cw_FP c) (ablocks B (x_ly c) (x_S c)) (ablocks B ly3 S3)
    (frames (x_S c)) ly3 [(3, x_fpos c)] a).
{ intros a Ha. pose proof Ha as Ha'. unfold cw_FP in Ha'. unfold awr_byte, awr_prog_or_caller.
  apply inFP_app in Ha' as [Hg | Hb].
  - right; right; right; right; left. split; [exact Ha|]. split.
    + rewrite (AF0m.ts_prog _ HB). unfold AF0m.TFIB_PROG_STATIC.
      destruct (cw4_pg_cases a Hg) as [Hr | Hr]; unfold A_G_REC, A_REC_SPILL in Hr.
      * apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
      * apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
    + exact (proj1 (PROG_UNOWNED a (cw4_pg_cmd a Hg))).
  - right; left. split; [exact Ha|].
    destruct (inFP_ablocks_fp_inv _ _ Hb) as (p & n & Hpn & Hr).
    exists p, n. split; [exact (cw5_rec_repA_in_blocks B _ _ _ _ _ _ HREC Hpn) | exact Hr]. }
(* the frame's flag word is no byte of that footprint *)
assert (HFPfl : forall a, cw_F c + 504 <= a < cw_F c + 512 -> ~ inFP (cw_FP c) a).
{ intros a Ha Hf. unfold cw_FP in Hf. apply inFP_app in Hf as [Hg | Hb].
  - destruct (PROG_UNOWNED a (cw4_pg_cmd a Hg)) as (Himg & _).
    apply (frm_img SEGS B LAWS ly3 S3 W3 (ms_mem ms) mdv 3 (x_fpos c) a HAR3 Hin3); [|exact Himg].
    rewrite EFA. change (fs_frame_bytes 3) with 512. lia.
  - destruct (inFP_ablocks_fp_inv _ _ Hb) as (p & n & Hpn & Hr).
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms) mdv p n 3 (x_fpos c) HAR3
      (cw5_rec_repA_in_blocks B _ _ _ _ _ _ HREC Hpn) Hin3) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA in Hd. change (fs_frame_bytes 3) with 512 in Hd. lia. }
pose (KC := fun (ly' : alayout) (S' : astate) (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) =>
  exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
  sup_chain_m (x_R c) id vs = (R', t) /\
  getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
  rec_repA B ly' S' (rdW W' mem') R' O' /\
  (forall pn, In pn O' -> In pn (x_O c) \/ ~ In pn (ablocks B ly3 S3)) /\
  In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
  (forall pn, In pn (ablocks B ly3 S3) -> ~ In pn (x_O c) -> pn <> (q, Z.of_nat (length t) + 1)) /\
  ~ In q (map fst O') /\
  astr_atR (rdW W' mem') q t /\
  (forall pn, In pn (ablocks B ly3 S3) -> ~ In pn (x_O c) ->
     In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
  (forall pn, In pn (ablocks B ly' S') ->
     (In pn (ablocks B ly3 S3) /\ ~ In pn (x_O c)) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
  blocks_bytes S' <= blocks_bytes S3 + LIVE_SUP_CHAIN (x_R c) id vs /\
  mo_le MT S3 S' (XM_SUP_CHAIN MT (x_R c) id vs)).
rewrite (proj1 (proj2 (cw_sig_of SIGP))).
unfold cw_post.
eapply srr_after_callF_base.
{ eapply (cl_callS_wideF B LAWS W3 (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_sup_chain)) CHAIN_WORDS_STK (cw_sp0 c)
    (cw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)] ly3 S3 mdv 0 SUP_CHAIN_STK (cw_FP c)
    (EV_SUP_CHAIN (x_R c)) (cw_s1 c - cw_sp0 c) (Z_to_bv 64 (BASE + 32144)) ch1 KC HJ Qsp).
  - exact (cw5_mod_sub (cw_s1 c) (cw_sp0 c) 16 ltac:(lia)
      (cw5_mod_of_div (cw_s1 c) 32 16 ltac:(lia) ltac:(exists 2; reflexivity) ltac:(lia) H32) H16).
  - lia.
  - unfold SUP_CHAIN_STK, SUP_CHAIN_OWN, ESTACK. lia.
  - lia.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - rewrite Hs0c. replace (cw_sp0 c + (cw_s1 c - cw_sp0 c)) with (cw_s1 c) by lia. exact Hch1.
  - intros HPRE1. eapply SRr_mono.
    { apply (SUP_CHAIN fx ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv ch1 id (cw_F c + 32) vs (x_R c) (x_O c) HPRE1).
      - exact HFRM.
      - exact HROD.
      - exact HRO.
      - exact Q10'.
      - lia.
      - exact Q11'.
      - lia.
      - exact Q12'.
      - lia.
      - exact HFv32.
      - lia.
      - replace (cw_F c + 32) with (cw_F c + 8 * 4) by lia. rewrite Z_mod_plus_full. exact Hf4.
      - left. exact HAFOBJ.
      - exact HVS3.
      - exact HREC.
      - rewrite Hfr3, length_app. cbn [length]. pose proof (cp_frames _ _ _ _ _ HPRE). lia.
      - pose proof (cp_nev _ _ _ _ _ HPRE). unfold EV_CHAIN_WORDS in *. lia.
      - pose proof (cp_live _ _ _ _ _ HPRE). lia.
      - apply (mo_ok_step MT MTL (x_S c) S3 0 (XM_SUP_CHAIN MT (x_R c) id vs)); [|exact Umeter].
        exact (mo_ok_le MT MTL _ _ _ (cp_meter _ _ _ _ _ HPRE) HXM). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. rewrite Q1. split; [reflexivity|]. split; [exact Hf1|]. split; [exact Hf2|].
    split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - exact HAWR.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. pose proof (cw5_FP_low B MT c HPRE a Ha). lia. }
cbv beta. intros fx1 ly4 S4 W4 regs4 mem4 md4 Hwle4 Hfx (HJ4 & HJc4 & HP4 & HK4).
pose proof (cw5_fi_call B MT c 0 (EV_SUP_CHAIN (x_R c)) ly3 S3 W3 (ms_regs ms) (ms_mem ms) mdv ly4 S4 W4 regs4 mem4 md4
  SUP_CHAIN_STK (cw_sp0 c + (cw_s1 c - cw_sp0 c)) (cw_FP c) HPRE HFI1 HJ4 HJc4 ltac:(lia)
  (cw5_FP_low B MT c HPRE) HFPfl HP4) as HFI4.
unfold KC in HK4.
destruct HK4 as (R' & t & q & O' & Hsm & Hq10 & Hq64 & Hrec' & HOsub & Hqin & Hfresh & HqO & Hstr & Hkept & Hcls & Hbb & Hmle).
(* 0x8e274: j 0x8e280, at the FP state sup_chain returned *)
apply (cw4_jump (fx := fx1) B MT c ly4 S4 W4 regs4 mem4 md4 (HKJ fx1)).
unfold INV_KJ.
exists (0 + EV_SUP_CHAIN (x_R c)). split; [pose proof (cw4_ev (x_R c)); lia|].
split; [exact HFI4|].
unfold cw_Q. cbv beta. rewrite HRUN, Hsm. cbv beta iota.
exists O', q, (Z.of_nat (length t) + 1).
split; [exact Hrec'|].
split; [exact Hq10|].
split; [exact Hq64|].
split; [exact Hqin|].
split; [intros Hin; apply HqO; exact (in_map fst _ _ Hin)|].
split; [exact Hstr|].
split; [lia|].
split.
{ intros pn Hpn HnO. assert (Hpn3 : In pn (ablocks B ly3 S3)) by (eapply Permutation_in; [exact (Permutation_sym Uperm) | exact Hpn]).
  exact (proj2 (Hkept pn Hpn3 HnO)). }
split.
{ intros pn Hpn HnO. assert (Hpn3 : In pn (ablocks B ly3 S3)) by (eapply Permutation_in; [exact (Permutation_sym Uperm) | exact Hpn]).
  exact (proj1 (Hkept pn Hpn3 HnO)). }
split.
{ intros pn Hpn. destruct (Hcls pn Hpn) as [[H1 H2] | [H1 | H1]].
  - left. split; [eapply Permutation_in; [exact Uperm | exact H1] | exact H2].
  - right; left; exact H1.
  - right; right; exact H1. }
split.
{ intros pn Hpn. destruct (HOsub pn Hpn) as [H1 | H1]; [left; exact H1|].
  right. intros H2. apply H1. eapply Permutation_in; [exact (Permutation_sym Uperm) | exact H2]. }
split; [lia|].
apply (mo_le_mono MT MTL _ _ _ _ (mo_le_trans MT MTL _ _ _ _ _ Umeter Hmle)). exact HXM.
Qed.
End e2.
End f2.
End d2.
