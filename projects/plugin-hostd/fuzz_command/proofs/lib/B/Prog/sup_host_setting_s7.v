(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the fifth segment of check_reply's walk (fuzz_command.asan, 0x86d78), the
   strcmp call of the refusal path (0x86fb8) and the branch into the epilogue, ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (the step through a call and back) and A/ACh5.v (a segment that ends
   in another segment's statement), at c8557374ad2e.

   The code of the segment is
     0x86fb8  jal  wrapper_strcmp       a0 = g_rec.reply, a1 = s3 = F + 32, which holds "resp <code>"
     0x86fbc  beqz a0, 0x86ff8          equal: the epilogue; else j 0x870d8, the abort
   The entry facts give `xr = refusal_text (reply_code_a xr)` for a negative code (reply_okA), and the frame holds
   `refusal_text code ++ [0]` (the snprintf step of segment 4), so the two strings are equal, the interceptor
   returns 0, and the abort edge 0x86fc0 is not taken.

   The walk runs with the symbolic regions dropped (`st_ok_pi_submem` with []): the two instructions write no
   memory, so the engine's frame is empty and every byte the walk reads is the byte of the state the segment was
   entered in. The interceptor's own writes are the ones its contract allows, inside its scratch window below sp. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s5.v, with its module paths and module names changed; 658 of its 699 lines of code are new or changed and 371 lines of the source are left out. *)
(* The last three segment lemmas of sup_host_setting's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan), on the points and statements of sup_host_setting_s0.v:
   - hs_seg_as2: from AS2 (0x8b804, back from arg_s(c, words)) `mv a0,s6`, the call of the free wrapper (0x589cc, at
     0x8b808) on the word list's block through afree04_sub, back at FR (0x8b80c);
   - hs_seg_fr: from FR `auipc s2,0x558` (A_HI 151 = 0x5e380c), `ld a0,-0x194(s2)` (A_OBJ 63 = 0x5e3678,
     g_rec.host_settings), `mv a1,s11`, the call of mix_call (0x8ad54, at 0x8b818) through cl_callS_na, back at MIX
     (0x8b81c);
   - hs_seg_mix: from MIX the digest store `sd a0,-0x194(s2)`, the frame's magic retired `sd a0,0(s4)`, the frame's
     shadow := f5, the frame's flag byte := 0 (`ld a0,0x38(s3); sb zero,0(a0)`: the release, aj_flag_store_pi), the
     epilogue (the 13 saved registers reloaded from the 160-byte frame at s0 = sp0), the return (paj_ret_at), and
     the post hs_post.
   The B twin of the ASan walk's sup_host_setting_s7.v (a working branch e323bbe76d2), with the B
   frame release of lib/A/Prog/answer_code.v's epilogue. The segment has no ASan report edge and no UBSan trap:
   0x8b82c `beqz s3` (s3 = F) is decided by the symbolic executor from the fact 4096 <= F (hsb7_fMIX). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05 YI16 YG05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibF PaLibG PaLibH PaSB PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_calls_free_c rec_canonical_c record_c arg_line_c arg_s_c xmalloc_c mix_call_c sup_host_setting_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_host_setting_aux sup_host_setting_s1 sup_host_setting_s0 sup_host_setting_s3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma hsb7_saved_lt : forall j r, nth_error HS_SAVED j = Some r -> (j < 13)%nat.
Proof.
intros j r H. assert (Hne : nth_error HS_SAVED j <> None) by (rewrite H; discriminate).
apply nth_error_Some in Hne. exact Hne.
Qed.

Lemma hsb7_bytes_sfs : forall cid pos s, blocks_bytes (stack_free_state cid pos s) = blocks_bytes s.
Proof. intros cid pos s. reflexivity. Qed.

Lemma hsb7_rhost_rec : forall R fn A, r_host (rec_record R fn A) = r_host R.
Proof. intros R fn A. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); reflexivity. Qed.

Lemma hsb7_denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* the n-wide field read over `aview segs H mem` is the symbolic executor's `val_mem segs (mrestrict H mem)`
   (B_socket_send.v's SSRecB, ref copy) *)
Lemma hsb7_aval_mem_view : forall segs H mem a n v,
val_mem segs (mrestrict H mem) a n v -> aval_mem (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YG0f.le_byte, YO0f.le_byte.
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma hsb7_val_mem_view : forall segs H mem a n v,
aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. pose proof (Hv k Hk) as Hb. unfold aview in Hb.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; [|discriminate]. cbn [option_map] in Hb.
injection Hb as Hb. f_equal. transitivity (Z_to_bv 8 (bv_unsigned b)); [symmetry; apply Z_to_bv_bv_unsigned|].
f_equal. rewrite Hb. reflexivity.
Qed.

(* FR's seed: g_rec.host_settings through the auipc pair's object atom A_OBJ 63, read-only, its value the extra
   atom 32; the shadow base s10 (the token executor's Bx) *)
Definition hsb7_rH : YP09.region := YP09.mkRegion (Some (A_OBJ 63)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition hsb7_fK : facts := mkFacts [(26%nat, mkAF HS_SB HS_SB 0)] [] [].

Lemma hsb7_bv5_eq : forall (z : Z) (r : bv 5), bv_unsigned r = z -> Z_to_bv 5 z = r.
Proof. intros z r <-. apply Z_to_bv_bv_unsigned. Qed.

(* MIX's seed (0x8b81c): the digest cell g_rec.host_settings at s2 - 0x194 (written), the frame's header word at
   s4 = F (written: the retired magic), the frame's flag pointer at s3 + 56 = F + 56 (read: the extra atom 32 = FL),
   the frame's 8 shadow bytes at s9 (written: f5), the flag byte at FL (written: the release), and the 13 saved
   registers at s0 - 8 - 8 j = sp0 - 8 - 8 j (read: the extra atom 33 + j holds HS_SAVED's j-th register) *)
Definition hsb7_rD : YP09.region := YP09.mkRegion (Some 18%nat) (-404) (-396) (-404) (-396) [].
Definition hsb7_rHd : YP09.region := YP09.mkRegion (Some 20%nat) 0 8 0 8 [].
Definition hsb7_rFP : YP09.region := YP09.mkRegion (Some 19%nat) 56 64 56 56 [YP09.mkChunk 56 (CVal 8 (SOff 32 0))].
Definition hsb7_rSh : YP09.region := YP09.mkRegion (Some 25%nat) 0 8 0 8 [].
Definition hsb7_rFl : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition hsb7_rSv : YP09.region := YP09.mkRegion (Some 8%nat) (-104) 0 (-104) (-104)
[YP09.mkChunk (-104) (CVal 8 (SOff 45 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0)); YP09.mkChunk (-88) (CVal 8 (SOff 43 0));
 YP09.mkChunk (-80) (CVal 8 (SOff 42 0)); YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
 YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0)); YP09.mkChunk (-40) (CVal 8 (SOff 37 0));
 YP09.mkChunk (-32) (CVal 8 (SOff 36 0)); YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
 YP09.mkChunk (-8) (CVal 8 (SOff 33 0))].
(* s3 = F is at least 4096: 0x8b82c `beqz s3` is decided not taken *)
Definition hsb7_fMIX : facts := mkFacts [(19%nat, mkAF 4096 (2 ^ 47) 0)] [] [].
Definition hsb7_ssMIX : sstate :=
mkSS HS_MIX sr_atoms [hsb7_rD; hsb7_rHd; hsb7_rFP; hsb7_rSh; hsb7_rFl; hsb7_rSv] None hsb7_fMIX.
(* the env's extra atoms at MIX: FL, then the entry's saved registers in HS_SAVED's order *)
Definition hsb7_ext (regs : bvmap 5 word) (fl : Z) : list word :=
Z_to_bv 64 fl :: map (fun r => getr regs (Z_to_bv 5 r)) HS_SAVED.


Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma hsb7_ablocks_sfs : forall B ly cid pos s, ablocks B ly (stack_free_state cid pos s) = ablocks B ly s.
Proof. intros B ly cid pos s. unfold ablocks. rewrite blocks_stack_free_state. reflexivity. Qed.

(* one saved register of the frame, as a chunk of the saved-register region at s0 = sp0 *)
Lemma hsb7_chunk_fr : forall (E : env) (W : world SEGS) memc sp0 (regs : bvmap 5 word) (j : nat) (r : Z),
hs_frame (aview SEGS (w_H W) memc) sp0 regs ->
nth_error HS_SAVED j = Some r ->
ew E (33 + j)%nat = getr regs (Z_to_bv 5 r) ->
YP09.chunk_ok SEGS E (mrestrict (w_H W) memc) sp0 (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (33 + j) 0))).
Proof.
intros E W memc sp0 regs j r HFR Hj Hew.
apply (chunk_ok_val SEGS E _ sp0 (-8 - 8 * Z.of_nat j) 8 (SOff (33 + j) 0) (bv_unsigned (ew E (33 + j)))).
- cbn [sv_denot]. rewrite Z.add_0_r. reflexivity.
- pose proof (bv_unsigned_in_range 64 (ew E (33 + j))) as Hr.
  change (bv_modulus 64) with (2 ^ 64) in Hr. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
- cbn. lia.
- apply hsb7_val_mem_view. rewrite Hew. change (N.to_nat 8) with 8%nat.
  replace (sp0 + (-8 - 8 * Z.of_nat j)) with (sp0 - 8 - 8 * Z.of_nat j) by lia.
  exact (HFR j r Hj).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HH : hs_hyps B MT.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let MLW : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B (hh_HB B MT HH)).

(* ---- AS2 0x8b804: a0 := w, the call of the free wrapper on the word list ---- *)
Lemma hs_seg_as2 : forall x, ST_FR B MT x -> ST_AS2 B MT x.
Proof.
intros x FR. unfold ST_AS2.
intros fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 w b3 CX FXR MID REP Hw4 RG R22.
pose proof CX as (HPRE & HROD & HRO & (Hpl & Hptok) & H10 & H11 & H12 & HNT & HLINE & Hp0 & Hp8 & HTA & HLPS & HPS &
  HTOKS & HWL & HREP0 & HFRM & HEV & HLIVE & HMO & HTAIL & HRM0).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof RG as ((K2 & K9 & K8 & K3 & K4 & K24 & K25 & K26) & R19 & R20 & R27).
pose proof MID as (HJ & Hk & HMLE & HBB & HFR & HFL & HBA).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (hs3_sp1 (spZ (i_regs x)) Hal16 ltac:(lia)) as (S1a & S1b & S1c).
pose proof hs3_stk as FS.
assert (HAS : ASTACK = 16384) by reflexivity.
pose proof (hh_MTL B MT HH) as ML.
pose (E := Eimg (Ereg regs1 [])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (HS : st_ok_pi SEGS VAL E (mkSS HS_AS2 sr_atoms [] None (mkFacts [(26%nat, mkAF HS_SB HS_SB 0)] [] []))
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + HS_AS2)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact (regs_ok_Eimg_Ereg regs1 []).
  - reflexivity.
  - constructor.
  - exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (EE 26%nat 26%bv eq_refl), K26. unfold w64.
    rewrite !unsigned_lit_small by (unfold HS_SB; lia). rewrite Z.pow_0_r, !Z.mod_1_r. unfold HS_SB. lia. }
assert (SHOK : sh_ok SEGS hs3_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
clearbody E.
(* 0x8b804 .. 0x8b808: a0 := s6 = w, the call of the free wrapper *)
paj_run_tok RUN HS HJ SHOK hs3_Bspan.
{ apply awr_ok_nil. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
assert (KEQ : forall a, aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
{ intros a. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|]. intros (r & Hr & _). destruct Hr. }
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10.
prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
rewrite (EE 2%nat 2%bv eq_refl), K2 in P2. rewrite (EE 3%nat 3%bv eq_refl), K3 in P3. rewrite (EE 4%nat 4%bv eq_refl), K4 in P4.
rewrite (EE 8%nat 8%bv eq_refl), K8 in P8. rewrite (EE 9%nat 9%bv eq_refl), K9 in P9.
rewrite (EE 22%nat 22%bv eq_refl), R22 in P10.
rewrite (EE 19%nat 19%bv eq_refl), R19 in P19. rewrite (EE 20%nat 20%bv eq_refl), R20 in P20.
rewrite (EE 24%nat 24%bv eq_refl), K24 in P24. rewrite (EE 25%nat 25%bv eq_refl), K25 in P25.
rewrite (EE 26%nat 26%bv eq_refl), K26 in P26. rewrite (EE 27%nat 27%bv eq_refl), R27 in P27.
assert (Qsp : spZ (ms_regs ms) = spZ (i_regs x) + (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x))).
{ unfold spZ at 1. rewrite P2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
(* the word list's block, none of the recorder's *)
pose proof HJ as (HARc & _ & _ & _ & _ & HFRSc & HNEVc & _).
pose proof HBA as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7).
set (nw := LIVE_XMALLOC (hs_wsz x)) in *.
assert (Hwin : In (w, nw) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym BA1)). apply in_or_app. left. right; right; left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ w nw HARc Hwin) as (_ & Hw4096 & Hwceil & _ & _ & _ & Hnw0).
pose proof (req_size_pos nw ltac:(lia)) as Hwrq.
assert (ND : List.NoDup ([(b0, hs_b0 x); (b1, hs_b1 x); (w, nw); (b3, hs_b3 x)] ++ Rest))
  by exact (Permutation_NoDup BA1 (RecBLemmas.recb_ablocks_nodup_m B lyc Sc Wc (ms_mem ms) mdv HARc)).
cbn [app] in ND.
apply NoDup_cons_iff in ND as [Nb0 ND]. apply NoDup_cons_iff in ND as [Nb1 ND].
apply NoDup_cons_iff in ND as [Nw ND].
assert (HNW : forall pn, In pn ((b3, hs_b3 x) :: (b1, hs_b1 x) :: (b0, hs_b0 x) :: O1) -> pn <> (w, nw)).
{ intros pn Hpn Heq. subst pn. destruct Hpn as [Hb | [Hb | [Hb | Ho1]]].
  - apply Nw. left. exact Hb.
  - apply Nb1. left. symmetry. exact Hb.
  - apply Nb0. right. left. symmetry. exact Hb.
  - apply Nw. right. exact (BA7 _ Ho1). }
(* the free wrapper's premises at the call *)
assert (HEVc : st_nev Sc < EV_MAX).
{ unfold EV_SUP_HOST_SETTING, hs_k4, hs_k3, hs_k2, hs_k1, hs_k0 in *. lia. }
assert (HMOc : mo_ok MT Sc (mo_free MT)).
{ apply (mok_station MT (i_S x) Sc (XM_SUP_HOST_SETTING MT (i_R x) (i_line x) (i_toks x)) (hs_m4 MT x) _ ML HMO HMLE).
  - exact (mo_free_nonneg MT ML).
  - unfold XM_SUP_HOST_SETTING, hs_m4, hs_m3, hs_m2, hs_m1, hs_m0, hs_wsz. lia. }
assert (HCHx : exists ch, chain_pre lyc (rdW Wc (ms_mem ms)) (ms_regs ms) ch).
{ (* a class-B site (a Theorem Labs lane's PASS4-REFIT.md section B): the chain pushed by the prologue, as chain_pre *)
  destruct (hs3_achain B MT x fpos lyc Sc Wc (ms_mem ms) mdv k (ms_regs ms) CX HJ
    (hs3_frame_kept_on (rdW Wc memc) _ _ _ (fun b _ => KEQ b) HFR) ltac:(rewrite Qsp; lia) P8) as (ch & HCH0).
  exists ch. apply (achain_chain_pre lyc _ (spZ (ms_regs ms)) (s0Z (ms_regs ms)) ch (ms_regs ms) HCH0).
  - split; [|lia]. rewrite Qsp.
    pose proof CX as (HPRE' & _). pose proof HPRE' as (_ & _ & _ & _ & _ & (Hal' & Hs0' & Hc' & Hl' & _) & _).
    destruct (hs3_sp1 (spZ (i_regs x)) Hal' ltac:(pose proof (@ASAN_CEIL_range rc) as [C1' _]; unfold ASAN_CEIL in C1'; lia))
      as (S1' & _).
    pose proof hs3_stk as FS'. clear - S1' Hs0' Hc' Hl' FS'. rewrite FS' in Hl'. lia.
  - reflexivity.
  - unfold raZ. rewrite P1, unsigned_lit_small by lia. lia. }
destruct HCHx as (ch & HCH).
assert (HCOV : In (w, nw) (ablocks B (i_ly x) (i_S x)) -> forall i, 0 <= i < req_size nw -> inFP (hs_FP (i_O x)) (w + i)).
{ intros Hin0 i Hi.
  pose proof (BA6 (w, nw) ltac:(right; right; left; reflexivity) Hin0) as HwO.
  unfold hs_FP. apply inFP_cons. right. apply inFP_cons. right.
  exact (inFP_ablocks_fp (i_O x) w nw i HwO Hi). }
rewrite (pal_free B (hh_TL B MT HH)).
eapply SRr_bind.
{ eapply (afree04_sub SEGS B LAWS pa_segs_low MT (hh_free B MT HH fx) Wc (ms_regs ms) (ms_mem ms)
    SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [(0, fpos)]
    lyc Sc mdv k w nw (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x)) (getr (ms_regs ms) 1) ch HJ Hwin P10 Qsp S1b
    ltac:(lia) ltac:(rewrite FS, HAS; lia)).
  - rewrite P3. exact Hgp.
  - rewrite P4. exact Htp.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact HEVc.
  - exact HCH.
  - exact HCOV.
  - exact HMOc. }
(* back at 0x8b80c *)
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & El1 & El2) & Hfrs2 & HK & MLE2 & HJc).
pose proof HK as (KK1 & KK2 & KK3 & KK4 & _).
destruct (hs3_frame_facts B MT x fpos lyc Sc Wc (ms_mem ms) mdv k CX HJ) as (HFin & EFA & EFL & HF4096 & HFceil & HF64).
assert (HIN2 : forall pn, In pn (ablocks B lyc Sc) -> pn <> (w, nw) -> In pn (ablocks B ly2 S2)).
{ intros pn Hpn Hne. rewrite El1 in Hpn. rewrite El2.
  apply in_app_or in Hpn as [H | [H | H]]; apply in_or_app; [left; exact H | congruence | right; exact H]. }
(* a byte of a live block other than the word list's is kept by the free *)
assert (KB : forall p n i, In (p, n) (ablocks B lyc Sc) -> (p, n) <> (w, nw) -> 0 <= i < req_size n ->
  rdW W2 mem2 (p + i) = rdW Wc memc (p + i)).
{ intros p n i Hin Hne Hi. rewrite <- (KEQ (p + i)). apply (KK2 p n i Hin Hi).
  pose proof (sep_blocks SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv p n w nw HARc Hin Hwin Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. cbv beta. lia. }
rewrite P1.
refine (FR fpos ly2 S2 W2 mem2 md2 regs2 (k + 1) O1 Rest b0 b1 b3 CX FXR _ _ _).
- refine (conj HJ2 (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  + unfold hs_k5. lia.
  + exact (mle_station MT _ _ _ _ _ ML HMLE MLE2).
  + rewrite (blocks_bytes_bsum B ly2 S2), El2, bsum_app.
    rewrite (blocks_bytes_bsum B lyc Sc), El1, bsum_app, bsum_cons in HBB. cbn [snd] in HBB. lia.
  + apply (hs3_frame_kept_on (rdW Wc memc)); [|exact HFR].
    intros b Hb. rewrite <- (KEQ b). apply KK1; lia.
  + apply (hs3_aval_on (rdW Wc memc)); [|exact HFL].
    intros b Hb. rewrite <- (KEQ b). apply (KK4 0 fpos b HFin).
    * left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 0) with 64. cbn in Hb. lia.
    * pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv w nw 0 fpos HARc Hwin HFin) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA in Hd. change (fs_frame_bytes 0) with 64 in Hd.
      cbn in Hb. cbv beta. lia.
  + split; [|split; [exact BA2|split; [exact BA3|split; [exact BA4|split; [exact BA5|split; [|exact BA7]]]]]].
    * rewrite El2.
      assert (PP : Permutation ((w, nw) :: l1 ++ l2) ((w, nw) :: [(b0, hs_b0 x); (b1, hs_b1 x); (b3, hs_b3 x)] ++ Rest)).
      { eapply Permutation_trans; [apply Permutation_middle|]. rewrite <- El1.
        eapply Permutation_trans; [exact BA1|].
        apply Permutation_sym. exact (Permutation_middle [(b0, hs_b0 x); (b1, hs_b1 x)] ((b3, hs_b3 x) :: Rest) (w, nw)). }
      exact (Permutation_cons_inv PP).
    * intros pn Hpn Hin0. apply BA6; [|exact Hin0].
      destruct Hpn as [<- | [<- | [<- | []]]]; [left | right; left | right; right; right; left]; reflexivity.
- apply (hs_rec_kept B lyc Sc ly2 S2 (rdW Wc memc) (rdW W2 mem2) _ _ REP).
  + intros a [Ha | (pn & Hpn & Ha)].
    * assert (HPa : Exists (in_zr a) recb_PG) by exact (proj2 (hs3_rec_fp (i_O x) a Ha)).
      destruct (RecBLemmas.recb_prog_unowned_m B (hh_HB B MT HH) (hh_prog_img B MT HH) a HPa) as (Hi1 & Hi2 & Hi3).
      rewrite <- (KEQ a). exact (KK3 a Hi1 Hi2 Hi3).
    * destruct pn as [p n]. cbn [fst snd] in Ha.
      destruct (hs_rec_own B _ _ _ _ _ REP (p, n) Hpn) as (Hin & _ & _).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos n ltac:(lia)) as Hrq.
      replace a with (p + (a - p)) by lia.
      exact (KB p n (a - p) Hin (HNW (p, n) Hpn) ltac:(lia)).
  + intros pn Hpn. exact (HIN2 pn (proj1 (hs_rec_own B _ _ _ _ _ REP pn Hpn)) (HNW pn Hpn)).
- split.
  + split; [transitivity (getr (ms_regs ms) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact P2]|].
    split; [transitivity (getr (ms_regs ms) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact P9]|].
    split; [transitivity (getr (ms_regs ms) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact P8]|].
    split; [transitivity (getr (ms_regs ms) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact P3]|].
    split; [transitivity (getr (ms_regs ms) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact P4]|].
    split; [transitivity (getr (ms_regs ms) 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact P24]|].
    split; [transitivity (getr (ms_regs ms) 25); [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact P25]|].
    transitivity (getr (ms_regs ms) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact P26].
  + split; [transitivity (getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact P19]|].
    split; [transitivity (getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact P20]|].
    transitivity (getr (ms_regs ms) 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | exact P27].
Qed.

(* the auipc pair at 0x8b80c / 0x8b810: A_HI 151 = 0x5e380c (cmd_val_his), A_OBJ 63 = g_rec.host_settings
   (cmd_val_objs) *)
Lemma hsb7_obj63 : VAL (A_OBJ 63) = A_G_REC + OFF_HOST.
Proof. rewrite (hh_vobjs B MT HH 63%nat) by (vm_compute; lia). vm_compute. reflexivity. Qed.
Lemma hsb7_hi151 : VAL (A_HI 151) = 0x5e380c.
Proof. rewrite (hh_vhis B MT HH 151%nat) by (vm_compute; lia). vm_compute. reflexivity. Qed.

(* ---- FR 0x8b80c: s2 := 0x5e380c, a0 := g_rec.host_settings, a1 := c, the call of mix_call ---- *)
Lemma hs_seg_fr : forall x, ST_MIX B MT x -> ST_FR B MT x.
Proof.
intros x MIX. unfold ST_FR.
intros fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 b3 CX FXR MID REP RG.
pose proof CX as (HPRE & HROD & HRO & (Hpl & Hptok) & H10 & H11 & H12 & HNT & HLINE & Hp0 & Hp8 & HTA & HLPS & HPS &
  HTOKS & HWL & HREP0 & HFRM & HEV & HLIVE & HMO & HTAIL & HRM0).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof RG as ((K2 & K9 & K8 & K3 & K4 & K24 & K25 & K26) & R19 & R20 & R27).
pose proof MID as (HJ & Hk & HMLE & HBB & HFR & HFL & HBA).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (hs3_sp1 (spZ (i_regs x)) Hal16 ltac:(lia)) as (S1a & S1b & S1c).
pose proof hs3_stk as FS.
destruct (hs_rec_hostval B lyc Sc (rdW Wc memc) _ _ REP) as [Hh0 Hh0r].
rewrite hsb7_rhost_rec in Hh0, Hh0r.
pose (E := Eimg (Ereg regs1 [Z_to_bv 64 (r_host (i_R x))])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = Z_to_bv 64 (r_host (i_R x))).
{ unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 0). }
assert (E63 : bv_unsigned (ew E (A_OBJ 63)) = A_G_REC + OFF_HOST).
{ unfold E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite hsb7_obj63.
  apply unsigned_lit_small. unfold A_G_REC, OFF_HOST. lia. }
assert (E151 : ew E 551 = Z_to_bv 64 0x5e380c).
{ unfold E. change 551%nat with (A_HI 151). rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia).
  rewrite hsb7_hi151. reflexivity. }
assert (HS : st_ok_pi SEGS VAL E (mkSS HS_FR sr_atoms [hsb7_rH] None hsb7_fK)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + HS_FR)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact (regs_ok_Eimg_Ereg regs1 _).
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, hsb7_rH.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E63. split; [unfold A_G_REC, OFF_HOST; lia|]. split; [unfold A_G_REC, OFF_HOST; lia|].
    split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (A_G_REC + OFF_HOST) 0 8 (SOff 32 0) (r_host (i_R x))).
    + rewrite hsb7_denot_off0. exact E32.
    + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + cbn. lia.
    + rewrite Z.add_0_r. change (N.to_nat 8) with 8%nat. apply hsb7_val_mem_view. exact Hh0.
  - split; exact I.
  - split; [|split; exact I]. cbn [hsb7_fK f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (EE 26%nat 26%bv eq_refl), K26. unfold w64.
    rewrite !unsigned_lit_small by (unfold HS_SB; lia). rewrite Z.pow_0_r, !Z.mod_1_r. unfold HS_SB. lia. }
assert (SHOK : sh_ok SEGS hs3_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
clearbody E.
(* 0x8b80c .. 0x8b818: s2 := A_HI 151, a0 := g_rec.host_settings (A_OBJ 63), a1 := s11 = c, the call of mix_call *)
paj_run_tok RUN HS HJ SHOK hs3_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?bl0 ?blc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp bl0 blc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
assert (KEQ : forall a, aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
{ intros a. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hr & Ha).
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end.
  destruct Hr as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20.
prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
rewrite (EE 2%nat 2%bv eq_refl), K2 in P2. rewrite (EE 3%nat 3%bv eq_refl), K3 in P3. rewrite (EE 4%nat 4%bv eq_refl), K4 in P4.
rewrite (EE 8%nat 8%bv eq_refl), K8 in P8. rewrite (EE 9%nat 9%bv eq_refl), K9 in P9.
rewrite E32 in P10. rewrite (EE 27%nat 27%bv eq_refl), R27 in P11. rewrite E151 in P18.
rewrite (EE 19%nat 19%bv eq_refl), R19 in P19. rewrite (EE 20%nat 20%bv eq_refl), R20 in P20.
rewrite (EE 24%nat 24%bv eq_refl), K24 in P24. rewrite (EE 25%nat 25%bv eq_refl), K25 in P25.
rewrite (EE 26%nat 26%bv eq_refl), K26 in P26. rewrite (EE 27%nat 27%bv eq_refl), R27 in P27.
assert (Qsp : spZ (ms_regs ms) = spZ (i_regs x) + (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x))).
{ unfold spZ at 1. rewrite P2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (SIGMX : SIG CS_mix_call = BASE + AF_mix_call).
{ rewrite (hh_sigp B MT HH CS_mix_call ltac:(unfold cmd_prog_syms; repeat (first [left; reflexivity | right])));
  try (f_equal; vm_compute; reflexivity). }
rewrite SIGMX.
(* mix_call's premises at the call *)
pose proof HJ as (HARc & _ & _ & _ & _ & HFRSc & HNEVc & _).
destruct (hs3_rod_now B MT HH x fpos lyc Sc Wc (ms_mem ms) mdv k CX HJ) as [HRODc HROc].
assert (REPc : rec_repA B lyc Sc (rdW Wc (ms_mem ms)) (rec_record (i_R x) REC_HOST_SETTING (hs_args (i_line x) (i_toks x)))
  ((b3, hs_b3 x) :: (b1, hs_b1 x) :: (b0, hs_b0 x) :: O1))
  by exact (hs_rec_kept B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc (ms_mem ms)) _ _ REP (fun a _ => KEQ a)
    (fun pn H => proj1 (hs_rec_own B _ _ _ _ _ REP pn H))).
destruct (hs_rec_last B lyc Sc (rdW Wc (ms_mem ms)) (i_R x) (hs_args (i_line x) (i_toks x)) _ REPc) as (P & HCALL & _).
assert (HEVc : st_nev Sc + EV_MIX_CALL <= EV_MAX).
{ unfold EV_MIX_CALL, EV_SUP_HOST_SETTING, hs_k5, hs_k4, hs_k3, hs_k2, hs_k1, hs_k0 in *. lia. }
assert (P10' : getr (ms_regs ms) 10 = w64 (r_host (i_R x))) by exact P10.
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS Wc (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_mix_call)) SUP_HOST_SETTING_STK
    (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [(0, fpos)] lyc Sc mdv k
    MIX_CALL_STK [] EV_MIX_CALL (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x)) (getr (ms_regs ms) 1)
    (fun ly2 S2 (W2 : world SEGS) regs2 mem2 md2 =>
      getr regs2 10 = w64 (mixcall (r_host (i_R x)) REC_HOST_SETTING (hs_args (i_line x) (i_toks x))) /\
      Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ ly2 = lyc /\ S2 = Sc)
    HJ Qsp S1b ltac:(lia) ltac:(unfold MIX_CALL_STK, ESTACK; lia) ltac:(rewrite FS; unfold MIX_CALL_STK, ESTACK; lia)).
  - rewrite P3. exact Hgp.
  - rewrite P4. exact Htp.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite P1, unsigned_lit_small by lia. lia.
  - intros HPREc.
    eapply SRr_mono.
    { exact (hh_mix B MT HH fx lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv (r_host (i_R x)) (rec_slot (i_R x))
        (REC_HOST_SETTING, hs_args (i_line x) (i_toks x)) P HPREc HRODc P10' Hh0r P11 (hs3_slot_cases (i_R x))
        HCALL HROc HEVc). }
    cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJc & HPc & HKc).
    exists ly2, S2, regs2, mem2, md2. split; [exact Hc2|]. split; [exact HJc|]. split; [exact HPc|].
    cbn [fst snd] in HKc. exact HKc.
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
(* back at 0x8b81c *)
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2c & HP2 & HK10 & HKperm & Ely2 & ES2).
subst ly2 S2.
pose proof HJ2c as (HAR2 & _ & _ & _ & _ & _ & _ & _ & J1 & J2 & J3 & J4 & _).
destruct (hs3_frame_facts B MT x fpos lyc Sc Wc (ms_mem ms) mdv k CX HJ) as (HFin & EFA & EFL & HF4096 & HFceil & HF64).
rewrite P1.
refine (MIX fpos lyc Sc W2 mem2 md2 regs2 (k + EV_MIX_CALL) O1 Rest b0 b1 b3 CX FXR _ _ _ _ _).
- refine (conj HJ2 (conj _ (conj HMLE (conj HBB (conj _ (conj _ HBA)))))).
  + unfold EV_MIX_CALL. lia.
  + apply (hs3_frame_kept_on (rdW Wc memc)); [|exact HFR].
    intros b Hb. rewrite <- (KEQ b). apply J1; [lia | lia | exact (inFP_nil b)].
  + apply (hs3_aval_on (rdW Wc memc)); [|exact HFL].
    intros b Hb. rewrite <- (KEQ b). apply (J4 0 fpos b HFin); [|exact (inFP_nil b)].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 0) with 64. cbn in Hb. lia.
- apply (hs_rec_kept B lyc Sc lyc Sc (rdW Wc memc) (rdW W2 mem2) _ _ REP).
  + intros a [Ha | (pn & Hpn & Ha)].
    * assert (HPa : Exists (in_zr a) recb_PG) by exact (proj2 (hs3_rec_fp (i_O x) a Ha)).
      destruct (RecBLemmas.recb_prog_unowned_m B (hh_HB B MT HH) (hh_prog_img B MT HH) a HPa) as (Hi1 & Hi2 & Hi3).
      rewrite <- (KEQ a). exact (J3 a Hi1 Hi2 Hi3 (fp_spares_closed [] a sink_closed_nil (inFP_nil a))).
    * destruct pn as [p n]. cbn [fst snd] in Ha.
      destruct (hs_rec_own B _ _ _ _ _ REP (p, n) Hpn) as (Hin & _ & _).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos n ltac:(lia)) as Hrq.
      replace a with (p + (a - p)) by lia. rewrite <- (KEQ (p + (a - p))).
      exact (J2 p n (a - p) Hin Hin ltac:(lia) (inFP_nil _)).
  + intros pn Hpn. exact (proj1 (hs_rec_own B _ _ _ _ _ REP pn Hpn)).
- split.
  + split; [transitivity (getr (ms_regs ms) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact P2]|].
    split; [transitivity (getr (ms_regs ms) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact P9]|].
    split; [transitivity (getr (ms_regs ms) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact P8]|].
    split; [transitivity (getr (ms_regs ms) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact P3]|].
    split; [transitivity (getr (ms_regs ms) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact P4]|].
    split; [transitivity (getr (ms_regs ms) 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact P24]|].
    split; [transitivity (getr (ms_regs ms) 25); [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact P25]|].
    transitivity (getr (ms_regs ms) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact P26].
  + split; [transitivity (getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact P19]|].
    split; [transitivity (getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact P20]|].
    transitivity (getr (ms_regs ms) 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | exact P27].
- transitivity (getr (ms_regs ms) 18); [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | exact P18].
- exact HK10.
Qed.

(* a register of the entry, through its extra atom: Z_to_bv 5 r is the register's literal *)
Ltac hsb7_greg EXj := etransitivity; [exact EXj | f_equal; apply hsb7_bv5_eq; vm_compute; reflexivity].

(* ---- MIX 0x8b81c: the digest stored, the frame's magic retired, its shadow := f5, its flag byte := 0 (the
   release), the saved registers back, the return ---- *)
Lemma hs_seg_mix : forall x, ST_MIX B MT x.
Proof.
intros x. unfold ST_MIX.
intros fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 b3 CX FXR MID REP RG Hs2 Ha0.
pose proof CX as (HPRE & HROD & HRO & (Hpl & Hptok) & H10 & H11 & H12 & HNT & HLINE & Hp0 & Hp8 & HTA & HLPS & HPS &
  HTOKS & HWL & HREP0 & HFRM & HEV & HLIVE & HMO & HTAIL & HRM0).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof RG as ((K2 & K9 & K8 & K3 & K4 & K24 & K25 & K26) & R19 & R20 & R27).
pose proof MID as (HJ & Hk & HMLE & HBB & HFR & HFL & HBA).
pose proof HBA as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7).
pose proof asan_consts as (C1 & _).
pose proof hs3_stk as FS.
pose proof (hh_MTL B MT HH) as MTL0.
pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'.
pose proof HJ as (HARc & _ & _ & _ & _ & HFRSc & HNEVc & _).
(* the frame, its shadow and its flag byte *)
destruct (hs3_frame_facts B MT x fpos lyc Sc Wc memc mdc k CX HJ) as (HFin & EFA & EFL & HF4096 & HFceil & HF64).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HARc HFin) as (_ & HFapp & HFpres & HFSpres).
rewrite EFA in HFapp, HFpres, HFSpres.
change (fs_frame_bytes 0) with 64 in HFapp, HFpres, HFSpres. change (64 / 8) with 8 in HFSpres.
destruct (al_flag _ _ LAWS _ _ _ _ _ 0 fpos HARc HFin) as (HFLp & HFLo & HFLapp & HFLceil).
rewrite EFL in HFLp, HFLo, HFLapp, HFLceil.
destruct (al_client_img _ _ LAWS _ _ _ _ _ (hs_FL x fpos) HARc) as [_ HFLimg].
{ right. right. exists 0, fpos. split; [exact HFin | symmetry; exact EFL]. }
set (F := hs_F x fpos) in *. set (FL := hs_FL x fpos) in *. clearbody F FL.
assert (HFq : 8 * (F / 8) <= F < 8 * (F / 8) + 8).
{ pose proof (Z.div_mod F 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as MB.
  set (q := F / 8) in *. set (m := F mod 8) in *. clearbody q m. lia. }
assert (HSA : shadow_addr F = HS_SB + F / 8) by (unfold shadow_addr, SHADOW_OFF, HS_SB; reflexivity).
rewrite HSA in HFSpres.
set (Fq := F / 8) in *. clearbody Fq.
assert (HFapp' : F + 64 <= 0x7fff7000 \/ (0x10007fff8000 <= F /\ F + 64 <= alloc_ceiling)).
{ clear - HFapp. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia. }
assert (HFLapp' : 4096 <= FL /\ (FL < 0x7fff7000 \/ 0x10007fff8000 <= FL)).
{ clear - HFLapp. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp. lia. }
assert (HFLnF : ~ (F <= FL < F + 64)) by (intros Hx; exact (proj2 (HFpres FL Hx) HFLo)).
assert (HFLnI : ~ (0x5e3678 <= FL < 0x5e3680)).
{ intros Hx. apply HFLimg. apply (hh_prog_img B MT HH). apply hs3_grec_in. unfold A_G_REC, REC_SIZE. lia. }
assert (HFimg : F + 64 <= 0x5e3678 \/ 0x5e3680 <= F).
{ destruct (Z_le_gt_dec (F + 64) 0x5e3678) as [H|H]; [left; exact H|].
  destruct (Z_le_gt_dec 0x5e3680 F) as [H'|H']; [right; exact H'|]. exfalso.
  apply (frm_img SEGS B LAWS lyc Sc Wc memc mdc 0 fpos (Z.max F 0x5e3678) HARc HFin);
    [rewrite EFA; change (fs_frame_bytes 0) with 64; lia|].
  apply (hh_prog_img B MT HH). apply hs3_grec_in. unfold A_G_REC, REC_SIZE. lia. }
assert (Hsp0 : alloc_ceiling + 104 <= spZ (i_regs x)) by (rewrite FS in Hslo; lia).
(* the new digest *)
pose (hmix := mixcall (r_host (i_R x)) REC_HOST_SETTING (hs_args (i_line x) (i_toks x))).
destruct (hs_rec_hostval B lyc Sc (rdW Wc memc) _ _ REP) as [_ Hh0r].
rewrite hsb7_rhost_rec in Hh0r.
assert (Hhm : 0 <= hmix < 2 ^ 64) by (apply mixcall_range; exact Hh0r).
(* the seed *)
pose (E := Eimg (Ereg regs1 (hsb7_ext (i_regs x) FL))).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = Z_to_bv 64 FL).
{ unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs1 _ 0). }
assert (EX : forall j r, nth_error HS_SAVED j = Some r -> ew E (33 + j) = getr (i_regs x) (Z_to_bv 5 r)).
{ intros j r Hn. pose proof (hsb7_saved_lt j r Hn) as Hj.
  unfold E. rewrite Eimg_low by (unfold A_TEXT; lia).
  change (33 + j)%nat with (32 + S j)%nat. rewrite ew_Ereg_extra. unfold hsb7_ext. cbn [nth].
  do 13 (destruct j as [|j]; [cbn in Hn; injection Hn as <-; reflexivity|]). exfalso. lia. }
assert (U18 : bv_unsigned (ew E 18) = 0x5e380c).
{ rewrite (EE 18%nat 18%bv eq_refl), Hs2. unfold w64. apply unsigned_lit_small. lia. }
assert (U19 : bv_unsigned (ew E 19) = F).
{ rewrite (EE 19%nat 19%bv eq_refl), R19. unfold w64. apply unsigned_lit_small. lia. }
assert (U20 : bv_unsigned (ew E 20) = F).
{ rewrite (EE 20%nat 20%bv eq_refl), R20. unfold w64. apply unsigned_lit_small. lia. }
assert (U25 : bv_unsigned (ew E 25) = HS_SB + Fq).
{ rewrite (EE 25%nat 25%bv eq_refl), K25. unfold w64. apply unsigned_lit_small. unfold HS_SB. lia. }
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = spZ (i_regs x)).
{ rewrite (EE 8%nat 8%bv eq_refl), K8. unfold w64. apply unsigned_lit_small. lia. }
assert (U10 : sv_denot E (SOff 10 0) = Z_to_bv 64 hmix).
{ rewrite hsb7_denot_off0, (EE 10%nat 10%bv eq_refl), Ha0. reflexivity. }
assert (HS : st_ok_pi SEGS VAL E hsb7_ssMIX
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + HS_MIX)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold hsb7_ssMIX. apply pa_entry_st_ok_full.
  - exact (regs_ok_Eimg_Ereg regs1 _).
  - vm_compute. reflexivity.
  - unfold hsb7_rD, hsb7_rHd, hsb7_rFP, hsb7_rSh, hsb7_rFl, hsb7_rSv.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + (* the digest cell, written *)
      rewrite U18. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (hh_prog_writable B MT HH lyc Sc Wc memc mdc _ HARc).
      apply hs3_grec_in. unfold A_G_REC, REC_SIZE. lia.
    + (* the frame's header word, written *)
      rewrite U20. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (F + o) ltac:(lia))).
    + (* the frame's flag pointer, read *)
      rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ F 56 8 (SOff 32 0) FL).
      * rewrite hsb7_denot_off0. exact E32.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * change (N.to_nat 8) with 8%nat. apply hsb7_val_mem_view. exact HFL.
    + (* the frame's shadow, written *)
      rewrite U25. split; [unfold HS_SB; lia|]. split; [unfold HS_SB; lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS).
      exact (proj1 (HFSpres o ltac:(lia))).
    + (* the flag byte, written *)
      rewrite U32. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). replace (FL + o) with FL by lia. exact HFLp.
    + (* the 13 saved registers, read *)
      rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * exact (hsb7_chunk_fr E Wc memc (spZ (i_regs x)) (i_regs x) 12 27 HFR eq_refl (EX 12%nat 27 eq_refl)).
      * exact (hsb7_chunk_fr E Wc memc (spZ (i_regs x)) (i_regs x) 11 26 HFR eq_refl (EX 11%nat 26 eq_refl)).
      * exact (hsb7_chunk_fr E Wc memc (spZ (i_regs x)) (i_regs x) 10 25 HFR eq_refl (EX 10%nat 25 eq_refl)).
      * exact (hsb7_chunk_fr E Wc memc (spZ (i_regs x)) (i_regs x) 9 24 HFR eq_refl (EX 9%nat 24 eq_refl)).
      * exact (hsb7_chunk_fr E Wc memc (spZ (i_regs x)) (i_regs x) 8 23 HFR eq_refl (EX 8%nat 23 eq_refl)).
      * exact (hsb7_chunk_fr E Wc memc (spZ (i_regs x)) (i_regs x) 7 22 HFR eq_refl (EX 7%nat 22 eq_refl)).
      * exact (hsb7_chunk_fr E Wc memc (spZ (i_regs x)) (i_regs x) 6 21 HFR eq_refl (EX 6%nat 21 eq_refl)).
      * exact (hsb7_chunk_fr E Wc memc (spZ (i_regs x)) (i_regs x) 5 20 HFR eq_refl (EX 5%nat 20 eq_refl)).
      * exact (hsb7_chunk_fr E Wc memc (spZ (i_regs x)) (i_regs x) 4 19 HFR eq_refl (EX 4%nat 19 eq_refl)).
      * exact (hsb7_chunk_fr E Wc memc (spZ (i_regs x)) (i_regs x) 3 18 HFR eq_refl (EX 3%nat 18 eq_refl)).
      * exact (hsb7_chunk_fr E Wc memc (spZ (i_regs x)) (i_regs x) 2 9 HFR eq_refl (EX 2%nat 9 eq_refl)).
      * exact (hsb7_chunk_fr E Wc memc (spZ (i_regs x)) (i_regs x) 1 8 HFR eq_refl (EX 1%nat 8 eq_refl)).
      * exact (hsb7_chunk_fr E Wc memc (spZ (i_regs x)) (i_regs x) 0 1 HFR eq_refl (EX 0%nat 1 eq_refl)).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, hsb7_rD, hsb7_rHd, hsb7_rFP, hsb7_rSh, hsb7_rFl, hsb7_rSv.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U18, U20, U19, U25, U32, U8.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    clear - HF4096 HFceil C1 HFapp' HFimg HFLapp' HFLceil HFLnF HFLnI Hsp0 HFq.
    unfold HS_SB. repeat split; lia.
  - split; [|split; exact I]. cbn [hsb7_fMIX f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, Z.pow_0_r, Z.mod_1_r. lia. }
clearbody E.
unfold hs_at.
(* 0x8b81c .. 0x8b8bc: the run, its flag store releasing the frame (0, fpos) *)
pose (RUNF := aj_flag_store_pi B LAWS MLW (hh_free_law B MT HH) (hh_FFL B MT HH)).
paj_run_flag_sh RUNF HS HJ.
- lia.
- intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  + left. rewrite U18 in Hr. right; right; right; right; left.
    assert (Hga : A_G_REC <= a < A_G_REC + REC_SIZE) by (unfold A_G_REC, REC_SIZE; lia).
    destruct (hs3_rec_fp (i_O x) a (or_introl Hga)) as [Hfp Hpg].
    split; [exact Hfp|]. split; [rewrite (ts_prog B (hh_HB B MT HH)); exact Hpg | exact (hh_prog_img B MT HH a Hpg)].
  + left. rewrite U20 in Hr. right; right; right; left. exists 0, fpos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 0) with 64. lia.
  + exfalso. lia.
  + left. rewrite U25 in Hr. right; right; right; left. exists 0, fpos. split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EFA, HSA. change (fs_frame_bytes 0 / 8) with 8. lia.
  + right. rewrite U32 in Hr. rewrite EFL. lia.
  + exfalso. lia.
- intros msr HSr. rewrite EFL.
  pose proof (st_ok_pi_region_nth E _ _ 4 _ HSr eq_refl) as HR4.
  pose proof (field_of_region E _ 32 FL _ 0 1 0 1 0 1%N (SLit 0) 0 HR4 U32 ltac:(cbn [In]; tauto) eq_refl
    ltac:(lia) ltac:(lia)) as HV.
  specialize (HV 0%nat ltac:(lia)). rewrite !Z.add_0_r in HV. rewrite HV. reflexivity.
- cbn [ms_mem mkst] in HF, HFr, HG.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
  prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
  prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  (* the run wrote the digest cell, the frame's header word and shadow, and the flag byte; nothing else *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((A_G_REC + OFF_HOST <= a < A_G_REC + OFF_HOST + 8) \/ (F <= a < F + 8) \/
       (HS_SB + Fq <= a < HS_SB + Fq + 8) \/ a = FL) ->
    rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha Hno.
    apply (kept_of_frame E (ss_mem hsb7_ssMIX) (w_H Wc) memc (ms_mem ms)
      (fun a => (A_G_REC + OFF_HOST <= a < A_G_REC + OFF_HOST + 8) \/ (F <= a < F + 8) \/
         (HS_SB + Fq <= a < HS_SB + Fq + 8) \/ a = FL) HFr); [| exact Ha | exact Hno].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    destruct Hin as [Hq | [Hq | [Hq | [Hq | [Hq | [Hq | []]]]]]]; inversion Hq; subst; cbn [base_val] in Hrr;
      rewrite ?U18, ?U19, ?U20, ?U25, ?U32, ?U8 in Hrr; cbv beta; unfold A_G_REC, OFF_HOST; lia. }
  (* the recorder's bytes are none of the written bytes *)
  set (O' := (b3, hs_b3 x) :: (b1, hs_b1 x) :: (b0, hs_b0 x) :: O1) in *.
  assert (NZ : forall a, hs_in_rec a \/ hs_in_own O' a ->
    ~ (F <= a < F + 8) /\ ~ (HS_SB + Fq <= a < HS_SB + Fq + 8) /\ a <> FL /\ 0 <= a < 2 ^ 64).
  { intros a [Ha | (pn & Hpn & Ha)].
    - pose proof (proj2 (hs3_rec_fp (i_O x) a Ha)) as HPa.
      pose proof (hh_prog_img B MT HH a HPa) as Himg.
      assert (Hlo : 0 <= a < 0x5e3798)
        by (clear - Ha; unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia).
      split.
      { intros Hf. apply (frm_img SEGS B LAWS lyc Sc Wc memc mdc 0 fpos a HARc HFin); [|exact Himg].
        rewrite EFA. change (fs_frame_bytes 0) with 64. lia. }
      split; [unfold HS_SB; lia|]. split; [intros Heq; rewrite Heq in Himg; exact (HFLimg Himg) | lia].
    - destruct pn as [p n]. cbn [fst snd] in Ha.
      destruct (hs_rec_own B _ _ _ _ _ REP (p, n) Hpn) as (Hin & _ & _).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARc Hin) as (_ & Hp4096 & Hpceil & Hpapp & Hppres & _ & Hn0).
      pose proof (req_size_pos n ltac:(lia)) as Hrq.
      pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc p n 0 fpos HARc Hin HFin) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA in Hd. change (fs_frame_bytes 0) with 64 in Hd.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
      split; [lia|]. split; [unfold HS_SB; lia|].
      split; [intros Heq; apply (proj2 (Hppres FL ltac:(lia))); exact HFLo | lia]. }
  (* the digest cell holds the new digest *)
  pose proof (st_ok_pi_region_nth E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  pose proof (field_of_region E (mrestrict (w_H Wc) (ms_mem ms)) 18 0x5e380c _ (-404) (-396) (-404) (-396) (-404) 8%N
    (SOff 10 0) hmix HR0 U18 ltac:(cbn [In]; tauto) U10 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hhm)
    ltac:(cbn; lia)) as V0.
  assert (VH : aval_mem (rdW Wc (ms_mem ms)) (A_G_REC + OFF_HOST) 8 hmix).
  { replace (A_G_REC + OFF_HOST) with (0x5e380c + -404) by (unfold A_G_REC, OFF_HOST; lia).
    apply hsb7_aval_mem_view. exact V0. }
  assert (HRH : rec_repA B lyc Sc (rdW Wc (ms_mem ms))
    (set_host (rec_record (i_R x) REC_HOST_SETTING (hs_args (i_line x) (i_toks x))) hmix) O').
  { apply (hs_rec_host B lyc Sc (rdW Wc memc) (rdW Wc (ms_mem ms)) _ _ hmix REP Hhm VH).
    intros a Ha Hno. destruct (NZ a Ha) as (N1 & N2 & N3 & N4). apply KEEP; [exact N4|].
    intros [H | [H | [H | H]]]; [exact (Hno H) | exact (N1 H) | exact (N2 H) | exact (N3 H)]. }
  assert (A33 : ew E 33 = getr (i_regs x) 1) by hsb7_greg (EX 0%nat 1 eq_refl).
  assert (RA : v_jalr (getr (ms_regs ms) 1) 0 = getr (i_regs x) 1).
  { rewrite P1. transitivity (v_jalr (getr (i_regs x) 1) 0); [f_equal; exact A33 | exact Hra']. }
  (* the return *)
  eapply (paj_ret_at (PL := PL_cmd) (PI := PI) Wc _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold hs_post. cbv zeta. unfold apost_baseF.
  exists fx, lyc, (stack_free_state 0 fpos Sc), (ms_regs ms), (ms_mem ms).
  eexists.
  split; [rewrite RA; reflexivity|].
  split; [exact (proj1 FXR)|].
  split; [exact (proj2 FXR)|].
  split.
  { eapply (ajournal_mono_k SEGS B); [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
    unfold hs_k5, hs_k4, hs_k3, hs_k2, hs_k1, hs_k0, EV_SUP_HOST_SETTING in *. lia. }
  split.
  { apply aregs_preserved_eqs.
    - etransitivity; [exact P2|]. etransitivity; [exact (EE 8%nat 8%bv eq_refl)|].
      etransitivity; [exact K8|]. unfold w64, spZ. apply Z_to_bv_bv_unsigned.
    - etransitivity; [exact P3|]. etransitivity; [exact (EE 3%nat 3%bv eq_refl)|]. exact K3.
    - etransitivity; [exact P4|]. etransitivity; [exact (EE 4%nat 4%bv eq_refl)|]. exact K4.
    - etransitivity; [exact P8|]. hsb7_greg (EX 1%nat 8 eq_refl).
    - etransitivity; [exact P9|]. hsb7_greg (EX 2%nat 9 eq_refl).
    - etransitivity; [exact P18|]. hsb7_greg (EX 3%nat 18 eq_refl).
    - etransitivity; [exact P19|]. hsb7_greg (EX 4%nat 19 eq_refl).
    - etransitivity; [exact P20|]. hsb7_greg (EX 5%nat 20 eq_refl).
    - etransitivity; [exact P21|]. hsb7_greg (EX 6%nat 21 eq_refl).
    - etransitivity; [exact P22|]. hsb7_greg (EX 7%nat 22 eq_refl).
    - etransitivity; [exact P23|]. hsb7_greg (EX 8%nat 23 eq_refl).
    - etransitivity; [exact P24|]. hsb7_greg (EX 9%nat 24 eq_refl).
    - etransitivity; [exact P25|]. hsb7_greg (EX 10%nat 25 eq_refl).
    - etransitivity; [exact P26|]. hsb7_greg (EX 11%nat 26 eq_refl).
    - etransitivity; [exact P27|]. hsb7_greg (EX 12%nat 27 eq_refl). }
  exists O'.
  split.
  { unfold sup_host_setting_m. cbv zeta. unfold rec_mix_host. cbn [fst snd]. rewrite hsb7_rhost_rec.
    apply (hs_rec_kept B lyc Sc lyc (stack_free_state 0 fpos Sc) (rdW Wc (ms_mem ms)) (rdW Wc (ms_mem ms)) _ _ HRH).
    - intros a _. reflexivity.
    - intros pn Hpn. rewrite hsb7_ablocks_sfs. exact (proj1 (hs_rec_own B _ _ _ _ _ REP pn Hpn)). }
  split.
  { intros pn Hpn.
    assert (HNw : In pn [(b0, hs_b0 x); (b1, hs_b1 x); (b3, hs_b3 x)] -> In pn (i_O x) \/ ~ In pn (ablocks B (i_ly x) (i_S x))).
    { intros Hn. destruct (in_dec hs3_pair_dec pn (ablocks B (i_ly x) (i_S x))) as [Hin | Hin];
        [left; exact (BA6 pn Hn Hin) | right; exact Hin]. }
    destruct Hpn as [Hp | [Hp | [Hp | Ho1]]].
    - apply HNw. rewrite <- Hp. right; right; left; reflexivity.
    - apply HNw. rewrite <- Hp. right; left; reflexivity.
    - apply HNw. rewrite <- Hp. left; reflexivity.
    - left. exact (BA5 _ Ho1). }
  split.
  { intros pn Hpn Hno. rewrite hsb7_ablocks_sfs. apply (Permutation_in _ (Permutation_sym BA1)).
    apply in_or_app. right. exact (BA3 pn Hpn Hno). }
  split.
  { intros pn Hpn. rewrite hsb7_ablocks_sfs in Hpn. apply (Permutation_in _ BA1) in Hpn.
    apply in_app_or in Hpn as [Hn | Hr].
    - right. destruct Hn as [<- | [<- | [<- | []]]]; [right; right; left | right; left | left]; reflexivity.
    - destruct (in_dec hs3_pair_dec pn (i_O x)) as [Hin | Hin].
      + right. right; right; right. exact (BA4 pn Hr Hin).
      + left. split; [exact (BA2 pn Hr) | exact Hin]. }
  split.
  { rewrite hsb7_bytes_sfs. unfold hs_l4, hs_l3, hs_l2, hs_l1, hs_wsz, LIVE_SUP_HOST_SETTING in HBB |- *. lia. }
  unfold stack_free_state. apply (mo_le_set_fs_r MT (hh_MTLF B MT HH)).
  apply (mle_weaken MT _ _ _ _ MTL0 HMLE).
  unfold hs_m5, hs_m4, hs_m3, hs_m2, hs_m1, hs_m0, hs_wsz, XM_SUP_HOST_SETTING. lia.
Qed.

End e.
End f.
End d.
