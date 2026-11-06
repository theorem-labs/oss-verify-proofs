(* fs program part, lane ENTRY, segment S2 of the LLVMFuzzerTestOneInput walk (fs.asan 0x80f88-0x81024) against
   FSH_Fn_entry.v fs_entry_goal: from the resume after __asan_stack_malloc_0 (FSW_entry_defs.v ss_B2 / INV_B2) to the
   return of memchr(data, 0, size) (fe_ss RA_memchr [] / INV_C1). rule 24: no function proved here (fs's own harness
   entry, written in the donor cgif_file_fuzzer's form; `proof-index LLVMFuzzerTestOneInput` covers other units'
   harnesses only).
   The code (dis fs.asan): `mv s2, a0; j; mv s8, s2; bnez s2` (taken: the granted frame is at least 4096, so the
   real-stack fallback 0x80f9c-0x80fb4 is dead), `sd s8, 0(s1)`, the frame header words at s8 + 0 / 8 / 16,
   `srli s9, s8, 3; add s9, s9, s6`, the eight shadow stores f1 f1 f1 f1 f8 f3 f3 f3 at s9 + 0 .. 7, then
   memchr(data, 0, size) at 0x81020 (PC_memchr, ra 0x81024).
   Method: one engine run to 0x80ff0 (FSW_K fsw_run_to_AJU); s9 re-expressed as the extra atom 45 (fe_SF, YI08
   st_ok_set_reg) and the frame's 8 shadow bytes added as a region at it (YI0n st_ok_add_region', region facts from
   AR_frames_law as in FSW_frame.fsw_readd_frame_regions); a second run to PC_memchr; the call is FsEntryRt's fe_memchr at
   FSW_K fsw_ecall_preU_k_at, its journal put back by FSW_K fsw_intrin_atU (window: memchr's stack window below sp);
   the canonical state at the return by FSW_entry_canon.fe_canon.
   Ported from: a Theorem Labs lane's crcs lane, a working branch c4bfd3bc057,
   lib/A/FSH_check_reject_clean_starved.v:91-150 (crcs_img_keep, crcs_glob_img, crcs_roP_img, crcs_glob_keep): the image
   byte facts, here as s2_img_keep, s2_glob_img, s2_roP_img, s2_stat_keep. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YC5d YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YG0s YE01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_frame3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
ACfn FSH_Harness FSH_Fn_entry FSW_entry_defs FSW_entry_canon.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the symbolic states of the two runs (the engine's own output, vm_compute) ---- *)
Definition s2_ss1 : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs entry_tbl FUEL 0x80ff0 ss_B2).
(* the frame's 8 shadow bytes, at the extra atom 45 (fe_SF) *)
Definition s2_sh_region : YP09.region := YP09.mkRegion (Some 45%nat) 0 8 0 8 [].
Definition s2_ss1' : sstate :=
  mkSS (ss_pc s2_ss1) (sr_set (ss_regs s2_ss1) 25%bv (SOff 45 0)) (s2_sh_region :: ss_mem s2_ss1)
    (ss_resv s2_ss1) (ss_facts s2_ss1).
Definition s2_ss2 : sstate := Eval vm_compute in fst (sym_run_toN tfibsegs entry_tbl FUEL PC_memchr s2_ss1').
Lemma s2_run1 : sym_run_toN tfibsegs entry_tbl FUEL 0x80ff0 ss_B2 = (s2_ss1, RS_running).
Proof. vm_compute. reflexivity. Qed.
Lemma s2_run2 : sym_run_toN tfibsegs entry_tbl FUEL PC_memchr s2_ss1' = (s2_ss2, RS_running).
Proof. vm_compute. reflexivity. Qed.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ---- image facts ---- *)
(* fuzz/alloc.c's statics are image bytes (the last RW segment [0xa1000, 0x5fd000) of tfibsegs) *)
Lemma s2_glob_img : forall a, (G_FAIL <= a < G_FAIL + 8 \/ G_LIVE <= a < G_LIVE + 8 \/ G_PEAK <= a < G_PEAK + 8 \/
  G_COUNT <= a < G_COUNT + 8) -> in_img tfibsegs a.
Proof.
intros a Ha.
assert (Hx : existsb (fun s => (Z.of_N (seg_base s) <=? 0xa1000) && (0x5fd000 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
  tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hx as (sg & Hin & Hc). apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hin|]. unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT in Ha. lia.
Qed.
Lemma s2_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & H1 & H2). apply s2_glob_img. unfold FS_PSTAT_FP in Hr.
unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in H1, H2; lia.
Qed.
Lemma s2_pstat_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof. apply sink_closed_pos. unfold FS_PSTAT_FP. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.
(* every read-only byte arodata_okP speaks of is an image byte below the statics *)
Lemma s2_roP_img : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> in_img tfibsegs a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr]|].
assert (Hx : existsb (fun s => (Z.of_N (seg_base s) <=? 0x9f000) && (0xa1000 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
  tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hx as (sg & Hin & Hc). apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hin|]. unfold FS_RLO, FS_RHI in Hr. lia.
Qed.
Lemma s2_roP_low : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> a < 0xa1000.
Proof.
intros a [(sg & Hin & Hw & Hr) | Hr]; [|unfold FS_RLO, FS_RHI in Hr; lia].
assert (Hx : forallb (fun s => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 0xa1000)) tfibsegs = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hx sg Hin) as Hs. cbv beta in Hs. rewrite Hw in Hs. cbn [orb] in Hs.
apply Z.leb_le in Hs. lia.
Qed.
Lemma s2_roP_notFP : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
intros a Ha (r & Hr & H1 & H2). pose proof (s2_roP_low a Ha) as Hl. unfold FS_PSTAT_FP in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in H1, H2; lia.
Qed.
(* a run's stores outside the image leave every image byte unchanged *)
Lemma s2_img_keep : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> (forall a, in_wrange E rs a -> ~ in_img tfibsegs a) ->
  forall a, in_img tfibsegs a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
intros E rs m m' HF Hw a Ha. apply HF. pose proof (fs_segs_img a Ha) as Hb.
rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold FS_IMG_END in Hb; change (bv_modulus 64) with (2 ^ 64); lia).
intros Hin. exact (Hw a Hin Ha).
Qed.
Lemma s2_frame_img : forall E rs (H : word -> bool) m m',
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> ~ in_img tfibsegs a) ->
  forall a, in_img tfibsegs a -> mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros E rs H m m' HF Hw a Ha. unfold mbyte. rewrite (s2_img_keep E rs _ _ HF Hw a Ha). reflexivity.
Qed.
(* fs_stat survives any memory change that keeps the image bytes *)
Lemma s2_stat_keep : forall (W : world tfibsegs) m m' live cnt,
  (forall a, in_img tfibsegs a -> mbyte tfibsegs (mrestrict (w_H W) m') a = mbyte tfibsegs (mrestrict (w_H W) m) a) ->
  fs_stat tfibsegs W m live cnt -> fs_stat tfibsegs W m' live cnt.
Proof.
intros W m m' live cnt Hk (peak & G1 & G2 & G3 & G4 & R). exists peak.
assert (VB : forall g v, (G_FAIL <= g /\ g + 8 <= G_FAIL + 8 \/ G_LIVE <= g /\ g + 8 <= G_LIVE + 8 \/
    G_PEAK <= g /\ g + 8 <= G_PEAK + 8 \/ G_COUNT <= g /\ g + 8 <= G_COUNT + 8) ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W) m') g 8 v).
{ intros g v Hg Hv k Hkk. rewrite Hk by (apply s2_glob_img; lia). exact (Hv k Hkk). }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [lia | exact G1]|]. split; [apply VB; [lia | exact G2]|].
split; [apply VB; [lia | exact G3]|]. split; [apply VB; [lia | exact G4]|]. exact R.
Qed.

(* ---- small facts ---- *)
Lemma s2_zfind_lt : forall c l k, zfind c l = Some k -> (k < length l)%nat.
Proof.
intros c l. induction l as [|x t IH]; intros k H; cbn in H; [discriminate|].
destruct (x =? c); [injection H as <-; cbn; lia|].
destruct (zfind c t) as [j|] eqn:Ej; cbn in H; [injection H as <-; cbn; specialize (IH j eq_refl); lia | discriminate].
Qed.
Lemma s2_mchr_len : forall c l, 0 <= mchr_len c l <= Z.of_nat (length l) /\
  (0 < Z.of_nat (length l) -> 0 < mchr_len c l).
Proof.
intros c l. unfold mchr_len. destruct (zfind c l) as [k|] eqn:E; [|lia].
pose proof (s2_zfind_lt c l k E). lia.
Qed.
Lemma s2_reg : forall (H : word -> bool) E ss ms (r : bv 5) n,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> YK11.getr (ms_regs ms) r = ew E n.
Proof. intros H E ss ms r n HS Hr. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. apply fsw_SOff0. Qed.
Lemma s2_rdword_of_val : forall (H : word -> bool) mem a v, 0 <= v < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict H mem) a 8 v -> rdword (aview tfibsegs H mem) a = Some v.
Proof.
intros H mem a v Hv Hm.
assert (K : forall k : nat, (k < 8)%nat -> aview tfibsegs H mem (a + Z.of_nat k) = Some (YG0f.le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hm k Hk). cbn [option_map]. f_equal.
  change (YO0f.le_byte v 8 k) with (YG0f.le_byte v 8 k).
  assert (Hr : 0 <= YG0f.le_byte v 8 k < 256) by (unfold YG0f.le_byte; apply Z.mod_pos_bound; lia).
  rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. change (bv_modulus 8) with 256. lia. }
unfold rdword.
pose proof (K 0%nat ltac:(lia)) as H0. pose proof (K 1%nat ltac:(lia)) as H1. pose proof (K 2%nat ltac:(lia)) as H2.
pose proof (K 3%nat ltac:(lia)) as H3. pose proof (K 4%nat ltac:(lia)) as H4. pose proof (K 5%nat ltac:(lia)) as H5.
pose proof (K 6%nat ltac:(lia)) as H6. pose proof (K 7%nat ltac:(lia)) as H7.
cbv [Z.of_nat Pos.of_succ_nat Pos.succ] in H0, H1, H2, H3, H4, H5, H6, H7. rewrite Z.add_0_r in H0.
rewrite H0, H1, H2, H3, H4, H5, H6, H7. f_equal. apply YG0s.le_bytes8. exact Hv.
Qed.
(* the saved words read the same under two envs carrying fe_extra, on two memories that agree on the save area *)
Lemma s2_sv_keep : forall cx E E' m m' base,
  fe_E cx E -> fe_E cx E' ->
  (forall a, base - 88 <= a < base -> mbyte tfibsegs m' a = mbyte tfibsegs m a) ->
  Forall (YP09.chunk_ok tfibsegs E m base) fe_sv_chunks -> Forall (YP09.chunk_ok tfibsegs E' m' base) fe_sv_chunks.
Proof.
intros cx E E' m m' base HE HE' Hm H. unfold fe_sv_chunks in *. rewrite Forall_map in H |- *.
rewrite Forall_forall in *. intros k Hk. pose proof (H k Hk) as Hc. apply in_seq in Hk.
intros i Hi. destruct (Hc i Hi) as (b & Hb & Hmb). exists b.
cbn [cbyte YP09.c_val YP09.c_off YP09.c_len cv_len] in Hb, Hmb, Hi |- *.
split.
- rewrite fsw_SOff0 in Hb |- *.
  assert (Ek : ew E' (33 + k) = ew E (33 + k)).
  { replace (33 + k)%nat with (32 + (1 + k))%nat by lia. rewrite (HE (1 + k)%nat), (HE' (1 + k)%nat) by lia. reflexivity. }
  rewrite Ek. exact Hb.
- rewrite Hm; [exact Hmb|]. lia.
Qed.
End h.

Ltac s2_cs := unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
  let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis fe_mch : amemchr_realizesU tfibsegs B PC_memchr.

(* arodata at any state of a journal from the entry over FS_PSTAT_FP: the read-only bytes are image bytes outside it *)
Lemma s2_arodata_journal : forall STK sp0 ly S (W : world tfibsegs) mem md own ly' S' W' mem' md' k,
  ajournal tfibsegs B STK sp0 FS_PSTAT_FP ly S W mem md own ly' S' W' mem' md' k ->
  YE01.arodata_okS tfibsegs B FS_RLO FS_RHI (aview tfibsegs (w_H W) mem) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem').
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ HR a Ha Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a (s2_roP_img a Ha) Ho He (s2_roP_notFP a Ha) (fp_spares_closed FS_PSTAT_FP a s2_pstat_closed)).
exact (HR a Ha Ho He).
Qed.

Lemma fe_seg2 : forall POST,
  fe_from B FS_PSTAT_FP POST (fe_ss RA_memchr []) (INV_C1 B) ->
  fe_from B FS_PSTAT_FP POST ss_B2 (INV_B2 B).
Proof.
intros POST HN cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HI HS.
destruct HI as (-> & -> & Eab & Enev & Ebb & _ & E8 & E9 & E2 & E10 & E19 & E20 & E22 & E3 & E4 & E26 & E27 & _ & _
  & Hstat).
pose proof HB as (Hpre & _).
destruct Hpre as (HAFN & _ & Hp & Hn & Hpn & Hlen & Hg8 & Hfr0 & _ & _ & Hro & _).
pose proof HAFN as (HAR0 & _ & _ & Hgp & Htp & _).
pose proof (fsw_sp_pre B LLVMF_STK _ _ _ _ _ _ _ HAFN) as (Hal16 & Hceil & H47 & _).
change (spZ (c_regs cx)) with (fe_sp0 cx) in Hal16, Hceil, H47.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : LLVMF_STK = 32768) by reflexivity.
(* memchr's stack bound over the definitions, not its value: fsw_ecall_preU_k_at's `0 <= STK1` and
   `STK1 - o <= LLVMF_STK` at o = sp1 - sp0 >= -127, which also puts memchr's window [sp1 - STK_RT_STR, sp1) above
   alloc_ceiling (so above every image, heap and fake-frame byte) *)
assert (HSTR : 0 <= STK_RT_STR /\ STK_RT_STR + 127 <= LLVMF_STK) by (split; apply Z.leb_le; vm_compute; reflexivity).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
set (sp0 := fe_sp0 cx) in *. set (sp1 := fe_sp1 cx) in *.
pose proof (fsw_realign_facts (sp0 - 96) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (S1 & S2 & S3x).
change (32 * ((sp0 - 96) / 32)) with sp1 in S1, S2, S3x.
(* the frame: atom 10, at least 4096, in the application range *)
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
assert (Hin0 : In (0, c_fpos cx) (frames S3)) by (rewrite Hfrs, Hfr0; left; reflexivity).
assert (ELY : ly_F ly3 = ly_F (c_ly cx)) by (destruct Hly as (_ & _ & _ & _ & _ & L & _); exact L).
assert (EF : frame_addr ly3 0 (c_fpos cx) = fe_F cx) by (unfold fe_F, frame_addr; rewrite ELY; reflexivity).
assert (EFL : flag_addr ly3 0 (c_fpos cx) = fe_FL cx) by (unfold fe_FL, flag_addr; rewrite ELY; reflexivity).
pose proof (ARU_AR tfibsegs B ly3 S3 [] W3 (ms_mem ms3) md3 HARU) as HAR3.
destruct (al_frames _ _ (AR_laws_ok tfibsegs B) ly3 S3 W3 _ md3 0 (c_fpos cx) HAR3 Hin0) as (Hal32 & Happ & _ & _).
destruct (frames_bounds tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 _ md3 0 (c_fpos cx) HAR3 Hin0) as (H4096 & Hfc & _).
destruct (al_flag _ _ (AR_laws_ok tfibsegs B) ly3 S3 W3 _ md3 0 (c_fpos cx) HAR3 Hin0) as (_ & _ & Hflapp & Hflc).
rewrite EF in Hal32, Happ, H4096, Hfc. rewrite Hfb in Happ, Hfc. rewrite EFL in Hflapp, Hflc.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ, Hflapp.
set (F := fe_F cx) in *.
assert (ESF : fe_SF cx = SHADOW_OFF + F / 8) by reflexivity.
assert (HSF1 : SHADOW_OFF + F / 8 + 8 <= kHighMemBeg) by (unfold SHADOW_OFF; rewrite C3; Z.div_mod_to_equations; lia).
(* the atoms *)
assert (E44 : ew E 44 = Z_to_bv 64 (fe_FL cx)) by exact (HE 12%nat ltac:(lia)).
assert (E45 : ew E 45 = Z_to_bv 64 (fe_SF cx)) by exact (HE 13%nat ltac:(lia)).
assert (V8 : bv_unsigned (ew E 8) = sp0) by (rewrite E8; apply wz; lia).
assert (V9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply wz; lia).
assert (V2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2; apply wz; lia).
assert (V10 : bv_unsigned (ew E 10) = F) by (rewrite E10; apply wz; lia).
assert (V45 : bv_unsigned (ew E 45) = SHADOW_OFF + F / 8)
  by (rewrite E45, ESF; apply wz; unfold SHADOW_OFF in *; Z.div_mod_to_equations; lia).
assert (Hsp1x : 0 <= sp1) by lia.
(* the run's write ranges are allowed bytes of the journal, and hold no image byte *)
assert (AW : forall a, (sp0 - 88 <= a < sp0 \/ sp1 <= a < sp1 + 8 \/ F <= a < F + 64 \/
    SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8) ->
  awr_byte tfibsegs B LLVMF_STK sp0 FS_PSTAT_FP (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(0, c_fpos cx)]
    (frames (c_S cx)) a).
{ intros a Ha. unfold awr_byte. left. unfold awr_byte0. rewrite HSTK.
  destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [left; lia | left; lia | |].
  - right; right; right. exists 0, (c_fpos cx). split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite EF, Hfb. lia.
  - right; right; right. exists 0, (c_fpos cx). split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
    rewrite EF, Hfb. unfold shadow_addr. change (64 / 8) with 8. lia. }
assert (NI : forall a, (sp0 - 88 <= a < sp0 \/ sp1 <= a < sp1 + 8 \/ F <= a < F + 64 \/
    SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8) -> ~ in_img tfibsegs a).
{ intros a Ha Hi. pose proof (fs_segs_img a Hi) as Hb. unfold FS_IMG_END in Hb.
  destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [lia | lia | | unfold SHADOW_OFF in Ha; lia].
  exact (frm_img tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 _ md3 0 (c_fpos cx) a HAR3 Hin0
    ltac:(rewrite EF, Hfb; lia) Hi). }
(* ---- run 1: 0x80f88 -> 0x80ff0 ---- *)
eapply (fsw_run_to_AJU B entry_tbl entry_tbl_ok W3 FUEL 0x80ff0 E ss_B2 s2_ss1 RS_running ms3
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS s2_run1 I HARU HJ).
{ intros a (r & Hin & Hr). apply AW.
  unfold ss_B2, fsw_resume_ss, fsw_resume_regions in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
    rewrite ?V8, ?V9, ?V10 in Hr; rewrite ?Hfb in Hr; lia. }
intros ms1 mat1 HS1 HJ1 HARU1 _ HFr1 _.
remember (with_vm_backing (m_vm_lazy md3) mat1 md3) as md1 eqn:Emd1. clear Emd1.
assert (Hstat1 : fs_stat tfibsegs W3 (ms_mem ms1) (c_live cx) (c_cnt cx)).
{ apply (s2_stat_keep W3 (ms_mem ms3)); [|exact Hstat].
  apply (s2_frame_img E (ss_mem ss_B2) (w_H W3) _ _ HFr1).
  intros a (r & Hin & Hr). apply NI.
  unfold ss_B2, fsw_resume_ss, fsw_resume_regions in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]]; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
    rewrite ?V8, ?V9, ?V10 in Hr; rewrite ?Hfb in Hr; lia. }
clear HFr1 Hstat HS HJ HARU HAR3.
(* ---- s9 := the shadow atom, and the frame's shadow region ---- *)
pose proof (ARU_AR tfibsegs B ly3 S3 [] W3 (ms_mem ms1) md1 HARU1) as HAR1.
destruct (al_frames _ _ (AR_laws_ok tfibsegs B) ly3 S3 W3 _ md1 0 (c_fpos cx) HAR1 Hin0) as (_ & _ & _ & Hsh1).
rewrite EF, Hfb in Hsh1. change (64 / 8) with 8 in Hsh1.
assert (HS1a : st_ok tfibsegs E
  (mkSS (ss_pc s2_ss1) (sr_set (ss_regs s2_ss1) 25%bv (SOff 45 0)) (ss_mem s2_ss1) (ss_resv s2_ss1) (ss_facts s2_ss1))
  (restrict (w_H W3) ms1)).
{ apply (st_ok_set_reg tfibsegs E s2_ss1 (restrict (w_H W3) ms1) 25%bv (SOff 45 0) HS1).
  - intros Hc. apply (f_equal bv_unsigned) in Hc. discriminate Hc.
  - change (ms_regs (restrict (w_H W3) ms1)) with (ms_regs ms1).
    rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E s2_ss1 ms1 25%bv HS1).
    change (sr_get (ss_regs s2_ss1) 25%bv) with (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 22 0)).
    apply U_inj. rewrite U_SAlu, U_srl3, (U_atom E 10 F E10) by lia.
    rewrite (U_atom E 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia).
    rewrite (U_atom E 45 (fe_SF cx) E45) by (rewrite ESF; unfold SHADOW_OFF in *; Z.div_mod_to_equations; lia).
    cbn [zalu_raw]. rewrite ESF, (Z.add_comm (F / 8) SHADOW_OFF). apply zcanon_id.
    unfold M64, SHADOW_OFF in *. Z.div_mod_to_equations. lia. }
assert (HS1' : st_ok tfibsegs E s2_ss1' (restrict (w_H W3) ms1)).
{ refine (st_ok_add_region' tfibsegs E _ (restrict (w_H W3) ms1) s2_sh_region HS1a eq_refl _ _).
  - unfold region_ok, s2_sh_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite V45.
    split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF in *; lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable tfibsegs).
    destruct (Hsh1 o Ho) as (Hpo & _). exact Hpo.
  - unfold s2_sh_region, s2_ss1. cbn [ss_mem all_disjoint extent_disjoint base_val YP09.r_base YP09.r_lo YP09.r_hi].
    unfold extent_disjoint. cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite V45, V8, V9, V10. unfold SHADOW_OFF in *. lia. }
clear HS1 HS1a Hsh1 HAR1.
(* ---- run 2: 0x80ff0 -> PC_memchr ---- *)
eapply (fsw_run_to_AJU B entry_tbl entry_tbl_ok W3 FUEL PC_memchr E s2_ss1' s2_ss2 RS_running ms1
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS1' s2_run2 I HARU1 HJ1).
{ intros a (r & Hin & Hr). apply AW.
  unfold s2_ss1', s2_sh_region, s2_ss1 in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
    rewrite ?V8, ?V9, ?V10, ?V45 in Hr; lia. }
intros ms2 mat2 HS2 HJ2 HARU2 _ HFr2 _.
remember (with_vm_backing (m_vm_lazy md1) mat2 md1) as md2 eqn:Emd2. clear Emd2.
assert (Hstat2 : fs_stat tfibsegs W3 (ms_mem ms2) (c_live cx) (c_cnt cx)).
{ apply (s2_stat_keep W3 (ms_mem ms1)); [|exact Hstat1].
  apply (s2_frame_img E (ss_mem s2_ss1') (w_H W3) _ _ HFr2).
  intros a (r & Hin & Hr). apply NI.
  unfold s2_ss1', s2_sh_region, s2_ss1 in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hr;
    rewrite ?V8, ?V9, ?V10, ?V45 in Hr; lia. }
clear HFr2 Hstat1 HS1' HJ1 HARU1.
(* ---- the call memchr(data, 0, size) ---- *)
pose proof (st_ok_restrict_mkst tfibsegs (w_H W3) E s2_ss2 ms2 HS2 eq_refl) as Hshape.
rewrite Hshape. change (ss_pc s2_ss2) with PC_memchr.
set (regsT := ms_regs ms2) in *. set (memT := ms_mem ms2) in *.
assert (R1 : YK11.getr regsT 1%bv = Z_to_bv 64 0x81024)
  by exact (fsw_reg_lit (w_H W3) E s2_ss2 ms2 1%bv 0x81024 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R11 : YK11.getr regsT 11%bv = Z_to_bv 64 0)
  by exact (fsw_reg_lit (w_H W3) E s2_ss2 ms2 11%bv 0 HS2 ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (R10 : YK11.getr regsT 10%bv = ew E 20) by exact (s2_reg (w_H W3) E s2_ss2 ms2 10%bv 20 HS2 eq_refl).
assert (R12 : YK11.getr regsT 12%bv = ew E 19) by exact (s2_reg (w_H W3) E s2_ss2 ms2 12%bv 19 HS2 eq_refl).
assert (R2 : YK11.getr regsT 2%bv = ew E 2) by exact (s2_reg (w_H W3) E s2_ss2 ms2 2%bv 2 HS2 eq_refl).
assert (R3 : YK11.getr regsT 3%bv = ew E 3) by exact (s2_reg (w_H W3) E s2_ss2 ms2 3%bv 3 HS2 eq_refl).
assert (R4 : YK11.getr regsT 4%bv = ew E 4) by exact (s2_reg (w_H W3) E s2_ss2 ms2 4%bv 4 HS2 eq_refl).
assert (R8 : YK11.getr regsT 8%bv = ew E 8) by exact (s2_reg (w_H W3) E s2_ss2 ms2 8%bv 8 HS2 eq_refl).
assert (R9 : YK11.getr regsT 9%bv = ew E 9) by exact (s2_reg (w_H W3) E s2_ss2 ms2 9%bv 9 HS2 eq_refl).
assert (R18 : YK11.getr regsT 18%bv = ew E 10) by exact (s2_reg (w_H W3) E s2_ss2 ms2 18%bv 10 HS2 eq_refl).
assert (R19 : YK11.getr regsT 19%bv = ew E 19) by exact (s2_reg (w_H W3) E s2_ss2 ms2 19%bv 19 HS2 eq_refl).
assert (R20 : YK11.getr regsT 20%bv = ew E 20) by exact (s2_reg (w_H W3) E s2_ss2 ms2 20%bv 20 HS2 eq_refl).
assert (R22 : YK11.getr regsT 22%bv = ew E 22) by exact (s2_reg (w_H W3) E s2_ss2 ms2 22%bv 22 HS2 eq_refl).
assert (R24 : YK11.getr regsT 24%bv = ew E 10) by exact (s2_reg (w_H W3) E s2_ss2 ms2 24%bv 10 HS2 eq_refl).
assert (R25 : YK11.getr regsT 25%bv = ew E 45) by exact (s2_reg (w_H W3) E s2_ss2 ms2 25%bv 45 HS2 eq_refl).
assert (R26 : YK11.getr regsT 26%bv = ew E 26) by exact (s2_reg (w_H W3) E s2_ss2 ms2 26%bv 26 HS2 eq_refl).
assert (R27 : YK11.getr regsT 27%bv = ew E 27) by exact (s2_reg (w_H W3) E s2_ss2 ms2 27%bv 27 HS2 eq_refl).
assert (Hspt : spZ regsT = sp1) by (unfold spZ; rewrite R2; exact V2).
(* the regions the call keeps: the saved words and the frame's flag word *)
pose proof (fsw_region_nth E s2_ss2 (restrict (w_H W3) ms2) 1 _ HS2 eq_refl) as RS1.
pose proof (fsw_region_nth E s2_ss2 (restrict (w_H W3) ms2) 3 _ HS2 eq_refl) as RS3.
cbn [ms_mem restrict] in RS1, RS3. fold memT in RS1, RS3.
assert (Hsv2 : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) memT) sp0) fe_sv_chunks).
{ destruct RS1 as (_ & _ & _ & Hcs). cbn [YP09.r_chunks YP09.r_base base_val] in Hcs. rewrite V8 in Hcs. exact Hcs. }
assert (Hfl2 : val_mem tfibsegs (mrestrict (w_H W3) memT) (F + 56) 8 (fe_FL cx)).
{ refine (fsw_field E (mrestrict (w_H W3) memT) 10 F _ 0 64 0 64 56 8 (SOff 44 0) (fe_FL cx) RS3 V10 _ _ _ _).
  - cbn [In]. right; right; right; left. reflexivity.
  - rewrite fsw_SOff0. exact E44.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - lia. }
clear RS1 RS3.
(* the journal's reading at the call: arodata, rom_view, the payload *)
pose proof (ARU_AR tfibsegs B ly3 S3 [] W3 memT md2 HARU2) as HAR2.
assert (HRO2 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W3) memT))
  by exact (s2_arodata_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 Hro).
destruct (proj2 IMG ly3 S3 W3 memT md2 HAR2 HRO2) as (HROM & _).
assert (Hlen' : Z.of_nat (length (fe_bytes cx)) = c_n cx) by (unfold fe_bytes; rewrite length_map; lia).
assert (Hnot : forall i, 0 <= i < c_n cx -> 0 < c_n cx -> ~ inFP FS_PSTAT_FP (c_p cx + i)).
{ intros i Hi Hn0 Hf. destruct Hpn as [(Hz & _) | (_ & HinB)]; [lia|].
  apply (blk_img tfibsegs B (AR_laws_ok tfibsegs B) _ _ _ _ _ (c_p cx) (c_n cx) (c_p cx + i) HAR0 HinB);
    [unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia | exact (s2_pstat_img _ Hf)]. }
assert (Hkeep : forall ly' S' W' mem' md' k' own',
  ajournal tfibsegs B LLVMF_STK sp0 FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own' ly' S' W' mem' md' k' ->
  ablocks B ly' S' = ablocks B (c_ly cx) (c_S cx) ->
  forall i, 0 <= i < c_n cx -> aview tfibsegs (w_H W') mem' (c_p cx + i) = aview tfibsegs (w_H (c_W cx)) (c_mem cx) (c_p cx + i)).
{ intros ly' S' W' mem' md' k' own' HJx Eabx i Hi.
  destruct Hpn as [(Hz & _) | (_ & HinB)]; [lia|].
  pose proof HJx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  apply (F2 (c_p cx) (c_n cx) i HinB); [rewrite Eabx; exact HinB | unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia
    | exact (Hnot i Hi ltac:(lia))]. }
assert (Hzb : zbytes_at tfibsegs W3 memT (c_p cx) (fe_bytes cx)).
{ unfold zbytes_at, fe_bytes. apply (garr8_frame tfibsegs _ _ _ _ Hg8). intros a Ha. rewrite length_map, <- Hlen in Ha.
  replace a with (c_p cx + (a - c_p cx)) by lia. apply (mbyte_of_aview tfibsegs).
  exact (Hkeep _ _ _ _ _ _ _ HJ2 Eab (a - c_p cx) ltac:(lia)). }
assert (HDATA : 4096 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\ amem_range (c_p cx) (c_n cx + 8) /\
  range_addressable (aview tfibsegs (w_H W3) memT) SHADOW_OFF (c_p cx) (mchr_len 0 (fe_bytes cx)) /\
  (0 < c_n cx -> shadow_hull_vis (aview tfibsegs (w_H W3) memT) (c_p cx) (mchr_len 0 (fe_bytes cx)))).
{ pose proof (s2_mchr_len 0 (fe_bytes cx)) as (ML1 & ML2). rewrite Hlen' in ML1, ML2.
  destruct Hpn as [(Hz & Hpe) | (Hnr & HinB)].
  - rewrite Hz, Hpe in *. unfold A_EMPTY, amem_range, kLowMemEnd.
    split; [lia|]. split; [lia|]. split; [left; lia|]. split; [intros x Hx; lia | intros; lia].
  - rewrite <- Eab in HinB.
    destruct (al_blocks _ _ (AR_laws_ok tfibsegs B) ly3 S3 W3 memT md2 (c_p cx) (c_n cx) HAR2 HinB)
      as (_ & Hb1 & Hb2 & Hb3 & _).
    assert (Hreq : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
    rewrite Hreq in Hb2, Hb3.
    split; [lia|]. split; [lia|].
    split; [unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in *; lia|].
    split.
    + apply (range_addressable_of_block tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 memT md2 (c_p cx) (c_n cx));
        [exact HAR2 | exact HinB | lia | rewrite Hreq; lia].
    + intros Hn0. apply (shadow_hull_vis_of_block tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 memT md2 (c_p cx) (c_n cx));
        [exact HAR2 | exact HinB | lia | rewrite Hreq; lia | lia]. }
destruct HDATA as (Hx1 & Hx2 & Ham & Hrax & Hhull).
assert (Hnr : 0 <= c_n cx < 2 ^ 32) by (destruct Hpn as [(Hz & _) | (Hnr & _)]; lia).
assert (HPRE : ecall_preU_k tfibsegs B STK_RT_STR ly3 S3 [] W3 regsT memT md2).
{ apply (fsw_ecall_preU_k_at B LLVMF_STK sp0 FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly3 S3 [] W3 memT md2 0 regsT (sp1 - sp0) STK_RT_STR HJ2 HARU2).
  - rewrite Hspt. lia.
  - rewrite Zminus_mod, Hal16, S3x. reflexivity.
  - lia.
  - change ESTACK with 4096. lia.
  - lia.
  - lia.
  - rewrite R1. vm_compute. reflexivity.
  - rewrite R3, E3. exact Hgp.
  - rewrite R4, E4. exact Htp. }
assert (Hx' : YK11.getr regsT 10%bv = w64 (c_p cx)) by (rewrite R10, E20; exact Hp).
assert (Hn' : YK11.getr regsT 12%bv = w64 (c_n cx)) by (rewrite R12, E19; exact Hn).
set (Wr := fun a => spZ regsT - STK_RT_STR <= a < spZ regsT).
set (Qm := fun (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) =>
  aregs_preserved regsT regs' /\ YK11.getr regs' 10%bv = w64 (fe_memchr_res cx) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H W3) mem' a = aview tfibsegs (w_H W3) memT a)).
eapply SRr_bind.
{ apply (fsw_intrin_atU B LLVMF_STK sp0 FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly3 S3 [] W3 memT md2 0 [] Wr (YK11.getr regsT 1%bv) _ Qm HJ2).
  - eapply SRr_mono.
    + exact (fe_mch ly3 S3 [] W3 regsT memT md2 (c_p cx) 0 (c_n cx) (fe_bytes cx) HPRE HROM Hx'
        R11 ltac:(lia) Hn' Hnr Hzb Hlen' Hx1 Hx2 Ham Hrax Hhull).
    + intros W' c' _ (-> & regs' & mem' & md' & v & -> & HARx & HPOx & HPx & Hsbm & Hv10 & Hvr & HR & Hfrx & Hprx).
      split; [reflexivity|]. exists regs', mem', md'.
      split; [unfold cfg_at, raZ, YG0d.w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
      split; [split; [exact HARx | split; [exact (ARU_ok tfibsegs B _ _ _ _ _ _ HARU2) | exact HPOx]]|].
      split; [exact Hsbm|]. split; [exact Hfrx|]. split; [exact Hprx|].
      split; [exact HPx|]. split; [|exact Hfrx].
      rewrite Hv10. unfold fe_memchr_res. destruct (zfind 0 (fe_bytes cx)); rewrite HR; reflexivity.
  - intros a Ha. unfold Wr in Ha. rewrite Hspt in Ha. unfold awr_byte. left. unfold awr_byte0. left.
    rewrite HSTK. lia. }
intros W' c' _ (-> & regs2 & mem2 & md3' & -> & HJ3 & HARU3 & HP3 & H10 & Hfr3).
rewrite R1.
assert (P : forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr regs2 r = YK11.getr regsT r)
  by (intros r Hr; exact (fsw_pres regsT regs2 r HP3 Hr)).
assert (G8 : YK11.getr regs2 8%bv = Z_to_bv 64 sp0)
  by (rewrite P by s2_cs; rewrite R8; exact E8).
assert (G9 : YK11.getr regs2 9%bv = Z_to_bv 64 sp1)
  by (rewrite P by s2_cs; rewrite R9; exact E9).
assert (G2 : YK11.getr regs2 2%bv = Z_to_bv 64 sp1)
  by (rewrite P by s2_cs; rewrite R2; exact E2).
assert (G18 : YK11.getr regs2 18%bv = Z_to_bv 64 F)
  by (rewrite P by s2_cs; rewrite R18; exact E10).
assert (G24 : YK11.getr regs2 24%bv = Z_to_bv 64 F)
  by (rewrite P by s2_cs; rewrite R24; exact E10).
assert (G25 : YK11.getr regs2 25%bv = Z_to_bv 64 (fe_SF cx))
  by (rewrite P by s2_cs; rewrite R25; exact E45).
assert (G3 : YK11.getr regs2 3%bv = YK11.getr (c_regs cx) 3%bv)
  by (rewrite P by s2_cs; rewrite R3; exact E3).
assert (G4 : YK11.getr regs2 4%bv = YK11.getr (c_regs cx) 4%bv)
  by (rewrite P by s2_cs; rewrite R4; exact E4).
assert (G26 : YK11.getr regs2 26%bv = YK11.getr (c_regs cx) 26%bv)
  by (rewrite P by s2_cs; rewrite R26; exact E26).
assert (G27 : YK11.getr regs2 27%bv = YK11.getr (c_regs cx) 27%bv)
  by (rewrite P by s2_cs; rewrite R27; exact E27).
assert (G19 : YK11.getr regs2 19%bv = Z_to_bv 64 (c_n cx))
  by (rewrite P by s2_cs; rewrite R19, E19; exact Hn).
assert (G20 : YK11.getr regs2 20%bv = Z_to_bv 64 (c_p cx))
  by (rewrite P by s2_cs; rewrite R20, E20; exact Hp).
assert (G22 : YK11.getr regs2 22%bv = Z_to_bv 64 SHADOW_OFF)
  by (rewrite P by s2_cs; rewrite R22; exact E22).
(* the call kept every byte below its stack window *)
assert (K3 : forall a, 0 <= a < sp1 - STK_RT_STR ->
  mbyte tfibsegs (mrestrict (w_H W3) mem2) a = mbyte tfibsegs (mrestrict (w_H W3) memT) a).
{ intros a Ha. apply (mbyte_of_aview tfibsegs). apply Hfr3; [lia|]. unfold Wr. rewrite Hspt. lia. }
assert (K3' : forall a, sp1 <= a < 2 ^ 64 ->
  mbyte tfibsegs (mrestrict (w_H W3) mem2) a = mbyte tfibsegs (mrestrict (w_H W3) memT) a).
{ intros a Ha. apply (mbyte_of_aview tfibsegs). apply Hfr3; [lia|]. unfold Wr. rewrite Hspt. lia. }
set (E' := Ereg regs2 (fe_extra cx ++ [])).
apply (HN cx E' 0 ly3 S3 [] W3 (YK11.mkst regs2 (Z_to_bv 64 0x81024) mem2 (YK11.seg_rom tfibsegs)) md3' HB
  (fe_E_Ereg cx regs2 [])).
- exact HJ3.
- exact HARU3.
- (* INV_C1 *)
  unfold INV_C1.
  assert (EE : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E' n = YK11.getr regs2 r)
    by (intros n r Hr; exact (ew_Ereg_nat regs2 _ n r Hr)).
  split; [reflexivity|]. split; [exact Eab|]. split; [exact Enev|]. split; [exact Ebb|].
  split.
  { split; [lia|]. split.
    - pose proof HJ3 as (_ & _ & _ & _ & Hio3 & _). exact (aos_step_closed_same_io FS_PSTAT_FP _ _ s2_pstat_closed Hio3).
    - split; [exact (Hkeep _ _ _ _ _ _ _ HJ3 Eab) | lia]. }
  split.
  { unfold fe_regs_core.
    rewrite (EE 8%nat 8%bv), (EE 9%nat 9%bv), (EE 2%nat 2%bv), (EE 18%nat 18%bv), (EE 24%nat 24%bv), (EE 25%nat 25%bv),
      (EE 3%nat 3%bv), (EE 4%nat 4%bv), (EE 26%nat 26%bv), (EE 27%nat 27%bv) by reflexivity.
    rewrite G8, G9, G2, G18, G24, G25, G3, G4, G26, G27. repeat split; reflexivity. }
  rewrite (EE 10%nat 10%bv), (EE 19%nat 19%bv), (EE 20%nat 20%bv), (EE 22%nat 22%bv) by reflexivity.
  rewrite H10, G19, G20, G22. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  apply (s2_stat_keep W3 memT); [|exact Hstat2].
  intros a Ha. pose proof (fs_segs_img a Ha) as Hb. unfold FS_IMG_END in Hb. apply K3. lia.
- (* the canonical state at the return *)
  assert (Hpres3 : forall a, sp0 - 88 <= a < sp0 -> apresent (w_H W3) mem2 a).
  { pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr & _).
    intros a Ha. apply Hpr. rewrite HSTK. lia. }
  assert (Hsv3 : Forall (YP09.chunk_ok tfibsegs E' (mrestrict (w_H W3) mem2) sp0) fe_sv_chunks).
  { apply (s2_sv_keep cx E E' (mrestrict (w_H W3) memT) (mrestrict (w_H W3) mem2) sp0 HE (fe_E_Ereg cx regs2 [])).
    - intros a Ha. apply K3'. lia.
    - exact Hsv2. }
  assert (Hflag3 : rdword (aview tfibsegs (w_H W3) mem2) (F + 56) = Some (fe_FL cx)).
  { apply s2_rdword_of_val; [lia|]. intros j Hj. rewrite K3 by lia. exact (Hfl2 j Hj). }
  exact (fe_canon B cx ly3 S3 [] W3 mem2 md3' regs2 [] RA_memchr [] HARU3 Hin0 ELY G8 G24 G18 G25 Hal16
    ltac:(rewrite HSTK in Hceil; lia) H47 Hpres3 Hsv3 Hflag3 fe_regions_wf_nil (Forall_nil _) (Forall_nil _)).
Qed.
End s.
