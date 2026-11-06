(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 1266 of its 1332 lines of code are new or changed and 1014 lines of the source are left out. *)
(* preset_base64_decode (fs.asan 0x8481c), part E of the walk (a Theorem Labs lane): the entry to the loop head,
   `dec_entry_ok_stage : dec_stage_entry B CTX` (FSW_dec_defs.v). The prologue and strlen (text) by the engine and
   strlen's contract, fuzz_malloc (dec_size tb) by its contract, then
   - a refused allocation returns 0: dec_post's first arm (decE_null, sub-part N);
   - a granted one reaches the loop head 0x848bc with nothing read, dec_head ... 0 [] 0 0, and the stage's
     continuation takes over (decE_nonnull, sub-part Q);
   the caller's objects (the value at lenp, the window slack, the text, the read-only view) survive fuzz_malloc (decE_kept_malloc,
   sub-part K); decE_spine is the run from the entry to the resumed state at 0x84880 (decE_res) in both arms.
   The walk's journal has its window top at the ENTRY sp (window [sp - STK, sp)), so that every resume after a call
   (fsw_resume_after_rtU_args, fsw_after_callFPU_args: frame [sp0 - f, sp0)) is at the function's own 112-byte frame;
   it is widened to dec_J's raised top ot (decE_widen) only at the ends of the part, where the bytes [sp, ot) are
   present again (wkeep / *lenp's value).
   Section hypotheses: HSS, HIMG (constant facts about B), HSTRLEN, HMALLOC (callee contracts). No trace premise at the
   fuzz_malloc call: fuzz_malloc_spec dropped its CTX premise (ALLOC, a Theorem Labs lane, with the writer specs' drop, owner
   a Theorem Labs lane 05:00Z). Over RELOC's FP-keyed core the resume after the program call is
   FSW_K3's PROVED fsw_after_callFPU_args, not a copied statement.
   Rule 24 (a Theorem Labs lane, 2026-10-28T22:32Z; proof-index v5 built 2026-10-28T21:58:24Z, exit 0): released proofs
   of preset_base64_decode exist for fs's PLAIN and UBSAN builds only, none for ASan; templates, not drop-ins. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_Fn_writer
FSW_K FSW_K3 FSW_ret FSW_rres FSW_strkit FSW_writer_tbl FSW_writer_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSW_dec_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the resume states after strlen (0x8486c) and fuzz_malloc (0x84880): the 112-byte frame at atom 2 = sp - 112 with
   the 13 saved words (dec_saved: s11 .. s1, s0, ra at sp - 104 .. sp - 8). A saved register the code has changed by the
   call (s5 = the shadow base, s0 = lenp, s2 = text, ra) is an extra atom: xatom 0 .. 3 = entry s5, s0, s2, ra; the others
   are the resumed registers, which hold their entry values ---- *)
Definition decE_xs (d : DE) : list word :=
  [getr (d_regs d) 21; getr (d_regs d) 8; getr (d_regs d) 18; getr (d_regs d) 1].
Definition decE_cs : list YP09.chunk :=
  [YP09.mkChunk 8 (CVal 8 (SOff 27 0)); YP09.mkChunk 16 (CVal 8 (SOff 26 0)); YP09.mkChunk 24 (CVal 8 (SOff 25 0));
   YP09.mkChunk 32 (CVal 8 (SOff 24 0)); YP09.mkChunk 40 (CVal 8 (SOff 23 0)); YP09.mkChunk 48 (CVal 8 (SOff 22 0));
   YP09.mkChunk 56 (CVal 8 (SOff 33 0)); YP09.mkChunk 64 (CVal 8 (SOff 20 0)); YP09.mkChunk 72 (CVal 8 (SOff 19 0));
   YP09.mkChunk 80 (CVal 8 (SOff 35 0)); YP09.mkChunk 88 (CVal 8 (SOff 9 0)); YP09.mkChunk 96 (CVal 8 (SOff 34 0));
   YP09.mkChunk 104 (CVal 8 (SOff 36 0))].
(* the saved registers that hold their entry values across the part *)
Definition decE_kregs : list (bv 5) := [9; 19; 20; 22; 23; 24; 25; 26; 27]%bv.
Section E0. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(* ---- the state right after fuzz_malloc returned, at 0x84880 (both arms): the journal at the entry sp, ARU, the resumed
   symbolic state, the registers the rest of the part reads, and the caller's kept objects ---- *)
Definition decE_res (B : asyms) (d : DE) (W' : world tfibsegs) (ly' : alayout) (S' : astate) (U' : list (Z * Z))
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
  ajournal tfibsegs B STK_preset_base64_decode (d_sp d) (d_FP d) (d_ly d) (d_S d) (d_W d)
    (unpoison (d_U d) (d_mem d)) (d_md d) [] ly' S' W' (unpoison U' mem') md' k /\
  ARU tfibsegs B ly' S' U' W' mem' md' /\
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ decE_xs d)) (fss_retT DEC_RA_MALLOC DEC_F decE_cs [] [])
    (restrict (w_H W') (YK11.mkst regs' (Z_to_bv 64 DEC_RA_MALLOC) mem' (YK11.seg_rom tfibsegs))) /\
  spZ regs' = d_sp d - DEC_F /\ getr regs' 3 = getr (d_regs d) 3 /\ getr regs' 4 = getr (d_regs d) 4 /\
  getr regs' 8 = w64 (d_lenp d) /\ getr regs' 18 = w64 (d_text d) /\ getr regs' 21 = w64 SHADOW_OFF /\
  (forall r, In r decE_kregs -> getr regs' r = getr (d_regs d) r) /\
  dec_kept B d W' mem'.

(* ---- the frame chunks and dec_frame_ok ---- *)
Lemma decE_cs_den : forall d regs, (forall r, In r decE_kregs -> getr regs r = getr (d_regs d) r) ->
  forall j r, nth_error dec_saved j = Some r ->
  exists e, nth_error decE_cs j = Some (YP09.mkChunk (8 + 8 * Z.of_nat j) (CVal 8 e)) /\
    sv_denot (Ereg regs (fs_extraT ++ decE_xs d)) e = getr (d_regs d) r.
Proof.
intros d regs HK j r Hj.
do 13 (destruct j as [|j];
  [cbn in Hj; injection Hj as <-; eexists; split; [reflexivity|];
   rewrite fsw_SOff0;
   first
   [ lazymatch goal with |- ew _ ?n = getr _ ?q => rewrite (ew_Ereg_nat regs _ n q eq_refl) end;
     apply HK; cbv [decE_kregs In]; auto 20
   | lazymatch goal with |- ew _ ?n = _ =>
       let j := eval compute in (n - 32)%nat in change n with (32 + j)%nat end;
     rewrite ew_Ereg_extra; reflexivity ] |]).
cbn in Hj. destruct j; discriminate Hj.
Qed.
Lemma decE_chunks_of_frame : forall d (W : world tfibsegs) m b regs,
  (forall r, In r decE_kregs -> getr regs r = getr (d_regs d) r) ->
  dec_frame_ok W m b (d_regs d) ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs (fs_extraT ++ decE_xs d)) (mrestrict (w_H W) m) b) decE_cs.
Proof.
intros d W m b regs HK HF. apply Forall_forall. intros c Hc.
destruct (In_nth_error _ _ Hc) as (j & Hj).
assert (Hlt : (j < length dec_saved)%nat).
{ apply nth_error_Some. intros E. apply nth_error_None in E. pose proof (nth_error_Some decE_cs j) as [H1 _].
  assert (length decE_cs = length dec_saved) as EL by reflexivity. rewrite Hj in H1. specialize (H1 ltac:(discriminate)). lia. }
destruct (nth_error dec_saved j) as [r|] eqn:Hr; [|apply nth_error_None in Hr; lia].
destruct (decE_cs_den d regs HK j r Hr) as (e & Hc' & He). rewrite Hj in Hc'. injection Hc' as ->.
apply (chunk_ok_val tfibsegs _ _ _ _ 8 e (bv_unsigned (getr (d_regs d) r))).
- rewrite He. symmetry. apply Z_to_bv_bv_unsigned.
- pose proof (u64_range (getr (d_regs d) r)). cbn [Z.of_N]. lia.
- cbn [Z.of_N]. lia.
- replace (b + (8 + 8 * Z.of_nat j)) with (b + 8 + 8 * Z.of_nat j) by lia. exact (HF j r Hr).
Qed.
Lemma decE_frame_of_chunks : forall d (W : world tfibsegs) m b regs,
  (forall r, In r decE_kregs -> getr regs r = getr (d_regs d) r) ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs (fs_extraT ++ decE_xs d)) (mrestrict (w_H W) m) b) decE_cs ->
  dec_frame_ok W m b (d_regs d).
Proof.
intros d W m b regs HK HC j r Hj.
destruct (decE_cs_den d regs HK j r Hj) as (e & Hc & He).
pose proof (proj1 (Forall_forall _ _) HC _ (nth_error_In _ _ Hc)) as Hck.
replace (b + 8 + 8 * Z.of_nat j) with (b + (8 + 8 * Z.of_nat j)) by lia.
apply (val_of_chunk_ok tfibsegs _ _ _ _ 8 e (bv_unsigned (getr (d_regs d) r)) Hck).
- rewrite He. symmetry. apply Z_to_bv_bv_unsigned.
- pose proof (u64_range (getr (d_regs d) r)). cbn [Z.of_N]. lia.
- cbn [Z.of_N]. lia.
Qed.

(* ---- a journal whose window top is the entry sp, widened to a raised top ot once the bytes [sp, ot) are present ---- *)
Lemma decE_widen : forall B STK sp ot FP ly S (W : world tfibsegs) mem md ly' S' (W' : world tfibsegs) mem' md' k,
  ajournal tfibsegs B STK sp FP ly S W mem md [] ly' S' W' mem' md' k ->
  sp <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (forall a, sp <= a < ot -> apresent (w_H W') mem' a) ->
  ajournal tfibsegs B (STK + (ot - sp)) ot FP ly S W mem md [] ly' S' W' mem' md' k.
Proof.
intros B STK sp ot FP ly S W mem md ly' S' W' mem' md' k
  (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & J13 & J14 & J15 & J16 & J17) Hot Hal Htop Hpres.
pose proof J15 as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop0 & Htop2).
unfold ajournal.
repeat (split; [eassumption|]).
split; [intros a Ha Hn; apply J9; [exact Ha | lia]|].
repeat (split; [eassumption|]).
split; [intros a Ha; destruct (Z_lt_le_dec a sp) as [L|L]; [apply J14; lia | apply Hpres; lia]|].
split; [|split; eassumption].
unfold astk_ok. repeat split; lia.
Qed.
End E0.

(* ===== spine helpers ===== *)
Ltac decE_cs_side := unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
  let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.
Ltac decE_in := cbv [In]; repeat (first [left; reflexivity | right]).
Definition decE_csl : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Section S0. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* the frame chunks of the entry state at the strlen call: offsets from the entry sp, atoms of the entry env *)
Definition decE_cs0 : list YP09.chunk :=
  [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
   YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
(* the a0 the code passes to fuzz_malloc: ((len >> 2) << 1) + (len >> 2) + 3 *)
Definition decE_size_sv : sv :=
  SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SAlu ALU_SRL (SOff 10 0) (SLit 2)) (SLit 1))
    (SAlu ALU_SRL (SOff 10 0) (SLit 2))) (SLit 3).
Definition decE_avk (d : DE) (W : world tfibsegs) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> a < alloc_ceiling \/ d_sp d <= a ->
    aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.

Lemma decE_size_den : forall E (len : Z), ew E 10 = Z_to_bv 64 len -> 0 <= len < 2 ^ 32 ->
  sv_denot E decE_size_sv = Z_to_bv 64 (len / 4 * 3 + 3).
Proof.
intros E len H10 Hl. unfold decE_size_sv. apply bv_eq.
assert (D : 0 <= len / 4 <= len) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
change (bv_unsigned (sv_denot E ?x)) with (U E x).
rewrite unsigned_lit_small by lia.
rewrite !U_SAlu, (U_atom E 10 len H10 ltac:(lia)), !U_lit by lia. cbn [zalu_raw].
change (Z.land 2 63) with 2. change (Z.land 1 63) with 1.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
unfold zcanon, M64. rewrite (Z.mod_small (len / 4)) by lia.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
repeat rewrite Z.mod_small by lia. lia.
Qed.

Lemma decE_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z => existsb (fun s => (Z.of_N (seg_base s) <=? fst r) &&
  (snd r <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs) FS_PSTAT_FP = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H. apply existsb_exists in H as (s & Hs & Hss).
apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.


(* a byte whose mbyte is equal and that is no image byte has the same raw (restricted) byte *)
Lemma decE_restrict_of_mbyte : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a ->
  mbyte tfibsegs (mrestrict H' m') a = mbyte tfibsegs (mrestrict H m) a ->
  mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
intros H H' m m' a Ha Hn E. unfold mbyte in E. rewrite (YCbq.seg_rom_none tfibsegs a Ha Hn) in E.
destruct (mrestrict H' m' (Z_to_bv 64 a)), (mrestrict H m (Z_to_bv 64 a)); congruence.
Qed.
(* a byte that keeps its value keeps its writability (wview reads only the byte asked) *)
Lemma decE_writable_eq : forall (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> (writable_at tfibsegs m a <-> writable_at tfibsegs m' a).
Proof. intros m m' a H. unfold writable_at, wview. rewrite H. reflexivity. Qed.

Lemma decE_val_mem_av : forall (W : world tfibsegs) m m' a (n : nat) v,
  (forall i, 0 <= i < Z.of_nat n -> aview tfibsegs (w_H W) m' (a + i) = aview tfibsegs (w_H W) m (a + i)) ->
  val_mem tfibsegs (mrestrict (w_H W) m) a n v -> val_mem tfibsegs (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' a n v Hk Hv k Hk'. rewrite (mbyte_of_aview tfibsegs _ _ _ _ _ (Hk (Z.of_nat k) ltac:(lia))). exact (Hv k Hk').
Qed.

Lemma decE_glob_av : forall (W : world tfibsegs) m m' live peak cnt fail,
  (forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail AV (G1 & G2 & G3 & G4 & R). pose proof asan_consts as (C1 & _).
assert (VB : forall a v, 0 <= a -> a + 8 <= alloc_ceiling -> val_mem tfibsegs (mrestrict (w_H W) m) a 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) m') a 8 v)
  by (intros a v Ha Hb Hv; apply (decE_val_mem_av W m); [intros i Hi; apply AV; cbn in Hi; lia | exact Hv]).
unfold fs_glob, fs_glob_at. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply VB; [lia | lia | exact G1]|].
split; [apply VB; [lia | lia | exact G2]|].
split; [apply VB; [lia | lia | exact G3]|].
split; [apply VB; [lia | lia | exact G4]|].
exact R.
Qed.

Lemma decE_ro_av : forall B (W : world tfibsegs) m m',
  (forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m').
Proof.
intros B W m m' AV HR a Ha Ho He. pose proof asan_consts as (C1 & _).
assert (Hb : 0 <= a < alloc_ceiling).
{ destruct Ha as [(sg & Hin & Hw & Hr) | Hr]; [|unfold FS_RLO, FS_RHI in Hr; lia].
  assert (Hi : in_img tfibsegs a) by (exists sg; split; [exact Hin | exact Hr]).
  pose proof (fs_segs_img a Hi) as Hl. unfold FS_IMG_END in Hl. lia. }
rewrite (AV a Hb). exact (HR a Ha Ho He).
Qed.

Lemma decE_cstr_av : forall (W : world tfibsegs) m m' p l,
  (forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  cstr_ok tfibsegs W m p l -> cstr_ok tfibsegs W m' p l.
Proof.
intros W m m' p l AV H. pose proof asan_consts as (C1 & _).
unfold cstr_ok, cstr in H |- *.
repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
repeat match goal with |- _ /\ _ => split end; try assumption; lazymatch goal with
  | Hg : garr8 _ (mrestrict _ m) p (l ++ [0]) |- garr8 _ _ p (l ++ [0]) =>
      apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg); intros a Ha; rewrite length_app in Ha; cbn [length] in Ha;
      apply (mbyte_of_aview tfibsegs); apply AV; lia
  | Hra : range_addressable (aview _ _ m) ?o ?q ?n |- range_addressable (aview _ _ m') ?o ?q ?n =>
      intros x Hx; destruct (Hra x Hx) as (s & Hs1 & Hs2); exists s; split; [|exact Hs2];
      rewrite AV; [exact Hs1|]; unfold shadow_of_addr, SHADOW_OFF; lia
  | Hhv : shadow_hull_vis (aview _ _ m) ?q ?n |- shadow_hull_vis (aview _ _ m') ?q ?n =>
      intros s Hsr; rewrite AV; [exact (Hhv s Hsr)|]; unfold shadow_addr, SHADOW_OFF in Hsr; lia
  | Htl : forall a, _ -> aview _ _ m a <> None |- forall a, _ -> aview _ _ m' a <> None =>
      (* the word holding the NUL ends at or below alloc_ceiling: p + |l| + 1 <= alloc_ceiling and alloc_ceiling is
         4096-aligned (YM05.alloc_ceiling_value), as FSW_K.cstr_ok_below *)
      intros a Ha; rewrite AV; [exact (Htl a Ha)|];
      pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia));
      pose proof (Z.div_mod (p + Z.of_nat (length l)) 8 ltac:(lia));
      pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia));
      pose proof (proj2 YM05.alloc_ceiling_value); lia
  end.
Qed.


Lemma decE_cs0_den : forall regs j r, nth_error dec_saved j = Some r ->
  exists e, nth_error decE_cs0 j = Some (YP09.mkChunk (-104 + 8 * Z.of_nat j) (CVal 8 e)) /\
    sv_denot (Ereg regs fs_extraT) e = getr regs r.
Proof.
intros regs j r Hj.
do 13 (destruct j as [|j];
  [cbn in Hj; injection Hj as <-; eexists; split; [reflexivity|];
   rewrite fsw_SOff0;
   lazymatch goal with |- ew _ ?n = getr _ ?q => exact (ew_Ereg_nat regs _ n q eq_refl) end |]).
cbn in Hj. destruct j; discriminate Hj.
Qed.
Lemma decE_frame_of_cs0 : forall (W : world tfibsegs) m sp regs,
  Forall (YP09.chunk_ok tfibsegs (Ereg regs fs_extraT) (mrestrict (w_H W) m) sp) decE_cs0 ->
  dec_frame_ok W m (sp - 112) regs.
Proof.
intros W m sp regs HC j r Hj.
destruct (decE_cs0_den regs j r Hj) as (e & Hc & He).
pose proof (proj1 (Forall_forall _ _) HC _ (nth_error_In _ _ Hc)) as Hck.
replace (sp - 112 + 8 + 8 * Z.of_nat j) with (sp + (-104 + 8 * Z.of_nat j)) by lia.
apply (val_of_chunk_ok tfibsegs _ _ _ _ 8 e (bv_unsigned (getr regs r)) Hck).
- rewrite He. symmetry. apply Z_to_bv_bv_unsigned.
- pose proof (u64_range (getr regs r)). cbn [Z.of_N]. lia.
- cbn [Z.of_N]. lia.
Qed.


Lemma decE_frame_avk : forall d (W : world tfibsegs) E rs m m',
  frame_of E rs m m' ->
  (forall r a, In r rs -> base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
     alloc_ceiling <= a < d_sp d) ->
  decE_avk d W m m'.
Proof.
intros d W E rs m m' HF Hw a Ha Hn. apply (aview_at tfibsegs). apply HF. rewrite (wz a Ha).
intros (r & Hin & Hr). pose proof (Hw r a Hin Hr). lia.
Qed.

Lemma decE_kept_avk : forall B d (W : world tfibsegs) m m',
  alloc_ceiling <= d_sp d -> 0 <= d_lenp d -> (d_lenp d + 8 <= alloc_ceiling \/ d_sp d <= d_lenp d) ->
  d_lenp d + 8 <= 2 ^ 64 -> d_ot d <= 2 ^ 47 ->
  decE_avk d W m m' -> dec_kept B d W m -> dec_kept B d W m'.
Proof.
intros B d W m m' Hsp Hl0 Hl Hl64 Hot AVK (K1 & K2 & K3 & K4).
pose proof asan_consts as (C1 & _).
assert (AV : forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a)
  by (intros a Ha; apply AVK; lia).
split; [|split; [|split]].
- apply (decE_val_mem_av W m); [|exact K1]. intros i Hi. cbn in Hi. apply AVK; lia.
- intros a Ha Hn. destruct (K2 a Ha Hn) as [E1 E2].
  assert (Eb : mbyte tfibsegs (mrestrict (w_H W) m') a = mbyte tfibsegs (mrestrict (w_H W) m) a)
    by (apply (mbyte_of_aview tfibsegs); apply AVK; lia).
  split; [rewrite Eb; exact E1|].
  rewrite E2.
  assert (Hni : ~ in_img tfibsegs a) by (intros Hin; pose proof (fs_segs_img a Hin); unfold FS_IMG_END in *; lia).
  exact (decE_writable_eq _ _ a (decE_restrict_of_mbyte _ _ _ _ a ltac:(lia) Hni Eb)).
- exact (decE_cstr_av W m m' _ _ AV K3).
- exact (decE_ro_av B W m m' AV K4).
Qed.

End S0.

(* ===== part E proper: the two arms after fuzz_malloc (sub-parts N, Q), the caller's objects across fuzz_malloc
   (sub-part K), the spine entry -> strlen -> fuzz_malloc, and the stage ===== *)
Section P. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the two shadow-base cells of fss0T / fss_retT (owner: the final instance, FSH_Base.v:116) *)
Hypothesis HSS : FsShadowSyms B.
(* the image facts (FSH_Rt.v fs_img_facts, owner S0 / the final instance): rom_view for strlen and the read-only
   arm of the text across fuzz_malloc *)
Hypothesis HIMG : fs_img_facts tfibsegs B.



Lemma decE_null : forall d W' ly' S' regs' mem' md',
  dec_entry_ok B d -> d_cnt d = d_fail d ->
  decE_res B d W' ly' S' (d_U d) regs' mem' md' 0 ->
  getr regs' 10 = w64 0 ->
  ablocks B ly' S' = ablocks B (d_ly d) (d_S d) ->
  fs_glob tfibsegs W' mem' (d_live d) (d_peak d) (d_cnt d + 1) SIZE_MAXZ ->
  SRr tfibsegs W' (mkCfg (YK11.mkst regs' (Z_to_bv 64 DEC_RA_MALLOC) mem' (YK11.seg_rom tfibsegs)) md') (dec_post B d).
Proof.
intros d W' ly' S' regs' mem' md' HOK Hcf HRES HA0 HBL HG'.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Esp : d_sp d = spZ (d_regs d)) by reflexivity.
assert (HSTK : 112 <= STK_preset_base64_decode) by (vm_compute; discriminate).
assert (HF112 : DEC_F = 112) by reflexivity.
(* ---- the entry facts ---- *)
destruct HOK as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vlenp & _ & _ & HGLOB & _ & _ & _ & HCNT & HPL).
destruct HPRE as (HPREU & _).
pose proof (fsw_ARU B STK_preset_base64_decode (d_ly d) (d_S d) (d_U d) (d_W d) (d_regs d) (d_mem d) (d_md d) (d_ch d)
  HPREU) as HARU0.
pose proof HPREU as (HAP & _ & _).
pose proof HAP as (HAR & Hra & _ & _ & _ & Hstk & _ & _ & _).
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hcnt0 : 0 <= d_cnt d) by (destruct HGLOB as (_ & _ & _ & _ & _ & _ & Hc & _); lia).
(* ---- the two placements of *lenp: the raised top ot, its present bytes, and where lenp lies ---- *)
assert (HOT : d_sp d <= d_ot d /\ d_ot d mod 16 = 0 /\ d_ot d <= ly_top (d_ly d) /\
  (forall a, d_sp d <= a < d_ot d -> apresent (w_H (d_W d)) (d_mem d) a)).
{ destruct HPL as [(_ & Hsl & Hlo & Hot16 & Hottop & Hpres & _) | (_ & Hoteq & _ & _)].
  - split; [lia|]. split; [exact Hot16|]. split; [exact Hottop|]. intros a Ha. apply Hpres. lia.
  - rewrite Hoteq. split; [lia|]. split; [exact Hsp16|]. split; [exact Htop|]. intros a Ha. lia. }
destruct HOT as (Hspot & Hot16 & Hottop & HPRES).
assert (HLP : (d_sp d <= d_lenp d /\ d_lenp d + 8 <= 2 ^ 47) \/ (0 <= d_lenp d /\ d_lenp d + 8 <= alloc_ceiling)).
{ destruct HPL as [(_ & Hsl & Hlo & _) | (_ & _ & (cid & pos & Hin & Hfr) & _)]; [left; lia | right].
  pose proof (Hfr (d_lenp d) ltac:(lia)) as Hr0. pose proof (Hfr (d_lenp d + 7) ltac:(lia)) as Hr7.
  unfold in_zr, frame_rng in Hr0, Hr7. cbn [fst snd] in Hr0, Hr7.
  destruct (frames_bounds tfibsegs B LAWS (d_ly d) (d_S d) (d_W d) (unpoison (d_U d) (d_mem d)) (d_md d) cid pos HAR Hin)
    as (Hf0 & Hfc & _).
  lia. }
(* ---- the resumed state after fuzz_malloc ---- *)
destruct HRES as (HJ & HARU & HS0 & Gsp & G3 & G4 & _ & _ & _ & HK & HKEPT).
destruct HKEPT as (Vl' & HWK & _ & _).
assert (E2 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ decE_xs d)) 2) = d_sp d - DEC_F)
  by (rewrite (ew_Ereg_nat regs' (fs_extraT ++ decE_xs d) 2 2%bv eq_refl); exact Gsp).
(* ---- a0 = 0: the `beqz a0` at 0x84880 is taken ---- *)
assert (HS : st_ok tfibsegs (Ereg regs' (fs_extraT ++ decE_xs d))
  (add_cond (fss_retT DEC_RA_MALLOC DEC_F decE_cs [] []) (mkAC BC_EQ (SOff 10 0) (SLit 0)))
  (restrict (w_H W') (YK11.mkst regs' (Z_to_bv 64 DEC_RA_MALLOC) mem' (YK11.seg_rom tfibsegs)))).
{ apply YP06.st_ok_add_cond; [exact HS0|].
  rewrite fsw_SOff0, (ew_Ereg_nat regs' (fs_extraT ++ decE_xs d) 10 10%bv eq_refl), HA0.
  vm_compute. reflexivity. }
clear HS0.
(* ---- the run to the `ret` 0x849bc and the return, into fpostU at the raised top ---- *)
assert (MAIN : SRr tfibsegs W' (mkCfg (YK11.mkst regs' (Z_to_bv 64 DEC_RA_MALLOC) mem' (YK11.seg_rom tfibsegs)) md')
  (fpostU tfibsegs B (d_STKJ d) (d_ot d) (d_FP d) (d_regs d) (d_ly d) (d_S d) (d_U d) (d_W d) (d_mem d) (d_md d) 0 (d_U d)
     (fun (ly2 : alayout) (S2 : astate) (W2 : world tfibsegs) (regs2 : bvmap 5 word)
          (mem2 : word -> option byte) (md2 : Model) =>
        getr regs2 10 = w64 0 /\ ablocks B ly2 S2 = ablocks B (d_ly d) (d_S d) /\
        wkeep tfibsegs (d_W d) W2 (d_mem d) mem2 (spZ (d_regs d)) (d_ot d) (d_lenp d) 8 /\
        val_mem tfibsegs (mrestrict (w_H W2) mem2) (d_lenp d) 8 (d_v d) /\
        fs_glob tfibsegs W2 mem2 (d_live d) (d_peak d) ((d_cnt d + 1) mod 2 ^ 64) SIZE_MAXZ))).
{ fsw_aj_runU fsw_wr_tbl_ok HS HJ HARU.
  - (* the writes of the run: only the function's own frame [sp - 112, sp), inside the journal's window *)
    unfold add_cond, fss_retT, fsT_ret_regions. cbn [ss_mem app].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := - DEC_F);
      [reflexivity | rewrite E2; lia | cbv [fstk_ret YP09.r_wlo]; lia | cbv [fstk_ret YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_nil.
  - (* at the return instruction: every byte outside the frame is the byte before the run *)
    assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
      ms_mem ms (Z_to_bv 64 a) = mem' (Z_to_bv 64 a)).
    { intros a Ha Hna. apply HF. rewrite (wz a Ha). intros (r & Hin & Hr).
      unfold add_cond, fss_retT, fsT_ret_regions in Hin. cbn [ss_mem app In] in Hin.
      destruct Hin as [<-|[<-|[<-|[]]]];
        cbv [fstk_ret fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        try (rewrite E2 in Hr); lia. }
    assert (MWE : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
      mrestrict (w_H W') (ms_mem ms) (Z_to_bv 64 a) = mrestrict (w_H W') mem' (Z_to_bv 64 a))
      by (intros a Ha Hna; unfold mrestrict; rewrite (MEQ a Ha Hna); reflexivity).
    assert (MB : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
      mbyte tfibsegs (mrestrict (w_H W') (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W') mem') a)
      by (intros a Ha Hna; unfold mbyte; rewrite (MWE a Ha Hna); reflexivity).
    assert (SB : same_below mem' (ms_mem ms) alloc_ceiling) by (intros x Hx; apply MEQ; lia).
    (* the window slack above sp keeps its bytes and writability; *lenp keeps its value *)
    assert (HKEEP : wkeep tfibsegs (d_W d) W' (d_mem d) (ms_mem ms) (spZ (d_regs d)) (d_ot d) (d_lenp d) 8).
    { intros a Ha Hno. destruct (HWK a Ha Hno) as [Hm Hw]. split.
      - rewrite (MB a ltac:(lia) ltac:(lia)). exact Hm.
      - exact (iff_trans Hw (decE_writable_eq _ _ a (MWE a ltac:(lia) ltac:(lia)))). }
    assert (VL : val_mem tfibsegs (mrestrict (w_H W') (ms_mem ms)) (d_lenp d) 8 (d_v d)).
    { intros k Hk. rewrite (MB (d_lenp d + Z.of_nat k) ltac:(lia) ltac:(lia)). exact (Vl' k Hk). }
    assert (HGL : fs_glob tfibsegs W' (ms_mem ms) (d_live d) (d_peak d) ((d_cnt d + 1) mod 2 ^ 64) SIZE_MAXZ).
    { rewrite Z.mod_small by lia. exact (fs_glob_below W' mem' (ms_mem ms) _ _ _ _ SB HG'). }
    (* the return address: the reloaded ra is the entry ra (extra atom 36 = xatom 3) *)
    assert (R1 : getr (ms_regs ms) 1%bv = getr (d_regs d) 1%bv).
    { lazymatch type of HS with
      | st_ok _ _ ?ssf _ =>
        exact (fsw_reg_extra (w_H W') regs' (fs_extraT ++ decE_xs d) ssf ms 1%bv 4 HS ltac:(vm_compute; reflexivity))
      end. }
    eapply (fsw_retU B fsw_wr_tbl fsw_wr_tbl_ok).
    + exact HS.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
    + rewrite R1. exact Hra.
    + (* the journal widened from the entry sp to the raised top ot *)
      unfold d_STKJ.
      apply (decE_widen B STK_preset_base64_decode (d_sp d) (d_ot d) (d_FP d) (d_ly d) (d_S d) (d_W d)
        (unpoison (d_U d) (d_mem d)) (d_md d) ly' S' W' (unpoison (d_U d) (ms_mem ms)) _ 0 HJ Hspot Hot16 Hottop).
      intros a Ha.
      pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & J9 & _).
      apply (apresent_transfer tfibsegs (w_H (d_W d)) (w_H W') (unpoison (d_U d) (d_mem d))
        (unpoison (d_U d) (ms_mem ms)) a); [lia | | apply J9; lia |].
      * intros Hi. pose proof (fs_segs_img a Hi) as Hb. unfold FS_IMG_END in Hb. lia.
      * apply (fsw_apresent_poison B (d_ly d) (d_S d) (d_U d) (d_W d) (d_mem d) (d_md d) a HARU0); [lia|].
        exact (HPRES a Ha).
    + exact HARU.
    + (* the callee-saved registers: sp = atom 2 + 112, s0 / s2 / s5 the reloaded extra atoms, the others kept *)
      lazymatch type of HS with
      | st_ok _ _ ?ssf _ =>
        apply (fsw_preserved (w_H W') (Ereg regs' (fs_extraT ++ decE_xs d)) ssf ms (d_regs d)
          (fun r : bv 5 => sr_get (ss_regs ssf) r) HS);
        [vm_compute; reflexivity|];
        let r := fresh "r" in let Hr := fresh "Hr" in
        intros r Hr; cbv [CALLEE_SAVED In] in Hr;
        repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]
      end;
      cbv beta;
      lazymatch goal with
      | |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e'
      end;
      first
      [ apply fsw_sp_back; rewrite E2; lia
      | rewrite fsw_SOff0;
        first
        [ lazymatch goal with |- ew _ ?n = getr _ ?q => rewrite (ew_Ereg_nat regs' _ n q eq_refl) end;
          first [exact G3 | exact G4 | apply HK; cbv [decE_kregs In]; auto 20]
        | lazymatch goal with |- ew _ ?n = _ =>
            let j := eval compute in (n - 32)%nat in change n with (32 + j)%nat end;
          rewrite ew_Ereg_extra; reflexivity ] ].
    + intros mat2. cbv beta.
      split.
      { unfold w64. lazymatch type of HS with
        | st_ok _ _ ?ssf _ => exact (fsw_reg_lit (w_H W') _ ssf ms 10%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(lia))
        end. }
      split; [exact HBL|]. split; [exact HKEEP|]. split; [exact VL | exact HGL]. }
(* ---- dec_post's first arm: cnt = fail, k = 0, U' = U ---- *)
eapply SRr_mono; [exact MAIN|].
intros W2 c2 _ HP. cbv beta zeta delta [dec_post]. left. split; [exact Hcf | exact HP].
Qed.


(* a byte off the image that reads as Some through mrestrict H is present (H says visible, the memory holds it) *)
Lemma decQ_apresent_of_mbyte : forall (H : word -> bool) (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a -> mbyte tfibsegs (mrestrict H m) a <> None -> apresent H m a.
Proof.
intros H m a Ha Hn Hb. unfold apresent. unfold mbyte, mrestrict in Hb.
rewrite (YCbq.seg_rom_none tfibsegs a Ha Hn) in Hb.
revert Hb. destruct (H (Z_to_bv 64 a)); intros Hb; [exfalso; apply Hb; reflexivity|].
split; [reflexivity|].
revert Hb. destruct (m (Z_to_bv 64 a)) as [b|]; intros Hb; [exists b; reflexivity | exfalso; apply Hb; reflexivity].
Qed.
Lemma decQ_mbyte_of_apresent : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> mbyte tfibsegs (mrestrict H m) a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.

Lemma decE_nonnull : forall d q W' ly' S' regs' mem' md',
  dec_entry_ok B d -> d_cnt d <> d_fail d ->
  decE_res B d W' ly' S' (d_U d ++ [(q - HEAD, HEAD)]) regs' mem' md' 1 ->
  getr regs' 10 = w64 q -> 4096 + HEAD <= q ->
  ablocks B ly' S' = ablocks B (d_ly d) (d_S d) ++ [(q - HEAD, d_n d + HEAD)] ->
  fs_heads B ly' S' (d_U d ++ [(q - HEAD, HEAD)]) ->
  fs_rblock tfibsegs B ly' S' W' mem' q (d_n d) ->
  range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF q (d_n d) ->
  fs_glob tfibsegs W' mem' (d_live d + d_n d) (Z.max (d_peak d) (d_live d + d_n d)) (d_cnt d + 1) (d_fail d) ->
  (forall Wc lyc Sc Uc regsc memc mdc k q0, dec_head B d q0 0 [] 0 0 Wc lyc Sc Uc regsc memc mdc k ->
     SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 DEC_HEAD) memc (YK11.seg_rom tfibsegs)) mdc) (dec_post B d)) ->
  SRr tfibsegs W' (mkCfg (YK11.mkst regs' (Z_to_bv 64 DEC_RA_MALLOC) mem' (YK11.seg_rom tfibsegs)) md') (dec_post B d).
Proof.
intros d q W' ly' S' regs' mem' md' HOK Hcf HRES G10 Hq HBL HHD HRB HRA HGL HK.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HF112 : 112 <= STK_preset_base64_decode) by (vm_compute; discriminate).
destruct HRES as (HJ & HARU & HS & Esp & R3 & R4 & R8 & R18 & R21 & RK & HKEPT).
pose proof HJ as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & J13 & J14 & J15 & J16 & J17).
pose proof J15 as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HOK as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPLACE).
destruct HPRE as (HPREU & _).
pose proof HPREU as (HAP & _ & _).
pose proof HAP as (HAR0 & _).
unfold d_sp in *. unfold DEC_F in Esp.
(* ---- the two placements of *lenp: the raised top, lenp's bounds, the entry presence of [sp, ot) ---- *)
assert (HPL : spZ (d_regs d) <= d_ot d /\ d_ot d mod 16 = 0 /\ d_ot d <= ly_top (d_ly d) /\
  4096 <= d_lenp d /\ d_lenp d + 8 <= 2 ^ 47 /\
  (spZ (d_regs d) <= d_lenp d \/ d_lenp d + 8 <= alloc_ceiling) /\
  (forall a, spZ (d_regs d) <= a < d_ot d -> apresent (w_H (d_W d)) (d_mem d) a)).
{ destruct HPLACE as [(_ & Hsl & Hlo & Hot16 & Hottop & Hpres & _) | (_ & Hot & (cid & pos & Hin & Hfr) & _)].
  - split; [lia|]. split; [exact Hot16|]. split; [exact Hottop|]. split; [lia|]. split; [lia|].
    split; [left; exact Hsl | exact Hpres].
  - destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ cid pos HAR0 Hin) as (Hf1 & Hf2 & _).
    pose proof (Hfr (d_lenp d) ltac:(lia)) as Fa. pose proof (Hfr (d_lenp d + 7) ltac:(lia)) as Fb.
    unfold in_zr, frame_rng in Fa, Fb. cbn [fst snd] in Fa, Fb.
    rewrite Hot. split; [lia|]. split; [exact Hsp16|]. split; [exact Htop|]. split; [lia|]. split; [lia|].
    split; [right; lia | intros a Ha; lia]. }
destruct HPL as (Hspot & Hot16 & Hottop & Hl4096 & Hl47 & Hlpos & Hpres0).
(* ---- q's block: below alloc_ceiling ---- *)
pose proof HRB as (HinB & Hq16 & Hn0 & VH).
pose proof HARU as (HARc & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc HinB) as (_ & Hb4096 & Hbceil & _).
pose proof (req_size_pos (d_n d + HEAD) ltac:(unfold HEAD; lia)) as (RQ1 & RQ2).
unfold HEAD in Hq, Hb4096, Hbceil, RQ1, RQ2.
(* ---- the resumed env and the condition a0 = q <> 0 ---- *)
set (E := Ereg regs' (fs_extraT ++ decE_xs d)) in *.
assert (E10 : ew E 10 = Z_to_bv 64 q) by (unfold E; rewrite (ew_Ereg_nat regs' _ 10 10%bv eq_refl); exact G10).
assert (E2 : bv_unsigned (ew E 2) = spZ (d_regs d) - 112)
  by (unfold E; rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact Esp).
assert (HSc : st_ok tfibsegs E
  (add_cond (fss_retT DEC_RA_MALLOC DEC_F decE_cs [] []) (mkAC BC_NE (SOff 10 0) (SLit 0)))
  (restrict (w_H W') (YK11.mkst regs' (Z_to_bv 64 DEC_RA_MALLOC) mem' (YK11.seg_rom tfibsegs)))).
{ apply (st_ok_add_cond tfibsegs); [exact HS|].
  rewrite branch_ne_U, (U_atom E 10 q E10 ltac:(lia)), U_lit by lia.
  apply Bool.negb_true_iff, Z.eqb_neq. lia. }
clear HS.
(* ---- the run from 0x84880 to the loop head 0x848bc ---- *)
fsw_aj_run_toU fsw_wr_tbl_ok HSc HJ HARU DEC_HEAD.
- (* the run writes only the 112-byte frame [sp - 112, sp), inside the journal's window *)
  cbn [add_cond fss_retT fsT_ret_regions ss_mem app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -112);
    [reflexivity | rewrite E2; lia | cbv [fstk_ret YP09.r_wlo]; lia | cbv [fstk_ret YP09.r_whi DEC_F]; lia |].
  apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil.
- (* at the loop head *)
  (* every byte outside the frame is the byte after fuzz_malloc *)
  assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (d_regs d) - 112 <= a < spZ (d_regs d)) ->
    ms_mem ms (Z_to_bv 64 a) = mem' (Z_to_bv 64 a)).
  { intros a Ha Hna. apply HF. rewrite (wz a Ha). intros (r & Hin & Hr).
    cbn [add_cond fss_retT fsT_ret_regions ss_mem app In] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]];
      cbv [fstk_ret fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val DEC_F] in Hr;
      try (rewrite E2 in Hr); lia. }
  assert (MWE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (d_regs d) - 112 <= a < spZ (d_regs d)) ->
    mrestrict (w_H W') (ms_mem ms) (Z_to_bv 64 a) = mrestrict (w_H W') mem' (Z_to_bv 64 a))
    by (intros a Ha Hna; unfold mrestrict; rewrite (MEQ a Ha Hna); reflexivity).
  assert (MB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (d_regs d) - 112 <= a < spZ (d_regs d)) ->
    mbyte tfibsegs (mrestrict (w_H W') (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W') mem') a)
    by (intros a Ha Hna; unfold mbyte; rewrite (MWE a Ha Hna); reflexivity).
  assert (SB : same_below mem' (ms_mem ms) alloc_ceiling) by (intros x Hx; apply MEQ; lia).
  assert (MV : forall a k v, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
    (spZ (d_regs d) <= a \/ a + Z.of_nat k <= spZ (d_regs d) - 112) ->
    val_mem tfibsegs (mrestrict (w_H W') mem') a k v -> val_mem tfibsegs (mrestrict (w_H W') (ms_mem ms)) a k v)
    by (intros a k v H0 Hk Hout Hv i Hi; rewrite (MB (a + Z.of_nat i) ltac:(lia) ltac:(lia)); exact (Hv i Hi)).
  (* the caller's kept objects *)
  destruct HKEPT as (KV & KW & KC & KR).
  assert (KV' : val_mem tfibsegs (mrestrict (w_H W') (ms_mem ms)) (d_lenp d) 8 (d_v d))
    by (apply (MV (d_lenp d) 8%nat (d_v d)); [lia | lia | lia | exact KV]).
  assert (KW' : wkeep tfibsegs (d_W d) W' (d_mem d) (ms_mem ms) (spZ (d_regs d)) (d_ot d) (d_lenp d) 8).
  { intros a Ha Hno. destruct (KW a Ha Hno) as [K1 K2]. split.
    - rewrite (MB a ltac:(lia) ltac:(lia)). exact K1.
    - pose proof (decE_writable_eq (mrestrict (w_H W') mem') (mrestrict (w_H W') (ms_mem ms)) a
        (MWE a ltac:(lia) ltac:(lia))) as WE. tauto. }
  assert (KC' : cstr_ok tfibsegs W' (ms_mem ms) (d_text d) (d_tb d)) by exact (cstr_ok_below W' mem' (ms_mem ms) _ _ SB KC).
  assert (KR' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') (ms_mem ms)))
    by exact (arodata_below B W' mem' (ms_mem ms) SB KR).
  (* q's block, its shadow and the globals: all below alloc_ceiling *)
  assert (HRB' : fs_rblock tfibsegs B ly' S' W' (ms_mem ms) q (d_n d)).
  { unfold fs_rblock. split; [exact HinB|]. split; [exact Hq16|]. split; [exact Hn0|].
    exact (val_mem_below (w_H W') mem' (ms_mem ms) alloc_ceiling (q - HEAD) 8%nat (d_n d) SB
             ltac:(unfold HEAD; lia) ltac:(unfold HEAD; lia) VH). }
  assert (HRA' : range_addressable (aview tfibsegs (w_H W') (ms_mem ms)) SHADOW_OFF q (d_n d)).
  { eapply range_addressable_agree; [|exact HRA].
    intros x Hx. apply (aview_below (w_H W') mem' (ms_mem ms) alloc_ceiling _ SB).
    unfold shadow_of_addr, SHADOW_OFF.
    pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. }
  assert (HGL' : fs_glob tfibsegs W' (ms_mem ms) (d_live d + d_n d) (Z.max (d_peak d) (d_live d + d_n d))
                   (d_cnt d + 1) (d_fail d))
    by exact (fs_glob_below W' mem' (ms_mem ms) _ _ _ _ SB HGL).
  (* the bytes [sp, ot) are present again: *lenp's 8 bytes by its value, the others by wkeep and the entry presence *)
  assert (HPRES : forall a, spZ (d_regs d) <= a < d_ot d ->
    apresent (w_H W') (unpoison (d_U d ++ [(q - HEAD, HEAD)]) (ms_mem ms)) a).
  { intros a Ha.
    assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
    assert (Hni : ~ in_img tfibsegs a)
      by (intros Hi; pose proof (fs_segs_img a Hi) as Hi'; unfold FS_IMG_END in Hi'; lia).
    apply (fsw_apresent_poison B ly' S' _ W' (ms_mem ms) _ a HARU);
      [first [lia | unfold kHighMemBeg in *; lia]|].
    apply (decQ_apresent_of_mbyte _ _ a Ha64 Hni).
    destruct (Z.le_gt_cases (d_lenp d) a) as [L1|L1];
      [destruct (Z.lt_ge_cases a (d_lenp d + 8)) as [L2|L2]|].
    - pose proof (KV' (Z.to_nat (a - d_lenp d)) ltac:(lia)) as Hb.
      rewrite Z2Nat.id in Hb by lia. replace (d_lenp d + (a - d_lenp d)) with a in Hb by lia.
      rewrite Hb. discriminate.
    - destruct (KW' a Ha ltac:(lia)) as [K1 _]. rewrite K1. apply decQ_mbyte_of_apresent. exact (Hpres0 a Ha).
    - destruct (KW' a Ha ltac:(lia)) as [K1 _]. rewrite K1. apply decQ_mbyte_of_apresent. exact (Hpres0 a Ha). }
  (* reading the final symbolic state: registers and the frame region *)
  lazymatch type of HSc with
  | st_ok _ _ ?ssf _ =>
    assert (RA : forall (r r' : bv 5) n, sr_get (ss_regs ssf) r = SOff n 0 -> Z.of_nat n = bv_unsigned r' ->
                  getr (ms_regs ms) r = getr regs' r')
      by (intros r r' n H1 H2; exact (fsw_reg_atom (w_H W') regs' (fs_extraT ++ decE_xs d) ssf ms r r' n HSc H1 H2));
    assert (RL : forall (r : bv 5) z, sr_get (ss_regs ssf) r = SLit z -> 0 <= z < 2 ^ 64 ->
                  getr (ms_regs ms) r = Z_to_bv 64 z)
      by (intros r z H1 H2; exact (fsw_reg_lit (w_H W') E ssf ms r z HSc H1 H2));
    assert (HREG0 : region_ok tfibsegs E (mrestrict (w_H W') (ms_mem ms))
                      (YP09.mkRegion (Some 2%nat) 0 112 0 112 (YP09.mkChunk 0 (CVal 8 (SOff 8 0)) :: decE_cs)))
      by exact (fsw_region_nth E ssf (restrict (w_H W') ms) 0 _ HSc eq_refl);
    assert (Hshape : ms = YK11.mkst (ms_regs ms) (Z_to_bv 64 DEC_HEAD) (ms_mem ms) (YK11.seg_rom tfibsegs))
      by exact (st_ok_restrict_mkst tfibsegs (w_H W') E ssf ms HSc eq_refl)
  end.
  rewrite Hshape.
  apply (HK W' ly' S' (d_U d ++ [(q - HEAD, HEAD)]) (ms_regs ms) (ms_mem ms) _ 1 q).
  unfold dec_head. cbv zeta.
  split.
  { unfold dec_J, d_STKJ, d_sp.
    exact (decE_widen B STK_preset_base64_decode (spZ (d_regs d)) (d_ot d) _ _ _ _ _ _ _ _ _ _ _ _
             HJ Hspot Hot16 Hottop HPRES). }
  split; [exact HARU|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact HHD|].
  split; [exact HBL|].
  split; [unfold HEAD; lia|].
  split; [exact HRB'|].
  split; [exact HRA'|].
  split; [exact Hcf|].
  split; [exact HGL'|].
  (* registers *)
  split; [unfold spZ at 1, d_sp, DEC_F; rewrite (RA 2%bv 2%bv 2%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)); exact Esp|].
  split; [rewrite (RA 3%bv 3%bv 3%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)); exact R3|].
  split; [rewrite (RA 4%bv 4%bv 4%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)); exact R4|].
  split; [exact (RL 8%bv DEC_WSMASK ltac:(vm_compute; reflexivity) ltac:(unfold DEC_WSMASK; lia))|].
  split; [rewrite (RA 9%bv 10%bv 10%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)); exact G10|].
  split; [rewrite (RA 18%bv 18%bv 18%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)), R18;
          change (Z.of_nat 0) with 0; rewrite Z.add_0_r; reflexivity|].
  split; [exact (RL 19%bv G_B64 ltac:(vm_compute; reflexivity) ltac:(unfold G_B64; lia))|].
  split; [rewrite (RA 20%bv 18%bv 18%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)), R18;
          change (Z.of_nat 0) with 0; rewrite Z.add_0_r; reflexivity|].
  split; [rewrite (RA 21%bv 21%bv 21%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)); exact R21|].
  split; [exact (RL 22%bv 0 ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split; [exact (RL 23%bv 0 ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split; [lia|].
  split; [exact (RL 24%bv 0 ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split; [exact (RL 25%bv 61 ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split; [exact (RL 26%bv 0 ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split; [exact (RL 27%bv 2 ltac:(vm_compute; reflexivity) ltac:(lia))|].
  (* the frame: the 13 saved words and the spilled lenp *)
  pose proof HREG0 as (_ & _ & _ & HCH).
  cbn [YP09.r_base YP09.r_chunks base_val] in HCH. rewrite E2 in HCH.
  split.
  { unfold d_sp, DEC_F. apply (decE_frame_of_chunks d W' (ms_mem ms) _ regs' RK).
    exact (Forall_inv_tail HCH). }
  split.
  { unfold dec_lenp_slot, d_sp, DEC_F.
    pose proof (fsw_field E (mrestrict (w_H W') (ms_mem ms)) 2%nat (spZ (d_regs d) - 112) _ 0 112 0 112 0 8%N
                  (SOff 8 0) (d_lenp d) HREG0 E2 (or_introl eq_refl)) as X.
    rewrite Z.add_0_r in X. apply X.
    - rewrite fsw_SOff0. unfold E. rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl). exact R8.
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    - cbn. lia. }
  (* the data *)
  split; [unfold dec_kept, d_sp; split; [exact KV'|]; split; [exact KW'|]; split; [exact KC' | exact KR']|].
  split; [exact (garr8_nil tfibsegs _ _)|].
  (* the model at i = 0 *)
  split; [lia|].
  split; [lia|].
  split; [cbn; lia|].
  split; [constructor|].
  split; [reflexivity|].
  reflexivity.
Qed.


Lemma decK_ro_img : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> in_img tfibsegs a.
Proof.
intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
assert (Hb : existsb (fun s => (Z.of_N (seg_base s) <=? FS_RLO) &&
  (FS_RHI <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hb as (s & Hs & Hss). apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.
(* fs's four alloc.c statics are not read-only: they lie in a writable segment and outside [FS_RLO, FS_RHI)
   (the new premise `~ inFP FP a` of ajournal's image clause, RELOC's FP-keyed core) *)
Lemma decK_ro_not_pstat : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
intros a Hro (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z => forallb (fun s => seg_writable s ||
  (snd r <=? Z.of_N (seg_base s)) || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? fst r)) tfibsegs)
  FS_PSTAT_FP = true) by (vm_compute; reflexivity).
assert (Hlo : forallb (fun r : Z * Z => (FS_RHI <=? fst r) || (snd r <=? FS_RLO)) FS_PSTAT_FP = true)
  by (vm_compute; reflexivity).
destruct Hro as [(s & Hs & Hw & Hseg) | Hr2].
- pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H1. cbn beta in H1.
  pose proof (proj1 (forallb_forall _ _) H1 s Hs) as H2. cbn beta in H2.
  rewrite Hw in H2. cbn [orb] in H2.
  apply orb_prop in H2 as [H | H]; apply Z.leb_le in H; lia.
- pose proof (proj1 (forallb_forall _ _) Hlo r Hr) as H1. cbn beta in H1.
  apply orb_prop in H1 as [H | H]; apply Z.leb_le in H; lia.
Qed.
Lemma decK_ro_strs_img : forall s l a, In (s, l) FS_RO_STRS -> s <= a < s + Z.of_nat (length l) + 1 ->
  in_img tfibsegs a.
Proof.
intros s l a Hin Ha.
assert (Hb : forallb (fun r : Z * list Z => existsb (fun sg => (Z.of_N (seg_base sg) <=? fst r) &&
  (fst r + Z.of_nat (length (snd r)) + 1 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs) FS_RO_STRS = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb (s, l) Hin) as H. cbn [fst snd] in H.
apply existsb_exists in H as (sg & Hsg & Hss). apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hsg | lia].
Qed.
Lemma decK_pstat_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof. apply sink_closed_pos. unfold FS_PSTAT_FP. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil. Qed.

(* ---- small arithmetic / byte facts ---- *)
Lemma decK_sh_range : forall x, 0 <= x < 2 ^ 61 -> 0 <= shadow_addr x < 2 ^ 64.
Proof.
intros x Hx. unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_upper_bound x 8 (2 ^ 61) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma decK_amem_data : forall p n a, 4096 <= p -> amem_range p n -> p <= a < p + n ->
  0 <= a < 2 ^ 64 /\ (a < SHADOW_OFF \/ kHighMemBeg <= a).
Proof.
intros p n a H1 H3 H4. pose proof asan_consts as (_ & _ & C3 & C4 & C5).
unfold amem_range, SHADOW_OFF in *. lia.
Qed.
Lemma decK_bv8_inj : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> Z_to_bv 8 x = Z_to_bv 8 y -> x = y.
Proof.
intros x y Hx Hy E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E.
rewrite (bv_wrap_small 8 x), (bv_wrap_small 8 y) in E by (change (bv_modulus 8) with 256; lia). exact E.
Qed.
(* two C strings at the same address are the same string *)
Lemma decK_cstr_same : forall (m : word -> option byte) tb l p,
  garr8 tfibsegs m p (tb ++ [0]) -> garr8 tfibsegs m p (l ++ [0]) ->
  Forall (fun c => c <> 0) tb -> Forall (fun c => c <> 0) l -> tb = l.
Proof.
intros m tb. induction tb as [|c tb IH]; intros l p H1 H2 N1 N2.
- destruct l as [|c' l]; [reflexivity|]. exfalso.
  pose proof (garr8_mbyte tfibsegs m p _ 0 H1 ltac:(cbn; lia)) as E1.
  pose proof (garr8_mbyte tfibsegs m p _ 0 H2 ltac:(cbn; lia)) as E2.
  pose proof (garr8_bytes_ok tfibsegs m p _ H2) as BO. unfold bytes_ok in BO. cbn [app] in BO.
  apply Forall_inv in BO. apply Forall_inv in N2. cbn [nth app] in E1, E2. rewrite E1 in E2.
  assert (E : Z_to_bv 8 0 = Z_to_bv 8 c') by congruence.
  apply N2. symmetry. apply decK_bv8_inj; [lia | lia | exact E].
- destruct l as [|c' l].
  + exfalso.
    pose proof (garr8_mbyte tfibsegs m p _ 0 H1 ltac:(cbn; lia)) as E1.
    pose proof (garr8_mbyte tfibsegs m p _ 0 H2 ltac:(cbn; lia)) as E2.
    pose proof (garr8_bytes_ok tfibsegs m p _ H1) as BO. unfold bytes_ok in BO. cbn [app] in BO.
    apply Forall_inv in BO. apply Forall_inv in N1. cbn [nth app] in E1, E2. rewrite E1 in E2.
    assert (E : Z_to_bv 8 c = Z_to_bv 8 0) by congruence.
    apply N1. apply decK_bv8_inj; [lia | lia | exact E].
  + change ((c :: tb) ++ [0]) with ([c] ++ (tb ++ [0])) in H1.
    change ((c' :: l) ++ [0]) with ([c'] ++ (l ++ [0])) in H2.
    apply (garr8_app tfibsegs) in H1 as [H1a H1b]. apply (garr8_app tfibsegs) in H2 as [H2a H2b].
    pose proof (garr8_mbyte tfibsegs m p _ 0 H1a ltac:(cbn; lia)) as E1.
    pose proof (garr8_mbyte tfibsegs m p _ 0 H2a ltac:(cbn; lia)) as E2.
    pose proof (garr8_bytes_ok tfibsegs m p _ H1a) as BO1. pose proof (garr8_bytes_ok tfibsegs m p _ H2a) as BO2.
    unfold bytes_ok in BO1, BO2. apply Forall_inv in BO1. apply Forall_inv in BO2.
    cbn [nth] in E1, E2. rewrite E1 in E2. assert (E : Z_to_bv 8 c = Z_to_bv 8 c') by congruence.
    assert (Ec : c = c') by (apply decK_bv8_inj; [lia | lia | exact E]). subst c'.
    cbn [length Z.of_nat] in H1b, H2b.
    rewrite (IH l (p + 1) H1b H2b (Forall_inv_tail N1) (Forall_inv_tail N2)). reflexivity.
Qed.
(* ---- the unpoisoned and the raw memory ---- *)
(* a byte that is no shadow byte reads the same in both *)
Lemma decK_unp_data : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 -> a < SHADOW_OFF \/ kHighMemBeg <= a ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros ly S U W mem md a H Ha Hr. apply aview_unpoison_out. rewrite (wz a Ha).
destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
pose proof (ush_facts tfibsegs B ly S U W mem md a H E) as (_ & L1 & L2). lia.
Qed.
(* a user-poisoned shadow byte is visible (0xf7), so visibility carries from the unpoisoned memory *)
Lemma decK_vis_unp : forall (W : world tfibsegs) mem U s,
  upoisoned tfibsegs W mem U -> aview tfibsegs (w_H W) (unpoison U mem) s <> None -> aview tfibsegs (w_H W) mem s <> None.
Proof.
intros W mem U s HP Hv. rewrite (aview_mod tfibsegs (w_H W) (unpoison U mem) s) in Hv.
rewrite (aview_mod tfibsegs (w_H W) mem s).
assert (Hs : 0 <= s mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
destruct (in_ush U (s mod 2 ^ 64)) eqn:E.
- rewrite (HP _ E). discriminate.
- rewrite aview_unpoison_out in Hv; [exact Hv|]. rewrite (wz _ Hs). exact E.
Qed.
(* granule-aligned ranges disjoint from [x, x + n) poison no shadow byte of it *)
Lemma decK_ush_out : forall U x n,
  (forall r, In r U -> fst r mod 8 = 0 /\ snd r mod 8 = 0 /\ (fst r + snd r <= x \/ x + n <= fst r)) ->
  forall y, x <= y < x + n -> in_ush U (shadow_addr y) = false.
Proof.
intros U x n HU y Hy. destruct (in_ush U (shadow_addr y)) eqn:E; [|reflexivity]. exfalso.
apply in_ush_spec in E as ([a c] & Hr & Hs). destruct (HU _ Hr) as (A8 & C8 & D). cbn [fst snd] in *.
apply Z.mod_divide in A8 as [i ->]; [|lia]. apply Z.mod_divide in C8 as [j ->]; [|lia].
unfold shadow_addr in Hs. rewrite !Z.div_mul in Hs by lia.
pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)). lia.
Qed.
(* cstr_ok of the unpoisoned memory is cstr_ok of the raw one when no shadow byte of the string is user-poisoned *)
Lemma decK_cstr_unp : forall ly S U (W : world tfibsegs) mem md p l,
  ARU tfibsegs B ly S U W mem md -> cstr_ok tfibsegs W (unpoison U mem) p l ->
  (forall y, p <= y < p + Z.of_nat (length l) + 1 -> in_ush U (shadow_addr y) = false) ->
  cstr_ok tfibsegs W mem p l.
Proof.
intros ly S U W mem md p l H ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl) HO.
pose proof asan_consts as (C1 & _).
assert (AV : forall a, p <= a < p + (Z.of_nat (length l) + 8) ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a).
{ intros a Ha. destruct (decK_amem_data p (Z.of_nat (length l) + 8) a H4096 Ham Ha) as [Ha1 Ha2].
  exact (decK_unp_data ly S U W mem md a H Ha1 Ha2). }
split; [split; [|exact Hnz]|].
{ apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  apply (mbyte_of_aview tfibsegs). symmetry. apply AV. lia. }
split; [exact H4096|]. split; [exact Hcl|]. split; [exact H32|]. split; [exact Ham|].
split.
{ eapply range_addressable_agree; [|exact Hra]. intros x Hx. symmetry. apply aview_unpoison_out.
  change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). rewrite wz; [apply HO; lia|]. apply decK_sh_range. lia. }
split.
{ intros s Hs. exact (decK_vis_unp W mem U s (proj2 (proj2 H)) (Hhv s Hs)). }
intros a Ha. rewrite <- AV; [exact (Htl a Ha)|].
pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)).
pose proof (Z.div_mod (p + Z.of_nat (length l)) 8 ltac:(lia)).
pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)).
pose proof (proj2 YM05.alloc_ceiling_value). lia.
Qed.

(* a string in a block the journal keeps, its bytes out of the footprint: cstr_ok at the end of the journal (the
   structure of a Theorem Labs lane's FMW_kitS.v cstr_ok_kept_blk; only the string's bytes are taken from the start) *)
Lemma decK_cstr_blk : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l b m,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly' S') -> b <= p -> p + Z.of_nat (length l) + 1 <= b + m ->
  (forall a, p <= a < p + Z.of_nat (length l) + 1 -> ~ inFP FP a) ->
  cstr tfibsegs W mem p l -> 4096 <= p -> p + Z.of_nat (length l) + 1 <= alloc_ceiling ->
  Z.of_nat (length l) < 2 ^ 32 -> amem_range p (Z.of_nat (length l) + 8) ->
  cstr_ok tfibsegs W' mem' p l.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l b m HJ Hin Hin' Hb Hbm HnF (Hg & Hnz) H4096 Hcl H32 Ham.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (Hm : 0 < m) by lia.
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
split; [split; [|exact Hnz]|].
{ apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  apply (mbyte_of_aview tfibsegs). replace a with (b + (a - b)) by lia.
  apply (F2 b m (a - b) Hin Hin'); [rewrite Hrq; lia | replace (b + (a - b)) with a by lia; apply HnF; lia]. }
split; [exact H4096|]. split; [exact Hcl|]. split; [clear H32; (destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR' Hin') as (_ & _ & _ & _ & _ & _ & HmxL); unfold MALLOC_MAX in HmxL; lia)|]. split; [exact Ham|].
split.
{ apply (range_addressable_of_block tfibsegs B LAWS ly' S' W' mem' md' b m p _ HAR' Hin' Hb). rewrite Hrq. lia. }
split.
{ destruct (al_shadow _ _ LAWS ly' S' W' mem' md' b m HAR' Hin') as (_ & Hhv').
  apply (shadow_hull_vis_sub _ b (req_size m) p _ Hhv' Hb); rewrite ?Hrq; lia. }
intros a Ha. apply (block_word_tail_vis B ly' S' W' mem' md' b m HAR' Hin' Hm).
pose proof (word_end_mono (p + Z.of_nat (length l)) (b + m - 1) ltac:(lia)). lia.
Qed.
(* ---- blocks and heads ---- *)
(* a range of U (a head at the start of a live block, fs_heads) misses [x, x + n) inside block b past its own head *)
Lemma decK_heads_disj : forall ly S U (W : world tfibsegs) mem md b m x n,
  AR tfibsegs B ly S W mem md -> fs_heads B ly S U -> In (b, m) (ablocks B ly S) ->
  b + 16 <= x -> x + n <= b + req_size m ->
  forall r, In r U -> fst r + snd r <= x \/ x + n <= fst r.
Proof.
intros ly S U W mem md b m x n HAR FH Hb Hx Hxn r Hr.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (FH r Hr) as (E16 & m' & Hm' & M16).
destruct r as [q s]. cbn [fst snd] in *. subst s.
destruct (Z.eq_dec q b) as [->|NE]; [left; lia|].
pose proof (sep_blocks tfibsegs B LAWS ly S W mem md q m' b m HAR Hm' Hb
  ltac:(intros E; injection E as E1 E2; exact (NE E1))) as D.
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
(* the block appended by an allocation is disjoint from every block it is appended to *)
Lemma decK_new_disj : forall ly S (W : world tfibsegs) mem md (A : list (Z * Z)) b m x y,
  AR tfibsegs B ly S W mem md -> ablocks B ly S = A ++ [(x, y)] -> In (b, m) A ->
  zdisjoint (b, req_size m) (x, req_size y).
Proof.
intros ly S W mem md A b m x y HAR E Hin.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (Hx : In (x, y) (ablocks B ly S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md x y HAR Hx) as (_ & _ & _ & _ & _ & PW & _).
apply in_split in Hin as (l1 & l2 & EA). rewrite E, EA in PW.
apply (YCbq.pairwise_In2 zdisjoint _ _ _ (map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) l1)
  (map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) l2) [] PW).
rewrite !map_app. cbn [map]. rewrite <- app_assoc. reflexivity.
Qed.
(* the read-only view carries to the unpoisoned memory (image bytes are below SHADOW_OFF) *)
Lemma decK_aro_unp : forall ly S U (W : world tfibsegs) mem md,
  ARU tfibsegs B ly S U W mem md -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U mem)).
Proof.
intros ly S U W mem md H HR a Hro Hno Her. pose proof (fs_segs_img a (decK_ro_img a Hro)) as Hb.
rewrite (decK_unp_data ly S U W mem md a H);
  [exact (HR a Hro Hno Her) | unfold FS_IMG_END in Hb; lia | left; unfold FS_IMG_END, SHADOW_OFF in *; lia].
Qed.

(* ---- the lemma ---- *)
Lemma decE_kept_malloc : forall d memC mdC regsC ly' S' U' W' mem' md' kc,
  dec_entry_ok B d ->
  ARU tfibsegs B (d_ly d) (d_S d) (d_U d) (d_W d) memC mdC ->
  dec_kept B d (d_W d) memC ->
  spZ regsC = d_sp d - DEC_F ->
  ajournal tfibsegs B STK_fuzz_malloc (spZ regsC) FS_PSTAT_FP (d_ly d) (d_S d) (d_W d) (unpoison (d_U d) memC) mdC []
    ly' S' W' (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' -> fs_heads B ly' S' U' ->
  ((U' = d_U d /\ ablocks B ly' S' = ablocks B (d_ly d) (d_S d)) \/
   (exists q, U' = d_U d ++ [(q - HEAD, HEAD)] /\
      ablocks B ly' S' = ablocks B (d_ly d) (d_S d) ++ [(q - HEAD, d_n d + HEAD)])) ->
  dec_kept B d W' mem'.
Proof.
intros d memC mdC regsC ly' S' U' W' mem' md' kc HE HARU HK Hsp HJ HUOK' HUPO' HFH' HBL.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & _ & C3 & _).
destruct HK as (HV & HWK & HCS & HRO).
destruct HE as (_ & HFH & _ & _ & _ & _ & HWS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPL).
pose proof HJ as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & J13 & J14 & J15 & J16 & J17).
pose proof J15 as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & _ & Htop2).
unfold d_sp, DEC_F in *.
assert (HAR0 : AR tfibsegs B (d_ly d) (d_S d) (d_W d) (unpoison (d_U d) memC) mdC) by exact (proj1 HARU).
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact J1 | split; assumption]).
(* the stack above the callee's window: raw bytes kept *)
assert (SEQ : forall a, spZ (d_regs d) <= a < 2 ^ 47 ->
  aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H (d_W d)) memC a).
{ intros a Ha.
  rewrite <- (fsw_aview_unpoison_high B ly' S' U' W' mem' md' a HARU' ltac:(lia)).
  rewrite <- (fsw_aview_unpoison_high B (d_ly d) (d_S d) (d_U d) (d_W d) memC mdC a HARU ltac:(lia)).
  apply J9; lia. }
(* the 8 bytes of *lenp: kept in both placements *)
assert (KEQ : forall a, d_lenp d <= a < d_lenp d + 8 ->
  aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H (d_W d)) memC a).
{ intros a Ha. destruct HPL as [(_ & Hsl & Hlo & _ & Hot & _) | (_ & Hot & (cid & pos & Hcp & Hfr) & _)].
  - apply SEQ. lia.
  - pose proof (Hfr a Ha) as Hz. unfold in_zr, frame_rng in Hz. cbn [fst snd] in Hz.
    destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ cid pos HAR0 Hcp) as (FB1 & FB2 & FB3).
    assert (Hd : 0 <= a < 2 ^ 64 /\ (a < SHADOW_OFF \/ kHighMemBeg <= a))
      by (unfold in_app, kLowShadowBeg, ASAN_CEIL in FB3; unfold SHADOW_OFF; lia).
    rewrite <- (decK_unp_data ly' S' U' W' mem' md' a HARU' (proj1 Hd) (proj2 Hd)).
    rewrite <- (decK_unp_data (d_ly d) (d_S d) (d_U d) (d_W d) memC mdC a HARU (proj1 Hd) (proj2 Hd)).
    apply (J12 cid pos a Hcp (or_introl (Hfr a Ha))).
    intros Hf. exact (frm_img tfibsegs B LAWS _ _ _ _ _ cid pos a HAR0 Hcp Hz (decE_pstat_img a Hf)). }
(* (d) the read-only view *)
assert (HRO' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem')).
{ intros a Hro Hno Her. pose proof (decK_ro_img a Hro) as Hi. pose proof (fs_segs_img a Hi) as Hb.
  assert (Hd : 0 <= a < 2 ^ 64 /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)) by (unfold FS_IMG_END, SHADOW_OFF in *; lia).
  rewrite <- (decK_unp_data ly' S' U' W' mem' md' a HARU' (proj1 Hd) (proj2 Hd)).
  rewrite (J11 a Hi Hno Her (decK_ro_not_pstat a Hro) (fp_spares_closed FS_PSTAT_FP a decK_pstat_closed)).
  rewrite (decK_unp_data (d_ly d) (d_S d) (d_U d) (d_W d) memC mdC a HARU (proj1 Hd) (proj2 Hd)).
  exact (HRO a Hro Hno Her). }
unfold dec_kept, d_sp.
split.
(* (a) *lenp's value *)
{ intros k Hk. rewrite (mbyte_of_aview tfibsegs (w_H (d_W d)) (w_H W') memC mem' (d_lenp d + Z.of_nat k)
    (KEQ (d_lenp d + Z.of_nat k) ltac:(lia))).
  exact (HV k Hk). }
split.
(* (b) the window slack [sp, ot) outside *lenp *)
{ intros a Ha Hn. destruct (HWK a Ha Hn) as (W1 & W2).
  destruct HPL as [(_ & Hsl & Hlo & _ & Hot & _) | (_ & Hot & _)]; [|lia].
  assert (M1 : mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H (d_W d)) memC) a)
    by (apply (mbyte_of_aview tfibsegs); apply SEQ; lia).
  split; [rewrite M1; exact W1|].
  assert (Hni : ~ in_img tfibsegs a) by (intros Hi; pose proof (fs_segs_img a Hi); unfold FS_IMG_END in *; lia).
  pose proof (decE_restrict_of_mbyte _ _ _ _ a ltac:(lia) Hni M1) as RAW.
  assert (WEQ : writable_at tfibsegs (mrestrict (w_H (d_W d)) memC) a <->
                writable_at tfibsegs (mrestrict (w_H W') mem') a)
    by (unfold writable_at, wview; rewrite RAW; reflexivity).
  exact (iff_trans W2 WEQ). }
split; [|exact HRO'].
(* (c) the text *)
set (LEN := Z.of_nat (length (d_tb d))) in *.
assert (BLK : forall b m, In (b, m) (ablocks B (d_ly d) (d_S d)) -> b <= d_text d -> d_text d + LEN + 1 <= b + m ->
  (forall r, In r (d_U d) -> fst r + snd r <= d_text d \/ d_text d + LEN + 1 <= fst r) ->
  cstr_ok tfibsegs W' mem' (d_text d) (d_tb d)).
{ intros b m Hin Hb Hbm HU0.
  assert (Hin' : In (b, m) (ablocks B ly' S'))
    by (destruct HBL as [(_ & ->) | (q & _ & ->)]; [exact Hin | apply in_or_app; left; exact Hin]).
  pose proof HCS as ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & _).
  assert (Hm : 0 < m) by lia.
  assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  assert (Hcu : cstr tfibsegs (d_W d) (unpoison (d_U d) memC) (d_text d) (d_tb d)).
  { split; [|exact Hnz]. apply (garr8_frame tfibsegs _ _ (d_text d) (d_tb d ++ [0]) Hg).
    intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
    apply (mbyte_of_aview tfibsegs).
    destruct (decK_amem_data (d_text d) (LEN + 8) a H4096 Ham ltac:(lia)) as [Ha1 Ha2].
    exact (decK_unp_data _ _ _ _ _ _ a HARU Ha1 Ha2). }
  assert (HC1 : cstr_ok tfibsegs W' (unpoison U' mem') (d_text d) (d_tb d)).
  { apply (decK_cstr_blk STK_fuzz_malloc (spZ regsC) FS_PSTAT_FP (d_ly d) (d_S d) (d_W d) (unpoison (d_U d) memC) mdC []
      ly' S' W' (unpoison U' mem') md' kc (d_text d) (d_tb d) b m HJ Hin Hin' Hb Hbm);
      [| exact Hcu | exact H4096 | exact Hcl | lia | exact Ham].
    intros a Ha Hf. apply (blk_img tfibsegs B LAWS _ _ _ _ _ b m a HAR0 Hin); [rewrite Hrq; lia | exact (decE_pstat_img a Hf)]. }
  apply (decK_cstr_unp ly' S' U' W' mem' md' _ _ HARU' HC1).
  intros y Hy. apply (decK_ush_out U' (d_text d) (LEN + 1)); [|lia].
  intros r Hr. destruct (upoison_ok_In B ly' S' U' r HUOK' Hr) as (A8 & _ & C8 & _).
  split; [exact A8|]. split; [exact C8|].
  destruct HBL as [(-> & _) | (q & -> & HBq)].
  - destruct (HU0 r Hr); lia.
  - apply in_app_or in Hr as [Hr | [<- | []]]; [destruct (HU0 r Hr); lia|].
    pose proof (decK_new_disj ly' S' W' _ md' (ablocks B (d_ly d) (d_S d)) b m (q - HEAD) (d_n d + HEAD)
      J1 HBq Hin) as D.
    unfold zdisjoint in D. cbn [fst snd] in D |- *.
    assert (Hn0 : 0 <= d_n d) by (unfold d_n, dec_size; pose proof (Z.div_pos (Z.of_nat (length (d_tb d))) 4 ltac:(lia) ltac:(lia)); lia).
    assert (Hrq' : req_size (d_n d + HEAD) = d_n d + HEAD) by (unfold req_size, HEAD in *; destruct (Z.eqb_spec (d_n d + 16) 0); lia).
    rewrite Hrq, Hrq' in D. unfold HEAD in *. lia. }
destruct HWS as [(E0 & _) | [(p0 & k0 & _ & (HinB & Hp16 & Hk0 & _) & Hps & Hpe) |
  [(p0 & k0 & _ & HinB & Hps & Hpe & HU) | (l & Hinl & _)]]].
- destruct (d_tb d); discriminate E0.
- rewrite length_app in Hpe. cbn [length] in Hpe.
  assert (Hrq : req_size (k0 + HEAD) = k0 + HEAD) by (unfold req_size, HEAD in *; destruct (Z.eqb_spec (k0 + 16) 0); lia).
  apply (BLK (p0 - HEAD) (k0 + HEAD) HinB); [unfold HEAD; lia | unfold LEN, HEAD; lia |].
  intros r Hr.
  destruct (decK_heads_disj (d_ly d) (d_S d) (d_U d) (d_W d) (unpoison (d_U d) memC) mdC (p0 - HEAD) (k0 + HEAD)
    (d_text d) (LEN + 1) HAR0 HFH HinB ltac:(unfold HEAD; lia) ltac:(rewrite Hrq; unfold LEN, HEAD; lia) r Hr); lia.
- rewrite length_app in Hpe. cbn [length] in Hpe.
  apply (BLK p0 k0 HinB Hps); [unfold LEN; lia|].
  intros r Hr. destruct (HU r Hr) as [X|X]; [left; exact X | right; rewrite length_app in X; cbn [length] in X; unfold LEN; lia].
- (* a read-only table string: the same string as the table's entry (the bytes at the start), then fs_img_facts at
     the end state; its shadow bytes are no block granule's (blk_img) *)
  pose proof HIMG as (_ & HIM).
  pose proof (decK_aro_unp _ _ _ _ _ _ HARU HRO) as HROu0.
  destruct (HIM _ _ _ _ _ HAR0 HROu0) as (_ & _ & HS0 & _).
  pose proof (proj1 (proj1 (Forall_forall _ _) HS0 (d_text d, l) Hinl)) as HCl0. cbn [fst snd] in HCl0.
  destruct HCl0 as ((Hgl & Hnzl) & Hl4096 & Hlcl & _ & Hlam & _).
  pose proof HCS as ((Hg & Hnz) & _).
  assert (Hgl' : garr8 tfibsegs (mrestrict (w_H (d_W d)) memC) (d_text d) (l ++ [0])).
  { apply (garr8_frame tfibsegs _ _ (d_text d) (l ++ [0]) Hgl). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
    apply (mbyte_of_aview tfibsegs).
    destruct (decK_amem_data (d_text d) (Z.of_nat (length l) + 8) a ltac:(lia) Hlam ltac:(lia)) as [Ha1 Ha2].
    symmetry. exact (decK_unp_data _ _ _ _ _ _ a HARU Ha1 Ha2). }
  pose proof (decK_cstr_same _ (d_tb d) l (d_text d) Hg Hgl' Hnz Hnzl) as Etl. subst l.
  pose proof (decK_aro_unp ly' S' U' W' mem' md' HARU' HRO') as HROu'.
  destruct (HIM _ _ _ _ _ J1 HROu') as (_ & _ & HS1 & _).
  pose proof (proj1 (proj1 (Forall_forall _ _) HS1 (d_text d, d_tb d) Hinl)) as HC1. cbn [fst snd] in HC1.
  apply (decK_cstr_unp ly' S' U' W' mem' md' _ _ HARU' HC1).
  intros y Hy.
  pose proof (decK_ro_strs_img (d_text d) (d_tb d) y Hinl Hy) as Hiy.
  pose proof (fs_segs_img y Hiy) as Hyb.
  assert (NB : forall p n, In (p, n) (ablocks B ly' S') -> ~ (p <= y < p + req_size n))
    by (intros p n Hpn Hr; exact (blk_img tfibsegs B LAWS _ _ _ _ _ p n y J1 Hpn Hr Hiy)).
  pose proof (ARU_shadow_out_block tfibsegs B ly' S' U' W' mem' md' y HARU' ltac:(unfold FS_IMG_END in Hyb; lia) NB) as X.
  rewrite wz in X; [exact X|]. apply decK_sh_range. unfold FS_IMG_END in Hyb. lia.
Qed.

(* ---- the callees and the one kit step the spine takes as hypotheses ---- *)
(* strlen's contract (FSH_Gen astrlen_realizesU at fs.asan's PC_strlen; owner RUNTIME, FSH_Rt.v FsRt.fr_strlen) *)
Hypothesis HSTRLEN : astrlen_realizesU tfibsegs B PC_strlen.
(* fuzz_malloc's contract (FSH_Fn_alloc.v fuzz_malloc_spec; owner ALLOC) *)
Hypothesis HMALLOC : fuzz_malloc_spec tfibsegs B.
(* the resume after the program call is FSW_K3's proved fsw_after_callFPU_args (kit head hv5a; it was a Section
   hypothesis here while S0 had not adopted RELOC's YCbq) *)

(* ---- the spine: entry -> strlen -> fuzz_malloc, to the resumed state at 0x84880 (decE_res) in both arms; the
   arms' continuations are the spine's premises ---- *)
Lemma decE_spine : forall d, dec_entry_ok B d ->
  (forall W' ly' S' regs' mem' md',
     d_cnt d = d_fail d -> decE_res B d W' ly' S' (d_U d) regs' mem' md' 0 -> getr regs' 10 = w64 0 ->
     ablocks B ly' S' = ablocks B (d_ly d) (d_S d) ->
     fs_glob tfibsegs W' mem' (d_live d) (d_peak d) (d_cnt d + 1) SIZE_MAXZ ->
     SRr tfibsegs W' (mkCfg (YK11.mkst regs' (Z_to_bv 64 DEC_RA_MALLOC) mem' (YK11.seg_rom tfibsegs)) md') (dec_post B d)) ->
  (forall q W' ly' S' regs' mem' md',
     d_cnt d <> d_fail d -> decE_res B d W' ly' S' (d_U d ++ [(q - HEAD, HEAD)]) regs' mem' md' 1 ->
     getr regs' 10 = w64 q -> 4096 + HEAD <= q ->
     ablocks B ly' S' = ablocks B (d_ly d) (d_S d) ++ [(q - HEAD, d_n d + HEAD)] ->
     fs_heads B ly' S' (d_U d ++ [(q - HEAD, HEAD)]) ->
     fs_rblock tfibsegs B ly' S' W' mem' q (d_n d) ->
     range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF q (d_n d) ->
     fs_glob tfibsegs W' mem' (d_live d + d_n d) (Z.max (d_peak d) (d_live d + d_n d)) (d_cnt d + 1) (d_fail d) ->
     SRr tfibsegs W' (mkCfg (YK11.mkst regs' (Z_to_bv 64 DEC_RA_MALLOC) mem' (YK11.seg_rom tfibsegs)) md') (dec_post B d)) ->
  SRr tfibsegs (d_W d) (cfg_at tfibsegs A_preset_base64_decode (d_regs d) (d_mem d) (d_md d)) (dec_post B d).
Proof.
intros d Hd KN KQ.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : STK_preset_base64_decode = ltac:(let v := eval vm_compute in STK_preset_base64_decode in exact v)) by reflexivity.
assert (FM : STK_fuzz_malloc = ltac:(let v := eval vm_compute in STK_fuzz_malloc in exact v)) by reflexivity.
assert (FR : STK_RT_STR = ltac:(let v := eval vm_compute in STK_RT_STR in exact v)) by reflexivity.
assert (FE : ESTACK = 4096) by reflexivity.
pose proof Hd as Hd0.
destruct d as [ly S U W regs mem md ch ot text lenp tb live peak cnt fail v FP].
unfold dec_entry_ok in Hd0.
cbn [d_ly d_S d_U d_W d_regs d_mem d_md d_ch d_ot d_text d_lenp d_tb d_live d_peak d_cnt d_fail d_v d_FP] in Hd0.
cbn [d_ly d_S d_U d_W d_regs d_mem d_md d_ch d_ot d_text d_lenp d_tb d_live d_peak d_cnt d_fail d_v d_FP d_n] in KN, KQ |- *.
set (d := mkDE ly S U W regs mem md ch ot text lenp tb live peak cnt fail v FP) in *.
destruct Hd0 as (HPRE & HH & HFRL & H10 & H11 & HCS & HWS & HBO & HLEN & Hl8 & HV & Hv & HDJ & HGL & HEV & HLV
  & HLIVE & HCNT & HPL).
destruct HPRE as (HPREU & HRO).
pose proof (fsw_ARU B STK_preset_base64_decode _ _ _ _ _ _ _ _ HPREU) as HARU0.
pose proof HPREU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HCS as (_ & Htx4 & Htxc & Htx32 & _).
(* the placement facts both arms share *)
assert (HLP : 0 <= lenp /\ lenp + 8 <= 2 ^ 64 /\ (lenp + 8 <= alloc_ceiling \/ spZ regs <= lenp) /\
  spZ regs <= ot <= 2 ^ 47).
{ destruct HPL as [(HFP & Hsl & Hlo & Hot16 & Hottop & Hpot & Hchl) | (HFP & Hot & (cid & pos & Hcp & Hin) & Hpl)].
  - lia.
  - destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md cid pos HAR Hcp) as (F1 & F2 & _).
    pose proof (Hin lenp ltac:(lia)) as I1. pose proof (Hin (lenp + 7) ltac:(lia)) as I2.
    cbv [in_zr frame_rng fst snd] in I1, I2. lia. }
destruct HLP as (Hl0 & Hl64 & Hlpl & Hotb).
assert (Hsplo : alloc_ceiling + 16528 <= spZ regs) by (rewrite FS in Hslo; lia).
assert (HK0 : dec_kept B d W mem).
{ split; [exact HV|]. split; [intros a _ _; split; [reflexivity | tauto]|]. split; [exact HCS | exact HRO]. }
(* ---- entry state and the journal at the entry sp ---- *)
assert (HS : st_ok tfibsegs (Ereg regs fs_extraT) (fss0T A_preset_base64_decode 112)
  (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 A_preset_base64_decode) mem (YK11.seg_rom tfibsegs)))).
{ apply (fsw_entryT B STK_preset_base64_decode 112 ly S U W regs mem md ch A_preset_base64_decode
    (proj1 HSS) (proj2 HSS) HPREU); [rewrite FS; lia | vm_compute; reflexivity]. }
set (E := Ereg regs fs_extraT) in HS.
assert (E2 : bv_unsigned (ew E 2) = spZ regs)
  by (unfold E; rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
assert (HJ : ajournal tfibsegs B STK_preset_base64_decode (spZ regs) FP ly S W (unpoison U mem) md []
               ly S W (unpoison U mem) md 0)
  by exact (ajournal_init tfibsegs B STK_preset_base64_decode FP ly S W regs (unpoison U mem) md ch HAP).
(* ---- run 1: entry -> PC_strlen ---- *)
unfold cfg_at.
fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARU0 PC_strlen.
{ cbv [fss0T fsT_regions ss_mem].
  eapply awr_ok_cons_stack with (n := 2%nat);
    [reflexivity | exact E2 | cbv [fstk YP09.r_wlo]; rewrite FS; lia | cbv [fstk YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil. }
rename ms into ms1.
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdT := m) in * end.
assert (AV1 : decE_avk d W mem (ms_mem ms1)).
{ apply (decE_frame_avk d W E _ mem (ms_mem ms1) HF).
  intros r a Hin Ha. cbv [fss0T fsT_regions ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbv [fstk fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    try rewrite E2 in Ha; change (d_sp d) with (spZ regs); rewrite FS in Hslo; lia. }
assert (Hspc : alloc_ceiling <= d_sp d) by (change (d_sp d) with (spZ regs); rewrite FS in Hslo; lia).
assert (Hotc : d_ot d <= 2 ^ 47) by (change (d_ot d) with ot; lia).
pose proof (decE_kept_avk B d W mem (ms_mem ms1) Hspc Hl0 Hlpl Hl64 Hotc AV1 HK0) as HK1.
assert (AVB1 : forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) mem a)
  by (intros a Ha; apply AV1; lia).
pose proof (decE_glob_av W mem (ms_mem ms1) live peak cnt fail AVB1 HGL) as HG1.
pose proof (fsw_reg_lit _ E _ ms1 1%bv DEC_RA_STRLEN HS ltac:(vm_compute; reflexivity)
  ltac:(unfold DEC_RA_STRLEN; lia)) as R1.
pose proof (fsw_reg_off _ E _ ms1 2%bv 2 (-112) (spZ regs) HS ltac:(vm_compute; reflexivity) E2 ltac:(lia)) as R2.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms1 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms1 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms1 8%bv 11%bv 11 HS ltac:(vm_compute; reflexivity) eq_refl) as R8.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms1 10%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms1 18%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl) as R18.
pose proof (fsw_reg_extra _ regs fs_extraT _ ms1 21%bv 0 HS ltac:(vm_compute; reflexivity)) as R21.
cbn [nth fs_extraT] in R21.
assert (RK1 : forall r, In r decE_kregs -> getr (ms_regs ms1) r = getr regs r).
{ intros r Hr. cbv [decE_kregs In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- getr _ ?r = _ =>
    let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
    exact (fsw_reg_atom _ regs fs_extraT _ ms1 r r n HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
  end. }
assert (Hspt : spZ (ms_regs ms1) = spZ regs - 112) by (unfold spZ at 1; rewrite R2; lia).
assert (HFR1 : dec_frame_ok W (ms_mem ms1) (spZ regs - 112) regs).
{ apply decE_frame_of_cs0.
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    pose proof (fsw_region_nth E ss (restrict (w_H W) ms1) 0 _ HS eq_refl) as HR0 end.
  destruct HR0 as (_ & _ & _ & HC0). cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in HC0.
  rewrite E2 in HC0. exact HC0. }
clear HF HFr HG.
(* ---- the call of strlen (pc PC_strlen, ra 0x8486c, a0 = text) ---- *)
pose proof HK1 as (K1v & K1w & K1c & K1r).
pose proof HARU0 as (HAR1 & HUOK0 & HPO1).
assert (HRO1u : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U (ms_mem ms1)))).
{ intros a Ha Ho He.
  assert (Hb : 0 <= a < SHADOW_OFF).
  { destruct Ha as [(sg & Hin & Hw & Hr) | Hr]; [|unfold FS_RLO, FS_RHI in Hr; unfold SHADOW_OFF; lia].
    assert (Hi : in_img tfibsegs a) by (exists sg; split; [exact Hin | exact Hr]).
    pose proof (fs_segs_img a Hi) as Hl. unfold FS_IMG_END in Hl. unfold SHADOW_OFF; lia. }
  assert (Hb64 : 0 <= a < 2 ^ 64) by (unfold SHADOW_OFF in Hb; lia).
  rewrite (decK_unp_data ly S U W (ms_mem ms1) mdT a HARU0 Hb64 (or_introl (proj2 Hb))). exact (K1r a Ha Ho He). }
assert (HROM1 : rom_view tfibsegs W (ms_mem ms1)).
{ pose proof HIMG as (_ & HIM).
  destruct (HIM ly S W (unpoison U (ms_mem ms1)) mdT HAR1 HRO1u) as (HRV & _).
  intros a Ha. pose proof Ha as (sg & Hin & Hw & Hr).
  assert (Hi : in_img tfibsegs a) by (exists sg; split; [exact Hin | exact Hr]).
  pose proof (fs_segs_img a Hi) as Hl.
  assert (Hb : 0 <= a < SHADOW_OFF) by (unfold FS_IMG_END in Hl; unfold SHADOW_OFF; lia).
  assert (Hb64 : 0 <= a < 2 ^ 64) by (unfold SHADOW_OFF in Hb; lia).
  rewrite <- (decK_unp_data ly S U W (ms_mem ms1) mdT a HARU0 Hb64 (or_introl (proj2 Hb))). exact (HRV a Ha). }
assert (HPRE1 : ecall_preU_k tfibsegs B STK_RT_STR ly S U W (ms_regs ms1) (ms_mem ms1) mdT).
{ apply (fsw_ecall_preU_k_at B STK_preset_base64_decode (spZ regs) FP ly S W (unpoison U mem) md [] ly S U W
    (ms_mem ms1) mdT 0 (ms_regs ms1) (-112) STK_RT_STR HJ HARU0).
  - rewrite Hspt. lia.
  - reflexivity.
  - lia.
  - rewrite FE, FS. lia.
  - rewrite FR. lia.
  - rewrite FR, FS. lia.
  - rewrite R1. apply ret_ok_even. rewrite unsigned_lit_small by (unfold DEC_RA_STRLEN; lia). reflexivity.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp. }
assert (H10T : getr (ms_regs ms1) 10 = w64 text) by (rewrite R10; exact H10).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms1 HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ apply (fsw_intrin_atU B STK_preset_base64_decode (spZ regs) FP ly S W (unpoison U mem) md [] ly S U W (ms_mem ms1)
    mdT 0 U (fun a => spZ (ms_regs ms1) - STK_RT_STR <= a < spZ (ms_regs ms1)) (Z_to_bv 64 DEC_RA_STRLEN) _
    (fun regs2 mem2 md2 => aregs_preserved (ms_regs ms1) regs2 /\ getr regs2 10 = w64 (Z.of_nat (length tb)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (ms_regs ms1) - STK_RT_STR <= a < spZ (ms_regs ms1)) ->
          aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) (ms_mem ms1) a)) HJ).
  - eapply SRr_mono; [exact (HSTRLEN ly S U W (ms_regs ms1) (ms_mem ms1) mdT text tb HPRE1 HROM1 H10T K1c)|].
    intros W2 c2 _ (EW & regs2 & mem2 & md2 & v0 & Ec & HAR2 & PO2 & HP2 & Hsame & H10v & Hv0 & Hlen & Hfr & Hgr).
    split; [exact EW|]. exists regs2, mem2, md2.
    split.
    { rewrite Ec. unfold cfg_at, raZ, w64. rewrite R1, unsigned_lit_small by (unfold DEC_RA_STRLEN; lia).
      reflexivity. }
    split; [split; [exact HAR2 | split; [exact HUOK0 | exact PO2]]|].
    split; [exact Hsame|].
    split.
    { intros a Ha Hn. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Eu.
      - apply (aview_unpoison_in tfibsegs). exact Eu.
      - rewrite (aview_unpoison_out tfibsegs (w_H W) U mem2 a Eu),
          (aview_unpoison_out tfibsegs (w_H W) U (ms_mem ms1) a Eu).
        exact (Hfr a Ha Hn). }
    split.
    { intros a (Hh & b & Hb). split; [exact Hh|]. unfold unpoison in Hb |- *.
      destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))); [eexists; reflexivity|].
      destruct (Hgr a (conj Hh (ex_intro _ b Hb))) as (_ & b' & Hb'). exists b'. exact Hb'. }
    split; [exact HP2|]. split; [rewrite H10v, Hlen; reflexivity|]. exact Hfr.
  - intros a Ha. left; left. rewrite Hspt, FR in Ha. rewrite FS. lia. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & H102 & Hfr2).
(* ---- the resumed state at 0x8486c ---- *)
assert (RK2 : forall r, In r decE_kregs -> getr regs2 r = getr regs r).
{ intros r Hr. rewrite <- (RK1 r Hr). apply (fsw_pres _ _ r HP2).
  cbv [decE_kregs In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]; decE_cs_side. }
assert (Hsp2 : spZ regs2 = spZ regs - 112).
{ unfold spZ at 1. rewrite (fsw_pres _ _ 2%bv HP2) by decE_cs_side. exact Hspt. }
assert (KEEP2 : forall a, spZ regs - 112 <= a < spZ regs ->
  mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms1)) a).
{ intros a Ha. apply (mbyte_of_aview tfibsegs). apply Hfr2; [lia|]. rewrite Hspt, FR. lia. }
assert (AV2 : decE_avk d W (ms_mem ms1) mem2).
{ intros a Ha Hs. apply Hfr2; [exact Ha|]. rewrite Hspt, FR. change (d_sp d) with (spZ regs) in Hs. lia. }
pose proof (decE_kept_avk B d W (ms_mem ms1) mem2 Hspc Hl0 Hlpl Hl64 Hotc AV2 HK1) as HK2.
assert (AVB2 : forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) (ms_mem ms1) a)
  by (intros a Ha; apply AV2; lia).
pose proof (decE_glob_av W _ mem2 live peak cnt fail AVB2 HG1) as HG2.
assert (HPD2 : pairwise_disjoint (Ereg regs2 (fs_extraT ++ decE_xs d)) (fsT_ret_regions 112 decE_cs [])).
{ apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region.
  cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl). change (bv_unsigned (getr regs2 2)) with (spZ regs2). rewrite Hsp2.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia]. }
assert (HS2 : st_ok tfibsegs (Ereg regs2 (fs_extraT ++ decE_xs d)) (fss_retT DEC_RA_STRLEN 112 decE_cs [] [])
  (restrict (w_H W) (YK11.mkst regs2 (Z_to_bv 64 DEC_RA_STRLEN) mem2 (YK11.seg_rom tfibsegs)))).
{ apply (fsw_resume_after_rtU_args B STK_preset_base64_decode (spZ regs) FP ly S W (unpoison U mem) md [] ly S U W
    mem2 md2 0 (ms_regs ms1) regs2 (ms_mem ms1) 112 (decE_xs d) decE_cs [] [] DEC_RA_STRLEN (proj1 HSS) (proj2 HSS)
    HJ2 HARU2 HP2 Hspt).
  - lia.
  - rewrite FS. lia.
  - reflexivity.
  - vm_compute. reflexivity.
  - repeat constructor; cbn; lia.
  - exact (decE_chunks_of_frame d W (ms_mem ms1) (spZ regs - 112) regs2 RK2 HFR1).
  - exact KEEP2.
  - constructor.
  - exact HPD2.
  - exact I. }
clear HS.
(* ---- run 2: 0x8486c -> A_fuzz_malloc ---- *)
fsw_aj_run_toU fsw_wr_tbl_ok HS2 HJ2 HARU2 A_fuzz_malloc.
{ cbv [fss_retT fsT_ret_regions ss_mem app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -112);
    [reflexivity
    | rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); change (bv_unsigned (getr regs2 2)) with (spZ regs2); lia
    | cbv [fstk_ret YP09.r_wlo]; rewrite FS; lia | cbv [fstk_ret YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil. }
rename ms into ms3.
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdC := m) in * end.
(* ---- at the fuzz_malloc call (pc A_fuzz_malloc, ra 0x84880, a0 = dec_size tb, s0 = lenp) ---- *)
assert (AV3 : decE_avk d W mem2 (ms_mem ms3)).
{ apply (decE_frame_avk d W _ _ mem2 (ms_mem ms3) HF).
  intros r a Hin Ha. cbv [fss_retT fsT_ret_regions ss_mem app In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbv [fstk_ret fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    try (rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl) in Ha;
         change (bv_unsigned (getr regs2 2)) with (spZ regs2) in Ha);
    change (d_sp d) with (spZ regs); lia. }
clear HF HFr HG.
pose proof (decE_kept_avk B d W mem2 (ms_mem ms3) Hspc Hl0 Hlpl Hl64 Hotc AV3 HK2) as HK3.
assert (AVB3 : forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) (ms_mem ms3) a = aview tfibsegs (w_H W) mem2 a)
  by (intros a Ha; apply AV3; lia).
pose proof (decE_glob_av W _ _ live peak cnt fail AVB3 HG2) as HG3.
pose proof (fsw_reg_lit _ _ _ ms3 1%bv DEC_RA_MALLOC HS2 ltac:(vm_compute; reflexivity)
  ltac:(unfold DEC_RA_MALLOC; lia)) as R1c.
assert (PC : forall r : bv 5, In r decE_csl ->
  getr (ms_regs ms3) r = getr (ms_regs ms1) r).
{ intros r Hr. cbv [decE_csl In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- getr _ ?r = _ =>
    let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
    rewrite (fsw_reg_atom _ regs2 _ _ ms3 r r n HS2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
    apply (fsw_pres _ _ r HP2); decE_cs_side end. }
assert (I2 : In (2%bv : bv 5) decE_csl) by (cbv [decE_csl]; decE_in).
assert (I3 : In (3%bv : bv 5) decE_csl) by (cbv [decE_csl]; decE_in).
assert (I4 : In (4%bv : bv 5) decE_csl) by (cbv [decE_csl]; decE_in).
assert (I8 : In (8%bv : bv 5) decE_csl) by (cbv [decE_csl]; decE_in).
assert (I18 : In (18%bv : bv 5) decE_csl) by (cbv [decE_csl]; decE_in).
assert (I21 : In (21%bv : bv 5) decE_csl) by (cbv [decE_csl]; decE_in).
assert (Hspc3 : spZ (ms_regs ms3) = spZ regs - 112) by (unfold spZ at 1; rewrite (PC 2%bv I2); exact Hspt).
assert (Hs0c : s0Z (ms_regs ms3) = lenp).
{ unfold s0Z. rewrite (PC 8%bv I8), R8, H11. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (R10c : getr (ms_regs ms3) 10 = w64 (dec_size tb)).
{ lazymatch type of HS2 with st_ok _ _ ?ss _ =>
    rewrite (st_ok_restrict_reg tfibsegs (w_H W) _ ss ms3 10%bv HS2);
    assert (Hr10 : sr_get (ss_regs ss) 10%bv = decE_size_sv) by (vm_compute; reflexivity) end.
  rewrite Hr10. unfold w64, dec_size. apply decE_size_den; [|lia].
  rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl). exact H102. }
(* the callee's chain from s0 = lenp: in the fake frame lenp is below alloc_ceiling (chain []); on the real stack the
   entry's chain (dec_chain_lenp) reads only words >= sp, which the walk leaves as they were *)
assert (HCH : exists ch1, achain ly (aview tfibsegs (w_H W) (unpoison U (ms_mem ms3))) (spZ regs - 112) lenp ch1).
{ destruct HPL as [(HFP & Hsl & Hlo & Hot16 & Hottop & Hpot & (chl & Hchl)) | (HFP & Hot & (cid & pos & Hcp & Hin) & Hpl)].
  - exists chl.
    apply (achain_lower ly _ (spZ regs) (spZ regs - 112) lenp chl); [|lia].
    apply (achain_kept ly (aview tfibsegs (w_H W) (unpoison U mem)) _ (spZ regs) lenp chl (spZ regs) Hchl); [lia | lia |].
    intros a Ha. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & J9 & _). apply J9; lia.
  - exists []. apply achain_low.
    destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md cid pos HAR Hcp) as (F1 & F2 & _).
    assert (Hlb : lenp <= lenp < lenp + 8) by lia. pose proof (Hin lenp Hlb) as I1.
    cbv [in_zr frame_rng fst snd] in I1. lia. }
destruct HCH as (ch1 & Hach).
pose proof HARU2 as (HAR3 & HUOK3 & HPO3).
pose proof HK3 as (K3v & K3w & K3c & K3r).
assert (HPREc : fpreU tfibsegs B STK_fuzz_malloc ly S U W (ms_regs ms3) (ms_mem ms3) mdC ch1).
{ apply (fsw_fpreU_atFP B STK_preset_base64_decode (spZ regs) FP ly S U W (unpoison U mem) md [] ly S W
    (ms_mem ms3) mdC 0 (ms_regs ms3) STK_fuzz_malloc (-112) ch1 HJ2 HARU2 K3r).
  - rewrite Hspc3. lia.
  - reflexivity.
  - lia.
  - rewrite FM. lia.
  - rewrite FS, FM. lia.
  - rewrite R1c. apply ret_ok_even. rewrite unsigned_lit_small by (unfold DEC_RA_MALLOC; lia). reflexivity.
  - unfold raZ. rewrite R1c, unsigned_lit_small by (unfold DEC_RA_MALLOC; lia). unfold DEC_RA_MALLOC. lia.
  - rewrite (PC 3%bv I3), R3. exact Hgp.
  - rewrite (PC 4%bv I4), R4. exact Htp.
  - rewrite Hspc3, Hs0c. exact Hach. }
assert (HN1 : 0 <= Z.of_nat (length tb) / 4 <= 2 ^ 26)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (Hn1 : 1 <= dec_size tb) by (unfold dec_size; lia).
assert (Hn0 : 0 < dec_size tb) by lia.
assert (Hn2 : dec_size tb + HEAD < MALLOC_MAX) by (unfold dec_size, HEAD, MALLOC_MAX; lia).
assert (Hev1 : 1 <= dec_ev tb)
  by (unfold dec_ev, EV_fuzz_malloc, EV_preset_base64_decode; destruct (WriterSpec.b64_dec tb); lia).
assert (HEV1 : st_nev S + 1 <= EV_MAX) by lia.
assert (HLV1 : blocks_bytes S + (dec_size tb + HEAD) <= LIVE_MAX) by exact HLV.
(* ---- the resume after fuzz_malloc, common to both arms ---- *)
assert (HFPS : fsw_fp_sub B ly S ly S [] FP FS_PSTAT_FP).
{ intros a Ha. right; right; left. split; [|exact (decE_pstat_img a Ha)].
  destruct HPL as [(HFP & _) | (HFP & _)]; rewrite HFP; [exact Ha|].
  destruct Ha as (r0 & Hr0 & Ha0). exists r0. split; [apply in_or_app; left; exact Hr0 | exact Ha0]. }
assert (HFR3 : dec_frame_ok W (ms_mem ms3) (spZ regs - 112) regs).
{ apply (decE_frame_of_chunks d W (ms_mem ms3) (spZ regs - 112) regs2 RK2).
  lazymatch type of HS2 with st_ok _ _ ?ss _ =>
    pose proof (fsw_region_nth _ ss (restrict (w_H W) ms3) 0 _ HS2 eq_refl) as HR0 end.
  destruct HR0 as (_ & _ & _ & HC0). cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in HC0.
  rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl) in HC0. change (bv_unsigned (getr regs2 2)) with (spZ regs2) in HC0.
  rewrite Hsp2 in HC0. exact HC0. }
assert (AFTER : forall W' ly' S' U' regs' mem' md' kc,
  ajournal tfibsegs B STK_fuzz_malloc (spZ (ms_regs ms3)) FS_PSTAT_FP ly S W (unpoison U (ms_mem ms3)) mdC []
    ly' S' W' (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' -> fs_heads B ly' S' U' ->
  aregs_preserved (ms_regs ms3) regs' ->
  ((U' = U /\ ablocks B ly' S' = ablocks B ly S) \/
   (exists q, U' = U ++ [(q - HEAD, HEAD)] /\ ablocks B ly' S' = ablocks B ly S ++ [(q - HEAD, dec_size tb + HEAD)])) ->
  decE_res B d W' ly' S' U' regs' mem' md' (0 + kc)).
{ intros W' ly' S' U' regs' mem' md' kc HJc OK' PO' HH' HP' HAR'.
  assert (PB : forall r : bv 5, In r decE_csl ->
    getr regs' r = getr (ms_regs ms1) r).
  { intros r Hr. rewrite <- (PC r Hr). apply (fsw_pres _ _ r HP').
    cbv [decE_csl In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]; decE_cs_side. }
  assert (RKc : forall r, In r decE_kregs -> getr regs' r = getr regs r).
  { intros r Hr. rewrite <- (RK1 r Hr). apply PB.
    cbv [decE_kregs In] in Hr. cbv [decE_csl]. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]; decE_in. }
  assert (Hspr : spZ regs' = spZ regs - 112) by (unfold spZ at 1; rewrite (PB 2%bv I2); exact Hspt).
  assert (HPD' : pairwise_disjoint (Ereg regs' (fs_extraT ++ decE_xs d)) (fsT_ret_regions 112 decE_cs [])).
  { apply pairwise_disjoint_of_extents.
    unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl). change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hspr.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia]. }
  assert (Hf1 : 0 < 112) by lia. assert (Hf2 : 0 <= STK_fuzz_malloc) by (rewrite FM; lia).
  assert (Hf3 : STK_fuzz_malloc + 112 <= STK_preset_base64_decode) by (rewrite FS, FM; lia).
  assert (Hf4 : 112 mod 16 = 0) by reflexivity.
  assert (Hwf : regions_wf (fsT_ret_regions 112 decE_cs []) = true) by (vm_compute; reflexivity).
  assert (Hbd : Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 112) decE_cs)
    by (repeat constructor; cbn; lia).
  pose proof (decE_chunks_of_frame d W (ms_mem ms3) (spZ regs - 112) regs' RKc HFR3) as Hcs.
  assert (Hrs : Forall (region_ok tfibsegs (Ereg regs' (fs_extraT ++ decE_xs d)) (mrestrict (w_H W') mem')) [])
    by constructor.
  assert (Hgf : atoms_ok (Ereg regs' (fs_extraT ++ decE_xs d)) []) by exact I.
  pose proof (fsw_after_callFPU_args B STK_preset_base64_decode (spZ regs) FP [] ly S U W mem md W ly S U (ms_mem ms3)
    mdC 0 STK_fuzz_malloc FS_PSTAT_FP 112 (ms_regs ms3) ly' S' U' W' regs' mem' md' kc (decE_xs d) decE_cs [] []
    DEC_RA_MALLOC (proj1 HSS) (proj2 HSS) HJ2 HARU2 HJc HFPS OK' PO' HP' Hspc3 Hf1 Hf2 Hf3 Hf4 Hwf Hbd Hcs Hrs HPD' Hgf)
    as (HJ' & HARU' & HS').
  pose proof (decE_kept_malloc d (ms_mem ms3) mdC (ms_regs ms3) ly' S' U' W' mem' md' kc Hd HARU2 HK3 Hspc3 HJc OK' PO' HH' HAR')
    as HK'.
  split; [exact HJ'|]. split; [exact HARU'|]. split; [exact HS'|].
  split; [exact Hspr|].
  split; [rewrite (PB 3%bv I3); exact R3|].
  split; [rewrite (PB 4%bv I4); exact R4|].
  split; [rewrite (PB 8%bv I8), R8; exact H11|].
  split; [rewrite (PB 18%bv I18), R18; exact H10|].
  split; [rewrite (PB 21%bv I21), R21; reflexivity|].
  split; [exact RKc|].
  exact HK'. }
(* ---- the call ---- *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms3 HS2 eq_refl). cbn [ss_pc].
eapply SRr_bind; [exact (HMALLOC ly S U W (ms_regs ms3) (ms_mem ms3) mdC ch1 (dec_size tb) live peak cnt fail
  HPREc HH R10c Hn1 Hn2 HG3 (fun _ => HLIVE) HCNT HEV1 (fun _ => HLV1))|].
intros W' c' _ [(Hcf & HQ1) | (Hcf & res & HQ2)].
- destruct HQ1 as (ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP' & H10' & Hbl' & HH' & HG').
  rewrite R1c.
  exact (KN W' ly' S' regs' mem' md' Hcf
    (AFTER W' ly' S' U regs' mem' md' 0 HJc OK' PO' HH' HP' (or_introl (conj eq_refl Hbl'))) H10' Hbl' HG').
- destruct HQ2 as (ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP' & H10' & Hres4 & Hbl' & HH' & Hrb & Hra'
    & HG').
  rewrite R1c.
  exact (KQ res W' ly' S' regs' mem' md' Hcf
    (AFTER W' ly' S' _ regs' mem' md' 1 HJc OK' PO' HH' HP' (or_intror (ex_intro _ res (conj eq_refl Hbl'))))
    H10' Hres4 Hbl' HH' (Hrb Hn0) Hra' HG').
Qed.

(* ---- the stage ---- *)
Lemma dec_entry_ok_stage : dec_stage_entry B.
Proof.
intros d Hd Hk. apply (decE_spine d Hd).
- intros W' ly' S' regs' mem' md' Hcf Hres H10 Hbl HG.
  exact (decE_null d W' ly' S' regs' mem' md' Hd Hcf Hres H10 Hbl HG).
- intros q W' ly' S' regs' mem' md' Hcf Hres H10 Hq Hbl HH Hrb Hra HG.
  exact (decE_nonnull d q W' ly' S' regs' mem' md' Hd Hcf Hres H10 Hq Hbl HH Hrb Hra HG Hk).
Qed.
End P.
