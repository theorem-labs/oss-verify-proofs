(* LLVMFuzzerTestOneInput 0x8091c (fuzz_manifest.c:293-321): the walk's context (llvmf_pre's facts in one record),
   the input's windows, and the concrete state at each point the walk resumes from (after the prologue: sp = sp0 - 64,
   ra, s0..s6 in their slots, s5 = the shadow base). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YCbp YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0l ACej FMPstat AE2k ACfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_llvmf0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* resume points *)
Definition LF_P0 : Z := 0x8097c.   (* k computed (s3 = k, s1 = size, a0 = data); next: snez s6, s1 *)
Definition LF_P1 : Z := 0x809c4.   (* both memchr calls done: s0 = un, s3 = tn; next: the 4 MiB test *)
Definition LF_P2 : Z := 0x809e0.   (* after check_no_overread (uri, un, text, tn) *)
Definition LF_P3 : Z := 0x80a24.   (* u = malloc (un + 1) holds uri's un bytes and a NUL (s1 = u); next: addi a0, s3, 1 *)
Definition LF_P4 : Z := 0x80a60.   (* t = malloc (tn + 1) holds text's tn bytes and a NUL (s4 = t); next: jal fuzz_alloc_live *)
Definition LF_P5 : Z := 0x80a8c.   (* after check_bounded_alloc (s2 = live, s3 = named) *)
Definition LF_P6 : Z := 0x80ab0.   (* after check_reject_clean_starved (t, u) *)
Definition LF_R : Z := 0x80ac8.    (* a0 := 0; the epilogue; ret (also the tn > 4 MiB exit) *)
Definition LF_FRAME : Z := 64.
(* the saved registers (ra, s0..s6) and their slots above sp0 - 64 *)
Definition lf_saved_regs : list Z := [1; 8; 9; 18; 19; 20; 21; 22].
Definition lf_saved_offs : list Z := [56; 48; 40; 32; 24; 16; 8; 0].
(* the callee-saved registers the body changes (sp, s0..s6); the others (gp, tp, s7..s11) keep their entry values *)
Definition lf_X : list Z := [2; 8; 9; 18; 19; 20; 21; 22].

(* llvmf_pre's facts, with fm_stat's peak named *)
Record lfx := mkLX {
  lx_ly : alayout; lx_S : astate; lx_W : world tfibsegs; lx_regs : bvmap 5 word; lx_mem : word -> option byte;
  lx_md : Model; lx_p : Z; lx_pl : list byte; lx_live : Z; lx_peak : Z; lx_cnt : Z }.
Definition lx_sp0 (cx : lfx) : Z := spZ (lx_regs cx).
Definition lx_n (cx : lfx) : Z := Z.of_nat (length (lx_pl cx)).
Definition lx_dl (cx : lfx) : list Z := map (fun b : byte => bv_unsigned b) (lx_pl cx).
(* fuzz_manifest.c:295-297: k, uri = data + (size ? 1 : 0), text = uri + k *)
Definition lx_s6 (cx : lfx) : Z := if lx_n cx =? 0 then 0 else 1.
Definition lx_k (cx : lfx) : Z := if lx_n cx =? 0 then 0 else Z.min (nth 0 (lx_dl cx) 0) (lx_n cx - 1).
Definition lx_uri (cx : lfx) : Z := lx_p cx + lx_s6 cx.
Definition lx_text (cx : lfx) : Z := lx_uri cx + lx_k cx.
(* the two windows memchr scans: k bytes at uri, size - (size ? 1 : 0) - k bytes at text *)
Definition lx_uw (cx : lfx) : list Z := firstn (Z.to_nat (lx_k cx)) (skipn (Z.to_nat (lx_s6 cx)) (lx_dl cx)).
Definition lx_tw (cx : lfx) : list Z := skipn (Z.to_nat (lx_s6 cx + lx_k cx)) (lx_dl cx).
(* fuzz_strnlen: the bytes before the first NUL of the window, or the whole window *)
Definition lf_cut (l : list Z) : list Z :=
  match ManifestModel.find_idx (fun c => c =? 0) l with Some j => firstn j l | None => l end.
Definition lx_ub (cx : lfx) : list Z := lf_cut (lx_uw cx).
Definition lx_tb (cx : lfx) : list Z := lf_cut (lx_tw cx).
Definition lx_un (cx : lfx) : Z := Z.of_nat (length (lx_ub cx)).
Definition lx_tn (cx : lfx) : Z := Z.of_nat (length (lx_tb cx)).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* llvmf_pre at the record (the assembly lemma proves it from llvmf_pre, with st_nev from EV_LIB) *)
Definition lf_base (cx : lfx) : Prop :=
  afn_pre tfibsegs B LLVMF_STK (lx_ly cx) (lx_S cx) (lx_W cx) (lx_regs cx) (lx_mem cx) (lx_md cx) [] /\
  raZ (lx_regs cx) = RA_LLVMF /\
  getr (lx_regs cx) 10 = w64 (lx_p cx) /\ getr (lx_regs cx) 11 = w64 (lx_n cx) /\
  ((lx_n cx = 0 /\ lx_p cx = A_EMPTY) \/ (0 < lx_n cx < 2 ^ 26 /\ In (lx_p cx, lx_n cx) (ablocks B (lx_ly cx) (lx_S cx)))) /\
  garr8 tfibsegs (rdW (lx_W cx) (lx_mem cx)) (lx_p cx) (lx_dl cx) /\ frames (lx_S cx) = [] /\
  st_nev (lx_S cx) + EV_LLVMF <= EV_MAX /\ blocks_bytes (lx_S cx) + LIVE_LIB <= LIVE_MAX /\
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H (lx_W cx)) (lx_mem cx)) /\
  fm_glob tfibsegs (lx_W cx) (lx_mem cx) (lx_live cx) (lx_peak cx) (lx_cnt cx) SIZE_MAXZ /\
  0 <= lx_cnt cx /\ lx_cnt cx + CNT_LIB < 2 ^ 33 /\ lx_live cx + 2 ^ 9 < 2 ^ 33.

Definition lf_post (cx : lfx) : world tfibsegs -> config -> Prop :=
  llvmf_post B (lx_regs cx) (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx) (lx_p cx) (lx_n cx) (lx_live cx) (lx_cnt cx).

(* the walk's journal from the entry state *)
Definition lf_J (cx : lfx) ly' S' (W' : world tfibsegs) mem' md' (k : Z) : Prop :=
  ajournal tfibsegs B LLVMF_STK (lx_sp0 cx) FM_PSTAT_FP (lx_ly cx) (lx_S cx) (lx_W cx) (lx_mem cx) (lx_md cx)
    [] ly' S' W' mem' md' k.

(* the saved registers in their slots above sp0 - 64 *)
Definition lf_frame (cx : lfx) (W : world tfibsegs) (m : word -> option byte) : Prop :=
  forall j o r, nth_error lf_saved_offs j = Some o -> nth_error lf_saved_regs j = Some r ->
    val_mem tfibsegs (rdW W m) (lx_sp0 cx - LF_FRAME + o) 8 (bv_unsigned (getr (lx_regs cx) (Z_to_bv 5 r))).

(* the input bytes as they were at entry *)
Definition lf_inkept (cx : lfx) (W' : world tfibsegs) (m' : word -> option byte) : Prop :=
  forall i, 0 <= i < lx_n cx -> aview tfibsegs (w_H W') m' (lx_p cx + i) = aview tfibsegs (w_H (lx_W cx)) (lx_mem cx) (lx_p cx + i).

(* what holds at every resume point after the prologue: the journal, the frame, sp, the callee-saved registers outside
   lf_X (gp, tp, s7..s11) as at entry, s5 = shadow base, the input bytes, the relro view *)
Definition lf_core (cx : lfx) ly' S' (W' : world tfibsegs) regs' mem' md' (k : Z) : Prop :=
  lf_J cx ly' S' W' mem' md' k /\ lf_frame cx W' mem' /\
  spZ regs' = lx_sp0 cx - LF_FRAME /\ kept_from (lx_regs cx) regs' lf_X /\
  getr regs' 21 = w64 FMW_SB /\ lf_inkept cx W' mem' /\
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W') mem').

(* fuzz/alloc.c's statics: after check_no_overread (two reader calls when un > 0), after names (peak reset to live,
   one more), after check_reject_clean_starved (one more) *)
Definition lf_glob2 (cx : lfx) (W' : world tfibsegs) mem' : Prop :=
  fm_glob tfibsegs W' mem' (lx_live cx) (rt_peak (lx_ub cx) (lx_live cx) (lx_peak cx))
    (if (length (lx_ub cx) =? 0)%nat then lx_cnt cx else lx_cnt cx + 2) SIZE_MAXZ.
Definition lf_glob5 (cx : lfx) (W' : world tfibsegs) mem' : Prop :=
  fm_glob tfibsegs W' mem' (lx_live cx) (rt_peak (lx_ub cx) (lx_live cx) (lx_live cx))
    (if (length (lx_ub cx) =? 0)%nat then lx_cnt cx else lx_cnt cx + 3) SIZE_MAXZ.
Definition lf_glob6 (cx : lfx) (W' : world tfibsegs) mem' : Prop :=
  fm_glob tfibsegs W' mem' (lx_live cx) (rt_peak (lx_ub cx) (lx_live cx) (lx_live cx))
    (if (length (lx_ub cx) =? 0)%nat then lx_cnt cx else lx_cnt cx + 4) SIZE_MAXZ.

(* ---- the concrete state at each resume point ---- *)
(* 0x8097c: s1 = size, s3 = k, a0 = data; nothing allocated, no event, the statics as at entry *)
Definition lf_P0 (cx : lfx) ly' S' (W' : world tfibsegs) regs' mem' md' (k : Z) : Prop :=
  lf_core cx ly' S' W' regs' mem' md' k /\ k = 0 /\
  Permutation (ablocks B ly' S') (ablocks B (lx_ly cx) (lx_S cx)) /\
  fm_glob tfibsegs W' mem' (lx_live cx) (lx_peak cx) (lx_cnt cx) SIZE_MAXZ /\
  getr regs' 9 = w64 (lx_n cx) /\ getr regs' 10 = w64 (lx_p cx) /\ getr regs' 19 = w64 (lx_k cx).
(* 0x809c4: s0 = un, s2 = text, s3 = tn, s4 = uri; nothing allocated, no event, the statics as at entry *)
Definition lf_P1 (cx : lfx) ly' S' (W' : world tfibsegs) regs' mem' md' (k : Z) : Prop :=
  lf_core cx ly' S' W' regs' mem' md' k /\ k = 0 /\
  Permutation (ablocks B ly' S') (ablocks B (lx_ly cx) (lx_S cx)) /\
  fm_glob tfibsegs W' mem' (lx_live cx) (lx_peak cx) (lx_cnt cx) SIZE_MAXZ /\
  getr regs' 8 = w64 (lx_un cx) /\ getr regs' 18 = w64 (lx_text cx) /\ getr regs' 19 = w64 (lx_tn cx) /\
  getr regs' 20 = w64 (lx_uri cx).
(* 0x809e0, after check_no_overread: tn <= MANIFEST_MAX *)
Definition lf_P2 (cx : lfx) ly' S' (W' : world tfibsegs) regs' mem' md' (k : Z) : Prop :=
  lf_core cx ly' S' W' regs' mem' md' k /\ 0 <= k <= EV_check_no_overread /\
  Permutation (ablocks B ly' S') (ablocks B (lx_ly cx) (lx_S cx)) /\ lf_glob2 cx W' mem' /\
  lx_tn cx <= MANIFEST_MAX /\
  getr regs' 8 = w64 (lx_un cx) /\ getr regs' 18 = w64 (lx_text cx) /\ getr regs' 19 = w64 (lx_tn cx) /\
  getr regs' 20 = w64 (lx_uri cx).
(* 0x80a24: the block u (un + 1 bytes, s1) holds ub and a NUL *)
Definition lf_P3 (cx : lfx) ly' S' (W' : world tfibsegs) regs' mem' md' (k u : Z) : Prop :=
  lf_core cx ly' S' W' regs' mem' md' k /\ 0 <= k <= EV_check_no_overread + 1 /\
  Permutation (ablocks B ly' S') ((u, lx_un cx + 1) :: ablocks B (lx_ly cx) (lx_S cx)) /\ lf_glob2 cx W' mem' /\
  lx_tn cx <= MANIFEST_MAX /\ cstr_ok tfibsegs W' mem' u (lx_ub cx) /\
  getr regs' 8 = w64 (lx_un cx) /\ getr regs' 9 = w64 u /\ getr regs' 18 = w64 (lx_text cx) /\
  getr regs' 19 = w64 (lx_tn cx).
(* 0x80a60: the block t (tn + 1 bytes, s4) holds tb and a NUL *)
Definition lf_P4 (cx : lfx) ly' S' (W' : world tfibsegs) regs' mem' md' (k u t : Z) : Prop :=
  lf_core cx ly' S' W' regs' mem' md' k /\ 0 <= k <= EV_check_no_overread + 2 /\
  Permutation (ablocks B ly' S') ((t, lx_tn cx + 1) :: (u, lx_un cx + 1) :: ablocks B (lx_ly cx) (lx_S cx)) /\
  lf_glob2 cx W' mem' /\ lx_tn cx <= MANIFEST_MAX /\
  cstr_ok tfibsegs W' mem' u (lx_ub cx) /\ cstr_ok tfibsegs W' mem' t (lx_tb cx) /\
  getr regs' 8 = w64 (lx_un cx) /\ getr regs' 9 = w64 u /\ getr regs' 20 = w64 t.
(* 0x80a8c, after live, peak_reset, names (t, u), peak, check_bounded_alloc: s2 = live, s3 = named *)
Definition lf_P5 (cx : lfx) ly' S' (W' : world tfibsegs) regs' mem' md' (k u t : Z) : Prop :=
  lf_core cx ly' S' W' regs' mem' md' k /\ 0 <= k <= EV_check_no_overread + 2 + EV_names /\
  Permutation (ablocks B ly' S') ((t, lx_tn cx + 1) :: (u, lx_un cx + 1) :: ablocks B (lx_ly cx) (lx_S cx)) /\
  lf_glob5 cx W' mem' /\ lx_tn cx <= MANIFEST_MAX /\
  cstr_ok tfibsegs W' mem' u (lx_ub cx) /\ cstr_ok tfibsegs W' mem' t (lx_tb cx) /\
  getr regs' 8 = w64 (lx_un cx) /\ getr regs' 9 = w64 u /\ getr regs' 18 = w64 (lx_live cx) /\
  getr regs' 19 = w64 (ManifestModel.names (lx_tb cx) (lx_ub cx)) /\ getr regs' 20 = w64 t.
(* 0x80ab0, after check_as_written, check_reject_clean, check_reject_clean_starved *)
Definition lf_P6 (cx : lfx) ly' S' (W' : world tfibsegs) regs' mem' md' (k u t : Z) : Prop :=
  lf_core cx ly' S' W' regs' mem' md' k /\
  0 <= k <= EV_check_no_overread + 2 + EV_names + EV_check_reject_clean_starved /\
  Permutation (ablocks B ly' S') ((t, lx_tn cx + 1) :: (u, lx_un cx + 1) :: ablocks B (lx_ly cx) (lx_S cx)) /\
  lf_glob6 cx W' mem' /\ cstr_ok tfibsegs W' mem' u (lx_ub cx) /\
  getr regs' 8 = w64 (lx_un cx) /\ getr regs' 9 = w64 u /\ getr regs' 20 = w64 t.
(* 0x80ac8: everything freed, the statics back at live with at most CNT_LIB more reader allocations *)
Definition lf_R (cx : lfx) ly' S' (W' : world tfibsegs) regs' mem' md' (k : Z) : Prop :=
  lf_core cx ly' S' W' regs' mem' md' k /\ 0 <= k <= EV_LLVMF /\
  Permutation (ablocks B ly' S') (ablocks B (lx_ly cx) (lx_S cx)) /\
  exists peak' cnt', fm_glob tfibsegs W' mem' (lx_live cx) peak' cnt' SIZE_MAXZ /\
    lx_cnt cx <= cnt' <= lx_cnt cx + CNT_LIB.

(* ---- frame lemmas ---- *)
Lemma lf_saved_offs_range : forall j o, nth_error lf_saved_offs j = Some o -> 0 <= o <= 56.
Proof.
intros j o Ho. pose proof (nth_error_In _ _ Ho) as Hi.
assert (F : Forall (fun o => 0 <= o <= 56) lf_saved_offs) by (repeat constructor; lia).
exact (proj1 (Forall_forall _ _) F o Hi).
Qed.
Lemma lf_saved_regs_range : forall j r, nth_error lf_saved_regs j = Some r -> 0 <= r < 32.
Proof.
intros j r Hr. pose proof (nth_error_In _ _ Hr) as Hi.
assert (F : Forall (fun r => 0 <= r < 32) lf_saved_regs) by (repeat constructor; lia).
exact (proj1 (Forall_forall _ _) F r Hi).
Qed.
(* the frame is kept by any step that leaves [sp0 - 64, sp0) as it was *)
Lemma lf_frame_kept : forall cx (W W' : world tfibsegs) m m',
  (forall a, lx_sp0 cx - LF_FRAME <= a < lx_sp0 cx -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  lf_frame cx W m -> lf_frame cx W' m'.
Proof.
intros cx W W' m m' HK HF j o r Ho Hr. eapply (val_mem_kept tfibsegs); [|exact (HF j o r Ho Hr)].
intros k Hk. pose proof (lf_saved_offs_range j o Ho). unfold LF_FRAME. apply HK. unfold LF_FRAME. cbn in Hk. lia.
Qed.
Lemma lf_frame_below : forall cx (W : world tfibsegs) m m',
  same_below m m' (2 ^ 64) -> 0 <= lx_sp0 cx - LF_FRAME -> lx_sp0 cx <= 2 ^ 47 ->
  lf_frame cx W m -> lf_frame cx W m'.
Proof.
intros cx W m m' HS H0 H1. apply lf_frame_kept. intros a Ha.
apply (aview_below (w_H W) m m' (2 ^ 64) a HS). lia.
Qed.
(* the frame from the prologue's stack chunks (offsets relative to sp0; atom r = the entry register r) *)
Lemma lf_frame_of_chunks : forall cx (W : world tfibsegs) m lo hi wlo whi cs extra,
  region_ok tfibsegs (Ereg (lx_regs cx) extra) (rdW W m) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  (forall j o r, nth_error lf_saved_offs j = Some o -> nth_error lf_saved_regs j = Some r ->
     In (YP09.mkChunk (o - LF_FRAME) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
  lf_frame cx W m.
Proof.
intros cx W m lo hi wlo whi cs extra HR Hcs j o r Ho Hr.
pose proof (lf_saved_regs_range j r Hr) as Rr.
assert (E2 : bv_unsigned (ew (Ereg (lx_regs cx) extra) 2) = lx_sp0 cx)
  by (rewrite (ew_Ereg_nat (lx_regs cx) extra 2 2%bv eq_refl); reflexivity).
pose proof (fmw_field _ _ 2 (lx_sp0 cx) cs lo hi wlo whi (o - LF_FRAME) 8%N (SOff (Z.to_nat r) 0)
  (bv_unsigned (getr (lx_regs cx) (Z_to_bv 5 r))) HR E2 (Hcs j o r Ho Hr)) as V.
replace (lx_sp0 cx + (o - LF_FRAME)) with (lx_sp0 cx - LF_FRAME + o) in V by lia.
apply V.
- rewrite fmw_SOff0. rewrite (ew_Ereg_nat (lx_regs cx) extra (Z.to_nat r) (Z_to_bv 5 r)).
  + symmetry. apply Z_to_bv_bv_unsigned.
  + rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. unfold bv_modulus. cbn [Z.of_N]. lia.
- apply u64_range.
- cbn; lia.
Qed.
(* a string in a block the caller allocated: its home for a program callee *)
Lemma lf_kept_blk : forall ly S u m rest l,
  Permutation (ablocks B ly S) ((u, m) :: rest) -> Z.of_nat (length l) + 1 <= m -> cstr_kept B ly S u l.
Proof.
intros ly S u m rest l HP Hm. left. exists u, m. split; [|lia].
apply (Permutation_in _ (Permutation_sym HP)). left. reflexivity.
Qed.
End c.
