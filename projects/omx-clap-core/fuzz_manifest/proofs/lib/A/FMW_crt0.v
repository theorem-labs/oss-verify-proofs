(* check_round_trip 0x80ea0 (fuzz_manifest.c:253-291): the walk's context (check_round_trip_spec's premises), its post,
   and the concrete state at each point the walk resumes from (after the prologue: sp = sp0 - 112, the 13 saved
   registers in their slots, s0 = uri, s10 = the shadow base). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0l ACej FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_kit FMW_K FMW_seg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* resume points (return addresses of check_round_trip's calls) *)
Definition CRT_P1 : Z := 0x80eec.   (* after strlen (uri) *)
Definition CRT_P2 : Z := 0x80f00.   (* after names ("", uri) *)
Definition CRT_P3 : Z := 0x80f24.   (* after malloc (3 n + 64), beqz a0 (dead: t >= 4096), mv s2, a0 *)
Definition CRT_P4 : Z := 0x80f3c.   (* after snprintf tw *)
Definition CRT_P5 : Z := 0x80f48.   (* after names (text, uri) *)
Definition CRT_P6 : Z := 0x80f68.   (* after snprintf tx *)
Definition CRT_P7 : Z := 0x80f74.   (* after as_ruled (text, uri) *)
Definition CRT_L : Z := 0x80fb0.    (* loop head: the shadow check of uri[k - 1] *)
Definition CRT_L1 : Z := 0x80fd4.   (* after plain (uri + k) *)
Definition CRT_L2 : Z := 0x80ff4.   (* after snprintf t1 *)
Definition CRT_L3 : Z := 0x81000.   (* after names *)
Definition CRT_L4 : Z := 0x81020.   (* after snprintf t2 *)
Definition CRT_L5 : Z := 0x8102c.   (* after names *)
Definition CRT_L6 : Z := 0x8104c.   (* after snprintf t3 *)
Definition CRT_L7 : Z := 0x81058.   (* after names *)
Definition CRT_L8 : Z := 0x81078.   (* after snprintf t1x *)
Definition CRT_L9 : Z := 0x81084.   (* after as_ruled; the loop step *)
Definition CRT_X : Z := 0x810ac.    (* exit: a0 = text; epilogue; tail call free *)
Definition CRT_X0 : Z := 0x810ec.   (* exit for n = 0: epilogue; ret *)
Definition CRT_FRAME : Z := 112.
(* the saved registers (ra, s0, s1, s2..s11) and their slots above sp after the prologue *)
Definition crt_saved_regs : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition crt_saved_offs : list Z := [104; 96; 88; 80; 72; 64; 56; 48; 40; 32; 24; 16; 8].
(* the text buffer's size, fuzz_manifest.c:266 *)
Definition crt_tsz (n : Z) : Z := 3 * n + 64.

Record crtx := mkCX {
  cx_ly : alayout; cx_S : astate; cx_W : world tfibsegs; cx_regs : bvmap 5 word; cx_mem : word -> option byte;
  cx_md : Model; cx_ch : list (Z * Z * Z); cx_u : Z; cx_ub : list Z; cx_live : Z; cx_peak : Z; cx_cnt : Z }.
Definition cx_sp0 (cx : crtx) : Z := spZ (cx_regs cx).
Definition cx_n (cx : crtx) : Z := Z.of_nat (length (cx_ub cx)).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* check_round_trip_spec's premises at CTX_check_round_trip, fail = SIZE_MAX (from quiet) *)
Definition crt_base (cx : crtx) : Prop :=
  fpre tfibsegs B STK_check_round_trip (cx_ly cx) (cx_S cx) (cx_W cx) (cx_regs cx) (cx_mem cx) (cx_md cx) (cx_ch cx) /\
  In (raZ (cx_regs cx) :: spine (cx_ch cx)) CTX_check_round_trip /\
  getr (cx_regs cx) 10 = w64 (cx_u cx) /\ cstr_ok tfibsegs (cx_W cx) (cx_mem cx) (cx_u cx) (cx_ub cx) /\
  cstr_kept B (cx_ly cx) (cx_S cx) (cx_u cx) (cx_ub cx) /\ (length (cx_ub cx) <= 255)%nat /\
  fm_glob tfibsegs (cx_W cx) (cx_mem cx) (cx_live cx) (cx_peak cx) (cx_cnt cx) SIZE_MAXZ /\
  quiet (cx_cnt cx) SIZE_MAXZ (3 + 4 * 254) /\ cx_live cx + cx_n cx + 3 < 2 ^ 33 /\
  st_nev (cx_S cx) + EV_check_round_trip <= EV_MAX /\ blocks_bytes (cx_S cx) + LIVE_check_round_trip <= LIVE_MAX.

Definition crt_post (cx : crtx) : world tfibsegs -> config -> Prop :=
  fpost tfibsegs B STK_check_round_trip FM_PSTAT_FP (cx_regs cx) (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    EV_check_round_trip (fun ly' S' W' regs' mem' md' =>
      Permutation (ablocks B ly' S') (ablocks B (cx_ly cx) (cx_S cx)) /\
      fm_glob tfibsegs W' mem' (cx_live cx) (rt_peak (cx_ub cx) (cx_live cx) (cx_peak cx))
        (cx_cnt cx + rt_calls (cx_ub cx)) SIZE_MAXZ).

(* the walk's journal from the entry state *)
Definition crt_J (cx : crtx) ly' S' (W' : world tfibsegs) mem' md' (k : Z) : Prop :=
  ajournal tfibsegs B STK_check_round_trip (cx_sp0 cx) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly' S' W' mem' md' k.

(* the saved registers in their slots above sp0 - 112 *)
Definition crt_frame (cx : crtx) (W : world tfibsegs) (m : word -> option byte) : Prop :=
  forall j o r, nth_error crt_saved_offs j = Some o -> nth_error crt_saved_regs j = Some r ->
    val_mem tfibsegs (rdW W m) (cx_sp0 cx - CRT_FRAME + o) 8 (bv_unsigned (getr (cx_regs cx) (Z_to_bv 5 r))).

(* what holds at every resume point after the prologue: the journal, the frame, sp/gp/tp, s0 = uri, s10 = shadow base,
   the uri string and its home, the relro view, the blocks (the entry's, plus the text buffer once allocated), the
   statics, and the event and live-byte budgets left *)
Definition crt_core (cx : crtx) ly' S' (W' : world tfibsegs) regs' mem' md' (k : Z) : Prop :=
  crt_J cx ly' S' W' mem' md' k /\ crt_frame cx W' mem' /\
  spZ regs' = cx_sp0 cx - CRT_FRAME /\ getr regs' 3 = getr (cx_regs cx) 3 /\ getr regs' 4 = getr (cx_regs cx) 4 /\
  getr regs' 8 = w64 (cx_u cx) /\ getr regs' 26 = w64 FMW_SB /\
  cstr_ok tfibsegs W' mem' (cx_u cx) (cx_ub cx) /\ cstr_kept B ly' S' (cx_u cx) (cx_ub cx) /\
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W') mem').

(* the statics after `c` reader calls (the first of them raises the peak to rt_peak) *)
Definition crt_glob (cx : crtx) (W' : world tfibsegs) mem' (c : Z) : Prop :=
  fm_glob tfibsegs W' mem' (cx_live cx)
    (if c =? 0 then cx_peak cx else rt_peak (cx_ub cx) (cx_live cx) (cx_peak cx)) (cx_cnt cx + c) SIZE_MAXZ.

(* ---- the concrete state at each resume point ---- *)
(* back at 0x80f00 after names ("", uri): a0 = 0, s3 = n *)
Definition crt_P2 (cx : crtx) ly' S' (W' : world tfibsegs) regs' mem' md' (k : Z) : Prop :=
  crt_core cx ly' S' W' regs' mem' md' k /\ 0 <= k <= EV_names /\
  getr regs' 10 = w64 0 /\ getr regs' 19 = w64 (cx_n cx) /\
  Permutation (ablocks B ly' S') (ablocks B (cx_ly cx) (cx_S cx)) /\
  crt_glob cx W' mem' (if cx_n cx =? 0 then 0 else 1).
(* 0x810ec, n = 0: the epilogue and ret *)
Definition crt_X0 (cx : crtx) ly' S' (W' : world tfibsegs) regs' mem' md' (k : Z) : Prop :=
  crt_core cx ly' S' W' regs' mem' md' k /\ 0 <= k <= EV_names /\ cx_n cx = 0 /\
  Permutation (ablocks B ly' S') (ablocks B (cx_ly cx) (cx_S cx)) /\ crt_glob cx W' mem' 0.
(* after the text buffer t (3 n + 64 bytes, s2) is allocated (s1 = its size), n >= 1, m reader calls made (each counted
   in g_count; the journal's event count is at most 1 + 2 m) *)
Definition crt_tcore (cx : crtx) ly' S' (W' : world tfibsegs) regs' mem' md' (k t m : Z) : Prop :=
  crt_core cx ly' S' W' regs' mem' md' k /\ 0 <= k <= 1 + 2 * m /\ 1 <= cx_n cx /\
  getr regs' 9 = w64 (crt_tsz (cx_n cx)) /\ getr regs' 18 = w64 t /\ 4096 <= t /\
  Permutation (ablocks B ly' S') ((t, crt_tsz (cx_n cx)) :: ablocks B (cx_ly cx) (cx_S cx)) /\
  crt_glob cx W' mem' m.
Definition crt_P3 (cx : crtx) ly' S' W' regs' mem' md' (k t : Z) : Prop :=
  crt_tcore cx ly' S' W' regs' mem' md' k t 1 /\ getr regs' 10 = w64 t /\ getr regs' 19 = w64 (cx_n cx).
Definition crt_P5 (cx : crtx) ly' S' W' regs' mem' md' (k t : Z) : Prop :=
  crt_tcore cx ly' S' W' regs' mem' md' k t 2 /\ getr regs' 10 = w64 1 /\ getr regs' 19 = w64 (cx_n cx).
Definition crt_P7 (cx : crtx) ly' S' W' regs' mem' md' (k t : Z) : Prop :=
  crt_tcore cx ly' S' W' regs' mem' md' k t 3 /\ getr regs' 19 = w64 (cx_n cx).
(* the loop registers at split point k (fuzz_manifest.c:274-288): s3 = uri + k, s4 = uri + k - 1, s5 = 1, s6..s8 = the
   t2, t3, t1x formats, s9 = k, s11 = n - k, and the t1 format at sp *)
Definition crt_lregs (cx : crtx) (W' : world tfibsegs) regs' mem' (k : nat) : Prop :=
  getr regs' 19 = w64 (cx_u cx + Z.of_nat k) /\ getr regs' 20 = w64 (cx_u cx + Z.of_nat k - 1) /\
  getr regs' 21 = w64 1 /\ getr regs' 22 = w64 FMT_t2 /\ getr regs' 23 = w64 FMT_t3 /\ getr regs' 24 = w64 FMT_t1x /\
  getr regs' 25 = w64 (Z.of_nat k) /\ getr regs' 27 = w64 (cx_n cx - Z.of_nat k) /\
  val_mem tfibsegs (rdW W' mem') (cx_sp0 cx - CRT_FRAME) 8 FMT_t1.
(* reader calls the split points from k on will make *)
Definition crt_rest (cx : crtx) (k : nat) : Z :=
  4 * Z.of_nat (rt_used (cx_ub cx) k (length (cx_ub cx) - k + 1)).
(* the loop head 0x80fb0 at split point k (1 <= k < n), m = rt_calls - what the split points from k on add *)
Definition crt_L (cx : crtx) ly' S' W' regs' mem' md' (k0 t m : Z) (k : nat) : Prop :=
  crt_tcore cx ly' S' W' regs' mem' md' k0 t m /\ crt_lregs cx W' regs' mem' k /\
  1 <= Z.of_nat k < cx_n cx /\ m + crt_rest cx k = rt_calls (cx_ub cx) /\
  forallb (fun c => negb (c =? 62)) (firstn (k - 1) (cx_ub cx)) = true.
(* after plain (uri + k) at 0x80fd4: uri[k - 1] is not '>' *)
Definition crt_L1 (cx : crtx) ly' S' W' regs' mem' md' (k0 t m : Z) (k : nat) : Prop :=
  crt_L cx ly' S' W' regs' mem' md' k0 t m k /\ ManifestModel.byte_at (cx_ub cx) (k - 1) <> 62 /\
  getr regs' 10 = w64 (if ManifestModel.plain_name (skipn k (cx_ub cx)) then 1 else 0).
(* inside the four reader calls of split point k (plain (uri + k) holds): j of them made, a0 = 1 after each names *)
Definition crt_Lj (cx : crtx) ly' S' W' regs' mem' md' (k0 t m : Z) (k : nat) (j : Z) : Prop :=
  crt_tcore cx ly' S' W' regs' mem' md' k0 t (m + j) /\ crt_lregs cx W' regs' mem' k /\
  1 <= Z.of_nat k < cx_n cx /\ m + crt_rest cx k = rt_calls (cx_ub cx) /\
  ManifestModel.byte_at (cx_ub cx) (k - 1) <> 62 /\ ManifestModel.plain_name (skipn k (cx_ub cx)) = true /\
  getr regs' 10 = w64 1 /\ forallb (fun c => negb (c =? 62)) (firstn k (cx_ub cx)) = true.
(* the loop step 0x81084 after split point k: m reader calls made, the split points from k + 1 on add the rest *)
Definition crt_I (cx : crtx) ly' S' W' regs' mem' md' (k0 t m : Z) (k : nat) : Prop :=
  crt_tcore cx ly' S' W' regs' mem' md' k0 t m /\ crt_lregs cx W' regs' mem' k /\
  1 <= Z.of_nat k < cx_n cx /\ m + crt_rest cx (S k) = rt_calls (cx_ub cx) /\
  forallb (fun c => negb (c =? 62)) (firstn k (cx_ub cx)) = true.
(* 0x810ac: every reader call made; a0 := t, the epilogue, tail call free (t) *)
Definition crt_X (cx : crtx) ly' S' W' regs' mem' md' (k0 t : Z) : Prop :=
  crt_tcore cx ly' S' W' regs' mem' md' k0 t (rt_calls (cx_ub cx)).

Lemma crt_saved_offs_range : forall j o, nth_error crt_saved_offs j = Some o -> 8 <= o <= 104.
Proof.
intros j o Ho. pose proof (nth_error_In _ _ Ho) as Hi.
assert (F : Forall (fun o => 8 <= o <= 104) crt_saved_offs) by (repeat constructor; lia).
exact (proj1 (Forall_forall _ _) F o Hi).
Qed.
Lemma crt_saved_regs_range : forall j r, nth_error crt_saved_regs j = Some r -> 0 <= r < 32.
Proof.
intros j r Hr. pose proof (nth_error_In _ _ Hr) as Hi.
assert (F : Forall (fun r => 0 <= r < 32) crt_saved_regs) by (repeat constructor; lia).
exact (proj1 (Forall_forall _ _) F r Hi).
Qed.
(* the frame is kept by any step that leaves [sp0 - 112, sp0) as it was *)
Lemma crt_frame_kept : forall cx (W W' : world tfibsegs) m m',
  (forall a, cx_sp0 cx - CRT_FRAME <= a < cx_sp0 cx -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  crt_frame cx W m -> crt_frame cx W' m'.
Proof.
intros cx W W' m m' HK HF j o r Ho Hr. eapply (val_mem_kept tfibsegs); [|exact (HF j o r Ho Hr)].
intros k Hk. pose proof (crt_saved_offs_range j o Ho). unfold CRT_FRAME. apply HK. unfold CRT_FRAME. cbn in Hk. lia.
Qed.
Lemma crt_frame_below : forall cx (W : world tfibsegs) m m',
  same_below m m' (2 ^ 64) -> 0 <= cx_sp0 cx - CRT_FRAME -> cx_sp0 cx <= 2 ^ 47 ->
  crt_frame cx W m -> crt_frame cx W m'.
Proof.
intros cx W m m' HS H0 H1. apply crt_frame_kept. intros a Ha.
apply (aview_below (w_H W) m m' (2 ^ 64) a HS). lia.
Qed.
(* the frame from the prologue's stack chunks (offsets relative to sp0; atom r = the entry register r) *)
Lemma crt_frame_of_chunks : forall cx (W : world tfibsegs) m lo hi wlo whi cs extra,
  region_ok tfibsegs (Ereg (cx_regs cx) extra) (rdW W m) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  (forall j o r, nth_error crt_saved_offs j = Some o -> nth_error crt_saved_regs j = Some r ->
     In (YP09.mkChunk (o - CRT_FRAME) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
  crt_frame cx W m.
Proof.
intros cx W m lo hi wlo whi cs extra HR Hcs j o r Ho Hr.
pose proof (crt_saved_regs_range j r Hr) as Rr.
assert (E2 : bv_unsigned (ew (Ereg (cx_regs cx) extra) 2) = cx_sp0 cx)
  by (rewrite (ew_Ereg_nat (cx_regs cx) extra 2 2%bv eq_refl); reflexivity).
pose proof (fmw_field _ _ 2 (cx_sp0 cx) cs lo hi wlo whi (o - CRT_FRAME) 8%N (SOff (Z.to_nat r) 0)
  (bv_unsigned (getr (cx_regs cx) (Z_to_bv 5 r))) HR E2 (Hcs j o r Ho Hr)) as V.
replace (cx_sp0 cx + (o - CRT_FRAME)) with (cx_sp0 cx - CRT_FRAME + o) in V by lia.
apply V.
- rewrite fmw_SOff0. rewrite (ew_Ereg_nat (cx_regs cx) extra (Z.to_nat r) (Z_to_bv 5 r)).
  + symmetry. apply Z_to_bv_bv_unsigned.
  + rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|]. unfold bv_modulus. cbn [Z.of_N]. lia.
- apply u64_range.
- cbn; lia.
Qed.
End c.
