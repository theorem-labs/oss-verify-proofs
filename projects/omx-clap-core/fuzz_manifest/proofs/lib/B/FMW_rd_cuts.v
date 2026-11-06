(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_rd_cuts.v on a working branch e2e59892bef: re-designed for B's code (cut invariants with B's registers, frame slots and pcs). *)
(* lv2_locate_manifest_readings on fm.asan-ubsan: the semantic invariants at the walk's interface cuts and the segment
   statements (A's lib/A/FMW_rd_cuts.v with B's registers, frame slots and pcs).
   Interface cuts (every segment file builds its own symbolic states from these Props):
     entry (rd_base)      0x81e94
     L  (rd_L)            0x81fa8  the declaration scan's head: s5 = at = text + i, s1 = read_again = d, fuel f
     P  (rd_P)            0x82060  a0 = s11 (6 "PREFIX" or 7 "@prefix"), head text i = Some (i + s11), s6 := at + s11
     C8 (rd_C8)           0x821c0  after strchr (ns, '>'), s8 = ns = text + S p3
     PL (rd_PL)           0x8227c  plain_local's loop head at local[q] (s8 = q, a3 = n)
     R  (rd_com + facts)  0x82374  the shared return (FMW_rd_ret.v), a0 = s9
   Segments: PRE entry -> {R, L 0 0 (S TL)}; LP L -> {R, L, P}; PP P -> {L, C8}; C8 C8 -> {R, L, PL 0};
   PL PL -> {R, L, PL (q + 1)}. The scan's value follows fm's pure model (ManifestModel.scan / readings, fuel f as in
   fm's plain proof lib/Prog/readings_scan.v:601 LoopAt, step lemmas sc_* :230-274).
   Every UBSan guard (a branch to RD_TRAP 0x823b4) is refuted inside the segment that reaches it: the pointers it tests
   are text / uri positions below alloc_ceiling, never 0 or -1, and their sums do not wrap. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the scan's frame locals (stored at 0x81f44..0x81fa0); read_again lives in s1 on B *)
Definition rd_loc_list (cx : rdcx) : list (Z * Z) :=
  [(0x10, cx_sp cx); (0x18, RD_MASK2); (0x20, cx_u cx); (0x28, cx_ulen cx); (0x50, cx_t cx);
   (0x58, cx_u cx - 2); (0x60, RD_PREFIX)].
Definition rd_slots_ok (cx : rdcx) (W3 : world tfibsegs) (mem3 : word -> option byte) (sl : list (Z * Z)) : Prop :=
  Forall (fun s => val_mem tfibsegs (rdW W3 mem3) (cx_F cx + fst s) 8 (snd s) /\ 0 <= snd s < 2 ^ 64) sl.

(* what holds throughout the declaration scan (after fuzz_free, the uri found nowhere as "<uri>"): the common facts at
   k = EV_names, U = []; s0 = -1, s1 = d, s2 = 32, s3 = 5, s4 = mask1, s7 = 58 (lv2_locate.c's constants); the frame
   locals; *rp = v + d; the blocks back to the entry's; the statics after one allocation; d <= 16 *)
Definition rd_loop (cx : rdcx) (d : nat) ly3 S3 (W3 : world tfibsegs) (regs3 : bvmap 5 word)
  (mem3 : word -> option byte) (md3 : Model) : Prop :=
  rd_com B cx EV_names [] ly3 S3 W3 regs3 mem3 md3 /\
  getr regs3 8 = w64 RD_M1 /\ getr regs3 9 = w64 (Z.of_nat d) /\ getr regs3 18 = w64 32 /\ getr regs3 19 = w64 5 /\
  getr regs3 20 = w64 RD_MASK1 /\ getr regs3 23 = w64 58 /\
  rd_slots_ok cx W3 mem3 (rd_loc_list cx) /\
  val_mem tfibsegs (rdW W3 mem3) (cx_sp cx) 8 (cx_v cx + Z.of_nat d) /\
  Permutation (ablocks B ly3 S3) (ablocks B (cx_ly cx) (cx_S cx)) /\
  fm_glob tfibsegs W3 mem3 (cx_live cx) (Z.max (cx_peak cx) (cx_live cx + cx_ulen cx + 3)) (cx_cnt cx + 1) (cx_fail cx) /\
  cx_cnt cx <> cx_fail cx /\ cx_ub cx <> [] /\ whole (cx_tb cx) (cx_ub cx) = false /\ (d <= 16)%nat.

(* the scan's accounting: position i, d readings so far, fuel f (readings_scan.v:601-608) *)
Definition rd_acc (cx : rdcx) (i d f : nat) : Prop :=
  (i <= length (cx_tb cx))%nat /\ (length (cx_tb cx) - i < f)%nat /\
  names (cx_tb cx) (cx_ub cx) = scan (cx_tb cx) (cx_ub cx) i d f /\
  nreadings (cx_tb cx) (cx_ub cx) = (d + readings (cx_tb cx) (cx_ub cx) i d f)%nat.

(* L, 0x81fa8: s5 = at = text + i *)
Definition rd_L (cx : rdcx) (i d f : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  rd_loop cx d ly3 S3 W3 regs3 mem3 md3 /\ rd_acc cx i d f /\
  getr regs3 21 = w64 (cx_t cx + Z.of_nat i).

(* P, 0x82060: a "PREFIX"/"@prefix" head at i; a0 = s11 = 6 or 7, s5 = at *)
Definition rd_P (cx : rdcx) (i d f s11 : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  rd_loop cx d ly3 S3 W3 regs3 mem3 md3 /\ rd_acc cx i d f /\
  (i < length (cx_tb cx))%nat /\ head (cx_tb cx) i = Some (i + s11)%nat /\ (s11 = 6 \/ s11 = 7)%nat /\
  getr regs3 10 = w64 (Z.of_nat s11) /\ getr regs3 21 = w64 (cx_t cx + Z.of_nat i).

(* the declaration body's positions (readings_scan.v:177-187 dbody): p0 = i + s11 a space, p1 after the spaces, the
   name up to p2 = ':', p3 = '<' after the spaces *)
Definition rd_decl (cx : rdcx) (i s11 p1 p2 p3 : nat) : Prop :=
  let tb := cx_tb cx in
  head tb i = Some (i + s11)%nat /\ (s11 = 6 \/ s11 = 7)%nat /\
  is_space (byte_at tb (i + s11)) = true /\
  p1 = (i + s11 + count_while is_space (skipn (i + s11) tb))%nat /\
  p2 = (p1 + count_while name_ok (skipn p1 tb))%nat /\ byte_at tb p2 = 58 /\
  p3 = (S p2 + count_while is_space (skipn (S p2) tb))%nat /\ byte_at tb p3 = 60 /\ (S p3 <= length tb)%nat.

(* s10 = the bytes consumed after p0 = text + i + s11 (B's s9 and s10 count down from u - 2 - s11 - at and u - 2 - p0) *)
Definition rd_s10 (i s11 p3 : nat) : Z := Z.of_nat p3 - Z.of_nat i - Z.of_nat s11 - 1.
Definition rd_p0 (cx : rdcx) (i s11 : nat) : Z := cx_t cx + Z.of_nat i + Z.of_nat s11.

(* C8, 0x821c0: strchr (ns, '>') answered r; s5 = at, s6 = text + p1, s8 = ns, F+0x48 = the name's length *)
Definition rd_C8 (cx : rdcx) (i d f s11 p1 p2 p3 : nat) (r : Z) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  let p0 := rd_p0 cx i s11 in let s10 := rd_s10 i s11 p3 in
  rd_loop cx d ly3 S3 W3 regs3 mem3 md3 /\ rd_acc cx i d f /\ (i < length (cx_tb cx))%nat /\
  rd_decl cx i s11 p1 p2 p3 /\
  rd_slots_ok cx W3 mem3 [(0x48, Z.of_nat p2 - Z.of_nat p1)] /\
  getr regs3 21 = w64 (cx_t cx + Z.of_nat i) /\ getr regs3 22 = w64 (cx_t cx + Z.of_nat p1) /\
  getr regs3 24 = w64 (cx_t cx + Z.of_nat (S p3)) /\
  getr regs3 25 = w64 (cx_u cx - 2 - Z.of_nat s11 - (cx_t cx + Z.of_nat i) - s10) /\
  getr regs3 26 = w64 (cx_u cx - 2 - p0 - s10) /\
  getr regs3 10 = w64 r /\
  ((r = 0 /\ ~ In 62 (skipn (S p3) (cx_tb cx))) \/
   (exists j, FMH_Rt.first_at (skipn (S p3) (cx_tb cx)) 62 j /\ r = cx_t cx + Z.of_nat (S p3) + Z.of_nat j)).

(* PL, 0x8227c: the declaration matched (ns_len = o < uri_len, the namespace equals the uri's first o bytes),
   local = uri + o has n = uri_len - o bytes, its last byte is not '.', local[0 .. q) are plain; s5 = close = ns + o,
   s6 = text + p1, s8 = q, a3 = n; F+0x08, F+0x30, F+0x38 = local, F+0x40 = ~local, F+0x48 = the name's length *)
Definition rd_PL (cx : rdcx) (i d f s11 p1 p2 p3 o q : nat) ly3 S3 W3 regs3 mem3 md3 : Prop :=
  let tb := cx_tb cx in let ub := cx_ub cx in let n := (length ub - o)%nat in
  rd_loop cx d ly3 S3 W3 regs3 mem3 md3 /\ rd_acc cx i d f /\ (i < length tb)%nat /\
  rd_decl cx i s11 p1 p2 p3 /\
  find_idx (fun c => c =? 62) (skipn (S p3) tb) = Some o /\ (o < length ub)%nat /\
  firstn o (skipn (S p3) tb) = firstn o ub /\
  last (skipn o ub) 0 <> 46 /\ (q < n)%nat /\ forallb plain_ok (firstn q (skipn o ub)) = true /\
  rd_slots_ok cx W3 mem3 [(0x08, cx_u cx + Z.of_nat o); (0x30, cx_u cx + Z.of_nat o); (0x38, cx_u cx + Z.of_nat o);
                          (0x40, RD_M1 - (cx_u cx + Z.of_nat o)); (0x48, Z.of_nat p2 - Z.of_nat p1)] /\
  getr regs3 13 = w64 (Z.of_nat n) /\ getr regs3 21 = w64 (cx_t cx + Z.of_nat (S p3) + Z.of_nat o) /\
  getr regs3 22 = w64 (cx_t cx + Z.of_nat p1) /\ getr regs3 24 = w64 (Z.of_nat q).

(* ---- the segment statements: every cut reaches readings_spec's post ---- *)
Definition rd_seg_L (CTX : list (list Z)) (f : nat) : Prop :=
  forall cx i d ly3 S3 W3 regs3 mem3 md3,
  rd_base B CTX cx -> rd_L cx i d f ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs RD_L regs3 mem3 md3) (rd_post B cx).
Definition rd_seg_P (CTX : list (list Z)) (f : nat) : Prop :=
  forall cx i d s11 ly3 S3 W3 regs3 mem3 md3,
  rd_base B CTX cx -> rd_P cx i d f s11 ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs RD_P regs3 mem3 md3) (rd_post B cx).
Definition rd_seg_C8 (CTX : list (list Z)) (f : nat) : Prop :=
  forall cx i d s11 p1 p2 p3 r ly3 S3 W3 regs3 mem3 md3,
  rd_base B CTX cx -> rd_C8 cx i d f s11 p1 p2 p3 r ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs RD_C8 regs3 mem3 md3) (rd_post B cx).
Definition rd_seg_PL (CTX : list (list Z)) (f : nat) (m : nat) : Prop :=
  forall cx i d s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3,
  (length (cx_ub cx) - o - q <= m)%nat ->
  rd_base B CTX cx -> rd_PL cx i d f s11 p1 p2 p3 o q ly3 S3 W3 regs3 mem3 md3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs RD_PL regs3 mem3 md3) (rd_post B cx).
(* the entry segment: readings' own entry state (readings_spec's premises) *)
Definition rd_seg_E (CTX : list (list Z)) : Prop :=
  forall cx, rd_base B CTX cx ->
  SRr tfibsegs (cx_W cx) (cfg_at tfibsegs A_readings (cx_regs cx) (cx_mem cx) (cx_md cx)) (rd_post B cx).
End c.
