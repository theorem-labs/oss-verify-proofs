(* Modified by Theorem Labs: reac-repacer/fuzz_uci's check_value in the caller-journal form of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a; cgif_file_fuzzer lib/A/ACey.v trfc_specX, lib/YC20.v tlzw_spec), at this unit's core names and image A. *)
(* check_value_cg: the ASan walk contract of check_value (fuzz_uci.asan 0x7f62c = uci_sigma US_check_value,
   AF_check_value = 0x344 of lib/A/Prog/UciPList.v), as STATEMENTS only (no proof).

   The C (fuzz_uci.c check_value): fuzz_dup the n reply bytes (malloc(n ? n : 1), abort on NULL, memcpy), rp_uci_int on
   the copy, expected_value of the reply itself, abort unless equal, free the copy, return the value.
   The code (DIS of image A): `addi sp, sp, -0x40` (frame 0x40); +0x20 `mv s0, a2` (s0 = cur); malloc trampoline 0x51788
   at +0x40 with a0 = n + (n == 0) (+0x38 `seqz`, +0x3c `add`); `beqz a0` at +0x44 to __asan_handle_no_return / abort
   (+0x254 / +0x258); __asan_memcpy 0x50674 at +0x58 (skipped when n = 0, `beqz s4` at +0x4c, which goes to the call of
   rp_uci_int at +0xb4 with n = 0); rp_uci_int at +0x68 otherwise; expected_value inlined, reading the reply bytes r[i] with
   __asan_report_load1 checks (+0xa8, +0x10c, +0x188, +0x1f8); `bne s2, s0` at +0x220 to the abort; free trampoline
   0x51784 at +0x228; returns the value (`mv a0, s2` at +0x22c).
   The aborts are refuted by the malloc rule (no NULL) and by lib/Spec/UciModel.v uci_value_ok (rp_uci_int_m =
   expected_value_m). Both traces are fixed (s0 = cur at both calls, so the chain is empty): its contract takes no call
   context. *)
From Stdlib Require Import ZArith List Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import UciPSyms UciPAddr UciCg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require rp_uci_int_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require rp_uci_int_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YK11.
Module PR := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog.rp_uci_int_cg.
Module PRc := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.rp_uci_int_c.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* check_value's own frame (`addi sp, sp, -0x40` at US_check_value); its allocator calls use ASTACK below their sp. *)
Definition CV_FRAME : Z := 0x40.
Definition CV_STK : Z := CV_FRAME + ASTACK.
(* malloc, free: one model event each (YC5d.v). *)
Definition CV_EV : Z := 2.
(* Live bytes it adds: one block of max(n, 1) <= REPLY_MAX bytes. *)
Definition CV_LIVE : Z := PR.REPLY_MAX.

(* The return addresses of its allocator calls, as offsets from its entry: malloc at +0x40, free at +0x228 (0x7f670,
   0x7f858). *)
Definition UCI_CV_RA_MALLOC : Z := uci_sigma US_check_value + 0x44.
Definition UCI_CV_RA_FREE : Z := uci_sigma US_check_value + 0x22c.

Section cv. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal := (@ajournal rc tfib_sink_head segs B).

(* The meter cost of one call: its allocation of max(n, 1) bytes and one free. *)
Definition uci_cv_cost (n : Z) : Z := mo_malloc MT (Z.max n 1) + mo_free MT.

(* What a call leaves: as check_no_overread_cg.v uci_cno_post, with CV_EV events, uci_cv_cost, and the result in a0:
   rp_uci_int_m of the n reply bytes (lib/Prog/check_value_c.v). *)
Definition uci_cv_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (n cur : Z) (bs : list byte) : world segs -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regs 1) mem2 (YK11.seg_rom segs)) md2 /\
    ajournal STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + CV_EV) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    @acall_kept rc segs B lyc Sc W memc W2 mem2 (spZ regs - CV_STK) (spZ regs) (fun _ => False) /\
    mo_le MT Sc S2 (uci_cv_cost n) /\
    YK11.getr regs2 10 = w64 (rp_uci_int_m (PRc.zbytes bs) cur).

(* The contract at entry address a: as check_no_overread_cg.v uci_check_no_overread_cg without a call context. *)
Definition uci_check_value_cg (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (r n cur T : Z) (bs : list byte),
    ajournal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
    YK0s.ret_ok (YK11.getr regs 1) -> 4096 <= raZ regs ->
    YK11.getr regs 3 = w64 (as_gp B) -> YK11.getr regs 4 = w64 (as_tp B) ->
    YK11.getr regs 10 = w64 r -> YK11.getr regs 11 = w64 n -> YK11.getr regs 12 = w64 cur ->
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CV_STK -> spZ regs <= sp0 ->
    INT_MIN <= cur <= INT_MAX ->
    0 <= n <= PR.REPLY_MAX -> Z.of_nat (length bs) = n ->
    (0 < n -> exists bA nA, In (bA, nA) (ablocks B lyc Sc) /\ bA <= r /\ r + n <= bA + nA) ->
    garr8 segs (mrestrict (w_H W) memc) r (map (fun b : byte => bv_unsigned b) bs) ->
    uci_rom_view_rd W memc ->
    st_nev S + k + CV_EV <= EV_MAX -> blocks_bytes Sc + CV_LIVE <= LIVE_MAX ->
    mo_ok MT Sc T -> uci_cv_cost n <= T ->
    SRr segs W (@cfg_at fx segs a regs memc mdc)
      (uci_cv_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n cur bs).

(* Its two traces (lib/A/ACej.v TRACES_check_value rows [0x51a24; 0x7f670] and [0x518c4; 0x7f858]). *)
Definition uci_cv_ufix : Prop :=
  In (uci_utrace (pc_malloc_ra0 (as_code B)) [UCI_CV_RA_MALLOC]) (as_universe B) /\
  In (uci_utrace (pc_free_ra0 (as_code B)) [UCI_CV_RA_FREE]) (as_universe B).

(* The statement the walk will prove (check_no_overread_cg.v's premises without the call-context row). *)
Definition uci_check_value_cg_holds_stmt : Prop :=
  pc_wrap_malloc (as_code B) = uci_sigma US___interceptor_trampoline_malloc ->
  pc_wrap_free (as_code B) = uci_sigma US___interceptor_trampoline_free ->
  uci_cells B ->
  uci_ro_rd_unowned B -> uci_rom_no_errno B ->
  AR_laws segs B -> ameter_laws MT ->
  uci_cv_ufix ->
  (forall fx' : YK11.FPState, @amalloc04_rule fx' rc tfib_sink_head segs B MT) ->
  (forall fx' : YK11.FPState, @afree04_rule fx' rc tfib_sink_head segs B MT) ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OCpy (uci_sigma US___asan_memcpy)) ->
  (forall fx' : YK11.FPState, @PR.uci_rp_uci_int_cg fx' rc B (uci_sigma US_rp_uci_int)) ->
  uci_check_value_cg (uci_sigma US_check_value).
End cv.
