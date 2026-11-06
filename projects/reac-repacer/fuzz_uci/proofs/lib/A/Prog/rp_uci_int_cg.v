(* Modified by Theorem Labs: the realizes form of proofs/libreac/fuzz_boxreg/lib/A/Rt/MemchrDef.v amemchr_realizes (origin/ossv/recipes 88154566652a), stated for reac-repacer/fuzz_uci's rp_uci_int in image A, in the module and naming conventions of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v. *)
(* rp_uci_int_cg: the ASan contract of rp_uci_int (fuzz_uci.asan 0x7fef0, listing name US_rp_uci_int,
   AF_rp_uci_int = 0xc08 of lib/A/Prog/UciPList.v), as a STATEMENT only (no proof).

   The C (src/repace_conf.c rp_uci_int): parse the first line of the n-byte reply r (memchr (r, '\n', n)) as a decimal
   int, returning cur when there is none. The model is lib/Spec/UciModel.v rp_uci_int_m of the n bytes.
   The code (DIS of image A): `addi sp, sp, -0x30` (frame 0x30); when n = 0 it returns cur before any call
   (0x7ff0c); otherwise it calls the memchr interceptor's trampoline 0x4107c at 0x7ff30 with a0 = r, a1 = 0xa
   (0x7ff24 `addi a1, zero, 0xa`), a2 = n, and loads the reply bytes with four `lb` each guarded by an
   __asan_report_load1 check of their shadow byte (0x7ff94, 0x8003c, 0x800b4, 0x80100). It calls nothing else.
   The form is the runtime contracts' realizes form (MemchrDef.v amemchr_realizes): ecall_pre at entry, return to ra
   with AR at the same state, callee-saved registers kept, the result in a0, and every byte outside its stack window
   unchanged. Its stack window is its frame plus the memchr interceptor's ESTACK below it. The memchr contract is the
   general one at c = '\n' (MemchrDef.v amemchr_realizesM at musl memchr's constant window [0x10350, 0x10370), whose
   read-only view the caller passes as consts_view). The report branches are refuted by the shadow premises of the
   reply (range_addressable), and no report entry has a contract. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0s YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.A.Prog Require Import UciPSyms UciPAddr UciCg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog Require rp_uci_int_c.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YK11.
Module PRc := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Prog.rp_uci_int_c.
#[global] Remove Hints OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* rp_uci_int's own frame (its first instruction `addi sp, sp, -0x30` at US_rp_uci_int) and its stack window: the
   frame plus the ESTACK the memchr interceptor uses below the call's sp. *)
Definition RUI_FRAME : Z := 0x30.
Definition RUI_STK : Z := RUI_FRAME + ESTACK.
(* A reply is at most the 255 bytes the harness hands over (its length byte; lib/Prog/check_no_overread_c.v). *)
Definition REPLY_MAX : Z := 255.
(* musl memchr's constant window (lib/A/AE39.v mc_bounds), read by the memchr interceptor this function calls. *)
Definition UCI_MC_LO : Z := 0x10350.
Definition UCI_MC_HI : Z := 0x10370.

Section rui. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.

(* The contract at entry address a. r (a0) holds the n (a1) reply bytes bs, cur (a2) is an int; the reply is
   visible, outside the call's stack window, and addressable in the shadow; the read-only window of musl memchr is the
   image's (consts_view). The post: return to ra at the same AR state, a0 = rp_uci_int_m of the n bytes. *)
Definition uci_rp_uci_int_cg (a : Z) : Prop :=
  forall ly S W regs mem md (r n cur : Z) (bs : list byte),
    ecall_pre segs B ly S W regs mem md ->
    ly_stk_lo ly + RUI_STK <= spZ regs ->
    (forall x, spZ regs - RUI_STK <= x < spZ regs -> apresent (w_H W) mem x) ->
    YK11.getr regs 10 = w64 r -> YK11.getr regs 11 = w64 n -> YK11.getr regs 12 = w64 cur ->
    0 <= n <= REPLY_MAX -> Z.of_nat (length bs) = n -> INT_MIN <= cur <= INT_MAX ->
    0 < r -> r + n <= 2 ^ 63 ->
    garr8 segs (mrestrict (w_H W) mem) r (map (fun b : byte => bv_unsigned b) bs) ->
    (forall x, r <= x < r + n -> aview segs (w_H W) mem x <> None /\ ~ (spZ regs - RUI_STK <= x < spZ regs)) ->
    amem_range r n ->
    range_addressable (aview segs (w_H W) mem) SHADOW_OFF r n ->
    (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) r n) ->
    consts_view segs UCI_MC_LO UCI_MC_HI W mem ->
    SRr segs W (@cfg_at fx segs a regs mem md)
      (fun W' c' => W' = W /\ exists regs' mem' md',
         c' = @cfg_at fx segs (raZ regs) regs' mem' md' /\
         @AR rc segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
         YK11.getr regs' 10 = w64 (rp_uci_int_m (PRc.zbytes bs) cur) /\
         (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - RUI_STK <= x < spZ regs) ->
            aview segs (w_H W) mem' x = aview segs (w_H W) mem x) /\
         (forall x, apresent (w_H W) mem x -> apresent (w_H W) mem' x)).

(* The statement the walk will prove: the runtime cells (the shadow base and its GOT word, read at 0x7ff18), the
   allocator laws, errno outside the read-only image, and the memchr interceptor's contract at c = '\n' give the
   contract at US_rp_uci_int. *)
Definition uci_rp_uci_int_holds_stmt : Prop :=
  uci_cells B -> AR_laws segs B -> uci_rom_no_errno B ->
  (forall fx' : YK11.FPState,
     @amemchr_realizesM fx' rc segs B UCI_MC_LO UCI_MC_HI (uci_sigma US___interceptor_trampoline_memchr)) ->
  uci_rp_uci_int_cg (uci_sigma US_rp_uci_int).
End rui.
