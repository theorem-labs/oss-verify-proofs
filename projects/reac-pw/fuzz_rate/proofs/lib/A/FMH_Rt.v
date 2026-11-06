(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/FMH_Rt.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* fm program part: the runtime contracts fm's target code needs that the donor core does not state, in the donor's
   per-call form (YG0d.v:317-419: ecall_pre, argument registers, range premises on aview, SRr to the return address with
   AR kept, callee-saved registers kept, same_but_materialized, a memory frame). Statements only; the walks are
   RtScan's (strlen, strchr, strncmp, memchr), RtStr's (strstr, strncasecmp, isalnum) and RtPrintf's (snprintf);
   a sibling that proves its own donor-form Definition of the same name replaces the one here.
   bcmp: the donor's abcmp_realizes (YG0d.v:352) at PC_bcmp. Poison / unpoison: Poison's tfib_poison16 /
   tfib_unpoison16 (design/POISON.md section 7). Design: port-fm design/HARNESS.md section 4. *)
(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMH_Rt.v (cold/port-fm-rtprintf-param 3e35620c52e) *)
(* Modified by Theorem Labs, 2026-10 (h-decbox-a4, G9 row P8-A-base): fuzz_disco.asan's SUBSET of fm's file, the two
   names the G9 snprintf route reads (FMbz_clean.v, FMrt_lift.v; g9/P0/pieces/P8-A-base.md): rt_post_ro and
   rt_post_roU, fm's text, module paths changed (no numeral in them). Dropped: the pure answer models, fm's format
   pieces and seven formats (disco's formats: SnFF's FF_disco, P2), the per-function contracts astrlen_ .. asnprintf_
   (the route states its own) and the record FmRt, whose fr_strncmp / fr_strncasecmp / fr_strstr / fr_isalnum name
   functions ABSENT in fuzz_disco (g9/P0 codeid-A.tsv). No ManifestModel / YC20 Require. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import FMH_Base.
Import ListNotations.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the post of a call that writes nothing but its stack window: return to ra, AR kept, a0 = v with R v *)
Definition rt_post_ro (STK : Z) ly S W regs mem md (R : Z -> Prop) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md' (v : Z),
    c' = cfg_at segs (raZ regs) regs' mem' md' /\
    AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
    getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
(* the same with user-poisoned ranges U live across the call (strstr runs inside fm's poison window, POISON.md 8) *)
Definition rt_post_roU (STK : Z) ly S (U : list (Z * Z)) W regs mem md (R : Z -> Prop) : world segs -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md' (v : Z),
    c' = cfg_at segs (raZ regs) regs' mem' md' /\
    AR segs B ly S W (unpoison U mem') md' /\ upoisoned segs W mem' U /\
    aregs_preserved regs regs' /\ same_but_materialized md md' /\
    getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
    (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a).
End c.
