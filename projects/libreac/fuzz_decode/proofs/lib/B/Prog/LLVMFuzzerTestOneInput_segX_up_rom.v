(* LLVMFuzzerTestOneInput_segX_up_rom: the one read-only word the image-B `up` segment of LLVMFuzzerTestOneInput
   (+0x840..+0x968) reads, the divide-by-36 multiplier 0xe38e38e38e38e38f at decodeb_obj 9 = UPSTREAM_DIV36_AT =
   DIV36_MAGIC_AT = 0x10338.

   The segment reads it in line at +0x854 (`ld a1, %lo(obj 9)(a1)`, the PLdHi slot). It comes from the statement's
   dec_crt_cells B, whose row lib/B/Prog/check_round_trip_cg.v:253 is this word as a constant cell of B, held at every
   state by AR's am_const (lib/Reusable/YG0n.v:211). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0s YK04 YA0i YA0n YA0o YP09 YG00 YG01 YG0f YG0v YG0n YG0d YI04 YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr reac_upstream_decode_c
  check_round_trip_cg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* bv is a record with a proof field, so two equal bytes need bv_eq, not reflexivity. *)
Lemma opt_byte_eq : forall x y : option byte,
  option_map (fun b : byte => bv_unsigned b) x = option_map (fun b : byte => bv_unsigned b) y -> x = y.
Proof.
intros [x|] [y|] H; cbn [option_map] in H; try discriminate; [|reflexivity].
injection H as H. f_equal. apply bv_eq. exact H.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* A c8 cell of as_const at an image address reads its value: lib/A/DecodeCallocEntryB.v:468 const_cell_valB,
   copied. *)
Lemma up_const_val : forall ly S W mem md a e,
  AR decodesegsB0 B ly S W mem md -> In (c8 (ANum a) e) (as_const B ly) ->
  val_mem decodesegsB0 (mrestrict (w_H W) mem) a 8 (aeval B ly e).
Proof.
intros ly S W mem md a e HAR Hin.
pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ (proj1 HAR)) _ Hin) as Hc.
unfold cell_holds, c8 in Hc. cbn [c_at YG0f.c_val c_w] in Hc. change (aeval B ly (ANum a)) with a in Hc.
intros k Hk. specialize (Hc k Hk). unfold aview in Hc.
destruct (mbyte decodesegsB0 (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|]; [|discriminate].
injection Hc as Hc. unfold YO0f.le_byte, YG0f.le_byte in *. rewrite <- Hc. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* The last row of dec_crt_cells. *)
Lemma up_div36_cell : dec_crt_cells B -> forall ly,
  In (z8 (ANum (decodeb_obj 9%nat)) 0xe38e38e38e38e38f) (as_const B ly).
Proof. intros HC ly. pose proof (HC ly) as H. decompose [and] H. assumption. Qed.

(* The in-line read at +0x854: the 8-byte word the PLdHi slot loads, at any state AR holds of. *)
Lemma up_div36_val : dec_crt_cells B -> forall ly S W mem md,
  AR decodesegsB0 B ly S W mem md ->
  val_mem decodesegsB0 (mrestrict (w_H W) mem) (decodeb_obj 9) 8 0xe38e38e38e38e38f.
Proof.
intros HC ly S W mem md HAR.
exact (up_const_val ly S W mem md (decodeb_obj 9) (ANum 0xe38e38e38e38e38f) HAR (up_div36_cell HC ly)).
Qed.

End c.
