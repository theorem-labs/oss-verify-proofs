(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BigModel.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_BigRun () := "C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8BigModel4bindC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8BigModel1MC13~~~I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8BigModel5event01C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8BigModel5event02C13~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6BigRun>payload_eventsC13~~~I47Corelib4Init5Logic2eq00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8BigModel5event00C13~~~K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8BigModel4site02C13~~~I47Corelib7Numbers7BinNums1Z00K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8BigModel5event03C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8BigModel3exn01C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8BigModel5event04C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8BigModel3exn02C13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition sso_max : nat := 22%nat.
Definition str_alloc_bytes (n : nat) : Z :=
  if (n =? 23)%nat then 26 else Z.lor (Z.of_nat n) 7 + 1.

Record outcome := Outcome {
  o_events : list event;       (* [comment removed for export] *)
  o_thrown : option exn;       (* [comment removed for export] *)
  o_b : option sto;            (* [comment removed for export] *)
  o_c : option sto;            (* [comment removed for export] *)
  o_d : option sto             (* [comment removed for export] *)
}.

Definition harness_body (p : list Z) : M (option exn * option sto * option sto * option sto) :=
  if (length p <? 5000)%nat then
    do ra <- to_bigint lit_a sto_empty ;                      (* [comment removed for export] *)
    match ra with
    | ParseErr => ret (None, None, None, None)                (* [comment removed for export] *)
    | ParseOk a =>
      do rb <- to_bigint p sto_empty ;                        (* [comment removed for export] *)
      match rb with
      | ParseErr =>
          (* [comment removed for export] *)
          emit (EThrow SystemError22) ;; destroy a ;; emit ECatch ;;
          ret (Some SystemError22, None, None, None)
      | ParseOk b =>
          do x <- copy a ;                                    (* [comment removed for export] *)
          do m1 <- mod_assign x b ;                           (* [comment removed for export] *)
          match m1 with
          | ModZero =>
              (* [comment removed for export] *)
              destroy x ;; destroy b ;; destroy a ;; emit ECatch ;;
              ret (Some ZeroDivide, Some b, None, None)
          | ModAssert xc =>
              (* [comment removed for export] *)
              destroy xc ;; destroy b ;; destroy a ;; emit ECatch ;;
              ret (Some AssertNMaxSize, Some b, None, None)
          | ModOk x1 =>
              do c <- copy x1 ;                               (* [comment removed for export] *)
              destroy x1 ;;                                   (* [comment removed for export] *)
              do x2 <- copy b ;                               (* [comment removed for export] *)
              do m2 <- mod_assign x2 a ;                      (* [comment removed for export] *)
              match m2 with
              | ModZero =>
                  destroy x2 ;; destroy c ;; destroy b ;; destroy a ;; emit ECatch ;;
                  ret (Some ZeroDivide, Some b, Some c, None)
              | ModAssert xc =>                                (* [comment removed for export] *)
                  destroy xc ;; destroy c ;; destroy b ;; destroy a ;; emit ECatch ;;
                  ret (Some AssertNMaxSize, Some b, Some c, None)
              | ModOk x3 =>
                  do d <- copy x3 ;                           (* [comment removed for export] *)
                  destroy x3 ;;                               (* [comment removed for export] *)
                  destroy d ;; destroy c ;; destroy b ;; destroy a ;;   (* [comment removed for export] *)
                  ret (None, Some b, Some c, Some d)
              end
          end
      end
    end
  else ret (None, None, None, None).

Definition harness (p : list Z) : M (option exn * option sto * option sto * option sto) :=
  let n := length p in
  do sb <- (if (sso_max <? n)%nat then do blk <- alloc (str_alloc_bytes n) SiteString ; ret (Some blk)
            else ret None) ;                                  (* [comment removed for export] *)
  do r <- harness_body p ;
  match sb with
  | Some blk => emit (EFree blk (str_alloc_bytes n)) ;; ret r    (* [comment removed for export] *)
  | None => ret r
  end.

Definition run_payload (p : list Z) : outcome :=
  let '(r, s) := harness p st_init in
  let '(ex, b, c, d) := r in
  Outcome (rev (st_evs s)) ex b c d.

(* [comment removed for export] *)
Definition payload_events (p : list Z) : list event := o_events (run_payload p).

(* [comment removed for export] *)
Example ev_123 : payload_events [49;50;51] = [EAlloc 0 64 SiteReserve; EFree 0 64].
Proof.
ltac2:(KReplay.run1 (kr_t_BigRun ()) [] "p;1p;3p;2p10000p4p7210p10018p4p710p8g002=j1:Tg002]j10Tg003Bj12Tg003`j35Tg004kj29Tg0066j14Tg006Vj31Tg0076j26Tg007Pj13Tg0085j17Tg009Ej38Tg009_R0#:R1g00:jR2g00;IR3#0#0#0#0#0#0#2R4g00;n351924%40510510R0'6g00=8R4%33#0#0R3#0#3#2%33R3#0#2%33#2%4451451431#7=810do"). Qed.

Example ev_empty : payload_events [] = [EAlloc 0 64 SiteReserve; EFree 0 64; EThrow SystemError22; ECatch].
Proof.
ltac2:(KReplay.run1 (kr_t_BigRun ()) [] "p;1p;3p;2g002=j1:Tg002]j10Tg003Bj14Tg003`j33Tg004kj29Tg00=Vj18Tg0066j12Tg006Vj31Tg0076j25Tg0085j16Tg009Ej37Tg009_R0#:R1g00:jR2g00;I#0#0#0#0#0#0#4R3g00;n331923g00>a#8g00?j%20510510510510R0'5g00=8#2#6=710do"). Qed.

Example ev_zero : payload_events [48] = [EAlloc 0 64 SiteReserve; EFree 0 64; EThrow ZeroDivide; ECatch].
Proof.
ltac2:(KReplay.run1 (kr_t_BigRun ()) [] "p;1p;3p;2g002=j1<Tg003Bj13Tg003`j35Tg004kj2;Tg00=Vj1:Tg0066j12Tg006Vj30Tg0076j26Tg007Pj17Tg0085j18Tg009Ej39Tg002]j14Tf0#4#4p=1g009_R0#<R1g00:jR2g00;IR3#1#1#1#3R4g00;n351;24g00A5#:g00?j%20500500500500R0'6g00=8R4%73#1#1#3%2430#8=910do"). Qed.
