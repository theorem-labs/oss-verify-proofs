(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec CatSim SeqExec StoreOk AsanPopFree.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Notation ASEGS := Asan.M.loaded_segments (only parsing).

(* [comment removed for export] *)
Definition asan_popfree_head : Z := 0x5425c.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Lemma PF0 : fetch_word ASEGS (Z_to_bv 64 asan_popfree_head) = Some PW0. Proof. vm_refl. Qed.
Lemma PF1 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 4)) = Some PW1. Proof. vm_refl. Qed.
Lemma PF2 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 8)) = Some PW2. Proof. vm_refl. Qed.
Lemma PF3 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 12)) = Some PW3. Proof. vm_refl. Qed.
Lemma PF4 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 16)) = Some PW4. Proof. vm_refl. Qed.
Lemma PF5 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 20)) = Some PW5. Proof. vm_refl. Qed.
Lemma PF6 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 24)) = Some PW6. Proof. vm_refl. Qed.
Lemma PF7 : fetch_word ASEGS (Z_to_bv 64 (asan_popfree_head + 28)) = Some PW7. Proof. vm_refl. Qed.

Theorem asan_popfree_spec : popfree_spec Asan.M.loaded_segments asan_popfree_head.
Proof.
  apply popfree_spec_of_code; [unfold asan_popfree_head; lia | exact PF0 | exact PF1 | exact PF2 | exact PF3 | exact PF4 | exact PF5 | exact PF6 | exact PF7].
Qed.

(* [comment removed for export] *)
Theorem asan_popfree_loop_run : forall regs mem rom i e c s n,
  getr regs 10 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 e -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 21 = Z_to_bv 64 s -> getr regs 19 = Z_to_bv 64 n ->
  (0 <= i)%Z -> (i < n)%Z -> (4 * n <= e)%Z -> (e < 2 ^ 64)%Z ->
  (0 <= c)%Z -> (0 <= s)%Z -> (c + (n - i) * s < 2 ^ 64)%Z ->
  (forall d (m : nat), (0 <= d)%Z -> (d + Z.of_nat m <= 4 * (n - i))%Z ->
     RiscvSemantics.store_ok ASEGS mem (Z_to_bv 64 (e - 4 * n + d)) m = true) ->
  exists regs',
    msteps ASEGS (mkst regs (Z_to_bv 64 asan_popfree_head) mem rom)
                (mkst regs' (Z_to_bv 64 (asan_popfree_head + 32)) (pf_mem mem e c s i (Z.to_nat (n - i))) rom)
    /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 e
    /\ getr regs' 12 = Z_to_bv 64 (c + (n - i) * s)
    /\ getr regs' 21 = Z_to_bv 64 s /\ getr regs' 19 = Z_to_bv 64 n
    /\ getr regs' 14 = Z_to_bv 64 ((c + (n - i - 1) * s) / 16) /\ getr regs' 15 = Z_to_bv 64 (e - 4 * n)
    /\ (forall r : reg, r <> 10 -> r <> 12 -> r <> 14 -> r <> 15 -> getr regs' r = getr regs r).
Proof.
  ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPopFree.popfree_loop_run); constr:(@OSSVerify.boost_beast.http_request.images.Asan.M.loaded_segments); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPopFreeAsan.asan_popfree_head); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Corelib.Init.Datatypes.nil); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Corelib.Numbers.BinNums.Z); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Corelib.Init.Logic.eq); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPopFreeAsan.PF0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPopFreeAsan.PF1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPopFreeAsan.PF2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPopFreeAsan.PF3); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPopFreeAsan.PF4); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPopFreeAsan.PF5); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPopFreeAsan.PF6); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanPopFreeAsan.PF7)|] [|@Ha; @__ff; @__varmap; @__wit; @__arith; @__sat0; @__sat1|] "##y#&#Z#:#1#?#@#>###+#/#$#4#7#B#A#F#N#O#%#T#S#,#3#5#6#8#9#;#=#E#G#J#I#H#<#K#M#Q#P#R#L#)#*#U#V#W#X#Y#Z#[#\#.#D#-#2#0#C)#T$#U$#V$#W%#X%#Y%#J%##$########%#VS&)#'D*&D%VS',&'D#k##%#k##'#&D0WS(1+Kj##L#j#$%#&D*k##L#k#$(#US)MUS*MUS+CUS,CUS-C$J$#####%#(C#$s####$#########$#$#$#$###$###$#####%#(C#XNC6S.#[O=GEEF#P%s#3(C#WS/C'#(Cs#:US0s#6WS1C$#XNC&S2#[Os#%GEEF#P[S3s#&GEEF+#VS4s#'FVS5QRVS6HS#WS7Q#Rm$%#WS8CDKXS9HS#$#l#%*)#l#&s#1s#0#l#'s#4s#3#&s#,9VS$:6'#s#BVS%%#l#('#Hl#)s#>s#;#l#*s#Is#C#&s#3IVS$I='#s#IVS%%#m#'#_S:S;I#S<S=S>S?S@SASBSC#"). Qed.
