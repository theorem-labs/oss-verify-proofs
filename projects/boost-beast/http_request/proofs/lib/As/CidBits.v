(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition cb1 (size : Z) : Z := Z.lor size (size ≫ 1 mod 18446744073709551616) mod 18446744073709551616.
Definition cb2 (e1 : Z) : Z := Z.lor e1 (e1 ≫ 2 mod 18446744073709551616) mod 18446744073709551616.
Definition cb3 (e2 : Z) : Z := Z.lor e2 (e2 ≫ 4 mod 18446744073709551616) mod 18446744073709551616.
Definition cb4 (e3 : Z) : Z := Z.lor e3 (e3 ≫ 8 mod 18446744073709551616) mod 18446744073709551616.
Definition cb5 (e4 : Z) : Z := Z.lor e4 (e4 ≫ 16 mod 18446744073709551616) mod 18446744073709551616.
Definition cb6 (e5 : Z) : Z := Z.lor e5 (e5 ≫ 32 mod 18446744073709551616) mod 18446744073709551616.
Definition cb7 (e6 : Z) : Z := Z.lxor e6 18446744073709551615 mod 18446744073709551616.
Definition cb8 (e7 : Z) : Z := (e7 - Z.land (e7 ≫ 1 mod 18446744073709551616) 6148914691236517205 mod 18446744073709551616) mod 18446744073709551616.
Definition cb9 (e8 : Z) : Z := (Z.land e8 3689348814741910323 + Z.land (e8 ≫ 2 mod 18446744073709551616) 3689348814741910323) mod 18446744073709551616.
Definition cb10 (e9 : Z) : Z := (e9 + e9 ≫ 4) mod 18446744073709551616.
Definition cb11 (e10 : Z) : Z := ((Z.land e10 1085102592571150095 mod 18446744073709551616 * 72340172838076673) mod 18446744073709551616) ≫ 56 mod 18446744073709551616.
Definition cb12 (e11 : Z) : Z := bv_swrap 32 (62 - e11) mod 18446744073709551616.
Definition cb13 (size e12 : Z) : Z := size ≫ (e12 mod 64) mod 18446744073709551616.
Definition cb14 (e12 : Z) : Z := bv_swrap 32 (18446744073709551615 ≪ (e12 mod 32)) mod 18446744073709551616.
Definition cb15 (size e14 : Z) : Z := Z.land size (Z.lxor e14 18446744073709551615 mod 18446744073709551616) mod 18446744073709551616.
Definition cb16 (e11 e13 e15 : Z) : Z := (Z.lor (Z.lxor (e11 ≪ 1 mod 18446744073709551616) 126 mod 18446744073709551616) (Z.land e13 1 mod 18446744073709551616) + Z.b2z (0 mod 18446744073709551616 <? e15) mod 18446744073709551616 + -2) mod 18446744073709551616.

Definition cidbits (size : Z) : Z :=
  let e1 := cb1 size in
  let e2 := cb2 e1 in
  let e3 := cb3 e2 in
  let e4 := cb4 e3 in
  let e5 := cb5 e4 in
  let e6 := cb6 e5 in
  let e7 := cb7 e6 in
  let e8 := cb8 e7 in
  let e9 := cb9 e8 in
  let e10 := cb10 e9 in
  let e11 := cb11 e10 in
  let e12 := cb12 e11 in
  let e13 := cb13 size e12 in
  let e14 := cb14 e12 in
  let e15 := cb15 size e14 in
  let e16 := cb16 e11 e13 e15 in
  e16.

(* [comment removed for export] *)
Fixpoint forall_range (f : Z -> bool) (a : Z) (n : nat) : bool :=
  match n with O => true | S k => if f a then forall_range f (a + 1) k else false end.
Definition forall_rangeZ (f : Z -> bool) (a n : Z) : bool := forall_range f a (Z.to_nat n).
Lemma forall_range_spec : forall f n a x, forall_range f a n = true -> a <= x < a + Z.of_nat n -> f x = true.
Proof.
  intros f n. induction n as [|k IH]; intros a x H Hx; [cbn in Hx; lia|].
  cbn [forall_range] in H. destruct (f a) eqn:E; [|discriminate].
  destruct (Z.eq_dec x a) as [->|NE]; [exact E|]. eapply IH; [exact H|]. lia.
Qed.
Lemma forall_rangeZ_spec : forall f a n x, forall_rangeZ f a n = true -> 0 <= n -> a <= x < a + n -> f x = true.
Proof. intros f a n x H Hn Hx. eapply forall_range_spec; [exact H|]. rewrite Z2Nat.id by exact Hn. exact Hx. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition M64 : Z := 18446744073709551615.
Lemma mod64_land : forall x, x mod 18446744073709551616 = Z.land x 18446744073709551615.
Proof. intros x. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by (clear; lia). reflexivity. Qed.
Lemma mod6_land : forall x, x mod 64 = Z.land x 63.
Proof. intros x. change 63 with (Z.ones 6). rewrite Z.land_ones by (clear; lia). reflexivity. Qed.
Lemma mod5_land : forall x, x mod 32 = Z.land x 31.
Proof. intros x. change 31 with (Z.ones 5). rewrite Z.land_ones by (clear; lia). reflexivity. Qed.
Lemma swrap32_land : forall z, bv_swrap 32 z = Z.land (z + 2147483648) 4294967295 - 2147483648.
Proof.
  intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  change (4294967296 `div` 2) with 2147483648. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by (clear; lia). reflexivity.
Qed.

Definition cf1 (size : Z) : Z := Z.land (Z.lor size (Z.land (size ≫ 1) 18446744073709551615)) 18446744073709551615.
Definition cf2 (e1 : Z) : Z := Z.land (Z.lor e1 (Z.land (e1 ≫ 2) 18446744073709551615)) 18446744073709551615.
Definition cf3 (e2 : Z) : Z := Z.land (Z.lor e2 (Z.land (e2 ≫ 4) 18446744073709551615)) 18446744073709551615.
Definition cf4 (e3 : Z) : Z := Z.land (Z.lor e3 (Z.land (e3 ≫ 8) 18446744073709551615)) 18446744073709551615.
Definition cf5 (e4 : Z) : Z := Z.land (Z.lor e4 (Z.land (e4 ≫ 16) 18446744073709551615)) 18446744073709551615.
Definition cf6 (e5 : Z) : Z := Z.land (Z.lor e5 (Z.land (e5 ≫ 32) 18446744073709551615)) 18446744073709551615.
Definition cf7 (e6 : Z) : Z := Z.land (Z.lxor e6 18446744073709551615) 18446744073709551615.
Definition cf8 (e7 : Z) : Z := Z.land (e7 - Z.land (Z.land (Z.land (e7 ≫ 1) 18446744073709551615) 6148914691236517205) 18446744073709551615) 18446744073709551615.
Definition cf9 (e8 : Z) : Z := Z.land (Z.land e8 3689348814741910323 + Z.land (Z.land (e8 ≫ 2) 18446744073709551615) 3689348814741910323) 18446744073709551615.
Definition cf10 (e9 : Z) : Z := Z.land (e9 + e9 ≫ 4) 18446744073709551615.
Definition cf11 (e10 : Z) : Z := Z.land ((Z.land (Z.land (Z.land e10 1085102592571150095) 18446744073709551615 * 72340172838076673) 18446744073709551615) ≫ 56) 18446744073709551615.
Definition cf12 (e11 : Z) : Z := Z.land (Z.land (62 - e11 + 2147483648) 4294967295 - 2147483648) 18446744073709551615.
Definition cf13 (size e12 : Z) : Z := Z.land (size ≫ (Z.land e12 63)) 18446744073709551615.
Definition cf14 (e12 : Z) : Z := Z.land (Z.land (18446744073709551615 ≪ (Z.land e12 31) + 2147483648) 4294967295 - 2147483648) 18446744073709551615.
Definition cf15 (size e14 : Z) : Z := Z.land (Z.land size (Z.land (Z.lxor e14 18446744073709551615) 18446744073709551615)) 18446744073709551615.
Definition cf16 (e11 e13 e15 : Z) : Z :=
  Z.land (Z.lor (Z.land (Z.lxor (Z.land (e11 ≪ 1) 18446744073709551615) 126) 18446744073709551615) (Z.land (Z.land e13 1) 18446744073709551615)
          + Z.land (Z.b2z (Z.land 0 18446744073709551615 <? e15)) 18446744073709551615 + -2) 18446744073709551615.

Lemma cf1_eq : forall x, cb1 x = cf1 x. Proof. intros. unfold cb1, cf1. rewrite !mod64_land. reflexivity. Qed.
Lemma cf2_eq : forall x, cb2 x = cf2 x. Proof. intros. unfold cb2, cf2. rewrite !mod64_land. reflexivity. Qed.
Lemma cf3_eq : forall x, cb3 x = cf3 x. Proof. intros. unfold cb3, cf3. rewrite !mod64_land. reflexivity. Qed.
Lemma cf4_eq : forall x, cb4 x = cf4 x. Proof. intros. unfold cb4, cf4. rewrite !mod64_land. reflexivity. Qed.
Lemma cf5_eq : forall x, cb5 x = cf5 x. Proof. intros. unfold cb5, cf5. rewrite !mod64_land. reflexivity. Qed.
Lemma cf6_eq : forall x, cb6 x = cf6 x. Proof. intros. unfold cb6, cf6. rewrite !mod64_land. reflexivity. Qed.
Lemma cf7_eq : forall x, cb7 x = cf7 x. Proof. intros. unfold cb7, cf7. rewrite !mod64_land. reflexivity. Qed.
Lemma cf8_eq : forall x, cb8 x = cf8 x. Proof. intros. unfold cb8, cf8. rewrite !mod64_land. reflexivity. Qed.
Lemma cf9_eq : forall x, cb9 x = cf9 x. Proof. intros. unfold cb9, cf9. rewrite !mod64_land. reflexivity. Qed.
Lemma cf10_eq : forall x, cb10 x = cf10 x. Proof. intros. unfold cb10, cf10. rewrite !mod64_land. reflexivity. Qed.
Lemma cf11_eq : forall x, cb11 x = cf11 x. Proof. intros. unfold cb11, cf11. rewrite !mod64_land. reflexivity. Qed.
Lemma cf12_eq : forall x, cb12 x = cf12 x. Proof. intros. unfold cb12, cf12. rewrite !mod64_land, swrap32_land. reflexivity. Qed.
Lemma cf13_eq : forall x y, cb13 x y = cf13 x y. Proof. intros. unfold cb13, cf13. rewrite !mod64_land, mod6_land. reflexivity. Qed.
Lemma cf14_eq : forall x, cb14 x = cf14 x. Proof. intros. unfold cb14, cf14. rewrite !mod64_land, swrap32_land, mod5_land. reflexivity. Qed.
Lemma cf15_eq : forall x y, cb15 x y = cf15 x y. Proof. intros. unfold cb15, cf15. rewrite !mod64_land. reflexivity. Qed.
Lemma cf16_eq : forall x y z, cb16 x y z = cf16 x y z. Proof. ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.land); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.lor); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Stdlib.ZArith.BinInt.Z.lxor); constr:(@Stdlib.ZArith.BinInt.Z.shiftl); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Numbers.BinNums.xH); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xI); constr:(@Stdlib.ZArith.BinInt.Z.b2z); constr:(@Stdlib.ZArith.BinInt.Z.ltb); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.mod64_land); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cb16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf16)|] [|@z; @y; @x|] "#%U#'#<#*###$#%#3#8#1#9#&#;#=#>#4#5#,#-#/#:#.#<#+#7#6#2#00#/$#0$#1%#2%#3%#4&#5%#6$#7)#8%#9$#:$#;%.GVIF##G##############################################################################################################################.#'s#D#$G$#$#$#$###.#/*#'#,%Es#O'#.)%#'H0,#D-#'#3&'#UJs#U&$#$1$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#.#%s#>#VIKs$9%#%/#s#M%#'%Fs$=%#))%#%H+,#E-#%#.&'#&#s#L%#1(CD#j#$C#%s#Z4'/s#d)D#,s#XE-#'#s#h&&#&#s#W%#<(C#.j#$C#%s$S?/Ds#g%#A)#/&#,&#s#`%#s#%(C#7j#$C#%s#ls#()s#$D&#3&#s#g%#s#,(C#>j#$C#%s#ns#/&s#(D&#s#m%#s#2(C#s#$j#$C#,DE-#%#s#7&s#0#&#s#u%#s#:(C#s#,j#$C#/@s$(%#s#>)#9,s#7D-#%#s#B&&#&#s$$%#s#EVLC#*H+Cs#?.$s$-#*s$,+C=8$s$,#*s$3+Cs#&@$s$3#*s%%+Cs#1s#)$s$@#*s$9+Cs#>s#4$s$9#'s$0s$D*s$1+Cs#Rs#B%$#WMFEDWNFED(C$#m#&#j#$C#j#%C#j#&C##"). Qed.

Definition cidfast (size : Z) : Z :=
  let e11 := cf11 (cf10 (cf9 (cf8 (cf7 (cf6 (cf5 (cf4 (cf3 (cf2 (cf1 size)))))))))) in
  let e12 := cf12 e11 in
  cf16 e11 (cf13 size e12) (cf15 size (cf14 e12)).

Lemma forall_range_ext : forall f g n a, (forall x, f x = g x) -> forall_range f a n = forall_range g a n.
Proof. intros f g n. induction n as [|k IH]; intros a E; [reflexivity|]. cbn [forall_range]. rewrite (E a), (IH (a + 1) E). reflexivity. Qed.
Lemma forall_rangeZ_ext : forall f g a n, (forall x, f x = g x) -> forall_rangeZ f a n = forall_rangeZ g a n.
Proof. intros f g a n E. unfold forall_rangeZ. apply forall_range_ext. exact E. Qed.

Lemma cid_chkF_lo : forall_rangeZ (fun s => Z.eqb (cidfast s) (class_id s)) 513 32512 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma cid_chkF_hi : forall_rangeZ (fun s => Z.eqb (cidfast s) (class_id s)) 33025 32512 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma cidbits_unfold : forall size, cidbits size = cb16 (cb11 (cb10 (cb9 (cb8 (cb7 (cb6 (cb5 (cb4 (cb3 (cb2 (cb1 size))))))))))) (cb13 size (cb12 (cb11 (cb10 (cb9 (cb8 (cb7 (cb6 (cb5 (cb4 (cb3 (cb2 (cb1 size))))))))))))) (cb15 size (cb14 (cb12 (cb11 (cb10 (cb9 (cb8 (cb7 (cb6 (cb5 (cb4 (cb3 (cb2 (cb1 size)))))))))))))).
Proof. intros size. reflexivity. Qed.

Lemma cidbits_fast : forall size, cidbits size = cidfast size.
Proof.
  ltac2:(KReplay.run [|constr:(@Corelib.Numbers.BinNums.Z); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cb16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cb11); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cb10); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cb9); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cb8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cb7); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cb6); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cb5); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cb4); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cb3); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cb2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cb1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cb13); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cb12); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cb15); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cb14); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cidfast); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf16); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf11); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf10); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf9); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf7); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf6); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf5); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf4); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf3); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf2); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf1); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf13); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf12); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf15); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf14); constr:(@Corelib.Init.Logic.eq_refl); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf1_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf2_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf3_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf4_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf5_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf6_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf7_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf8_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf9_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf10_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf11_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf12_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf13_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf14_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf15_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cf16_eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cidbits); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.CidBits.cidbits_unfold)|] [|@z; @size|] "#%z#%#\#(###$#5#4#3#2#1#0#/#.#-#,#+#7#6#;#G#9#8#*#L#M#N#O#P#Q#R#S#T#U#V#W#X#Y#Z#[#\#]#^#:#<#J#)#K#H#I#=#>#?#@#A#B#C#D#E#F4#K&#L&#M%#N)#O$#P%#Q$#R$#S$#T$#U$#V$#W$#X$#Y$#Z$#[$UFDUG#UH#UI#UJ#UK#UL#UM#UN#UO#UP#UQ#VRD#US%$VS&D#WS''%#US#E#CD#j#$C#$+)'US$E3#2#1#0#/#.#-#,#+#*#)#(E#'$%E#$'%##CD#j#$C#%D;UFEUG#UH#UI#UJ#UK#UL#UM#UN#UO#UP#UQ#VRE#$%#D#C#4j#$C#'s#.%ED$*(##C#9j#$C#(Ds#3'-%E#$0D##C#?j#$C#)s#:(ED'D%E#$7%##C#s#&j#$C#*s#B)D(E#'$%E#$D%##C#s#.j#$C#+s#K*D)#(E#'$%E#$'%##C#s#7j#$C#,s#U+D*#)#(E#'$%E#$'%##C#s#Aj#$C#-s#`,D+#*#)#(E#'$%E#$'%##C#s#Lj#$C#.s#l-D,#+#*#)#(E#'$%E#$'%##C#s#Xj#$C#/s#y.D-#,#+#*#)#(E#'$%E#$'%##C#s#ej#$C#0s$+/D.#-#,#+#*#)#(E#'$%E#$'%##C#s#sj#$C#1s$:0D/#.#-#,#+#*#)#(E#'$%E#$'%##C#s$&j#$C#2s$J1D0#/#.#-#,#+#*#)#(E#'$%E#$'%##C#s$6j#$C#3s$[2D1#0#/#.#-#,#+#*#)#(E#'$%E#$'%##C#s$Gj#$C#US$D3D2#1#0#/#.#-#,#+#*#)#(E#'$%E#$'%##C#s$Yj#$C#342#1#0#/#.#-#,#+#*#)#(D#'$%D#$'%#VS(C#US)D&Cs#%4$s%3#US*s%4&Cs#8s#($s%4#US+s%5&Cs#Js#;$s%5#US,s%6&Cs#[s#M$s%6#US-s%7&Cs#ks#^$s%7#US.s%8&Cs#zs#n$s%8#US/s%9&Cs$,s#}$s%9#US0s%:&Cs$9s$/$s%:#US1s%;&Cs$Es$<$s%;#US2s%<&Cs$Ps$H$s%<#US3s%=&Cs$Zs$S$s%=#US4s%>&Cs$cs$]$s%>#VS5Ds%?&Cs$ks$f$s%?#US6s%A&Cs$rs$n$s%@#VS7Ds%A&Cs%)s$u$s%A#WS8s%Fs%Ds%B&Cs%>s%,$s%B#US#D#Cs%D#m#%#US9DUS:D&Cs%Hs%E%$#j#%C##"). Qed.
Lemma cid_chk_lo : forall_rangeZ (fun s => Z.eqb (cidbits s) (class_id s)) 513 32512 = true.
Proof.
  rewrite (forall_rangeZ_ext _ (fun s => Z.eqb (cidfast s) (class_id s))); [exact cid_chkF_lo|].
  intros x. rewrite cidbits_fast. reflexivity.
Qed.
Lemma cid_chk_hi : forall_rangeZ (fun s => Z.eqb (cidbits s) (class_id s)) 33025 32512 = true.
Proof.
  rewrite (forall_rangeZ_ext _ (fun s => Z.eqb (cidfast s) (class_id s))); [exact cid_chkF_hi|].
  intros x. rewrite cidbits_fast. reflexivity.
Qed.

Lemma cidbits_ok : forall size e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16,
  512 < size <= 65536 ->
  e1 = cb1 size ->
  e2 = cb2 e1 ->
  e3 = cb3 e2 ->
  e4 = cb4 e3 ->
  e5 = cb5 e4 ->
  e6 = cb6 e5 ->
  e7 = cb7 e6 ->
  e8 = cb8 e7 ->
  e9 = cb9 e8 ->
  e10 = cb10 e9 ->
  e11 = cb11 e10 ->
  e12 = cb12 e11 ->
  e13 = cb13 size e12 ->
  e14 = cb14 e12 ->
  e15 = cb15 size e14 ->
  e16 = cb16 e11 e13 e15 ->
  e16 = class_id size.
Proof.
  intros size e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 SZ He1 He2 He3 He4 He5 He6 He7 He8 He9 He10 He11 He12 He13 He14 He15 He16.
  assert (C : Z.eqb (cidbits size) (class_id size) = true).
  { destruct (Z.lt_ge_cases size 33025).
    - exact (forall_rangeZ_spec (fun s => Z.eqb (cidbits s) (class_id s)) 513 32512 size cid_chk_lo ltac:(lia) ltac:(lia)).
    - exact (forall_rangeZ_spec (fun s => Z.eqb (cidbits s) (class_id s)) 33025 32512 size cid_chk_hi ltac:(lia) ltac:(lia)). }
  apply Z.eqb_eq in C. rewrite cidbits_unfold in C. subst. exact C.
Qed.

(* [comment removed for export] *)
Lemma class_id_chk : forall_rangeZ (fun s => (1 <=? class_id s) && (class_id s <? 32)) 1 65536 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma class_id_range : forall size, 1 <= size <= 65536 -> 1 <= class_id size < 32.
Proof.
  intros size Hs.
  pose proof (forall_rangeZ_spec (fun s => (1 <=? class_id s) && (class_id s <? 32)) 1 65536 size class_id_chk ltac:(lia) ltac:(lia)) as C.
  cbv beta in C. apply andb_prop in C. destruct C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. lia.
Qed.

(* [comment removed for export] *)
Lemma class_size_ge_chk : forall_rangeZ (fun s => s <=? class_size (class_id s)) 1 65536 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma class_size_ge : forall size, 1 <= size <= 65536 -> size <= class_size (class_id size).
Proof.
  intros size Hs.
  pose proof (forall_rangeZ_spec (fun s => s <=? class_size (class_id s)) 1 65536 size class_size_ge_chk ltac:(lia) ltac:(lia)) as C.
  cbv beta in C. apply Z.leb_le in C. exact C.
Qed.
