(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanHexScan AsanHexTree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition both_hex2_blocks : list (positive * nat) :=
  [(1%positive, 0%nat); (1%positive, 1%nat); (1%positive, 2%nat); (1%positive, 3%nat); (1%positive, 4%nat); (1%positive, 5%nat); (1%positive, 6%nat); (1%positive, 7%nat); (1%positive, 8%nat); (1%positive, 9%nat); (1%positive, 10%nat); (1%positive, 11%nat); (1%positive, 12%nat); (1%positive, 13%nat); (1%positive, 14%nat)].
Lemma both_hex2_gallv : gallv AsanUbsan_seg_bytes_002 both_hex2_blocks.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanHexTree.ztr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanHexTree.gtree); constr:(@OSSVerify.boost_beast.http_request.images.AsanUbsan.AsanUbsan_seg_bytes_002); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Numbers.Cyclic.Int63.Uint63Axioms.of_pos_rec); constr:(@Corelib.Init.Nat.sub); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanHexTree.vtree); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanHexTree.gallv); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.positive); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BothPlanImagesHex.both_hex2_blocks)|] Array.empty "#%S###:#*#/#(#8#9#+#2#5#4#7#;#<#.#-#,#)#0#'#3#&#:#6#1.#/$#0%#1%#2&#3&#4&#5%#6'#7'#8&#9%#H##########################################################################################################################$#H%#D&CH#'CH$(E$#$(s#E%#D&Cs#G#'Cs#H$(E$#$-s#I%#D&Cs#K#'Cs#L$(E$#$2s#M%#D&Cs#O#'Cs#P$(E$#$7s#Q%#D&Cs#S#'Cs#T$(E$#$<s#U%#D&Cs#W#'Cs#X$(E$#$As#Y%#D&Cs#[#'Cs#\$(E$#$s#&s#]%#D&Cs#_#'Cs#`$(E$#$s#+s#a%#D&Cs#c#'Cs#d$(E$#$s#0s#e%#D&Cs#g#'Cs#h$(E$#$s#5s#i%#D&Cs#k#'Cs#l$(E$#$s#:s#m%#D&Cs#o#'Cs#p$(E$#$s#?s#q%#D&Cs#s#'Cs#t$(E$#$s#Ds#u%#D&Cs#w#'Cs#x$(E$#$s#Is#y%#D&Cs#{#'Cs#|$(E$#-#I-)#-/#-5#-;#-A#-s#'#-s#-#-s#3#-s#9#-s#?#-s#E#-s#K#-s#Q#)Es#Xm$#s#X)Es#Um$#s#U)Es#Rm$#s#R)Es#Om$#s#O)Es#Lm$#s#L)Es#Im$#s#I)Es#Fm$#s#F)Es#Cm$#s#C)Es#@m$#s#@)Es#=m$#s#=)Es#:m$#s#:)Es#7m$#s#7)Es#4m$#s#4)Es#1m$#s#1)Es#.m$#s#.*s#/I#K*s#5s#/&#*s#;s#/)#*s#As#/,#*s#Gs#//#*s#Ms#/2#*s#Ss#/5#*s#Ys#/8#*s#_s#/;#*s#es#/>#*s#ks#/A#*s#qs#/s#$#*s#ws#/s#'#*s#}s#/s#*#*s$'s#/s#-#VLFG+FGDH+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$lUM2,3$#,4&#,5(#,6*#,7,#,8.#,90#,:2#,;4#,<6#,=8#,>:#,?<#,@>#,A@#VJC#m#s#$#VJCNm#$##"). Qed.
Lemma both_hex2_0 : scanN AsanUbsan_seg_bytes_002 64 0 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma both_hex2 : vpt AsanUbsan_seg_bytes_002 0 32768.
Proof.
  change 32768%N with (1 + 32767)%N. apply vpt_app; [exact (scanN_sound _ _ 0 1 both_hex2_0)|].
  apply (vtree_scan_sound _ both_hex2_blocks); [exact both_hex2_gallv| vm_compute; reflexivity].
Qed.

Lemma both_len2 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_002) / 2) = 32768%N.
Proof. vm_compute. reflexivity. Qed.
Lemma both_len3 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 5648384%N.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition both_hex3a_blocks : list (positive * nat) :=
  [(1%positive, 0%nat); (1%positive, 1%nat); (1%positive, 2%nat); (1%positive, 3%nat); (1%positive, 4%nat); (1%positive, 5%nat); (1%positive, 6%nat); (1%positive, 7%nat); (1%positive, 8%nat); (1%positive, 9%nat); (1%positive, 10%nat); (1%positive, 11%nat); (1%positive, 12%nat); (1%positive, 13%nat); (1%positive, 14%nat); (2%positive, 14%nat); (12%positive, 12%nat); (26%positive, 11%nat); (216%positive, 8%nat); (434%positive, 7%nat); (870%positive, 6%nat)].
Lemma both_hex3a_gallv : gallv AsanUbsan_seg_bytes_003 both_hex3a_blocks.
Proof. unfold both_hex3a_blocks. gallv_vm. Qed.
Lemma both_hex3a_0 : scanN AsanUbsan_seg_bytes_003 64 0 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma both_hex3a : vpt AsanUbsan_seg_bytes_003 0 55744.
Proof.
  change 55744%N with (1 + 55743)%N. apply vpt_app; [exact (scanN_sound _ _ 0 1 both_hex3a_0)|].
  apply (vtree_scan_sound _ both_hex3a_blocks); [exact both_hex3a_gallv| vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)
Definition both_hex3b_blocks : list (positive * nat) :=
  [(36511%positive, 4%nat); (1141%positive, 9%nat); (571%positive, 10%nat); (143%positive, 12%nat); (9%positive, 16%nat); (5%positive, 17%nat); (6%positive, 17%nat); (28%positive, 15%nat); (58%positive, 14%nat); (118%positive, 13%nat); (952%positive, 10%nat); (1906%positive, 9%nat); (7628%positive, 7%nat); (61032%positive, 4%nat); (122066%positive, 3%nat)].
Lemma both_hex3b_gallv : gallv AsanUbsan_seg_bytes_003 both_hex3b_blocks.
Proof. unfold both_hex3b_blocks. gallv_vm. Qed.
Lemma both_hex3b : vpt AsanUbsan_seg_bytes_003 584176 392360.
Proof. apply (vtree_scan_sound _ both_hex3b_blocks); [exact both_hex3b_gallv| vm_compute; reflexivity]. Qed.
