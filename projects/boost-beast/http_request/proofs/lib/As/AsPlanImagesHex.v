(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanHexScan AsanHexTree.
Unset Lia Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition asan_hex2_blocks : list (positive * nat) :=
  [(1%positive, 0%nat); (1%positive, 1%nat); (1%positive, 2%nat); (1%positive, 3%nat); (1%positive, 4%nat); (1%positive, 5%nat); (1%positive, 6%nat); (1%positive, 7%nat); (1%positive, 8%nat); (1%positive, 9%nat); (1%positive, 10%nat); (1%positive, 11%nat); (1%positive, 12%nat); (1%positive, 13%nat); (1%positive, 14%nat)].
Lemma asan_hex2_gallv : gallv Asan_seg_bytes_002 asan_hex2_blocks.
Proof. ltac2:(KReplay.run [|constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanHexTree.ztr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanHexTree.gtree); constr:(@OSSVerify.boost_beast.http_request.images.Asan.Asan_seg_bytes_002); constr:(@Corelib.Init.Datatypes.O); constr:(@Corelib.Numbers.Cyclic.Int63.Uint63Axioms.of_pos_rec); constr:(@Corelib.Init.Nat.sub); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Numbers.BinNums.xH); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanHexTree.vtree); constr:(@Corelib.Init.Logic.and); constr:(@Corelib.Init.Logic.True); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsanHexTree.gallv); constr:(@Corelib.Init.Datatypes.cons); constr:(@Corelib.Init.Datatypes.prod); constr:(@Corelib.Numbers.BinNums.positive); constr:(@Corelib.Init.Datatypes.nat); constr:(@Corelib.Init.Datatypes.pair); constr:(@Corelib.Init.Datatypes.nil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsPlanImagesHex.asan_hex2_blocks)|] Array.empty "#%S###:#*#/#(#8#9#+#2#5#4#7#;#<#.#-#,#)#0#'#3#&#:#6#1.#/$#0%#1%#2&#3&#4&#5%#6'#7'#8&#9%#H##########################################################################################################################$#H%#D&CH#'CH$(E$#$(s#E%#D&Cs#G#'Cs#H$(E$#$-s#I%#D&Cs#K#'Cs#L$(E$#$2s#M%#D&Cs#O#'Cs#P$(E$#$7s#Q%#D&Cs#S#'Cs#T$(E$#$<s#U%#D&Cs#W#'Cs#X$(E$#$As#Y%#D&Cs#[#'Cs#\$(E$#$s#&s#]%#D&Cs#_#'Cs#`$(E$#$s#+s#a%#D&Cs#c#'Cs#d$(E$#$s#0s#e%#D&Cs#g#'Cs#h$(E$#$s#5s#i%#D&Cs#k#'Cs#l$(E$#$s#:s#m%#D&Cs#o#'Cs#p$(E$#$s#?s#q%#D&Cs#s#'Cs#t$(E$#$s#Ds#u%#D&Cs#w#'Cs#x$(E$#$s#Is#y%#D&Cs#{#'Cs#|$(E$#-#I-)#-/#-5#-;#-A#-s#'#-s#-#-s#3#-s#9#-s#?#-s#E#-s#K#-s#Q#)Es#Xm$#s#X)Es#Um$#s#U)Es#Rm$#s#R)Es#Om$#s#O)Es#Lm$#s#L)Es#Im$#s#I)Es#Fm$#s#F)Es#Cm$#s#C)Es#@m$#s#@)Es#=m$#s#=)Es#:m$#s#:)Es#7m$#s#7)Es#4m$#s#4)Es#1m$#s#1)Es#.m$#s#.*s#/I#K*s#5s#/&#*s#;s#/)#*s#As#/,#*s#Gs#//#*s#Ms#/2#*s#Ss#/5#*s#Ys#/8#*s#_s#/;#*s#es#/>#*s#ks#/A#*s#qs#/s#$#*s#ws#/s#'#*s#}s#/s#*#*s$'s#/s#-#VLFG+FGDH+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$l+FGDs$lUM2,3$#,4&#,5(#,6*#,7,#,8.#,90#,:2#,;4#,<6#,=8#,>:#,?<#,@>#,A@#VJC#m#s#$#VJCNm#$##"). Qed.
Lemma asan_hex2_0 : scanN Asan_seg_bytes_002 64 0 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex2 : vpt Asan_seg_bytes_002 0 32768.
Proof.
  change 32768%N with (1 + 32767)%N. apply vpt_app; [exact (scanN_sound _ _ 0 1 asan_hex2_0)|].
  apply (vtree_scan_sound _ asan_hex2_blocks); [exact asan_hex2_gallv| vm_compute; reflexivity].
Qed.

Lemma asan_len2 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_002) / 2) = 32768%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_len3 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 5644288%N.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition asan_hex3a_blocks : list (positive * nat) :=
  [(1%positive, 0%nat); (1%positive, 1%nat); (1%positive, 2%nat); (1%positive, 3%nat); (1%positive, 4%nat); (1%positive, 5%nat); (1%positive, 6%nat); (1%positive, 7%nat); (1%positive, 8%nat); (1%positive, 9%nat); (1%positive, 10%nat); (1%positive, 11%nat); (1%positive, 12%nat); (1%positive, 13%nat); (1%positive, 14%nat); (2%positive, 14%nat); (12%positive, 12%nat); (52%positive, 10%nat); (106%positive, 9%nat); (428%positive, 7%nat)].
Lemma asan_hex3a_gallv : gallv Asan_seg_bytes_003 asan_hex3a_blocks.
Proof. unfold asan_hex3a_blocks. gallv_vm. Qed.
Lemma asan_hex3a_0 : scanN Asan_seg_bytes_003 64 0 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex3a : vpt Asan_seg_bytes_003 0 54912.
Proof.
  change 54912%N with (1 + 54911)%N. apply vpt_app; [exact (scanN_sound _ _ 0 1 asan_hex3a_0)|].
  apply (vtree_scan_sound _ asan_hex3a_blocks); [exact asan_hex3a_gallv| vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)
Definition asan_hex3b_blocks : list (positive * nat) :=
  [(36459%positive, 4%nat); (9115%positive, 6%nat); (2279%positive, 8%nat); (285%positive, 11%nat); (143%positive, 12%nat); (9%positive, 16%nat); (5%positive, 17%nat); (6%positive, 17%nat); (28%positive, 15%nat); (58%positive, 14%nat); (118%positive, 13%nat); (1904%positive, 9%nat); (3810%positive, 8%nat); (15244%positive, 6%nat); (60980%positive, 4%nat); (121962%positive, 3%nat)].
Lemma asan_hex3b_gallv : gallv Asan_seg_bytes_003 asan_hex3b_blocks.
Proof. unfold asan_hex3b_blocks. gallv_vm. Qed.
Lemma asan_hex3b : vpt Asan_seg_bytes_003 583344 392360.
Proof. apply (vtree_scan_sound _ asan_hex3b_blocks); [exact asan_hex3b_gallv| vm_compute; reflexivity]. Qed.
