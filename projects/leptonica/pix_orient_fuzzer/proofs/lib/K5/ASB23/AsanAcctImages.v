(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import AsanAcct.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_AsanAcctImages () := "K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib2K52AS8AsanAcct@wx_segs_nowrap_bC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C69OSSVerify5KrLib2K52AS8AsanAcctCwx_segs_nowrap_of_bC1?~~~~~~~~~~~~~~~C49OSSVerify5KrImgJTgt_pix_orient_fuzzer_bothZTgt_pix_orient_fuzzer_both_loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib2K52AS8AsanAcct<segs_below_bC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K55ASB23>AsanAcctImages8Asan_topC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2K52AS8AsanAcctDH_off_segments_aboveC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03c69OSSVerify5KrLib2K55ASB23>AsanAcctImages?Asan_segs_belowC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2K52AS8AsanAcct=ranges_from_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52AS8AsanAcctBH_off_segments_mkHC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition Asan_top : Z := 0x79a000%Z.
Lemma Asan_wx_nowrap : wx_segs_nowrap AsanUbsan_loaded_segments.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcctImages ()) [] "p;2p;1p;3g0000j23Tg000Jj12Tg001Nj30Tg001hj21Tg002oR0g004ZR1g005:R2'3%20=012d'1o"). Qed.
Lemma Asan_segs_below : segs_below_b AsanUbsan_loaded_segments Asan_top = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcctImages ()) [] "p;2p;3g0000j22Tg005Zj21Tg001Nj30Tg004ZR0g005:R1'2g002og006Z'1=001do"). Qed.
Lemma Asan_H_off_above : forall H : word -> bool,
  (forall a, H a = true -> (Asan_top <= bv_unsigned a)%Z) ->
  H_off_segments AsanUbsan_loaded_segments H.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcctImages ()) [] "h01Hh12Hah21ap;1p;3p;2p;5g007_j10Tg008Dj16Tg008bj12Tg001Nj31Tg009Ej25Tg009oj24Tg00:Kj53Tg00;S#0#0#0#0#0#0#6R0#2R1g004ZR2[f1R3f0R4O1g005:512g006ZR21503'4[^21g002oP3P2g00<8P4D3W1W0o"). Qed.
Lemma Asan_H_off_mkH : forall L A,
  ranges_from_b L Asan_top = true ->
  H_off_segments AsanUbsan_loaded_segments (mkH L A).
Proof.
ltac2:(KReplay.run1 (kr_t_AsanAcctImages ()) [] "h01Ah12HLh21Lp;1p;2p;3p;6g007_j10Tg008Dj17Tg008bj13Tg00=Dj21Tg00=dj12Tg00>Dj26Tg001Nj35Tg00?Ej64Tg00;S#0#0#0#0#0#0#7#3R0/10#2g00@KR0/10#2g004Zf1R0g006ZR1'6g005:35g002of2P0P1g00<8f0E4W1W0W2o"). Qed.
