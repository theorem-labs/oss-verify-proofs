(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc3nat46Stdlib6ZArith6BinInt1Zja2le37Corelib4Init5Logicl73andja3addja6of_natja3pow04Npos35stdpp9bitvectorbdefinitionsoc2bvl72eqhc4listhc4boolhc6lengthhc6optionhc4true3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeta7Segment3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshh98store_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~hlc5u8arr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hpf2wa79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUbSTRW_memset~~~~~~htf8ms_factsja6to_nat37Corelib5Lists7ListDefij76repeathc4prodhh9cwrite_to_memhpf9upd_byteshc4conshc3nilhc4pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ip05munchip05wmonohpf7mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6StrFun~~~~~~iu96filledl72orja2lt" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition ms_facts : ltac2:(zQ "20!h9!j4>1A$0>1n$0>1i$0>1k$1P") := ltac2:(zQ "70!l2!mb!h9!n1!j4!n7!o0\1A$2\1n$2\1i$2\1k$4@2$1@2$0Z^2@2$1@2$0@2$3^2@1$5^1^3@2$1@2$0Z^4@2$0@2$3^4^3@2$6+2+k0").

Lemma ms_store_ok : ltac2:(zQ "h10!o6!q9!qe!h9!r3!j4!ra!s1!sa!t3!hgf!hl0!hp6!ht9!ii2!n1!iie>4segs@1$4$a>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1A$3>1n$3>2bs@1$4@1$1@1$0#8>1i$3>1k$5>1a@1$1@1$0#k0>0@4$c^8^7^6^4>0@3$2$5@2$7@1$1@1$0#8^5@1$h0^6>0@4$e^8^7^5^4>0@3$2@1$1@1$0#k0^4@1$d@2$f^9^6@3$2$6@4$b^c^b^5^6$9").
Proof.
  (intros segs m A n bs i k a ARR LEN nd_i1 Ha; ndestruct nd_i1 as (Hi & Hk & _)).
  eapply (u8arr_store_ok_n segs m A bs i k a ARR); [lia | rewrite LEN; lia | exact Ha].
Qed.

Lemma ms_store : ltac2:(zQ "he3!o6!h9!q9!ike!mb!iie!il8!ilf!n1!j4!qe!imf!inc!s1!r3!io3!sa!io9!hp6!isc!it5!ite!ji7!jj1!hgf!ht9!ii2!l2!jj6!n7&>0@1$2@1$0#k0@1$h0@1$2@1$0#8&@3$7^h1^9@3$3@1$2@1$0#8^d^a&@3$b^e@1$5^b@3$3@1$2@1$0#8^d^a>4segs@1$e$h8>2m0~0>1m~0>1A$1>1n$1>2bs@1$e@1$2@1$0#8>2cb@1$2@1$0#8>1Q>0$1P>1i$1>1k$9>1a@1$2@1$0#k0>0@4$h2^b^9^8^6>0@3$h6^6^7^5>0@3$a$9@2$d@1$2@1$0#8^8@1$5^9>0@2$h5^e^c>0@3$h3@3$c@2$6$1$1@4$h1$1$1^c@2$8^c^b@1$f@2$6$1$1^e^d>0@3$h4^h0^f^e>0@4$ha^e^d^9^8>0@3$a@1$2@1$0#k0^8@1$h9@2$8^f^a@2$4@4$h2^h3~1^h0~2@2$4@3$h6^d~2\1j$1@2$h7@1^d^1@2$4@2$hb^c^1@2$hc^1@2$8^c@1$hd^b@2$4@3$a$9@2$d@1$2@1$0#8~2@1$5^f@2$4@2$h5^h3~1@2$4@3$h3@3$c@2$6$1$1@4$h1$1$1^h0@2$8^h0^f@1$f@2$6$1$1^h2~1@3$h4^h3^h2~1").
Proof.
  intros segs m0 m A n bs cb Q i k a ARR FIL LEN MI MU WM MF Ha.
  assert (SOK : store_ok segs m a (length (repeat cb k)) = true).
  { rewrite repeat_length. eapply ms_store_ok; eauto. }
  ndestruct MF as (Hi & Hk & A0 & An). subst a.
  split; [|split; [|split; [|split; [|split]]]].
  - apply (u8arr_write_bytes segs m A bs i _ ARR); [lia|]. rewrite repeat_length, LEN. lia.
  - apply filled_updZ; [exact FIL | lia | rewrite LEN; lia].
  - rewrite upd_bytes_length; [exact LEN|]. rewrite repeat_length, LEN. lia.
  - apply mem_inv_store; assumption.
  - apply munch_write; [exact MU | lia | rewrite repeat_length; lia |]. cbn [inside]. left. rewrite repeat_length. lia.
  - apply wmono_write. exact WM.
Qed.

(* [comment removed for export] *)
Ltac ms_arr_store MF bytes_tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs ?Q, LEN : length ?bs = Z.to_nat ?n,
    MI : mem_inv ?segs ?m, MU : munch _ ?m0 ?m, WM : wmono ?segs ?m0 ?m
    |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs0) _) =>
    lazymatch type of MF with ms_facts _ _ ?i ?k =>
     let xs := eval cbv beta iota delta [repeat] in (repeat cb k) in
     let kz := eval vm_compute in (Z.of_nat k) in
     replace (write_to_mem m a bs0) with (write_to_mem m (wa (A + i)%Z) xs)
       by (apply (f_equal2 (write_to_mem m)); [ unfold wa; first [ reflexivity | f_equal; lia | rewrite ?Z.add_0_r; apply Z_to_bv_bv_unsigned ] | bytes_tac ]);
     let ARR' := fresh "ARR" in let FIL' := fresh "FIL" in let LEN' := fresh "LEN" in
     let MI' := fresh "MI" in let MU' := fresh "MU" in let WM' := fresh "WM" in
     destruct (ms_store segs m0 m A n bs cb Q i k _ ARR FIL LEN MI MU WM MF eq_refl)
       as (ARR' & FIL' & LEN' & MI' & MU' & WM');
     change (repeat cb k) with xs in ARR', FIL', LEN', MI', MU', WM';
     change (repeat cb k) with xs;
     cbv beta in FIL'; change (Z.of_nat k) with kz in FIL';
     clear ARR FIL LEN MI MU WM MF;
     repeat match goal with
     | H : store_ok segs m _ _ = true |- _ => clear H
     | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
     end;
     let m' := fresh "m" in remember (write_to_mem m (wa (A + i)%Z) xs) as m' eqn:Heqm; clear Heqm; try clear m;
     let bs' := fresh "bs" in remember (upd_bytes bs (Z.to_nat i) xs) as bs' eqn:Heqbs; clear Heqbs; try clear bs;
     rename ARR' into ARR; rename FIL' into FIL; rename LEN' into LEN;
     rename MI' into MI; rename MU' into MU; rename WM' into WM
    end
  end.

Ltac mst i k bytes_tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, LEN : length ?bs = Z.to_nat ?n |- _ =>
    let MF := fresh "MF" in let SOK := fresh "SOK" in
    assert (MF : ms_facts A n i k) by (unfold ms_facts; lia);
    pose proof (ms_store_ok segs m A n bs i k (wa (A + i)) ARR LEN MF eq_refl) as SOK; unfold wa in SOK;
    zstep; [ ms_arr_store MF bytes_tac | .. ]
  end.

