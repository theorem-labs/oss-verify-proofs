(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import StrFun.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_STRW_memset () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.Lib.Arr.u8arr"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.to_nat"; "ms_facts"; "OSSVerify.KrLib.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.Heap.StrFun.filled"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "Corelib.Lists.ListDef.repeat"; "OSSVerify.KrLib.Lib.Mem.upd_bytes"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"].


(* [comment removed for export] *)
Definition ms_facts (A n i : Z) (k : nat) : Prop :=
  (0 <= i /\ i + Z.of_nat k <= n /\ 0 <= A /\ A + n <= 2^64)%Z.

Lemma ms_store_ok : ltac2:(CDefT.buildp (gd_tbl_STRW_memset ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Pn,$4.Pbs,(0.(2.&8.))Pi,$4.Pk,$5.Pa,(2.&40.)P,(6.R8.R7.R6.R4.)P,(7.$5.(8.(2.&8.)R5.)(9.R6.))P,(:.R8.R7.R5.R4.)P,(7.(2.&40.)R4.(;.(<.R9.R6.)))(7.$=.(>.R<.R;.R5.R6.)$?.)")
(* [comment removed for export] *).
Proof.
  (intros segs m A n bs i k a ARR LEN dd_H; ddestruct dd_H as (Hi & Hk & _); intros Ha).
  eapply (u8arr_store_ok_n segs m A bs i k a ARR); [lia | rewrite LEN; lia | exact Ha].
Qed.

Lemma ms_store : ltac2:(CDefT.buildp (gd_tbl_STRW_memset ()) "Psegs,(0.$1.)Pm0,P,(2.&40.)(3.(2.&8.))Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Pn,$4.Pbs,(0.(2.&8.))Pcb,(2.&8.)PQ,P,$4.SpPi,$4.Pk,$5.Pa,(2.&40.)P,(6.R;.R9.R8.R6.)P,(10.R6.R7.R5.)P,(7.$5.(8.(2.&8.)R8.)(9.R9.))P,(11.R>.R<.)P,(12.(13.(14.$4.$4.)(15.$4.$4.R<.(<.R<.R;.))(16.(14.$4.$4.)))R>.R=.)P,(17.R10.R?.R>.)P,(:.R>.R=.R9.R8.)P,(7.(2.&40.)R8.(;.(<.R?.R:.)))(18.(6.R13.(19.R11.R9.(1:.(2.&8.)R=.R:.))R10.(1;.R>.(9.R;.)(1:.(2.&8.)R=.R:.)))(18.(10.R=.(1;.R>.(9.R;.)(1:.(2.&8.)R=.R:.))Lj,$4.(1<.A1.R=.R1.(18.(1=.R<.R1.)(1>.R1.(<.R<.(1?.R;.))))))(18.(7.$5.(8.(2.&8.)(1;.R>.(9.R;.)(1:.(2.&8.)R=.R:.)))(9.R?.))(18.(11.R13.(19.R11.R9.(1:.(2.&8.)R=.R:.)))(18.(12.(13.(14.$4.$4.)(15.$4.$4.R10.(<.R10.R?.))(16.(14.$4.$4.)))R12.(19.R11.R9.(1:.(2.&8.)R=.R:.)))(17.R13.R12.(19.R11.R9.(1:.(2.&8.)R=.R:.))))))))")
(* [comment removed for export] *).
Proof.
  intros segs m0 m A n bs cb Q i k a ARR FIL LEN MI MU WM MF Ha.
  assert (SOK : store_ok segs m a (length (repeat cb k)) = true).
  { rewrite repeat_length. eapply ms_store_ok; eauto. }
  ddestruct MF as (Hi & Hk & A0 & An). subst a.
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

