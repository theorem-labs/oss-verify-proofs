(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import STRW_merge.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc3nat37Corelib4Init5Logicja3and46Stdlib6ZArith6BinInt1Zl42lel43addl46of_natja2eqja2or37Corelib4Init3Natoa3add37Corelib4Init5Peanoq22lel43pow04Npos35stdpp9bitvectorbdefinitionss72bvhc4listl46to_nathc4boolhc6lengthhc6optionhc4true37Corelib5Lists7ListDefhh96firstnhh95skipn3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehk37Segment3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsho38store_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8STRW_tac~~~~~~hs68st_facts79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~ih35u8arr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~il62wa79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6StrFun~~~~~~ip66copiedho3cwrite_to_memhc4prodhc4conshc3nilhc4pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jg95munchjg95wmonoil68bytes_atil67mem_invil69upd_bytesjg93ivl" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac anorm REG imm :=
  lazymatch REG with
  | Z_to_bv 64 ?E =>
      let E' :=
        lazymatch imm with
        | 0%Z => E
        | _ => lazymatch E with
               | Z.add ?x ?a =>
                   let isl := lazymatch a with Z0 => true | Zpos _ => true | Zneg _ => true | _ => false end in
                   lazymatch isl with
                   | true => let s := eval vm_compute in (a + imm)%Z in
                             lazymatch s with 0%Z => x | _ => constr:(Z.add x s) end
                   | false => constr:(Z.add E imm)
                   end
               | _ => constr:(Z.add E imm)
               end
        end in
      constr:(Z_to_bv 64 E')
  | _ => lazymatch imm with 0%Z => REG | _ => constr:(Z_to_bv 64 (bv_unsigned REG + imm)%Z) end
  end.

Ltac cur_mem_addr :=
  lazymatch goal with |- evt ?segs _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with
    | Some (Load _ _ _ ?rs ?imm, _) =>
        let rz := eval vm_compute in (bv_unsigned rs) in
        let immz := eval vm_compute in (bv_signed imm) in
        let REG := reg_val rz in anorm REG immz
    | Some (Store _ ?rs _ ?imm, _) =>
        let rz := eval vm_compute in (bv_unsigned rs) in
        let immz := eval vm_compute in (bv_signed imm) in
        let REG := reg_val rz in anorm REG immz
    end end end.

(* [comment removed for export] *)
Ltac addr_tac :=
  unfold wa;
  first [ reflexivity
        | f_equal; lia
        | lazymatch goal with |- ?v = Z_to_bv 64 ?e =>
            replace e with (bv_unsigned v) by lia; symmetry; apply Z_to_bv_bv_unsigned end ].

(* [comment removed for export] *)

Definition st_facts : ltac2:(zQ "20!h9!j4>1S$0>1D$0>1n$0>4base$0>1c$1>1k$1>2kw$1>1P$0P") := ltac2:(zQ "b0!ke!mc!h9!n1!j4!n7!o0!o5!pc!r6!rb\1S$2\1D$2\1n$2\4base$2\1c$4\1k$4\2kw$4\1P$2@2$0@2$1Z^5@2$0@2$9@2$8^4^3^2@2$0@3$6$2^1@2$3^5@1$5^4@2$0@2$1Z^1@2$0@2$1@2$3^1@1$5^3^6@2$0@2$7@2$1@2$3^8^6^7@2$1@2$3^7^6^8@2$0@2$1Z^7@2$1@2$3^7^6@2$a+2+k0").

Lemma mc_store_ok : ltac2:(zQ "h40!s1!u4!u9!h9!j4!o0!v0!v9!hg0!hg9!hh2!hj0!hja!hn8!hra!ig7!ikd!ip0!it4!n1>4segs@1$2$d>2m1>0@1$1@1$0#k0@1$9@1$1@1$0#8>1S$3>1D$3>1n$3>3src@1$2@1$1@1$0#8>2kw$4>4base$3>3xsw@1$2@1$1@1$0#8>1c$4>1k$4>1P$3>2bs@1$2@1$1@1$0#8>1a@1$1@1$0#k0>0@4$h0^e^d^b^2>0@3$h2^a^3@1$6^4>0@3$5$4@2$8@1$1@1$0#8^b@1$6^c>0@3$5@1$2@1$1@1$0#8@3$b@1$1@1$0#8^b@3$c@1$1@1$0#8@1$6^a^c^9>0@8$f^h0^f^e^b^9^8^c^7>0@3$5@1$1@1$0#k0^6@1$h1@2$h3^h0^8@3$5$7@4$e^h4^h3^7^a$a").
Proof.
  (intros segs m1 S D n src kw base xsw c k P bs a DST [L _] LEN _ nd_i3 Ha; ndestruct nd_i3 as (_ & _ & _ & HP & Hk & _)).
  eapply (u8arr_store_ok_n segs m1 D bs P k a DST); [lia | | exact Ha]. rewrite L, LEN. lia.
Qed.

Lemma mc_store : ltac2:(zQ "hd1!s1!u4!h9!u9!v0!j4!ke!o0!ite!iue!n1!iv5!hg0!ivc!hg9!jg2!hj0!hja!ikd!jk5!jke!jl7!jm3!jme!it4!hn8!ig7!ip0!n7&>0@1$1@1$0#k0@1$e@1$1@1$0#8>4segs@1$3$h9>2m0~0>2m1~0>1S$2>1D$2>1n$2>3src@1$3@1$1@1$0#8>2kw$5>4base$2>3xsw@1$3@1$1@1$0#8>1c$5>1k$5>1P$2>2bs@1$3@1$1@1$0#8>2xs@1$3@1$1@1$0#8>1a@1$1@1$0#k0>0@4$h5^h0^e^d^a>0@4$h2^h1^f^d^4>0@3$h8^c^5@1$4^6>0@2$h6^h3^h1>0@3$h3@3$b@2$9$2$2@4$f$2$2^h0@2$a^h0^f@1$d@2$9$2$2^h3^h2>0@3$h4^h5^h4^h3>0@3$7$5@2$c@1$1@1$0#8^h0@1$4^h1>0@3$7@1$3@1$1@1$0#8@3$h0@1$1@1$0#8^h0@3$h1@1$1@1$0#8@1$4^f^h1^e>0@8$ha^h5^h4^h3^h0^e^d^h1^c>0@3$7@1$3@1$1@1$0#8^b@3$h0@1$1@1$0#8^e@3$h1@1$1@1$0#8^f^h0>0@3$7$5@2$c@1$1@1$0#8^c^f>0@3$7@1$1@1$0#k0^c@1$hb@2$a^h7^f@2$6@4$h5^hc@3$8^ha^d^e^h9^h6@2$6@4$h2^hc@3$8^ha^d^e^h8@3$h7^f@1$4^h0^e@2$6@3$h8^h6@3$h7^f@1$4^h0^e@1$4@2$a^h0@1$hc^h1@2$6@2$h6^hc@3$8^ha^d^e@2$6@3$h3@3$b@2$9$2$2@4$f$2$2^h8@2$a^h8^h7@1$d@2$9$2$2^hb@3$8^ha^d^e@3$h4^hc^hb@3$8^ha^d^e").
Proof.
  (intros segs m0 m1 S D n src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW nd_i4 Hxs Hl Ha; ndestruct nd_i4 as (Hb & Hc & HPb & HP & Hk & SEP & D0 & Dn)).
  pose proof (proj1 CP) as Lbs.
  assert (SOK : store_ok segs m1 a (length xs) = true).
  { rewrite Hl. eapply mc_store_ok; eauto. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]; eauto; lia. }
  subst a. split; [|split; [|split; [|split; [|split]]]].
  - apply bytes_at_write_other; [exact SRC | lia | lia | rewrite LEN; lia].
  - apply (u8arr_write_bytes segs m1 D bs P xs DST); [lia|]. rewrite Lbs, LEN. lia.
  - apply (f_equal (@length byte)) in CP || idtac.
    rewrite <- Hl. apply copied_updZ; [exact CP | lia | | rewrite LEN; lia].
    rewrite Hl, Hxs. eapply window_sub; eauto; lia.
  - apply mem_inv_store; assumption.
  - apply munch_write; [exact MU | lia | lia |]. cbn [inside]. left. lia.
  - apply wmono_write. exact WM.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac by_byte := symmetry; apply le1_zxb.
Ltac by_lw := symmetry; lazymatch goal with |- le4 (sext 64 (bv_extract 0 32 (le_bytes_to_word ?w))) = _ =>
                lazymatch goal with L : length w = 4%nat, E : w = _ |- _ => rewrite (le4_lw w L); exact E end end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac cst_core HW c k bytes_tac SF :=
  lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
  let xs := eval cbv beta iota delta [firstn skipn] in (firstn k (skipn c xsw)) in
  let kz := eval vm_compute in (Z.of_nat k) in
  lazymatch goal with
  | SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
    MI : mem_inv ?segs ?m, MU : munch _ ?m0 ?m, WM : wmono ?segs ?m0 ?m, LEN : length src = Z.to_nat _
    |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs0) _) =>
     replace bs0 with xs by bytes_tac;
     let SRC' := fresh "SRC" in let DST' := fresh "DST" in let CP' := fresh "CP" in
     let MI' := fresh "MI" in let MU' := fresh "MU" in let WM' := fresh "WM" in
     destruct (mc_store segs m0 m S D _ src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW SF
                 ltac:(reflexivity) ltac:(reflexivity) ltac:(addr_tac))
       as (SRC' & DST' & CP' & MI' & MU' & WM');
     change (Z.of_nat k) with kz in CP';
     clear SRC DST CP MI MU WM SF;
     repeat match goal with
     | H : store_ok segs m _ _ = true |- _ => clear H
     | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
     end;
     let m' := fresh "m" in remember (write_to_mem m a xs) as m' eqn:Heqm; clear Heqm; try clear m;
     let bs' := fresh "bs" in remember (upd_bytes bs (Z.to_nat P) xs) as bs' eqn:Heqbs; clear Heqbs; try clear bs;
     rename SRC' into SRC; rename DST' into DST; rename CP' into CP;
     rename MI' into MI; rename MU' into MU; rename WM' into WM
  end end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac st HW c k bytes_tac :=
  lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
  lazymatch goal with
  | SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
    MU : munch [(_, _ + ?n)%Z] _ ?m, LEN : length src = Z.to_nat _ |- _ =>
    let a := cur_mem_addr in
    let SF := fresh "SF" in let SOK := fresh "SOK" in
    assert (SF : st_facts S D n base c k kw P) by (unfold st_facts; lia);
    pose proof (mc_store_ok segs m S D n src kw base xsw c k P bs a DST CP LEN HW SF ltac:(addr_tac)) as SOK;
    zstep; [ cst_core HW c k bytes_tac SF | .. ]
  end end.
Ltac st1 HW c := st HW c 1%nat by_byte.
Ltac st4 HW c := st HW c 4%nat by_lw.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mc_inv : ltac2:(zQ "71!s1!u4!u9!h9!hg9!hn8!jnb&>0@1$1@1$0#k0@1$4@1$1@1$0#8>4segs@1$2$5>1S$3>1D$3>3src@1$2@1$1@1$0#8>1W@1$2$6>2m0~0>2m1~0>2bs@1$2@1$1@1$0#8>1P$3P") := ltac2:(zQ "f1!s1!u4!ke!u9!h9!hg9!hn8!ikd!jnb!jk5!jke!jl7!jm3!it4!v0&>0@1$1@1$0#k0@1$5@1$1@1$0#8\4segs@1$3$6\1S$4\1D$4\3src@1$3@1$1@1$0#8\1W@1$3$8\2m0~0\2m1~0\2bs@1$3@1$1@1$0#8\1P$4@2$2@4$b^9^3^8^6@2$2@4$7^9^3^7^2@2$2@3$d^6^2@1$e^1@2$2@2$c^9^3@2$2@3$9^5^4^3@3$a^9^4^3").

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
