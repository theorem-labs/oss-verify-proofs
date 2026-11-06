(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AllocWalkKit AW_LargeAlloc1 AW_PoisonRemap1 AllocTacX.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~he3ivl37Corelib7Numbers7BinNumsm01Z46Stdlib6ZArith6BinInt1Znd2le03fst03snd37Corelib4Init5Logicq42or37Corelib5Lists7ListDefrd6Forall03nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAllocPerfKit~~~~~~u27out_img04cons04pair04prodheddisjoint_fromnd3addm04Npos35stdpp9bitvectorbdefinitionshld2bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsfAW_PoisonRemap1~~~~~~ho04RENV06option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~ht55asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~ih93memhe5munchhe5wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AseAW_LargeAlloc1~~~~~~ime4SENVhldbbv_unsignedu26parked" s.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition out_img : ltac2:(zQ "20!h8!la>1W@1$0$1P") := ltac2:(zQ "80!n9!la!p5!pa!h8!pf!r8!t4\1W@1$4$1@3$7$1\1r$1@2$6@2$2@3$5$0$0^1+hggg0@2$2+nhmgg0@3$3$0$0^1^1").

Lemma out_img_nil : ltac2:(zQ "30!td!hi4!la@1$1@1$0$2"). Proof. constructor. Qed.
Lemma out_img_cons : ltac2:(zQ "90!n9!hi4!p5!hie!h8!hj4!hja!r8!la>2lo$0>2hi$0>1W@1$4$8>0@2$7@2$2^2+hggg0@2$2+nhmgg0^3>0@1$1^2@1$1@3$3@2$6$0$0@4$5$0$0^5^4^3").
Proof. intros lo hi W H HW. constructor; [exact H| exact HW]. Qed.

Lemma out_img_disjoint : ltac2:(zQ "70!p5!n9!h8!hi4!hk0!la!hl0>1W@1$2$5>1a$1>1n$1>0@1$3^3>0@2$0+hggg0^3>0@2$0@2$6^4^3+nhmgg0>0@2$0Z^4@3$4^7^6^5").
Proof.
  induction W as [|[lo hi] W IH]; intros a n HW Ha Hn Hn0; [exact I|].
  inversion HW as [|r W' Hr HW']; subst. cbn [fst snd] in Hr. cbn [disjoint_from]. split; [| apply IH; assumption].
  destruct Hr as [Hr|Hr]; [right| left]; lia.
Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Lemma renv_transport_img : ltac2:(zQ "b0!hl6!hna!hs5!h8!hsd!ih0!hi4!il7!la!ile!im6>1g@1$1@1$0#k0>1b@1$1@1$0#8>1m$7>2m'>0@1$1@1$0#k0@1$4@1$1@1$0#8>1W@1$3$8>0@3$2^5^4^3>0@3$9^2^4^3>0@3$a$5^5^4>0@1$6^4@3$2^9^8^6").
  Proof.
    intros g b m m' W E MU WM HW.
    apply (renv_transport g b m m' W E MU WM); apply (out_img_disjoint W _ _ HW); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma senv_transport_img : ltac2:(zQ "h00!hl6!hl0!p5!n9!hna!ir2!ira!h8!hsd!ih0!hi4!il7!hk0!la!ile!im6>2tp@1$4@1$0#k0>3TSD$3>3CTX$3>2TH$3>1m$b>2m'>0@1$4@1$0#k0@1$8@1$4@1$0#8>1W@1$7$d>0@5$5^7^6^5^4^3>0@3$e^2^4^3>0@3$f$9^5^4>0@1$a^4>0@2$2+hggg0@2$1@2$6@1$0#k0^b-l8>0@2$2@2$1@2$1@2$6@1$0#k0^c-l8+8+nhmgg0>0@2$2+hggg0^c>0@2$2@2$1^d+8+nhmgg0>0@3$c^9@2$1^d+p8+8@5$5^h0^f^e^d^b").
  Proof.
    intros tp TSD CTX TH m m' W E MU WM HW T1 T2 D1 D2 DC.
    apply (senv_transport tp TSD CTX TH m m' W E MU WM); try exact DC; apply (out_img_disjoint W _ _ HW); lia.
  Qed.
End HCW.

(* [comment removed for export] *)
Ltac out_img_tac tac :=
  repeat first [ apply out_img_nil | apply out_img_cons; [ tac | ] ].

(* [comment removed for export] *)
Ltac renv_img_at E MU WM E' :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of E with AW_PoisonRemap1.RENV ?g ?b m =>
      assert (E' : AW_PoisonRemap1.RENV g b m');
      [ apply (renv_transport_img g b m m' W E MU WM); out_img_tac ltac:(cbn [fst snd]; region_decide) | ]
    end end.
Ltac senv_img_at E MU WM E' :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of E with SENV ?tp ?TSD ?CTX ?TH m =>
      assert (E' : SENV tp TSD CTX TH m');
      [ apply (senv_transport_img tp TSD CTX TH m m' W E MU WM);
        [ out_img_tac ltac:(cbn [fst snd]; region_decide) | .. ]; cbn [disjoint_from]; region_decide | ]
    end end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition parked : ltac2:(zQ "00>1PPP") := ltac2:(zQ "00\1PP^1").
Lemma park : ltac2:(zQ "10!is9>1PP>0^1@1$0^2"). Proof. intros P p. exact p. Qed.
Lemma unpark : ltac2:(zQ "10!is9>1PP>0@1$0^1^2"). Proof. intros P p. exact p. Qed.
Global Opaque parked.

(* [comment removed for export] *)
Ltac park_mem m keep :=
  repeat match goal with
  | H : rw_cells _ m _ _ |- _ => tryif constr_eq H keep then fail else apply park in H
  | H : ro_cells _ m _ _ |- _ => apply park in H
  | H : stk _ m _ _ |- _ => tryif constr_eq H keep then fail else apply park in H
  | H : u8arr _ m _ _ |- _ => apply park in H
  | H : u32arr _ m _ _ |- _ => apply park in H
  | H : u64arr _ m _ _ |- _ => apply park in H
  | H : u8ro _ m _ _ |- _ => apply park in H
  | H : bytes_at _ m _ _ |- _ => apply park in H
  | H : wr_at _ m _ _ |- _ => apply park in H
  end.
Ltac unpark_all := repeat match goal with H : parked _ |- _ => apply unpark in H end.

(* [comment removed for export] *)
Ltac spill_block FR lo hi tac :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m0 _) =>
    let MUP := fresh "MUP" in let WMP := fresh "WMP" in
    pose proof (munch_refl [(lo, hi)] m0) as MUP; pose proof (wmono_refl segs m0) as WMP;
    park_mem m0 FR;
    tac;
    unpark_all;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      transport_after_call segs m0 m1 MUP WMP; clear MUP WMP
    end
  end.

(* [comment removed for export] *)
Ltac spill_frame tac :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
    match goal with FRx : rw_cells _ m0 ?A [CB ?n _] |- _ =>
      let hi := lazymatch A with
                | (?b + ?k)%Z => let k' := eval vm_compute in (k + Z.of_nat n)%Z in constr:((b + k')%Z)
                | _ => constr:((A + Z.of_nat n)%Z)
                end in
      spill_block FRx A hi tac
    end
  end.

(* [comment removed for export] *)
Ltac st1f := step; fix_lit_store; try (rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned by lia).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac join_open JT JOIN := evar (JT : Prop); cut JT; [ intros JOIN | ].
Ltac join_here JT JOIN :=
  lazymatch goal with |- ?G => let e := eval unfold JT in JT in unify e G end; unfold JT in JOIN; exact JOIN.
Ltac join_here1 JT JOIN r :=
  lazymatch goal with |- evt ?s ?P (MS ?R ?F ?pc ?fc ?rv ?mm ?ro) =>
    let e := eval unfold JT in JT in
    unify e (forall x : word, evt s P (MS (bvmap_set r x R) F pc fc rv mm ro)) end;
  unfold JT in JOIN; eapply JOIN.
Ltac join_here3 JT JOIN r1 r2 r3 :=
  lazymatch goal with |- evt ?s ?P (MS ?R ?F ?pc ?fc ?rv ?mm ?ro) =>
    let e := eval unfold JT in JT in
    unify e (forall x y z : word, evt s P (MS (bvmap_set r1 x (bvmap_set r2 y (bvmap_set r3 z R))) F pc fc rv mm ro)) end;
  unfold JT in JOIN; eapply JOIN.
Ltac join_again JT JOIN := unfold JT in JOIN; first [ exact JOIN | eapply JOIN ].
(* [comment removed for export] *)
