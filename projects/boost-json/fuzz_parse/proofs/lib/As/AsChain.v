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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep Exec TacX CellsX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsUnwind.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc3and37Corelib4Init9Datatypesj64prod46Stdlib6ZArith6BinInt1Zl52lel52ltl53powj64listj64pairhc2eq89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsChain3HCW~~~~~~p06achain79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~ta3mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~hhd5aceil36Stdlib5Lists4Listhm42Inl53addl56modulo04Npos35stdpp9bitvectorbdefinitionshp22bvj66option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hre2wal53subhc3iffta8as_chainta3asrtaachain_lawsj63appj64consj63nilhc3not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsUnwind~~~~~~ik15upush79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~io84cellj63natj63sndhc2ex37Corelib5Lists7ListDefitd3map79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~ivb5asegsio82C8hp27Z_to_bvitd6firstnik1bframe_chainik15uloop79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jn28rw_cells" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW.
  Context {HCEIL : HeapCeil}.

Inductive achain (m : mem) : Z -> list (Z * Z) -> Prop :=
| ach_nil : forall cur, (cur <= aceil \/ cur mod 8 <> 0) -> achain m cur []
| ach_cons : forall cur CH fp ra,
    achain m cur CH -> 0 <= cur < 2^64 -> 0 <= ra < 2^64 ->
    fp mod 16 = 0 -> aceil + 16 <= fp -> fp < 2^64 ->
    rw_cells asegs m (fp - 16) [C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 ra)] ->
    achain m fp ((fp, ra) :: CH).

(* [comment removed for export] *)

Lemma achain_range_law : ltac2:(zQ "f0!h9!j0!ke!md!n2!n7!nd!o4!ob!t1!hh7!hlb!hn7!hnd!ho3>1m$a>3cur$0>2CH@1$6@2$2$0$0>2fp$0>2ra$0>0@3$9^5^4^3>0@3$c@2$2$0$0@4$7$0$0^3^2^4@2$1@2$1@2$3@2$d@1$b?5HCEIL+h0^4@2$4^4@2$5+2+k0@2$1@3$8$0@2$e^4+8Z@2$1@2$3Z^3@2$4^3@2$5+2+k0").
Proof.
  intros m cur CH fp ra H. induction H as [cur Hc|cur CH fp' ra' H IH Hcur Hra Hal Hlo Hhi RC]; intros IN; [destruct IN|].
  destruct IN as [E|IN]; [injection E; intros <- <-| apply IH; exact IN].
  split; [lia|]. split; [Z.div_mod_to_equations; nia| lia].
Qed.

Lemma achain_ext_law : ltac2:(zQ "h00!h9!hoc!hqf!hr5!ke!t1!hv8!nd!o4!j0!ob!hh7!hn7!md!n2!hve>1m$b>2m'>1x@1$2@1$1#k0@1$3@1$2@1$1#8>3cur$0>2CH@1$7@2$4$0$0>0@3$5^4^2^1>0>2fp$0>2ra$0>1a$0>0@3$c@2$4$0$0@4$8$0$0^3^2^5>0@2$9@2$d@2$f^4+h0^2@2$e^2^4@3$a@1$3@1$2@1$1#8@1^9@1$6^3@1^a@1$6^3@3$5^5^4^3").
Proof.
  intros m m' cur CH H. induction H as [cur Hc|cur CH fp ra H IH Hcur Hra Hal Hlo Hhi RC]; intros EQ.
  - apply ach_nil. exact Hc.
  - apply (ach_cons m' cur); try assumption.
    + apply IH. intros fp' ra' a IN Ha. apply (EQ fp' ra'); [right; exact IN| exact Ha].
    + destruct RC as [[WF (B0 & B1 & BB)] (W0 & W1 & WW)]. split; [split; [exact WF|]|].
      * split; [exact B0|]. split; [exact B1|]. intros i Hi. unfold mrd. rewrite (EQ fp ra); [apply BB; exact Hi| left; reflexivity|].
        cbn in Hi. lia.
      * split; [exact W0|]. split; [exact W1|]. intros i Hi.
        pose proof (WW i Hi) as HW. unfold wview in *. rewrite (EQ fp ra); [exact HW| left; reflexivity| cbn in Hi; lia].
Qed.

(* [comment removed for export] *)
Lemma achain_laws : ltac2:(zQ "90!h9!nd!ke!ig4!t1!iga!ih5!ihb!hh7>1H$6>0>1m$8>3cur$0>2CH@1$1@2$2$0$0@2$3@4$5^4^3^2^1@3$4^3^2^1@2$7?5HCEIL^2").
Proof.
  intros H E. split; [| split; [| split]].
  - intros m cur Hc. apply (proj2 (E _ _ _)). apply ach_nil. exact Hc.
  - intros m cur CH fp ra C Hcur Hra Hal Hlo Hhi RC. apply (proj2 (E _ _ _)). apply (ach_cons m cur); try assumption. apply (proj1 (E _ _ _)). exact C.
  - intros m m' cur CH C EQ. apply (proj2 (E _ _ _)). eapply achain_ext_law; [apply (proj1 (E _ _ _)); exact C| exact EQ].
  - intros m cur CH fp ra C IN. eapply achain_range_law; [apply (proj1 (E _ _ _)); exact C| exact IN].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma upush_neq : ltac2:(zQ "80!h9!nd!ob!ii8!iie!ij5!ijb!inf>3pc0$0>2ra$0>3acc@1$1$0>0@1$6@3$2$0^2^3@3$2@1$1$0@3$7^4^3^2@3$3$0^2@3$4$0^3@1$5$0").
Proof. intros pc0 ra acc NE. unfold upush. destruct (Z.eqb_spec ra pc0); [contradiction| reflexivity]. Qed.

Section Bridge.
  Variable top : Z.

  (* [comment removed for export] *)
  Lemma achain_frame_chain_gen : ltac2:(zQ "he0!h9!nd!ke!iie!j0!is4!md!isc!it2!it8!iv4!hoc!jj6!jjf!n2!n7!jk5!ii8!ij5!ob!ijb!jl0!t1!hh7!hlb!jla!jm9!jqd!hn7!hve>1m$h7>1L@1$1@2$2$0$0>3cur$0>0@3$h6^3^1^2>2bp$0>3ra0$0>0@4$hb$c^6@2$hd^2+h0@3$3$5@1$d@2$h0@1$b#k0^4@3$3$5@1$d@2$h0@1$b#k0^1@1$h2$5>0@2$6@1$h8?5HCEIL^3>0@2$4@2$6Z^6@2$e^6@2$f+2+k0>0@2$4@2$6Z^4@2$e^4@2$f+2+k0@2$9@1$1@2$2$0$0\3CHu@1$1@2$2$0$0@2$4@5$h9$c^b?3top^7^1>3pc0$0>2md$0>3acc@1$1$0>0@1$h4@3$hc$0^3@3$3$0^9@4$a@2$2$0$0$0@2$8$0$0^d@2$9$7\1j$7@3$h3@1$1$0@4$ha^5^4^6^3@3$h1$0^3@3$h5$0^1@3$3$0^b@4$a@2$2$0$0$0@2$8$0$0^f").
  Proof.
    intros m L cur H. induction H as [cur Hc|cur L fp ra1 H IH Hcur Hra1 Hal Hlo Hhi RC]; intros bp ra0 REC BP CUR RA0.
    - (* [comment removed for export] *)
      assert (G : goodframe bp cur top = false).
      { unfold goodframe. destruct Hc as [Hc|Hc].
        - destruct (Z.ltb_spec bp cur); [lia| reflexivity].
        - destruct (Z.eqb_spec (cur mod 8) 0); [lia|]. rewrite andb_false_r. reflexivity. }
      exists [(ra0, cur)]. split.
      + apply fc_last; assumption.
      + intros pc0 md acc NI.
        destruct (Z.leb_spec md (Z.of_nat (length acc))).
        { exists 0%nat. rewrite uloop_cut by lia. cbn. rewrite app_nil_r. reflexivity. }
        destruct (Z.ltb_spec ra0 KPAGE).
        { exists 0%nat. rewrite uloop_page by lia. cbn. rewrite app_nil_r. reflexivity. }
        rewrite uloop_last by lia. rewrite upush_neq by (intros K; apply NI; left; exact K).
        exists 1%nat. reflexivity.
    - (* [comment removed for export] *)
      destruct (goodframe bp fp top) eqn:G.
      + ndestruct (IH fp ra1 RC ltac:(lia) Hcur Hra1) as (CH' & FC' & UL').
        exists ((ra0, fp) :: CH'). split.
        * apply fc_link; try assumption; lia.
        * intros pc0 md acc NI. pose proof (frame_chain_nonnil _ _ _ _ _ FC') as NN.
          destruct CH' as [|x rest]; [congruence|].
          destruct (Z.leb_spec md (Z.of_nat (length acc))).
          { exists 0%nat. rewrite uloop_cut by lia. cbn. rewrite app_nil_r. reflexivity. }
          destruct (Z.ltb_spec ra0 KPAGE).
          { exists 0%nat. rewrite uloop_page by lia. cbn. rewrite app_nil_r. reflexivity. }
          rewrite uloop_link by lia. rewrite upush_neq by (intros K; apply NI; left; exact K).
          destruct (UL' pc0 md (acc ++ [ra0]) ltac:(intros K; apply NI; right; exact K)) as [j E].
          exists (S j). rewrite E, <- app_assoc. reflexivity.
      + exists [(ra0, fp)]. split.
        * apply fc_last; try assumption; lia.
        * intros pc0 md acc NI.
          destruct (Z.leb_spec md (Z.of_nat (length acc))).
          { exists 0%nat. rewrite uloop_cut by lia. cbn. rewrite app_nil_r. reflexivity. }
          destruct (Z.ltb_spec ra0 KPAGE).
          { exists 0%nat. rewrite uloop_page by lia. cbn. rewrite app_nil_r. reflexivity. }
          rewrite uloop_last by lia. rewrite upush_neq by (intros K; apply NI; left; exact K).
          exists 1%nat. reflexivity.
  Qed.

  (* [comment removed for export] *)
End Bridge.

(* [comment removed for export] *)

End HCW.

(* [comment removed for export] *)
