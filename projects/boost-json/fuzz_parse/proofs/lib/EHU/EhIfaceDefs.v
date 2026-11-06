(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem Cells Step Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc3and46Stdlib6ZArith6BinInt1Zj62lej62lthc2or89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHUbEhIfaceDefs6EHDEFS~~~~~~ld9eh_static37Corelib4Init9Datatypesr24listr23nat04Npos35stdpp9bitvectorbdefinitionstd2bv37Corelib5Lists7ListDefvf6repeattd7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~hi93memr24consld2b879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ho78bytes_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~hsd5rsegsr23nilld5zeros36Stdlib5Lists4Listii12Inho73le879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~ik12wzr26optionho72war26lengthhc2eqj63addj66of_natld7eh_idlej63powr24Nonevf3mapld7PH_ADDRld6PH_ENTld6PH_NUMhc2exldceh_auxv_list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~ivb4u64shi9aRAUXV_CELLr24prodr24pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jl94cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jpd8rw_cellsjl92C8r23fstr23sndvf6ForallldcEH_IMG_WORDSjl92C4hi9aRSSP_GUARD" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module EHDEFS.

(* [comment removed for export] *)
  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition eh_static : ltac2:(zQ "10!h9>1a$0P") := ltac2:(zQ "50!j0!ke!l3!l8!h9\1a$4@2$3@2$0@2$1+hgths8^1@2$2^1+hgtjv0@2$0@2$1+hguri0^1@2$2^1+hguri7").

Lemma eh_static_range : ltac2:(zQ "60!j0!ke!l3!l8!h9!q6>1a$4>0@1$5^1@2$3@2$0@2$1+hgths8^2@2$2^2+hgtjv0@2$0@2$1+hguri0^2@2$2^2+hguri7").
Proof. intros a [H|H]; lia. Qed.

Definition zeros : ltac2:(zQ "40!sa!t1!t7!va>1n$1@1$0@1$3@1$2#8") := ltac2:(zQ "50!t7!t1!hh6!hhf!va\1n$1@3$2@1$4@1$0#8@2$3@1$0#8Z^1").
Definition b8 : ltac2:(zQ "30!t7!h9!va>1z$1@1$2@1$0#8") := ltac2:(zQ "30!t7!h9!hhf\1z$1@2$2@1$0#8^1").

(* [comment removed for export] *)
Definition eh_idle : ltac2:(zQ "10!hn4>1m$0P") := ltac2:(zQ "f4!hnb!h9!t7!va!ho2!hs1!iga!ih3!j0!ih9!l8!ij4!ija!inc!hn4&@3$0@1$3@1$2#8@1$4Z@1$7@1$3@1$2#8&@3$0$1+hguri3@3$0$1+hguri5@1$7$1&@3$0$1+hguri1~1&@3$b$1^1~2\1m$e@2$8@4$5$6^1+hgths8@1$9N8@2$8@4$5$6^1+hgtht0@1$9N8@2$8@4$5$6^1+hgtht8@1$9N4@2$8@2$a@4$5$6^1+hgthu0@1$9N8@2$8@4$5$6^1+hgthu0@1$c@1$d+hgthvc@4$5$6^1+hgthvc@3$0@1$3@1$2#8@1$4+o0@3$0@1$3@1$2#8@1$4Z@3$0@1$3@1$2#8@1$4+nd~0@2$a>1p$1>0~3@4$5$6^3^2@3$0@1$3@1$2#8@1$4Z~0>1p$1>0~3@4$5$6^3^2@3$0@1$3@1$2#8@1$4+1~0").   (* [comment removed for export] *)

Lemma bytes_at_agree : ltac2:(zQ "f0!t7!va!io2!h9!hs1!iob!iga!ip1!sa!j0!ipa!ipf!ke!l3!iq5>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>2m'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>1a$3>2bs@1$8@1$1@1$0#8>0@4$4$6^4^2^1>0>1i$3>0@2$9@2$c^4^1@2$d^1@2$b^4@1$e@2$7@1$1@1$0#8^3@3$a@1$2@1$1@1$0#8@1^6@1$5^2@1^7@1$5^2@4$4$6^5^4^3").
Proof.
  (intros m m' a bs nd_i1 Hag; ndestruct nd_i1 as (H0 & H1 & H)). split; [exact H0|]. split; [exact H1|].
  intros i Hi. unfold mrd. rewrite (Hag (a + Z.of_nat i)) by lia. apply H. exact Hi.
Qed.

Lemma eh_idle_agree : ltac2:(zQ "d0!t7!va!io2!iqe!iob!j0!ipa!h9!q6!hn4!ke!l3!ir8>1m$9>2m'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>0@1$3^2>0>1a$7>0@2$5@2$aZ^1@2$b^1@2$c+2+k0>0@1$8^2@3$6@1$2@1$1@1$0#8@1^5@1$4^3@1^6@1$4^3@1$3^3").
Proof.
  (intros m m' nd_i2 Hag; ndestruct nd_i2 as (G0 & G1 & G2 & P & F)).
  assert (AG : forall lo n, 0x10d1c8 <= lo -> lo + Z.of_nat n <= 0x10d3f0 ->
            forall i, lo <= i < lo + Z.of_nat n -> m' (wa i) = m (wa i)).
  { intros lo n Hlo Hhi i Hi. apply Hag; [lia|]. left. lia. }
  assert (AF : forall lo n, 0x10eb20 <= lo -> lo + Z.of_nat n <= 0x10eb27 ->
            forall i, lo <= i < lo + Z.of_nat n -> m' (wa i) = m (wa i)).
  { intros lo n Hlo Hhi i Hi. apply Hag; [lia|]. right. lia. }
  split; [eapply bytes_at_agree; [exact G0 | apply AG; cbn; lia]|].
  split; [eapply bytes_at_agree; [exact G1 | apply AG; cbn; lia]|].
  split; [eapply bytes_at_agree; [exact G2 | apply AG; cbn; lia]|].
  split.
  - destruct P as [P | [P1 P2]].
    + left. eapply bytes_at_agree; [exact P | apply AG; cbn; lia].
    + right. split; (eapply bytes_at_agree; [eassumption | apply AG; cbn -[Z.add]; rewrite ?length_le8; cbn; lia]).
  - destruct F as [F|F]; [left|right]; intros p Hp; pose proof (F p Hp) as X;
      (eapply bytes_at_agree; [exact X | apply AF; cbn [In] in Hp; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
Qed.

(* [comment removed for export] *)
Lemma eh_idle_of_pristine : ltac2:(zQ "90!t7!va!io2!ire!ipa!h9!iqe!q6!iob>1m>1x@1$1@1$0#k0@1$2@1$1@1$0#8>0>1a$5>0@1$7^1@3$4@1$2@1$1@1$0#8@1^3@1$8^2@1$3@1$1@1$0#8@1$6^2").
Proof.
  intros m H.
  assert (Z8 : forall lo n, 0x10d1c8 <= lo -> lo + Z.of_nat n <= 0x10d3f0 \/ (0x10eb20 <= lo /\ lo + Z.of_nat n <= 0x10eb27) ->
             (forall i, (i < n)%nat -> seg_rom rsegs (wa (lo + Z.of_nat i)) = Some (b8 0)) ->
             bytes_at rsegs m lo (zeros n)).
  { intros lo n Hlo Hr Hrom. split; [lia|]. unfold zeros. rewrite repeat_length. split; [lia|].
    intros i Hi. unfold mrd. rewrite H by (unfold eh_static; lia).
    rewrite (Hrom i Hi). symmetry. rewrite nth_error_repeat by exact Hi. reflexivity. }
  split; [apply Z8; [lia|lia|]; intros i Hi; do 8 (destruct i as [|i]; [vm_compute; reflexivity|]); lia|].
  split; [apply Z8; [lia|lia|]; intros i Hi; do 8 (destruct i as [|i]; [vm_compute; reflexivity|]); lia|].
  split; [apply Z8; [lia|lia|]; intros i Hi; do 4 (destruct i as [|i]; [vm_compute; reflexivity|]); lia|].
  split; [left; apply Z8; [lia|lia|]; intros i Hi; do 8 (destruct i as [|i]; [vm_compute; reflexivity|]); lia|].
  left. intros p Hp. change [b8 0; b8 0] with (zeros 2).
  cbn [In] in Hp. destruct Hp as [<- |[<- |[<- |[]]]];
    (apply Z8; [lia|lia|]; intros i Hi; do 2 (destruct i as [|i]; [vm_compute; reflexivity|]); lia).
Qed.

(* [comment removed for export] *)
Definition PH_ADDR : Z := 0x10040.
Definition PH_ENT  : Z := 56.
Definition PH_NUM  : Z := 10.
Definition eh_auxv_list : ltac2:(zQ "40!h9!sa!t7!va>3x16$0>2x6$0>3x11$0>3x12$0>3x23$0>3rnd$0@1$1@1$3@1$2#k0") := ltac2:(zQ "a0!h9!hnb!ih3!is5!t7!isb!it5!ite!inc!va\3x16$0\2x6$0\3x11$0\3x12$0\3x23$0\3rnd$0@4$3$0@1$9@1$4#k0$8@3$1$0+3@3$1$0$5@3$1$0+4@3$1$0$6@3$1$0+5@3$1$0$7@3$1$0+h0@3$1$0^6@3$1$0+6@3$1$0^5@3$1$0+b@3$1$0^4@3$1$0+c@3$1$0^3@3$1$0+h7@3$1$0^2@3$1$0+h9@3$1$0^1@3$1$0Z@3$1$0Z@1$2$0").
Definition eh_auxv_ok : ltac2:(zQ "20!h9!hn4>1m$1>1B$0P") := ltac2:(zQ "f0!j0!h9!ke!iu7!ir8!l3!hs1!iga!iuc!jj5!ija!inc!jjd!hn4!ipf\1m$d\1B$1@2$3$1\2av$1@2$3$1\3x16$1@2$3$1\2x6$1@2$3$1\3x11$1@2$3$1\3x12$1@2$3$1\3x23$1@2$3$1\3rnd$1@2$0@4$6$7^9$c@1$a@1$b^7@2$0@4$6$7^9^7@1$9@6$8^6^5^4^3^2^1@2$0@2$2^8^7@2$0@2$2@2$e^7+q0@2$4+2+k0@2$0@2$0@2$2Z^6@2$5^6@2$4+2+k0@2$0@2$0@2$2Z^5@2$5^5@2$4+2+k0@2$0@2$0@2$2Z^4@2$5^4@2$4+2+k0@2$0@2$0@2$2Z^3@2$5^3@2$4+2+k0@2$0@2$0@2$2Z^2@2$5^2@2$4+2+k0@2$0@2$2Z^1@2$5^1@2$4+2+k0").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition EH_IMG_WORDS : ltac2:(zQ "30!h9!sa!jkb@1$1@2$2$0$0") := ltac2:(zQ "50!h9!jkb!hnb!jl2!ih3@3$2@2$1$0$0@4$3$0$0+vrpu0+tnsp4@3$2@2$1$0$0@4$3$0$0+vrpu8+tnssc@3$2@2$1$0$0@4$3$0$0+vrpv0+tntm8@3$2@2$1$0$0@4$3$0$0+vrqh0+tnuoc@3$2@2$1$0$0@4$3$0$0+vrqh8+tnvn4@3$2@2$1$0$0@4$3$0$0+vrqi0+tnvpc@3$2@2$1$0$0@4$3$0$0+vrqj8+togk8@3$2@2$1$0$0@4$3$0$0+vrrg8+vsuu8@3$2@2$1$0$0@4$3$0$0+vrri0Z@3$2@2$1$0$0@4$3$0$0+vrrm0+vrrg8@3$2@2$1$0$0@4$3$0$0+vrrn8+pmil4@3$2@2$1$0$0@4$3$0$0+vrrs0+vpjr0@3$2@2$1$0$0@4$3$0$0+vrrt0+vsuk0@3$2@2$1$0$0@4$3$0$0+vrrt8+vsuj8@3$2@2$1$0$0@4$3$0$0+vrru0+hgths8@3$2@2$1$0$0@4$3$0$0+vrsn8+hiusj8@3$2@2$1$0$0@4$3$0$0+vssv8+pojl0@3$2@2$1$0$0@4$3$0$0+vsuj8+nrhl0@3$2@2$1$0$0@4$3$0$0+vsuk0+nrilc@1$4@2$1$0$0").                                  (* [comment removed for export] *)
Definition eh_img : ltac2:(zQ "10!hn4>1m$0P") := ltac2:(zQ "h40!h9!jp5!hnb!ih3!jt8!iga!jkb!j0!t7!ju4!inc!va!jua!jv0!iu7!jv6!jvf!kge!kh4!hn4\1m$h3@2$7@3$f@2$6$0$0\2av@2$6$0$0@4$4$5^2@3$c$0$0^1@3$2$1@1$9@1$a@3$d$0$0^1@1$3$1$h0@2$7@4$4$5^1+hivjq8@3$2$1@1$h1@1$aZ@1$3$1@2$e@1$b@1$8#k0\3can@1$b@1$8#k0@4$4$5^2$h2@3$2$1@1$9^1@1$3$1").              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition eh_STACK : Z := 24576.   (* [comment removed for export] *)

End EHDEFS.
(* [comment removed for export] *)
