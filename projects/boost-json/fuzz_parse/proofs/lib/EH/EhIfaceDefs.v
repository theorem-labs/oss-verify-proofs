(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem Cells Step Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc3and46Stdlib6ZArith6BinInt1Zj62lej62lthc2or89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbEhIfaceDefs6EHDEFS~~~~~~ld9eh_static37Corelib4Init9Datatypesr14listr13nat04Npos35stdpp9bitvectorbdefinitionstc2bv37Corelib5Lists7ListDefve6repeattc7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~hi83memr14consld2b879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ho58bytes_at79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~hsb5rsegsr13nilld5zeros36Stdlib5Lists4Listihe2Inho53le879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~ije2wzr16optionho52war16lengthhc2eqj63addj66of_natld7eh_idlej63powr14Noneve3mapld7PH_ADDRld6PH_ENTld6PH_NUMhc2exldceh_auxv_list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~iv84u64shi8aRAUXV_CELLr14prodr14pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~jl64cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jpa8rw_cellsjl62C8r13fstr13sndve6ForallldcEH_IMG_WORDSjl62C4hi8aRSSP_GUARD" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module EHDEFS.

(* [comment removed for export] *)
  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition eh_static : ltac2:(zQ "10!h9>1a$0P") := ltac2:(zQ "50!j0!ke!l3!l8!h9\1a$4@2$3@2$0@2$1+hgpso8^1@2$2^1+hgpur0@2$0@2$1+hgrlu0^1@2$2^1+hgrlu7").

Lemma eh_static_range : ltac2:(zQ "60!j0!ke!l3!l8!h9!q5>1a$4>0@1$5^1@2$3@2$0@2$1+hgpso8^2@2$2^2+hgpur0@2$0@2$1+hgrlu0^2@2$2^2+hgrlu7").
Proof. intros a [H|H]; lia. Qed.

Definition zeros : ltac2:(zQ "40!s9!t0!t6!v9>1n$1@1$0@1$3@1$2#8") := ltac2:(zQ "50!t6!t0!hh5!hhe!v9\1n$1@3$2@1$4@1$0#8@2$3@1$0#8Z^1").
Definition b8 : ltac2:(zQ "30!t6!h9!v9>1z$1@1$2@1$0#8") := ltac2:(zQ "30!t6!h9!hhe\1z$1@2$2@1$0#8^1").

(* [comment removed for export] *)
Definition eh_idle : ltac2:(zQ "10!hn2>1m$0P") := ltac2:(zQ "f4!hn9!h9!t6!v9!ho0!hrf!ig7!ih0!j0!ih6!l8!ij1!ij7!in9!hn2&@3$0@1$3@1$2#8@1$4Z@1$7@1$3@1$2#8&@3$0$1+hgrlu3@3$0$1+hgrlu5@1$7$1&@3$0$1+hgrlu1~1&@3$b$1^1~2\1m$e@2$8@4$5$6^1+hgpso8@1$9N8@2$8@4$5$6^1+hgpsp0@1$9N8@2$8@4$5$6^1+hgpsp8@1$9N4@2$8@2$a@4$5$6^1+hgpsq0@1$9N8@2$8@4$5$6^1+hgpsq0@1$c@1$d+hgpsrc@4$5$6^1+hgpsrc@3$0@1$3@1$2#8@1$4+o0@3$0@1$3@1$2#8@1$4Z@3$0@1$3@1$2#8@1$4+nd~0@2$a>1p$1>0~3@4$5$6^3^2@3$0@1$3@1$2#8@1$4Z~0>1p$1>0~3@4$5$6^3^2@3$0@1$3@1$2#8@1$4+1~0").   (* [comment removed for export] *)

Lemma bytes_at_agree : ltac2:(zQ "f0!t6!v9!inf!h9!hrf!io8!ig7!ioe!s9!j0!ip7!ipc!ke!l3!iq2>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>2m'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>1a$3>2bs@1$8@1$1@1$0#8>0@4$4$6^4^2^1>0>1i$3>0@2$9@2$c^4^1@2$d^1@2$b^4@1$e@2$7@1$1@1$0#8^3@3$a@1$2@1$1@1$0#8@1^6@1$5^2@1^7@1$5^2@4$4$6^5^4^3").
Proof.
  (intros m m' a bs nd_i1 Hag; ndestruct nd_i1 as (H0 & H1 & H)). split; [exact H0|]. split; [exact H1|].
  intros i Hi. unfold mrd. rewrite (Hag (a + Z.of_nat i)) by lia. apply H. exact Hi.
Qed.

Lemma eh_idle_agree : ltac2:(zQ "d0!t6!v9!inf!iqb!io8!j0!ip7!h9!q5!hn2!ke!l3!ir5>1m$9>2m'>1x@1$1@1$0#k0@1$2@1$1@1$0#8>0@1$3^2>0>1a$7>0@2$5@2$aZ^1@2$b^1@2$c+2+k0>0@1$8^2@3$6@1$2@1$1@1$0#8@1^5@1$4^3@1^6@1$4^3@1$3^3").
Proof.
  (intros m m' nd_i2 Hag; ndestruct nd_i2 as (G0 & G1 & G2 & P & F)).
  assert (AG : forall lo n, 0x109c88 <= lo -> lo + Z.of_nat n <= 0x109eb0 ->
            forall i, lo <= i < lo + Z.of_nat n -> m' (wa i) = m (wa i)).
  { intros lo n Hlo Hhi i Hi. apply Hag; [lia|]. left. lia. }
  assert (AF : forall lo n, 0x10b5e0 <= lo -> lo + Z.of_nat n <= 0x10b5e7 ->
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
Lemma eh_idle_of_pristine : ltac2:(zQ "90!t6!v9!inf!irb!ip7!h9!iqb!q5!io8>1m>1x@1$1@1$0#k0@1$2@1$1@1$0#8>0>1a$5>0@1$7^1@3$4@1$2@1$1@1$0#8@1^3@1$8^2@1$3@1$1@1$0#8@1$6^2").
Proof.
  intros m H.
  assert (Z8 : forall lo n, 0x109c88 <= lo -> lo + Z.of_nat n <= 0x109eb0 \/ (0x10b5e0 <= lo /\ lo + Z.of_nat n <= 0x10b5e7) ->
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
Definition eh_auxv_list : ltac2:(zQ "40!h9!s9!t6!v9>3x16$0>2x6$0>3x11$0>3x12$0>3x23$0>3rnd$0@1$1@1$3@1$2#k0") := ltac2:(zQ "a0!h9!hn9!ih0!is2!t6!is8!it2!itb!in9!v9\3x16$0\2x6$0\3x11$0\3x12$0\3x23$0\3rnd$0@4$3$0@1$9@1$4#k0$8@3$1$0+3@3$1$0$5@3$1$0+4@3$1$0$6@3$1$0+5@3$1$0$7@3$1$0+h0@3$1$0^6@3$1$0+6@3$1$0^5@3$1$0+b@3$1$0^4@3$1$0+c@3$1$0^3@3$1$0+h7@3$1$0^2@3$1$0+h9@3$1$0^1@3$1$0Z@3$1$0Z@1$2$0").
Definition eh_auxv_ok : ltac2:(zQ "20!h9!hn2>1m$1>1B$0P") := ltac2:(zQ "f0!j0!h9!ke!iu4!ir5!l3!hrf!ig7!iu9!jj2!ij7!in9!jja!hn2!ipc\1m$d\1B$1@2$3$1\2av$1@2$3$1\3x16$1@2$3$1\2x6$1@2$3$1\3x11$1@2$3$1\3x12$1@2$3$1\3x23$1@2$3$1\3rnd$1@2$0@4$6$7^9$c@1$a@1$b^7@2$0@4$6$7^9^7@1$9@6$8^6^5^4^3^2^1@2$0@2$2^8^7@2$0@2$2@2$e^7+q0@2$4+2+k0@2$0@2$0@2$2Z^6@2$5^6@2$4+2+k0@2$0@2$0@2$2Z^5@2$5^5@2$4+2+k0@2$0@2$0@2$2Z^4@2$5^4@2$4+2+k0@2$0@2$0@2$2Z^3@2$5^3@2$4+2+k0@2$0@2$0@2$2Z^2@2$5^2@2$4+2+k0@2$0@2$2Z^1@2$5^1@2$4+2+k0").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition EH_IMG_WORDS : ltac2:(zQ "30!h9!s9!jk8@1$1@2$2$0$0") := ltac2:(zQ "50!h9!jk8!hn9!jkf!ih0@3$2@2$1$0$0@4$3$0$0+vokt8+tknuc@3$2@2$1$0$0@4$3$0$0+voku0+tkoi4@3$2@2$1$0$0@4$3$0$0+voku8+tkos0@3$2@2$1$0$0@4$3$0$0+volg8+tkpu4@3$2@2$1$0$0@4$3$0$0+volh0+tkqsc@3$2@2$1$0$0@4$3$0$0+volh8+tkqv4@3$2@2$1$0$0@4$3$0$0+volj0+tkrq0@3$2@2$1$0$0@4$3$0$0+vomg0+vppq8@3$2@2$1$0$0@4$3$0$0+vomh8Z@3$2@2$1$0$0@4$3$0$0+voml8+vomg0@3$2@2$1$0$0@4$3$0$0+vomn0+pitqc@3$2@2$1$0$0@4$3$0$0+vomr8+vluq8@3$2@2$1$0$0@4$3$0$0+voms8+vppg0@3$2@2$1$0$0@4$3$0$0+vomt0+vpov8@3$2@2$1$0$0@4$3$0$0+vomt8+hgpso8@3$2@2$1$0$0@4$3$0$0+vonn0+hirmv8@3$2@2$1$0$0@4$3$0$0+vpnv0+pkuq8@3$2@2$1$0$0@4$3$0$0+vpov8+nnsq8@3$2@2$1$0$0@4$3$0$0+vppg0+nntr4@1$4@2$1$0$0").                                  (* [comment removed for export] *)
Definition eh_img : ltac2:(zQ "10!hn2>1m$0P") := ltac2:(zQ "h40!h9!jp2!hn9!ih0!jt5!ig7!jk8!j0!t6!ju1!in9!v9!ju7!jud!iu4!jv3!jvc!kgb!kh1!hn2\1m$h3@2$7@3$f@2$6$0$0\2av@2$6$0$0@4$4$5^2@3$c$0$0^1@3$2$1@1$9@1$a@3$d$0$0^1@1$3$1$h0@2$7@4$4$5^1+hirum8@3$2$1@1$h1@1$aZ@1$3$1@2$e@1$b@1$8#k0\3can@1$b@1$8#k0@4$4$5^2$h2@3$2$1@1$9^1@1$3$1").              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition eh_STACK : Z := 24576.   (* [comment removed for export] *)

End EHDEFS.
(* [comment removed for export] *)
