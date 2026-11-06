(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec StepTac StoreOk SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04prod37Corelib7Numbers7BinNumshe1Z04list03nat04pair04cons03nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~l76kentryl74ELitl75KWordl72SA37Corelib5Lists7ListDefr33map89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U9LibDiagKn4FPX1~~~~~~t07cell_knhe4Npos35stdpp9bitvectorbdefinitionshi42bv06optionhi47Z_to_bv04Some37Corelib4Init5Logichm02eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshnah0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hs63rdn69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~ig8floaded_segmentsr36Forallt07cell_ok04bool46Stdlib6ZArith6BinInt1Zima3leb04andbima6of_natima3addima3pow04truel73env79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~ir39kentry_okt09cell_wf_bir37know_okt08cells_okt08kn_cells36Stdlib5Lists4Listjj27forallbt0adiag_cells03apphm03andima2leima2ltt0bcells_agreet06CANARYl74EVarl72evt09canary_ok" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition diag_cells : ltac2:(zQ "40!h8!j7!jb!k1@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!j7!h8!k1!k6!kc!l2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vkmr8N8+kmvl4@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vrrg8N8+vsuu8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vrrk8N8+ttqo0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vrrl0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vrrm0N8+vrrg8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vrsn8N8+hiusj8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vrsq8N8+vkms0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vrsr0N8+vkmr8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsst0N8+vsst0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsuu8N4+5@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsuv0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsuv8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsvg8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsvh0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsvi0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsvj0N8+uiuu8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsvk0N8+hivju0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsvk8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsvm0N4+2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsvn0N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsvn4N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsvn8N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsvt0N8+vsuu8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsvu0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsvu8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vtgg0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vtgh0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vtgm4N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vtgs0N8+vsvt8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vthj8N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hiuskcN4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hiusl8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hiuum8N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hiuuobN1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hivjs0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hivjt0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hiusk8N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hiusl0N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hiusm0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hgthk0N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hgthk4N1Z@1$5@2$1@2$1$0$2$0").

(* [comment removed for export] *)
Definition pf1_cells : ltac2:(zQ "40!h8!j7!jb!k1@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!j7!h8!k1!k6!kc!l2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vrsn8N8+hiusj8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsvt8N4+5@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vsvv8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vtgg0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vtgh0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vtgi0N8+ujor0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vtgj0N8+hivju8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vtgj8N8+kg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vtgl0N4+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vtgm0N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vtgm4N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vtgm8N4+a@1$5@2$1@2$1$0$2$0").

Definition cell_kn : ltac2:(zQ "40!h8!j7!k1!p6>1c@2$0@2$0$1$2$1$3") := ltac2:(zQ "70!h8!j7!k1!pf!p6!q6!qe\1c@2$0@2$0$1$2$1M0\1c@2$0@2$0$1$2$1$4^1\1p@2$0$1$2\1v$1M0\1p@2$0$1$2$4^2\1a$1\1w$2@3$5@2$6@1$3Z^2^1@1$3^3").
Definition kn_cells : ltac2:(zQ "50!jb!h8!j7!k1!p6>2cs@1$0@2$1@2$1$2$3$2@1$0$4") := ltac2:(zQ "70!h8!j7!k1!jb!sa!p6!hh3\2cs@1$3@2$0@2$0$1$2$1@4$4@2$0@2$0$1$2$1$5$6^1").

Definition cell_ok : ltac2:(zQ "60!h8!hhd!j7!hk1!k1!hk7>3mem>0@1$3@1$1#k0@1$5@1$3@1$1#8>1c@2$0@2$0$2$4$2P") := ltac2:(zQ "d0!h8!j7!hhd!k1!hk1!jb!hk7!hkf!hla!hn4!hr1!ig1!ije\3mem>0@1$4@1$2#k0@1$6@1$4@1$2#8\1c@2$0@2$0$1$3$1M0\1c@2$0@2$0$1$3$1P^1\1p@2$0$1$3\1v$1M0\1p@2$0$1$3P^2\1a$1\1w$3@3$9@1$6@1$5@1$4@1$2#8@4$b$c^6@2$7@1$2#k0^2^1@2$8@1$5@1$4@1$2#8@2$a^1@2$7@1$2#k0^3").
Definition cells_ok : ltac2:(zQ "70!h8!hhd!j7!hk1!jb!k1!hk7>3mem>0@1$3@1$1#k0@1$6@1$3@1$1#8>2cs@1$4@2$0@2$0$2$5$2P") := ltac2:(zQ "90!h8!j7!k1!hhd!hk1!jb!hk7!il1!ila\3mem>0@1$4@1$3#k0@1$6@1$4@1$3#8\2cs@1$5@2$0@2$0$1$2$1@3$7@2$0@2$0$1$2$1@1$8^2^1").

Definition cell_wf_b : ltac2:(zQ "40!h8!j7!im4!k1>1c@2$0@2$0$1$3$1$2") := ltac2:(zQ "90!h8!j7!k1!io2!io9!iof!im4!ip9!iq0\1c@2$0@2$0$1$2$1M0\1c@2$0@2$0$1$2$1$6^1\1p@2$0$1$2\1v$1M0\1p@2$0$1$2$6^2\1a$1\1w$2@2$4@2$4@2$4@2$3+1@1$5^1@2$3@1$5^1+8@2$3Z^2@2$3@2$7^2@1$5^1@2$8+2+k0").

Lemma cell_know : ltac2:(zQ "f0!h8!hhd!j7!hk1!im4!k1!hk7!iq7!hn4!iqd!iv8!hh3!ila!jg5!ije>1E$9>3mem>0@1$3@1$1#k0@1$6@1$3@1$1#8>1c@2$0@2$0$2$5$2>0@3$8$4@1$d^1$7>0@2$c^3^2@4$a$e^5^4@1$b^3").
Proof.
  intros E mem [[a w] v] Hwf Hc. unfold cell_wf_b in Hwf.
  repeat (apply andb_true_iff in Hwf; destruct Hwf as [Hwf ?]).
  apply Z.leb_le in Hwf. repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  unfold cell_kn. eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0) a w (ELit v) (Z_to_bv 64 v));
    [reflexivity | reflexivity | lia | lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia |].
  rewrite u_small by lia. rewrite Z.add_0_l. exact Hc.
Qed.

Lemma cells_know : ltac2:(zQ "h10!h8!j7!k1!hhd!hk1!im4!jb!hk7!iq7!hn4!iqd!jh1!jg5!jhc!ji7!ije!jk5>1E$a>3mem>0@1$4@1$3#k0@1$7@1$4@1$3#8>2cs@1$6@2$0@2$0$1$2$1>0@3$9$5@3$h0@2$0@2$0$1$2$1$c^1$8>0@2$d^3^2@4$b$f^5^4@1$e^3").
Proof.
  intros E mem cs. induction cs as [|c cs IH]; intros Hwf Hok.
  - constructor.
  - cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 H2].
    inversion Hok; subst. constructor; [apply cell_know; assumption | apply IH; assumption].
Qed.

Lemma diag_cells_wf : ltac2:(zQ "90!h8!j7!im4!k1!iq7!hn4!jg5!jl0!jk5@3$5$2@3$8@2$0@2$0$1$3$1$6$7$4").
Proof. vm_compute. reflexivity. Qed.

Corollary diag_cells_know : ltac2:(zQ "90!hhd!jl0!hk1!hk7!iqd!jh1!jhc!ji7!ije>1E$4>3mem>0@1$2@1$0#k0@1$3@1$2@1$0#8>0@2$6^1$1@4$5$8^3^2@1$7$1").
Proof. intros E mem H. apply cells_know; [apply diag_cells_wf | exact H]. Qed.

(* [comment removed for export] *)
Lemma know_ok_app : ltac2:(zQ "90!p6!jh1!ije!jb!hhd!hk1!jld!hk7!iqd>1E$8>3mem>0@1$5@1$4#k0@1$7@1$5@1$4#8>2k1@1$3$0>2k2@1$3$0>0@4$1$2^4^3^2>0@4$1$2^5^4^2@4$1$2^6^5@3$6$0^4^3").
Proof. intros E mem k1 k2 H1 H2. unfold know_ok. apply Forall_app. split; assumption. Qed.

(* [comment removed for export] *)
Definition cells_agree : ltac2:(zQ "71!hhd!hk1!hk7!h8!j7!jb!k1&>0@1$1@1$0#k0@1$2@1$1@1$0#8>3mem~0>4mem'~0>2cs@1$5@2$3@2$3$4$6$4P") := ltac2:(zQ "f1!j7!h8!k1!hhd!hk1!hk7!hkf!jb!jm2!hn4!il1!ip9!jm9!jmf!iof&>0@1$4@1$3#k0@1$5@1$4@1$3#8\3mem~0\4mem'~0\2cs@1$7@2$1@2$1$0$2$0@3$a@2$1@2$1$0$2$0\1c@2$1@2$1$0$2$0M1\1c@2$1@2$1$0$2$0P^1\1y@2$1$0$2\2y0$0M1\1y@2$1$0$2P^2\1a$0\1w$2>1i$0>0@2$8@2$c^3^1@2$d^1@2$b^3@1$e^2@3$9@1$5@1$4@1$3#8@1^9@2$6@1$3#k0^2@1^a@2$6@1$3#k0^2^1").

Lemma cell_ok_agree : ltac2:(zQ "h21!j7!k1!hhd!k6!hk1!hk7!h8!hn4!ila!hkf!im4!iq7!jm2!jg5!ip9!jm9!jmf!iof&>1x@1$4@1$2#k0@1$5@1$4@1$2#8>3mem~0>4mem'~0>1a$0>1w$1>1v$0>0@3$7$a@1$d@4$3@2$6$0$1$0@4$3$0$1^3^2^1$b>0>1i$0>0@2$c@2$f^5^1@2$h0^1@2$e^5@1$h1^4@3$7@1$5@1$4@1$2#8@1^7@2$9@1$2#k0^2@1^8@2$9@1$2#k0^2>0@2$8^7@4$3@2$6$0$1$0@4$3$0$1^5^4^3@2$8^7@4$3@2$6$0$1$0@4$3$0$1^6^5^4").
Proof.
  intros mem mem' a w v Hwf Hag Hc. unfold cell_ok in *. unfold cell_wf_b in Hwf.
  repeat (apply andb_true_iff in Hwf; destruct Hwf as [Hwf ?]).
  repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  rewrite (rdn_ext RSEGS w mem' mem (Z_to_bv 64 a)); [exact Hc | rewrite u_small by lia; lia |].
  intros x Hx. rewrite u_small in Hx by lia.
  rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hag. lia.
Qed.

Lemma cells_ok_agree : ltac2:(zQ "e1!h8!hhd!j7!hk1!k1!hk7!jhc!im4!jb!iq7!hn4!jg5!jn5!jk5&>0@1$3@1$1#k0@1$5@1$3@1$1#8>3mem~0>4mem'~0>2cs@1$8@2$0@2$0$2$4$2>0@3$a$7@3$d@2$0@2$0$2$4$2$b^1$9>0@3$c^4^3^2>0@2$6^5^3@2$6^5^4").
Proof.
  intros mem mem' cs. induction cs as [|[[a w] v] cs IH]; intros Hwf Hag Hok; [constructor|].
  cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 H2].
  inversion Hag; subst. inversion Hok; subst.
  constructor; [eapply cell_ok_agree; eassumption | apply IH; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CANARY : Z := 0x12ec38.
Definition canary_ok : ltac2:(zQ "40!hhd!hk1!hk7!j7>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>3can$3P") := ltac2:(zQ "h00!hhd!hk1!jb!hk7!jm2!hkf!hla!hn4!j7!hr1!ig1!jo3!ije!jm9!jmf!iq0\3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8\3can$8@2$4@3$7@1$3@1$2@1$1@1$0#8@4$a$c^2@2$5@1$0#k0$bN8@2$6@1$2@1$1@1$0#8@2$9N8@2$5@1$0#k0^1@2$4@2$dZ^1@2$e^1@2$f+2+k0").

Lemma canary_know : ltac2:(zQ "h10!hhd!hk1!k1!hk7!hn4!j7!pf!joc!q6!qe!iqd!jp3!iv8!jo3!jp8!ije!hkf>1E$a>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>1k$2>3can$5>0@3$4@1$1@1$0#k0@2$b^4^2@2$h0@1$0#k0^1>0@2$e^4^2@4$c$f^6^5@3$8@2$9@1$6Z$dN8@1$7^4").
Proof.
  intros E mem k can Hk [Hc Hr]. unfold CANARY in *.
  eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0) 0x12ec38 8%nat (EVar k) (Z_to_bv 64 can));
    [reflexivity | cbn [edenot]; exact Hk | lia | lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia |].
  rewrite u_small by lia. rewrite Z.add_0_l. exact Hc.
Qed.
End FPX1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
