(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec StepTac StoreOk SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04prod37Corelib7Numbers7BinNumshe1Z04list03nat04pair04cons03nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~l76kentryl74ELitl75KWordl72SA37Corelib5Lists7ListDefr33map79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9LibDiagKn4FPX1~~~~~~t07cell_knhe4Npos35stdpp9bitvectorbdefinitionshi22bv06optionhi27Z_to_bv04Some37Corelib4Init5Logichle2eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshn8h0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hs43rdn69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~ig6floaded_segmentsr36Forallt07cell_ok04bool46Stdlib6ZArith6BinInt1Zim83leb04andbim86of_natim83addim83pow04truet09cell_wf_bl73env79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~ird9kentry_okt08cells_okt08kn_cellsird7know_ok36Stdlib5Lists4Listjj07forallbt0adiag_cells03apphle3andim82leim82ltt0bcells_agreet06CANARYt09canary_okl74EVarl72ev" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition diag_cells : ltac2:(zQ "40!h8!j7!jb!k1@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!j7!h8!k1!k6!kc!l2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vhih0N8+knjk0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vomg0N8+vppq8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vomk0N8+tqlt8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vomk8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+voml8N8+vomg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vonn0N8+hirmv8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vonq0N8+vhih8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vonq8N8+vhih0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpns8N8+vpns8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vppq8N4+5@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vppr0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vppr8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpps8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vppt0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vppu0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vppv0N8+tvqk0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpqg0N8+hiruq0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpqg8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpqi0N4+2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpqj0N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpqj4N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpqj8N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpqp0N8+vppq8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpqq0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpqq8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpqs0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpqt0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpri4N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpro0N8+vpqp8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vprv8N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hirngcN4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hirnh8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hirpi8N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hirpkbN1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hiruo0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hirup0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hirng8N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hirnh0N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hirni0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hgpsg0N1Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hgpsg4N1Z@1$5@2$1@2$1$0$2$0").

(* [comment removed for export] *)
Definition pf1_cells : ltac2:(zQ "40!h8!j7!jb!k1@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!j7!h8!k1!k6!kc!l2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vonn0N8+hirmv8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpqp8N4+5@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpqr8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpqs0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpqt0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpqu0N8+ugkg8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpqv0N8+hiruq8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpqv8N8+kg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vprh0N4+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpri0N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpri4N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+vpri8N4+a@1$5@2$1@2$1$0$2$0").

Definition cell_kn : ltac2:(zQ "40!h8!j7!k1!p6>1c@2$0@2$0$1$2$1$3") := ltac2:(zQ "70!h8!j7!k1!pf!p6!q6!qe\1c@2$0@2$0$1$2$1M0\1c@2$0@2$0$1$2$1$4^1\1p@2$0$1$2\1v$1M0\1p@2$0$1$2$4^2\1a$1\1w$2@3$5@2$6@1$3Z^2^1@1$3^3").
Definition kn_cells : ltac2:(zQ "50!jb!h8!j7!k1!p6>2cs@1$0@2$1@2$1$2$3$2@1$0$4") := ltac2:(zQ "70!h8!j7!k1!jb!sa!hh1!p6\2cs@1$3@2$0@2$0$1$2$1@4$4@2$0@2$0$1$2$1$6$5^1").

Definition cell_ok : ltac2:(zQ "60!h8!hhb!j7!hjf!k1!hk5>3mem>0@1$3@1$1#k0@1$5@1$3@1$1#8>1c@2$0@2$0$2$4$2P") := ltac2:(zQ "d0!h8!j7!hhb!k1!hjf!jb!hk5!hkd!hl8!hn2!hqf!hvf!ijc\3mem>0@1$4@1$2#k0@1$6@1$4@1$2#8\1c@2$0@2$0$1$3$1M0\1c@2$0@2$0$1$3$1P^1\1p@2$0$1$3\1v$1M0\1p@2$0$1$3P^2\1a$1\1w$3@3$9@1$6@1$5@1$4@1$2#8@4$b$c^6@2$7@1$2#k0^2^1@2$8@1$5@1$4@1$2#8@2$a^1@2$7@1$2#k0^3").
Definition cells_ok : ltac2:(zQ "70!h8!hhb!j7!hjf!jb!k1!hk5>3mem>0@1$3@1$1#k0@1$6@1$3@1$1#8>2cs@1$4@2$0@2$0$2$5$2P") := ltac2:(zQ "90!h8!j7!k1!hhb!hjf!jb!hk5!ikf!il8\3mem>0@1$4@1$3#k0@1$6@1$4@1$3#8\2cs@1$5@2$0@2$0$1$2$1@3$7@2$0@2$0$1$2$1@1$8^2^1").

Definition cell_wf_b : ltac2:(zQ "40!h8!j7!im2!k1>1c@2$0@2$0$1$3$1$2") := ltac2:(zQ "90!h8!j7!k1!io0!io7!iod!im2!ip7!ipe\1c@2$0@2$0$1$2$1M0\1c@2$0@2$0$1$2$1$6^1\1p@2$0$1$2\1v$1M0\1p@2$0$1$2$6^2\1a$1\1w$2@2$4@2$4@2$4@2$3+1@1$5^1@2$3@1$5^1+8@2$3Z^2@2$3@2$7^2@1$5^1@2$8+2+k0").

Lemma cell_know : ltac2:(zQ "f0!h8!hhb!j7!hjf!im2!k1!hk5!iq5!hn2!hh1!il8!iqb!ir7!jg2!ijc>1E$c>3mem>0@1$3@1$1#k0@1$6@1$3@1$1#8>1c@2$0@2$0$2$5$2>0@3$8$4@1$b^1$7>0@2$a^3^2@4$d$e^5^4@1$9^3").
Proof.
  intros E mem [[a w] v] Hwf Hc. unfold cell_wf_b in Hwf.
  repeat (apply andb_true_iff in Hwf; destruct Hwf as [Hwf ?]).
  apply Z.leb_le in Hwf. repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  unfold cell_kn. eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0) a w (ELit v) (Z_to_bv 64 v));
    [reflexivity | reflexivity | lia | lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia |].
  rewrite u_small by lia. rewrite Z.add_0_l. exact Hc.
Qed.

Lemma cells_know : ltac2:(zQ "h10!h8!j7!k1!hhb!hjf!im2!jb!hk5!iq5!hn2!iqb!jgf!jha!ir7!ji5!ijc!jk3>1E$d>3mem>0@1$4@1$3#k0@1$7@1$4@1$3#8>2cs@1$6@2$0@2$0$1$2$1>0@3$9$5@3$h0@2$0@2$0$1$2$1$a^1$8>0@2$b^3^2@4$e$f^5^4@1$c^3").
Proof.
  intros E mem cs. induction cs as [|c cs IH]; intros Hwf Hok.
  - constructor.
  - cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 H2].
    inversion Hok; subst. constructor; [apply cell_know; assumption | apply IH; assumption].
Qed.

Lemma diag_cells_wf : ltac2:(zQ "90!h8!j7!im2!k1!iq5!hn2!iqb!jke!jk3@3$5$2@3$8@2$0@2$0$1$3$1$6$7$4").
Proof. vm_compute. reflexivity. Qed.

Corollary diag_cells_know : ltac2:(zQ "90!hhb!jke!hjf!hk5!jgf!jha!ir7!ji5!ijc>1E$6>3mem>0@1$2@1$0#k0@1$3@1$2@1$0#8>0@2$4^1$1@4$7$8^3^2@1$5$1").
Proof. intros E mem H. apply cells_know; [apply diag_cells_wf | exact H]. Qed.

(* [comment removed for export] *)
Lemma know_ok_app : ltac2:(zQ "90!p6!ji5!ijc!jb!hhb!hjf!jlb!hk5!ir7>1E$8>3mem>0@1$5@1$4#k0@1$7@1$5@1$4#8>2k1@1$3$0>2k2@1$3$0>0@4$1$2^4^3^2>0@4$1$2^5^4^2@4$1$2^6^5@3$6$0^4^3").
Proof. intros E mem k1 k2 H1 H2. unfold know_ok. apply Forall_app. split; assumption. Qed.

(* [comment removed for export] *)
Definition cells_agree : ltac2:(zQ "71!hhb!hjf!hk5!h8!j7!jb!k1&>0@1$1@1$0#k0@1$2@1$1@1$0#8>3mem~0>4mem'~0>2cs@1$5@2$3@2$3$4$6$4P") := ltac2:(zQ "f1!j7!h8!k1!hhb!hjf!hk5!hkd!jb!jm0!hn2!ikf!ip7!jm7!jmd!iod&>0@1$4@1$3#k0@1$5@1$4@1$3#8\3mem~0\4mem'~0\2cs@1$7@2$1@2$1$0$2$0@3$a@2$1@2$1$0$2$0\1c@2$1@2$1$0$2$0M1\1c@2$1@2$1$0$2$0P^1\1y@2$1$0$2\2y0$0M1\1y@2$1$0$2P^2\1a$0\1w$2>1i$0>0@2$8@2$c^3^1@2$d^1@2$b^3@1$e^2@3$9@1$5@1$4@1$3#8@1^9@2$6@1$3#k0^2@1^a@2$6@1$3#k0^2^1").

Lemma cell_ok_agree : ltac2:(zQ "h21!j7!k1!hhb!k6!hjf!hk5!h8!hn2!il8!hkd!im2!iq5!jm0!iqb!ip7!jm7!jmd!iod&>1x@1$4@1$2#k0@1$5@1$4@1$2#8>3mem~0>4mem'~0>1a$0>1w$1>1v$0>0@3$7$a@1$d@4$3@2$6$0$1$0@4$3$0$1^3^2^1$b>0>1i$0>0@2$c@2$f^5^1@2$h0^1@2$e^5@1$h1^4@3$7@1$5@1$4@1$2#8@1^7@2$9@1$2#k0^2@1^8@2$9@1$2#k0^2>0@2$8^7@4$3@2$6$0$1$0@4$3$0$1^5^4^3@2$8^7@4$3@2$6$0$1$0@4$3$0$1^6^5^4").
Proof.
  intros mem mem' a w v Hwf Hag Hc. unfold cell_ok in *. unfold cell_wf_b in Hwf.
  repeat (apply andb_true_iff in Hwf; destruct Hwf as [Hwf ?]).
  repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  rewrite (rdn_ext RSEGS w mem' mem (Z_to_bv 64 a)); [exact Hc | rewrite u_small by lia; lia |].
  intros x Hx. rewrite u_small in Hx by lia.
  rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hag. lia.
Qed.

Lemma cells_ok_agree : ltac2:(zQ "e1!h8!hhb!j7!hjf!k1!hk5!jgf!im2!jb!iq5!hn2!iqb!jn3!jk3&>0@1$3@1$1#k0@1$5@1$3@1$1#8>3mem~0>4mem'~0>2cs@1$8@2$0@2$0$2$4$2>0@3$a$7@3$d@2$0@2$0$2$4$2$b^1$9>0@3$c^4^3^2>0@2$6^5^3@2$6^5^4").
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
Definition CANARY : Z := 0x12b6f8.
Definition canary_ok : ltac2:(zQ "40!hhb!hjf!hk5!j7>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>3can$3P") := ltac2:(zQ "h00!hhb!hjf!jb!hk5!jm0!hkd!hl8!hn2!j7!hqf!jo1!hvf!ijc!jm7!jmd!ipe\3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8\3can$8@2$4@3$7@1$3@1$2@1$1@1$0#8@4$b$c^2@2$5@1$0#k0$aN8@2$6@1$2@1$1@1$0#8@2$9N8@2$5@1$0#k0^1@2$4@2$dZ^1@2$e^1@2$f+2+k0").

Lemma canary_know : ltac2:(zQ "h10!hhb!hjf!k1!hk5!hn2!j7!jo1!joa!pf!jp6!q6!qe!ir7!jpd!jg2!ijc!hkd>1E$c>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>1k$2>3can$5>0@3$4@1$1@1$0#k0@2$d^4^2@2$h0@1$0#k0^1>0@2$7^4^2@4$e$f^6^5@3$a@2$b@1$8Z$6N8@1$9^4").
Proof.
  intros E mem k can Hk [Hc Hr]. unfold CANARY in *.
  eapply (kword_intro RSEGS E mem (ELit 0) (Z_to_bv 64 0) 0x12b6f8 8%nat (EVar k) (Z_to_bv 64 can));
    [reflexivity | cbn [edenot]; exact Hk | lia | lia | rewrite u_small by lia; lia | rewrite u_small by lia; lia |].
  rewrite u_small by lia. rewrite Z.add_0_l. exact Hc.
Qed.
End FPX1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
