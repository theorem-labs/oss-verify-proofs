(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem Cells Exec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Export FP ZBridge.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Export CodeTab.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14listk16option01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~mc4cellmc8cells_at37Corelib4Init5Logicra3andmcacells_size79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~u15wr_at46Stdlib6ZArith6BinInt1Zhi36of_natk14Somera2eqk13nat3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshl7dov_read_bytesmc6cbytesmc7cell_atmc5csizeu12wa89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step8WithSegs~~~~~~hrf8rw_cellshi33addhrf8ro_cellsk14boolk14truemc8cb_splitmcbcb_split_ok37Corelib4Init3Natik93add37Corelib4Init5Peanoim22lehl78store_okhl7cwrite_to_memmc8cell_updmc7cell_wfhi32lek16lengthra2orhi33powu17mem_invhf7Z_to_bvhfbbv_unsigned3h5LinuxProcessSemanticsfLinuxProcessSem6BvBaseiuadZ_to_le_bytesu13le83h5LinuxProcessSemantics5Riscv3Semjj05low32u13le402N0u13le2hfabv_extractu13le1hl7dmachine_state3h5LinuxProcessSemantics5Riscv5Instrjof5instrk14prod3h5LinuxProcessSemantics5Riscv7Preludejs35bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~jv23evtk15falsek14pair3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypekk37Segmenthl79MachineOkhl7afetch_wordhl78is_ecallhl7emachine_result3h5LinuxProcessSemantics5Riscv7DecodeCkrcadecode_anyjj04Corejj04exec79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~lg02MSlg0binterp_eff0lg0blift_result" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : ltac2:(zQ "20!l9!kn8@1$0$1").

Definition ro_cells : ltac2:(zQ "60!h9!jc!l9!m0!m9!q8>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1A$4>2cs@1$2$5P") := ltac2:(zQ "70!h9!jc!l9!m0!m9!q8!qf\1m>0@1$1@1$0#k0@1$3@1$1@1$0#8\1A$4\2cs@1$2$5@4$6?4segs^3^2^1").
Definition rw_cells : ltac2:(zQ "60!h9!jc!l9!m0!m9!q8>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1A$4>2cs@1$2$5P") := ltac2:(zQ "b0!h9!jc!l9!m0!se!m9!q8!qf!t4!hhb!hjb\1m>0@1$1@1$0#k0@1$3@1$1@1$0#8\1A$5\2cs@1$2$6@2$4@4$7?4segs^3^2^1@4$9?4segs^3^2@1$a@1$8^1").

Lemma rw_cells_read : ltac2:(zQ "h10!h9!q8!jc!l9!m0!hk5!hkc!hl1!m9!hoe!hpf!hq8!hr2!hra!ig3!igf!hjb>1m>0@1$2@1$0#k0@1$4@1$2@1$0#8>1A$8>2cs@1$3$1>1k$7>1c$1>0@3$e^5^4^3>0@3$6@1$4$1@2$b^4^3@2$5$1^2@3$6@1$4@1$3@1$2@1$0#8@4$9?4segs^7@1$d@2$f^6@1$h0^4@1$c^3@2$5@1$3@1$2@1$0#8@1$a^3").
Proof. intros m A cs k c [H _]. apply cells_at_read. exact H. Qed.

Lemma ro_cells_read : ltac2:(zQ "h10!h9!q8!jc!l9!m0!hk5!hkc!hl1!m9!hoe!hpf!hq8!hr2!hra!ih6!igf!hjb>1m>0@1$2@1$0#k0@1$4@1$2@1$0#8>1A$8>2cs@1$3$1>1k$7>1c$1>0@3$e^5^4^3>0@3$6@1$4$1@2$b^4^3@2$5$1^2@3$6@1$4@1$3@1$2@1$0#8@4$9?4segs^7@1$d@2$f^6@1$h0^4@1$c^3@2$5@1$3@1$2@1$0#8@1$a^3").
Proof. intros m A cs k c H. apply cells_at_read. exact H. Qed.

Lemma rw_cells_read_at : ltac2:(zQ "h10!h9!jc!hkc!q8!l9!hl1!m0!hk5!m9!hoe!hpf!hq8!hr2!hra!ig3!igf!hjb>1m>0@1$1@1$0#k0@1$6@1$1@1$0#8>1A$8>2cs@1$4$3>1k$5>1c$3>1n$5>1a@1$1@1$0#k0>0@3$e^7^6^5>0@3$2@1$6$3@2$b^6^5@2$7$3^4>0@3$2$5^4@1$c^5>0@3$2@1$1@1$0#k0^4@1$d@2$f^9@1$h0^7@3$2@1$6@1$4@1$1@1$0#8@4$9?4segs^b^5^6@2$7@1$4@1$1@1$0#8@1$a^7").
Proof. intros; subst; eapply rw_cells_read; eauto. Qed.

Lemma ro_cells_read_at : ltac2:(zQ "h10!h9!jc!hkc!q8!l9!hl1!m0!hk5!m9!hoe!hpf!hq8!hr2!hra!ih6!igf!hjb>1m>0@1$1@1$0#k0@1$6@1$1@1$0#8>1A$8>2cs@1$4$3>1k$5>1c$3>1n$5>1a@1$1@1$0#k0>0@3$e^7^6^5>0@3$2@1$6$3@2$b^6^5@2$7$3^4>0@3$2$5^4@1$c^5>0@3$2@1$1@1$0#k0^4@1$d@2$f^9@1$h0^7@3$2@1$6@1$4@1$1@1$0#8@4$9?4segs^b^5^6@2$7@1$4@1$1@1$0#8@1$a^7").
Proof. intros; subst; eapply ro_cells_read; eauto. Qed.

Lemma rw_cells_cb_split : ltac2:(zQ "d0!l9!q8!hl1!hkc!h9!ig3!jc!ii2!m0!ii9!m9!ij0!ijb>1m>0@1$6@1$4#k0@1$8@1$6@1$4#8>1A$a>2cs@1$0$1>3cs2@1$0$1>1k$2>1n$2>0@3$5^6^5^4>0@3$3$7@3$c^5^3^2$9>0@3$3@1$0$1^5@3$b^6^4^3@3$5^9^8^6").
Proof.
  intros m A cs cs2 k n [Hc Hw] Hok ->. split.
  - apply cells_at_cb_split; assumption.
  - rewrite cells_size_cb_split; [exact Hw| exact (cells_at_wf _ _ _ _ Hc) | exact Hok].
Qed.

Lemma ro_cells_cb_split : ltac2:(zQ "d0!l9!q8!hl1!hkc!h9!ih6!jc!ii2!m0!ii9!m9!ij0!ijb>1m>0@1$6@1$4#k0@1$8@1$6@1$4#8>1A$a>2cs@1$0$1>3cs2@1$0$1>1k$2>1n$2>0@3$5^6^5^4>0@3$3$7@3$c^5^3^2$9>0@3$3@1$0$1^5@3$b^6^4^3@3$5^9^8^6").
Proof. intros m A cs cs2 k n Hc Hok ->. apply cells_at_cb_split; assumption. Qed.

Lemma cell_at_bound : ltac2:(zQ "b0!q8!hk5!l9!hl1!m0!hkc!ilb!in6!hq8!t4!hr2>2cs@1$2$0>1k$3>1c$0>0@3$5@1$4$0@2$8^3^2@2$1$0^1@2$7@2$6^3@1$a^2@1$9^4").
Proof.
  intros cs k c H. destruct (cell_at_split cs k c c H) as (pre & post & -> & Hsz & _).
  rewrite cells_size_app. cbn. lia.
Qed.

Lemma rw_cells_store_ok : ltac2:(zQ "h20!q8!hl1!hkc!m0!h9!jc!hk5!ii2!l9!ii9!m9!inc!hq8!hr2!hra!ig3!igf!hjb>1m>0@1$5@1$4#k0@1$3@1$5@1$4#8>1A$a>2cs@1$8$0>1k$1>1c$0>1j$1>0@3$f^6^5^4>0@3$2@1$3$0@2$c^5^4@2$6$0^3>0@3$2$1^3@1$d^4@3$2$7@4$b?4segs^9@1$e@2$h0^8@1$h1^6^4$9").
Proof.
  intros m A cs k c j [Hc Hw] Hk ->. pose proof (cell_at_bound _ _ _ Hk).
  apply (wr_at_store_ok segs m A (Z.of_nat (cells_size cs))); [exact Hw| lia | lia].
Qed.

Lemma rw_cells_store_ok_at : ltac2:(zQ "h20!hkc!h9!q8!jc!hl1!m0!hk5!ii2!l9!ii9!m9!inc!hq8!hr2!hra!ig3!igf!hjb>1m>0@1$3@1$1#k0@1$5@1$3@1$1#8>1A$a>2cs@1$8$2>1k$4>1c$2>1j$4>1a@1$3@1$1#k0>0@3$f^7^6^5>0@3$0@1$5$2@2$c^6^5@2$6$2^4>0@3$0$4^4@1$d^5>0@3$0@1$3@1$1#k0^4@1$e@2$h0^9@1$h1^7@3$0$7@4$b?4segs^b^5^6$9").
Proof. intros; subst. eapply rw_cells_store_ok; eauto. Qed.

Lemma rw_cells_write : ltac2:(zQ "h30!q8!hl1!m0!hkc!h9!hr2!ig3!jc!hk5!l9!m9!io8!hpf!hq8!ip8!iq3!hra!igf!hjb>1m>0@1$7@1$4#k0@1$2@1$7@1$4#8>1A$a>2cs@1$9$0>1k$1>1c$0>2c'$0>0@3$6^6^5^4>0@3$3@1$2$0@2$d^5^4@2$8$0^3>0@3$3$1@1$5^3@1$5^4>0@1$f^4@3$6@3$b^a@1$h0@2$h1^9@1$h2^7@1$c^5^9@3$e^8^7^5").
Proof.
  intros m A cs k c c' [Hc Hw] Hk Hsz Hwf. split.
  - eapply cells_at_write; eauto.
  - destruct (cell_at_split cs k c c' Hk) as (pre & post & -> & Hszp & ->).
    rewrite cells_size_app in *. cbn [cells_size] in *. rewrite Hsz. apply wr_at_write. exact Hw.
Qed.

Lemma rw_cells_frame : ltac2:(zQ "h00!h9!jc!iqd!igf!hjb!ir3!l9!m9!ig3!m0!irc!io8!q8!t4!hra!is1>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1A$7>2cs@1$6$c>1a$7>2bs@1$6@1$1@1$0#8>0@3$8^5^4^3>0@2$2Z^3>0@2$2@2$3^4@1$4@2$5@1$1@1$0#8^3@2$f+2+k0>0@2$a@2$2@2$3^7@1$4@1$d^6^5@2$2@2$3^5@1$4@2$5@1$1@1$0#8^4^7@3$8@3$b^9@1$e^6^5^8^7").
Proof.
  intros m A cs a bs [Hc Hw] Ha Hl Hd. split.
  - apply cells_at_frame; assumption.
  - apply wr_at_write. exact Hw.
Qed.

Lemma ro_cells_frame : ltac2:(zQ "h00!h9!jc!iqd!igf!hjb!ir3!l9!m9!ih6!m0!irc!io8!q8!t4!hra!is1>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1A$7>2cs@1$6$c>1a$7>2bs@1$6@1$1@1$0#8>0@3$8^5^4^3>0@2$2Z^3>0@2$2@2$3^4@1$4@2$5@1$1@1$0#8^3@2$f+2+k0>0@2$a@2$2@2$3^7@1$4@1$d^6^5@2$2@2$3^5@1$4@2$5@1$1@1$0#8^4^7@3$8@3$b^9@1$e^6^5^8^7").
Proof. intros. apply cells_at_frame; assumption. Qed.

Lemma rw_cells_bound : ltac2:(zQ "d0!h9!iqd!jc!l9!m0!se!m9!q8!t4!ig3!igf!hjb!is1>1m>0@1$2@1$0#k0@1$4@1$2@1$0#8>1A$6>2cs@1$3$7>0@3$9^3^2^1@2$5@2$1Z^3@2$1@2$a^3@1$b@1$8^2@2$c+2+k0").
Proof. intros m A cs [H _]. eapply cells_at_bound; eauto. Qed.

(* [comment removed for export] *)
Lemma mem_inv_store_cbytes : ltac2:(zQ "d0!h9!jc!is8!ii2!m0!ii9!hkc!inc!io8!hpf!q8!iq3!hr2>1m>0@1$1@1$0#k0@1$4@1$1@1$0#8>1a@1$1@1$0#k0>2c'$a>0@2$2?4segs^3>0@1$b^2>0@3$6$3@4$7?4segs^5^4@1$c^3$5@2$2?4segs@3$8^6^5@1$9^4").
Proof.
  intros m a c' Hinv Hwf Hok. apply mem_inv_store; [assumption|].
  rewrite cbytes_length by assumption. exact Hok.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma unsigned_Z_to_bv_add : ltac2:(zQ "70!h9!it2!m9!igf!hkc!jc!itc>1e$2>1d$2@3$4@1$5@1$0#k0@2$1@1$0#k0@2$3@2$6@1$0#k0@2$1@1$0#k0^2^1@2$1@1$0#k0@2$3^2^1").
Proof.
  intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma unsigned_Z_to_bv_add_r : ltac2:(zQ "70!h9!it2!m9!igf!hkc!jc!itc>1e$2>1d$2@3$4@1$5@1$0#k0@2$1@1$0#k0@2$3^1@2$6@1$0#k0@2$1@1$0#k0^2@2$1@1$0#k0@2$3^1^2").
Proof.
  intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma Z_to_bv_lit_self : ltac2:(zQ "50!h9!jc!hkc!it2!itc>1x@1$1@1$0#k0@3$2@1$1@1$0#k0@2$3@1$0#k0@2$4@1$0#k0^1^1").
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma wa_of_Z_to_bv : ltac2:(zQ "60!m9!hkc!h9!hra!it2!jc>1E$0>1e$0>0@3$1$0^2^1@3$1@1$5@1$2#k0@1$3^2@2$4@1$2#k0^3").
Proof. intros; subst; reflexivity. Qed.
Lemma wa_of_var : ltac2:(zQ "60!h9!hkc!m9!jc!hra!itc>1x@1$3@1$0#k0>1e$2>0@3$1$2@2$5@1$0#k0^2^1@3$1@1$3@1$0#k0@1$4^2^3").
Proof. intros; subst. unfold wa. apply Z_to_bv_lit_self. Qed.

Lemma store_bytes_8' : ltac2:(zQ "70!h9!jc!l9!hkc!jh9!jia!itc>1v@1$1@1$0#k0@3$3@1$2@1$1@1$0#8@2$4N8@2$6@1$0#k0^1@1$5^1").
Proof. exact store_bytes_8. Qed.
Lemma store_bytes_4' : ltac2:(zQ "80!h9!jc!l9!hkc!jh9!jl2!jlb!itc>1v@1$1@1$0#k0@3$3@1$2@1$1@1$0#8@2$4N4@2$7@1$0#i0@1$5^1@1$6^1").
Proof. exact store_bytes_4. Qed.
Lemma store_bytes_2' : ltac2:(zQ "90!h9!jc!l9!hkc!jm1!jh9!jm5!jmb!itc>1v@1$1@1$0#k0@3$3@1$2@1$1@1$0#8@2$5N2@2$8@1$0#h0@4$7@1$0#k0$4@1$0#h0^1@1$6^1").
Proof. exact store_bytes_2. Qed.
Lemma store_bytes_1' : ltac2:(zQ "90!h9!jc!l9!hkc!jm1!jh9!jn8!jmb!itc>1v@1$1@1$0#k0@3$3@1$2@1$1@1$0#8@2$5N1@2$8@1$0#8@4$7@1$0#k0$4@1$0#8^1@1$6^1").
Proof. exact store_bytes_1. Qed.

(* [comment removed for export] *)
Lemma evt_step_gen : ltac2:(zQ "hb1!h9!jc!m0!hkc!m9!jne!jr3!hk5!jrc!ju9!kid!ii2!kj4!l9!kjc!kn8!ko3!kp0!kpe!kqa!ku2!kv0!kv8!ljd!lk3!ll2!it2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$d$f>1Q>0$5P>1R@2$9@1$0#5@1$1@1$0#k0>1F@2$9@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>2fc@1$1@1$0#i0>2rv@1$2@1$1@1$0#k0>1m~0>2ro~0>1w@1$1@1$0#i0>1i$6>2sz$4>3ms1$5>0@3$3@1$2@1$1@1$0#i0@2$h1^d^9@2$7@1$1@1$0#i0^4>0@3$3$b@1$h2^5$c>0@3$3@1$2@2$8$6$4@1$h4^6@2$7@2$8$6$4@4$e$6$4^5^4>0@3$3@1$h3$5@2$h9^8@3$h8^h0@3$h6@2$ha@1$0#k0^5^6@5$h5^e^d^c^b^a^9@2$h0$5^4>0@3$a^h1^h0^5@3$a^h2^h1@7$h7^h0^f^e^d^c^b^a").
Proof.
  intros segs Q R F pc fc rv m ro w i sz ms1 Hf He Hd Hx Hq. eapply evt_step; [|exact Hq].
  split; [reflexivity|]. rewrite (step_gen segs R F pc fc rv m ro w i sz Hf He Hd). exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac slia := first [ exact I | lia | split; [lia|exact I] ].

Ltac is_Zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.

(* [comment removed for export] *)
Ltac set_concl g' := change_no_check g'.
Ltac cbv_concl_beta_iota :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv beta iota in g in set_concl g'.
Ltac cbv_concl_iota :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv iota in g in set_concl g'.
Ltac cbv_concl_zeta :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv zeta in g in set_concl g'.

(* [comment removed for export] *)
Ltac fold_closed_in_goal :=
  repeat match goal with
  | |- context [bv_unsigned (@BV ?n ?z ?p)] => let v := eval vm_compute in (bv_unsigned (@BV n z p)) in change (bv_unsigned (@BV n z p)) with v
  | |- context [bv_signed (@BV ?n ?z ?p)] => let v := eval vm_compute in (bv_signed (@BV n z p)) in change (bv_signed (@BV n z p)) with v
  | |- context [bv_signed (bv_concat ?n ?a ?b)] => let v := eval vm_compute in (bv_signed (bv_concat n a b)) in is_Zlit v; change (bv_signed (bv_concat n a b)) with v
  | |- context [bv_unsigned (bv_concat ?n ?a ?b)] => let v := eval vm_compute in (bv_unsigned (bv_concat n a b)) in is_Zlit v; change (bv_unsigned (bv_concat n a b)) with v
  | |- context [bv_unsigned (Z_to_bv ?n ?z)] => is_Zlit z; let v := eval vm_compute in (bv_unsigned (Z_to_bv n z)) in
        change (bv_unsigned (Z_to_bv n z)) with v
  | |- context [bv_signed (Z_to_bv ?n ?z)] => is_Zlit z; let v := eval vm_compute in (bv_signed (Z_to_bv n z)) in
        change (bv_signed (Z_to_bv n z)) with v
  | |- context [Z.shiftl ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.shiftl a b) in change (Z.shiftl a b) with v
  | |- context [Z.shiftr ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.shiftr a b) in change (Z.shiftr a b) with v
  | |- context [Z.land ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.land a b) in change (Z.land a b) with v
  | |- context [Z.lor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with v
  | |- context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v
  | |- context [bv_swrap ?n ?z] => is_Zlit z; let v := eval vm_compute in (bv_swrap n z) in
        change (bv_swrap n z) with v
  | |- context [bv_wrap ?n ?z] => is_Zlit z; let v := eval vm_compute in (bv_wrap n z) in
        change (bv_wrap n z) with v
  | |- context [Z.add ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v
  | |- context [Z.sub ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.sub a b) in change (Z.sub a b) with v
  | |- context [Z.mul ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.mul a b) in change (Z.mul a b) with v
  | |- context [Z.add (Z.add ?x ?a) ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.add a b) in
        replace (Z.add (Z.add x a) b) with (Z.add x v) by (exact (Z.add_assoc x a b))
  | |- context [Z_to_bv 64 (Z.add ?x 0)] => rewrite (Z.add_0_r x)
  end.

(* [comment removed for export] *)
Ltac fold_lit_load :=
  repeat match goal with
  | |- context [bv_extract 0 ?n (le_bytes_to_word ?bs)] =>
      lazymatch bs with (_ :: _)%list => idtac end;
      let t := constr:(bv_extract 0 n (le_bytes_to_word bs)) in
      let z := eval vm_compute in (bv_unsigned t) in
      is_Zlit z;
      rewrite (bv_lit_eq n t z) by (vm_compute; reflexivity)
  | |- context [@sext ?k 64 (Z_to_bv ?k ?z)] =>
      is_Zlit z;
      let t := constr:(@sext k 64 (Z_to_bv k z)) in
      let z' := eval vm_compute in (bv_unsigned t) in
      rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
  | |- context [@zext ?k 64 (Z_to_bv ?k ?z)] =>
      is_Zlit z;
      let t := constr:(@zext k 64 (Z_to_bv k z)) in
      let z' := eval vm_compute in (bv_unsigned t) in
      rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
  | |- context [low32 (Z_to_bv 64 ?z)] =>
      is_Zlit z;
      let t := constr:(low32 (Z_to_bv 64 z)) in
      let z' := eval vm_compute in (bv_unsigned t) in
      rewrite (bv_lit_eq 32 t z') by (vm_compute; reflexivity)
  | |- context [nan_box (Z_to_bv 32 ?z)] =>
      is_Zlit z;
      let t := constr:(nan_box (Z_to_bv 32 z)) in
      let z' := eval vm_compute in (bv_unsigned t) in
      rewrite (bv_lit_eq 64 t z') by (vm_compute; reflexivity)
  end.

(* [comment removed for export] *)
Ltac simp_is_x0 :=
  repeat match goal with
  | |- context [is_x0 ?r] => let v := eval vm_compute in (is_x0 r) in change (is_x0 r) with v
  end; cbv_concl_beta_iota.

(* [comment removed for export] *)
Ltac is_concrete_map R := lazymatch R with TNode _ _ _ => idtac | TEmpty => idtac end.
Ltac map_cbv_get :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv beta iota delta [tget] in g in set_concl g'.
Ltac map_cbv_set :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv beta iota delta [tset] in g in set_concl g'.

Ltac norm_fchain :=
  repeat match goal with
  | |- context [@bvmap_set 5 word ?k ?x (@bvmap_set 5 word ?k' ?y ?R)] =>
      let a := eval vm_compute in (bv_unsigned k) in
      let b := eval vm_compute in (bv_unsigned k') in
      let c := eval vm_compute in (Z.compare a b) in
      lazymatch c with
      | Eq => rewrite (bvmap_set_set_same' k k' x y R) by reflexivity
      | Gt => rewrite (bvmap_set_set_comm k k' x y R) by reflexivity
      end
  end.

Ltac simp_regs :=
  repeat match goal with
  | |- context [reg_get ?R ?r] =>
      is_concrete_map R;
      let p := eval vm_compute in (bv_key r) in
      change (reg_get R r) with (match tget p R with Some v => v | None => w0 end);
      map_cbv_get
  | |- context [@bvmap_set 5 word ?r ?v ?R] =>
      is_concrete_map R;
      let p := eval vm_compute in (bv_key r) in
      change (@bvmap_set 5 word r v R) with (@tset Wrd64 p v R);   (* [comment removed for export] *)
      map_cbv_set
  | |- context [reg_get (@bvmap_set 5 word ?k ?v ?R) ?r] =>
      first [ rewrite (freg_get_same R k r v) by reflexivity
            | rewrite (freg_get_other R k r v) by reflexivity ]
  end;
  norm_fchain.

Ltac exec_cbv :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval cbv beta iota zeta delta [lift_result interp_eff0 exec with_pc with_regs with_fregs with_fcsr with_resv
     rget rset fget fset c_regs c_fregs c_pc c_fcsr c_resv MS_of_core load_val store_val branch_taken inval_resv
     width_bytes accrue fari_d fcmp_d fari_s fcmp_s] in g in
  set_concl g'.

(* [comment removed for export] *)
Ltac vnorm_rw_for i :=
  lazymatch i with
  | OpImm ALU_ADD _ _ _ => rewrite ?alu_addi
  | OpImm ALU_AND _ _ _ => rewrite ?alu_andi
  | OpImm ALU_OR _ _ _ => rewrite ?alu_ori
  | OpImm ALU_XOR _ _ _ => rewrite ?alu_xori
  | OpImm ALU_SLT _ _ _ => rewrite ?alu_slti
  | OpImm ALU_SLTU _ _ _ => rewrite ?alu_sltiu
  | ShiftImm ALU_SLL _ _ _ => rewrite ?alu_slli
  | ShiftImm ALU_SRL _ _ _ => rewrite ?alu_srli
  | ShiftImm ALU_SRA _ _ _ => rewrite ?alu_srai
  | Op ALU_ADD _ _ _ => rewrite ?alu_add
  | Op ALU_SUB _ _ _ => rewrite ?alu_sub
  | Op ALU_SLT _ _ _ => rewrite ?alu_slt
  | Op ALU_SLTU _ _ _ => rewrite ?alu_sltu
  | Op ALU_AND _ _ _ => rewrite ?alu_and
  | Op ALU_OR _ _ _ => rewrite ?alu_or
  | Op ALU_XOR _ _ _ => rewrite ?alu_xor
  | Op ALU_SLL _ _ _ => rewrite ?alu_sll
  | Op ALU_SRL _ _ _ => rewrite ?alu_srl
  | Op ALU_SRA _ _ _ => rewrite ?alu_sra
  | OpImm32 _ _ _ => rewrite ?w_addiw
  | ShiftImm32 ALU_SLL _ _ _ => rewrite ?w_slliw
  | ShiftImm32 ALU_SRL _ _ _ => rewrite ?w_srliw
  | ShiftImm32 ALU_SRA _ _ _ => rewrite ?w_sraiw
  | Op32 ALU_ADD _ _ _ => rewrite ?w_addw
  | Op32 ALU_SUB _ _ _ => rewrite ?w_subw
  | Op32 ALU_SLL _ _ _ => rewrite ?w_sllw
  | Op32 ALU_SRL _ _ _ => rewrite ?w_srlw
  | Op32 ALU_SRA _ _ _ => rewrite ?w_sraw
  | Mul M_MUL _ _ _ => rewrite ?m_mul
  | Mul M_MULH _ _ _ => rewrite ?m_mulh
  | Mul M_MULHSU _ _ _ => rewrite ?m_mulhsu
  | Mul M_MULHU _ _ _ => rewrite ?m_mulhu
  | Mul M_DIV _ _ _ => rewrite ?m_div
  | Mul M_REM _ _ _ => rewrite ?m_rem
  | Mul32 M_MUL _ _ _ => rewrite ?w_mulw
  | Mul32 M_DIV _ _ _ => rewrite ?w_divw
  | Mul32 M_REM _ _ _ => rewrite ?w_remw
  | Mul32 M_DIVU _ _ _ => rewrite ?w_divuw
  | Mul32 M_REMU _ _ _ => rewrite ?w_remuw
  | Lui _ _ => rewrite ?b_lui
  | Auipc _ _ => rewrite ?b_auipc
  | Load _ _ _ _ _ => rewrite ?b_addsext
  | Store _ _ _ _ => rewrite ?b_addsext
  | FLoad _ _ _ _ => rewrite ?b_addsext
  | FStore _ _ _ _ => rewrite ?b_addsext
  | Jalr _ _ _ => rewrite ?b_addsext
  | Jal _ _ => rewrite ?b_addsext
  | Branch _ _ _ _ => rewrite ?b_addsext
  (* [comment removed for export] *)
  | Fsgnj _ _ _ _ _ => rewrite ?sgnj_self, ?sgnjx_self, ?sgnjn_self
  | Fmv _ _ _ _ => rewrite ?fmv_x_w_val; fold_lit_load
  | Fari _ _ _ _ _ _ => idtac
  | Fcmp _ _ _ _ _ => idtac
  | Fcvt _ _ _ _ _ => idtac
  | Fsqrt _ _ _ _ => idtac
  | Fminmax _ _ _ _ _ => idtac
  | Fclass _ _ _ => idtac
  | Csr _ _ _ _ => idtac
  | CsrI _ _ _ _ => idtac
  | _ =>
  rewrite ?alu_addi, ?alu_andi, ?alu_ori, ?alu_xori, ?alu_slti, ?alu_sltiu,
          ?alu_add, ?alu_sub, ?alu_slt, ?alu_sltu, ?alu_and, ?alu_or, ?alu_xor,
          ?alu_slli, ?alu_srli, ?alu_srai, ?alu_sll, ?alu_srl, ?alu_sra,
          ?w_addiw, ?w_slliw, ?w_srliw, ?w_sraiw, ?w_addw, ?w_subw, ?w_sllw, ?w_srlw, ?w_sraw,
          ?m_mul, ?m_mulh, ?m_mulhsu, ?m_mulhu, ?m_div, ?m_rem, ?w_mulw, ?w_divw, ?w_remw, ?w_divuw, ?w_remuw,
          ?b_addsext, ?b_lui, ?b_auipc
  end.

(* [comment removed for export] *)
Ltac lit_add_lits :=
  repeat match goal with
  | |- context [@bv_add 64 (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] =>
      is_Zlit a; is_Zlit b;
      lazymatch eval vm_compute in (andb (andb (Z.leb 0 a) (Z.ltb a 18446744073709551616))
                                         (andb (Z.leb 0 b) (Z.ltb b 18446744073709551616))) with
      | true => let c := eval vm_compute in (a + b)%Z in change (@bv_add 64 (Z_to_bv 64 a) (Z_to_bv 64 b)) with (Z_to_bv 64 c)
      | false => rewrite (lit_add_lit a b)
      end
  end;
  (match goal with |- context [@bv_add 64 (Z_to_bv 64 _) (Z_to_bv 64 _)] => rewrite ?lit_add_lit | _ => idtac end).
(* [comment removed for export] *)
Ltac ret_pc_lits :=
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
       lazymatch eval vm_compute in (andb (Z.leb 0 n) (Z.ltb n 18446744073709551616)) with
       | true => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (apply bv_eq; vm_compute; reflexivity)
       | false => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
       end
  end.
Ltac unfold_vdefs :=
  let g := lazymatch goal with |- ?g => g end in
  let g' := eval unfold v_addi, v_add, v_sub, v_mul, v_andi, v_ori, v_xori, v_and, v_or, v_xor,
         v_slli, v_srli, v_srai, v_sll, v_srl, v_sra, v_lui, v_auipc,
         v_addiw, v_slliw, v_srliw, v_sraiw, v_addw, v_subw, v_sllw, v_srlw, v_sraw,
         v_mulh, v_mulhsu, v_mulhu, v_mulw, btgt in g in
  set_concl g'.
Ltac vnorm_tail :=
  lit_add_lits;
  (match goal with |- context [w0] => change w0 with (Z_to_bv 64 0) | _ => idtac end);
  (match goal with |- context [w1] => change w1 with (Z_to_bv 64 1) | _ => idtac end);
  unfold_vdefs;
  (match goal with |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite ?unsigned_Z_to_bv_add, ?unsigned_Z_to_bv_add_r | _ => idtac end);
  fold_closed_in_goal;
  (match goal with |- context [Z_to_bv 64 (bv_unsigned _)] => rewrite ?Z_to_bv_lit_self | _ => idtac end);
  (match goal with |- context [bv_and _ (bv_not _)] =>
     repeat match goal with |- context [@bv_and 64 ?x (@bv_not 64 (Z_to_bv 64 1))] => change (@bv_and 64 x (@bv_not 64 (Z_to_bv 64 1))) with (ret_pc x) end;
     rewrite ?ret_pc_fold
   | _ => idtac end);
  (* [comment removed for export] *)
  ret_pc_lits.

Ltac vnorm_for i := vnorm_rw_for i; vnorm_tail.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zlit a := lazymatch a with Z0 => a | Zpos _ => a | Zneg _ => a end.

Ltac addr_diff E A :=
  lazymatch E with
  | Z.add ?X ?c1 =>
      lazymatch A with
      | Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
      | X => zlit c1
      | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
      end
  | _ =>
      lazymatch A with
      | Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
      | E => constr:(0%Z)
      | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
      end
  end.

(* [comment removed for export] *)
Ltac addr_expr a :=
  lazymatch a with
  | Z_to_bv 64 ?E => E
  | wa ?E => E
  | _ => constr:(Z.add (bv_unsigned a) 0)
  end.
(* [comment removed for export] *)
Ltac is_natlit n := lazymatch n with O => idtac | S ?k => is_natlit k end.
Ltac zlit_of t :=
  lazymatch t with
  | Z0 => t | Zpos _ => t | Zneg _ => t
  | Z.of_nat ?n => let chk := match n with _ => is_natlit n end in eval cbv in t
  end.
Ltac is_zlit_term a := match a with _ => let v := zlit_of a in idtac end.

(* [comment removed for export] *)
Ltac sb_split a kX :=
  lazymatch a with
  | Z.add ?a1 ?k1 =>
      match constr:(tt) with
      | _ => let d1 := zlit_of k1 in
             lazymatch a1 with
             | Z.add ?a2 ?k2 =>
                 match constr:(tt) with
                 | _ => let d2 := zlit_of k2 in let d := eval vm_compute in (d2 + d1)%Z in
                        kX a2 d constr:(@eq_sym Z _ _ (Z.add_assoc a2 k2 k1))
                 | _ => kX a1 d1 constr:(@eq_refl Z a)
                 end
             | Z.sub ?a2 ?k2 =>
                 match constr:(tt) with
                 | _ => let d2 := zlit_of k2 in let d := eval vm_compute in (d1 - d2)%Z in
                        kX a2 d constr:(@eq_sym Z _ _ (Z.add_assoc a2 (- k2)%Z k1))
                 | _ => kX a1 d1 constr:(@eq_refl Z a)
                 end
             | _ => kX a1 d1 constr:(@eq_refl Z a)
             end
      | _ => kX a 0%Z constr:(@eq_sym Z _ _ (Z.add_0_r a))
      end
  | Z.sub ?a1 ?k1 =>
      match constr:(tt) with
      | _ => let d1 := zlit_of k1 in let d := eval vm_compute in (- d1)%Z in
             kX a1 d constr:(@eq_refl Z a)
      | _ => kX a 0%Z constr:(@eq_sym Z _ _ (Z.add_0_r a))
      end
  | _ => kX a 0%Z constr:(@eq_sym Z _ _ (Z.add_0_r a))
  end.

(* [comment removed for export] *)
Ltac zaddr_eq_fast :=
  lazymatch goal with
  | |- @eq Z ?E ?E' =>
      sb_split E ltac:(fun X d pf =>
        sb_split E' ltac:(fun X' d' pf' =>
          constr_eq X X'; constr_eq d d';
          exact (@eq_trans Z E (X + d)%Z E' pf (@eq_sym Z E' (X + d)%Z pf'))))
  end.

(* [comment removed for export] *)
Ltac addr_eq_tac :=
  symmetry;
  first [ apply wa_of_Z_to_bv; zaddr_eq_fast
        | apply wa_of_var; zaddr_eq_fast
        | apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ].

Ltac cells_cbv := cbv beta iota zeta delta [cell_at cell_upd csize cells_size Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add cbytes].

Ltac eval_cb_split cs kn n :=
  eval cbv beta iota zeta delta [cb_split cb_split_ok cb_pieces csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app] in (cb_split cs kn n).
Ltac eval_cb_split_ok cs kn n :=
  eval cbv beta iota zeta delta [cb_split cb_split_ok cb_pieces csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app] in (cb_split_ok cs kn n).

(* [comment removed for export] *)
Ltac name_junk_pieces := fail.
Ltac gen_junk_cursors H :=
  repeat match type of H with
  | context [@firstn ?T ?k ?bs] => is_var bs; let j := fresh "jb" in set (j := @firstn T k bs) in *; clearbody j
  | context [@skipn ?T ?k ?bs] => is_var bs; let j := fresh "jb" in set (j := @skipn T k bs) in *; clearbody j
  end.

(* [comment removed for export] *)
Ltac split_for_access H segs m A cs kn n :=
  let ok := eval_cb_split_ok cs kn n in
  lazymatch ok with
  | true =>
      let cs2 := eval_cb_split cs kn n in
      lazymatch cs2 with
      | cs => idtac
      | _ => first [ apply (rw_cells_cb_split segs m A cs cs2 kn n) in H
                   | apply (ro_cells_cb_split segs m A cs cs2 kn n) in H ];
             [ | cells_cbv; reflexivity | cbv beta iota zeta delta [cb_split cb_split_ok cb_pieces csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app]; reflexivity ];
             try (name_junk_pieces; gen_junk_cursors H)   (* [comment removed for export] *)
      end
  end.

Ltac eval_cell_at cs kn := eval cbv beta iota zeta delta [cell_at csize Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add] in (cell_at cs kn).



(* [comment removed for export] *)
Ltac load_post :=
  (let g := lazymatch goal with |- ?g => g end in
   let g' := eval cbv beta iota delta [cbytes] in g in set_concl g');
  rewrite ?load_u64, ?zext_extract_le4, ?sext_extract_le4, ?zext_extract_le2, ?sext_extract_le2,
          ?zext_extract_le1, ?sext_extract_le1, ?zext_extract_byte, ?sext_extract_byte;
  fold_lit_load.


(* [comment removed for export] *)
Ltac solve_load_base :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | (* [comment removed for export] *)
                replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.

(* [comment removed for export] *)

Ltac solve_load := solve_load_base.

Ltac solve_store :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv_concl_beta_iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                (* [comment removed for export] *)
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv_concl_beta_iota
    end
  end.

(* [comment removed for export] *)
Ltac cell_of_bytes bs :=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  end.

Ltac simpl_sizes :=
  rewrite ?app_length;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length; cbn [length].

Ltac transport_chunks segs m a bs :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.

Ltac mem_after_store :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    lazymatch goal with
    | H : rw_cells segs m A ?cs |- _ =>
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          (* [comment removed for export] *)
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; try clear m; try rename H' into H
        end
    end
  end.

Ltac mem_after_store_opt :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) => mem_after_store
  | _ => idtac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rm_proof rm c :=
  let z := eval vm_compute in (bv_unsigned rm) in
  lazymatch z with
  | 7%Z =>
      lazymatch c with
      | Core _ _ _ ?fc _ =>
          lazymatch goal with
          | FRM : frm0 fc |- _ => constr:(rmode_dyn rm c (@eq_refl Z 7%Z) FRM)
          | _ => fail 100 "FP instruction with dynamic rounding mode: need a hypothesis [frm0" fc "]"
          end
      end
  | _ =>
      let md := eval vm_compute in (match rmode_of_Z z with Some md => md | None => RNE end) in
      constr:(rmode_static rm c md (@eq_refl bool false) (@eq_refl (option rmode) (Some md)))
  end.

(* [comment removed for export] *)
Ltac exec_pre i :=
  lazymatch goal with
  | |- context [exec ?sz _ ?c] =>
    lazymatch i with
    | Fari ?op FMT_D ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_d sz op rd rs1 rs2 rm c _ H)
    | Fari ?op FMT_S ?rd ?rs1 ?rs2 ?rm => let H := rm_proof rm c in rewrite (exec_fari_s sz op rd rs1 rs2 rm c _ H)
    | Fsqrt FMT_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fsqrt_d sz rd rs1 rm c _ H)
    | Fcmp ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_d sz op rd rs1 rs2 c)
    | Fcmp ?op FMT_S ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_s sz op rd rs1 rs2 c)
    | Fminmax ?op FMT_D ?rd ?rs1 ?rs2 => rewrite (exec_fminmax_d sz op rd rs1 rs2 c); cbv_concl_zeta
    | Fcvt FC_W FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_w_d sz rd rs1 rm c _ H)
    | Fcvt FC_WU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_wu_d sz rd rs1 rm c _ H)
    | Fcvt FC_L FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_d sz rd rs1 rm c _ H)
    | Fcvt FC_LU FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_lu_d sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_w sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_wu sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_L ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_l sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_LU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_lu sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_W ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_w sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_WU ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_wu sz rd rs1 rm c _ H)
    | Fcvt FC_D FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_d_s sz rd rs1 rm c _ H)
    | Fcvt FC_S FC_D ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_s_d sz rd rs1 rm c _ H)
    | Csr ?op ?rd ?rs1 ?csr =>
        let sl := eval vm_compute in (csr_slice csr) in
        lazymatch sl with
        | Some (?lo, ?len) =>
            rewrite (exec_csr_rw sz op rd rs1 csr c lo len ltac:(vm_compute; reflexivity)); cbv_concl_zeta;
            simp_is_x0; try change (negb true) with false; try change (negb false) with true; cbv_concl_iota
        | None => fail 100 "CSR access to an unknown CSR:" csr
        end
    | CsrI ?op ?rd ?uimm ?csr =>
        let sl := eval vm_compute in (csr_slice csr) in
        lazymatch sl with
        | Some (?lo, ?len) =>
            rewrite (exec_csri_rw sz op rd uimm csr c lo len ltac:(vm_compute; reflexivity)); cbv_concl_zeta;
            let w := eval vm_compute in (negb (Z.eqb (bv_unsigned uimm) 0)) in
            try change (negb (Z.eqb (bv_unsigned uimm) 0)) with w; cbv_concl_iota
        | None => fail 100 "CSR access to an unknown CSR:" csr
        end
    | _ => idtac
    end
  end;
  (* [comment removed for export] *)
  try match goal with
  | FRM : frm0 ?f |- context [slice_get ?f' 5 3] => constr_eq f f'; rewrite (frm0_slice_get f FRM)
  end.

(* [comment removed for export] *)
Ltac prove_frm0 :=
  first [ assumption
        | apply frm0_accrue; prove_frm0
        | apply frm0_slice_set_fflags; prove_frm0 ].

Ltac norm_fcsr :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ ?fce _ _ _) =>
      tryif is_var fce then idtac else
      (let fcn := fresh "fc" in
       let E := fresh "Efc" in
       tryif (let H := fresh "FRM" in
              assert (H : frm0 fce) by prove_frm0;
              repeat match goal with
              | H' : frm0 ?f |- _ => lazymatch f with fce => fail | _ => clear H' end
              end;
              remember fce as fcn eqn:E; clear E;
              try rename H into FRM)
       then idtac
       else (remember fce as fcn eqn:E; clear E))
  | _ => idtac
  end.

Ltac post_step i :=
  lazymatch i with
  | Fari _ _ _ _ _ _ => norm_fcsr
  | Fcmp _ _ _ _ _ => norm_fcsr
  | Fcvt _ _ _ _ _ => norm_fcsr
  | Fsqrt _ _ _ _ => norm_fcsr
  | Fminmax _ _ _ _ _ => norm_fcsr
  | Fma _ _ _ _ _ _ _ => norm_fcsr
  | Csr _ _ _ _ => norm_fcsr
  | CsrI _ _ _ _ => norm_fcsr
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac step_core segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
    let ec := eval vm_compute in (is_ecall w) in
    lazymatch ec with
    | false =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        (* [comment removed for export] *)
        first
        [ ct_lookup segs pc ltac:(fun C i' sz' => constr_eq i i'; constr_eq sz sz';
            eapply (evt_step_ct segs C _ R F pc fc rv m ro i sz);
            [ exact_no_check (@eq_refl bool true) | exact_no_check (@eq_refl (option ct_entry) (@Some ct_entry (i, sz))) | | ])
        | eapply (evt_step_gen segs _ R F (Z_to_bv 64 pc) fc rv m ro w i sz);
          [ vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | | ] ];
        [ exec_pre i;
          exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i ]
      | None => fail "undecodable instruction at" pc
      end
    | true => fail "ecall at" pc
    end
  | None => fail "no instruction at" pc
  end.

Ltac step :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

(* [comment removed for export] *)
Ltac unfold_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb].
(* [comment removed for export] *)
Ltac fold_lit_ux :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv ?n ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_unsigned (Z_to_bv n z)) in
      replace (bv_unsigned (Z_to_bv n z)) with v by (vm_compute; reflexivity)
  | |- context [bv_signed (Z_to_bv ?n ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_signed (Z_to_bv n z)) in
      replace (bv_signed (Z_to_bv n z)) with v by (vm_compute; reflexivity)
  end.
Ltac solve_cond_base :=
  first [ reflexivity
        | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
        | apply Z.leb_le; lia | apply Z.leb_gt; lia
        | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia ].
Ltac solve_cond_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); solve_cond_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); solve_cond_rec
  | _ => solve_cond_base
  end.
Ltac solve_cond := unfold_cond; fold_lit_ux; solve_cond_rec.
Ltac if_true :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with true; [cbv_concl_iota| symmetry; solve_cond]
  end.
Ltac if_false :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      replace c with false; [cbv_concl_iota| symmetry; solve_cond]
  end.
(* [comment removed for export] *)
Ltac if_cases H :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      destruct c eqn:H; [ | ]
  end.

(* [comment removed for export] *)
Ltac fold_lit_ux_in H :=
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv ?n ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_unsigned (Z_to_bv n z)) in
      replace (bv_unsigned (Z_to_bv n z)) with v in H by (vm_compute; reflexivity)
  | context [bv_signed (Z_to_bv ?n ?z)] => is_Zlit z;
      let v := eval vm_compute in (bv_signed (Z_to_bv n z)) in
      replace (bv_signed (Z_to_bv n z)) with v in H by (vm_compute; reflexivity)
  end.
(* [comment removed for export] *)
Ltac zify_bool H :=
  lazymatch type of H with
  | negb _ = true => apply (proj1 (Bool.negb_true_iff _)) in H; zify_bool H
  | negb _ = false => apply (proj1 (Bool.negb_false_iff _)) in H; zify_bool H
  | Z.eqb (Z.b2z ?b) 0 = true => apply Z.eqb_eq in H; apply (proj1 (zb_b2z_zero b)) in H; zify_bool H
  | Z.eqb (Z.b2z ?b) 0 = false => apply Z.eqb_neq in H; apply (proj1 (zb_b2z_nonzero b)) in H; zify_bool H
  | Z.eqb _ _ = true => apply Z.eqb_eq in H
  | Z.eqb _ _ = false => apply Z.eqb_neq in H
  | Z.ltb _ _ = true => apply Z.ltb_lt in H
  | Z.ltb _ _ = false => apply Z.ltb_ge in H
  | Z.leb _ _ = true => apply Z.leb_le in H
  | Z.leb _ _ = false => apply Z.leb_gt in H
  | andb _ _ = true =>
      apply andb_true_iff in H;
      let H1 := fresh H in let H2 := fresh H in destruct H as [H1 H2]; zify_bool H1; zify_bool H2
  | orb _ _ = false =>
      apply orb_false_iff in H;
      let H1 := fresh H in let H2 := fresh H in destruct H as [H1 H2]; zify_bool H1; zify_bool H2
  | _ => idtac
  end.

Ltac zify_cond H :=
  rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H;
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; zsimp_in H;
  zify_bool H.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac zstep := step; zsimp.
(* [comment removed for export] *)
