(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import ShapeAlg.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe4Npos36Stdlib7Strings6Stringje6string35stdpp9bitvectorbdefinitionsle2bv36Stdlib7Strings5Asciio05ascii37Corelib5Lists7ListDefpe3mapo0cnat_of_asciijeh4list_ascii_of_string46Stdlib6ZArith6BinInt1Zu26of_natle7Z_to_bvhe1Z3h5LinuxProcessSemanticsfLinuxProcessSem5Statehh15eventhh17WriteEv3h5LinuxProcessSemanticsfLinuxProcessSem2Fshl32Fs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~ho44TSetho46t_emitho46t_exit69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~htb1Whtb9exit_code05false04trueo05Asciije6String03apphtb3s2bjebEmptyString04cons03nil03nat04boolpe3nthhtb5t_dielebbv_unsigned46Stdlib5Arith8PeanoNat3Natiof3ltbu26modulou26to_nat01S06length37Corelib4Init3Natise3addhtb9MAX_INPUThtbbmsg_overrunhtbbmsg_refusedhtb9msg_shorthtbazero_linesu23addu23lebu23mulhtb6t_bodyhtbemsg_read_errorhtbfmsg_cannot_openhtb9msg_usage36Stdlib5Lists4Listjnb2hd06optionho46t_alt2htbdlist_byte_eqbhl39fs_lookuphtb8dot_pathhtb8t_openedhtbct_opened_diriof3leb" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
Definition s2b : ltac2:(zQ "40!h8!j7!l5!nb>1s$2@1$0@1$3@1$1#8") := ltac2:(zQ "90!j7!p6!r5!rb!sa!l5!va!hg3!nb\1s$5@4$2$1@1$8@1$0#8\1a$1@2$7@1$0#8@1$6@1$3^1@1$4^1").

Definition W : ltac2:(zQ "50!h8!j7!hgd!hjf!nb>2ch$2>1s@1$0@1$4@1$1#8@1$0$3") := ltac2:(zQ "80!j7!nb!h8!r5!hgd!hk8!hjf!hg3\2ch$4\1s@1$2@1$1@1$0#8@4$3@1$1@1$0#8$6@1$5@2$7@1$0#k0^2^1").

Definition exit_code : ltac2:(zQ "30!j7!hgd!nb>1z$1@1$2@1$0#k0") := ltac2:(zQ "30!j7!hgd!hg3\1z$1@2$2@1$0#k0^1").

(* [comment removed for export] *)
Definition t_die : ltac2:(zQ "50!h8!j7!hne!hrf!nb>3msg@1$0@1$4@1$1#8>2fs$2$3") := ltac2:(zQ "80!h8!j7!hne!hs7!ht1!ih2!ih7!nb\3msg@1$0@1$7@1$1#8\2fs$2@2$3@2$5+2^2@2$4@1$6+2^1").

Definition msg_usage : ltac2:(zQ "30!h8!j7!nb>5argv0@1$0@1$2@1$1#8@1$0@1$2@1$1#8") := ltac2:(zQ "d0!ii4!iib!ij1!ij9!j7!nb!ik2!ik7!ike!ilc!h8!im2!hg3\5argv0@1$a@1$5@1$4#8@3$6@1$5@1$4#8@1$7@2$3@8$2$1$0$1$0$1$1$1$0@2$3@8$2$1$1$0$0$1$1$1$0@2$3@8$2$1$0$0$0$0$1$1$0@2$3@8$2$1$1$1$0$0$1$1$0@2$3@8$2$1$0$1$0$0$1$1$0@2$3@8$2$0$1$0$1$1$1$0$0@2$3@8$2$0$0$0$0$0$1$0$0$8@3$6@1$5@1$4#8^1@3$6@1$5@1$4#8@1$7@2$3@8$2$0$0$0$0$0$1$0$0@2$3@8$2$1$0$0$1$0$0$1$0@2$3@8$2$0$1$1$1$0$0$1$0@2$3@8$2$0$0$0$0$1$0$1$0@2$3@8$2$1$0$1$0$1$0$1$0@2$3@8$2$0$0$1$0$1$0$1$0$8@3$9@1$5@1$4#8@2$c@1$4#8+a@1$b@1$5@1$4#8").
Definition msg_cannot_open : ltac2:(zQ "30!h8!j7!nb>4path@1$0@1$2@1$1#8@1$0@1$2@1$1#8") := ltac2:(zQ "d0!ii4!iib!ij1!ij9!j7!nb!ik2!ilc!h8!im2!ik7!ike!hg3\4path@1$8@1$5@1$4#8@3$6@1$5@1$4#8@1$a@2$3@8$2$1$1$0$0$0$1$1$0@2$3@8$2$0$0$1$1$0$1$1$0@2$3@8$2$1$0$0$1$0$1$1$0@2$3@8$2$0$1$0$1$1$1$0$0@2$3@8$2$0$0$0$0$0$1$0$0@2$3@8$2$1$1$0$0$0$1$1$0@2$3@8$2$1$0$0$0$0$1$1$0@2$3@8$2$0$1$1$1$0$1$1$0@2$3@8$2$0$1$1$1$0$1$1$0@2$3@8$2$1$1$1$1$0$1$1$0@2$3@8$2$0$0$1$0$1$1$1$0@2$3@8$2$0$0$0$0$0$1$0$0@2$3@8$2$1$1$1$1$0$1$1$0@2$3@8$2$0$0$0$0$1$1$1$0@2$3@8$2$1$0$1$0$0$1$1$0@2$3@8$2$0$1$1$1$0$1$1$0@2$3@8$2$0$0$0$0$0$1$0$0$b@3$6@1$5@1$4#8^1@3$7@1$5@1$4#8@2$c@1$4#8+a@1$9@1$5@1$4#8").
Definition msg_read_error : ltac2:(zQ "30!h8!j7!nb>4path@1$0@1$2@1$1#8@1$0@1$2@1$1#8") := ltac2:(zQ "d0!ii4!iib!ij1!ij9!j7!nb!ik2!ilc!h8!im2!ik7!ike!hg3\4path@1$8@1$5@1$4#8@3$6@1$5@1$4#8@1$a@2$3@8$2$1$1$0$0$0$1$1$0@2$3@8$2$0$0$1$1$0$1$1$0@2$3@8$2$1$0$0$1$0$1$1$0@2$3@8$2$0$1$0$1$1$1$0$0@2$3@8$2$0$0$0$0$0$1$0$0@2$3@8$2$0$1$0$0$1$1$1$0@2$3@8$2$1$0$1$0$0$1$1$0@2$3@8$2$1$0$0$0$0$1$1$0@2$3@8$2$0$0$1$0$0$1$1$0@2$3@8$2$0$0$0$0$0$1$0$0@2$3@8$2$1$0$1$0$0$1$1$0@2$3@8$2$0$1$0$0$1$1$1$0@2$3@8$2$0$1$0$0$1$1$1$0@2$3@8$2$1$1$1$1$0$1$1$0@2$3@8$2$0$1$0$0$1$1$1$0@2$3@8$2$0$0$0$0$0$1$0$0@2$3@8$2$1$1$1$1$0$1$1$0@2$3@8$2$0$1$1$1$0$1$1$0@2$3@8$2$0$0$0$0$0$1$0$0$b@3$6@1$5@1$4#8^1@3$7@1$5@1$4#8@2$c@1$4#8+a@1$9@1$5@1$4#8").
Definition msg_refused : list byte :=
  s2b "cli: input >= 67108864 bytes, refused" ++ [Z_to_bv 8 10].
Definition msg_short : list byte :=
  s2b "cli: input shorter than header" ++ [Z_to_bv 8 10].
Definition msg_overrun : list byte :=
  s2b "cli: config_len overruns input" ++ [Z_to_bv 8 10].

(* [comment removed for export] *)
Fixpoint zero_lines (calls : nat) : list byte :=
  match calls with
  | O => []
  | S k => Z_to_bv 8 48 :: Z_to_bv 8 10 :: zero_lines k
  end.

Definition MAX_INPUT : Z := 67108864%Z.

(* [comment removed for export] *)
Definition t_body : ltac2:(zQ "50!h8!j7!hne!hrf!nb>4data@1$0@1$4@1$1#8>2fs$2$3") := ltac2:(zQ "hf0!j7!im7!imc!nb!hgd!in2!hrf!in8!hg3!io1!iqa!ir1!ira!is3!is6!h8!iu0!hne!hs7!ht1!iu7!ih2!ih7!iv4!jg3!jh2!jhf!jid!jj3!jj9!va\4data@1$f@1$3@1$0#8\2fs$h1=3len$1@2$e@1$3@1$0#8^2M2\0$2$6@2$hc$h4@1$he^1@2$7$h8^2M2\0$2$6@2$a^1N6@2$7$h9^2=2b0$4@2$9@1$0#8@4$5@1$3@1$0#8N0^3@2$8@1$0#8Z=2b1$4@2$9@1$0#8@4$5@1$3@1$0#8N1^4@2$8@1$0#8Z=2b2$4@2$9@1$0#8@4$5@1$3@1$0#8N2^5@2$8@1$0#8Z=3cfg$4@2$hb^3@2$hd+hg0^2=aconfig_len$1@1$c@2$b^1+ogg0M2\0$2$6@2$a^6@2$h0N6^1@2$7$h7^7=5calls$1M1\aconfig_len$1$1^1N1\1n$1@1$d@1$c@2$b^4+4@2$h2@2$h5+1@1$ha^1@2$h3@1$h6Z^8").

(* [comment removed for export] *)
Definition t_opened : ltac2:(zQ "50!h8!j7!hne!hrf!nb>4data@1$0@1$4@1$1#8>2fs$2$3") := ltac2:(zQ "50!h8!j7!hne!jjf!nb\4data@1$0@1$4@1$1#8\2fs$2@2$3^2^1").

(* [comment removed for export] *)
Definition t_opened_dir : ltac2:(zQ "50!h8!j7!hne!hrf!nb>4path@1$0@1$4@1$1#8>2fs$2$3") := ltac2:(zQ "60!h8!j7!hne!jk9!in8!nb\4path@1$0@1$5@1$1#8\2fs$2@2$4@1$3^2^1").

Definition dot_path : ltac2:(zQ "30!h8!j7!nb@1$0@1$2@1$1#8") := ltac2:(zQ "50!j7!nb!ilc!im2!hg3@3$2@1$1@1$0#8@2$4@1$0#8+ie@1$3@1$1@1$0#8").

Fixpoint list_byte_eqb (p q : list byte) : bool :=
  match p, q with
  | [], [] => true
  | a :: p', b :: q' => bv_eqb a b && list_byte_eqb p' q'
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition spec : ltac2:(zQ "50!h8!j7!hne!hrf!nb>4argv@1$0@1$0@1$4@1$1#8>3fs0$2$3") := ltac2:(zQ "h40!h8!j7!nb!in8!hrf!imc!jlb!im2!jme!joe!jp4!jpc!jq6!is6!hne!jr7!js4!jt0!jtc!juc\4argv@1$0@1$0@1$2@1$1#8\3fs0$eM0\4argv@1$0@1$0@1$2@1$1#8$4^2@2$3@1$8@3$9@1$0@1$2@1$1#8@1$7@1$2@1$1#8^2^1\1l@1$0@1$2@1$1#8\2l0@1$0@1$0@1$2@1$1#8M0\2l0@1$0@1$0@1$2@1$1#8$4^1@2$3@1$8@3$9@1$0@1$2@1$1#8@1$7@1$2@1$1#8^4^3\4path@1$0@1$2@1$1#8\2l1@1$0@1$0@1$2@1$1#8M0\2l1@1$0@1$0@1$2@1$1#8$4^1M5\0$5$4@2$h3Nhgg0@2$d@1$2@1$1#8^2@2$3@1$6^2^5M5\0$5$4@2$c^2@1$7@1$2@1$1#8@2$3@1$6^2^5M5\0$5$4@2$c^2$h0@2$b@2$3@1$6^2^5@2$h2^2^5Ma\1x@1$a@1$0@1$2@1$1#8$4@2$f^5^2\4data@1$0@1$2@1$1#8@2$b@2$3@1$6^3^6@2$h1^1^6@2$3@1$6^2^5\2l2@1$0@1$2@1$1#8\2l3@1$0@1$0@1$2@1$1#8@2$3@1$8@3$9@1$0@1$2@1$1#8@1$7@1$2@1$1#8^8^7").
(* [comment removed for export] *)
