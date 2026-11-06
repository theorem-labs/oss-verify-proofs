(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc3. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4 LibStdioCall MainWalk_defs.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe1Z04cons03nil04prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~kc7scriptskc9sym_statekc8sidecond04true69OSSVerify6Proofsaboost_jsonafuzz_parse3libdMainWalk_defs~~~~~~r25FUELMkc8sym_exec69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~hg5floaded_segmentskc6kentrykc4EVarkc3KWrkc2SAkc4ELitkc4KImgkc6KAlignkc6KRangekc5KWord03app89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsdAsTRWalk_defs4FPX1~~~~~~hp53knTkc4exprr23spx04bool05falsekc3SCR" s.
Import ListNotations.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := Asan.M.loaded_segments.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition STOPST : ltac2:(zQ "20!h8!j7@1$0$1") := ltac2:(zQ "30!j7!jb!k1@3$1$0+pgrlc@3$1$0+pgrl8@3$1$0+ouvt4@3$1$0+rvjn8@3$1$0+rutn8@3$1$0+ruqp4@3$1$0+rusj8@3$1$0+rusq8@1$2$0").
(* [comment removed for export] *)
Definition runT : ltac2:(zQ "60!h8!k6!ob!p5!j7!q1>5stops@1$0$4>3scr$2>2ss$3@2$1@2$1$3@1$0$5$2") := ltac2:(zQ "a0!h8!k1!qc!j7!v2!ob!q1!va!p5!hja\5stops@1$0$3\3scr$5\2ss$8@7$7$9$4$2^3^2^1@1$1$6").

(* [comment removed for export] *)
Definition knT : ltac2:(zQ "20!h8!hkd@1$0$1") := ltac2:(zQ "a0!hkd!jb!hl6!hld!hm3!hm8!hmf!k1!hn6!hnf@3$1$0@2$8@1$2N0+h0@3$1$0@3$9@1$2N0+nvvvnvohhgg0+nvvvvvvvvvo0@3$1$0@2$3@2$4@1$2N0-o0+o0@3$1$0@2$3@2$4@1$5Z+mviop0+i0@3$1$0@2$3@2$4@1$5Z+nhkki8+hj0@3$1$0@2$6+hggg0+mngg0@3$1$0@2$6+hqtgg0+hrngg0@1$7$0").
(* [comment removed for export] *)
Definition knT0 : ltac2:(zQ "20!h8!hkd@1$0$1") := ltac2:(zQ "80!hm8!hkd!jb!ho8!hm3!hp0!k1!htd@3$5$1@3$2$1@3$3@2$4@1$0Z+mviop0N1@1$0Z@3$2$1@3$3@2$4@1$0Z+nhkmmbN1@1$0Z@3$2$1@3$3@2$4@1$0Z+nhkki8N1@1$0Z@3$2$1@3$3@2$4@1$0Z+nhkkicN4@1$0Z@3$2$1@3$3@2$4@1$0Z+nhkkj0N4@1$0+1@3$2$1@3$3@2$4@1$0Z+nhkkj8N8@1$0+nhkkk0@3$2$1@3$3@2$4@1$0Z+nhkkk0N8@1$0Z@1$6$1$7").
(* [comment removed for export] *)
Definition knT8 : ltac2:(zQ "20!h8!hkd@1$0$1") := ltac2:(zQ "90!hl6!hkd!jb!ho8!hm3!hp0!k1!htd!hm8@3$5$1@3$2$1@3$3@2$4@1$0N0-8N8@1$8+ruqp4@3$2$1@3$3@2$4@1$0N0-h0N8@1$0N1@3$2$1@3$3@2$4@1$0N0-h8N8@1$0N2@3$2$1@3$3@2$4@1$0N0-i0N8@1$0N3@3$2$1@3$3@2$4@1$0N0-i8N8@1$0N4@3$2$1@3$3@2$4@1$0N0-j0N8@1$0N5@3$2$1@3$3@2$4@1$0N0-j8N8@1$0N6@3$2$1@3$3@2$4@1$0N0-k0N8@1$0N7@3$2$1@3$3@2$4@1$0N0-k8N8@1$0N8@1$6$1$7").

(* [comment removed for export] *)
Definition srT00 : ltac2:(zQ "20!h8!hu4@1$0$1") := ltac2:(zQ "50!hu4!jb!hl6!hm8!k1@3$1$0@1$3Z@3$1$0@1$3+ruqp4@3$1$0@1$2N0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2Nh6@3$1$0@1$2Nh7@3$1$0@1$2N8@3$1$0@1$2N2@3$1$0@1$2N7@3$1$0@1$2N3@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2Ni0@3$1$0@1$2Ni1@3$1$0@1$2Ni2@3$1$0@1$2Ni3@3$1$0@1$2Ni4@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition rT0 := Eval vm_compute in runT STOPST noscr (SS 0xbebf0 srT00 [] knT0 46).
Definition srT0 : list expr := Eval vm_compute in s_regs (fst (fst rT0)).
(* [comment removed for export] *)
Definition srT10 : ltac2:(zQ "20!h8!hu4@1$0$1") := ltac2:(zQ "60!hu4!jb!hl6!hm8!k1!hub@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-l0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2N3@3$1$0@1$2N7@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N8@3$1$0@1$3+mviop0@3$1$0@1$2Ni3@3$1$0@1$2Ni4@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrT1a : ltac2:(zQ "10!ob$0") := ltac2:(zQ "70!hv1!jb!k1!hv7!hu4!hl6!hve@3$6@3$1$0$3@3$1$0$3@1$2$0@3$1$4@1$5N5@1$2$4@1$2$0").   (* [comment removed for export] *)
Definition scrT1b : ltac2:(zQ "10!ob$0") := ltac2:(zQ "80!hv1!jb!k1!hu4!hv7!qc!hl6!hve@3$7@3$1$0$4@3$1$0$5@1$2$0@3$1$3@1$6N5@1$2$3@1$2$0").    (* [comment removed for export] *)
Definition scrT1c : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!hv1!k1!jb!qc!hve!hu4@3$4@3$2$0$3@3$2$0$3@1$1$0@1$1$5@1$1$0").            (* [comment removed for export] *)
Definition scrT1d : ltac2:(zQ "10!ob$0") := ltac2:(zQ "70!hv1!k1!jb!hv7!qc!hve!hu4@3$5@3$2$0$4@3$2$0$3@1$1$0@1$1$6@1$1$0").           (* [comment removed for export] *)
Definition rT1a := Eval vm_compute in runT STOPST scrT1a (SS 0xbec38 srT10 [] knT 46).
Definition rT1b := Eval vm_compute in runT STOPST scrT1b (SS 0xbec38 srT10 [] knT 46).
Definition rT1c := Eval vm_compute in runT STOPST scrT1c (SS 0xbec38 srT10 [] knT 46).
Definition rT1d := Eval vm_compute in runT STOPST scrT1d (SS 0xbec38 srT10 [] knT 46).
Definition srT1a : list expr := Eval vm_compute in s_regs (fst (fst rT1a)).
Definition srT1b : list expr := Eval vm_compute in s_regs (fst (fst rT1b)).
Definition srT1c : list expr := Eval vm_compute in s_regs (fst (fst rT1c)).
Definition srT1d : list expr := Eval vm_compute in s_regs (fst (fst rT1d)).
(* [comment removed for export] *)
Definition srT20 : ltac2:(zQ "20!h8!hu4@1$0$1") := ltac2:(zQ "60!hu4!jb!hl6!hm8!k1!hub@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-l0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2N3@3$1$0@1$2N7@3$1$0@1$2N4@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N8@3$1$0@1$3+mviop0@3$1$0@1$2N6@3$1$0@1$2Ni4@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrT2 : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!hv1!k1!jb!hv7!hve!hu4@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").   (* [comment removed for export] *)
Definition rT2 := Eval vm_compute in runT STOPST scrT2 (SS 0xbec54 srT20 [] knT 46).
Definition srT2 : list expr := Eval vm_compute in s_regs (fst (fst rT2)).
(* [comment removed for export] *)
Definition srT30 : ltac2:(zQ "20!h8!hu4@1$0$1") := ltac2:(zQ "60!hu4!jb!hl6!hm8!k1!hub@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-l0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2N3@3$1$0@1$2N7@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N4@3$1$0@1$2N8@3$1$0@1$3+mviop0@3$1$0@1$2N6@3$1$0@1$2Ni4@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition rT3 := Eval vm_compute in runT STOPST noscr (SS 0xbec68 srT30 [] knT 46).
Definition srT3 : list expr := Eval vm_compute in s_regs (fst (fst rT3)).
(* [comment removed for export] *)
Definition srT50 : ltac2:(zQ "20!h8!hu4@1$0$1") := ltac2:(zQ "60!hu4!jb!hl6!hm8!k1!hub@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-l0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2N3@3$1$0@1$2N4@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N9@3$1$0@1$2Na@3$1$0@1$3+mviop0@3$1$0@1$2N6@3$1$0@1$3Z@3$1$0@1$3-2@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition rT5 := Eval vm_compute in runT STOPST noscr (SS 0xbeca8 srT50 [] knT 46).
Definition srT5 : list expr := Eval vm_compute in s_regs (fst (fst rT5)).
(* [comment removed for export] *)
Definition srT60 : ltac2:(zQ "20!h8!hu4@1$0$1") := ltac2:(zQ "60!hu4!jb!hl6!hm8!k1!hub@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-l0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2N3@3$1$0@1$2N4@3$1$0@1$3Z@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N9@3$1$0@1$2Ni1@3$1$0@1$3+mviop0@3$1$0@1$2N6@3$1$0@1$3Z@3$1$0@1$3-2@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition rT6 := Eval vm_compute in runT STOPST noscr (SS 0xbecbc srT60 [] knT 46).
Definition srT6 : list expr := Eval vm_compute in s_regs (fst (fst rT6)).
(* [comment removed for export] *)
Definition srT70 : ltac2:(zQ "20!h8!hu4@1$0$1") := ltac2:(zQ "60!hu4!jb!hl6!hm8!k1!hub@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-l0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2N3@3$1$0@1$2N4@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N9@3$1$0@1$3Z@3$1$0@1$3+mviop0@3$1$0@1$2N6@3$1$0@1$3Z@3$1$0@1$3-2@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrT7a : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!hv1!k1!jb!qc!hve!hu4@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").    (* [comment removed for export] *)
Definition scrT7b : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!hv1!k1!jb!hv7!hve!hu4@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").   (* [comment removed for export] *)
Definition rT7a := Eval vm_compute in runT STOPST scrT7a (SS 0xbeccc srT70 [] knT 46).
Definition rT7b := Eval vm_compute in runT STOPST scrT7b (SS 0xbeccc srT70 [] knT 46).
Definition srT7a : list expr := Eval vm_compute in s_regs (fst (fst rT7a)).
Definition srT7b : list expr := Eval vm_compute in s_regs (fst (fst rT7b)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition srT80 : ltac2:(zQ "20!h8!hu4@1$0$1") := ltac2:(zQ "60!hu4!jb!hl6!hm8!k1!hub@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-l0@3$1$0@1$2Nh1@3$1$0@1$3+mvkjt8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2Nh6@3$1$0@1$2Nh7@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2Ni0@3$1$0@1$2Ni1@3$1$0@1$3+mviop0@3$1$0@1$2Ni3@3$1$0@1$3Z@3$1$0@1$3-2@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition rT8 := Eval vm_compute in runT STOPST noscr (SS 0xbece8 srT80 [] knT8 46).
Definition srT8 : list expr := Eval vm_compute in s_regs (fst (fst rT8)).

(* [comment removed for export] *)
End FPX1.
(* [comment removed for export] *)
