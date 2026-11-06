(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb
  PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefMemcpyLib SymDriveH4 LibStdioCall MainWalk_defs.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe1Z04cons03nil04prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~kc7scriptskc9sym_statekc8sidecond04true69OSSVerify6Proofsaboost_jsonafuzz_parse3libdMainWalk_defs~~~~~~r25FUELMkc8sym_exec69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~hg5floaded_segmentskc6kentrykc4EVarkc3KWrkc2SAkc4ELitkc4KImgkc6KAlignkc6KRangekc5KWord03app89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsdAsTRWalk_defs4FPX1~~~~~~hpa3knTkc4exprr23spx04bool05falsekc3SCR" s.
Import ListNotations.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition STOPST : ltac2:(zQ "20!h8!j7@1$0$1") := ltac2:(zQ "30!j7!jb!k1@3$1$0+pgqvc@3$1$0+pgqv8@3$1$0+ouvn4@3$1$0+rvih4@3$1$0+ruth4@3$1$0+ruqj0@3$1$0+rurt4@3$1$0+rusk4@1$2$0").
(* [comment removed for export] *)
Definition runT : ltac2:(zQ "60!h8!k6!ob!p5!j7!q1>5stops@1$0$4>3scr$2>2ss$3@2$1@2$1$3@1$0$5$2") := ltac2:(zQ "a0!h8!k1!qc!j7!v2!ob!q1!va!p5!hjf\5stops@1$0$3\3scr$5\2ss$8@7$7$9$4$2^3^2^1@1$1$6").

(* [comment removed for export] *)
Definition knT : ltac2:(zQ "20!h8!hl2@1$0$1") := ltac2:(zQ "a0!hl2!jb!hlb!hm2!hm8!hmd!hn4!k1!hnb!ho4@3$1$0@2$8@1$2N0+h0@3$1$0@3$9@1$2N0+nvvvnvohhgg0+nvvvvvvvvvo0@3$1$0@2$3@2$4@1$2N0-o0+o0@3$1$0@2$3@2$4@1$5Z+muvnt0+i0@3$1$0@2$3@2$4@1$5Z+nhhjm8+hj0@3$1$0@2$6+hggg0+mngg0@3$1$0@2$6+hqqgg0+hrkgg0@1$7$0").
(* [comment removed for export] *)
Definition knT0 : ltac2:(zQ "20!h8!hl2@1$0$1") := ltac2:(zQ "80!hmd!hl2!jb!hod!hm8!hp5!k1!hu2@3$5$1@3$2$1@3$3@2$4@1$0Z+muvnt0N1@1$0Z@3$2$1@3$3@2$4@1$0Z+nhhlqbN1@1$0Z@3$2$1@3$3@2$4@1$0Z+nhhjm8N1@1$0Z@3$2$1@3$3@2$4@1$0Z+nhhjmcN4@1$0Z@3$2$1@3$3@2$4@1$0Z+nhhjn0N4@1$0+1@3$2$1@3$3@2$4@1$0Z+nhhjn8N8@1$0+nhhjo0@3$2$1@3$3@2$4@1$0Z+nhhjo0N8@1$0Z@1$6$1$7").
(* [comment removed for export] *)
Definition knT8 : ltac2:(zQ "20!h8!hl2@1$0$1") := ltac2:(zQ "90!hlb!hl2!jb!hod!hm8!hp5!k1!hu2!hmd@3$5$1@3$2$1@3$3@2$4@1$0N0-8N8@1$8+ruqj0@3$2$1@3$3@2$4@1$0N0-h0N8@1$0N1@3$2$1@3$3@2$4@1$0N0-h8N8@1$0N2@3$2$1@3$3@2$4@1$0N0-i0N8@1$0N3@3$2$1@3$3@2$4@1$0N0-i8N8@1$0N4@3$2$1@3$3@2$4@1$0N0-j0N8@1$0N5@3$2$1@3$3@2$4@1$0N0-j8N8@1$0N6@3$2$1@3$3@2$4@1$0N0-k0N8@1$0N7@3$2$1@3$3@2$4@1$0N0-k8N8@1$0N8@1$6$1$7").

(* [comment removed for export] *)
Definition srT00 : ltac2:(zQ "20!h8!hu9@1$0$1") := ltac2:(zQ "50!hu9!jb!hlb!hmd!k1@3$1$0@1$3Z@3$1$0@1$3+ruqj0@3$1$0@1$2N0@3$1$0@1$2Nh1@3$1$0@1$3+mvhjh8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2Nh6@3$1$0@1$2Nh7@3$1$0@1$2N8@3$1$0@1$2N2@3$1$0@1$2N7@3$1$0@1$2N3@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2Ni0@3$1$0@1$2Ni1@3$1$0@1$2Ni2@3$1$0@1$2Ni3@3$1$0@1$2Ni4@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition rT0 := Eval vm_compute in runT STOPST noscr (SS 0xbeb8c srT00 [] knT0 46).
Definition srT0 : list expr := Eval vm_compute in s_regs (fst (fst rT0)).
(* [comment removed for export] *)
Definition srT10 : ltac2:(zQ "20!h8!hu9@1$0$1") := ltac2:(zQ "60!hu9!jb!hlb!hmd!k1!hv0@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-l0@3$1$0@1$2Nh1@3$1$0@1$3+mvhjh8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2N3@3$1$0@1$2N7@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N8@3$1$0@1$3+muvnt0@3$1$0@1$2Ni3@3$1$0@1$2Ni4@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrT1a : ltac2:(zQ "10!ob$0") := ltac2:(zQ "70!hv6!jb!k1!hvc!hu9!hlb!ig3@3$6@3$1$0$3@3$1$0$3@1$2$0@3$1$4@1$5N5@1$2$4@1$2$0").   (* [comment removed for export] *)
Definition scrT1b : ltac2:(zQ "10!ob$0") := ltac2:(zQ "80!hv6!jb!k1!hu9!hvc!qc!hlb!ig3@3$7@3$1$0$4@3$1$0$5@1$2$0@3$1$3@1$6N5@1$2$3@1$2$0").    (* [comment removed for export] *)
Definition scrT1c : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!hv6!k1!jb!qc!ig3!hu9@3$4@3$2$0$3@3$2$0$3@1$1$0@1$1$5@1$1$0").            (* [comment removed for export] *)
Definition scrT1d : ltac2:(zQ "10!ob$0") := ltac2:(zQ "70!hv6!k1!jb!hvc!qc!ig3!hu9@3$5@3$2$0$4@3$2$0$3@1$1$0@1$1$6@1$1$0").           (* [comment removed for export] *)
Definition rT1a := Eval vm_compute in runT STOPST scrT1a (SS 0xbebd4 srT10 [] knT 46).
Definition rT1b := Eval vm_compute in runT STOPST scrT1b (SS 0xbebd4 srT10 [] knT 46).
Definition rT1c := Eval vm_compute in runT STOPST scrT1c (SS 0xbebd4 srT10 [] knT 46).
Definition rT1d := Eval vm_compute in runT STOPST scrT1d (SS 0xbebd4 srT10 [] knT 46).
Definition srT1a : list expr := Eval vm_compute in s_regs (fst (fst rT1a)).
Definition srT1b : list expr := Eval vm_compute in s_regs (fst (fst rT1b)).
Definition srT1c : list expr := Eval vm_compute in s_regs (fst (fst rT1c)).
Definition srT1d : list expr := Eval vm_compute in s_regs (fst (fst rT1d)).
(* [comment removed for export] *)
Definition srT20 : ltac2:(zQ "20!h8!hu9@1$0$1") := ltac2:(zQ "60!hu9!jb!hlb!hmd!k1!hv0@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-l0@3$1$0@1$2Nh1@3$1$0@1$3+mvhjh8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2N3@3$1$0@1$2N7@3$1$0@1$2N4@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N2@3$1$0@1$2N8@3$1$0@1$3+muvnt0@3$1$0@1$2N6@3$1$0@1$2Ni4@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrT2 : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!hv6!k1!jb!hvc!ig3!hu9@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").   (* [comment removed for export] *)
Definition rT2 := Eval vm_compute in runT STOPST scrT2 (SS 0xbebf0 srT20 [] knT 46).
Definition srT2 : list expr := Eval vm_compute in s_regs (fst (fst rT2)).
(* [comment removed for export] *)
Definition srT30 : ltac2:(zQ "20!h8!hu9@1$0$1") := ltac2:(zQ "60!hu9!jb!hlb!hmd!k1!hv0@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-l0@3$1$0@1$2Nh1@3$1$0@1$3+mvhjh8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2N3@3$1$0@1$2N7@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N4@3$1$0@1$2N8@3$1$0@1$3+muvnt0@3$1$0@1$2N6@3$1$0@1$2Ni4@3$1$0@1$2Ni5@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition rT3 := Eval vm_compute in runT STOPST noscr (SS 0xbec04 srT30 [] knT 46).
Definition srT3 : list expr := Eval vm_compute in s_regs (fst (fst rT3)).
(* [comment removed for export] *)
Definition srT50 : ltac2:(zQ "20!h8!hu9@1$0$1") := ltac2:(zQ "60!hu9!jb!hlb!hmd!k1!hv0@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-l0@3$1$0@1$2Nh1@3$1$0@1$3+mvhjh8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2N3@3$1$0@1$2N4@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N9@3$1$0@1$2Na@3$1$0@1$3+muvnt0@3$1$0@1$2N6@3$1$0@1$3Z@3$1$0@1$3-2@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition rT5 := Eval vm_compute in runT STOPST noscr (SS 0xbec44 srT50 [] knT 46).
Definition srT5 : list expr := Eval vm_compute in s_regs (fst (fst rT5)).
(* [comment removed for export] *)
Definition srT60 : ltac2:(zQ "20!h8!hu9@1$0$1") := ltac2:(zQ "60!hu9!jb!hlb!hmd!k1!hv0@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-l0@3$1$0@1$2Nh1@3$1$0@1$3+mvhjh8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2N3@3$1$0@1$2N4@3$1$0@1$3Z@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N9@3$1$0@1$2Ni1@3$1$0@1$3+muvnt0@3$1$0@1$2N6@3$1$0@1$3Z@3$1$0@1$3-2@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition rT6 := Eval vm_compute in runT STOPST noscr (SS 0xbec58 srT60 [] knT 46).
Definition srT6 : list expr := Eval vm_compute in s_regs (fst (fst rT6)).
(* [comment removed for export] *)
Definition srT70 : ltac2:(zQ "20!h8!hu9@1$0$1") := ltac2:(zQ "60!hu9!jb!hlb!hmd!k1!hv0@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-l0@3$1$0@1$2Nh1@3$1$0@1$3+mvhjh8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2N3@3$1$0@1$2N4@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2N9@3$1$0@1$3Z@3$1$0@1$3+muvnt0@3$1$0@1$2N6@3$1$0@1$3Z@3$1$0@1$3-2@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition scrT7a : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!hv6!k1!jb!qc!ig3!hu9@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").    (* [comment removed for export] *)
Definition scrT7b : ltac2:(zQ "10!ob$0") := ltac2:(zQ "60!hv6!k1!jb!hvc!ig3!hu9@3$4@3$2$0$3@1$1$0@1$1$5@1$1$0").   (* [comment removed for export] *)
Definition rT7a := Eval vm_compute in runT STOPST scrT7a (SS 0xbec68 srT70 [] knT 46).
Definition rT7b := Eval vm_compute in runT STOPST scrT7b (SS 0xbec68 srT70 [] knT 46).
Definition srT7a : list expr := Eval vm_compute in s_regs (fst (fst rT7a)).
Definition srT7b : list expr := Eval vm_compute in s_regs (fst (fst rT7b)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition srT80 : ltac2:(zQ "20!h8!hu9@1$0$1") := ltac2:(zQ "60!hu9!jb!hlb!hmd!k1!hv0@3$1$0@1$3Z@3$1$0@1$2Nf@3$1$0@1$5-l0@3$1$0@1$2Nh1@3$1$0@1$3+mvhjh8@3$1$0@1$2Nh3@3$1$0@1$2Nh4@3$1$0@1$2Nh5@3$1$0@1$2Nh6@3$1$0@1$2Nh7@3$1$0@1$2Nh8@3$1$0@1$2Nh9@3$1$0@1$2Nha@3$1$0@1$2Nhb@3$1$0@1$2Nhc@3$1$0@1$2Nhd@3$1$0@1$2Nhe@3$1$0@1$2Nhf@3$1$0@1$2Ni0@3$1$0@1$2Ni1@3$1$0@1$3+muvnt0@3$1$0@1$2Ni3@3$1$0@1$3Z@3$1$0@1$3-2@3$1$0@1$2Ni6@3$1$0@1$2Ni7@3$1$0@1$2Ni8@3$1$0@1$2Ni9@3$1$0@1$2Nia@3$1$0@1$2Nib@3$1$0@1$2Nic@3$1$0@1$2Nid@1$4$0").
Definition rT8 := Eval vm_compute in runT STOPST noscr (SS 0xbec84 srT80 [] knT8 46).
Definition srT8 : list expr := Eval vm_compute in s_regs (fst (fst rT8)).

(* [comment removed for export] *)
End FPX1.
(* [comment removed for export] *)
