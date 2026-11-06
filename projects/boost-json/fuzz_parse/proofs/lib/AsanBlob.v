(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From Stdlib Require Import PrimInt63 PrimString.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AsanPlanCore AsanPlan.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z57Corelib7Numbers6Cyclic5Int639PrimInt63hc3int37Corelib4Init9Datatypeska4boolhc3eqbhc4land46Stdlib6ZArith6BinInt1Zn63addn64div2n64evenn63opp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanBlob3AXB~~~~~~q8dz_of_int_bitska3nat37Corelib7StringsaPrimStringvd6stringvd6lengthq88z_of_intn66to_natka4prod89OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanBlob3AXB3Dec~~~~~~hk66rd_numka4pairq84unzzn63eqb3h5LinuxProcessSemantics5Riscv5Instrhq75aluop08positivehq77ALU_ANDhq77ALU_ADDhq76ALU_ORhq77ALU_SLLhq77ALU_SLThq78ALU_SLTUhq77ALU_SRAhq77ALU_SRLhq77ALU_SUBhq77ALU_XORhq75mulophq76M_REMUhq75M_DIVhq76M_DIVUhq75M_MULhq76M_MULHhq78M_MULHSUhq77M_MULHUhq75M_REM79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~iq55mkindiq55KHOLEiq54KFOGiq55KNONEiq59KNONELAZYiq53KRWiq57KRWLAZY79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~ji54exprhk66rdexprji55saddrhk63rdZhk63rdeji52SAji56kentryhk64rdsaji54KUnkhk65rdnatji56KAlignji55KBlobji55KDisjji55KFillji54KImgji56KRangeji55KWordji53KWrji55KZeroji56sentryji52SEji59sym_stateka4listhk66rdlistka6optionhk64rdkehk65rdopthk64rdseji53SSRiq54amaphk68mkind_ofhk63rdNiq52AMiq53afdiq55FdDiriq56FdFileiq55FdStdiq54vmopiq55VProthk63rdbiq56VFixIniq54VNewiq56VUnmapiq53acshk66rdpairhk64rdamhk64rdfdhk64rdsshk66rdvmopiq53ACSq84blobq86blob_sq85evtabq86finishq87fuel_ofq85rdacs" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.   (* [comment removed for export] *)
Open Scope Z_scope.

Module AXB.

(* [comment removed for export] *)
Definition zc : ltac2:(zQ "20!h9!k4>1c$1$0") := ltac2:(zQ "60!m2!h9!m9!mf!oe!k4\1c$5@2$4@2$4@2$4@2$4M0\0$0$1@2$2@2$3^1Ih0I0Z+h0M0\0$0$1@2$2@2$3^1I8I0Z+8M0\0$0$1@2$2@2$3^1I4I0Z+4M0\0$0$1@2$2@2$3^1I2I0Z+2M0\0$0$1@2$2@2$3^1I1I0Z+1").

(* [comment removed for export] *)
Definition FIN : string := "0123456789!#$%&'()+,".
Definition NONFIN : string := "-./:;<=>?@[\]^_`{|}~".

(* [comment removed for export] *)
Fixpoint find_in (a : string) (c : int) (k : nat) (i : int) {struct k} : int :=
  match k with
  | O => 20%uint63
  | S k' => if PrimInt63.eqb (get a i) c then i else find_in a c k' (PrimInt63.add i 1)
  end.

Definition unzz : ltac2:(zQ "10!h9>1n$0$0") := ltac2:(zQ "60!m2!h9!p4!oe!pb!q2\1n$1M0\0$0$1@1$4^1@1$2^1@1$5@1$2@2$3^1+1").

(* [comment removed for export] *)
Fixpoint z_of_int_bits (k : nat) (c : int) {struct k} : Z :=
  match k with
  | O => 0
  | S k' => (if PrimInt63.eqb (PrimInt63.land c 1) 0 then 0 else 1) + 2 * z_of_int_bits k' (PrimInt63.lsr c 1)
  end.
Definition z_of_int : ltac2:(zQ "20!h9!k4>1c$1$0") := ltac2:(zQ "20!k4!u7\1c$0@2$1Njf^1").
(* [comment removed for export] *)
Definition fuel_of : ltac2:(zQ "20!v7!hh9>1s$1$0") := ltac2:(zQ "50!hi2!hh9!hib!oe!hj6\1s$1@1$4@2$3@1$2@1$0^1+1").

Section Dec.
Variable s : string.
Variable F : nat.
(* [comment removed for export] *)
Variable ev : ltac2:(zQ "20!h9!jm6>0$0$1").

(* [comment removed for export] *)
Fixpoint rd_num (i : int) (k : nat) {struct k} : Z * int :=
  match k with
  | O => (0, i)
  | S k' =>
      let c := get s i in
      let f := find_in FIN c 20 0 in
      if PrimInt63.ltb f 20 then (zc f, PrimInt63.add i 1)
      else let (r, j) := rd_num (PrimInt63.add i 1) k' in (zc (find_in NONFIN c 20 0) + 20 * r, j)
  end.

Definition rdN : ltac2:(zQ "30!k4!hjf!h9>1i$0@2$1$2$0") := ltac2:(zQ "20!k4!ho9\1i$0@2$1^1?1F").
Definition rdZ : ltac2:(zQ "30!k4!hjf!h9>1i$0@2$1$2$0") := ltac2:(zQ "60!k4!h9!hjf!hp3!ho9!hpa\1i$0M2\1p@2$2$1$0@2$2$1$0@2$4^1?1F\1n$1\1j$0@4$3$1$0@1$5^2^1").
Definition rdnat : ltac2:(zQ "30!k4!v7!hjf>1i$0@2$2$1$0") := ltac2:(zQ "70!k4!hjf!v7!h9!hp3!ho9!hj6\1i$0M1\1p@2$1$3$0@2$1$2$0@2$5^1?1F\1n$3\1j$0@4$4$2$0@1$6^2^1").
Definition rdb : ltac2:(zQ "30!k4!m2!hjf>1i$0@2$2$1$0") := ltac2:(zQ "70!k4!hjf!m2!h9!hp3!ho9!hq1\1i$0M1\1p@2$1$3$0@2$1$2$0@2$5^1?1F\1n$3\1j$0@4$4$2$0@2$6^2+1^1").

Fixpoint rd_listn {A : Type} (r : int -> A * int) (n : nat) (i : int) {struct n} : list A * int :=
  match n with
  | O => ([], i)
  | S n' => let (x, j) := r i in let (xs, k) := rd_listn r n' j in (x :: xs, k)
  end.
Definition rdlist {A : Type} (r : int -> A * int) (i : int) : list A * int :=
  let (n, j) := rd_num i F in rd_listn r (Z.to_nat n) j.
Definition rdopt {A : Type} (r : int -> A * int) (i : int) : option A * int :=
  let (n, j) := rd_num i F in if Z.eqb n 0 then (None, j) else let (x, k) := r j in (Some x, k).
Definition rdpair {A B : Type} (ra : int -> A * int) (rb : int -> B * int) (i : int) : (A * B) * int :=
  let (a, j) := ra i in let (b, k) := rb j in ((a, b), k).

Definition aluop_of : ltac2:(zQ "20!h9!hsb>1n$0$1") := ltac2:(zQ "d0!ht4!hte!hsb!h9!hu9!hv4!hve!ig9!ih4!ii0!iib!ij6!ik1\1n$3M3\1n$3$2^1$4\1p$0M0\1p$0$2^1\2p0$0M0\2p0$0$2^1\2p1$0M0\2p1$0$2^1\2p2$0$1\2p2$0$1$9\2p1$0M0\2p1$0$2^1\2p2$0$1\2p2$0$1$c$7\2p0$0M0\2p0$0$2^1\2p1$0M0\2p1$0$2^1\2p2$0$1\2p2$0$1$a\2p1$0M0\2p1$0$2^1\2p2$0$1\2p2$0M0\2p2$0$2^1\2p3$0$1\2p3$0$1$5$8$6$b\1p$0$1").
Definition mulop_of : ltac2:(zQ "20!h9!ikc>1n$0$1") := ltac2:(zQ "b0!ht4!il5!ikc!h9!ilf!im8!in2!inb!io5!ip1!ipc\1n$3M3\1n$3$2^1$6\1p$0M0\1p$0$2^1\2p0$0M0\2p0$0$2^1\2p1$0$1\2p1$0M0\2p1$0$2^1\2p2$0$1\2p2$0$1$5$9\2p0$0M0\2p0$0$2^1\2p1$0M0\2p1$0$2^1\2p2$0$1\2p2$0$1$a\2p1$0M0\2p1$0$2^1\2p2$0$1\2p2$0$1$4$8$7\1p$0$1").
Definition mkind_of : ltac2:(zQ "20!h9!iu3>1n$0$1") := ltac2:(zQ "90!ht4!iuc!iu3!h9!iv5!ivd!jg6!jh3!jha\1n$3M3\1n$3$2^1$7\1p$0M0\1p$0$2^1\2p0$0M0\2p0$0$2^1\2p1$0$1\2p1$0$1$6\2p0$0M0\2p0$0$2^1\2p1$0$1\2p1$0M0\2p1$0$2^1\2p2$0$1\2p2$0$1$4$5$8\1p$0$1").

Fixpoint rdexpr (f : nat) (i : int) {struct f} : expr * int :=
  match f with
  | O => (ELit 0, i)
  | S f' =>
      let (t, j) := rd_num i F in
      match t with
      | 0 => let (z, k) := rdZ j in (ELit z, k)
      | 1 => let (n, k) := rdN j in (ev n, k)
      | 2 => let (o, k) := rdN j in let (a, l) := rdexpr f' k in let (b, m) := rdexpr f' l in (EAlu (aluop_of o) a b, m)
      | 3 => let (o, k) := rdN j in let (a, l) := rdexpr f' k in let (b, m) := rdexpr f' l in (EAluw (aluop_of o) a b, m)
      | 4 => let (o, k) := rdN j in let (a, l) := rdexpr f' k in let (b, m) := rdexpr f' l in (EMd (mulop_of o) a b, m)
      | 5 => let (o, k) := rdN j in let (a, l) := rdexpr f' k in let (b, m) := rdexpr f' l in (EMdw (mulop_of o) a b, m)
      | 6 => let (sx, k) := rdb j in let (lo, l) := rdnat k in let (n, m) := rdnat l in let (e, p) := rdexpr f' m in (EExt sx lo n e, p)
      | _ => let (sx, k) := rdb j in let (kk, l) := rdnat k in let (z, m) := rdZ l in let (n, p) := rdnat m in (EBlob sx kk z n, p)
      end
  end.

Definition rde : ltac2:(zQ "30!k4!hjf!jm6>0$0@2$1$2$0") := ltac2:(zQ "10!jme@1$0?1F").
Definition rdsa : ltac2:(zQ "30!k4!hjf!jn8>1i$0@2$1$2$0") := ltac2:(zQ "90!k4!hjf!jn8!h9!jm6!hp3!jo1!jo8!jof\1i$0M1\1p@2$1$4$0@2$1$2$0@1$7^1\1b$4\1j$0M1\1p@2$1$3$0@2$1$2$0@1$6^1\1o$3\1k$0@4$5$2$0@2$8^4^2^1").

Definition rdke : ltac2:(zQ "30!k4!hjf!jp5>1i$0@2$1$2$0") := ltac2:(zQ "h88!k4!hjf!jp5!jm6!ht4!jn8!hp3!jo8!jpf!h9!jq7!jo1!v7!jqf!ho9!jr8!js2!jsb!jt4!jtd!ju5!juf!jv8!jvf&\1n$3\1l$0@4$6$2$0@2$a^4^2^1&M1\1p@2$1$3$0@2$1$2$0@1$7^1~0&\1k$0~1&\1a$5~2&M1\1p@2$1$5$0@2$1$2$0@1$8^5~3&\2p2$4~4&M1\1p@2$1$5$0@2$1$2$0@1$8^6~3&\2p3$4~6\1i$0M1\1p@2$1$9$0@2$1$2$0@2$e^1?1F\1t$9\1j$0M9\1t$9@2$1$2$0^2M1\1p@2$1$5$0@2$1$2$0@1$8^1\1a$5\1k$0M1\1p@2$1$c$0@2$1$2$0@1$d^1\1w$c\1l$0M1\1p@2$1$3$0@2$1$2$0@1$7^1\1v$3\1m$0@4$6$2$0@3$h5^6^4^2^1\1p$4M4\1p$4@2$1$2$0^1\2p0$4M4\2p0$4@2$1$2$0^1\2p1$4M4\2p1$4@2$1$2$0^1~5~5M1\1p@2$1$5$0@2$1$2$0@1$8^4\2a1$5\1k$0M1\1p@2$1$3$0@2$1$2$0@1$7^1\2n1$3\1l$0M1\1p@2$1$5$0@2$1$2$0@1$8^1\2a2$5\1m$0M1\1p@2$1$3$0@2$1$2$0@1$7^1\2n2$3\1p$0@4$6$2$0@4$h1^8^6^4^2^1\2p1$4M4\2p1$4@2$1$2$0^1~5~5M1\1p@2$1$3$0@2$1$2$0@1$7^4\1e$3\1k$0M1\1p@2$1$9$0@2$1$2$0@1$b^1\2lo$9\1l$0M1\1p@2$1$9$0@2$1$2$0@1$b^1\2hi$9\1m$0@4$6$2$0@3$h4^6^4^2^1M1\1p@2$1$9$0@2$1$2$0@1$b^3\2lo$9\1k$0M1\1p@2$1$9$0@2$1$2$0@1$b^1\2hi$9\1l$0@4$6$2$0@2$h3^4^2^1\2p0$4M4\2p0$4@2$1$2$0^1\2p1$4M4\2p1$4@2$1$2$0^1~5~5M1\1p@2$1$5$0@2$1$2$0@1$8^4\1a$5\1k$0M1\1p@2$1$3$0@2$1$2$0@1$7^1\1n$3\1l$0@4$6$2$0@2$h6^4^2^1\2p1$4M4\2p1$4@2$1$2$0^1~5\2p2$4M4\2p2$4@2$1$2$0^1~7~7M1\1p@2$1$5$0@2$1$2$0@1$8^5\1a$5\1k$0M1\1p@2$1$3$0@2$1$2$0@1$7^1\1n$3\1l$0M1\1p@2$1$9$0@2$1$2$0@1$b^1\1c$9\1m$0@4$6$2$0@3$h2^6^4^2^1M1\1p@2$1$3$0@2$1$2$0@1$7^4\1e$3\1k$0M1\1p@2$1$9$0@2$1$2$0@1$b^1\1m$9\1l$0@4$6$2$0@2$f^4^2^1M1\1p@2$1$5$0@2$1$2$0@1$8^3\1a$5\1k$0M1\1p@2$1$3$0@2$1$2$0@1$7^1\1n$3\1l$0M1\1p@2$1$c$0@2$1$2$0@1$d^1\2kk$c\1m$0@4$6$2$0@3$h0^6^4^2^1M1\1p@2$1$5$0@2$1$2$0@1$8^2\1a$5\1k$0M1\1p@2$1$3$0@2$1$2$0@1$7^1\1n$3\1l$0@4$6$2$0@2$h7^4^2^1\1p$4M1\1p@2$1$5$0@2$1$2$0@1$8^2~3").

Definition rdse : ltac2:(zQ "30!k4!hjf!kg8>1i$0@2$1$2$0") := ltac2:(zQ "b0!k4!hjf!kg8!v7!jm6!jn8!hp3!jo8!jqf!jpf!kh2\1i$0M1\1p@2$1$5$0@2$1$2$0@1$9^1\1a$5\1j$0M1\1p@2$1$3$0@2$1$2$0@1$8^1\1w$3\1k$0M1\1p@2$1$4$0@2$1$2$0@1$7^1\1v$4\1l$0@4$6$2$0@3$a^6^4^2^1").

Definition rdss : ltac2:(zQ "30!k4!hjf!kh8>1i$0@2$1$2$0") := ltac2:(zQ "h50!k4!hjf!kh8!ki5!kic!jm6!jp5!jn8!kg8!v7!kj6!h9!hp3!jo1!jo8!kjf!jqf!kk7!jpf!kl0!kl8\1i$0M1\1p@2$1$b$0@2$1$2$0@1$d^1\2pc$b\1j$0M1\1p@2$1@1$3$5$0@2$1$2$0@3$4$5$e^1\2rs@1$3$5\1k$0M1\1p@2$1@1$3$8$0@2$1$2$0@3$4$8$h3^1\2lg@1$3$8\1l$0M1\1p@2$1@1$3$6$0@2$1$2$0@3$4$6$f^1\2kn@1$3$6\1m$0M1\1p@2$1$9$0@2$1$2$0@1$h0^1\2nx$9\1p$0M1\1p@2$1@1$a$7$0@2$1$2$0@3$h1$7$h2^1\2rv@1$a$7\1q$0@4$c$2$0@6$h4^c^a^8^6^4^2^1").

Definition rdam : ltac2:(zQ "30!k4!hjf!klf>1i$0@2$1$2$0") := ltac2:(zQ "a0!k4!hjf!klf!jm6!h9!jo8!hp3!km7!kn3!kna\1i$0M1\1p@2$1$3$0@2$1$2$0@1$5^1\1b$3\1j$0M1\1p@2$1$3$0@2$1$2$0@1$5^1\2ln$3\1k$0M1\1p@2$1$4$0@2$1$2$0@1$8^1\2kd$4\1l$0@4$6$2$0@3$9^6^4@1$7^2^1").

Definition rdfd : ltac2:(zQ "30!k4!hjf!ko0>1i$0@2$1$2$0") := ltac2:(zQ "e0!k4!hjf!ko0!ht4!hp3!h9!jm6!ko7!v7!jo8!ho9!jqf!kp0!kpa\1i$0M1\1p@2$1$5$0@2$1$2$0@2$a^1?1F\1t$5\1j$0M5\1t$5@2$1$2$0^2@4$4$2$0$d^1\1p$3M3\1p$3@2$1$2$0^1\2p0$3@4$4$2$0$7^3\2p0$3@4$4$2$0$7^3M1\1p@2$1$8$0@2$1$2$0@1$b^2\2kk$8\1k$0M1\1p@2$1$6$0@2$1$2$0@1$9^1\2ln$6\1l$0M1\1p@2$1$6$0@2$1$2$0@1$9^1\3off$6\1m$0@4$4$2$0@3$c^6^4^2^1\1p$3@4$4$2$0$7^2").

Definition rdvmop : ltac2:(zQ "30!k4!hjf!kq3>1i$0@2$1$2$0") := ltac2:(zQ "h16!k4!hjf!kq3!jm6!jo8!ht4!hp3!h9!m2!kqb!kr4!km7!kn3!ho9!krb!ks5!ksd&\1n$3\1l$0@4$6$2$0@2$9^4^2^1&M1\1p@2$1$3$0@2$1$2$0@1$4^1~0&\1k$0~1&\1a$3~2&M1\1p@2$1$3$0@2$1$2$0@1$4^4~3&\2p1$5~4\1i$0M1\1p@2$1$7$0@2$1$2$0@2$d^1?1F\1t$7\1j$0M7\1t$7@2$1$2$0^2M1\1p@2$1$7$0@2$1$2$0@1$c^1\2kd$7\1k$0M1\1p@2$1$3$0@2$1$2$0@1$4^1\1a$3\1l$0M1\1p@2$1$3$0@2$1$2$0@1$4^1\1n$3\1m$0@4$6$2$0@3$f@1$b^6^4^2^1\1p$5M5\1p$5@2$1$2$0^1\2p0$5M1\1p@2$1$3$0@2$1$2$0@1$4^3~3\2p0$5M5\2p0$5@2$1$2$0^1~5~5M1\1p@2$1$3$0@2$1$2$0@1$4^3\1a$3\1k$0M1\1p@2$1$3$0@2$1$2$0@1$4^1\1n$3\1l$0@4$6$2$0@2$h0^4^2^1M1\1p@2$1$8$0@2$1$2$0@1$a^2\1x$8\1k$0M1\1p@2$1$8$0@2$1$2$0@1$a^1\1y$8\1l$0M1\1p@2$1$3$0@2$1$2$0@1$4^1\1a$3\1m$0M1\1p@2$1$3$0@2$1$2$0@1$4^1\1n$3\1p$0@4$6$2$0@4$e^8^6^4^2^1\1p$5M1\1p@2$1$3$0@2$1$2$0@1$4^2~3").

Definition rdacs : ltac2:(zQ "30!k4!hjf!kt7>1i$0@2$1$2$0") := ltac2:(zQ "h62!hjf!k4!jm6!kt7!ki5!h9!jo8!jo1!kic!klf!kq3!m2!kte!ko0!kh8!hp3!ku8!kr4!kv0!kv8!lg0!lga&\1p@2$0@1$4@2$0$2$2$1@2$0$3$1&@3$8@2$0$2$2@4$c$2$2$6$6^1\1i$1M0\1p@2$0$e$1@2$0$3$1@1$h3^1\2ss$e\2j1$1M0\1p@2$0@1$4$9$1@2$0$3$1@3$8$9$h0^1\2mp@1$4$9\2j2$1M0\1p@2$0$5$1@2$0$3$1@1$7^1\2ts$5\2j3$1M0\1p@2$0$5$1@2$0$3$1@1$7^1\2yl$5\2j4$1M0\1p@2$0$5$1@2$0$3$1@1$7^1\2eg$5\2j5$1M0~0~1\3vis@1$4@2$0$2$2\2j6$1M0~0~1\2gh@1$4@2$0$2$2\2j7$1M0\1p@2$0$5$1@2$0$3$1@1$7^1\2ab$5\2j8$1M0\1p@2$0$2$1@2$0$3$1@1$6^1\2bk$2\2j9$1M0\1p@2$0$d$1@2$0$3$1@1$h2^1\2fd$d\3j10$1M0\1p@2$0$b$1@2$0$3$1@1$h1^1\2td$b\3j11$1M0\1p@2$0@1$4$a$1@2$0$3$1@3$8$a$h4^1\2vo@1$4$a\3j12$1@4$f$3$1@c$h5^h8^h6^h4^h2^h0^e^c^a^8^6^4^2^1").

(* [comment removed for export] *)
Definition ENDMARK : Z := 4242.
Definition finish {A : Type} (xi : A * int) : option A :=
  let (x, i) := xi in
  let (e, j) := rd_num i F in
  if (Z.eqb e ENDMARK && PrimInt63.eqb j (length s))%bool then Some x else None.

End Dec.

(* [comment removed for export] *)
Record blob : Type := Blob { blob_s : string }.

(* [comment removed for export] *)
Fixpoint evtab (tab : list (Z * expr)) (n : Z) : expr :=
  match tab with [] => EVar (Z.to_nat n) | (k, e) :: r => if Z.eqb n k then e else evtab r n end.

(* [comment removed for export] *)
Definition acs_of_tab : ltac2:(zQ "70!ki5!kj6!hjf!h9!lh1!kt7!jm6>3tab@1$0@2$2$3$6>1b$4@1$1$5") := ltac2:(zQ "d0!ki5!v7!hjf!h9!hh9!lh1!lh8!li1!li9!lj2!ljc!kt7!jm6\3tab@1$0@2$2$3$c\1b$5=1s$4@1$6^1=1F$1@1$9^1@4$8^2^1$b@4$a^2^1@1$7^4I0").
(* [comment removed for export] *)

End AXB.

Declare Scope axb_scope.
Delimit Scope axb_scope with axb.
Bind Scope axb_scope with AXB.blob.
String Notation AXB.blob AXB.Blob AXB.blob_s : axb_scope.

(* [comment removed for export] *)
Ltac axb t := let v := eval vm_compute in t in
  lazymatch v with Some ?x => exact_no_check x | _ => fail "AsanBlob: the blob does not decode" end.
(* [comment removed for export] *)
(* [comment removed for export] *)
