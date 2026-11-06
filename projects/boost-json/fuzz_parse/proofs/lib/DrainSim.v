(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SimInv ExitSim PropExec CatSim CatExec SeqExec StreamExec WallSim StreamSim.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe4Npos35stdpp9bitvectorbdefinitionsje2bv3h5LinuxProcessSemanticsfLinuxProcessSem5Statem05event37Corelib5Lists7ListDefp63mapm06ReadEv36Stdlib5Lists4Listrc8flat_map79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8DrainSim4FPX1~~~~~~ta8reads_chje7Z_to_bv3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshifdmachine_state37Corelib4Init5Logichn73andhn72ex69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~hp86msteps06length37Corelib4Init5Peanohu32le69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7ExitSim~~~~~~hvd7to_exit69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7WallSim~~~~~~ik27to_wall03nil04prodhn72eq06optionhif6ms_gpr3h5LinuxProcessSemanticsfLinuxProcessSem3Runiqah0advance_past_svcjebbv_unsigned04Some04cons03nat04pair3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasejh08len_wordiqacapply_effectm07MemCopym09mkEffectU46Stdlib6ZArith6BinInt1Zjn12lejn16of_nat04bool04truehe1Zhifems_svc_pendinghifh0ms_writable_bytehif8set_gpr0m0aaccess_okbm0eread_bytes_maphp8bbuf_modeled79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8DrainSim5Drain~~~~~~kg97lh_nextkg96to_out69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8DrainSim~~~~~~klf5procs3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypekq37Segment" s.   (* [comment removed for export] *)

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Proc.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Context {A : Type}.
Variable f : ltac2:(zQ "30!ip8!j7!lb>0?1A>0@1$2@1$1#8@1$0?1A").

Fixpoint procs (a : A) (bs : list byte) : option A :=
  match bs with
  | [] => Some a
  | b :: rest => match f a b with Some a' => procs a' rest | None => None end
  end.

End Proc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

(* [comment removed for export] *)
Definition reads_ch : ltac2:(zQ "40!h8!j7!lb!oe>3rch@1$2@1$1#k0>6blocks@1$0@1$0@1$2@1$1#8@1$0$3") := ltac2:(zQ "70!j7!lb!h8!oe!qd!r3!sf\3rch@1$1@1$0#k0\6blocks@1$2@1$2@1$1@1$0#8@4$6@1$2@1$1@1$0#8$3\2bs@1$2@1$1@1$0#8@4$4@1$1@1$0#8$3@1$5^3^1^1").

(* [comment removed for export] *)
Definition reads : ltac2:(zQ "40!h8!j7!oe!lb>6blocks@1$0@1$0@1$3@1$1#8@1$0$2") := ltac2:(zQ "50!h8!j7!hha!hi5!lb\6blocks@1$0@1$0@1$4@1$1#8@2$2@2$3@1$1#k0Z^1").

End FPX1.

Section Traces.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Context {A : Type}.
Variable cnt : word.
Variable f : A -> byte -> option A.
Variable out : A -> list byte.
Variable ec : word.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End Traces.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

End FPX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Drain.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Context {A : Type}.
Variable segs : ltac2:(zQ "20!h8!kt8@1$0$1").
Variable cnt : word.
Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.
Variable f : ltac2:(zQ "30!ip8!j7!lb>0?1A>0@1$2@1$1#8@1$0?1A").
Variable out : ltac2:(zQ "30!h8!j7!lb>0?1A@1$0@1$2@1$1#8").
Variable ec : word.
Hypothesis Hec : (bv_unsigned ec < 256)%Z.
Variable LH : ltac2:(zQ "10!hm6>0?1A>0$0P").

(* [comment removed for export] *)
Definition lh_next : ltac2:(zQ "10!hm6>1a?1A>2ms$0P") := ltac2:(zQ "40!hm6!hob!hp2!ht1\1a?1A\2ms$0@2$2$0\3ms'$0@2$1@3$3?4segs^2^1@2?2LH^3^1").

(* [comment removed for export] *)
Definition WrFin : ltac2:(zQ "40!h8!j7!hm6!lb>2bs@1$0@1$3@1$1#8>2ms$2P") := ltac2:(zQ "a0!j7!hi5!lb!htb!h8!hob!hv7!hm6!ij7!inc\2bs@1$4@1$2@1$0#8\2ms$7@2$5@2$6N1@2$3@1$2@1$0#8^2@5$9?4segs@2$1@1$0#k0+1^1^2@2$8?4segs@2$1@1$0#k0Z").

(* [comment removed for export] *)
Inductive to_out : list byte -> machine_state -> Prop :=
| tout_exit : forall ms, to_exit segs (Z_to_bv 64 0) ms -> to_out [] ms
| tout_wr : forall bs ms, WrFin bs ms -> to_out bs ms
| tout_step : forall bs ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_out bs ms' -> to_out bs ms.

(* [comment removed for export] *)
Definition ReadPend : ltac2:(zQ "10!hm6>1a?1A>2ms$0P") := ltac2:(zQ "i64!j7!lb!h8!io7!ioc!hob!ip2!ip8!hp2!iq0!it6!iub!iv9!ivf!htb!jg5!jga!jjf!jkb!jlb!jm5!jo9!jof!hi5!jp9!jpf!jq5!hm6!jq9!jrb!jt0!jtc!ju9!jva!kka!kl5!kpa!ij7&@2$4@1$1@1$0#k0@1$2@1$1@1$0#8&@1$3~0&@2$4@1$1@1$0#k0@1$1@1$0#k0&@1$3~2\1a?1A\2ms$hb@2$8@1$1@1$0#k0\3buf@1$1@1$0#k0@2$8@1$1@1$0#k0\2x8@1$1@1$0#k0@2$5@3$6@1$7@1$1@1$0#k0@1$hc^3@2$c@1$1@1$0#k0^1@2$5@3$6$ha@2$b@1$0#k0^1+jf@2$5@3$6@1$1@1$0#k0@2$9^3N0@2$h7@1$0#k0Z@2$5@3$6@1$1@1$0#k0@2$9^3N1^2@2$5@3$6@1$1@1$0#k0@2$9^3N2?3cnt@2$5@2$8@1$2@1$1@1$0#8\1w@1$2@1$1@1$0#8@3$6@1$7@1$2@1$1@1$0#8@3$i0@2$hd?4segs^4^3?3cnt@2$c@1$2@1$1@1$0#8^1@2$5@3$6$h8@2$hf^2@2$b@1$0#k0?3cnt$h9@2$5@2$i3@1?3out^4@1$a@2$he^3@2$h7@1$0#k0Z@2$5@1$i1@1?3out^4>2bs@1$2@1$1@1$0#8>0@2$h5+1@1$h6@2$e@1$1@1$0#8^1>0@2$h5@1$h6@2$e@1$1@1$0#8^2@2$b@1$0#k0?3cntM7\1x@1$7?1AP@4$i4?1A?1f^7^3\2a'?1A@2$i2^1@1$a@2$h2^7@6$h4@2$h1@1$1@1$0#8^4@3$d~0@4$h0@1$1@1$0#k0@1$2@1$1@1$0#8^6^4~1~3~3@1$3$h3@1$3@2$4@1$1@1$0#k0$f@3$i5?4segs?2ec@1$a@2$h2^6@6$h4@2$h1@1$1@1$0#8^3@3$d~0@4$h0@1$1@1$0#k0@1$2@1$1@1$0#8^5^3~1~3~3@1$3$h3@1$3@2$4@1$1@1$0#k0$f").

(* [comment removed for export] *)
Inductive to_rd : A -> machine_state -> Prop :=
| trd_here : forall a ms, ReadPend a ms -> to_rd a ms
| trd_step : forall a ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_rd a ms' -> to_rd a ms.

(* [comment removed for export] *)

(* [comment removed for export] *)
Variable H_LH : forall a ms, LH a ms -> to_rd a ms.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


End Drain.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
