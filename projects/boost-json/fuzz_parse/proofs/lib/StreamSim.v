(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SimInv ExitSim CatSim WallSim.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14list37Corelib4Init5Logicm02eq3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypen97Segment3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsr8dmachine_stater86ms_gpr3h5LinuxProcessSemanticsfLinuxProcessSem3Runhg89sys_input3h5LinuxProcessSemanticsfLinuxProcessSem5Statehk16in_argm03andm02ex69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6CatSim~~~~~~ho46mstepsk16length37Corelib4Init5Peanoht02le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9StreamSim4Loop~~~~~~hua7lh_next69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7WallSim~~~~~~ij67to_wallhf7Z_to_bvk13nilk14prodhfbbv_unsignedk14Somek16optionhg8h0advance_past_svc46Stdlib6ZArith6BinInt1Zis52leis56of_natk14boolk14consk13natk14pairk14true01Z3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasejh28len_wordr8ems_svc_pendingr8h0ms_writable_byter88set_gpr0hg8capply_effecthk17MemCopyhk1aaccess_okbhk19mkEffectUhk1eread_bytes_map69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7ExitSim~~~~~~js57to_exithua5to_wr" s.   (* [comment removed for export] *)

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma in_arg1_sys_input : ltac2:(zQ "90!h9!jc!l9!n4!qe!uf!vf!hj4!hmf>4segs@1$2$4>2ms$5>2x8@1$1@1$0#k0@3$3@1$1@1$0#k0@2$8@3$7^3^2^1N1@2$6^2N1").
Proof. reflexivity. Qed.

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

Fixpoint wseg_ok (segs : list Segment) (a : word) (n : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match find_segment segs (bv_unsigned a) 1 with
      | Some seg =>
          (seg_writable seg
           && match segment_byte_at (seg_bytes seg)
                      (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) with
              | Some _ => true
              | None => false
              end
           && wseg_ok segs (a + 1) n')%bool
      | None => false
      end
  end.

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
Inductive chunks (cnt : word) : InputStream -> list (list byte) -> InputStream -> Prop :=
| chunks_nil : forall s, chunks cnt s [] s
| chunks_cons : forall s bs blocks s'',
    (1 <= Z.of_nat (length bs))%Z ->
    (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
    fst (stream_take s (length bs)) = bs ->
    chunks cnt (snd (stream_take s (length bs))) blocks s'' ->
    chunks cnt s (bs :: blocks) s''.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Loop.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!l9!qe@1$0$1").
Variable LH : ltac2:(zQ "10!uf>0$0P").
Variable cnt : word.
(* [comment removed for export] *)
Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.

(* [comment removed for export] *)
Definition lh_next : ltac2:(zQ "10!uf>2ms$0P") := ltac2:(zQ "40!uf!hn9!hnf!hrd\2ms$0@2$2$0\3ms'$0@2$1@3$3?4segs^2^1@1?2LH^1").

(* [comment removed for export] *)
Definition WrPend : ltac2:(zQ "40!l9!h9!uf!jc>2bs@1$0@1$3@1$1#8>2ms$2P") := ltac2:(zQ "a0!h9!jc!hs7!l9!hn9!hu4!uf!iib!in0!inb\2bs@1$3@1$1@1$0#8\2ms$6@2$4@2$5N1@2$2@1$1@1$0#8^2@5$8?4segs@2$9@1$0#k0+1^1^2$7").

(* [comment removed for export] *)
Inductive to_wr (bs : list byte) : machine_state -> Prop :=
| twr_here : forall ms, WrPend bs ms -> to_wr bs ms
| twr_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wr bs ms' -> to_wr bs ms.

(* [comment removed for export] *)
Definition ReadPend : ltac2:(zQ "10!uf>2ms$0P") := ltac2:(zQ "i33!h9!jc!l9!hn9!n4!io5!iob!hnf!vf!inb!ip2!iq0!hs7!iq7!ir0!itd!iu3!iud!iv4!ivb!jg1!jg8!jgf!jk1!uf!jkd!jle!jn2!jnd!jod!jp8!jq6!jr3!jvf!kga&@2$6@1$1@1$0#k0@1$2@1$1@1$0#8&@2$6@1$1@1$0#k0@1$1@1$0#k0&@1$5~1\2ms$h8@2$7@1$1@1$0#k0\3buf@1$1@1$0#k0@2$7@1$1@1$0#k0\2x8@1$1@1$0#k0@2$3@3$4@1$d@1$1@1$0#k0@1$h9^3@2$b@1$1@1$0#k0^1@2$3@3$4$h6@2$a@1$0#k0^1+jf@2$3@3$4@1$1@1$0#k0@2$8^3N0@2$9@1$0#k0Z@2$3@3$4@1$1@1$0#k0@2$8^3N1^2@2$3@3$4@1$1@1$0#k0@2$8^3N2?3cnt@2$3@2$7@1$2@1$1@1$0#8\1w@1$2@1$1@1$0#8@3$4@1$d@1$2@1$1@1$0#8@3$i0@2$ha?4segs^4^3?3cnt@2$b@1$2@1$1@1$0#8^1@2$3@3$4$h1@2$he^2@2$a@1$0#k0?3cnt$h5@2$3@3$i1?4segs@2$9@1$0#k0Z@1$e@2$hb^3@2$9@1$0#k0Z>2bs@1$2@1$1@1$0#8>0@2$f+1@1$h0@2$c@1$1@1$0#8^1>0@2$f@1$h0@2$c@1$1@1$0#8^2@2$a@1$0#k0?3cnt@2$i2^3@1$e@2$hc^6@6$hf@2$h7@1$1@1$0#8^3@3$h2~0@4$h4@1$1@1$0#k0@1$2@1$1@1$0#8^5^3@1$5~0~2~2@1$5$hd@1$5@2$6@1$1@1$0#k0$h3").

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Inductive to_rd : machine_state -> Prop :=
| trd_here : forall ms, ReadPend ms -> to_rd ms
| trd_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_rd ms' -> to_rd ms.

(* [comment removed for export] *)
Hypothesis H_LH : forall ms, LH ms -> to_rd ms.

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


End Loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
