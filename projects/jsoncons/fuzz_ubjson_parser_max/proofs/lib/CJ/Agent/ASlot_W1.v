(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A MallocFacts_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_ASlot_W1 () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.ASlot_W1.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_malloc_enframe."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["1bool"; "1true"; "2and"; "2eq"; "3Z"; "4span_chk"; "4span_exit"; "4span_fn"; "5zseq"; "6size_class"; "7forallb"; "8add"; "8le"; "8lt"; "8mul"; "0cnt"]; ["0sc"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Section TA.
Context {R : Type}.
Variables (sc : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Definition ta_avz (st3 : mstate) (m3 : aptr) : Malloc.M R :=
activate_group m3 st3 (fun st4 mask =>
guard 40 (negb (mask =? 0)) (
ta_fin (decay_bounces (m_sizeclass (get_meta_rec st4 m3)) st4) m3 mask k) bail) bail.
Definition ta_act (st2 : mstate) (m2 : aptr) (mask : Z) : Malloc.M R :=
let mr2 := get_meta_rec st2 m2 in
let gai := match m_mem mr2 with Some _ => group_active_idx st2 (default (0%N,-1) (m_mem mr2)) | None => 0 end in
let '(st3, m3) :=
if Z.land mask (mask_upto gai) =? 0 then
if negb (optr_eqb (m_next mr2) (Some m2)) then
match m_next mr2 with
| Some mn => (set_active sc (Some mn) st2, mn)
| None => (st2, m2)
end
else
let cnt := gai + 2 in
let size := size_class (m_sizeclass mr2) * UNIT in
let span := UNIT + size * cnt in
let cnt := span_loop 300%nat cnt span size in
let cnt := if m_last_idx mr2 + 1 <? cnt then m_last_idx mr2 + 1 else cnt in
match m_mem mr2 with
| Some g => (set_group_active_idx g (cnt - 1) st2, m2)
| None => (st2, m2)
end
else (st2, m2) in
ta_avz st3 m3.
Definition ta_m (st1 : mstate) (m1 : aptr) : Malloc.M R :=
let mask := m_freed (get_meta_rec st1 m1) in
let '(st2, m2, mask) :=
let mr := get_meta_rec st1 m1 in
if (mask =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0) then
match m_next mr with
| Some mn => (set_active sc (Some mn) st1, mn, m_freed (get_meta_rec st1 mn))
| None => (st1, m1, mask)
end
else (st1, m1, mask) in
ta_act st2 m2 mask.
Lemma try_avail_eq st :
try_avail sc st k bail =
match active st sc with
| None => k st 0
| Some m =>
if negb (m_avail (get_meta_rec st m) =? 0) then ta_fin st m (m_avail (get_meta_rec st m)) k else
let step1 : option (mstate * aptr) :=
if m_freed (get_meta_rec st m) =? 0 then
let st1 := dequeue (LActive sc) m st in
match active st1 sc with None => None | Some m1 => Some (st1, m1) end
else
match m_next (get_meta_rec st m) with
| Some m1 => Some (set_active sc (Some m1) st, m1)
| None => None
end in
match step1 with
| None => if m_freed (get_meta_rec st m) =? 0 then k (dequeue (LActive sc) m st) 0
else SVis (EUndef UBadPtr) (fun _ => bail)
| Some (st1, m1) => ta_m st1 m1
end
end.
Proof. reflexivity. Qed.
End TA.
Section AS.
Context {R : Type}.
Variables (lay : layout_hook) (f : nat) (sc req : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Definition as_grp (st1 : mstate) : Malloc.M R :=
alloc_group R lay (alloc_slot lay f) st1 sc req (fun st2 go =>
match go with
| None => k st2 (-1)
| Some g =>
let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
queue (LActive sc) g st3 (fun st4 => k st4 0) bail
end) bail.
Definition as_k (st1 : mstate) (first : Z) : Malloc.M R :=
if negb (first =? 0) then k st1 (ctz32 first) else as_grp st1.
Lemma alloc_slot_S st : alloc_slot lay (S f) st sc req k bail = try_avail sc st as_k bail.
Proof. reflexivity. Qed.
End AS.
Fixpoint span_exit (fuel : nat) (span size : Z) : bool :=
match fuel with
| O => false
| S f => if Z.lxor span (span + size - 1) <? 4096 then span_exit f (span + size) size else true
end.
Definition span_fn (sc cnt : Z) : bool :=
span_exit 300 (16 + size_class sc * 16 * cnt) (size_class sc * 16).
Definition span_chk (sc : Z) : bool := forallb (span_fn sc) (zseq 2 32).
Lemma span_chk_true : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W1 "<'3'0&:'4&5&8+1+Q?%3221%73651(1%;3:21").
Proof. vm_compute. reflexivity. Qed.
Lemma span_fn_ok : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W1 "K'4'2&<+1r2%3221&=+Q@%2241%8241+2%9217+Q1%;291%=231'3'0&7r4r3%3221(1%73621p091p0?1pQ0I1pQ2J1").
Proof. intros sc cnt.
intros Hsc Hc.
pose proof (forallb_zseq span_chk 1 47 sc span_chk_true ltac:(lia) ltac:(lia)) as X. unfold span_chk in X.
exact (forallb_zseq (span_fn sc) 2 32 cnt X ltac:(lia) ltac:(lia)).
Qed.
Lemma span_exit_ok : ltac2:(TCodec.tc2 tcn__CJ_Agent_ASlot_W1 "Q4'4'2&<+1r2%3221&=+Q@%2241%8241+2%9217+Q1%;291%=231'3'0&6uY<&;+@&>&9r4%211%4215r3%6221%9281%<3;14(1%@3?21p0B1p0H1pQ0Q21pQ2Q31").
Proof. intros sc cnt. intros Hsc Hc. exact (span_fn_ok sc cnt Hsc Hc). Qed.
End CEIL_WRAP_1.
