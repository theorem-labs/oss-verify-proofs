(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export Q7S0.Mq1.
Import ListNotations.
Import QlEo_c1.Mq0.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Record PState := mkPS {
ps_m   : mstate;
ps_brk : Z;
ps_fa  : unit;
ps_so  : unit
}.
Definition set_m (v : mstate) (s : PState) := mkPS v (ps_brk s) (ps_fa s) (ps_so s).
Definition set_brk_ps (v : Z) (s : PState) := mkPS (ps_m s) v (ps_fa s) (ps_so s).
End RC__1.

Local Notation MP := (Ql2m.Mq3.M PState).
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Definition neg_errno (e : Z) : Z := 2^64 - e.

Definition MAP_FIXED_Z : Z := 16.

Inductive fixed_ans : Type := FxKept (e : Z) | FxDone | FxLost (e : Z).
Definition dec_mmap_fixed (addr len : Z) (rsp : resp) : option fixed_ans :=
match rsp with
| mkEffectU r [] [] [] [] [] => match errno_of r with Some e => Some (FxKept e) | None => None end
| mkEffectU r [] [] [(a, n)] [] [] =>
if bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len)) then
match errno_of r with
| Some e => Some (FxLost e)
| None => if bv_eqb r (Z_to_bv 64 addr) then Some FxDone else None
end
else None
| _ => None
end.

Definition dec_mprotect_rw (addr len : Z) (rsp : resp) : option range_ans :=
match dec_mprotect addr len rsp with
| Some (RgErr e) => if e =? ENOSYS then None else Some (RgErr e)
| Some (RgDone true) => Some (RgDone true)
| _ => None
end.

Definition ev_step (e : ev) : MP Z :=
match e with
| EBrk req =>
if req =? 0 then
(r <- msys (NBrk 0) dec_brk0 ;; mupd (set_brk_ps r) ;;; mret r)
else
(s <- mget ;;
a <- msys (NBrk req) (dec_brk (ps_brk s) req) ;;
match a with
| BrkGrown => mupd (set_brk_ps req) ;;; mret req
| BrkSame => mret (ps_brk s)
end)
| EMmap addr len prot flags =>
if negb (Z.land flags MAP_FIXED_Z =? 0) then
(a <- msys (NMmap addr len prot flags) (dec_mmap_fixed addr len) ;;
mret match a with FxKept e => neg_errno e | FxDone => addr | FxLost e => neg_errno e end)
else if prot =? 0 then
(a <- msys (NMmap addr len prot flags) (dec_mmap_none len []) ;;
mret match a with MmErr e => neg_errno e | MmOk x => x end)
else
(a <- msys (NMmap addr len prot flags) (dec_mmap len []) ;;
mret match a with MmErr e => neg_errno e | MmOk x => x end)
| EMunmap addr len =>
a <- msys (NMunmap addr len) (dec_munmap addr len) ;;
mret match a with RgErr e => neg_errno e | RgDone _ => 0 end
| EMprotect addr len prot =>
a <- msys (NMprotect addr len prot) (dec_mprotect_rw addr len) ;;
mret match a with RgErr e => neg_errno e | RgDone _ => 0 end
| EPeek _ _ _ => munr
| EUndef _ => munr
| EMremap old oldlen newlen flags =>

a <- msys (NMremap old oldlen newlen flags) (dec_mremap old oldlen newlen []) ;;
mret match a with MrErr e => neg_errno e | MrInPlace => old | MrMoved a => a end
end.

Fixpoint membed {R} (t : stree ev Z R) : MP R :=
match t with
| SRet r => mret r
| SVis e k => z <- ev_step e ;; membed (k z)
end.

Definition bptr : Type := (cptr * Z)%type.

Definition raw_malloc (n : Z) : MP (option bptr) :=
s <- mget ;;
'(st', p) <- membed (cmalloc (ps_m s) n) ;;
mupd (set_m st') ;;;
mret (match p with Some slot => Some (slot, fresh_off st' slot n) | None => None end).
Definition raw_free (p : bptr) : MP unit :=
s <- mget ;;
st' <- membed (cfree (ps_m s) (Some (fst p))) ;;
mupd (set_m st').

Definition raw_realloc (slot : cptr) (off n : Z) : MP (option bptr) :=
s <- mget ;;
'(st', r) <- membed (crealloc (ps_m s) slot off n) ;;
mupd (set_m st') ;;;
mret (match r with
| None => None
| Some RRSame => Some (slot, off)
| Some (RRNew b) => Some b
end).

Definition raw_calloc (m n : Z) : MP (option bptr) :=
s <- mget ;;
'(st', p) <- membed (ccalloc (ps_m s) m n) ;;
mupd (set_m st') ;;;
mret (match p with Some slot => Some (slot, fresh_off st' slot (m * n)) | None => None end).

Definition ptr_addr (s : PState) (p : bptr) : Z := conc (ps_m s) (fst p) + UNIT * snd p.

Definition ps_init (reserved : list (Z * Z)) : PState := mkPS (strip (minit 0 reserved)) 0 tt tt.
Definition reservedZ (segs : list Segment) : list (Z * Z) :=
map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p))) (segments_reserved segs).

End RC__2.
