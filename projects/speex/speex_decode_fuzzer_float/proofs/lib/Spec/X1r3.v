(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bo X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1ra X1qu X1ri.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Record PState := mkPS {
ps_m   : mstate;
ps_brk : Z;
ps_fa  : Z * Z;
ps_so  : stdout_st;
ps_hdr : gmap cptr Z
}.
Definition set_m (v : mstate) (s : PState) := mkPS v (ps_brk s) (ps_fa s) (ps_so s) (ps_hdr s).
Definition set_brk_ps (v : Z) (s : PState) := mkPS (ps_m s) v (ps_fa s) (ps_so s) (ps_hdr s).
Definition set_fa_ps (v : Z * Z) (s : PState) := mkPS (ps_m s) (ps_brk s) v (ps_so s) (ps_hdr s).
Definition set_so_ps (v : stdout_st) (s : PState) := mkPS (ps_m s) (ps_brk s) (ps_fa s) v (ps_hdr s).
Definition set_hdr_ps (v : gmap cptr Z) (s : PState) := mkPS (ps_m s) (ps_brk s) (ps_fa s) (ps_so s) v.

Local Notation MP := (X1qx.M PState).

Definition neg_errno (e : Z) : Z := 2^64 - e.

Definition MAP_FIXED_Z : Z := 16.

Inductive fixed_ans : Type := FxKept (e : Z) | FxDone | FxLost (e : Z).
Definition dec_mmap_fixed (addr len : Z) (rsp : resp) : option fixed_ans :=
match rsp with
| mkEffectU r [] [] [] [] _ => match errno_of r with Some e => Some (FxKept e) | None => None end
| mkEffectU r [] [] [(a, n)] [] _ =>
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

Definition ev_step (ceil : Z) (e : ev) : MP Z :=
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
(a <- msys (NMmap addr len prot flags) (dec_mmap_none ceil len []) ;;
mret match a with MmErr e => neg_errno e | MmOk x => x end)
else
(a <- msys (NMmap addr len prot flags) (dec_mmap ceil len []) ;;
mret match a with MmErr e => neg_errno e | MmOk x => x end)
| EMunmap addr len =>
a <- msys (NMunmap addr len) (dec_munmap addr len) ;;
mret match a with RgErr e => neg_errno e | RgDone _ => 0 end
| EMprotect addr len prot =>
a <- msys (NMprotect addr len prot) (dec_mprotect_rw addr len) ;;
mret match a with RgErr e => neg_errno e | RgDone _ => 0 end
| EPeek _ _ _ => munr
| EUndef _ => munr
end.

Fixpoint membed {R} (ceil : Z) (t : stree ev Z R) : MP R :=
match t with
| SRet r => mret r
| SVis e k => z <- ev_step ceil e ;; membed ceil (k z)
end.

Definition bptr : Type := (cptr * Z)%type.
Definition ptop (p : bptr) : bool := 0 <=? snd p.

Definition slot_top (cs : mstate) (c : cptr) : bool :=
match (s_slots cs) !! c with
| Some (g, _) => negb (m_maplen (get_meta_rec cs g) =? 0)
| None => false
end.

Definition enf_raw (hdr : gmap cptr Z) (cs : mstate) (c : cptr) : Z :=
match hdr !! c with
| None => Z.land (c_mmap_counter (s_ctx cs)) 255
| Some q => Z.land (q + 1) 255
end.
Definition real_off (hdr : gmap cptr Z) (cs : mstate) (c : cptr) (n : Z) : Z :=
match (s_slots cs) !! c with
| Some (g, _) => fold_off (enf_raw hdr cs c) ((get_stride (get_meta_rec cs g) - IB - n) / UNIT)
| None => 0
end.

Definition cont_q (c : cptr) : Z := (snd c - UNIT) / UNIT.

Definition new_containers (cs cs' : mstate) : list cptr :=
filter (fun c => slot_top cs' c && match (s_groups cs) !! c with None => true | Some _ => false end)
(map fst (map_to_list (s_groups cs'))).
Definition mark_conts (l : list cptr) (hdr : gmap cptr Z) : gmap cptr Z :=
fold_right (fun c h => <[c := cont_q c]> h) hdr l.

Definition new_top_slot (cs cs' : mstate) (c : cptr) : bool :=
slot_top cs' c && match (s_slots cs) !! c with None => true | Some _ => false end.
Definition prune_new (cs cs' : mstate) (hdr : gmap cptr Z) : gmap cptr Z :=
filter (fun kv : cptr * Z => negb (new_top_slot cs cs' (fst kv))) hdr.
Definition hdr_after (cs cs' : mstate) (hdr : gmap cptr Z) : gmap cptr Z :=
mark_conts (new_containers cs cs') (prune_new cs cs' hdr).

Definition raw_malloc (n : Z) : MP (option bptr) :=
s <- mget ;;
'(st', p) <- membed (s_ceil (ps_m s)) (cmalloc (ps_m s) n) ;;
let hdr1 := hdr_after (ps_m s) st' (ps_hdr s) in
match p with
| None => mupd (fun s0 => set_hdr_ps hdr1 (set_m st' s0)) ;;; mret None
| Some slot =>
if slot_top st' slot then
let off := real_off hdr1 st' slot n in
mupd (fun s0 => set_hdr_ps (<[slot := off]> hdr1) (set_m st' s0)) ;;; mret (Some (slot, off))
else
mupd (fun s0 => set_hdr_ps hdr1 (set_m st' s0)) ;;; mret (Some (slot, -1))
end.
Definition raw_free (p : bptr) : MP unit :=
s <- mget ;;
st' <- membed (s_ceil (ps_m s)) (cfree (ps_m s) (Some (fst p))) ;;
mupd (set_m st').

Definition ptr_addr (s : PState) (p : bptr) : Z := conc (ps_m s) (fst p) + UNIT * snd p.

Definition ps_init (ceil : Z) (reserved : list (Z * Z)) : PState :=
mkPS (strip (minit 0 ceil reserved)) 0 (0, 0) stdout_init ∅.

Definition argv_Z (argv : list (list byte)) : list (list Z) := map (map bv_unsigned) argv.
Definition reservedZ (segs : list Segment) : list (Z * Z) :=
map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p))) (segments_reserved segs).

