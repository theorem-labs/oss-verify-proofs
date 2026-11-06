(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From stdpp Require gmap. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require ITree Nodes Decode. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec Require Monad. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require RunP.
Module Prog.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require ITree Nodes Decode. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.MState OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Mem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.Exec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.ITree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Decode.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec Require Monad. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004.Prelim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Monad OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004.STree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029.Malloc.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
Record PState := mkPS {
  ps_m   : mstate;        (* [comment removed for export] *)
  ps_brk : Z;             (* [comment removed for export] *)
  ps_fa  : Z * Z;         (* [comment removed for export] *)
  ps_so  : unit           (* [comment removed for export] *)
}.
Definition set_m (v : mstate) (s : PState) := mkPS v (ps_brk s) (ps_fa s) (ps_so s).
Definition set_brk_ps (v : Z) (s : PState) := mkPS (ps_m s) v (ps_fa s) (ps_so s).
Definition set_fa_ps (v : Z * Z) (s : PState) := mkPS (ps_m s) (ps_brk s) v (ps_so s).
Definition set_so_ps (v : unit) (s : PState) := mkPS (ps_m s) (ps_brk s) (ps_fa s) v.
End CEIL_WRAP_1.


Local Notation MP := (Monad.M PState).
Section CEIL_WRAP_2.
Context {RUNp : RunP}.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition neg_errno (e : Z) : Z := 2^64 - e.

Definition MAP_FIXED_Z : Z := 16.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition dec_mprotect_rw (addr len : Z) (rsp : resp) : option range_ans :=
  match dec_mprotect addr len rsp with
  | Some (RgErr e) => if e =? ENOSYS then None else Some (RgErr e)
  | Some (RgDone true) => Some (RgDone true)
  | _ => None
  end.

(* [comment removed for export] *)
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
  | EPeek _ _ _ => munr      (* [comment removed for export] *)
  | EUndef _ => munr         (* [comment removed for export] *)
  end.

Fixpoint membed {R} (t : stree ev Z R) : MP R :=
  match t with
  | SRet r => mret r
  | SVis e k => z <- ev_step e ;; membed (k z)
  end.

(* [comment removed for export] *)
Definition bptr : Type := (cptr * Z)%type.

Definition fresh_off (cs : mstate) (slot : cptr) (n : Z) : Z :=
  match (s_slots cs) !! slot with
  | Some (g, idx) =>
      let mr := get_meta_rec cs g in
      fold_off (Z.land (c_mmap_counter (s_ctx cs)) 255) ((get_stride mr - IB - n) / UNIT)
  | None => 0
  end.

Definition raw_malloc (n : Z) : MP (option bptr) :=
  s <- mget ;;
  '(st', p) <- membed (cmalloc (ps_m s) n) ;;
  mupd (set_m st') ;;;
  mret (match p with Some slot => Some (slot, fresh_off st' slot n) | None => None end).
Definition raw_free (p : bptr) : MP unit :=
  s <- mget ;;
  st' <- membed (cfree (ps_m s) (Some (fst p))) ;;
  mupd (set_m st').

(* [comment removed for export] *)
Definition ptr_addr (s : PState) (p : bptr) : Z := conc (ps_m s) (fst p) + UNIT * snd p.

(* [comment removed for export] *)
Definition ps_init (reserved : list (Z * Z)) : PState :=
  mkPS (strip (minit secret_val reserved)) 0 (0, 0) tt.   (* [comment removed for export] *)

Definition argv_Z (argv : list (list byte)) : list (list Z) := map (map bv_unsigned) argv.
Definition reservedZ (segs : list Segment) : list (Z * Z) :=
  map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p))) (segments_reserved segs).
End CEIL_WRAP_2.



End Prog.
From Stdlib Require ZArith NArith List Lia Bool Permutation. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Specs Run. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0044. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Module KInv.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require Import ITree Nodes Decode.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec Require Monad. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0044. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004.Prelim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Monad OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0044.MSafe OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004.STree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029.Malloc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046.Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_KInv () := "C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstC35stdpp4base6LookupC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_transC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsI47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsI47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC4ELinuxProcessSemantics?LinuxProcessSem5State5m_tidC4ELinuxProcessSemantics?LinuxProcessSem5State7m_stdinI47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2CJ3Lib5Nodes7vm_onlyC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State;InputStream00".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive brk_phase : Type :=
| BPUntried                 (* [comment removed for export] *)
| BPQueried (cur : Z)       (* [comment removed for export] *)
| BPGuard (cur : Z)         (* [comment removed for export] *)
| BPLive                    (* [comment removed for export] *)
| BPDead.                   (* [comment removed for export] *)

Record mled : Type := mkLed {
  ld_resv : list (Z * Z);          (* [comment removed for export] *)
  ld_groups : list (Z * Z);        (* [comment removed for export] *)
  ld_metas : list (Z * Z * Z);     (* [comment removed for export] *)
  ld_brkreg : option (Z * Z);      (* [comment removed for export] *)
  ld_brk : brk_phase;
  ld_live : list cptr              (* [comment removed for export] *)
}.

Definition led_init (resv : list (Z * Z)) : mled := mkLed resv [] [] None BPUntried [].
Definition set_groups (v : list (Z * Z)) (L : mled) := mkLed (ld_resv L) v (ld_metas L) (ld_brkreg L) (ld_brk L) (ld_live L).
Definition set_metas (v : list (Z * Z * Z)) (L : mled) := mkLed (ld_resv L) (ld_groups L) v (ld_brkreg L) (ld_brk L) (ld_live L).
Definition set_brkreg (v : option (Z * Z)) (L : mled) := mkLed (ld_resv L) (ld_groups L) (ld_metas L) v (ld_brk L) (ld_live L).
Definition set_brkph (v : brk_phase) (L : mled) := mkLed (ld_resv L) (ld_groups L) (ld_metas L) (ld_brkreg L) v (ld_live L).
Definition set_live (v : list cptr) (L : mled) := mkLed (ld_resv L) (ld_groups L) (ld_metas L) (ld_brkreg L) (ld_brk L) v.

(* [comment removed for export] *)
Definition lranges (L : mled) : list (Z * Z) :=
  ld_resv L
  ++ map (fun g => (fst g, round_up_pg (snd g))) (ld_groups L)
  ++ map (fun m => (fst (fst m), round_up_pg (snd (fst m)))) (ld_metas L)
  ++ match ld_brkreg L with Some (b, l) => [(b + PGSZ, round_up_pg l - PGSZ)] | None => [] end.

(* [comment removed for export] *)
Definition lbrk_pages_ok (L : mled) (lo len : Z) : bool :=
  (0 <? lo) && (lo + len <=? alloc_ceiling) && ranges_free (lranges L) lo len.

Definition MAPF : Z := MAP_PRIVATE + MAP_ANON.
Definition MAPFX : Z := MAP_PRIVATE + MAP_ANON + MAP_FIXED.
Definition LEN_MAX : Z := 2^63.   (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint g_remove (a : Z) (l : list (Z * Z)) : list (Z * Z) :=
  match l with
  | [] => []
  | y :: l' => if fst y =? a then l' else y :: g_remove a l'
  end.
Definition bump_meta (a : Z) (m : Z * Z * Z) : Z * Z * Z :=
  let '(b, l, k) := m in if b + (1 + k) * PGSZ =? a then (b, l, k + 1) else m.
Fixpoint ap_remove (c : aptr) (l : list aptr) : list aptr :=
  match l with
  | [] => []
  | y :: l' => if aptr_eqb y c then l' else y :: ap_remove c l'
  end.

(* [comment removed for export] *)
Definition brk_quiet (L : mled) : Prop :=
  match ld_brk L with BPQueried _ | BPGuard _ => False | _ => True end.

Definition event_pre (L : mled) (e : ev) : Prop :=
  match e with
  | EBrk req =>
      (req = 0 /\ ld_brk L = BPUntried)
      \/ (exists cur, ld_brk L = BPQueried cur /\ req = round_up_pg cur + 2 * PGSZ)
      \/ (exists b l, ld_brk L = BPLive /\ ld_brkreg L = Some (b, l) /\ req = b + l + PGSZ)
  | EMmap a len prot flags =>
      (brk_quiet L /\ a = 0 /\ flags = MAPF /\ (prot = PROT_NONE \/ prot = PROT_RW) /\ 0 < len < LEN_MAX)
      \/ (exists cur, ld_brk L = BPGuard cur /\ a = round_up_pg cur /\ len = PGSZ /\ prot = PROT_NONE /\ flags = MAPFX)
  | EMunmap a len => brk_quiet L /\ exists l, In (a, l) (ld_groups L) /\ (len = l \/ len = round_up_pg l)
        (* [comment removed for export] *)
  | EMprotect a len prot =>
      brk_quiet L /\ len = PGSZ /\ prot = PROT_RW /\
      exists b l k, In (b, l, k) (ld_metas L) /\ a = b + (1 + k) * PGSZ /\ (2 + k) * PGSZ <= round_up_pg l
  | EPeek _ _ _ => False
  | EUndef _ => False
  end.

Definition answer_ok (L : mled) (e : ev) (z : Z) : bool :=
  match e with
  | EBrk req =>
      if req =? 0 then brk0_answer_ok z
      else match ld_brk L with
           | BPQueried cur => brk_answer_ok cur req z && (negb (z =? req) || lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ))
           | _ => match ld_brkreg L with
                  | Some (b, l) => brk_answer_ok (b + l) req z && (negb (z =? req) || lbrk_pages_ok L (b + l) PGSZ)
                  | None => false
                  end
           end
  | EMmap a len prot flags =>
      if Z.land flags MAP_FIXED =? 0 then mmap_answer_ok (lranges L) len z
      else mmap_fixed_answer_ok a z
  | EMunmap _ _ => munmap_answer_ok z
  | EMprotect _ _ _ => mprotect_answer_ok z
  | _ => false
  end.

Definition event_post (L : mled) (e : ev) (z : Z) : mled :=
  match e with
  | EBrk req =>
      if req =? 0 then set_brkph (BPQueried z) L
      else if z =? req then
             match ld_brk L with
             | BPQueried cur => set_brkph (BPGuard cur) L
             | _ => match ld_brkreg L with
                    | Some (b, l) => set_brkreg (Some (b, l + PGSZ)) L
                    | None => L
                    end
             end
           else set_brkph BPDead L
  | EMmap a len prot flags =>
      if Z.land flags MAP_FIXED =? 0 then
        if is_err z then L
        else if prot =? PROT_NONE then set_metas ((z, len, 0) :: ld_metas L) L
        else set_groups ((z, len) :: ld_groups L) L
      else set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)
  | EMunmap a len => set_groups (g_remove a (ld_groups L)) L
  | EMprotect a len prot =>
      if (z =? 0) || (z =? TWO64 - ENOSYS) then set_metas (map (bump_meta a) (ld_metas L)) L else L
  | _ => L
  end.

(* [comment removed for export] *)
Fixpoint ctree_ok {R} (L : mled) (t : stree ev Z R) (Post : mled -> R -> Prop) : Prop :=
  match t with
  | SRet r => Post L r
  | SVis e k => event_pre L e /\ forall z, answer_ok L e z = true -> ctree_ok (event_post L e z) (k z) Post
  end.

(* [comment removed for export] *)
Inductive cpath {R} : mled -> stree ev Z R -> mled -> R -> Prop :=
| cpath_ret L r : cpath L (SRet r) L r
| cpath_vis L e k z L' r :
    answer_ok L e z = true -> cpath (event_post L e z) (k z) L' r -> cpath L (SVis e k) L' r.

(* [comment removed for export] *)
Inductive creach : mstate -> mled -> Prop :=
| creach_init resv : creach (strip (minit secret_val resv)) (led_init resv)   (* [comment removed for export] *)
| creach_malloc cs L n L' cs' r :
    creach cs L -> 0 <= n -> cpath L (cmalloc cs n) L' (cs', r) ->
    creach cs' (match r with Some c => set_live (c :: ld_live L') L' | None => L' end)
| creach_free cs L c L' cs' :
    creach cs L -> In c (ld_live L) -> cpath L (cfree cs (Some c)) L' cs' ->
    creach cs' (set_live (ap_remove c (ld_live L')) L').

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition went (b n : Z) : word * word := (wz b, wz n).
Definition wwZ (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (snd e)).
Definition elo (e : word * word) : Z := bv_unsigned (fst e).
Definition ehi (e : word * word) : Z := bv_unsigned (fst e) + bv_unsigned (snd e).

(* [comment removed for export] *)
Definition wcov (maps : list (word * word)) (lo hi : Z) : Prop :=
  forall x, lo <= x < hi -> exists e, In e maps /\ elo e <= x < ehi e.

(* [comment removed for export] *)
Definition edisj (e1 e2 : word * word) : Prop := ehi e1 <= elo e2 \/ ehi e2 <= elo e1.
Inductive pwdisj : list (word * word) -> Prop :=
| pwdisj_nil : pwdisj []
| pwdisj_cons e l : (forall e', In e' l -> edisj e e') -> pwdisj l -> pwdisj (e :: l).
Definition vmwf (maps : list (word * word)) : Prop :=
  (forall e, In e maps -> elo e < ehi e <= 2^64) /\ pwdisj maps.

(* [comment removed for export] *)
Definition brk_disj (L : mled) (b n : Z) : Prop :=
  forall b0 l0, ld_brkreg L = Some (b0, l0) -> b + n <= b0 + PGSZ \/ b0 + l0 <= b.

(* [comment removed for export] *)
Record KL (L : mled) (pbrk : Z) (mo : Model) : Prop := mkKL {
  kl_minv : minv mo;
  kl_halt : m_halted mo = None;
  kl_wf : vmwf (vm_maps (m_vmmaps mo));
  kl_resv : ld_resv L = map wwZ (vm_reserved (m_vmmaps mo));
  kl_resv_top : forall e, In e (vm_reserved (m_vmmaps mo)) -> ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo));
  kl_start : 0 < bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) mod PGSZ = 0
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) <= bv_unsigned (vm_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= alloc_ceiling;
  kl_groups : forall b l, In (b, l) (ld_groups L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l);
  kl_metas : forall b l k, In (b, l, k) (ld_metas L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
      /\ 0 <= k /\ (1 + k) * PGSZ <= mmap_len l
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l)
      /\ (forall q, 1 + k <= q -> (q + 1) * PGSZ <= mmap_len l ->
            exists e, In e (vm_noaccess (m_vmmaps mo)) /\ elo e <= b + q * PGSZ /\ b + q * PGSZ + PGSZ <= ehi e);
  kl_distinct : List.NoDup (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L));
  kl_brkreg : forall b l, ld_brkreg L = Some (b, l) ->
      0 < b /\ b mod PGSZ = 0 /\ 2 * PGSZ <= l /\ l mod PGSZ = 0 /\ b + l <= alloc_ceiling
      /\ wcov (vm_maps (m_vmmaps mo)) (b + PGSZ) (b + l);
  kl_phase : match ld_brk L with
      | BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
      | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
      | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
          /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_ceiling
          /\ (exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
          /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
          /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
      | BPDead => True
      end }.

(* [comment removed for export] *)
Definition frame_ok (G : PState -> Model -> Prop) : Prop :=
  forall s s' mo mo', ps_fa s' = ps_fa s -> ps_so s' = ps_so s -> vm_only mo mo' -> G s mo -> G s' mo'.

Lemma vm_only_refl : forall mo, vm_only mo mo.
Proof.
ltac2:(KReplay.run1 (kr_t_KInv ()) ["CEIL_WRAP_1"] "h02mop;1p;2p;3p;4p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000cR1p4p710p8P0P1p4p7210p8P0p1001@p4p7210p8p1001Tp4p70p1002Dp4p710R0p8g002bR1p4p70P0p8g003Pj10Tg0045j1?Tg004Sj1;Tg0056j25Tg005Vj1>Tg0066j1<Tg006jj31Tg007Dj1:Tg0087j19Tg008Yj16Tg009Pj17Tg00:Dj18Tg00;:j24Tg00;Uj22Tg00;oj43Tg00<Jj2=Tg00=Cg00>9#0#0#0#0#0#0#?#;R0g00>^'5#>R2f0R3#<R4;14%:3R5=115R6%90R0%63R7;17R8%73R9=109R:g00?VR;%83R<;1<R='4R>'4R?'41224P6P?1215P8P>1207P:P=120912;<C3C3C3C31=33eW0o"). Qed.
Lemma vm_only_trans : forall a b c, vm_only a b -> vm_only b c -> vm_only a c.
Proof.
ltac2:(KReplay.run1 (kr_t_KInv ()) ["CEIL_WRAP_1"] "h01Hh12H0h22H1h32H2h42H4h52H5h62H6h72H7h82H3h92H8h:1ah;1bh<1cp;2p;1p;3p;6p;4p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000cR1p4p710p8P0P1p4p7210p8P0p1001@p4p7210p8p1001Tp4p70g002DR0p4p710R1p8g002bR2p4p70P1p8g00<Jj24Tg003Pj1>Tg0045j1HTg004Sj1FTg0056j2JTg005Vj1ITg0066j16Tg006jj31Tg007Dj12Tg0087j1ETg008Yj13Tg009Pj10Tg00:Dj15Tg00;:R1j2;TP0j6?Tg00;oj4@Tf1R0f0R3512p=7f2R4%30;13p==g00?VR5%50;13p=8f3R6%04;10/;3p=91;03,;4p=A%539150p=<A1640/;3p=:%339140p=D%039140p=C%00=143p=BA1503p=Gg00=CR71440P1g00>9#>#>#>#>#>#>#H#FR8g00>^'J#IR9%64%6631%24%26'7%E8R8%367=4P8P4%06%56,84C93A1464f5R4/46[P3f4#6%64519%24f6R6#2R:'7%36R;9=84P8P4%06R<%56R=,84C93AP1f7R>#2,7:P8P;%3>P8P<%0>1<=>C:C:14>6f9R6/4>[P3f8#2%26'7P8%36f:R>#3R=P8P6%0>R<%5>R;,86C9C:P1f;R:9D8=P8P<%0:1<;:C:14:>f=R>/4:[P3f<%3>5=8P8P>f>R:#0R;%5:R<,8>C9P1f?R=9C8;1<<=14=:fAR:/4=[P3f@%0:5B8fBR=#5R<,8:14=:P1%6=fCR;#6519%2=%2;'7%3;9=8=P8P=%0;1<<;C93AfER</4;P3fD#6%6<519%2<fFR;#2R?'7%3;R@9=8<P8P<%0;RA%5;RB,8<C93AP1fGR<#2,7?P8P@%3<P8PA%0<1<B<C:C:fIRB/4<P3fH#2%2B'7P8%3BfJR<#3RAP8PB%0<R@%5<R?,8BC9C:P1fKRB9D8AP8P@%0B1<?BC:fMR?/4BP3fL%3?5=8P8P?fNRB#0R@%5BRA,8?C9P1fOR19C8@1<A1fQRA/41P3fP%0A5B8fRR1#5R@,8A%61RAfTR?#6RC519%21RD%2?RE'7RF%31RG%3?RH518RI%01RJ%0?RK518RL%5?RM,G@RN';RO';RP';P9PAfSRA#6PCP>PBE?PFPPP2PD%2APEP6P<E?PIPOP8PG%3APHP4P;E?PLPNP8PJ%0APKP0P=E?P5P@%5APMP3P:E?C@C@C@C@14?1eW9W7P0P3O2n2001000000121000000W7W6P0P3O2n2001000000121000000W6W5P0P3O2n2001000000121000000W5W4P0P3O2n2001000000121000000W4W8W3P0P3O2n2001000000121000000W3W2P0P3O2n2001000000121000000W2W1P0P3O2n2001000000121000000W1W0P0P3O2n2001000000121000000W0X<7X;7W:o"). Qed.

(* [comment removed for export] *)
Definition ev_step_post (L : mled) (e : ev) (G : PState -> Model -> Prop) (s0 : PState)
  : Z -> PState -> Model -> Prop :=
  fun z s mo => answer_ok L e z = true /\ KL (event_post L e z) (ps_brk s) mo /\ G s mo
                /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0.
End CEIL_WRAP_1.


(* [comment removed for export] *)

End KInv.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Specs Run. From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
Module KStep.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require ITree Nodes Decode. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Mh_0039.MState OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.ITree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Nodes OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib.Decode.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec Require Monad. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0044. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004.Prelim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Monad OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0044.MSafe OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0004.STree OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0029.Malloc OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046.Prog OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Spec.Mh_0046.KInv.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_KStep () := "C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstC35stdpp4base6LookupC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_transC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsK47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive02I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z9land_onesC47Corelib4Init5Logic8eq_ind_rI46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4aptrC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib2CJ4Spec7Mh_00045STree5stree00C1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00c79OSSVerify5KrLib2CJ4Spec7Mh_00464Prog6membedC1?~~~~~~~~~~~~~~~C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4optrC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4cptrC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ4Spec7Mh_00464Prog4bptrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula07K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C56Stdlib6ZArith6BinInt1Z;mod_opp_l_zK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr03c79OSSVerify5KrLib2CJ4Spec7Mh_00465KStep9land_4095C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc;round_up_pgC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C79OSSVerify5KrLib2CJ4Spec7Mh_00296Malloc4PGSZC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ4Spec7Mh_00465KStep7PGSZ_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC46Stdlib6ZArith4ZdivAZ_div_mod_eq_fullC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_neg_boundI47Corelib4Init5Logic3and00C56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC69OSSVerify5KrLib2CJ3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr04C4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op205C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeK47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00c79OSSVerify5KrLib2CJ4Spec7Mh_00465KStep<page_size_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib6Decode>mmap_len_boundC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv:Z_mod_multC69OSSVerify5KrLib2CJ3Lib6Decode8mmap_lenC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib2CJ3Lib7Mh_00396MState<unsigned_litC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02c79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv2wzC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2CJ3Lib4RunPCalloc_ceiling_rangeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib4RunP=alloc_ceilingC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07I47Corelib4Init5Logic4True00c79OSSVerify5KrLib2CJ4Spec7Mh_00465KStep;unsigned_wzC1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00K47Corelib4Init9Datatypes4prod01c79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv4wentC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv3eloC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndc79OSSVerify5KrLib2CJ4Spec7Mh_00464KInv3ehiC1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma PGSZ_eq : PGSZ = 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_KStep ()) ["CEIL_WRAP_1"] "p;1p;2p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000cR1p4p710p8P0P1p4p7210p8P0p1001@p4p7210p8p1001Tp4p70p1002Dp4p710R0p8p1002bp4p70P0p8g003Pj13Tg003nj22Tg004Hj11Tf0#1#1p=0g004mg005K#0#0#0#0#0#0#3'2o"). Qed.
Lemma page_size_eq : page_size = 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_KStep ()) ["CEIL_WRAP_1"] "p;1p;2p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000cR1p4p710p8P0P1p4p7210p8P0p1001@p4p7210p8p1001Tp4p70p1002Dp4p710R0p8p1002bp4p70P0p8g003Pj13Tg003nj22Tg004Hj11Tf0#1#1p=0g004mg005K#0#0#0#0#0#0#3'2o"). Qed.

Lemma land_4095 : forall x, Z.land x 4095 = x mod 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_KStep ()) ["CEIL_WRAP_1"] "h07__arithh14__ffh28__varmaph35__with41xh51zp;1p;2p;3p;4p;7p;6p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000cR1p4p710p8P0P1p4p7210p8P0p1001@p4p7210p8p1001Tp4p70p1002Dp4p710R0p8p1002bp4p70P0p8g004Hj11Tg003Pj12Tg0060j1=Tg006Uj2HTg0072j23Tg007Rj34Tg003nj25Tg007lj1;Tg008Jj2:Tg008hj17Tg009Hj18Tg009hj19Tg00:Fj1GTg00:dj1FTg00;Oj26Tg00<2j4CTg00<]j7BTg00=Aj2?Tg00=cj2>Tg00>Oj3@Tg00>nj4ATg00?`j2<Tg00@<j3DTg00@_j6ETf0R0#1#1p=0g004mR1P1g005KR2#1R3#2%=2#0#2R2'H,30f1R4%13#0#0#0#0#0#2R3'39410X511303,51%;2,:0g00A=R3#7%83%91%G1%F1R3g00Aig00BHR5P5g00BhR5P1g00CHR6,61g00Cf1612CCg00DMFB1?35P0f2R5g00DmR3g00EMR7'51>05=437dA@164CAb1b2b31<62P0b09D02EEW4o"). Qed.

Lemma round_up_pg_aligned : forall x, x mod 4096 = 0 -> round_up_pg x = x.
Proof.
ltac2:(KReplay.run1 (kr_t_KStep ()) ["CEIL_WRAP_1"] "h04__x1h17__arithh24__ffh36__sat0h48__varmaph55__with64__x2h71zh81Hh92Hxh:6__sat1h;1xp;1p;2p;3p;6p;4p;7p;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710R3p8P0P2p4p7210p8P0p1001@R0p4p7210R2p8p1001Tp4p70p1002Dp4p710R4p8p100Emp4p70R5p100Fmp4p710p8P5p100Gop4p710p8P5p100HMp60721000R6p8P5p100IMR7p4p710p8P5P7p4p7210p8P5p100IfR7p4p710R8p8P5P7p4p741110p8P5p100J?p4p73110p8P5P2p8P5P0p4p73110p8p100JQp4p70P6p8p1002bp4p70P4p8p100KQp4p70R4P1p8P4P6p8P4p100LQp607000p8P4P3p8P4P8p8P4P0p4p710p8g004Hj19Tg003Pj1>Tg0072j24Tg00MOj15Tg00Mlj2XTg008Jj2CTg00NIj2;Tg007Rj32Tg00Nfj2<Tg008hj1GTg009Hj1cTg009hj1`Tg00:Fj1]Tg00:dj1ZTg00;Oj2DTg00OWj6WTg00=Aj2VTg003nj2STg00=cj2RTg00>Oj3QTg00>nj4PTg00P;j1OTg00PYj2NTg00Q:j1LTg00QYj2@Tg00RBj3KTg00Rkj3JTg00STj2ITg00T@j3MTg00T`j2ATg00U>j2BTg00Uaj1HTg00VCj4TTg00Vhj4UTg00WFj2bTg00Wij3aTg0060j1=Tg00XLj1_Tg00@_j6ETg00YPj1\Tg00?`j2[Tg00<2j4FTg00<]j7YTg00ZWj8^Tf0R0#9#9p=6g004mR4g00CHR8720p=31[80p=0P4f1R3g00[;P0CFp=:P3g00AiR6g00BHR1P1g00BhR5P0g00DMFYp=1f3R2P6P1P1P5f2R7P3P0G^p=7P4P3g00CfP0CFp=?%=0#=p=8g005KR9#9R:#9#6#6#6#6#6#>R;,40#3P4P;%57%>9,X0'C,;7=247X74P4%53R</4;R=1;70=247X74P3P;1<3;R>%03%0;R?142;R@#0[[RAg00A=RB#GRC%cBRD%`4RE%]4RF%Z4RGP6P1P1P51D4;R61D48RH':,1GEW1VG5R5P0P7g00DmRIg00EMRJ'S1R07=2IJdAQ483CPR8b2b4b5%3;g00[b[P0b1b3P>PA%O9,N4g00\?RA#L,@45K41@4A5J4g00\^'I=MBCRCPD1A43PFPG1B49RB/:H,1GRA%H1R1PAC7P5P8b2b4b5X04%30%33[^04P0P@P7O2b1b3CT%3=1<7;%07f4/4;#0\?[%52R=/<;%0=f5R=#5/4;R;#0\?[PCPDP41A47P3PECUPFPGPG1b4B,?H,1GP1PG1?H6,1GP11B4:R:,?H,1GC7C7P1PG1::H,1GP1Aa4B:/:B,1GC7C7P5P8b2b4b5X04X64%50#0%02\?[%371;72=247[[^04^64P0P;P=P3P2O4b1b3b:b8%=9#8#8#8#8#8#>,C<%_<EEg00]Jg00^JEE%\3=243eW9X;4o"). Qed.

Lemma round_up_pg_eq : forall x, round_up_pg x = page_round_up_Z x.
Proof.
ltac2:(KReplay.run1 (kr_t_KStep ()) ["CEIL_WRAP_1"] "h01zh12H0h23H10h33H16h47__arithh54__ffh64__p1h76__sat5h86__sat6h96__sat7h:8__varmaph;5__with<4__x1h=4__x2h>4__x3h?4__x4h@4__x5hA4__x6hB4__x7hC1HhD2H1hE3H11hF3H12hG3H13hH3H14hI3H15hJ3H17hK3H18hL3H19hM2H2hN3H20hO2H3hP2H4hQ2H5hR2H6hS2H7hT2H8hU2H9hV6__sat4hW6__sat8hX6__sat9hY1xp&0p;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710R3p8P0P2p4p7210p8P0p1001@R0p4p7210R2p8p1001Tp4p70p1002Dp4p710R4p8p100Emp4p70R5p100Fmp4p710p8P5p100Gop4p710p8P5p100HMp60721000R6p8P5p100IMR7p4p710p8P5P7p4p7210p8P5p100IfR7p4p710R8p8P5P7p4p741110p8P5p100J?p4p73110p8P5P2p8P5P0p4p73110p8p100JQp4p70P6p8p1002bp4p70P4p8p100KQp4p70R4P1p8P4P6p8P4p100LQp607000p8P4P3p8P4P8p8P4P0p4p710p8g004Hj1JTg003Pj1VTg00MOj14Tg00Mlj2RTg008Jj2]Tg00NIj21Tg00_Lj23Tg00_ij2FTg0072j20Tg008hj1lTg009Hk108Tg009hk107Tg00:Fk106Tg00:dk104Tg00;Oj2PTg00=Aj2|Tg003nj2eTg00=cj2vTg007Rj3QTg00>Oj3sTg00>nj4rTg00`Fj2=Tg00`bj3ij2STg00aIj2cTg0060j1ATg00Nfj2LTg00b0j2GTg00baj2TTg00cBj1kTg00c[j2bTg00?`j2DTg00dBj2CTg00d]j2aTg00eCj2`Tg00eij2_Tg00fhk205Tg00Q:j19Tg00QYj2jTg00gIk203Tg00h2k302Tg00P;k101Tg00PYj2~Tg00RBj3ZTg00STj2gTg00h[j2fTg00T`j2NTg00Vhj4YTg00iGj6{Tg00Uaj1zTg00OWj6uTg00U>j2dTg00ikj3OTg00WFj2tTg00jNj3wTg00XLj1yTg00@_j6XTg00YPj1pTg00k1j1}Tg00<2j4[Tg00<]j7hTg00Rkj3oTg00T@k300Tg00koj7nTg00Wij3mTg00ZWj8^Tf0R0#J#Jp=If2R4f1R8'1/R0p=5g004mR3?Q80p=7P3P8g00lSP0C[p=\P8g00AiR6g00BHR1P1g00BhR5P0g00DMR2Fhp=>g00CHR7/D41=80'Cp=8f3R91F48/105Q3p=:%A0#Ap=M1D70p=2AQ307p=K1j30p=EAo380p=6g00A=R:@0080p=<1d30p=BP4P6P1P1P5P3P8g00CfP0C[P2Fhp=;P4P6P1P1P5P8P0Fnp=WP3P8g00[;P0C[p=HAm380p=@P9P6P1P1P5P4P8P0G^p=Uf6R2P6P1P1P5f5R;f4R<P9P6P1P1P5P4P8P0G^G^p=?1D78/C0p=x1=80,C4p=qP3g005KR=#JR>#JR?#I#I#I#I#I#VR@%48RA%V=RB,R0'],18g00m:RC=58B/3C/FC'7X03P3P@1R@B,]A,181180RD/RB/30/F0'7X03P3%40RE/0@RFA58@B/3@/F@,7DX03%l:RD&08:R:&073&063RG&043RH1P37RI1P3@RJ'\'>1|H5RKP0P4g00DmRLg00EMRM'e1v04=QLMdAs378CrRMb5b:b;1=7@RLP0b4RN9iE@A8FF@1cA@PAP@13A@10A@C:%A=RA#ARF#A#M#M#M#M#VRO,14RP/c@PPP@13P@10P@C:119ORQ1LQ@%2Q%2@RR11;ORS/0@#2[[11<ORT/G@%2TRU112ORV/3@#2\R[%4;RW/L@%2Wf7RW#4/0@#2\R[%42RX/G@%2XRYf8RZ#4R[/3@#2\R[PNbVb7b8b97i@10Q@RQ?8Q@1LT@10V@#2\R\U1GS@%2S11WORS/3@#2\R[1LX@10[@#2\R\YA5W@BRY/G@%2Yf9RY?5@BRX/3@#2\R[1G[@%2[f:R[#4/3@#2\R[1TX@%K@RX#kRUA5[@BRVP@13V@10V@C:[1SV@f;RV?5@BRT/0@RQ?8Q@\L1bT@1=@7RTf<RQ?5@BRN/0@R\,=@1D\7'C[1aN@f=RN?5@BR\/3@#K\X1`\@f>?5@BR\/0@/7\\Xg00n2R]1_\@R\eP\f?R\#4/T@f@#4R^P@13^@10^@C:\U1S^@fA#4R^/0@R_?8_@\L1b^@fBR^#4R_/0@R`,=@1D`7'C\T1a_@fC#4R_/3@#K\X1`_@fD#4R_/0@/7_\XP]1__@R_eP_fER_/1O/T@fF/1OR`P@13`@10`@C:\U1S`@fGR`/1ORU/0@Ra?8a@\L1bU@fH/1ORU/0@Ra,=@1Da7'C\T1aU@fIRU/1ORT/3@#K\X1`T@fJ/1ORT/0@/7T\XP]1_T@RTePTP<g00nN2057@'ePLeRLO1fKR7/1O/0@RT?8T@PVPLO1fL#4/0@RV?8V@P^PLO1fM?5@B/0@RL?8L@p-0RLg00\?R^#9#9#9#9RV#9RT#9R]#ERa1j3^R^'62033@>023^Rb%9]R]#9Rc#9#E&01=,~3Rd%E]R]5Z3%EVRV9Z3d,6a'6'6'6g00\^Re'g'fRfAZ3da/6^%Ec%ET/6V,6]'6,6b/ge'fRe1<fD,<e,<e,<f,<f,<e'<'<P:P3P31N3<P41N32CYP8P31N3;P91N3WCYCYPGPH%JA#BRG9;HIPHP6P1P1P5PYE{5WH%z1R:PHPHPHP6P1P1P51HJI,>HEuR5P:1d3=R=1P3O'@R1%A>#BR69O3J/@G'H,>HCUP:PH%B>R>9;HI1\>J,>H5WHP:PHPHP5P:1t3=%B?9O3J/@>'H,>HCUP:PH%BFRF9;HI1\FJ,>H5WHP:PHPHP5P:1@=J1P3B5w3R5%BARA9O3J/@F'H,>HCUP:PHPHA;HI5P:PHA;HIJR5P:A;HIAF?P:PHPHA;HI1P:PHP5P:A;HI6F?P:1@=>AO3AJ'H,>HF?F?F?F?PKPMb5b:b;X<3X=3X>3X?3X@3XA3XB3W61x;Wg00[b\XRXPPP@P2PWC:[A899@%4<P@PWP;C:\X%2[R;?q[@A52@BR2P@PZPQC:\X%22P;\R[%2S%2N\R[11ZY1F[@'7[[[[[[[[^<3^=3^>3^?3^@3^A3^B3^6LP0fORL/1OR[/0@RZ/=@A5L@BRR/0@PZ13[@%4LR[/3@13R@10[@PLP9PYP4P\P8P_P`PUO@b4b1b2b3%47/0@,17A57@B/3@/F@'7ebNbLbKbJb3bIbHbGbFbEb2bUbTbSbRbQb1bCb7b8b9bWbXbPbObMbD1]EO%yEEXPCg00o4EXg00]Jg00^JEX%p0%}0'7eXY3o"). Qed.

Lemma mmap_len_ge : forall l, 0 < l -> l <= mmap_len l < l + 4096.
Proof.
ltac2:(KReplay.run1 (kr_t_KStep ()) ["CEIL_WRAP_1"] "h01lp;2p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710R3p8P0P2p4p7210p8P0p1001@R0p4p7210R2p8p1001Tp4p70p1002Dp4p710R4p8p100Emp4p70R5p100Fmp4p710p8P5p100Gop4p710p8P5p100HMp60721000R6p8P5p100IMR7p4p710p8P5P7p4p7210p8P5p100IfR7p4p710R8p8P5P7p4p741110p8P5p100J?p4p73110p8P5P2p8P5P0p4p73110p8p100JQp4p70P6p8p1002bp4p70P4p8p100KQp4p70R4P1p8P4P6p8P4p100LQp607000p8P4P3p8P4P8p8P4P0p4p710p8g00`Fj21Tg010;j20Tg004mg00CHf0R0'1f1/00UW0o"). Qed.

Lemma mmap_len_aligned : forall l, (mmap_len l) mod 4096 = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_KStep ()) ["CEIL_WRAP_1"] "h01lh11zp;1p;2p;3p;6p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710R3p8P0P2p4p7210p8P0p1001@R0p4p7210R2p8p1001Tp4p70p1002Dp4p710R4p8p100Emp4p70R5p100Fmp4p710p8P5p100Gop4p710p8P5p100HMp60721000R6p8P5p100IMR7p4p710p8P5P7p4p7210p8P5p100IfR7p4p710R8p8P5P7p4p741110p8P5p100J?p4p73110p8P5P2p8P5P0p4p73110p8p100JQp4p70P6p8p1002bp4p70P4p8p100KQp4p70R4P1p8P4P6p8P4p100LQp607000p8P4P3p8P4P8p8P4P0p4p710p8g003Pj16Tg00NIj25Tg00Mlj24Tg00_Lj27Tg00_ij2;Tg0072j23Tg007Rj32Tg011<j2:Tg00@_j69Tg011\j18Tg004Hj11Tf0R0#1#1p=0g004mR4P4g005KR8#0#0#0#0#0#0#6R3f1/50%68R8'4/70/;0/33g00CHR6524X141503/48/73/:3g00m:g00o4E9%80/33=246eW0o"). Qed.

Lemma mmap_len_of_aligned : forall l, 0 <= l -> l mod 4096 = 0 -> mmap_len l = l.
Proof.
ltac2:(KReplay.run1 (kr_t_KStep ()) ["CEIL_WRAP_1"] "h02H1h13H15h22H3h32H9h44__x1h54__x2h64__x3h74__x4h84__x5h91Hh:2H0h;3H10h<3H11h=3H12h>3H13h?3H14h@3H16hA3H17hB3H18hC3H19hD2H2hE2H4hF2H5hG2H6hH2H7hI2H8hJ2HahK2HlhL7__arithhM4__ffhN6__sat2hO6__sat3hP6__sat4hQ6__sat5hR6__sat6hS8__varmaphT5__withU1lhV1zp;1p;2p;3p;4p;6p;7p;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710R3p8P0P2p4p7210p8P0p1001@R0p4p7210R2p8p1001Tp4p70p1002Dp4p710R4p8p100Emp4p70R5p100Fmp4p710p8P5p100Gop4p710p8P5p100HMp60721000R6p8P5p100IMR7p4p710p8P5P7p4p7210p8P5p100IfR7p4p710R8p8P5P7p4p741110p8P5p100J?p4p73110p8P5P2p8P5P0p4p73110p8p100JQp4p70P6p8p1002bp4p70P4p8p100KQp4p70R4P1p8P4P6p8P4p100LQp607000p8P4P3p8P4P8p8P4P0p4p710p8g004Hj1FTg003Pj1KTg0072j20Tg00_Lj22Tg00_ij27Tg00aIj2XTg00NIj21Tg0060j1ETg00`bj2HTg00`Fj2:Tg00b0j2Zj3fTg00Nfj2lj3hTg00baj2UTg00cBj1dTg00c[j2LTg00?`j2DTg00dBj2CTg00d]j2OTg00eCj2NTg00eij2MTg00fhj2_Tg003nj2YTg00P;j1^Tg00PYj2]Tg00Q:j1=Tg00RBj3?Tg00QYj2WTg00STj2VTg00h[j2JTg00gIj2yTg00h2j3xTg008hj1wTg00T@j3\Tg009Hj1vTg00T`j2[Tg009hj1uTg00Vhj4TTg00:Fj1tTg00:dj1pTg00;Oj2STg00OWj6oTg00Uaj1nTg00U>j2BTg00ikj3QTg00Wij3PTg00<2j4GTg00koj7gTg00jNj3iTg00=Aj2jTg00=cj2kTg007Rj3RTg00>Oj3eTg00>nj4mTg00@_j6bTg011\j1qTg00Mlj2aTg00Rkj3rTg00<]j7sTg00ZWj8`Tg00CHR0f0R4'Dp=6%F4#Fp=@g004mR8?R40p=>f2R3f1R6'1/a4p=4AR864p=3%E4#Ep=I1D031:64'Cp=91W84p=<Ar864p=5P8P6g00[;P4CGp=AP6g00AiR1g00BHR5P5g00BhR2P4g00DMFsp=8f3R7P1P5P5P2P3P6P4G`p=;1:64,C3p=c%64g005KR9#FR:#FR;#@#@#@#@#@#KR<,06#>P8P<%K9R=9474/24/74/37XV81X3<123<,7<103<'1,33%E9R>#ER?#E#I#I#I#I#KR@,17RA/X<12A<,7<10A<'1,3Af4RA/1@/H<1:0<RBf5RC/1@/0<RD?9D<[A4C<=RD/Z<%6D%6<RDf7RE?4<=/2<#6[[f6RF/1@RG/l<%6Gf8RG/1@/0<#6\D[11E@RH/Z<%6Hf9RH/1@/2<#6\D[AhG<E10H<#6\DAfH<Gf:RH/2<#6\DA4H<=/U<%><RH#dRDf;RG?4<=RI12I<,7<10I<'1'3[1HI<f<?4<=RI/0<RJ?9J<\B1LI<1:<0RIf=?4<=RJ/0<RK,:<1DK0'C[1OJ<f>?4<=RJ/2<#>\H1NJ<f??4<=RJ/0</3J\Hg00n2RK1MJ<RJePJf@RJ/U<fARL12L<,7<10L<'1'3\D1HL<fBRL/0<RM?9M<\B1LL<fCRM/0<RN,:<1DN0'C\I1OM<fDRM/2<#>\H1NM<fERM/0</3M\HPK1MM<RMePMfFRM/1@/U<fG/1@RN12N<,7<10N<'1'3\D1HN<fH/1@RN/0<RD?9D<\B1LN<fI/1@RN/0<RD,:<1DD0'C\I1ON<fJRN/1@RI/2<#>\H1NI<fK/1@RI/0</3I\HPK1MI<RIePIPAg00nN1_0<'YPBeRBO1fLRI/1@/0<RK?9K<PGPBO1fM/0<RG?9G<PLPBO1fN?4<=/0<RL?9L<PNPBO1fORB/1@/0<R@?9@<g00A=R@%^9,]8RNg00\?RL#=RG#=RK#=RD#=RO#=RP#=RQ#<RR5?8%<KRK9?8N1W8LRL'5'5%=Q#<RQ%<ORO9?8N%<DRD'5,5R'5%<G/5Lg00\^RG'V'J'J15KL,5R1y8<=x8LA?8NQ%<PA?8ND,5O'5'5'5/VG'J%w@5\@3\%v@P8P81[8AP3%u8R@CTP6P8P@P71[8CCTCT%t8%p8R@P@P@P1P5P5P21S8<RG1S80RO'A,8@EoRD%n5RN1B8:R:1B8;9Q8G1B8>R>5P8'A,8@C;PNP@P@P1P5P5P2P8POg00CfR51B8?R?CG,8@P8P?g00lSPGCG,8@FgPNP@P@PDPNAP8:G1S8=5i81B89R99Q8G=P8?'A,8@C;PNP@1A>O,8@PNP@P8POP5P:CG,8@PNAQ89G/A:,8@C;C;C;C;C;1j@2P4P3g00DmR@g00EMR2'Y1k43=R@2dAe806CmbMbSbTX48X58X68X78X88g00[b\HRH17<A/17,33[%6CR6?cC<A4A<=17<7/1E'3\H%>C17C</3F\6[[[[^48^58^68^78^88P4fQR4?4<=R6/0<124<104<P4126<PJP3PMPBfPO:bLb0b2b3b1A4I<=/2</7</3IebCbBbAb@b1b?b>b=b<b;b3bIbHbGbFbEb2bDbNbObPbQbRb0b:b9g00m:g00o4Eb%q3/33eWJWKXU8o"). Qed.

Lemma unsigned_wz : forall z, 0 <= z < 2^64 -> bv_unsigned (wz z) = z.
Proof.
ltac2:(KReplay.run1 (kr_t_KStep ()) ["CEIL_WRAP_1"] "h01zp;2p;1p;3p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710R3p8P0P2p4p7210p8P0p1001@R0p4p7210R2p8p1001Tp4p70p1002Dp4p710R4p8p100Emp4p70R5p100Fmp4p710p8P5p100Gop4p710p8P5p100HMp60721000R6p8P5p100IMR7p4p710p8P5P7p4p7210p8P5p100IfR7p4p710R8p8P5P7p4p741110p8P5p100J?p4p73110p8P5P2p8P5P0p4p73110p8p100JQp4p70P6p8p1002bp4p70P4p8p100KQp4p70R4P1p8P4P6p8P4p100LQp607000p8P4P3p8P4P8p8P4P0p4p710p8g00?`j2:Tg004Hj10Tg003Pj11Tg006Uj22Tg00`Fj29Tg00dBj28Tg012Wj24Tg013^j13Tg014<j15Tg0158j26Tg007Rj37Tg004mR0g00CHf0R4':g005K#0R8#1%08#0#0#0#0R8#1'2,94'8f1R3/44%38%53'6=703eUW0o"). Qed.

Lemma alloc_ceiling_lt : alloc_ceiling < 2^63.
Proof.
ltac2:(KReplay.run1 (kr_t_KStep ()) ["CEIL_WRAP_1"] "h02Hah14__p1h26__sat1h34__x1h4<CEIL_RANGE__h57__arithh64__ffh76__sat0h88__varmaph95__witp;1p;2p;3p;6p;4p;7p;8p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0p1000cR2p4p710R3p8P0P2p4p7210p8P0p1001@R0p4p7210R2p8p1001Tp4p70p1002Dp4p710R4p8p100Emp4p70R5p100Fmp4p710p8P5p100Gop4p710p8P5p100HMp60721000R6p8P5p100IMR7p4p710p8P5P7p4p7210p8P5p100IfR7p4p710R8p8P5P7p4p741110p8P5p100J?p4p73110p8P5P2p8P5P0p4p73110p8p100JQp4p70P6p8p1002bp4p70P4p8p100KQp4p70R4P1p8P4P6p8P4p100LQp607000p8P4P3p8P4P8p8P4P0p4p710p8g015bj1UTg0060j11Tg004Hj10Tg003Pj15Tg016fj1CTg00?`j23Tg00dBj27Tg017dj2?Tg00`Fj26Tg006Uj2TTg018Lj3STg00fhj2RTg003nj2<Tg008hj1MTg009Hj1LTg00T`j2ITg00:Fj1HTg00:dj1FTg00iGj6ETg00U>j2DTg00;Oj29Tg00<2j4:Tg00koj7GTg00Uaj1BTg013^j1JTg0190j3KTg00ZWj8ATg00=Aj2@Tg00=cj2NTg007Rj3OTg00>Oj3PTg00>nj4QTg00<]j7>Tf0R0#1#1#1#1p=2%00#0p==%00#0#0#0p=8%00#0#0#0#0#0#0#0p=4f1R4g00AiR8g00BHR3P3g00BhR6P0g00DMF>p=;p,4RUNpR1#Ug005KR5#1#2R2#1#2#2R7#0#2#2#0#=#8#4#4#5%C1R1'3R9%17#2#2#0#=#8#4#4#5R7,31'7%05#5R:%52R;'?g00CHR</6:R=13<;1T:;R>,6<[R?[13<:R@g019SRAAS:;4UW013<>\A^0@P4g00nN1R<:'<P=eO1P?p-0R?g004mR=g00A=R@#M%L@1I=4%H=%F=R@P8P3P3P6P@P8P3P3P6P@P8P3P3P6f3EEP=1D=5R5g00Cf19=7C:,;@FG%B3P=P5g00lS19=:%J25K=C:,;@GA1@@6P0f2R@g00DmR6g00EMR2'<1N0@=O62dAP=<4CQb6b8b9W3W11307,74164>[^3=^1?P0P9P1f4O3b5b2b7b2b4o"). Qed.
(* [comment removed for export] *)

Lemma elo_went : forall b n, 0 <= b < 2^64 -> elo (went b n) = b.
Proof.
ltac2:(KReplay.run1 (kr_t_KStep ()) ["CEIL_WRAP_1"] "h01bh11np;2p;1p;4p;3p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0g000cR2p4p710R3p8P0P2p4p7210p8P0p1001@R0p4p7210R4p8p1001Tp4p70p1002Dp4p710R5p8p100Emp4p70R6p100Fmp4p710p8P6p100Gop4p710p8P6p100HMp60721000R7p8P6p100IMR8p4p710p8P6P8p4p7210p8P6p100IfR8p4p710R9p8P6P8p4p741110p8P6p100J?p4p73110p8P6P4p8P6P0p4p73110p8p100JQp4p70P7p8p1002bp4p70P5p8p100KQp4p70R5P1p8P5P7p8P5p100LQp607000p8P5P3p8P5P9p8P5P0p4p710p8g00?`j2?Tg004Hj10Tg003Pj12Tg006Uj24Tg00`Fj2>Tg00dBj2;Tg019oj2:Tg013^j15Tg01;5j16Tg014<j11Tg01;Xj47TP2j38Tg0158j29Tg007Rj33Tg01<8j2=Tg01=6j1<Tg004mR2g00CHf1R0'?g005K#0R5#2%05#0#0#0#0R5#2'4,>0';f2R9f0':%55R5%65R5P5P5%19%10C7785'9=329e1=90#<=329eUX12W0o"). Qed.
Lemma ehi_went : forall b n, 0 <= b < 2^64 -> 0 <= n < 2^64 -> ehi (went b n) = b + n.
Proof.
ltac2:(KReplay.run1 (kr_t_KStep ()) ["CEIL_WRAP_1"] "h01zh11bh21np;2p;1p;3p;6p;4p-1R0p10000p4p710R1p8P0p1000GR2p4p710p8P0P2p4p7210p8P0g000cR2p4p710R3p8P0P2p4p7210p8P0p1001@R0p4p7210R4p8p1001Tp4p70p1002Dp4p710R5p8p100Emp4p70R6p100Fmp4p710p8P6p100Gop4p710p8P6p100HMp60721000R7p8P6p100IMR8p4p710p8P6P8p4p7210p8P6p100IfR8p4p710R9p8P6P8p4p741110p8P6p100J?p4p73110p8P6P4p8P6P0p4p73110p8p100JQp4p70P7p8p1002bp4p70P5p8p100KQp4p70R5P1p8P5P7p8P5p100LQp607000p8P5P3p8P5P9p8P5P0p4p710p8g00?`j2CTg004Hj10Tg003Pj14Tg006Uj28Tg00`Fj2BTg00dBj2;Tg013^j1:Tg014<j15Tg0158j22Tg00NIj21Tg007Rj33Tg003nj29Tg019oj26Tg00@_j67Tg01;5j1ATg01;Xj4@TP2j3<Tg01>3j3=Tg01<8j2>Tg01>Pj1?Tg004mR2g00CHf1R0'Cg005K#0R5#4%05#0#0#0#0R5#4'8,B0';R9P2f3R3f0R7%:5R5%53R1'2R6'1f4R4/13R8532X02P2f2R:1147=328X02113:R8,92%5:R4,2516:7E7P61630E7%A5R0P0P0P1P4C@R47<0,25A=004,25'1=328e1>3:#?=328eV9UX22W1o"). Qed.
End CEIL_WRAP_1.



End KStep.
