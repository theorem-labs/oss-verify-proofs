(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Module ActrB.

Definition SBw : w64 := ActrA.SBw.
Definition K_TWIN : w64 := ActrA.K_TWIN.
Definition K_FRAME : w64 := wlit 7%uint63.
Definition K_FTWIN : w64 := wlit 8%uint63.

Definition ZC_BASE : w64 := wlit 140737488355328%uint63.
Definition BLK_LO : w64 := ActrA.BLK_LO.
Definition BLK_HI : w64 := ActrA.BLK_HI.
Definition sp_region := ActrA.sp_region.
Definition stack_room_g := ActrA.stack_room_g.
Definition forget_stack_below_sp_g := ActrA.forget_stack_below_sp_g.

Definition acall_pre (TP : int) (room : int) (st : sstate) : option (int * list sv) :=
  match call_pre st, getr st X4, find_op HEAP_ID (s_ops st) with
  | Some r, VL tp, Some hargs =>
      if weqb tp (wlit TP) && stack_room_g st room
         && ActrA.sp_floor_ok st hargs && ActrA.sp_top_ok st
         && ActrA.twins_intact st hargs
      then Some (r, hargs) else None
  | _, _, _ => None
  end.

Definition acall_pre_nt (TP : int) (room : int) (st : sstate) : option (int * list sv) :=
  match call_pre st, getr st X4, find_op HEAP_ID (s_ops st) with
  | Some r, VL tp, Some hargs =>
      if weqb tp (wlit TP) && stack_room_g st room
         && ActrA.sp_floor_ok st hargs && ActrA.sp_top_ok st
      then Some (r, hargs) else None
  | _, _, _ => None
  end.

Definition del_window_k := ActrA.del_window_k.
Definition heap_del_window_k := ActrA.heap_del_window_k.

Definition find_twin (fs : list fact) (k : int) : option int :=
  let fix go (l : list fact) : option int :=
    match l with
    | FEq (VP sh o) (VAlu ALU_ADD (VAlu ALU_SRL (VP k' o') (VL c3)) (VL sb)) :: l' =>
        if PrimInt63.eqb k k' && weqb o wzero && weqb o' wzero && weqb c3 (wlit 3%uint63) && weqb sb SBw then Some sh else go l'
    | _ :: l' => go l'
    | [] => None
    end in go fs.
Definition link_fact (sh k : int) : fact :=
  FEq (VP sh wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw)).

Section WithSegs.
Variable segs : list Segment.

Inductive fstat := FLive | FDead | FUnk.
Definition frame_status (st : sstate) (lo : sv) : fstat :=
  match lo with
  | VP kf z =>
      if weqb z wzero then
        match IMap.find kf (s_regs st) with
        | Some rf =>

            if can_read segs (s_facts st) (s_priv st) kf rf 24%uint63 8%uint63 then
              match region_load segs kf rf 24%uint63 8%uint63 false with
              | Some rs => match decide_ltu (s_facts st) rs (getr st X2) with
                           | Some true => FDead
                           | Some false => FLive
                           | None => FUnk
                           end
              | None => FUnk
              end
            else FUnk
        | None => FUnk
        end
      else FUnk
  | _ => FUnk
  end.
Fixpoint frames_all_live (n : nat) (ws : list sv) (st : sstate) : bool :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' =>
      (if sv_eqb kd (VL K_FRAME) then match frame_status st l with FLive => true | _ => false end else true)
      && frames_all_live n' ws' st
  | _, _ => true
  end.

Definition frames_pre (st : sstate) (hargs : list sv) (cls : int) : bool :=
  match heap_nwin hargs, hargs with
  | Some n, VL md :: a :: VL nw :: rest => frames_all_live n (firstn (3 * n) rest) st
  | _, _ => false
  end.

Fixpoint drop_dead (n : nat) (ws : list sv) (st : sstate) (R : IMap.t region) (cnt : list int)
  : list sv * IMap.t region * list int :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' =>
      let '(ws2, R2, c2) := drop_dead n' ws' st R cnt in
      if sv_eqb kd (VL K_FRAME) && (match frame_status st l with FDead => true | _ => false end) then
        match l with
        | VP kf _ => match find_twin (s_facts st) kf with
                     | Some shf =>
                         (ws2, IMap.remove shf (IMap.remove kf R2), shf :: c2)
                     | None => (l :: sz :: kd :: ws2, R2, c2)
                     end
        | _ => (l :: sz :: kd :: ws2, R2, c2)
        end
      else (l :: sz :: kd :: ws2, R2, c2)
  | _, _ => (ws, R, cnt)
  end.

Fixpoint drop_orphans (n : nat) (ws : list sv) (shs : list int) (cnt : int) : list sv * int :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' =>
      let '(ws2, c2) := drop_orphans n' ws' shs cnt in
      match l with
      | VP k z => if sv_eqb kd (VL K_FTWIN) && weqb z wzero && existsb (PrimInt63.eqb k) shs
                  then (ws2, PrimInt63.add c2 1%uint63) else (l :: sz :: kd :: ws2, c2)
      | _ => (l :: sz :: kd :: ws2, c2)
      end
  | _, _ => (ws, cnt)
  end.
Fixpoint nodup_int (l : list int) : bool :=
  match l with [] => true | x :: l' => negb (existsb (PrimInt63.eqb x) l') && nodup_int l' end.

Fixpoint pay_credit (n : nat) (ws : list sv) : option (list sv) :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' =>
      match l, sz, kd with
      | VL a, VL z, VL k0 =>
          if weqb k0 wzero && weqb z wzero && wleu ZC_BASE a then
            if wleu (wadd ZC_BASE (wlit 16%uint63)) a then Some (VL (wsub a (wlit 16%uint63)) :: sz :: kd :: ws') else None
          else match pay_credit n' ws' with Some ws2 => Some (l :: sz :: kd :: ws2) | None => None end
      | _, _, _ => match pay_credit n' ws' with Some ws2 => Some (l :: sz :: kd :: ws2) | None => None end
      end
  | _, _ => None
  end.

Definition stack_malloc_apply (TP : int) (cls : int) (st : sstate) : option (list sstate) :=
  match acall_pre TP 4096%uint63 st with
  | Some (r, hargs) =>
      let size := PrimInt63.lsl 64%uint63 cls in
      let usz := PrimInt63.sub size 8%uint63 in
      if PrimInt63.leb cls 2%uint63 && frames_pre st hargs cls
         && ActrA.sp_altop_ok st hargs then
        match forget_stack_below_sp_g st with
        | Some st1 =>
                let sp := getr st X2 in
                let st2 := clobber st1 in
                let (kf, st3) := fresh st2 in let (shf, st5) := fresh st3 in
                let fr := region_store (Region 0%uint63 (VL (wlit usz)) true BGUnk IMap.empty) 24%uint63 8%uint63 sp in
                let tw := Region 0%uint63 (VL (wlit (PrimInt63.lsr size 3%uint63))) true BGZero IMap.empty in
                match heap_add_window hargs (VP kf wzero) (VL (wlit usz)) (VL K_FRAME) with
                | Some h1 =>
                    match heap_add_window h1 (VP shf wzero) (VL (wlit (PrimInt63.lsr size 3%uint63))) (VL K_FTWIN) with
                    | Some h2 =>
                        let R' := IMap.add shf tw (IMap.add kf fr (s_regs st5)) in
                        let st6 := set_ops (setregs st5 R') (set_op HEAP_ID h2 (s_ops st5)) in
                        let st7 := addfact (addfact (addfact st6 (FRange kf BLK_LO BLK_HI)) (FAlign kf 6%uint63)) (link_fact shf kf) in
                        Some [setpc (setr st7 X10 (VP kf wzero)) r]
                    | None => None
                    end
                | None => None
                end
        | None => None
        end
      else None
  | None => None
  end.
Definition stack_malloc_c (pc TP cls : int) : contract := Contract pc (stack_malloc_apply TP cls).

Definition frame_abandon_apply (st : sstate) : option (list sstate) :=
  match find_op HEAP_ID (s_ops st) with
  | Some hargs =>
      match heap_nwin hargs, hargs with
      | Some n, VL md :: a :: VL nw :: rest =>
          let '(ws1, R1, shs) := drop_dead n (firstn (3 * n) rest) st (s_regs st) [] in
          let c1 := of_Z (Z.of_nat (length shs)) in
          if negb (Nat.eqb (length shs) 0) && Nat.leb (length shs) 16 && nodup_int shs then
            let n1 := (n - length shs)%nat in
            let '(ws2, c2) := drop_orphans n1 ws1 shs 0%uint63 in
            if PrimInt63.eqb c2 c1 then
              match pay_credit (n1 - Z.to_nat (to_Z c2)) ws2 with
              | Some ws3 =>
                  let h' := VL md :: a :: VL (wsub nw (wlit (PrimInt63.add c1 c2))) :: ws3 ++ skipn (3 * n) rest in
                  Some [set_ops (setregs st R1) (set_op HEAP_ID h' (s_ops st))]
              | None => None
              end
            else None
          else None
      | _, _ => None
      end
  | None => None
  end.
Definition frame_abandon_c (pc : int) : contract := Contract pc frame_abandon_apply.

Definition fake_free_apply (RF RT : r5) (OFF : int) (st : sstate) : option (list sstate) :=
  match s_resv st, getr st RF, ActrA.aheap_windows st with
  | RNone, VP kf z, Some (hargs, wl) =>
      match find_twin (s_facts st) kf, heap_find_window hargs (VP kf wzero) with
      | Some shf, Some (_, len, kd) =>
          match IMap.find shf (s_regs st) with
          | Some rsh =>
              if weqb z wzero && fresh_ok st && sv_eqb kd (VL K_FRAME) && sv_eqb len (VL (wlit OFF))
                 && negb (r5_eqb RT X0)
                 && ActrA.afree_ok_k K_FRAME K_FTWIN st wl kf shf
                 && ActrA.stack_room_g st 0%uint63 && ActrA.sp_floor_ok st hargs
                 && PrimInt63.eqb (rg_lo rsh) 0%uint63
                 && match DefsA.CtrA.win_lookup wl shf with Some (lent, _) => known_eq (s_facts st) (rg_hi rsh) lent | None => false end
              then
                match heap_del_window_k hargs (VP kf wzero) K_FRAME with
                | Some h1 =>
                    match heap_del_window_k h1 (VP shf wzero) K_FTWIN with
                    | Some h2 =>
                        let (v, st1) := fresh st in
                        let R' := IMap.remove shf (IMap.remove kf (s_regs st1)) in
                        Some [setpc (setr (set_ops (setregs st1 R') (set_op HEAP_ID h2 (s_ops st1))) RT (VP v wzero))
                                    (PrimInt63.add (s_pc st) 8%uint63)]
                    | None => None
                    end
                | None => None
                end
              else None
          | None => None
          end
      | _, _ => None
      end
  | _, _, _ => None
  end.
Definition fake_free_c (pc : int) (RF RT : r5) (OFF : int) : contract := Contract pc (fake_free_apply RF RT OFF).

Definition void_call_apply (TP room : int) (st : sstate) : option (list sstate) :=
  match acall_pre TP room st with
  | Some (r, _) =>
      match forget_stack_below_sp_g st with
      | Some st1 => let st2 := clobber st1 in let (v, st3) := fresh st2 in Some [setpc (setr st3 X10 (VP v wzero)) r]
      | None => None
      end
  | None => None
  end.

Definition SSH_ID : int := 12%uint63.
Definition ssh_present (st : sstate) : bool := match find_op SSH_ID (s_ops st) with Some [] => true | _ => false end.
Definition hnr_apply (TP : int) (st : sstate) : option (list sstate) :=
  match find_op HEAP_ID (s_ops st) with
  | Some hargs =>
      if ssh_present st && ActrA.sp_altop_ok st hargs
      then void_call_apply TP 12288%uint63 st else None
  | None => None
  end.
Definition hnr_c (pc TP : int) : contract := Contract pc (hnr_apply TP).

Definition unwind_wrap_apply (TP REAL : int) (st : sstate) : option (list sstate) :=
  if negb (ssh_present st) then None else
  match acall_pre TP 16384%uint63 st with
  | Some (_, hargs) =>
      if negb (ActrA.sp_altop_ok st hargs) then None else
      match forget_stack_below_sp_g st with
      | Some st1 => let a0 := getr st X10 in let ra := getr st X1 in
                    Some [setpc (setr (setr (clobber st1) X10 a0) X1 ra) REAL]
      | None => None
      end
  | None => None
  end.
Definition unwind_wrap_c (pc TP REAL : int) : contract := Contract pc (unwind_wrap_apply TP REAL).

Definition tls_get_addr_apply (TP : int) (TLSADDR : w64) (st : sstate) : option (list sstate) :=
  match acall_pre TP 4096%uint63 st, getr st X10 with
  | Some (r, _), VP k off =>
      match IMap.find k (s_regs st), okey off, okey (wadd off (wlit 8%uint63)) with
      | Some rg, Some o0, Some o8 =>
          if negb (can_read segs (s_facts st) (s_priv st) k rg o0 8%uint63 && can_read segs (s_facts st) (s_priv st) k rg o8 8%uint63)
          then None else
          match region_load segs k rg o0 8%uint63 false, region_load segs k rg o8 8%uint63 false with
          | Some (VL m), Some (VL o) =>

              let above_sp := match getr st X2 with
                              | VP ks offs => PrimInt63.eqb k ks && negb (wlts off offs)
                              | _ => false
                              end in
              if weqb m wone && weqb o wzero && above_sp then
                match forget_stack_below_sp_g st with
                | Some st1 => Some [setpc (setr (clobber st1) X10 (VL TLSADDR)) r]
                | None => None
                end
              else None
          | _, _ => None
          end
      | _, _, _ => None
      end
  | _, _ => None
  end.
Definition tls_get_addr_c (pc TP : int) (TLSADDR : w64) : contract := Contract pc (tls_get_addr_apply TP TLSADDR).

Definition NMAX : int := 4096%uint63.
Definition in_region (r : region) (o : w64) (len : int) : bool :=
  match okey o, okey (wadd o (wlit len)), rg_hi r with
  | Some k0, Some k1, VL hi => kleb (rg_lo r) k0 && kleb k0 k1 && negb (wt hi) &&
                               (match okey hi with Some kh => kleb k1 kh | None => false end)
  | _, _, _ => false
  end.
Fixpoint copy_cells (fuel : nat) (ks : int) (rs : region) (os : w64) (rd : region) (od : w64) (i len : int) : option region :=
  match fuel with
  | O => if PrimInt63.leb len i then Some rd else None
  | S f =>
      if PrimInt63.leb len i then Some rd else
      let so := wadd os (wlit i) in let dof := wadd od (wlit i) in
      match okey so, okey dof with
      | Some sk, Some dk =>
          let w := if PrimInt63.leb 8%uint63 (PrimInt63.sub len i) && PrimInt63.eqb (PrimInt63.land sk 7%uint63) 0%uint63
                      && PrimInt63.eqb (PrimInt63.land dk 7%uint63) 0%uint63 then 8%uint63 else 1%uint63 in
          let rd' := match region_load segs ks rs sk w false with
                     | Some v => region_store rd dk w v
                     | None => region_forget rd (granule dk) (PrimInt63.add (granule dk) 1%uint63)
                     end in
          copy_cells f ks rs os rd' od (PrimInt63.add i w) len
      | _, _ => None
      end
  end.
Definition ranges_disjoint (os od : w64) (len : int) : bool :=

  let d := wsub os od in let d' := wsub od os in
  (negb (wt d) && wleu (wlit len) d) || (negb (wt d') && wleu (wlit len) d').
Definition memcpy_apply (TP : int) (st : sstate) : option (list sstate) :=
  match acall_pre TP 4096%uint63 st, getr st X10, getr st X11, getr st X12 with
  | Some (r, _), VP kd od, VP ks os, VL n =>
      match IMap.find kd (s_regs st), IMap.find ks (s_regs st) with
      | Some rd, Some rs =>
          let len := wl n in
          if negb (wt n) && PrimInt63.leb len NMAX && negb (PrimInt63.eqb kd 0%uint63) && negb (PrimInt63.eqb ks 0%uint63)
             && rg_w rd && in_region rd od len && in_region rs os len
             && (negb (PrimInt63.eqb kd ks) || ranges_disjoint os od len)
          then
            match copy_cells (Z.to_nat (to_Z len) + 1) ks rs os rd od 0%uint63 len with
            | Some rd' =>

                match forget_stack_below_sp_g (setregs st (IMap.add kd rd' (s_regs st))) with
                | Some st1 => Some [setpc (setr (clobber st1) X10 (VP kd od)) r]
                | None => None
                end
            | None => None
            end
          else None
      | _, _ => None
      end
  | _, _, _, _ => None
  end.
Definition memcpy_c (pc TP : int) : contract := Contract pc (memcpy_apply TP).

Fixpoint set_cells (fuel : nat) (rd : region) (od : w64) (b : int) (i len : int) : option region :=
  match fuel with
  | O => if PrimInt63.leb len i then Some rd else None
  | S f =>
      if PrimInt63.leb len i then Some rd else
      match okey (wadd od (wlit i)) with
      | Some dk =>
          let w8 := PrimInt63.leb 8%uint63 (PrimInt63.sub len i) && PrimInt63.eqb (PrimInt63.land dk 7%uint63) 0%uint63 in
          let b8 := PrimInt63.mul b 0x0101010101010101%uint63 in
          let v := if w8 then VL (W64 (PrimInt63.leb 128%uint63 b) (PrimInt63.land b8 9223372036854775807%uint63)) else VL (wlit b) in
          set_cells f (region_store rd dk (if w8 then 8%uint63 else 1%uint63) v) od b (PrimInt63.add i (if w8 then 8%uint63 else 1%uint63)) len
      | None => None
      end
  end.
Definition memset_apply (TP : int) (st : sstate) : option (list sstate) :=
  match acall_pre TP 4096%uint63 st, getr st X10, getr st X11, getr st X12 with
  | Some (r, _), VP kd od, VL c, VL n =>
      match IMap.find kd (s_regs st) with
      | Some rd =>
          let len := wl n in let b := PrimInt63.land (wl c) 255%uint63 in
          if negb (wt n) && PrimInt63.leb len NMAX && negb (PrimInt63.eqb kd 0%uint63) && rg_w rd && in_region rd od len
          then
            match set_cells (Z.to_nat (to_Z len) + 1) rd od b 0%uint63 len with
            | Some rd' =>
                match forget_stack_below_sp_g (setregs st (IMap.add kd rd' (s_regs st))) with
                | Some st1 => Some [setpc (setr (clobber st1) X10 (VP kd od)) r]
                | None => None
                end
            | None => None
            end
          else None
      | None => None
      end
  | _, _, _, _ => None
  end.
Definition memset_c (pc TP : int) : contract := Contract pc (memset_apply TP).

Definition vec_hi (n : int) (oA : w64) (k : int) : sv := VAlu ALU_SRL (VAlu ALU_SUB (VP n oA) (VP k wzero)) (VL (wlit 3%uint63)).
Definition al8 (o : w64) : bool := negb (wt o) && PrimInt63.eqb (PrimInt63.land (wl o) 7%uint63) 0%uint63.

Fixpoint find_lbk_to (fs : list fact) (n k : int) : option w64 :=
  match fs with
  | [] => None
  | FULe (VP k' o) (VP n' z) :: fs' =>
      if PrimInt63.eqb n' n && PrimInt63.eqb k' k && weqb z wzero then Some o else find_lbk_to fs' n k
  | FEq (VP n' z) (VP k' o) :: fs' =>
      if PrimInt63.eqb n' n && PrimInt63.eqb k' k && weqb z wzero then Some o else find_lbk_to fs' n k
  | _ :: fs' => find_lbk_to fs' n k
  end.

Definition hi_mid (k : int) (h : sv) : option sv :=
  match h with
  | VL g => if negb (wt g) && PrimInt63.ltb (wl g) 288230376151711744%uint63
            then Some (VP k (wlit (PrimInt63.lsl (wl g) 3%uint63))) else None
  | VAlu ALU_SRL (VAlu ALU_SUB (VP n oA) (VP k' z)) (VL c) =>
      if PrimInt63.eqb k' k && weqb z wzero && weqb c (wlit 3%uint63) then Some (VP n oA) else None
  | _ => None
  end.

Fixpoint al8_sv (fs : list fact) (v : sv) : bool :=
  match v with
  | VL c => al8 c
  | VP n o => al8 o && PrimInt63.leb 3%uint63 (find_align fs n)
  | VAlu ALU_ADD a b => al8_sv fs a && al8_sv fs b
  | _ => false
  end.

Definition mid_hi (fs : list fact) (k : int) (mid : sv) : option sv :=
  match mid with
  | VP n o =>
      if PrimInt63.eqb n k then (if al8 o then Some (VL (wlit (PrimInt63.lsr (wl o) 3%uint63))) else None)
      else match find_lbk_to fs n k with
           | Some o2 =>
               if al8 o && al8 o2 && PrimInt63.leb 3%uint63 (find_align fs n) && PrimInt63.leb 3%uint63 (find_align fs k)
                  && nowrap_kb fs n o && nowrap_kb fs k o2
               then Some (vec_hi n o k) else None
           | None => None
           end
  | _ => None
  end.

Definition is_subview_of (fs : list fact) (k : int) (s' : int) (r' : region) : bool :=
  negb (rg_w r') && (match rg_bg r' with BGZero => true | _ => false end)
  && match ActrA.block_of_twin fs s' with
     | Some n => negb (PrimInt63.eqb n k) && (match find_lbk_to fs n k with Some _ => true | None => false end)
     | None => false
     end.

Definition annotate_apply (TP : int) (st : sstate) : option (list sstate) := ActrA.annotate_apply st.
Definition annotate_c (pc TP : int) : contract := ActrA.annotate_c pc.
End WithSegs.

End ActrB.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.
Import Actr.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Module ActrB.

Definition SBw : w64 := ActrA.SBw.
Definition K_TWIN : w64 := ActrA.K_TWIN.
Definition K_FRAME : w64 := wlit 7%uint63.
Definition K_FTWIN : w64 := wlit 8%uint63.

Definition ZC_BASE : w64 := wlit 140737488355328%uint63.
Definition BLK_LO : w64 := ActrA.BLK_LO.
Definition BLK_HI : w64 := ActrA.BLK_HI.
Definition sp_region := ActrA.sp_region.
Definition stack_room_g := ActrA.stack_room_g.
Definition forget_stack_below_sp_g := ActrA.forget_stack_below_sp_g.

Definition acall_pre (TP : int) (room : int) (st : sstate) : option (int * list sv) :=
  match call_pre st, getr st X4, find_op HEAP_ID (s_ops st) with
  | Some r, VL tp, Some hargs =>
      if weqb tp (wlit TP) && stack_room_g st room
         && ActrA.sp_floor_ok st hargs && ActrA.sp_top_ok st
         && ActrA.twins_intact st hargs
      then Some (r, hargs) else None
  | _, _, _ => None
  end.

Definition acall_pre_nt (TP : int) (room : int) (st : sstate) : option (int * list sv) :=
  match call_pre st, getr st X4, find_op HEAP_ID (s_ops st) with
  | Some r, VL tp, Some hargs =>
      if weqb tp (wlit TP) && stack_room_g st room
         && ActrA.sp_floor_ok st hargs && ActrA.sp_top_ok st
      then Some (r, hargs) else None
  | _, _, _ => None
  end.

Definition del_window_k := ActrA.del_window_k.
Definition heap_del_window_k := ActrA.heap_del_window_k.

Definition find_twin (fs : list fact) (k : int) : option int :=
  let fix go (l : list fact) : option int :=
    match l with
    | FEq (VP sh o) (VAlu ALU_ADD (VAlu ALU_SRL (VP k' o') (VL c3)) (VL sb)) :: l' =>
        if PrimInt63.eqb k k' && weqb o wzero && weqb o' wzero && weqb c3 (wlit 3%uint63) && weqb sb SBw then Some sh else go l'
    | _ :: l' => go l'
    | [] => None
    end in go fs.
Definition link_fact (sh k : int) : fact :=
  FEq (VP sh wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw)).

Section WithSegs.
Variable segs : list Segment.

Inductive fstat := FLive | FDead | FUnk.
Definition frame_status (st : sstate) (lo : sv) : fstat :=
  match lo with
  | VP kf z =>
      if weqb z wzero then
        match IMap.find kf (s_regs st) with
        | Some rf =>

            if can_read segs (s_facts st) (s_priv st) kf rf 24%uint63 8%uint63 then
              match region_load segs kf rf 24%uint63 8%uint63 false with
              | Some rs => match decide_ltu (s_facts st) rs (getr st X2) with
                           | Some true => FDead
                           | Some false => FLive
                           | None => FUnk
                           end
              | None => FUnk
              end
            else FUnk
        | None => FUnk
        end
      else FUnk
  | _ => FUnk
  end.
Fixpoint frames_all_live (n : nat) (ws : list sv) (st : sstate) : bool :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' =>
      (if sv_eqb kd (VL K_FRAME) then match frame_status st l with FLive => true | _ => false end else true)
      && frames_all_live n' ws' st
  | _, _ => true
  end.

Definition frames_pre (st : sstate) (hargs : list sv) (cls : int) : bool :=
  match heap_nwin hargs, hargs with
  | Some n, VL md :: a :: VL nw :: rest => frames_all_live n (firstn (3 * n) rest) st
  | _, _ => false
  end.

Fixpoint drop_dead (n : nat) (ws : list sv) (st : sstate) (R : IMap.t region) (cnt : list int)
  : list sv * IMap.t region * list int :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' =>
      let '(ws2, R2, c2) := drop_dead n' ws' st R cnt in
      if sv_eqb kd (VL K_FRAME) && (match frame_status st l with FDead => true | _ => false end) then
        match l with
        | VP kf _ => match find_twin (s_facts st) kf with
                     | Some shf =>
                         (ws2, IMap.remove shf (IMap.remove kf R2), shf :: c2)
                     | None => (l :: sz :: kd :: ws2, R2, c2)
                     end
        | _ => (l :: sz :: kd :: ws2, R2, c2)
        end
      else (l :: sz :: kd :: ws2, R2, c2)
  | _, _ => (ws, R, cnt)
  end.

Fixpoint drop_orphans (n : nat) (ws : list sv) (shs : list int) (cnt : int) : list sv * int :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' =>
      let '(ws2, c2) := drop_orphans n' ws' shs cnt in
      match l with
      | VP k z => if sv_eqb kd (VL K_FTWIN) && weqb z wzero && existsb (PrimInt63.eqb k) shs
                  then (ws2, PrimInt63.add c2 1%uint63) else (l :: sz :: kd :: ws2, c2)
      | _ => (l :: sz :: kd :: ws2, c2)
      end
  | _, _ => (ws, cnt)
  end.
Fixpoint nodup_int (l : list int) : bool :=
  match l with [] => true | x :: l' => negb (existsb (PrimInt63.eqb x) l') && nodup_int l' end.

Fixpoint pay_credit (n : nat) (ws : list sv) : option (list sv) :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' =>
      match l, sz, kd with
      | VL a, VL z, VL k0 =>
          if weqb k0 wzero && weqb z wzero && wleu ZC_BASE a then
            if wleu (wadd ZC_BASE (wlit 16%uint63)) a then Some (VL (wsub a (wlit 16%uint63)) :: sz :: kd :: ws') else None
          else match pay_credit n' ws' with Some ws2 => Some (l :: sz :: kd :: ws2) | None => None end
      | _, _, _ => match pay_credit n' ws' with Some ws2 => Some (l :: sz :: kd :: ws2) | None => None end
      end
  | _, _ => None
  end.

Definition stack_malloc_apply (TP : int) (cls : int) (st : sstate) : option (list sstate) :=
  match acall_pre TP 4096%uint63 st with
  | Some (r, hargs) =>
      let size := PrimInt63.lsl 64%uint63 cls in
      let usz := PrimInt63.sub size 8%uint63 in
      if PrimInt63.leb cls 2%uint63 && frames_pre st hargs cls
         && ActrA.sp_altop_ok st hargs then
        match forget_stack_below_sp_g st with
        | Some st1 =>
                let sp := getr st X2 in
                let st2 := clobber st1 in
                let (kf, st3) := fresh st2 in let (shf, st5) := fresh st3 in
                let fr := region_store (Region 0%uint63 (VL (wlit usz)) true BGUnk IMap.empty) 24%uint63 8%uint63 sp in
                let tw := Region 0%uint63 (VL (wlit (PrimInt63.lsr size 3%uint63))) true BGZero IMap.empty in
                match heap_add_window hargs (VP kf wzero) (VL (wlit usz)) (VL K_FRAME) with
                | Some h1 =>
                    match heap_add_window h1 (VP shf wzero) (VL (wlit (PrimInt63.lsr size 3%uint63))) (VL K_FTWIN) with
                    | Some h2 =>
                        let R' := IMap.add shf tw (IMap.add kf fr (s_regs st5)) in
                        let st6 := set_ops (setregs st5 R') (set_op HEAP_ID h2 (s_ops st5)) in
                        let st7 := addfact (addfact (addfact st6 (FRange kf BLK_LO BLK_HI)) (FAlign kf 6%uint63)) (link_fact shf kf) in
                        Some [setpc (setr st7 X10 (VP kf wzero)) r]
                    | None => None
                    end
                | None => None
                end
        | None => None
        end
      else None
  | None => None
  end.
Definition stack_malloc_c (pc TP cls : int) : contract := Contract pc (stack_malloc_apply TP cls).

Definition frame_abandon_apply (st : sstate) : option (list sstate) :=
  match find_op HEAP_ID (s_ops st) with
  | Some hargs =>
      match heap_nwin hargs, hargs with
      | Some n, VL md :: a :: VL nw :: rest =>
          let '(ws1, R1, shs) := drop_dead n (firstn (3 * n) rest) st (s_regs st) [] in
          let c1 := of_Z (Z.of_nat (length shs)) in
          if negb (Nat.eqb (length shs) 0) && Nat.leb (length shs) 16 && nodup_int shs then
            let n1 := (n - length shs)%nat in
            let '(ws2, c2) := drop_orphans n1 ws1 shs 0%uint63 in
            if PrimInt63.eqb c2 c1 then
              match pay_credit (n1 - Z.to_nat (to_Z c2)) ws2 with
              | Some ws3 =>
                  let h' := VL md :: a :: VL (wsub nw (wlit (PrimInt63.add c1 c2))) :: ws3 ++ skipn (3 * n) rest in
                  Some [set_ops (setregs st R1) (set_op HEAP_ID h' (s_ops st))]
              | None => None
              end
            else None
          else None
      | _, _ => None
      end
  | None => None
  end.
Definition frame_abandon_c (pc : int) : contract := Contract pc frame_abandon_apply.

Definition fake_free_apply (RF RT : r5) (OFF : int) (st : sstate) : option (list sstate) :=
  match s_resv st, getr st RF, ActrA.aheap_windows st with
  | RNone, VP kf z, Some (hargs, wl) =>
      match find_twin (s_facts st) kf, heap_find_window hargs (VP kf wzero) with
      | Some shf, Some (_, len, kd) =>
          match IMap.find shf (s_regs st) with
          | Some rsh =>
              if weqb z wzero && fresh_ok st && sv_eqb kd (VL K_FRAME) && sv_eqb len (VL (wlit OFF))
                 && negb (r5_eqb RT X0)
                 && ActrA.afree_ok_k K_FRAME K_FTWIN st wl kf shf
                 && ActrA.stack_room_g st 0%uint63 && ActrA.sp_floor_ok st hargs
                 && PrimInt63.eqb (rg_lo rsh) 0%uint63
                 && match DefsA.CtrA.win_lookup wl shf with Some (lent, _) => known_eq (s_facts st) (rg_hi rsh) lent | None => false end
              then
                match heap_del_window_k hargs (VP kf wzero) K_FRAME with
                | Some h1 =>
                    match heap_del_window_k h1 (VP shf wzero) K_FTWIN with
                    | Some h2 =>
                        let (v, st1) := fresh st in
                        let R' := IMap.remove shf (IMap.remove kf (s_regs st1)) in
                        Some [setpc (setr (set_ops (setregs st1 R') (set_op HEAP_ID h2 (s_ops st1))) RT (VP v wzero))
                                    (PrimInt63.add (s_pc st) 8%uint63)]
                    | None => None
                    end
                | None => None
                end
              else None
          | None => None
          end
      | _, _ => None
      end
  | _, _, _ => None
  end.
Definition fake_free_c (pc : int) (RF RT : r5) (OFF : int) : contract := Contract pc (fake_free_apply RF RT OFF).

Definition void_call_apply (TP room : int) (st : sstate) : option (list sstate) :=
  match acall_pre TP room st with
  | Some (r, _) =>
      match forget_stack_below_sp_g st with
      | Some st1 => let st2 := clobber st1 in let (v, st3) := fresh st2 in Some [setpc (setr st3 X10 (VP v wzero)) r]
      | None => None
      end
  | None => None
  end.

Definition SSH_ID : int := 12%uint63.
Definition ssh_present (st : sstate) : bool := match find_op SSH_ID (s_ops st) with Some [] => true | _ => false end.
Definition hnr_apply (TP : int) (st : sstate) : option (list sstate) :=
  match find_op HEAP_ID (s_ops st) with
  | Some hargs =>
      if ssh_present st && ActrA.sp_altop_ok st hargs
      then void_call_apply TP 12288%uint63 st else None
  | None => None
  end.
Definition hnr_c (pc TP : int) : contract := Contract pc (hnr_apply TP).

Definition unwind_wrap_apply (TP REAL : int) (st : sstate) : option (list sstate) :=
  if negb (ssh_present st) then None else
  match acall_pre TP 16384%uint63 st with
  | Some (_, hargs) =>
      if negb (ActrA.sp_altop_ok st hargs) then None else
      match forget_stack_below_sp_g st with
      | Some st1 => let a0 := getr st X10 in let ra := getr st X1 in
                    Some [setpc (setr (setr (clobber st1) X10 a0) X1 ra) REAL]
      | None => None
      end
  | None => None
  end.
Definition unwind_wrap_c (pc TP REAL : int) : contract := Contract pc (unwind_wrap_apply TP REAL).

Definition tls_get_addr_apply (TP : int) (TLSADDR : w64) (st : sstate) : option (list sstate) :=
  match acall_pre TP 4096%uint63 st, getr st X10 with
  | Some (r, _), VP k off =>
      match IMap.find k (s_regs st), okey off, okey (wadd off (wlit 8%uint63)) with
      | Some rg, Some o0, Some o8 =>
          if negb (can_read segs (s_facts st) (s_priv st) k rg o0 8%uint63 && can_read segs (s_facts st) (s_priv st) k rg o8 8%uint63)
          then None else
          match region_load segs k rg o0 8%uint63 false, region_load segs k rg o8 8%uint63 false with
          | Some (VL m), Some (VL o) =>

              let above_sp := match getr st X2 with
                              | VP ks offs => PrimInt63.eqb k ks && negb (wlts off offs)
                              | _ => false
                              end in
              if weqb m wone && weqb o wzero && above_sp then
                match forget_stack_below_sp_g st with
                | Some st1 => Some [setpc (setr (clobber st1) X10 (VL TLSADDR)) r]
                | None => None
                end
              else None
          | _, _ => None
          end
      | _, _, _ => None
      end
  | _, _ => None
  end.
Definition tls_get_addr_c (pc TP : int) (TLSADDR : w64) : contract := Contract pc (tls_get_addr_apply TP TLSADDR).

Definition NMAX : int := 4096%uint63.
Definition in_region (r : region) (o : w64) (len : int) : bool :=
  match okey o, okey (wadd o (wlit len)), rg_hi r with
  | Some k0, Some k1, VL hi => kleb (rg_lo r) k0 && kleb k0 k1 && negb (wt hi) &&
                               (match okey hi with Some kh => kleb k1 kh | None => false end)
  | _, _, _ => false
  end.
Fixpoint copy_cells (fuel : nat) (ks : int) (rs : region) (os : w64) (rd : region) (od : w64) (i len : int) : option region :=
  match fuel with
  | O => if PrimInt63.leb len i then Some rd else None
  | S f =>
      if PrimInt63.leb len i then Some rd else
      let so := wadd os (wlit i) in let dof := wadd od (wlit i) in
      match okey so, okey dof with
      | Some sk, Some dk =>
          let w := if PrimInt63.leb 8%uint63 (PrimInt63.sub len i) && PrimInt63.eqb (PrimInt63.land sk 7%uint63) 0%uint63
                      && PrimInt63.eqb (PrimInt63.land dk 7%uint63) 0%uint63 then 8%uint63 else 1%uint63 in
          let rd' := match region_load segs ks rs sk w false with
                     | Some v => region_store rd dk w v
                     | None => region_forget rd (granule dk) (PrimInt63.add (granule dk) 1%uint63)
                     end in
          copy_cells f ks rs os rd' od (PrimInt63.add i w) len
      | _, _ => None
      end
  end.
Definition ranges_disjoint (os od : w64) (len : int) : bool :=

  let d := wsub os od in let d' := wsub od os in
  (negb (wt d) && wleu (wlit len) d) || (negb (wt d') && wleu (wlit len) d').
Definition memcpy_apply (TP : int) (st : sstate) : option (list sstate) :=
  match acall_pre TP 4096%uint63 st, getr st X10, getr st X11, getr st X12 with
  | Some (r, _), VP kd od, VP ks os, VL n =>
      match IMap.find kd (s_regs st), IMap.find ks (s_regs st) with
      | Some rd, Some rs =>
          let len := wl n in
          if negb (wt n) && PrimInt63.leb len NMAX && negb (PrimInt63.eqb kd 0%uint63) && negb (PrimInt63.eqb ks 0%uint63)
             && rg_w rd && in_region rd od len && in_region rs os len
             && (negb (PrimInt63.eqb kd ks) || ranges_disjoint os od len)
          then
            match copy_cells (Z.to_nat (to_Z len) + 1) ks rs os rd od 0%uint63 len with
            | Some rd' =>

                match forget_stack_below_sp_g (setregs st (IMap.add kd rd' (s_regs st))) with
                | Some st1 => Some [setpc (setr (clobber st1) X10 (VP kd od)) r]
                | None => None
                end
            | None => None
            end
          else None
      | _, _ => None
      end
  | _, _, _, _ => None
  end.
Definition memcpy_c (pc TP : int) : contract := Contract pc (memcpy_apply TP).

Fixpoint set_cells (fuel : nat) (rd : region) (od : w64) (b : int) (i len : int) : option region :=
  match fuel with
  | O => if PrimInt63.leb len i then Some rd else None
  | S f =>
      if PrimInt63.leb len i then Some rd else
      match okey (wadd od (wlit i)) with
      | Some dk =>
          let w8 := PrimInt63.leb 8%uint63 (PrimInt63.sub len i) && PrimInt63.eqb (PrimInt63.land dk 7%uint63) 0%uint63 in
          let b8 := PrimInt63.mul b 0x0101010101010101%uint63 in
          let v := if w8 then VL (W64 (PrimInt63.leb 128%uint63 b) (PrimInt63.land b8 9223372036854775807%uint63)) else VL (wlit b) in
          set_cells f (region_store rd dk (if w8 then 8%uint63 else 1%uint63) v) od b (PrimInt63.add i (if w8 then 8%uint63 else 1%uint63)) len
      | None => None
      end
  end.
Definition memset_apply (TP : int) (st : sstate) : option (list sstate) :=
  match acall_pre TP 4096%uint63 st, getr st X10, getr st X11, getr st X12 with
  | Some (r, _), VP kd od, VL c, VL n =>
      match IMap.find kd (s_regs st) with
      | Some rd =>
          let len := wl n in let b := PrimInt63.land (wl c) 255%uint63 in
          if negb (wt n) && PrimInt63.leb len NMAX && negb (PrimInt63.eqb kd 0%uint63) && rg_w rd && in_region rd od len
          then
            match set_cells (Z.to_nat (to_Z len) + 1) rd od b 0%uint63 len with
            | Some rd' =>
                match forget_stack_below_sp_g (setregs st (IMap.add kd rd' (s_regs st))) with
                | Some st1 => Some [setpc (setr (clobber st1) X10 (VP kd od)) r]
                | None => None
                end
            | None => None
            end
          else None
      | None => None
      end
  | _, _, _, _ => None
  end.
Definition memset_c (pc TP : int) : contract := Contract pc (memset_apply TP).

Definition vec_hi (n : int) (oA : w64) (k : int) : sv := VAlu ALU_SRL (VAlu ALU_SUB (VP n oA) (VP k wzero)) (VL (wlit 3%uint63)).
Definition al8 (o : w64) : bool := negb (wt o) && PrimInt63.eqb (PrimInt63.land (wl o) 7%uint63) 0%uint63.

Fixpoint find_lbk_to (fs : list fact) (n k : int) : option w64 :=
  match fs with
  | [] => None
  | FULe (VP k' o) (VP n' z) :: fs' =>
      if PrimInt63.eqb n' n && PrimInt63.eqb k' k && weqb z wzero then Some o else find_lbk_to fs' n k
  | FEq (VP n' z) (VP k' o) :: fs' =>
      if PrimInt63.eqb n' n && PrimInt63.eqb k' k && weqb z wzero then Some o else find_lbk_to fs' n k
  | _ :: fs' => find_lbk_to fs' n k
  end.

Definition hi_mid (k : int) (h : sv) : option sv :=
  match h with
  | VL g => if negb (wt g) && PrimInt63.ltb (wl g) 288230376151711744%uint63
            then Some (VP k (wlit (PrimInt63.lsl (wl g) 3%uint63))) else None
  | VAlu ALU_SRL (VAlu ALU_SUB (VP n oA) (VP k' z)) (VL c) =>
      if PrimInt63.eqb k' k && weqb z wzero && weqb c (wlit 3%uint63) then Some (VP n oA) else None
  | _ => None
  end.

Fixpoint al8_sv (fs : list fact) (v : sv) : bool :=
  match v with
  | VL c => al8 c
  | VP n o => al8 o && PrimInt63.leb 3%uint63 (find_align fs n)
  | VAlu ALU_ADD a b => al8_sv fs a && al8_sv fs b
  | _ => false
  end.

Definition mid_hi (fs : list fact) (k : int) (mid : sv) : option sv :=
  match mid with
  | VP n o =>
      if PrimInt63.eqb n k then (if al8 o then Some (VL (wlit (PrimInt63.lsr (wl o) 3%uint63))) else None)
      else match find_lbk_to fs n k with
           | Some o2 =>
               if al8 o && al8 o2 && PrimInt63.leb 3%uint63 (find_align fs n) && PrimInt63.leb 3%uint63 (find_align fs k)
                  && nowrap_kb fs n o && nowrap_kb fs k o2
               then Some (vec_hi n o k) else None
           | None => None
           end
  | _ => None
  end.

Definition is_subview_of (fs : list fact) (k : int) (s' : int) (r' : region) : bool :=
  negb (rg_w r') && (match rg_bg r' with BGZero => true | _ => false end)
  && match ActrA.block_of_twin fs s' with
     | Some n => negb (PrimInt63.eqb n k) && (match find_lbk_to fs n k with Some _ => true | None => false end)
     | None => false
     end.

Definition annotate_apply (TP : int) (st : sstate) : option (list sstate) := ActrA.annotate_apply st.
Definition annotate_c (pc TP : int) : contract := ActrA.annotate_c pc.
End WithSegs.

End ActrB.
End TwinB.
