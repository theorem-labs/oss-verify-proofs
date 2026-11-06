(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.openssl.bignum.lib.Common Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition havoc_caller_saved (Rg : regfile hval) : regfile hval :=
  RF VU (r2 Rg) (r3 Rg) (r4 Rg) VU VU VU (r8 Rg) (r9 Rg) VU VU VU VU VU VU VU VU
     (r18 Rg) (r19 Rg) (r20 Rg) (r21 Rg) (r22 Rg) (r23 Rg) (r24 Rg) (r25 Rg) (r26 Rg) (r27 Rg) VU VU VU VU.

Definition drop_below (rg : region) (off : int) : region :=
  RG (rg_abs rg) (rg_size rg) (rg_al rg) (rg_wr rg) (rg_dflt rg) (rg_d rg)
     (iremove (fun k => k <? to_Z (off >> 3)%uint63) (rg_cells rg) 0 1).

Definition HK_STACK : int := 16384.

Definition clobber_stack (S : sstate) (M : mem) : option mem :=
  match rget S X2 with
  | VP t o =>
      if wh o then None else
      match mget M t with
      | Some rg =>
          match rg_abs rg, rg_dflt rg with
          | None, DUnk =>
              if ((wl o land 15 =? 0) && (HK_STACK <=? wl o) && (wl o <=? rg_size rg))%uint63 && rg_wr rg
              then Some (mset M t (drop_below rg (wl o))) else None
          | _, _ => None
          end
      | None => None
      end
  | _ => None
  end.

Definition hk_return (S : sstate) (res : hval) (M : mem) (nx : int) : option sstate :=
  match rget S X1, clobber_stack S M, s_resv S with
  | VC ra, Some M', RNone => Some (SS (w_and ra w_notone) (rf_set (havoc_caller_saved (s_regs S)) X10 res) RNone M' (s_abs S) nx)
  | _, _, _ => None
  end.

Fixpoint depth_for (fuel : nat) (n : int) (d : nat) : nat :=
  match fuel with
  | O => d
  | Datatypes.S f => if (n <=? (8 << of_Z (Z.of_nat d)))%uint63 then d else depth_for f n (Datatypes.S d)
  end.

Definition new_region (M : mem) (t n al : int) (df : rdflt) : mem :=
  mset M t (RG None n al true df (depth_for 60 n 0) IEmpty).

Definition kill_region (M : mem) (t : int) (rg : region) : mem :=
  mset M t (RG (Some 0%uint63) 0 0 false DUnk 0 IEmpty).

Fixpoint copy_cells_rec (src : region) (d : nat) (acc : itrie cell) (k : int) (cnt : nat) : itrie cell :=
  match cnt with
  | O => acc
  | Datatypes.S cnt' =>
      copy_cells_rec src d (match iget (rg_d src) (rg_cells src) k with Some c => iset d acc k c | None => acc end) (k + 1)%uint63 cnt'
  end.

Definition copy_cells (src : region) (n : int) (d : nat) : itrie cell :=
  copy_cells_rec src d IEmpty 0 (Z.to_nat (to_Z (n >> 3)%uint63)).

Section Drive.
Variable segs : list Segment.
Context {CD : Type}.
Variable hooks : list (w64 * (CD -> sstate -> option (CD * sstate))).
Variable final : w64 -> bool.

Definition is_hook_pc (pc : w64) : bool := existsb (fun h => w_eqb (fst h) pc) hooks.
Definition stop_pc (pc : w64) : bool := final pc || is_hook_pc pc.

Fixpoint find_hook (l : list (w64 * (CD -> sstate -> option (CD * sstate)))) (pc : w64) :=
  match l with
  | [] => None
  | (p, h) :: r => if w_eqb p pc then Some h else find_hook r pc
  end.

Inductive dres : Type :=
| DDone (cd : CD) (S : sstate)
| DStuck (code : int) (cd : CD) (S : sstate)
| DFuel (cd : CD) (S : sstate).

Fixpoint hx_drive (k : nat) (n : nat) (ic : icache) (cd : CD) (S : sstate) : icache * dres :=
  match hx_run segs stop_pc n ic S with
  | (ic', RStop S') =>
      if final (s_pc S') then (ic', DDone cd S') else
      match find_hook hooks (s_pc S') with
      | Some h =>
          match h cd S' with
          | Some (cd', S'') =>
              if (s_next S' <=? s_next S'')%uint63 then
                match k with O => (ic', DFuel cd' S'') | Datatypes.S k' => hx_drive k' n ic' cd' S'' end
              else (ic', DStuck 102 cd S')
          | None => (ic', DStuck 100 cd S')
          end
      | None => (ic', DStuck 101 cd S')
      end
  | (ic', RStuck c S') => (ic', DStuck c cd S')
  | (ic', RRun S') => (ic', DFuel cd S')
  end.

End Drive.

Definition hk_at {CD : Type} (pc : w64) (h : CD -> sstate -> option (CD * sstate)) : CD -> sstate -> option (CD * sstate) :=
  fun cd S => if w_eqb (s_pc S) pc then h cd S else None.

Record acd : Type := ACD { a_ops : list (Z * Z * Z); a_tags : list int  ; a_n : Z }.

Definition tag_of (cd : acd) (k : Z) : option int := nth_error (a_tags cd) (Z.to_nat (a_n cd - 1 - k)).

Definition zval (v : hval) : option Z := match v with VC w => Some (wZ w) | _ => None end.

Definition hk_malloc (cd : acd) (S : sstate) : option (acd * sstate) :=
  match a_ops cd, zval (rget S X10) with
  | (0, n, _) :: rest, Some n' =>
      if (n =? n') && (0 <? n) && (n <? 4294967296) then
        let t := s_next S in
        match hk_return S (VP t w_zero) (new_region (s_mem S) t (of_Z n) 4 DUnk) (t + 1)%uint63 with
        | Some S' => Some (ACD rest (t :: a_tags cd) (a_n cd + 1), S')
        | None => None
        end
      else None
  | _, _ => None
  end.

Definition hk_free (cd : acd) (S : sstate) : option (acd * sstate) :=
  match rget S X10 with
  | VC w => if is_zero w then match hk_return S VU (s_mem S) (s_next S) with Some S' => Some (cd, S') | None => None end else None
  | VP t o =>
      match a_ops cd with
      | (1, k, _) :: rest =>
          match tag_of cd k, mget (s_mem S) t with
          | Some t', Some rg =>
              if (t =? t')%uint63 && is_zero o && negb (rg_size rg =? 0)%uint63 then
                match hk_return S VU (kill_region (s_mem S) t rg) (s_next S) with
                | Some S' => Some (ACD rest (a_tags cd) (a_n cd), S')
                | None => None
                end
              else None
          | _, _ => None
          end
      | _ => None
      end
  | VU | VN _ _ => None
  end.

Definition hk_realloc (cd : acd) (S : sstate) : option (acd * sstate) :=
  match a_ops cd, rget S X10, zval (rget S X11) with
  | (2, k, n) :: rest, VP t o, Some n' =>
      match tag_of cd k, mget (s_mem S) t with
      | Some t', Some rg =>
          if (t =? t')%uint63 && is_zero o && (n =? n') && (0 <? n) && (n <? 4294967296) && negb (rg_size rg =? 0)%uint63
             && (rg_size rg <=? of_Z n)%uint63 then
            let t2 := s_next S in
            let d2 := depth_for 60 (of_Z n) 0 in
            let rg2 := RG None (of_Z n) 4 true DUnk d2 (copy_cells rg (rg_size rg) d2) in
            match hk_return S (VP t2 w_zero) (mset (kill_region (s_mem S) t rg) t2 rg2) (t2 + 1)%uint63 with
            | Some S' => Some (ACD rest (t2 :: a_tags cd) (a_n cd + 1), S')
            | None => None
            end
          else None
      | _, _ => None
      end
  | _, _, _ => None
  end.

Section MemHooks.
Variable segs : list Segment.

Fixpoint fill (fuel : nat) (M : mem) (abs : abstab) (ctx : vctx) (a : hval) (n : int) (c8 c64 : w64) : option mem :=
  match fuel with
  | O => None
  | Datatypes.S f =>
      if (n =? 0)%uint63 then Some M else
      let al8 := match a with VP _ o => (wl o land 7 =? 0)%uint63 | VC w => (wl w land 7 =? 0)%uint63 | VU | VN _ _ => false end in
      if al8 && (8 <=? n)%uint63 then
        match hx_store segs M abs a SZ8 (VC c64) with
        | Some M' => fill f M' abs ctx (v_alu64 ctx ALU_ADD a (VC (W false 8))) (n - 8)%uint63 c8 c64
        | None => None
        end
      else
        match hx_store segs M abs a SZ1 (VC c8) with
        | Some M' => fill f M' abs ctx (v_alu64 ctx ALU_ADD a (VC (W false 1))) (n - 1)%uint63 c8 c64
        | None => None
        end
  end.

Definition rep8 (c : int) : w64 :=
  let b := (c land 255)%uint63 in
  W (128 <=? b)%uint63 (b lor (b << 8) lor (b << 16) lor (b << 24) lor (b << 32) lor (b << 40) lor (b << 48) lor ((b land 127) << 56))%uint63.

Definition hk_memset {CD : Type} (cd : CD) (S : sstate) : option (CD * sstate) :=
  match rget S X11, rget S X12 with
  | VC c, VC n =>
      if wh n then None else
      match fill (Datatypes.S (Z.to_nat (to_Z (wl n)))) (s_mem S) (s_abs S) (ctx_of (s_mem S)) (rget S X10) (wl n) (W false (wl c land 255)%uint63) (rep8 (wl c)) with
      | Some M' => match hk_return S (rget S X10) M' (s_next S) with Some S' => Some (cd, S') | None => None end
      | None => None
      end
  | _, _ => None
  end.

Fixpoint copy (fuel : nat) (M : mem) (abs : abstab) (ctx : vctx) (d s : hval) (n : int) : option mem :=
  match fuel with
  | O => None
  | Datatypes.S f =>
      if (n =? 0)%uint63 then Some M else
      let al v := match v with VP _ o => (wl o land 7 =? 0)%uint63 | VC w => (wl w land 7 =? 0)%uint63 | VU | VN _ _ => false end in
      let sz := if al d && al s && (8 <=? n)%uint63 then SZ8 else SZ1 in
      let k := nbytes sz in
      match hx_load segs M abs s sz false with
      | Some v =>
          match hx_store segs M abs d sz v with
          | Some M' => copy f M' abs ctx (v_alu64 ctx ALU_ADD d (VC (W false k))) (v_alu64 ctx ALU_ADD s (VC (W false k))) (n - k)%uint63
          | None => None
          end
      | None => None
      end
  end.

Definition hk_memcpy {CD : Type} (cd : CD) (S : sstate) : option (CD * sstate) :=
  match rget S X12 with
  | VC n =>
      if wh n then None else
      match copy (Datatypes.S (Z.to_nat (to_Z (wl n)))) (s_mem S) (s_abs S) (ctx_of (s_mem S)) (rget S X10) (rget S X11) (wl n) with
      | Some M' => match hk_return S (rget S X10) M' (s_next S) with Some S' => Some (cd, S') | None => None end
      | None => None
      end
  | _ => None
  end.

End MemHooks.

Section MemHooks2.
Variable segs : list Segment.

Fixpoint forget_range (fuel : nat) (M : mem) (abs : abstab) (ctx : vctx) (a : hval) (n : int) : option mem :=
  match fuel with
  | O => None
  | Datatypes.S f =>
      if (n =? 0)%uint63 then Some M else
      let al8 := match a with VP _ o => (wl o land 7 =? 0)%uint63 | VC w => (wl w land 7 =? 0)%uint63 | VU | VN _ _ => false end in
      let sz := if al8 && (8 <=? n)%uint63 then SZ8 else SZ1 in
      match hx_store segs M abs a sz VU with
      | Some M' => forget_range f M' abs ctx (v_alu64 ctx ALU_ADD a (VC (W false (nbytes sz)))) (n - nbytes sz)%uint63
      | None => None
      end
  end.

Definition hk_memcpy_forget {CD : Type} (cd : CD) (S : sstate) : option (CD * sstate) :=
  match rget S X12 with
  | VC n =>
      if wh n then None else
      match forget_range (Datatypes.S (Z.to_nat (to_Z (wl n)))) (s_mem S) (s_abs S) (ctx_of (s_mem S)) (rget S X10) (wl n) with
      | Some M' => match hk_return S (rget S X10) M' (s_next S) with Some S' => Some (cd, S') | None => None end
      | None => None
      end
  | _ => None
  end.

End MemHooks2.

Section FinalHooks.
Variable segs : list Segment.

Variable errno_tag : int.
Variable errno_addr : int.

Variable tpv : w64.
Variable stk_tag : int.

Definition reset_errno (M : mem) : option mem :=
  match mget M errno_tag with
  | Some rg =>
      match rg_abs rg, rg_dflt rg with
      | Some a, DUnk =>
          if (a =? errno_addr)%uint63 && (rg_size rg =? 4)%uint63 && rg_wr rg
          then Some (mset M errno_tag (RG (rg_abs rg) (rg_size rg) (rg_al rg) (rg_wr rg) DUnk (rg_d rg) IEmpty))
          else None
      | _, _ => None
      end
  | None => None
  end.

Definition tp_ok (S : sstate) : bool := match rget S X4 with VC w => w_eqb w tpv | _ => false end.
Definition sp_ok (S : sstate) : bool := match rget S X2 with VP t _ => (t =? stk_tag)%uint63 | _ => false end.

Definition hk_malloc_v (cd : acd) (S : sstate) : option (acd * sstate) :=
  if tp_ok S && sp_ok S then
    match reset_errno (s_mem S) with
    | Some M1 => hk_malloc cd (SS (s_pc S) (s_regs S) (s_resv S) M1 (s_abs S) (s_next S))
    | None => None
    end
  else None.

Definition hk_realloc_v (cd : acd) (S : sstate) : option (acd * sstate) :=
  if tp_ok S && sp_ok S then
    match reset_errno (s_mem S) with
    | Some M1 => hk_realloc cd (SS (s_pc S) (s_regs S) (s_resv S) M1 (s_abs S) (s_next S))
    | None => None
    end
  else None.

Definition hk_free_null (cd : acd) (S : sstate) : option (acd * sstate) :=
  match rget S X10 with
  | VC w => if is_zero w then match hk_return S VU (s_mem S) (s_next S) with Some S' => Some (cd, S') | None => None end else None
  | _ => None
  end.

Fixpoint fill_cells (d : nat) (cells : itrie cell) (k : int) (cnt : nat) (c64 : w64) : itrie cell :=
  match cnt with
  | O => cells
  | Datatypes.S cnt' => fill_cells d (iset d cells k (CW c64 255)) (k + 1)%uint63 cnt' c64
  end.

Definition hk_memset8 {CD : Type} (cd : CD) (S : sstate) : option (CD * sstate) :=
  match rget S X10, rget S X11, rget S X12 with
  | VP t o, VC c, VC n =>
      if wh o || wh n then None else
      match mget (s_mem S) t with
      | Some rg =>
          match rg_abs rg with
          | None =>
              if ((wl o land 7 =? 0) && (wl n land 7 =? 0) && (wl o <=? rg_size rg) && (wl n <=? rg_size rg) && (wl o + wl n <=? rg_size rg))%uint63 && rg_wr rg then
                let rg' := RG (rg_abs rg) (rg_size rg) (rg_al rg) (rg_wr rg) (rg_dflt rg) (rg_d rg)
                              (fill_cells (rg_d rg) (rg_cells rg) (wl o >> 3)%uint63 (Z.to_nat (to_Z (wl n >> 3)%uint63)) (rep8 (wl c))) in
                match hk_return S (VP t o) (mset (s_mem S) t rg') (s_next S) with Some S' => Some (cd, S') | None => None end
              else None
          | Some _ => None
          end
      | None => None
      end
  | _, _, _ => None
  end.

End FinalHooks.
