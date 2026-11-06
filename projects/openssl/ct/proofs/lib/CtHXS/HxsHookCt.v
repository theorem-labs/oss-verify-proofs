(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxHook HxQuery.
From OSSVerify.Proofs.openssl.ct.lib.HXS Require Import HxsStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.


(* [comment removed for export] *)
Definition NB_MAX : Z := 1700.
Definition CALLS_MAX : Z := 4000.

Record xcd : Type := XCD { x_blocks : list int; x_frames : list int; x_calls : Z; x_nb : Z (* [comment removed for export] *) }.

Section Hooks.
Variable segs : list Segment.
Variable shb : w64.
(* [comment removed for export] *)
Variable tpv : w64.
Variable stk_tag : int.
Variable rt_stack : int.
(* [comment removed for export] *)
Variable traces : list (list int).
Variable root_tag : int.
Variable img_top : int.
(* [comment removed for export] *)
Variable gds : list (Z * Z * Z).

Definition xtp_ok (S : sstate) : bool := match rget S X4 with VC w => w_eqb w tpv | _ => false end.
Definition xsp_ok (S : sstate) : bool := match rget S X2 with VP t _ => (t =? stk_tag)%uint63 | _ => false end.

(* [comment removed for export] *)
Definition even_up (t : int) : int := if tag_even t then t else (t + 1)%uint63.

(* [comment removed for export] *)
Definition xclobber_stack (S : sstate) (M : mem) : option mem :=
  match rget S X2 with
  | VP t o =>
      if wh o then None else
      match mget M t with
      | Some rg =>
          match rg_abs rg, rg_dflt rg with
          | None, DUnk =>
              if ((wl o land 15 =? 0) && (rt_stack <=? wl o) && (wl o <=? rg_size rg))%uint63 && rg_wr rg
              then Some (mset M t (drop_below rg (wl o))) else None
          | _, _ => None
          end
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition xret (S : sstate) (res : hval) (M : mem) (nx : int) : option sstate :=
  match rget S X1, s_resv S with
  | VC ra, RNone => Some (SS (w_and ra w_notone) (rf_set (havoc_caller_saved (s_regs S)) X10 res) RNone M (s_abs S) nx)
  | _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stk_word (rg : region) (off : int) : option hval :=
  match rd_cell segs rg (off >> 3)%uint63 with
  | CW w km => if (km =? 255)%uint63 then Some (VC w) else None
  | CP t o => Some (VP t o)
  | CN _ _ => None
  end.

(* [comment removed for export] *)
Fixpoint uw_walk (fuel : nat) (rg : region) (f : int) (fp : hval) : option (list int) :=
  match fuel with
  | O => None
  | Datatypes.S fuel' =>
      match fp with
      | VP t o =>
          if (t =? stk_tag)%uint63 then
            if negb (wh o) && (f + 16 <=? wl o)%uint63 && (wl o land 7 =? 0)%uint63 && (wl o <=? rg_size rg)%uint63 then
              match stk_word rg (wl o - 16)%uint63, stk_word rg (wl o - 8)%uint63 with
              | Some fp', Some (VC ra) =>
                  if wh ra then None else
                  match uw_walk fuel' rg (wl o) fp' with Some l => Some (wl ra :: l) | None => None end
              | _, _ => None
              end
            else None
          else if (t =? root_tag)%uint63 && is_zero o then Some [] else None
      | VC w => if wh w || negb (wl w land 7 =? 0)%uint63 || (wl w <? img_top)%uint63 then Some [] else None
      | _ => None
      end
  end.

Fixpoint list_eqb (a b : list int) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y)%uint63 && list_eqb a' b'
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition unwind_okb (S : sstate) : bool :=
  match rget S X1, rget S X2 with
  | VC ra, VP t o =>
      if (t =? stk_tag)%uint63 && negb (wh o) && negb (wh ra) then
        match mget (s_mem S) t with
        | Some rg =>
            match rg_abs rg with
            | None =>
                if rg_wr rg && (wl o <=? rg_size rg)%uint63 then
                  match uw_walk 64 rg (wl o) (rget S X8) with
                  | Some ras => existsb (list_eqb (wl ra :: ras)) traces
                  | None => false
                  end
                else false
            | Some _ => false
            end
        | None => false
        end
      else false
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition shadow_region (n8 : int) (wr : bool) (df : rdflt) : region := RG None n8 0 wr df (depth_for 60 n8 0) IEmpty.

(* [comment removed for export] *)
Definition ushadow_region (n : int) : region :=
  let nb := ((n + 7) >> 3)%uint63 in
  let d := depth_for 60 nb 0 in
  if (n land 7 =? 0)%uint63 then RG None nb 0 false DZero d IEmpty
  else let q := (n >> 3)%uint63 in
       (* [comment removed for export] *)
       RG None nb 0 false DZero d (iset d IEmpty (q >> 3)%uint63 (CW (W false ((n land 7) << (8 * (q land 7)))%uint63) ((1 << ((q land 7) + 1)) - 1)%uint63)).

Definition hkx_malloc (cd : xcd) (S : sstate) : option (xcd * sstate) :=
  if xtp_ok S && xsp_ok S && unwind_okb S then
    match rget S X10 with
    | VC n =>
        if negb (wh n) && (0 <? wl n)%uint63 && (wl n <=? 64512)%uint63 && (x_nb cd <? NB_MAX) && (x_calls cd <? CALLS_MAX) then
          let t := even_up (s_next S) in
          match xclobber_stack S (s_mem S) with
          | Some Mc =>
              let M1 := mset (new_region Mc t (wl n) 4 DUnk) (sh_tag t) (ushadow_region (wl n)) in
              if (t <? 999990)%uint63 then
                match xret S (VP t w_zero) M1 (t + 2)%uint63 with
                | Some S' => Some (XCD (t :: x_blocks cd) (x_frames cd) (x_calls cd + 1) (x_nb cd + 1), S')
                | None => None
                end
              else None
          | None => None
          end
        else None
    | _ => None
    end
  else None.

Fixpoint remove_tag (t : int) (l : list int) : list int :=
  match l with
  | [] => []
  | x :: r => if (x =? t)%uint63 then r else x :: remove_tag t r
  end.

Definition hkx_realloc (cd : xcd) (S : sstate) : option (xcd * sstate) :=
  if xtp_ok S && xsp_ok S && unwind_okb S then
    match rget S X10, rget S X11 with
    | VP t o, VC n =>
        match mget (s_mem S) t, mget (s_mem S) (sh_tag t) with
        | Some rg, Some rgs =>
            if is_zero o && existsb (fun x => (x =? t)%uint63) (x_blocks cd) && negb (wh n) && (0 <? wl n)%uint63 && (wl n <=? 64512)%uint63
               && negb (rg_size rg =? 0)%uint63 && (rg_size rg <=? wl n)%uint63 && (x_nb cd <? NB_MAX) && (x_calls cd <? CALLS_MAX) then
              let t2 := even_up (s_next S) in
              let d2 := depth_for 60 (wl n) 0 in
              let rg2 := RG None (wl n) 4 true DUnk d2 (copy_cells rg (rg_size rg) d2) in
              match xclobber_stack S (s_mem S) with
              | Some Mc =>
                  let M1 := mset (mset (kill_region (kill_region Mc t rg) (sh_tag t) rgs) t2 rg2) (sh_tag t2) (ushadow_region (wl n)) in
                  if (t2 <? 999990)%uint63 then
                    match xret S (VP t2 w_zero) M1 (t2 + 2)%uint63 with
                    | Some S' => Some (XCD (t2 :: remove_tag t (x_blocks cd)) (x_frames cd) (x_calls cd + 1) (x_nb cd), S')
                    | None => None
                    end
                  else None
              | None => None
              end
            else None
        | _, _ => None
        end
    | _, _ => None
    end
  else None.

Definition hkx_free_null (cd : xcd) (S : sstate) : option (xcd * sstate) :=
  if xtp_ok S && xsp_ok S && unwind_okb S then
    match rget S X10 with
    | VC w => if is_zero w then
                match xclobber_stack S (s_mem S) with
                | Some Mc => match xret S VU Mc (s_next S) with
                             | Some S' => Some (XCD (x_blocks cd) (x_frames cd) (x_calls cd + 1) (x_nb cd), S') | None => None end
                | None => None
                end
              else None
    | _ => None
    end
  else None.

(* [comment removed for export] *)
Definition fshadow_zero (rss : region) (o n : int) : bool :=
  match rg_abs rss with None => true | Some _ => false end
  && ((o >> 3) + (n >> 3) <=? rg_size rss)%uint63
  && kb_check segs rss (to_Z (o >> 3)%uint63) (repeat (KB 0) (Z.to_nat (to_Z (n >> 3)%uint63))).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hkx_memset8 (cd : xcd) (S : sstate) : option (xcd * sstate) :=
  if xtp_ok S && xsp_ok S && (x_calls cd <? CALLS_MAX) then
    match rget S X10, rget S X11, rget S X12, rget S X2 with
    | VP t o, VC c, VC n, VP _ osp =>
        if wh o || wh n then None else
        (* [comment removed for export] *)
        match xclobber_stack S (s_mem S) with
        | Some Mc =>
        match mget Mc t with
        | Some rg =>
            match rg_abs rg with
            | None =>
                if ((wl o land 7 =? 0) && (wl n land 7 =? 0) && (0 <? wl n) && (wl o <=? rg_size rg) && (wl n <=? rg_size rg) && (wl o + wl n <=? rg_size rg))%uint63
                   && rg_wr rg && tag_even t
                   && (existsb (fun x => (x =? t)%uint63) (x_blocks cd)
                       || ((t =? stk_tag)%uint63 && (wl osp <=? wl o)%uint63)
                       (* [comment removed for export] *)
                       || (existsb (fun x => (x =? t)%uint63) (x_frames cd)
                           && match mget Mc (sh_tag t) with
                              | Some rgs => fshadow_zero rgs (wl o) (wl n)
                              | None => false end))
                   && negb (wh c) && (wl c <? 256)%uint63 && (wl n <? 1099511627776)%uint63 (* [comment removed for export] *) then
                  let rg' := RG (rg_abs rg) (rg_size rg) (rg_al rg) (rg_wr rg) (rg_dflt rg) (rg_d rg)
                                (fill_cells (rg_d rg) (rg_cells rg) (wl o >> 3)%uint63 (Z.to_nat (to_Z (wl n >> 3)%uint63)) (rep8 (wl c))) in
                  match xret S (VP t o) (mset Mc t rg') (s_next S) with
                  | Some S' => Some (XCD (x_blocks cd) (x_frames cd) (x_calls cd + 1) (x_nb cd), S') | None => None end
                else None
            | Some _ => None
            end
        | None => None
        end
        | None => None
        end
    | _, _, _, _ => None
    end
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition FS0_CLIENT : int := 56.

(* [comment removed for export] *)
Definition hkx_stack_mallocK (fs : int) (cd : xcd) (S : sstate) : option (xcd * sstate) :=
  if xtp_ok S && xsp_ok S && (Z.of_nat (length (x_frames cd)) <? 15) && (x_calls cd <? CALLS_MAX) then
    let t := even_up (s_next S) in
    match xclobber_stack S (s_mem S) with
    | Some Mc =>
        let M1 := mset (new_region Mc t fs 6 DUnk) (sh_tag t) (shadow_region ((fs + 8) >> 3)%uint63 true DUnk) in
        if (t <? 999990)%uint63 then
          match xret S (VP t w_zero) M1 (t + 2)%uint63 with
          | Some S' => Some (XCD (x_blocks cd) (t :: x_frames cd) (x_calls cd + 1) (x_nb cd), S')
          | None => None
          end
        else None
    | None => None
    end
  else None.

Definition hkx_stack_malloc0 := hkx_stack_mallocK FS0_CLIENT.
Definition hkx_stack_malloc1 := hkx_stack_mallocK 120%uint63.
Definition hkx_stack_malloc2 := hkx_stack_mallocK 248%uint63.

(* [comment removed for export] *)
Definition flag_known_zero (rg : region) : bool :=
  match rd_cell segs rg 0 with
  | CW w km => ((km land 1 =? 1) && (wl w land 255 =? 0))%uint63
  | CP _ _ | CN _ _ => false
  end.

Definition hkx_release (cd : xcd) (S : sstate) : option (xcd * sstate) :=
  match x_frames cd with
  | t :: fr =>
      match mget (s_mem S) t, mget (s_mem S) (sh_tag t) with
      | Some rg, Some rgs =>
          if ((rg_size rg =? 56) || (rg_size rg =? 120) || (rg_size rg =? 248))%uint63 && (even_up (s_next S) <? 999990)%uint63 then
            let fl := even_up (s_next S) in
            (* [comment removed for export] *)
            let rg64 := RG None (rg_size rg + 8)%uint63 (rg_al rg) false (rg_dflt rg) (rg_d rg) (iset (rg_d rg) (rg_cells rg) (rg_size rg >> 3)%uint63 (CP fl w_zero)) in
            let rgf := RG None 1 0 true DUnk 0 (iset 0 IEmpty 0 (CW w_one 1)) in
            (* [comment removed for export] *)
            let St := SS (s_pc S) (s_regs S) (s_resv S) (mset (mset IEmpty t rg64) fl rgf) (s_abs S) (fl + 2)%uint63 in
            match hxs_step shb segs IEmpty St with
            | (_, SNext S1) =>
                match hxs_step shb segs IEmpty S1 with
                | (_, SNext S2) =>
                    match mget (s_mem S2) fl with
                    | Some rgf2 =>
                        if flag_known_zero rgf2 && w_eqb (s_pc S2) (w_add (s_pc S) (W false 8)) then
                          let M3 := kill_region (kill_region (s_mem S) t rg) (sh_tag t) rgs in
                          Some (XCD (x_blocks cd) fr (x_calls cd + 1) (x_nb cd), SS (s_pc S2) (s_regs S2) (s_resv S2) M3 (s_abs S) (fl + 2)%uint63)
                        else None
                    | None => None
                    end
                | _ => None
                end
            | _ => None
            end
          else None
      | _, _ => None
      end
  | [] => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hkx_posix_memalign (cd : xcd) (S : sstate) : option (xcd * sstate) :=
  if xtp_ok S && xsp_ok S && unwind_okb S then
    match rget S X10, rget S X11, rget S X12 with
    | VP tm o, VC al, VC n =>
        if negb (wh o) && negb (wh al) && negb (wh n) && (wl al =? 64)%uint63 && (wl n =? 32768)%uint63
           && (wl o land 7 =? 0)%uint63 && (x_nb cd <? NB_MAX) && (x_calls cd <? CALLS_MAX)
           && (tag_even tm) && existsb (fun x => (x =? tm)%uint63) (x_frames cd) then
          let t := even_up (s_next S) in
          match xclobber_stack S (s_mem S) with
          | Some Mc =>
              match mget Mc tm with
              | Some rgm =>
                  if rg_wr rgm && (wl o <=? rg_size rgm)%uint63 && (wl o + 8 <=? rg_size rgm)%uint63 && match rg_abs rgm with None => true | Some _ => false end then
                    let rgm' := RG (rg_abs rgm) (rg_size rgm) (rg_al rgm) (rg_wr rgm) (rg_dflt rgm) (rg_d rgm) (iset (rg_d rgm) (rg_cells rgm) (wl o >> 3)%uint63 (CP t w_zero)) in
                    let M1 := mset (mset (mset Mc tm rgm') t (RG None (wl n) 6 true DUnk (depth_for 60 (wl n) 0) IEmpty)) (sh_tag t) (ushadow_region (wl n)) in
                    if (t <? 999990)%uint63 then
                      match xret S (VC w_zero) M1 (t + 2)%uint63 with
                      | Some S' => Some (XCD (t :: x_blocks cd) (x_frames cd) (x_calls cd + 1) (x_nb cd + 1), S')
                      | None => None
                      end
                    else None
                  else None
              | None => None
              end
          | None => None
          end
        else None
    | _, _, _ => None
    end
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition gds_cover (lo n : Z) : bool := existsb (fun g => (fst (fst g) <=? lo) && (lo + n <=? fst (fst g) + snd (fst g))) gds.

Definition memcpy_src_ok (cd : xcd) (M : mem) (src : hval) (n : int) : bool :=
  match src with
  | VC s => negb (wh s) && gds_cover (to_Z (wl s)) (to_Z n)
  | VP ts os => negb (wh os) && tag_even ts && existsb (fun x => (x =? ts)%uint63) (x_frames cd) && ((wl os land 7 =? 0) && (n land 7 =? 0))%uint63
                && match mget M ts, mget M (sh_tag ts) with
                   | Some rs, Some rss => match rg_abs rs with None => true | Some _ => false end && (wl os <=? rg_size rs)%uint63 && (n <=? rg_size rs)%uint63 && (wl os + n <=? rg_size rs)%uint63
                                          && fshadow_zero rss (wl os) n
                   | _, _ => false
                   end
  | _ => false
  end.

Definition hkx_memcpy (cd : xcd) (S : sstate) : option (xcd * sstate) :=
  if xtp_ok S && xsp_ok S && (x_calls cd <? CALLS_MAX) then
    match rget S X10, rget S X12 with
    | VP t o, VC n =>
        if wh o || wh n then None else
        match mget (s_mem S) t with
        | Some rg =>
            if tag_even t && existsb (fun x => (x =? t)%uint63) (x_blocks cd)
               && rg_wr rg && (wl o <=? rg_size rg)%uint63 && (wl n <=? rg_size rg)%uint63 && (wl o + wl n <=? rg_size rg)%uint63 && (0 <? wl n)%uint63 && (wl n <? 1099511627776)%uint63
               && match rg_abs rg with None => true | Some _ => false end
               && memcpy_src_ok cd (s_mem S) (rget S X11) (wl n) then
              match copy segs (Datatypes.S (Z.to_nat (to_Z (wl n)))) (s_mem S) (s_abs S) (ctx_of (s_mem S)) (VP t o) (rget S X11) (wl n) with
              | Some M' =>
                  match xclobber_stack S M' with
                  | Some Mc => match xret S (VP t o) Mc (s_next S) with
                               | Some S' => Some (XCD (x_blocks cd) (x_frames cd) (x_calls cd + 1) (x_nb cd), S') | None => None end
                  | None => None
                  end
              | None => None
              end
            else None
        | None => None
        end
    | _, _ => None
    end
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint img_strlen (fuel : nat) (i : nat) (x : int) (acc : int) : option int :=
  match fuel with
  | O => None
  | Datatypes.S f => match img_byte segs i x with
                    | Some b => if (b =? 0)%uint63 then Some acc else img_strlen f i (x + 1)%uint63 (acc + 1)%uint63
                    | None => None
                    end
  end.

(* [comment removed for export] *)
Fixpoint img_bytes_ok (fuel : nat) (i : nat) (x : int) : bool :=
  match fuel with
  | O => true
  | Datatypes.S f => match img_byte segs i x with Some _ => img_bytes_ok f i (x + 1)%uint63 | None => false end
  end.

(* [comment removed for export] *)
Definition seg0_off (a : Z) : option int :=
  match segs with
  | sg :: _ => if (Z.of_N (seg_base sg) <=? a) && (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) && negb (seg_writable sg)
               then Some (of_Z (a - Z.of_N (seg_base sg))) else None
  | [] => None
  end.

Definition hkx_strlen (cd : xcd) (S : sstate) : option (xcd * sstate) :=
  if xtp_ok S && xsp_ok S && (x_calls cd <? CALLS_MAX) then
    match rget S X10 with
    | VC s =>
        if wh s then None else
        match seg0_off (to_Z (wl s)) with
        | Some x =>
            match img_strlen 4096 0%nat x 0 with
            | Some len =>
                (* [comment removed for export] *)
                match seg0_off (to_Z (wl s) + to_Z len + 8) with
                | Some _ =>
                    if gds_cover (to_Z (wl s)) (to_Z len + 1) && img_bytes_ok 7 0%nat (x + len + 1)%uint63 then
                      match xclobber_stack S (s_mem S) with
                      | Some Mc => match xret S (VC (W false len)) Mc (s_next S) with
                                   | Some S' => Some (XCD (x_blocks cd) (x_frames cd) (x_calls cd + 1) (x_nb cd), S') | None => None end
                      | None => None
                      end
                    else None
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | _ => None
    end
  else None.

End Hooks.
