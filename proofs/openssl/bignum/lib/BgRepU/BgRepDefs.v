(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Image.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnU Require BnRep.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Lib_iface.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prog BnBase BnModel BnTree BnInv BgState BgInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation bgusegs := ImageBg.bgusegs.
Notation ST := (bstate bptr).
Notation BN := (bignum bptr).

Definition CONST_ONE : Z := 0x2d0170.
Definition DATA_ONE : Z := 0x413e8.

Definition BN_STRUCT_SZ : Z := 24.
Definition BN_CTX_SZ : Z := 72.
Definition MONT_CTX_SZ : Z := 96.
Definition RECP_SC_SZ : Z := 12.
Definition RECP_CTX_SZ : Z := 64.
Definition ITEM_SZ : Z := POOL_ITEM_BYTES.
Definition FRAMES_SZ : Z := 4 * Z.of_nat BN_CTX_START_FRAMES.
Definition TMOD_BUF_SZ : Z := 16.

Definition GOT_BN_ADD : Z := 0x31c550.
Definition GOT_BN_SUB : Z := 0x31c558.

Definition LIBW_bgr : list (Z * Z) := BnRep.LIBW_bn ++ [(CONST_ONE, CONST_ONE + BN_STRUCT_SZ); (0x31c550, 0x31c560)].
Definition libw (a : Z) : Prop := Lib_iface.rin_ivs LIBW_bgr a.

Definition vref (r : bnref) (s : ST) : Prop := (r < length (st_bns s))%nat.

Inductive place : Type :=
  | PHeap (a : Z) (q : bptr) (off : Z)
  | PFrame (a : Z)
  | PFrameBuf (a d : Z)
  | PStatic (a : Z).

Definition place_addr (p : place) : Z := match p with PHeap a _ _ => a | PFrame a => a | PFrameBuf a _ => a | PStatic a => a end.

Record placement : Type := mkPL {
  pl_bn : bnref -> option place;
  pl_ctx : option (Z * bptr);
  pl_mont : option (Z * bptr);
  pl_recp : option Z
}.

Definition pl_empty : placement := mkPL (fun _ => None) None None None.
Definition pl_set (PL : placement) (r : bnref) (p : option place) : placement :=
  mkPL (fun r' => if (r' =? r)%nat then p else pl_bn PL r') (pl_ctx PL) (pl_mont PL) (pl_recp PL).
Definition pl_set_ctx (PL : placement) (c : option (Z * bptr)) : placement := mkPL (pl_bn PL) c (pl_mont PL) (pl_recp PL).
Definition pl_set_mont (PL : placement) (mo : option (Z * bptr)) : placement := mkPL (pl_bn PL) (pl_ctx PL) mo (pl_recp PL).
Definition pl_set_recp (PL : placement) (rc : option Z) : placement := mkPL (pl_bn PL) (pl_ctx PL) (pl_mont PL) rc.

Definition mont_ref (r : bnref) : bool := ((r =? RMontRR) || (r =? RMontN) || (r =? RMontNi))%nat.

Definition pl_of (PL : placement) (r : bnref) : option place :=
  if (r =? ROne)%nat then Some (PStatic CONST_ONE)
  else if (r =? RMontRR)%nat then match pl_mont PL with Some (am, qm) => Some (PHeap am qm 0) | None => None end
  else if (r =? RMontN)%nat then match pl_mont PL with Some (am, qm) => Some (PHeap (am + 24) qm 24) | None => None end
  else if (r =? RMontNi)%nat then match pl_mont PL with Some (am, qm) => Some (PHeap (am + 48) qm 48) | None => None end
  else if (r <? NFIX)%nat then pl_bn PL r else None.

Definition fr_ivs (p : option place) : list (Z * Z) :=
  match p with
  | Some (PFrame a) => [(a, a + BN_STRUCT_SZ)]
  | Some (PFrameBuf a d) => [(a, a + BN_STRUCT_SZ); (d, d + TMOD_BUF_SZ)]
  | _ => []
  end.
Fixpoint pl_frames_n (PL : placement) (n : nat) : list (Z * Z) :=
  match n with O => [] | S k => fr_ivs (pl_bn PL k) ++ pl_frames_n PL k end.

Definition recp_ivs (rc : option Z) : list (Z * Z) := match rc with Some c => [(c, c + RECP_SC_SZ)] | None => [] end.
Definition pl_frames (PL : placement) : list (Z * Z) := pl_frames_n PL NFIX ++ recp_ivs (pl_recp PL).

Definition pl_frames_in (PL : placement) (lo hi : Z) : Prop :=
  forall iv, In iv (pl_frames PL) -> lo <= fst iv /\ snd iv <= hi.

Definition iv_apart (iv iv' : Z * Z) : Prop := snd iv <= fst iv' \/ snd iv' <= fst iv.

Definition pl_wf (PL : placement) : Prop :=
     (forall r p, pl_bn PL r = Some p ->
        (r < NFIX)%nat /\ r <> ROne /\ mont_ref r = false
        /\ match p with PHeap _ _ off => off = 0 | PStatic _ => False | PFrame a => 0 < a /\ a mod 8 = 0 | PFrameBuf a d => 0 < a /\ 0 < d /\ iv_apart (a, a + BN_STRUCT_SZ) (d, d + TMOD_BUF_SZ) /\ a mod 8 = 0 /\ d mod 8 = 0 end)
  /\ (forall r r' p p' iv iv', r <> r' -> pl_bn PL r = Some p -> pl_bn PL r' = Some p' -> In iv (fr_ivs (Some p)) -> In iv' (fr_ivs (Some p')) -> iv_apart iv iv')
  /\ match pl_recp PL with
     | Some c => 0 < c /\ (forall r p iv, pl_bn PL r = Some p -> In iv (fr_ivs (Some p)) -> iv_apart iv (c, c + RECP_SC_SZ))
     | None => True
     end.

Definition opt_ids (o : option (Z * bptr)) : list bptr := match o with Some (_, q) => [q] | None => [] end.
Fixpoint pl_bn_ids (PL : placement) (n : nat) : list bptr :=
  match n with
  | O => []
  | S k => match pl_bn PL k with Some (PHeap _ q _) => [q] | _ => [] end ++ pl_bn_ids PL k
  end.
Definition pl_ids (PL : placement) : list bptr := pl_bn_ids PL NFIX ++ opt_ids (pl_ctx PL) ++ opt_ids (pl_mont PL).

Definition place_ok (OW : list block) (p : place) : Prop :=
  match p with
  | PHeap a q off => exists n, In (q, a - off, n) OW /\ 0 <= off /\ off + BN_STRUCT_SZ <= n
  | _ => True
  end.

Definition ref_at (s : ST) (OW : list block) (PL : placement) (r : bnref) (a : Z) : Prop :=
  if (r <? NFIX)%nat then exists p, pl_of PL r = Some p /\ place_addr p = a
  else let i := (r - NFIX)%nat in
       exists q H, nth_error (gx_items (st_ctx s)) (i / BN_CTX_POOL_SIZE)%nat = Some q /\ In (q, H, ITEM_SZ) OW
                   /\ a = H + 24 * Z.of_nat (i mod BN_CTX_POOL_SIZE)%nat.

Definition XW (PL : placement) : list (Z * Z) := LIBW_bgr ++ pl_frames PL.

Definition bn_cells (D : Z) (b : BN) : list cell :=
  [C8 (wz D); C4 (wz (Z.of_nat (bn_top b))); C4 (wz (Z.of_nat (bn_dmax b))); C4 (wz (Z.b2z (bn_neg b))); C4 (wz (bn_flags b))].

Definition bn_arr (m : mem) (OW : list block) (pl : option place) (D : Z) (b : BN) : Prop :=
  match bn_d b with
  | Some p => In (p, D, 8 * Z.of_nat (bn_dmax b)) OW /\ u64arr bgusegs m D (wlimbs (bn_buf b))
  | None => match pl with
            | Some (PFrameBuf _ d) => D = d /\ u64arr bgusegs m D (wlimbs (bn_buf b)) /\ length (bn_buf b) = 2%nat
            | Some (PStatic _) => D = DATA_ONE /\ bn_buf b = [1]
            | _ => D = 0 /\ bn_buf b = []
            end
  end.

Definition struct_cells (m : mem) (pl : option place) (a : Z) (cs : list cell) : Prop :=
  match pl with Some (PStatic _) => ro_cells bgusegs m a cs | _ => rw_cells bgusegs m a cs end.

Definition bn_rep (m : mem) (OW : list block) (pl : option place) (a : Z) (b : BN) : Prop :=
  exists D, struct_cells m pl a (bn_cells D b) /\ bn_arr m OW pl D b.

Definition bnR : Type := Z -> BN -> bnref -> Prop.
Definition repR (m : mem) (OW : list block) (PL : placement) : bnR := fun a b r => bn_rep m OW (pl_of PL r) a b.
Definition holeR (hs : list bnref) (m : mem) (OW : list block) (PL : placement) : bnR := fun a b r => In r hs \/ bn_rep m OW (pl_of PL r) a b.

Fixpoint bns_gen (R : bnR) (a : Z) (l : list BN) (i : nat) : Prop :=
  match l with
  | [] => True
  | b :: l' => R a b (RPool i) /\ bns_gen R (a + 24) l' (S i)
  end.

Definition ctx_cells (H Cu T I : Z) (c : bg_ctx bptr) : list cell :=
  [C8 (wz H); C8 (wz Cu); C8 (wz T);
   C4 (wz (Z.of_nat (gx_pused c))); C4 (wz (Z.of_nat (BN_CTX_POOL_SIZE * length (gx_items c))));
   C8 (wz I); C4 (wz (Z.of_nat (length (gx_frames c)))); C4 (wz (Z.of_nat (gx_ssize c)));
   C4 (wz (Z.of_nat (gx_used c))); C4 (wz (Z.of_nat (gx_err_stack c))); C4 (wz (Z.b2z (gx_too_many c)));
   C4 (wz 0); C8 (wz 0)].

Definition cur_addr (Hs : list Z) (c : bg_ctx bptr) : Z := match gx_current c with Some k => nth k Hs 0 | None => 0 end.

Fixpoint items_gen (R : bnR) (cxo : bool) (m : mem) (OW : list block) (items : list bptr) (Hs : list Z) (vals : list BN) (k : nat) (prev : Z) : Prop :=
  match items, Hs with
  | [], [] => vals = []
  | q :: items', H :: Hs' =>
      In (q, H, ITEM_SZ) OW /\ (BN_CTX_POOL_SIZE <= length vals)%nat
      /\ bns_gen R H (firstn BN_CTX_POOL_SIZE vals) (BN_CTX_POOL_SIZE * k)
      /\ (cxo = false -> rw_cells bgusegs m (H + 384) [C8 (wz prev); C8 (wz (hd 0 Hs'))])
      /\ items_gen R cxo m OW items' Hs' (skipn BN_CTX_POOL_SIZE vals) (S k) H
  | _, _ => False
  end.

Definition stack_rep (m : mem) (OW : list block) (I : Z) (c : bg_ctx bptr) : Prop :=
  match gx_indexes c with
  | None => I = 0 /\ gx_ssize c = 0%nat /\ gx_frames c = []
  | Some q => In (q, I, FRAMES_SZ) OW /\ gx_ssize c = BN_CTX_START_FRAMES
              /\ exists stale : list word,
                   (length (gx_frames c) + length stale = BN_CTX_START_FRAMES)%nat
                   /\ u32arr bgusegs m I (map (fun k => wz (Z.of_nat k)) (gx_frames c) ++ stale)
  end.

Definition ctx_gen (R : bnR) (cxo : bool) (m : mem) (OW : list block) (a : Z) (c : bg_ctx bptr) (vals : list BN) : Prop :=
  exists Hs I,
    length Hs = length (gx_items c)
    /\ (cxo = false -> rw_cells bgusegs m a (ctx_cells (hd 0 Hs) (cur_addr Hs c) (last Hs 0) I c) /\ stack_rep m OW I c)
    /\ items_gen R cxo m OW (gx_items c) Hs vals 0 0.

Definition mont_cells (s : ST) : list cell := [C8 (wz (st_n0 s)); C8 (wz 0); C4 (wz (st_ri s)); C4 (wz BN_FLG_MALLOCED)].

Definition recp_cells (s : ST) : list cell := [C4 (wz (st_rbits s)); C4 (wz (st_rshift s)); C4 (wz 0)].

Definition bn_mem_gen (R : bnR) (cxo : bool) (s : ST) (m : mem) (OW : list block) (PL : placement) : Prop :=
     (forall r p, (r < NFIX)%nat -> pl_of PL r = Some p -> place_ok OW p /\ R (place_addr p) (getbn r s) r)
  /\ (forall r, (r < NFIX)%nat -> pl_of PL r = None -> getbn r s = bn_nil 0)
  /\ match pl_ctx PL with
     | None => st_ctx s = gx_nil /\ skipn NFIX (st_bns s) = []
     | Some (ac, qc) => In (qc, ac, BN_CTX_SZ) OW /\ ctx_gen R cxo m OW ac (st_ctx s) (skipn NFIX (st_bns s))
     end
  /\ (match pl_mont PL with
      | None => True
      | Some (am, qm) => In (qm, am, MONT_CTX_SZ) OW /\ rw_cells bgusegs m (am + 72) (mont_cells s)
      end
      /\ match pl_recp PL with
         | None => True
         | Some c => rw_cells bgusegs m c (recp_cells s)
         end).

Definition all_ids (s : ST) (PL : placement) (EA : BnRep.err_addrs) : list bptr := pl_ids PL ++ BnRep.ea_ids EA ++ map fst (blocks_of s).
Definition ids_ok (s : ST) (PL : placement) (EA : BnRep.err_addrs) : Prop := List.NoDup (all_ids s PL EA).

Definition bn_state_hc (cxo : bool) (hs : list bnref) (s : ST) (m : mem) (OW : list block) (PL : placement) (EA : BnRep.err_addrs) : Prop :=
  st_wf s /\ pl_wf PL /\ ids_ok s PL EA /\ bn_mem_gen (holeR hs m OW PL) cxo s m OW PL.

Definition got_arith_cells (m : mem) : Prop :=
  ro_cells bgusegs m GOT_BN_ADD [C8 (wz 0x10a744)] /\ ro_cells bgusegs m GOT_BN_SUB [C8 (wz 0x10ac14)].

Definition lib_cells (m : mem) : Prop := Lib_iface.ossl_exit_cells m /\ got_arith_cells m.

Definition lib_state_hc (cxo : bool) (hs : list bnref) (s : ST) (m : mem) (OW : list block) (PL : placement) (EA : BnRep.err_addrs) : Prop :=
  BnRep.crypto_statics m /\ BnRep.err_inv m OW EA /\ lib_cells m /\ bn_state_hc cxo hs s m OW PL EA.

Notation lib_state_h := (lib_state_hc false).
Notation bn_state_h := (bn_state_hc false).
Definition bn_state := bn_state_hc false [].
Definition lib_state := lib_state_hc false [].

Definition const_one_cells (m : mem) : Prop := ro_cells bgusegs m CONST_ONE (bn_cells DATA_ONE bn_const_one).

Definition lib_inv_bgr (m : mem) (OW : list block) : Prop :=
  (exists EA, List.NoDup (BnRep.ea_ids EA) /\ BnRep.crypto_statics m /\ BnRep.err_inv m OW EA /\ Lib_iface.ossl_exit_cells m)
  /\ const_one_cells m /\ got_arith_cells m.

