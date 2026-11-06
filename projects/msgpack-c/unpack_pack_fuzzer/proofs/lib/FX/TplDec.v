(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From Stdlib Require Import PrimInt63 Uint63 PrimString.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan Notation PlanDec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import W64 Val Mem FI St Plan.

Module TplDec.
Import PlanDec.

Record tst := TS {
  t_d : dst;
  t_fcp : IMap.t fact; t_nfc : int;
  t_fl : list (list fact); t_flp : IMap.t (list fact); t_nfl : int;
  t_cells : list cell; t_grans : list (int * gran);
  t_rg : list region; t_rgp : IMap.t region; t_nrg : int;
  t_sregs : list (int * region);
  t_rf : list (rf sv); t_rfp : IMap.t (rf sv); t_nrf : int;
  t_ops : list opinst; t_priv : list (int * int);
  t_st : list sstate; t_out : list template; t_ok : bool }.

Definition upd_d (t : tst) (d : dst) : tst :=
  TS d (t_fcp t) (t_nfc t) (t_fl t) (t_flp t) (t_nfl t) (t_cells t) (t_grans t) (t_rg t) (t_rgp t) (t_nrg t) (t_sregs t) (t_rf t) (t_rfp t) (t_nrf t)
     (t_ops t) (t_priv t) (t_st t) (t_out t) (t_ok t && d_ok d).
Definition tbad (t : tst) : tst :=
  TS (t_d t) (t_fcp t) (t_nfc t) (t_fl t) (t_flp t) (t_nfl t) (t_cells t) (t_grans t) (t_rg t) (t_rgp t) (t_nrg t) (t_sregs t) (t_rf t) (t_rfp t) (t_nrf t)
     (t_ops t) (t_priv t) (t_st t) (t_out t) false.

Definition dset (d : dst) (i : int) (svs : list sv) (fcs : list fact) : dst :=
  DS i svs fcs (d_pl d) (d_svp d) (d_nsv d) (d_stp d) (d_nst d) (d_ok d).

Definition bg_at (s : string) (i : int) : bg * int :=
  let c := ch s i in let i1 := PrimInt63.add i 1%uint63 in
  if PrimInt63.eqb c 48%uint63 then (BGNone, i1) else if PrimInt63.eqb c 49%uint63 then (BGZero, i1)
  else if PrimInt63.eqb c 50%uint63 then (BGImage, i1) else if PrimInt63.eqb c 51%uint63 then (BGUnk, i1)
  else let '(j, k) := num s i1 in let '(sh, l) := num s k in (BGBlob j sh, l).

Definition rf_of_list (l : list sv) : option (rf sv) :=
  match l with
  | [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15;a16;a17;a18;a19;a20;a21;a22;a23;a24;a25;a26;a27;a28;a29;a30;a31] =>
      Some (RF a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31)
  | _ => None
  end.

Definition tok2 (s : string) (t : tst) : tst :=
  let d := t_d t in let i := d_i d in let c := ch s i in let i1 := PrimInt63.add i 1%uint63 in
  let withd (d' : dst) (t' : tst) : tst := upd_d t' d' in
  if PrimInt63.eqb c 122%uint63   then
    match d_fc d with
    | f :: r => TS (dset d i1 (d_sv d) r) (IMap.add (t_nfc t) f (t_fcp t)) (PrimInt63.add (t_nfc t) 1%uint63) (t_fl t) (t_flp t) (t_nfl t) (t_cells t) (t_grans t)
                   (t_rg t) (t_rgp t) (t_nrg t) (t_sregs t) (t_rf t) (t_rfp t) (t_nrf t) (t_ops t) (t_priv t) (t_st t) (t_out t) (t_ok t)
    | [] => tbad t end
  else if PrimInt63.eqb c 37%uint63   then
    let '(n, j) := num s i1 in
    match IMap.find n (t_fcp t) with Some f => upd_d t (dset d j (d_sv d) (f :: d_fc d)) | None => tbad t end
  else if PrimInt63.eqb c 91%uint63   then
    let '(n, j) := num s i1 in
    let tl := if PrimInt63.eqb (ch s j) 48%uint63 then Some ([], PrimInt63.add j 1%uint63)
              else let '(m, k) := num s (PrimInt63.add j 1%uint63) in match IMap.find m (t_flp t) with Some l => Some (l, k) | None => None end in
    match tl, popn (nat_of n) (d_fc d) [] with
    | Some (l0, k), Some (fs, rest) =>
        TS (dset d k (d_sv d) rest) (t_fcp t) (t_nfc t) ((fs ++ l0) :: t_fl t) (t_flp t) (t_nfl t) (t_cells t) (t_grans t)
           (t_rg t) (t_rgp t) (t_nrg t) (t_sregs t) (t_rf t) (t_rfp t) (t_nrf t) (t_ops t) (t_priv t) (t_st t) (t_out t) (t_ok t)
    | _, _ => tbad t end
  else if PrimInt63.eqb c 36%uint63   then
    match t_fl t with
    | l :: r => TS (seti d i1) (t_fcp t) (t_nfc t) r (IMap.add (t_nfl t) l (t_flp t)) (PrimInt63.add (t_nfl t) 1%uint63) (t_cells t) (t_grans t)
                   (t_rg t) (t_rgp t) (t_nrg t) (t_sregs t) (t_rf t) (t_rfp t) (t_nrf t) (t_ops t) (t_priv t) (t_st t) (t_out t) (t_ok t)
    | [] => tbad t end
  else if PrimInt63.eqb c 38%uint63   then
    let '(n, j) := num s i1 in
    match IMap.find n (t_flp t) with
    | Some l => TS (seti d j) (t_fcp t) (t_nfc t) (l :: t_fl t) (t_flp t) (t_nfl t) (t_cells t) (t_grans t)
                   (t_rg t) (t_rgp t) (t_nrg t) (t_sregs t) (t_rf t) (t_rfp t) (t_nrf t) (t_ops t) (t_priv t) (t_st t) (t_out t) (t_ok t)
    | None => tbad t end
  else if PrimInt63.eqb c 67%uint63   then
    let '(ix, j) := num s i1 in let '(w, k) := num s j in
    match d_sv d with
    | v :: r => TS (dset d k r (d_fc d)) (t_fcp t) (t_nfc t) (t_fl t) (t_flp t) (t_nfl t) (Cell ix w v :: t_cells t) (t_grans t)
                   (t_rg t) (t_rgp t) (t_nrg t) (t_sregs t) (t_rf t) (t_rfp t) (t_nrf t) (t_ops t) (t_priv t) (t_st t) (t_out t) (t_ok t)
    | [] => tbad t end
  else if PrimInt63.eqb c 78%uint63   then
    let b := bit s i1 in let '(key, j) := num s (PrimInt63.add i 2%uint63) in let '(n, k) := num s j in
    match popn (nat_of n) (t_cells t) [] with
    | Some (cs, rest) => TS (seti d k) (t_fcp t) (t_nfc t) (t_fl t) (t_flp t) (t_nfl t) rest ((key, Gran b cs) :: t_grans t)
                            (t_rg t) (t_rgp t) (t_nrg t) (t_sregs t) (t_rf t) (t_rfp t) (t_nrf t) (t_ops t) (t_priv t) (t_st t) (t_out t) (t_ok t)
    | None => tbad t end
  else if PrimInt63.eqb c 72%uint63   then
    let '(lo, j) := num s i1 in let w := bit s j in let '(g, k) := bg_at s (PrimInt63.add j 1%uint63) in let '(n, l) := num s k in
    match d_sv d, popn (nat_of n) (t_grans t) [] with
    | hi :: r, Some (gs, rest) =>
        TS (dset d l r (d_fc d)) (t_fcp t) (t_nfc t) (t_fl t) (t_flp t) (t_nfl t) (t_cells t) rest
           (Region lo hi w g (imap_of gs) :: t_rg t) (t_rgp t) (t_nrg t) (t_sregs t) (t_rf t) (t_rfp t) (t_nrf t) (t_ops t) (t_priv t) (t_st t) (t_out t) (t_ok t)
    | _, _ => tbad t end
  else if PrimInt63.eqb c 100%uint63   then
    let '(base, j) := num s i1 in let '(na, k) := num s j in let '(nr, l) := num s k in let '(rems, m) := nums (nat_of nr) s l [] in
    match IMap.find base (t_rgp t), popn (nat_of na) (t_grans t) [] with
    | Some rb, Some (adds, rest) =>
        TS (seti d m) (t_fcp t) (t_nfc t) (t_fl t) (t_flp t) (t_nfl t) (t_cells t) rest
           (reg_upd rb adds rems :: t_rg t) (t_rgp t) (t_nrg t) (t_sregs t) (t_rf t) (t_rfp t) (t_nrf t) (t_ops t) (t_priv t) (t_st t) (t_out t) (t_ok t)
    | _, _ => tbad t end
  else if PrimInt63.eqb c 74%uint63   then
    match t_rg t with
    | r :: rest => TS (seti d i1) (t_fcp t) (t_nfc t) (t_fl t) (t_flp t) (t_nfl t) (t_cells t) (t_grans t)
                      rest (IMap.add (t_nrg t) r (t_rgp t)) (PrimInt63.add (t_nrg t) 1%uint63) (t_sregs t) (t_rf t) (t_rfp t) (t_nrf t) (t_ops t) (t_priv t) (t_st t) (t_out t) (t_ok t)
    | [] => tbad t end
  else if PrimInt63.eqb c 75%uint63   then
    let '(n, j) := num s i1 in
    match IMap.find n (t_rgp t) with
    | Some r => TS (seti d j) (t_fcp t) (t_nfc t) (t_fl t) (t_flp t) (t_nfl t) (t_cells t) (t_grans t)
                   (r :: t_rg t) (t_rgp t) (t_nrg t) (t_sregs t) (t_rf t) (t_rfp t) (t_nrf t) (t_ops t) (t_priv t) (t_st t) (t_out t) (t_ok t)
    | None => tbad t end
  else if PrimInt63.eqb c 79%uint63   then
    let '(key, j) := num s i1 in
    match t_rg t with
    | r :: rest => TS (seti d j) (t_fcp t) (t_nfc t) (t_fl t) (t_flp t) (t_nfl t) (t_cells t) (t_grans t)
                      rest (t_rgp t) (t_nrg t) ((key, r) :: t_sregs t) (t_rf t) (t_rfp t) (t_nrf t) (t_ops t) (t_priv t) (t_st t) (t_out t) (t_ok t)
    | [] => tbad t end
  else if PrimInt63.eqb c 64%uint63   then
    match popn 32 (d_sv d) [] with
    | Some (l, rest) =>
        match rf_of_list l with
        | Some x => TS (dset d i1 rest (d_fc d)) (t_fcp t) (t_nfc t) (t_fl t) (t_flp t) (t_nfl t) (t_cells t) (t_grans t)
                       (t_rg t) (t_rgp t) (t_nrg t) (t_sregs t) (x :: t_rf t) (t_rfp t) (t_nrf t) (t_ops t) (t_priv t) (t_st t) (t_out t) (t_ok t)
        | None => tbad t end
    | None => tbad t end
  else if PrimInt63.eqb c 94%uint63   then
    match t_rf t with
    | x :: rest => TS (seti d i1) (t_fcp t) (t_nfc t) (t_fl t) (t_flp t) (t_nfl t) (t_cells t) (t_grans t)
                      (t_rg t) (t_rgp t) (t_nrg t) (t_sregs t) rest (IMap.add (t_nrf t) x (t_rfp t)) (PrimInt63.add (t_nrf t) 1%uint63) (t_ops t) (t_priv t) (t_st t) (t_out t) (t_ok t)
    | [] => tbad t end
  else if PrimInt63.eqb c 95%uint63   then
    let '(n, j) := num s i1 in
    match IMap.find n (t_rfp t) with
    | Some x => TS (seti d j) (t_fcp t) (t_nfc t) (t_fl t) (t_flp t) (t_nfl t) (t_cells t) (t_grans t)
                   (t_rg t) (t_rgp t) (t_nrg t) (t_sregs t) (x :: t_rf t) (t_rfp t) (t_nrf t) (t_ops t) (t_priv t) (t_st t) (t_out t) (t_ok t)
    | None => tbad t end
  else if PrimInt63.eqb c 126%uint63   then
    let '(id, j) := num s i1 in let '(n, k) := num s j in
    match popn (nat_of n) (d_sv d) [] with
    | Some (args, rest) => TS (dset d k rest (d_fc d)) (t_fcp t) (t_nfc t) (t_fl t) (t_flp t) (t_nfl t) (t_cells t) (t_grans t)
                              (t_rg t) (t_rgp t) (t_nrg t) (t_sregs t) (t_rf t) (t_rfp t) (t_nrf t) (OpI id args :: t_ops t) (t_priv t) (t_st t) (t_out t) (t_ok t)
    | None => tbad t end
  else if PrimInt63.eqb c 35%uint63   then
    let '(lo, j) := num s i1 in let '(hi, k) := num s j in
    TS (seti d k) (t_fcp t) (t_nfc t) (t_fl t) (t_flp t) (t_nfl t) (t_cells t) (t_grans t)
       (t_rg t) (t_rgp t) (t_nrg t) (t_sregs t) (t_rf t) (t_rfp t) (t_nrf t) (t_ops t) ((lo, hi) :: t_priv t) (t_st t) (t_out t) (t_ok t)
  else if PrimInt63.eqb c 33%uint63   then
    let '(pc, j) := num s i1 in let '(nx, k) := num s j in let rc := ch s k in
    let '(nregs, l) := num s (PrimInt63.add k 1%uint63) in let '(nops, m) := num s l in let '(npriv, e) := num s m in
    let rv : option (sresv * list sv) :=
      if PrimInt63.eqb rc 48%uint63 then Some (RNone, d_sv d) else if PrimInt63.eqb rc 50%uint63 then Some (RUnk, d_sv d)
      else match d_sv d with a :: r => Some (RAddr a, r) | [] => None end in
    match rv, t_fl t, t_rf t, popn (nat_of nregs) (t_sregs t) [], popn (nat_of nops) (t_ops t) [], popn (nat_of npriv) (t_priv t) [] with
    | Some (resv, svs), fs :: fls, ffx :: rfx :: rfs, Some (regs, sregs'), Some (ops, ops'), Some (pv, pv') =>
        TS (dset d e svs (d_fc d)) (t_fcp t) (t_nfc t) fls (t_flp t) (t_nfl t) (t_cells t) (t_grans t)
           (t_rg t) (t_rgp t) (t_nrg t) sregs' rfs (t_rfp t) (t_nrf t) ops' pv'
           (SS pc rfx ffx resv (imap_of regs) fs ops pv nx :: t_st t) (t_out t) (t_ok t)
    | _, _, _, _, _, _ => tbad t end
  else if PrimInt63.eqb c 41%uint63   then
    match d_sv d, t_st t with
    | m :: svs, st :: sts => TS (dset d i1 svs (d_fc d)) (t_fcp t) (t_nfc t) (t_fl t) (t_flp t) (t_nfl t) (t_cells t) (t_grans t)
                               (t_rg t) (t_rgp t) (t_nrg t) (t_sregs t) (t_rf t) (t_rfp t) (t_nrf t) (t_ops t) (t_priv t) sts (Tpl st m :: t_out t) (t_ok t)
    | _, _ => tbad t end
  else upd_d t (tok s d).

Fixpoint loop2 (p : positive) (s : string) (len : int) (t : tst) : tst * bool :=
  let step1 (t : tst) : tst * bool :=
    if PrimInt63.ltb (d_i (t_d t)) len then (if t_ok t then (tok2 s t, false) else (t, true)) else (t, true) in
  match p with
  | xH => step1 t
  | xO q => let '(t1, fin) := loop2 q s len t in if fin then (t1, true) else loop2 q s len t1
  | xI q => let '(t1, fin) := loop2 q s len t in if fin then (t1, true) else
            let '(t2, fin2) := loop2 q s len t1 in if fin2 then (t2, true) else step1 t2
  end.

Definition dec_tpls (s : string) : list template :=
  let d0 := DS 0%uint63 [] [] [] IMap.empty 0%uint63 IMap.empty 0%uint63 true in
  let t0 := TS d0 IMap.empty 0%uint63 [] IMap.empty 0%uint63 [] [] [] IMap.empty 0%uint63 [] [] IMap.empty 0%uint63 [] [] [] [] true in
  let '(t, _) := loop2 (2^40)%positive s (PrimString.length s) t0 in
  if t_ok t then List.rev' (t_out t) else [].

Definition dummy : template := Tpl (SS 0%uint63 (rf_init (VL wzero)) (rf_init (VL wzero)) RNone IMap.empty [] [] [] 0%uint63) (VL wzero).
Definition nth_tpl (l : list template) (n : nat) : template := nth n l dummy.

End TplDec.
