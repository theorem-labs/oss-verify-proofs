(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.

Module ION.

(* [comment removed for export] *)
Inductive open_outcome : Type :=
| ONone                      (* [comment removed for export] *)
| OTooLong                   (* [comment removed for export] *)
| ONoEnt                     (* [comment removed for export] *)
| ODir                       (* [comment removed for export] *)
| OFile (lo hi : Z).         (* [comment removed for export] *)

(* [comment removed for export] *)
Record iotab : Type := IOT {
  io_open : open_outcome; io_blob : nat;
  io_cfg : option (Z * Z); io_room : option (Z * Z); io_cmod : option (Z * Z); io_b1s : option (Z * Z) }.
Definition iot_simple (o : open_outcome) (jb : nat) : iotab := IOT o jb None None None None.

Definition CHZ : Z := 65536.
Definition FCAP : Z := 2 ^ 26.

(* [comment removed for export] *)
Definition XB0 (jb : nat) : expr := EBlob false jb 0 1.
Definition XB1S (jb : nat) : expr := EBlob true jb 1 1.
Definition XB2 (jb : nat) : expr := EBlob false jb 2 1.
Definition CFGX (jb : nat) : expr :=
  EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit (2 ^ 57)) (XB1S jb)) (ELit 49)) (XB0 jb).
Definition XCM (jb : nat) : expr := EAlu ALU_AND (XB2 jb) (ELit 3).
Definition XROOM (jb : nat) (len : expr) : expr := esub (esub len (ELit 6)) (CFGX jb).

(* [comment removed for export] *)
Definition hbyte (i : nat) (c : list byte) : Z := bv_unsigned (nth i c (Z_to_bv 8 0)).
Definition cfglen (c : list byte) : Z := (hbyte 0 c + 256 * hbyte 1 c) mod 32768.
Definition flenZ (c : list byte) : Z := Z.min (Z.of_nat (length c)) (2 ^ 26).
Definition room (c : list byte) : Z := flenZ c - 6 - cfglen c.
Definition cmod (c : list byte) : Z := hbyte 2 c mod 4.
Definition b1s (c : list byte) : Z := bv_swrap 8 (hbyte 1 c) mod 2 ^ 64.

Definition in_opt (o : option (Z * Z)) (v : Z) : Prop :=
  match o with Some (lo, hi) => lo <= v <= hi | None => True end.
(* [comment removed for export] *)
Definition hdr_ok (T : iotab) (c : list byte) : Prop :=
  in_opt (io_cfg T) (cfglen c)
  /\ (match io_room T with Some (lo, hi) => lo <= room c <= hi | None => True end)   (* [comment removed for export] *)
  /\ in_opt (io_cmod T) (cmod c)
  /\ in_opt (io_b1s T) (b1s c).

Section WithSegs.
Variable segs : list Segment.
Variable nx0 : nat.
Variable T : iotab.

(* [comment removed for export] *)
Definition at_sys (cs : acs) (nr : Z) : bool :=
  is_ecall_at segs cs && match reg_lit cs 17 with Some z => Z.eqb z nr | None => false end.

Definition reg_is (cs : acs) (r : nat) (z : Z) : bool :=
  match reg_lit cs r with Some z' => Z.eqb z' z | None => false end.

(* [comment removed for export] *)
Definition ret_with (cs : acs) (r : expr) (k : list kentry) (nx : nat) (f : afd) : acs :=
  let ss := a_ss cs in
  ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 r) k nx)
      (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) f (a_tidset cs).
Definition ret_simple (cs : acs) (r : expr) : acs := ret_with cs r (kn cs) (nxt cs) (a_fd cs).

Definition is_std (f : afd) : bool := match f with FdStd => true | _ => false end.

(* [comment removed for export] *)
Definition open_ignored : Z := 524288 + 32768 + 2048.   (* [comment removed for export] *)
Definition openat_args_ok (cs : acs) : bool :=
  let k := kn cs in
  at_sys cs 56
  && match reg_lit cs 10 with Some z => Z.eqb (z mod 2 ^ 32) (2 ^ 32 - 100) | None => false end
  && len_eqb k (reg cs 11) e_str1
  && match reg_lit cs 12 with Some z => Z.eqb (Z.ldiff z open_ignored) 0 | None => false end
  && match xlo k (EVar V_ARGC) with Some lo => Z.leb 2 lo | None => false end
  && is_std (a_fd cs).

(* [comment removed for export] *)
Definition node_openat2 (cs : acs) : option (acs * acs) :=
  match io_open T with
  | ODir | OFile _ _ =>
      if (openat_args_ok cs && fresh_ok nx0 cs)%bool then
        let v := nxt cs in let k := kn cs in
        let err := ret_with cs (EVar v) (KRange (EVar v) (two64 - 24) (two64 - 12) :: k) (S v) FdStd in
        let ok := match io_open T with
                  | OFile lo hi => ret_with cs (ELit 3) (KRange (EVar v) (Z.max lo 0) (Z.min hi FCAP) :: k) (S v)
                                           (FdFile (io_blob T) (EVar v) (ELit 0))
                  | _ => ret_with cs (ELit 3) k (S v) FdDir
                  end in
        Some (err, ok)
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_openat_err (cs : acs) : option acs :=
  if openat_args_ok cs then
    match io_open T with
    | OTooLong => Some (ret_simple cs (ELit (two64 - 36)))
    | ONoEnt => Some (ret_simple cs (ELit (two64 - 2)))
    | _ => None
    end
  else None.

(* [comment removed for export] *)
Definition dst_hi_ok (k : list kentry) (db : expr) (dk : Z) (n : expr) : bool :=
  match xhi k db, xhi k n with
  | Some h, Some hn => Z.leb (h + dk + hn) (2 ^ 47)   (* [comment removed for export] *)
  | _, _ => false
  end.
Definition dst_ok (cs : acs) (n : expr) : option (expr * Z) :=
  let k := kn cs in
  let '(db, dk) := split_lit (reg cs 11) in
  if (flat_x k db dk n && kwritable_x k k db dk n && dst_hi_ok k db dk n)%bool then Some (db, dk) else None.

(* [comment removed for export] *)
Definition kcut (db : expr) (dk : Z) (k : list kentry) : list kentry :=
  match db with ELit 0 => kimg_cut k (dk mod two64) CHZ | _ => k end.

(* [comment removed for export] *)
Definition node_read (cs : acs) (args : list expr) : option acs :=
  let k := kn cs in
  match args, a_fd cs with
  | [ELit jz], FdFile kb len off =>
      if (at_sys cs 63 && reg_is cs 10 3 && reg_is cs 12 CHZ && Z.leb 0 jz
          && match lit_of off with Some o => Z.eqb o (CHZ * jz) | None => false end
          && Z.leb (CHZ * (jz + 1)) FCAP)%bool then
        match dst_ok cs (ELit CHZ), xlo k len, xhi k len with
        | Some (db, dk), Some llo, Some lhi =>
            let j := Z.to_nat jz in
            let k := kcut db dk k in     (* [comment removed for export] *)
            let k1 := kn_havoc k db dk (ELit CHZ) in
            if Z.leb (CHZ * (jz + 1)) llo then
              Some (ret_with cs (ELit CHZ) (KBlob (SA db dk) (ELit CHZ) (kb + j)%nat :: k1) (nxt cs)
                             (FdFile kb len (ELit (CHZ * (jz + 1)))))
            else if (Z.leb (CHZ * jz) llo && Z.ltb lhi (CHZ * (jz + 1)))%bool then
              let n := esub len (ELit (CHZ * jz)) in
              Some (ret_with cs n (KBlob (SA db dk) n (kb + j)%nat :: k1) (nxt cs) (FdFile kb len len))
            else None
        | _, _, _ => None
        end
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition node_read_havoc (cs : acs) : option acs :=
  let k := kn cs in
  match a_fd cs with
  | FdFile kb len off =>
      if (at_sys cs 63 && reg_is cs 10 3 && reg_is cs 12 CHZ && lin_ge0 k [(len, 0)] [(off, CHZ)])%bool then
        match dst_ok cs (ELit CHZ) with
        | Some (db, dk) =>
            let k := kcut db dk k in     (* [comment removed for export] *)
            (* [comment removed for export] *)
            Some (ret_with cs (ELit CHZ) (KUnk (SA db dk) (ELit CHZ) :: kn_havoc k db dk (ELit CHZ)) (nxt cs) (FdFile kb len (eaddz off CHZ)))
        | None => None
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_read_havoc_short (cs : acs) : option acs :=
  let k := kn cs in
  match a_fd cs with
  | FdFile kb len off =>
      if (at_sys cs 63 && reg_is cs 10 3 && reg_is cs 12 CHZ
          && lin_ge0 k [(len, 0)] [(off, 0)] && lin_ge0 k [(off, CHZ - 1)] [(len, 0)]
          && match xhi k len with Some h => Z.ltb h FCAP | None => false end)%bool then
        match dst_ok cs (ELit CHZ) with
        | Some (db, dk) =>
            let k := kcut db dk k in     (* [comment removed for export] *)
            (* [comment removed for export] *)
            Some (ret_with cs (esub len off) (KUnk (SA db dk) (esub len off) :: kn_havoc k db dk (ELit CHZ)) (nxt cs) (FdFile kb len len))
        | None => None
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition opt_fact (o : option (Z * Z)) (e : expr) : list kentry :=
  match o with Some (lo, hi) => [KRange e lo hi] | None => [] end.
(* [comment removed for export] *)
Definition XOVER (jb : nat) (len : expr) : expr := esub (eaddz (CFGX jb) 6) len.
Definition room_fact (len : expr) : list kentry :=
  match io_room T with
  | Some (lo, hi) => if Z.leb 0 lo then [KRange (XROOM (io_blob T) len) lo hi]
                     else if Z.ltb hi 0 then [KRange (XOVER (io_blob T) len) (- hi) (- lo)] else []
  | None => []
  end.
Definition header_facts (len : expr) : list kentry :=
  opt_fact (io_cfg T) (CFGX (io_blob T)) ++ room_fact len
  ++ opt_fact (io_cmod T) (XCM (io_blob T)) ++ opt_fact (io_b1s T) (XB1S (io_blob T)).
Definition node_header_facts (cs : acs) : option acs :=
  match io_open T, a_fd cs with
  | OFile flo fhi, FdFile kb len off =>
      if Nat.eqb kb (io_blob T)
      then Some (set_kn cs (KRange len (Z.max flo 0) (Z.min fhi FCAP) :: header_facts len ++ kn cs)) else None   (* [comment removed for export] *)
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition lensplit_len (q r : nat) : expr := eadd (escale CHZ (EVar q)) (EVar r).
Definition node_lensplit (cs : acs) : option acs :=
  let k := kn cs in
  match a_fd cs with
  | FdFile kb (EVar v) off =>
      match xlo k (EVar v), xhi k (EVar v) with
      | Some lo, Some hi =>
          if (fresh_ok NX0 cs && Z.leb 0 lo && Z.leb hi FCAP)%bool then   (* [comment removed for export] *)
            let q := nxt cs in let r := S q in
            let lenE := lensplit_len q r in
            let kf := [KRange (EVar r) 0 (CHZ - 1); KRange (EVar q) (lo / CHZ) (hi / CHZ); KRange lenE lo hi] in
            let ss := a_ss cs in
            Some (ACS (mk_ss (pc cs) (s_regs ss) (kf ++ k) (S r))
                     (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs)
                     (FdFile kb lenE off) (a_tidset cs))
          else None
      | _, _ => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition residue_sharp (k : list kentry) (e ne : expr) (logc : Z) : list kentry :=
  let '(e', s) := deand e in
  if Z.ltb 0 s then
    match xlo1 k e', xhi1 k e' with
    | Some lo', Some _ =>
        if Z.leb s lo' then
          let '(c0, ts) := lin_of e' in
          let a := Z.min (Z.min (ealign k (unlin (0, ts))) logc) 40 in
          let m := 2 ^ a in
          let rlo := c0 mod m in
          [KRange (esub e' ne) rlo (s - ((s - rlo) mod m))]
        else []
    | _, _ => []
    end
  else [].

Definition node_fresha (cs : acs) (r : nat) (logc : Z) (base : option nat) : option acs :=
  let k := kn cs in let c := 2 ^ logc in
  let b := match base with Some rb => reg cs rb | None => ELit 0 end in
  let e := match base with Some _ => esub (reg cs r) b | None => reg cs r end in
  if (Nat.ltb 0 r && Nat.ltb r 32 && Z.leb 0 logc && Z.leb logc 40 && Z.leb logc (ealign k e)
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) e && fresh_ok NX0 cs)%bool then
    match xlo2 k e, xhi2 k e with
    | Some lo, Some hi =>
        let v := nxt cs in
        let ne := escale c (EVar v) in
        let kf := KRange (EVar v) ((lo + c - 1) / c) (hi / c) :: KRange (esub e ne) 0 0 :: residue_sharp k e ne logc in
        Some (bump (set_reg (add_kn cs kf) r (match base with Some _ => eadd b ne | None => ne end)) 1)
    | _, _ => None
    end
  else None.

(* [comment removed for export] *)
Definition srl_atom_fact (k : list kentry) (a : expr) : list kentry :=
  match a with
  | EAlu ALU_SRL x (ELit s) =>
      if (Z.leb 1 s && Z.leb s 40 && lin_nowrap k x)%bool then
        let '(c0, ts) := lin_of x in
        let al := Z.min (ealign k (unlin (0, ts))) s in
        if Z.leb 1 al then
          let ma := 2 ^ al in let m := 2 ^ s in
          let rlo := c0 mod ma in
          let rhi := m - 1 - ((m - 1 - rlo) mod ma) in
          KRange (srl_rem x m) rlo rhi
          :: (if (Z.leb rhi c0 && Z.ltb c0 two64)%bool
              then [KRange (esub (escale m a) (unlin (0, ts))) (c0 - rhi) (c0 - rlo)]   (* [comment removed for export] *)
              else [])
        else []
      else []
  | _ => []
  end.

Definition node_srlsharp (cs : acs) (r : nat) : option acs :=
  if (Nat.ltb 0 r && Nat.ltb r 32)%bool then
    let k := kn cs in
    let '(_, ts) := lin_of (reg cs r) in
    Some (set_kn cs (flat_map (fun t => srl_atom_fact k (snd t)) ts ++ k))
  else None.

(* [comment removed for export] *)
Definition srl_window (k : list kentry) (x : expr) (s : Z) : option (Z * Z) :=
  if (Z.leb 1 s && Z.leb s 40 && lin_nowrap k x)%bool then
    let '(c0, ts) := lin_of x in
    let al := Z.min (ealign k (unlin (0, ts))) s in
    if Z.leb 1 al then
      let ma := 2 ^ al in let m := 2 ^ s in
      let rlo := c0 mod ma in Some (rlo, m - 1 - ((m - 1 - rlo) mod ma))
    else None
  else None.

(* [comment removed for export] *)
Definition as_round (e : expr) : option (Z * expr * Z) :=
  match e with
  | EMd M_MUL (ELit m) (EAlu ALU_SRL x (ELit s)) => Some (m, x, s)
  | _ => None
  end.
Definition srl_pair_fact (k : list kentry) (e1 e2 : expr) : list kentry :=
  match as_round e1, as_round e2 with
  | Some (m1, x1, s1), Some (m2, x2, s2) =>
      let '(c1, ts1) := lin_of x1 in let '(c2, ts2) := lin_of x2 in
      if (Z.eqb s1 s2 && Z.eqb m1 (2 ^ s1) && Z.eqb m2 (2 ^ s1) && expr_eqb (unlin (0, ts1)) (unlin (0, ts2))
          && lin_nowrap k x1 && lin_nowrap k x2)%bool then
        match srl_window k x1 s1 with
        | Some (rlo1, rhi1) =>
            let m := 2 ^ s1 in let d := c2 - c1 in let kk := d mod m in
            let lo := if Z.ltb (rhi1 + kk) m then d - kk else if Z.leb m (rlo1 + kk) then d - kk + m else d - kk in
            let hi := if Z.leb m (rlo1 + kk) then d - kk + m else if Z.ltb (rhi1 + kk) m then d - kk else d - kk + m in
            if (Z.leb 0 lo && Z.ltb hi two64)%bool then [KRange (esub e2 e1) lo hi] else []
        | None => []
        end
      else []
  | _, _ => []
  end.

Definition node_srlsharp2 (cs : acs) (r1 r2 : nat) : option acs :=
  if (Nat.ltb 0 r1 && Nat.ltb r1 32 && Nat.ltb 0 r2 && Nat.ltb r2 32)%bool then
    let k := kn cs in
    let '(_, ts1) := lin_of (reg cs r1) in let '(_, ts2) := lin_of (reg cs r2) in
    Some (set_kn cs (srl_pair_fact k (reg cs r1) (reg cs r2)
                     ++ flat_map (fun t => srl_atom_fact k (snd t)) ts1
                     ++ flat_map (fun t => srl_atom_fact k (snd t)) ts2 ++ k))
  else None.

(* [comment removed for export] *)
Definition node_droplenfacts (cs : acs) : option acs :=
  match a_fd cs with
  | FdFile _ len _ => Some (set_kn cs (List.filter (fun K => match K with KRange e _ _ => negb (expr_eqb e len) | _ => true end) (kn cs)))
  | _ => None
  end.

(* [comment removed for export] *)
Definition cnt_ok (cs : acs) : bool :=
  let k := kn cs in
  match xlo k (reg cs 12), xhi k (reg cs 12) with
  | Some lo, Some hi => Z.leb 1 lo && Z.leb hi CHZ
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition node_read_eof (cs : acs) : option acs :=
  let k := kn cs in
  match a_fd cs with
  | FdFile kb len off =>
      if (at_sys cs 63 && reg_is cs 10 3 && len_eqb k off len && cnt_ok cs
          && match xhi k len with Some h => Z.ltb h FCAP | None => false end)%bool then
        match dst_ok cs (reg cs 12) with
        | Some _ => Some (ret_simple cs (ELit 0))
        | None => None
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_read_dir (cs : acs) : option acs :=
  match a_fd cs with
  | FdDir =>
      if (at_sys cs 63 && reg_is cs 10 3 && cnt_ok cs)%bool then
        match dst_ok cs (reg cs 12) with
        | Some _ => Some (ret_simple cs (ELit (two64 - 21)))
        | None => None
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_close (cs : acs) : option acs :=
  if (at_sys cs 57 && reg_is cs 10 3 && negb (is_std (a_fd cs)))%bool
  then Some (ret_with cs (ELit 0) (kn cs) (nxt cs) FdStd) else None.

(* [comment removed for export] *)
Definition node_ioctl (cs : acs) : option acs :=
  if (at_sys cs 29 && reg_is cs 10 1 && reg_is cs 11 0x5413)%bool
  then Some (ret_simple cs (ELit (two64 - 25))) else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xn_ws (id : nat) (args : list expr) (cs : acs) : option (list (saddr * expr)) :=
  match id with
  | 11%nat | 12%nat | 17%nat =>
      match dst_ok cs (ELit CHZ) with Some (db, dk) => Some [(SA db dk, ELit CHZ)] | None => None end
  | 13%nat => Some []
  | _ => None
  end.

Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with
  | 10%nat => node_openat_err cs
  | 11%nat => node_read cs args
  | 12%nat => node_read_havoc cs
  | 13%nat => node_read_eof cs
  | 14%nat => node_read_dir cs
  | 15%nat => node_close cs
  | 16%nat => node_ioctl cs
  | 17%nat => node_read_havoc_short cs
  | 18%nat => node_header_facts cs
  | 19%nat => node_lensplit cs
  | 22%nat => match args with
             | [ELit r; ELit logc] => if Z.leb 0 r then node_fresha cs (Z.to_nat r) logc None else None
             | [ELit r; ELit logc; ELit rb] => if (Z.leb 0 r && Z.ltb 0 rb && Z.ltb rb 32)%bool then node_fresha cs (Z.to_nat r) logc (Some (Z.to_nat rb)) else None
             | _ => None end
  | 24%nat => node_droplenfacts cs
  | 23%nat => match args with
             | [ELit r] => if Z.leb 0 r then node_srlsharp cs (Z.to_nat r) else None
             | [ELit r2; ELit r1] => if (Z.leb 0 r1 && Z.leb 0 r2)%bool then node_srlsharp2 cs (Z.to_nat r1) (Z.to_nat r2) else None
             | _ => None end
  | _ => None
  end.

Definition xb (id : nat) (args : list expr) (cs : acs) : option (acs * acs) :=
  match id with
  | 0%nat => node_openat2 cs
  | _ => None
  end.

End WithSegs.
End ION.
