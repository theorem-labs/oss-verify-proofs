(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3B AsanPlanCore FContractAsan AsanPGVal.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2B. Import APC.
Open Scope Z_scope.

Module FN.
Section X.
  Variable segs : list Segment.
  Variable A : atable.
  Variable nx0 : N.
  Variable P : FAParams.

  (* [comment removed for export] *)
  Definition cell_is (k : list kentry) (b : expr) (off : Z) (w : nat) (v : Z) : bool :=
    flat_x k b off (ELit (Z.of_nat w)) &&
    match know_lookup segs k b off w false [] [] with
    | LHit e sc _ => match sc, erange k e with [], Some (lo, hi) => Z.eqb lo v && Z.eqb hi v | _, _ => false end
    | _ => false
    end.
  (* [comment removed for export] *)
  Definition cell_expr (k : list kentry) (b : expr) (off : Z) : option expr :=
    if flat_x k b off (ELit 8) then
      match know_lookup segs k b off 8 false [] [] with LHit e [] _ => Some e | _ => None end
    else None.
  (* [comment removed for export] *)
  Definition rw_lit (k : list kentry) (b : expr) (off n : Z) : bool := kwritable k k b off n && flat_x k b off (ELit n).
  Definition rw_x (k : list kentry) (b : expr) (off : Z) (n : expr) : bool := kwritable_x k k b off n && flat_x k b off n.
  (* [comment removed for export] *)
  Definition zero_lit (k : list kentry) (b : expr) (off n : Z) : bool := kzero_x k k b off (ELit n) && flat_x k b off (ELit n).
  (* [comment removed for export] *)
  Definition gsh_ok (k : list kentry) (r : Z * Z * Z) : bool :=
    let '(a, cnt, v) := r in
    Z.ltb 0 cnt && Z.leb 0 a && Z.ltb (a + cnt) two64 &&
    forallb (fun i => cell_is k (ELit 0) (a + Z.of_nat i) 1 v) (seq 0 (Z.to_nat cnt)).
  Definition kcell_ok (k : list kentry) (c : Z * Z * Z) : bool :=
    let '(a, w, v) := c in
    Z.leb 1 w && Z.leb w 8 && Z.leb 0 a && cell_is k (ELit 0) a (Z.to_nat w) v.
  Definition pristine_ok (k : list kentry) (r : Z * Z) : bool :=
    Z.leb 0 (fst r) && Z.leb (fst r) (snd r) && img_cov k (fst r) (snd r).
  (* [comment removed for export] *)
  Definition apart_all (k : list kentry) (ws : list (expr * Z * expr)) (b : expr) (off : Z) (w : Z) : bool :=
    forallb (fun r => let '(wb, wk, wn) := r in ranges_apart_x k b off (ELit w) wb wk wn) ws.

  (* [comment removed for export] *)
  Definition havoc1 (k : list kentry) (b : expr) (off : Z) (n : expr) : list kentry :=
    match b, n with
    | ELit 0, ELit len => kn_havocK (kimg_cut k off len) b off n   (* [comment removed for export] *)
    | _, _ => kn_havocK k b off n
    end.
  Fixpoint havocs (k : list kentry) (ws : list (expr * Z * expr)) : list kentry :=
    match ws with
    | [] => k
    | (b, off, n) :: ws' => havocs (havoc1 k b off n) ws'
    end.

  (* [comment removed for export] *)
  Record fctx := FC {
    c_ret : Z; c_sp : expr; c_spb : expr; c_spk : Z; c_data : expr; c_db : expr; c_dk : Z; c_ne : expr;
    c_efs : expr; c_fsb : expr; c_fsk : Z; c_edb : expr; c_dbb : expr; c_dbk : Z;
    c_ectx : expr; c_cxb : expr; c_cxk : Z; c_ethr : expr; c_thb : expr; c_thk : Z;
    c_nlo : Z; c_nhi : Z; c_dlo : Z; c_dhi : Z; c_splo : Z; c_sphi : Z; c_flo : Z; c_fhi : Z;
    c_shf : expr * Z * expr;      (* [comment removed for export] *)
    c_shs : expr * Z * expr;      (* [comment removed for export] *)
    c_shd : expr * Z;             (* [comment removed for export] *)
    c_ws : list (expr * Z * expr); (* [comment removed for export] *)
    c_wall : list (expr * Z * expr) (* [comment removed for export] *)
  }.

  Definition mk_ctx (cs : acs) : option fctx :=
    let k := kn cs in
    if negb (Z.eqb (pc cs) (fa_entry P)) then None else
    match ret_lit cs, reg_lit cs 4 with
    | Some ret, Some tp =>
      if negb (Z.eqb ret (fa_ret P) && Z.eqb tp (fa_tp P))%bool then None else
      let sp := reg cs 2 in let data := reg cs 10 in let ne := reg cs 11 in
      let '(spb, spk) := split_lit sp in let '(db, dk) := split_lit data in
      match cell_expr k (ELit 0) (fa_tp P), cell_expr k (ELit 0) (fa_tp P + 0x8), cell_expr k (ELit 0) (fa_tsd P) with
      | Some efs, Some edb, Some ectx =>
        let '(fsb, fsk) := split_lit efs in let '(dbb, dbk) := split_lit edb in let '(cxb, cxk) := split_lit ectx in
        match cell_expr k cxb (cxk + 0x98) with
        | Some ethr =>
          let '(thb, thk) := split_lit ethr in
          match xlo k ne, xhi k ne, xlo k data, xhi k data, xlo k sp, xhi k sp, xlo k efs, xhi k efs with
          | Some nlo, Some nhi, Some dlo, Some dhi, Some splo, Some sphi, Some flo, Some fhi =>
            let fr := fa_frame P in
            let shf := shadow_of A k (eaddz sp (- fr)) (ELit fr) in
            let shs := shadow_of A k (eaddz efs FS_FRAMES) (ELit FS_FRAMES_LEN) in
            let shd := split_lit (eadd (mkSrl k data 3) (ELit (shadow_off A))) in
            let ws := [ (spb, spk - fr, ELit fr)                               (* [comment removed for export] *)
                      ; (fsb, fsk, ELit FS_HINTS)                              (* [comment removed for export] *)
                      ; (fsb, fsk + FS_FRAMES, ELit FS_FRAMES_LEN)             (* [comment removed for export] *)
                      ; (fst (fst shs), snd (fst shs), snd shs)                (* [comment removed for export] *)
                      ; (ELit 0, fa_prng P, ELit 8)                            (* [comment removed for export] *)
                      ; (ELit 0, fa_errno P, ELit 4) ] in                      (* [comment removed for export] *)
            let wall := [ (spb, spk - fr, ELit fr); (fst (fst shf), snd (fst shf), snd shf); (fsb, fsk, ELit FS_HINTS)
                        ; (fsb, fsk + FS_FLAGS, ELit FS_FLAGS_LEN); (fsb, fsk + FS_FRAMES, ELit FS_FRAMES_LEN)
                        ; (fst (fst shs), snd (fst shs), snd shs); (ELit 0, fa_prng P, ELit 8); (ELit 0, fa_errno P, ELit 4)
                        ; (spb, spk, ELit 16); (fst (fst shf), snd (fst shf) + fr / 8, ELit 2) ] in   (* [comment removed for export] *)
            Some (FC ret sp spb spk data db dk ne efs fsb fsk edb dbb dbk ectx cxb cxk ethr thb thk
                     nlo nhi dlo dhi splo sphi flo fhi shf shs shd ws wall)
          | _, _, _, _, _, _, _, _ => None
          end
        | None => None
        end
      | _, _, _ => None
      end
    | _, _ => None
    end.

  (* [comment removed for export] *)
  Definition partial_ok (k : list kentry) (c : fctx) : bool :=
    Z.leb 3 (ealign k (c_ne c)) ||
    let '(pb, pk) := split_lit (eadd (eadd (mkSrl k (c_data c) 3) (ELit (shadow_off A))) (mkSrl k (c_ne c) 3)) in
    (flat_x k pb pk (ELit 1) &&
     match know_lookup segs k pb pk 1 false [] [] with
     | LHit e sc _ =>
         match sc with
         | [] => PGV.partial_val_ok k (c_ne c) e   (* [comment removed for export] *)
         | _ => false
         end
     | _ => false
     end).

  (* [comment removed for export] *)
  Definition chain_ok (k : list kentry) (c : fctx) : bool :=
    flat_x k (c_dbb c) (c_dbk c) (ELit 32) && flat_x k (c_cxb c) (c_cxk c) (ELit 160) && flat_x k (c_thb c) (c_thk c) (ELit 64) &&
    match xlo k (c_edb c), xlo k (c_ectx c), xlo k (c_ethr c) with
    | Some dblo, Some cxlo, Some thlo => Z.leb 1 dblo && Z.leb 1 cxlo && Z.leb 1 thlo
    | _, _, _ => false
    end.

  (* [comment removed for export] *)
  Definition shd_split (k : list kentry) (e : expr) : option (expr * expr) :=
    let l := lin_of e in
    let '(dts, rts) := lsplit_divc 8 (snd l) in
    let B := unlin (fst l - fst l mod 8, dts) in
    let t := unlin (fst l mod 8, rts) in
    if (Z.leb 3 (ealign k B) && lin_nowrap k e && lin_nowrap_l k (fst l - fst l mod 8) dts && lin_nowrap_l k (fst l mod 8) rts)%bool
    then Some (B, t) else None.

  (* [comment removed for export] *)
  Definition tests (cs : acs) (c : fctx) : list bool :=
    let k := kn cs in
    let fr := fa_frame P in
    let '(shfb, shfk, shfn) := c_shf c in let '(shsb, shsk, shsn) := c_shs c in let '(shdb, shdk) := c_shd c in
    [ (* [comment removed for export] *)
      fresh_ok nx0 cs
    ; Z.eqb (shadow_off A) (fa_shoff P) && Z.eqb (fr mod 32) 0 && Z.ltb 0 fr && Z.ltb fr F_SPLO
    ; Z.leb 0 (c_nlo c) && Z.ltb (c_nhi c) (fa_nmax P)
    ; Z.leb 1 (c_dlo c)                                                            (* [comment removed for export] *)
    ; Z.ltb (c_dhi c + c_nhi c) (2 ^ 63) || lin_ge0 k [(ELit (2 ^ 63), (-1))] [(c_data c, 0); (c_ne c, 0)]     (* [comment removed for export] *)
    ; Z.leb 4 (ealign k (c_data c))                                                (* [comment removed for export] *)
    ; Z.eqb (c_nhi c) 0 || (Z.leb 1 (c_nlo c) && (Z.leb HIGHMEM_LO (c_dlo c) || off_band k (a_maps cs) (c_data c) 0 (c_ne c))   (* [comment removed for export] *)
                            && (Z.leb (c_dhi c + c_nhi c) (VA_HI - 64) || lin_ge0 k [(ELit (VA_HI - 64), 0)] [(c_data c, 0); (c_ne c, 0)]))   (* [comment removed for export] *)
    ; Z.leb 4 (ealign k (c_sp c))                                                  (* [comment removed for export] *)
    ; Z.leb F_SPLO (c_splo c) && Z.leb (c_sphi c + 16) F_SPHI                      (* [comment removed for export] *)
    ; Z.leb 12 (ealign k (c_efs c)) && (Z.leb HIGHMEM_LO (c_flo c) || off_band k (a_maps cs) (c_efs c) 0 (ELit FS_LEN))   (* [comment removed for export] *)
      && Z.leb (c_fhi c + FS_LEN) VA_HI   (* [comment removed for export] *)
    (* [comment removed for export] *)
    ; Z.leb (c_dhi c + c_nhi c + 4096) (c_splo c - fr) || lin_ge0 k [(c_sp c, (- fr - 4096))] [(c_data c, 0); (c_ne c, 0)]   (* [comment removed for export] *)
    ; Z.leb (c_fhi c + FS_LEN + 4096) (c_splo c - fr) || lin_ge0 k [(c_sp c, (- fr - 4096))] [(c_efs c, 0); (ELit FS_LEN, 0)]   (* [comment removed for export] *)
    ; Z.leb (c_fhi c + FS_LEN + 4096) (c_dlo c) || Z.leb (c_dhi c + c_nhi c) (c_flo c)       (* [comment removed for export] *)
      || (Z.leb 4096 (c_dlo c) && negb (Z.eqb (c_nhi c) 0) && ranges_apart_x k (c_db c) (c_dk c - 4096) (eaddz (c_ne c) 4096) (c_fsb c) (c_fsk c) (ELit FS_LEN))
    (* [comment removed for export] *)
    ; Z.eqb (c_nhi c) 0 || rw_x k (c_db c) (c_dk c) (c_ne c)
    ; Z.eqb (c_nhi c) 0 || ((Z.ltb (c_nhi c) 8 || kzero_x k k shdb shdk (mkSrl k (c_ne c) 3)) && partial_ok k c)
    ; Z.eqb (c_nhi c) 0 || rw_x k shdb (shdk - 2) (eaddz (mkSrl k (c_ne c) 3) 6)
    (* [comment removed for export] *)
    ; rw_lit k (c_spb c) (c_spk c - fr) (fr + 16)                                  (* [comment removed for export] *)
    ; kzero_x k k shfb shfk shfn && flat_x k shfb shfk shfn && kwritable_x k k shfb shfk (ELit (fr / 8 + 2))   (* [comment removed for export] *)
    ; rw_lit k shfb (shfk - 8) 8
    ; rw_lit k shfb (shfk + fr / 8) 10                                              (* [comment removed for export] *)
    (* [comment removed for export] *)
    ; rw_lit k (c_fsb c) (c_fsk c) FS_HINTS
    ; cell_is k (c_fsb c) (c_fsk c + FS_SSL) 8 20
    ; cell_is k (c_fsb c) (c_fsk c + FS_NEEDSGC) 1 0
    ; zero_lit k (c_fsb c) (c_fsk c + FS_FLAGS) FS_FLAGS_LEN && rw_lit k (c_fsb c) (c_fsk c + FS_FLAGS) FS_FLAGS_LEN
    ; rw_lit k (c_fsb c) (c_fsk c + FS_FRAMES) FS_FRAMES_LEN
    ; rw_lit k shsb (shsk - 8) (FS_FRAMES_LEN / 8 + 16)
    (* [comment removed for export] *)
    ; cell_is k (c_dbb c) (c_dbk c + 0x18) 8 (fa_tp P)
    ; rw_lit k (c_thb c) (c_thk c + 0x30) 16
    ; apart_all k (c_wall c) (c_dbb c) (c_dbk c + 0x18) 8 && apart_all k (c_wall c) (c_cxb c) (c_cxk c + 0x98) 8
      && apart_all k (c_wall c) (c_thb c) (c_thk c + 0x30) 16
    (* [comment removed for export] *)
    ; forallb (kcell_ok k) (fa_kcells P)
    ; forallb (gsh_ok k) (fa_gsh P)
    ; forallb (pristine_ok k) (fa_pristine P)
    ; rw_lit k (ELit 0) (fa_prng P) 8 && rw_lit k (ELit 0) (fa_errno P) 4
    (* [comment removed for export] *)
    ; Z.eqb (c_nhi c) 0 || (Z.leb 3 (ealign k shdb) && rw_x k shdb (shdk - shdk mod 8) (eaddz (mkSrl k (c_ne c) 3) (9 + shdk mod 8)))
      || rw_x k shdb (shdk - 7) (eaddz (mkSrl k (c_ne c) 3) 16)   (* [comment removed for export] *)
      || match shd_split k shdb with   (* [comment removed for export] *)
         | Some (B, t) =>
             match xhi k t with
             | Some th => Z.ltb (th + c_nhi c / 8 + 16) two64 && rw_x k B (shdk - shdk mod 8) (eaddz (eadd t (mkSrl k (c_ne c) 3)) (9 + shdk mod 8))
             | None => false
             end
         | None => false
         end
    (* [comment removed for export] *)
    ; chain_ok k c
    (* [comment removed for export] *)
    ; Z.leb (fa_imgend P) (c_flo c)
    ]%bool.

  Fixpoint first_false (i : nat) (l : list bool) : nat :=
    match l with [] => 0 | b :: l' => if b then first_false (S i) l' else i end.

  (* [comment removed for export] *)
  Definition node_F_ref (cs : acs) : option acs :=
    match mk_ctx cs with
    | Some c => if forallb (fun b => b) (tests cs c)
                then after_call nx0 cs (fa_ret P) (Some (ELit 0)) (havocs (kn cs) (c_ws c))
                else None
    | None => None
    end.

  (* [comment removed for export] *)
  Definition cell_isB (bc : bctx) (kx : AX2B.kix) (b : expr) (off : Z) (w : nat) (v : Z) : bool :=
    flat_xB bc b off (ELit (Z.of_nat w)) &&
    match know_lookupBX segs bc kx b off w false [] [] with
    | LHit e sc _ => match sc, erangeB bc e with [], Some (lo, hi) => Z.eqb lo v && Z.eqb hi v | _, _ => false end
    | _ => false
    end.
  Definition cell_exprB (bc : bctx) (kx : AX2B.kix) (b : expr) (off : Z) : option expr :=
    if flat_xB bc b off (ELit 8) then
      match know_lookupBX segs bc kx b off 8 false [] [] with LHit e [] _ => Some e | _ => None end
    else None.
  Definition rw_litB (bc : bctx) (k : list kentry) (b : expr) (off n : Z) : bool := kwritableB bc k b off n && flat_xB bc b off (ELit n).
  Definition rw_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool := kwritable_xB bc k b off n && flat_xB bc b off n.
  Definition zero_litB (bc : bctx) (k : list kentry) (b : expr) (off n : Z) : bool := kzero_xB bc k b off (ELit n) && flat_xB bc b off (ELit n).
  Definition gsh_okB (bc : bctx) (kx : AX2B.kix) (r : Z * Z * Z) : bool :=
    let '(a, cnt, v) := r in
    Z.ltb 0 cnt && Z.leb 0 a && Z.ltb (a + cnt) two64 &&
    forallb (fun i => cell_isB bc kx (ELit 0) (a + Z.of_nat i) 1 v) (seq 0 (Z.to_nat cnt)).
  Definition kcell_okB (bc : bctx) (kx : AX2B.kix) (c : Z * Z * Z) : bool :=
    let '(a, w, v) := c in
    Z.leb 1 w && Z.leb w 8 && Z.leb 0 a && cell_isB bc kx (ELit 0) a (Z.to_nat w) v.
  Definition pristine_okB (bc : bctx) (r : Z * Z) : bool :=
    Z.leb 0 (fst r) && Z.leb (fst r) (snd r) && img_covB bc (fst r) (snd r).
  Definition apart_allB (bc : bctx) (ws : list (expr * Z * expr)) (b : expr) (off : Z) (w : Z) : bool :=
    forallb (fun r => let '(wb, wk, wn) := r in ranges_apart_xB bc b off (ELit w) wb wk wn) ws.

  Definition mk_ctxB (bc : bctx) (kx : AX2B.kix) (cs : acs) : option fctx :=
    let k := kn cs in
    if negb (Z.eqb (pc cs) (fa_entry P)) then None else
    match ret_lit cs, reg_lit cs 4 with
    | Some ret, Some tp =>
      if negb (Z.eqb ret (fa_ret P) && Z.eqb tp (fa_tp P))%bool then None else
      let sp := reg cs 2 in let data := reg cs 10 in let ne := reg cs 11 in
      let '(spb, spk) := split_lit sp in let '(db, dk) := split_lit data in
      match cell_exprB bc kx (ELit 0) (fa_tp P), cell_exprB bc kx (ELit 0) (fa_tp P + 0x8), cell_exprB bc kx (ELit 0) (fa_tsd P) with
      | Some efs, Some edb, Some ectx =>
        let '(fsb, fsk) := split_lit efs in let '(dbb, dbk) := split_lit edb in let '(cxb, cxk) := split_lit ectx in
        match cell_exprB bc kx cxb (cxk + 0x98) with
        | Some ethr =>
          let '(thb, thk) := split_lit ethr in
          match xloB bc ne, xhiB bc ne, xloB bc data, xhiB bc data, xloB bc sp, xhiB bc sp, xloB bc efs, xhiB bc efs with
          | Some nlo, Some nhi, Some dlo, Some dhi, Some splo, Some sphi, Some flo, Some fhi =>
            let fr := fa_frame P in
            let shf := shadow_ofB A bc (eaddz sp (- fr)) (ELit fr) in
            let shs := shadow_ofB A bc (eaddz efs FS_FRAMES) (ELit FS_FRAMES_LEN) in
            let shd := split_lit (eadd (mkSrlB bc data 3) (ELit (shadow_off A))) in
            let ws := [ (spb, spk - fr, ELit fr)                               (* [comment removed for export] *)
                      ; (fsb, fsk, ELit FS_HINTS)                              (* [comment removed for export] *)
                      ; (fsb, fsk + FS_FRAMES, ELit FS_FRAMES_LEN)             (* [comment removed for export] *)
                      ; (fst (fst shs), snd (fst shs), snd shs)                (* [comment removed for export] *)
                      ; (ELit 0, fa_prng P, ELit 8)                            (* [comment removed for export] *)
                      ; (ELit 0, fa_errno P, ELit 4) ] in                      (* [comment removed for export] *)
            let wall := [ (spb, spk - fr, ELit fr); (fst (fst shf), snd (fst shf), snd shf); (fsb, fsk, ELit FS_HINTS)
                        ; (fsb, fsk + FS_FLAGS, ELit FS_FLAGS_LEN); (fsb, fsk + FS_FRAMES, ELit FS_FRAMES_LEN)
                        ; (fst (fst shs), snd (fst shs), snd shs); (ELit 0, fa_prng P, ELit 8); (ELit 0, fa_errno P, ELit 4)
                        ; (spb, spk, ELit 16); (fst (fst shf), snd (fst shf) + fr / 8, ELit 2) ] in   (* [comment removed for export] *)
            Some (FC ret sp spb spk data db dk ne efs fsb fsk edb dbb dbk ectx cxb cxk ethr thb thk
                     nlo nhi dlo dhi splo sphi flo fhi shf shs shd ws wall)
          | _, _, _, _, _, _, _, _ => None
          end
        | None => None
        end
      | _, _, _ => None
      end
    | _, _ => None
    end.

  Definition partial_okB (bc : bctx) (kx : AX2B.kix) (k : list kentry) (c : fctx) : bool :=
    if Z.leb 3 (ealignB bc (c_ne c)) then true else   (* [comment removed for export] *)
    let '(pb, pk) := split_lit (eadd (eadd (mkSrlB bc (c_data c) 3) (ELit (shadow_off A))) (mkSrlB bc (c_ne c) 3)) in
    (if flat_xB bc pb pk (ELit 1) then
     match know_lookupBX segs bc kx pb pk 1 false [] [] with
     | LHit e sc _ =>
         match sc with
         | [] => PGV.partial_val_okB bc (c_ne c) e   (* [comment removed for export] *)
         | _ => false
         end
     | _ => false
     end else false).

  Definition chain_okB (bc : bctx) (c : fctx) : bool :=
    flat_xB bc (c_dbb c) (c_dbk c) (ELit 32) && flat_xB bc (c_cxb c) (c_cxk c) (ELit 160) && flat_xB bc (c_thb c) (c_thk c) (ELit 64) &&
    match xloB bc (c_edb c), xloB bc (c_ectx c), xloB bc (c_ethr c) with
    | Some dblo, Some cxlo, Some thlo => Z.leb 1 dblo && Z.leb 1 cxlo && Z.leb 1 thlo
    | _, _, _ => false
    end.

  Definition shd_splitB (bc : bctx) (e : expr) : option (expr * expr) :=
    let l := lin_of e in
    let '(dts, rts) := lsplit_divc 8 (snd l) in
    let B := unlin (fst l - fst l mod 8, dts) in
    let t := unlin (fst l mod 8, rts) in
    if (Z.leb 3 (ealignB bc B) && lin_nowrapB bc e && lin_nowrap_lB bc (fst l - fst l mod 8) dts && lin_nowrap_lB bc (fst l mod 8) rts)%bool
    then Some (B, t) else None.

  Definition testsB (bc : bctx) (kx : AX2B.kix) (cs : acs) (c : fctx) : list bool :=
    let k := kn cs in
    let fr := fa_frame P in
    let '(shfb, shfk, shfn) := c_shf c in let '(shsb, shsk, shsn) := c_shs c in let '(shdb, shdk) := c_shd c in
    [ (* [comment removed for export] *)
      fresh_ok nx0 cs
    ; Z.eqb (shadow_off A) (fa_shoff P) && Z.eqb (fr mod 32) 0 && Z.ltb 0 fr && Z.ltb fr F_SPLO
    ; Z.leb 0 (c_nlo c) && Z.ltb (c_nhi c) (fa_nmax P)
    ; Z.leb 1 (c_dlo c)                                                            (* [comment removed for export] *)
    (* [comment removed for export] *)
    ; if Z.ltb (c_dhi c + c_nhi c) (2 ^ 63) then true else lin_ge0B bc [(ELit (2 ^ 63), (-1))] [(c_data c, 0); (c_ne c, 0)]     (* [comment removed for export] *)
    ; Z.leb 4 (ealignB bc (c_data c))                                                (* [comment removed for export] *)
    ; if Z.eqb (c_nhi c) 0 then true else
        (if (if Z.leb 1 (c_nlo c) then (if Z.leb HIGHMEM_LO (c_dlo c) then true else off_bandB bc (a_maps cs) (c_data c) 0 (c_ne c)) else false)   (* [comment removed for export] *)
         then (if Z.leb (c_dhi c + c_nhi c) (VA_HI - 64) then true else lin_ge0B bc [(ELit (VA_HI - 64), 0)] [(c_data c, 0); (c_ne c, 0)]) else false)   (* [comment removed for export] *)
    ; Z.leb 4 (ealignB bc (c_sp c))                                                  (* [comment removed for export] *)
    ; Z.leb F_SPLO (c_splo c) && Z.leb (c_sphi c + 16) F_SPHI                      (* [comment removed for export] *)
    ; if (if Z.leb 12 (ealignB bc (c_efs c)) then (if Z.leb HIGHMEM_LO (c_flo c) then true else off_bandB bc (a_maps cs) (c_efs c) 0 (ELit FS_LEN)) else false)   (* [comment removed for export] *)
      then Z.leb (c_fhi c + FS_LEN) VA_HI else false   (* [comment removed for export] *)
    (* [comment removed for export] *)
    ; if Z.leb (c_dhi c + c_nhi c + 4096) (c_splo c - fr) then true else lin_ge0B bc [(c_sp c, (- fr - 4096))] [(c_data c, 0); (c_ne c, 0)]   (* [comment removed for export] *)
    ; if Z.leb (c_fhi c + FS_LEN + 4096) (c_splo c - fr) then true else lin_ge0B bc [(c_sp c, (- fr - 4096))] [(c_efs c, 0); (ELit FS_LEN, 0)]   (* [comment removed for export] *)
    ; if (if Z.leb (c_fhi c + FS_LEN + 4096) (c_dlo c) then true else Z.leb (c_dhi c + c_nhi c) (c_flo c)) then true       (* [comment removed for export] *)
      else (if (if Z.leb 4096 (c_dlo c) then negb (Z.eqb (c_nhi c) 0) else false) then ranges_apart_xB bc (c_db c) (c_dk c - 4096) (eaddz (c_ne c) 4096) (c_fsb c) (c_fsk c) (ELit FS_LEN) else false)
    (* [comment removed for export] *)
    ; if Z.eqb (c_nhi c) 0 then true else rw_xB bc k (c_db c) (c_dk c) (c_ne c)
    ; if Z.eqb (c_nhi c) 0 then true else (if (if Z.ltb (c_nhi c) 8 then true else kzero_xB bc k shdb shdk (mkSrlB bc (c_ne c) 3)) then partial_okB bc kx k c else false)
    ; if Z.eqb (c_nhi c) 0 then true else rw_xB bc k shdb (shdk - 2) (eaddz (mkSrlB bc (c_ne c) 3) 6)
    (* [comment removed for export] *)
    ; rw_litB bc k (c_spb c) (c_spk c - fr) (fr + 16)                                  (* [comment removed for export] *)
    ; if (if kzero_xB bc k shfb shfk shfn then flat_xB bc shfb shfk shfn else false) then kwritable_xB bc k shfb shfk (ELit (fr / 8 + 2)) else false   (* [comment removed for export] *)
    ; rw_litB bc k shfb (shfk - 8) 8
    ; rw_litB bc k shfb (shfk + fr / 8) 10                                              (* [comment removed for export] *)
    (* [comment removed for export] *)
    ; rw_litB bc k (c_fsb c) (c_fsk c) FS_HINTS
    ; cell_isB bc kx (c_fsb c) (c_fsk c + FS_SSL) 8 20
    ; cell_isB bc kx (c_fsb c) (c_fsk c + FS_NEEDSGC) 1 0
    ; zero_litB bc k (c_fsb c) (c_fsk c + FS_FLAGS) FS_FLAGS_LEN && rw_litB bc k (c_fsb c) (c_fsk c + FS_FLAGS) FS_FLAGS_LEN
    ; rw_litB bc k (c_fsb c) (c_fsk c + FS_FRAMES) FS_FRAMES_LEN
    ; rw_litB bc k shsb (shsk - 8) (FS_FRAMES_LEN / 8 + 16)
    (* [comment removed for export] *)
    ; cell_isB bc kx (c_dbb c) (c_dbk c + 0x18) 8 (fa_tp P)
    ; rw_litB bc k (c_thb c) (c_thk c + 0x30) 16
    ; if (if apart_allB bc (c_wall c) (c_dbb c) (c_dbk c + 0x18) 8 then apart_allB bc (c_wall c) (c_cxb c) (c_cxk c + 0x98) 8 else false)
      then apart_allB bc (c_wall c) (c_thb c) (c_thk c + 0x30) 16 else false
    (* [comment removed for export] *)
    ; forallb (kcell_okB bc kx) (fa_kcells P)
    ; forallb (gsh_okB bc kx) (fa_gsh P)
    ; forallb (pristine_okB bc) (fa_pristine P)
    ; if rw_litB bc k (ELit 0) (fa_prng P) 8 then rw_litB bc k (ELit 0) (fa_errno P) 4 else false
    (* [comment removed for export] *)
    ; if (if (if Z.eqb (c_nhi c) 0 then true else (if Z.leb 3 (ealignB bc shdb) then rw_xB bc k shdb (shdk - shdk mod 8) (eaddz (mkSrlB bc (c_ne c) 3) (9 + shdk mod 8)) else false))
          then true else rw_xB bc k shdb (shdk - 7) (eaddz (mkSrlB bc (c_ne c) 3) 16))   (* [comment removed for export] *)
      then true else
         match shd_splitB bc shdb with   (* [comment removed for export] *)
         | Some (B, t) =>
             match xhiB bc t with
             | Some th => if Z.ltb (th + c_nhi c / 8 + 16) two64 then rw_xB bc k B (shdk - shdk mod 8) (eaddz (eadd t (mkSrlB bc (c_ne c) 3)) (9 + shdk mod 8)) else false
             | None => false
             end
         | None => false
         end
    (* [comment removed for export] *)
    ; chain_okB bc c
    (* [comment removed for export] *)
    ; Z.leb (fa_imgend P) (c_flo c)
    ]%bool.

  Definition node_F (cs : acs) : option acs :=
    let bc := mkbc (kn cs) in let kx := AX2B.mk_kix (kn cs) in   (* [comment removed for export] *)
    match mk_ctxB bc kx cs with
    | Some c => if forallb (fun b => b) (testsB bc kx cs c)
                then after_call nx0 cs (fa_ret P) (Some (ELit 0)) (havocs (kn cs) (c_ws c))
                else None
    | None => None
    end.
  Lemma know_lookupBX_eqf2 : forall fk, know_lookupBX segs (mkbc fk) (AX2B.mk_kix fk) = know_lookup segs fk.
  Proof. intros. bcfe. rewrite know_lookupBX_eq, know_lookupB_eqf. reflexivity. Qed.
  Lemma cell_isB_eqf : forall fk, cell_isB (mkbc fk) (AX2B.mk_kix fk) = cell_is fk.
  Proof. intros. bcfe. unfold cell_isB, cell_is. rewrite ?flat_xB_eqf, ?know_lookupBX_eqf2, ?erangeB_eqf. reflexivity. Qed.
  Lemma cell_exprB_eqf : forall fk, cell_exprB (mkbc fk) (AX2B.mk_kix fk) = cell_expr fk.
  Proof. intros. bcfe. unfold cell_exprB, cell_expr. rewrite ?flat_xB_eqf, ?know_lookupBX_eqf2. reflexivity. Qed.
  Lemma mk_ctxB_eq : forall cs, mk_ctxB (mkbc (kn cs)) (AX2B.mk_kix (kn cs)) cs = mk_ctx cs.
  Proof.
    intros cs. unfold mk_ctxB, mk_ctx. cbv zeta.
    rewrite ?cell_exprB_eqf, ?xloB_eqf, ?xhiB_eqf, ?shadow_ofB_eqf, ?mkSrlB_eqf. reflexivity.
  Qed.
  Lemma testsB_eq : forall cs c, testsB (mkbc (kn cs)) (AX2B.mk_kix (kn cs)) cs c = tests cs c.
  Proof.
    intros cs c. unfold testsB, tests, partial_okB, partial_ok, chain_okB, chain_ok, shd_splitB, shd_split,
      rw_xB, rw_x, rw_litB, rw_lit, zero_litB, zero_lit, apart_allB, apart_all, kcell_okB, kcell_ok, gsh_okB, gsh_ok, pristine_okB, pristine_ok.
    cbv zeta.
    rewrite ?ealignB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?kwritable_xB_eqf, ?kwritableB_eqf, ?flat_xB_eqf, ?kzero_xB_eqf,
      ?cell_isB_eqf, ?know_lookupBX_eqf2, ?erangeB_eqf, ?mkSrlB_eqf, ?xhiB_eqf, ?xloB_eqf, ?lin_nowrapB_eqf, ?lin_nowrap_lB_eqf, ?img_covB_eqf,
      ?off_bandB_eqf, ?PGV.partial_val_okB_eqf.
    reflexivity.
  Qed.
  Lemma node_F_eq : forall cs, node_F cs = node_F_ref cs.
  Proof. intros cs. unfold node_F, node_F_ref. cbv zeta. rewrite mk_ctxB_eq. destruct (mk_ctx cs) as [c|]; [|reflexivity]. rewrite testsB_eq. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition diag (cs : acs) : nat :=
    let k := kn cs in
    if negb (Z.eqb (pc cs) (fa_entry P)) then 100%nat else
    match ret_lit cs, reg_lit cs 4 with
    | Some _, Some _ =>
        match cell_expr k (ELit 0) (fa_tp P), cell_expr k (ELit 0) (fa_tp P + 0x8), cell_expr k (ELit 0) (fa_tsd P) with
        | Some _, Some _, Some _ =>
            match mk_ctx cs with
            | Some c => match first_false 1 (tests cs c) with
                        | O => match node_F cs with Some _ => 0%nat | None => 200%nat end
                        | S i => S i
                        end
            | None => 102%nat
            end
        | _, _, _ => 101%nat
        end
    | _, _ => 100%nat
    end.

  Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
    match id, args with
    | 102%nat, [] => node_F cs
    | _, _ => None
    end.
End X.
End FN.
