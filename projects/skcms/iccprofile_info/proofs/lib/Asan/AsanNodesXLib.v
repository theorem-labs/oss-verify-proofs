(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From Stdlib Require Import Logic.FunctionalExtensionality.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2B. Import APC.
Unset Lia Cache.
Open Scope Z_scope.

Module XLN.

#[local] Notation SB := AsFuzzContract.AS_SB.
Import AsFuzzContract(aa_entry, aa_gfool, aa_depth, aa_tp, aa_tsdv, aa_dtv, aa_ro, aa_c64, aa_c32, aa_c8, aa_r64, aa_shb,
  FS_SIZE, FS_HINT0, FS_HINT5, FS_SSL, FS_NEEDSGC, FS_FLAGS0, FS_FLAGS0_LEN, FS_FLAGS5, FS_FLAGS5_LEN, FS_FRAMES0, FS_FRAMES5,
  FS_FRAMES_LEN, FS_SHFRAMES_LEN, AS_LOWEND, AS_HIGHBEG, AS_IMGLO, AS_IMGHI).

(* [comment removed for export] *)
Definition abi_of (A : atable) : AsFuzzContract.as_abi := AsFuzzContract.asan_abi.

Definition xregion : Type := (expr * Z * expr)%type.

Fixpoint xl_havoc (k : list kentry) (rs : list xregion) : list kentry :=
  match rs with
  | [] => k
  | (b, off, n) :: rs' => xl_havoc (kn_havoc k b off n) rs'
  end.

(* [comment removed for export] *)
Definition in_hullb (A : atable) (z : Z) : bool := ((img_lo A <=? z) && (z <? img_hi A))%bool.

Section Node.
  Variable B : AsFuzzContract.as_abi.
  Variable segs : list Segment.
  Variable A : atable.
  Variable nx0 : nat.

  #[local] Notation D := (aa_depth B).

  (* [comment removed for export] *)
  Definition word_at (k : list kentry) (b : expr) (off : Z) : option expr :=
    if flat_x k b off (ELit 8) then
      match know_lookup segs k b off 8 false [] [] with
      | LHit e [] _ => Some e
      | _ => None
      end
    else None.

  (* [comment removed for export] *)
  Definition wr_ok (k : list kentry) (b : expr) (off : Z) (n : expr) : bool := flat_x k b off n && kwritable_x k k b off n.
  (* [comment removed for export] *)
  Definition rd8_ok (k : list kentry) (b : expr) (off : Z) : bool := flat_x k b off (ELit 8) && kn_readable segs k k b off 8.
  (* [comment removed for export] *)
  Definition cell_ok (k : list kentry) (a w v : Z) : bool :=
    (Z.leb 0 v && Z.ltb v (2 ^ (8 * w)) && Z.leb 1 w && Z.leb w 8 && flat_x k (ELit 0) a (ELit w) &&
     match know_lookup segs k (ELit 0) a (Z.to_nat w) false [] [] with
     | LHit (ELit v') [] _ => Z.eqb v' v
     | _ => false
     end)%bool.
  (* [comment removed for export] *)
  Definition shb_ok (k : list kentry) (a v : Z) : bool :=
    (negb (in_hullb A a) && Z.leb 0 a && cell_ok k a 1 v)%bool.
  (* [comment removed for export] *)
  Definition xcover (k : list kentry) (rb : expr) (rk : Z) (ne : expr) : bool :=
    existsb (fun K => match K with
                      | KUnk (SA cb ck) len | KZero (SA cb ck) len | KFill (SA cb ck) len _ | KBlob (SA cb ck) len _ | KWr (SA cb ck) len =>
                          xinside k rb rk ne cb ck len
                      | _ => false
                      end) k.

  (* [comment removed for export] *)
  Definition in_maps (cs : acs) (b : expr) (off : Z) (n : expr) : bool :=
    existsb (fun m => (negb (is_fog m) && xinside (kn cs) b off n (am_base m) 0 (am_len m))%bool) (a_maps cs).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition XIMGHI : Z := Z.max AS_IMGHI (img_hi A).
  (* [comment removed for export] *)
  Definition app_end (k : list kentry) (b : expr) (off : Z) (n : expr) (hi nh : Z) : Z :=
    match base_range k b with
    | Some (lo1, hi1) => match end_hi k b off n lo1 hi1 nh with Some e => Z.min e (hi + off + nh) | None => hi + off + nh end
    | None => hi + off + nh
    end.
  Definition app_num (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
    match xlo k b, xhi k b, xhi k n with
    | Some lo, Some hi, Some nh =>
        let eh := app_end k b off n hi nh in
        (Z.leb (img_hi A) (2 ^ 47) && Z.leb 4096 (lo + off) && Z.leb eh (2 ^ 47)
         && (Z.leb eh AS_LOWEND || Z.leb AS_HIGHBEG (lo + off)
             || ranges_apart_x k b off n (ELit 0) AS_LOWEND (ELit (AS_HIGHBEG - AS_LOWEND)))
         && (Z.leb eh AS_IMGLO || Z.leb XIMGHI (lo + off)
             || ranges_apart_x k b off n (ELit 0) AS_IMGLO (ELit (XIMGHI - AS_IMGLO))))%bool
    | _, _, _ => false
    end.
  (* [comment removed for export] *)
  Definition app_ok (cs : acs) (b : expr) (off : Z) (n : expr) : bool := app_num (kn cs) b off n && in_maps cs b off n.

  (* [comment removed for export] *)
  Definition heapcell_ok (cs : acs) (cb : expr) (coff : Z) (fb : expr) (fk : Z) : bool :=
    (app_ok cs cb coff (ELit 8) && ranges_apart_x (kn cs) cb coff (ELit 8) fb fk (ELit FS_SIZE))%bool.

  (* [comment removed for export] *)
  Definition shx (k : list kentry) (e : expr) : expr := eadd (ELit SB) (mkSrl k e 3).

  (* [comment removed for export] *)
  Definition xl_mods (ub : expr) (uk : Z) (fb : expr) (fk : Z) (hb : expr) (hk : Z) : list xregion :=
    [ (ub, uk - D, ELit D);
      (ELit 0, aa_gfool B, ELit 4);
      (fb, fk + FS_HINT0, ELit 8); (fb, fk + FS_HINT5, ELit 8);
      (fb, fk + FS_FLAGS0, ELit FS_FLAGS0_LEN); (fb, fk + FS_FLAGS5, ELit FS_FLAGS5_LEN);
      (fb, fk + FS_FRAMES0, ELit FS_FRAMES_LEN); (fb, fk + FS_FRAMES5, ELit FS_FRAMES_LEN);
      (hb, hk + FS_FRAMES0 / 8, ELit FS_SHFRAMES_LEN); (hb, hk + FS_FRAMES5 / 8, ELit FS_SHFRAMES_LEN) ].

  (* [comment removed for export] *)
  Definition zx1_strip (e : expr) : expr := match e with EExt false 0 1 e' => e' | _ => e end.
  Definition pg_count (k : list kentry) (ne : expr) (nlo nhi : Z) : expr :=
    if (Z.eqb (nlo / 8) (nhi / 8) && Z.leb 0 nlo)%bool then ELit (nlo / 8) else mkSrl k ne 3.
  Definition pg_cell (k : list kentry) (sdb : expr) (sdk : Z) (ne : expr) (nlo nhi : Z) : expr * Z :=
    match pg_count k ne nlo nhi with
    | ELit c => if (Z.leb 0 c && Z.ltb c two64)%bool then (sdb, sdk + c) else (eadd sdb (ELit c), sdk)
    | g => (eadd sdb g, sdk)
    end.
  Definition pg_val_ok (k : list kentry) (ne : expr) (nhi : Z) (e1 : expr) : bool :=
    (match e1 with EAlu ALU_AND ne' (ELit z7) => Z.eqb z7 7 && expr_eqb ne' ne | _ => false end
     || (expr_eqb e1 ne && Z.leb nhi 7)
     || respell_ok (KRange (EAlu ALU_AND ne (ELit 7)) 1 7 :: k) e1 (EAlu ALU_AND ne (ELit 7)))%bool.
  (* [comment removed for export] *)
  Definition pg_val_okL (k : list kentry) (ne : expr) (nhi : Z) (e1 : expr) : bool :=
    if match e1 with EAlu ALU_AND ne' (ELit z7) => Z.eqb z7 7 && expr_eqb ne' ne | _ => false end then true
    else if (expr_eqb e1 ne && Z.leb nhi 7)%bool then true
    else respell_ok (KRange (EAlu ALU_AND ne (ELit 7)) 1 7 :: k) e1 (EAlu ALU_AND ne (ELit 7)).
  Lemma pg_val_okL_eqf : pg_val_okL = pg_val_ok.
  Proof.
    repeat (apply functional_extensionality; intros ?). unfold pg_val_okL, pg_val_ok.
    destruct (match x2 with EAlu ALU_AND ne' (ELit z7) => Z.eqb z7 7 && expr_eqb ne' x0 | _ => false end); [reflexivity|].
    destruct (expr_eqb x2 x0 && Z.leb x1 7)%bool; reflexivity.
  Qed.
  Definition pg_lookup (k : list kentry) (sdb : expr) (sdk : Z) (ne : expr) (nlo nhi : Z) : option expr :=
    let '(pb, pk) := pg_cell k sdb sdk ne nlo nhi in
    if flat_x k pb pk (ELit 1) then
      match know_lookup segs k pb pk 1 false [] [] with
      | LHit e0 [] _ => if pg_val_ok k ne nhi (zx1_strip e0) then Some (zx1_strip e0) else None
      | _ => None
      end
    else None.
  (* [comment removed for export] *)
  Definition kzx0 (k : list kentry) (sdb : expr) (sdk : Z) (g : expr) : bool :=
    match g with ELit 0 => true | _ => kzero_x k k sdb sdk g end.

  Definition xl_dre (k : list kentry) (sdb : expr) (sdk : Z) (ne : expr) (nlo nhi : Z) : list kentry :=
    if Z.eqb nhi 0 then [] else
    (match pg_count k ne nlo nhi with ELit 0 => [] | g => [KZero (SA sdb sdk) g] end)
    ++ (if (Z.eqb nlo nhi && negb (Z.eqb (nlo mod 8) 0) && flat_x k sdb (sdk + nlo / 8) (ELit 1) &&
            match know_lookup segs k sdb (sdk + nlo / 8) 1 false [] [] with
            | LHit (ELit v) [] _ => Z.eqb v (nlo mod 8)
            | _ => false
            end)%bool
        then [KWord (SA sdb (sdk + nlo / 8)) 1 (ELit (nlo mod 8))] else [])
    ++ (if ((Z.ltb 0 nlo || match xlo k (EAlu ALU_AND ne (ELit 7)) with Some lo => Z.ltb 0 lo | None => false end)
            && Z.leb 0 sdk)%bool
        then match pg_lookup k sdb sdk ne nlo nhi with
             | Some e1 => [KWord (SA (fst (pg_cell k sdb sdk ne nlo nhi)) (snd (pg_cell k sdb sdk ne nlo nhi))) 1 e1]
             | None => []
             end
        else []).

  (* [comment removed for export] *)
  Definition xl_post_kn (k : list kentry) (ub : expr) (uk : Z) (fb : expr) (fk : Z) (hb : expr) (hk : Z) (dre : list kentry) : list kentry :=
    KZero (SA fb (fk + FS_FLAGS0)) (ELit FS_FLAGS0_LEN)
    :: KZero (SA fb (fk + FS_FLAGS5)) (ELit FS_FLAGS5_LEN)
    :: KUnk (SA fb (fk + FS_HINT0)) (ELit 8)
    :: KUnk (SA fb (fk + FS_HINT5)) (ELit 8)
    :: dre ++ xl_havoc k (xl_mods ub uk fb fk hb hk).

  (* [comment removed for export] *)
  Definition pgran_ok (k : list kentry) (sdb : expr) (sdk : Z) (ne : expr) (nlo nhi : Z) : bool :=
    (Z.leb 3 (ealign k ne)
     || match xhi k (EAlu ALU_AND ne (ELit 7)) with Some h => Z.eqb h 0 | None => false end
     || (Z.eqb nlo nhi &&
         (Z.eqb (nlo mod 8) 0
          || (flat_x k sdb (sdk + nlo / 8) (ELit 1) &&
              match know_lookup segs k sdb (sdk + nlo / 8) 1 false [] [] with
              | LHit (ELit v) [] _ => Z.eqb v (nlo mod 8)
              | _ => false
              end)))
     || (Z.leb 0 sdk && match pg_lookup k sdb sdk ne nlo nhi with Some _ => true | None => false end))%bool.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition xl_nums (k : list kentry) (u data ne F : expr) (ub : expr) (uk : Z) (hb : expr) (hk : Z) (sub : expr) (suk : Z)
             (sdb : expr) (sdk : Z) (nlo nhi ulo uhi : Z) : bool :=
    (Z.leb 0 nlo
     && Z.ltb 0 D && Z.leb D (2 ^ 32) && Z.eqb (D mod 8) 0 && Z.leb 0 (aa_tp B) && Z.ltb (aa_tp B + 48) (2 ^ 64)
     && Z.leb 0 (aa_tsdv B) && Z.ltb (aa_tsdv B + 8) (2 ^ 64) && Z.leb 0 (aa_gfool B)
     && Z.leb (img_hi A) SB && flat_x k hb hk (ELit 1) && flat_x k sub suk (ELit 1) && (Z.eqb nhi 0 || flat_x k sdb sdk (ELit 1))
     && Z.ltb nhi (2 ^ 26)
     && lin_ge0 k [(u, - D)] [(e_sp0, STK_OFF)] && Z.ltb uhi (2 ^ 47) && Z.leb D ulo
     && Z.leb 4 (ealign k u) && Z.leb 4 (ealign k data) && Z.leb 12 (ealign k F)
     && Z.leb 3 (ealign k ub) && Z.eqb ((uk - D) mod 8) 0)%bool.
  (* [comment removed for export] *)
  Definition xl_data (cs : acs) (ne : expr) (db : expr) (dk : Z) (fb : expr) (fk : Z) (sdb : expr) (sdk : Z) (nlo nhi : Z) : bool :=
    let k := kn cs in
    (Z.eqb nhi 0 || (app_ok cs db dk ne && ranges_apart_x k db dk ne fb fk (ELit FS_SIZE)
                     && xcover k db dk ne && kzx0 k sdb sdk (pg_count k ne nlo nhi) && pgran_ok k sdb sdk ne nlo nhi))%bool.
  (* [comment removed for export] *)
  Definition xl_arena (cs : acs) (fb : expr) (fk : Z) : bool := app_ok cs fb fk (ELit FS_SIZE).
  (* [comment removed for export] *)
  Definition xl_stack (k : list kentry) (ub : expr) (uk : Z) (sub : expr) (suk : Z) : bool :=
    (wr_ok k ub (uk - D) (ELit D) && kzero_x k k sub (suk + (uk - D) / 8) (ELit (D / 8)))%bool.
  (* [comment removed for export] *)
  Definition xl_img (k : list kentry) : bool :=
    (Z.leb (rw_lo A) (aa_gfool B) && Z.leb (aa_gfool B + 4) (rw_lo A + rw_len A) && in_hullb A (aa_gfool B) && in_hullb A (aa_gfool B + 3)
     && forallb (fun w : Z * Z => img_cov k (fst w) (snd w)) (aa_ro B)
     && forallb (fun c : Z * Z => cell_ok k (fst c) 8 (snd c)) (aa_c64 B)
     && forallb (fun c : Z * Z => cell_ok k (fst c) 4 (snd c)) (aa_c32 B)
     && forallb (fun c : Z * Z => cell_ok k (fst c) 1 (snd c)) (aa_c8 B)
     && forallb (fun a : Z => rd8_ok k (ELit 0) a) (aa_r64 B)
     && forallb (fun c : Z * Z => shb_ok k (fst c) (snd c)) (aa_shb B))%bool.
  (* [comment removed for export] *)
  Definition xl_chains (cs : acs) (fb : expr) (fk : Z) : bool :=
    let k := kn cs in
    (match word_at k (ELit 0) (aa_tsdv B) with
     | Some ctx =>
         let '(cb, ck) := split_lit ctx in
         heapcell_ok cs cb (ck + 152) fb fk &&
         match word_at k cb (ck + 152) with
         | Some thr =>
             let '(tb, tk) := split_lit thr in
             heapcell_ok cs tb (tk + 48) fb fk && heapcell_ok cs tb (tk + 56) fb fk && rd8_ok k tb (tk + 48) && rd8_ok k tb (tk + 56)
         | None => false
         end
     | None => false
     end
     && match word_at k (ELit 0) (aa_tp B + 0x8) with
        | Some dtls =>
            let '(eb, ek) := split_lit dtls in
            match xlo k dtls, xhi k dtls with
            | Some tlo, Some thi =>
                Z.ltb 0 tlo && Z.ltb thi (2 ^ 64 - 1) && heapcell_ok cs eb (ek + 24) fb fk &&
                match word_at k eb (ek + 24) with
                | Some v24 => match xlo k v24 with Some vlo => Z.ltb 0 vlo | None => false end
                | None => false
                end
            | _, _ => false
            end
        | None => false
        end)%bool.
  (* [comment removed for export] *)
  Definition xl_fs (k : list kentry) (fb : expr) (fk : Z) (hb : expr) (hk : Z) : bool :=
    (rd8_ok k fb (fk + FS_HINT0) && rd8_ok k fb (fk + FS_HINT5)
     && match know_lookup segs k fb (fk + FS_SSL) 8 false [] [] with LHit (ELit v) [] _ => Z.eqb v 20 | _ => false end
     && flat_x k fb (fk + FS_SSL) (ELit 8)
     && match know_lookup segs k fb (fk + FS_NEEDSGC) 1 false [] [] with LHit (ELit v) [] _ => Z.eqb v 0 | _ => false end
     && flat_x k fb (fk + FS_NEEDSGC) (ELit 1)
     && kzero_x k k fb (fk + FS_FLAGS0) (ELit FS_FLAGS0_LEN) && kzero_x k k fb (fk + FS_FLAGS5) (ELit FS_FLAGS5_LEN)
     && wr_ok k fb (fk + FS_HINT0) (ELit 8) && wr_ok k fb (fk + FS_HINT5) (ELit 8)
     && wr_ok k fb (fk + FS_FLAGS0) (ELit FS_FLAGS0_LEN) && wr_ok k fb (fk + FS_FLAGS5) (ELit FS_FLAGS5_LEN)
     && wr_ok k fb (fk + FS_FRAMES0) (ELit FS_FRAMES_LEN) && wr_ok k fb (fk + FS_FRAMES5) (ELit FS_FRAMES_LEN)
     && wr_ok k hb (hk + FS_FRAMES0 / 8) (ELit FS_SHFRAMES_LEN) && wr_ok k hb (hk + FS_FRAMES5 / 8) (ELit FS_SHFRAMES_LEN))%bool.

  Definition xl_checks (cs : acs) (u data ne F : expr) (ub : expr) (uk : Z) (db : expr) (dk : Z) (fb : expr) (fk : Z)
             (hb : expr) (hk : Z) (sub : expr) (suk : Z) (sdb : expr) (sdk : Z) : bool :=
    let k := kn cs in
    match xlo k ne, xhi k ne, xlo k u, xhi k u with
    | Some nlo, Some nhi, Some ulo, Some uhi =>
        (xl_nums k u data ne F ub uk hb hk sub suk sdb sdk nlo nhi ulo uhi
         && xl_data cs ne db dk fb fk sdb sdk nlo nhi && xl_arena cs fb fk && xl_stack k ub uk sub suk
         && xl_img k && xl_chains cs fb fk && xl_fs k fb fk hb hk)%bool
    | _, _, _, _ => false
    end.

  Definition XLnode (chk : bool) (args : list expr) (cs : acs) : option acs :=
    let k := kn cs in
    if negb (Z.eqb (pc cs) (aa_entry B)) then None else
    match ret_lit cs with
    | None => None
    | Some ret =>
        let u := reg cs 2 in let data := reg cs 10 in let ne := reg cs 11 in
        match reg_lit cs 4 with
        | None => None
        | Some tpv =>
            if negb (Z.eqb tpv (aa_tp B)) then None else
            match word_at k (ELit 0) (aa_tp B) with
            | None => None
            | Some F =>
                let '(ub, uk) := split_lit u in let '(db, dk) := split_lit data in let '(fb, fk) := split_lit F in
                let '(hb, hk) := split_lit (shx k F) in       (* [comment removed for export] *)
                let '(sub, suk) := split_lit (shx k ub) in    (* [comment removed for export] *)
                let '(sdb, sdk) := split_lit (shx k data) in  (* [comment removed for export] *)
                if (negb chk || xl_checks cs u data ne F ub uk db dk fb fk hb hk sub suk sdb sdk)%bool
                then let dre := match xlo k ne, xhi k ne with
                                | Some nlo, Some nhi => xl_dre k sdb sdk ne nlo nhi
                                | _, _ => []
                                end in
                     after_call nx0 cs ret (Some (ELit 0)) (xl_post_kn k ub uk fb fk hb hk dre)
                else None
            end
        end
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition word_atB (bc : bctx) (b : expr) (off : Z) : option expr :=
    if flat_xB bc b off (ELit 8) then
      match know_lookupB segs bc b off 8 false [] [] with
      | LHit e [] _ => Some e
      | _ => None
      end
    else None.
  Definition wr_okB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool := flat_xB bc b off n && kwritable_xB bc k b off n.
  Definition cell_okB (bc : bctx) (a w v : Z) : bool :=
    (Z.leb 0 v && Z.ltb v (2 ^ (8 * w)) && Z.leb 1 w && Z.leb w 8 && flat_xB bc (ELit 0) a (ELit w) &&
     match know_lookupB segs bc (ELit 0) a (Z.to_nat w) false [] [] with
     | LHit (ELit v') [] _ => Z.eqb v' v
     | _ => false
     end)%bool.
  Definition shb_okB (bc : bctx) (a v : Z) : bool :=
    (negb (in_hullb A a) && Z.leb 0 a && cell_okB bc a 1 v)%bool.
  Definition pg_lookupB (bc : bctx) (k : list kentry) (sdb : expr) (sdk : Z) (ne : expr) (nlo nhi : Z) : option expr :=
    let '(pb, pk) := pg_cell k sdb sdk ne nlo nhi in
    if flat_xB bc pb pk (ELit 1) then
      match know_lookupB segs bc pb pk 1 false [] [] with
      | LHit e0 [] _ => if pg_val_okL k ne nhi (zx1_strip e0) then Some (zx1_strip e0) else None
      | _ => None
      end
    else None.
  Definition kzx0B (bc : bctx) (k : list kentry) (sdb : expr) (sdk : Z) (g : expr) : bool :=
    match g with ELit 0 => true | _ => kzero_xB bc k sdb sdk g end.
  Definition xl_stackB (bc : bctx) (k : list kentry) (ub : expr) (uk : Z) (sub : expr) (suk : Z) : bool :=
    (wr_okB bc k ub (uk - D) (ELit D) && kzero_xB bc k sub (suk + (uk - D) / 8) (ELit (D / 8)))%bool.
  Definition xcoverB (bc : bctx) (k : list kentry) (rb : expr) (rk : Z) (ne : expr) : bool :=
    existsb (fun K => match K with
                      | KUnk (SA cb ck) len | KZero (SA cb ck) len | KFill (SA cb ck) len _ | KBlob (SA cb ck) len _ | KWr (SA cb ck) len =>
                          xinsideB bc rb rk ne cb ck len
                      | _ => false
                      end) k.
  Definition in_mapsB (bc : bctx) (cs : acs) (b : expr) (off : Z) (n : expr) : bool :=
    existsb (fun m => (negb (is_fog m) && xinsideB bc b off n (am_base m) 0 (am_len m))%bool) (a_maps cs).
  Definition app_endB (bc : bctx) (b : expr) (off : Z) (n : expr) (hi nh : Z) : Z :=
    match base_rangeB bc b with
    | Some (lo1, hi1) => match end_hiB bc b off n lo1 hi1 nh with Some e => Z.min e (hi + off + nh) | None => hi + off + nh end
    | None => hi + off + nh
    end.
  Definition app_numB (bc : bctx) (b : expr) (off : Z) (n : expr) : bool :=
    match xloB bc b, xhiB bc b, xhiB bc n with
    | Some lo, Some hi, Some nh =>
        let eh := app_endB bc b off n hi nh in
        (Z.leb (img_hi A) (2 ^ 47) && Z.leb 4096 (lo + off) && Z.leb eh (2 ^ 47)
         && (Z.leb eh AS_LOWEND || Z.leb AS_HIGHBEG (lo + off)
             || ranges_apart_xB bc b off n (ELit 0) AS_LOWEND (ELit (AS_HIGHBEG - AS_LOWEND)))
         && (Z.leb eh AS_IMGLO || Z.leb XIMGHI (lo + off)
             || ranges_apart_xB bc b off n (ELit 0) AS_IMGLO (ELit (XIMGHI - AS_IMGLO))))%bool
    | _, _, _ => false
    end.
  Definition app_okB (bc : bctx) (cs : acs) (b : expr) (off : Z) (n : expr) : bool := app_numB bc b off n && in_mapsB bc cs b off n.
  Definition heapcell_okB (bc : bctx) (cs : acs) (cb : expr) (coff : Z) (fb : expr) (fk : Z) : bool :=
    (app_okB bc cs cb coff (ELit 8) && ranges_apart_xB bc cb coff (ELit 8) fb fk (ELit FS_SIZE))%bool.
  Definition xl_dreB (bc : bctx) (k : list kentry) (sdb : expr) (sdk : Z) (ne : expr) (nlo nhi : Z) : list kentry :=
    if Z.eqb nhi 0 then [] else
    (match pg_count k ne nlo nhi with ELit 0 => [] | g => [KZero (SA sdb sdk) g] end)
    ++ (if (Z.eqb nlo nhi && negb (Z.eqb (nlo mod 8) 0) && flat_xB bc sdb (sdk + nlo / 8) (ELit 1) &&
            match know_lookupB segs bc sdb (sdk + nlo / 8) 1 false [] [] with
            | LHit (ELit v) [] _ => Z.eqb v (nlo mod 8)
            | _ => false
            end)%bool
        then [KWord (SA sdb (sdk + nlo / 8)) 1 (ELit (nlo mod 8))] else [])
    ++ (if ((Z.ltb 0 nlo || match xloB bc (EAlu ALU_AND ne (ELit 7)) with Some lo => Z.ltb 0 lo | None => false end)
            && Z.leb 0 sdk)%bool
        then match pg_lookupB bc k sdb sdk ne nlo nhi with
             | Some e1 => [KWord (SA (fst (pg_cell k sdb sdk ne nlo nhi)) (snd (pg_cell k sdb sdk ne nlo nhi))) 1 e1]
             | None => []
             end
        else []).
  Definition pgran_okB (bc : bctx) (k : list kentry) (sdb : expr) (sdk : Z) (ne : expr) (nlo nhi : Z) : bool :=
    (Z.leb 3 (ealignB bc ne)
     || match xhiB bc (EAlu ALU_AND ne (ELit 7)) with Some h => Z.eqb h 0 | None => false end
     || (Z.eqb nlo nhi &&
         (Z.eqb (nlo mod 8) 0
          || (flat_xB bc sdb (sdk + nlo / 8) (ELit 1) &&
              match know_lookupB segs bc sdb (sdk + nlo / 8) 1 false [] [] with
              | LHit (ELit v) [] _ => Z.eqb v (nlo mod 8)
              | _ => false
              end)))
     || (Z.leb 0 sdk && match pg_lookupB bc k sdb sdk ne nlo nhi with Some _ => true | None => false end))%bool.
  Definition xl_numsB (bc : bctx) (k : list kentry) (u data ne F : expr) (ub : expr) (uk : Z) (hb : expr) (hk : Z) (sub : expr) (suk : Z)
             (sdb : expr) (sdk : Z) (nlo nhi ulo uhi : Z) : bool :=
    (Z.leb 0 nlo
     && Z.ltb 0 D && Z.leb D (2 ^ 32) && Z.eqb (D mod 8) 0 && Z.leb 0 (aa_tp B) && Z.ltb (aa_tp B + 48) (2 ^ 64)
     && Z.leb 0 (aa_tsdv B) && Z.ltb (aa_tsdv B + 8) (2 ^ 64) && Z.leb 0 (aa_gfool B)
     && Z.leb (img_hi A) SB && flat_xB bc hb hk (ELit 1) && flat_xB bc sub suk (ELit 1) && (Z.eqb nhi 0 || flat_xB bc sdb sdk (ELit 1))
     && Z.ltb nhi (2 ^ 26)
     && lin_ge0B bc [(u, - D)] [(e_sp0, STK_OFF)] && Z.ltb uhi (2 ^ 47) && Z.leb D ulo
     && Z.leb 4 (ealignB bc u) && Z.leb 4 (ealignB bc data) && Z.leb 12 (ealignB bc F)
     && Z.leb 3 (ealignB bc ub) && Z.eqb ((uk - D) mod 8) 0)%bool.
  Definition xl_dataB (bc : bctx) (cs : acs) (ne : expr) (db : expr) (dk : Z) (fb : expr) (fk : Z) (sdb : expr) (sdk : Z) (nlo nhi : Z) : bool :=
    let k := kn cs in
    (Z.eqb nhi 0 || (app_okB bc cs db dk ne && ranges_apart_xB bc db dk ne fb fk (ELit FS_SIZE)
                     && xcoverB bc k db dk ne && kzx0B bc k sdb sdk (pg_count k ne nlo nhi) && pgran_okB bc k sdb sdk ne nlo nhi))%bool.
  Definition xl_arenaB (bc : bctx) (cs : acs) (fb : expr) (fk : Z) : bool := app_okB bc cs fb fk (ELit FS_SIZE).
  (* [comment removed for export] *)
  Definition rd8_okB (bc : bctx) (k : list kentry) (b : expr) (off : Z) : bool := flat_xB bc b off (ELit 8) && kn_readableB segs bc k b off 8.
  Definition xl_imgB (bc : bctx) (k : list kentry) : bool :=
    (Z.leb (rw_lo A) (aa_gfool B) && Z.leb (aa_gfool B + 4) (rw_lo A + rw_len A) && in_hullb A (aa_gfool B) && in_hullb A (aa_gfool B + 3)
     && forallb (fun w : Z * Z => img_covB bc (fst w) (snd w)) (aa_ro B)
     && forallb (fun c : Z * Z => cell_okB bc (fst c) 8 (snd c)) (aa_c64 B)
     && forallb (fun c : Z * Z => cell_okB bc (fst c) 4 (snd c)) (aa_c32 B)
     && forallb (fun c : Z * Z => cell_okB bc (fst c) 1 (snd c)) (aa_c8 B)
     && forallb (fun a : Z => rd8_okB bc k (ELit 0) a) (aa_r64 B)
     && forallb (fun c : Z * Z => shb_okB bc (fst c) (snd c)) (aa_shb B))%bool.
  Definition xl_fsB (bc : bctx) (k : list kentry) (fb : expr) (fk : Z) (hb : expr) (hk : Z) : bool :=
    (rd8_okB bc k fb (fk + FS_HINT0) && rd8_okB bc k fb (fk + FS_HINT5)
     && match know_lookupB segs bc fb (fk + FS_SSL) 8 false [] [] with LHit (ELit v) [] _ => Z.eqb v 20 | _ => false end
     && flat_xB bc fb (fk + FS_SSL) (ELit 8)
     && match know_lookupB segs bc fb (fk + FS_NEEDSGC) 1 false [] [] with LHit (ELit v) [] _ => Z.eqb v 0 | _ => false end
     && flat_xB bc fb (fk + FS_NEEDSGC) (ELit 1)
     && kzero_xB bc k fb (fk + FS_FLAGS0) (ELit FS_FLAGS0_LEN) && kzero_xB bc k fb (fk + FS_FLAGS5) (ELit FS_FLAGS5_LEN)
     && wr_okB bc k fb (fk + FS_HINT0) (ELit 8) && wr_okB bc k fb (fk + FS_HINT5) (ELit 8)
     && wr_okB bc k fb (fk + FS_FLAGS0) (ELit FS_FLAGS0_LEN) && wr_okB bc k fb (fk + FS_FLAGS5) (ELit FS_FLAGS5_LEN)
     && wr_okB bc k fb (fk + FS_FRAMES0) (ELit FS_FRAMES_LEN) && wr_okB bc k fb (fk + FS_FRAMES5) (ELit FS_FRAMES_LEN)
     && wr_okB bc k hb (hk + FS_FRAMES0 / 8) (ELit FS_SHFRAMES_LEN) && wr_okB bc k hb (hk + FS_FRAMES5 / 8) (ELit FS_SHFRAMES_LEN))%bool.
  Definition xl_chainsB (bc : bctx) (cs : acs) (fb : expr) (fk : Z) : bool :=
    let k := kn cs in
    (match word_atB bc (ELit 0) (aa_tsdv B) with
     | Some ctx =>
         let '(cb, ck) := split_lit ctx in
         heapcell_okB bc cs cb (ck + 152) fb fk &&
         match word_atB bc cb (ck + 152) with
         | Some thr =>
             let '(tb, tk) := split_lit thr in
             heapcell_okB bc cs tb (tk + 48) fb fk && heapcell_okB bc cs tb (tk + 56) fb fk && rd8_okB bc k tb (tk + 48) && rd8_okB bc k tb (tk + 56)
         | None => false
         end
     | None => false
     end
     && match word_atB bc (ELit 0) (aa_tp B + 0x8) with
        | Some dtls =>
            let '(eb, ek) := split_lit dtls in
            match xloB bc dtls, xhiB bc dtls with
            | Some tlo, Some thi =>
                Z.ltb 0 tlo && Z.ltb thi (2 ^ 64 - 1) && heapcell_okB bc cs eb (ek + 24) fb fk &&
                match word_atB bc eb (ek + 24) with
                | Some v24 => match xloB bc v24 with Some vlo => Z.ltb 0 vlo | None => false end
                | None => false
                end
            | _, _ => false
            end
        | None => false
        end)%bool.
  Definition xl_checksB (bc : bctx) (cs : acs) (u data ne F : expr) (ub : expr) (uk : Z) (db : expr) (dk : Z) (fb : expr) (fk : Z)
             (hb : expr) (hk : Z) (sub : expr) (suk : Z) (sdb : expr) (sdk : Z) : bool :=
    let k := kn cs in
    match xloB bc ne, xhiB bc ne, xloB bc u, xhiB bc u with
    | Some nlo, Some nhi, Some ulo, Some uhi =>
        (xl_numsB bc k u data ne F ub uk hb hk sub suk sdb sdk nlo nhi ulo uhi
         && xl_dataB bc cs ne db dk fb fk sdb sdk nlo nhi && xl_arenaB bc cs fb fk && xl_stackB bc k ub uk sub suk
         && xl_imgB bc k && xl_chainsB bc cs fb fk && xl_fsB bc k fb fk hb hk)%bool
    | _, _, _, _ => false
    end.
  Definition XLnodeB (chk : bool) (args : list expr) (cs : acs) : option acs :=
    let k := kn cs in
    let bc := mkbc k in
    if negb (Z.eqb (pc cs) (aa_entry B)) then None else
    match ret_lit cs with
    | None => None
    | Some ret =>
        let u := reg cs 2 in let data := reg cs 10 in let ne := reg cs 11 in
        match reg_lit cs 4 with
        | None => None
        | Some tpv =>
            if negb (Z.eqb tpv (aa_tp B)) then None else
            match word_atB bc (ELit 0) (aa_tp B) with
            | None => None
            | Some F =>
                let '(ub, uk) := split_lit u in let '(db, dk) := split_lit data in let '(fb, fk) := split_lit F in
                let '(hb, hk) := split_lit (shx k F) in
                let '(sub, suk) := split_lit (shx k ub) in
                let '(sdb, sdk) := split_lit (shx k data) in
                if (negb chk || xl_checksB bc cs u data ne F ub uk db dk fb fk hb hk sub suk sdb sdk)%bool
                then let dre := match xloB bc ne, xhiB bc ne with
                                | Some nlo, Some nhi => xl_dreB bc k sdb sdk ne nlo nhi
                                | _, _ => []
                                end in
                     after_call nx0 cs ret (Some (ELit 0)) (xl_post_kn k ub uk fb fk hb hk dre)
                else None
            end
        end
    end.
  Lemma XLnodeB_eq : forall chk args cs, XLnodeB chk args cs = XLnode chk args cs.
  Proof.
    intros chk args cs. cbv zeta. unfold XLnodeB, XLnode, xl_checksB, xl_checks, xl_numsB, xl_nums, xl_dataB, xl_data, xl_arenaB, xl_arena,
      xl_chainsB, xl_chains, heapcell_okB, heapcell_ok, app_okB, app_ok, app_numB, app_num, app_endB, app_end, in_mapsB, in_maps, xcoverB, xcover,
      pgran_okB, pgran_ok, xl_dreB, xl_dre, xl_fsB, xl_fs, rd8_okB, rd8_ok,
      word_atB, word_at, wr_okB, wr_ok, cell_okB, cell_ok, shb_okB, shb_ok, pg_lookupB, pg_lookup, kzx0B, kzx0, xl_stackB, xl_stack, xl_imgB, xl_img,
      rd8_okB, rd8_ok, cell_okB, cell_ok.
    unfold xl_stackB, xl_stack, xl_imgB, xl_img, wr_okB, wr_ok, shb_okB, shb_ok, cell_okB, cell_ok, rd8_okB, rd8_ok, pg_lookupB, pg_lookup,
      kzx0B, kzx0, word_atB, word_at.
    rewrite !kn_readableB_eqf, !xloB_eqf, !xhiB_eqf, !ranges_apart_xB_eqf, !xinsideB_eqf, !lin_ge0B_eqf, !ealignB_eqf, !base_rangeB_eqf, !end_hiB_eqf,
      ?flat_xB_eqf, ?know_lookupB_eqf, ?kwritable_xB_eqf, ?kzero_xB_eqf, ?img_covB_eqf, ?pg_val_okL_eqf. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
    if Nat.eqb id 110 then XLnodeB true args cs else None.
End Node.

(* [comment removed for export] *)
Definition xn_dev (segs : list Segment) (A : atable) (nx0 : nat) (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 110 then XLnode (abi_of A) segs A nx0 false args cs else None.
End XLN.
