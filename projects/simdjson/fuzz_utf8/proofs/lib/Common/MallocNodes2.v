(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanNodesArg MallocDefs ImgParams MallocNodes.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.

Module MN2.
Section WithSegs.
  Context {fx : FPState}.
  Variable segs : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable MTB : mtab.
  Variable G : gparams.        (* [comment removed for export] *)
  #[local] Notation kz := (MN.kz segs).
  #[local] Notation kzB := (kreadZB segs).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition decode_W (We : expr) : option (expr * Z) :=
    match We with
    | ELit w => let w' := w mod two64 in Some (ELit (w' / 4096), w' mod 4096)
    | EAlu ALU_ADD (EMd M_MUL (ELit m) Se) (ELit c) =>
        if (Z.eqb m 4096 && Z.leb 0 c && Z.ltb c 4096)%bool then Some (Se, c) else None
    | EMd M_MUL (ELit m) Se => if Z.eqb m 4096 then Some (Se, 0) else None
    | _ => None
    end.

  Definition times16 (e : expr) : expr := mkMd M_MUL (ELit 16) e.

  (* [comment removed for export] *)
  Definition SLOT_ID : nat := 50.
  Definition slot_args (start stride n off W : expr) (idx : Z) (p : expr) : list expr :=
    [start; stride; n; off; W; ELit idx; p].
  Definition slot_atom (args : list expr) : gatom := GA SLOT_ID args.
  (* [comment removed for export] *)
  Definition slot_fp (args : list expr) : list (expr * expr) :=
    match args with
    | [start; sd; nn; o; W; idx; p] =>
        [(mkAlu ALU_ADD start (ELit (-4)), mkAlu ALU_ADD (mkAlu ALU_SUB p start) (ELit 4));
         (mkAlu ALU_ADD p nn, mkAlu ALU_ADD (mkAlu ALU_SUB (mkAlu ALU_ADD start sd) (mkAlu ALU_ADD p nn)) (ELit (-3)))]
    | _ => []
    end.
  (* [comment removed for export] *)
  Definition Gm : gparams := GPAR (fun id args => if Nat.eqb id SLOT_ID then slot_fp args else []) (fun _ => false).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition extG_m (id : nat) : bool := ((id =? 20) || (id =? 21))%nat.

  (* [comment removed for export] *)
  Definition slots_of (cs : acs) : list (list expr) :=
    List.map g_args (List.filter (fun g => Nat.eqb (g_id g) SLOT_ID) (a_props cs)).

  (* [comment removed for export] *)
  Definition wapart (k : list kentry) (W : list (saddr * expr)) (r : expr * expr) : bool :=
    forallb (fun w => ranges_apart_x k (a_base (fst w)) (a_off (fst w)) (snd w) (fst r) 0 (snd r)) W.
  Definition keep1 (k : list kentry) (W : list (saddr * expr)) (nx : nat) (g : gatom) : bool :=
    (gvars_lt nx g && forallb (wapart k W) (g_fp G (g_id g) (g_args g)))%bool.
  Definition keep_props (k : list kentry) (W : list (saddr * expr)) (nx : nat) (l : list gatom) : list gatom :=
    List.filter (keep1 k W nx) l.
  Lemma keep_props_vars : forall k W nx l, forallb (gvars_lt nx) (keep_props k W nx l) = true.
  Proof.
    intros k W nx l. apply forallb_forall. intros g Hg. unfold keep_props in Hg. apply filter_In in Hg as [_ H1].
    unfold keep1 in H1. apply andb_prop in H1 as [H _]. exact H.
  Qed.

  (* [comment removed for export] *)
  Definition stride_lit (Se : expr) (li sc : Z) : option Z :=            (* [comment removed for export] *)
    match Se with ELit m => Some (slot_stride (m mod two64) li sc) | _ => None end.
  Definition stride_e (Se : expr) (stl : option Z) : expr :=              (* [comment removed for export] *)
    match stl with Some st => ELit st | None => mkAlu ALU_ADD (mkMd M_MUL (ELit 4096) Se) (ELit (-16)) end.
  Definition si_of (stl : option Z) (idx : Z) : Z := match stl with Some st => st * idx | None => 0 end.   (* [comment removed for export] *)
  Definition sbound (stl : option Z) (S : Z) : Z := match stl with Some st => st | None => 4096 * S - 16 end.
  Definition single_ok (stl : option Z) (li idx : Z) : bool :=            (* [comment removed for export] *)
    match stl with Some _ => true | None => (Z.eqb li 0 && Z.eqb idx 0)%bool end.
  Definition sc_ok (Se : expr) (li sc Slo : Z) : bool :=                  (* [comment removed for export] *)
    match Se with ELit m => (negb ((Z.eqb (m mod two64) 0) || negb (Z.eqb li 0)) || Z.ltb sc 48)%bool | _ => Z.leb 1 Slo end.

  (* [comment removed for export] *)
  Inductive nres : Type := RStage (n : nat) (info : list (option Z)) | RConj (bs : list bool) | RFresh | ROk (cs' : acs).
  Definition oz {T} (o : option T) : option Z := match o with Some _ => Some 1 | None => None end.
  Definition all_true (bs : list bool) : bool := List.fold_right andb true bs.
  Definition res_opt (r : nres) : option acs := match r with ROk cs' => Some cs' | _ => None end.

  (* [comment removed for export] *)
  Definition node_enframe2r (cs : acs) : nres :=
    let k := kn cs in
    if negb (Z.eqb (pc cs) (mt_enframe MTB)) then RStage 0 [Some (pc cs); Some (mt_enframe MTB)] else
    match ret_lit cs, reg_lit cs 11, reg_lit cs 13 with
    | Some ret, Some idx, Some ctr =>
      let ne := reg cs 12 in
      let '(Gb, gk) := split_lit (reg cs 10) in
      match kread8e segs k Gb (gk + 16), kread8e segs k Gb (gk + 32) with
      | Some Me, Some We =>
        match decode_W We with
        | Some (Se, c) =>
          let li := c mod 32 in let sc := (c / 64) mod 64 in
          let stl := stride_lit Se li sc in
          let ste := stride_e Se stl in
          let si := si_of stl idx in
          let '(Mb, Mk) := split_lit Me in
          let sk := Mk + 16 + si in                                                             (* [comment removed for export] *)
          let e := mkAlu ALU_ADD (eaddz Mb (sk - 4)) ste in                                     (* [comment removed for export] *)
          let '(eb, ek) := split_lit e in
          let hlen := mkAlu ALU_ADD ste (ELit (-1)) in                                          (* [comment removed for export] *)
          match kz k Mb (sk - 4) 1, kz k eb ek 1 with
          | Some z4, Some zend =>
              (* [comment removed for export] *)
              let hdr := true in
              match xlo k ne, xhi k ne, xlo k Se, xhi k Se, xlo k Mb, xhi k Mb, xlo k Gb, xhi k Gb, xlo k eb, xhi k eb with
              | Some nlo, Some nhi, Some Slo, Some Shi, Some mlo, Some mhi, Some glo, Some ghi, Some elo, Some ehi =>
                let shi := sbound stl Shi in                                                          (* [comment removed for export] *)
                let slo := sbound stl Slo in
                let v := nxt cs in
                let off := EVar v in
                let p := mkAlu ALU_ADD (eaddz Mb sk) (times16 off) in
                let pn := mkAlu ALU_ADD p ne in                                                        (* [comment removed for export] *)
                let r4 := mkAlu ALU_SUB ste (mkAlu ALU_ADD ne (times16 off)) in                       (* [comment removed for export] *)
                let len1 := mkAlu ALU_ADD (times16 off) (ELit 3) in                                   (* [comment removed for export] *)
                let len2 := mkAlu ALU_ADD r4 (ELit (-4)) in                                            (* [comment removed for export] *)
                let kf := [KRange (EVar v) 0 (Z.min 255 ((shi - 4 - nlo) / 16)); KRange r4 4 (shi - nlo)] in
                let sargs := slot_args (eaddz Mb sk) ste ne off We idx p in
                let bs := [ single_ok stl li idx                                        (* [comment removed for export] *)
                          ; sc_ok Se li sc Slo                                          (* [comment removed for export] *)
                          ; Z.eqb z4 0                                                  (* [comment removed for export] *)
                          ; Z.eqb zend 0                                                (* [comment removed for export] *)
                          ; Z.leb 0 idx; Z.ltb idx 32; Z.leb idx li                     (* [comment removed for export] *)
                          ; Z.leb (si + 4096) (16 * 65536)                              (* [comment removed for export] *)
                          ; Z.leb 16 slo; Z.ltb shi (2 ^ 31); Z.leb Shi (2 ^ 40)        (* [comment removed for export] *)
                          ; Z.leb 4 (ealign k Me)                                       (* [comment removed for export] *)
                          ; fresh_ok nx0 cs                                             (* [comment removed for export] *)
                          ; Z.leb 0 nlo; lin_ge0 k [(ste, 0)] [(ne, 4)]                 (* [comment removed for export] *)
                          ; Z.leb 0 (mlo + Mk); Z.ltb (mhi + sk + shi + 1) two64        (* [comment removed for export] *)
                          ; Z.leb 0 (glo + gk); Z.ltb (ghi + gk + 40) two64             (* [comment removed for export] *)
                          ; Z.leb 0 (elo + ek); Z.ltb (ehi + ek + 1) two64              (* [comment removed for export] *)
                          ; kwritable_x k k Mb (sk - 3) hlen                            (* [comment removed for export] *)
                          ; (Z.leb (img_hi A) (mlo + sk - 4) || ranges_apart_x k (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)) Mb (sk - 4) (mkAlu ALU_ADD hlen (ELit 1)))%bool                             (* [comment removed for export] *)
                          ; ranges_apart_x k Gb (gk + 16) (ELit 24) Mb (sk - 3) hlen    (* [comment removed for export] *)
                          ; AN.kimg_cover k (mt_sct MTB) (mt_sct MTB + 96)              (* [comment removed for export] *)
                          ; expr_vars_lt v Me; expr_vars_lt v ne; expr_vars_lt v We     (* [comment removed for export] *)
                          ; expr_vars_lt v (reg cs 10); expr_vars_lt v Se               (* [comment removed for export] *)
                          ; forallb (expr_vars_lt (S v)) sargs                          (* [comment removed for export] *)
                          ; hdr ] in                                                    (* [comment removed for export] *)
                if all_true bs then
                  let cs1 := bump (add_kn cs kf) 1 in
                  let k1 := kn_havoc (kn cs1) Mb (sk - 3) len1 in
                  let k2 := kn_havoc k1 pn 0 len2 in
                  (* [comment removed for export] *)
                  let k3 := KUnk (SA Mb (sk - 3)) len1 :: KUnk (SA pn 0) len2 :: KUnk (SA Mb (sk - 3)) hlen :: k2 in
                  match after_call nx0 cs1 ret (Some p) k3 with
                  | Some cs' => ROk (set_props cs' (slot_atom sargs
                                                   :: keep_props (kn cs1) [(SA Mb (sk - 3), len1); (SA pn 0, len2)] v (a_props cs)))
                  | None => RFresh
                  end
                else RConj bs
              | a1, a2, a3, a4, a5, a6, a7, a8, a9, a10 =>
                  RStage 5 [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; Some sk; Some ek]  (* [comment removed for export] *)
              end
          | a1, a3 => RStage 3 [a1; kz k Mb (sk - 3) 1; a3; Some sk; Some ek]           (* [comment removed for export] *)
          end
        | None => RStage 2 [Some 50505]                                      (* [comment removed for export] *)
        end
      | a1, a2 => RStage 2 [oz a1; oz a2; Some gk]                           (* [comment removed for export] *)
      end
    | a1, a2, a3 => RStage 1 [a1; a2; a3]                                    (* [comment removed for export] *)
    end.
  (* [comment removed for export] *)
  Definition node_enframe2rM (cs : acs) : nres :=
    let k := kn cs in let bc := AX2B.mkbc k in   (* [comment removed for export] *)
    if negb (Z.eqb (pc cs) (mt_enframe MTB)) then RStage 0 [Some (pc cs); Some (mt_enframe MTB)] else
    match ret_lit cs, reg_lit cs 11, reg_lit cs 13 with
    | Some ret, Some idx, Some ctr =>
      let ne := reg cs 12 in
      let '(Gb, gk) := split_lit (reg cs 10) in
      match kread8eB segs bc Gb (gk + 16), kread8eB segs bc Gb (gk + 32) with
      | Some Me, Some We =>
        match decode_W We with
        | Some (Se, c) =>
          let li := c mod 32 in let sc := (c / 64) mod 64 in
          let stl := stride_lit Se li sc in
          let ste := stride_e Se stl in
          let si := si_of stl idx in
          let '(Mb, Mk) := split_lit Me in
          let sk := Mk + 16 + si in                                                             (* [comment removed for export] *)
          let e := mkAlu ALU_ADD (eaddz Mb (sk - 4)) ste in                                     (* [comment removed for export] *)
          let '(eb, ek) := split_lit e in
          let hlen := mkAlu ALU_ADD ste (ELit (-1)) in                                          (* [comment removed for export] *)
          match kzB bc Mb (sk - 4) 1, kzB bc eb ek 1 with
          | Some z4, Some zend =>
              (* [comment removed for export] *)
              let hdr := true in
              match AX2B.xloB bc ne, AX2B.xhiB bc ne, AX2B.xloB bc Se, AX2B.xhiB bc Se, AX2B.xloB bc Mb, AX2B.xhiB bc Mb, AX2B.xloB bc Gb, AX2B.xhiB bc Gb, AX2B.xloB bc eb, AX2B.xhiB bc eb with
              | Some nlo, Some nhi, Some Slo, Some Shi, Some mlo, Some mhi, Some glo, Some ghi, Some elo, Some ehi =>
                let shi := sbound stl Shi in                                                          (* [comment removed for export] *)
                let slo := sbound stl Slo in
                let v := nxt cs in
                let off := EVar v in
                let p := mkAlu ALU_ADD (eaddz Mb sk) (times16 off) in
                let pn := mkAlu ALU_ADD p ne in                                                        (* [comment removed for export] *)
                let r4 := mkAlu ALU_SUB ste (mkAlu ALU_ADD ne (times16 off)) in                       (* [comment removed for export] *)
                let len1 := mkAlu ALU_ADD (times16 off) (ELit 3) in                                   (* [comment removed for export] *)
                let len2 := mkAlu ALU_ADD r4 (ELit (-4)) in                                            (* [comment removed for export] *)
                let kf := [KRange (EVar v) 0 (Z.min 255 ((shi - 4 - nlo) / 16)); KRange r4 4 (shi - nlo)] in
                let sargs := slot_args (eaddz Mb sk) ste ne off We idx p in
                let bs := [ single_ok stl li idx                                        (* [comment removed for export] *)
                          ; sc_ok Se li sc Slo                                          (* [comment removed for export] *)
                          ; Z.eqb z4 0                                                  (* [comment removed for export] *)
                          ; Z.eqb zend 0                                                (* [comment removed for export] *)
                          ; Z.leb 0 idx; Z.ltb idx 32; Z.leb idx li                     (* [comment removed for export] *)
                          ; Z.leb (si + 4096) (16 * 65536)                              (* [comment removed for export] *)
                          ; Z.leb 16 slo; Z.ltb shi (2 ^ 31); Z.leb Shi (2 ^ 40)        (* [comment removed for export] *)
                          ; Z.leb 4 (AX2B.ealignB bc Me)                                       (* [comment removed for export] *)
                          ; fresh_ok nx0 cs                                             (* [comment removed for export] *)
                          ; Z.leb 0 nlo; AX2B.lin_ge0B bc [(ste, 0)] [(ne, 4)]                 (* [comment removed for export] *)
                          ; Z.leb 0 (mlo + Mk); Z.ltb (mhi + sk + shi + 1) two64        (* [comment removed for export] *)
                          ; Z.leb 0 (glo + gk); Z.ltb (ghi + gk + 40) two64             (* [comment removed for export] *)
                          ; Z.leb 0 (elo + ek); Z.ltb (ehi + ek + 1) two64              (* [comment removed for export] *)
                          ; kwritable_xB bc k Mb (sk - 3) hlen                            (* [comment removed for export] *)
                          ; (Z.leb (img_hi A) (mlo + sk - 4) || AX2B.ranges_apart_xB bc (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)) Mb (sk - 4) (mkAlu ALU_ADD hlen (ELit 1)))%bool                             (* [comment removed for export] *)
                          ; AX2B.ranges_apart_xB bc Gb (gk + 16) (ELit 24) Mb (sk - 3) hlen    (* [comment removed for export] *)
                          ; AN.kimg_cover k (mt_sct MTB) (mt_sct MTB + 96)              (* [comment removed for export] *)
                          ; expr_vars_lt v Me; expr_vars_lt v ne; expr_vars_lt v We     (* [comment removed for export] *)
                          ; expr_vars_lt v (reg cs 10); expr_vars_lt v Se               (* [comment removed for export] *)
                          ; forallb (expr_vars_lt (S v)) sargs                          (* [comment removed for export] *)
                          ; hdr ] in                                                    (* [comment removed for export] *)
                if all_true bs then
                  let cs1 := bump (add_kn cs kf) 1 in
                  let k1 := kn_havocM (kn cs1) Mb (sk - 3) len1 in
                  let k2 := kn_havocM k1 pn 0 len2 in
                  (* [comment removed for export] *)
                  let k3 := KUnk (SA Mb (sk - 3)) len1 :: KUnk (SA pn 0) len2 :: KUnk (SA Mb (sk - 3)) hlen :: k2 in
                  match after_call nx0 cs1 ret (Some p) k3 with
                  | Some cs' => ROk (set_props cs' (slot_atom sargs
                                                   :: keep_props (kn cs1) [(SA Mb (sk - 3), len1); (SA pn 0, len2)] v (a_props cs)))
                  | None => RFresh
                  end
                else RConj bs
              | a1, a2, a3, a4, a5, a6, a7, a8, a9, a10 =>
                  RStage 5 [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; Some sk; Some ek]  (* [comment removed for export] *)
              end
          | a1, a3 => RStage 3 [a1; kzB bc Mb (sk - 3) 1; a3; Some sk; Some ek]           (* [comment removed for export] *)
          end
        | None => RStage 2 [Some 50505]                                      (* [comment removed for export] *)
        end
      | a1, a2 => RStage 2 [oz a1; oz a2; Some gk]                           (* [comment removed for export] *)
      end
    | a1, a2, a3 => RStage 1 [a1; a2; a3]                                    (* [comment removed for export] *)
    end.
  Lemma node_enframe2rM_eq : forall cs, node_enframe2rM cs = node_enframe2r cs.
  Proof.
    intros. unfold node_enframe2rM, node_enframe2r. cbv zeta.
    rewrite ?kread8eB_eqf. rewrite ?kreadZB_eqf. rewrite ?kread_bytesB_eqf. rewrite ?AX2B.xloB_eqf. rewrite ?AX2B.xhiB_eqf. rewrite ?AX2B.erangeB_eqf. rewrite ?AX2B.ealignB_eqf. rewrite ?AX2B.lin_ge0B_eqf. rewrite ?AX2B.ranges_apart_xB_eqf. rewrite ?AX2B.xinsideB_eqf. rewrite ?AX2B.foldKB_eqf. rewrite ?len_eqbB_eqf. rewrite ?page_alignedB_eqf. rewrite ?kwritable_xB_eqf. rewrite ?kwritableB_eqf. rewrite ?flat_xB_eqf. rewrite ?kzero_xB_eqf. rewrite ?off_image_xB_eqf. rewrite ?kn_havocB_eqf. rewrite ?kn_havocM_eq. rewrite ?kn_unfillB_eqf. rewrite ?kn_unfillM_eq. rewrite ?AN.eeqB_eqf. rewrite ?AN.argc_okB_eqf. rewrite ?AN.pieces_walkB_eqf. rewrite ?AN.extra_piecesB_eqf. rewrite ?AN.off_lazyB_eqf.
    reflexivity.
  Qed.
  (* [comment removed for export] *)
  Definition node_enframe2 (cs : acs) (args : list expr) : option acs := res_opt (node_enframe2r cs).
  Definition node_enframe2M (cs : acs) (args : list expr) : option acs := res_opt (node_enframe2rM cs).   (* [comment removed for export] *)
  Lemma node_enframe2M_eq : forall cs args, node_enframe2M cs args = node_enframe2 cs args.
  Proof. intros. unfold node_enframe2M, node_enframe2. rewrite node_enframe2rM_eq. reflexivity. Qed.

  (* [comment removed for export] *)
  Fixpoint find_slot (k : list kentry) (pa : expr) (ss : list (list expr)) : option (list expr) :=
    match ss with
    | [] => None
    | ([_; _; _; _; _; _; p] as s) :: rest =>
        if (expr_eqb p pa || len_eqb k p pa)%bool then Some s else find_slot k pa rest
    | _ :: rest => find_slot k pa rest
    end.

  (* [comment removed for export] *)
  Definition node_freehead2r (cs : acs) : nres :=
    let k := kn cs in let pa := reg cs 10 in
    if negb (Z.eqb (pc cs) (mt_free MTB)) then RStage 0 [Some (pc cs); Some (mt_free MTB)] else
    let '(spb, spk) := split_lit (reg cs 2) in                                    (* [comment removed for export] *)
    match find_slot k pa (slots_of cs), xlo k spb, xhi k spb with
    | Some [start; ste; ne; off; Ws; ELit idx; p], Some splo, Some sphi =>
      let sp := splo + spk in                                                       (* [comment removed for export] *)
      match decode_W Ws, xlo k ste, xhi k ste with
      | Some (Se, c), Some slo, Some shi =>
        let li := c mod 32 in let sc := (c / 64) mod 64 in
        match (match ste with ELit st => Some ((st mod two64) * idx) | _ => if Z.eqb idx 0 then Some 0 else None end) with
        | Some si =>                                                                (* [comment removed for export] *)
          let Me := mkAlu ALU_ADD start (ELit (- (16 + si))) in                   (* [comment removed for export] *)
          let '(mb, mk) := split_lit Me in
          match kread8e segs k mb mk with                                           (* [comment removed for export] *)
          | Some ge =>
            let '(gb, gk) := split_lit ge in
            let ak := gk - gk mod 4096 in                                           (* [comment removed for export] *)
            let e := mkAlu ALU_ADD start (mkAlu ALU_ADD ste (ELit (-4))) in          (* [comment removed for export] *)
            let '(eb, ek) := split_lit e in
            let '(hb, hk) := split_lit start in
            match kread8e segs k gb (gk + 16), kread8e segs k gb (gk + 32), kz k gb (gk + 24) 4, kz k gb (gk + 28) 4,
                  kread8e segs k gb ak, kread8e segs k (ELit 0) (mt_secret MTB), kz k eb ek 1 with   (* [comment removed for export] *)
            | Some Me', Some We, Some avail, Some freed, Some sec, Some sec', Some zend =>
              match xlo k off, xhi k off, xlo k gb, xhi k gb, xlo k hb, xhi k hb, xlo k Se, xhi k Se,
                    xlo k mb, xhi k mb, xlo k eb, xhi k eb with
              | Some olo, Some ohi, Some glo, Some ghi, Some hl, Some hh, Some Slo, Some Shi, Some mlo, Some mhi, Some elo, Some ehi =>
                let qlo := si / 16 + olo in let qhi := si / 16 + ohi in                  (* [comment removed for export] *)
                let reserved := mkAlu ALU_SUB (mkAlu ALU_ADD ste (ELit (-4))) (mkAlu ALU_ADD ne (times16 off)) in
                let e12 := mkAlu ALU_ADD start (mkAlu ALU_ADD ste (ELit (-16))) in
                let bs := [ len_eqb k Me' Me                                        (* [comment removed for export] *)
                          ; expr_eqb We Ws                                          (* [comment removed for export] *)
                          ; Z.eqb zend 0                                            (* [comment removed for export] *)
                          ; Z.leb 1 slo; Z.leb Shi (2 ^ 40)                         (* [comment removed for export] *)
                          ; Z.leb 0 idx; Z.ltb idx 32; Z.eqb (si mod 16) 0; Z.leb 0 si   (* [comment removed for export] *)
                          ; ((Z.ltb sc 48 && Z.leb (size_class sc * idx) qlo && Z.ltb qhi (size_class sc * (idx + 1)))
                             || (Z.eqb sc 63 && Z.leb 1 Slo && Z.eqb li 0))%bool    (* [comment removed for export] *)
                          ; (Z.eqb Shi 0 || Z.leb qhi (Slo * 256 - 1))%bool         (* [comment removed for export] *)
                          ; Z.leb 0 olo                                             (* [comment removed for export] *)
                          ; negb (Z.testbit avail idx); negb (Z.testbit freed idx)  (* [comment removed for export] *)
                          ; Z.leb 0 avail; Z.ltb avail (2 ^ 32); Z.leb 0 freed; Z.ltb freed (2 ^ 32)   (* [comment removed for export] *)
                          ; page_aligned k gb                                       (* [comment removed for export] *)
                          ; expr_eqb sec sec'                                       (* [comment removed for export] *)
                          ; Z.leb 0 (glo + ak); Z.ltb (ghi + gk + 40) two64; Z.leb (16 + si) (hl + hk)   (* [comment removed for export] *)
                          ; Z.leb 0 (mlo + mk); Z.ltb (mhi + mk + 8) two64          (* [comment removed for export] *)
                          ; Z.leb 0 (elo + ek); Z.ltb (ehi + ek + 1) two64          (* [comment removed for export] *)
                          ; (Z.leb (hh + hk + shi) (sp - 48) || Z.leb (ehi + ek + 4) (sp - 48) || (inside_maps k (a_maps cs) hb hk ste && expr_eqb spb e_sp0 && Z.leb (- STK_BELOW) (spk - 48)))%bool   (* [comment removed for export] *)
                          ; (Z.leb (ghi + gk + 40) (sp - 48) || (inside_maps k (a_maps cs) gb gk (ELit 40) && expr_eqb spb e_sp0 && Z.leb (- STK_BELOW) (spk - 48)))%bool   (* [comment removed for export] *)
                          ; Z.leb 0 (mt_secret MTB); Z.leb (mt_secret MTB + 8) (sp - 48)     (* [comment removed for export] *)
                          ; Z.ltb (sphi + spk) two64; Z.leb (img_hi A) (sp - 48)   (* [comment removed for export] *)
                          ; (Z.leb (img_hi A) (hl + hk - 16 - si) || ranges_apart_x k (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)) hb (hk - 16 - si) (mkAlu ALU_ADD ste (ELit (13 + si))))%bool   (* [comment removed for export] *)
                          ; kwritable_x k k spb (spk - 48) (ELit 48)                (* [comment removed for export] *)
                          ; AN.kimg_cover k (mt_sct MTB) (mt_sct MTB + 96)          (* [comment removed for export] *)
                          ; fresh_ok nx0 cs                                         (* [comment removed for export] *)
                          ; expr_vars_lt (nxt cs) ge; expr_vars_lt (nxt cs) reserved; expr_vars_lt (nxt cs) e12   (* [comment removed for export] *)
                          ; expr_vars_lt (nxt cs) pa; expr_vars_lt (nxt cs) We                                     (* [comment removed for export] *)
                          ; Z.ltb (hh + hk) two64 ] in                              (* [comment removed for export] *)
                if all_true bs then
                  let saves := [KWord (SA spb (spk - 8)) 8 (reg cs 1); KWord (SA spb (spk - 16)) 8 (reg cs 8);
                                KWord (SA spb (spk - 24)) 8 (reg cs 9); KWord (SA spb (spk - 32)) 8 (reg cs 18);
                                KWord (SA spb (spk - 40)) 8 (reg cs 19)] in
                  let k1 := saves ++ KUnk (SA spb (spk - 48)) (ELit 48) :: kn_havoc k spb (spk - 48) (ELit 48) in
                  let ss := a_ss cs in
                  let nx := s_next ss in
                  let sr0 := sr_fresh (s_regs ss) caller_saved nx in
                  let sr := sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr0
                              2 (EAlu ALU_ADD spb (ELit (spk - 48)))) 9 pa) 8 (ELit idx)) 10 ge) 11 We) 14 reserved) 15 e12 in
                  if (kn_vars_lt nx k1 && expr_vars_lt nx spb)%bool
                  then ROk (set_props (with_ss cs (mk_ss (mt_free_k MTB) sr k1 (nx + NCS)))
                                      (keep_props k [(SA spb (spk - 48), ELit 48)] nx (a_props cs)))
                  else RFresh
                else RConj bs
              | a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12 =>
                  RStage 6 [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12; Some mk; Some ek; Some hk]   (* [comment removed for export] *)
              end
            | a1, a2, a3, a4, a5, a6, a7 => RStage 5 [oz a1; oz a2; a3; a4; oz a5; oz a6; a7; Some gk; Some ak; Some ek]   (* [comment removed for export] *)
            end
          | None => RStage 4 [Some mk]                                                 (* [comment removed for export] *)
          end
        | None => RStage 3 [Some idx]                                                  (* [comment removed for export] *)
        end
      | a1, a2, a3 => RStage 2 [oz a1; a2; a3]                                         (* [comment removed for export] *)
      end
    | Some s, b, c => RStage 1 [Some (Z.of_nat (length s)); b; c]                      (* [comment removed for export] *)
    | None, b, c => RStage 1 [None; b; c; Some (Z.of_nat (length (slots_of cs)))]     (* [comment removed for export] *)
    end.
  (* [comment removed for export] *)
  Definition node_freehead2rM (cs : acs) : nres :=
    let k := kn cs in let bc := AX2B.mkbc k in   (* [comment removed for export] *) let pa := reg cs 10 in
    if negb (Z.eqb (pc cs) (mt_free MTB)) then RStage 0 [Some (pc cs); Some (mt_free MTB)] else
    let '(spb, spk) := split_lit (reg cs 2) in                                    (* [comment removed for export] *)
    match find_slot k pa (slots_of cs), AX2B.xloB bc spb, AX2B.xhiB bc spb with
    | Some [start; ste; ne; off; Ws; ELit idx; p], Some splo, Some sphi =>
      let sp := splo + spk in                                                       (* [comment removed for export] *)
      match decode_W Ws, AX2B.xloB bc ste, AX2B.xhiB bc ste with
      | Some (Se, c), Some slo, Some shi =>
        let li := c mod 32 in let sc := (c / 64) mod 64 in
        match (match ste with ELit st => Some ((st mod two64) * idx) | _ => if Z.eqb idx 0 then Some 0 else None end) with
        | Some si =>                                                                (* [comment removed for export] *)
          let Me := mkAlu ALU_ADD start (ELit (- (16 + si))) in                   (* [comment removed for export] *)
          let '(mb, mk) := split_lit Me in
          match kread8eB segs bc mb mk with                                           (* [comment removed for export] *)
          | Some ge =>
            let '(gb, gk) := split_lit ge in
            let ak := gk - gk mod 4096 in                                           (* [comment removed for export] *)
            let e := mkAlu ALU_ADD start (mkAlu ALU_ADD ste (ELit (-4))) in          (* [comment removed for export] *)
            let '(eb, ek) := split_lit e in
            let '(hb, hk) := split_lit start in
            match kread8eB segs bc gb (gk + 16), kread8eB segs bc gb (gk + 32), kzB bc gb (gk + 24) 4, kzB bc gb (gk + 28) 4,
                  kread8eB segs bc gb ak, kread8eB segs bc (ELit 0) (mt_secret MTB), kzB bc eb ek 1 with   (* [comment removed for export] *)
            | Some Me', Some We, Some avail, Some freed, Some sec, Some sec', Some zend =>
              match AX2B.xloB bc off, AX2B.xhiB bc off, AX2B.xloB bc gb, AX2B.xhiB bc gb, AX2B.xloB bc hb, AX2B.xhiB bc hb, AX2B.xloB bc Se, AX2B.xhiB bc Se,
                    AX2B.xloB bc mb, AX2B.xhiB bc mb, AX2B.xloB bc eb, AX2B.xhiB bc eb with
              | Some olo, Some ohi, Some glo, Some ghi, Some hl, Some hh, Some Slo, Some Shi, Some mlo, Some mhi, Some elo, Some ehi =>
                let qlo := si / 16 + olo in let qhi := si / 16 + ohi in                  (* [comment removed for export] *)
                let reserved := mkAlu ALU_SUB (mkAlu ALU_ADD ste (ELit (-4))) (mkAlu ALU_ADD ne (times16 off)) in
                let e12 := mkAlu ALU_ADD start (mkAlu ALU_ADD ste (ELit (-16))) in
                let bs := [ len_eqbB bc Me' Me                                        (* [comment removed for export] *)
                          ; expr_eqb We Ws                                          (* [comment removed for export] *)
                          ; Z.eqb zend 0                                            (* [comment removed for export] *)
                          ; Z.leb 1 slo; Z.leb Shi (2 ^ 40)                         (* [comment removed for export] *)
                          ; Z.leb 0 idx; Z.ltb idx 32; Z.eqb (si mod 16) 0; Z.leb 0 si   (* [comment removed for export] *)
                          ; ((Z.ltb sc 48 && Z.leb (size_class sc * idx) qlo && Z.ltb qhi (size_class sc * (idx + 1)))
                             || (Z.eqb sc 63 && Z.leb 1 Slo && Z.eqb li 0))%bool    (* [comment removed for export] *)
                          ; (Z.eqb Shi 0 || Z.leb qhi (Slo * 256 - 1))%bool         (* [comment removed for export] *)
                          ; Z.leb 0 olo                                             (* [comment removed for export] *)
                          ; negb (Z.testbit avail idx); negb (Z.testbit freed idx)  (* [comment removed for export] *)
                          ; Z.leb 0 avail; Z.ltb avail (2 ^ 32); Z.leb 0 freed; Z.ltb freed (2 ^ 32)   (* [comment removed for export] *)
                          ; page_alignedB bc gb                                       (* [comment removed for export] *)
                          ; expr_eqb sec sec'                                       (* [comment removed for export] *)
                          ; Z.leb 0 (glo + ak); Z.ltb (ghi + gk + 40) two64; Z.leb (16 + si) (hl + hk)   (* [comment removed for export] *)
                          ; Z.leb 0 (mlo + mk); Z.ltb (mhi + mk + 8) two64          (* [comment removed for export] *)
                          ; Z.leb 0 (elo + ek); Z.ltb (ehi + ek + 1) two64          (* [comment removed for export] *)
                          ; (Z.leb (hh + hk + shi) (sp - 48) || Z.leb (ehi + ek + 4) (sp - 48) || (inside_maps k (a_maps cs) hb hk ste && expr_eqb spb e_sp0 && Z.leb (- STK_BELOW) (spk - 48)))%bool   (* [comment removed for export] *)
                          ; (Z.leb (ghi + gk + 40) (sp - 48) || (inside_maps k (a_maps cs) gb gk (ELit 40) && expr_eqb spb e_sp0 && Z.leb (- STK_BELOW) (spk - 48)))%bool   (* [comment removed for export] *)
                          ; Z.leb 0 (mt_secret MTB); Z.leb (mt_secret MTB + 8) (sp - 48)     (* [comment removed for export] *)
                          ; Z.ltb (sphi + spk) two64; Z.leb (img_hi A) (sp - 48)   (* [comment removed for export] *)
                          ; (Z.leb (img_hi A) (hl + hk - 16 - si) || AX2B.ranges_apart_xB bc (ELit 0) (img_lo A) (ELit (img_hi A - img_lo A)) hb (hk - 16 - si) (mkAlu ALU_ADD ste (ELit (13 + si))))%bool   (* [comment removed for export] *)
                          ; kwritable_xB bc k spb (spk - 48) (ELit 48)                (* [comment removed for export] *)
                          ; AN.kimg_cover k (mt_sct MTB) (mt_sct MTB + 96)          (* [comment removed for export] *)
                          ; fresh_ok nx0 cs                                         (* [comment removed for export] *)
                          ; expr_vars_lt (nxt cs) ge; expr_vars_lt (nxt cs) reserved; expr_vars_lt (nxt cs) e12   (* [comment removed for export] *)
                          ; expr_vars_lt (nxt cs) pa; expr_vars_lt (nxt cs) We                                     (* [comment removed for export] *)
                          ; Z.ltb (hh + hk) two64 ] in                              (* [comment removed for export] *)
                if all_true bs then
                  let saves := [KWord (SA spb (spk - 8)) 8 (reg cs 1); KWord (SA spb (spk - 16)) 8 (reg cs 8);
                                KWord (SA spb (spk - 24)) 8 (reg cs 9); KWord (SA spb (spk - 32)) 8 (reg cs 18);
                                KWord (SA spb (spk - 40)) 8 (reg cs 19)] in
                  let k1 := saves ++ KUnk (SA spb (spk - 48)) (ELit 48) :: kn_havocB bc spb (spk - 48) (ELit 48) in
                  let ss := a_ss cs in
                  let nx := s_next ss in
                  let sr0 := sr_fresh (s_regs ss) caller_saved nx in
                  let sr := sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr0
                              2 (EAlu ALU_ADD spb (ELit (spk - 48)))) 9 pa) 8 (ELit idx)) 10 ge) 11 We) 14 reserved) 15 e12 in
                  if (kn_vars_lt nx k1 && expr_vars_lt nx spb)%bool
                  then ROk (set_props (with_ss cs (mk_ss (mt_free_k MTB) sr k1 (nx + NCS)))
                                      (keep_props k [(SA spb (spk - 48), ELit 48)] nx (a_props cs)))
                  else RFresh
                else RConj bs
              | a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12 =>
                  RStage 6 [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12; Some mk; Some ek; Some hk]   (* [comment removed for export] *)
              end
            | a1, a2, a3, a4, a5, a6, a7 => RStage 5 [oz a1; oz a2; a3; a4; oz a5; oz a6; a7; Some gk; Some ak; Some ek]   (* [comment removed for export] *)
            end
          | None => RStage 4 [Some mk]                                                 (* [comment removed for export] *)
          end
        | None => RStage 3 [Some idx]                                                  (* [comment removed for export] *)
        end
      | a1, a2, a3 => RStage 2 [oz a1; a2; a3]                                         (* [comment removed for export] *)
      end
    | Some s, b, c => RStage 1 [Some (Z.of_nat (length s)); b; c]                      (* [comment removed for export] *)
    | None, b, c => RStage 1 [None; b; c; Some (Z.of_nat (length (slots_of cs)))]     (* [comment removed for export] *)
    end.
  Lemma node_freehead2rM_eq : forall cs, node_freehead2rM cs = node_freehead2r cs.
  Proof.
    intros. unfold node_freehead2rM, node_freehead2r. cbv zeta.
    rewrite ?kread8eB_eqf. rewrite ?kreadZB_eqf. rewrite ?kread_bytesB_eqf. rewrite ?AX2B.xloB_eqf. rewrite ?AX2B.xhiB_eqf. rewrite ?AX2B.erangeB_eqf. rewrite ?AX2B.ealignB_eqf. rewrite ?AX2B.lin_ge0B_eqf. rewrite ?AX2B.ranges_apart_xB_eqf. rewrite ?AX2B.xinsideB_eqf. rewrite ?AX2B.foldKB_eqf. rewrite ?len_eqbB_eqf. rewrite ?page_alignedB_eqf. rewrite ?kwritable_xB_eqf. rewrite ?kwritableB_eqf. rewrite ?flat_xB_eqf. rewrite ?kzero_xB_eqf. rewrite ?off_image_xB_eqf. rewrite ?kn_havocB_eqf. rewrite ?kn_havocM_eq. rewrite ?kn_unfillB_eqf. rewrite ?kn_unfillM_eq. rewrite ?AN.eeqB_eqf. rewrite ?AN.argc_okB_eqf. rewrite ?AN.pieces_walkB_eqf. rewrite ?AN.extra_piecesB_eqf. rewrite ?AN.off_lazyB_eqf.
    reflexivity.
  Qed.
  (* [comment removed for export] *)
  Definition node_freehead2 (cs : acs) (args : list expr) : option acs := res_opt (node_freehead2r cs).
  Definition node_freehead2M (cs : acs) (args : list expr) : option acs := res_opt (node_freehead2rM cs).   (* [comment removed for export] *)
  Lemma node_freehead2M_eq : forall cs args, node_freehead2M cs args = node_freehead2 cs args.
  Proof. intros. unfold node_freehead2M, node_freehead2. rewrite node_freehead2rM_eq. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
    match id with
    | 20%nat => node_enframe2M cs args      (* [comment removed for export] *)
    | 21%nat => node_freehead2M cs args
    | _ => None
    end.
End WithSegs.
End MN2.
