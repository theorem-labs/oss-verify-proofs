(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3B AsanPlanCore AsanNodesRP.
From Stdlib Require Import FunctionalExtensionality.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module ALN.
Import AX2. Import AX2B. Import APC. Import AsanNodesRP.





Definition LIB_FRAME : Z := 4096.             
Definition LIB_NMAX : Z := 2 ^ 26.            
Definition LIB_KHI : Z := 0x10007fff8000.     
Definition LIB_HIEND : Z := 0x800000000000.   
Definition LIB_LOSH : Z := 0x7fff7000.        
Definition LIB_IMGLO : Z := 0x10000.          
Definition LIB_IMGHI : Z := 0x689000.         

Definition band_hi (A : atable) : Z := Z.max LIB_IMGLO (Z.min (img_hi A) LIB_IMGHI).
Definition LIB_SH : Z := 0x7fff8000.          (* [comment removed for export] *)
Definition FS_LEN : Z := 11571200.            (* [comment removed for export] *)
Definition FS_FLAGS : Z := 4096.
Definition FS_FRAMES : Z := 36864.
Definition FS_SHLO : Z := 4608.               (* [comment removed for export] *)
Definition FS_SHHI : Z := 1446400.            (* [comment removed for export] *)

(* [comment removed for export] *)
Record libtab : Type := LIBTAB {
  lt_tp  : Z;                 (* [comment removed for export] *)
  lt_ctx : Z;                 (* [comment removed for export] *)
  lt_dt  : Z;                 (* [comment removed for export] *)
  lt_can : Z;                 (* [comment removed for export] *)
  lt_ro  : list (Z * Z);      (* [comment removed for export] *)
  lt_rt  : list (Z * Z);      (* [comment removed for export] *)
  lt_gsh : list (Z * Z)       (* [comment removed for export] *)
}.

(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.
Variable L : libtab.
Variable A : atable.
Variable nx0 : nat.

#[local] Notation LIB_TP := (lt_tp L).
#[local] Notation CTX_CELL := (lt_ctx L).
#[local] Notation DT_CELL := (lt_dt L).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition img_readZ (a : Z) (n : nat) : option Z :=
  match rdn segs (fun _ => None) (Z_to_bv 64 a) n with
  | Some bs => Some (bytes_le_to_Z bs)
  | None => None
  end.

(* [comment removed for export] *)
Definition lfp_inside (lo hi : Z) : bool := existsb (fun r => (fst r <=? lo) && (hi <=? snd r))%bool (lib_fp A).

(* [comment removed for export] *)
Definition ro_range_ok (k : list kentry) (r : Z * Z) : bool :=
  let lo := fst r in let hi := snd r in
  if lfp_inside lo hi then true
  else if img_cov k lo hi then true
  else let n := Z.to_nat (hi - lo) in
       ((0 <? hi - lo) && (hi - lo <=? 8) &&
        match kreadZ segs k (ELit 0) lo n, img_readZ lo n with
        | Some v, Some w => Z.eqb v w
        | _, _ => false
        end)%bool.
Definition ro_ok_b (k : list kentry) : bool := forallb (ro_range_ok k) (lt_ro L).

(* [comment removed for export] *)
Definition cells_ok_b (k : list kentry) (l : list (Z * Z)) : bool :=
  forallb (fun c => match kreadZ segs k (ELit 0) (fst c) 1 with Some v => Z.eqb v (snd c) | None => false end) l.

(* [comment removed for export] *)
Definition piece_of (b : expr) (K : kentry) : option (Z * Z) :=
  match K with
  | KUnk (SA kb kk) (ELit l) | KZero (SA kb kk) (ELit l) | KFill (SA kb kk) (ELit l) _ | KBlob (SA kb kk) (ELit l) _ =>
      if (expr_eqb kb b && (0 <=? l) && (l <? two64))%bool then Some (kk, kk + l) else None
  | KWord (SA kb kk) w _ => if expr_eqb kb b then Some (kk, kk + Z.of_nat w) else None
  | _ => None
  end.
Fixpoint cover_step (ps : list (Z * Z)) (cur : Z) : Z :=
  match ps with
  | [] => cur
  | (lo, hi) :: r => if (lo <=? cur) && (cur <? hi) then cover_step r hi else cover_step r cur
  end%bool.
Fixpoint cover_go (fuel : nat) (ps : list (Z * Z)) (cur stop : Z) : bool :=
  if stop <=? cur then true else
  match fuel with
  | O => false
  | S f => let cur' := cover_step ps cur in if cur' <=? cur then false else cover_go f ps cur' stop
  end.
Definition kcover (k : list kentry) (b : expr) (off len : Z) : bool :=
  let ps := flat_map (fun K => match piece_of b K with Some p => [p] | None => [] end) k in
  cover_go (S (length ps)) ps off (off + len).

(* [comment removed for export] *)
Definition lib_payload_shadow_ok (k : list kentry) (data ne : expr) (nhi : Z) : bool := RPN.sym_shadow_ok segs k data ne.

(* [comment removed for export] *)
Definition app_memb (k : list kentry) (b : expr) (bk : Z) (ne : expr) (lo hi nhi : Z) : bool :=
  (hi + nhi <=? LIB_LOSH) || (LIB_KHI <=? lo) || ranges_apart_x k b bk ne (ELit LIB_LOSH) 0 (ELit (LIB_KHI - LIB_LOSH)).
Definition img_apartb (k : list kentry) (b : expr) (bk : Z) (n : Z) (lo hi : Z) : bool :=
  (hi + n <=? LIB_IMGLO) || (band_hi A <=? lo) || ranges_apart_x k b bk (ELit n) (ELit LIB_IMGLO) 0 (ELit (band_hi A - LIB_IMGLO)).
(* [comment removed for export] *)
Definition ctx_cellb (k : list kentry) (b : expr) (bk : Z) (n : Z) (lo hi : Z) : bool :=
  (4096 <=? lo) && img_apartb k b bk n lo hi && app_memb k b bk (ELit n) lo hi n && (hi + n <=? LIB_HIEND).

(* [comment removed for export] *)
Definition sshadow_sym (k : list kentry) (sp : expr) : bool :=
  let '(hb, hk) := split_lit (mkAlu ALU_ADD (mkSrl k (eaddz sp (- LIB_FRAME)) 3) (ELit LIB_SH)) in
  flat_x k hb hk (ELit (LIB_FRAME / 8)) && kzero_x k k hb hk (ELit (LIB_FRAME / 8)).

(* [comment removed for export] *)
Definition lib_extra_guard (cs : acs) (qb : expr) (qk : Z) (splo sphi : Z) (bb : expr) (bk : Z) (ne : expr) (nhi dlo dhi : Z)
  : option expr :=
  let k := kn cs in
  match know_lookup segs k (ELit 0) LIB_TP 8 false [] [] with
  | LHit fse [] _ =>
    let '(fb, fk) := split_lit fse in
    (* [comment removed for export] *)
    let she := mkAlu ALU_ADD (mkSrl k fse 3) (ELit LIB_SH) in
    let '(hb, hk) := split_lit she in
    match xlo k fse, xhi k fse,
          know_lookup segs k (ELit 0) CTX_CELL 8 false [] [], know_lookup segs k (ELit 0) DT_CELL 8 false [] [] with
    | Some flo, Some fhi, LHit ctxe [] _, LHit dte [] _ =>
      let '(cb, ck) := split_lit ctxe in
      match know_lookup segs k cb (ck + 0x98) 8 false [] [] with
      | LHit thre [] _ =>
        let '(tb, tk) := split_lit thre in
        let '(db, dk) := split_lit dte in
        match xlo k (mkAlu ALU_ADD ctxe (ELit 0x98)), xhi k (mkAlu ALU_ADD ctxe (ELit 0x98)),
              xlo k (mkAlu ALU_ADD thre (ELit 0x30)), xhi k (mkAlu ALU_ADD thre (ELit 0x30)),
              xlo k (mkAlu ALU_ADD dte (ELit 0x18)), xhi k (mkAlu ALU_ADD dte (ELit 0x18)), xlo k ctxe, xhi k ctxe with
        | Some c98lo, Some c98hi, Some t30lo, Some t30hi, Some d18lo, Some d18hi, Some clo, Some chi =>
          if ((* [comment removed for export] *)
              (12 <=? ealign k fse) && (img_hi A <=? flo) && app_memb k fb fk (ELit FS_LEN) flo fhi FS_LEN && (fhi + FS_LEN <=? LIB_HIEND)   (* [comment removed for export] *)
              (* [comment removed for export] *)
              && flat_x k fb fk (ELit FS_LEN) && kwritable_x A k k fb fk (ELit FS_LEN)
              && flat_x k hb (hk + FS_SHLO) (ELit (FS_SHHI - FS_SHLO)) && kwritable_x A k k hb (hk + FS_SHLO) (ELit (FS_SHHI - FS_SHLO))
              (* [comment removed for export] *)
              && kzero_x k k fb (fk + FS_FLAGS) (ELit 32768)
              && match kreadZ segs k fb (fk + 88) 8 with Some 20 => true | _ => false end
              && match kreadZ segs k fb (fk + 96) 1 with Some 0 => true | _ => false end
              (* [comment removed for export] *)
              && cells_ok_b k (lt_rt L) && ro_ok_b k && cells_ok_b k (lt_gsh L)
              (* [comment removed for export] *)
              && match kread8e segs k (ELit 0) (lt_can L) with Some _ => true | None => false end
              (* [comment removed for export] *)
              && (kzero_x k k (ELit 0) (LIB_SH + (splo - LIB_FRAME) / 8) (ELit ((sphi - splo + LIB_FRAME) / 8 + 2)) || sshadow_sym k (reg cs 2))
              (* [comment removed for export] *)
              && (0 <=? clo) && (chi + 0xa0 <=? LIB_HIEND)
              && ctx_cellb k cb (ck + 0x98) 8 c98lo c98hi && ctx_cellb k tb (tk + 0x30) 16 t30lo t30hi   (* [comment removed for export] *)
              && ctx_cellb k db (dk + 0x18) 8 d18lo d18hi
              && flat_x k cb (ck + 0x98) (ELit 8) && flat_x k db (dk + 0x18) (ELit 8)
              && flat_x k tb (tk + 0x30) (ELit 16) && kwritable_x A k k tb (tk + 0x30) (ELit 16)
              && match kreadZ segs k db (dk + 0x18) 8 with Some v => Z.eqb v LIB_TP | None => false end
              (* [comment removed for export] *)
              && ((c98hi + 8 <=? splo - LIB_FRAME) || ranges_apart_x k qb qk (ELit LIB_FRAME) cb (ck + 0x98) (ELit 8))   (* [comment removed for export] *)
              && ((t30hi + 16 <=? splo - LIB_FRAME) || ranges_apart_x k qb qk (ELit LIB_FRAME) tb (tk + 0x30) (ELit 16))
              && ((d18hi + 8 <=? splo - LIB_FRAME) || ranges_apart_x k qb qk (ELit LIB_FRAME) db (dk + 0x18) (ELit 8))
              && ranges_apart_x k cb (ck + 0x98) (ELit 8) fb fk (ELit FS_LEN)
              && ranges_apart_x k tb (tk + 0x30) (ELit 16) fb fk (ELit FS_LEN)
              && ranges_apart_x k db (dk + 0x18) (ELit 8) fb fk (ELit FS_LEN)
              (* [comment removed for export] *)
              && ((fhi + FS_LEN <=? splo - LIB_FRAME) || ranges_apart_x k qb qk (ELit LIB_FRAME) fb fk (ELit FS_LEN))   (* [comment removed for export] *)
              && (Z.eqb nhi 0 || Z.leb (dhi + nhi) flo || Z.leb (fhi + FS_LEN) dlo || ranges_apart_x k bb bk ne fb fk (ELit FS_LEN))
              (* [comment removed for export] *)
              && lib_payload_shadow_ok k (reg cs 10) ne nhi)%bool
          then Some fse else None
        | _, _, _, _, _, _, _, _ => None
        end
      | _ => None
      end
    | _, _, _, _ => None
    end
  | _ => None
  end.

(* [comment removed for export] *)
Definition lib_extra_effect (fb : expr) (fk : Z) (hb : expr) (hk : Z) (k : list kentry) : list kentry :=
  KUnk (SA fb fk) (ELit FS_LEN)                              (* [comment removed for export] *)
  :: KWord (SA fb (fk + 88)) 8 (ELit 20)                    (* [comment removed for export] *)
  :: KZero (SA fb (fk + 96)) (ELit 1)                       (* [comment removed for export] *)
  :: KZero (SA fb (fk + FS_FLAGS)) (ELit 32768)             (* [comment removed for export] *)
  :: KUnk (SA hb (hk + FS_SHLO)) (ELit (FS_SHHI - FS_SHLO))            (* [comment removed for export] *)
  :: k.

(* [comment removed for export] *)
Fixpoint lib_fp_havoc (rs : list (Z * Z)) (k : list kentry) : list kentry :=
  match rs with
  | [] => k
  | (lo, hi) :: rs' => lib_fp_havoc rs' (kn_havoc (kimg_cut k lo (hi - lo)) (ELit 0) lo (ELit (hi - lo)))
  end.

(* [comment removed for export] *)
Definition summary_lib_ref (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_lib A)) then None else
  match ret_lit cs, reg_lit cs 4 with
  | Some ret, Some tp =>
    if negb (Z.eqb ret (lib_ret A) && Z.eqb (ret mod 4) 0 && Z.eqb tp LIB_TP)%bool then None else
    let data := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(bb, bk) := split_lit data in
    let '(qb, qk) := split_lit (eaddz sp (- LIB_FRAME)) in
    match xhi k ne, xlo k data, xhi k data, xlo k sp, xhi k sp with
    | Some nhi, Some dlo, Some dhi, Some splo, Some sphi =>
      if (Z.leb 0 nhi && Z.ltb nhi LIB_NMAX
          && Z.leb 4096 dlo && Z.ltb (dhi + nhi + 4096) (2 ^ 62) && Z.leb 4 (ealign k data)
          && (Z.eqb bk 0 || flat_x k bb bk (ELit 1))
          && Z.leb 4 (ealign k sp) && Z.leb (2 ^ 32 + LIB_FRAME) splo && Z.leb LIB_KHI (splo - LIB_FRAME) && Z.leb sphi LIB_HIEND
          && flat_x k qb qk (ELit LIB_FRAME) && kwritable A k k qb qk LIB_FRAME
          && (Z.leb (dhi + nhi) (splo - LIB_FRAME) || Z.leb sphi dlo
              || ranges_apart_x k qb qk (ELit LIB_FRAME) bb bk ne)
          && (Z.eqb nhi 0 || Z.leb (dhi + nhi) (img_lo A) || Z.leb (img_hi A) dlo)
          && (Z.eqb nhi 0 || ((img_hi A <=? dlo) && app_memb k bb bk ne dlo dhi nhi
                               && (if dhi + nhi <=? LIB_HIEND then true else lin_ge0 k [(ELit LIB_HIEND, 0%Z)] [(bb, bk); (ne, 0%Z)])))
             (* [comment removed for export] *)
          && (Z.eqb nhi 0 || kn_readable_x k bb bk ne || kcover k bb bk nhi)
          && fresh_ok nx0 cs)%bool
      then match lib_extra_guard cs qb qk splo sphi bb bk ne nhi dlo dhi with
           | Some fse =>
               let '(fb, fk) := split_lit fse in
               let she := mkAlu ALU_ADD (mkSrl k fse 3) (ELit LIB_SH) in
               let '(hb, hk) := split_lit she in
               let k1 := kn_havoc k qb qk (ELit LIB_FRAME) in
               let k2 := lib_fp_havoc (lib_fp A) k1 in
               let k3 := kn_havoc k2 fb fk (ELit FS_LEN) in
               let k4 := kn_havoc k3 hb (hk + FS_SHLO) (ELit (FS_SHHI - FS_SHLO)) in
               after_call nx0 cs ret (Some (ELit 0)) (lib_extra_effect fb fk hb hk k4)
           | None => None
           end
      else None
    | _, _, _, _, _ => None
    end
  | _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ro_range_okB (bc : bctx) (r : Z * Z) : bool :=
  let lo := fst r in let hi := snd r in
  if lfp_inside lo hi then true
  else if img_covB bc lo hi then true
  else let n := Z.to_nat (hi - lo) in
       ((0 <? hi - lo) && (hi - lo <=? 8) &&
        match kreadZB segs bc (ELit 0) lo n, img_readZ lo n with
        | Some v, Some w => Z.eqb v w
        | _, _ => false
        end)%bool.
Definition ro_ok_bB (bc : bctx) : bool := forallb (ro_range_okB bc) (lt_ro L).
Definition cells_ok_bB (bc : bctx) (l : list (Z * Z)) : bool :=
  forallb (fun c => match kreadZB segs bc (ELit 0) (fst c) 1 with Some v => Z.eqb v (snd c) | None => false end) l.
Definition kn_readable_xB (bc : bctx) (rb : expr) (rk : Z) (ne : expr) : bool :=
  existsb (fun K => match K with
                    | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
                        xinsideLB bc rb rk ne kb kk len   (* [comment removed for export] *)
                    | _ => false
                    end) (bc_fk bc).

(* [comment removed for export] *)
Definition kreadZI (bc : bctx) (kx : kix) (b : expr) (off : Z) (n : nat) : option Z :=
  match know_lookupABI bc kx segs (bc_fk bc) b off n false [] [] with
  | LHit (ELit z) [] _ => Some (z mod two64)
  | _ => None
  end.
Lemma kreadZI_eq : forall bc, kreadZI bc (mk_kix (bc_fk bc)) = kreadZB segs bc.
Proof. intros. bcfe. unfold kreadZI, kreadZB, know_lookupB. rewrite know_lookupABI_eq. reflexivity. Qed.
Definition ro_range_okI (bc : bctx) (kx : kix) (r : Z * Z) : bool :=
  let lo := fst r in let hi := snd r in
  if lfp_inside lo hi then true
  else if img_covB bc lo hi then true
  else let n := Z.to_nat (hi - lo) in
       ((0 <? hi - lo) && (hi - lo <=? 8) &&
        match kreadZI bc kx (ELit 0) lo n, img_readZ lo n with
        | Some v, Some w => Z.eqb v w
        | _, _ => false
        end)%bool.
Definition ro_ok_bI (bc : bctx) (kx : kix) : bool := forallb (ro_range_okI bc kx) (lt_ro L).
Definition cells_ok_bI (bc : bctx) (kx : kix) (l : list (Z * Z)) : bool :=
  forallb (fun c => match kreadZI bc kx (ELit 0) (fst c) 1 with Some v => Z.eqb v (snd c) | None => false end) l.
Lemma kreadZI_eqk : forall k, kreadZI (mkbc k) (mk_kix k) = kreadZB segs (mkbc k).
Proof. intros k. exact (kreadZI_eq (mkbc k)). Qed.
Lemma ro_ok_bI_eq : forall k, ro_ok_bI (mkbc k) (mk_kix k) = ro_ok_bB (mkbc k).
Proof. intros. unfold ro_ok_bI, ro_ok_bB, ro_range_okI, ro_range_okB. rewrite kreadZI_eqk. reflexivity. Qed.
Lemma cells_ok_bI_eq : forall k, cells_ok_bI (mkbc k) (mk_kix k) = cells_ok_bB (mkbc k).
Proof. intros. bcfe. unfold cells_ok_bI, cells_ok_bB. rewrite kreadZI_eqk. reflexivity. Qed.

Lemma ro_range_okB_eqf : forall fk, ro_range_okB (mkbc fk) = ro_range_ok fk.
Proof. intros. bcfe. unfold ro_range_okB, ro_range_ok. rewrite ?img_covB_eqf, ?kreadZB_eqf. reflexivity. Qed.
Lemma ro_ok_bB_eqf : forall fk, ro_ok_bB (mkbc fk) = ro_ok_b fk.
Proof. intros. unfold ro_ok_bB, ro_ok_b. rewrite ro_range_okB_eqf. reflexivity. Qed.
Lemma cells_ok_bB_eqf : forall fk, cells_ok_bB (mkbc fk) = cells_ok_b fk.
Proof. intros. bcfe. unfold cells_ok_bB, cells_ok_b. rewrite ?kreadZB_eqf. reflexivity. Qed.
Lemma kn_readable_xB_eqf : forall fk, kn_readable_xB (mkbc fk) = kn_readable_x fk.
Proof. intros. bcfe. unfold kn_readable_xB, kn_readable_x. rewrite bc_fk_mkbc, ?xinsideLB_eqf. autorewrite with bceq. reflexivity. Qed.

(* [comment removed for export] *)
Definition app_membB (bc : bctx) (b : expr) (bk : Z) (ne : expr) (lo hi nhi : Z) : bool :=
  (if (if (hi + nhi <=? LIB_LOSH) then true else (LIB_KHI <=? lo)) then true else ranges_apart_xB bc b bk ne (ELit LIB_LOSH) 0 (ELit (LIB_KHI - LIB_LOSH))).   (* [comment removed for export] *)
Definition img_apartbB (bc : bctx) (b : expr) (bk : Z) (n : Z) (lo hi : Z) : bool :=
  (if (if (hi + n <=? LIB_IMGLO) then true else (band_hi A <=? lo)) then true else ranges_apart_xB bc b bk (ELit n) (ELit LIB_IMGLO) 0 (ELit (band_hi A - LIB_IMGLO))).   (* [comment removed for export] *)
Definition ctx_cellbB (bc : bctx) (b : expr) (bk : Z) (n : Z) (lo hi : Z) : bool :=
  (4096 <=? lo) && img_apartbB bc b bk n lo hi && app_membB bc b bk (ELit n) lo hi n && (hi + n <=? LIB_HIEND).
Lemma app_membB_eqf : forall fk, app_membB (mkbc fk) = app_memb fk.
Proof. intros. bcfe. unfold app_membB, app_memb. autorewrite with bceq. reflexivity. Qed.
Lemma img_apartbB_eqf : forall fk, img_apartbB (mkbc fk) = img_apartb fk.
Proof. intros. bcfe. unfold img_apartbB, img_apartb. autorewrite with bceq. reflexivity. Qed.
Lemma ctx_cellbB_eqf : forall fk, ctx_cellbB (mkbc fk) = ctx_cellb fk.
Proof. intros. bcfe. unfold ctx_cellbB, ctx_cellb. rewrite app_membB_eqf, img_apartbB_eqf. reflexivity. Qed.
Hint Rewrite app_membB_eqf img_apartbB_eqf ctx_cellbB_eqf : bceq.

Definition lib_extra_guardB (bc : bctx) (kx : kix) (cs : acs) (qb : expr) (qk : Z) (splo sphi : Z) (bb : expr) (bk : Z) (ne : expr) (nhi dlo dhi : Z)
  : option expr :=
  let k := bc_fk bc in
  match know_lookupB segs bc (ELit 0) LIB_TP 8 false [] [] with
  | LHit fse [] _ =>
    let '(fb, fk) := split_lit fse in
    let she := mkAlu ALU_ADD (mkSrlB bc fse 3) (ELit LIB_SH) in
    let '(hb, hk) := split_lit she in
    match xloB bc fse, xhiB bc fse,
          know_lookupB segs bc (ELit 0) CTX_CELL 8 false [] [], know_lookupB segs bc (ELit 0) DT_CELL 8 false [] [] with
    | Some flo, Some fhi, LHit ctxe [] _, LHit dte [] _ =>
      let '(cb, ck) := split_lit ctxe in
      match know_lookupB segs bc cb (ck + 0x98) 8 false [] [] with
      | LHit thre [] _ =>
        let '(tb, tk) := split_lit thre in
        let '(db, dk) := split_lit dte in
        match xloB bc (mkAlu ALU_ADD ctxe (ELit 0x98)), xhiB bc (mkAlu ALU_ADD ctxe (ELit 0x98)),
              xloB bc (mkAlu ALU_ADD thre (ELit 0x30)), xhiB bc (mkAlu ALU_ADD thre (ELit 0x30)),
              xloB bc (mkAlu ALU_ADD dte (ELit 0x18)), xhiB bc (mkAlu ALU_ADD dte (ELit 0x18)), xloB bc ctxe, xhiB bc ctxe with
        | Some c98lo, Some c98hi, Some t30lo, Some t30hi, Some d18lo, Some d18hi, Some clo, Some chi =>
          if ((12 <=? ealignB bc fse) && (img_hi A <=? flo) && app_membB bc fb fk (ELit FS_LEN) flo fhi FS_LEN && (fhi + FS_LEN <=? LIB_HIEND)
              && flat_xB bc fb fk (ELit FS_LEN) && kwritable_xB A bc k fb fk (ELit FS_LEN)
              && flat_xB bc hb (hk + FS_SHLO) (ELit (FS_SHHI - FS_SHLO)) && kwritable_xB A bc k hb (hk + FS_SHLO) (ELit (FS_SHHI - FS_SHLO))
              && kzero_xB bc k fb (fk + FS_FLAGS) (ELit 32768)
              && match kreadZB segs bc fb (fk + 88) 8 with Some 20 => true | _ => false end
              && match kreadZB segs bc fb (fk + 96) 1 with Some 0 => true | _ => false end
              && cells_ok_bI bc kx (lt_rt L) && ro_ok_bI bc kx && cells_ok_bI bc kx (lt_gsh L)
              && match kread8eB segs bc (ELit 0) (lt_can L) with Some _ => true | None => false end
              && (if kzero_xB bc k (ELit 0) (LIB_SH + (splo - LIB_FRAME) / 8) (ELit ((sphi - splo + LIB_FRAME) / 8 + 2)) then true else sshadow_sym k (reg cs 2))   (* [comment removed for export] *)
              && (0 <=? clo) && (chi + 0xa0 <=? LIB_HIEND)
              && ctx_cellbB bc cb (ck + 0x98) 8 c98lo c98hi && ctx_cellbB bc tb (tk + 0x30) 16 t30lo t30hi
              && ctx_cellbB bc db (dk + 0x18) 8 d18lo d18hi
              && flat_xB bc cb (ck + 0x98) (ELit 8) && flat_xB bc db (dk + 0x18) (ELit 8)
              && flat_xB bc tb (tk + 0x30) (ELit 16) && kwritable_xB A bc k tb (tk + 0x30) (ELit 16)
              && match kreadZB segs bc db (dk + 0x18) 8 with Some v => Z.eqb v LIB_TP | None => false end
              && (if (c98hi + 8 <=? splo - LIB_FRAME) then true else ranges_apart_xB bc qb qk (ELit LIB_FRAME) cb (ck + 0x98) (ELit 8))
              && (if (t30hi + 16 <=? splo - LIB_FRAME) then true else ranges_apart_xB bc qb qk (ELit LIB_FRAME) tb (tk + 0x30) (ELit 16))
              && (if (d18hi + 8 <=? splo - LIB_FRAME) then true else ranges_apart_xB bc qb qk (ELit LIB_FRAME) db (dk + 0x18) (ELit 8))
              && ranges_apart_xB bc cb (ck + 0x98) (ELit 8) fb fk (ELit FS_LEN)
              && ranges_apart_xB bc tb (tk + 0x30) (ELit 16) fb fk (ELit FS_LEN)
              && ranges_apart_xB bc db (dk + 0x18) (ELit 8) fb fk (ELit FS_LEN)
              && (if (fhi + FS_LEN <=? splo - LIB_FRAME) then true else ranges_apart_xB bc qb qk (ELit LIB_FRAME) fb fk (ELit FS_LEN))
              && (if (if (if Z.eqb nhi 0 then true else Z.leb (dhi + nhi) flo) then true else Z.leb (fhi + FS_LEN) dlo) then true else ranges_apart_xB bc bb bk ne fb fk (ELit FS_LEN))
              && RPN.sym_shadow_okB segs bc (reg cs 10) ne)%bool
          then Some fse else None
        | _, _, _, _, _, _, _, _ => None
        end
      | _ => None
      end
    | _, _, _, _ => None
    end
  | _ => None
  end.

Lemma lib_extra_guardB_eq : forall cs, lib_extra_guardB (mkbc (kn cs)) (mk_kix (kn cs)) cs = lib_extra_guard cs.
Proof.
  intros. bcfe. unfold lib_extra_guardB, lib_extra_guard, lib_payload_shadow_ok.
  rewrite ?cells_ok_bI_eq, ?ro_ok_bI_eq. rewrite bc_fk_mkbc.
  rewrite ?kwritable_xB_eqf, ?kzero_xB_eqf, ?flat_xB_eqf, ?kreadZB_eqf, ?kread8eB_eqf, ?cells_ok_bB_eqf, ?ro_ok_bB_eqf, ?RPN.sym_shadow_okB_eqf.
  autorewrite with bceq. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint lib_fp_havocM (rs : list (Z * Z)) (k : list kentry) : list kentry :=
  match rs with
  | [] => k
  | (lo, hi) :: rs' => lib_fp_havocM rs' (kn_havocM (kimg_cut k lo (hi - lo)) (ELit 0) lo (ELit (hi - lo)))
  end.
Lemma lib_fp_havocM_eq : lib_fp_havocM = lib_fp_havoc.
Proof.
  apply functional_extensionality; intros rs. apply functional_extensionality; revert rs.
  induction rs as [|[lo hi] rs IH]; intros k; cbn [lib_fp_havocM lib_fp_havoc]; [reflexivity|]. rewrite kn_havocM_eq. apply IH.
Qed.

Definition summary_lib (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_lib A)) then None else
  match ret_lit cs, reg_lit cs 4 with
  | Some ret, Some tp =>
    if negb (Z.eqb ret (lib_ret A) && Z.eqb (ret mod 4) 0 && Z.eqb tp LIB_TP)%bool then None else
    let bc := mkbc k in let kx := mk_kix k in
    let data := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(bb, bk) := split_lit data in
    let '(qb, qk) := split_lit (eaddz sp (- LIB_FRAME)) in
    match xhiB bc ne, xloB bc data, xhiB bc data, xloB bc sp, xhiB bc sp with
    | Some nhi, Some dlo, Some dhi, Some splo, Some sphi =>
      if (Z.leb 0 nhi && Z.ltb nhi LIB_NMAX
          && Z.leb 4096 dlo && Z.ltb (dhi + nhi + 4096) (2 ^ 62) && Z.leb 4 (ealignB bc data)
          && (Z.eqb bk 0 || flat_xB bc bb bk (ELit 1))
          && Z.leb 4 (ealignB bc sp) && Z.leb (2 ^ 32 + LIB_FRAME) splo && Z.leb LIB_KHI (splo - LIB_FRAME) && Z.leb sphi LIB_HIEND
          && flat_xB bc qb qk (ELit LIB_FRAME) && kwritableB A bc k qb qk LIB_FRAME
          && (if (if Z.leb (dhi + nhi) (splo - LIB_FRAME) then true else Z.leb sphi dlo) then true
              else ranges_apart_xB bc qb qk (ELit LIB_FRAME) bb bk ne)
          && (Z.eqb nhi 0 || Z.leb (dhi + nhi) (img_lo A) || Z.leb (img_hi A) dlo)
          && (Z.eqb nhi 0 || ((img_hi A <=? dlo) && app_membB bc bb bk ne dlo dhi nhi
                               && (if dhi + nhi <=? LIB_HIEND then true else lin_ge0B bc [(ELit LIB_HIEND, 0%Z)] [(bb, bk); (ne, 0%Z)])))
          && (if (if Z.eqb nhi 0 then true else kn_readable_xB bc bb bk ne) then true else kcover k bb bk nhi)
          && fresh_ok nx0 cs)%bool
      then match lib_extra_guardB bc kx cs qb qk splo sphi bb bk ne nhi dlo dhi with
           | Some fse =>
               let '(fb, fk) := split_lit fse in
               let she := mkAlu ALU_ADD (mkSrlB bc fse 3) (ELit LIB_SH) in
               let '(hb, hk) := split_lit she in
               let k1 := kn_havocB bc qb qk (ELit LIB_FRAME) in
               let k2 := lib_fp_havocM (lib_fp A) k1 in
               let k3 := kn_havocM k2 fb fk (ELit FS_LEN) in
               let k4 := kn_havocM k3 hb (hk + FS_SHLO) (ELit (FS_SHHI - FS_SHLO)) in
               after_call nx0 cs ret (Some (ELit 0)) (lib_extra_effect fb fk hb hk k4)
           | None => None
           end
      else None
    | _, _, _, _, _ => None
    end
  | _, _ => None
  end.

Lemma summary_lib_eq : forall cs, summary_lib cs = summary_lib_ref cs.
Proof.
  intros cs. unfold summary_lib, summary_lib_ref. cbv zeta.
  rewrite lib_extra_guardB_eq, ?kwritableB_eqf, ?flat_xB_eqf, ?kn_readable_xB_eqf, ?kn_havocB_eqf, ?kn_havocM_eq, ?lib_fp_havocM_eq.
  autorewrite with bceq. reflexivity.
Qed.
End WithSegs.
End ALN.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
