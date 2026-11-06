(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.

Module EXN.

(* [comment removed for export] *)
Definition TAB_CAP : Z := 4096.

Section WithSegs.
Variable segs : list Segment.
Variable IT : itab.
Variable nx0 : nat.

(* [comment removed for export] *)
Fixpoint le_val (bs : list Z) : Z :=
  match bs with [] => 0 | b :: rest => Z.lor b (Z.shiftl (le_val rest) 8) end.

(* [comment removed for export] *)
Definition elem_val (kl : list kentry) (B : expr) (sx : bool) (n : nat) (k : Z) : option Z :=
  match know_bytes_lit segs kl B k n with
  | Some bs => let u := le_val bs in
               Some (if sx then (bv_swrap (8 * N.of_nat n) u) mod two64 else u)
  | None => None
  end.

(* [comment removed for export] *)
Fixpoint scan (kl : list kentry) (B : expr) (sx : bool) (n : nat) (k step : Z) (cnt : nat) (acc : option (Z * Z))
  : option (Z * Z) :=
  match cnt with
  | O => acc
  | S c =>
      match elem_val kl B sx n k with
      | Some v =>
          let acc' := match acc with
                      | Some (mn, mx) => Some (Z.min mn v, Z.max mx v)
                      | None => Some (v, v)
                      end in
          scan kl B sx n (k + step) step c acc'
      | None => None   (* [comment removed for export] *)
      end
  end.
(* [comment removed for export] *)
Fixpoint scan_mask (kl : list kentry) (B : expr) (sx : bool) (n : nat) (k step : Z) (cnt : nat) (m : Z) (acc : option (option Z))
  : option (option Z) :=
  match cnt with
  | O => match acc with Some a => Some a | None => Some None end
  | S c =>
      match elem_val kl B sx n k with
      | Some v =>
          let b := Z.land v m in
          let acc' := match acc with
                      | None => Some (Some b)
                      | Some (Some b0) => if Z.eqb b0 b then Some (Some b0) else Some None
                      | Some None => Some None
                      end in
          scan_mask kl B sx n (k + step) step c m acc'
      | None => None
      end
  end.
(* [comment removed for export] *)
Definition stride_log (k : list kentry) (X : expr) (xl : Z) : Z := Z.min 6 (ealign k (mkAlu ALU_SUB X (ELit xl))).

(* [comment removed for export] *)
Definition tab_entry (B : expr) (K : kentry) : bool :=
  match K with
  | KWord (SA kb _) _ (ELit _) | KZero (SA kb _) (ELit _) | KFill (SA kb _) (ELit _) _ => expr_eqb kb B
  | KImg _ _ => match B with ELit 0 => true | _ => false end
  | _ => false
  end.

Definition load_width (sz : msize) : nat :=
  match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end%nat.

(* [comment removed for export] *)
Definition node_tabread (cs : acs) (args : list expr) : option acs :=
  if negb (fresh_ok nx0 cs && Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64)%bool then None else
  match itab_lookup IT (pc cs) with
  | Some (Load sz sx rd rs imm) =>
      if bv_eqb rd 0%bv then None else
      let n := load_width sz in
      let sx' := match sz with SZ8 => false | _ => sx end in
      let e := mkAlu ALU_ADD (sr_get (s_regs (a_ss cs)) rs) (ELit (bv_signed imm)) in
      let msk := match args with [_; ELit m] => if (Z.leb 0 m && Z.ltb m two64)%bool then Some m else None | _ => None end in
      match match args with
            | [] => Some (ELit 0, e)
            | [B] | [B; ELit _] => Some (B, mkAlu ALU_SUB e B)
            | _ => None
            end with
      | None => None
      | Some (B, X) =>
      (* [comment removed for export] *)
      let '(Bb, Bo) := split_lit B in
      match xlo (kn cs) X, xhi (kn cs) X, xlo (kn cs) B, xhi (kn cs) B, xlo (kn cs) Bb, xhi (kn cs) Bb with
      | Some xl, Some xh, Some bl, Some bh, Some bbl, Some bbh =>
          let st := 2 ^ stride_log (kn cs) X xl in
          let cnt := (xh - xl) / st + 1 in
          if negb (Z.leb 0 xl && Z.leb xl xh && Z.leb cnt TAB_CAP && Z.leb 0 (bl + xl) && Z.leb (bh + xh + Z.of_nat n) two64
                   && Z.leb 0 (bbl + Bo) && Z.ltb (bbh + Bo) two64)%bool
          then None else
          let kl := List.filter (tab_entry Bb) (kn cs) in
          match scan kl Bb sx' n (Bo + xl) st (Z.to_nat cnt) None with
          | Some (mn, mx) =>
              let ss := a_ss cs in
              let rv := if Z.eqb mn mx then ELit mn else EVar (nxt cs) in
              let facts := if Z.eqb mn mx then [] else [KRange rv mn mx] in
              (* [comment removed for export] *)
              let mfact := match msk with
                           | Some m => if Z.eqb mn mx then [] else
                                       match scan_mask kl Bb sx' n (Bo + xl) st (Z.to_nat cnt) m None with
                                       | Some (Some b) => [KRange (mkAlu ALU_AND rv (ELit m)) b b]
                                       | _ => []
                                       end
                           | None => [] end in
              let nx' := if Z.eqb mn mx then nxt cs else S (nxt cs) in
              (* [comment removed for export] *)
              let recs := if rec_onb (kn cs) then [KWord (SA e 0) n rv] else [] in   (* [comment removed for export] *)
              Some (with_ss cs (mk_ss (pc cs + 4) (sr_upd (s_regs ss) (ridx rd) rv)
                                      ((facts ++ mfact) ++ recs ++ s_know ss) nx'))
          | None => None
          end
      | _, _, _, _, _, _ => None
      end
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition node_recon (cs : acs) (args : list expr) : option acs :=
  match args with
  | [] => Some (if rec_onb (kn cs) then cs else set_kn cs (KRec :: kn cs))
  | _ => None
  end.
Definition node_recoff (cs : acs) (args : list expr) : option acs :=
  match args with
  | [] => Some (set_kn cs (List.filter (fun K => negb (krecb K)) (kn cs)))
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint bcore (e : expr) : option nat :=
  match e with
  | EExt _ 0 1 (EVar v) => Some v
  | EExt _ 0 1 a => bcore a
  | _ => None
  end.
Definition node_brespell (cs : acs) (args : list expr) : option acs :=
  match args with
  | [ELit r] =>
      let rn := Z.to_nat r in
      if negb (Nat.ltb 0 rn && Nat.ltb rn 32)%bool then None else
      match reg cs rn with
      | EExt sx 0 1 a =>
          match bcore (EExt sx 0 1 a) with
          | Some v => Some (set_reg cs rn (if sx then EExt true 0 1 (EExt false 0 1 (EVar v)) else EExt false 0 1 (EVar v)))
          | None => None
          end
      | _ => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition elem_valI (kx : AX2B.kix) (B : expr) (sx : bool) (n : nat) (k : Z) : option Z :=
  match AX2B.know_bytes_litI segs kx B k n with
  | Some bs => let u := le_val bs in
               Some (if sx then (bv_swrap (8 * N.of_nat n) u) mod two64 else u)
  | None => None
  end.
Fixpoint scanI (kx : AX2B.kix) (B : expr) (sx : bool) (n : nat) (k step : Z) (cnt : nat) (acc : option (Z * Z))
  : option (Z * Z) :=
  match cnt with
  | O => acc
  | S c =>
      match elem_valI kx B sx n k with
      | Some v =>
          let acc' := match acc with
                      | Some (mn, mx) => Some (Z.min mn v, Z.max mx v)
                      | None => Some (v, v)
                      end in
          scanI kx B sx n (k + step) step c acc'
      | None => None
      end
  end.
Lemma scanI_eq : forall kl B sx n cnt k step acc,
  scanI (AX2B.mk_kix0 kl) B sx n k step cnt acc = scan kl B sx n k step cnt acc.
Proof.
  intros kl B sx n cnt. induction cnt as [|c IH]; intros k step acc; [reflexivity|].
  cbn [scanI scan]. unfold elem_valI, elem_val. rewrite AX2B.know_bytes_litI_eq.
  destruct (know_bytes_lit segs kl B k n); [|reflexivity]. apply IH.
Qed.
Definition scanK (kl : list kentry) (B : expr) (sx : bool) (n : nat) (k step : Z) (cnt : nat) (acc : option (Z * Z)) :=
  scanI (AX2B.mk_kix0 kl) B sx n k step cnt acc.
Lemma scanK_eqf : scanK = scan.
Proof.
  repeat (apply functional_extensionality; intros ?). unfold scanK. apply scanI_eq.
Qed.
Fixpoint scan_maskI (kx : AX2B.kix) (B : expr) (sx : bool) (n : nat) (k step : Z) (cnt : nat) (m : Z) (acc : option (option Z))
  : option (option Z) :=
  match cnt with
  | O => match acc with Some a => Some a | None => Some None end
  | S c =>
      match elem_valI kx B sx n k with
      | Some v =>
          let b := Z.land v m in
          let acc' := match acc with
                      | None => Some (Some b)
                      | Some (Some b0) => if Z.eqb b0 b then Some (Some b0) else Some None
                      | Some None => Some None
                      end in
          scan_maskI kx B sx n (k + step) step c m acc'
      | None => None
      end
  end.
Lemma scan_maskI_eq : forall kl B sx n cnt m k step acc,
  scan_maskI (AX2B.mk_kix0 kl) B sx n k step cnt m acc = scan_mask kl B sx n k step cnt m acc.
Proof.
  intros kl B sx n cnt m. induction cnt as [|c IH]; intros k step acc; [reflexivity|].
  cbn [scan_maskI scan_mask]. unfold elem_valI, elem_val. rewrite AX2B.know_bytes_litI_eq.
  destruct (know_bytes_lit segs kl B k n); [|reflexivity]. apply IH.
Qed.
Definition scan_maskK (kl : list kentry) (B : expr) (sx : bool) (n : nat) (k step : Z) (cnt : nat) (m : Z) (acc : option (option Z)) :=
  scan_maskI (AX2B.mk_kix0 kl) B sx n k step cnt m acc.
Lemma scan_maskK_eqf : scan_maskK = scan_mask.
Proof.
  repeat (apply functional_extensionality; intros ?). unfold scan_maskK. apply scan_maskI_eq.
Qed.
Definition node_tabreadM (cs : acs) (args : list expr) : option acs :=
  if negb (fresh_ok nx0 cs && Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64)%bool then None else
  match itab_lookup IT (pc cs) with
  | Some (Load sz sx rd rs imm) =>
      if bv_eqb rd 0%bv then None else
      let n := load_width sz in
      let sx' := match sz with SZ8 => false | _ => sx end in
      let e := mkAlu ALU_ADD (sr_get (s_regs (a_ss cs)) rs) (ELit (bv_signed imm)) in
      let msk := match args with [_; ELit m] => if (Z.leb 0 m && Z.ltb m two64)%bool then Some m else None | _ => None end in
      match match args with
            | [] => Some (ELit 0, e)
            | [B] | [B; ELit _] => Some (B, mkAlu ALU_SUB e B)
            | _ => None
            end with
      | None => None
      | Some (B, X) =>
      (* [comment removed for export] *)
      let '(Bb, Bo) := split_lit B in
      match xlo (kn cs) X, xhi (kn cs) X, xlo (kn cs) B, xhi (kn cs) B, xlo (kn cs) Bb, xhi (kn cs) Bb with
      | Some xl, Some xh, Some bl, Some bh, Some bbl, Some bbh =>
          let st := 2 ^ stride_log (kn cs) X xl in
          let cnt := (xh - xl) / st + 1 in
          if negb (Z.leb 0 xl && Z.leb xl xh && Z.leb cnt TAB_CAP && Z.leb 0 (bl + xl) && Z.leb (bh + xh + Z.of_nat n) two64
                   && Z.leb 0 (bbl + Bo) && Z.ltb (bbh + Bo) two64)%bool
          then None else
          let kl := List.filter (tab_entry Bb) (kn cs) in
          match scanK kl Bb sx' n (Bo + xl) st (Z.to_nat cnt) None with   (* [comment removed for export] *)
          | Some (mn, mx) =>
              let ss := a_ss cs in
              let rv := if Z.eqb mn mx then ELit mn else EVar (nxt cs) in
              let facts := if Z.eqb mn mx then [] else [KRange rv mn mx] in
              (* [comment removed for export] *)
              let mfact := match msk with
                           | Some m => if Z.eqb mn mx then [] else
                                       match scan_maskK kl Bb sx' n (Bo + xl) st (Z.to_nat cnt) m None with
                                       | Some (Some b) => [KRange (mkAlu ALU_AND rv (ELit m)) b b]
                                       | _ => []
                                       end
                           | None => [] end in
              let nx' := if Z.eqb mn mx then nxt cs else S (nxt cs) in
              (* [comment removed for export] *)
              let recs := if rec_onb (kn cs) then [KWord (SA e 0) n rv] else [] in   (* [comment removed for export] *)
              Some (with_ss cs (mk_ss (pc cs + 4) (sr_upd (s_regs ss) (ridx rd) rv)
                                      ((facts ++ mfact) ++ recs ++ s_know ss) nx'))
          | None => None
          end
      | _, _, _, _, _, _ => None
      end
      end
  | _ => None
  end.

Lemma node_tabreadM_eq : forall cs args, node_tabreadM cs args = node_tabread cs args.
Proof.
  intros cs args. unfold node_tabreadM, node_tabread. rewrite scanK_eqf, scan_maskK_eqf. reflexivity.
Qed.
Lemma node_tabreadM_eqf : node_tabreadM = node_tabread.
Proof. apply functional_extensionality; intros cs. apply functional_extensionality; intros args. apply node_tabreadM_eq. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition node_namecell (cs : acs) (args : list expr) : option acs :=
  match args with
  | [a; ELit nz] =>
      let k := kn cs in
      let '(ab, ao) := split_lit a in
      if (fresh_ok nx0 cs && (Z.eqb nz 1 || Z.eqb nz 2 || Z.eqb nz 4 || Z.eqb nz 8)
          && expr_vars_lt (nxt cs) ab && kwritable k k ab ao nz)%bool
      then let ss := a_ss cs in
           Some (with_ss cs (mk_ss (s_pc ss) (s_regs ss) (KWord (SA ab ao) (Z.to_nat nz) (EVar (nxt cs)) :: s_know ss) (S (nxt cs))))
      else None
  | _ => None
  end.

Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with
  | 40%nat => node_tabreadM cs args   (* [comment removed for export] *)
  | 41%nat => node_recon cs args
  | 42%nat => node_recoff cs args
  | 44%nat => node_brespell cs args   (* [comment removed for export] *)
  | 45%nat => node_namecell cs args   (* [comment removed for export] *)
  | _ => None
  end.
Lemma xn_unfold : forall id args cs,
  xn id args cs = match id with 40%nat => node_tabread cs args | 41%nat => node_recon cs args | 42%nat => node_recoff cs args | 44%nat => node_brespell cs args | 45%nat => node_namecell cs args | _ => None end.
Proof. intros id args cs. unfold xn. do 46 (destruct id as [|id]; [first [reflexivity | apply node_tabreadM_eq] |]). reflexivity. Qed.

End WithSegs.
End EXN.
