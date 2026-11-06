(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg AllocCfg.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxMemSound FxValSound FxStepSound FxStepMain FxRun FxRn FxSys.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fent : Type := (int * int * int)%type.

Record fledger : Type := FL {
  fl_maps : list fent;     (* [comment removed for export] *)
  fl_na   : list fent;     (* [comment removed for export] *)
  fl_brk  : int;           (* [comment removed for export] *)
  fl_c    : Z;             (* [comment removed for export] *)
  fl_S    : Z              (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Inductive role : Set := RSrc | RTgt.

(* [comment removed for export] *)
Inductive dres : Type :=
| DOne (F : fstate) (L : fledger) (n : int)
| DTwo (F1 : fstate) (L1 : fledger) (n1 : int) (F2 : fstate) (L2 : fledger) (n2 : int).

(* [comment removed for export] *)
Inductive dtree : Type :=
| DLeaf (F : fstate) (L : fledger) (n : int) (r : stop)
| DFork (t1 t2 : dtree).

Fixpoint leaf_in (x : fstate * fledger * int * stop) (t : dtree) : Prop :=
  match t with
  | DLeaf F L n r => x = (F, L, n, r)
  | DFork t1 t2 => leaf_in x t1 \/ leaf_in x t2
  end.

Section DriveDefs.
Local Open Scope uint63_scope.

(* [comment removed for export] *)
Definition conc (v : fval) : option int :=
  match v with
  | FV t (W64 top lo) => if (t =? 0) && ((top land 1) =? 0) then Some lo else None
  end.

(* [comment removed for export] *)
Definition ptr (v : fval) : option (int * int) :=
  match v with
  | FV t (W64 top lo) => if ((top land 1) =? 0) && is_plain t then Some (t, lo) else None
  end.

(* [comment removed for export] *)
Definition pg_up (len : int) : int := ((len + 4095) >> 12) << 12.

Definition fent_eqb (e1 e2 : fent) : bool :=
  match e1, e2 with
  | (t1, o1, l1), (t2, o2, l2) => (t1 =? t2) && (o1 =? o2) && (l1 =? l2)
  end.

Definition fent_tag (e : fent) : int := fst (fst e).

Definition mem_fent (e : fent) (l : list fent) : bool := existsb (fent_eqb e) l.
Definition mem_int (t : int) (l : list int) : bool := existsb (fun x => x =? t) l.

Definition drop_tag (t : int) (l : list fent) : list fent :=
  List.filter (fun e => negb (fent_tag e =? t)) l.

Variable IM : fimage.
Variable code : itrie finstr.

Definition ecall_here (F : fstate) : bool :=
  match iget (f_pc F) code with Some FEcall => true | _ => false end.

(* [comment removed for export] *)
Variable Rb Rc Lim : Z.
Variable rl : role.
Variable keep : list int.
(* [comment removed for export] *)
Variable xsys : fstate -> fledger -> int -> option dres.
(* [comment removed for export] *)
Variable xask : fstate -> option (int * int).

Definition grant_fits (L : fledger) (nZ : Z) : bool :=
  (4096 + (Rb + fl_S L) + (Rc + fl_c L) * (nZ + 4096) + nZ <=? 140735332483072)%Z
  && match rl with RSrc => true | RTgt => (fl_S L + nZ <=? Lim)%Z end.

Definition tag_ok (F : fstate) (n : int) : bool :=
  (0 <? n) && (n <? 1152921504606846976) && regions_lt_b n (f_mem F).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition sys_grant (F : fstate) (L : fledger) (n : int) (len : int) : option dres :=
  let nZi := pg_up len in
  if (0 <? len) && (len <=? 4611686018427387904) && (nZi <=? 4611686018427387904)
     && tag_ok F n && grant_fits L (to_Z nZi)
  then Some (DOne (fx_grant F n nZi)
                  (FL ((n, 0, nZi) :: fl_maps L) (fl_na L) (fl_brk L) (fl_c L + 1) (fl_S L + to_Z nZi))
                  (n + 1))
  else None.

(* [comment removed for export] *)
Definition sys_unmap (F : fstate) (L : fledger) (n : int) (t off len : int) : option dres :=
  match iget t (f_mem F) with
  | Some rg =>
      if (off =? 0) && negb (t =? 0) && (t <? n) && negb (t =? fl_brk L) && negb (mem_int t keep)
         && (0 <? len) && (len <=? 4611686018427387904)
         && (rg_lo rg =? 0) && (pg_up len =? rg_len rg)
         && mem_fent (t, 0, rg_len rg) (fl_maps L)
      then Some (DOne (fx_unmap F t)
                      (FL (drop_tag t (fl_maps L)) (drop_tag t (fl_na L)) (fl_brk L)
                          (fl_c L - 1) (fl_S L - to_Z (rg_len rg)))
                      n)
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition sys_brk_query (F : fstate) (L : fledger) (n : int) : option dres :=
  match iget (fl_brk L) (f_mem F) with
  | Some rg => if fl_brk L <? n
               then Some (DOne (fx_ret F (FV (fl_brk L) (W64 0 (rg_len rg)))) L n)
               else None
  | None => None
  end.

Definition na_fits (L : fledger) (nZ : Z) : bool :=
  (4096 + (Rb + fl_S L) + (Rc + fl_c L) * (nZ + 4096) + nZ <=? 140735332483072)%Z.

(* [comment removed for export] *)
Definition sys_grant_na (F : fstate) (L : fledger) (n : int) (len : int) : option dres :=
  let nZi := pg_up len in
  if (0 <? len) && (len <=? 4611686018427387904) && (nZi <=? 4611686018427387904)
     && tag_ok F n && na_fits L (to_Z nZi)
  then Some (DOne (fx_grant_na F n nZi)
                  (FL ((n, 0, nZi) :: fl_maps L) ((n, 0, nZi) :: fl_na L) (fl_brk L)
                      (fl_c L + 1) (fl_S L + to_Z nZi))
                  (n + 1))
  else None.

(* [comment removed for export] *)
Definition ent_covers (t off sz : int) (e : fent) : bool :=
  match e with (t', eo, el) => (t' =? t) && (eo <=? off) && (off + sz <=? eo + el) end.

(* [comment removed for export] *)
Definition ent_sub (t off sz : int) (e : fent) : list fent :=
  match e with
  | (t', eo, el) =>
      if negb (t' =? t) then [e]
      else
        (if eo <? off then [(t, eo, if el <? off - eo then el else off - eo)] else [])
        ++ (if off + sz <? eo + el
            then let mx := if eo <? off + sz then off + sz else eo in [(t, mx, eo + el - mx)]
            else [])
  end.
Definition fl_sub (t off sz : int) (l : list fent) : list fent := flat_map (ent_sub t off sz) l.

(* [comment removed for export] *)
Definition range_ok (F : fstate) (n t off len : int) : bool :=
  match iget t (f_mem F) with
  | Some rg =>
      (t <? n) && negb (mem_int t keep) && (0 <? len) && (len <=? 2305843009213693952)
      && (off <? 4611686018427387904) && (off + pg_up len <? 4611686018427387904)
      && ((off land 4095) =? 0) && (12 <=? rg_align rg) && (rg_align rg <? 64)
  | None => false
  end.

(* [comment removed for export] *)
Definition sys_guard (F : fstate) (L : fledger) (n : int) (t off len : int) : option dres :=
  let nZi := pg_up len in
  if range_ok F n t off len then
    match List.find (ent_covers t off nZi) (fl_maps L) with
    | Some _ =>
        Some (DOne (fx_guard F t (off >> 12) (Z.to_nat (to_Z (nZi >> 12))))
                   (FL (fl_maps L) ((t, off, nZi) :: fl_sub t off nZi (fl_na L))
                       (fl_brk L) (fl_c L) (fl_S L))
                   n)
    | None => None
    end
  else None.

(* [comment removed for export] *)
Definition sys_expose (F : fstate) (L : fledger) (n : int) (t off len : int) : option dres :=
  let nZi := pg_up len in
  if range_ok F n t off len
     && match rl with RSrc => true | RTgt => (fl_S L <=? Lim)%Z end then
    match List.find (ent_covers t off nZi) (fl_na L) with
    | Some _ =>
        Some (DOne (fx_expose F t (off >> 12) (Z.to_nat (to_Z (nZi >> 12))))
                   (FL (fl_maps L) (fl_sub t off nZi (fl_na L))
                       (fl_brk L) (fl_c L) (fl_S L))
                   n)
    | None => None
    end
  else None.

(* [comment removed for export] *)
Definition sys_brk_grow (F : fstate) (L : fledger) (n : int) (t off : int) : option dres :=
  match iget t (f_mem F) with
  | Some rg =>
      let d := off - rg_len rg in
      if (t =? fl_brk L) && (t <? n) && negb (mem_int t keep)
         && (rg_len rg <? off) && (off <=? 4611686018427387904)
         && ((d land 4095) =? 0) && ((rg_len rg land 4095) =? 0) && (rg_lo rg <=? rg_len rg)
      then Some (DTwo (fx_brk_grow F t (Z.to_nat (to_Z (d >> 12))))
                      (FL ((t, rg_len rg, d) :: fl_maps L) (fl_na L) (fl_brk L)
                          (fl_c L + 1) (fl_S L + to_Z d))
                      n
                      (fx_ret F (FV t (W64 0 (rg_len rg)))) L n)
      else None
  | None => None
  end.

Definition drive_sys_own (F : fstate) (L : fledger) (n : int) : option dres :=
  if negb (ecall_here F) then None else
  match conc (rget F 17) with
  | None => None
  | Some nr =>
    if nr =? 222 then
      match conc (rget F 11), conc (rget F 12), conc (rget F 13), conc (rget F 15) with
      | Some len, Some prot, Some flags, Some o =>
          if negb (o =? 0) then None
          else if (prot =? 3) && (flags =? 34) then sys_grant F L n len
          else if (prot =? 0) && (flags =? 34) then sys_grant_na F L n len
          else if (prot =? 0) && (flags =? 50) then
            match ptr (rget F 10) with
            | Some (t, off) => sys_guard F L n t off len
            | None => None
            end
          else None
      | _, _, _, _ => None
      end
    else if nr =? 215 then
      match ptr (rget F 10), conc (rget F 11) with
      | Some (t, off), Some len => sys_unmap F L n t off len
      | _, _ => None
      end
    else if nr =? 214 then
      match ptr (rget F 10) with
      | Some (t, off) =>
          if (t =? 0) && (off =? 0) then sys_brk_query F L n else sys_brk_grow F L n t off
      | None => None
      end
    else if nr =? 226 then
      match ptr (rget F 10), conc (rget F 11), conc (rget F 12) with
      | Some (t, off), Some len, Some prot =>
          if prot =? 3 then sys_expose F L n t off len else None
      | _, _, _ => None
      end
    else None
  end.

Definition drive_sys (F : fstate) (L : fledger) (n : int) : option dres :=
  match drive_sys_own F L n with
  | Some r => Some r
  | None => xsys F L n
  end.

(* [comment removed for export] *)
Definition rebound (rg : region) (clo chi : int) : region :=
  RGK (rg_lo rg) (rg_len rg) (rg_align rg) (rg_dflt rg) (rg_pages rg) clo chi (rg_kind rg).
Definition set_bounds (F : fstate) (t : int) (rg : region) (clo chi : int) : fstate :=
  FS (f_pc F) (f_regs F) (iset t (rebound rg clo chi) (f_mem F)) (f_resv F).
Definition refine_region (F : fstate) (n t thr : int) : option (fstate * fstate) :=
  match iget t (f_mem F) with
  | Some rg =>
      if (t <? n) && (12 <=? rg_align rg) && ((thr land 4095) =? 0) && (4096 <=? thr)
         && (rg_clo rg <? thr) && (thr <=? rg_chi rg)
      then Some (set_bounds F t rg (rg_clo rg) (thr - 4096), set_bounds F t rg thr (rg_chi rg))
      else None
  | None => None
  end.
Definition ask_split (F : fstate) (n : int) : option (fstate * fstate) :=
  match xask F with
  | Some (t, thr) => refine_region F n t thr
  | None => None
  end.

(* [comment removed for export] *)
Fixpoint drive (bp : int) (k : nat) (fuel : nat) (F : fstate) (L : fledger) (n : int) : dtree :=
  match fuel with
  | O => DLeaf F L n SFuel
  | S fuel' =>
      match fx_run IM code bp k F with
      | (F1, r, _) =>
          match r with
          | SFuel => drive bp k fuel' F1 L n
          | SEcall =>
              match drive_sys F1 L n with
              | Some (DOne F2 L2 n2) => drive bp k fuel' F2 L2 n2
              | Some (DTwo F2 L2 n2 F3 L3 n3) =>
                  DFork (drive bp k fuel' F2 L2 n2) (drive bp k fuel' F3 L3 n3)
              | None => DLeaf F1 L n SEcall
              end
          | SStuck _ =>
              match ask_split F1 n with
              | Some (Fa, Fb) => DFork (drive bp k fuel' Fa L n) (drive bp k fuel' Fb L n)
              | None => DLeaf F1 L n r
              end
          | SBreak => DLeaf F1 L n r
          end
      end
  end.

(* [comment removed for export] *)
Definition ask_b5_slot (s : slot) : option (int * int) :=
  match s with
  | SV (FV t (W64 top off)) j =>
      if (j =? 5) && (t <? kind_lim) && ((top land 1) =? 0) && (off <? 1099511627776)
      then Some (t, (((1099511627776 - off) + 4095) >> 12) << 12)
      else None
  | _ => None
  end.
Definition ask_b5_val (v : fval) : option (int * int) :=
  match v with
  | FV t (W64 top off) =>
      if (vkind t =? 5) && ((top land 1) =? 0) && (off <? 1099511627776)
      then Some (vbase t, (((1099511627776 - off) + 4095) >> 12) << 12)
      else None
  end.
Definition xask_b5 (F : fstate) : option (int * int) :=
  match iget (f_pc F) code with
  | Some (FLoad _ _ _ rs1 imm) =>
      match fv_alu (f_mem F) ALU_ADD (rget F rs1) (FV 0 imm) with
      | Some (FV t (W64 _ off)) =>
          match iget t (f_mem F) with
          | Some rg =>
              match page_at IM rg t (off >> 12) with
              | Some p => ask_b5_slot (sget (off land 7) (slots_at IM p (off >> 12) ((off land 4095) >> 3)))
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | Some (FBranch _ rs1 rs2 _ _) =>
      match ask_b5_val (rget F rs1) with
      | Some a => Some a
      | None => ask_b5_val (rget F rs2)
      end
  | _ => None
  end.

End DriveDefs.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition same_but_vm (m m' : Model) : Prop :=
  m_fd m' = m_fd m /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m
  /\ m_lim m' = m_lim m /\ m_time m' = m_time m.

Lemma same_but_vm_refl m : same_but_vm m m.
Proof. repeat split; reflexivity. Qed.

Lemma same_but_vm_trans m1 m2 m3 : same_but_vm m1 m2 -> same_but_vm m2 m3 -> same_but_vm m1 m3.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6).
  repeat split; congruence.
Qed.

(* [comment removed for export] *)
Lemma same_but_vm_creds m m' : same_but_vm m m' -> m_creds m' = m_creds m.
Proof. intros (_ & _ & _ & H & _). unfold m_creds. rewrite H. reflexivity. Qed.
Lemma same_but_vm_fds m m' : same_but_vm m m' -> m_fds m' = m_fds m.
Proof. intros (H & _). unfold m_fds. rewrite H. reflexivity. Qed.
Lemma same_but_vm_fs m m' : same_but_vm m m' -> m_fs m' = m_fs m.
Proof. intros (_ & _ & H & _). unfold m_fs. rewrite H. reflexivity. Qed.
Lemma same_but_vm_tid m m' : same_but_vm m m' -> m_tid m' = m_tid m.
Proof. intros (_ & _ & _ & H & _). unfold m_tid. rewrite H. reflexivity. Qed.
Lemma same_but_vm_halted m m' : same_but_vm m m' -> m_halted m' = m_halted m.
Proof. intros (_ & _ & _ & H & _). unfold m_halted. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma XI_vm_of_creds (XI : (int -> word) -> Model -> Prop) :
  (forall rho m m', m_creds m' = m_creds m -> XI rho m -> XI rho m') ->
  forall rho m m', same_but_vm m m' -> XI rho m -> XI rho m'.
Proof. intros H rho m m' Hs. apply H. apply same_but_vm_creds. exact Hs. Qed.

(* [comment removed for export] *)
Definition XI_frame (m0 : Model) : (int -> word) -> Model -> Prop := fun _ m => same_but_vm m0 m.
Lemma XI_frame_init m0 rho : XI_frame m0 rho m0.
Proof. apply same_but_vm_refl. Qed.
Lemma XI_frame_rho m0 (xtags : list int) : forall rho rho' m,
  (forall t, In t xtags -> rho' t = rho t) -> XI_frame m0 rho m -> XI_frame m0 rho' m.
Proof. intros rho rho' m _ H. exact H. Qed.
Lemma XI_frame_vm m0 : forall rho m m', same_but_vm m m' -> XI_frame m0 rho m -> XI_frame m0 rho m'.
Proof. intros rho m m' H1 H2. exact (same_but_vm_trans _ _ _ H2 H1). Qed.

Definition XI_and (X1 X2 : (int -> word) -> Model -> Prop) : (int -> word) -> Model -> Prop :=
  fun rho m => X1 rho m /\ X2 rho m.
Lemma XI_and_rho X1 X2 (xt1 xt2 : list int) :
  (forall rho rho' m, (forall t, In t xt1 -> rho' t = rho t) -> X1 rho m -> X1 rho' m) ->
  (forall rho rho' m, (forall t, In t xt2 -> rho' t = rho t) -> X2 rho m -> X2 rho' m) ->
  forall rho rho' m, (forall t, In t (xt1 ++ xt2) -> rho' t = rho t) -> XI_and X1 X2 rho m -> XI_and X1 X2 rho' m.
Proof.
  intros H1 H2 rho rho' m Hag [A B]. split.
  - apply (H1 rho rho' m); [|exact A]. intros t Ht. apply Hag. apply in_or_app. left. exact Ht.
  - apply (H2 rho rho' m); [|exact B]. intros t Ht. apply Hag. apply in_or_app. right. exact Ht.
Qed.
Lemma XI_and_vm X1 X2 :
  (forall rho m m', same_but_vm m m' -> X1 rho m -> X1 rho m') ->
  (forall rho m m', same_but_vm m m' -> X2 rho m -> X2 rho m') ->
  forall rho m m', same_but_vm m m' -> XI_and X1 X2 rho m -> XI_and X1 X2 rho m'.
Proof. intros H1 H2 rho m m' Hs [A B]. split; [exact (H1 _ _ _ Hs A) | exact (H2 _ _ _ Hs B)]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Drive.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.
Hypothesis Halloc : sc_alloc cfg = false.
(* [comment removed for export] *)
Variable R0 : list (word * word).
Variable Rb Rc Lim : Z.
Hypothesis HRb : live_bytes R0 <= Rb.
Hypothesis HRc : Z.of_nat (length R0) <= Rc.
Variable rl : role.
(* [comment removed for export] *)
Variable keep : list int.
Variable mem0 : word -> option byte.
(* [comment removed for export] *)
Variable XI : (int -> word) -> Model -> Prop.
Variable xtags : list int.
Hypothesis XI_rho : forall rho rho' m, (forall t, In t xtags -> rho' t = rho t) -> XI rho m -> XI rho' m.
Hypothesis XI_vm : forall rho m m', same_but_vm m m' -> XI rho m -> XI rho m'.

Local Abbreviation Rn := (FxRn.Rn segs IM).

(* [comment removed for export] *)
Definition in_ival (rho : int -> word) (t : int) (rg : region) (x : Z) : Prop :=
  bv_unsigned (rho t) + to_Z (rg_lo rg) <= x < bv_unsigned (rho t) + to_Z (rg_len rg).

(* [comment removed for export] *)
Definition covered (V : VmMaps) (x : Z) : Prop :=
  (exists p, In p (vm_reserved V ++ vm_maps V) /\ e_lo p <= x < e_hi p) \/ alloc_top V <= x.

(* [comment removed for export] *)
Definition regions_covered (rho : int -> word) (M : itrie region) (V : VmMaps) : Prop :=
  forall t rg, iget t M = Some rg ->
    to_Z (rg_lo rg) < to_Z (rg_len rg) /\ forall x, in_ival rho t rg x -> covered V x.

Definition ent_ok (rho : int -> word) (M : itrie region) (l : list (word * word)) (e : fent) : Prop :=
  let '(t, off, len) := e in
  exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= to_Z off
             /\ to_Z off + to_Z len <= to_Z (rg_len rg)
             /\ In (adr rho t (to_Z off), Z_to_bv 64 (to_Z len)) l.

Definition mirror (rho : int -> word) (L : fledger) (M : itrie region) (V : VmMaps) : Prop :=
  Forall (ent_ok rho M (vm_maps V)) (fl_maps L)
  /\ Forall (ent_ok rho M (vm_noaccess V)) (fl_na L)
  /\ exists rgb, iget (fl_brk L) M = Some rgb /\ adr rho (fl_brk L) (to_Z (rg_len rgb)) = vm_brk V.

(* [comment removed for export] *)
Definition den (rho : int -> word) (e : fent) : word * word :=
  let '(t, off, len) := e in (adr rho t (to_Z off), Z_to_bv 64 (to_Z len)).

Definition exact (rho : int -> word) (L : fledger) (V : VmMaps) : Prop :=
  vm_maps V = map (den rho) (fl_maps L) /\ vm_noaccess V = map (den rho) (fl_na L).

(* [comment removed for export] *)
Definition ent_in (M : itrie region) (e : fent) : Prop :=
  let '(t, off, len) := e in
  exists rg, iget t M = Some rg /\ to_Z (rg_lo rg) <= to_Z off
             /\ to_Z off + to_Z len <= to_Z (rg_len rg).

(* [comment removed for export] *)
Definition pristine (M : itrie region) (t : int) : Prop :=
  t <> 0%uint63 /\ exists rg, iget t M = Some rg /\ rg_dflt rg = None
                              /\ forall pn, iget pn (rg_pages rg) = None.

Definition frame_ok (rho : int -> word) (M : itrie region) (mem : word -> option byte) : Prop :=
  forall t, In t keep ->
    pristine M t /\
    forall rg x, iget t M = Some rg -> in_ival rho t rg (bv_unsigned x) -> mem x = mem0 x.

Definition budget (ms : machine_state) (m : Model) : Prop :=
  match rl with RSrc => within_budget_cfg cfg segs (mkCfg ms m) | RTgt => True end.

Definition DInv (n : int) (rho : int -> word) (F : fstate) (L : fledger)
    (ms : machine_state) (m : Model) : Prop :=
  Rn n rho F ms
  /\ rho 0%uint63 = Z_to_bv 64 0
  /\ m_halted m = None /\ model_nolazy m
  /\ ledger_inv R0 Lim (fl_c L) (fl_S L) (m_vmmaps m)
  /\ regions_covered rho (f_mem F) (m_vmmaps m)
  /\ mirror rho L (f_mem F) (m_vmmaps m)
  /\ budget ms m
  /\ XI rho m
  /\ (forall t, In t xtags -> to_Z t < to_Z n)
  /\ frame_ok rho (f_mem F) (ms_mem ms).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma Rn_R n rho F ms : Rn n rho F ms -> rho 0%uint63 = Z_to_bv 64 0 -> R segs IM rho F ms.
Proof. intros H H0. apply H. apply agree_refl. exact H0. Qed.

Lemma u64 (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. apply u64_range. Qed.

Lemma adr_0 rho t : adr rho t 0 = rho t.
Proof.
  unfold adr. apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma region_ok_nowrap rho t rg :
  region_ok rho t rg -> bv_unsigned (rho t) + to_Z (rg_len rg) < 2 ^ 63.
Proof. intros (_ & _ & H & _). exact H. Qed.

(* [comment removed for export] *)
Lemma R_region_ok rho F ms t rg :
  R segs IM rho F ms -> iget t (f_mem F) = Some rg -> region_ok rho t rg.
Proof. intros HR Hg. exact (proj1 (proj1 (R_mem _ _ _ _ _ HR) t rg Hg)). Qed.

Lemma R_regions_sep rho F ms : R segs IM rho F ms -> regions_sep rho (f_mem F).
Proof. intros HR. exact (proj2 (R_mem _ _ _ _ _ HR)). Qed.

(* [comment removed for export] *)
Lemma ival_disjoint rho M t t' rg rg' x :
  regions_sep rho M -> t <> t' -> iget t M = Some rg -> iget t' M = Some rg' ->
  in_ival rho t rg x -> in_ival rho t' rg' x -> False.
Proof.
  intros Hsep Hne Hg Hg' [H1 H2] [H3 H4]. destruct (Hsep t t' rg rg' Hne Hg Hg'); lia.
Qed.

(* [comment removed for export] *)
Lemma sep_from_free rho M V a nZ :
  regions_covered rho M V ->
  0 < nZ < 2 ^ 64 ->
  bv_unsigned a + nZ <= alloc_top V ->
  region_free (vm_reserved V ++ vm_maps V) a (Z_to_bv 64 nZ) = true ->
  sep_from rho M (bv_unsigned a) (bv_unsigned a + nZ).
Proof.
  intros Hcov HnZ Htop Hfree t rg Hg. unfold rg_ival. cbn [fst snd].
  destruct (Hcov t rg Hg) as [Hne Hbytes].
  set (lo := bv_unsigned (rho t) + to_Z (rg_lo rg)) in *.
  set (hi := bv_unsigned (rho t) + to_Z (rg_len rg)) in *.
  destruct (Z_le_gt_dec (bv_unsigned a + nZ) lo) as [|H1]; [left; assumption|].
  destruct (Z_le_gt_dec hi (bv_unsigned a)) as [|H2]; [right; assumption|].
  exfalso.
  assert (Hx : in_ival rho t rg (Z.max lo (bv_unsigned a))).
  { unfold in_ival. fold lo hi. unfold lo, hi in *. lia. }
  destruct (Hbytes _ Hx) as [(p & Hp & Hpx) | Hat].
  - pose proof (region_free_In_disj _ _ _ _ Hfree Hp) as Hd.
    unfold e_disj, e_hi, e_lo, e_sz in Hd. cbn [fst snd] in Hd.
    rewrite u64_lit in Hd by lia. unfold e_hi, e_lo, e_sz in Hpx. lia.
  - lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma R_reg_get rho F ms (r : reg) :
  R segs IM rho F ms -> is_x0 r = false ->
  reg_get (ms_regs ms) r = dv rho (FxState.rget F (ireg r)).
Proof.
  intros HR Hx. rewrite <- (R_regs _ _ _ _ _ HR r). unfold Sem.rget. rewrite Hx. reflexivity.
Qed.

Lemma pend_x8 rho F ms :
  R segs IM rho F ms -> ms_reg ms 17 = dv rho (FxState.rget F 17%uint63).
Proof. intros HR. exact (R_reg_get rho F ms 17%bv HR eq_refl). Qed.

Lemma pend_gpr0 rho F ms : R segs IM rho F ms -> ms_gpr (ms_pend ms) 0 = dv rho (FxState.rget F 10%uint63).
Proof. intros HR. exact (R_reg_get rho F ms 10%bv HR eq_refl). Qed.
Lemma pend_gpr1 rho F ms : R segs IM rho F ms -> ms_gpr (ms_pend ms) 1 = dv rho (FxState.rget F 11%uint63).
Proof. intros HR. exact (R_reg_get rho F ms 11%bv HR eq_refl). Qed.
Lemma pend_gpr2 rho F ms : R segs IM rho F ms -> ms_gpr (ms_pend ms) 2 = dv rho (FxState.rget F 12%uint63).
Proof. intros HR. exact (R_reg_get rho F ms 12%bv HR eq_refl). Qed.
Lemma pend_gpr3 rho F ms : R segs IM rho F ms -> ms_gpr (ms_pend ms) 3 = dv rho (FxState.rget F 13%uint63).
Proof. intros HR. exact (R_reg_get rho F ms 13%bv HR eq_refl). Qed.
Lemma pend_gpr5 rho F ms : R segs IM rho F ms -> ms_gpr (ms_pend ms) 5 = dv rho (FxState.rget F 15%uint63).
Proof. intros HR. exact (R_reg_get rho F ms 15%bv HR eq_refl). Qed.

Lemma conc_sound rho v lo :
  rho 0%uint63 = Z_to_bv 64 0 -> conc v = Some lo ->
  dv rho v = Z_to_bv 64 (to_Z lo) /\ bv_unsigned (dv rho v) = to_Z lo.
Proof.
  intros H0 H. destruct v as [t [top l]]. cbn [conc] in H.
  destruct (t =? 0)%uint63 eqn:Et; [|discriminate].
  destruct ((top land 1) =? 0)%uint63 eqn:Etop; [|discriminate].
  cbn [andb] in H. injection H as <-.
  apply Uint63.eqb_spec in Et. subst t.
  apply Uint63.eqb_spec in Etop. apply (f_equal to_Z) in Etop. rewrite i63_land1, to_Z_0 in Etop.
  rewrite (dv_conc rho H0). unfold wbv. rewrite (wZ_even_top top l Etop).
  split; [reflexivity|]. apply u64_lit. pose proof (i63_range l). lia.
Qed.

Lemma ptr_sound rho v t off :
  ptr v = Some (t, off) -> dv rho v = adr rho t (to_Z off).
Proof.
  intros H. destruct v as [t' [top l]]. cbn [ptr] in H.
  destruct ((top land 1) =? 0)%uint63 eqn:Etop; [|discriminate].
  destruct (is_plain t') eqn:Epl; [|discriminate]. cbn [andb] in H. injection H as <- <-.
  apply Uint63.eqb_spec in Etop. apply (f_equal to_Z) in Etop. rewrite i63_land1, to_Z_0 in Etop.
  unfold is_plain in Epl. apply ltb_spec in Epl. change (to_Z kind_lim) with (2 ^ 60) in Epl.
  apply (dv_adr rho t' top l Epl Etop).
Qed.

Lemma pg_up_spec len :
  to_Z len <= 2 ^ 62 -> to_Z (pg_up len) = page_round_up_Z (to_Z len).
Proof.
  intros H. pose proof (i63_range len) as Hl. unfold pg_up, page_round_up_Z, page_size.
  rewrite lsl_spec, lsr_spec, add_spec, i63_wB.
  change (to_Z 4095) with 4095. change (2 ^ to_Z 12) with 4096.
  rewrite (Z.mod_small (to_Z len + 4095)) by lia.
  replace (to_Z len + 4096 - 1) with (to_Z len + 4095) by lia.
  apply Z.mod_small. Z.div_mod_to_equations. lia.
Qed.

Lemma fent_eqb_eq e1 e2 : fent_eqb e1 e2 = true -> e1 = e2.
Proof.
  destruct e1 as [[t1 o1] l1], e2 as [[t2 o2] l2]. cbn [fent_eqb]. intros H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Uint63.eqb_spec in H1, H2, H3. subst. reflexivity.
Qed.

Lemma mem_fent_In e l : mem_fent e l = true -> In e l.
Proof.
  unfold mem_fent. intros H. apply existsb_exists in H as (x & Hx & He).
  apply fent_eqb_eq in He. subst x. exact Hx.
Qed.

Lemma mem_int_false t l : mem_int t l = false -> ~ In t l.
Proof.
  unfold mem_int. intros H Hin.
  assert (existsb (fun x => (x =? t)%uint63) l = true).
  { apply existsb_exists. exists t. split; [exact Hin | apply Uint63.eqb_refl]. }
  congruence.
Qed.

Lemma drop_tag_In t e l : In e (drop_tag t l) -> In e l /\ fent_tag e <> t.
Proof.
  unfold drop_tag. intros H. apply filter_In in H as [H1 H2]. split; [exact H1|].
  apply negb_true_iff in H2. apply eqb_false_spec in H2. exact H2.
Qed.

Lemma ecall_here_at F : ecall_here code F = true -> at_ecall F.
Proof.
  unfold ecall_here, at_ecall. intros H.
  destruct (iget (f_pc F) code) as [fi|] eqn:Hi; [|discriminate].
  pose proof (Hcode _ _ Hi) as Hb. unfold build_entry in Hb.
  destruct ((to_Z (f_pc F) <? pc_bound - 4) && (0 <=? to_Z (f_pc F))) eqn:Hrng; [|discriminate].
  apply andb_true_iff in Hrng as [Hlt _]. apply Z.ltb_lt in Hlt. exact Hlt.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition same_shape (M M' : itrie region) : Prop :=
  forall t, match iget t M, iget t M' with
            | Some rg, Some rg' =>
                rg_lo rg' = rg_lo rg /\ rg_len rg' = rg_len rg /\ rg_align rg' = rg_align rg
                /\ rg_dflt rg' = rg_dflt rg
            | None, None => True
            | _, _ => False
            end.

Lemma same_shape_refl M : same_shape M M.
Proof. intros t. destruct (iget t M); [repeat split; reflexivity | exact I]. Qed.

Lemma same_shape_trans M1 M2 M3 : same_shape M1 M2 -> same_shape M2 M3 -> same_shape M1 M3.
Proof.
  intros H12 H23 t. specialize (H12 t). specialize (H23 t).
  destruct (iget t M1), (iget t M2), (iget t M3); try contradiction; try exact I.
  destruct H12 as (A1 & A2 & A3 & A4), H23 as (B1 & B2 & B3 & B4).
  repeat split; congruence.
Qed.

Lemma fx_step_shape F F' : fx_step IM code F = FNext F' -> same_shape (f_mem F) (f_mem F').
Proof.
  intros H. destruct (fx_step_mem IM code F F' H) as [E | (a & sz & v & Hst)].
  - rewrite E. apply same_shape_refl.
  - intros t. exact (fm_store_regions' IM _ _ _ _ _ t Hst).
Qed.

Lemma fx_run_shape : forall bp k F F' r cnt,
  fx_run IM code bp k F = (F', r, cnt) -> same_shape (f_mem F) (f_mem F').
Proof.
  intros bp k. induction k as [|k IH]; intros F F' r cnt H; cbn [fx_run] in H.
  - destruct (f_pc F =? bp)%uint63; [injection H as <- _ _; apply same_shape_refl|].
    destruct (fx_step IM code F) as [s'| |c] eqn:Es; injection H as <- _ _;
      [exact (fx_step_shape _ _ Es) | apply same_shape_refl | apply same_shape_refl].
  - destruct (fx_run IM code bp k F) as [[s1 r1] n1] eqn:E1.
    destruct (stop_is_fuel r1).
    + destruct (fx_run IM code bp k s1) as [[s2 r2] n2] eqn:E2. injection H as <- _ _.
      exact (same_shape_trans _ _ _ (IH _ _ _ _ E1) (IH _ _ _ _ E2)).
    + injection H as <- _ _. exact (IH _ _ _ _ E1).
Qed.

Lemma same_shape_get M M' t rg' :
  same_shape M M' -> iget t M' = Some rg' ->
  exists rg, iget t M = Some rg /\ rg_lo rg' = rg_lo rg /\ rg_len rg' = rg_len rg.
Proof.
  intros Hs Hg. specialize (Hs t). rewrite Hg in Hs.
  destruct (iget t M) as [rg|]; [|contradiction]. exists rg. destruct Hs as (A & B & _).
  split; [reflexivity | split; assumption].
Qed.

Lemma same_shape_get' M M' t rg :
  same_shape M M' -> iget t M = Some rg ->
  exists rg', iget t M' = Some rg' /\ rg_lo rg' = rg_lo rg /\ rg_len rg' = rg_len rg.
Proof.
  intros Hs Hg. specialize (Hs t). rewrite Hg in Hs.
  destruct (iget t M') as [rg'|]; [|contradiction]. exists rg'. destruct Hs as (A & B & _).
  split; [reflexivity | split; assumption].
Qed.

Lemma in_ival_shape rho t rg rg' x :
  rg_lo rg' = rg_lo rg -> rg_len rg' = rg_len rg -> in_ival rho t rg' x -> in_ival rho t rg x.
Proof. unfold in_ival. intros -> ->. trivial. Qed.

Lemma regions_covered_shape rho M M' V :
  same_shape M M' -> regions_covered rho M V -> regions_covered rho M' V.
Proof.
  intros Hs Hc t rg' Hg. destruct (same_shape_get _ _ _ _ Hs Hg) as (rg & Hg0 & E1 & E2).
  destruct (Hc t rg Hg0) as [Hne Hb]. split; [rewrite E1, E2; exact Hne|].
  intros x Hx. apply Hb. exact (in_ival_shape _ _ _ _ _ E1 E2 Hx).
Qed.

Lemma ent_ok_shape rho M M' l e : same_shape M M' -> ent_ok rho M l e -> ent_ok rho M' l e.
Proof.
  intros Hs. destruct e as [[t off] len]. intros (rg & Hg & H1 & H2 & H3).
  destruct (same_shape_get' _ _ _ _ Hs Hg) as (rg' & Hg' & E1 & E2).
  exists rg'. rewrite E1, E2. repeat split; assumption.
Qed.

Lemma mirror_shape rho L M M' V : same_shape M M' -> mirror rho L M V -> mirror rho L M' V.
Proof.
  intros Hs (H1 & H2 & rgb & Hb & Hbrk). split; [|split].
  - eapply Forall_impl; [|exact H1]. intros e. apply ent_ok_shape. exact Hs.
  - eapply Forall_impl; [|exact H2]. intros e. apply ent_ok_shape. exact Hs.
  - destruct (same_shape_get' _ _ _ _ Hs Hb) as (rg' & Hg' & E1 & E2).
    exists rg'. split; [exact Hg'|]. rewrite E2. exact Hbrk.
Qed.

(* [comment removed for export] *)
Lemma pristine_no_page M t rg pn :
  pristine M t -> iget t M = Some rg -> page_at IM rg t pn = None.
Proof.
  intros (Hne & rg0 & Hg0 & Hd & Hp) Hg. rewrite Hg in Hg0. injection Hg0 as <-.
  unfold page_at. rewrite Hp, Hd.
  destruct (t =? 0)%uint63 eqn:E; [apply Uint63.eqb_spec in E; contradiction | reflexivity].
Qed.

Lemma pristine_store M a sz v M' t :
  fm_store IM M a sz v = Some M' -> pristine M t -> iget t M' = iget t M.
Proof.
  destruct a as [ta [top off]]. intros Hst Hpr.
  destruct (fm_store_inv IM _ _ _ _ _ _ _ Hst) as (rg & p & Hrg & Hp & _ & _ & _ & _ & ->).
  destruct (Uint63.eqb t ta) eqn:E.
  - apply Uint63.eqb_spec in E. subst ta.
    rewrite (pristine_no_page M t rg _ Hpr Hrg) in Hp. discriminate.
  - apply iget_iset_other. intros ->. rewrite Uint63.eqb_refl in E. discriminate.
Qed.

Lemma pristine_step F F' t :
  fx_step IM code F = FNext F' -> pristine (f_mem F) t -> iget t (f_mem F') = iget t (f_mem F).
Proof.
  intros H Hpr. destruct (fx_step_mem IM code F F' H) as [E | (a & sz & v & Hst)].
  - rewrite E. reflexivity.
  - exact (pristine_store _ _ _ _ _ _ Hst Hpr).
Qed.

Lemma pristine_eq M M' t : iget t M' = iget t M -> pristine M t -> pristine M' t.
Proof. intros E (Hne & rg & Hg & H). split; [exact Hne|]. exists rg. rewrite E. split; assumption. Qed.

Lemma pristine_run : forall bp k F F' r cnt t,
  fx_run IM code bp k F = (F', r, cnt) -> pristine (f_mem F) t ->
  iget t (f_mem F') = iget t (f_mem F).
Proof.
  intros bp k. induction k as [|k IH]; intros F F' r cnt t H Hpr; cbn [fx_run] in H.
  - destruct (f_pc F =? bp)%uint63; [injection H as <- _ _; reflexivity|].
    destruct (fx_step IM code F) as [s'| |c] eqn:Es; injection H as <- _ _;
      [exact (pristine_step _ _ _ Es Hpr) | reflexivity | reflexivity].
  - destruct (fx_run IM code bp k F) as [[s1 r1] n1] eqn:E1.
    destruct (stop_is_fuel r1).
    + destruct (fx_run IM code bp k s1) as [[s2 r2] n2] eqn:E2. injection H as <- _ _.
      pose proof (IH _ _ _ _ t E1 Hpr) as H1.
      rewrite (IH _ _ _ _ t E2 (pristine_eq _ _ _ H1 Hpr)). exact H1.
    + injection H as <- _ _. exact (IH _ _ _ _ t E1 Hpr).
Qed.

(* [comment removed for export] *)
Lemma pristine_unclaimed rho F ms t rg x :
  R segs IM rho F ms -> pristine (f_mem F) t -> iget t (f_mem F) = Some rg ->
  in_ival rho t rg (bv_unsigned x) -> ~ claimed_wr IM rho (f_mem F) x.
Proof.
  intros HR Hpr Hg Hx (t1 & rg1 & pn & p & j & Hg1 & Hpn & Hp & Hw & Hj & Hhi & ->).
  destruct (Uint63.eqb t1 t) eqn:E.
  - apply Uint63.eqb_spec in E. subst t1. rewrite Hg in Hg1. injection Hg1 as <-.
    rewrite (pristine_no_page _ _ _ _ Hpr Hg) in Hp. discriminate.
  - assert (Hne : t1 <> t) by (intros ->; rewrite Uint63.eqb_refl in E; discriminate).
    destruct (proj1 (R_mem _ _ _ _ _ HR) t1 rg1 Hg1) as [Hreg Hpages].
    destruct (Hpages pn p Hpn Hp) as (_ & Hlo & _).
    pose proof (region_ok_nowrap _ _ _ Hreg) as Hnw.
    pose proof (i63_range pn) as Hpn0. pose proof (i63_range (rg_lo rg1)) as Hl0.
    rewrite adr_unsigned in Hx by lia.
    apply (ival_disjoint rho (f_mem F) t1 t rg1 rg (bv_unsigned (rho t1) + (to_Z pn * 4096 + j))
             (R_regions_sep _ _ _ HR) Hne Hg1 Hg); [|exact Hx].
    unfold in_ival. lia.
Qed.

Lemma DInv_run n rho F L ms m bp k F1 r cnt :
  (k <= 61)%nat ->
  fx_run IM code bp k F = (F1, r, cnt) ->
  DInv n rho F L ms m ->
  exists ms1, rsteps segs (nat_of_int cnt) ms = MachineOk ms1
    /\ DInv n rho F1 L ms1 m
    /\ (r = SEcall -> RiscvSemantics.step segs ms1 = MachineOk (ms_pend ms1)).
Proof.
  intros Hk Hrun (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfr).
  destruct (fx_run_Rn segs IM code Hcode n rho bp k F F1 r cnt ms Hk Hrun H0 HRn)
    as (ms1 & Hsteps & HRn1 & Hec & Hframe & _ & _).
  pose proof (fx_run_shape _ _ _ _ _ _ Hrun) as Hshape.
  exists ms1. split; [exact Hsteps|]. split; [|exact Hec].
  split; [exact HRn1|]. split; [exact H0|]. split; [exact Hh|]. split; [exact Hnl|].
  split; [exact Hli|]. split; [exact (regions_covered_shape _ _ _ _ Hshape Hcov)|].
  split; [exact (mirror_shape _ _ _ _ _ Hshape Hmir)|]. split.
  - unfold budget in *. destruct rl; [|exact I].
    eapply within_budget_cfg_star; [exact Hbud|].
    exact (rsteps_star_cfg cfg segs _ ms m ms1 Hh (proj1 Hnl) Hsteps).
  - split; [exact HXI|]. split; [exact Hxt|].
    intros t Ht. destruct (Hfr t Ht) as [Hpr Hmem].
    pose proof (pristine_run _ _ _ _ _ _ t Hrun Hpr) as Eg.
    split; [exact (pristine_eq _ _ _ Eg Hpr)|].
    intros rg x Hg Hx. rewrite Eg in Hg.
    rewrite Hframe; [exact (Hmem rg x Hg Hx)|].
    exact (pristine_unclaimed rho F ms t rg x (Rn_R _ _ _ _ HRn H0) Hpr Hg Hx).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ent_ok_den rho M l e : ent_ok rho M l e -> In (den rho e) l.
Proof. destruct e as [[t off] len]. intros (rg & _ & _ & _ & H). exact H. Qed.

Lemma ent_ok_tag rho M l e : ent_ok rho M l e -> exists rg, iget (fent_tag e) M = Some rg.
Proof. destruct e as [[t off] len]. intros (rg & Hrg & _). exists rg. exact Hrg. Qed.

Lemma map_den_ext rho rho' (l : list fent) :
  (forall e, In e l -> rho' (fent_tag e) = rho (fent_tag e)) ->
  map (den rho') l = map (den rho) l.
Proof.
  intros H. apply map_ext_in. intros [[t off] len] He. cbn [den].
  pose proof (H _ He) as E. cbn [fent_tag fst] in E. unfold adr. rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma map_den_regions rho rho' (M : itrie region) l fl :
  (forall t rg, iget t M = Some rg -> rho' t = rho t) ->
  Forall (ent_ok rho M l) fl -> map (den rho') fl = map (den rho) fl.
Proof.
  intros Hreg Hfl. apply map_den_ext. intros e He.
  destruct (ent_ok_tag _ _ _ _ (proj1 (Forall_forall _ _) Hfl e He)) as [rg Hrg].
  exact (Hreg _ _ Hrg).
Qed.

(* [comment removed for export] *)
Lemma map_den_fl_sub rho t off sz (l : list fent) lo hi :
  (forall e, In e l -> map (den rho) (ent_sub t off sz e)
                       = iv_subtract (fst (den rho e)) (snd (den rho e)) lo hi) ->
  map (den rho) (fl_sub t off sz l) = maps_subtract (map (den rho) l) lo hi.
Proof.
  unfold fl_sub. induction l as [|e l IH]; intros H; [reflexivity|].
  cbn [flat_map map]. rewrite map_app, (H e (or_introl eq_refl)), IH.
  - destruct (den rho e) as [a s]. reflexivity.
  - intros e' He'. apply H. right. exact He'.
Qed.

Lemma map_den_drop_tag_sub rho t (l : list fent) lo hi :
  (forall e, In e l -> iv_subtract (fst (den rho e)) (snd (den rho e)) lo hi
                       = if (fent_tag e =? t)%uint63 then [] else [den rho e]) ->
  map (den rho) (drop_tag t l) = maps_subtract (map (den rho) l) lo hi.
Proof.
  unfold drop_tag. induction l as [|e l IH]; intros H; [reflexivity|].
  cbn [List.filter map]. pose proof (H e (or_introl eq_refl)) as He.
  assert (IH' := IH (fun e' He' => H e' (or_intror He'))).
  destruct (den rho e) as [a s] eqn:Ed. cbn [maps_subtract]. cbn [fst snd] in He. rewrite He.
  destruct (fent_tag e =? t)%uint63; cbn [negb app map]; rewrite ?Ed, IH'; reflexivity.
Qed.

Lemma map_den_drop_tag_remove rho t (l : list fent) (a : word) :
  (forall e, In e l -> bv_eqb (fst (den rho e)) a = (fent_tag e =? t)%uint63) ->
  map (den rho) (drop_tag t l) = map_remove (map (den rho) l) a.
Proof.
  unfold drop_tag, map_remove. induction l as [|e l IH]; intros H; [reflexivity|].
  cbn [List.filter map]. rewrite (H e (or_introl eq_refl)).
  assert (IH' := IH (fun e' He' => H e' (or_intror He'))).
  destruct (fent_tag e =? t)%uint63; cbn [negb map]; rewrite IH'; reflexivity.
Qed.

Lemma ent_ok_iff rho M l e : ent_ok rho M l e <-> ent_in M e /\ In (den rho e) l.
Proof.
  destruct e as [[t off] len]. cbn [ent_ok ent_in den]. split.
  - intros (rg & H1 & H2 & H3 & H4). split; [exists rg; repeat split; assumption | exact H4].
  - intros [(rg & H1 & H2 & H3) H4]. exists rg. repeat split; assumption.
Qed.

Lemma ent_in_shape M M' e : same_shape M M' -> ent_in M e -> ent_in M' e.
Proof.
  destruct e as [[t off] len]. intros Hs (rg & Hg & H1 & H2).
  destruct (same_shape_get' _ _ _ _ Hs Hg) as (rg' & Hg' & E1 & E2).
  exists rg'. rewrite E1, E2. repeat split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition dres_in (x : fstate * fledger * int) (res : dres) : Prop :=
  match res with
  | DOne F L n => x = (F, L, n)
  | DTwo F1 L1 n1 F2 L2 n2 => x = (F1, L1, n1) \/ x = (F2, L2, n2)
  end.

(* [comment removed for export] *)
Definition sys_ok (res : dres) (ms : machine_state) (m : Model) : Prop :=
  exists (I : Type) (i0 : I) (nx : I -> config),
    (forall e st, sstep_cfg segs cfg (mkCfg (ms_pend ms) m) e st <->
                  exists i, e = [] /\ st = SNext (nx i))
    /\ forall i, exists F' L' n' rho' ms' m' k,
         dres_in (F', L', n') res
         /\ rsteps segs k (cfg_ms (nx i)) = MachineOk ms' /\ cfg_model (nx i) = m'
         /\ DInv n' rho' F' L' ms' m'.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition no_region (rho : int -> word) (M : itrie region) (x : Z) : Prop :=
  forall t rg, iget t M = Some rg -> ~ in_ival rho t rg x.

(* [comment removed for export] *)
Record node_ext (n : int) (rho : int -> word) (F : fstate) (L : fledger) (ms : machine_state) (m : Model)
                (n' : int) (rho' : int -> word) (F' : fstate) (L' : fledger) (ms' : machine_state) (m' : Model)
  : Prop := mk_node_ext {
  ne_n     : to_Z n <= to_Z n';
  ne_rho   : forall t, to_Z t < to_Z n -> rho' t = rho t;
  ne_fregs : ms_fregs ms' = ms_fregs ms;
  ne_fcsr  : ms_fcsr ms' = ms_fcsr ms;
  ne_rom   : ms_rom ms' = ms_rom ms;
  ne_vm    : same_but_vm m m';
  ne_sp    : vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m);
  ne_high  : forall x, alloc_top (m_vmmaps m) <= bv_unsigned x -> no_region rho (f_mem F) (bv_unsigned x) ->
               ms_mem ms' x = ms_mem ms x /\ no_region rho' (f_mem F') (bv_unsigned x);
  ne_sbrk  : vm_start_brk (m_vmmaps m') = vm_start_brk (m_vmmaps m);
  ne_mbase : vm_mmap_base (m_vmmaps m') = vm_mmap_base (m_vmmaps m);
  ne_exact : DInv n rho F L ms m -> exact rho L (m_vmmaps m) -> exact rho' L' (m_vmmaps m')
}.

(* [comment removed for export] *)
Definition sys_okX (n : int) (rho : int -> word) (F : fstate) (L : fledger)
                   (res : dres) (ms : machine_state) (m : Model) : Prop :=
  exists (I : Type) (i0 : I) (nx : I -> config),
    (forall e st, sstep_cfg segs cfg (mkCfg (ms_pend ms) m) e st <->
                  exists i, e = [] /\ st = SNext (nx i))
    /\ forall i, exists F' L' n' rho' ms' m' k,
         dres_in (F', L', n') res
         /\ rsteps segs k (cfg_ms (nx i)) = MachineOk ms' /\ cfg_model (nx i) = m'
         /\ DInv n' rho' F' L' ms' m'
         /\ node_ext n rho F L ms m n' rho' F' L' ms' m'.

Lemma sys_okX_ok n rho F L res ms m : sys_okX n rho F L res ms m -> sys_ok res ms m.
Proof.
  intros (I & i0 & nx & Hiff & Hsucc). exists I, i0, nx. split; [exact Hiff|].
  intros i. destruct (Hsucc i) as (F' & L' & n' & rho' & ms' & m' & k & H1 & H2 & H3 & H4 & _).
  exists F', L', n', rho', ms', m', k. split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.

(* [comment removed for export] *)
Lemma node_ext_same n rho F L ms m n' rho' F' ms' :
  to_Z n <= to_Z n' -> (forall t, to_Z t < to_Z n -> rho' t = rho t) ->
  (forall t rg, iget t (f_mem F) = Some rg -> rho' t = rho t) ->
  f_mem F' = f_mem F -> ms_mem ms' = ms_mem ms ->
  ms_fregs ms' = ms_fregs ms -> ms_fcsr ms' = ms_fcsr ms -> ms_rom ms' = ms_rom ms ->
  node_ext n rho F L ms m n' rho' F' L ms' m.
Proof.
  intros Hn Hrho Hreg HM Hmem Hfr Hfc Hrom. constructor; try assumption.
  - apply same_but_vm_refl.
  - reflexivity.
  - intros x _ Hno. split; [rewrite Hmem; reflexivity|].
    intros t rg Hg Hx. rewrite HM in Hg. apply (Hno t rg Hg).
    unfold in_ival in *. rewrite <- (Hreg t rg Hg). exact Hx.
  - reflexivity.
  - reflexivity.
  - (* [comment removed for export] *)
    intros (_ & _ & _ & _ & _ & _ & (Hm1 & Hm2 & _) & _) [E1 E2].
    split; [rewrite (map_den_regions rho rho' _ _ _ Hreg Hm1); exact E1
           | rewrite (map_den_regions rho rho' _ _ _ Hreg Hm2); exact E2].
Qed.

Lemma rsteps_pend ms :
  ms_svc_pending ms = None -> RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  rsteps segs 1 ms = MachineOk (ms_pend ms).
Proof. intros Hsvc Hs. cbn [rsteps]. rewrite Hsvc, Hs. reflexivity. Qed.

Lemma budget_pend ms m :
  budget ms m -> m_halted m = None -> model_nolazy m ->
  ms_svc_pending ms = None -> RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  budget (ms_pend ms) m.
Proof.
  unfold budget. destruct rl; [|trivial]. intros Hb Hh Hnl Hsvc Hs.
  eapply within_budget_cfg_star; [exact Hb|].
  exact (rsteps_star_cfg cfg segs 1 ms m (ms_pend ms) Hh (proj1 Hnl) (rsteps_pend ms Hsvc Hs)).
Qed.

Lemma budget_step ms m e ms' m' :
  budget ms m -> sstep_cfg segs cfg (mkCfg ms m) e (SNext (mkCfg ms' m')) -> budget ms' m'.
Proof.
  unfold budget. destruct rl; [|trivial]. intros Hb Hs.
  exact (within_budget_cfg_step cfg segs _ _ _ Hb Hs).
Qed.

Lemma f_mem_fx_sysret F r M' : f_mem (fx_sysret F r M') = M'.
Proof. reflexivity. Qed.

Lemma rho_upd_other rho n a t : t <> n -> rho_upd rho n a t = rho t.
Proof.
  intros Hne. unfold rho_upd. destruct (t =? n)%uint63 eqn:E; [|reflexivity].
  apply Uint63.eqb_spec in E. contradiction.
Qed.

Lemma rho_upd_same rho n a : rho_upd rho n a n = a.
Proof. unfold rho_upd. rewrite Uint63.eqb_refl. reflexivity. Qed.

Lemma lt_neq (t n : int) : to_Z t < to_Z n -> t <> n.
Proof. intros H ->. lia. Qed.

Lemma in_ival_rho rho rho' t rg x : rho' t = rho t -> in_ival rho' t rg x -> in_ival rho t rg x.
Proof. unfold in_ival. intros ->. trivial. Qed.

Lemma adr_rho rho rho' t z : rho' t = rho t -> adr rho' t z = adr rho t z.
Proof. unfold adr. intros ->. reflexivity. Qed.

Lemma covered_mono V V' x :
  vm_reserved V' = vm_reserved V -> vm_init_sp V' = vm_init_sp V ->
  (forall p, In p (vm_maps V) -> In p (vm_maps V')) ->
  covered V x -> covered V' x.
Proof.
  intros HR Hsp Hsub [(p & Hp & Hx) | Hat].
  - left. exists p. split; [|exact Hx]. rewrite HR. apply in_app_iff. apply in_app_iff in Hp.
    destruct Hp as [Hp|Hp]; [left; exact Hp | right; apply Hsub; exact Hp].
  - right. rewrite (alloc_top_same_sp V V' Hsp). exact Hat.
Qed.

(* [comment removed for export] *)
Lemma ent_ok_ext rho rho' M M' (l l' : list (word * word)) e :
  rho' (fent_tag e) = rho (fent_tag e) -> iget (fent_tag e) M' = iget (fent_tag e) M ->
  (forall p, In p l -> In p l') ->
  ent_ok rho M l e -> ent_ok rho' M' l' e.
Proof.
  destruct e as [[t off] len]. cbn [fent_tag fst]. intros Hr Hg Hsub (rg & Hrg & H1 & H2 & H3).
  exists rg. rewrite Hg. repeat split; try assumption.
  rewrite (adr_rho rho rho' t _ Hr). apply Hsub. exact H3.
Qed.

Lemma ms_pend_svc ms : ms_svc_pending (ms_pend ms) = Some (ms_reg ms 17).
Proof. reflexivity. Qed.

Lemma eqb_lit (x c : int) : (x =? c)%uint63 = true -> to_Z x = to_Z c.
Proof. intros H. apply Uint63.eqb_spec in H. subst. reflexivity. Qed.

Lemma rl_cases : rl = RSrc \/ rl = RTgt.
Proof. destruct rl; [left | right]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma regions_lt_b_ok n M : regions_lt_b n M = true -> regions_lt n M.
Proof.
  unfold regions_lt_b, regions_lt. intros H t rg Hg.
  pose proof (proj1 (iall_spec _ M) H t rg Hg) as Hlt. cbv beta in Hlt.
  apply ltb_spec in Hlt. exact Hlt.
Qed.

Lemma to_Z_succ61 (n : int) : to_Z n < 2 ^ 60 -> to_Z (n + 1)%uint63 = to_Z n + 1.
Proof.
  intros H. pose proof (i63_range n). rewrite add_spec, to_Z_1, i63_wB. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma regions_lt_rho rho n a M t rg :
  regions_lt n M -> iget t M = Some rg -> rho_upd rho n a t = rho t.
Proof. intros Hlt Hg. apply rho_upd_other. apply lt_neq. exact (Hlt t rg Hg). Qed.

Lemma sys_grant_succ n rho F L ms m len res a :
  sys_grant Rb Rc Lim rl F L n len = Some res ->
  DInv n rho F L ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 222 ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  bv_unsigned (ms_gpr (ms_pend ms) 2) = 3 ->
  bv_unsigned (ms_gpr (ms_pend ms) 3) = 34 ->
  bv_unsigned (ms_gpr (ms_pend ms) 5) = 0 ->
  mmap_grant_b m a (page_round_up_Z (to_Z len)) = true ->
  exists L',
    res = DOne (fx_grant F n (pg_up len)) L' (n + 1)%uint63
    /\ sstep_cfg segs cfg (mkCfg (ms_pend ms) m) []
         (SNext (mkCfg (sysret (ms_pend ms) a (apply_zeros (ms_mem (ms_pend ms))
                                                 [(a, Z_to_bv 64 (page_round_up_Z (to_Z len)))]))
                       (mmap_grant_model a (page_round_up_Z (to_Z len)) m)))
    /\ DInv (n + 1)%uint63 (rho_upd rho n a) (fx_grant F n (pg_up len)) L'
         (sysret (ms_pend ms) a (apply_zeros (ms_mem (ms_pend ms)) [(a, Z_to_bv 64 (page_round_up_Z (to_Z len)))]))
         (mmap_grant_model a (page_round_up_Z (to_Z len)) m)
    /\ node_ext n rho F L ms m (n + 1)%uint63 (rho_upd rho n a) (fx_grant F n (pg_up len)) L'
         (sysret (ms_pend ms) a (apply_zeros (ms_mem (ms_pend ms)) [(a, Z_to_bv 64 (page_round_up_Z (to_Z len)))]))
         (mmap_grant_model a (page_round_up_Z (to_Z len)) m).
Proof.
  intros Hsys (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfr) Hat Hstep Hx8 Ha1 Ha2 Ha3 Ha5 Ha.
  unfold sys_grant in Hsys. cbv zeta in Hsys.
  destruct ((0 <? len)%uint63 && (len <=? 4611686018427387904)%uint63
            && (pg_up len <=? 4611686018427387904)%uint63 && tag_ok F n
            && grant_fits Rb Rc Lim rl L (to_Z (pg_up len))) eqn:Hchk; [|discriminate].
  injection Hsys as <-.
  apply andb_true_iff in Hchk as [Hchk Hfit]. apply andb_true_iff in Hchk as [Hchk Htag].
  apply andb_true_iff in Hchk as [Hchk Hup]. apply andb_true_iff in Hchk as [Hpos Hle].
  apply ltb_spec in Hpos. apply leb_spec in Hle, Hup. rewrite to_Z_0 in Hpos.
  change (to_Z 4611686018427387904) with (2 ^ 62) in Hle, Hup.
  pose proof (pg_up_spec len Hle) as HnZ.
  set (nZi := pg_up len) in *. set (nZ := page_round_up_Z (to_Z len)) in *.
  assert (HnZpos : 0 < nZ) by (apply page_round_up_Z_pos; exact Hpos).
  assert (HnZmod : nZ mod 4096 = 0) by (apply page_round_up_Z_mod).
  unfold tag_ok in Htag. apply andb_true_iff in Htag as [Htag Hlt].
  apply andb_true_iff in Htag as [Hn0 Hn61]. apply ltb_spec in Hn0, Hn61. rewrite to_Z_0 in Hn0.
  change (to_Z 1152921504606846976) with (2 ^ 60) in Hn61.
  apply regions_lt_b_ok in Hlt.
  pose proof (Rn_R _ _ _ _ HRn H0) as HR. pose proof (R_svc _ _ _ _ _ HR) as Hsvc.
  pose proof (budget_pend ms m Hbud Hh Hnl Hsvc Hstep) as Hbud1.
  assert (Hargs : mmap_anon_args (ms_pend ms) (to_Z len)).
  { unfold mmap_anon_args. repeat split; assumption. }
  destruct (ledger_inv_params_nonneg _ _ _ _ _ Hli) as [Hc0 HS0].
  unfold grant_fits in Hfit. apply andb_true_iff in Hfit as [Hpig Hacct].
  apply Z.leb_le in Hpig. rewrite HnZ in Hpig.
  assert (Hpig' : page_size + (live_bytes R0 + fl_S L) + (Z.of_nat (length R0) + fl_c L) * (nZ + page_size) + nZ
                  <= alloc_lo_bound).
  { rewrite alloc_lo_bound_val. unfold page_size.
    assert ((Z.of_nat (length R0) + fl_c L) * (nZ + 4096) <= (Rc + fl_c L) * (nZ + 4096))
      by (apply Z.mul_le_mono_nonneg_r; lia).
    lia. }
  fold nZ in Ha. eexists. split; [reflexivity|]. fold nZi nZ.
  assert (Hstepa : sstep_cfg segs cfg (mkCfg (ms_pend ms) m) []
            (SNext (mkCfg (sysret (ms_pend ms) a (apply_zeros (ms_mem (ms_pend ms)) [(a, Z_to_bv 64 nZ)]))
                          (mmap_grant_model a nZ m)))).
  { apply (mmap_anon_step_iff cfg segs (ms_pend ms) _ m (to_Z len) Halloc Hh (proj1 Hnl)
             (ms_pend_svc ms) Hx8 Hargs (ex_intro _ a Ha)).
    exists a. repeat split. exact Ha. }
  pose proof Ha as Hg. apply mmap_grant_b_iff in Hg as (Hal & Hapos & Hatop & Hfree & _).
  destruct (ledger_inv_alloc_top _ _ _ _ _ Hli) as [_ Htop].
  unfold page_size in Hal. unfold TASK_SIZE in Htop.
  assert (Hsep : sep_from rho (f_mem F) (bv_unsigned a) (bv_unsigned a + to_Z nZi)).
  { rewrite HnZ. apply (sep_from_free rho (f_mem F) (m_vmmaps m) a nZ Hcov); [lia | exact Hatop | exact Hfree]. }
  pose proof (fx_grant_sound segs IM n rho F ms a nZi HRn Hat Hn0 Hn61 Hlt
                ltac:(lia) ltac:(rewrite HnZ; exact HnZmod) Hal Hapos ltac:(lia) ltac:(lia) Hsep) as HRn'.
  rewrite HnZ in HRn'.
  set (rho' := rho_upd rho n a) in *.
  set (M' := iset n (RG 0 nZi 12 (Some PKZero) iempty grant_clo (grant_chi nZi)) (f_mem F)).
  assert (HM' : f_mem (fx_grant F n nZi) = M') by reflexivity.
  assert (Hmaps : vm_maps (m_vmmaps (mmap_grant_model a nZ m)) = (a, Z_to_bv 64 nZ) :: vm_maps (m_vmmaps m))
    by reflexivity.
  assert (Hother : forall t rg, iget t (f_mem F) = Some rg -> rho' t = rho t /\ iget t M' = Some rg).
  { intros t rg Hgt. split; [exact (regions_lt_rho rho n a _ _ _ Hlt Hgt)|].
    unfold M'. rewrite iget_iset_other; [exact Hgt|]. intros ->. pose proof (Hlt _ _ Hgt). lia. }
  split; [exact Hstepa|].
  split.
  2:{ constructor.
      - rewrite (to_Z_succ61 n Hn61). lia.
      - intros t Ht. unfold rho'. apply rho_upd_other. apply lt_neq. exact Ht.
      - rewrite sysret_fregs. reflexivity.
      - rewrite sysret_fcsr. reflexivity.
      - rewrite sysret_rom. reflexivity.
      - repeat split; reflexivity.
      - reflexivity.
      - intros x Hx Hno. split.
        + rewrite sysret_mem, apply_zeros_one. rewrite u64_lit by lia.
          replace ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + nZ)) with false
            by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
          reflexivity.
        + rewrite HM'. intros t rg Hgt Hxin. unfold M' in Hgt. rewrite iget_iset in Hgt.
          destruct (t =? n)%uint63 eqn:E.
          * apply Uint63.eqb_spec in E. subst t. injection Hgt as <-. unfold in_ival in Hxin.
            cbn [rg_lo rg_len] in Hxin. unfold rho' in Hxin. rewrite rho_upd_same, to_Z_0, HnZ in Hxin. lia.
          * apply (Hno t rg Hgt). exact (in_ival_rho rho rho' t rg _ (proj1 (Hother t rg Hgt)) Hxin).
      - reflexivity.
      - reflexivity.
      - intros _ [E1 E2]. destruct Hmir as (Hm1 & Hm2 & _). split.
        + cbn [fl_maps map]. rewrite Hmaps, E1. f_equal.
          * cbn [den]. rewrite to_Z_0, adr_0. unfold rho'. rewrite rho_upd_same, HnZ. reflexivity.
          * symmetry. exact (map_den_regions rho rho' _ _ _ (fun t rg Hgt => proj1 (Hother t rg Hgt)) Hm1).
        + cbn [fl_na]. change (vm_noaccess (m_vmmaps (mmap_grant_model a nZ m))) with (vm_noaccess (m_vmmaps m)).
          rewrite E2. symmetry.
          exact (map_den_regions rho rho' _ _ _ (fun t rg Hgt => proj1 (Hother t rg Hgt)) Hm2). }
  split; [exact HRn'|].
  split. { unfold rho'. rewrite rho_upd_other; [exact H0|]. intros E. rewrite <- E, to_Z_0 in Hn0. lia. }
  split; [exact Hh|]. split; [apply model_nolazy_with_vmmaps; exact Hnl|].
  split; [cbn [fl_c fl_S]; rewrite HnZ; exact (mmap_anon_inv R0 Lim (fl_c L) (fl_S L) m a (to_Z len) Hli Hpos Ha)|].
  split.
  { (* [comment removed for export] *)
    rewrite HM'. intros t rg Hgt. unfold M' in Hgt. rewrite iget_iset in Hgt.
    destruct (t =? n)%uint63 eqn:E.
    - apply Uint63.eqb_spec in E. subst t. injection Hgt as <-. cbn [rg_lo rg_len].
      rewrite to_Z_0. split; [lia|]. intros x Hx. unfold in_ival in Hx. cbn [rg_lo rg_len] in Hx.
      unfold rho' in Hx. rewrite rho_upd_same, to_Z_0, HnZ in Hx.
      left. exists (a, Z_to_bv 64 nZ). split.
      + apply in_app_iff. right. rewrite Hmaps. left. reflexivity.
      + unfold e_hi, e_lo, e_sz. cbn [fst snd]. rewrite u64_lit by lia. lia.
    - destruct (Hcov t rg Hgt) as [Hne Hb]. split; [exact Hne|]. intros x Hx.
      apply (covered_mono (m_vmmaps m)); [reflexivity | reflexivity | | ].
      + intros p Hp. rewrite Hmaps. right. exact Hp.
      + apply Hb. exact (in_ival_rho rho rho' t rg x (proj1 (Hother t rg Hgt)) Hx). }
  split.
  { (* [comment removed for export] *)
    rewrite HM'. destruct Hmir as (Hm1 & Hm2 & rgb & Hgb & Hbrk). split; [|split].
    - cbn [fl_maps]. constructor.
      + exists (RG 0 nZi 12 (Some PKZero) iempty grant_clo (grant_chi nZi)). unfold M'. rewrite iget_iset_same. cbn [rg_lo rg_len].
        rewrite to_Z_0. split; [reflexivity|]. split; [lia|]. split; [lia|].
        rewrite Hmaps. left. rewrite adr_0. unfold rho'. rewrite rho_upd_same, HnZ. reflexivity.
      + eapply Forall_impl; [|exact Hm1]. intros e He.
        destruct (ent_ok_tag _ _ _ _ He) as [rg Hrg]. destruct (Hother _ _ Hrg) as [Er Eg].
        apply (ent_ok_ext rho rho' (f_mem F) M' (vm_maps (m_vmmaps m))); try assumption.
        * rewrite Eg, Hrg. reflexivity.
        * intros p Hp. rewrite Hmaps. right. exact Hp.
    - cbn [fl_na]. eapply Forall_impl; [|exact Hm2]. intros e He.
      destruct (ent_ok_tag _ _ _ _ He) as [rg Hrg]. destruct (Hother _ _ Hrg) as [Er Eg].
      apply (ent_ok_ext rho rho' (f_mem F) M' (vm_noaccess (m_vmmaps m))); try assumption.
      + rewrite Eg, Hrg. reflexivity.
      + intros p Hp. exact Hp.
    - cbn [fl_brk]. destruct (Hother _ _ Hgb) as [Er Eg]. exists rgb. split; [exact Eg|].
      rewrite (adr_rho rho rho' _ _ Er). exact Hbrk. }
  split; [exact (budget_step _ _ _ _ _ Hbud1 Hstepa)|].
  split.
  { apply (XI_rho rho rho'); [|apply (XI_vm rho m); [repeat split; reflexivity | exact HXI]].
    intros tx Htx. unfold rho'. apply rho_upd_other. apply lt_neq. exact (Hxt tx Htx). }
  split; [intros tx Htx; rewrite (to_Z_succ61 n Hn61); pose proof (Hxt tx Htx); lia|].
  (* [comment removed for export] *)
  rewrite HM'. intros t Ht. destruct (Hfr t Ht) as [Hpr Hmem].
  destruct Hpr as (Hne0 & rgt & Hgt & Hpr2). destruct (Hother _ _ Hgt) as [Er Eg].
  split; [split; [exact Hne0 | exists rgt; split; [exact Eg | exact Hpr2]]|].
  intros rg x Hgx Hx. rewrite Eg in Hgx. injection Hgx as <-.
  apply (in_ival_rho rho rho' t rgt _ Er) in Hx.
  rewrite sysret_mem, apply_zeros_one.
  destruct (Hsep t rgt Hgt) as [Hs|Hs]; unfold rg_ival in Hs; cbn [fst snd] in Hs;
    unfold in_ival in Hx; rewrite ?HnZ in Hs; rewrite u64_lit by lia.
  - replace ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + nZ)) with false
      by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
    exact (Hmem rgt x Hgt Hx).
  - replace ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + nZ)) with false
      by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    exact (Hmem rgt x Hgt Hx).
Qed.

Lemma sys_grant_soundX n rho F L ms m len res :
  sys_grant Rb Rc Lim rl F L n len = Some res ->
  DInv n rho F L ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 222 ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  bv_unsigned (ms_gpr (ms_pend ms) 2) = 3 ->
  bv_unsigned (ms_gpr (ms_pend ms) 3) = 34 ->
  bv_unsigned (ms_gpr (ms_pend ms) 5) = 0 ->
  sys_okX n rho F L res ms m.
Proof.
  intros Hsys HD Hat Hstep Hx8 Ha1 Ha2 Ha3 Ha5. pose proof Hsys as Hsys0.
  pose proof HD as (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfr).
  unfold sys_grant in Hsys. cbv zeta in Hsys.
  destruct ((0 <? len)%uint63 && (len <=? 4611686018427387904)%uint63
            && (pg_up len <=? 4611686018427387904)%uint63 && tag_ok F n
            && grant_fits Rb Rc Lim rl L (to_Z (pg_up len))) eqn:Hchk; [|discriminate].
  clear Hsys.
  apply andb_true_iff in Hchk as [Hchk Hfit]. apply andb_true_iff in Hchk as [Hchk Htag].
  apply andb_true_iff in Hchk as [Hchk Hup]. apply andb_true_iff in Hchk as [Hpos Hle].
  apply ltb_spec in Hpos. apply leb_spec in Hle, Hup. rewrite to_Z_0 in Hpos.
  change (to_Z 4611686018427387904) with (2 ^ 62) in Hle, Hup.
  pose proof (pg_up_spec len Hle) as HnZ.
  set (nZi := pg_up len) in *. set (nZ := page_round_up_Z (to_Z len)) in *.
  assert (HnZpos : 0 < nZ) by (apply page_round_up_Z_pos; exact Hpos).
  assert (HnZmod : nZ mod 4096 = 0) by (apply page_round_up_Z_mod).
  unfold tag_ok in Htag. apply andb_true_iff in Htag as [Htag Hlt].
  apply andb_true_iff in Htag as [Hn0 Hn61]. apply ltb_spec in Hn0, Hn61. rewrite to_Z_0 in Hn0.
  change (to_Z 1152921504606846976) with (2 ^ 60) in Hn61.
  apply regions_lt_b_ok in Hlt.
  pose proof (Rn_R _ _ _ _ HRn H0) as HR. pose proof (R_svc _ _ _ _ _ HR) as Hsvc.
  pose proof (budget_pend ms m Hbud Hh Hnl Hsvc Hstep) as Hbud1.
  assert (Hargs : mmap_anon_args (ms_pend ms) (to_Z len)).
  { unfold mmap_anon_args. repeat split; assumption. }
  destruct (ledger_inv_params_nonneg _ _ _ _ _ Hli) as [Hc0 HS0].
  unfold grant_fits in Hfit. apply andb_true_iff in Hfit as [Hpig Hacct].
  apply Z.leb_le in Hpig. rewrite HnZ in Hpig.
  assert (Hpig' : page_size + (live_bytes R0 + fl_S L) + (Z.of_nat (length R0) + fl_c L) * (nZ + page_size) + nZ
                  <= alloc_lo_bound).
  { rewrite alloc_lo_bound_val. unfold page_size.
    assert ((Z.of_nat (length R0) + fl_c L) * (nZ + 4096) <= (Rc + fl_c L) * (nZ + 4096))
      by (apply Z.mul_le_mono_nonneg_r; lia).
    lia. }
  assert (Hex : exists a, mmap_grant_b m a nZ = true).
  { destruct rl_cases as [Erl|Erl].
    - pose proof Hbud1 as Hb. unfold budget in Hb. rewrite Erl in Hb.
      exact (mmap_anon_grant_exists_src cfg segs R0 Lim (fl_c L) (fl_S L) (ms_pend ms) _ m (to_Z len)
               Hli Hb Hh (ms_pend_svc ms) Hx8 Hargs Hpig').
    - rewrite Erl in Hacct. apply Z.leb_le in Hacct. rewrite HnZ in Hacct.
      exact (mmap_grant_exists_inv_acct R0 Lim (fl_c L) (fl_S L) m nZ Hli (proj2 Hnl) ltac:(lia) Hpig' Hacct). }
  pose proof (mmap_anon_step_iff cfg segs (ms_pend ms) _ m (to_Z len) Halloc Hh (proj1 Hnl)
                (ms_pend_svc ms) Hx8 Hargs Hex) as Hiff. cbv zeta in Hiff. fold nZ in Hiff.
  destruct Hex as [a0 Ha0].
  exists {a : word | mmap_grant_b m a nZ = true}, (exist _ a0 Ha0),
    (fun i => mkCfg (sysret (ms_pend ms) (proj1_sig i)
                       (apply_zeros (ms_mem (ms_pend ms)) [(proj1_sig i, Z_to_bv 64 nZ)]))
                    (mmap_grant_model (proj1_sig i) nZ m)).
  split.
  { intros e st. rewrite Hiff. split.
    - intros (a & Ha & -> & ->). exists (exist _ a Ha). split; reflexivity.
    - intros ([a Ha] & -> & ->). exists a. repeat split. exact Ha. }
  intros [a Ha]. cbn [proj1_sig].
  destruct (sys_grant_succ n rho F L ms m len _ a Hsys0 HD Hat Hstep Hx8 Ha1 Ha2 Ha3 Ha5 Ha)
    as (L' & E & _ & HD' & Hne).
  eexists (fx_grant F n (pg_up len)), L', (n + 1)%uint63, (rho_upd rho n a), _, _, 0%nat.
  cbn [cfg_ms cfg_model rsteps]. rewrite E. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact HD' | exact Hne].
Qed.

Lemma sys_grant_sound n rho F L ms m len res :
  sys_grant Rb Rc Lim rl F L n len = Some res ->
  DInv n rho F L ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 222 ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  bv_unsigned (ms_gpr (ms_pend ms) 2) = 3 ->
  bv_unsigned (ms_gpr (ms_pend ms) 3) = 34 ->
  bv_unsigned (ms_gpr (ms_pend ms) 5) = 0 ->
  sys_ok res ms m.
Proof.
  intros. eapply sys_okX_ok. eapply sys_grant_soundX; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma maps_subtract_keep : forall l lo hi q,
  In q l -> lo <= hi -> 0 < e_sz q -> (e_hi q <= lo \/ hi <= e_lo q) ->
  In q (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] r IH]; intros lo hi q Hin Hle Hpos Hd; [contradiction|].
  cbn [maps_subtract]. apply in_app_iff. destruct Hin as [<- | Hin].
  - left. unfold e_sz, e_hi, e_lo in *. cbn [fst snd] in *.
    rewrite (iv_subtract_disj a sz lo hi Hle Hpos Hd). left. reflexivity.
  - right. apply IH; assumption.
Qed.

Lemma map_remove_keep maps (a : word) p : In p maps -> fst p <> a -> In p (map_remove maps a).
Proof.
  intros Hin Hne. unfold map_remove. apply filter_In. split; [exact Hin|].
  apply negb_true_iff. apply bv_eqb_false_iff. exact Hne.
Qed.

Lemma entries_base_neq R L c S h p q :
  ledger_inv R L c S h -> In p (vm_maps h) -> In q (vm_maps h) -> p <> q -> fst p <> fst q.
Proof.
  intros Hli Hp Hq Hne.
  pose proof (pw_disj_In _ _ _ (li_disj _ _ _ _ _ Hli) Hp Hq Hne) as Hd.
  pose proof (proj1 (Forall_forall _ _) (li_pos _ _ _ _ _ Hli)) as Hpos.
  exact (e_disj_base_neq p q Hd (Hpos p Hp) (Hpos q Hq)).
Qed.

(* [comment removed for export] *)
Lemma ent_range rho t off len rg :
  region_ok rho t rg -> to_Z (rg_lo rg) <= to_Z off -> to_Z off + to_Z len <= to_Z (rg_len rg) ->
  e_lo (adr rho t (to_Z off), Z_to_bv 64 (to_Z len)) = bv_unsigned (rho t) + to_Z off
  /\ e_hi (adr rho t (to_Z off), Z_to_bv 64 (to_Z len)) = bv_unsigned (rho t) + to_Z off + to_Z len.
Proof.
  intros Hreg H1 H2. pose proof (region_ok_nowrap _ _ _ Hreg) as Hnw.
  pose proof (i63_range off). pose proof (i63_range len). pose proof (u64 (rho t)).
  unfold e_hi, e_lo, e_sz. cbn [fst snd].
  rewrite adr_unsigned by lia. rewrite u64_lit by lia. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ent_in_range rho (M : itrie region) e :
  (forall t' rg', iget t' M = Some rg' -> region_ok rho t' rg') -> ent_in M e ->
  exists rg, iget (fent_tag e) M = Some rg
    /\ bv_unsigned (rho (fent_tag e)) + to_Z (rg_lo rg) <= e_lo (den rho e)
    /\ e_hi (den rho e) <= bv_unsigned (rho (fent_tag e)) + to_Z (rg_len rg).
Proof.
  intros Hreg. destruct e as [[t off] len]. intros (rg & Hg & H1 & H2). cbn [fent_tag fst den].
  exists rg. split; [exact Hg|].
  destruct (ent_range rho t off len rg (Hreg _ _ Hg) H1 H2) as [El Eh]. rewrite El, Eh. lia.
Qed.

(* [comment removed for export] *)
Lemma unmap_exact_na rho (M : itrie region) l t rg na :
  (forall t' rg', iget t' M = Some rg' -> region_ok rho t' rg') -> regions_sep rho M ->
  iget t M = Some rg -> to_Z (rg_lo rg) = 0 ->
  Forall (fun q => 0 < e_sz q) l ->
  Forall (ent_ok rho M l) na ->
  map (den rho) (drop_tag t na)
  = maps_subtract (map (den rho) na) (bv_unsigned (rho t)) (bv_unsigned (rho t) + to_Z (rg_len rg)).
Proof.
  intros Hreg Hsep Hg Hlo0 Hpos Hna. apply map_den_drop_tag_sub. intros e He.
  pose proof (proj1 (Forall_forall _ _) Hna e He) as Hok. apply ent_ok_iff in Hok as [Hin Hden].
  pose proof (proj1 (Forall_forall _ _) Hpos _ Hden) as Hp.
  destruct (ent_in_range rho M e Hreg Hin) as (rg' & Hg' & Hl & Hh).
  pose proof (i63_range (rg_len rg)) as Hlen.
  destruct (den rho e) as [a s] eqn:Ed. unfold e_hi, e_lo, e_sz in *. cbn [fst snd] in *.
  destruct (fent_tag e =? t)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. rewrite Et, Hg in Hg'. injection Hg' as <-. rewrite Et in Hl, Hh.
    apply iv_subtract_inside; lia.
  - apply eqb_false_spec in Et. apply iv_subtract_disj; [lia | exact Hp |].
    destruct (Hsep _ _ _ _ Et Hg' Hg) as [Hd|Hd]; [left | right]; lia.
Qed.

(* [comment removed for export] *)
Lemma unmap_exact_maps rho (M : itrie region) t rg fm :
  (forall t' rg', iget t' M = Some rg' -> region_ok rho t' rg') -> regions_sep rho M ->
  iget t M = Some rg -> to_Z (rg_lo rg) = 0 -> 0 < to_Z (rg_len rg) ->
  pw_disj (map (den rho) fm) -> Forall (fun p => 0 < e_sz p) (map (den rho) fm) ->
  Forall (ent_in M) fm ->
  In (t, 0%uint63, rg_len rg) fm ->
  map (den rho) (drop_tag t fm) = map_remove (map (den rho) fm) (rho t).
Proof.
  intros Hreg Hsep Hg Hlo0 Hlen Hdisj Hpos Hin Hwhole. apply map_den_drop_tag_remove. intros e He.
  pose proof (proj1 (Forall_forall _ _) Hin e He) as Hine.
  pose proof (proj1 (Forall_forall _ _) Hpos _ (in_map (den rho) _ _ He)) as Hp.
  destruct (ent_in_range rho M e Hreg Hine) as (rg' & Hg' & Hl & Hh).
  pose proof (proj1 (Forall_forall _ _) Hin _ Hwhole) as Hinw.
  destruct (ent_in_range rho M _ Hreg Hinw) as (rgw & Hgw & Hlw & Hhw).
  cbn [fent_tag fst] in Hgw, Hlw, Hhw. rewrite Hg in Hgw. injection Hgw as <-.
  assert (Ew : fst (den rho (t, 0%uint63, rg_len rg)) = rho t).
  { cbn [den fst]. rewrite to_Z_0. apply adr_0. }
  assert (Elw : e_lo (den rho (t, 0%uint63, rg_len rg)) = bv_unsigned (rho t)).
  { unfold e_lo. rewrite Ew. reflexivity. }
  assert (Esw : e_sz (den rho (t, 0%uint63, rg_len rg)) = to_Z (rg_len rg)).
  { unfold e_sz. cbn [den snd]. apply u64_lit. pose proof (i63_range (rg_len rg)). lia. }
  destruct (fent_tag e =? t)%uint63 eqn:Et.
  - apply Uint63.eqb_spec in Et. rewrite Et, Hg in Hg'. injection Hg' as <-. rewrite Et in Hl, Hh.
    destruct (entry_eq_dec_prop (den rho e) (den rho (t, 0%uint63, rg_len rg))) as [E|E].
    + rewrite E, Ew. apply bv_eqb_refl_true.
    + exfalso.
      pose proof (pw_disj_In _ _ _ Hdisj (in_map (den rho) _ _ He) (in_map (den rho) _ _ Hwhole) E) as Hd.
      unfold e_disj, e_hi in *. lia.
  - apply eqb_false_spec in Et. apply bv_eqb_false_iff. intros E.
    assert (Ez : e_lo (den rho e) = bv_unsigned (rho t)) by (unfold e_lo; rewrite E; reflexivity).
    unfold e_hi in *.
    destruct (Hsep _ _ _ _ Et Hg' Hg) as [Hd|Hd]; lia.
Qed.

Lemma sys_unmap_soundX n rho F L ms m t off len res :
  sys_unmap keep F L n t off len = Some res ->
  DInv n rho F L ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 215 ->
  ms_gpr (ms_pend ms) 0 = adr rho t (to_Z off) ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  sys_okX n rho F L res ms m.
Proof.
  intros Hsys (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfr) Hat Hstep Hx8 Ha0 Ha1.
  unfold sys_unmap in Hsys. destruct (iget t (f_mem F)) as [rg|] eqn:Hg; [|discriminate].
  match type of Hsys with (if ?c then _ else _) = _ => destruct c eqn:Hchk; [|discriminate] end.
  injection Hsys as <-.
  repeat match type of Hchk with (_ && _ = true) =>
    let H := fresh "Hc" in apply andb_true_iff in Hchk as [Hchk H] end.
  rename Hchk into Hoff.
  apply Uint63.eqb_spec in Hoff. subst off. rewrite to_Z_0, adr_0 in Ha0.
  apply negb_true_iff in Hc7. apply eqb_false_spec in Hc7.       (* [comment removed for export] *)
  apply ltb_spec in Hc6.                                         (* [comment removed for export] *)
  apply negb_true_iff in Hc5. apply eqb_false_spec in Hc5.       (* [comment removed for export] *)
  apply negb_true_iff in Hc4. apply mem_int_false in Hc4.        (* [comment removed for export] *)
  apply ltb_spec in Hc3. rewrite to_Z_0 in Hc3.                  (* [comment removed for export] *)
  apply leb_spec in Hc2. change (to_Z 4611686018427387904) with (2 ^ 62) in Hc2.
  apply Uint63.eqb_spec in Hc1.                                  (* [comment removed for export] *)
  apply Uint63.eqb_spec in Hc0.                                  (* [comment removed for export] *)
  apply mem_fent_In in Hc.
  assert (Hlo0 : to_Z (rg_lo rg) = 0) by (rewrite Hc1; reflexivity).
  pose proof (pg_up_spec len Hc2) as Hup. rewrite Hc0 in Hup.
  pose proof (Rn_R _ _ _ _ HRn H0) as HR. pose proof (R_svc _ _ _ _ _ HR) as Hsvc.
  pose proof (budget_pend ms m Hbud Hh Hnl Hsvc Hstep) as Hbud1.
  pose proof (R_region_ok _ _ _ _ _ HR Hg) as Hreg.
  pose proof (R_regions_sep _ _ _ HR) as Hsep.
  pose proof (i63_range (rg_len rg)) as Hlenr.
  set (nw := Z_to_bv 64 (to_Z (rg_len rg))).
  assert (Hnw : bv_unsigned nw = to_Z (rg_len rg)) by (apply u64_lit; lia).
  destruct Hmir as (Hm1 & Hm2 & rgb & Hgb & Hbrk).
  assert (Hin : In (rho t, nw) (vm_maps (m_vmmaps m))).
  { pose proof (proj1 (Forall_forall _ _) Hm1 _ Hc) as (rg' & _ & _ & _ & Hi).
    rewrite to_Z_0, adr_0 in Hi. exact Hi. }
  assert (Hargs : munmap_entry_args (ms_pend ms) m (to_Z len) nw).
  { apply (munmap_entry_args_of_inv R0 Lim (fl_c L) (fl_S L)); try assumption.
    - rewrite Hnw. exact Hup.
    - rewrite Ha0. exact Hin. }
  pose proof (munmap_entry_step_iff cfg segs (ms_pend ms) _ m (to_Z len) nw Hh Hnl
                (ms_pend_svc ms) Hx8 Hargs) as Hiff.
  rewrite Ha0 in Hiff.
  exists unit, tt, (fun _ => mkCfg (sysret (ms_pend ms) (Z_to_bv 64 0)
                               (apply_unmaps (ms_mem (ms_pend ms)) [(rho t, nw)]))
                            (with_vmmaps (ledger_unmap (rho t) nw (m_vmmaps m)) m)).
  split.
  { intros e st. rewrite Hiff. split.
    - intros [-> ->]. exists tt. split; reflexivity.
    - intros (_ & -> & ->). split; reflexivity. }
  intros _.
  assert (Hstepa : sstep_cfg segs cfg (mkCfg (ms_pend ms) m) []
            (SNext (mkCfg (sysret (ms_pend ms) (Z_to_bv 64 0)
                             (apply_unmaps (ms_mem (ms_pend ms)) [(rho t, nw)]))
                          (with_vmmaps (ledger_unmap (rho t) nw (m_vmmaps m)) m)))).
  { apply Hiff. split; reflexivity. }
  pose proof (fx_unmap_sound segs IM n rho F ms t rg HRn Hat Hg Hc7 Hc6 Hlo0) as HRn'.
  (* [comment removed for export] *)
  assert (Hival : forall x, in_ival rho t rg x <-> bv_unsigned (rho t) <= x < bv_unsigned (rho t) + to_Z (rg_len rg)).
  { intros x. unfold in_ival. rewrite Hlo0. lia. }
  assert (Hne_len : 0 < to_Z (rg_len rg)) by (pose proof (proj1 (Hcov t rg Hg)); lia).
  assert (Hother : forall t', t' <> t -> iget t' (iremove t (f_mem F)) = iget t' (f_mem F)).
  { intros t' Hne. apply iget_iremove_other. intros E. apply Hne. symmetry. exact E. }
  assert (HM' : f_mem (fx_unmap F t) = iremove t (f_mem F)) by reflexivity.
  eexists _, _, _, rho, _, _, 0%nat. cbn [cfg_ms cfg_model rsteps]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  2:{ constructor.
      - lia.
      - intros; reflexivity.
      - rewrite sysret_fregs. reflexivity.
      - rewrite sysret_fcsr. reflexivity.
      - rewrite sysret_rom. reflexivity.
      - repeat split; reflexivity.
      - reflexivity.
      - intros x Hx Hno. split.
        + rewrite sysret_mem, apply_unmaps_one, Hnw.
          replace ((bv_unsigned (rho t) <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned (rho t) + to_Z (rg_len rg)))
            with false; [reflexivity|].
          symmetry. apply not_true_iff_false. intros Hb. apply andb_true_iff in Hb as [B1 B2].
          apply Z.leb_le in B1. apply Z.ltb_lt in B2.
          exact (Hno t rg Hg (proj2 (Hival _) (conj B1 B2))).
        + rewrite HM'. intros t' rg' Hg' Hxin.
          destruct (Uint63.eqb t' t) eqn:E.
          * apply Uint63.eqb_spec in E. subst t'. rewrite iget_iremove_same in Hg'. discriminate.
          * assert (Hne' : t' <> t) by (intros ->; rewrite Uint63.eqb_refl in E; discriminate).
            rewrite (Hother t' Hne') in Hg'. exact (Hno t' rg' Hg' Hxin).
      - reflexivity.
      - reflexivity.
      - intros _ [E1 E2].
        assert (Hregs : forall t' rg', iget t' (f_mem F) = Some rg' -> region_ok rho t' rg')
          by (intros t' rg' Hg'; exact (R_region_ok _ _ _ _ _ HR Hg')).
        split.
        + cbn [fl_maps].
          change (vm_maps (m_vmmaps (with_vmmaps (ledger_unmap (rho t) nw (m_vmmaps m)) m)))
            with (map_remove (vm_maps (m_vmmaps m)) (rho t)).
          rewrite E1. symmetry.
          apply (unmap_exact_maps rho (f_mem F) t rg (fl_maps L) Hregs Hsep Hg Hlo0 Hne_len).
          * rewrite <- E1. exact (li_disj _ _ _ _ _ Hli).
          * rewrite <- E1. exact (li_pos _ _ _ _ _ Hli).
          * eapply Forall_impl; [|exact Hm1]. intros e He. exact (proj1 (proj1 (ent_ok_iff _ _ _ _) He)).
          * exact Hc.
        + cbn [fl_na].
          change (vm_noaccess (m_vmmaps (with_vmmaps (ledger_unmap (rho t) nw (m_vmmaps m)) m)))
            with (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned (rho t)) (bv_unsigned (rho t) + bv_unsigned nw)).
          rewrite Hnw, E2. symmetry.
          apply (unmap_exact_na rho (f_mem F) (vm_noaccess (m_vmmaps m)) t rg (fl_na L) Hregs Hsep Hg Hlo0); [|exact Hm2].
          eapply Forall_impl; [|exact (li_noacc _ _ _ _ _ Hli)]. intros q0 [Hq0 _]. exact Hq0. }
  split; [exact HRn'|]. split; [exact H0|]. split; [exact Hh|].
  split; [apply model_nolazy_with_vmmaps; exact Hnl|].
  split.
  { cbn [fl_c fl_S]. rewrite <- Hnw.
    exact (munmap_entry_inv R0 Lim (fl_c L) (fl_S L) m (rho t) nw Hli Hin). }
  split.
  { (* [comment removed for export] *)
    rewrite HM'. intros t' rg' Hg'. rewrite iget_iremove in Hg'.
    destruct (t' =? t)%uint63 eqn:E; [discriminate|]. apply eqb_false_spec in E.
    destruct (Hcov t' rg' Hg') as [Hne Hb]. split; [exact Hne|]. intros x Hx.
    destruct (Hb x Hx) as [(p & Hp & Hpx) | Hat'].
    - left. exists p. split; [|exact Hpx]. apply in_app_iff in Hp. apply in_app_iff.
      destruct Hp as [Hp|Hp]; [left; exact Hp|]. right.
      change (vm_maps (m_vmmaps (with_vmmaps (ledger_unmap (rho t) nw (m_vmmaps m)) m)))
        with (map_remove (vm_maps (m_vmmaps m)) (rho t)).
      apply map_remove_keep; [exact Hp|].
      destruct (entry_eq_dec_prop p (rho t, nw)) as [Ep|Ep].
      + exfalso. subst p. unfold e_hi, e_lo, e_sz in Hpx. cbn [fst snd] in Hpx. rewrite Hnw in Hpx.
        exact (ival_disjoint rho (f_mem F) t' t rg' rg x Hsep E Hg' Hg Hx (proj2 (Hival x) Hpx)).
      + exact (entries_base_neq _ _ _ _ _ p (rho t, nw) Hli Hp Hin Ep).
    - right. exact Hat'. }
  split.
  { (* [comment removed for export] *)
    rewrite HM'. split; [|split].
    - cbn [fl_maps]. apply Forall_forall. intros e He. apply drop_tag_In in He as [He Htag].
      pose proof (proj1 (Forall_forall _ _) Hm1 _ He) as Hok.
      destruct e as [[t' off'] len']. cbn [fent_tag fst] in Htag.
      destruct Hok as (rg' & Hg' & Hl1 & Hl2 & Hi).
      exists rg'. rewrite (Hother t' Htag). repeat split; try assumption.
      change (vm_maps (m_vmmaps (with_vmmaps (ledger_unmap (rho t) nw (m_vmmaps m)) m)))
        with (map_remove (vm_maps (m_vmmaps m)) (rho t)).
      apply map_remove_keep; [exact Hi|].
      apply (entries_base_neq _ _ _ _ _ _ (rho t, nw) Hli Hi Hin).
      intros Eq.
      pose proof (proj1 (Forall_forall _ _) (li_pos _ _ _ _ _ Hli) _ Hi) as Hpos. cbv beta in Hpos.
      destruct (ent_range rho t' off' len' rg' (R_region_ok _ _ _ _ _ HR Hg') Hl1 Hl2) as [El Eh].
      unfold e_hi in Eh. rewrite El in Eh.
      assert (Hbase : bv_unsigned (rho t) = bv_unsigned (rho t') + to_Z off').
      { rewrite <- El. rewrite Eq. reflexivity. }
      apply (ival_disjoint rho (f_mem F) t' t rg' rg (bv_unsigned (rho t)) Hsep Htag Hg' Hg).
      + unfold in_ival. lia.
      + apply Hival. lia.
    - cbn [fl_na]. apply Forall_forall. intros e He. apply drop_tag_In in He as [He Htag].
      pose proof (proj1 (Forall_forall _ _) Hm2 _ He) as Hok.
      destruct e as [[t' off'] len']. cbn [fent_tag fst] in Htag.
      destruct Hok as (rg' & Hg' & Hl1 & Hl2 & Hi).
      exists rg'. rewrite (Hother t' Htag). repeat split; try assumption.
      change (vm_noaccess (m_vmmaps (with_vmmaps (ledger_unmap (rho t) nw (m_vmmaps m)) m)))
        with (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned (rho t)) (bv_unsigned (rho t) + bv_unsigned nw)).
      pose proof (proj1 (Forall_forall _ _) (li_noacc _ _ _ _ _ Hli) _ Hi) as [Hpos _].
      destruct (ent_range rho t' off' len' rg' (R_region_ok _ _ _ _ _ HR Hg') Hl1 Hl2) as [El Eh].
      apply maps_subtract_keep; [exact Hi | lia | exact Hpos |].
      rewrite El, Eh, Hnw.
      destruct (Hsep t' t rg' rg Htag Hg' Hg) as [Hd|Hd]; [left | right]; lia.
    - cbn [fl_brk]. exists rgb. split; [|exact Hbrk].
      rewrite Hother; [exact Hgb|]. intros E. apply Hc5. symmetry. exact E. }
  split; [exact (budget_step _ _ _ _ _ Hbud1 Hstepa)|].
  split; [apply (XI_vm rho m); [repeat split; reflexivity | exact HXI]|]. split; [exact Hxt|].
  (* [comment removed for export] *)
  rewrite HM'. intros tk Htk. destruct (Hfr tk Htk) as [Hpr Hmem].
  assert (Hnek : tk <> t) by (intros ->; contradiction).
  split; [exact (pristine_eq _ _ _ (Hother tk Hnek) Hpr)|].
  intros rgk x Hgk Hx. rewrite (Hother tk Hnek) in Hgk.
  rewrite sysret_mem, apply_unmaps_one, Hnw.
  replace ((bv_unsigned (rho t) <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned (rho t) + to_Z (rg_len rg)))
    with false; [exact (Hmem rgk x Hgk Hx)|].
  symmetry. apply not_true_iff_false. intros Hb. apply andb_true_iff in Hb as [B1 B2].
  apply Z.leb_le in B1. apply Z.ltb_lt in B2.
  exact (ival_disjoint rho (f_mem F) tk t rgk rg _ Hsep Hnek Hgk Hg Hx (proj2 (Hival _) (conj B1 B2))).
Qed.

Lemma sys_unmap_sound n rho F L ms m t off len res :
  sys_unmap keep F L n t off len = Some res ->
  DInv n rho F L ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 215 ->
  ms_gpr (ms_pend ms) 0 = adr rho t (to_Z off) ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  sys_ok res ms m.
Proof.
  intros. eapply sys_okX_ok. eapply sys_unmap_soundX; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sys_brk_query_soundX n rho F L ms m res :
  sys_brk_query F L n = Some res ->
  DInv n rho F L ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 214 ->
  bv_unsigned (ms_gpr (ms_pend ms) 0) = 0 ->
  sys_okX n rho F L res ms m.
Proof.
  intros Hsys (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfr) Hat Hstep Hx8 Ha0.
  unfold sys_brk_query in Hsys.
  destruct (iget (fl_brk L) (f_mem F)) as [rg|] eqn:Hg; [|discriminate].
  destruct (fl_brk L <? n)%uint63 eqn:Hlt; [|discriminate]. injection Hsys as <-.
  apply ltb_spec in Hlt.
  pose proof (Rn_R _ _ _ _ HRn H0) as HR. pose proof (R_svc _ _ _ _ _ HR) as Hsvc.
  pose proof (budget_pend ms m Hbud Hh Hnl Hsvc Hstep) as Hbud1.
  pose proof (brk_query_step_iff cfg segs (ms_pend ms) _ m Hh (proj1 Hnl) (ms_pend_svc ms) Hx8
                (or_introl Ha0)) as Hiff.
  exists unit, tt, (fun _ => mkCfg (sysret (ms_pend ms) (vm_brk (m_vmmaps m)) (ms_mem (ms_pend ms))) m).
  split.
  { intros e st. rewrite Hiff. split.
    - intros [-> ->]. exists tt. split; reflexivity.
    - intros (_ & -> & ->). split; reflexivity. }
  intros _.
  assert (Hstepa : sstep_cfg segs cfg (mkCfg (ms_pend ms) m) []
            (SNext (mkCfg (sysret (ms_pend ms) (vm_brk (m_vmmaps m)) (ms_mem (ms_pend ms))) m))).
  { apply Hiff. split; reflexivity. }
  destruct Hmir as (Hm1 & Hm2 & rgb & Hgb & Hbrk).
  rewrite Hg in Hgb. injection Hgb as <-.
  assert (Hdv : forall rho', agree n rho rho' ->
            dv rho' (FV (fl_brk L) (W64 0 (rg_len rg))) = vm_brk (m_vmmaps m)).
  { intros rho' [_ Hag].
    rewrite (dv_adr rho' (fl_brk L) 0%uint63 (rg_len rg) (proj1 (R_region_ok _ _ _ _ _ HR Hg)) eq_refl).
    rewrite (adr_rho rho rho' _ _ (Hag _ Hlt)). exact Hbrk. }
  pose proof (fx_ret_sound segs IM n rho F ms _ _ HRn Hat Hdv) as HRn'.
  eexists _, _, _, rho, _, _, 0%nat. cbn [cfg_ms cfg_model rsteps]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  2:{ apply node_ext_same; [lia | intros; reflexivity | intros; reflexivity | reflexivity | reflexivity
                            | reflexivity | reflexivity | reflexivity]. }
  split; [exact HRn'|]. split; [exact H0|]. split; [exact Hh|]. split; [exact Hnl|].
  split; [exact Hli|]. split; [exact Hcov|].
  split; [split; [exact Hm1 | split; [exact Hm2 | exists rg; split; [exact Hg | exact Hbrk]]]|].
  split; [exact (budget_step _ _ _ _ _ Hbud1 Hstepa)|].
  split; [exact HXI|]. split; [exact Hxt|].
  exact Hfr.
Qed.

Lemma sys_brk_query_sound n rho F L ms m res :
  sys_brk_query F L n = Some res ->
  DInv n rho F L ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 214 ->
  bv_unsigned (ms_gpr (ms_pend ms) 0) = 0 ->
  sys_ok res ms m.
Proof.
  intros. eapply sys_okX_ok. eapply sys_brk_query_soundX; eassumption.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sys_grant_na_succ n rho F L ms m len res a :
  sys_grant_na Rb Rc F L n len = Some res ->
  DInv n rho F L ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 222 ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  bv_unsigned (ms_gpr (ms_pend ms) 2) = 0 ->
  bv_unsigned (ms_gpr (ms_pend ms) 3) = 34 ->
  bv_unsigned (ms_gpr (ms_pend ms) 5) = 0 ->
  mmap_grant_na_b (m_vmmaps m) a (page_round_up_Z (to_Z len)) = true ->
  exists L',
    res = DOne (fx_grant_na F n (pg_up len)) L' (n + 1)%uint63
    /\ sstep_cfg segs cfg (mkCfg (ms_pend ms) m) []
         (SNext (mkCfg (sysret (ms_pend ms) a (apply_unmaps (ms_mem (ms_pend ms))
                                                 [(a, Z_to_bv 64 (page_round_up_Z (to_Z len)))]))
                       (mmap_na_model a (page_round_up_Z (to_Z len)) m)))
    /\ DInv (n + 1)%uint63 (rho_upd rho n a) (fx_grant_na F n (pg_up len)) L'
         (sysret (ms_pend ms) a (apply_unmaps (ms_mem (ms_pend ms)) [(a, Z_to_bv 64 (page_round_up_Z (to_Z len)))]))
         (mmap_na_model a (page_round_up_Z (to_Z len)) m)
    /\ node_ext n rho F L ms m (n + 1)%uint63 (rho_upd rho n a) (fx_grant_na F n (pg_up len)) L'
         (sysret (ms_pend ms) a (apply_unmaps (ms_mem (ms_pend ms)) [(a, Z_to_bv 64 (page_round_up_Z (to_Z len)))]))
         (mmap_na_model a (page_round_up_Z (to_Z len)) m).
Proof.
  intros Hsys (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfr) Hat Hstep Hx8 Ha1 Ha2 Ha3 Ha5 Ha.
  unfold sys_grant_na in Hsys. cbv zeta in Hsys.
  destruct ((0 <? len)%uint63 && (len <=? 4611686018427387904)%uint63
            && (pg_up len <=? 4611686018427387904)%uint63 && tag_ok F n
            && na_fits Rb Rc L (to_Z (pg_up len))) eqn:Hchk; [|discriminate].
  injection Hsys as <-.
  apply andb_true_iff in Hchk as [Hchk Hfit]. apply andb_true_iff in Hchk as [Hchk Htag].
  apply andb_true_iff in Hchk as [Hchk Hup]. apply andb_true_iff in Hchk as [Hpos Hle].
  apply ltb_spec in Hpos. apply leb_spec in Hle, Hup. rewrite to_Z_0 in Hpos.
  change (to_Z 4611686018427387904) with (2 ^ 62) in Hle, Hup.
  pose proof (pg_up_spec len Hle) as HnZ.
  set (nZi := pg_up len) in *. set (nZ := page_round_up_Z (to_Z len)) in *.
  assert (HnZpos : 0 < nZ) by (apply page_round_up_Z_pos; exact Hpos).
  assert (HnZmod : nZ mod 4096 = 0) by (apply page_round_up_Z_mod).
  unfold tag_ok in Htag. apply andb_true_iff in Htag as [Htag Hlt].
  apply andb_true_iff in Htag as [Hn0 Hn61]. apply ltb_spec in Hn0, Hn61. rewrite to_Z_0 in Hn0.
  change (to_Z 1152921504606846976) with (2 ^ 60) in Hn61.
  apply regions_lt_b_ok in Hlt.
  pose proof (Rn_R _ _ _ _ HRn H0) as HR. pose proof (R_svc _ _ _ _ _ HR) as Hsvc.
  pose proof (budget_pend ms m Hbud Hh Hnl Hsvc Hstep) as Hbud1.
  assert (Hargs : mmap_na_args (ms_pend ms) (to_Z len)).
  { unfold mmap_na_args. repeat split; assumption. }
  destruct (ledger_inv_params_nonneg _ _ _ _ _ Hli) as [Hc0 HS0].
  unfold na_fits in Hfit. rename Hfit into Hpig.
  apply Z.leb_le in Hpig. rewrite HnZ in Hpig.
  assert (Hpig' : page_size + (live_bytes R0 + fl_S L) + (Z.of_nat (length R0) + fl_c L) * (nZ + page_size) + nZ
                  <= alloc_lo_bound).
  { rewrite alloc_lo_bound_val. unfold page_size.
    assert ((Z.of_nat (length R0) + fl_c L) * (nZ + 4096) <= (Rc + fl_c L) * (nZ + 4096))
      by (apply Z.mul_le_mono_nonneg_r; lia).
    lia. }
  fold nZ in Ha. eexists. split; [reflexivity|]. fold nZi nZ.
  assert (Hstepa : sstep_cfg segs cfg (mkCfg (ms_pend ms) m) []
            (SNext (mkCfg (sysret (ms_pend ms) a (apply_unmaps (ms_mem (ms_pend ms)) [(a, Z_to_bv 64 nZ)]))
                          (mmap_na_model a nZ m)))).
  { apply (mmap_na_step_iff cfg segs (ms_pend ms) _ m (to_Z len) Halloc Hh (proj1 Hnl)
             (ms_pend_svc ms) Hx8 Hargs (ex_intro _ a Ha)).
    exists a. repeat split. exact Ha. }
  pose proof Ha as Hg. apply mmap_grant_na_b_iff in Hg as (Hal & Hapos & Hatop & Hfree).
  destruct (ledger_inv_alloc_top _ _ _ _ _ Hli) as [_ Htop].
  unfold page_size in Hal. unfold TASK_SIZE in Htop.
  assert (Hsep : sep_from rho (f_mem F) (bv_unsigned a) (bv_unsigned a + to_Z nZi)).
  { rewrite HnZ. apply (sep_from_free rho (f_mem F) (m_vmmaps m) a nZ Hcov); [lia | exact Hatop | exact Hfree]. }
  pose proof (fx_grant_na_sound segs IM n rho F ms a nZi HRn Hat Hn0 Hn61 Hlt
                ltac:(lia) ltac:(rewrite HnZ; exact HnZmod) Hal Hapos ltac:(lia) ltac:(lia) Hsep) as HRn'.
  rewrite HnZ in HRn'.
  set (rho' := rho_upd rho n a) in *.
  set (M' := iset n (RG 0 nZi 12 None iempty grant_clo (grant_chi nZi)) (f_mem F)).
  assert (HM' : f_mem (fx_grant_na F n nZi) = M') by reflexivity.
  assert (Hmaps : vm_maps (m_vmmaps (mmap_na_model a nZ m)) = (a, Z_to_bv 64 nZ) :: vm_maps (m_vmmaps m))
    by reflexivity.
  assert (Hnacc : vm_noaccess (m_vmmaps (mmap_na_model a nZ m)) = (a, Z_to_bv 64 nZ) :: vm_noaccess (m_vmmaps m))
    by reflexivity.
  assert (Hother : forall t rg, iget t (f_mem F) = Some rg -> rho' t = rho t /\ iget t M' = Some rg).
  { intros t rg Hgt. split; [exact (regions_lt_rho rho n a _ _ _ Hlt Hgt)|].
    unfold M'. rewrite iget_iset_other; [exact Hgt|]. intros ->. pose proof (Hlt _ _ Hgt). lia. }
  split; [exact Hstepa|].
  split.
  2:{ constructor.
      - rewrite (to_Z_succ61 n Hn61). lia.
      - intros t Ht. unfold rho'. apply rho_upd_other. apply lt_neq. exact Ht.
      - rewrite sysret_fregs. reflexivity.
      - rewrite sysret_fcsr. reflexivity.
      - rewrite sysret_rom. reflexivity.
      - repeat split; reflexivity.
      - reflexivity.
      - intros x Hx Hno. split.
        + rewrite sysret_mem, apply_unmaps_one. rewrite u64_lit by lia.
          replace ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + nZ)) with false
            by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
          reflexivity.
        + rewrite HM'. intros t rg Hgt Hxin. unfold M' in Hgt. rewrite iget_iset in Hgt.
          destruct (t =? n)%uint63 eqn:E.
          * apply Uint63.eqb_spec in E. subst t. injection Hgt as <-. unfold in_ival in Hxin.
            cbn [rg_lo rg_len] in Hxin. unfold rho' in Hxin. rewrite rho_upd_same, to_Z_0, HnZ in Hxin. lia.
          * apply (Hno t rg Hgt). exact (in_ival_rho rho rho' t rg _ (proj1 (Hother t rg Hgt)) Hxin).
      - reflexivity.
      - reflexivity.
      - intros _ [E1 E2]. destruct Hmir as (Hm1 & Hm2 & _).
        assert (Ehd : den rho' (n, 0%uint63, nZi) = (a, Z_to_bv 64 nZ)).
        { cbn [den]. rewrite to_Z_0, adr_0. unfold rho'. rewrite rho_upd_same, HnZ. reflexivity. }
        split.
        + cbn [fl_maps map]. rewrite Hmaps, E1, Ehd. f_equal.
          symmetry. exact (map_den_regions rho rho' _ _ _ (fun t rg Hgt => proj1 (Hother t rg Hgt)) Hm1).
        + cbn [fl_na map]. rewrite Hnacc, E2, Ehd. f_equal.
          symmetry. exact (map_den_regions rho rho' _ _ _ (fun t rg Hgt => proj1 (Hother t rg Hgt)) Hm2). }
  split; [exact HRn'|].
  split. { unfold rho'. rewrite rho_upd_other; [exact H0|]. intros E. rewrite <- E, to_Z_0 in Hn0. lia. }
  split; [exact Hh|]. split; [apply model_nolazy_with_vmmaps; exact Hnl|].
  split; [cbn [fl_c fl_S]; rewrite HnZ; exact (mmap_na_inv R0 Lim (fl_c L) (fl_S L) m a (to_Z len) Hli Hpos Ha)|].
  split.
  { (* [comment removed for export] *)
    rewrite HM'. intros t rg Hgt. unfold M' in Hgt. rewrite iget_iset in Hgt.
    destruct (t =? n)%uint63 eqn:E.
    - apply Uint63.eqb_spec in E. subst t. injection Hgt as <-. cbn [rg_lo rg_len].
      rewrite to_Z_0. split; [lia|]. intros x Hx. unfold in_ival in Hx. cbn [rg_lo rg_len] in Hx.
      unfold rho' in Hx. rewrite rho_upd_same, to_Z_0, HnZ in Hx.
      left. exists (a, Z_to_bv 64 nZ). split.
      + apply in_app_iff. right. rewrite Hmaps. left. reflexivity.
      + unfold e_hi, e_lo, e_sz. cbn [fst snd]. rewrite u64_lit by lia. lia.
    - destruct (Hcov t rg Hgt) as [Hne Hb]. split; [exact Hne|]. intros x Hx.
      apply (covered_mono (m_vmmaps m)); [reflexivity | reflexivity | | ].
      + intros p Hp. rewrite Hmaps. right. exact Hp.
      + apply Hb. exact (in_ival_rho rho rho' t rg x (proj1 (Hother t rg Hgt)) Hx). }
  split.
  { (* [comment removed for export] *)
    rewrite HM'. destruct Hmir as (Hm1 & Hm2 & rgb & Hgb & Hbrk). split; [|split].
    - cbn [fl_maps]. constructor.
      + exists (RG 0 nZi 12 None iempty grant_clo (grant_chi nZi)). unfold M'. rewrite iget_iset_same. cbn [rg_lo rg_len].
        rewrite to_Z_0. split; [reflexivity|]. split; [lia|]. split; [lia|].
        rewrite Hmaps. left. rewrite adr_0. unfold rho'. rewrite rho_upd_same, HnZ. reflexivity.
      + eapply Forall_impl; [|exact Hm1]. intros e He.
        destruct (ent_ok_tag _ _ _ _ He) as [rg Hrg]. destruct (Hother _ _ Hrg) as [Er Eg].
        apply (ent_ok_ext rho rho' (f_mem F) M' (vm_maps (m_vmmaps m))); try assumption.
        * rewrite Eg, Hrg. reflexivity.
        * intros p Hp. rewrite Hmaps. right. exact Hp.
    - cbn [fl_na]. constructor.
      + exists (RG 0 nZi 12 None iempty grant_clo (grant_chi nZi)). unfold M'. rewrite iget_iset_same. cbn [rg_lo rg_len].
        rewrite to_Z_0. split; [reflexivity|]. split; [lia|]. split; [lia|].
        rewrite Hnacc. left. rewrite adr_0. unfold rho'. rewrite rho_upd_same, HnZ. reflexivity.
      + eapply Forall_impl; [|exact Hm2]. intros e He.
        destruct (ent_ok_tag _ _ _ _ He) as [rg Hrg]. destruct (Hother _ _ Hrg) as [Er Eg].
        apply (ent_ok_ext rho rho' (f_mem F) M' (vm_noaccess (m_vmmaps m))); try assumption.
        * rewrite Eg, Hrg. reflexivity.
        * intros p Hp. rewrite Hnacc. right. exact Hp.
    - cbn [fl_brk]. destruct (Hother _ _ Hgb) as [Er Eg]. exists rgb. split; [exact Eg|].
      rewrite (adr_rho rho rho' _ _ Er). exact Hbrk. }
  split; [exact (budget_step _ _ _ _ _ Hbud1 Hstepa)|].
  split.
  { apply (XI_rho rho rho'); [|apply (XI_vm rho m); [repeat split; reflexivity | exact HXI]].
    intros tx Htx. unfold rho'. apply rho_upd_other. apply lt_neq. exact (Hxt tx Htx). }
  split; [intros tx Htx; rewrite (to_Z_succ61 n Hn61); pose proof (Hxt tx Htx); lia|].
  (* [comment removed for export] *)
  rewrite HM'. intros t Ht. destruct (Hfr t Ht) as [Hpr Hmem].
  destruct Hpr as (Hne0 & rgt & Hgt & Hpr2). destruct (Hother _ _ Hgt) as [Er Eg].
  split; [split; [exact Hne0 | exists rgt; split; [exact Eg | exact Hpr2]]|].
  intros rg x Hgx Hx. rewrite Eg in Hgx. injection Hgx as <-.
  apply (in_ival_rho rho rho' t rgt _ Er) in Hx.
  rewrite sysret_mem, apply_unmaps_one.
  destruct (Hsep t rgt Hgt) as [Hs|Hs]; unfold rg_ival in Hs; cbn [fst snd] in Hs;
    unfold in_ival in Hx; rewrite ?HnZ in Hs; rewrite u64_lit by lia.
  - replace ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + nZ)) with false
      by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
    exact (Hmem rgt x Hgt Hx).
  - replace ((bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + nZ)) with false
      by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    exact (Hmem rgt x Hgt Hx).
Qed.

Lemma sys_grant_na_soundX n rho F L ms m len res :
  sys_grant_na Rb Rc F L n len = Some res ->
  DInv n rho F L ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 222 ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  bv_unsigned (ms_gpr (ms_pend ms) 2) = 0 ->
  bv_unsigned (ms_gpr (ms_pend ms) 3) = 34 ->
  bv_unsigned (ms_gpr (ms_pend ms) 5) = 0 ->
  sys_okX n rho F L res ms m.
Proof.
  intros Hsys HD Hat Hstep Hx8 Ha1 Ha2 Ha3 Ha5. pose proof Hsys as Hsys0.
  pose proof HD as (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfr).
  unfold sys_grant_na in Hsys. cbv zeta in Hsys.
  destruct ((0 <? len)%uint63 && (len <=? 4611686018427387904)%uint63
            && (pg_up len <=? 4611686018427387904)%uint63 && tag_ok F n
            && na_fits Rb Rc L (to_Z (pg_up len))) eqn:Hchk; [|discriminate].
  clear Hsys.
  apply andb_true_iff in Hchk as [Hchk Hfit]. apply andb_true_iff in Hchk as [Hchk Htag].
  apply andb_true_iff in Hchk as [Hchk Hup]. apply andb_true_iff in Hchk as [Hpos Hle].
  apply ltb_spec in Hpos. apply leb_spec in Hle, Hup. rewrite to_Z_0 in Hpos.
  change (to_Z 4611686018427387904) with (2 ^ 62) in Hle, Hup.
  pose proof (pg_up_spec len Hle) as HnZ.
  set (nZi := pg_up len) in *. set (nZ := page_round_up_Z (to_Z len)) in *.
  assert (HnZpos : 0 < nZ) by (apply page_round_up_Z_pos; exact Hpos).
  assert (HnZmod : nZ mod 4096 = 0) by (apply page_round_up_Z_mod).
  unfold tag_ok in Htag. apply andb_true_iff in Htag as [Htag Hlt].
  apply andb_true_iff in Htag as [Hn0 Hn61]. apply ltb_spec in Hn0, Hn61. rewrite to_Z_0 in Hn0.
  change (to_Z 1152921504606846976) with (2 ^ 60) in Hn61.
  apply regions_lt_b_ok in Hlt.
  pose proof (Rn_R _ _ _ _ HRn H0) as HR. pose proof (R_svc _ _ _ _ _ HR) as Hsvc.
  pose proof (budget_pend ms m Hbud Hh Hnl Hsvc Hstep) as Hbud1.
  assert (Hargs : mmap_na_args (ms_pend ms) (to_Z len)).
  { unfold mmap_na_args. repeat split; assumption. }
  destruct (ledger_inv_params_nonneg _ _ _ _ _ Hli) as [Hc0 HS0].
  unfold na_fits in Hfit. rename Hfit into Hpig.
  apply Z.leb_le in Hpig. rewrite HnZ in Hpig.
  assert (Hpig' : page_size + (live_bytes R0 + fl_S L) + (Z.of_nat (length R0) + fl_c L) * (nZ + page_size) + nZ
                  <= alloc_lo_bound).
  { rewrite alloc_lo_bound_val. unfold page_size.
    assert ((Z.of_nat (length R0) + fl_c L) * (nZ + 4096) <= (Rc + fl_c L) * (nZ + 4096))
      by (apply Z.mul_le_mono_nonneg_r; lia).
    lia. }
  assert (Hex : exists a, mmap_grant_na_b (m_vmmaps m) a nZ = true).
  { exact (mmap_grant_na_exists_inv R0 Lim (fl_c L) (fl_S L) (m_vmmaps m) nZ Hli ltac:(lia) Hpig'). }
  pose proof (mmap_na_step_iff cfg segs (ms_pend ms) _ m (to_Z len) Halloc Hh (proj1 Hnl)
                (ms_pend_svc ms) Hx8 Hargs Hex) as Hiff. cbv zeta in Hiff. fold nZ in Hiff.
  destruct Hex as [a0 Ha0].
  exists {a : word | mmap_grant_na_b (m_vmmaps m) a nZ = true}, (exist _ a0 Ha0),
    (fun i => mkCfg (sysret (ms_pend ms) (proj1_sig i)
                       (apply_unmaps (ms_mem (ms_pend ms)) [(proj1_sig i, Z_to_bv 64 nZ)]))
                    (mmap_na_model (proj1_sig i) nZ m)).
  split.
  { intros e st. rewrite Hiff. split.
    - intros (a & Ha & -> & ->). exists (exist _ a Ha). split; reflexivity.
    - intros ([a Ha] & -> & ->). exists a. repeat split. exact Ha. }
  intros [a Ha]. cbn [proj1_sig].
  destruct (sys_grant_na_succ n rho F L ms m len _ a Hsys0 HD Hat Hstep Hx8 Ha1 Ha2 Ha3 Ha5 Ha)
    as (L' & E & _ & HD' & Hne).
  eexists (fx_grant_na F n (pg_up len)), L', (n + 1)%uint63, (rho_upd rho n a), _, _, 0%nat.
  cbn [cfg_ms cfg_model rsteps]. rewrite E. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact HD' | exact Hne].
Qed.

Lemma sys_grant_na_sound n rho F L ms m len res :
  sys_grant_na Rb Rc F L n len = Some res ->
  DInv n rho F L ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 222 ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  bv_unsigned (ms_gpr (ms_pend ms) 2) = 0 ->
  bv_unsigned (ms_gpr (ms_pend ms) 3) = 34 ->
  bv_unsigned (ms_gpr (ms_pend ms) 5) = 0 ->
  sys_ok res ms m.
Proof.
  intros. eapply sys_okX_ok. eapply sys_grant_na_soundX; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma upd_region_get M t f t' :
  iget t' (upd_region M t f) =
  if (t' =? t)%uint63 then option_map f (iget t M) else iget t' M.
Proof.
  unfold upd_region. destruct (iget t M) as [rg|] eqn:E.
  - rewrite iget_iset. destruct (t' =? t)%uint63; reflexivity.
  - destruct (t' =? t)%uint63 eqn:E'; [|reflexivity].
    apply Uint63.eqb_spec in E'. subst t'. rewrite E. reflexivity.
Qed.

Lemma upd_region_shape M t (f : region -> region) :
  (forall rg, rg_lo (f rg) = rg_lo rg /\ rg_len (f rg) = rg_len rg /\ rg_align (f rg) = rg_align rg
              /\ rg_dflt (f rg) = rg_dflt rg) ->
  same_shape M (upd_region M t f).
Proof.
  intros Hf t'. rewrite upd_region_get. destruct (t' =? t)%uint63 eqn:E.
  - apply Uint63.eqb_spec in E. subst t'. destruct (iget t M) as [rg|]; cbn [option_map]; [apply Hf | exact I].
  - destruct (iget t' M); [repeat split; reflexivity | exact I].
Qed.

Lemma lsr12_mul (x : int) : to_Z (x land 4095)%uint63 = 0 -> to_Z (x >> 12)%uint63 * 4096 = to_Z x.
Proof.
  rewrite to_Z_land4095, to_Z_lsr12. intros H.
  pose proof (Z.div_mod (to_Z x) 4096 ltac:(lia)) as Hdm. rewrite H in Hdm.
  generalize dependent (to_Z x / 4096). intros q Hq. lia.
Qed.

Lemma pages_of_nat (z : Z) :
  0 < z -> z mod 4096 = 0 ->
  Z.of_nat (Z.to_nat (z / 4096)) * 4096 = z /\ (0 < Z.to_nat (z / 4096))%nat.
Proof.
  intros Hz Hm. pose proof (Z.div_mod z 4096 ltac:(lia)) as Hdm. rewrite Hm in Hdm.
  generalize dependent (z / 4096). intros q Hq. split; lia.
Qed.

Lemma align_4096 (x al : Z) : 12 <= al -> x mod 2 ^ al = 0 -> x mod 4096 = 0.
Proof.
  intros Hal Hx. apply Z.mod_divide in Hx; [|apply Z.pow_nonzero; lia].
  apply Z.mod_divide; [lia|]. eapply Z.divide_trans; [|exact Hx].
  exists (2 ^ (al - 12)). change 4096 with (2 ^ 12). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma node_ext_repage n rho F L ms m F' L' ms' m' t rg :
  iget t (f_mem F) = Some rg ->
  same_shape (f_mem F) (f_mem F') ->
  same_but_vm m m' -> vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m) ->
  ms_fregs ms' = ms_fregs ms -> ms_fcsr ms' = ms_fcsr ms -> ms_rom ms' = ms_rom ms ->
  (forall x, ~ in_ival rho t rg (bv_unsigned x) -> ms_mem ms' x = ms_mem ms x) ->
  vm_start_brk (m_vmmaps m') = vm_start_brk (m_vmmaps m) ->
  vm_mmap_base (m_vmmaps m') = vm_mmap_base (m_vmmaps m) ->
  (DInv n rho F L ms m -> exact rho L (m_vmmaps m) -> exact rho L' (m_vmmaps m')) ->
  node_ext n rho F L ms m n rho F' L' ms' m'.
Proof.
  intros Hg Hshape Hvm Hsp Hfr Hfc Hrom Hmem Hsb Hmb Hex. constructor; try assumption.
  - lia.
  - intros; reflexivity.
  - intros x _ Hno. split; [apply Hmem; exact (Hno t rg Hg)|].
    intros t' rg' Hg' Hx. destruct (same_shape_get _ _ _ _ Hshape Hg') as (rg0 & Hg0 & E1 & E2).
    apply (Hno t' rg0 Hg0). unfold in_ival in *. rewrite <- E1, <- E2. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma range_ok_sound F n t off len :
  range_ok keep F n t off len = true ->
  exists rg, iget t (f_mem F) = Some rg /\ to_Z t < to_Z n /\ ~ In t keep
    /\ 0 < to_Z len <= 2 ^ 62 /\ to_Z off < 2 ^ 62
    /\ to_Z off + page_round_up_Z (to_Z len) < 2 ^ 62
    /\ to_Z (off + pg_up len)%uint63 = to_Z off + page_round_up_Z (to_Z len)
    /\ to_Z (off land 4095)%uint63 = 0 /\ 12 <= to_Z (rg_align rg).
Proof.
  unfold range_ok. destruct (iget t (f_mem F)) as [rg|]; [|discriminate]. intros H.
  repeat match type of H with (_ && _ = true) =>
    let H' := fresh "Hc" in apply andb_true_iff in H as [H H'] end.
  exists rg. split; [reflexivity|].
  apply ltb_spec in H. apply negb_true_iff in Hc6. apply mem_int_false in Hc6.
  apply ltb_spec in Hc5. rewrite to_Z_0 in Hc5. apply leb_spec in Hc4. apply ltb_spec in Hc3, Hc2.
  change (to_Z 4611686018427387904) with (2 ^ 62) in *.
  change (to_Z 2305843009213693952) with (2 ^ 61) in *.
  apply Uint63.eqb_spec in Hc1. apply (f_equal to_Z) in Hc1. rewrite to_Z_0 in Hc1.
  apply leb_spec in Hc0. change (to_Z 12) with 12 in Hc0.
  pose proof (pg_up_spec len ltac:(lia)) as Hup.
  pose proof (page_round_up_Z_lt (to_Z len)) as Hlt. unfold page_size in Hlt.
  pose proof (page_round_up_Z_ge (to_Z len)) as Hge.
  pose proof (i63_range off) as Hoff.
  assert (Hadd : to_Z (off + pg_up len)%uint63 = to_Z off + page_round_up_Z (to_Z len)).
  { rewrite add_spec, i63_wB, Hup. apply Z.mod_small. lia. }
  rewrite Hadd in Hc2. repeat split; try assumption; lia.
Qed.

Lemma find_some_In {A} (f : A -> bool) l x : List.find f l = Some x -> In x l /\ f x = true.
Proof. apply find_some. Qed.

(* [comment removed for export] *)
Lemma ent_covers_sound rho M l t off sz e :
  ent_covers t off sz e = true -> ent_ok rho M l e ->
  (forall rg, iget t M = Some rg -> to_Z (rg_len rg) <= 2 ^ 62) ->
  to_Z off + to_Z sz < 2 ^ 63 ->
  exists eo el rg, e = (t, eo, el) /\ iget t M = Some rg
    /\ to_Z (rg_lo rg) <= to_Z eo /\ to_Z eo <= to_Z off
    /\ to_Z off + to_Z sz <= to_Z eo + to_Z el /\ to_Z eo + to_Z el <= to_Z (rg_len rg)
    /\ In (adr rho t (to_Z eo), Z_to_bv 64 (to_Z el)) l.
Proof.
  destruct e as [[t' eo] el]. cbn [ent_covers]. intros H (rg & Hg & H1 & H2 & H3) Hlen Hsum.
  apply andb_true_iff in H as [H Hb]. apply andb_true_iff in H as [Ht Ha].
  apply Uint63.eqb_spec in Ht. subst t'. apply leb_spec in Ha, Hb.
  pose proof (Hlen rg Hg) as Hl62. pose proof (i63_range eo). pose proof (i63_range el).
  pose proof (i63_range off). pose proof (i63_range sz).
  rewrite !add_spec, i63_wB in Hb.
  rewrite (Z.mod_small (to_Z off + to_Z sz)) in Hb by lia.
  rewrite (Z.mod_small (to_Z eo + to_Z el)) in Hb by lia.
  exists eo, el, rg. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma DInv_repage n rho F L ms m F' na' ms' m' t rg :
  DInv n rho F L ms m ->
  iget t (f_mem F) = Some rg -> ~ In t keep ->
  Rn n rho F' ms' ->
  same_shape (f_mem F) (f_mem F') ->
  (forall t', t' <> t -> iget t' (f_mem F') = iget t' (f_mem F)) ->
  m_halted m' = None -> model_nolazy m' ->
  ledger_inv R0 Lim (fl_c L) (fl_S L) (m_vmmaps m') ->
  vm_reserved (m_vmmaps m') = vm_reserved (m_vmmaps m) ->
  vm_maps (m_vmmaps m') = vm_maps (m_vmmaps m) ->
  vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m) ->
  vm_brk (m_vmmaps m') = vm_brk (m_vmmaps m) ->
  Forall (ent_ok rho (f_mem F') (vm_noaccess (m_vmmaps m'))) na' ->
  budget ms' m' -> same_but_vm m m' ->
  (forall x, ~ in_ival rho t rg (bv_unsigned x) -> ms_mem ms' x = ms_mem ms x) ->
  DInv n rho F' (FL (fl_maps L) na' (fl_brk L) (fl_c L) (fl_S L)) ms' m'.
Proof.
  intros (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfr) Hg Hnk HRn' Hshape Hother
         Hh' Hnl' Hli' HR HM Hsp Hbrk Hna Hbud' Hcreds Hmem.
  pose proof (Rn_R _ _ _ _ HRn H0) as HR0.
  split; [exact HRn'|]. split; [exact H0|]. split; [exact Hh'|]. split; [exact Hnl'|].
  split; [exact Hli'|]. split.
  { intros t' rg' Hg'. destruct (regions_covered_shape _ _ _ _ Hshape Hcov t' rg' Hg') as [Hne Hb].
    split; [exact Hne|]. intros x Hx.
    apply (covered_mono (m_vmmaps m)); [exact HR | exact Hsp | | exact (Hb x Hx)].
    intros p Hp. rewrite HM. exact Hp. }
  split.
  { destruct Hmir as (Hm1 & _ & rgb & Hgb & Hb). split; [|split].
    - cbn [fl_maps]. rewrite HM. eapply Forall_impl; [|exact Hm1]. intros e. apply ent_ok_shape. exact Hshape.
    - exact Hna.
    - cbn [fl_brk]. destruct (same_shape_get' _ _ _ _ Hshape Hgb) as (rg' & Hg' & _ & E2).
      exists rg'. split; [exact Hg'|]. rewrite E2, Hbrk. exact Hb. }
  split; [exact Hbud'|]. split; [exact (XI_vm rho m m' Hcreds HXI)|]. split; [exact Hxt|].
  intros tk Htk. destruct (Hfr tk Htk) as [Hpr Hm0].
  assert (Hnek : tk <> t) by (intros ->; contradiction).
  split; [exact (pristine_eq _ _ _ (Hother tk Hnek) Hpr)|].
  intros rgk x Hgk Hx. rewrite (Hother tk Hnek) in Hgk. rewrite Hmem; [exact (Hm0 rgk x Hgk Hx)|].
  intros Hxin. exact (ival_disjoint rho (f_mem F) tk t rgk rg _ (R_regions_sep _ _ _ HR0) Hnek Hgk Hg Hx Hxin).
Qed.

Lemma mod4096_add a b : a mod 4096 = 0 -> b mod 4096 = 0 -> (a + b) mod 4096 = 0.
Proof. intros Ha Hb. rewrite Z.add_mod, Ha, Hb by lia. reflexivity. Qed.

Lemma adr_as_Z rho t z : adr rho t z = Z_to_bv 64 (bv_unsigned (rho t) + z).
Proof.
  unfold adr. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  apply Zplus_mod_idemp_r.
Qed.

Lemma maps_subtract_piece : forall l lo hi q x,
  In q l -> In x (iv_subtract (fst q) (snd q) lo hi) -> In x (maps_subtract l lo hi).
Proof.
  induction l as [|[a sz] r IH]; intros lo hi q x Hq Hx; [contradiction|].
  cbn [maps_subtract]. apply in_app_iff. destruct Hq as [<- | Hq].
  - left. exact Hx.
  - right. exact (IH lo hi q x Hq Hx).
Qed.

(* [comment removed for export] *)
Lemma ent_sub_den rho (M : itrie region) t off sz rg e :
  (forall t' rg', iget t' M = Some rg' -> region_ok rho t' rg') -> regions_sep rho M ->
  iget t M = Some rg ->
  to_Z (rg_lo rg) <= to_Z off -> to_Z off + to_Z sz <= to_Z (rg_len rg) ->
  ent_in M e -> 0 < e_sz (den rho e) ->
  map (den rho) (ent_sub t off sz e)
  = iv_subtract (fst (den rho e)) (snd (den rho e))
      (bv_unsigned (rho t) + to_Z off) (bv_unsigned (rho t) + to_Z off + to_Z sz)
  /\ forall e', In e' (ent_sub t off sz e) -> ent_in M e'.
Proof.
  intros Hreg Hsep Hg Hlo Hhi. destruct e as [[t' eo] el]. intros (rg' & Hg' & Hb1 & Hb2) Hpos.
  pose proof (Hreg _ _ Hg') as Hok'. pose proof (region_ok_nowrap _ _ _ Hok') as Hnw'.
  pose proof (i63_range eo) as Heo. pose proof (i63_range el) as Hel.
  pose proof (i63_range off) as Hoff. pose proof (i63_range sz) as Hsz.
  pose proof (u64_range (rho t')) as Hrt'.
  assert (Ea : bv_unsigned (adr rho t' (to_Z eo)) = bv_unsigned (rho t') + to_Z eo)
    by (apply adr_unsigned; lia).
  assert (Es : bv_unsigned (Z_to_bv 64 (to_Z el)) = to_Z el) by (apply u64_lit; lia).
  unfold e_sz in Hpos. cbn [den fst snd] in *. rewrite Es in Hpos.
  unfold ent_sub. destruct (t' =? t)%uint63 eqn:Et; cbn [negb].
  2:{ (* [comment removed for export] *)
    apply eqb_false_spec in Et. split.
    - cbn [map den]. symmetry. apply iv_subtract_disj; [lia | rewrite Es; exact Hpos |].
      rewrite Ea, Es. destruct (Hsep t' t rg' rg Et Hg' Hg) as [Hd|Hd]; [left | right]; lia.
    - intros e' [<- | []]. exists rg'. repeat split; assumption. }
  apply Uint63.eqb_spec in Et. subst t'. rewrite Hg in Hg'. injection Hg' as <-.
  destruct Hok' as (_ & Hl62 & _).
  assert (Eos : to_Z (off + sz)%uint63 = to_Z off + to_Z sz)
    by (rewrite add_spec, i63_wB; apply Z.mod_small; lia).
  assert (Eel : to_Z (eo + el)%uint63 = to_Z eo + to_Z el)
    by (rewrite add_spec, i63_wB; apply Z.mod_small; lia).
  unfold iv_subtract. cbn zeta. rewrite Ea, Es.
  assert (Emx : to_Z (if (eo <? off + sz)%uint63 then (off + sz)%uint63 else eo)
                = Z.max (to_Z eo) (to_Z off + to_Z sz)).
  { destruct (ltbP eo (off + sz)%uint63) as [E2|E2]; rewrite Eos in E2; lia. }
  assert (Emn : to_Z eo < to_Z off ->
                to_Z (if (el <? off - eo)%uint63 then el else (off - eo)%uint63)
                = Z.min (to_Z el) (to_Z off - to_Z eo)).
  { intros E1. assert (Esub : to_Z (off - eo)%uint63 = to_Z off - to_Z eo) by (apply i63_sub_small; lia).
    destruct (ltbP el (off - eo)%uint63) as [E2|E2]; rewrite Esub in E2; lia. }
  split.
  - rewrite map_app. f_equal.
    + destruct (ltbP eo off) as [E1|E1].
      * rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [map den]. rewrite (Emn E1). do 3 f_equal. lia.
      * rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
    + destruct (ltbP (off + sz)%uint63 (eo + el)%uint63) as [E1|E1]; rewrite Eos, Eel in E1.
      * rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn zeta. cbn [map den].
        set (mx := if (eo <? off + sz)%uint63 then (off + sz)%uint63 else eo) in *.
        assert (Esub : to_Z (eo + el - mx)%uint63 = to_Z eo + to_Z el - to_Z mx)
          by (rewrite i63_sub_small; lia).
        rewrite adr_as_Z, Esub, Emx. do 2 f_equal; f_equal; lia.
      * rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
  - intros e' He'. apply in_app_iff in He' as [He'|He'].
    + destruct (ltbP eo off) as [E1|E1]; [|contradiction]. destruct He' as [<- | []].
      exists rg. split; [exact Hg|]. split; [exact Hb1|]. rewrite (Emn E1). lia.
    + destruct (ltbP (off + sz)%uint63 (eo + el)%uint63) as [E1|E1]; [|contradiction].
      rewrite Eos, Eel in E1. destruct He' as [<- | []].
      cbn zeta. set (mx := if (eo <? off + sz)%uint63 then (off + sz)%uint63 else eo) in *.
      assert (Esub : to_Z (eo + el - mx)%uint63 = to_Z eo + to_Z el - to_Z mx)
        by (rewrite i63_sub_small; lia).
      exists rg. split; [exact Hg|]. rewrite Esub, Emx. split; lia.
Qed.

(* [comment removed for export] *)
Lemma fl_sub_mirror rho (M M' : itrie region) l t off sz rg na :
  (forall t' rg', iget t' M = Some rg' -> region_ok rho t' rg') -> regions_sep rho M ->
  iget t M = Some rg ->
  to_Z (rg_lo rg) <= to_Z off -> to_Z off + to_Z sz <= to_Z (rg_len rg) ->
  same_shape M M' ->
  Forall (fun q => 0 < e_sz q) l ->
  Forall (ent_ok rho M l) na ->
  Forall (ent_ok rho M' (maps_subtract l (bv_unsigned (rho t) + to_Z off)
                                         (bv_unsigned (rho t) + to_Z off + to_Z sz)))
         (fl_sub t off sz na).
Proof.
  intros Hreg Hsep Hg Hlo Hhi Hshape Hpos Hna. apply Forall_forall. intros e' He'.
  unfold fl_sub in He'. apply in_flat_map in He' as (e & He & He').
  pose proof (proj1 (Forall_forall _ _) Hna e He) as Hok. apply ent_ok_iff in Hok as [Hin Hden].
  pose proof (proj1 (Forall_forall _ _) Hpos _ Hden) as Hp.
  destruct (ent_sub_den rho M t off sz rg e Hreg Hsep Hg Hlo Hhi Hin Hp) as [Hmap Hpieces].
  apply ent_ok_iff. split; [exact (ent_in_shape _ _ _ Hshape (Hpieces e' He'))|].
  apply (maps_subtract_piece _ _ _ (den rho e) _ Hden). rewrite <- Hmap. apply in_map. exact He'.
Qed.

(* [comment removed for export] *)
Lemma fl_sub_exact rho (M : itrie region) l t off sz rg na :
  (forall t' rg', iget t' M = Some rg' -> region_ok rho t' rg') -> regions_sep rho M ->
  iget t M = Some rg ->
  to_Z (rg_lo rg) <= to_Z off -> to_Z off + to_Z sz <= to_Z (rg_len rg) ->
  Forall (fun q => 0 < e_sz q) l ->
  Forall (ent_ok rho M l) na ->
  map (den rho) (fl_sub t off sz na)
  = maps_subtract (map (den rho) na) (bv_unsigned (rho t) + to_Z off)
                                     (bv_unsigned (rho t) + to_Z off + to_Z sz).
Proof.
  intros Hreg Hsep Hg Hlo Hhi Hpos Hna. apply map_den_fl_sub. intros e He.
  pose proof (proj1 (Forall_forall _ _) Hna e He) as Hok. apply ent_ok_iff in Hok as [Hin Hden].
  pose proof (proj1 (Forall_forall _ _) Hpos _ Hden) as Hp.
  exact (proj1 (ent_sub_den rho M t off sz rg e Hreg Hsep Hg Hlo Hhi Hin Hp)).
Qed.

(* [comment removed for export] *)
Record range_facts (rho : int -> word) (F : fstate) (n t off len : int) (rg : region) : Prop := {
  rf_get   : iget t (f_mem F) = Some rg;
  rf_lt    : to_Z t < to_Z n;
  rf_keep  : ~ In t keep;
  rf_len   : 0 < to_Z len <= 2 ^ 62;
  rf_nZ    : to_Z (pg_up len) = page_round_up_Z (to_Z len);
  rf_sum   : to_Z off + page_round_up_Z (to_Z len) < 2 ^ 62;
  rf_add   : to_Z (off + pg_up len)%uint63 = to_Z off + page_round_up_Z (to_Z len);
  rf_pn    : to_Z (off >> 12)%uint63 * 4096 = to_Z off;
  rf_k     : Z.of_nat (Z.to_nat (to_Z (pg_up len >> 12)%uint63)) * 4096 = page_round_up_Z (to_Z len);
  rf_kpos  : (0 < Z.to_nat (to_Z (pg_up len >> 12)%uint63))%nat;
  rf_al    : 12 <= to_Z (rg_align rg);
  rf_offal : to_Z off mod 4096 = 0
}.

Lemma range_facts_of rho F n t off len :
  range_ok keep F n t off len = true -> exists rg, range_facts rho F n t off len rg.
Proof.
  intros H. destruct (range_ok_sound F n t off len H)
    as (rg & Hg & Hlt & Hnk & Hlen & Hoff & Hsum & Hadd & Hal0 & Halign).
  exists rg. pose proof (pg_up_spec len (proj2 Hlen)) as HnZ.
  assert (Hpos : 0 < page_round_up_Z (to_Z len)) by (apply page_round_up_Z_pos; lia).
  pose proof (page_round_up_Z_mod (to_Z len)) as Hmod. unfold page_size in Hmod.
  destruct (pages_of_nat _ Hpos Hmod) as [Hk Hkpos].
  constructor; try assumption.
  - exact (lsr12_mul off Hal0).
  - rewrite to_Z_lsr12, HnZ. exact Hk.
  - rewrite to_Z_lsr12, HnZ. exact Hkpos.
  - rewrite <- to_Z_land4095. exact Hal0.
Qed.

(* [comment removed for export] *)
Lemma range_addr rho F ms t off nZ eo el rg :
  R segs IM rho F ms -> iget t (f_mem F) = Some rg ->
  12 <= to_Z (rg_align rg) -> to_Z off mod 4096 = 0 ->
  to_Z (rg_lo rg) <= to_Z eo -> to_Z eo <= to_Z off -> 0 < nZ ->
  to_Z off + nZ <= to_Z eo + to_Z el -> to_Z eo + to_Z el <= to_Z (rg_len rg) ->
  bv_unsigned (adr rho t (to_Z off)) = bv_unsigned (rho t) + to_Z off
  /\ bv_unsigned (adr rho t (to_Z off)) mod 4096 = 0
  /\ bv_unsigned (adr rho t (to_Z off)) + nZ < 2 ^ 63
  /\ e_lo (adr rho t (to_Z eo), Z_to_bv 64 (to_Z el)) = bv_unsigned (rho t) + to_Z eo
  /\ e_hi (adr rho t (to_Z eo), Z_to_bv 64 (to_Z el)) = bv_unsigned (rho t) + to_Z eo + to_Z el.
Proof.
  intros HR Hg Hal Hoffal H1 H2 HnZ H3 H4.
  pose proof (R_region_ok _ _ _ _ _ HR Hg) as Hreg.
  pose proof (ent_range rho t eo el rg Hreg H1 H4) as Hrange.
  destruct Hreg as (_ & Hl62 & Hnw & _ & Halign & _).
  pose proof (align_4096 _ _ Hal Halign) as Hal4096. clear Halign.
  pose proof (i63_range off). pose proof (i63_range eo). pose proof (i63_range el). pose proof (u64 (rho t)).
  assert (Ha : bv_unsigned (adr rho t (to_Z off)) = bv_unsigned (rho t) + to_Z off)
    by (apply adr_unsigned; clear Hal4096 Hoffal; lia).
  split; [exact Ha|]. split.
  { rewrite Ha. apply mod4096_add; [exact Hal4096 | exact Hoffal]. }
  split; [clear Hal4096 Hoffal; lia|].
  exact Hrange.
Qed.

Lemma sys_guard_soundX n rho F L ms m t off len res :
  sys_guard keep F L n t off len = Some res ->
  DInv n rho F L ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 222 ->
  ms_gpr (ms_pend ms) 0 = adr rho t (to_Z off) ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  bv_unsigned (ms_gpr (ms_pend ms) 2) = 0 ->
  bv_unsigned (ms_gpr (ms_pend ms) 3) = 50 ->
  bv_unsigned (ms_gpr (ms_pend ms) 5) = 0 ->
  sys_okX n rho F L res ms m.
Proof.
  intros Hsys HD Hat Hstep Hx8 Ha0 Ha1 Ha2 Ha3 Ha5.
  pose proof HD as (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfr).
  unfold sys_guard in Hsys. cbv zeta in Hsys.
  destruct (range_ok keep F n t off len) eqn:Hrange; [|discriminate].
  destruct (List.find (ent_covers t off (pg_up len)) (fl_maps L)) as [e|] eqn:Hfind; [|discriminate].
  injection Hsys as <-.
  destruct (range_facts_of rho F n t off len Hrange) as [rg RF]. destruct RF.
  set (nZi := pg_up len) in *. set (nZ := page_round_up_Z (to_Z len)) in *.
  set (pn := (off >> 12)%uint63) in *. set (k := Z.to_nat (to_Z (nZi >> 12)%uint63)) in *.
  assert (HnZpos : 0 < nZ) by (apply page_round_up_Z_pos; lia).
  pose proof (Rn_R _ _ _ _ HRn H0) as HR. pose proof (R_svc _ _ _ _ _ HR) as Hsvc.
  pose proof (budget_pend ms m Hbud Hh Hnl Hsvc Hstep) as Hbud1.
  pose proof (R_regions_sep _ _ _ HR) as Hsep.
  assert (Hregs : forall t' rg', iget t' (f_mem F) = Some rg' -> region_ok rho t' rg')
    by (intros t' rg' Hg'; exact (R_region_ok _ _ _ _ _ HR Hg')).
  assert (Hposna : Forall (fun q => 0 < e_sz q) (vm_noaccess (m_vmmaps m))).
  { eapply Forall_impl; [|exact (li_noacc _ _ _ _ _ Hli)]. intros q0 [Hq0 _]. exact Hq0. }
  assert (Hl62 : forall t' rg', iget t' (f_mem F) = Some rg' -> to_Z (rg_len rg') <= 2 ^ 62).
  { intros t' rg' Hg'. exact (proj1 (proj2 (R_region_ok _ _ _ _ _ HR Hg'))). }
  destruct Hmir as (Hm1 & Hm2 & rgb & Hgb & Hbrk).
  apply find_some in Hfind as [HeIn Hecov].
  destruct (ent_covers_sound rho (f_mem F) _ t off nZi e Hecov
              (proj1 (Forall_forall _ _) Hm1 _ HeIn) (Hl62 t) ltac:(rewrite rf_nZ0; fold nZ; lia))
    as (eo & el & rg' & -> & Hg' & He1 & He2 & He3 & He4 & HpIn).
  rewrite rf_get0 in Hg'. injection Hg' as <-. rewrite rf_nZ0 in He3. fold nZ in He3.
  destruct (range_addr rho F ms t off nZ eo el rg HR rf_get0 rf_al0 rf_offal0 He1 He2 HnZpos He3 He4)
    as (Hau & Hamod & Ha63 & Eplo & Ephi).
  set (addr := adr rho t (to_Z off)) in *. set (p := (adr rho t (to_Z eo), Z_to_bv 64 (to_Z el))) in *.
  pose proof (i63_range off) as Hoff0.
  assert (HnZw : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply u64_lit; lia).
  assert (Hargs : mmap_guard_args (ms_pend ms) m (to_Z len)).
  { apply (mmap_guard_args_of_inv R0 Lim (fl_c L) (fl_S L) (ms_pend ms) m (to_Z len) p); try assumption; try lia.
    - rewrite Ha0. exact Hamod.
    - rewrite Ha0, Eplo, Hau. lia.
    - rewrite Ha0, Ephi, Hau. fold nZ. lia. }
  pose proof (mmap_guard_step_iff cfg segs (ms_pend ms) _ m (to_Z len) Halloc Hh Hnl
                (ms_pend_svc ms) Hx8 Hargs) as Hiff. cbv zeta in Hiff. fold nZ in Hiff.
  rewrite Ha0 in Hiff.
  exists unit, tt, (fun _ => mkCfg (sysret (ms_pend ms) addr (apply_unmaps (ms_mem (ms_pend ms)) [(addr, Z_to_bv 64 nZ)]))
                            (mmap_guard_model addr nZ m)).
  split.
  { intros e st. rewrite Hiff. split.
    - intros [-> ->]. exists tt. split; reflexivity.
    - intros (_ & -> & ->). split; reflexivity. }
  intros _.
  assert (Hstepa : sstep_cfg segs cfg (mkCfg (ms_pend ms) m) []
            (SNext (mkCfg (sysret (ms_pend ms) addr (apply_unmaps (ms_mem (ms_pend ms)) [(addr, Z_to_bv 64 nZ)]))
                          (mmap_guard_model addr nZ m)))).
  { apply Hiff. split; reflexivity. }
  pose proof (i63_range pn) as Hpn0.
  pose proof (fx_guard_sound segs IM n rho F ms t rg pn k HRn Hat rf_get0 rf_lt0 rf_kpos0
                ltac:(lia) ltac:(lia) ltac:(lia)) as HRn'.
  rewrite rf_pn0, rf_k0 in HRn'. fold addr in HRn'.
  eexists _, _, _, rho, _, _, 0%nat. cbn [cfg_ms cfg_model rsteps]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  2:{ apply (node_ext_repage n rho F L ms m _ _ _ _ t rg rf_get0).
      - apply upd_region_shape. intros r. cbn. repeat split; reflexivity.
      - repeat split; reflexivity.
      - reflexivity.
      - rewrite sysret_fregs. reflexivity.
      - rewrite sysret_fcsr. reflexivity.
      - rewrite sysret_rom. reflexivity.
      - intros x Hx. rewrite sysret_mem, apply_unmaps_one, HnZw, Hau.
        replace ((bv_unsigned (rho t) + to_Z off <=? bv_unsigned x)
                 && (bv_unsigned x <? bv_unsigned (rho t) + to_Z off + nZ)) with false; [reflexivity|].
        symmetry. apply not_true_iff_false. intros Hb. apply andb_true_iff in Hb as [B1 B2].
        apply Z.leb_le in B1. apply Z.ltb_lt in B2. apply Hx. unfold in_ival. lia.
      - reflexivity.
      - reflexivity.
      - intros _ [E1 E2]. split; [exact E1|]. cbn [fl_na map].
        change (vm_noaccess (m_vmmaps (mmap_guard_model addr nZ m)))
          with ((addr, Z_to_bv 64 nZ) :: maps_subtract (vm_noaccess (m_vmmaps m))
                                           (bv_unsigned addr) (bv_unsigned addr + bv_unsigned (Z_to_bv 64 nZ))).
        f_equal; [cbn [den]; rewrite rf_nZ0; reflexivity|].
        rewrite HnZw, Hau, <- rf_nZ0, E2. symmetry.
        exact (fl_sub_exact rho (f_mem F) (vm_noaccess (m_vmmaps m)) t off nZi rg (fl_na L) Hregs Hsep rf_get0
                 ltac:(lia) ltac:(rewrite rf_nZ0; lia) Hposna Hm2). }
  apply (DInv_repage n rho F L ms m _ _ _ _ t rg HD rf_get0 rf_keep0 HRn').
  - apply upd_region_shape. intros r. cbn. repeat split; reflexivity.
  - intros t' Hne. cbn [fx_guard fx_sysret f_mem]. rewrite upd_region_get.
    destruct (t' =? t)%uint63 eqn:E; [apply Uint63.eqb_spec in E; contradiction | reflexivity].
  - exact Hh.
  - apply model_nolazy_with_vmmaps. exact Hnl.
  - apply (mmap_guard_inv R0 Lim (fl_c L) (fl_S L) m addr nZ p Hli HpIn); [|lia].
    unfold e_inside. rewrite Eplo, Ephi. unfold e_hi, e_lo, e_sz. cbn [fst snd]. rewrite HnZw. lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - (* [comment removed for export] *)
    change (vm_noaccess (m_vmmaps (mmap_guard_model addr nZ m)))
      with ((addr, Z_to_bv 64 nZ) :: maps_subtract (vm_noaccess (m_vmmaps m))
                                       (bv_unsigned addr) (bv_unsigned addr + bv_unsigned (Z_to_bv 64 nZ))).
    assert (Hshape : same_shape (f_mem F) (f_mem (fx_guard F t pn k))).
    { apply upd_region_shape. intros r. cbn. repeat split; reflexivity. }
    constructor.
    + destruct (same_shape_get' _ _ _ _ Hshape rf_get0) as (rg2 & Hg2 & E1 & E2).
      exists rg2. rewrite E1, E2. split; [exact Hg2|]. split; [lia|]. split; [rewrite rf_nZ0; fold nZ; lia|].
      left. rewrite rf_nZ0. reflexivity.
    + (* [comment removed for export] *)
      rewrite HnZw, Hau, <- rf_nZ0.
      eapply Forall_impl;
        [|exact (fl_sub_mirror rho (f_mem F) _ _ t off nZi rg (fl_na L) Hregs Hsep rf_get0
                   ltac:(lia) ltac:(rewrite rf_nZ0; lia) Hshape Hposna Hm2)].
      intros e'. apply ent_ok_ext; [reflexivity | reflexivity |]. intros p' Hp'. right. exact Hp'.
  - exact (budget_step _ _ _ _ _ Hbud1 Hstepa).
  - repeat split; reflexivity.
  - intros x Hx. rewrite sysret_mem, apply_unmaps_one, HnZw, Hau.
    replace ((bv_unsigned (rho t) + to_Z off <=? bv_unsigned x)
             && (bv_unsigned x <? bv_unsigned (rho t) + to_Z off + nZ)) with false; [reflexivity|].
    symmetry. apply not_true_iff_false. intros Hb. apply andb_true_iff in Hb as [B1 B2].
    apply Z.leb_le in B1. apply Z.ltb_lt in B2. apply Hx. unfold in_ival. lia.
Qed.

Lemma sys_guard_sound n rho F L ms m t off len res :
  sys_guard keep F L n t off len = Some res ->
  DInv n rho F L ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 222 ->
  ms_gpr (ms_pend ms) 0 = adr rho t (to_Z off) ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  bv_unsigned (ms_gpr (ms_pend ms) 2) = 0 ->
  bv_unsigned (ms_gpr (ms_pend ms) 3) = 50 ->
  bv_unsigned (ms_gpr (ms_pend ms) 5) = 0 ->
  sys_ok res ms m.
Proof.
  intros. eapply sys_okX_ok. eapply sys_guard_soundX; eassumption.
Qed.

Lemma sys_expose_soundX n rho F L ms m t off len res :
  sys_expose Lim rl keep F L n t off len = Some res ->
  DInv n rho F L ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 226 ->
  ms_gpr (ms_pend ms) 0 = adr rho t (to_Z off) ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  bv_unsigned (ms_gpr (ms_pend ms) 2) = 3 ->
  sys_okX n rho F L res ms m.
Proof.
  intros Hsys HD Hat Hstep Hx8 Ha0 Ha1 Ha2.
  pose proof HD as (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfr).
  unfold sys_expose in Hsys. cbv zeta in Hsys.
  destruct (range_ok keep F n t off len
            && match rl with RSrc => true | RTgt => (fl_S L <=? Lim) end) eqn:Hchk; [|discriminate].
  apply andb_true_iff in Hchk as [Hrange Hacct].
  destruct (List.find (ent_covers t off (pg_up len)) (fl_na L)) as [e|] eqn:Hfind; [|discriminate].
  injection Hsys as <-.
  destruct (range_facts_of rho F n t off len Hrange) as [rg RF]. destruct RF.
  set (nZi := pg_up len) in *. set (nZ := page_round_up_Z (to_Z len)) in *.
  set (pn := (off >> 12)%uint63) in *. set (k := Z.to_nat (to_Z (nZi >> 12)%uint63)) in *.
  assert (HnZpos : 0 < nZ) by (apply page_round_up_Z_pos; lia).
  pose proof (Rn_R _ _ _ _ HRn H0) as HR. pose proof (R_svc _ _ _ _ _ HR) as Hsvc.
  pose proof (budget_pend ms m Hbud Hh Hnl Hsvc Hstep) as Hbud1.
  pose proof (R_regions_sep _ _ _ HR) as Hsep.
  assert (Hregs : forall t' rg', iget t' (f_mem F) = Some rg' -> region_ok rho t' rg')
    by (intros t' rg' Hg'; exact (R_region_ok _ _ _ _ _ HR Hg')).
  assert (Hposna : Forall (fun q => 0 < e_sz q) (vm_noaccess (m_vmmaps m))).
  { eapply Forall_impl; [|exact (li_noacc _ _ _ _ _ Hli)]. intros q0 [Hq0 _]. exact Hq0. }
  assert (Hl62 : forall t' rg', iget t' (f_mem F) = Some rg' -> to_Z (rg_len rg') <= 2 ^ 62).
  { intros t' rg' Hg'. exact (proj1 (proj2 (R_region_ok _ _ _ _ _ HR Hg'))). }
  destruct Hmir as (Hm1 & Hm2 & rgb & Hgb & Hbrk).
  apply find_some in Hfind as [HeIn Hecov].
  destruct (ent_covers_sound rho (f_mem F) _ t off nZi e Hecov
              (proj1 (Forall_forall _ _) Hm2 _ HeIn) (Hl62 t) ltac:(rewrite rf_nZ0; fold nZ; lia))
    as (eo & el & rg' & -> & Hg' & He1 & He2 & He3 & He4 & HqIn).
  rewrite rf_get0 in Hg'. injection Hg' as <-. rewrite rf_nZ0 in He3. fold nZ in He3.
  destruct (range_addr rho F ms t off nZ eo el rg HR rf_get0 rf_al0 rf_offal0 He1 He2 HnZpos He3 He4)
    as (Hau & Hamod & Ha63 & Eqlo & Eqhi).
  set (addr := adr rho t (to_Z off)) in *. set (q := (adr rho t (to_Z eo), Z_to_bv 64 (to_Z el))) in *.
  pose proof (i63_range off) as Hoff0. pose proof (i63_range eo) as Heo0. pose proof (i63_range el) as Hel0.
  assert (HnZw : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (apply u64_lit; lia).
  assert (Hargs : mprotect_rw_args (ms_pend ms) m (to_Z len)).
  { apply (mprotect_rw_args_of_inv R0 Lim (fl_c L) (fl_S L) (ms_pend ms) m (to_Z len) q); try assumption; try lia.
    - rewrite Ha0. exact Hamod.
    - rewrite Ha0, Eqlo, Hau. lia.
    - rewrite Ha0, Eqhi, Hau. fold nZ. lia. }
  assert (Hgate : mprotect_budget_ok m (ms_gpr (ms_pend ms) 0) (Z_to_bv 64 nZ) = true).
  { destruct rl_cases as [Erl|Erl].
    - pose proof Hbud1 as Hb. unfold budget in Hb. rewrite Erl in Hb.
      apply (mprotect_budget_ok_of_premise segs (ms_pend ms) _ m (to_Z len) Hx8 Hargs).
      exact (within_budget_alloc_not_refused cfg segs (ms_pend ms) m _ Hb Hh (ms_pend_svc ms)).
    - rewrite Erl in Hacct. apply Z.leb_le in Hacct.
      exact (mprotect_budget_ok_acct R0 Lim (fl_c L) (fl_S L) m _ _ Hli (proj2 Hnl) Hacct). }
  pose proof (mprotect_rw_step_iff cfg segs (ms_pend ms) _ m (to_Z len) Halloc Hh (proj1 Hnl)
                (ms_pend_svc ms) Hx8 Hargs Hgate) as Hiff. cbv zeta in Hiff. fold nZ in Hiff.
  rewrite Ha0 in Hiff.
  exists unit, tt, (fun _ => mkCfg (sysret (ms_pend ms) (Z_to_bv 64 0)
                               (apply_zeros (ms_mem (ms_pend ms)) [(addr, Z_to_bv 64 nZ)]))
                            (mprotect_rw_model addr nZ m)).
  split.
  { intros e st. rewrite Hiff. split.
    - intros [-> ->]. exists tt. split; reflexivity.
    - intros (_ & -> & ->). split; reflexivity. }
  intros _.
  assert (Hstepa : sstep_cfg segs cfg (mkCfg (ms_pend ms) m) []
            (SNext (mkCfg (sysret (ms_pend ms) (Z_to_bv 64 0)
                             (apply_zeros (ms_mem (ms_pend ms)) [(addr, Z_to_bv 64 nZ)]))
                          (mprotect_rw_model addr nZ m)))).
  { apply Hiff. split; reflexivity. }
  pose proof (i63_range pn) as Hpn0.
  pose proof (fx_expose_sound segs IM n rho F ms t rg pn k HRn Hat rf_get0 rf_lt0 rf_kpos0
                ltac:(lia) ltac:(lia) ltac:(lia)) as HRn'.
  rewrite rf_pn0, rf_k0 in HRn'. fold addr in HRn'.
  eexists _, _, _, rho, _, _, 0%nat. cbn [cfg_ms cfg_model rsteps]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  2:{ apply (node_ext_repage n rho F L ms m _ _ _ _ t rg rf_get0).
      - apply upd_region_shape. intros r. cbn. repeat split; reflexivity.
      - repeat split; reflexivity.
      - reflexivity.
      - rewrite sysret_fregs. reflexivity.
      - rewrite sysret_fcsr. reflexivity.
      - rewrite sysret_rom. reflexivity.
      - intros x Hx. rewrite sysret_mem, apply_zeros_one, HnZw, Hau.
        replace ((bv_unsigned (rho t) + to_Z off <=? bv_unsigned x)
                 && (bv_unsigned x <? bv_unsigned (rho t) + to_Z off + nZ)) with false; [reflexivity|].
        symmetry. apply not_true_iff_false. intros Hb. apply andb_true_iff in Hb as [B1 B2].
        apply Z.leb_le in B1. apply Z.ltb_lt in B2. apply Hx. unfold in_ival. lia.
      - reflexivity.
      - reflexivity.
      - intros _ [E1 E2]. split; [exact E1|]. cbn [fl_na].
        change (vm_noaccess (m_vmmaps (mprotect_rw_model addr nZ m)))
          with (maps_subtract (vm_noaccess (m_vmmaps m))
                  (bv_unsigned addr) (bv_unsigned addr + bv_unsigned (Z_to_bv 64 nZ))).
        rewrite HnZw, Hau, <- rf_nZ0, E2. symmetry.
        exact (fl_sub_exact rho (f_mem F) (vm_noaccess (m_vmmaps m)) t off nZi rg (fl_na L) Hregs Hsep rf_get0
                 ltac:(lia) ltac:(rewrite rf_nZ0; lia) Hposna Hm2). }
  apply (DInv_repage n rho F L ms m _ _ _ _ t rg HD rf_get0 rf_keep0 HRn').
  - apply upd_region_shape. intros r. cbn. repeat split; reflexivity.
  - intros t' Hne. cbn [fx_expose fx_sysret f_mem]. rewrite upd_region_get.
    destruct (t' =? t)%uint63 eqn:E; [apply Uint63.eqb_spec in E; contradiction | reflexivity].
  - exact Hh.
  - apply model_nolazy_with_vmmaps. exact Hnl.
  - apply (mprotect_rw_inv R0 Lim (fl_c L) (fl_S L) m addr nZ Hli). rewrite HnZw. lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - (* [comment removed for export] *)
    change (vm_noaccess (m_vmmaps (mprotect_rw_model addr nZ m)))
      with (maps_subtract (vm_noaccess (m_vmmaps m))
              (bv_unsigned addr) (bv_unsigned addr + bv_unsigned (Z_to_bv 64 nZ))).
    assert (Hshape : same_shape (f_mem F) (f_mem (fx_expose F t pn k))).
    { apply upd_region_shape. intros r. cbn. repeat split; reflexivity. }
    rewrite HnZw, Hau, <- rf_nZ0.
    exact (fl_sub_mirror rho (f_mem F) _ _ t off nZi rg (fl_na L) Hregs Hsep rf_get0
             ltac:(lia) ltac:(rewrite rf_nZ0; lia) Hshape Hposna Hm2).
  - exact (budget_step _ _ _ _ _ Hbud1 Hstepa).
  - repeat split; reflexivity.
  - intros x Hx. rewrite sysret_mem, apply_zeros_one, HnZw, Hau.
    replace ((bv_unsigned (rho t) + to_Z off <=? bv_unsigned x)
             && (bv_unsigned x <? bv_unsigned (rho t) + to_Z off + nZ)) with false; [reflexivity|].
    symmetry. apply not_true_iff_false. intros Hb. apply andb_true_iff in Hb as [B1 B2].
    apply Z.leb_le in B1. apply Z.ltb_lt in B2. apply Hx. unfold in_ival. lia.
Qed.

Lemma sys_expose_sound n rho F L ms m t off len res :
  sys_expose Lim rl keep F L n t off len = Some res ->
  DInv n rho F L ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 226 ->
  ms_gpr (ms_pend ms) 0 = adr rho t (to_Z off) ->
  bv_unsigned (ms_gpr (ms_pend ms) 1) = to_Z len ->
  bv_unsigned (ms_gpr (ms_pend ms) 2) = 3 ->
  sys_ok res ms m.
Proof.
  intros. eapply sys_okX_ok. eapply sys_expose_soundX; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ent_ok_grow rho M M' l l' t e :
  (forall t', t' <> t -> iget t' M' = iget t' M) ->
  (forall rg, iget t M = Some rg -> exists rg', iget t M' = Some rg' /\ rg_lo rg' = rg_lo rg
                                             /\ to_Z (rg_len rg) <= to_Z (rg_len rg')) ->
  (forall p, In p l -> In p l') ->
  ent_ok rho M l e -> ent_ok rho M' l' e.
Proof.
  intros Hother Hgrow Hsub. destruct e as [[t' off] len]. intros (rg & Hg & H1 & H2 & H3).
  destruct (Uint63.eqb t' t) eqn:E.
  - apply Uint63.eqb_spec in E. subst t'. destruct (Hgrow rg Hg) as (rg' & Hg' & El & Eh).
    exists rg'. rewrite El. split; [exact Hg'|]. split; [exact H1|]. split; [lia|]. apply Hsub. exact H3.
  - apply eqb_false_spec in E. exists rg. rewrite (Hother t' E). repeat split; try assumption.
    apply Hsub. exact H3.
Qed.

Lemma sys_brk_grow_soundX n rho F L ms m t off res :
  sys_brk_grow keep F L n t off = Some res ->
  DInv n rho F L ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 214 ->
  ms_gpr (ms_pend ms) 0 = adr rho t (to_Z off) ->
  sys_okX n rho F L res ms m.
Proof.
  intros Hsys HD Hat Hstep Hx8 Ha0.
  pose proof HD as (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfr).
  unfold sys_brk_grow in Hsys. destruct (iget t (f_mem F)) as [rg|] eqn:Hg; [|discriminate].
  cbv zeta in Hsys.
  match type of Hsys with (if ?c then _ else _) = _ => destruct c eqn:Hchk; [|discriminate] end.
  injection Hsys as <-.
  repeat match type of Hchk with (_ && _ = true) =>
    let H := fresh "Hc" in apply andb_true_iff in Hchk as [Hchk H] end.
  apply Uint63.eqb_spec in Hchk.                                  (* [comment removed for export] *)
  apply ltb_spec in Hc5.                                          (* [comment removed for export] *)
  apply negb_true_iff in Hc4. apply mem_int_false in Hc4.         (* [comment removed for export] *)
  apply ltb_spec in Hc3.                                          (* [comment removed for export] *)
  apply leb_spec in Hc2. change (to_Z 4611686018427387904) with (2 ^ 62) in Hc2.
  apply Uint63.eqb_spec in Hc1. apply (f_equal to_Z) in Hc1. rewrite to_Z_0, to_Z_land4095 in Hc1.
  apply Uint63.eqb_spec in Hc0. apply (f_equal to_Z) in Hc0. rewrite to_Z_0, to_Z_land4095 in Hc0.
  apply leb_spec in Hc.                                           (* [comment removed for export] *)
  set (d := (off - rg_len rg)%uint63) in *.
  pose proof (i63_range off) as Hoff0. pose proof (i63_range (rg_len rg)) as Hlen0.
  assert (Hd : to_Z d = to_Z off - to_Z (rg_len rg)) by (apply i63_sub_small; lia).
  assert (Hdpos : 0 < to_Z d) by lia.
  destruct (pages_of_nat (to_Z d) Hdpos Hc1) as [Hk Hkpos]. rewrite <- to_Z_lsr12 in Hk, Hkpos.
  set (k := Z.to_nat (to_Z (d >> 12)%uint63)) in *.
  pose proof (Rn_R _ _ _ _ HRn H0) as HR. pose proof (R_svc _ _ _ _ _ HR) as Hsvc.
  pose proof (budget_pend ms m Hbud Hh Hnl Hsvc Hstep) as Hbud1.
  pose proof (R_regions_sep _ _ _ HR) as Hsep.
  pose proof (R_region_ok _ _ _ _ _ HR Hg) as (_ & Hl62 & Hnw & _ & _).
  pose proof (u64 (rho t)) as Hrt.
  destruct Hmir as (Hm1 & Hm2 & rgb & Hgb & Hbrk). rewrite <- Hchk, Hg in Hgb. injection Hgb as <-.
  rewrite <- Hchk in Hbrk.
  assert (Hbrku : bv_unsigned (vm_brk (m_vmmaps m)) = bv_unsigned (rho t) + to_Z (rg_len rg)).
  { rewrite <- Hbrk. apply adr_unsigned; lia. }
  assert (Ha0u : bv_unsigned (ms_gpr (ms_pend ms) 0) = bv_unsigned (rho t) + to_Z off).
  { rewrite Ha0. apply adr_unsigned; lia. }
  assert (Hbal : bv_unsigned (vm_brk (m_vmmaps m)) mod 4096 = 0) by exact (li_brk_al _ _ _ _ _ Hli).
  assert (Hargs : brk_grow_args (ms_pend ms) m).
  { apply (brk_grow_args_of_inv R0 Lim (fl_c L) (fl_S L)); [exact Hli | lia |].
    unfold page_size. rewrite Ha0u.
    replace (bv_unsigned (rho t) + to_Z off) with (bv_unsigned (vm_brk (m_vmmaps m)) + to_Z d) by lia.
    apply mod4096_add; assumption. }
  (* [comment removed for export] *)
  assert (Hdv : forall rho', agree n rho rho' ->
            dv rho' (FV t (W64 0 (rg_len rg))) = vm_brk (m_vmmaps m)).
  { intros rho' [_ Hag].
    rewrite (dv_adr rho' t 0%uint63 (rg_len rg) (proj1 (R_region_ok _ _ _ _ _ HR Hg)) eq_refl).
    rewrite (adr_rho rho rho' _ _ (Hag _ Hc5)). exact Hbrk. }
  destruct (brk_grow_b m (ms_gpr (ms_pend ms) 0)) eqn:Hgate.
  2:{ (* [comment removed for export] *)
    pose proof (brk_grow_step_iff_blocked cfg segs (ms_pend ms) _ m Hh (proj1 Hnl) (ms_pend_svc ms)
                  Hx8 Hargs Hgate) as Hiff.
    exists unit, tt, (fun _ => mkCfg (sysret (ms_pend ms) (vm_brk (m_vmmaps m)) (ms_mem (ms_pend ms))) m).
    split.
    { intros e st. rewrite Hiff. split.
      - intros [-> ->]. exists tt. split; reflexivity.
      - intros (_ & -> & ->). split; reflexivity. }
    intros _.
    assert (Hstepa : sstep_cfg segs cfg (mkCfg (ms_pend ms) m) []
              (SNext (mkCfg (sysret (ms_pend ms) (vm_brk (m_vmmaps m)) (ms_mem (ms_pend ms))) m))).
    { apply Hiff. split; reflexivity. }
    pose proof (fx_ret_sound segs IM n rho F ms _ _ HRn Hat Hdv) as HRn'.
    eexists _, _, _, rho, _, _, 0%nat. cbn [cfg_ms cfg_model rsteps]. split; [right; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split.
    2:{ apply node_ext_same; [lia | intros; reflexivity | intros; reflexivity | reflexivity | reflexivity
                              | reflexivity | reflexivity | reflexivity]. }
    split; [exact HRn'|]. split; [exact H0|]. split; [exact Hh|]. split; [exact Hnl|].
    split; [exact Hli|]. split; [exact Hcov|].
    split; [split; [exact Hm1 | split; [exact Hm2 | exists rg; rewrite <- Hchk; split; [exact Hg | exact Hbrk]]]|].
    split; [exact (budget_step _ _ _ _ _ Hbud1 Hstepa)|]. split; [exact HXI|]. split; [exact Hxt|]. exact Hfr. }
  (* [comment removed for export] *)
  pose proof (brk_grow_step_iff cfg segs (ms_pend ms) _ m Halloc Hh (proj1 Hnl) (ms_pend_svc ms)
                Hx8 Hargs Hgate) as Hiff.
  pose proof Hgate as Hgate'. unfold brk_grow_b in Hgate'. cbv zeta in Hgate'.
  apply andb_true_iff in Hgate' as [Hgate' _]. apply andb_true_iff in Hgate' as [Htop Hfree].
  apply Z.leb_le in Htop. rewrite Ha0u in Htop.
  destruct (ledger_inv_alloc_top _ _ _ _ _ Hli) as [_ Htask]. unfold TASK_SIZE in Htask.
  assert (Hdw : bv_unsigned (Z_to_bv 64 (to_Z d)) = to_Z d) by (apply u64_lit; lia).
  assert (Hfree' : region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))
                     (vm_brk (m_vmmaps m)) (Z_to_bv 64 (to_Z d)) = true).
  { apply (region_free_sub _ _ _ _ _ Hfree). unfold e_inside, e_hi, e_lo, e_sz. cbn [fst snd].
    rewrite Hdw, Ha0u, Hbrku. unfold page_size. rewrite u64_lit by lia. lia. }
  pose proof (sep_from_free rho (f_mem F) (m_vmmaps m) (vm_brk (m_vmmaps m)) (to_Z d) Hcov
                ltac:(lia) ltac:(lia) Hfree') as Hsepn.
  assert (Hsep' : forall t' rg', t' <> t -> iget t' (f_mem F) = Some rg' ->
            bv_unsigned (rho t) + to_Z (rg_len rg) + Z.of_nat k * 4096 <= fst (rg_ival rho t' rg')
            \/ snd (rg_ival rho t' rg') <= bv_unsigned (rho t) + to_Z (rg_lo rg)).
  { intros t' rg' Hne Hg'. destruct (Hsepn t' rg' Hg') as [Hs|Hs]; rewrite Hbrku in Hs.
    - left. lia.
    - unfold rg_ival in *. cbn [fst snd] in *.
      destruct (Hsep t t' rg rg' ltac:(intros E; apply Hne; symmetry; exact E) Hg Hg') as [Hq|Hq].
      + pose proof (proj1 (Hcov t' rg' Hg')). lia.
      + right. exact Hq. }
  pose proof (fx_brk_grow_sound segs IM n rho F ms t rg k HRn Hat Hg Hc5 Hkpos Hc0 Hc
                ltac:(lia) ltac:(lia) Hsep') as HRn'.
  replace (to_Z (rg_len rg) + Z.of_nat k * 4096) with (to_Z off) in HRn' by lia.
  rewrite Hk, Hbrk, <- Ha0 in HRn'.
  exists unit, tt, (fun _ => mkCfg (sysret (ms_pend ms) (ms_gpr (ms_pend ms) 0)
                               (apply_zeros (ms_mem (ms_pend ms)) (brk_grow_zeros (ms_gpr (ms_pend ms) 0) m)))
                            (brk_grow_model (ms_gpr (ms_pend ms) 0) m)).
  split.
  { intros e st. rewrite Hiff. split.
    - intros [-> ->]. exists tt. split; reflexivity.
    - intros (_ & -> & ->). split; reflexivity. }
  intros _.
  assert (Hstepa : sstep_cfg segs cfg (mkCfg (ms_pend ms) m) []
            (SNext (mkCfg (sysret (ms_pend ms) (ms_gpr (ms_pend ms) 0)
                             (apply_zeros (ms_mem (ms_pend ms)) (brk_grow_zeros (ms_gpr (ms_pend ms) 0) m)))
                          (brk_grow_model (ms_gpr (ms_pend ms) 0) m)))).
  { apply Hiff. split; reflexivity. }
  assert (Hzeros : brk_grow_zeros (ms_gpr (ms_pend ms) 0) m = [(vm_brk (m_vmmaps m), Z_to_bv 64 (to_Z d))]).
  { unfold brk_grow_zeros. do 3 f_equal. lia. }
  rewrite Hzeros in *.
  (* [comment removed for export] *)
  assert (Hlen' : (rg_len rg + (of_Z (Z.of_nat k) << 12))%uint63 = off).
  { apply to_Z_inj. rewrite add_spec, lsl_spec, of_Z_spec, i63_wB. change (2 ^ to_Z 12) with 4096.
    rewrite (Z.mod_small (Z.of_nat k)) by lia. rewrite (Z.mod_small (Z.of_nat k * 4096)) by lia.
    rewrite Z.mod_small by lia. lia. }
  set (rg1 := RGK (rg_lo rg) off (rg_align rg) (rg_dflt rg)
                 (zero_pages k (rg_len rg >> 12)%uint63 (rg_pages rg)) (rg_clo rg) (rg_chi rg) (rg_kind rg)).
  assert (HM' : f_mem (fx_brk_grow F t k) = iset t rg1 (f_mem F)).
  { unfold fx_brk_grow. rewrite Hg. cbv zeta. rewrite Hlen'. reflexivity. }
  assert (Hother : forall t', t' <> t -> iget t' (iset t rg1 (f_mem F)) = iget t' (f_mem F)).
  { intros t' Hne. apply iget_iset_other. intros E. apply Hne. symmetry. exact E. }
  assert (Hmaps : vm_maps (m_vmmaps (brk_grow_model (ms_gpr (ms_pend ms) 0) m))
                  = (vm_brk (m_vmmaps m), Z_to_bv 64 (to_Z d)) :: vm_maps (m_vmmaps m)).
  { unfold brk_grow_model. rewrite m_vmmaps_with_vmmaps'. unfold ledger_brk_grow. cbn [vm_maps].
    do 3 f_equal. lia. }
  eexists _, _, _, rho, _, _, 0%nat. cbn [cfg_ms cfg_model rsteps]. split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  2:{ constructor.
      - lia.
      - intros; reflexivity.
      - rewrite sysret_fregs. reflexivity.
      - rewrite sysret_fcsr. reflexivity.
      - rewrite sysret_rom. reflexivity.
      - repeat split; reflexivity.
      - reflexivity.
      - intros x Hx Hno. split.
        + rewrite sysret_mem, apply_zeros_one, Hdw, Hbrku.
          replace ((bv_unsigned (rho t) + to_Z (rg_len rg) <=? bv_unsigned x)
                   && (bv_unsigned x <? bv_unsigned (rho t) + to_Z (rg_len rg) + to_Z d)) with false;
            [reflexivity|].
          symmetry. apply andb_false_iff. right. apply Z.ltb_ge. lia.
        + rewrite HM'. intros t' rg' Hg' Hxin. rewrite iget_iset in Hg'.
          destruct (t' =? t)%uint63 eqn:E.
          * apply Uint63.eqb_spec in E. subst t'. injection Hg' as <-. unfold in_ival in Hxin.
            cbn [rg1 rg_lo rg_len] in Hxin. lia.
          * exact (Hno t' rg' Hg' Hxin).
      - reflexivity.
      - reflexivity.
      - intros _ [E1 E2]. split.
        + cbn [fl_maps map]. rewrite Hmaps, E1. f_equal. cbn [den]. rewrite Hbrk. reflexivity.
        + exact E2. }
  split; [exact HRn'|]. split; [exact H0|]. split; [exact Hh|].
  split; [apply model_nolazy_with_vmmaps; exact Hnl|].
  split.
  { cbn [fl_c fl_S]. replace (to_Z d) with (bv_unsigned (ms_gpr (ms_pend ms) 0) - bv_unsigned (vm_brk (m_vmmaps m))) by lia.
    exact (brk_grow_inv R0 Lim (fl_c L) (fl_S L) (ms_pend ms) m Hli Hargs Hgate). }
  split.
  { (* [comment removed for export] *)
    rewrite HM'. intros t' rg' Hg'. rewrite iget_iset in Hg'.
    destruct (t' =? t)%uint63 eqn:E.
    - apply Uint63.eqb_spec in E. subst t'. injection Hg' as <-. cbn [rg1 rg_lo rg_len].
      split; [lia|]. intros x Hx. unfold in_ival in Hx. cbn [rg1 rg_lo rg_len] in Hx.
      destruct (Z_lt_ge_dec x (bv_unsigned (rho t) + to_Z (rg_len rg))) as [Hold|Hnew].
      + apply (covered_mono (m_vmmaps m)); [reflexivity | reflexivity | |].
        * intros p Hp. rewrite Hmaps. right. exact Hp.
        * apply (proj2 (Hcov t rg Hg)). unfold in_ival. lia.
      + left. exists (vm_brk (m_vmmaps m), Z_to_bv 64 (to_Z d)). split.
        * apply in_app_iff. right. rewrite Hmaps. left. reflexivity.
        * unfold e_hi, e_lo, e_sz. cbn [fst snd]. rewrite Hdw, Hbrku. lia.
    - destruct (Hcov t' rg' Hg') as [Hne Hb]. split; [exact Hne|]. intros x Hx.
      apply (covered_mono (m_vmmaps m)); [reflexivity | reflexivity | | exact (Hb x Hx)].
      intros p Hp. rewrite Hmaps. right. exact Hp. }
  assert (Hgrow : forall rg0, iget t (f_mem F) = Some rg0 ->
            exists rg', iget t (iset t rg1 (f_mem F)) = Some rg' /\ rg_lo rg' = rg_lo rg0
                        /\ to_Z (rg_len rg0) <= to_Z (rg_len rg')).
  { intros rg0 Hg0. rewrite Hg in Hg0. injection Hg0 as <-. exists rg1. rewrite iget_iset_same.
    cbn [rg1 rg_lo rg_len]. split; [reflexivity|]. split; [reflexivity | lia]. }
  split.
  { (* [comment removed for export] *)
    rewrite HM'. split; [|split].
    - cbn [fl_maps]. constructor.
      + exists rg1. rewrite iget_iset_same. cbn [rg1 rg_lo rg_len]. split; [reflexivity|].
        split; [lia|]. split; [lia|]. rewrite Hmaps. left. rewrite Hbrk. reflexivity.
      + eapply Forall_impl; [|exact Hm1]. intros e.
        apply (ent_ok_grow rho (f_mem F) _ _ _ t e Hother Hgrow).
        intros p Hp. rewrite Hmaps. right. exact Hp.
    - cbn [fl_na]. eapply Forall_impl; [|exact Hm2]. intros e.
      apply (ent_ok_grow rho (f_mem F) _ _ _ t e Hother Hgrow). intros p Hp. exact Hp.
    - cbn [fl_brk]. exists rg1. rewrite <- Hchk, iget_iset_same. split; [reflexivity|].
      cbn [rg1 rg_len]. rewrite <- Ha0. reflexivity. }
  split; [exact (budget_step _ _ _ _ _ Hbud1 Hstepa)|].
  split; [apply (XI_vm rho m); [repeat split; reflexivity | exact HXI]|]. split; [exact Hxt|].
  (* [comment removed for export] *)
  rewrite HM'. intros tk Htk. destruct (Hfr tk Htk) as [Hpr Hmem].
  assert (Hnek : tk <> t) by (intros ->; contradiction).
  split; [exact (pristine_eq _ _ _ (Hother tk Hnek) Hpr)|].
  intros rgk x Hgk Hx. rewrite (Hother tk Hnek) in Hgk.
  rewrite sysret_mem, apply_zeros_one, Hdw, Hbrku.
  replace ((bv_unsigned (rho t) + to_Z (rg_len rg) <=? bv_unsigned x)
           && (bv_unsigned x <? bv_unsigned (rho t) + to_Z (rg_len rg) + to_Z d)) with false;
    [exact (Hmem rgk x Hgk Hx)|].
  symmetry. apply not_true_iff_false. intros Hb. apply andb_true_iff in Hb as [B1 B2].
  apply Z.leb_le in B1. apply Z.ltb_lt in B2.
  destruct (Hsepn tk rgk Hgk) as [Hs|Hs]; unfold rg_ival in Hs; cbn [fst snd] in Hs;
    rewrite Hbrku in Hs; unfold in_ival in Hx; lia.
Qed.

Lemma sys_brk_grow_sound n rho F L ms m t off res :
  sys_brk_grow keep F L n t off = Some res ->
  DInv n rho F L ms m -> at_ecall F ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  bv_unsigned (ms_reg ms 17) = 214 ->
  ms_gpr (ms_pend ms) 0 = adr rho t (to_Z off) ->
  sys_ok res ms m.
Proof.
  intros. eapply sys_okX_ok. eapply sys_brk_grow_soundX; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Variable xsys : fstate -> fledger -> int -> option dres.
Hypothesis xsys_sound : forall n rho F L ms m res,
  xsys F L n = Some res -> DInv n rho F L ms m ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  sys_ok res ms m.

Lemma ptr00 rho : rho 0%uint63 = Z_to_bv 64 0 -> bv_unsigned (adr rho 0%uint63 (to_Z 0%uint63)) = 0.
Proof. intros H0. rewrite to_Z_0, adr_0, H0. reflexivity. Qed.

Theorem drive_sys_own_soundX n rho F L ms m res :
  drive_sys_own code Rb Rc Lim rl keep F L n = Some res ->
  DInv n rho F L ms m ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  sys_okX n rho F L res ms m.
Proof.
  intros Hsys HD Hstep. pose proof HD as (HRn & H0 & _).
  pose proof (Rn_R _ _ _ _ HRn H0) as HR.
  unfold drive_sys_own in Hsys.
  destruct (ecall_here code F) eqn:Hec; cbn [negb] in Hsys; [|discriminate].
  pose proof (ecall_here_at F Hec) as Hat.
  destruct (conc (FxState.rget F 17)) as [nr|] eqn:Hnr; [|discriminate].
  destruct (conc_sound rho _ _ H0 Hnr) as [_ Hx8]. rewrite <- (pend_x8 rho F ms HR) in Hx8.
  destruct (nr =? 222)%uint63 eqn:E222.
  { apply eqb_lit in E222. change (to_Z 222) with 222 in E222. rewrite E222 in Hx8.
    destruct (conc (FxState.rget F 11)) as [len|] eqn:H11; [|discriminate].
    destruct (conc (FxState.rget F 12)) as [prot|] eqn:H12; [|discriminate].
    destruct (conc (FxState.rget F 13)) as [flags|] eqn:H13; [|discriminate].
    destruct (conc (FxState.rget F 15)) as [o|] eqn:H15; [|discriminate].
    destruct (conc_sound rho _ _ H0 H11) as [_ Ha1]. rewrite <- (pend_gpr1 rho F ms HR) in Ha1.
    destruct (conc_sound rho _ _ H0 H12) as [_ Ha2]. rewrite <- (pend_gpr2 rho F ms HR) in Ha2.
    destruct (conc_sound rho _ _ H0 H13) as [_ Ha3]. rewrite <- (pend_gpr3 rho F ms HR) in Ha3.
    destruct (conc_sound rho _ _ H0 H15) as [_ Ha5]. rewrite <- (pend_gpr5 rho F ms HR) in Ha5.
    destruct (o =? 0)%uint63 eqn:Eo; cbn [negb] in Hsys; [|discriminate].
    apply eqb_lit in Eo. rewrite Eo, to_Z_0 in Ha5.
    destruct ((prot =? 3)%uint63 && (flags =? 34)%uint63) eqn:Eg.
    { apply andb_true_iff in Eg as [Ep Ef]. apply eqb_lit in Ep, Ef. rewrite Ep in Ha2. rewrite Ef in Ha3.
      exact (sys_grant_soundX n rho F L ms m len res Hsys HD Hat Hstep Hx8 Ha1 Ha2 Ha3 Ha5). }
    destruct ((prot =? 0)%uint63 && (flags =? 34)%uint63) eqn:Ena.
    { apply andb_true_iff in Ena as [Ep Ef]. apply eqb_lit in Ep, Ef. rewrite Ep in Ha2. rewrite Ef in Ha3.
      exact (sys_grant_na_soundX n rho F L ms m len res Hsys HD Hat Hstep Hx8 Ha1 Ha2 Ha3 Ha5). }
    destruct ((prot =? 0)%uint63 && (flags =? 50)%uint63) eqn:Egd; [|discriminate].
    apply andb_true_iff in Egd as [Ep Ef]. apply eqb_lit in Ep, Ef. rewrite Ep in Ha2. rewrite Ef in Ha3.
    destruct (ptr (FxState.rget F 10)) as [[t off]|] eqn:H10; [|discriminate].
    pose proof (ptr_sound rho _ _ _ H10) as Ha0. rewrite <- (pend_gpr0 rho F ms HR) in Ha0.
    exact (sys_guard_soundX n rho F L ms m t off len res Hsys HD Hat Hstep Hx8 Ha0 Ha1 Ha2 Ha3 Ha5). }
  destruct (nr =? 215)%uint63 eqn:E215.
  { apply eqb_lit in E215. change (to_Z 215) with 215 in E215. rewrite E215 in Hx8.
    destruct (ptr (FxState.rget F 10)) as [[t off]|] eqn:H10; [|discriminate].
    destruct (conc (FxState.rget F 11)) as [len|] eqn:H11; [|discriminate].
    pose proof (ptr_sound rho _ _ _ H10) as Ha0. rewrite <- (pend_gpr0 rho F ms HR) in Ha0.
    destruct (conc_sound rho _ _ H0 H11) as [_ Ha1]. rewrite <- (pend_gpr1 rho F ms HR) in Ha1.
    exact (sys_unmap_soundX n rho F L ms m t off len res Hsys HD Hat Hstep Hx8 Ha0 Ha1). }
  destruct (nr =? 214)%uint63 eqn:E214.
  { apply eqb_lit in E214. change (to_Z 214) with 214 in E214. rewrite E214 in Hx8.
    destruct (ptr (FxState.rget F 10)) as [[t off]|] eqn:H10; [|discriminate].
    pose proof (ptr_sound rho _ _ _ H10) as Ha0. rewrite <- (pend_gpr0 rho F ms HR) in Ha0.
    destruct ((t =? 0)%uint63 && (off =? 0)%uint63) eqn:Eq.
    - apply andb_true_iff in Eq as [Et Eo]. apply Uint63.eqb_spec in Et, Eo. subst t off.
      apply (sys_brk_query_soundX n rho F L ms m res Hsys HD Hat Hstep Hx8).
      rewrite Ha0. exact (ptr00 rho H0).
    - exact (sys_brk_grow_soundX n rho F L ms m t off res Hsys HD Hat Hstep Hx8 Ha0). }
  destruct (nr =? 226)%uint63 eqn:E226; [|discriminate].
  apply eqb_lit in E226. change (to_Z 226) with 226 in E226. rewrite E226 in Hx8.
  destruct (ptr (FxState.rget F 10)) as [[t off]|] eqn:H10; [|discriminate].
  destruct (conc (FxState.rget F 11)) as [len|] eqn:H11; [|discriminate].
  destruct (conc (FxState.rget F 12)) as [prot|] eqn:H12; [|discriminate].
  destruct (prot =? 3)%uint63 eqn:Ep; [|discriminate].
  pose proof (ptr_sound rho _ _ _ H10) as Ha0. rewrite <- (pend_gpr0 rho F ms HR) in Ha0.
  destruct (conc_sound rho _ _ H0 H11) as [_ Ha1]. rewrite <- (pend_gpr1 rho F ms HR) in Ha1.
  destruct (conc_sound rho _ _ H0 H12) as [_ Ha2]. rewrite <- (pend_gpr2 rho F ms HR) in Ha2.
  apply eqb_lit in Ep. rewrite Ep in Ha2.
  exact (sys_expose_soundX n rho F L ms m t off len res Hsys HD Hat Hstep Hx8 Ha0 Ha1 Ha2).
Qed.

Theorem drive_sys_own_sound n rho F L ms m res :
  drive_sys_own code Rb Rc Lim rl keep F L n = Some res ->
  DInv n rho F L ms m ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  sys_ok res ms m.
Proof.
  intros. eapply sys_okX_ok. eapply drive_sys_own_soundX; eassumption.
Qed.

Theorem drive_sys_sound n rho F L ms m res :
  drive_sys code Rb Rc Lim rl keep xsys F L n = Some res ->
  DInv n rho F L ms m ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  sys_ok res ms m.
Proof.
  unfold drive_sys. intros Hsys HD Hstep.
  destruct (drive_sys_own code Rb Rc Lim rl keep F L n) as [r|] eqn:Hown.
  - injection Hsys as <-. exact (drive_sys_own_sound n rho F L ms m r Hown HD Hstep).
  - exact (xsys_sound n rho F L ms m res Hsys HD Hstep).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Variable xask : fstate -> option (int * int).

(* [comment removed for export] *)
Lemma mem_ok_rebound rho M m t rg clo chi :
  mem_ok segs IM rho M m -> iget t M = Some rg ->
  to_Z clo <= bv_unsigned (rho t) <= to_Z chi ->
  mem_ok segs IM rho (iset t (rebound rg clo chi) M) m.
Proof.
  intros [Hmem Hsep] Hg Hb. split.
  - intros t1 rg1 H1. rewrite iget_iset in H1. destruct (t1 =? t)%uint63 eqn:E.
    + apply Uint63.eqb_spec in E. subst t1. injection H1 as <-.
      destruct (Hmem t rg Hg) as [Hreg Hpages]. split.
      * destruct Hreg as (A1 & A2 & A3 & A4 & A5 & _ & A7). unfold region_ok, rebound.
        cbn [rg_lo rg_len rg_align rg_clo rg_chi rg_kind].
        split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
        split; [exact Hb | exact A7].
      * intros pn p Hpn Hp. exact (Hpages pn p Hpn Hp).
    + exact (Hmem t1 rg1 H1).
  - intros t1 t2 rg1 rg2 Hne H1 H2. rewrite iget_iset in H1, H2.
    destruct (t1 =? t)%uint63 eqn:E1; destruct (t2 =? t)%uint63 eqn:E2.
    + apply Uint63.eqb_spec in E1, E2. congruence.
    + injection H1 as <-. apply Uint63.eqb_spec in E1. subst t1. exact (Hsep t t2 rg rg2 Hne Hg H2).
    + injection H2 as <-. apply Uint63.eqb_spec in E2. subst t2. exact (Hsep t1 t rg1 rg Hne H1 Hg).
    + exact (Hsep t1 t2 rg1 rg2 Hne H1 H2).
Qed.

Lemma rebound_shape M t rg clo chi :
  iget t M = Some rg -> same_shape M (iset t (rebound rg clo chi) M).
Proof.
  intros Hg t'. rewrite iget_iset. destruct (t' =? t)%uint63 eqn:E.
  - apply Uint63.eqb_spec in E. subst t'. rewrite Hg. cbn. repeat split; reflexivity.
  - destruct (iget t' M); [repeat split; reflexivity | exact I].
Qed.

Lemma pristine_rebound M t rg clo chi t' :
  iget t M = Some rg -> pristine M t' -> pristine (iset t (rebound rg clo chi) M) t'.
Proof.
  intros Hg (Hne & rg' & Hg' & Hd & Hp). split; [exact Hne|]. rewrite iget_iset.
  destruct (t' =? t)%uint63 eqn:E.
  - apply Uint63.eqb_spec in E. subst t'. rewrite Hg in Hg'. injection Hg' as <-.
    exists (rebound rg clo chi). split; [reflexivity|]. split; [exact Hd | exact Hp].
  - exists rg'. split; [exact Hg'|]. split; [exact Hd | exact Hp].
Qed.

(* [comment removed for export] *)
Lemma DInv_rebound n rho F L ms m t rg clo chi :
  DInv n rho F L ms m -> iget t (f_mem F) = Some rg -> to_Z t < to_Z n ->
  to_Z clo <= bv_unsigned (rho t) <= to_Z chi ->
  DInv n rho (set_bounds F t rg clo chi) L ms m.
Proof.
  intros (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & Hbud & HXI & Hxt & Hfr) Hg C Hb.
  unfold DInv, set_bounds. cbn [f_mem].
  split.
  { intros rho' Hag. pose proof (HRn rho' Hag) as HR'. destruct HR' as [P1 P2 P3 P4 P5].
    constructor; cbn [f_pc f_regs f_mem f_resv]; try assumption.
    apply mem_ok_rebound; [exact P5 | exact Hg |]. rewrite (proj2 Hag t C). exact Hb. }
  split; [exact H0|]. split; [exact Hh|]. split; [exact Hnl|]. split; [exact Hli|].
  split; [exact (regions_covered_shape rho _ _ _ (rebound_shape _ t rg clo chi Hg) Hcov)|].
  split; [exact (mirror_shape rho L _ _ _ (rebound_shape _ t rg clo chi Hg) Hmir)|].
  split; [exact Hbud|]. split; [exact HXI|]. split; [exact Hxt|].
  intros t' Ht'. destruct (Hfr t' Ht') as [Hpr Hmem]. split; [exact (pristine_rebound _ t rg clo chi t' Hg Hpr)|].
  intros rg' x Hg' Hx. rewrite iget_iset in Hg'. destruct (t' =? t)%uint63 eqn:E.
  - apply Uint63.eqb_spec in E. subst t'. injection Hg' as <-. exact (Hmem rg x Hg Hx).
  - exact (Hmem rg' x Hg' Hx).
Qed.

(* [comment removed for export] *)
Lemma DInv_refine n rho F L ms m t thr Fa Fb :
  DInv n rho F L ms m -> refine_region F n t thr = Some (Fa, Fb) ->
  DInv n rho Fa L ms m \/ DInv n rho Fb L ms m.
Proof.
  intros HD Href. unfold refine_region in Href.
  destruct (iget t (f_mem F)) as [rg|] eqn:Hg; [|discriminate].
  match type of Href with (if ?c then _ else _) = _ => destruct c eqn:C end; [|discriminate].
  injection Href as <- <-.
  repeat match type of C with (_ && _ = true) =>
    let H' := fresh "Hc" in apply andb_true_iff in C as [C H'] end.
  apply ltb_spec in C, Hc0. apply leb_spec in Hc3, Hc1, Hc. apply Uint63.eqb_spec in Hc2.
  apply (f_equal to_Z) in Hc2. rewrite to_Z_land4095 in Hc2. change (to_Z 0) with 0 in Hc2.
  change (to_Z 12) with 12 in Hc3. change (to_Z 4096) with 4096 in Hc1.
  pose proof HD as (HRn & H0 & _).
  pose proof (Rn_R _ _ _ _ HRn H0) as HR.
  pose proof (R_region_ok _ _ _ _ _ HR Hg) as (_ & _ & _ & _ & Hal & [Hclo Hchi] & _).
  pose proof (align_4096 _ _ Hc3 Hal) as Hal12.
  assert (Hsub : to_Z (thr - 4096)%uint63 = to_Z thr - 4096).
  { rewrite sub_spec. change (to_Z 4096) with 4096. pose proof (i63_range thr) as Hthr. apply Z.mod_small.
    change wB with (2 ^ 63). clear - Hthr Hc1. lia. }
  assert (Hmk : forall clo chi, to_Z clo <= bv_unsigned (rho t) <= to_Z chi ->
            DInv n rho (set_bounds F t rg clo chi) L ms m)
    by (intros clo chi Hb; exact (DInv_rebound n rho F L ms m t rg clo chi HD Hg C Hb)).
  destruct (Z_lt_le_dec (bv_unsigned (rho t)) (to_Z thr)) as [Hlt|Hge].
  - left. apply Hmk. rewrite Hsub. split; [exact Hclo|].
    assert (E1 : bv_unsigned (rho t) = 4096 * (bv_unsigned (rho t) / 4096)) by (apply Z.div_exact; [clear; lia | exact Hal12]).
    assert (E2 : to_Z thr = 4096 * (to_Z thr / 4096)) by (apply Z.div_exact; [clear; lia | exact Hc2]).
    clear - Hlt E1 E2. lia.
  - right. apply Hmk. split; [exact Hge | exact Hchi].
Qed.

Local Abbreviation drv := (drive IM code Rb Rc Lim rl keep xsys xask).

(* [comment removed for export] *)
Theorem drive_universal : forall bp k, (k <= 61)%nat -> forall fuel n rho F L ms m T,
  DInv n rho F L ms m ->
  (forall F' L' n' r, leaf_in (F', L', n', r) (drv bp k fuel F L n) ->
     forall rho' ms' m', DInv n' rho' F' L' ms' m' ->
       (r = SEcall -> RiscvSemantics.step segs ms' = MachineOk (ms_pend ms')) ->
       realizes_cfg cfg segs (mkCfg ms' m') T) ->
  realizes_cfg cfg segs (mkCfg ms m) T.
Proof.
  intros bp k Hk. induction fuel as [|fuel IH]; intros n rho F L ms m T HD Hleaf.
  - apply (Hleaf F L n SFuel (eq_refl) rho ms m HD). discriminate.
  - cbn [drive] in Hleaf.
    destruct (fx_run IM code bp k F) as [[F1 r] cnt] eqn:Hrun.
    destruct (DInv_run n rho F L ms m bp k F1 r cnt Hk Hrun HD) as (ms1 & Hsteps & HD1 & Hec).
    pose proof HD as (_ & _ & Hh & Hnl & _).
    apply (rzc_rsteps cfg segs _ ms m ms1 T Hh (proj1 Hnl) Hsteps).
    destruct r as [| | |c].
    + (* [comment removed for export] *)
      exact (IH n rho F1 L ms1 m T HD1 Hleaf).
    + (* [comment removed for export] *)
      destruct (drive_sys code Rb Rc Lim rl keep xsys F1 L n) as [res|] eqn:Hsys.
      * destruct (drive_sys_sound n rho F1 L ms1 m res Hsys HD1 (Hec eq_refl))
          as (I & i0 & nx & Hiff & Hsucc).
        pose proof HD1 as (HRn1 & H01 & _).
        pose proof (R_svc _ _ _ _ _ (Rn_R _ _ _ _ HRn1 H01)) as Hsvc.
        apply (rzc_rsteps cfg segs 1 ms1 m (ms_pend ms1) T Hh (proj1 Hnl) (rsteps_pend ms1 Hsvc (Hec eq_refl))).
        apply (rzc_cases_same cfg segs _ I nx T i0).
        { apply node_ok_cfg_of_step_iff. exact Hiff. }
        intros i. destruct (Hsucc i) as (F' & L' & n' & rho' & ms' & m' & k' & Hin & Hk' & Hm' & HD').
        destruct (nx i) as [msi mi]. cbn [cfg_ms cfg_model] in Hk', Hm'. subst mi.
        pose proof HD' as (_ & _ & Hh' & Hnl' & _).
        apply (rzc_rsteps cfg segs k' msi m' ms' T Hh' (proj1 Hnl') Hk').
        apply (IH n' rho' F' L' ms' m' T HD').
        intros F'' L'' n'' r'' Hl. apply Hleaf.
        destruct res as [F2 L2 n2 | F2 L2 n2 F3 L3 n3]; cbn [dres_in] in Hin.
        -- injection Hin as -> -> ->. exact Hl.
        -- destruct Hin as [Hin|Hin]; injection Hin as -> -> ->; cbn [leaf_in]; [left | right]; exact Hl.
      * exact (Hleaf F1 L n SEcall eq_refl rho ms1 m HD1 Hec).
    + apply (Hleaf F1 L n SBreak eq_refl rho ms1 m HD1). discriminate.
    + (* [comment removed for export] *)
      destruct (ask_split xask F1 n) as [[Fa Fb]|] eqn:Hask.
      * unfold ask_split in Hask. destruct (xask F1) as [[ta thr]|]; [|discriminate].
        destruct (DInv_refine n rho F1 L ms1 m ta thr Fa Fb HD1 Hask) as [HDa|HDb].
        -- apply (IH n rho Fa L ms1 m T HDa). intros F'' L'' n'' r'' Hl. apply Hleaf. cbn [leaf_in]. left. exact Hl.
        -- apply (IH n rho Fb L ms1 m T HDb). intros F'' L'' n'' r'' Hl. apply Hleaf. cbn [leaf_in]. right. exact Hl.
      * apply (Hleaf F1 L n (SStuck c) eq_refl rho ms1 m HD1). discriminate.
Qed.

(* [comment removed for export] *)
Theorem drive_existential : forall bp k, (k <= 61)%nat -> forall fuel n rho F L ms m,
  DInv n rho F L ms m ->
  exists F' L' n' r rho' ms' m',
    leaf_in (F', L', n', r) (drv bp k fuel F L n)
    /\ star_cfg segs cfg (mkCfg ms m) [] (mkCfg ms' m')
    /\ DInv n' rho' F' L' ms' m'
    /\ (r = SEcall -> RiscvSemantics.step segs ms' = MachineOk (ms_pend ms')).
Proof.
  intros bp k Hk. induction fuel as [|fuel IH]; intros n rho F L ms m HD.
  - exists F, L, n, SFuel, rho, ms, m. split; [reflexivity|]. split; [apply star_cfg_refl|].
    split; [exact HD | discriminate].
  - cbn [drive].
    destruct (fx_run IM code bp k F) as [[F1 r] cnt] eqn:Hrun.
    destruct (DInv_run n rho F L ms m bp k F1 r cnt Hk Hrun HD) as (ms1 & Hsteps & HD1 & Hec).
    pose proof HD as (_ & _ & Hh & Hnl & _).
    pose proof (rsteps_star_cfg cfg segs _ ms m ms1 Hh (proj1 Hnl) Hsteps) as Hstar1.
    destruct r as [| | |c].
    + destruct (IH n rho F1 L ms1 m HD1) as (F' & L' & n' & r' & rho' & ms' & m' & Hl & Hst & HD' & He').
      exists F', L', n', r', rho', ms', m'. split; [exact Hl|]. split; [|split; assumption].
      exact (star_cfg_trans cfg segs _ [] _ [] _ Hstar1 Hst).
    + destruct (drive_sys code Rb Rc Lim rl keep xsys F1 L n) as [res|] eqn:Hsys.
      * destruct (drive_sys_sound n rho F1 L ms1 m res Hsys HD1 (Hec eq_refl))
          as (I & i0 & nx & Hiff & Hsucc).
        pose proof HD1 as (HRn1 & H01 & _).
        pose proof (R_svc _ _ _ _ _ (Rn_R _ _ _ _ HRn1 H01)) as Hsvc.
        pose proof (rsteps_star_cfg cfg segs 1 ms1 m (ms_pend ms1) Hh (proj1 Hnl)
                      (rsteps_pend ms1 Hsvc (Hec eq_refl))) as Hstar2.
        destruct (Hsucc i0) as (F2 & L2 & n2 & rho2 & ms2 & m2 & k2 & Hin & Hk2 & Hm2 & HD2).
        assert (Hstep : sstep_cfg segs cfg (mkCfg (ms_pend ms1) m) [] (SNext (nx i0))).
        { apply Hiff. exists i0. split; reflexivity. }
        destruct (nx i0) as [msi mi]. cbn [cfg_ms cfg_model] in Hk2, Hm2. subst mi.
        pose proof HD2 as (_ & _ & Hh2 & Hnl2 & _).
        pose proof (star_cfg_trans cfg segs _ [] _ [] _ (star_cfg_one cfg segs _ _ _ Hstep)
                      (rsteps_star_cfg cfg segs k2 msi m2 ms2 Hh2 (proj1 Hnl2) Hk2)) as Hstar3.
        destruct (IH n2 rho2 F2 L2 ms2 m2 HD2) as (F' & L' & n' & r' & rho' & ms' & m' & Hl & Hst & HD' & He').
        exists F', L', n', r', rho', ms', m'. split; [|split; [|split; assumption]].
        -- destruct res as [Fa La na | Fa La na Fb Lb nb]; cbn [dres_in] in Hin.
           ++ injection Hin as -> -> ->. exact Hl.
           ++ destruct Hin as [Hin|Hin]; injection Hin as -> -> ->; cbn [leaf_in]; [left | right]; exact Hl.
        -- exact (star_cfg_trans cfg segs _ [] _ [] _ Hstar1
                    (star_cfg_trans cfg segs _ [] _ [] _ Hstar2
                       (star_cfg_trans cfg segs _ [] _ [] _ Hstar3 Hst))).
      * exists F1, L, n, SEcall, rho, ms1, m. split; [reflexivity|]. split; [exact Hstar1|]. split; assumption.
    + exists F1, L, n, SBreak, rho, ms1, m. split; [reflexivity|]. split; [exact Hstar1|].
      split; [exact HD1 | discriminate].
    + destruct (ask_split xask F1 n) as [[Fa Fb]|] eqn:Hask.
      * unfold ask_split in Hask. destruct (xask F1) as [[ta thr]|]; [|discriminate].
        destruct (DInv_refine n rho F1 L ms1 m ta thr Fa Fb HD1 Hask) as [HDa|HDb].
        -- destruct (IH n rho Fa L ms1 m HDa) as (F' & L' & n' & r' & rho' & ms' & m' & Hl & Hst & HD' & He').
           exists F', L', n', r', rho', ms', m'. split; [cbn [leaf_in]; left; exact Hl|].
           split; [exact (star_cfg_trans cfg segs _ [] _ [] _ Hstar1 Hst)|]. split; assumption.
        -- destruct (IH n rho Fb L ms1 m HDb) as (F' & L' & n' & r' & rho' & ms' & m' & Hl & Hst & HD' & He').
           exists F', L', n', r', rho', ms', m'. split; [cbn [leaf_in]; right; exact Hl|].
           split; [exact (star_cfg_trans cfg segs _ [] _ [] _ Hstar1 Hst)|]. split; assumption.
      * exists F1, L, n, (SStuck c), rho, ms1, m. split; [reflexivity|]. split; [exact Hstar1|].
        split; [exact HD1 | discriminate].
Qed.

(* [comment removed for export] *)
Corollary DInv_frame n rho F L ms m t rg x :
  DInv n rho F L ms m -> In t keep -> iget t (f_mem F) = Some rg ->
  in_ival rho t rg (bv_unsigned x) -> ms_mem ms x = mem0 x.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr) Ht Hg Hx. exact (proj2 (Hfr t Ht) rg x Hg Hx).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma DInv_same_mem n rho F F' L ms ms' m :
  DInv n rho F L ms m ->
  f_mem F' = f_mem F -> ms_mem ms' = ms_mem ms ->
  Rn n rho F' ms' -> budget ms' m ->
  DInv n rho F' L ms' m.
Proof.
  intros (_ & H0 & Hh & Hnl & Hli & Hcov & Hmir & _ & HXI & Hxt & Hfr) HM Hmem HRn' Hbud'.
  unfold DInv. rewrite HM, Hmem. repeat (split; [assumption|]). exact Hfr.
Qed.

(* [comment removed for export] *)
Lemma DInv_fresh_tag n rho a F F' L ms ms' m :
  DInv n rho F L ms m ->
  to_Z n < 2 ^ 60 -> regions_lt n (f_mem F) ->
  f_mem F' = f_mem F -> ms_mem ms' = ms_mem ms ->
  Rn (n + 1)%uint63 (rho_upd rho n a) F' ms' -> budget ms' m ->
  DInv (n + 1)%uint63 (rho_upd rho n a) F' L ms' m.
Proof.
  intros (HRn & H0 & Hh & Hnl & Hli & Hcov & Hmir & _ & HXI & Hxt & Hfr) Hn61 Hlt HM Hmem HRn' Hbud'.
  set (rho' := rho_upd rho n a).
  assert (Hrho : forall t rg, iget t (f_mem F) = Some rg -> rho' t = rho t).
  { intros t rg Hg. exact (regions_lt_rho rho n a _ _ _ Hlt Hg). }
  pose proof (Rn_R _ _ _ _ HRn H0) as HR.
  assert (Hn0 : n <> 0%uint63).
  { intros ->. destruct Hmir as (_ & _ & rgb & Hgb & _). pose proof (Hlt _ _ Hgb) as Hb.
    rewrite to_Z_0 in Hb. pose proof (i63_range (fl_brk L)). lia. }
  unfold DInv. rewrite HM, Hmem. split; [exact HRn'|].
  split. { unfold rho'. rewrite rho_upd_other; [exact H0 | intros E; apply Hn0; symmetry; exact E]. }
  split; [exact Hh|]. split; [exact Hnl|]. split; [exact Hli|].
  split.
  { intros t rg Hg. destruct (Hcov t rg Hg) as [Hne Hb]. split; [exact Hne|].
    intros x Hx. apply Hb. exact (in_ival_rho rho rho' t rg x (Hrho t rg Hg) Hx). }
  split.
  { destruct Hmir as (Hm1 & Hm2 & rgb & Hgb & Hbrk). split; [|split].
    - eapply Forall_impl; [|exact Hm1]. intros e He. destruct (ent_ok_tag _ _ _ _ He) as [rg Hrg].
      apply (ent_ok_ext rho rho' (f_mem F) (f_mem F) _ _ e (Hrho _ _ Hrg) eq_refl (fun p Hp => Hp) He).
    - eapply Forall_impl; [|exact Hm2]. intros e He. destruct (ent_ok_tag _ _ _ _ He) as [rg Hrg].
      apply (ent_ok_ext rho rho' (f_mem F) (f_mem F) _ _ e (Hrho _ _ Hrg) eq_refl (fun p Hp => Hp) He).
    - exists rgb. split; [exact Hgb|]. rewrite (adr_rho rho rho' _ _ (Hrho _ _ Hgb)). exact Hbrk. }
  split; [exact Hbud'|].
  split.
  { apply (XI_rho rho rho'); [|exact HXI]. intros tx Htx. unfold rho'. apply rho_upd_other.
    apply lt_neq. exact (Hxt tx Htx). }
  split; [intros tx Htx; rewrite (to_Z_succ61 n Hn61); pose proof (Hxt tx Htx); lia|].
  intros t Ht. destruct (Hfr t Ht) as [Hpr Hm0]. split; [exact Hpr|].
  intros rg x Hg Hx. apply (Hm0 rg x Hg). exact (in_ival_rho rho rho' t rg _ (Hrho t rg Hg) Hx).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Hypothesis xsys_soundX : forall n rho F L ms m res,
  xsys F L n = Some res -> DInv n rho F L ms m ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  sys_okX n rho F L res ms m.

Theorem drive_sys_soundX n rho F L ms m res :
  drive_sys code Rb Rc Lim rl keep xsys F L n = Some res ->
  DInv n rho F L ms m ->
  RiscvSemantics.step segs ms = MachineOk (ms_pend ms) ->
  sys_okX n rho F L res ms m.
Proof.
  unfold drive_sys. intros Hsys HD Hstep.
  destruct (drive_sys_own code Rb Rc Lim rl keep F L n) as [r|] eqn:Hown.
  - injection Hsys as <-. exact (drive_sys_own_soundX n rho F L ms m r Hown HD Hstep).
  - exact (xsys_soundX n rho F L ms m res Hsys HD Hstep).
Qed.

Variable fr0 : bvmap 5 word.
Variable fc0 : bv 32.
Variable rom0 : word -> option byte.
Variable hi : word -> Prop.

Definition DInvX (n : int) (rho : int -> word) (F : fstate) (L : fledger)
                 (ms : machine_state) (m : Model) : Prop :=
  DInv n rho F L ms m
  /\ ms_fregs ms = fr0 /\ ms_fcsr ms = fc0 /\ ms_rom ms = rom0
  /\ (forall x, hi x -> alloc_top (m_vmmaps m) <= bv_unsigned x
                      /\ no_region rho (f_mem F) (bv_unsigned x)
                      /\ ms_mem ms x = mem0 x)
  /\ exact rho L (m_vmmaps m).

Lemma DInvX_DInv n rho F L ms m : DInvX n rho F L ms m -> DInv n rho F L ms m.
Proof. intros H. exact (proj1 H). Qed.

(* [comment removed for export] *)
Definition dext (n : int) (rho : int -> word) (m : Model) (n' : int) (rho' : int -> word) (m' : Model) : Prop :=
  to_Z n <= to_Z n' /\ (forall t, to_Z t < to_Z n -> rho' t = rho t) /\ same_but_vm m m'
  /\ vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m)
  /\ vm_start_brk (m_vmmaps m') = vm_start_brk (m_vmmaps m)
  /\ vm_mmap_base (m_vmmaps m') = vm_mmap_base (m_vmmaps m).

Lemma dext_refl n rho m : dext n rho m n rho m.
Proof.
  split; [lia|]. split; [intros; reflexivity|]. split; [apply same_but_vm_refl|].
  repeat split; reflexivity.
Qed.

Lemma dext_trans n0 rho0 m0 n1 rho1 m1 n2 rho2 m2 :
  dext n0 rho0 m0 n1 rho1 m1 -> dext n1 rho1 m1 n2 rho2 m2 -> dext n0 rho0 m0 n2 rho2 m2.
Proof.
  intros (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6). split; [lia|]. split; [|split].
  - intros t Ht. rewrite (B2 t ltac:(lia)). exact (A2 t Ht).
  - exact (same_but_vm_trans _ _ _ A3 B3).
  - repeat split; congruence.
Qed.

(* [comment removed for export] *)
Lemma claimed_in_region rho F ms x :
  R segs IM rho F ms -> claimed_wr IM rho (f_mem F) x ->
  exists t rg, iget t (f_mem F) = Some rg /\ in_ival rho t rg (bv_unsigned x).
Proof.
  intros HR (t1 & rg1 & pn & p & j & Hg1 & Hpn & Hp & Hw & Hj & Hhi & ->).
  destruct (proj1 (R_mem _ _ _ _ _ HR) t1 rg1 Hg1) as [Hreg Hpages].
  destruct (Hpages pn p Hpn Hp) as (_ & Hlo & _).
  pose proof (region_ok_nowrap _ _ _ Hreg) as Hnw.
  pose proof (i63_range pn) as Hpn0. pose proof (i63_range (rg_lo rg1)) as Hl0.
  exists t1, rg1. split; [exact Hg1|]. rewrite adr_unsigned by lia. unfold in_ival. lia.
Qed.

(* [comment removed for export] *)
Lemma DInvX_run n rho F L ms m bp k F1 r cnt :
  (k <= 61)%nat ->
  fx_run IM code bp k F = (F1, r, cnt) ->
  DInvX n rho F L ms m ->
  exists ms1, rsteps segs (nat_of_int cnt) ms = MachineOk ms1
    /\ DInvX n rho F1 L ms1 m
    /\ (r = SEcall -> RiscvSemantics.step segs ms1 = MachineOk (ms_pend ms1)).
Proof.
  intros Hk Hrun (HD & Hfr & Hfc & Hrom & Hhi & Hex).
  destruct (DInv_run n rho F L ms m bp k F1 r cnt Hk Hrun HD) as (ms1 & Hsteps & HD1 & Hec).
  pose proof HD as (HRn & H0 & _).
  destruct (fx_run_Rn segs IM code Hcode n rho bp k F F1 r cnt ms Hk Hrun H0 HRn)
    as (ms1' & Hsteps' & _ & _ & Hframe & _ & Erom).
  rewrite Hsteps in Hsteps'. injection Hsteps' as <-.
  destruct (fx_run_Rn_shape segs IM code Hcode n rho bp k F F1 r cnt ms ms1 Hk Hrun H0 HRn Hsteps)
    as [Efr Efc].
  pose proof (fx_run_shape _ _ _ _ _ _ Hrun) as Hshape.
  exists ms1. split; [exact Hsteps|]. split; [|exact Hec].
  split; [exact HD1|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
  split; [|exact Hex].
  intros x Hx. destruct (Hhi x Hx) as (Ht & Hno & Hm). split; [exact Ht|]. split.
  - intros t rg' Hg' Hin. destruct (same_shape_get _ _ _ _ Hshape Hg') as (rg0 & Hg0 & E1 & E2).
    apply (Hno t rg0 Hg0). exact (in_ival_shape rho t rg0 rg' _ E1 E2 Hin).
  - rewrite Hframe; [exact Hm|]. intros Hc.
    destruct (claimed_in_region rho F ms x (Rn_R _ _ _ _ HRn H0) Hc) as (t & rg & Hg & Hin).
    exact (Hno t rg Hg Hin).
Qed.

(* [comment removed for export] *)
Lemma DInvX_node n rho F L ms m n' rho' F' L' ms' m' :
  DInvX n rho F L ms m -> DInv n' rho' F' L' ms' m' ->
  node_ext n rho F L ms m n' rho' F' L' ms' m' ->
  DInvX n' rho' F' L' ms' m' /\ dext n rho m n' rho' m'.
Proof.
  intros (HD & Hfr & Hfc & Hrom & Hhi & Hex) HD' [Hn Hrho Efr Efc Erom Hvm Hsp Hhigh Hsb Hmb Hexact].
  split; [|split; [exact Hn | split; [exact Hrho | split; [exact Hvm | repeat split; assumption]]]].
  split; [exact HD'|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
  split; [|exact (Hexact HD Hex)].
  intros x Hx. destruct (Hhi x Hx) as (Ht & Hno & Hm).
  destruct (Hhigh x Ht Hno) as [Em Hno']. split; [|split; [exact Hno' | congruence]].
  unfold alloc_top in *. rewrite Hsp. exact Ht.
Qed.

(* [comment removed for export] *)
Lemma DInvX_refine n rho F L ms m t thr Fa Fb :
  DInvX n rho F L ms m -> refine_region F n t thr = Some (Fa, Fb) ->
  DInvX n rho Fa L ms m \/ DInvX n rho Fb L ms m.
Proof.
  intros (HD & Hfr & Hfc & Hrom & Hhi & Hex) Href.
  assert (Hno : forall F', (F' = Fa \/ F' = Fb) -> forall x, hi x ->
            alloc_top (m_vmmaps m) <= bv_unsigned x /\ no_region rho (f_mem F') (bv_unsigned x)
            /\ ms_mem ms x = mem0 x).
  { intros F' HF' x Hx. destruct (Hhi x Hx) as (Ht & Hno & Hm). split; [exact Ht|]. split; [|exact Hm].
    unfold refine_region in Href. destruct (iget t (f_mem F)) as [rg|] eqn:Hg; [|discriminate].
    match type of Href with (if ?c then _ else _) = _ => destruct c end; [|discriminate].
    injection Href as <- <-.
    assert (Hs : exists clo chi, f_mem F' = iset t (rebound rg clo chi) (f_mem F)).
    { destruct HF' as [-> | ->]; eexists _, _; reflexivity. }
    destruct Hs as (clo & chi & ->).
    intros t' rg' Hg' Hin.
    destruct (same_shape_get _ _ _ _ (rebound_shape _ t rg clo chi Hg) Hg') as (rg0 & Hg0 & E1 & E2).
    apply (Hno t' rg0 Hg0). exact (in_ival_shape rho t' rg0 rg' _ E1 E2 Hin). }
  destruct (DInv_refine n rho F L ms m t thr Fa Fb HD Href) as [HDa|HDb]; [left | right].
  - split; [exact HDa|]. split; [exact Hfr|]. split; [exact Hfc|]. split; [exact Hrom|].
    split; [apply Hno; left; reflexivity | exact Hex].
  - split; [exact HDb|]. split; [exact Hfr|]. split; [exact Hfc|]. split; [exact Hrom|].
    split; [apply Hno; right; reflexivity | exact Hex].
Qed.

(* [comment removed for export] *)
Theorem drive_universalX : forall bp k, (k <= 61)%nat -> forall fuel n rho F L ms m T,
  DInvX n rho F L ms m ->
  (forall F' L' n' r, leaf_in (F', L', n', r) (drv bp k fuel F L n) ->
     forall rho' ms' m', DInvX n' rho' F' L' ms' m' -> dext n rho m n' rho' m' ->
       (r = SEcall -> RiscvSemantics.step segs ms' = MachineOk (ms_pend ms')) ->
       realizes_cfg cfg segs (mkCfg ms' m') T) ->
  realizes_cfg cfg segs (mkCfg ms m) T.
Proof.
  intros bp k Hk fuel n0 rho0 F0 L0 ms0 m0 T HD0 Hleaf0.
  (* [comment removed for export] *)
  cut (forall fuel n rho F L ms m,
         DInvX n rho F L ms m -> dext n0 rho0 m0 n rho m ->
         (forall F' L' n' r, leaf_in (F', L', n', r) (drv bp k fuel F L n) ->
            forall rho' ms' m', DInvX n' rho' F' L' ms' m' -> dext n0 rho0 m0 n' rho' m' ->
              (r = SEcall -> RiscvSemantics.step segs ms' = MachineOk (ms_pend ms')) ->
              realizes_cfg cfg segs (mkCfg ms' m') T) ->
         realizes_cfg cfg segs (mkCfg ms m) T).
  { intros Hgen. exact (Hgen fuel n0 rho0 F0 L0 ms0 m0 HD0 (dext_refl _ _ _) Hleaf0). }
  clear fuel F0 L0 ms0 HD0 Hleaf0.
  induction fuel as [|fuel IH]; intros n rho F L ms m HD Hext Hleaf.
  - apply (Hleaf F L n SFuel (eq_refl) rho ms m HD Hext). discriminate.
  - cbn [drive] in Hleaf.
    destruct (fx_run IM code bp k F) as [[F1 r] cnt] eqn:Hrun.
    destruct (DInvX_run n rho F L ms m bp k F1 r cnt Hk Hrun HD) as (ms1 & Hsteps & HD1 & Hec).
    pose proof (DInvX_DInv _ _ _ _ _ _ HD) as (_ & _ & Hh & Hnl & _).
    apply (rzc_rsteps cfg segs _ ms m ms1 T Hh (proj1 Hnl) Hsteps).
    destruct r as [| | |c].
    + exact (IH n rho F1 L ms1 m HD1 Hext Hleaf).
    + destruct (drive_sys code Rb Rc Lim rl keep xsys F1 L n) as [res|] eqn:Hsys.
      * destruct (drive_sys_soundX n rho F1 L ms1 m res Hsys (DInvX_DInv _ _ _ _ _ _ HD1) (Hec eq_refl))
          as (I & i0 & nx & Hiff & Hsucc).
        pose proof (DInvX_DInv _ _ _ _ _ _ HD1) as (HRn1 & H01 & _).
        pose proof (R_svc _ _ _ _ _ (Rn_R _ _ _ _ HRn1 H01)) as Hsvc.
        apply (rzc_rsteps cfg segs 1 ms1 m (ms_pend ms1) T Hh (proj1 Hnl) (rsteps_pend ms1 Hsvc (Hec eq_refl))).
        apply (rzc_cases_same cfg segs _ I nx T i0).
        { apply node_ok_cfg_of_step_iff. exact Hiff. }
        intros i. destruct (Hsucc i) as (F' & L' & n' & rho' & ms' & m' & k' & Hin & Hk' & Hm' & HD' & Hne).
        destruct (nx i) as [msi mi]. cbn [cfg_ms cfg_model] in Hk', Hm'. subst mi.
        pose proof HD' as (_ & _ & Hh' & Hnl' & _).
        apply (rzc_rsteps cfg segs k' msi m' ms' T Hh' (proj1 Hnl') Hk').
        destruct (DInvX_node _ _ _ _ _ _ _ _ _ _ _ _ HD1 HD' Hne) as [HDX' Hext'].
        apply (IH n' rho' F' L' ms' m' HDX' (dext_trans _ _ _ _ _ _ _ _ _ Hext Hext')).
        intros F'' L'' n'' r'' Hl. apply Hleaf.
        destruct res as [F2 L2 n2 | F2 L2 n2 F3 L3 n3]; cbn [dres_in] in Hin.
        -- injection Hin as -> -> ->. exact Hl.
        -- destruct Hin as [Hin|Hin]; injection Hin as -> -> ->; cbn [leaf_in]; [left | right]; exact Hl.
      * exact (Hleaf F1 L n SEcall eq_refl rho ms1 m HD1 Hext Hec).
    + apply (Hleaf F1 L n SBreak eq_refl rho ms1 m HD1 Hext). discriminate.
    + destruct (ask_split xask F1 n) as [[Fa Fb]|] eqn:Hask.
      * unfold ask_split in Hask. destruct (xask F1) as [[ta thr]|]; [|discriminate].
        destruct (DInvX_refine n rho F1 L ms1 m ta thr Fa Fb HD1 Hask) as [HDa|HDb].
        -- apply (IH n rho Fa L ms1 m HDa Hext). intros F'' L'' n'' r'' Hl. apply Hleaf. cbn [leaf_in]. left. exact Hl.
        -- apply (IH n rho Fb L ms1 m HDb Hext). intros F'' L'' n'' r'' Hl. apply Hleaf. cbn [leaf_in]. right. exact Hl.
      * apply (Hleaf F1 L n (SStuck c) eq_refl rho ms1 m HD1 Hext). discriminate.
Qed.

(* [comment removed for export] *)
Theorem drive_existentialX : forall bp k, (k <= 61)%nat -> forall fuel n rho F L ms m,
  DInvX n rho F L ms m ->
  exists F' L' n' r rho' ms' m',
    leaf_in (F', L', n', r) (drv bp k fuel F L n)
    /\ star_cfg segs cfg (mkCfg ms m) [] (mkCfg ms' m')
    /\ DInvX n' rho' F' L' ms' m'
    /\ dext n rho m n' rho' m'
    /\ (r = SEcall -> RiscvSemantics.step segs ms' = MachineOk (ms_pend ms')).
Proof.
  intros bp k Hk. induction fuel as [|fuel IH]; intros n rho F L ms m HD.
  - exists F, L, n, SFuel, rho, ms, m. split; [reflexivity|]. split; [apply star_cfg_refl|].
    split; [exact HD|]. split; [apply dext_refl | discriminate].
  - cbn [drive].
    destruct (fx_run IM code bp k F) as [[F1 r] cnt] eqn:Hrun.
    destruct (DInvX_run n rho F L ms m bp k F1 r cnt Hk Hrun HD) as (ms1 & Hsteps & HD1 & Hec).
    pose proof (DInvX_DInv _ _ _ _ _ _ HD) as (_ & _ & Hh & Hnl & _).
    pose proof (rsteps_star_cfg cfg segs _ ms m ms1 Hh (proj1 Hnl) Hsteps) as Hstar1.
    destruct r as [| | |c].
    + destruct (IH n rho F1 L ms1 m HD1) as (F' & L' & n' & r' & rho' & ms' & m' & Hl & Hst & HD' & Hext' & He').
      exists F', L', n', r', rho', ms', m'. split; [exact Hl|]. split; [|split; [exact HD' | split; assumption]].
      exact (star_cfg_trans cfg segs _ [] _ [] _ Hstar1 Hst).
    + destruct (drive_sys code Rb Rc Lim rl keep xsys F1 L n) as [res|] eqn:Hsys.
      * destruct (drive_sys_soundX n rho F1 L ms1 m res Hsys (DInvX_DInv _ _ _ _ _ _ HD1) (Hec eq_refl))
          as (I & i0 & nx & Hiff & Hsucc).
        pose proof (DInvX_DInv _ _ _ _ _ _ HD1) as (HRn1 & H01 & _).
        pose proof (R_svc _ _ _ _ _ (Rn_R _ _ _ _ HRn1 H01)) as Hsvc.
        pose proof (rsteps_star_cfg cfg segs 1 ms1 m (ms_pend ms1) Hh (proj1 Hnl)
                      (rsteps_pend ms1 Hsvc (Hec eq_refl))) as Hstar2.
        destruct (Hsucc i0) as (F2 & L2 & n2 & rho2 & ms2 & m2 & k2 & Hin & Hk2 & Hm2 & HD2 & Hne2).
        assert (Hstep : sstep_cfg segs cfg (mkCfg (ms_pend ms1) m) [] (SNext (nx i0))).
        { apply Hiff. exists i0. split; reflexivity. }
        destruct (nx i0) as [msi mi]. cbn [cfg_ms cfg_model] in Hk2, Hm2. subst mi.
        pose proof HD2 as (_ & _ & Hh2 & Hnl2 & _).
        pose proof (star_cfg_trans cfg segs _ [] _ [] _ (star_cfg_one cfg segs _ _ _ Hstep)
                      (rsteps_star_cfg cfg segs k2 msi m2 ms2 Hh2 (proj1 Hnl2) Hk2)) as Hstar3.
        destruct (DInvX_node _ _ _ _ _ _ _ _ _ _ _ _ HD1 HD2 Hne2) as [HDX2 Hext2].
        destruct (IH n2 rho2 F2 L2 ms2 m2 HDX2) as (F' & L' & n' & r' & rho' & ms' & m' & Hl & Hst & HD' & Hext' & He').
        exists F', L', n', r', rho', ms', m'. split; [|split; [|split; [exact HD' | split; [|exact He']]]].
        -- destruct res as [Fa La na | Fa La na Fb Lb nb]; cbn [dres_in] in Hin.
           ++ injection Hin as -> -> ->. exact Hl.
           ++ destruct Hin as [Hin|Hin]; injection Hin as -> -> ->; cbn [leaf_in]; [left | right]; exact Hl.
        -- exact (star_cfg_trans cfg segs _ [] _ [] _ Hstar1
                    (star_cfg_trans cfg segs _ [] _ [] _ Hstar2
                       (star_cfg_trans cfg segs _ [] _ [] _ Hstar3 Hst))).
        -- exact (dext_trans _ _ _ _ _ _ _ _ _ Hext2 Hext').
      * exists F1, L, n, SEcall, rho, ms1, m. split; [reflexivity|]. split; [exact Hstar1|].
        split; [exact HD1|]. split; [apply dext_refl | exact Hec].
    + exists F1, L, n, SBreak, rho, ms1, m. split; [reflexivity|]. split; [exact Hstar1|].
      split; [exact HD1|]. split; [apply dext_refl | discriminate].
    + destruct (ask_split xask F1 n) as [[Fa Fb]|] eqn:Hask.
      * unfold ask_split in Hask. destruct (xask F1) as [[ta thr]|]; [|discriminate].
        destruct (DInvX_refine n rho F1 L ms1 m ta thr Fa Fb HD1 Hask) as [HDa|HDb].
        -- destruct (IH n rho Fa L ms1 m HDa) as (F' & L' & n' & r' & rho' & ms' & m' & Hl & Hst & HD' & Hext' & He').
           exists F', L', n', r', rho', ms', m'. split; [cbn [leaf_in]; left; exact Hl|].
           split; [exact (star_cfg_trans cfg segs _ [] _ [] _ Hstar1 Hst)|]. split; [exact HD' | split; assumption].
        -- destruct (IH n rho Fb L ms1 m HDb) as (F' & L' & n' & r' & rho' & ms' & m' & Hl & Hst & HD' & Hext' & He').
           exists F', L', n', r', rho', ms', m'. split; [cbn [leaf_in]; right; exact Hl|].
           split; [exact (star_cfg_trans cfg segs _ [] _ [] _ Hstar1 Hst)|]. split; [exact HD' | split; assumption].
      * exists F1, L, n, (SStuck c), rho, ms1, m. split; [reflexivity|]. split; [exact Hstar1|].
        split; [exact HD1|]. split; [apply dext_refl | discriminate].
Qed.

(* [comment removed for export] *)
Lemma DInvX_shape n rho F L ms m :
  DInvX n rho F L ms m -> ms_fregs ms = fr0 /\ ms_fcsr ms = fc0 /\ ms_rom ms = rom0.
Proof. intros (_ & A & B & C & _). repeat split; assumption. Qed.

Lemma DInvX_high n rho F L ms m x : DInvX n rho F L ms m -> hi x -> ms_mem ms x = mem0 x.
Proof. intros (_ & _ & _ & _ & H & _) Hx. exact (proj2 (proj2 (H x Hx))). Qed.

(* [comment removed for export] *)
Lemma DInvX_exact n rho F L ms m :
  DInvX n rho F L ms m ->
  vm_maps (m_vmmaps m) = map (den rho) (fl_maps L)
  /\ vm_noaccess (m_vmmaps m) = map (den rho) (fl_na L).
Proof. intros (_ & _ & _ & _ & _ & H). exact H. Qed.

(* [comment removed for export] *)
Lemma DInvX_vmmaps n rho F L ms m :
  DInvX n rho F L ms m ->
  exists rgb, iget (fl_brk L) (f_mem F) = Some rgb
    /\ vm_limit (m_vmmaps m) = Lim                                  (* [comment removed for export] *)
    /\ m_vmmaps m = mkVmMapsFull R0 (map (den rho) (fl_maps L)) (map (den rho) (fl_na L))
                      (vm_start_brk (m_vmmaps m)) (adr rho (fl_brk L) (to_Z (rg_len rgb))) (vm_limit (m_vmmaps m))
                      (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)).
Proof.
  intros ((_ & _ & _ & _ & Hli & _ & (_ & _ & rgb & Hgb & Hbrk) & _) & _ & _ & _ & _ & [E1 E2]).
  exists rgb. split; [exact Hgb|].
  pose proof (li_reserved _ _ _ _ _ Hli) as ER. pose proof (li_limit _ _ _ _ _ Hli) as EL.
  destruct (m_vmmaps m) as [r mp na sb b lim mb sp]. cbn [vm_reserved vm_maps vm_noaccess vm_start_brk
    vm_brk vm_limit vm_mmap_base vm_init_sp] in *. subst. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma DInv_nolazy n rho F L ms m : DInv n rho F L ms m -> model_nolazy m.
Proof. intros (_ & _ & _ & H & _). exact H. Qed.

Lemma DInv_pc n rho F L ms m : DInv n rho F L ms m -> ms_pc_val ms = Z_to_bv 64 (to_Z (f_pc F)).
Proof. intros (HRn & H0 & _). exact (R_pc _ _ _ _ _ (Rn_R _ _ _ _ HRn H0)). Qed.

Lemma DInv_svc n rho F L ms m : DInv n rho F L ms m -> ms_svc_pending ms = None.
Proof. intros (HRn & H0 & _). exact (R_svc _ _ _ _ _ (Rn_R _ _ _ _ HRn H0)). Qed.

Lemma DInv_resv n rho F L ms m : DInv n rho F L ms m -> f_resv F = None -> ms_resv ms = None.
Proof.
  intros (HRn & H0 & _) Hr. rewrite (R_resv _ _ _ _ _ (Rn_R _ _ _ _ HRn H0)), Hr. reflexivity.
Qed.

Lemma DInv_reg n rho F L ms m (r : reg) :
  DInv n rho F L ms m -> Sem.rget (core_of ms) r = dv rho (FxState.rget F (ireg r)).
Proof. intros (HRn & H0 & _). exact (R_regs _ _ _ _ _ (Rn_R _ _ _ _ HRn H0) r). Qed.

End Drive.
