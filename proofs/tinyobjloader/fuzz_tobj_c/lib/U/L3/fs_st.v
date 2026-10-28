From Stdlib Require Import ZArith List Bool PArith.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymCFG SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjXform ObjUnbase TobjJV TobjJVA.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Code.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr S_aa S_vp.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require S_vf S_ad.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require Import S_fs.
Import ListNotations.
Open Scope Z_scope.

Definition off (k : Z) : Z := fs_entry + k.
Definition mc_entry : Z := U.Code.StrAddr.memcpy_entry.
Definition FUEL_fs : nat := 3000%nat.
Definition cutpcs_fs : list Z :=
  [S_aa.aa_entry; S_vf.vf_entry; S_vp.vp_entry; S_ad.ad_entry; mc_entry;
   off 164; off 228; off 404; off 536; off 672; off 852;
   off 368; off 500; off 636; off 816; off 1036].

Definition run_of (S : sstate) : list sstate :=
  match sym_run segsU FUEL_fs cutpcs_fs S true with Some ls => map lf_state ls | None => [] end.
Definition leaves_at (S : sstate) (pc : Z) : list sstate := List.filter (fun l => Z.eqb (ss_pc l) pc) (run_of S).
Definition optS (x : option sstate) : sstate := match x with Some s => s | None => Pre_fs end.
Definition optR (x : option (list sobj)) : list sobj := match x with Some r => r | None => [] end.

Definition in_facts (f : sprop) (l : list sprop) : bool := existsb (sprop_eqb f) l.
Definition common_facts (L : sstate) (Ls : list sstate) : list sprop :=
  filter (fun f => forallb (fun M => in_facts f (ss_facts M)) Ls) (ss_facts L).

(* L with the registers rs replaced by fresh variables and the facts replaced by facts. *)
Fixpoint fresh_regs (regs : list sv) (rs : list nat) (nx : positive) : list sv * positive :=
  match rs with
  | [] => (regs, nx)
  | r :: t => fresh_regs (list_set regs r (SVar nx)) t (Pos.succ nx)
  end.
Definition gen (L : sstate) (pc : Z) (rs : list nat) (facts : list sprop) : sstate :=
  let '(regs, nx) := fresh_regs (ss_regs L) rs (ss_next L) in
  mkSS pc regs (ss_fregs L) (ss_fcsr L) (ss_resv L) (ss_objs L) facts nx (ss_lenient L).

Definition G_go : list sstate := leaves_at Pre_fs (off 164).
Definition C_go : sstate := Eval vm_compute in
  gen (nth 0 G_go Pre_fs) (off 164) [10%nat; 11%nat] (common_facts (nth 0 G_go Pre_fs) G_go).

Definition PreA1 : sstate := S_aa.Pre_aa 1.
Definition E_nm : sstate := Eval vm_compute in nth 0 (leaves_at C_go S_aa.aa_entry) Pre_fs.
Definition s_nm : wsub := (19%positive, dlo) :: infer_sub 10 E_nm PreA1.
Definition R_nm : list sobj := Eval vm_compute in optR (entails_fr E_nm PreA1 s_nm).
Definition T_nm_fail : sstate := Eval vm_compute in T_afterN NF E_nm s_nm R_nm S_aa.P_fail.
Definition T_nm_ok : sstate := Eval vm_compute in T_afterN NF E_nm s_nm R_nm (S_aa.P_ok 1).

(* after an aa call: post objects [frame; stack; arena; hdr; slot] first, then the 27 frame objects *)
Definition perm_aa : list nat := ([5; 0; 1] ++ seq 6 18 ++ [2] ++ seq 24 8 ++ [3; 4])%nat.
Definition C_nm_ok : sstate := Eval vm_compute in optS (apply_xforms T_nm_ok [XSelect perm_aa]).

Definition closeX (X : sstate) : sstate :=
  let n := length (ss_objs X) in
  drop_last_state (drop_last_state X (firstn (n - 1) (ss_objs X))) (firstn (n - 2) (ss_objs X)).

(* Join states by anti-unification: positions where the leaves differ get fresh variables, facts are kept when
   every leaf has them (up to the renaming and to the normal forms nsv/nsp). *)
Fixpoint nsv (e : sv) : sv :=
  match e with
  | SAlu ALU_ADD x (SLit k) =>
      match nsv x with SAlu ALU_ADD y (SLit j) => SAlu ALU_ADD y (SLit (j + k)) | y => SAlu ALU_ADD y (SLit k) end
  | SAlu op a b => SAlu op (nsv a) (nsv b)
  | SAluW op a b => SAluW op (nsv a) (nsv b)
  | SMd op a b => SMd op (nsv a) (nsv b)
  | SMdW op a b => SMdW op (nsv a) (nsv b)
  | SExt s w a => SExt s w (nsv a)
  | SLBytes l i k => SLBytes l (nsv i) k
  | _ => e
  end.
Definition sveq (a b : sv) : bool := sv_eqb a b || sv_eqb (nsv a) (nsv b).
Definition negc (c : branch_cond) : branch_cond :=
  match c with BC_EQ => BC_NE | BC_NE => BC_EQ | BC_LT => BC_GE | BC_GE => BC_LT | BC_LTU => BC_GEU | BC_GEU => BC_LTU end.
Fixpoint nsp (p : sprop) : sprop :=
  match p with
  | SPNot (SPBranch c a b) => SPBranch (negc c) (nsv a) (nsv b)
  | SPBranch c a b => SPBranch c (nsv a) (nsv b)
  | SPNot q => SPNot (nsp q)
  | SPUlt a b => SPUlt (nsv a) (nsv b)
  | SPUle a b => SPUle (nsv a) (nsv b)
  | SPEq a b => SPEq (nsv a) (nsv b)
  | _ => p
  end.

Definition au_acc : Type := list (sv * sv * positive).
Fixpoint au_find (a b : sv) (acc : au_acc) : option positive :=
  match acc with
  | [] => None
  | (x, y, v) :: t => if sv_eqb x a && sv_eqb y b then Some v else au_find a b t
  end.
Definition au_sv (a b : sv) (st : au_acc * positive) : sv * (au_acc * positive) :=
  let '(acc, nx) := st in
  if sveq a b then (a, st) else
  match au_find a b acc with
  | Some v => (SVar v, st)
  | None => (SVar nx, ((a, b, nx) :: acc, Pos.succ nx))
  end.
Fixpoint au_list (xs ys : list sv) (st : au_acc * positive) : option (list sv * (au_acc * positive)) :=
  match xs, ys with
  | [], [] => Some ([], st)
  | x :: xs', y :: ys' =>
      let '(z, st1) := au_sv x y st in
      match au_list xs' ys' st1 with Some (zs, st2) => Some (z :: zs, st2) | None => None end
  | _, _ => None
  end.
(* cells matched by offset and width; a cell only one side has is dropped *)
Fixpoint au_cells (cs ds : list cell) (st : au_acc * positive) : option (list cell * (au_acc * positive)) :=
  match cs with
  | [] => Some ([], st)
  | c :: cs' =>
      match find (fun d => sveq (c_off c) (c_off d) && Z.eqb (c_width c) (c_width d)) ds with
      | Some d =>
          let '(z, st1) := au_sv (c_val c) (c_val d) st in
          match au_cells cs' ds st1 with Some (zs, st2) => Some (mkCell (c_off c) (c_width c) z :: zs, st2) | None => None end
      | None => au_cells cs' ds st
      end
  end.
Definition au_obj (o p : sobj) (st : au_acc * positive) : option (sobj * (au_acc * positive)) :=
  if odefault_eqb (ob_dflt o) (ob_dflt p) then
    let '(b, st1) := au_sv (ob_base o) (ob_base p) st in
    let '(l, st2) := au_sv (ob_lo o) (ob_lo p) st1 in
    let '(h, st3) := au_sv (ob_hi o) (ob_hi p) st2 in
    match au_cells (ob_cells o) (ob_cells p) st3 with
    | Some (cs, st4) => Some (mkObj b l h cs (ob_dflt o), st4)
    | None => None
    end
  else None.
Fixpoint au_objs (os ps : list sobj) (st : au_acc * positive) : option (list sobj * (au_acc * positive)) :=
  match os, ps with
  | [], [] => Some ([], st)
  | o :: os', p :: ps' =>
      match au_obj o p st with
      | Some (z, st1) => match au_objs os' ps' st1 with Some (zs, st2) => Some (z :: zs, st2) | None => None end
      | None => None
      end
  | _, _ => None
  end.

Fixpoint rep_sv (a : sv) (v : positive) (e : sv) : sv :=
  if sv_eqb e a then SVar v else
  match e with
  | SAlu op x y => SAlu op (rep_sv a v x) (rep_sv a v y)
  | SAluW op x y => SAluW op (rep_sv a v x) (rep_sv a v y)
  | SMd op x y => SMd op (rep_sv a v x) (rep_sv a v y)
  | SMdW op x y => SMdW op (rep_sv a v x) (rep_sv a v y)
  | SExt s w x => SExt s w (rep_sv a v x)
  | SLBytes l i k => SLBytes l (rep_sv a v i) k
  | _ => e
  end.
Fixpoint rep_sp (a : sv) (v : positive) (p : sprop) : sprop :=
  match p with
  | SPBranch c x y => SPBranch c (rep_sv a v x) (rep_sv a v y)
  | SPNot q => SPNot (rep_sp a v q)
  | SPUlt x y => SPUlt (rep_sv a v x) (rep_sv a v y)
  | SPUle x y => SPUle (rep_sv a v x) (rep_sv a v y)
  | SPEq x y => SPEq (rep_sv a v x) (rep_sv a v y)
  | SPAlign i k => match a with SVar j => if Pos.eqb i j then SPAlign v k else p | _ => p end
  | SPTrue => SPTrue
  end.
Definition is_lit (e : sv) : bool := match e with SLit _ => true | _ => false end.
Definition rep_all (side : bool) (acc : au_acc) (p : sprop) : sprop :=
  fold_right (fun '(a, b, v) q => let t := if side then a else b in if is_lit t then q else rep_sp t v q) p acc.

Definition au_state (pc : Z) (nx0 : positive) (A B : sstate) : option sstate :=
  let st0 : au_acc * positive := ([], Pos.max nx0 (Pos.max (ss_next A) (ss_next B))) in
  match au_list (ss_regs A) (ss_regs B) st0 with
  | None => None
  | Some (regs, st1) =>
  match au_list (ss_fregs A) (ss_fregs B) st1 with
  | None => None
  | Some (fregs, st2) =>
  match au_objs (ss_objs A) (ss_objs B) st2 with
  | None => None
  | Some (objs, (acc, nx)) =>
      let FA0 := map (rep_all true acc) (ss_facts A) in
      let FA := ss_facts A ++ filter (fun f => negb (in_facts f (ss_facts A))) FA0 in
      let FB := map nsp (ss_facts B ++ map (rep_all false acc) (ss_facts B)) in
      let facts := filter (fun f => existsb (sprop_eqb (nsp f)) FB) FA in
      Some (mkSS pc regs fregs (ss_fcsr A) (ss_resv A) objs facts nx (ss_lenient A))
  end end end.
(* fresh variables start above every input's ss_next, so the intermediate join's own variables cannot clash with
   variables of the leaves still to come *)
Fixpoint au_fold (pc : Z) (nx0 : positive) (A : sstate) (Bs : list sstate) : sstate :=
  match Bs with
  | [] => A
  | B :: Bs' => match au_state pc nx0 A B with Some J => au_fold pc (ss_next J) J Bs' | None => Pre_fs end
  end.
Definition au_states (pc : Z) (A : sstate) (Bs : list sstate) : sstate :=
  au_fold pc (fold_right (fun S m => Pos.max (ss_next S) m) (ss_next A) Bs) A Bs.
Definition head_of (S : sstate) : sv :=
  match find (fun c => sveq (c_off c) (SLit 48)) (ob_cells (nth 21 (ss_objs S) O_AF)) with
  | Some c => c_val c | None => SLit 0 end.

Definition J228 : sstate := Eval vm_compute in
  au_states (off 228) (nth 0 (leaves_at C_go (off 228)) Pre_fs) [closeX (nth 0 (leaves_at C_nm_ok (off 228)) Pre_fs)].

Definition PreA16 : sstate := S_aa.Pre_aa 16.
Definition wfacts (S : sstate) (fs : list sprop) : sstate :=
  mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S) fs (ss_next S) (ss_lenient S).
(* vector finalize at an inlined arena_dup: element size e, count var c, capacity var k *)
Definition mfa (e : Z) (c : positive) : sprop := SPUle (SMd M_MUL (SLit e) (SVar c)) (SLit two47).
Definition mfb (e : Z) (c k : positive) : sprop := SPUle (SMd M_MUL (SLit e) (SVar c)) (SMd M_MUL (SLit e) (SVar k)).
Definition E_of (J : sstate) (e : Z) (c k : positive) : sstate :=
  let E := nth 0 (leaves_at J S_aa.aa_entry) Pre_fs in wfacts E (mfa e c :: mfb e c k :: ss_facts E).
Definition s_of (E : sstate) : wsub := (19%positive, dlo) :: infer_sub 10 E PreA16.
Definition R_of (E : sstate) : list sobj := optR (entails_fr E PreA16 (s_of E)).
Definition Tf_of (E : sstate) : sstate := T_afterN NF E (s_of E) (R_of E) S_aa.P_fail.
Definition Tk_of (E : sstate) : sstate := optS (apply_xforms (T_afterN NF E (s_of E) (R_of E) (S_aa.P_ok 16)) [XSelect perm_aa]).

Definition E_mi : sstate := Eval vm_compute in E_of J228 12 114 115.
Definition T_mi_fail : sstate := Eval vm_compute in Tf_of E_mi.
Definition C_mi_ok : sstate := Eval vm_compute in Tk_of E_mi.
Definition X_mi_L0 : sstate := Eval vm_compute in nth 0 (leaves_at C_mi_ok (off 368)) Pre_fs.

(* copy-loop head: index register ri := fresh vI with vI < n, scratch registers fresh, cells of the source data and
   of the slot dropped *)
Definition drop_cells (os : list sobj) (idx : list nat) : list sobj :=
  map (fun '(i, o) => if existsb (Nat.eqb i) idx then mkObj (ob_base o) (ob_lo o) (ob_hi o) [] (ob_dflt o) else o)
    (combine (seq 0 (length os)) os).
Definition loop_cut (X : sstate) (ri : nat) (tmps : list nat) (idx : list nat) (n : sv) : sstate :=
  let vI := SVar (ss_next X) in
  let '(regs, nx) := fresh_regs (list_set (ss_regs X) ri vI) tmps (Pos.succ (ss_next X)) in
  mkSS (ss_pc X) regs (ss_fregs X) (ss_fcsr X) (ss_resv X) (drop_cells (ss_objs X) idx) (SPUlt vI n :: ss_facts X) nx
    (ss_lenient X).
Definition vI_of (C : sstate) : sv := nth 11 (ss_regs C) (SLit 0).

Definition n_mi : sv := SMd M_MUL (SLit 12) (SVar 114).
Definition C_mi_L : sstate := Eval vm_compute in loop_cut X_mi_L0 11 [14; 15]%nat [22; 31]%nat n_mi.

Definition J404 : sstate := Eval vm_compute in
  au_states (off 404) (nth 0 (leaves_at C_go (off 404)) Pre_fs)
    [closeX (nth 0 (leaves_at C_nm_ok (off 404)) Pre_fs); closeX (nth 0 (leaves_at C_mi_ok (off 404)) Pre_fs);
     closeX (nth 0 (leaves_at C_mi_L (off 404)) Pre_fs)].

Definition join_of (pc : Z) (J Ck CL : sstate) : sstate :=
  au_states pc (nth 0 (leaves_at J pc) Pre_fs) (map closeX (leaves_at Ck pc ++ leaves_at CL pc)).

Definition E_fv : sstate := Eval vm_compute in E_of J404 4 117 118.
Definition T_fv_fail : sstate := Eval vm_compute in Tf_of E_fv.
Definition C_fv_ok : sstate := Eval vm_compute in Tk_of E_fv.
Definition X_fv_L0 : sstate := Eval vm_compute in nth 0 (leaves_at C_fv_ok (off 500)) Pre_fs.
Definition n_fv : sv := SMd M_MUL (SLit 4) (SVar 117).
Definition C_fv_L : sstate := Eval vm_compute in loop_cut X_fv_L0 11 [14; 15]%nat [23; 31]%nat n_fv.
Definition J536 : sstate := Eval vm_compute in join_of (off 536) J404 C_fv_ok C_fv_L.

Definition E_mm : sstate := Eval vm_compute in E_of J536 4 120 121.
Definition T_mm_fail : sstate := Eval vm_compute in Tf_of E_mm.
Definition C_mm_ok : sstate := Eval vm_compute in Tk_of E_mm.
Definition X_mm_L0 : sstate := Eval vm_compute in nth 0 (leaves_at C_mm_ok (off 636)) Pre_fs.
Definition n_mm : sv := SMd M_MUL (SLit 4) (SVar 120).
Definition C_mm_L : sstate := Eval vm_compute in loop_cut X_mm_L0 11 [14; 15]%nat [24; 31]%nat n_mm.
Definition J672 : sstate := Eval vm_compute in join_of (off 672) J536 C_mm_ok C_mm_L.

Definition E_sg : sstate := Eval vm_compute in E_of J672 4 123 124.
Definition T_sg_fail : sstate := Eval vm_compute in Tf_of E_sg.
Definition C_sg_ok : sstate := Eval vm_compute in Tk_of E_sg.
Definition X_sg_L0 : sstate := Eval vm_compute in nth 0 (leaves_at C_sg_ok (off 816)) Pre_fs.
Definition n_sg : sv := SMd M_MUL (SLit 4) (SVar 123).
Definition C_sg_L : sstate := Eval vm_compute in loop_cut X_sg_L0 11 [14; 15]%nat [25; 31]%nat n_sg.
Definition J852 : sstate := Eval vm_compute in join_of (off 852) J672 C_sg_ok C_sg_L.
Definition hJ852 : positive := Eval vm_compute in match head_of J852 with SVar h => h | _ => 1%positive end.

(* after a failed aa call: post objects [frame; stack; arena] first, then the 27 frame objects *)
Definition perm_fail : list nat := ([3; 0; 1] ++ seq 4 18 ++ [2] ++ seq 22 8)%nat.
Definition Cf (T : sstate) : sstate := optS (apply_xforms T [XSelect perm_fail]).
Definition C_nm_fail : sstate := Eval vm_compute in Cf T_nm_fail.
Definition C_mi_fail : sstate := Eval vm_compute in Cf T_mi_fail.
Definition C_fv_fail : sstate := Eval vm_compute in Cf T_fv_fail.
Definition C_mm_fail : sstate := Eval vm_compute in Cf T_mm_fail.
Definition C_sg_fail : sstate := Eval vm_compute in Cf T_sg_fail.

Definition amF (E : sstate) (s : wsub) : amode := am_subst (import_sub s NF S_aa.P_fail (ss_next E)) (AHead S_aa.vHD).
Definition amK (E : sstate) (s : wsub) (al : Z) : amode :=
  am_subst (import_sub s NF (S_aa.P_ok al) (ss_next E)) (AOpen S_aa.vH S_aa.vNX S_aa.vCAP [(S_aa.vP, S_aa.vSZ)]).
Definition am_nm_fail : amode := Eval vm_compute in amF E_nm s_nm.
Definition am_nm_ok : amode := Eval vm_compute in amK E_nm s_nm 1.
Definition am_mi_fail : amode := Eval vm_compute in amF E_mi (s_of E_mi).
Definition am_mi_ok : amode := Eval vm_compute in amK E_mi (s_of E_mi) 16.
Definition am_fv_fail : amode := Eval vm_compute in amF E_fv (s_of E_fv).
Definition am_fv_ok : amode := Eval vm_compute in amK E_fv (s_of E_fv) 16.
Definition am_mm_fail : amode := Eval vm_compute in amF E_mm (s_of E_mm).
Definition am_mm_ok : amode := Eval vm_compute in amK E_mm (s_of E_mm) 16.
Definition am_sg_fail : amode := Eval vm_compute in amF E_sg (s_of E_sg).
Definition am_sg_ok : amode := Eval vm_compute in amK E_sg (s_of E_sg) 16.
Definition amJ (J : sstate) : amode := AHead (head_of J).

(* exits: raw call leaves, leaves reaching a join from an open-arena cut (closed in the proof), the tail, the posts *)
Definition E_mi0 : sstate := Eval vm_compute in nth 0 (leaves_at J228 S_aa.aa_entry) Pre_fs.
Definition E_fv0 : sstate := Eval vm_compute in nth 0 (leaves_at J404 S_aa.aa_entry) Pre_fs.
Definition E_mm0 : sstate := Eval vm_compute in nth 0 (leaves_at J536 S_aa.aa_entry) Pre_fs.
Definition E_sg0 : sstate := Eval vm_compute in nth 0 (leaves_at J672 S_aa.aa_entry) Pre_fs.
Definition X_nm228 : sstate := Eval vm_compute in nth 0 (leaves_at C_nm_ok (off 228)) Pre_fs.
Definition X_nm404 : sstate := Eval vm_compute in nth 0 (leaves_at C_nm_ok (off 404)) Pre_fs.
Definition X_mi_a : sstate := Eval vm_compute in nth 0 (leaves_at C_mi_ok (off 404)) Pre_fs.
Definition X_mi_b : sstate := Eval vm_compute in nth 0 (leaves_at C_mi_L (off 404)) Pre_fs.
Definition X_fv_a : sstate := Eval vm_compute in nth 0 (leaves_at C_fv_ok (off 536)) Pre_fs.
Definition X_fv_b : sstate := Eval vm_compute in nth 0 (leaves_at C_fv_L (off 536)) Pre_fs.
Definition X_mm_a : sstate := Eval vm_compute in nth 0 (leaves_at C_mm_ok (off 672)) Pre_fs.
Definition X_mm_b : sstate := Eval vm_compute in nth 0 (leaves_at C_mm_L (off 672)) Pre_fs.
Definition X_sg_a : sstate := Eval vm_compute in nth 0 (leaves_at C_sg_ok (off 852)) Pre_fs.
Definition X_sg_b : sstate := Eval vm_compute in nth 0 (leaves_at C_sg_L (off 852)) Pre_fs.

Definition z0 : sv := SLit 0.
Definition cp_var (n : sv) (C : sstate) : sv := SAlu ALU_SUB n (vI_of C).
Definition cutsE : list aedesc :=
  [ (Pre_fs, (tv0, ahd), (100, z0));
    (C_go, (tv0, ahd), (98, z0));
    (C_nm_fail, (tv0, am_nm_fail), (94, z0));
    (C_nm_ok, (tv0, am_nm_ok), (94, z0));
    (J228, (tv0, amJ J228), (92, z0));
    (C_mi_fail, (tv0, am_mi_fail), (88, z0));
    (C_mi_ok, (tv0, am_mi_ok), (88, z0));
    (C_mi_L, (tv0, am_mi_ok), (86, cp_var n_mi C_mi_L));
    (J404, (tv0, amJ J404), (84, z0));
    (C_fv_fail, (tv0, am_fv_fail), (80, z0));
    (C_fv_ok, (tv0, am_fv_ok), (80, z0));
    (C_fv_L, (tv0, am_fv_ok), (78, cp_var n_fv C_fv_L));
    (J536, (tv0, amJ J536), (76, z0));
    (C_mm_fail, (tv0, am_mm_fail), (72, z0));
    (C_mm_ok, (tv0, am_mm_ok), (72, z0));
    (C_mm_L, (tv0, am_mm_ok), (70, cp_var n_mm C_mm_L));
    (J672, (tv0, amJ J672), (68, z0));
    (C_sg_fail, (tv0, am_sg_fail), (64, z0));
    (C_sg_ok, (tv0, am_sg_ok), (64, z0));
    (C_sg_L, (tv0, am_sg_ok), (62, cp_var n_sg C_sg_L)) ].
Definition exitsE : list aedesc :=
  [ (E_nm, (tv0, ahd), (96, z0));
    (X_nm228, (tv0, am_nm_ok), (93, z0));
    (X_nm404, (tv0, am_nm_ok), (93, z0));
    (E_mi0, (tv0, amJ J228), (90, z0));
    (X_mi_a, (tv0, am_mi_ok), (87, z0));
    (X_mi_b, (tv0, am_mi_ok), (85, z0));
    (E_fv0, (tv0, amJ J404), (82, z0));
    (X_fv_a, (tv0, am_fv_ok), (79, z0));
    (X_fv_b, (tv0, am_fv_ok), (77, z0));
    (E_mm0, (tv0, amJ J536), (74, z0));
    (X_mm_a, (tv0, am_mm_ok), (71, z0));
    (X_mm_b, (tv0, am_mm_ok), (69, z0));
    (E_sg0, (tv0, amJ J672), (66, z0));
    (X_sg_a, (tv0, am_sg_ok), (63, z0));
    (X_sg_b, (tv0, am_sg_ok), (61, z0));
    (J852, (tv0, AHead (SVar hJ852)), (30, z0));
    (P_nop, (tv0, ahd), (0, z0));
    (P_fail, (tv0, amq), (0, z0));
    (P_failz, (tv0, amq), (0, z0)) ].
