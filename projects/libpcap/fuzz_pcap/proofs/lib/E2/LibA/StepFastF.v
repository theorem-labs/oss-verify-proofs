(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac StepFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF StepF0.
From Ltac2 Require Import Ltac2 Printf.
From Ltac2 Require Import Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import Ltac2.Bool.BoolNotations.
Import ListNotations.
Open Scope bv_scope.
Set Default Proof Mode "Classic".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sf_accs (segs : list Segment) (e : eff) (m : word -> option byte) : list memory_access :=
  match interp_eff_accesses segs e m with
  | MachineOk r => @accessed_ranges _ r
  | _ => []
  end.

Lemma sf_F_eq : forall segs ro e m ms1,
  lift_result ro (ieff segs e m) = MachineOk ms1 ->
  lift_resultF ro (interp_eff_accesses segs e m) = MachineOk (mkAccessReport _ ms1 (sf_accs segs e m)).
Proof.
  intros segs ro e m ms1 H. rewrite <- interp_eff_ieff in H. unfold interp_eff, drop_access_report in H. unfold sf_accs.
  destruct (interp_eff_accesses segs e m) as [[[c m'] accs]| |]; cbn in H |- *; [|discriminate|discriminate].
  injection H as <-. reflexivity.
Qed.

Lemma sf_evtF_step : forall segs RNG (Q : machine_state -> Prop) R F pc fc rv m ro w i sz ms1 accs,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (i, sz) ->
  lift_result ro (ieff segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m) = MachineOk ms1 ->
  sf_accs segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m = accs ->
  Forall (acc_in RNG) accs ->
  evtF segs RNG Q ms1 -> evtF segs RNG Q (MS R F pc fc rv m ro).
Proof.
  intros segs RNG Q R F pc fc rv m ro w i sz ms1 accs Hf He Hd Hx Ha Hfp K.
  eapply (evtF_step_acc segs RNG); [ reflexivity | | exact Hfp | exact K ].
  rewrite (stepF_gen segs R F pc fc rv m ro w i sz Hf He Hd). rewrite (sf_F_eq _ _ _ _ _ Hx), Ha. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sf_evtF_step1 : forall segs RNG (Q : machine_state -> Prop) R F pc fc rv m ro i sz ms1 accs,
  sf_fdec segs pc = Some (i, sz) ->
  lift_result ro (ieff segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m) = MachineOk ms1 ->
  sf_accs segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m = accs ->
  Forall (acc_in RNG) accs ->
  evtF segs RNG Q ms1 -> evtF segs RNG Q (MS R F pc fc rv m ro).
Proof.
  intros segs RNG Q R F pc fc rv m ro i sz ms1 accs Hfd Hx Ha Hfp K.
  destruct (sf_fdec_ok _ _ _ _ Hfd) as (w & Hf & He & Hd).
  exact (sf_evtF_step segs RNG Q R F pc fc rv m ro w i sz ms1 accs Hf He Hd Hx Ha Hfp K).
Qed.

Lemma sf_accs_done : forall segs c m, sf_accs segs (EDone c) m = [].
Proof. reflexivity. Qed.

Lemma sf_accs_load : forall segs (m : word -> option byte) (n : N) (a : word) (g : bv n -> core)
    (f : list byte -> word) (v : word),
  sf_load_goal segs m a (width_bytes n) f = Some v ->
  sf_accs segs (ELoad n a (fun x => EDone (g x))) m = [(a, width_bytes n)].
Proof.
  intros segs m n a g f v H. unfold sf_load_goal in H. unfold sf_accs. cbn [interp_eff_accesses].
  destruct (ov_read_bytes segs m a (width_bytes n)); [reflexivity|discriminate].
Qed.

Lemma sf_accs_store : forall segs (m : word -> option byte) (n : N) (a : word) (v : bv n) (c : core)
    (bs : list byte) (m' : word -> option byte),
  sf_store_goal segs m a (width_bytes n) bs = Some m' ->
  sf_accs segs (EStore n a v (EDone c)) m = [(a, width_bytes n)].
Proof.
  intros segs m n a v c bs m' H. unfold sf_store_goal in H. unfold sf_accs. cbn [interp_eff_accesses].
  destruct (store_ok segs m a (width_bytes n)); [reflexivity|discriminate].
Qed.

(* [comment removed for export] *)
Lemma sf_acc_norm : forall (RNG : footprint) (a a' : word) (n : nat),
  a = a' -> Forall (acc_in RNG) [(a', n)] -> Forall (acc_in RNG) [(a, n)].
Proof. intros RNG a a' n ->. exact (fun H => H). Qed.

Lemma sf_evtF_mem : forall segs RNG (Q : machine_state -> Prop) R F pc fc rv (m m' ro : word -> option byte),
  m = m' -> evtF segs RNG Q (MS R F pc fc rv m' ro) -> evtF segs RNG Q (MS R F pc fc rv m ro).
Proof. intros; subst; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac2 fold_r_deep (t : constr) : constr :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if Bool.and (Int.equal (Array.length args) 5) (Constr.equal h '@bvmap_set) then
        Constr.Unsafe.make (Constr.Unsafe.App h (Array.mapi (fun i a => if Int.equal i 4 then fold_r a else a) args))
      else fold_r t
  | _ => t
  end.
Ltac2 sf_step_ (ph : int ref) (z : bool) : unit :=
  let stop (k : int) := ph.(contents) := k; stop k in
  lazy_match! goal with
  | [ |- evtF ?segs ?rng ?q (MS ?r ?f (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) ] =>
    stop 1;
    let fw := tm "fetch" (fun () => eval vm_compute in (fetch_word $segs (Z_to_bv 64 $pc))) in
    let w := lazy_match! fw with Some ?w => w | _ => sf_fail "no instruction" end in
    (* [comment removed for export] *)
    (match reg_int w with
     | Some n => if Int.equal n 115 then sf_fail "ecall" else ()
     | None => let ec := eval vm_compute in (is_ecall $w) in (lazy_match! ec with false => () | _ => sf_fail "ecall" end)
     end);
    let d := tm "decode" (fun () => eval vm_compute in (decode_any $w)) in
    let (i, sz) := lazy_match! d with Some (?i, ?sz) => (i, sz) | _ => sf_fail "undecodable" end in
    (* [comment removed for export] *)
    let rd := lazy_match! i with
      | OpImm _ ?rd _ _ => Some rd | ShiftImm _ ?rd _ _ => Some rd | Op _ ?rd _ _ => Some rd | OpImm32 ?rd _ _ => Some rd
      | ShiftImm32 _ ?rd _ _ => Some rd | Op32 _ ?rd _ _ => Some rd | Lui ?rd _ => Some rd | Auipc ?rd _ => Some rd
      | Mul _ ?rd _ _ => Some rd | Mul32 _ ?rd _ _ => Some rd | Jal ?rd _ => Some rd | Jalr ?rd _ _ => Some rd
      | Load _ _ ?rd _ _ => Some rd
      | Branch _ _ _ _ => None | Store _ _ _ _ => None
      | _ => sf_fail "unsupported instruction"
      end in
    let rd := match rd with
      | Some rd => (match reg_int rd with Some n => if Int.equal n 0 then None else Some rd | None => sf_fail "rd" end)
      | None => None
      end in
    (if is_concrete_map r then () else sf_fail "symbolic register file");
    stop 2;
    let body := tm "exec_abs" (fun () => exec_abs sz i f pc fc rv) in
    let ru := lazy_match! r with mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => eval cbv beta iota delta [mkR] in $r | _ => r end in
    let hit := { contents := false } in
    let body := tm "resolve" (fun () => resolve (kof reference:(reg_get)) (kof reference:(bvmap_set)) ru 0 body hit) in
    let rnew := if hit.(contents) then ru else r in
    let body := Constr.Unsafe.substnl [rnew] 0 body in
    stop 3;
    let x := tm "mk_ctx" (fun () => mk_ctx z) in
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    let qchk := match Constr.Unsafe.kind q with Constr.Unsafe.Evar _ _ => [] | _ => [q] end in
    (* [comment removed for export] *)
    let trig := { contents := [] } in
    let bad_t (t : constr) : bool :=
      let id0 := (x.(idioms_seen)).(contents) in
      (x.(idioms_seen)).(contents) := false;
      let r := bad x t in
      (if (x.(idioms_seen)).(contents) then (if r then () else trig.(contents) := t :: trig.(contents))
       else (x.(idioms_seen)).(contents) := id0);
      (if id0 then (x.(idioms_seen)).(contents) := true else ());
      r in
    (x.(qmode)).(contents) := true;
    (if tm "rest" (fun () => List.exist (fun t => if bad_t t then (if sf_debug then printf "STEPFAST-BADREST: %t@ CULPRIT: %t" t (bad_culprit x t) else ()); true else false)
                                        qchk) then ((x.(qmode)).(contents) := false; sf_fail "rest not normal") else ());
    (x.(qmode)).(contents) := false;
    (if tm "rest" (fun () => List.exist (fun t => if bad_t t then (if sf_debug then printf "STEPFAST-BADREST: %t@ CULPRIT: %t" t (bad_culprit x t) else ()); true else false)
                                        [rng; f; fc; rv; m; ro]) then sf_fail "rest not normal" else ());
    (* [comment removed for export] *)
    (if List.exist (fun t => let t' := eval cbv delta [mkR] in $t in if Constr.equal t t' then false else true) [rng; f; fc; rv; m; ro; ru]
     then sf_fail "mkR in state" else ());
    let rdpath := match rd with Some rd => Some (key_path rd) | None => None end in
    stop 4;
    let dirty := tm "dirty" (fun () => List.rev (dirty_leaves x trig rdpath rnew [] [])) in
    stop 5;
    (* [comment removed for export] *)
    (match trig.(contents) with
     | [] => ()
     | tl =>
       if z then
         (if tm "idioms" (fun () => idioms_hit (List.fold_left (fun acc t => '(($acc, $t))) 'tt (List.rev tl)))
          then sf_fail "idioms" else ())
       else ()
     end);
    (* [comment removed for export] *)
    let ops := lazy_match! i with
      | OpImm ALU_ADD _ ?a _ => [a] | Op ALU_ADD _ ?a ?b => [a; b]
      | Jalr _ ?a _ => [a] | Load _ _ _ ?a _ => [a] | Store _ ?a _ _ => [a]
      | _ => []
      end in
    let susp_op := List.exist (fun k => match reg_int k with
                             | Some 0 => false
                             | Some _ => let l := tree_get (key_path k) ru in suspicious x l
                             | None => true
                             end) ops in
    (* [comment removed for export] *)
    (if (x.(uz_seen)).(contents) then
       (if susp_op then
          ((if sf_debug then List.iter (fun k => match reg_int k with Some 0 => () | Some _ => printf "STEPFAST-SUSP: %t" (tree_get (key_path k) ru) | None => () end) ops else ());
           sf_fail "suspicious operand")
        else if List.exist (fun (_, l) => risky x l) dirty then sf_fail "risky dirty leaf" else ())
     else ());
    let dirty := List.map (fun (p, l) => (p, leaf_cbv l)) dirty in
    let iv := Ltac1.of_constr i in
    (* [comment removed for export] *)
    let fdp := tm "vmeqs" (fun () =>
      let iz := mk_app (gref reference:(prod)) [| gref reference:(instr); gref reference:(Z) |] in
      vm_eq (mk_app (gref reference:(option)) [| iz |]) (mk_app (gref reference:(sf_fdec)) [| segs; mk_app (gref reference:(Z_to_bv)) [| x.(c_n64); pc |] |])
            (mk_app (gref reference:(Some)) [| iz; mk_app (gref reference:(pair)) [| gref reference:(instr); gref reference:(Z); i; sz |] |])) in
    let mr := gref reference:(machine_state) in
    let mrr := mk_app (gref reference:(machine_result)) [| mr |] in
    let ok := gref reference:(MachineOk) in
    let cms := gref reference:(MS) in
    let wd := mk_app (gref reference:(bv)) [| x.(c_n64) |] in
    let ty_mem := '(word -> option byte) in
    let clear_hyps := { contents := [] } in
    (* [comment removed for export] *)
    let joint (pass : unit -> unit) (l : (constr * constr) list) : constr list * constr :=
      let (ty, t) := tup l in
      let (h, tn) := tm "norm" (fun () => small_goal pass t ty) in
      (if sf_timing then printf "NORMED %t ~> %t" t tn else ());
      clear_hyps.(contents) := h :: clear_hyps.(contents);
      (untup (List.length l) tn, Control.hyp h) in
    let dpaths := List.map (fun (p, _) => p) dirty in
    let draws := List.map (fun (_, l) => l) dirty in
    stop 6;
    let accr : (constr * constr * constr * constr) option ref := { contents := None } in   (* [comment removed for export] *)
    let (eqp, ms1) := lazy_match! body with
    | EDone (Core ?r1 ?f1 ?pc1 ?fc1 ?rv1) =>
        (if Constr.equal f1 f then () else sf_fail "F changed");
        (if Constr.equal fc1 fc then () else sf_fail "fcsr changed");
        (if Constr.equal rv1 rv then () else sf_fail "resv changed");
        let rdc := match rdpath with
          | Some p => [(p, tree_get p r1)]
          | None => (if Constr.equal r1 rnew then () else sf_fail "changed registers"); []
          end in
        let lcomps := List.append rdc dirty in
        stop 61;
        let dpc := tm "direct_pc" (fun () => direct_pc x i pc sz pc1) in
        stop 62;
        let pcsmall := match dpc with None => true | _ => false end in
        let raws := List.append (List.map (fun (_, v) => v) lcomps) (if pcsmall then [pc1] else []) in
        let k := List.length raws in
        (match raws with [] => () | _ => () end);
        let (norms, hj) := match raws with
          | [] => ([], gref reference:(I))
          | [v] =>
              (match (lazy_match! i with OpImm ALU_ADD _ _ _ => tm "direct" (fun () => direct_addi x z v) | _ => None end) with
               | Some (vn, pf) => ([vn], pf)
               | None => joint (fun () => sf_passes x z i) [(wd, v)]
               end)
          | _ => joint (fun () => sf_passes x z i) (List.map (fun v => (wd, v)) raws)
          end in
        let lnorms := List.firstn (List.length lcomps) norms in
        let pcn := match dpc with
          | Some (pcn, _) => pcn
          | None => List.last norms
          end in
        let r1n := List.fold_left2 (fun t (p, _) vn => tree_set p vn t) r1 lcomps lnorms in
        let ms1 := mk_app cms [| r1n; f; pcn; fc; rv; m; ro |] in
        stop 63;
        (* [comment removed for export] *)
        let e1 :=
          match raws with
          | [] => None
          | _ =>
              let tys := List.map (fun _ => wd) raws in
              let projs := tup_proj tys (mk_rel 1) in
              let lprojs := List.firstn (List.length lcomps) projs in
              let rh := List.fold_left2 (fun t (p, _) pr => tree_set p pr t) r1 lcomps lprojs in
              let pch := if pcsmall then List.last projs else (match dpc with Some (_, None) => pcn | _ => pc1 end) in
              let fn := mk_lam @t (tup_ty tys) (mk_app ok [| mr; mk_app cms [| fold_r rh; f; pch; fc; rv; m; ro |] |]) in
              let (_, traw) := tup (List.map (fun v => (wd, v)) raws) in
              let (_, tnorm) := tup (List.map (fun v => (wd, v)) norms) in
              Some (mk_app (gref reference:(sf_congT)) [| tup_ty tys; fn; traw; tnorm; hj |], pch)
          end in
        (* [comment removed for export] *)
        let eqp := match dpc with
          | Some (_, Some pf) =>
              let fn2 := mk_lam @y wd (mk_app ok [| mr; mk_app cms [| fold_r r1n; f; mk_rel 1; fc; rv; m; ro |] |]) in
              let e2 := mk_app (gref reference:(sf_cong1)) [| fn2; pc1; pcn; pf |] in
              (match e1 with
               | None => e2
               | Some (e, _) =>
                   mk_app (gref reference:(sf_transMR)) [| mk_app ok [| mr; mk_app cms [| fold_r r1; f; pc1; fc; rv; m; ro |] |];
                             mk_app ok [| mr; mk_app cms [| fold_r r1n; f; pc1; fc; rv; m; ro |] |]; mk_app ok [| mr; fold_ms ms1 |]; e; e2 |]
               end)
          | _ =>
              (match e1 with
               | None => mk_app (gref reference:(sf_refl)) [| mk_app ok [| mr; fold_ms ms1 |] |]
               | Some (e, _) => e
               end)
          end in
        (eqp, ms1)
    | ELoad ?n ?a ?kk =>
        (* [comment removed for export] *)
        (let q' := eval cbv beta iota delta [tset mkR] in $q in if Constr.equal q q' then () else sf_fail "load: Q has mkR/redexes");
        let rdv := match rd with Some rd => rd | None => sf_fail "load to x0" end in
        let rp := match rdpath with Some p => p | None => sf_fail "load to x0" end in
        let (r1, f1, pc1, fc1, rv1) := match Constr.Unsafe.kind kk with
          | Constr.Unsafe.Lambda _ kb =>
              lazy_match! kb with
              | EDone (Core ?r1 ?f1 ?pc1 ?fc1 ?rv1) => (r1, f1, pc1, fc1, rv1)
              | _ => sf_fail "load shape"
              end
          | _ => sf_fail "load shape"
          end in
        (* [comment removed for export] *)
        (if Constr.equal f1 f then () else sf_fail "F changed");
        (if Constr.equal fc1 fc then () else sf_fail "fcsr changed");
        (if Constr.equal rv1 rv then () else sf_fail "resv changed");
        let fv := match Constr.Unsafe.kind r1 with
          | Constr.Unsafe.App h args => if Int.equal (Array.length args) 5 then sf_get args 3 else sf_fail "load shape"
          | _ => sf_fail "load shape"
          end in
        let nb := eval cbv beta iota delta [width_bytes] in (width_bytes $n) in
        let ext := match Constr.Unsafe.kind '(fun bs : list byte => @bv_extract 64 0 $n (le_bytes_to_word bs)) with
          | Constr.Unsafe.Lambda _ eb => eb
          | _ => sf_fail "ext"
          end in
        let fl := mk_lam @bs '(list byte) (Constr.Unsafe.substnl [ext] 0 fv) in
        let lg := mk_app (gref reference:(sf_load_goal)) [| segs; m; a; nb; fl |] in
        let owd := mk_app (gref reference:(option)) [| wd |] in
        let direct := match draws with [] => tm "directld" (fun () => sf_direct_load x z segs m a nb fl n) | _ => None end in
        (if sf_timing then (match direct with Some _ => printf "DIRECT-LD yes" | None => printf "DIRECT-LD no %t draws %i" i (List.length draws) end) else ());
        let (norms, hj) := match direct with
          | Some (vl0, pf) => ([mk_app (gref reference:(Some)) [| wd; vl0 |]], pf)
          | None =>
              let vt := mk_vt x in
              joint (fun () => sf_norm_load2 vt z i) ((owd, lg) :: List.map (fun v => (wd, v)) draws)
          end in
        let (vl, dnorms) := match norms with
          | sv :: dn => (lazy_match! sv with Some ?e => e | _ => sf_fail "load result" end, dn)
          | [] => sf_fail "load result"
          end in
        let pcn := match direct_pc x i pc sz pc1 with Some (pcn, None) => pcn | _ => sf_fail "load pc" end in
        let core_pair := mk_app (gref reference:(prod)) [| gref reference:(core); ty_mem |] in
        let kt := mk_lam @x wd (mk_app ok [| core_pair;
                     mk_app (gref reference:(pair)) [| gref reference:(core); ty_mem;
                        mk_app (gref reference:(Core)) [| mk_app (gref reference:(bvmap_set)) [| '5%N; wd; rdv; mk_rel 1; fold_r rnew |]; f; pc1; fc; rv |]; m |] |]) in
        let r1v := tree_set rp vl rnew in
        let r1n := List.fold_left2 (fun t p vn => tree_set p vn t) r1v dpaths dnorms in
        let ms1 := mk_app cms [| r1n; f; pcn; fc; rv; m; ro |] in
        let (h1, ek) := match draws with
          | [] => (hj, mk_app (gref reference:(sf_refl)) [| mk_app ok [| mr; fold_ms ms1 |] |])
          | _ =>
              let tys := List.map (fun _ => wd) draws in
              let tyl := tup_ty tys in
              let (_, traw) := tup (List.map (fun v => (wd, v)) draws) in
              let (_, tnorm) := tup (List.map (fun v => (wd, v)) dnorms) in
              let sv := mk_app (gref reference:(Some)) [| wd; vl |] in
              let h1 := pair_eq1 owd tyl lg sv traw tnorm hj in
              let h2 := pair_eq2 owd tyl lg sv traw tnorm hj in
              let projs := tup_proj tys (mk_rel 1) in
              let rh := List.fold_left2 (fun t p pr => tree_set p pr t) r1v dpaths projs in
              let fn := mk_lam @t tyl (mk_app ok [| mr; mk_app cms [| fold_r rh; f; pcn; fc; rv; m; ro |] |]) in
              (h1, mk_app (gref reference:(sf_congT)) [| tyl; fn; traw; tnorm; h2 |])
          end in
        (let gl := mk_lam @x (mk_app (gref reference:(bv)) [| n |]) (mk_app (gref reference:(Core)) [| fold_r_deep r1; f1; pc1; fc1; rv1 |]) in   (* [comment removed for export] *)
         accr.(contents) := Some (a, nb, n, mk_app (gref reference:(sf_accs_load)) [| segs; m; n; a; gl; fl; vl; h1 |]));
        (mk_app (gref reference:(sf_install_load)) [| segs; ro; m; a; nb; fl; vl; kt; mk_app ok [| mr; fold_ms ms1 |]; h1; ek |], ms1)
    | EStore ?n ?a ?v (EDone (Core ?r1 ?f1 ?pc1 ?fc1 ?rv1)) =>
        (if Constr.equal f1 f then () else sf_fail "F changed");
        (if Constr.equal fc1 fc then () else sf_fail "fcsr changed");
        (if Constr.equal rv1 rv then () else sf_fail "resv changed");
        (if Constr.equal r1 rnew then () else sf_fail "store changed registers");
        let nb := eval cbv beta iota delta [width_bytes] in (width_bytes $n) in
        let bs := mk_app (gref reference:(Z_to_le_bytes)) [| nb; mk_app (gref reference:(bv_unsigned)) [| n; v |] |] in
        let sg := mk_app (gref reference:(sf_store_goal)) [| segs; m; a; nb; bs |] in
        let omem := mk_app (gref reference:(option)) [| ty_mem |] in
        let direct := match draws with [] => tm "directst" (fun () => sf_direct_store x segs m a nb n v) | _ => None end in
        (if sf_timing then (match direct with Some _ => printf "DIRECT-ST yes" | None => printf "DIRECT-ST no %t draws %i v %t" i (List.length draws) v end) else ());
        let (norms, hj) := match direct with
          | Some (mn0, pf) => ([mk_app (gref reference:(Some)) [| ty_mem; mn0 |]], pf)
          | None =>
              let vt := mk_vt x in
              joint (fun () => sf_norm_store2 vt i) ((omem, sg) :: List.map (fun v => (wd, v)) draws)
          end in
        let (mn, dn1) := match norms with
          | sm :: dn => (lazy_match! sm with Some ?e => e | _ => sf_fail "store result" end, dn)
          | [] => sf_fail "store result"
          end in
        (* [comment removed for export] *)
        let (dnorms, hz) := match draws with
          | [] => ([], None)
          | _ => if z then
                   (let (dn2, h2) := joint (fun () => sf_zpasses x) (List.map (fun v => (wd, v)) dn1) in (dn2, Some (dn1, h2)))
                 else (dn1, None)
          end in
        let pcn := match direct_pc x i pc sz pc1 with Some (pcn, None) => pcn | _ => sf_fail "store pc" end in
        let core_pair := mk_app (gref reference:(prod)) [| gref reference:(core); ty_mem |] in
        let kt := mk_lam @x ty_mem (mk_app ok [| core_pair;
                     mk_app (gref reference:(pair)) [| gref reference:(core); ty_mem; mk_app (gref reference:(Core)) [| fold_r rnew; f; pc1; fc; rv |]; mk_rel 1 |] |]) in
        let r1n := List.fold_left2 (fun t p vn => tree_set p vn t) rnew dpaths dnorms in
        let ms1 := mk_app cms [| r1n; f; pcn; fc; rv; mn; ro |] in
        let (h1, ek) := match draws with
          | [] => (hj, mk_app (gref reference:(sf_refl)) [| mk_app ok [| mr; fold_ms ms1 |] |])
          | _ =>
              let tys := List.map (fun _ => wd) draws in
              let tyl := tup_ty tys in
              let (_, traw) := tup (List.map (fun v => (wd, v)) draws) in
              let (_, tn1) := tup (List.map (fun v => (wd, v)) dn1) in
              let (_, tnorm) := tup (List.map (fun v => (wd, v)) dnorms) in
              let sm := mk_app (gref reference:(Some)) [| ty_mem; mn |] in
              let h1 := pair_eq1 omem tyl sg sm traw tn1 hj in
              let h2 := pair_eq2 omem tyl sg sm traw tn1 hj in
              let h2 := match hz with
                | None => h2
                | Some (_, hz2) => mk_app (gref reference:(sf_trans)) [| tyl; traw; tn1; tnorm; h2; hz2 |]
                end in
              let projs := tup_proj tys (mk_rel 1) in
              let rh := List.fold_left2 (fun t p pr => tree_set p pr t) rnew dpaths projs in
              let fn := mk_lam @t tyl (mk_app ok [| mr; mk_app cms [| fold_r rh; f; pcn; fc; rv; mn; ro |] |]) in
              (h1, mk_app (gref reference:(sf_congT)) [| tyl; fn; traw; tnorm; h2 |])
          end in
        accr.(contents) := Some (a, nb, n, mk_app (gref reference:(sf_accs_store)) [| segs; m; n; a; v; mk_app (gref reference:(Core)) [| fold_r r1; f1; pc1; fc1; rv1 |]; bs; mn; h1 |]);
        (mk_app (gref reference:(sf_install_store)) [| segs; ro; m; a; nb; bs; mn; kt; mk_app ok [| mr; fold_ms ms1 |]; h1; ek |], ms1)
    | _ => sf_fail "raw shape"
    end in
    (if (x.(lit_delta)).(contents) then
       (if has_litself x ms1 then sf_fail "litself delta-instance in Q and a syntactic instance in the new state" else ())
     else ());
    stop 7;
    tm "install" (fun () =>
      let ms1f := if sf_fold_goal then fold_ms ms1 else ms1 in
      let k := tm "k" (fun () => strip_cast open_constr:(_ : evtF $segs $rng $q $ms1f)) in
      (* [comment removed for export] *)
      let macc := gref reference:(memory_access) in
      let accin := mk_app (gref reference:(acc_in)) [| rng |] in
      let (accs, acceq, fpp) :=
        match accr.(contents) with
        | None =>
            (* [comment removed for export] *)
            let c1 := lazy_match! body with EDone ?c => c | _ => sf_fail "F: raw shape" end in
            (mk_app (gref reference:(nil)) [| macc |],
             (* [comment removed for export] *)
             mk_app (gref reference:(eq_refl)) [| mk_app (gref reference:(list)) [| macc |]; mk_app (gref reference:(nil)) [| macc |] |],
             mk_app (gref reference:(Forall_nil)) [| macc; accin |])
        | Some (a, nb, n, pf) =>
            let (an, apf) := match direct_addr x a with
              | Some (an, apf) => (an, apf)
              | None => sf_fail "F: address form"
              end in
            let one (aa : constr) := mk_app (gref reference:(cons)) [| macc; mk_app (gref reference:(pair)) [| wd; gref reference:(nat); aa; nb |]; mk_app (gref reference:(nil)) [| macc |] |] in
            let fpg := mk_app (gref reference:(Forall)) [| macc; accin; one an |] in
            let hfp := Fresh.in_goal @sf_fp in
            tm "accs" (fun () => ltac1:(h g |- assert (h : g) by solve_accs) (Ltac1.of_ident hfp) (Ltac1.of_constr fpg));
            clear_hyps.(contents) := hfp :: clear_hyps.(contents);
            (one a, pf, mk_app (gref reference:(sf_acc_norm)) [| rng; a; an; nb; apf; Control.hyp hfp |])
        end in
      let term := mk_app (gref reference:(sf_evtF_step1)) [| segs; rng; q; fold_r ru; f; mk_app (gref reference:(Z_to_bv)) [| x.(c_n64); pc |]; fc; rv; m; ro; i; sz; fold_ms ms1; accs; fdp; eqp; acceq; fpp; k |] in   (* [comment removed for export] *)
      (if sf_check then
         match Constr.Unsafe.check term with
         | Val _ => ()
         | Err e => printf "STEPFAST-ILLTYPED %a" (fun () e => Message.of_exn e) e; sf_fail "ill-typed"
         end
       else ());
      match Constr.Unsafe.kind k with
      | Constr.Unsafe.Evar ev _ => tm "exact" (fun () => Std.exact_no_check term; Control.new_goal ev)
      | _ => sf_fail "install: continuation"
      end);
    stop 8;
    tm "clear" (fun () => Std.clear (clear_hyps.(contents)));
    stop 9;
    (* [comment removed for export] *)
    tm "post" (fun () => lazy_match! goal with
       | [ |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) ] => ltac1:(iv |- mem_after_store_opt; post_step iv) iv
       | [ |- _ ] => ()
       end);
    (if z then
       lazy_match! goal with
       | [ |- evtF ?segs' ?rng' ?q' (MS ?r' ?f' ?pc' ?fc' ?rv' ?m' ?ro') ] =>
           if Constr.is_var m' then () else
           (* [comment removed for export] *)
           let (h, mn) := small_goal (fun () => ltac1:(zsimp)) m' '(word -> option byte) in
           let k := strip_cast open_constr:(_ : evtF $segs' $rng' $q' (MS $r' $f' $pc' $fc' $rv' $mn $ro')) in
           let term := mk_app '@sf_evtF_mem [| segs'; rng'; q'; fold_r r'; f'; pc'; fc'; rv'; m'; mn; ro'; Control.hyp h; k |] in
           match Constr.Unsafe.kind k with
           | Constr.Unsafe.Evar ev _ => Std.exact_no_check term; Control.new_goal ev; Std.clear [h]
           | _ => sf_fail "install: continuation"
           end
       end
     else ())
  | [ |- _ ] => sf_fail "goal shape"
  end.

(* [comment removed for export] *)
Ltac2 sf_step (z : bool) : unit :=
  let ph := { contents := 0 } in
  if Bool.neg sf_debug then sf_step_ ph z else
  Control.plus (fun () => sf_step_ ph z)
    (fun e => (if sf_debug then
                 (lazy_match! goal with
                  | [ |- evtF _ _ _ (MS _ _ ?pc _ _ _ _) ] => printf "STEPFASTF-PHASE %i at pc %t" (ph.(contents)) pc
                  | [ |- _ ] => printf "STEPFAST-PHASE %i" (ph.(contents))
                  end) else ()); Control.zero e).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac step_core_oldF segs RNG R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
    let ec := eval vm_compute in (is_ecall w) in
    lazymatch ec with
    | false =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply (evtF_step_acc segs RNG);
        [ reflexivity
        | rewrite (stepF_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | solve_accs
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i ]
      | None => fail "undecodable instruction at" pc
      end
    | true => fail "ecall at" pc
    end
  | None => fail "no instruction at" pc
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac sf_old_step :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core_oldF segs RNG R F pc fc rv m ro
  | |- evtF _ _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.
Ltac sf_old_zstep := sf_old_step; zsimp.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac2 hyps_equal (h1 : (ident * constr option * constr) list) (h2 : (ident * constr option * constr) list) : bool :=
  if Int.equal (List.length h1) (List.length h2) then
    List.for_all2 (fun (a : ident * constr option * constr) (b : ident * constr option * constr) =>
       let (ia, ba, ta) := a in let (ib, bb, tb) := b in
       if Ident.equal ia ib then
         if Constr.equal ta tb then
           match ba, bb with
           | None, None => true
           | Some x, Some y => Constr.equal x y
           | _, _ => false
           end
         else false
       else false) h1 h2
  else false.

Ltac2 sf_old (z : bool) : unit := if z then ltac1:(sf_old_zstep) else ltac1:(sf_old_step).

Ltac2 sf_dual (z : bool) : unit :=
  let g0 := Control.goal () in
  let res := Control.case (fun () =>
     sf_step z;
     let g := Control.goal () in
     let hs := Control.hyps () in
     Control.zero (SF_Captured g hs)) in
  match res with
  | Val _ => sf_fail "impossible"
  | Err e =>
      match e with
      | SF_Captured gf hf =>
          sf_old z;
          let go := Control.goal () in
          let ho := Control.hyps () in
          if Constr.equal gf go then
            (if hyps_equal hf ho then printf "STEPFAST-OK" else
               printf "STEPFAST-MISMATCH(hyps) at %t" g0)
          else
            (* [comment removed for export] *)
            (* [comment removed for export] *)
            let qev (g : constr) := match Constr.Unsafe.kind g with
              | Constr.Unsafe.App f args =>
                  if Int.equal (Array.length args) 4 then (if is_k (kof reference:(evtF)) f then Some (mk_app (gref reference:(pair)) [| gref reference:(unit); gref reference:(unit); Array.get args 0; Array.get args 1 |], Array.get args 3) else None)
                  else None
              | _ => None end in
            match qev gf, qev go with
            | Some (s1, ms1), Some (s2, ms2) =>
                if Constr.equal s1 s2 then
                  (if Constr.equal ms1 ms2 then
                     (if hyps_equal hf ho then printf "STEPFAST-OK(evarQ)" else printf "STEPFAST-MISMATCH(hyps) at %t" g0)
                   else printf "STEPFAST-MISMATCH(goal) at %t@ FAST: %t@ OLD: %t" g0 gf go)
                else printf "STEPFAST-MISMATCH(goal) at %t@ FAST: %t@ OLD: %t" g0 gf go
            | _, _ => printf "STEPFAST-MISMATCH(goal) at %t@ FAST: %t@ OLD: %t" g0 gf go
            end
      | _ =>
          printf "STEPFAST-FALLBACK %a" (fun () e => Message.of_exn e) e;
          sf_old z
      end
  end.

(* [comment removed for export] *)
Ltac2 mutable sf_mode : int := 1.

Ltac2 sf_core1 (z : bool) : unit :=
  if Int.equal sf_mode 0 then sf_old z
  else if Int.equal sf_mode 1 then
    (* [comment removed for export] *)
    Control.once (fun () =>
      Control.plus (fun () => sf_step z)
        (fun e => (if sf_debug then printf "STEPFAST-FALLBACK %a" (fun () e => Message.of_exn e) e else ()); sf_old z))
  else sf_dual z.

(* [comment removed for export] *)
Ltac2 sf_core (z : bool) : unit := Control.enter (fun () => sf_core1 z).

Ltac sf_step_dual := ltac2:(sf_dual false).
Ltac sf_zstep_dual := ltac2:(sf_dual true).
Ltac sf_step_fast := ltac2:(sf_step false).
Ltac sf_zstep_fast := ltac2:(sf_step true).

(* [comment removed for export] *)
Ltac step_core segs RNG R F pc fc rv m ro ::= ltac2:(sf_core false).
Ltac zstep ::= ltac2:(sf_core true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac mem_after_store_stepF0 :=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.

Ltac mem_after_store ::=
  lazymatch goal with
  | |- evtF ?segs _ ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; sl_lit_sizes_in HB; cbn [cells_size csize Nat.add] in HB;
          let a := constr:((A + Z.of_nat kn)%Z) in
          let n' := sl_len_lit (cbytes c') in
          (* [comment removed for export] *)
          sl_facts_then a A kn constr:(Z.of_nat (length (cbytes c'))) n'
            ltac:(fun n'' Hn Ha Hl => sl_mas_new_tail segs m A kn bs c' cs c0 H HB n'' Hn Ha Hl)
            ltac:(fun _ => sl_mas_old_tail segs m A kn bs c' cs c0 H HB)
        end
    end
  end.
