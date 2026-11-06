(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame StepFast.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import ExecA StepA0.
From Ltac2 Require Import Ltac2 Printf.
From Ltac2 Require Import Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import Ltac2.Bool.BoolNotations.
Import ListNotations.
Local Open Scope bv_scope.   (* [comment removed for export] *)
Set Default Proof Mode "Classic".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sfA_accs (r : machine_result (access_report (core * (word -> option byte)))) : list acc :=
  match r with MachineOk rep => @accessed_ranges _ rep | _ => [] end.

Lemma sfA_bridge : forall ro (X : machine_result (access_report (core * (word -> option byte)))) ms1 rs,
  lift_result ro (drop_access_report X) = MachineOk ms1 -> sfA_accs X = rs ->
  lift_resultA ro X = MachineOk (ms1, rs).
Proof.
  intros ro X ms1 rs H1 H2. destruct X as [[[c m'] l]| |]; cbn in *; try discriminate.
  inversion H1; subst. reflexivity.
Qed.

Lemma sfA_evt_step : forall segs (P : acc -> Prop) (Q : machine_state -> Prop) R F pc fc rv m ro w i sz ms1 rs,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (i, sz) ->
  lift_result ro (interp_eff segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m) = MachineOk ms1 ->
  sfA_accs (interp_eff_accesses segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m) = rs ->
  Forall P rs ->
  evtA segs P Q ms1 -> evtA segs P Q (MS R F pc fc rv m ro).
Proof.
  intros segs P Q R F pc fc rv m ro w i sz ms1 rs Hf He Hd Hx Ha HP K.
  eapply evtA_step; [ | exact HP | exact K ]. split; [reflexivity|].
  rewrite (step_genA segs R F pc fc rv m ro w i sz Hf He Hd).
  apply sfA_bridge; [exact Hx | exact Ha].
Qed.

(* [comment removed for export] *)
Definition sfA_ok0 (r : machine_result (access_report (core * (word -> option byte)))) : bool :=
  match r with MachineOk rep => match @accessed_ranges _ rep with [] => true | _ => false end | _ => false end.

Lemma sfA_accs_load : forall segs (m : word -> option byte) nbits (a a' : word) (kk : bv nbits -> eff)
    (f : list byte -> word) (v : word),
  sf_load_goal segs m a (width_bytes nbits) f = Some v ->
  (forall x, sfA_ok0 (interp_eff_accesses segs (kk x) m) = true) ->
  a = a' ->
  sfA_accs (interp_eff_accesses segs (ELoad nbits a kk) m) = [(a', width_bytes nbits)].
Proof.
  intros segs m nbits a a' kk f v H1 H2 <-. unfold sf_load_goal in H1. cbn [interp_eff_accesses].
  destruct (ov_read_bytes segs m a (width_bytes nbits)) as [bs|]; [|discriminate].
  specialize (H2 (bv_extract 0 nbits (le_bytes_to_word bs))).
  destruct (interp_eff_accesses segs (kk (bv_extract 0 nbits (le_bytes_to_word bs))) m) as [[cm l]| |]; cbn in *; try discriminate.
  destruct l; [reflexivity|discriminate].
Qed.

Lemma sfA_accs_store : forall segs (m : word -> option byte) nbits (a a' : word) (v : bv nbits) (k : eff)
    (m' : word -> option byte),
  sf_store_goal segs m a (width_bytes nbits) (Z_to_le_bytes (width_bytes nbits) (bv_unsigned v)) = Some m' ->
  sfA_ok0 (interp_eff_accesses segs k (write_to_mem m a (Z_to_le_bytes (width_bytes nbits) (bv_unsigned v)))) = true ->
  a = a' ->
  sfA_accs (interp_eff_accesses segs (EStore nbits a v k) m) = [(a', width_bytes nbits)].
Proof.
  intros segs m nbits a a' v k m' H1 H2 <-. unfold sf_store_goal in H1. cbn [interp_eff_accesses].
  destruct (store_ok segs m a (width_bytes nbits)); [|discriminate].
  destruct (interp_eff_accesses segs k _) as [[cm l]| |]; cbn in *; try discriminate.
  destruct l; [reflexivity|discriminate].
Qed.

(* [comment removed for export] *)
Lemma sfA_evt_mem : forall segs (P : acc -> Prop) (Q : machine_state -> Prop) R F pc fc rv (m m' ro : word -> option byte),
  m = m' -> evtA segs P Q (MS R F pc fc rv m' ro) -> evtA segs P Q (MS R F pc fc rv m ro).
Proof. intros. subst. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac2 sfA_step_ (ph : int ref) (z : bool) : unit :=
  let stop (k : int) := ph.(contents) := k; stop k in
  lazy_match! goal with
  | [ |- evtA ?segs ?pp ?q (MS ?r ?f (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) ] =>
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
      | Mul M_DIVU _ _ _ => sf_fail "divu (vnorm_extra)" | Mul M_REMU _ _ _ => sf_fail "remu (vnorm_extra)"
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
    let qchk := pp :: (match Constr.Unsafe.kind q with Constr.Unsafe.Evar _ _ => [] | _ => [q] end) in
    (* [comment removed for export] *)
    let qk := { contents := q } in
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
                                        [f; fc; rv; m; ro]) then sf_fail "rest not normal" else ());
    (* [comment removed for export] *)
    (if List.exist (fun t => let t' := eval cbv delta [mkR] in $t in if Constr.equal t t' then false else true) [f; fc; rv; m; ro; ru]
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
    let (fwp, ecp, dcp) := tm "vmeqs" (fun () =>
      let bv32 := mk_app (gref reference:(bv)) [| x.(c_n32) |] in
      let obv32 := mk_app (gref reference:(option)) [| bv32 |] in
      let iz := mk_app (gref reference:(prod)) [| gref reference:(instr); gref reference:(Z) |] in
      (vm_eq obv32 (mk_app (gref reference:(fetch_word)) [| segs; mk_app (gref reference:(Z_to_bv)) [| x.(c_n64); pc |] |])
                   (mk_app (gref reference:(Some)) [| bv32; w |]),
       vm_eq (gref reference:(bool)) (mk_app (gref reference:(is_ecall)) [| w |]) (gref reference:(false)),
       vm_eq (mk_app (gref reference:(option)) [| iz |]) (mk_app (gref reference:(decode_any)) [| w |])
             (mk_app (gref reference:(Some)) [| iz; mk_app (gref reference:(pair)) [| gref reference:(instr); gref reference:(Z); i; sz |] |]))) in
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
    (* [comment removed for export] *)
    let r0id := Fresh.in_goal @sfR0 in
    let rT := if sf_share then Constr.Unsafe.make (Constr.Unsafe.Var r0id) else rnew in
    let tsetc := gref reference:(tset) in
    let tsetT (t : constr) (p : bool list) (v : constr) : constr :=
      if sf_share then mk_app tsetc [| wd; path_pos p; v; t |] else tree_set p v t in
    let ms1t := { contents := None } in
    stop 6;
    let (eqp, ms1, accs) := lazy_match! body with
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
        (* [comment removed for export] *)
        let r1T := if sf_share then (match rdpath with Some p => tsetT rT p (tree_get p r1) | None => rT end) else r1 in
        let r1nT := if sf_share then List.fold_left2 (fun t (p, _) vn => tsetT t p vn) rT lcomps lnorms else r1n in
        let ms1T := if sf_share then mk_app cms [| r1nT; f; pcn; fc; rv; m; ro |] else ms1 in
        ms1t.(contents) := Some ms1T;
        stop 63;
        (* [comment removed for export] *)
        let e1 :=
          match raws with
          | [] => None
          | _ =>
              let tys := List.map (fun _ => wd) raws in
              let projs := tup_proj tys (mk_rel 1) in
              let lprojs := List.firstn (List.length lcomps) projs in
              let rh := if sf_share then List.fold_left2 (fun t (p, _) pr => tsetT t p pr) rT lcomps lprojs
                        else List.fold_left2 (fun t (p, _) pr => tree_set p pr t) r1 lcomps lprojs in
              let pch := if pcsmall then List.last projs else (match dpc with Some (_, None) => pcn | _ => pc1 end) in
              let fn := mk_lam @t (tup_ty tys) (mk_app ok [| mr; mk_app cms [| rh; f; pch; fc; rv; m; ro |] |]) in
              let (_, traw) := tup (List.map (fun v => (wd, v)) raws) in
              let (_, tnorm) := tup (List.map (fun v => (wd, v)) norms) in
              (sf_eqchk (tup_ty tys) traw tnorm hj; Some (mk_app (gref reference:(sf_congT)) [| tup_ty tys; fn; traw; tnorm; hj |], pch))
          end in
        (* [comment removed for export] *)
        let eqp := match dpc with
          | Some (_, Some pf) =>
              let fn2 := mk_lam @y wd (mk_app ok [| mr; mk_app cms [| r1nT; f; mk_rel 1; fc; rv; m; ro |] |]) in
              let e2 := mk_app (gref reference:(sf_cong1)) [| fn2; pc1; pcn; pf |] in
              (match e1 with
               | None => e2
               | Some (e, _) =>
                   mk_app (gref reference:(sf_transMR)) [| mk_app ok [| mr; mk_app cms [| r1T; f; pc1; fc; rv; m; ro |] |];
                             mk_app ok [| mr; mk_app cms [| r1nT; f; pc1; fc; rv; m; ro |] |]; mk_app ok [| mr; ms1T |]; e; e2 |]
               end)
          | _ =>
              (match e1 with
               | None => mk_app (gref reference:(sf_refl)) [| mk_app ok [| mr; ms1T |] |]
               | Some (e, _) => e
               end)
          end in
        (eqp, ms1, None)
    | ELoad ?n ?a ?kk =>
        (* [comment removed for export] *)
        (* [comment removed for export] *)
        (let pp' := eval cbv beta iota delta [tset mkR] in $pp in if Constr.equal pp pp' then () else sf_fail "load: P not normal");
        (let q' := eval cbv beta iota delta [tset mkR] in $q in
         if Constr.equal q q' then ()
         else
           ((x.(qmode)).(contents) := true;
            let b := match Constr.Unsafe.kind q' with Constr.Unsafe.Evar _ _ => false | _ => bad_t q' end in
            (x.(qmode)).(contents) := false;
            if b then sf_fail "load: Q' not normal" else qk.(contents) := q'));
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
                        mk_app (gref reference:(Core)) [| mk_app (gref reference:(bvmap_set)) [| '5%N; wd; rdv; mk_rel 1; rT |]; f; pc1; fc; rv |]; m |] |]) in
        let r1v := tree_set rp vl rnew in
        let r1n := List.fold_left2 (fun t p vn => tree_set p vn t) r1v dpaths dnorms in
        let ms1 := mk_app cms [| r1n; f; pcn; fc; rv; m; ro |] in
        let r1vT := tsetT rT rp vl in
        let r1nT := if sf_share then List.fold_left2 (fun t p vn => tsetT t p vn) r1vT dpaths dnorms else r1n in
        let ms1T := if sf_share then mk_app cms [| r1nT; f; pcn; fc; rv; m; ro |] else ms1 in
        ms1t.(contents) := Some ms1T;
        let (h1, ek) := match draws with
          | [] => (hj, mk_app (gref reference:(sf_refl)) [| mk_app ok [| mr; ms1T |] |])
          | _ =>
              let tys := List.map (fun _ => wd) draws in
              let tyl := tup_ty tys in
              let (_, traw) := tup (List.map (fun v => (wd, v)) draws) in
              let (_, tnorm) := tup (List.map (fun v => (wd, v)) dnorms) in
              let sv := mk_app (gref reference:(Some)) [| wd; vl |] in
              let h1 := pair_eq1 owd tyl lg sv traw tnorm hj in
              let h2 := pair_eq2 owd tyl lg sv traw tnorm hj in
              let projs := tup_proj tys (mk_rel 1) in
              let rh := if sf_share then List.fold_left2 (fun t p pr => tsetT t p pr) r1vT dpaths projs
                        else List.fold_left2 (fun t p pr => tree_set p pr t) r1v dpaths projs in
              let fn := mk_lam @t tyl (mk_app ok [| mr; mk_app cms [| rh; f; pcn; fc; rv; m; ro |] |]) in
              (sf_eqchk tyl traw tnorm h2; (h1, mk_app (gref reference:(sf_congT)) [| tyl; fn; traw; tnorm; h2 |]))
          end in
        (* [comment removed for export] *)
        (* [comment removed for export] *)
        let (an, pa) := match (match draws with [] => direct_addr x a | _ => None end) with
          | Some (an, pn) => (an, pn)
          | None =>
              let restc := (owd, lg) :: List.map (fun v => (wd, v)) draws in
              let (ns, h) := joint (fun () => ltac1:(iv |- cbv beta delta [sf_load_goal]; vnorm_for iv) iv) ((wd, a) :: restc) in
              (match ns with
               | e :: restn =>
                   let (tyr, rraw) := tup restc in
                   let (_, rnorm) := tup (List.map2 (fun (ty, _) vn => (ty, vn)) restc restn) in
                   (e, pair_eq1 wd tyr a e rraw rnorm h)
               | [] => sf_fail "policy address"
               end)
          end in
        (* [comment removed for export] *)
        let kkT := if sf_share then
                     (match Constr.Unsafe.kind kk with
                      | Constr.Unsafe.Lambda b _ =>
                          let r1T := mk_app (gref reference:(bvmap_set)) [| '5%N; wd; rdv; fv; rT |] in
                          Constr.Unsafe.make (Constr.Unsafe.Lambda b
                            (mk_app (gref reference:(EDone)) [| mk_app (gref reference:(Core)) [| r1T; f; pc1; fc; rv |] |]))
                      | _ => kk
                      end)
                   else kk in
        let accp := mk_app (gref reference:(sfA_accs_load)) [| segs; m; n; a; an; kkT; fl; vl; h1;
                       mk_lam @x (mk_app (gref reference:(bv)) [| n |]) (mk_app (gref reference:(eq_refl)) [| gref reference:(bool); gref reference:(true) |]); pa |] in
        (mk_app (gref reference:(sf_install_load)) [| segs; ro; m; a; nb; fl; vl; kt; mk_app ok [| mr; ms1T |]; h1; ek |], ms1, Some (an, nb, accp))
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
                     mk_app (gref reference:(pair)) [| gref reference:(core); ty_mem; mk_app (gref reference:(Core)) [| rT; f; pc1; fc; rv |]; mk_rel 1 |] |]) in
        let r1n := List.fold_left2 (fun t p vn => tree_set p vn t) rnew dpaths dnorms in
        let ms1 := mk_app cms [| r1n; f; pcn; fc; rv; mn; ro |] in
        let r1nT := if sf_share then List.fold_left2 (fun t p vn => tsetT t p vn) rT dpaths dnorms else r1n in
        let ms1T := if sf_share then mk_app cms [| r1nT; f; pcn; fc; rv; mn; ro |] else ms1 in
        ms1t.(contents) := Some ms1T;
        let (h1, ek) := match draws with
          | [] => (hj, mk_app (gref reference:(sf_refl)) [| mk_app ok [| mr; ms1T |] |])
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
              let rh := if sf_share then List.fold_left2 (fun t p pr => tsetT t p pr) rT dpaths projs
                        else List.fold_left2 (fun t p pr => tree_set p pr t) rnew dpaths projs in
              let fn := mk_lam @t tyl (mk_app ok [| mr; mk_app cms [| rh; f; pcn; fc; rv; mn; ro |] |]) in
              (sf_eqchk tyl traw tnorm h2; (h1, mk_app (gref reference:(sf_congT)) [| tyl; fn; traw; tnorm; h2 |]))
          end in
        (* [comment removed for export] *)
        (* [comment removed for export] *)
        let (an, pa) := match (match draws with [] => direct_addr x a | _ => None end) with
          | Some (an, pn) => (an, pn)
          | None =>
              let restc := (omem, sg) :: List.map (fun v => (wd, v)) draws in
              let (ns, h) := joint (fun () => ltac1:(iv |- cbv beta delta [sf_store_goal]; vnorm_for iv) iv) ((wd, a) :: restc) in
              (match ns with
               | e :: restn =>
                   let (tyr, rraw) := tup restc in
                   let (_, rnorm) := tup (List.map2 (fun (ty, _) vn => (ty, vn)) restc restn) in
                   (e, pair_eq1 wd tyr a e rraw rnorm h)
               | [] => sf_fail "policy address"
               end)
          end in
        let kdone := if sf_share then mk_app (gref reference:(EDone)) [| mk_app (gref reference:(Core)) [| rT; f; pc1; fc; rv |] |]
                     else (lazy_match! body with EStore _ _ _ ?k => k end) in
        let accp := mk_app (gref reference:(sfA_accs_store)) [| segs; m; n; a; an; v; kdone; mn; h1;
                       mk_app (gref reference:(eq_refl)) [| gref reference:(bool); gref reference:(true) |]; pa |] in
        (mk_app (gref reference:(sf_install_store)) [| segs; ro; m; a; nb; bs; mn; kt; mk_app ok [| mr; ms1T |]; h1; ek |], ms1, Some (an, nb, accp))
    | _ => sf_fail "raw shape"
    end in
    (if (x.(lit_delta)).(contents) then
       (if has_litself x ms1 then sf_fail "litself delta-instance in Q and a syntactic instance in the new state" else ())
     else ());
    stop 7;
    let npol := { contents := 0 } in
    tm "install" (fun () =>
      let qkv := qk.(contents) in
      let k := tm "k" (fun () => strip_cast open_constr:(_ : evtA $segs $pp $qkv $ms1)) in
      let accT := '(acc) in
      let (rs, accp, polp) := match accs with
        | None =>
            let nil_ := mk_app (gref reference:(nil)) [| accT |] in
            (nil_, mk_app (gref reference:(eq_refl)) [| mk_app (gref reference:(list)) [| accT |]; nil_ |],
             mk_app (gref reference:(Forall_nil)) [| accT; pp |])
        | Some (an, nb, accp) =>
            let pr := mk_app (gref reference:(pair)) [| wd; gref reference:(nat); an; nb |] in
            let rs := mk_app (gref reference:(cons)) [| accT; pr; mk_app (gref reference:(nil)) [| accT |] |] in
            let fa := mk_app (gref reference:(Forall)) [| accT; pp; rs |] in
            let pv := strip_cast open_constr:(_ : $fa) in
            (rs, accp, pv)
        end in
      let ms1T := match ms1t.(contents) with Some t => t | None => ms1 end in
      let term := mk_app (gref reference:(sfA_evt_step)) [| segs; pp; q; (if sf_share then rT else r); f; mk_app (gref reference:(Z_to_bv)) [| x.(c_n64); pc |]; fc; rv; m; ro; w; i; sz; ms1T; rs; fwp; ecp; dcp; eqp; accp; polp; k |] in
      let term := if sf_share then
                    Constr.Unsafe.make (Constr.Unsafe.LetIn (Constr.Binder.make (Some r0id) (mk_app (gref reference:(bvmap)) [| '5%N; wd |])) r
                                          (Constr.Unsafe.closenl [r0id] 1 term))
                  else term in
      (if sf_check then
         match Constr.Unsafe.check term with
         | Val _ => ()
         | Err e => printf "STEPFASTA-ILLTYPED %a" (fun () e => Message.of_exn e) e; sf_fail "ill-typed"
         end
       else ());
      match Constr.Unsafe.kind k with
      | Constr.Unsafe.Evar ev _ =>
          tm "exact" (fun () =>
            Std.exact_no_check term;
            (match Constr.Unsafe.kind polp with
             | Constr.Unsafe.Evar evp _ =>
                 (* [comment removed for export] *)
                 Control.new_goal evp;
                 Control.focus 1 1 (fun () => Std.clear (clear_hyps.(contents)); tm "policy" (fun () => ltac1:(solve_policy)));
                 (npol.(contents) := Control.numgoals ())
             | _ => ()
             end);
            Control.new_goal ev)
      | _ => sf_fail "install: continuation"
      end);
    (* [comment removed for export] *)
    let ng := Int.add (npol.(contents)) 1 in
    Control.focus ng ng (fun () =>
    stop 8;
    tm "clear" (fun () => Std.clear (clear_hyps.(contents)));
    stop 9;
    (* [comment removed for export] *)
    tm "post" (fun () => lazy_match! goal with
       | [ |- evtA _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ _) _) ] => ltac1:(iv |- mem_after_store_opt; fix_lit_store; post_step iv) iv
       | [ |- _ ] => ()
       end);
    (if z then
       lazy_match! goal with
       | [ |- evtA ?segs' ?pp' ?q' (MS ?r' ?f' ?pc' ?fc' ?rv' ?m' ?ro') ] =>
           if Constr.is_var m' then () else
           (* [comment removed for export] *)
           let (h, mn) := small_goal (fun () => ltac1:(zsimp)) m' '(word -> option byte) in
           let k := strip_cast open_constr:(_ : evtA $segs' $pp' $q' (MS $r' $f' $pc' $fc' $rv' $mn $ro')) in
           let term := mk_app '@sfA_evt_mem [| segs'; pp'; q'; r'; f'; pc'; fc'; rv'; m'; mn; ro'; Control.hyp h; k |] in
           match Constr.Unsafe.kind k with
           | Constr.Unsafe.Evar ev _ => Std.exact_no_check term; Control.new_goal ev; Std.clear [h]
           | _ => sf_fail "install: continuation"
           end
       end
     else ()));
    (* [comment removed for export] *)
    (if z then (if Int.gt ng 1 then Control.focus 1 (Int.sub ng 1) (fun () => Control.enter (fun () => ltac1:(zsimp))) else ()) else ())
  | [ |- _ ] => sf_fail "goal shape"
  end.


(* [comment removed for export] *)
Ltac2 sfA_step (z : bool) : unit :=
  let ph := { contents := 0 } in
  if Bool.neg sf_debug then sfA_step_ ph z else
  Control.plus (fun () => sfA_step_ ph z)
    (fun e => (if sf_debug then
                 (lazy_match! goal with
                  | [ |- evtA _ _ _ (MS _ _ ?pc _ _ _ _) ] => printf "STEPFASTA-PHASE %i at pc %t" (ph.(contents)) pc
                  | [ |- _ ] => printf "STEPFASTA-PHASE %i" (ph.(contents))
                  end) else ()); Control.zero e).

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac stepA_core_old segs P R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
    let ec := eval vm_compute in (is_ecall w) in
    lazymatch ec with
    | false =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evtA_step;
        [ split; [reflexivity|];
          rewrite (step_genA segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbvA; simp_is_x0; simp_regs; vnorm_for i; amo_phase i;
          try solve_load; vnorm_extra i; try solve_store;
          reflexivity
        | solve_policy
        | simp_regs; vnorm_for i; vnorm_extra i; mem_after_store_opt; fix_lit_store; post_step i ]
      | None => fail "undecodable instruction at" pc
      end
    | true => fail "ecall at" pc
    end
  | None => fail "no instruction at" pc
  end.

Ltac sfA_old_step :=
  lazymatch goal with
  | |- evtA ?segs ?P ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => stepA_core_old segs P R F pc fc rv m ro
  | |- evtA _ _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.
Ltac sfA_old_zstep := sfA_old_step; zsimp.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac2 Type exn ::= [ SFA_Captured ((constr * (ident * constr option * constr) list) list) ].

Ltac2 sfA_snapshot () : (constr * (ident * constr option * constr) list) list :=
  let acc := { contents := [] } in
  Control.enter (fun () => acc.(contents) := (Control.goal (), Control.hyps ()) :: acc.(contents));
  List.rev (acc.(contents)).

Ltac2 sfA_old (z : bool) : unit := if z then ltac1:(sfA_old_zstep) else ltac1:(sfA_old_step).

(* [comment removed for export] *)
Ltac2 sfA_goal_eq (gf : constr) (go : constr) : bool :=
  if Constr.equal gf go then true
  else
    let qev (g : constr) := match Constr.Unsafe.kind g with
      | Constr.Unsafe.App f args =>
          if Int.equal (Array.length args) 4 then
            (if is_k (kof reference:(evtA)) f then Some (Array.get args 0, Array.get args 1, Array.get args 3) else None)
          else None
      | _ => None end in
    match qev gf, qev go with
    | Some (s1, p1, ms1), Some (s2, p2, ms2) =>
        if Constr.equal s1 s2 then (if Constr.equal p1 p2 then Constr.equal ms1 ms2 else false) else false
    | _, _ => false
    end.

Ltac2 sfA_dual (z : bool) : unit :=
  let g0 := Control.goal () in
  let res := Control.case (fun () =>
     sfA_step z;
     let snap := sfA_snapshot () in
     Control.zero (SFA_Captured snap)) in
  match res with
  | Val _ => sf_fail "impossible"
  | Err e =>
      match e with
      | SFA_Captured snapf =>
          sfA_old z;
          let snapo := sfA_snapshot () in
          if Int.equal (List.length snapf) (List.length snapo) then
            (if List.for_all2 (fun (gf, hf) (go, ho) => if sfA_goal_eq gf go then hyps_equal hf ho else false) snapf snapo
             then printf "STEPFASTA-OK"
             else printf "STEPFASTA-MISMATCH at %t@ FAST: %a@ OLD: %a" g0
                    (fun () l => List.fold_left (fun m (g, _) => Message.concat m (Message.concat (Message.of_string " || ") (Message.of_constr g))) (Message.of_string "") l) snapf
                    (fun () l => List.fold_left (fun m (g, _) => Message.concat m (Message.concat (Message.of_string " || ") (Message.of_constr g))) (Message.of_string "") l) snapo)
          else printf "STEPFASTA-MISMATCH(goal count %i vs %i) at %t" (List.length snapf) (List.length snapo) g0
      | _ =>
          printf "STEPFASTA-FALLBACK %a" (fun () e => Message.of_exn e) e;
          sfA_old z
      end
  end.

(* [comment removed for export] *)
Ltac2 mutable sfA_mode : int := 1.

Ltac2 sfA_core1 (z : bool) : unit :=
  if Int.equal sfA_mode 0 then sfA_old z
  else if Int.equal sfA_mode 1 then
    Control.once (fun () =>
      Control.plus (fun () => sfA_step z)
        (fun e => (if sf_debug then printf "STEPFASTA-FALLBACK %a" (fun () e => Message.of_exn e) e else ()); sfA_old z))
  else sfA_dual z.

(* [comment removed for export] *)
Ltac2 sfA_core (z : bool) : unit := Control.enter (fun () => sfA_core1 z).

(* [comment removed for export] *)
Ltac stepA_core segs P R F pc fc rv m ro ::= ltac2:(sfA_core false).
Ltac zstepA ::= ltac2:(sfA_core true).
(* [comment removed for export] *)
Ltac zstep ::=
  lazymatch goal with
  | |- evtA _ _ _ _ => ltac2:(sfA_core true)
  | |- _ => ltac2:(sf_core true)
  end.
