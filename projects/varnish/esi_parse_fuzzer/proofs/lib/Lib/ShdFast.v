(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MliaFast DietLia2 LiaTwx2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac shd_mlia := first [ mlia_fast | ltac2:(RL.oneshot_mlia ()) ].
Ltac shd_mlia2 := first [ mlia_fast | ltac2:(RL.oneshot_mlia ()) | lia ].

(* [comment removed for export] *)
Ltac2 rec shd_lastn (n : int) (l : 'a list) : 'a list :=
  let k := Int.sub (List.length l) n in if Int.le k 0 then l else List.skipn k l.
(* [comment removed for export] *)
  Ltac2 shd_build_l (sec : bool) (hyps : (ident * constr option * constr) list) : RL.table :=
    let bads := RL.bad_consts () in
    let ops := RL.op_consts () in let muls := RL.mul_consts () in let dms := RL.dm_consts () in let rels := RL.rel_consts () in
    let s := { RL.bv := FMap.empty FSet.Tags.ident_tag; RL.bk := FMap.empty FSet.Tags.constant_tag; RL.bo := []; RL.n := 0 } in
    (* [comment removed for export] *)
    let cats := { contents := [] } in let cdeep := { contents := [] } in let chyp := { contents := [] } in
    let known := { contents := FSet.empty FSet.Tags.ident_tag } in
    let csim := { contents := [] } in let clog := { contents := [] } in let cunc := { contents := [] } in
    let hid := { contents := [] } in let hcl := { contents := [] } in let hdm := { contents := [] } in
    let hlg := { contents := [] } in let hev := { contents := [] } in
    let others := { contents := [] } in
    let nh := { contents := 0 } in
    List.iter (fun h => let (id, body, ty) := h in
      known.(contents) := FSet.add id (known.(contents));
      match body with
      | Some _ => ()
      | None =>
          let loc := zt_is_local id in
          let add_hyp (parts : constr list) (logic : bool) :=
            let hi := nh.(contents) in
            nh.(contents) := Int.add hi 1;
            let anydm := { contents := false } in
            List.iter (fun p =>
              let c := { RL.ats := []; RL.simple := true; RL.dm := false; RL.unclean := false } in
              RL.stmt_atoms bads ops muls dms rels false s true c p;
              (if c.(RL.dm) then anydm.(contents) := true else ());
              cats.(contents) := c.(RL.ats) :: cats.(contents);
              (if c.(RL.dm) then
                 (let c2 := { RL.ats := []; RL.simple := true; RL.dm := false; RL.unclean := false } in
                  RL.stmt_atoms bads ops muls dms rels true s true c2 p;
                  cdeep.(contents) := c2.(RL.ats) :: cdeep.(contents))
               else cdeep.(contents) := c.(RL.ats) :: cdeep.(contents));
              chyp.(contents) := hi :: chyp.(contents);
              csim.(contents) := (if logic then false else c.(RL.simple)) :: csim.(contents);
              clog.(contents) := logic :: clog.(contents);
              cunc.(contents) := (if c.(RL.unclean) then true else c.(RL.dm)) :: cunc.(contents)) parts;
            hid.(contents) := id :: hid.(contents);
            hcl.(contents) := (if loc then true else sec) :: hcl.(contents);
            hdm.(contents) := anydm.(contents) :: hdm.(contents);
            hlg.(contents) := logic :: hlg.(contents);
            hev.(contents) := false :: hev.(contents) in
          match RL.plain_parts rels [] ty with
          | Some parts =>
              (* [comment removed for export] *)
              if RL.has_evar ty then (if loc then others.(contents) := id :: others.(contents) else ())
              else add_hyp parts false
          | None =>
              if RL.logical rels ty then
                (if RL.has_evar ty then (if loc then others.(contents) := id :: others.(contents) else ())
                 else add_hyp [ty] true)
              else if loc then (if zt_is_prop ty then others.(contents) := id :: others.(contents) else ())
              else ()
          end
      end) hyps;
    { RL.t_st := s; RL.t_bads := bads; RL.t_ops := ops; RL.t_muls := muls; RL.t_dms := dms; RL.t_rels := rels;
      RL.t_catoms := Array.of_list (List.rev (cats.(contents)));
      RL.t_cdeep := Array.of_list (List.rev (cdeep.(contents)));
      RL.t_chyp := Array.of_list (List.rev (chyp.(contents)));
      RL.t_csimple := Array.of_list (List.rev (csim.(contents)));
      RL.t_clogic := Array.of_list (List.rev (clog.(contents)));
      RL.t_cunclean := Array.of_list (List.rev (cunc.(contents)));
      RL.t_hid := Array.of_list (List.rev (hid.(contents)));
      RL.t_hclear := Array.of_list (List.rev (hcl.(contents)));
      RL.t_hdm := Array.of_list (List.rev (hdm.(contents)));
      RL.t_hlogic := Array.of_list (List.rev (hlg.(contents)));
      RL.t_hevar := Array.of_list (List.rev (hev.(contents)));
      RL.t_others := others.(contents);
      RL.t_known := known.(contents);
      RL.t_natoms := s.(RL.n) }.
  (* [comment removed for export] *)
  Ltac2 shd_oneshot_n1 (n : int) : unit :=
    Control.enter (fun () =>
      let tb := shd_build_l RL.sec (shd_lastn n (Control.hyps ())) in
      let ex := RL.new_exh () in
      RL.schedule tb ex (RL.tier tb) true).
  (* [comment removed for export] *)
  Ltac2 shd_oneshot_n1dm (n : int) : unit :=
    Control.enter (fun () =>
      let tb := shd_build_l RL.sec (shd_lastn n (Control.hyps ())) in
      let ex := RL.new_exh () in
      Control.once (fun () => Control.plus (fun () => RL.schedule tb ex (RL.tier tb) true) (fun _ => RL.schedule tb ex (RL.tier_dm tb) true))).
(* [comment removed for export] *)
Ltac shd_mlia0 := first [ mlia_fast | ltac2:(shd_oneshot_n1 24) ].
Ltac shd_mlia01 := first [ mlia_fast | ltac2:(shd_oneshot_n1dm 24) ].
Ltac shd_mlia02 := first [ mlia_fast | ltac2:(shd_oneshot_n1dm 24) | lia ].
