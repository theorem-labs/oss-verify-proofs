(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0034. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. From Ltac2 Require Ltac2.
Module ArtTac.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0034. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.MmapSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.As0StepLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtAtomics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0034.ArtRegs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtStk.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From Ltac2 Require Ltac2. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac alia_small := first [ solve [ L5FastLia.lia_ne ] | L5FastLia.lia_st ].
(* [comment removed for export] *)
Ltac alia_fat := first [ solve [ L5FastLia.prune_atomic; L5FastLia.lia_ne ] | solve [ L5FastLia.prune_arith; L5FastLia.lia_ne ] ].
Ltac alia := ltac2:(Ltac2.Control.enter (fun () => if Ltac2.Int.lt (Ltac2.List.length (Ltac2.Control.hyps ())) 60 then ltac1:(alia_small) else ltac1:(alia_fat))).

Local Ltac lia := alia.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac zif := repeat match goal with
  | |- context [?x <? ?y] => first [ replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia)
                                   | replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia) ]
  | |- context [?x =? ?y] => first [ replace (x =? y) with false by (symmetry; apply Z.eqb_neq; lia)
                                   | replace (x =? y) with true by (symmetry; apply Z.eqb_eq; lia) ]
  | |- context [?x <=? ?y] => first [ replace (x <=? y) with false by (symmetry; apply Z.leb_gt; lia)
                                   | replace (x <=? y) with true by (symmetry; apply Z.leb_le; lia) ] end.
(* [comment removed for export] *)
Ltac zbn := rewrite ?art_zb_addi, ?art_zb_add, ?art_zb_mul, ?art_zb_sub; try (rewrite !art_zb_slli by lia); try (rewrite !art_zb_xori_m1 by lia);
  try (rewrite !art_zb_sltiu by lia); try (rewrite !art_zb_sltu by lia); zif.
Ltac zcond := rwH; rewrite ?art_c_eq_zb, ?art_c_ltu_zb by lia;
  first [ apply Z.eqb_neq; lia | apply Z.eqb_eq; lia | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia | idtac ].
Ltac zbft F D := stepb_ft F D ltac:(zcond).
Ltac zbtk F D := stepb_tk F D ltac:(zcond).
(* [comment removed for export] *)
Ltac zaddr a :=
  gres; rwH; imm_norm; rewrite ?art_zb_addi, ?art_zb_add;
  lazymatch goal with |- rdn _ _ ?E _ = _ => replace E with (Z_to_bv 64 a : word) by (first [reflexivity | f_equal; lia | apply art_zb_eq; f_equal; lia]) end.
Ltac zld F D a HYP :=
  chain_step; [reflexivity | eapply step_ld; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply bytes_le_to_Z_8 ] | step_simpl; vnorm].
Ltac zlw F D a HYP :=
  chain_step; [reflexivity | eapply step_lw; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes4; lia ] | step_simpl; vnorm];
  rewrite ?art_v_lw_small by lia.
Ltac zlwu F D a HYP :=
  chain_step; [reflexivity | eapply step_lwu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes4; lia ] | step_simpl; vnorm].
(* [comment removed for export] *)
Ltac zst LEM n F D a v oktac :=
  chain_step; [reflexivity | eapply (LEM _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a : word) (Z_to_bv 64 v : word));
    [exact F | reflexivity | exact D
    | gres; rwH; imm_norm; rewrite ?art_zb_addi, ?art_zb_add; first [reflexivity | f_equal; lia | apply art_zb_eq; f_equal; lia]
    | gres; rwH; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]
    | oktac ]
  | step_simpl];
  change (wbytes ?M0 (Z_to_bv 64 a) (word_to_le_bytes n (Z_to_bv 64 v))) with (Wn n M0 a v).
Ltac zsw F D a v oktac := zst step_sw_at 4%nat F D a v oktac.
Ltac zsh F D a v oktac := zst step_sh_at 2%nat F D a v oktac.
(* [comment removed for export] *)
Ltac zsb F D a v oktac :=
  chain_step; [reflexivity | eapply (step_sb_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a : word) (Z_to_bv 64 v : word) (Z_to_bv 8 v));
    [exact F | reflexivity | exact D
    | gres; rwH; imm_norm; rewrite ?art_zb_addi, ?art_zb_add; first [reflexivity | f_equal; lia | apply art_zb_eq; f_equal; lia]
    | gres; rwH; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]
    | rewrite art_u_lit; [reflexivity | first [lia | assumption | auto with zarith]]
    | oktac ]
  | step_simpl];
  lazymatch goal with |- context [wbytes ?M0 (Z_to_bv 64 a) [Z_to_bv 8 v]] =>
    replace (wbytes M0 (Z_to_bv 64 a) [Z_to_bv 8 v]) with (Wn 1 M0 a v) by (unfold Wn; rewrite (art_bytes1 v) by (first [lia | assumption | auto with zarith]); reflexivity) end.
Ltac zsd F D a v oktac := zst step_sd_at 8%nat F D a v oktac.
(* [comment removed for export] *)
Ltac zapart :=
  lazymatch goal with |- apart _ _ _ _ => idtac | _ => fail end;
  first [ assumption
        | apply apart_sym; assumption
        | unfold apart at 1; lia
        | match goal with H : apart _ _ _ _ |- _ => unfold apart at 1; unfold apart in H; destruct H; lia end ].
(* [comment removed for export] *)
Ltac recell_old H := first [ exact H | apply cell_Wn_other; [ lia | lia | lia | lia | zapart | recell_old H ] | apply cell_Wf_other; [ lia | lia | lia | lia | zapart | recell_old H ] ].
Ltac rewok_old H := first [ exact H | eapply (wr_wok _ _ _ _ H); lia | apply wok_Wn; rewok_old H ].
(* [comment removed for export] *)
Ltac zamoadd_d F D a old v CELL oktac :=
  chain_step; [reflexivity
  | eapply (art_step_amoadd_d_x0 _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a : word) (Z_to_bv 64 v : word) (Z_to_bv 64 old : word));
    [ exact F | reflexivity | exact D
    | gres; rwH; rewrite ?art_zb_addi, ?art_zb_add; first [reflexivity | f_equal; lia | apply art_zb_eq; f_equal; lia]
    | rewrite art_u_lit by lia; lia
    | exact CELL | apply bytes_le_to_Z_8
    | gres; rwH; first [reflexivity | f_equal; lia]
    | oktac ]
  | step_simpl ];
  rewrite ?art_zb_add;
  change (wbytes ?M0 (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 (old + v)))) with (Wn 8 M0 a (old + v)).
(* [comment removed for export] *)
Ltac zstep F D := stepn F D; rwH; vals_lit; zbn.


(* [comment removed for export] *)
Ltac kept_solve :=
  gres; rwH;
  first [ reflexivity
        | rewrite Z_to_bv_bv_unsigned; reflexivity
        | f_equal; lia
        | lazymatch goal with
          | |- getr (regupd _ ?i _) ?r = _ =>
              first [ rewrite getr_other by (assumption || (symmetry; assumption) || reg_neq_tac); kept_solve
                    | let NE := fresh "NE" in
                      destruct (decide (r = i)) as [->|NE]; [kept_solve | rewrite getr_other by (exact NE || (symmetry; exact NE)); kept_solve] ]
          end ].

(* [comment removed for export] *)
Ltac zlh F D a HYP :=
  chain_step; [reflexivity | eapply step_lh; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm];
  rewrite ?art_v_lh_small by lia.
(* [comment removed for export] *)
Ltac zlbu F D a HYP :=
  chain_step; [reflexivity | eapply step_lbu; [exact F | reflexivity | exact D | zaddr a; first [eapply cell_rdn1; [ | exact HYP]; lia | exact HYP] ] | step_simpl; vnorm];
  try (rewrite art_u8_lit by lia).
Ltac zlb F D a HYP :=
  chain_step; [reflexivity | eapply step_lb; [exact F | reflexivity | exact D | zaddr a; first [eapply cell_rdn1; [ | exact HYP]; lia | exact HYP] ] | step_simpl; vnorm];
  try (rewrite art_v_lb_small by lia).

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zval :=
  lazymatch goal with
  | |- ?a = ?b =>
      first [ is_evar b; reflexivity | is_evar a; reflexivity | constr_eq a b; reflexivity
            | lazymatch a with Z_to_bv 64 _ => lazymatch b with Z_to_bv 64 _ => first [f_equal; lia | apply art_zb_eq; lia] end end
            | rewrite Z_to_bv_bv_unsigned; lazymatch goal with |- ?a' = ?b' => constr_eq a' b'; reflexivity end
            | bveq ]
  end.
(* [comment removed for export] *)
Ltac zcell_old :=
  lazymatch goal with
  | |- cell _ ?M ?a ?n ?v =>
      first [ match goal with H : cell _ M a n _ |- _ => exact H end
            | match goal with H : cell _ M ?a' n v |- _ => replace a with a' by lia; exact H end
            | lazymatch M with
              | Wn _ _ _ _ => first [ apply cell_Wn_hit; lia | apply cell_Wn_other; [lia|lia|lia|lia| zapart | zcell_old] ]
              | Wf _ _ _ _ => apply cell_Wf_other; [lia|lia|lia|lia| zapart | zcell_old]
              end ]
  end.
Ltac zwr_old :=
  lazymatch goal with
  | |- wr _ ?M ?b ?m =>
      first [ match goal with H : wr _ M b m |- _ => exact H end
            | match goal with H : wr _ M ?b' ?m' |- _ => apply (wr_sub _ _ _ _ _ _ H); lia end
            | lazymatch M with
              | Wn _ _ _ _ => apply wr_Wn; zwr_old
              | Wf _ _ _ _ => apply wr_Wf; zwr_old
              end ]
  end.
Ltac zwok_old :=
  lazymatch goal with
  | |- wok _ ?M ?b ?m =>
      first [ match goal with H : wok _ M b m |- _ => exact H end
            | match goal with H : wr _ M ?b' ?m' |- _ => apply (wr_wok _ _ _ _ H); lia end
            | lazymatch M with
              | Wn _ _ _ _ => apply wok_Wn; zwok_old
              | Wf _ _ _ _ => apply wok_Wf; zwok_old
              end ]
  end.
(* [comment removed for export] *)
Ltac zs_plit p := lazymatch p with xH => constr:(true) | xO ?q => zs_plit q | xI ?q => zs_plit q | _ => constr:(false) end.
Ltac zs_lit z := lazymatch z with Z0 => constr:(true) | Zpos ?p => zs_plit p | Zneg ?p => zs_plit p | _ => constr:(false) end.
Ltac zs_nlit n := lazymatch n with O => constr:(true) | S ?k => zs_nlit k | _ => constr:(false) end.
Ltac zs_neg k := lazymatch k with Zpos ?p => constr:(Zneg p) | Zneg ?p => constr:(Zpos p) | Z0 => constr:(Z0) end.
(* [comment removed for export] *)
Ltac zs_split a :=
  lazymatch a with
  | ?x + ?k1 + ?k2 =>
      lazymatch zs_lit k2 with
      | true => lazymatch zs_lit k1 with true => constr:((x, Sh_off2 k1 k2)) | false => constr:((x + k1, Sh_off k2)) end
      | false => constr:((a, Sh_bare)) end
  | ?x - ?k1 + ?k2 =>
      lazymatch zs_lit k2 with
      | true => lazymatch zs_lit k1 with true => let nk := zs_neg k1 in constr:((x, Sh_off2 nk k2)) | false => constr:((x - k1, Sh_off k2)) end
      | false => constr:((a, Sh_bare)) end
  | ?x + ?k1 => lazymatch zs_lit k1 with true => constr:((x, Sh_off k1)) | false => constr:((a, Sh_bare)) end
  | ?x - ?k1 => lazymatch zs_lit k1 with true => let nk := zs_neg k1 in constr:((x, Sh_off nk)) | false => constr:((a, Sh_bare)) end
  | _ => lazymatch zs_lit a with true => constr:((0, Sh_off a)) | false => constr:((a, Sh_bare)) end
  end.
(* [comment removed for export] *)
Ltac zs_upd env B lo hi :=
  lazymatch env with
  | cons (mkhull B ?l0 ?h0) ?tl => let l1 := eval cbv in (Z.min l0 lo) in let h1 := eval cbv in (Z.max h0 hi) in constr:(cons (mkhull B l1 h1) tl)
  | cons ?h ?tl => let tl' := zs_upd tl B lo hi in constr:(cons h tl')
  | nil => constr:(cons (mkhull B lo hi) nil)
  end.
Ltac zs_find env B :=
  lazymatch env with
  | cons (mkhull B _ _) _ => constr:(O)
  | cons _ ?tl => let j := zs_find tl B in constr:(S j)
  end.
Ltac zs_has_cell M := lazymatch goal with | _ : cell _ M _ _ _ |- _ => constr:(true) | _ => constr:(false) end.
Ltac zs_has_w M := lazymatch goal with | _ : wok _ M _ _ |- _ => constr:(true) | _ : wr _ M _ _ |- _ => constr:(true) | _ => constr:(false) end.
(* [comment removed for export] *)
Ltac zs_cdesc M first Mh env Bb ob mz :=
  let stop := constr:((env, @nil wlayer, M)) in
  let go n M' a knd :=
    lazymatch zs_nlit n with
    | false => stop
    | true =>
      let r := zs_split a in
      lazymatch r with
      | (?B, ?s) =>
        let o := eval cbv in (aoff s) in
        let e := eval cbv in (o + Z.of_nat n) in
        let disj := lazymatch B with
                    | Bb => eval cbv in ((e <=? ob) || (ob + mz <=? o))
                    | _ => constr:(true) end in
        lazymatch disj with
        | false => stop
        | true =>
          let env1 := zs_upd env B o e in
          let j := zs_find env1 B in
          let r' := zs_cdesc M' false Mh env1 Bb ob mz in
          lazymatch r' with (?env2, ?l', ?M0) => constr:((env2, cons (mkwl j s knd) l', M0)) end
        end
      end
    end in
  let hashyp := lazymatch M with
                | Mh => constr:(true)
                | _ => lazymatch first with true => constr:(false) | false => lazymatch Mh with tt => zs_has_cell M | _ => constr:(false) end end
                end in
  lazymatch hashyp with
  | true => stop
  | false =>
    lazymatch M with
    | Wn ?n ?M' ?a ?v => go n M' a constr:(WKn n v)
    | Wf ?M' ?a ?k ?bb => go k M' a constr:(WKf k bb)
    | _ => stop
    end
  end.
(* [comment removed for export] *)
Ltac zs_hull_apart :=
  first [ alia
        | match goal with H : apart _ _ _ _ |- _ => let H' := fresh "HA" in pose proof H as H'; unfold apart in H'; destruct H' as [H'|H']; alia end ].
Ltac zs_env_oth :=
  lazymatch goal with
  | |- env_oth nil _ _ => apply env_oth_nil
  | |- env_oth (cons _ _) _ _ => apply env_oth_cons; [ alia | alia | zs_hull_apart | zs_env_oth ]
  end.
Ltac zapart_n :=
  lazymatch goal with |- apart _ _ _ _ => idtac | _ => fail end;
  first [ assumption
        | apply apart_sym; assumption
        | unfold apart at 1; alia
        | match goal with H : apart _ _ _ _ |- _ => unfold apart at 1; unfold apart in H; destruct H; alia end ].
(* [comment removed for export] *)
Ltac zcell_prefix_to Mh :=
  lazymatch goal with
  | |- cell ?sg ?M ?b ?m ?u =>
      lazymatch zs_nlit m with true => idtac end;
      let rb := zs_split b in
      lazymatch rb with
      | (?Bb, ?sb) =>
        let ob := eval cbv in (aoff sb) in
        let mz := eval cbv in (Z.of_nat m) in
        let eb := eval cbv in (ob + mz) in
        let r := zs_cdesc M true Mh constr:(cons (mkhull Bb ob eb) nil) Bb ob mz in
        lazymatch r with
        | (_, nil, _) => fail
        | (?env, ?l, ?M0) =>
            let HE := fresh "HE" in
            assert (HE : env_ok env b mz) by (apply env_ok_intro; [ alia | alia | zs_env_oth ]);
            refine (cell_wstk_other sg env M0 l b sb m mz u (@eq_refl Z b) HE (@eq_refl bool true) _);
            clear HE
        end
      end
  end.
Ltac zcell_prefix := zcell_prefix_to tt.
Ltac zcell_n :=
  lazymatch goal with
  | |- cell _ ?M ?a ?n ?v =>
      first [ match goal with H : cell _ M a n _ |- _ => exact H end
            | match goal with H : cell _ M ?a' n v |- _ => replace a with a' by alia; exact H end
            | tryif zcell_prefix then zcell_n
              else lazymatch M with
                   | Wn _ _ _ _ => first [ apply cell_Wn_hit; alia | apply cell_Wn_other; [alia|alia|alia|alia| zapart_n | zcell_n] ]
                   | Wf _ _ _ _ => apply cell_Wf_other; [alia|alia|alia|alia| zapart_n | zcell_n]
                   end ]
  end.
Ltac zcell := first [ zcell_n | zcell_old ].

(* [comment removed for export] *)
Ltac zs_wdesc M first :=
  let hashyp := lazymatch first with true => constr:(false) | false => zs_has_w M end in
  lazymatch hashyp with
  | true => constr:((@nil slayer, M))
  | false =>
    lazymatch M with
    | Wn ?n ?M' ?a ?v => let r := zs_wdesc M' false in lazymatch r with (?l, ?M0) => constr:((cons (SLn n a v) l, M0)) end
    | Wf ?M' ?a ?k ?bb => let r := zs_wdesc M' false in lazymatch r with (?l, ?M0) => constr:((cons (SLf a k bb) l, M0)) end
    | _ => constr:((@nil slayer, M))
    end
  end.
Ltac zwr_n :=
  lazymatch goal with
  | |- wr ?sg ?M ?b ?m =>
      first [ match goal with H : wr _ M b m |- _ => exact H end
            | match goal with H : wr _ M ?b' ?m' |- _ => apply (wr_sub _ _ _ _ _ _ H); alia end
            | let r := zs_wdesc M true in
              lazymatch r with
              | (nil, _) => fail
              | (?l, ?M0) => refine (wr_sstk sg M0 l b m _); zwr_n
              end ]
  end.
Ltac zwr := first [ zwr_n | zwr_old ].
Ltac zwok_n :=
  lazymatch goal with
  | |- wok ?sg ?M ?b ?m =>
      first [ match goal with H : wok _ M b m |- _ => exact H end
            | match goal with H : wr _ M ?b' ?m' |- _ => apply (wr_wok _ _ _ _ H); alia end
            | let r := zs_wdesc M true in
              lazymatch r with
              | (nil, _) => fail
              | (?l, ?M0) => refine (wok_sstk sg M0 l b m _); zwok_n
              end ]
  end.
Ltac zwok := first [ zwok_n | zwok_old ].
(* [comment removed for export] *)
Ltac zs_hdesc M Mh :=
  lazymatch M with
  | Mh => constr:((@nil slayer, M))
  | Wn ?n ?M' ?a ?v => let r := zs_hdesc M' Mh in lazymatch r with (?l, ?M0) => constr:((cons (SLn n a v) l, M0)) end
  end.
Ltac rewok_n H :=
  lazymatch goal with
  | |- wok ?sg ?M ?b ?m =>
      lazymatch type of H with
      | wr _ ?Mh _ _ => let r := zs_hdesc M Mh in lazymatch r with (?l, ?M0) => refine (wok_sstk sg M0 l b m _); eapply (wr_wok _ _ _ _ H); alia end
      | wok _ ?Mh _ _ => let r := zs_hdesc M Mh in lazymatch r with (?l, ?M0) => refine (wok_sstk sg M0 l b m _); exact H end
      end
  end.
Ltac rewok H := first [ rewok_n H | rewok_old H ].

(* [comment removed for export] *)
Ltac recell_n H :=
  lazymatch type of H with
  | cell _ ?Mh _ _ _ =>
      first [ exact H
            | tryif zcell_prefix_to Mh then recell_n H
              else first [ apply cell_Wn_other; [ alia | alia | alia | alia | zapart_n | recell_n H ]
                         | apply cell_Wf_other; [ alia | alia | alia | alia | zapart_n | recell_n H ] ] ]
  end.
Ltac recell H := first [ recell_n H | recell_old H ].
(* [comment removed for export] *)
Ltac zsplit_k k :=
  first [ match goal with
          | |- context [cell _ ?M _ _ _] =>
              lazymatch M with Wn _ _ _ _ => idtac | Wf _ _ _ _ => idtac end;
              let mf := fresh "mfin" in set (mf := M); zsplit_k k; subst mf
          | |- context [getr ?R _] =>
              lazymatch R with regupd _ _ _ => idtac end;
              let rf := fresh "rfin" in set (rf := R); zsplit_k k; subst rf
          end
        | k ].
Ltac zsplit := zsplit_k ltac:(idtac; repeat match goal with |- _ /\ _ => split end).
Ltac zside :=
  first [ lazymatch goal with
          | |- ret_ok _ => unfold ret_ok; bveq
          | |- getr _ _ = _ => gres; rwH; zval
          | |- @eq word _ _ => gres; rwH; zval
          | |- cell _ _ _ _ _ => zcell
          | |- wr _ _ _ _ => zwr
          | |- wok _ _ _ _ => zwok
          | |- apart _ _ _ _ => zapart
          | |- _ => lia
          end
        | eassumption ].
Ltac zcall_k LEM := eapply msteps_trans; [ eapply LEM; try zside | ]; rnorm; norm_pc.
Tactic Notation "zcall" uconstr(LEM) := zcall_k LEM.
Lemma art_msteps_of_eq {fx : PropExec.FPState} : forall segs (a b : machine_state), a = b -> msteps segs a b.
Proof. intros segs a b ->. apply mst_refl. Qed.
Lemma art_mkst_eq {fx : PropExec.FPState} : forall r r' (p p' : word) (m m' rom : word -> option byte),
  r = r' -> p = p' -> m = m' -> mkst r p m rom = mkst r' p' m' rom.
Proof. intros; subst; reflexivity. Qed.
(* [comment removed for export] *)
Ltac zlia := first [ lia | reflexivity | rewrite ?art_u_lit by lia; lia | imm_norm; lia ].
Ltac zregs_eq :=
  lazymatch goal with
  | |- ?a = ?b => first [ constr_eq a b; reflexivity
                        | apply regupd_eq3; [ zregs_eq | zval ] ]
  end.
Ltac zmem_eq :=
  lazymatch goal with
  | |- ?a = ?b => first [ constr_eq a b; reflexivity
                        | apply Wn_eq; [ zmem_eq | zlia | zlia ]
                        | apply Wf_eq; [ zmem_eq | zlia | zlia | zlia ] ]
  end.
(* [comment removed for export] *)
Ltac zret :=
  rnorm; apply art_msteps_of_eq; apply art_mkst_eq; [ zregs_eq | zval | zmem_eq ].

(* [comment removed for export] *)
Ltac zm_dirty M :=
  first [ lazymatch M with context [@bv_signed _ _] => idtac end
        | lazymatch M with context [Z.ltb _ _] => idtac end
        | lazymatch M with context [Z.eqb _ _] => idtac end
        | lazymatch M with context [Z.leb _ _] => idtac end
        | lazymatch M with context [regupd _ _ _] => idtac end
        | match M with
          | context [@bv_unsigned _ ?w] =>
              lazymatch w with
              | getr ?rg ?i => tryif is_var rg
                               then lazymatch goal with | _ : getr rg i = _ |- _ => idtac | _ => fail end
                               else idtac
              | Z_to_bv 64 _ => fail
              | _ => tryif is_var w then fail else idtac
              end
          end ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac zpc_inert p :=
  lazymatch p with
  | @BV _ _ _ => idtac
  | Z_to_bv 64 ?z => first [ is_var z | is_Z_lit z ]
  | _ => is_var p
  end.
Ltac zmx_core plain hidden :=
  lazymatch goal with
  | |- msteps _ (mkst _ _ ?M _) ?B =>
      let withM := (tryif first [ is_var M | zm_dirty M ] then plain else (let mx := fresh "mx" in set (mx := M); hidden mx; subst mx)) in
      lazymatch B with
      | mkst ?r ?tpc ?m _ => tryif (is_evar r; is_evar m; zpc_inert tpc)
                             then (let bx := fresh "bx" in set (bx := B); withM; subst bx)
                             else withM
      | _ => withM
      end
  | |- _ => plain
  end.
(* [comment removed for export] *)
Ltac zmx2 plain hidden := first [ zmx_core plain hidden | plain ].

Ltac zbft_b F D := stepb_ft F D ltac:(zcond).
Ltac zbft F D ::= zmx2 ltac:(idtac; zbft_b F D) ltac:(fun mx => zbft_b F D).
Ltac zbtk_b F D := stepb_tk F D ltac:(zcond).
Ltac zbtk F D ::= zmx2 ltac:(idtac; zbtk_b F D) ltac:(fun mx => zbtk_b F D).
Ltac zld_b F D a HYP :=
  chain_step; [reflexivity | eapply step_ld; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply bytes_le_to_Z_8 ] | step_simpl; vnorm].
Ltac zld F D a HYP ::= zmx2 ltac:(idtac; zld_b F D a HYP) ltac:(fun mx => zld_b F D a HYP).
Ltac zlw_b F D a HYP :=
  chain_step; [reflexivity | eapply step_lw; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes4; lia ] | step_simpl; vnorm];
  rewrite ?art_v_lw_small by lia.
Ltac zlw F D a HYP ::= zmx2 ltac:(idtac; zlw_b F D a HYP) ltac:(fun mx => zlw_b F D a HYP).
Ltac zlwu_b F D a HYP :=
  chain_step; [reflexivity | eapply step_lwu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes4; lia ] | step_simpl; vnorm].
Ltac zlwu F D a HYP ::= zmx2 ltac:(idtac; zlwu_b F D a HYP) ltac:(fun mx => zlwu_b F D a HYP).
Ltac zst_b LEM n F D a v oktac :=
  chain_step; [reflexivity | eapply (LEM _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a : word) (Z_to_bv 64 v : word));
    [exact F | reflexivity | exact D
    | gres; rwH; imm_norm; rewrite ?art_zb_addi, ?art_zb_add; first [reflexivity | f_equal; lia | apply art_zb_eq; f_equal; lia]
    | gres; rwH; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]
    | oktac ]
  | step_simpl];
  change (wbytes ?M0 (Z_to_bv 64 a) (word_to_le_bytes n (Z_to_bv 64 v))) with (Wn n M0 a v).
Ltac zst_h LEM n F D a v oktac mx :=
  chain_step; [reflexivity | eapply (LEM _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a : word) (Z_to_bv 64 v : word));
    [exact F | reflexivity | exact D
    | gres; rwH; imm_norm; rewrite ?art_zb_addi, ?art_zb_add; first [reflexivity | f_equal; lia | apply art_zb_eq; f_equal; lia]
    | gres; rwH; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]
    | subst mx; oktac ]
  | step_simpl];
  change (wbytes ?M0 (Z_to_bv 64 a) (word_to_le_bytes n (Z_to_bv 64 v))) with (Wn n M0 a v).
Ltac zst LEM n F D a v oktac ::= zmx2 ltac:(idtac; zst_b LEM n F D a v oktac) ltac:(fun mx => zst_h LEM n F D a v oktac mx).
Ltac zsb_b F D a v oktac :=
  chain_step; [reflexivity | eapply (step_sb_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a : word) (Z_to_bv 64 v : word) (Z_to_bv 8 v));
    [exact F | reflexivity | exact D
    | gres; rwH; imm_norm; rewrite ?art_zb_addi, ?art_zb_add; first [reflexivity | f_equal; lia | apply art_zb_eq; f_equal; lia]
    | gres; rwH; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]
    | rewrite art_u_lit; [reflexivity | first [lia | assumption | auto with zarith]]
    | oktac ]
  | step_simpl];
  lazymatch goal with |- context [wbytes ?M0 (Z_to_bv 64 a) [Z_to_bv 8 v]] =>
    replace (wbytes M0 (Z_to_bv 64 a) [Z_to_bv 8 v]) with (Wn 1 M0 a v) by (unfold Wn; rewrite (art_bytes1 v) by (first [lia | assumption | auto with zarith]); reflexivity) end.
Ltac zsb_h F D a v oktac mx :=
  chain_step; [reflexivity | eapply (step_sb_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a : word) (Z_to_bv 64 v : word) (Z_to_bv 8 v));
    [exact F | reflexivity | exact D
    | gres; rwH; imm_norm; rewrite ?art_zb_addi, ?art_zb_add; first [reflexivity | f_equal; lia | apply art_zb_eq; f_equal; lia]
    | gres; rwH; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | f_equal; lia]
    | rewrite art_u_lit; [reflexivity | first [lia | assumption | auto with zarith]]
    | subst mx; oktac ]
  | step_simpl];
  lazymatch goal with |- context [wbytes ?M0 (Z_to_bv 64 a) [Z_to_bv 8 v]] =>
    replace (wbytes M0 (Z_to_bv 64 a) [Z_to_bv 8 v]) with (Wn 1 M0 a v) by (unfold Wn; rewrite (art_bytes1 v) by (first [lia | assumption | auto with zarith]); reflexivity) end.
Ltac zsb F D a v oktac ::= zmx2 ltac:(idtac; zsb_b F D a v oktac) ltac:(fun mx => zsb_h F D a v oktac mx).
Ltac zamoadd_d_b F D a old v CELL oktac :=
  chain_step; [reflexivity
  | eapply (art_step_amoadd_d_x0 _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a : word) (Z_to_bv 64 v : word) (Z_to_bv 64 old : word));
    [ exact F | reflexivity | exact D
    | gres; rwH; rewrite ?art_zb_addi, ?art_zb_add; first [reflexivity | f_equal; lia | apply art_zb_eq; f_equal; lia]
    | rewrite art_u_lit by lia; lia
    | exact CELL | apply bytes_le_to_Z_8
    | gres; rwH; first [reflexivity | f_equal; lia]
    | oktac ]
  | step_simpl ];
  rewrite ?art_zb_add;
  change (wbytes ?M0 (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 (old + v)))) with (Wn 8 M0 a (old + v)).
Ltac zamoadd_d_h F D a old v CELL oktac mx :=
  chain_step; [reflexivity
  | eapply (art_step_amoadd_d_x0 _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 a : word) (Z_to_bv 64 v : word) (Z_to_bv 64 old : word));
    [ exact F | reflexivity | exact D
    | gres; rwH; rewrite ?art_zb_addi, ?art_zb_add; first [reflexivity | f_equal; lia | apply art_zb_eq; f_equal; lia]
    | rewrite art_u_lit by lia; lia
    | subst mx; exact CELL | apply bytes_le_to_Z_8
    | gres; rwH; first [reflexivity | f_equal; lia]
    | subst mx; oktac ]
  | step_simpl ];
  rewrite ?art_zb_add;
  change (wbytes ?M0 (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 (old + v)))) with (Wn 8 M0 a (old + v)).
Ltac zamoadd_d F D a old v CELL oktac ::= zmx2 ltac:(idtac; zamoadd_d_b F D a old v CELL oktac) ltac:(fun mx => zamoadd_d_h F D a old v CELL oktac mx).
Ltac zstep_b F D := stepn F D; rwH; vals_lit; zbn.
Ltac zstep F D ::= zmx2 ltac:(idtac; zstep_b F D) ltac:(fun mx => zstep_b F D).
Ltac zlh_b F D a HYP :=
  chain_step; [reflexivity | eapply step_lh; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm];
  rewrite ?art_v_lh_small by lia.
Ltac zlh F D a HYP ::= zmx2 ltac:(idtac; zlh_b F D a HYP) ltac:(fun mx => zlh_b F D a HYP).
Ltac zlbu_b F D a HYP :=
  chain_step; [reflexivity | eapply step_lbu; [exact F | reflexivity | exact D | zaddr a; first [eapply cell_rdn1; [ | exact HYP]; lia | exact HYP] ] | step_simpl; vnorm];
  try (rewrite art_u8_lit by lia).
Ltac zlbu F D a HYP ::= zmx2 ltac:(idtac; zlbu_b F D a HYP) ltac:(fun mx => zlbu_b F D a HYP).
Ltac zlb_b F D a HYP :=
  chain_step; [reflexivity | eapply step_lb; [exact F | reflexivity | exact D | zaddr a; first [eapply cell_rdn1; [ | exact HYP]; lia | exact HYP] ] | step_simpl; vnorm];
  try (rewrite art_v_lb_small by lia).
Ltac zlb F D a HYP ::= zmx2 ltac:(idtac; zlb_b F D a HYP) ltac:(fun mx => zlb_b F D a HYP).
(* [comment removed for export] *)
Ltac stepn F D := zmx2 ltac:(idtac; WalkTac.stepn F D) ltac:(fun mx => WalkTac.stepn F D).
Ltac stepfence F D := zmx2 ltac:(idtac; As0StepLib.stepfence F D) ltac:(fun mx => As0StepLib.stepfence F D).
Ltac zcall_k LEM ::=
  lazymatch goal with
  | |- msteps _ _ ?B =>
      lazymatch B with
      | mkst ?r ?tpc ?m _ =>
          tryif (is_evar r; is_evar m; zpc_inert tpc)
          then (let bx := fresh "bx" in set (bx := B); eapply msteps_trans; [ eapply LEM; try zside | ]; rnorm; norm_pc; subst bx)
          else (eapply msteps_trans; [ eapply LEM; try zside | ]; rnorm; norm_pc)
      | _ => eapply msteps_trans; [ eapply LEM; try zside | ]; rnorm; norm_pc
      end
  | |- _ => eapply msteps_trans; [ eapply LEM; try zside | ]; rnorm; norm_pc
  end.

End ArtTac.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003.
Module ArtFxTac.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0034. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StepTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.WalkTac OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.As0StepLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtMem OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0034.ArtRegs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtAtomics OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtAtomics2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0081.ArtTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- msteps _ (mkstr ?R ?P ?MM _ ?RS) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM; idtac "RESV" RS | |- ?G => idtac "GOAL" G end; fail "SHOWST".
(* [comment removed for export] *)
Ltac zclosed V := lazymatch goal with
  | |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ => replace x with (Z_to_bv 64 V : word) by (apply bv_eq; vm_compute; reflexivity)
  | |- msteps _ (mkstr (regupd _ _ ?x) _ _ _ _) _ => replace x with (Z_to_bv 64 V : word) by (apply bv_eq; vm_compute; reflexivity) end.
(* [comment removed for export] *)
Ltac zwok' := idtac; lazymatch goal with |- store_ok ?sg ?mm (Z_to_bv 64 ?aa) ?nn = true => change (wok sg mm aa nn); zwok | |- wok _ _ _ _ => zwok end.
Ltac wpc0 := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.
(* [comment removed for export] *)
Ltac zcas6 Flr Dlr Fad Dad Fx1 Dx1 Fan Dan Fx2 Dx2 Fsc Dsc A OLD T1 T2 NEW CELL WOK :=
  chain_step; [reflexivity
    | eapply (art_step_lr_w _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 A) _ (Z_to_bv 64 OLD));
      [exact Flr | reflexivity | exact Dlr | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; reflexivity
      | exact CELL | apply art_bytes4; lia ]
    | ]; wpc0; rewrite art_v_lw_small by lia;
  chain_step; [reflexivity | eapply art_step_addi_r; [exact Fad | reflexivity | exact Dad | reflexivity] | ]; wpc0; gres; rwH; zclosed (NEW - OLD);
  chain_step; [reflexivity | eapply art_step_xor_r; [exact Fx1 | reflexivity | exact Dx1 | reflexivity] | ]; wpc0; gres; zclosed T1;
  chain_step; [reflexivity | eapply art_step_and_r; [exact Fan | reflexivity | exact Dan | reflexivity] | ]; wpc0; gres; rwH; zclosed T2;
  chain_step; [reflexivity | eapply art_step_xor_r; [exact Fx2 | reflexivity | exact Dx2 | reflexivity] | ]; wpc0; gres; zclosed NEW;
  chain_step; [reflexivity
    | eapply (art_step_sc_w_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 A));
      [exact Fsc | reflexivity | exact Dsc | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; reflexivity | gres; reflexivity
      | exact WOK ]
    | ]; wpc0;
  change (wbytes ?M0 (Z_to_bv 64 A) (word_to_le_bytes 4 (Z_to_bv 64 NEW))) with (Wn 4 M0 A NEW).
Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.


End ArtFxTac.
