(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib ArtMem ArtAtomics ArtRegs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Ltac recell H := first [ exact H | apply cell_Wn_other; [ lia | lia | lia | lia | zapart | recell H ] | apply cell_Wf_other; [ lia | lia | lia | lia | zapart | recell H ] ].
Ltac rewok H := first [ exact H | eapply (wr_wok _ _ _ _ H); lia | apply wok_Wn; rewok H ].
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
Ltac zcell :=
  lazymatch goal with
  | |- cell _ ?M ?a ?n ?v =>
      first [ match goal with H : cell _ M a n _ |- _ => exact H end
            | match goal with H : cell _ M ?a' n v |- _ => replace a with a' by lia; exact H end
            | lazymatch M with
              | Wn _ _ _ _ => first [ apply cell_Wn_hit; lia | apply cell_Wn_other; [lia|lia|lia|lia| zapart | zcell] ]
              | Wf _ _ _ _ => apply cell_Wf_other; [lia|lia|lia|lia| zapart | zcell]
              end ]
  end.
Ltac zwr :=
  lazymatch goal with
  | |- wr _ ?M ?b ?m =>
      first [ match goal with H : wr _ M b m |- _ => exact H end
            | match goal with H : wr _ M ?b' ?m' |- _ => apply (wr_sub _ _ _ _ _ _ H); lia end
            | lazymatch M with
              | Wn _ _ _ _ => apply wr_Wn; zwr
              | Wf _ _ _ _ => apply wr_Wf; zwr
              end ]
  end.
Ltac zwok :=
  lazymatch goal with
  | |- wok _ ?M ?b ?m =>
      first [ match goal with H : wok _ M b m |- _ => exact H end
            | match goal with H : wr _ M ?b' ?m' |- _ => apply (wr_wok _ _ _ _ H); lia end
            | lazymatch M with
              | Wn _ _ _ _ => apply wok_Wn; zwok
              | Wf _ _ _ _ => apply wok_Wf; zwok
              end ]
  end.
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
Tactic Notation "zcall" uconstr(LEM) := eapply msteps_trans; [ eapply LEM; try zside | ]; rnorm; norm_pc.
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
