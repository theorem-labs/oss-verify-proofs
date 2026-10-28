(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 BzInv. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzContracts DecCut.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem BzCMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecCutF DecTacF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecCutF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTacF.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.

Section ACeilS1. Context {ACEIL__ : ACeil}.
(* [comment removed for export] *)
Definition kq (K k : dres) : Prop := K = k.
Lemma kq_enter : forall segs (Q : dres -> machine_state -> Prop) k st,
  (forall K, kq K k -> evt segs (Q K) st) -> evt segs (Q k) st.
Proof. intros segs Q k st H. apply (H k). reflexivity. Qed.

(* [comment removed for export] *)
Lemma gbst_absorb : forall d l1 b1 c1 x l2 b2 c2,
  gbst (d_set_bsLive (gbst d l1 b1 c1) x) l2 b2 c2 = gbst d l2 b2 c2.
Proof. intros []; reflexivity. Qed.

(* [comment removed for export] *)
Lemma lor_shiftl8 : forall a b, (0 <= a)%Z -> (0 <= b < 256)%Z -> Z.lor (Z.shiftl a 8) b = (a * 256 + b)%Z.
Proof.
  Local Open Scope Z_scope.
  intros a b Ha Hb. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- Z.lxor_lor.
  - rewrite <- Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n 8).
    + replace (a * 256) with (a * 2 ^ 8) by reflexivity. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + rewrite (Z.bits_above_log2 b n); [apply Bool.andb_false_r| lia|].
      destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply (Z.lt_le_trans _ 8); [apply Z.log2_lt_pow2; lia| lia].
  - apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_le_dec n 8).
    + replace (a * 256) with (a * 2 ^ 8) by reflexivity. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    + rewrite (Z.bits_above_log2 b n); [apply Bool.andb_false_r| lia|].
      destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply (Z.lt_le_trans _ 8); [apply Z.log2_lt_pow2; lia| lia].
Qed.


(* [comment removed for export] *)
Lemma orw_mod32_land : forall bb u, (0 <= bb < 2^32)%Z -> (0 <= u < 256)%Z ->
  ((Z.lor (Z.land (bv_unsigned (sx32 (Z_to_bv 64 bb)) * 256) 18446744073709551615) u) mod 4294967296
   = u32 (Z.lor (Z.shiftl bb 8) u))%Z.
Proof.
  intros bb u Hbb Hu. unfold u32.
  change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  change 4294967296%Z with (2^32)%Z. change (2^64)%Z with (2^32 * 2^32)%Z.
  rewrite !lor_mod_pow2 by lia. f_equal.
  rewrite Zaux.Zmod_mod_mult by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2^8)%Z with 256%Z.
  rewrite <- (sx32_mod32 bb Hbb) at 2. change 4294967296%Z with (2^32)%Z.
  rewrite Z.mul_mod_idemp_l by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma orw_mod32 : forall bb u, (0 <= bb < 2^32)%Z -> (0 <= u < 256)%Z ->
  ((Z.lor ((bv_unsigned (sx32 (Z_to_bv 64 bb)) * 256) mod 18446744073709551616) u) mod 4294967296
   = u32 (Z.lor (Z.shiftl bb 8) u))%Z.
Proof.
  intros bb u Hbb Hu. rewrite <- (orw_mod32_land bb u Hbb Hu).
  change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity.
Qed.
End ACeilS1.

(* [comment removed for export] *)
Ltac gbvalue r WB RL n bb bl :=
  let v := reg_val r in
  lazymatch v with
  | Z_to_bv 64 (Z.land ?e ?m / ?p)%Z =>
      replace (Z.land e m / p)%Z with (gbval bb bl n) by
        (symmetry; change p with (2^(64 - n))%Z; apply (gbval_of_slli_srli _ _ _ _ _ WB RL); lia)
  | Z_to_bv 64 (Z.land ?e ?m) =>
      first [ replace (Z.land e m) with (gbval bb bl n) by (symmetry; change m with (2^n - 1)%Z; apply (gbval_of_srlw64 _ _ _ _ _ WB RL); lia)
            | replace (Z.land e m) with (gbval bb bl n) by (symmetry; change m with (2^n - 1)%Z; apply (gbval_of_srlw _ _ _ _ _ WB RL); lia) ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac hyp_chk H := let H' := fresh "CK_" in pose proof H as H'; clear H; rename H' into H.
Ltac kq_norm :=
  try match goal with H : kq _ _ |- _ =>
    cbv zeta in H; hyp_chk H;
    match goal with H2 : kq _ _ |- _ =>
      dmodel_cbn_in H2; cbn [s_in s_out s_avail_out s_tin s_tout s_set_in s_set_out s_set_avail_out s_set_tin s_set_tout] in H2 end end.
Ltac kq_fold := kq_norm; try match goal with H : kq ?K _ |- _ => unfold kq in H; subst K end.
Ltac kq_intro :=
  lazymatch goal with |- evt ?sg (?Q ?k) ?st =>
    first [ is_var k
          | apply (kq_enter sg Q k st); let K := fresh "K" in let KQ := fresh "KQ" in intros K KQ ] end.

(* [comment removed for export] *)
Ltac dimg_normF := cbn [di_segs di_got di_stderrp di_crc di_rnums di_dec] in *.

(* [comment removed for export] *)
Tactic Notation "gbF_call" uconstr(L) constr(MUL) constr(WML) constr(AOK) constr(DP) constr(FU) :=
  revive_all MUL WML AOK; kq_fold;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
    enter_cutF L DP; [ dmodel_cbn; unset_Z; lia | try fuelF .. ]; [ .. | first [clear dependent m | idtac] ]
  end.

(* [comment removed for export] *)
Ltac hide_all_but_atF keep :=
  repeat match goal with
  | H : rw_cells _ _ ?A _ |- _ => lazymatch keep with context [@cons Z A _] => fail | _ => hide H end
  | H : u32arr _ _ ?A _ |- _ => lazymatch keep with context [@cons Z A _] => fail | _ => hide H end
  | H : u8arr _ _ ?A _ |- _ => lazymatch keep with context [@cons Z A _] => fail | _ => hide H end
  | H : bytes_at _ _ ?A _ |- _ => lazymatch keep with context [@cons Z A _] => fail | _ => hide H end
  | H : drest_at _ _ _ _ |- _ => hide H
  | H : blk_at _ _ _ _ |- _ => hide H
  end.

(* [comment removed for export] *)
Ltac chunks_normF :=
  repeat match goal with
  | H : drest_at _ _ _ (r_of _) |- _ => unfold r_of in H
  | H : blk_at _ _ _ (blk_of _ _) |- _ => unfold blk_of in H
  end;
  repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => progress (dmodel_cbn_in H); hyp_chk H
  | H : u32arr _ _ _ _ |- _ => progress (dmodel_cbn_in H); hyp_chk H
  | H : u8arr _ _ _ _ |- _ => progress (dmodel_cbn_in H); hyp_chk H
  | H : drest_at _ _ _ _ |- _ => progress (dmodel_cbn_in H); hyp_chk H
  | H : blk_at _ _ _ _ |- _ => progress (dmodel_cbn_in H); hyp_chk H
  end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac chunks_opaqueF :=
  repeat match goal with
  | H : rw_cells _ _ _ ?cs |- _ =>
      match cs with context [C4 (Z_to_bv 64 (u32 ?x))] => let c := fresh "cw" in set (c := u32 x) in H end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac gbF_next_pre :=
  cbv zeta;
  repeat match goal with H : dpureF _ _ _ _ _ _ |- _ => clear H end;
  repeat match goal with H : fuel_ok _ _ _ |- _ => clear H end;
  repeat match goal with H : drun _ _ _ _ _ = _ |- _ => clear H end;
  repeat match goal with H : (bv_unsigned _ mod 4294967296 = _)%Z |- _ => clear H end;
  (* [comment removed for export] *)
  repeat match goal with H : (0 <= _ < 2 ^ 32)%Z |- _ => clear H end;
  repeat match goal with H : (_ <= _ <= 32)%Z |- _ => clear H end.
(* [comment removed for export] *)
Ltac gbF_next_post keep Wloc MD FU DP CONS DM MU :=
  (* [comment removed for export] *)
  cbn [s_in s_out s_avail_out s_tin s_tout length] in MD, FU, DP, CONS;
  (* [comment removed for export] *)
  rewrite ?gbst_absorb in MD; rewrite ?gbst_absorb in FU; rewrite ?gbst_absorb in DP;
  cbn [d_bsLive gbst d_set_bsLive d_set_bsBuff d_set_state] in CONS;
  (* [comment removed for export] *)
  repeat match goal with H1 : (?a < ?b)%nat, H2 : (?b < ?c)%nat |- _ =>
    let H3 := fresh "LTF" in pose proof (Nat.lt_trans a b c H1 H2) as H3; clear H1 H2 end;
  unfold W14, D14, DSTATE_SIZE in MU; cbn [app blk_ivls b_s b_strm] in MU;
  open_dmemF DM; dimg_normF; chunks_normF; chunks_opaqueF;
  hide_all_but_atF keep;
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (munch_refl Wloc mm) as MUL; pose proof (wmono_refl segs mm) as WML
  end;
  (* [comment removed for export] *)
  kq_intro;
  match goal with KQ : kq _ (drun _ _ _ _ _) |- _ => rewrite MD in KQ; clear MD end.

Ltac gbF_next keep Wloc :=
  gbF_next_pre;
  let F1 := fresh "F" in let bb := fresh "bb" in let bl := fresh "bl" in let inp := fresh "inp" in let tin := fresh "tin" in
  let til := fresh "til" in let tih := fresh "tih" in let m := fresh "m" in let wb := fresh "wb" in
  let MD := fresh "MD" in let FU := fresh "FU" in let LTF := fresh "LTF" in
  let DM := fresh "DM" in let FR := fresh "FR" in let ST := fresh "ST" in let MU := fresh "MU" in
  let WM := fresh "WM" in let MI := fresh "MI" in let DP := fresh "DP" in
  let RB := fresh "RB" in let RL := fresh "RL" in let WB := fresh "WB" in let CONS := fresh "CONS" in
  intros F1 bb bl inp tin til tih m wb MD FU LTF DM FR ST MU WM MI DP RB RL WB CONS; intros;
  gbF_next_post keep Wloc MD FU DP CONS DM MU.


(* [comment removed for export] *)
Ltac dpureF_solve DP ::=
  eapply (dpureF_frame _ _ _ _ _ _ _ _ _ DP); dmodel_cbn;
  [ (* [comment removed for export] *) first [ exact (dpureF_jwf _ _ _ _ _ _ DP)
                      | pose proof (dpureF_jwf _ _ _ _ _ _ DP) as X__; unfold jk_wf in *;
                        cbn [jk_set_t jk_set_s j_p1 j_p2 j_p3 j_s1 j_s2 j_q1 j_q2] in *; decompose [and] X__; clear X__;
                        repeat split; try assumption;
                        cbn [cells_bytes cbytes app]; rewrite ?length_app, ?length_le4, ?length_le8; first [reflexivity | ulia] ]
  | (* [comment removed for export] *) first [ exact (dpureF_static _ _ _ _ _ _ DP)
                          | pose proof (dpureF_static _ _ _ _ _ _ DP) as X__; unfold jk_static in *;
                            cbn [jk_set_t jk_set_s j_q1 j_q2 j_tol j_toh j_bzalloc j_bzfree j_opaque] in *; exact X__ ]
  | first [reflexivity | ulia] | first [reflexivity | ulia] | first [reflexivity | ulia]
  | first [reflexivity | ulia]
  | (* [comment removed for export] *) first [ exact (dpureF_in _ _ _ _ _ _ DP) | assumption | eapply (in_rel_tail _ _ _ _ _ (dpureF_in _ _ _ _ _ _ DP)); reflexivity | idtac ]
  | (* [comment removed for export] *) first [ cbn [length s_in]; ulia | idtac ]
  | (* [comment removed for export] *) first [ ulia | apply u32_range | apply u32_range' | let X := fresh "X_" in pose proof (dpureF_bb _ _ _ _ _ _ DP) as X; dmodel_cbn_in X; ulia | idtac ]
  | (* [comment removed for export] *) first [ ulia | let X := fresh "X_" in pose proof (dpureF_bl _ _ _ _ _ _ DP) as X; dmodel_cbn_in X; ulia | idtac ]
  | (* [comment removed for export] *) first [ ulia | let X := fresh "X_" in pose proof (dpureF_cbn _ _ _ _ _ _ DP) as X; dmodel_cbn_in X; ulia | idtac ]
  | (* [comment removed for export] *)
    first [ let X := fresh "CR_" in pose proof (dpureF_cbn _ _ _ _ _ _ DP) as X; dmodel_cbn_in X; cbn [length s_in] in *; ulia | idtac ]
  | (* [comment removed for export] *) first [ ulia | exact (dpureF_snb _ _ _ _ _ _ DP) | let X := fresh "X_" in pose proof (dpureF_snb _ _ _ _ _ _ DP) as X; dmodel_cbn_in X; ulia | idtac ]
  | (* [comment removed for export] *) first [ ulia | exact (dpureF_nbu _ _ _ _ _ _ DP) | let X := fresh "X_" in pose proof (dpureF_nbu _ _ _ _ _ _ DP) as X; dmodel_cbn_in X; ulia | idtac ]
  | (* [comment removed for export] *)
    first [ let X := fresh "RP_" in pose proof (dpureF_rep _ _ _ _ _ _ DP) as X;
            unfold drep in X |- *; dmodel_cbn_in X; hyp_chk X; dmodel_cbn;
            first [ exact X
                  | (* [comment removed for export] *)
                    decompose [and] X; repeat match goal with |- _ /\ _ => split end; try assumption;
                    first [ apply u32_range | apply u32_range' | ulia ] ]
          | idtac ] ].

(* [comment removed for export] *)
Ltac ret_nb := dmodel_cbn; unset_Z; lia.
Ltac ret_post := apply dpost14_ne; dmodel_cbn; cbv; discriminate.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac goal_fuel :=
  lazymatch goal with |- evt _ (_ ?k) _ =>
    lazymatch k with
    | drun ?F1 _ _ _ _ => F1
    | dgo ?F1 _ => F1
    | ?h ?F1 _ _ _ _ _ _ _ _ => F1
    | ?h ?F1 _ _ _ _ _ _ _ => F1
    | ?h ?F1 _ _ _ _ _ _ => F1
    | ?h ?F1 _ _ _ _ _ => F1
    | ?h ?F1 _ _ _ _ => F1
    | ?h ?F1 _ _ _ => F1
    end
  end.
(* [comment removed for export] *)
Tactic Notation "enter_nextF" constr(H) constr(DP) :=
  kq_fold; let F1 := goal_fuel in enter_cutF (H F1 ltac:(lia) _ _ _ JK_) DP.
(* [comment removed for export] *)
Tactic Notation "enter_sameF" constr(H) constr(DP) := kq_fold; enter_cutF (H _ _ _ JK_) DP.
(* [comment removed for export] *)
Tactic Notation "enter_retF" constr(R) constr(DP) :=
  kq_fold; first [ enter_cutF (R _ _ _ JK_) DP | enter_cutF (R _ _ _ _ JK_) DP ]; [ ret_nb | ret_post ].

(* [comment removed for export] *)
Ltac gbv r n v :=
  match goal with
  | WB : (bv_unsigned ?w mod 4294967296 = ?bb)%Z, RL : (_ <= ?bl <= 32)%Z |- _ =>
      gbvalue r WB RL n bb bl;
      let R := fresh "R" v in
      pose proof (gbval_range bb bl n ltac:(lia)) as R;
      let p := eval cbv in (2 ^ n)%Z in change (2 ^ n)%Z with p in R;
      set (v := gbval bb bl n) in *
  end.



(* [comment removed for export] *)
Ltac zb8_store_done ARR i :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?mm ?ga (le1 ?x)) _) =>
      lazymatch type of ARR with u8arr _ _ ?A (zb8 ?a ?n) =>
        let H := fresh "ARR" in
        pose proof (zb8_write1 segs mm A a n i x ARR ltac:(lia)) as H;
        let ga' := lazymatch ga with wa _ => ga | Z_to_bv 64 ?X => constr:(wa X) | _ => ga end in
        replace (wa (A + i)%Z) with ga' in H by (cbv delta [wa]; first [reflexivity | f_equal; lia | apply f_equal; lia]);
        clear ARR; store_done; rename H into ARR
      end
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?mm ?ga [Z_to_bv 8 ?z]) _) =>
      lazymatch type of ARR with u8arr _ _ ?A (zb8 ?a ?n) =>
        let H := fresh "ARR" in
        pose proof (zb8_write1_lit segs mm A a n i z ARR ltac:(lia)) as H;
        let ga' := lazymatch ga with wa _ => ga | Z_to_bv 64 ?X => constr:(wa X) | _ => ga end in
        replace (wa (A + i)%Z) with ga' in H by (cbv delta [wa]; first [reflexivity | f_equal; lia | apply f_equal; lia]);
        clear ARR; store_done; rename H into ARR
      end
  end.
(* [comment removed for export] *)
Ltac zb8_sb ARR i :=
  lazymatch goal with |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of ARR with u8arr _ _ ?A (zb8 ?a ?n) =>
    let SO := fresh "SO" in
    pose proof (u8arr_store_ok sg mm A (zb8 a n) i _ ARR ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO;
    step; zb8_store_done ARR i; try clear SO; unfold wr8 in ARR; zsimp_in ARR; try rewrite Z.mod_small in ARR by lia; zsimp; bz32l
  end end.




(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac crc_cellA H k :=
  cell_mod32 H k; change (2^32)%Z with 4294967296%Z in H;
  lazymatch type of H with
  | context [ ((Z.lor (Z.land (bv_unsigned (sx32 (Z_to_bv 64 ?bb)) * 256) 18446744073709551615) ?u) mod 4294967296)%Z ] =>
      rewrite (orw_mod32_land bb u) in H by first [lia | apply u32_range' | solve [unset_Z; first [lia | apply u32_range' | apply u32_range]] | mlia | unfold u32; mlia]
  | context [ ((Z.lor ((bv_unsigned (sx32 (Z_to_bv 64 ?bb)) * 256) mod 18446744073709551616) ?u) mod 4294967296)%Z ] =>
      rewrite (orw_mod32 bb u) in H by first [lia | apply u32_range' | solve [unset_Z; first [lia | apply u32_range' | apply u32_range]] | mlia | unfold u32; mlia]
  | _ => idtac
  end.
