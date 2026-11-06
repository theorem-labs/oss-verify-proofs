(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes FP ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Export Od_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Notation usegs := Image.usegs.

Definition OD_ENTRY : Z := 0x270d4.
Definition OD_FRAME : Z := 496.
Definition OD_ITER : Z := 0x2745c.
Definition OD_HEAD : Z := 0x277f4.
Definition OD_DISP : Z := 0x27860.
Definition OD_PLUS : Z := 0x2877c.
Definition OD_EXIT : Z := 0x29310.
Definition OD_TRAP : Z := 0x29320.
Definition OD_GTOP : Z := 0xb6000.
Definition OD_NEED : Z := 2656.
Definition OD_DPI_VPTR : Z := 0x7f750.
Definition OD_PSTR : Z := 0x43ba4.
Definition OD_FROMCH : Z := 0x2a094.
Definition OD_OPIDX : Z := 0x29e68.
Definition OD_GOT_TABS : Z := 0x82a18.
Definition OD_JTAB : Z := 0x13100.

Notation od_ok := (od_ok_g OD_FRAME OD_NEED OD_GTOP OD_DPI_VPTR).

Record od_oku (E : odenv) : Prop := mkOdOkU {
  oku_sp : (bv_unsigned (o_sp E) mod 16 = 0)%Z;
  oku_buf : (0 < o_BUF E)%Z;
  oku_copy : (0 < o_COPY E < 2^64)%Z;
  oku_sb : (0 < o_SB E)%Z;
  oku_idx : (4 < o_IDX E /\ o_IDX E mod 4 = 0)%Z;
  oku_impl : (0 < o_IMPL E /\ o_IMPL E mod 8 = 0)%Z
}.

Notation FR E := (bv_unsigned (o_sp E) + -496)%Z.
Notation FR_IT E := (bv_unsigned (o_sp E) + -272)%Z.
Notation FR_PA E := (bv_unsigned (o_sp E) + -208)%Z.
Notation tokI_read := (tokI_read_g usegs).
Notation tokB_read := (tokB_read_g usegs).

Definition K104 : Z := 0xffff0000ffff.
Definition K112 : Z := 0x271000000001.
Definition M1 : Z := 18446744073709551615.
Definition fr_k0 : list cell := [C8 (wz 0x3526a); C8 (wz 0xff00ff); C8 (wz 10000)].
Definition fr_k56 : list cell := [C8 (wz K104); C8 (wz K112); C8 (wz 0xa01); C8 (wz 100000000)].

Definition fr_k96 (v144 : Z) : list cell :=
  [C8 (wz 0x640001); C8 (wz 0xffffffff80808080); C8 (wz 0xffffffffcfcfcfd0); C8 (wz 0x46464646); C8 (wz 0x736c6166); C8 (wz 0);
   C8 (wz v144); C8 (wz 0x65757274); C8 (wz 0x7fffffff)].

Definition fr_k176 (v176 v184 v200 v208 v216 : Z) : list cell :=
  [C8 (wz v176); C8 (wz v184); C8 (wz 0x6c6c756e); C8 (wz v200); C8 (wz v208); C8 (wz v216)].

Definition iter_cells (E : odenv) (st : ost) (j273 j284 : list byte) : list cell :=
  [C8 (wz (o_BUF E)); C8 (wz (o_IDX E + 4 * o_pos st)); C8 (wz (if o_alive st then FR_PA E else 0)); C8 (wz (o_SB E + o_sbo st));
   C4 (wz (o_err st)); C4 (wz (o_depth st)); C8 (wz (o_IDX E)); C1 (Z_to_bv 8 0); CB 7 j273; C4 (wz 0); CB 4 j284].

Definition od_parser_cells (E : odenv) : list cell :=
  [CB 8 (o_j304 E); C8 (wz (o_IMPL E)); C8 (o_w320 E); C8 (o_w328 E); C8 (o_w336 E); C8 (o_w344 E); C8 (wz (o_SB E))].

Definition od_vt_cells (v0 v1 v2 v3 v5 v6 v7 v8 v9 : word) : list cell :=
  [C8 v0; C8 v1; C8 v2; C8 v3; C8 (wz OD_PSTR); C8 v5; C8 v6; C8 v7; C8 v8; C8 v9].

Definition od_W (E : odenv) : list ivl := [ (o_lo E, FR_PA E); (o_SB E, o_SB E + o_CAP E) ]%Z.

Definition ODINVg (E : odenv) (v144 v176 v184 v200 v208 v216 : Z) (st : ost) (m1 : mem) : Prop :=
  rw_cells usegs m1 (FR E) fr_k0 /\
  (exists j24 j32 j40 j48, rw_cells usegs m1 (bv_unsigned (o_sp E) + -472) [CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48]) /\
  rw_cells usegs m1 (bv_unsigned (o_sp E) + -440) fr_k56 /\
  (exists j88, rw_cells usegs m1 (bv_unsigned (o_sp E) + -408) [CB 8 j88]) /\
  rw_cells usegs m1 (bv_unsigned (o_sp E) + -400) (fr_k96 v144) /\
  (exists j168, rw_cells usegs m1 (bv_unsigned (o_sp E) + -328) [CB 8 j168]) /\
  rw_cells usegs m1 (bv_unsigned (o_sp E) + -320) (fr_k176 v176 v184 v200 v208 v216) /\
  (exists j273 j284, rw_cells usegs m1 (FR_IT E) (iter_cells E st j273 j284)) /\
  rw_cells usegs m1 (FR_PA E) (od_parser_cells E) /\
  rw_cells usegs m1 (bv_unsigned (o_sp E) + -152) (o_hi E) /\
  rw_cells usegs m1 (o_IMPL E) (dpi_cells E) /\
  (exists ws, u32arr usegs m1 (o_IDX E) ws /\ idx_ok E ws) /\
  bytes_at usegs m1 (o_BUF E) (padded_bytes (o_bs E)) /\
  wr_at usegs m1 (o_SB E) (o_CAP E) /\
  (exists v0 v1 v2 v3 v5 v6 v7 v8 v9, rw_cells usegs m1 OD_DPI_VPTR (od_vt_cells v0 v1 v2 v3 v5 v6 v7 v8 v9)) /\
  rw_cells usegs m1 OD_GOT_TABS [C8 (wz 0x137e8); C8 (wz 0x147c0); C8 (wz 0x14878); C8 (wz 0x138e8)] /\
  mem_inv usegs m1 /\ munch (od_W E) (o_m0 E) m1 /\ wmono usegs (o_m0 E) m1 /\
  stk usegs m1 (o_lo E) (FR E).

Notation ODINVv E v216 st m1 := (ODINVg E 0 2 1 (o_IDX E) 1 v216 st m1).
Notation ODINV E st m1 := (ODINVg E 0 2 1 (o_IDX E) 1 1 st m1).

Notation ODST E pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m :=
  (MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2
           (Z_to_bv 64 (o_COPY E)) (Z_to_bv 64 10) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (o_act E)) (Z_to_bv 64 (FR_IT E)) xs6 (Z_to_bv 64 (o_IDX E)) (Z_to_bv 64 122)
           (Z_to_bv 64 4) xs10 xs11 xt3 xt4 xt5 xt6)
      xF (Z_to_bv 64 pc) xfc None m (seg_rom usegs)).

Definition od_exit_k (E : odenv) (Q : machine_state -> Prop) : Prop :=
  forall st v144 v176 v184 v200 v208 v216 xra xt0 xt1 xt2 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    frm0 xfc -> ODINVg E v144 v176 v184 v200 v208 v216 st m1 ->
    evt usegs Q (MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2 (Z_to_bv 64 (o_COPY E)) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         xs2 xs3 (Z_to_bv 64 (o_act E)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 OD_EXIT) xfc None m1 (seg_rom usegs)).

Definition od_head_pre (E : odenv) (st0 st : ost) : Prop :=
  od_next_ok (o_bs E) (o_idxs E) 1 st0 st \/ od_dead (o_n E) st.
Definition od_head_k (E : odenv) (Q : machine_state -> Prop) (st0 : ost) : Prop :=
  forall st v216 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    od_head_pre E st0 st -> frm0 xfc -> ODINVv E v216 st m1 ->
    evt usegs Q (ODST E OD_HEAD xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 1) (Z_to_bv 64 1) xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).

Definition od_plus_k (E : odenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall st' xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    od_arm_out (o_bs E) (o_idxs E) st st' -> frm0 xfc -> ODINV E st' m1 ->
    evt usegs Q (ODST E OD_PLUS xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).

Definition arm_stmt (E : odenv) (entry : Z) : Prop :=
  forall (Q : machine_state -> Prop) st xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET ->
    od_head_ok (o_bs E) (o_idxs E) 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    evt usegs Q (ODST E entry xra xt0 xt1 xt2 (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xs11 xt3 xt4 xt5 xt6 xF xfc m1).

Ltac od_open_inv H :=
  let j24 := fresh "j24" in let j32 := fresh "j32" in let j40 := fresh "j40" in let j48 := fresh "j48" in
  let j88 := fresh "j88" in let j168 := fresh "j168" in let j273 := fresh "j273" in let j284 := fresh "j284" in
  let ws := fresh "ws" in
  let v0 := fresh "v0" in let v1 := fresh "v1" in let v2 := fresh "v2" in let v3 := fresh "v3" in let v5 := fresh "v5" in
  let v6 := fresh "v6" in let v7 := fresh "v7" in let v8 := fresh "v8" in let v9 := fresh "v9" in
  destruct H as (FR0 & (j24 & j32 & j40 & j48 & FR24) & FR56 & (j88 & FR88) & FR96 & (j168 & FR168) & FR176
                 & (j273 & j284 & ITER) & PARS & FRHI & DPI & (ws & IDXA & IDXOK) & BUFRO & SBW
                 & (v0 & v1 & v2 & v3 & v5 & v6 & v7 & v8 & v9 & VT) & GOT & MI & MU & WM & ST);
  unfold fr_k0 in FR0; unfold fr_k56 in FR56; unfold fr_k96 in FR96; unfold fr_k176 in FR176; unfold iter_cells in ITER; unfold dpi_cells in DPI;
  unfold od_parser_cells in PARS;
  unfold od_vt_cells in VT; unfold od_W in MU; unfold OD_DPI_VPTR in VT; unfold OD_GOT_TABS in GOT;
  unfold wz, K104, K112 in FR0, FR56, FR96, FR176, ITER, PARS, DPI, VT, GOT;
  let IDXL := fresh "IDXL" in let IDXF := fresh "IDXF" in destruct IDXOK as [IDXL IDXF];
  lazymatch type of BUFRO with
  | bytes_at _ _ _ (padded_bytes ?bs) => let PBL := fresh "PBL" in pose proof (padded_bytes_blen bs) as PBL
  end.

Lemma rw_cells_eq : forall segs (m : mem) A cs cs', rw_cells segs m A cs -> cs = cs' -> rw_cells segs m A cs'.
Proof. intros segs m A cs cs' H <-. exact H. Qed.
Lemma od_cons_eq : forall {A} (a b : A) l l', a = b -> l = l' -> a :: l = b :: l'.
Proof. intros A a b l l' -> ->. reflexivity. Qed.
Lemma od_C8_eq : forall a b, a = b -> C8 (Z_to_bv 64 a) = C8 (Z_to_bv 64 b).
Proof. intros a b ->. reflexivity. Qed.
Lemma od_C4_eq : forall a b, a = b -> C4 (Z_to_bv 64 a) = C4 (Z_to_bv 64 b).
Proof. intros a b ->. reflexivity. Qed.
Ltac od_cell_eq :=
  first [ reflexivity
        | apply od_C8_eq; lia
        | apply od_C4_eq; lia ].
Ltac od_cells_eq_rec :=
  lazymatch goal with
  | |- cons _ _ = cons _ _ => apply od_cons_eq; [od_cell_eq | od_cells_eq_rec]
  | |- _ => reflexivity
  end.
Ltac od_cells_eq :=
  unfold wz, K104, K112; cbn [o_adv o_setd o_sete o_abandon consume o_pos o_depth o_err o_alive o_sbo];
  repeat match goal with H : o_alive ?s = _ |- context [o_alive ?s] => rewrite H end;
  od_cells_eq_rec.
Ltac od_ass := first [eassumption | (eapply rw_cells_eq; [eassumption | od_cells_eq])].

Ltac od_close_inv :=
  lazymatch goal with
  | |- ODINVg _ _ _ _ _ _ _ _ _ =>
      try match goal with
          | HV : o_vptr ?E = ?v, HD : rw_cells _ _ (o_IMPL ?E) (C8 ?v :: _) |- _ => rewrite <- HV in HD
          end;
      unfold ODINVg, fr_k0, fr_k56, fr_k96, fr_k176, iter_cells, od_parser_cells, dpi_cells, od_vt_cells, od_W, OD_DPI_VPTR, OD_GOT_TABS, idx_ok;
      split; [od_ass|];
      split; [ do 4 eexists; eassumption | ];
      split; [od_ass|];
      split; [ eexists; eassumption | ];
      split; [od_ass|];
      split; [ eexists; eassumption | ];
      split; [od_ass|];
      split; [ do 2 eexists; od_ass | ];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
      split; [ eexists; split; [eassumption| split; eassumption] | ];
      split; [eassumption|]; split; [eassumption|];
      split; [ do 9 eexists; eassumption | ];
      split; [od_ass|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Ltac od_forget_1 H :=
  match type of H with
  | rw_cells ?s ?m ?A (C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: ?c1 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0; c1] v post) in H; cbn [app] in H
  | rw_cells ?s ?m ?A (?c0 :: ?c1 :: ?c2 :: C8 ?v :: ?post) => apply (rw_cells_forget_C8 s m A [c0; c1; c2] v post) in H; cbn [app] in H
  end.
Ltac od_forget H := repeat (od_forget_1 H).

Ltac od_env OK :=
  let BOK := fresh "BOK" in let S1 := fresh "S1" in let LEN := fresh "LEN" in let GLO := fresh "GLO" in let ROOM := fresh "ROOM" in
  let SP63 := fresh "SP63" in let BUFR := fresh "BUFR" in let SBR := fresh "SBR" in let CAPR := fresh "CAPR" in let IMPLR := fresh "IMPLR" in
  let SBI := fresh "SBI" in
  let IDXR := fresh "IDXR" in let ICAP := fresh "ICAP" in let ACT := fresh "ACT" in let VPT := fresh "VPT" in
  let S_SB := fresh "S_SB" in let S_SI := fresh "S_SI" in let S_SM := fresh "S_SM" in
  pose proof OK as [BOK S1 LEN GLO ROOM SP63 BUFR SBR CAPR SBI IMPLR IDXR ICAP ACT VPT S_SB S_SI S_SM];
  unfold S1_LEN_MAX, OD_FRAME, OD_NEED, OD_GTOP, OD_DPI_VPTR in *;
  lazymatch goal with E : odenv |- _ =>
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 (o_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    let NR := fresh "NR" in pose proof (od_n_range E S1) as NR
  end.
Ltac od_envu OKU :=
  let USP := fresh "USP" in let UBUF := fresh "UBUF" in let UCOPY := fresh "UCOPY" in let USB := fresh "USB" in
  let UIDX := fresh "UIDX" in let UIMPL := fresh "UIMPL" in
  pose proof OKU as [USP UBUF UCOPY USB UIDX UIMPL].

Lemma lxor_ones64 : forall x, (0 <= x < 18446744073709551616)%Z -> Z.lxor x 18446744073709551615 = (18446744073709551615 - x)%Z.
Proof. intros x H. apply zb_lxor_ones. lia. Qed.

Ltac ulx := repeat match goal with H : context [Z.lxor _ 18446744073709551615] |- _ => rewrite lxor_ones64 in H by lia end.
Ltac utrap := let G := fresh "UG" in if_cases G; zify_cond G; [exfalso; first [lia | ulx; lia]|]; try clear G.
Ltac uok := let G := fresh "UG" in if_cases G; zify_cond G; [|exfalso; first [lia | ulx; lia]]; try clear G.

Lemma od_land7 : forall x, (x mod 8 = 0)%Z -> Z.land x 7 = 0%Z.
Proof. intros x H. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.
Lemma od_land3 : forall x, (x mod 4 = 0)%Z -> Z.land x 3 = 0%Z.
Proof. intros x H. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. exact H. Qed.
Lemma od_sp_al8 : forall s k, (s mod 16 = 0)%Z -> (k mod 8 = 0)%Z -> ((s + k) mod 8 = 0)%Z.
Proof. intros s k Hs Hk. Z.div_mod_to_equations. lia. Qed.
Lemma od_idx_al4 : forall a k, (a mod 4 = 0)%Z -> ((a + 4 * k) mod 4 = 0)%Z.
Proof. intros a k Ha. Z.div_mod_to_equations. lia. Qed.

Ltac ual :=
  repeat match goal with
  | H : (?x mod 8 = 0)%Z |- context [Z.land ?x 7] => rewrite (od_land7 x H)
  | H : (?x mod 4 = 0)%Z |- context [Z.land ?x 3] => rewrite (od_land3 x H)
  end.

Lemma b2z_pos : forall x, (0 < x)%Z -> Z.b2z (0 <? x) = 1%Z.
Proof. intros x H. rewrite (proj2 (Z.ltb_lt 0 x) H). reflexivity. Qed.
Lemma b2z_lt1 : forall x, (0 < x)%Z -> Z.b2z (x <? 1) = 0%Z.
Proof. intros x H. rewrite (proj2 (Z.ltb_ge x 1)) by lia. reflexivity. Qed.
Ltac unz := rewrite ?b2z_pos, ?b2z_lt1 by lia.

Lemma wz_m1 : Z_to_bv 64 (-1) = Z_to_bv 64 18446744073709551615.
Proof. apply bv_eq. reflexivity. Qed.

Ltac od_st_eq_leaf :=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | exact wz_m1 | f_equal; cbn [o_adv o_setd o_sete o_pos o_depth o_err o_alive o_sbo]; unfold M1; lia]
  | |- _ => reflexivity
  end.
Ltac od_st_eq_tree :=
  lazymatch goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal; od_st_eq_tree
  | |- Some _ = Some _ => f_equal; od_st_eq_leaf
  | |- _ => reflexivity
  end.
Ltac od_st_eq :=
  unfold wz; cbv delta [mkR];
  lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; od_st_eq_tree
  end.

Ltac od_cur_mem k := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => k m end.
