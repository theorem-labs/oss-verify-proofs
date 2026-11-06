(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Export Od_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition OD_ENTRY : Z := 0x27114.
Definition OD_FRAME : Z := 512.
Definition OD_ITER : Z := 0x2743c.
Definition OD_HEAD : Z := 0x2765c.
Definition OD_DISP : Z := 0x276b0.
Definition OD_PLUS : Z := 0x27fd8.
Definition OD_EXIT : Z := 0x284fc.
Definition OD_GTOP : Z := 0xab000.
Definition OD_NEED : Z := 2656.
Definition OD_DPI_VPTR : Z := 0x744e8.
Definition OD_PSTR : Z := 0x3970c.
Definition OD_FROMCH : Z := 0x28d00.
Definition OD_GOT_TABS : Z := 0x777b0.
Definition OD_JTAB : Z := 0x13100.

Notation od_ok := (od_ok_g OD_FRAME OD_NEED OD_GTOP OD_DPI_VPTR).

Notation FR E := (bv_unsigned (o_sp E) + -512)%Z.
Notation FR_IT E := (bv_unsigned (o_sp E) + -272)%Z.
Notation FR_PA E := (bv_unsigned (o_sp E) + -208)%Z.
Notation tokI_read := (tokI_read_g psegs).
Notation tokB_read := (tokB_read_g psegs).

Definition K104 : Z := 0xffff0000ffff.
Definition K112 : Z := 0x271000000001.
Definition fr_k24 : list cell := [C8 (wz 0x3526a); C8 (wz 0x7fffffffffffffff); C8 (wz 0xff00ff); C8 (wz 10000)].
Definition fr_k96 : list cell := [C8 (wz 0xa01); C8 (wz K104); C8 (wz K112); C8 (wz 100000000)].

Definition fr_k144 (E : odenv) (v192 v200 v224 v232 : Z) : list cell :=
  [C8 (wz 0xffffffff80808080); C8 (wz 0xffffffffcfcfcfd0); C8 (wz 0x46464646); C8 (wz 0x736c6166); C8 (wz (o_COPY E)); C8 (wz 0x65757274);
   C8 (wz v192); C8 (wz v200); C8 (wz 0x1100000000); C8 (wz 0x6c6c756e); C8 (wz v224); C8 (wz v232)].

Definition iter_cells (E : odenv) (st : ost) (j289 j300 : list byte) : list cell :=
  [C8 (wz (o_BUF E)); C8 (wz (o_IDX E + 4 * o_pos st)); C8 (wz (if o_alive st then FR_PA E else 0)); C8 (wz (o_SB E + o_sbo st));
   C4 (wz (o_err st)); C4 (wz (o_depth st)); C8 (wz (o_IDX E)); C1 (Z_to_bv 8 0); CB 7 j289; C4 (wz 0); CB 4 j300].

Definition od_parser_cells (E : odenv) : list cell :=
  [CB 8 (o_j304 E); C8 (wz (o_IMPL E)); C8 (o_w320 E); C8 (o_w328 E); C8 (o_w336 E); C8 (o_w344 E); C8 (wz (o_SB E))].

Definition od_vt_cells (v0 v1 v2 v3 v5 v6 v7 v8 v9 : word) : list cell :=
  [C8 v0; C8 v1; C8 v2; C8 v3; C8 (wz OD_PSTR); C8 v5; C8 v6; C8 v7; C8 v8; C8 v9].

Definition od_W (E : odenv) : list ivl := [ (o_lo E, FR_PA E); (o_SB E, o_SB E + o_CAP E) ]%Z.

Definition ODINVg (E : odenv) (v192 v200 v224 v232 : Z) (st : ost) (m1 : mem) : Prop :=
  (exists j0 j8 j16, rw_cells psegs m1 (FR E) [CB 8 j0; CB 8 j8; CB 8 j16]) /\
  rw_cells psegs m1 (bv_unsigned (o_sp E) + -488) fr_k24 /\
  (exists j56 j64 j72 j80 j88, rw_cells psegs m1 (bv_unsigned (o_sp E) + -456) [CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88]) /\
  rw_cells psegs m1 (bv_unsigned (o_sp E) + -416) fr_k96 /\
  (exists j128 j136, rw_cells psegs m1 (bv_unsigned (o_sp E) + -384) [CB 8 j128; CB 8 j136]) /\
  rw_cells psegs m1 (bv_unsigned (o_sp E) + -368) (fr_k144 E v192 v200 v224 v232) /\
  (exists j289 j300, rw_cells psegs m1 (FR_IT E) (iter_cells E st j289 j300)) /\
  rw_cells psegs m1 (FR_PA E) (od_parser_cells E) /\
  rw_cells psegs m1 (bv_unsigned (o_sp E) + -152) (o_hi E) /\
  rw_cells psegs m1 (o_IMPL E) (dpi_cells E) /\
  (exists ws, u32arr psegs m1 (o_IDX E) ws /\ idx_ok E ws) /\
  bytes_at psegs m1 (o_BUF E) (padded_bytes (o_bs E)) /\
  wr_at psegs m1 (o_SB E) (o_CAP E) /\
  (exists v0 v1 v2 v3 v5 v6 v7 v8 v9, rw_cells psegs m1 OD_DPI_VPTR (od_vt_cells v0 v1 v2 v3 v5 v6 v7 v8 v9)) /\
  rw_cells psegs m1 OD_GOT_TABS [C8 (wz 0x137e8); C8 (wz 0x14878); C8 (wz 0x138e8)] /\
  mem_inv psegs m1 /\ munch (od_W E) (o_m0 E) m1 /\ wmono psegs (o_m0 E) m1 /\
  stk psegs m1 (o_lo E) (FR E).

Notation ODINV E st m1 := (ODINVg E 2 0 1 1 st m1).

Definition OD_PRE (E : odenv) (m1 : mem) : Prop :=
  (exists junk, rw_cells psegs m1 (FR E) [CB 304 junk]) /\
  rw_cells psegs m1 (FR_PA E) (od_parser_cells E) /\
  rw_cells psegs m1 (bv_unsigned (o_sp E) + -152) (o_hi E) /\
  rw_cells psegs m1 (o_IMPL E) (dpi_cells E) /\
  (exists ws, u32arr psegs m1 (o_IDX E) ws /\ idx_ok E ws) /\
  bytes_at psegs m1 (o_BUF E) (padded_bytes (o_bs E)) /\
  wr_at psegs m1 (o_SB E) (o_CAP E) /\
  (exists v0 v1 v2 v3 v5 v6 v7 v8 v9, rw_cells psegs m1 OD_DPI_VPTR (od_vt_cells v0 v1 v2 v3 v5 v6 v7 v8 v9)) /\
  rw_cells psegs m1 OD_GOT_TABS [C8 (wz 0x137e8); C8 (wz 0x14878); C8 (wz 0x138e8)] /\
  mem_inv psegs m1 /\
  stk psegs m1 (o_lo E) (FR E).

Notation ODST E pc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m :=
  (MS (mkR (Z_to_bv 64 1) (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2
           (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 1) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           (Z_to_bv 64 0x640001) (Z_to_bv 64 (o_act E)) (Z_to_bv 64 91) xs5 xs6 (Z_to_bv 64 1) xs8
           (Z_to_bv 64 10) (Z_to_bv 64 125) (Z_to_bv 64 122) xt3 xt4 xt5 (Z_to_bv 64 2))
      xF (Z_to_bv 64 pc) xfc None m (seg_rom psegs)).

Definition od_exit_k (E : odenv) (Q : machine_state -> Prop) : Prop :=
  forall st v192 v200 v224 v232 xra xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    frm0 xfc -> ODINVg E v192 v200 v224 v232 st m1 ->
    evt psegs Q (MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         xs2 (Z_to_bv 64 (o_act E)) xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 OD_EXIT) xfc None m1 (seg_rom psegs)).

Definition od_head_pre (E : odenv) (st0 st : ost) : Prop :=
  od_next_ok (o_bs E) (o_idxs E) 1 st0 st \/ od_dead (o_n E) st.
Definition od_head_k (E : odenv) (Q : machine_state -> Prop) (st0 : ost) : Prop :=
  forall st xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1,
    od_head_pre E st0 st -> frm0 xfc -> ODINV E st m1 ->
    evt psegs Q (ODST E OD_HEAD xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1).

Definition od_plus_k (E : odenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall st' xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1,
    od_arm_out (o_bs E) (o_idxs E) st st' -> frm0 xfc -> ODINV E st' m1 ->
    evt psegs Q (ODST E OD_PLUS xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs8 xt3 xt4 xt5 xF xfc m1).

Definition arm_stmt (E : odenv) (entry : Z) : Prop :=
  forall (Q : machine_state -> Prop) st xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1,
    tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET ->
    od_head_ok (o_bs E) (o_idxs E) 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st ->
    evt psegs Q (ODST E entry xt0 xt1 xt2 (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc m1).

Ltac od_open_inv H :=
  let j0 := fresh "j0" in let j8 := fresh "j8" in let j16 := fresh "j16" in
  let j56 := fresh "j56" in let j64 := fresh "j64" in let j72 := fresh "j72" in let j80 := fresh "j80" in let j88 := fresh "j88" in
  let j128 := fresh "j128" in let j136 := fresh "j136" in let j289 := fresh "j289" in let j300 := fresh "j300" in
  let ws := fresh "ws" in
  let v0 := fresh "v0" in let v1 := fresh "v1" in let v2 := fresh "v2" in let v3 := fresh "v3" in let v5 := fresh "v5" in
  let v6 := fresh "v6" in let v7 := fresh "v7" in let v8 := fresh "v8" in let v9 := fresh "v9" in
  destruct H as ((j0 & j8 & j16 & FR0) & FR24 & (j56 & j64 & j72 & j80 & j88 & FR56) & FR96 & (j128 & j136 & FR128) & FR144
                 & (j289 & j300 & ITER) & PARS & FRHI & DPI & (ws & IDXA & IDXOK) & BUFRO & SBW
                 & (v0 & v1 & v2 & v3 & v5 & v6 & v7 & v8 & v9 & VT) & GOT & MI & MU & WM & ST);
  unfold fr_k24 in FR24; unfold fr_k96 in FR96; unfold fr_k144 in FR144; unfold iter_cells in ITER; unfold dpi_cells in DPI;
  unfold od_parser_cells in PARS;
  unfold od_vt_cells in VT; unfold od_W in MU; unfold OD_DPI_VPTR in VT; unfold OD_GOT_TABS in GOT;
  unfold wz in FR24, FR96, FR144, ITER, PARS, DPI, VT, GOT;
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
  unfold wz; cbn [o_adv o_setd o_sete o_abandon consume o_pos o_depth o_err o_alive o_sbo];
  repeat match goal with H : o_alive ?s = _ |- context [o_alive ?s] => rewrite H end;
  od_cells_eq_rec.
Ltac od_ass := first [eassumption | (eapply rw_cells_eq; [eassumption | od_cells_eq])].

Ltac od_close_inv :=
  lazymatch goal with
  | |- ODINVg _ _ _ _ _ _ _ =>
      try match goal with
          | HV : o_vptr ?E = ?v, HD : rw_cells _ _ (o_IMPL ?E) (C8 ?v :: _) |- _ => rewrite <- HV in HD
          end;
      unfold ODINVg, fr_k24, fr_k96, fr_k144, iter_cells, od_parser_cells, dpi_cells, od_vt_cells, od_W, OD_DPI_VPTR, OD_GOT_TABS, idx_ok;
      split; [ do 3 eexists; eassumption | ];
      split; [eassumption|];
      split; [ do 5 eexists; eassumption | ];
      split; [eassumption|];
      split; [ do 2 eexists; eassumption | ];
      split; [eassumption|];
      split; [ do 2 eexists; od_ass | ];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
      split; [ eexists; split; [eassumption| split; eassumption] | ];
      split; [eassumption|]; split; [eassumption|];
      split; [ do 9 eexists; eassumption | ];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

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

Ltac od_st_eq_leaf :=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; cbn [o_adv o_setd o_sete o_pos o_depth o_err o_alive o_sbo]; lia]
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
