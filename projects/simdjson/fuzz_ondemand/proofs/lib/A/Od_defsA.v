(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Export Od_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface Sj_akit Sj_acps Sj_hkit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Export Sj_num_amem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition OD_ENTRY : Z := 0x969a4.
Definition OD_ITER : Z := 0x99ec8.
Definition OD_HEAD1 : Z := 0x972ec.
Definition OD_HEAD : Z := 0x972f4.
Definition OD_DISP : Z := 0x97394.
Definition OD_PLUS : Z := 0x98e3c.
Definition OD_EXIT : Z := 0x99d04.
Definition OD_NEED : Z := 0x10400.
Definition OD_DPI_VT : Z := 0x109840.
Definition OD_DPI_VPTR : Z := 0x109850.
Definition OD_PSTR : Z := 0xc4a1c.
Definition OD_FROMCH : Z := 0x9bf1c.
Definition OD_GOT_TABS : Z := 0x10d878.
Definition OD_JTAB : Z := 0x2305c.
Definition OD_TAB_FIN : Z := 0x23160.
Definition OD_TAB_SOWN : Z := 0x238a0.
Definition OD_TAB_SOW : Z := 0x239e0.
Definition OD_TAB_DIG : Z := 0x23b20.
Definition OD_TAB_POW5 : Z := 0x24d40.
Definition OD_TAB_ESC : Z := 0x28760.

Record oaenv : Type := mkOaEnv {
  oa_E :> odenv;
  oa_USP : Z;
  oa_S1 : Z;
  oa_F : Z
}.

Notation tokI_read := (tokI_read_g asegs).
Notation tokB_read := (tokB_read_g asegs).

Definition fr_k32 (vs6 : Z) : list cell :=
  [C8 (wz (vs6 + 32)); C8 (wz (vs6 + 16)); C8 (wz (vs6 + 36)); C8 (wz 3); C8 (wz 7);
   C8 (wz 0x3526a); C8 (wz 0x7fffffffffffffff); C8 (wz 0xff00ff); C8 (wz 10000)].
Definition fr_k128 (E : oaenv) : list cell :=
  [C8 (wz 0xffffffff80808080); C8 (wz 0xffffffffcfcfcfd0); C8 (wz 0x46464646); C8 (wz 0x736c6166); C8 (wz (o_COPY E)); C8 (wz 0x65757274)].

Definition fr_k184 (E : oaenv) (vs6 v224 v248 v304 v312 v328 v344 : Z) : list cell :=
  [C8 (wz (o_act E)); C8 (wz (oa_F E)); C8 (wz (oa_F E)); C8 (wz (oa_F E + 96)); C8 (wz (oa_F E + 104)); C8 (wz v224);
   C8 (wz 0x1100000000); C8 (wz (oa_F E / 8 + 2147450880)); C8 (wz v248);
   C8 (wz 0xa01); C8 (wz 0xffff0000ffff); C8 (wz 0x271000000001); C8 (wz 100000000); C8 (wz 0x640001); C8 (wz 0x6c6c756e);
   C8 (wz v304); C8 (wz v312); C8 (wz ((vs6 + 16) / 8 + 2147450880)); C8 (wz v328); C8 (wz ((vs6 + 32) / 8 + 2147450880)); C8 (wz v344)].

Definition iter_cells (E : oaenv) (st : ost) (j241 j252 : list byte) : list cell :=
  [C8 (wz (o_BUF E)); C8 (wz (o_IDX E + 4 * o_pos st)); C8 (wz (if o_alive st then oa_F E + 96 else 0)); C8 (wz (o_SB E + o_sbo st));
   C4 (wz (o_err st)); C4 (wz (o_depth st)); C8 (wz (o_IDX E)); C1 (Z_to_bv 8 0); CB 7 j241; C4 (wz 0); CB 4 j252].

Definition od_parser_cells (E : oaenv) : list cell :=
  [CB 8 (o_j304 E); C8 (wz (o_IMPL E)); C8 (o_w320 E); C8 (o_w328 E); C8 (o_w336 E); C8 (o_w344 E); C8 (wz (o_SB E))].

Definition od_vt_cells : list cell :=
  [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x1098c0); C8 (Z_to_bv 64 0xc5958); C8 (Z_to_bv 64 0x9cfa0); C8 (Z_to_bv 64 0x9f8d8);
   C8 (Z_to_bv 64 0xb2330); C8 (Z_to_bv 64 0xc4a1c); C8 (Z_to_bv 64 0xc51d0); C8 (Z_to_bv 64 0xc5d0c); C8 (Z_to_bv 64 0xc5e6c);
   C8 (Z_to_bv 64 0xc5fd4); C8 (Z_to_bv 64 0xc60c0)].

Definition od_got_cells : list cell :=
  [C8 (Z_to_bv 64 0x238a0); C8 (Z_to_bv 64 0x24d40); C8 (Z_to_bv 64 0x239e0); C8 (Z_to_bv 64 0x2d070)].

Definition od_W (E : oaenv) : list ivl :=
  [ (o_lo E, oa_S1 E + 352); (oa_F E + 192, oa_F E + 256); (o_SB E, o_SB E + o_CAP E) ]%Z.

Record od_oka (E : oaenv) : Prop := mkOdOkA {
  oka_bytes : bytes_ok (o_bs E);
  oka_s1 : S1OUT (o_bs E) (o_idxs E);
  oka_len : (o_len E <= S1_LEN_MAX)%Z;
  oka_act : (0 <= o_act E <= 12)%Z;
  oka_vptr : o_vptr E = Z_to_bv 64 OD_DPI_VPTR;

  oka_usp : (oa_USP E mod 16 = 0 /\ oa_USP E + 16 <= 0x800000000000)%Z;
  oka_S1 : (oa_S1 E mod 32 = 0 /\ oa_USP E - 528 <= oa_S1 E <= oa_USP E - 512)%Z;
  oka_lo : (0x66b000 <= o_lo E /\ o_lo E + OD_NEED <= oa_S1 E)%Z;

  oka_F : (oa_F E mod 64 = 0 /\ 0x66b000 <= oa_F E /\ oa_F E + 512 <= o_lo E)%Z;
  oka_Fsh : (oa_F E / 8 + 2147450880 + 64 <= o_lo E
             /\ (oa_F E + 512 <= oa_F E / 8 + 2147450880 \/ oa_F E / 8 + 2147450880 + 64 <= oa_F E))%Z;

  oka_copy : (0 < o_COPY E /\ o_COPY E mod 8 = 0 /\ o_COPY E <= o_BUF E <= o_COPY E + 3 /\ o_BUF E + o_len E + 64 <= o_lo E
              /\ (o_BUF E + o_len E + 64 <= 0x10000 \/ 0x66b000 <= o_COPY E))%Z;
  oka_sb : (0 < o_SB E /\ o_SB E mod 8 = 0 /\ o_SB E + o_CAP E <= o_lo E /\ (o_SB E + o_CAP E <= 0x10000 \/ 0x66b000 <= o_SB E))%Z;
  oka_cap : (o_len E + 62 <= o_CAP E)%Z;
  oka_impl : (0 < o_IMPL E /\ o_IMPL E mod 8 = 0 /\ o_IMPL E + 96 <= o_lo E /\ (o_IMPL E + 96 <= 0x10000 \/ 0x66b000 <= o_IMPL E))%Z;
  oka_idx : (0 < o_IDX E /\ o_IDX E mod 8 = 0 /\ o_IDX E + 4 * Z.of_nat (o_icap E) <= o_lo E
             /\ (o_IDX E + 4 * Z.of_nat (o_icap E) <= 0x10000 \/ 0x66b000 <= o_IDX E))%Z;
  oka_icap : (o_n E + 4 <= Z.of_nat (o_icap E))%Z;

  oka_sb_buf : (o_SB E + o_CAP E <= o_COPY E \/ o_BUF E + o_len E + 64 <= o_SB E)%Z;
  oka_sb_idx : (o_SB E + o_CAP E <= o_IDX E \/ o_IDX E + 4 * Z.of_nat (o_icap E) <= o_SB E)%Z;
  oka_sb_impl : (o_SB E + o_CAP E <= o_IMPL E \/ o_IMPL E + 96 <= o_SB E)%Z;
  oka_F_buf : (oa_F E + 512 <= o_COPY E \/ o_BUF E + o_len E + 64 <= oa_F E)%Z;
  oka_F_sb : (oa_F E + 512 <= o_SB E \/ o_SB E + o_CAP E <= oa_F E)%Z;
  oka_F_idx : (oa_F E + 512 <= o_IDX E \/ o_IDX E + 4 * Z.of_nat (o_icap E) <= oa_F E)%Z;
  oka_F_impl : (oa_F E + 512 <= o_IMPL E \/ o_IMPL E + 96 <= oa_F E)%Z;
  oka_Fs_sb : (oa_F E / 8 + 2147450880 + 64 <= o_SB E \/ o_SB E + o_CAP E <= oa_F E / 8 + 2147450880)%Z;

  oka_z_fin : forall m', munch (od_W E) (o_m0 E) m' -> wmono asegs (o_m0 E) m' -> shz m' OD_TAB_FIN 256;
  oka_z_sown : forall m', munch (od_W E) (o_m0 E) m' -> wmono asegs (o_m0 E) m' -> shz m' OD_TAB_SOWN 256;
  oka_z_sow : forall m', munch (od_W E) (o_m0 E) m' -> wmono asegs (o_m0 E) m' -> shz m' OD_TAB_SOW 256;
  oka_z_dig : forall m', munch (od_W E) (o_m0 E) m' -> wmono asegs (o_m0 E) m' -> shz m' OD_TAB_DIG 3544;
  oka_z_pow5 : forall m', munch (od_W E) (o_m0 E) m' -> wmono asegs (o_m0 E) m' -> shz m' OD_TAB_POW5 10416;
  oka_z_esc : forall m', munch (od_W E) (o_m0 E) m' -> wmono asegs (o_m0 E) m' -> shz m' OD_TAB_ESC 256;
  oka_z_vt : forall m', munch (od_W E) (o_m0 E) m' -> wmono asegs (o_m0 E) m' -> shz m' OD_DPI_VT 96;
  oka_z_sb : forall m', munch (od_W E) (o_m0 E) m' -> wmono asegs (o_m0 E) m' -> shz m' (o_SB E) (o_CAP E);
  oka_z_impl : forall m', munch (od_W E) (o_m0 E) m' -> wmono asegs (o_m0 E) m' -> shz m' (o_IMPL E) 96;
  oka_z_par : forall m', munch (od_W E) (o_m0 E) m' -> wmono asegs (o_m0 E) m' -> shz m' (oa_F E + 96) 56;
  oka_z_buf : forall m', munch (od_W E) (o_m0 E) m' -> wmono asegs (o_m0 E) m' -> shz m' (o_COPY E) (o_BUF E - o_COPY E + o_len E + 57);
  oka_z_idx : forall m', munch (od_W E) (o_m0 E) m' -> wmono asegs (o_m0 E) m' -> shz m' (o_IDX E) (4 * (o_n E + 3));
  oka_z_doc : forall m', munch (od_W E) (o_m0 E) m' -> wmono asegs (o_m0 E) m' -> shz m' (oa_F E + 192) 64
}.

Definition ODINVg (E : oaenv) (vs6 v224 v248 v304 v312 v328 v344 : Z) (st : ost) (m1 : mem) : Prop :=
  (exists j0 j8 j16 j24, rw_cells asegs m1 (oa_S1 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24]) /\
  rw_cells asegs m1 (oa_S1 E + 32) (fr_k32 vs6) /\
  (exists j104 j112 j120, rw_cells asegs m1 (oa_S1 E + 104) [CB 8 j104; CB 8 j112; CB 8 j120]) /\
  rw_cells asegs m1 (oa_S1 E + 128) (fr_k128 E) /\
  (exists j176, rw_cells asegs m1 (oa_S1 E + 176) [CB 8 j176]) /\
  rw_cells asegs m1 (oa_S1 E + 184) (fr_k184 E vs6 v224 v248 v304 v312 v328 v344) /\
  (exists j241 j252, rw_cells asegs m1 (oa_F E + 192) (iter_cells E st j241 j252)) /\
  rw_cells asegs m1 (oa_F E + 96) (od_parser_cells E) /\
  rw_cells asegs m1 (o_IMPL E) (dpi_cells E) /\
  (exists ws, u32arr asegs m1 (o_IDX E) ws /\ idx_ok E ws) /\
  bytes_at asegs m1 (o_BUF E) (padded_bytes (o_bs E)) /\
  wr_at asegs m1 (o_SB E) (o_CAP E) /\
  ro_cells asegs m1 OD_DPI_VT od_vt_cells /\
  ro_cells asegs m1 OD_GOT_TABS od_got_cells /\
  mem_inv asegs m1 /\ munch (od_W E) (o_m0 E) m1 /\ wmono asegs (o_m0 E) m1 /\
  stk asegs m1 (o_lo E) (oa_S1 E).

Notation ODINVh E v344 st m1 := (ODINVg E (oa_F E + 192) 0 2 1 1 1 v344 st m1).
Notation ODINV E st m1 := (ODINVg E (oa_F E + 192) 0 2 1 1 1 1 st m1).

Notation ODST E pc xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m :=
  (MS (mkR (Z_to_bv 64 (o_act E)) (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2
           (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880))
           (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 ((oa_F E + 228) / 8 + 2147450880)) (Z_to_bv 64 (oa_F E + 200))
           xs9 xs10 xs11 xt3 xt4 (Z_to_bv 64 1) (Z_to_bv 64 1))
      xF (Z_to_bv 64 pc) xfc None m (seg_rom asegs)).

Definition od_exit_k (E : oaenv) (Q : machine_state -> Prop) : Prop :=
  forall st vs6 v224 v248 v304 v312 v328 v344 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    frm0 xfc -> ODINVg E vs6 v224 v248 v304 v312 v328 v344 st m1 ->
    evt asegs Q (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2
                         (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         xs2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (oa_F E + 32)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 OD_EXIT) xfc None m1 (seg_rom asegs)).

Definition od_head_pre (E : oaenv) (st0 st : ost) : Prop :=
  od_next_ok (o_bs E) (o_idxs E) 1 st0 st \/ od_dead (o_n E) st.
Definition od_head_k (E : oaenv) (Q : machine_state -> Prop) (st0 : ost) : Prop :=
  forall st v344 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
    od_head_pre E st0 st -> frm0 xfc -> ODINVh E v344 st m1 ->
    evt asegs Q (ODST E OD_HEAD xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).

Definition od_plus_k (E : oaenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall st' xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
    od_arm_out (o_bs E) (o_idxs E) st st' -> frm0 xfc -> ODINV E st' m1 ->
    evt asegs Q (ODST E OD_PLUS xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).

Definition arm_k (E : oaenv) (Q : machine_state -> Prop) (entry : Z) (st : ost) : Prop :=
  forall xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xF xfc m1,
    frm0 xfc -> ODINV E st m1 ->
    evt asegs Q (ODST E entry (Z_to_bv 64 122) xt1 xt2 (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) xs11 xt3 xt4 xF xfc m1).

Definition arm_stmt (E : oaenv) (entry : Z) : Prop :=
  forall (Q : machine_state -> Prop) st,
    tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET ->
    od_head_ok (o_bs E) (o_idxs E) 1 st ->
    od_plus_k E Q st ->
    arm_k E Q entry st.

Ltac od_open_inv H :=
  let j0 := fresh "j0" in let j8 := fresh "j8" in let j16 := fresh "j16" in let j24 := fresh "j24" in
  let j104 := fresh "j104" in let j112 := fresh "j112" in let j120 := fresh "j120" in let j176 := fresh "j176" in
  let j241 := fresh "j241" in let j252 := fresh "j252" in
  let ws := fresh "ws" in
  destruct H as ((j0 & j8 & j16 & j24 & FR0) & FR32 & (j104 & j112 & j120 & FR104) & FR128 & (j176 & FR176) & FR184
                 & (j241 & j252 & ITER) & PARS & DPI & (ws & IDXA & IDXOK) & BUFRO & SBW & VT & GOT & MI & MU & WM & ST);
  unfold fr_k32 in FR32; unfold fr_k128 in FR128; unfold fr_k184 in FR184; unfold iter_cells in ITER; unfold dpi_cells in DPI;
  unfold od_parser_cells in PARS;
  unfold od_vt_cells, OD_DPI_VT in VT; unfold od_got_cells, OD_GOT_TABS in GOT; unfold od_W in MU;
  unfold wz in FR32, FR128, FR184, ITER, PARS, DPI;
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
  | |- ODINVg _ _ _ _ _ _ _ _ _ _ =>
      try match goal with
          | HV : o_vptr ?E = ?v, HD : rw_cells _ _ (o_IMPL ?E) (C8 ?v :: _) |- _ => rewrite <- HV in HD
          end;
      unfold ODINVg, fr_k32, fr_k128, fr_k184, iter_cells, od_parser_cells, dpi_cells, od_vt_cells, od_got_cells, od_W, OD_DPI_VT, OD_GOT_TABS, idx_ok;
      split; [ do 4 eexists; eassumption | ];
      split; [od_ass|];
      split; [ do 3 eexists; eassumption | ];
      split; [eassumption|];
      split; [ eexists; eassumption | ];
      split; [od_ass|];
      split; [ do 2 eexists; od_ass | ];
      split; [eassumption|]; split; [eassumption|];
      split; [ eexists; split; [eassumption| split; eassumption] | ];
      split; [eassumption|]; split; [eassumption|];
      split; [eassumption|]; split; [eassumption|];
      split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Ltac od_env OK :=
  let BOK := fresh "BOK" in let S1 := fresh "S1" in let LEN := fresh "LEN" in let ACT := fresh "ACT" in let VPT := fresh "VPT" in
  let USP16 := fresh "USP16" in let USPT := fresh "USPT" in let S32 := fresh "S32" in let S1R := fresh "S1R" in
  let LOB := fresh "LOB" in let LOR := fresh "LOR" in
  let F64 := fresh "F64" in let FB := fresh "FB" in let FR := fresh "FR" in let FSH := fresh "FSH" in let FSD := fresh "FSD" in
  let CP0 := fresh "CP0" in let CP8 := fresh "CP8" in let CPB := fresh "CPB" in let BUFR := fresh "BUFR" in let BUFD := fresh "BUFD" in
  let SB0 := fresh "SB0" in let SB8 := fresh "SB8" in let SBR := fresh "SBR" in let SBD := fresh "SBD" in let CAPR := fresh "CAPR" in
  let IM0 := fresh "IM0" in let IM8 := fresh "IM8" in let IMR := fresh "IMR" in let IMD := fresh "IMD" in
  let IX0 := fresh "IX0" in let IX8 := fresh "IX8" in let IXR := fresh "IXR" in let IXD := fresh "IXD" in let ICAP := fresh "ICAP" in
  let S_SB := fresh "S_SB" in let S_SI := fresh "S_SI" in let S_SM := fresh "S_SM" in
  let F_B := fresh "F_B" in let F_S := fresh "F_S" in let F_I := fresh "F_I" in let F_M := fresh "F_M" in let FS_S := fresh "FS_S" in
  let Z_FIN := fresh "Z_FIN" in let Z_SOWN := fresh "Z_SOWN" in let Z_SOW := fresh "Z_SOW" in let Z_DIG := fresh "Z_DIG" in
  let Z_POW5 := fresh "Z_POW5" in let Z_ESC := fresh "Z_ESC" in let Z_VT := fresh "Z_VT" in
  let Z_SB := fresh "Z_SB" in let Z_IMPL := fresh "Z_IMPL" in
  let Z_PAR := fresh "Z_PAR" in let Z_BUF := fresh "Z_BUF" in let Z_IDX := fresh "Z_IDX" in let Z_DOC := fresh "Z_DOC" in
  pose proof OK as [BOK S1 LEN ACT VPT [USP16 USPT] [S32 S1R] [LOB LOR] [F64 [FB FR]] [FSH FSD]
                    [CP0 [CP8 [CPB [BUFR BUFD]]]] [SB0 [SB8 [SBR SBD]]] CAPR [IM0 [IM8 [IMR IMD]]] [IX0 [IX8 [IXR IXD]]] ICAP
                    S_SB S_SI S_SM F_B F_S F_I F_M FS_S
                    Z_FIN Z_SOWN Z_SOW Z_DIG Z_POW5 Z_ESC Z_VT Z_SB Z_IMPL Z_PAR Z_BUF Z_IDX Z_DOC];

  clear FSD BUFD SBD IMD IXD S_SB S_SI S_SM FS_S;
  unfold S1_LEN_MAX, OD_NEED, OD_DPI_VPTR, OD_DPI_VT, OD_TAB_FIN, OD_TAB_SOWN, OD_TAB_SOW, OD_TAB_DIG, OD_TAB_POW5, OD_TAB_ESC, od_W in *;
  lazymatch goal with E : oaenv |- _ =>
    let NR := fresh "NR" in pose proof (od_n_range E S1) as NR
  end.

Ltac od_env_sep OK :=
  let FSD := fresh "FSD" in let BUFD := fresh "BUFD" in let SBD := fresh "SBD" in let IMD := fresh "IMD" in let IXD := fresh "IXD" in
  let S_SB := fresh "S_SB" in let S_SI := fresh "S_SI" in let S_SM := fresh "S_SM" in let FS_S := fresh "FS_S" in
  pose proof (proj2 (oka_Fsh _ OK)) as FSD;
  pose proof (proj2 (proj2 (proj2 (proj2 (oka_copy _ OK))))) as BUFD;
  pose proof (proj2 (proj2 (proj2 (oka_sb _ OK)))) as SBD;
  pose proof (proj2 (proj2 (proj2 (oka_impl _ OK)))) as IMD;
  pose proof (proj2 (proj2 (proj2 (oka_idx _ OK)))) as IXD;
  pose proof (oka_sb_buf _ OK) as S_SB; pose proof (oka_sb_idx _ OK) as S_SI; pose proof (oka_sb_impl _ OK) as S_SM;
  pose proof (oka_Fs_sb _ OK) as FS_S.

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

Lemma shz_read_off : forall (m : mem) B a n k adr, shz m (B + a) n -> ((a <=? k) && (k <? a + n))%bool = true ->
  adr = wa ((B + k) / 8 + 2147450880) -> ov_read_bytes asegs m adr 1 = Some [Z_to_bv 8 0].
Proof.
  intros m B a n k adr H HB ->. apply H. apply andb_prop in HB as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma shz_read_base : forall (m : mem) B n adr, shz m B n -> (0 <? n) = true ->
  adr = wa (B / 8 + 2147450880) -> ov_read_bytes asegs m adr 1 = Some [Z_to_bv 8 0].
Proof. intros m B n adr H HB ->. apply H. apply Z.ltb_lt in HB. lia. Qed.

Ltac od_lit_in L a0 n0 :=
  let b := eval vm_compute in (andb (Z.leb a0 L) (Z.ltb L (a0 + n0)))%Z in
  lazymatch b with true => idtac end.

Ltac od_serves a0 n0 X :=
  lazymatch a0 with
  | o_IDX ?E => lazymatch X with context [o_IDX E] => idtac end
  | o_COPY ?E => lazymatch X with context [o_BUF E] => idtac | context [o_COPY E] => idtac end
  | o_IMPL ?E => lazymatch X with context [o_IMPL E] => idtac end
  | o_SB ?E => lazymatch X with context [o_SB E] => idtac end
  | (oa_F ?E + _)%Z => fail
  | _ => lazymatch X with
         | (?L + _)%Z => od_lit_in L a0 n0
         | _ => od_lit_in X a0 n0
         end
  end.
Ltac od_load_hook :=
  match goal with
  | |- context [ov_read_bytes asegs ?m ?a 1] =>
      let Ea := addr_expr a in
      lazymatch Ea with
      | (?X / 8 + 2147450880)%Z =>
          lazymatch goal with
          | MU : munch ?W ?m0 m, WM : wmono asegs ?m0 m |- _ =>
              lazymatch X with
              | (oa_F ?E + ?k)%Z =>
                  match goal with
                  | SHP : (forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' (oa_F E + ?a0) ?n0) |- _ =>
                      rewrite (shz_read_off m (oa_F E) a0 n0 k a (SHP m MU WM) eq_refl eq_refl)
                  end
              | _ =>
                  match goal with
                  | SHP : (forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' ?a0 ?n0) |- _ =>
                      od_serves a0 n0 X;
                      first [ rewrite (shz_read_base m a0 n0 a (SHP m MU WM) eq_refl eq_refl)
                            | rewrite (shz_read m a0 n0 X a (SHP m MU WM) ltac:(lia) ltac:(reflexivity)) ]
                  end
              end
          end
      | Zpos _ =>

          let X := eval vm_compute in (8 * (Ea - 2147450880))%Z in
          lazymatch goal with
          | MU : munch ?W ?m0 m, WM : wmono asegs ?m0 m |- _ =>
              match goal with
              | SHP : (forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' ?a0 ?n0) |- _ =>
                  od_lit_in X a0 n0;
                  rewrite (shz_read m a0 n0 X a (SHP m MU WM) ltac:(lia) ltac:(reflexivity))
              end
          end
      end
  end;
  load_post.

Ltac ostep := zstep; anorm.

Ltac ochk := ostep; ostep; ostep; ostep; if_true.
Ltac ochkn := ostep; ostep; ostep; ostep; if_false.
