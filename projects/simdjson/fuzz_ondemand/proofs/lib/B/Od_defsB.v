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
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface Sj_akit Sj_acps Sj_hkit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Export Sj_num_amem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition OD_ENTRY : Z := 0x96940.
Definition OD_ITER : Z := 0x9bb5c.
Definition OD_HEAD : Z := 0x9758c.
Definition OD_DISP : Z := 0x9764c.
Definition OD_PLUS : Z := 0x9a5d4.
Definition OD_EXIT : Z := 0x9b978.
Definition OD_TRAP : Z := 0x96bbc.
Definition OD_NEED : Z := 0x10400.
Definition OD_DPI_VT : Z := 0x1179c0.
Definition OD_DPI_VPTR : Z := 0x1179d0.
Definition OD_PSTR : Z := 0xd2144.
Definition OD_FROMCH : Z := 0x9e77c.
Definition OD_OPIDX : Z := 0x9e088.
Definition OD_GOT_TABS : Z := 0x11b9f8.
Definition OD_JTAB : Z := 0x230cc.
Definition OD_TAB_FIN : Z := 0x231c0.
Definition OD_TAB_SOWN : Z := 0x23900.
Definition OD_TAB_SOW : Z := 0x23a40.
Definition OD_TAB_DIG : Z := 0x23b80.
Definition OD_TAB_POW10 : Z := 0x24cc0.
Definition OD_TAB_POW5 : Z := 0x24da0.
Definition OD_TAB_ESC : Z := 0x28400.

Record oaenv : Type := mkOaEnv {
  oa_E :> odenv;
  oa_USP : Z;
  oa_S1 : Z;
  oa_F : Z
}.

Notation tokI_read := (tokI_read_g bsegs).
Notation tokB_read := (tokB_read_g bsegs).

Definition fr_k8 (E : oaenv) (v88 : Z) : list cell :=
  [C8 (wz 3); C8 (wz 0x3526a); C8 (wz 0xff00ff); C8 (wz 10000); C8 (wz 0x736c6166);
   C8 (wz 0xffffffff80808080); C8 (wz 0xffffffffcfcfcfd0); C8 (wz 0x46464646); C8 (wz (oa_F E + 104)); C8 (wz 0x65757274); C8 (wz v88)].

Definition fr_k96 (E : oaenv) (v144 v152 : Z) (c96 c104 c224 c232 : cell) : list cell :=
  [c96; c104;
   C8 (wz 0); C8 (wz (oa_F E)); C8 (wz (oa_F E)); C8 (wz (o_COPY E)); C8 (wz v144); C8 (wz v152); C8 (wz 0x7fffffff);
   C8 (wz (oa_F E + 96)); C8 (wz 0xffff0000ffff); C8 (wz 0x271000000001); C8 (wz 0xa01); C8 (wz 100000000); C8 (wz 0x6c6c756e);
   C8 (wz 0x640001);
   c224; c232].

Definition fr_k240 (E : oaenv) (vs v240 v312 v336 v352 : Z) (c272 c304 c320 c376 : cell) : list cell :=
  [C8 (wz v240); C8 (wz (oa_F E / 8 + 2147450880)); C8 (wz (o_act E)); C8 (wz ((vs + 32) / 8 + 2147450880));
   c272;
   C8 (wz (vs + 32)); C8 (wz vs); C8 (wz (oa_F E + 32));
   c304; C8 (wz v312); c320;
   C8 (wz (vs + 16)); C8 (wz v336); C8 (wz (vs + 36)); C8 (wz v352); C8 (wz ((vs + 8) / 8 + 2147450880)); C8 (wz (vs + 8));
   c376].

Definition iter_cells (E : oaenv) (st : ost) (j241 j252 : list byte) : list cell :=
  [C8 (wz (o_BUF E)); C8 (wz (o_IDX E + 4 * o_pos st)); C8 (wz (if o_alive st then oa_F E + 96 else 0)); C8 (wz (o_SB E + o_sbo st));
   C4 (wz (o_err st)); C4 (wz (o_depth st)); C8 (wz (o_IDX E)); C1 (Z_to_bv 8 0); CB 7 j241; C4 (wz 0); CB 4 j252].

Definition od_parser_cells (E : oaenv) : list cell :=
  [CB 8 (o_j304 E); C8 (wz (o_IMPL E)); C8 (o_w320 E); C8 (o_w328 E); C8 (o_w336 E); C8 (o_w344 E); C8 (wz (o_SB E))].

Definition od_vt_cells : list cell :=
  [C8 (Z_to_bv 64 0x0); C8 (Z_to_bv 64 0x117a40); C8 (Z_to_bv 64 0xd3234); C8 (Z_to_bv 64 0x9f9e8); C8 (Z_to_bv 64 0xa2ec4);
   C8 (Z_to_bv 64 0xba8ac); C8 (Z_to_bv 64 0xd2144); C8 (Z_to_bv 64 0xd29e8); C8 (Z_to_bv 64 0xd3610); C8 (Z_to_bv 64 0xd3784);
   C8 (Z_to_bv 64 0xd38f8); C8 (Z_to_bv 64 0xd39e4)].

Definition od_got_cells : list cell :=
  [C8 (Z_to_bv 64 0x23900); C8 (Z_to_bv 64 0x24cc0); C8 (Z_to_bv 64 0x24da0); C8 (Z_to_bv 64 0x23a40); C8 (Z_to_bv 64 0x2cd30)].

Definition od_W (E : oaenv) : list ivl :=
  [ (o_lo E, oa_S1 E + 384); (oa_F E + 192, oa_F E + 256); (o_SB E, o_SB E + o_CAP E) ]%Z.

Record od_oka (E : oaenv) : Prop := mkOdOkA {
  oka_bytes : bytes_ok (o_bs E);
  oka_s1 : S1OUT (o_bs E) (o_idxs E);
  oka_len : (o_len E <= S1_LEN_MAX)%Z;
  oka_act : (0 <= o_act E <= 12)%Z;
  oka_vptr : o_vptr E = Z_to_bv 64 OD_DPI_VPTR;

  oka_usp : (oa_USP E mod 16 = 0 /\ oa_USP E + 16 <= 0x800000000000)%Z;
  oka_S1 : (oa_S1 E mod 32 = 0 /\ oa_USP E - 560 <= oa_S1 E <= oa_USP E - 544)%Z;
  oka_lo : (0x679000 <= o_lo E /\ o_lo E + OD_NEED <= oa_S1 E)%Z;

  oka_F : (oa_F E mod 64 = 0 /\ 0x679000 <= oa_F E /\ oa_F E + 512 <= o_lo E)%Z;
  oka_Fsh : (oa_F E / 8 + 2147450880 + 64 <= o_lo E
             /\ (oa_F E + 512 <= oa_F E / 8 + 2147450880 \/ oa_F E / 8 + 2147450880 + 64 <= oa_F E))%Z;

  oka_copy : (0 < o_COPY E /\ o_COPY E mod 8 = 0 /\ o_COPY E <= o_BUF E <= o_COPY E + 3 /\ o_BUF E + o_len E + 64 <= o_lo E
              /\ (o_BUF E + o_len E + 64 <= 0x10000 \/ 0x679000 <= o_COPY E))%Z;
  oka_sb : (0 < o_SB E /\ o_SB E mod 8 = 0 /\ o_SB E + o_CAP E <= o_lo E /\ (o_SB E + o_CAP E <= 0x10000 \/ 0x679000 <= o_SB E))%Z;
  oka_cap : (o_len E + 62 <= o_CAP E)%Z;
  oka_impl : (0 < o_IMPL E /\ o_IMPL E mod 8 = 0 /\ o_IMPL E + 96 <= o_lo E /\ (o_IMPL E + 96 <= 0x10000 \/ 0x679000 <= o_IMPL E))%Z;
  oka_idx : (0 < o_IDX E /\ o_IDX E mod 8 = 0 /\ o_IDX E + 4 * Z.of_nat (o_icap E) <= o_lo E
             /\ (o_IDX E + 4 * Z.of_nat (o_icap E) <= 0x10000 \/ 0x679000 <= o_IDX E))%Z;
  oka_icap : (o_n E + 4 <= Z.of_nat (o_icap E))%Z;

  oka_sb_buf : (o_SB E + o_CAP E <= o_COPY E \/ o_BUF E + o_len E + 64 <= o_SB E)%Z;
  oka_sb_idx : (o_SB E + o_CAP E <= o_IDX E \/ o_IDX E + 4 * Z.of_nat (o_icap E) <= o_SB E)%Z;
  oka_sb_impl : (o_SB E + o_CAP E <= o_IMPL E \/ o_IMPL E + 96 <= o_SB E)%Z;
  oka_F_buf : (oa_F E + 512 <= o_COPY E \/ o_BUF E + o_len E + 64 <= oa_F E)%Z;
  oka_F_sb : (oa_F E + 512 <= o_SB E \/ o_SB E + o_CAP E <= oa_F E)%Z;
  oka_F_idx : (oa_F E + 512 <= o_IDX E \/ o_IDX E + 4 * Z.of_nat (o_icap E) <= oa_F E)%Z;
  oka_F_impl : (oa_F E + 512 <= o_IMPL E \/ o_IMPL E + 96 <= oa_F E)%Z;
  oka_Fs_sb : (oa_F E / 8 + 2147450880 + 64 <= o_SB E \/ o_SB E + o_CAP E <= oa_F E / 8 + 2147450880)%Z;

  oka_z_fin : forall m', munch (od_W E) (o_m0 E) m' -> wmono bsegs (o_m0 E) m' -> shz m' OD_TAB_FIN 256;
  oka_z_sown : forall m', munch (od_W E) (o_m0 E) m' -> wmono bsegs (o_m0 E) m' -> shz m' OD_TAB_SOWN 256;
  oka_z_sow : forall m', munch (od_W E) (o_m0 E) m' -> wmono bsegs (o_m0 E) m' -> shz m' OD_TAB_SOW 256;
  oka_z_dig : forall m', munch (od_W E) (o_m0 E) m' -> wmono bsegs (o_m0 E) m' -> shz m' OD_TAB_DIG 3544;
  oka_z_pow5 : forall m', munch (od_W E) (o_m0 E) m' -> wmono bsegs (o_m0 E) m' -> shz m' OD_TAB_POW5 10416;
  oka_z_esc : forall m', munch (od_W E) (o_m0 E) m' -> wmono bsegs (o_m0 E) m' -> shz m' OD_TAB_ESC 256;
  oka_z_vt : forall m', munch (od_W E) (o_m0 E) m' -> wmono bsegs (o_m0 E) m' -> shz m' OD_DPI_VT 96;
  oka_z_sb : forall m', munch (od_W E) (o_m0 E) m' -> wmono bsegs (o_m0 E) m' -> shz m' (o_SB E) (o_CAP E);
  oka_z_impl : forall m', munch (od_W E) (o_m0 E) m' -> wmono bsegs (o_m0 E) m' -> shz m' (o_IMPL E) 96;
  oka_z_par : forall m', munch (od_W E) (o_m0 E) m' -> wmono bsegs (o_m0 E) m' -> shz m' (oa_F E + 96) 56;
  oka_z_buf : forall m', munch (od_W E) (o_m0 E) m' -> wmono bsegs (o_m0 E) m' -> shz m' (o_COPY E) (o_BUF E - o_COPY E + o_len E + 57);
  oka_z_idx : forall m', munch (od_W E) (o_m0 E) m' -> wmono bsegs (o_m0 E) m' -> shz m' (o_IDX E) (4 * (o_n E + 3));
  oka_z_doc : forall m', munch (od_W E) (o_m0 E) m' -> wmono bsegs (o_m0 E) m' -> shz m' (oa_F E + 192) 64
}.

Definition ODINVc (E : oaenv) (vs v88 v144 v152 v240 v312 v336 v352 : Z) (c96 c104 c224 c232 c272 c304 c320 c376 : cell)
                  (st : ost) (m1 : mem) : Prop :=
  rw_cells bsegs m1 (oa_S1 E + 8) (fr_k8 E v88) /\
  rw_cells bsegs m1 (oa_S1 E + 96) (fr_k96 E v144 v152 c96 c104 c224 c232) /\
  rw_cells bsegs m1 (oa_S1 E + 240) (fr_k240 E vs v240 v312 v336 v352 c272 c304 c320 c376) /\
  (exists j241 j252, rw_cells bsegs m1 (oa_F E + 192) (iter_cells E st j241 j252)) /\
  rw_cells bsegs m1 (oa_F E + 96) (od_parser_cells E) /\
  rw_cells bsegs m1 (o_IMPL E) (dpi_cells E) /\
  (exists ws, u32arr bsegs m1 (o_IDX E) ws /\ idx_ok E ws) /\
  bytes_at bsegs m1 (o_BUF E) (padded_bytes (o_bs E)) /\
  wr_at bsegs m1 (o_SB E) (o_CAP E) /\
  ro_cells bsegs m1 OD_DPI_VT od_vt_cells /\
  ro_cells bsegs m1 OD_GOT_TABS od_got_cells /\
  mem_inv bsegs m1 /\ munch (od_W E) (o_m0 E) m1 /\ wmono bsegs (o_m0 E) m1 /\
  stk bsegs m1 (o_lo E) (oa_S1 E).
Definition ODINVg (E : oaenv) (vs v88 v144 v152 v240 v312 v336 v352 : Z) (st : ost) (m1 : mem) : Prop :=
  exists j96 j104 j224 j232 j272 j304 j320 j376,
    ODINVc E vs v88 v144 v152 v240 v312 v336 v352 (CB 8 j96) (CB 8 j104) (CB 8 j224) (CB 8 j232) (CB 8 j272) (CB 8 j304) (CB 8 j320) (CB 8 j376) st m1.

Notation ODINVh E v336 v352 st m1 := (ODINVg E (oa_F E + 192) 0 2 1 (o_IDX E) 1 v336 v352 st m1).
Notation ODINVp E v352 st m1 := (ODINVg E (oa_F E + 192) 0 2 1 (o_IDX E) 1 1 v352 st m1).
Notation ODINV E st m1 := (ODINVg E (oa_F E + 192) 0 2 1 (o_IDX E) 1 1 (o_IDX E + 4 * o_pos st) st m1).

Notation ODST E pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m :=
  (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2
           (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 (Z_to_bv 64 (oa_F E + 224)) (Z_to_bv 64 (o_act E)) xs5 xs6
           (Z_to_bv 64 2147450880) (Z_to_bv 64 (oa_F E + 228)) (Z_to_bv 64 4)
           xs10 xs11 xt3 xt4 xt5 xt6)
      xF (Z_to_bv 64 pc) xfc None m (seg_rom bsegs)).

Definition od_exit_k (E : oaenv) (Q : machine_state -> Prop) : Prop :=
  forall st vs v88 v144 v152 v240 v312 v336 v352 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs8 xs9 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    frm0 xfc -> ODINVg E vs v88 v144 v152 v240 v312 v336 v352 st m1 ->
    evt bsegs Q (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2
                         (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 2147450880) xs8 xs9 (Z_to_bv 64 (oa_F E + 32)) xs11 xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 OD_EXIT) xfc None m1 (seg_rom bsegs)).

Definition od_head_pre (E : oaenv) (st0 st : ost) : Prop :=
  od_next_ok (o_bs E) (o_idxs E) 1 st0 st \/ od_dead (o_n E) st.
Definition od_head_k (E : oaenv) (Q : machine_state -> Prop) (st0 : ost) : Prop :=
  forall st v336 v352 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs5 xs6 xt3 xt4 xt5 xt6 xF xfc m1,
    od_head_pre E st0 st -> frm0 xfc -> ODINVh E v336 v352 st m1 ->
    evt bsegs Q (ODST E OD_HEAD xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 (oa_F E + 200))
                      (Z_to_bv 64 1) xs5 xs6 (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 (oa_F E + 192)) xt3 xt4 xt5 xt6 xF xfc m1).

Definition od_plus_k (E : oaenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall st' v352 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    od_arm_out (o_bs E) (o_idxs E) st st' -> frm0 xfc -> ODINVp E v352 st' m1 ->
    evt bsegs Q (ODST E OD_PLUS xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).

Definition arm_k (E : oaenv) (Q : machine_state -> Prop) (entry : Z) (st : ost) : Prop :=
  forall xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1,
    frm0 xfc -> ODINV E st m1 ->
    evt bsegs Q (ODST E entry xra xt0 xt1 xt2 (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      xs2 xs5 xs6 xs10 (Z_to_bv 64 (oa_F E + 192)) xt3 (Z_to_bv 64 2) xt5 xt6 xF xfc m1).

Definition arm_stmt (E : oaenv) (entry : Z) : Prop :=
  forall (Q : machine_state -> Prop) st,
    tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET ->
    od_head_ok (o_bs E) (o_idxs E) 1 st ->
    od_plus_k E Q st ->
    arm_k E Q entry st.

Definition od_shb (E : oaenv) : Prop :=
  forall m', munch (od_W E) (o_m0 E) m' -> wmono bsegs (o_m0 E) m' ->
    ro_cells bsegs m' g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)] /\
    ro_cells bsegs m' g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)].

Ltac od_open_invc H :=
  let j241 := fresh "j241" in let j252 := fresh "j252" in
  let ws := fresh "ws" in
  destruct H as (FR8 & FR96 & FR240
                 & (j241 & j252 & ITER) & PARS & DPI & (ws & IDXA & IDXOK) & BUFRO & SBW & VT & GOT & MI & MU & WM & ST);
  unfold fr_k8 in FR8; unfold fr_k96 in FR96; unfold fr_k240 in FR240; unfold iter_cells in ITER; unfold dpi_cells in DPI;
  unfold od_parser_cells in PARS;
  unfold od_vt_cells, OD_DPI_VT in VT; unfold od_got_cells, OD_GOT_TABS in GOT; unfold od_W in MU;
  unfold wz in FR8, FR96, FR240, ITER, PARS, DPI;
  let IDXL := fresh "IDXL" in let IDXF := fresh "IDXF" in destruct IDXOK as [IDXL IDXF];
  lazymatch type of BUFRO with
  | bytes_at _ _ _ (padded_bytes ?bs) => let PBL := fresh "PBL" in pose proof (padded_bytes_blen bs) as PBL
  end.
Ltac od_open_inv H :=
  let j96 := fresh "j96" in let j104 := fresh "j104" in let j224 := fresh "j224" in let j232 := fresh "j232" in
  let j272 := fresh "j272" in let j304 := fresh "j304" in let j320 := fresh "j320" in let j376 := fresh "j376" in
  destruct H as (j96 & j104 & j224 & j232 & j272 & j304 & j320 & j376 & H);
  od_open_invc H.

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

Ltac od_forget_k H k :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?l =>
      let pre := eval cbv [firstn] in (firstn k l) in
      let rest := eval cbv [skipn] in (skipn k l) in
      lazymatch rest with
      | C8 ?v :: ?post => apply (rw_cells_forget_C8 s m A pre v post) in H; cbn [app] in H
      | _ => idtac
      end
  end.
Ltac od_scrub_in m :=
  repeat match goal with
  | H : rw_cells _ m (oa_S1 _ + 96) (C8 _ :: _) |- _ => od_forget_k H 0%nat
  | H : rw_cells _ m (oa_S1 _ + 96) (_ :: C8 _ :: _) |- _ => od_forget_k H 1%nat
  | H : rw_cells _ m (oa_S1 _ + 96) (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C8 _ :: _) |- _ =>
      od_forget_k H 16%nat
  | H : rw_cells _ m (oa_S1 _ + 96) (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C8 _ :: _) |- _ =>
      od_forget_k H 17%nat
  | H : rw_cells _ m (oa_S1 _ + 240) (_ :: _ :: _ :: _ :: C8 _ :: _) |- _ => od_forget_k H 4%nat
  | H : rw_cells _ m (oa_S1 _ + 240) (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C8 _ :: _) |- _ => od_forget_k H 8%nat
  | H : rw_cells _ m (oa_S1 _ + 240) (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C8 _ :: _) |- _ => od_forget_k H 10%nat
  | H : rw_cells _ m (oa_S1 _ + 240) (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C8 _ :: _) |- _ =>
      od_forget_k H 17%nat
  end.
Ltac od_scrub :=
  lazymatch goal with
  | |- ODINVg _ _ _ _ _ _ _ _ _ _ ?m => od_scrub_in m
  | |- evt _ _ (MS _ _ _ _ _ ?m _) => od_scrub_in m
  end.

Ltac od_close_invc :=
  lazymatch goal with
  | |- ODINVc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      try match goal with
          | HV : o_vptr ?E = ?v, HD : rw_cells _ _ (o_IMPL ?E) (C8 ?v :: _) |- _ => rewrite <- HV in HD
          end;
      unfold ODINVc, fr_k8, fr_k96, fr_k240, iter_cells, od_parser_cells, dpi_cells, od_vt_cells, od_got_cells, od_W, OD_DPI_VT, OD_GOT_TABS, idx_ok;
      split; [od_ass|];
      split; [od_ass|];
      split; [od_ass|];
      split; [ do 2 eexists; od_ass | ];
      split; [eassumption|]; split; [eassumption|];
      split; [ eexists; split; [eassumption| split; eassumption] | ];
      split; [eassumption|]; split; [eassumption|];
      split; [eassumption|]; split; [eassumption|];
      split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.
Ltac od_close_inv :=
  lazymatch goal with
  | |- ODINVg _ _ _ _ _ _ _ _ _ _ _ => od_scrub; unfold ODINVg; do 8 eexists; od_close_invc
  | |- ODINVc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => od_close_invc
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
  adr = wa ((B + k) / 8 + 2147450880) -> ov_read_bytes bsegs m adr 1 = Some [Z_to_bv 8 0].
Proof.
  intros m B a n k adr H HB ->. apply H. apply andb_prop in HB as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma shz_read_base : forall (m : mem) B n adr, shz m B n -> (0 <? n) = true ->
  adr = wa (B / 8 + 2147450880) -> ov_read_bytes bsegs m adr 1 = Some [Z_to_bv 8 0].
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
  | Zpos _ => lazymatch X with
              | (Zpos ?L + _)%Z => od_lit_in (Zpos L) a0 n0
              | Zpos _ => od_lit_in X a0 n0
              end
  end.

Lemma shz_read_lit : forall (m : mem) a n X adr, shz m a n -> ((a <=? X) && (X <? a + n))%bool = true ->
  adr = wa (X / 8 + 2147450880) -> ov_read_bytes bsegs m adr 1 = Some [Z_to_bv 8 0].
Proof.
  intros m a n X adr H HB ->. apply H. apply andb_prop in HB as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Ltac od_load_hook :=
  match goal with
  | |- context [ov_read_bytes bsegs ?m ?a 1] =>
      let Ea := addr_expr a in
      lazymatch Ea with
      | Zpos _ =>
          let X := eval vm_compute in (8 * (Ea - 2147450880))%Z in
          lazymatch goal with
          | MU : munch ?W ?m0 m, WM : wmono bsegs ?m0 m |- _ =>
              match goal with
              | SHP : (forall m', munch W m0 m' -> wmono bsegs m0 m' -> shz m' (Zpos ?p0) (Zpos ?q0)) |- _ =>
                  od_lit_in X (Zpos p0) (Zpos q0);
                  rewrite (shz_read_lit m (Zpos p0) (Zpos q0) X a (SHP m MU WM) eq_refl eq_refl)
              end
          end
      | (?X / 8 + 2147450880)%Z =>
          lazymatch goal with
          | MU : munch ?W ?m0 m, WM : wmono bsegs ?m0 m |- _ =>
              lazymatch X with
              | (oa_F ?E + ?k)%Z =>
                  match goal with
                  | SHP : (forall m', munch W m0 m' -> wmono bsegs m0 m' -> shz m' (oa_F E + ?a0) ?n0) |- _ =>
                      rewrite (shz_read_off m (oa_F E) a0 n0 k a (SHP m MU WM) eq_refl eq_refl)
                  end
              | _ =>
                  match goal with
                  | SHP : (forall m', munch W m0 m' -> wmono bsegs m0 m' -> shz m' ?a0 ?n0) |- _ =>
                      od_serves a0 n0 X;
                      first [ rewrite (shz_read_base m a0 n0 a (SHP m MU WM) eq_refl eq_refl)
                            | rewrite (shz_read m a0 n0 X a (SHP m MU WM) ltac:(lia) ltac:(reflexivity)) ]
                  end
              end
          end
      end
  end;
  load_post.

Ltac ostep := zstep; anorm.

Ltac ochk := ostep; ostep; ostep; ostep; if_true.
Ltac ochkn := ostep; ostep; ostep; ostep; if_false.

Lemma lxor_ones64 : forall x, (0 <= x < 18446744073709551616)%Z -> Z.lxor x 18446744073709551615 = (18446744073709551615 - x)%Z.
Proof. intros x H. apply zb_lxor_ones. lia. Qed.

Ltac ulx := repeat match goal with H : context [Z.lxor _ 18446744073709551615] |- _ => rewrite lxor_ones64 in H by lia end.
Ltac utrap := let G := fresh "UG" in if_cases G; zify_cond G; [exfalso; first [lia | ulx; lia]|]; try clear G.
Ltac uok := let G := fresh "UG" in if_cases G; zify_cond G; [|exfalso; first [lia | ulx; lia]]; try clear G.

Lemma od_land7 : forall x, (x mod 8 = 0)%Z -> Z.land x 7 = 0%Z.
Proof. intros x H. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.
Lemma od_land3 : forall x, (x mod 4 = 0)%Z -> Z.land x 3 = 0%Z.
Proof. intros x H. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. exact H. Qed.
Lemma od_F_al8 : forall f k, (f mod 64 = 0)%Z -> (k mod 8 = 0)%Z -> ((f + k) mod 8 = 0)%Z.
Proof. intros f k Hf Hk. Z.div_mod_to_equations. lia. Qed.
Lemma od_F_al4 : forall f k, (f mod 64 = 0)%Z -> (k mod 4 = 0)%Z -> ((f + k) mod 4 = 0)%Z.
Proof. intros f k Hf Hk. Z.div_mod_to_equations. lia. Qed.
Lemma od_idx_al4 : forall a k, (a mod 8 = 0)%Z -> ((a + 4 * k) mod 4 = 0)%Z.
Proof. intros a k Ha. Z.div_mod_to_equations. lia. Qed.
Lemma od_land7_F : forall f k, (f mod 64 = 0)%Z -> (k mod 8 = 0)%Z -> Z.land (f + k) 7 = 0%Z.
Proof. intros f k Hf Hk. apply od_land7. apply od_F_al8; assumption. Qed.
Lemma od_land3_F : forall f k, (f mod 64 = 0)%Z -> (k mod 4 = 0)%Z -> Z.land (f + k) 3 = 0%Z.
Proof. intros f k Hf Hk. apply od_land3. apply od_F_al4; assumption. Qed.
Lemma od_land3_idx : forall a k, (a mod 8 = 0)%Z -> Z.land (a + 4 * k) 3 = 0%Z.
Proof. intros a k Ha. apply od_land3. apply od_idx_al4. exact Ha. Qed.
Lemma od_land3_idx4 : forall a k j, (a mod 8 = 0)%Z -> (j mod 4 = 0)%Z -> Z.land (a + 4 * k + j) 3 = 0%Z.
Proof. intros a k j Ha Hj. apply od_land3. Z.div_mod_to_equations. lia. Qed.
Ltac ual :=
  repeat match goal with
  | H : (?f mod 64 = 0)%Z |- context [Z.land (?f + ?k) 7] => rewrite (od_land7_F f k H eq_refl)
  | H : (?f mod 64 = 0)%Z |- context [Z.land (?f + ?k) 3] => rewrite (od_land3_F f k H eq_refl)
  | H : (?a mod 8 = 0)%Z |- context [Z.land (?a + 4 * ?k) 3] => rewrite (od_land3_idx a k H)
  | H : (?a mod 8 = 0)%Z |- context [Z.land (?a + 4 * ?k + ?j) 3] => rewrite (od_land3_idx4 a k j H eq_refl)
  | H : (?x mod 8 = 0)%Z |- context [Z.land ?x 7] => rewrite (od_land7 x H)
  | H : (?x mod 4 = 0)%Z |- context [Z.land ?x 3] => rewrite (od_land3 x H)
  end.
Ltac ual7 x := rewrite (od_land7 x) by (Z.div_mod_to_equations; lia).
Ltac ual3 x := rewrite (od_land3 x) by (Z.div_mod_to_equations; lia).

Lemma b2z_pos : forall x, (0 < x)%Z -> Z.b2z (0 <? x) = 1%Z.
Proof. intros x H. rewrite (proj2 (Z.ltb_lt 0 x) H). reflexivity. Qed.
Lemma b2z_lt1 : forall x, (0 < x)%Z -> Z.b2z (x <? 1) = 0%Z.
Proof. intros x H. rewrite (proj2 (Z.ltb_ge x 1)) by lia. reflexivity. Qed.
Ltac unz := rewrite ?b2z_pos, ?b2z_lt1 by lia.

Ltac ultb :=
  repeat match goal with
  | |- context [Z.b2z (?a <? ?b)] => first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
  end; cbn [Z.b2z].

Ltac od_al F64 :=
  lazymatch type of F64 with
  | (?f mod 64 = 0)%Z =>
      let A8 := fresh "A8" in let A8P := fresh "A8P" in let A4E := fresh "A4E" in let A4D := fresh "A4D" in
      assert (A8 : ((f + 192) mod 8 = 0)%Z) by (apply od_F_al8; [exact F64| reflexivity]);
      assert (A8P : ((f + 200) mod 8 = 0)%Z) by (apply od_F_al8; [exact F64| reflexivity]);
      assert (A4E : ((f + 224) mod 4 = 0)%Z) by (apply od_F_al4; [exact F64| reflexivity]);
      assert (A4D : ((f + 228) mod 4 = 0)%Z) by (apply od_F_al4; [exact F64| reflexivity])
  end.
