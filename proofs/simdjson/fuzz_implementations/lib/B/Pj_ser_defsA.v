(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Pj_rtkA Pj_defsA Pj_cpsA Pj_copyA Pj_ser_trefA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition PJ_HEAD_A : Z := 0xb8104.
Definition PJ_ITEM_A : Z := 0xb81dc.
Definition PJ_KEY_A : Z := 0xb8234.
Definition PJ_DISP_A : Z := 0xb8f14.
Definition PJ_JTAB_A : Z := 0x23944.
Definition PJ_STR_A : Z := 0xb9a50.
Definition PJ_FALSE_A : Z := 0xb927c.
Definition PJ_NULL_A : Z := 0xb9634.
Definition PJ_TRUE_A : Z := 0xb9520.
Definition PJ_I64_A : Z := 0xb8f7c.
Definition PJ_U64_A : Z := 0xb974c.
Definition PJ_DBL_A : Z := 0xb9f30.
Definition PJ_ARR_A : Z := 0xb90b8.
Definition PJ_OBJ_A : Z := 0xb9370.
Definition PJ_BIGINT_A : Z := 0xb9860.
Definition PJ_ENDS_A : Z := 0xba6f4.
Definition PJ_ITOA_A : Z := 0xb6f2c.
Definition PJ_UTOA_A : Z := 0xb720c.
Definition PJ_STR_FALSE_A : Z := 0x23a40.
Definition PJ_STR_TRUE_A : Z := 0x23a20.
Definition PJ_STR_NULL_A : Z := 0x23a00.
Definition PJ_RO176_A : Z := 0x239e0.
Definition PJ_RO184_A : Z := 0x239c0.
Definition END125 : Z := 125 * 2 ^ 56.
Definition END93 : Z := 93 * 2 ^ 56.
Definition TOPMASK : Z := 255 * 2 ^ 56.
Definition PJ_AVS_A : Z := 0xba6e8.
Definition PJ_AV_A : Z := 0xba6ec.
Definition PJ_AV1_A : Z := 0xba6f0.
Definition PJ_EXIT_A : Z := 0xbaa18.
Definition PJ_TRAP_A : Z := 0xbab44.
Definition PJ_NE_TAB_A : Z := 0x23a80.
Definition PJ_ESC_TAB_A : Z := 0x23b80.
Definition MASK32 : Z := 4294967295.
Definition MASK56 : Z := 72057594037927935.

Definition ser_shpatZ : list Z :=
  [241; 241; 241; 241; 248; 248; 248; 248; 248; 242; 242; 242; 242; 242; 248; 248; 248; 242; 242; 242; 242; 242;
   248; 248; 248; 242; 242; 242; 242; 242; 248; 242; 242; 242; 248; 242; 242; 242; 0; 0; 243; 243; 243; 243].
Definition ser_shpatA : list byte := map (Z_to_bv 8) ser_shpatZ.
Lemma ser_shpatA_length : length ser_shpatA = 44%nat.
Proof. reflexivity. Qed.

Record serI : Type := mkSI {
  si_q : Z;  si_dd : Z;  si_f : Z;
  si_j : Z;  si_c' : Z;
  si_R : Z;
  si_ra : word;  si_gp : word;
  si_s0 : word;  si_s1 : word;  si_s2 : word;  si_s3 : word;  si_s4 : word;  si_s5 : word;
  si_s6 : word;  si_s7 : word;  si_s8 : word;  si_s9 : word;  si_s10 : word;  si_s11 : word;
  si_fr : list (Z * nat);
  si_sp0 : Z;
  si_m0 : mem }.

Definition si_b (I : serI) : Z := si_q I - 416 - si_dd I.

Notation T5A E := ((pa_SB E + 72) / 8).
Notation S64A E := ((pa_SB E + 64) / 8).
Notation S80A E := ((pa_SB E + 80) / 8).
Notation SHDOCA E := (pa_DOC E / 8 + 2147450880).
Notation SHFA I := (si_f I / 8 + 2147450880).

Definition ser_savedA (I : serI) : list cell :=
  [C8 (si_s11 I); C8 (si_s10 I); C8 (si_s9 I); C8 (si_s8 I); C8 (si_s7 I); C8 (si_s6 I); C8 (si_s5 I); C8 (si_s4 I);
   C8 (si_s3 I); C8 (si_s2 I); C8 (si_s1 I); C8 (si_s0 I); C8 (si_ra I)].

Record xjA : Type := mkXJ { xj0 : word; xj8 : word; xj16 : word; xj24 : word; xj80 : word; xj208 : word; xj216 : word; xj288 : word; xj296 : word }.

Record wkA : Type := mkWK { w168 : word; w176 : word; w184 : word; w224 : word; w248 : word; w256 : word; w264 : word }.
Definition wkI (E : pjenvA) (x224 : word) : wkA :=
  mkWK (wz PJ_ESC_TAB_A) (wz PJ_RO176_A) (wz PJ_RO184_A) x224 (wz (S64A E)) (wz (T5A E)) (wz (S80A E)).
Definition wkC (E : pjenvA) : wkA := wkI E (wz END125).
Definition lnotw (z : Z) : word := wz (Z.lnot z mod 2^64).
Definition ser_frameA (E : pjenvA) (I : serI) (w : wkA) (x : xjA) : list cell :=
  [C8 (xj0 x); C8 (xj8 x); C8 (xj16 x); C8 (xj24 x); C8 (lnotw (si_f I + 304)); C8 (wz (si_f I + 241)); C8 (lnotw (si_f I + 241));
   C8 (wz (si_f I + 32)); C8 (wz (si_f I + 176)); C8 (wz (si_f I + 112)); C8 (xj80 x); C8 (wz 1); C8 (wz 1); C8 (wz (si_f I));
   C8 (wz (pa_DOC E)); C8 (wz (pa_DOC E + 8)); C8 (wz (si_f I + 304)); C8 (wz (si_f I + 273)); C8 (lnotw (si_f I + 273)); C8 (wz MASK56);
   C8 (wz (si_f I)); C8 (w168 w); C8 (w176 w); C8 (w184 w); C8 (wz (pa_SB E)); C8 (wz (SHFA I)); C8 (xj208 x); C8 (xj216 x);
   C8 (w224 w); C8 (wz (pa_SB E + 64)); C8 (wz (pa_SB E + 80)); C8 (w248 w); C8 (w256 w); C8 (w264 w); C8 (wz END93); C8 (wz TOPMASK);
   C8 (xj288 x); C8 (xj296 x); C8 (wz (si_f I))].

Lemma ser_frameA_size : forall E I w x, cells_size (ser_frameA E I w x) = 312%nat.
Proof. intros. reflexivity. Qed.
Lemma ser_savedA_size : forall I, cells_size (ser_savedA I) = 104%nat.
Proof. intros. reflexivity. Qed.

Lemma fs3 : fs_size 3 = 512.
Proof. reflexivity. Qed.
Lemma fs3s : shad (0 + fs_size 3) = SHB + 64.
Proof. reflexivity. Qed.

Section WithRT.
Variable RT : rt_sig.

Record sctxA (E : pjenvA) (D : nat) (I : serI) : Prop := mkSC {
  c_dd : si_dd I = 0 \/ si_dd I = 16;
  c_b32 : si_b I mod 32 = 0;
  c_q16 : si_q I mod 16 = 0;
  c_lo : pa_lo E + ser_needA D <= si_q I;
  c_qtop : si_q I + 16 <= USTACK_TOP;
  c_sp0 : si_sp0 I - STACK_WIN <= pa_lo E /\ 0x7fff80000000 <= si_sp0 I;

  c_f : 0 < si_f I /\ si_f I mod 64 = 0 /\ SEGTOP_A <= si_f I /\ si_f I + 512 <= pa_lo E;
  c_fF : si_f I + 512 <= pa_F E \/ pa_F E + fs_size (pa_kF E) <= si_f I;

  c_f_shf : si_f I + 512 <= SHFA I \/ SHFA I + 64 <= si_f I;
  c_F_shf : pa_F E + fs_size (pa_kF E) <= SHFA I \/ SHFA I + 64 <= pa_F E;
  c_f_shF : si_f I + 512 <= pa_F E / 8 + 2147450880 \/ (pa_F E + fs_size (pa_kF E)) / 8 + 2147450880 <= si_f I;
  c_F_shF : pa_F E + fs_size (pa_kF E) <= pa_F E / 8 + 2147450880 \/ (pa_F E + fs_size (pa_kF E)) / 8 + 2147450880 <= pa_F E;

  c_j : 1 <= si_j I <= pa_n E;
  c_c' : 0 <= si_c' I <= pa_sn E;
  c_R : 0 <= si_R I;

  c_F4 : In (pa_F E, pa_kF E) (si_fr I);
  c_fr3 : fcount 3 (si_fr I) + Z.of_nat D + 1 <= FRAMES_MAX3;
  c_frl : Z.of_nat (length (si_fr I)) + 2 * Z.of_nat D + 2 <= FRAMES_TOT;
  c_L : Z.of_nat (length (pa_L E)) + 3 <= LIVE_MAX }.

Lemma sctx_out : forall E D I, pjenvA_ok E -> sctxA E D I -> 41 * (si_j I - 1) + 6 * si_c' I + 2 <= PJ_OUTMAX (pa_len E).
Proof.
  intros E D I OK CX. pose proof (ok_sizes E OK) as [HT HS].
  eapply (pj_out_bound (pa_len E) (pa_n E) (pa_sn E) (si_j I) (si_c' I)); [apply (ok_len E OK)| exact HT| exact HS| | | lia].
  - pose proof (c_j E D I CX). lia.
  - pose proof (c_c' E D I CX). lia.
Qed.

Definition CREDA (E : pjenvA) (I : serI) (Σc : rts RT) (X : Z) (st : sbA) : Prop :=
  si_R I + X + pj_psi (pa_len E) st <= rt_credit RT Σc.

Lemma CREDA_le : forall E I Σc X X' st, CREDA E I Σc X st -> X' <= X -> CREDA E I Σc X' st.
Proof. intros E I Σc X X' st H HX. unfold CREDA in *. lia. Qed.
Lemma CREDA_sized : forall E I Σc X st n, CREDA E I Σc X st -> CREDA E I Σc X (sb_sized st n).
Proof. intros E I Σc X st n H. unfold CREDA in *. rewrite pj_psi_sized. exact H. Qed.

Definition sb_pureA (E : pjenvA) (st : sbA) : Prop :=
  (0 <= sa_k st /\ 64 * 2 ^ (sa_k st) <= sa_cap st <= PJ_CAPMAX (pa_len E))
  /\ (if sa_heap st then 0 < sa_buf st /\ sa_buf st mod 16 = 0 /\ sa_buf st + sa_cap st <= pa_lo E
      else sa_buf st = pa_SB E /\ sa_cap st = 64 /\ sa_k st = 0).

Definition serWA (E : pjenvA) (I : serI) (st : sbA) : list (Z * Z) :=
  [(si_b I, si_q I); (sa_buf st, sa_buf st + sa_cap st); (pa_SB E, pa_SB E + 88); (si_f I, si_f I + 320);
   (SHFA I, SHFA I + 64)].

Definition SREFA (E : pjenvA) (I : serI) (Σc : rts RT) (st : sbA) (m : mem) : Prop :=
  ART RT Σc m
  /\ rt_live RT Σc = sbchunkA st ++ pa_L E
  /\ rt_frames RT Σc = (si_f I, 3%nat) :: si_fr I
  /\ rt_sp0 RT Σc = si_sp0 I
  /\ DOCREPA E m
  /\ bytes_at bsegs m (shad (pa_SB E)) (repeat z8 11)
  /\ sb_pureA E st
  /\ rt_pres_fp (pa_L E) (si_fr I) (si_q I) [(pa_SB E, pa_SB E + 88)] (si_m0 I) m.

Definition SCURA (E : pjenvA) (I : serI) (w : wkA) (x : xjA) (shp isobj : list byte) (st : sbA) (m : mem) : Prop :=
  rw_cells bsegs m (si_b I) (ser_frameA E I w x)
  /\ stk bsegs m (si_b I + 312) (si_q I - 104)
  /\ rw_cells bsegs m (si_q I - 104) (ser_savedA I)
  /\ (exists h0 h1 h2, rw_cells bsegs m (si_f I) [C8 h0; C8 h1; C8 h2])
  /\ stk bsegs m (si_f I + 24) (si_f I + 304)
  /\ u8arr bsegs m (si_f I + 304) isobj /\ length isobj = 16%nat
  /\ u8arr bsegs m (SHFA I) shp /\ length shp = 44%nat /\ stk bsegs m (SHFA I + 44) (SHFA I + 64)
  /\ rw_cells bsegs m (pa_SB E + 64) [C8 (wz (sa_buf st)); C8 (wz (sa_size st)); C8 (wz (sa_cap st))]
  /\ 0 <= sa_size st <= sa_cap st
  /\ stk bsegs m (sa_buf st) (sa_buf st + sa_cap st)
  /\ stk bsegs m (pa_SB E) (pa_SB E + 64)
  /\ mem_inv bsegs m
  /\ stk bsegs m (pa_lo E) (si_b I).

Definition SERMA (E : pjenvA) (I : serI) (w : wkA) (x : xjA) (shp isobj : list byte) (Σc : rts RT) (st : sbA) (m : mem) : Prop :=
  SREFA E I Σc st m /\ SCURA E I w x shp isobj st m.

Definition SERMH (E : pjenvA) (I : serI) (isobj : list byte) (Σc : rts RT) (st : sbA) (m : mem) : Prop :=
  exists x w, SERMA E I w x ser_shpatA isobj Σc st m.
Definition SERMK (E : pjenvA) (I : serI) (isobj : list byte) (Σc : rts RT) (st : sbA) (m : mem) : Prop :=
  exists x x224, SERMA E I (wkI E x224) x ser_shpatA isobj Σc st m.
Definition SERMC (E : pjenvA) (I : serI) (isobj : list byte) (Σc : rts RT) (st : sbA) (m : mem) : Prop :=
  exists x, SERMA E I (wkC E) x ser_shpatA isobj Σc st m.
Lemma SERMK_of_C : forall E I isobj Σc st m, SERMC E I isobj Σc st m -> SERMK E I isobj Σc st m.
Proof. intros E I isobj Σc st m [x H]. exists x, (wz END125). exact H. Qed.
Lemma SERMH_of_K : forall E I isobj Σc st m, SERMK E I isobj Σc st m -> SERMH E I isobj Σc st m.
Proof. intros E I isobj Σc st m (x & x224 & H). exists x, (wkI E x224). exact H. Qed.

Definition kbyte (k : bool) : byte := Z_to_bv 8 (if k then 1 else 0).
Definition kinds_rel (ks : list bool) (isobj : list byte) : Prop :=
  nth_error isobj 0 = Some (Z_to_bv 8 0)
  /\ forall j k, nth_error (rev ks) j = Some k -> nth_error isobj (j + 1) = Some (kbyte k).

Lemma kinds_rel_push : forall ks isobj k, kinds_rel ks isobj -> (length ks + 1 < length isobj)%nat ->
  kinds_rel (k :: ks) (upd isobj (length ks + 1) (kbyte k)).
Proof.
  intros ks isobj k [H0 H] HL. split.
  - rewrite nth_error_upd_other by lia. exact H0.
  - intros j x Hj. cbn [rev] in Hj. destruct (Nat.lt_ge_cases j (length ks)) as [L|L].
    + rewrite nth_error_app1 in Hj by (rewrite length_rev; exact L). rewrite nth_error_upd_other by lia. apply H. exact Hj.
    + rewrite nth_error_app2 in Hj by (rewrite length_rev; exact L). rewrite length_rev in Hj.
      destruct (j - length ks)%nat as [|q] eqn:Eq; [| destruct q; discriminate].
      cbn in Hj. inversion Hj; subst x. replace j with (length ks) by lia. apply nth_error_upd_same. exact HL.
Qed.
Lemma kinds_rel_pop : forall k ks isobj, kinds_rel (k :: ks) isobj -> kinds_rel ks isobj.
Proof.
  intros k ks isobj [H0 H]. split; [exact H0|]. intros j x Hj. apply H. cbn [rev]. rewrite nth_error_app1; [exact Hj|].
  apply nth_error_Some. congruence.
Qed.
Lemma kinds_rel_top : forall k ks isobj, kinds_rel (k :: ks) isobj -> nth_error isobj (length ks + 1) = Some (kbyte k).
Proof.
  intros k ks isobj [_ H]. apply (H (length ks) k). cbn [rev]. rewrite nth_error_app2 by (rewrite length_rev; lia).
  rewrite length_rev, Nat.sub_diag. reflexivity.
Qed.

Definition item_okA (E : pjenvA) (ks : list bool) (d0 : nat) : Z -> Z -> Z -> Z -> Prop :=
  match ks with
  | [] => elemS (pa_T E) (pa_S E) (pa_sn E) ck_any d0
  | k :: _ => itemS (pa_T E) (pa_S E) (pa_sn E) k d0
  end.

End WithRT.

Notation SSTA I pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m :=
  (MS (mkR xra (Z_to_bv 64 (si_b I)) (si_gp I) (Z_to_bv 64 TPV_A) xt0 xt1 xt2 (Z_to_bv 64 (si_q I)) (Z_to_bv 64 (si_b I))
           xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
      F (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).

Notation LSTA E I pc i dp xs3 xs7 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m :=
  (SSTA I pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
        (Z_to_bv 64 (pa_SB E + 72)) xs3 (Z_to_bv 64 (pa_SB E + 64)) (Z_to_bv 64 (SHFA I)) (Z_to_bv 64 i) xs7 (Z_to_bv 64 (pa_SB E)) (Z_to_bv 64 2147450880)
        (Z_to_bv 64 dp) (Z_to_bv 64 (pa_DOC E))
        xt3 xt4 xt5 xt6 F fc m).

Section Conts.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).

Definition av_KA (E : pjenvA) (I : serI) (K : config -> Prop) (isobj : list byte) (il dp X A : Z) : Prop :=
  forall (Σ' : rts RT) (st' : sbA) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32)
         (xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    SERMC RT E I isobj Σ' st' m' -> frm0 fc' -> sa_size st' <= A -> CREDA RT E I Σ' X st' ->
    aevt Σ' K (LSTA E I PJ_AV_A il dp xs3 (wz (pa_SB E + 80)) xt5
                 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F' fc' m').

Definition disp_KA (E : pjenvA) (I : serI) (K : config -> Prop) (isobj : list byte) (i dp X A : Z) : Prop :=
  forall (Σ' : rts RT) (st' : sbA) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32)
         (xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    SERMK RT E I isobj Σ' st' m' -> frm0 fc' -> sa_size st' <= A -> CREDA RT E I Σ' X st' ->
    aevt Σ' K (LSTA E I PJ_DISP_A i dp xs3 (wz PJ_NE_TAB_A) xt5
                 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F' fc' m').

Definition exit_KA (E : pjenvA) (I : serI) (K : config -> Prop) : Prop :=
  forall (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
    SERMC RT E I isobj Σ st m -> frm0 fc -> sa_size st <= 41 * (si_j I - 1) + 6 * si_c' I + 2 -> CREDA RT E I Σ 0 st ->
    aevt Σ K (SSTA I PJ_EXIT_A xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 (wz (SHFA I)) xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m).

Definition key_stmtA : Prop :=
  forall (E : pjenvA) (D : nat) (I : serI) (K : config -> Prop) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
         (F : bvmap 5 word) (fc : bv 32) (i c l dp A X : Z)
         (xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    pjenvA_ok E -> sctxA E D I -> SERMK RT E I isobj Σ st m -> frm0 fc ->
    1 <= i < pa_n E -> pa_T E i = tword t_str c -> str_at (pa_S E) (pa_sn E) c l -> 0 <= dp <= 15 ->
    sa_size st <= A -> A + (3 + 6 * l) <= PJ_OUTMAX (pa_len E) -> CREDA RT E I Σ X st -> 0 <= X ->
    disp_KA E I K isobj (i + 1) dp X (A + (3 + 6 * l)) ->
    aevt Σ K (LSTA E I PJ_KEY_A i dp xs3 (wz PJ_NE_TAB_A) xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).

Definition str_stmtA : Prop :=
  forall (E : pjenvA) (D : nat) (I : serI) (K : config -> Prop) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
         (F : bvmap 5 word) (fc : bv 32) (i c l dp A X : Z)
         (xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    pjenvA_ok E -> sctxA E D I -> SERMC RT E I isobj Σ st m -> frm0 fc ->
    1 <= i < pa_n E -> pa_T E i = tword t_str c -> str_at (pa_S E) (pa_sn E) c l -> 0 <= dp <= 15 ->
    sa_size st <= A -> A + (2 + 6 * l) <= PJ_OUTMAX (pa_len E) -> CREDA RT E I Σ X st -> 0 <= X ->
    av_KA E I K isobj i dp X (A + (2 + 6 * l)) ->
    aevt Σ K (LSTA E I PJ_STR_A i dp xs3 (wz PJ_NE_TAB_A) xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).

Definition num_stmtA (pc t : Z) : Prop :=
  forall (E : pjenvA) (D : nat) (I : serI) (K : config -> Prop) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
         (F : bvmap 5 word) (fc : bv 32) (i dp A X : Z)
         (xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    pjenvA_ok E -> sctxA E D I -> SERMC RT E I isobj Σ st m -> frm0 fc ->
    1 <= i -> i + 1 < pa_n E -> ty (pa_T E) i = t -> 0 <= dp <= 15 ->
    sa_size st <= A -> A + 20 <= PJ_OUTMAX (pa_len E) -> CREDA RT E I Σ X st -> 1 <= X ->
    av_KA E I K isobj (i + 1) dp (X - 1) (A + 20) ->
    aevt Σ K (LSTA E I pc i dp xs3 (wz (pa_SB E + 80)) xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
Definition i64_stmtA : Prop := num_stmtA PJ_I64_A t_i64.
Definition u64_stmtA : Prop := num_stmtA PJ_U64_A t_u64.

Definition dbl_stmtA : Prop :=
  forall (E : pjenvA) (D : nat) (I : serI) (K : config -> Prop) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
         (F : bvmap 5 word) (fc : bv 32) (i dp A X : Z)
         (xs3 xs7 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    pjenvA_ok E -> sctxA E D I -> SERMC RT E I isobj Σ st m -> frm0 fc ->
    1 <= i -> i + 1 < pa_n E -> ty (pa_T E) i = t_dbl -> 0 <= dp <= 15 ->
    sa_size st <= A -> A + 27 <= PJ_OUTMAX (pa_len E) -> CREDA RT E I Σ X st -> 1 <= X ->
    av_KA E I K isobj (i + 1) dp (X - 1) (A + 27) ->
    aevt Σ K (LSTA E I PJ_DBL_A i dp xs3 xs7 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).

Definition atom_stmtA (pc N : Z) : Prop :=
  forall (E : pjenvA) (D : nat) (I : serI) (K : config -> Prop) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
         (F : bvmap 5 word) (fc : bv 32) (i dp A X : Z)
         (xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    pjenvA_ok E -> sctxA E D I -> SERMC RT E I isobj Σ st m -> frm0 fc -> 0 <= dp <= 15 ->
    sa_size st <= A -> A + N <= PJ_OUTMAX (pa_len E) -> CREDA RT E I Σ X st -> 0 <= X ->
    av_KA E I K isobj i dp X (A + N) ->
    aevt Σ K (LSTA E I pc i dp xs3 (wz (pa_SB E + 80)) xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).
Definition true_stmtA : Prop := atom_stmtA PJ_TRUE_A 4.
Definition false_stmtA : Prop := atom_stmtA PJ_FALSE_A 5.
Definition null_stmtA : Prop := atom_stmtA PJ_NULL_A 4.

Notation RESTA E := (rest_ok (pa_T E) (pa_S E) (pa_sn E)).

Definition head_stmtA (E : pjenvA) (I : serI) (K : config -> Prop) (D : nat) (fu : nat) : Prop :=
  forall (d0 : nat) (ks : list bool) (i i2 c c2 : Z) (after : bool) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
         (F : bvmap 5 word) (fc : bv 32) (w : wkA) (x : xjA)
         (xs3 xt5 xra xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    si_j I - i <= Z.of_nat fu -> (d0 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
    item_okA E ks d0 i i2 c c2 -> RESTA E d0 ks i2 c2 (si_j I) (si_c' I) -> (ks = [] -> after = false) -> 1 <= i -> 0 <= c ->
    SERMA RT E I w x ser_shpatA isobj Σ st m -> frm0 fc -> sa_size st <= 41 * (i - 1) + 6 * c + (if after then 2 else 3) ->
    CREDA RT E I Σ (2 * (si_j I - i) - 1) st ->
    aevt Σ K (LSTA E I PJ_HEAD_A i (Z.of_nat (length ks)) xs3 (wz (pa_SB E + 80)) xt5
                 xra xt0 xt1 xt2 xa0 (wz (Z.b2z after)) xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).

Definition disp_stmtA (E : pjenvA) (I : serI) (K : config -> Prop) (D : nat) (fu : nat) : Prop :=
  forall (d0 : nat) (ks : list bool) (i i2 c c2 : Z) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
         (F : bvmap 5 word) (fc : bv 32)
         (xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    si_j I - i <= Z.of_nat fu -> (d0 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
    elemS (pa_T E) (pa_S E) (pa_sn E) ck_any d0 i i2 c c2 -> RESTA E d0 ks i2 c2 (si_j I) (si_c' I) -> 1 <= i -> 0 <= c ->
    SERMK RT E I isobj Σ st m -> frm0 fc -> sa_size st <= 41 * (i - 1) + 6 * c + 3 ->
    CREDA RT E I Σ (2 * (si_j I - i) - 1) st ->
    aevt Σ K (LSTA E I PJ_DISP_A i (Z.of_nat (length ks)) xs3 (wz PJ_NE_TAB_A) xt5
                 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).

Definition aval_stmtA (E : pjenvA) (I : serI) (K : config -> Prop) (D : nat) (fu : nat) : Prop :=
  forall (d0 : nat) (ks : list bool) (i2 c2 : Z) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
         (F : bvmap 5 word) (fc : bv 32)
         (xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    si_j I - i2 <= Z.of_nat fu -> (d0 + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
    RESTA E d0 ks i2 c2 (si_j I) (si_c' I) -> 2 <= i2 -> 0 <= c2 ->
    SERMC RT E I isobj Σ st m -> frm0 fc -> sa_size st <= 41 * (i2 - 1) + 6 * c2 + 2 ->
    CREDA RT E I Σ (2 * (si_j I - i2) + 1) st ->
    aevt Σ K (LSTA E I PJ_AV_A (i2 - 1) (Z.of_nat (length ks)) xs3 (wz (pa_SB E + 80)) xt5
                 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).

Definition open_stmtA (E : pjenvA) (I : serI) (K : config -> Prop) (D : nat) (fu : nat) (k : bool) : Prop :=
  forall (d' : nat) (ks : list bool) (i e n c c2 : Z) (isobj : list byte) (Σ : rts RT) (st : sbA) (m : mem)
         (F : bvmap 5 word) (fc : bv 32)
         (xs3 xt5 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 : word),
    si_j I - (i + 1) <= Z.of_nat fu -> (S d' + length ks = D)%nat -> (length ks <= 15)%nat -> kinds_rel ks isobj ->
    ty (pa_T E) i = (if k then t_obj else t_arr) -> tnext (pa_T E i) = e + 1 -> ty (pa_T E) e = end_ty k ->
    tilesS (itemS (pa_T E) (pa_S E) (pa_sn E) k d') (i + 1) e n c c2 ->
    RESTA E (S d') ks (e + 1) c2 (si_j I) (si_c' I) -> 1 <= i -> 0 <= c ->
    SERMC RT E I isobj Σ st m -> frm0 fc -> sa_size st <= 41 * (i - 1) + 6 * c + 3 ->
    CREDA RT E I Σ (2 * (si_j I - i) - 1) st ->
    aevt Σ K (LSTA E I (if k then PJ_OBJ_A else PJ_ARR_A) i (Z.of_nat (length ks)) xs3 (wz (pa_SB E + 80)) xt5
                 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt6 F fc m).

Definition rec_okA (D : nat) : Prop := forall (k : bool) (d' : nat), (d' + 16 <= D)%nat -> cont_cpsA RT PMc k d'.

End Conts.
