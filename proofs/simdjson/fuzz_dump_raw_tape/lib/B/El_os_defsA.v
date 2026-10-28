(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Export FX_lib Pj_defsA Pj_os_defsA F_achk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout R_m2s I_consts I_qck D_kit RT_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation EL_SENTRY := 0x111cc0%Z (only parsing).
Notation EL_SENTRY_D := 0x111d1c%Z (only parsing).
Notation EL_GETLOC := 0x110698%Z (only parsing).
Notation EL_USE_FACET := 0x136c24%Z (only parsing).
Notation EL_LOC_D := 0x1363bc%Z (only parsing).
Notation EL_INS_UL := 0x112364%Z (only parsing).
Notation EL_INS_U := 0x111fc8%Z (only parsing).
Notation EL_INS_L := 0x112198%Z (only parsing).
Notation EL_INS_D := 0x112530%Z (only parsing).
Notation EL_INS_I := 0x111dc4%Z (only parsing).
Notation EL_NP_L := 0x11cfa8%Z (only parsing).
Notation EL_NP_UL := 0x11d500%Z (only parsing).
Notation EL_NP_D := 0x11da10%Z (only parsing).
Notation EL_WGI := 0x12038c%Z (only parsing).
Notation EL_WGF := 0x1207f0%Z (only parsing).
Notation EL_PAD := 0xb19a4%Z (only parsing).
Notation EL_STRNC := 0xb1e80%Z (only parsing).
Notation EL_SETFILL := 0xb201c%Z (only parsing).
Notation EL_ESC := 0xb0da0%Z (only parsing).
Notation EL_DUMP := 0xb04a0%Z (only parsing).
Notation EL_OSPUT := 0xb131c%Z (only parsing).
Notation EL_OVERFLOW := 0xb0168%Z (only parsing).
Notation EL_XSPUTN := 0x111a64%Z (only parsing).
Notation EL_MEMMOVE := 0x7ee94%Z (only parsing).
Notation EL_SNL := 0x14727c%Z (only parsing).
Notation EL_DO_WIDEN := 0x138584%Z (only parsing).
Notation EL_DO_WIDEN_R := 0x13858c%Z (only parsing).
Notation EL_DO_DECPT := 0x13b770%Z (only parsing).
Notation EL_DO_THSEP := 0x13b780%Z (only parsing).
Notation EL_DO_GROUPING := 0x13b790%Z (only parsing).

Notation EL_IMP := 0x6aac28%Z (only parsing).
Notation EL_CTYPE_F := 0x6aab48%Z (only parsing).
Notation EL_NPUT_F := 0x6aa9b0%Z (only parsing).
Notation EL_NPUNCT_F := 0x6aabc8%Z (only parsing).
Notation EL_CTYPE_VT := 0x16c558%Z (only parsing).
Notation EL_NPUT_VT := 0x16d120%Z (only parsing).
Notation EL_NPUNCT_VT := 0x16c710%Z (only parsing).
Notation EL_CTYPE_ID := 0x6aa8e0%Z (only parsing).
Notation EL_NPUT_ID := 0x6aa668%Z (only parsing).
Notation EL_NPUNCT_ID := 0x6aa8f0%Z (only parsing).
Notation EL_CLOC_CELL := 0x6aa7f0%Z (only parsing).
Notation EL_CLOC := 0x33380%Z (only parsing).
Notation EL_GOT_NPUT_ID := 0x16f500%Z (only parsing).
Notation EL_GOT_CTYPE_ID := 0x16f430%Z (only parsing).
Notation EL_NSB_VT := 0x168da8%Z (only parsing).
Notation EL_OS_VT := 0x168e30%Z (only parsing).
Notation EL_IOS_VT := 0x168e58%Z (only parsing).
Notation EL_TPLOC := 0x6abdb8%Z (only parsing).
Notation EL_GLOC := 0x6cc0b0%Z (only parsing).

Definition el_dccA (m : word -> option byte) : Prop :=
  ro_cells bsegs m 0x168e08 [C8 (Z_to_bv 64 0x111a64); C8 (Z_to_bv 64 0xb0168); C8 (Z_to_bv 64 8)]
  /\ ro_cells bsegs m 0x16c590 [C8 (Z_to_bv 64 0x138584)]
  /\ ro_cells bsegs m 0x16c598 [C8 (Z_to_bv 64 0x13858c)]
  /\ ro_cells bsegs m 0x16d140 [C8 (Z_to_bv 64 0x11cfa8); C8 (Z_to_bv 64 0x11d254); C8 (Z_to_bv 64 0x11d500);
                               C8 (Z_to_bv 64 0x11d788); C8 (Z_to_bv 64 0x11da10)]
  /\ ro_cells bsegs m 0x16c728 [C8 (Z_to_bv 64 0x13b770); C8 (Z_to_bv 64 0x13b780); C8 (Z_to_bv 64 0x13b790)]
  /\ ro_cells bsegs m 0x16f500 [C8 (Z_to_bv 64 0x6aa668)]
  /\ ro_cells bsegs m 0x16f430 [C8 (Z_to_bv 64 0x6aa8e0)].

Lemma el_dccA_agree : forall m m', el_dccA m -> agree_on (fun a => (0x168e08 <= a < 0x16f508)%Z) m m' -> el_dccA m'.
Proof.
  intros m m' (D1 & D2 & D2b & D3 & D4 & D5 & D6) AG.
  assert (RO : forall A cs, ro_cells bsegs m A cs -> (0x168e08 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= 0x16f508)%Z -> ro_cells bsegs m' A cs).
  { intros A cs H H1 H2. apply (ro_cells_agree bsegs m m' _ _ H). apply (agree_sub _ _ _ _ AG). intros x Hx. cbv beta. lia. }
  split; [apply (RO _ _ D1); cbn; lia|]. split; [apply (RO _ _ D2); cbn; lia|]. split; [apply (RO _ _ D2b); cbn; lia|]. split; [apply (RO _ _ D3); cbn; lia|].
  split; [apply (RO _ _ D4); cbn; lia|]. split; [apply (RO _ _ D5); cbn; lia| apply (RO _ _ D6); cbn; lia].
Qed.
Lemma el_dccA_munch : forall W m m', el_dccA m -> munch W m m' -> (forall a, (0x168e08 <= a < 0x16f508)%Z -> outside W a) -> el_dccA m'.
Proof. intros W m m' D MU HW. apply (el_dccA_agree m m' D). apply (agree_of_munch W m m' _ MU). exact HW. Qed.

Definition ios_cellsX (OS : Z) (vptr flags width fill : Z) (j148 j284 : list byte) : list cell :=
  [C8 (Z_to_bv 64 vptr);
   C4 (Z_to_bv 64 flags); CB 4 j148;
   C8 (Z_to_bv 64 6);
   C8 (Z_to_bv 64 width);
   C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 OS);
   C8 (Z_to_bv 64 0x6aac28);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0);
   C4 (Z_to_bv 64 fill); CB 4 j284].

Definition sb_cellsX (pb pp ep : word) (dum : list byte) : list cell :=
  [C8 (Z_to_bv 64 0x168da8); C8 (Z_to_bv 64 0x6aac28); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 pb; C8 pp; C8 ep; CB 64 dum].

Definition os_cellsX (OS : Z) (pb pp ep : word) (flags width fill : Z) (dum j148 j284 : list byte) : list cell :=
  sb_cellsX pb pp ep dum ++ [C8 (Z_to_bv 64 0x168e30)] ++ ios_cellsX OS 0x168e58 flags width fill j148 j284.

Lemma sb_cellsA_X : forall pb pp ep dum, sb_cellsA pb pp ep dum = sb_cellsX pb pp ep dum.
Proof. intros. reflexivity. Qed.
Lemma ios_cellsA_X : forall OS vptr fill j148 j284, ios_cellsA OS vptr fill j148 j284 = ios_cellsX OS vptr 0x1002 0 fill j148 j284.
Proof. intros. reflexivity. Qed.
Lemma os_cellsA_X : forall OS pb pp ep fill dum j148 j284,
  os_cellsA OS pb pp ep fill dum j148 j284 = os_cellsX OS pb pp ep 0x1002 0 fill dum j148 j284.
Proof. intros. reflexivity. Qed.
Lemma os_cellsX_size : forall OS pb pp ep flags width fill dum j148 j284,
  cells_size (os_cellsX OS pb pp ep flags width fill dum j148 j284) = 288%nat.
Proof. intros. reflexivity. Qed.

Definition PUTINV (OS pp ep : Z) : Prop := (pp = 0 /\ ep = 0)%Z \/ (ep = OS + 128 /\ OS + 64 <= pp <= OS + 128)%Z.

Definition FILLOK (fill : Z) : Prop := (fill = 0xffffffff \/ fill = 0x20 \/ fill = 0x30)%Z.
Definition fill_after (fill : Z) : Z := if (fill =? 0xffffffff)%Z then 0x20%Z else fill.
Lemma FILLOK_after : forall fill, FILLOK fill -> (fill_after fill = 0x20 \/ fill_after fill = 0x30)%Z.
Proof. intros fill [-> | [-> | ->]]; cbv; lia. Qed.

Definition OSX (m : word -> option byte) (OS fill : Z) : Prop :=
  exists pb pp ep dum j148 j284,
    rw_cells bsegs m OS (os_cellsX OS pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) 0x1002 0 fill dum j148 j284) /\ PUTINV OS pp ep.

Lemma OSFRESHA_OSX : forall m OS, OSFRESHA m OS -> OSX m OS 0xffffffff.
Proof.
  intros m OS (dum & j148 & j284 & H). exists (Z_to_bv 64 0), 0%Z, 0%Z, dum, j148, j284.
  split; [exact H | left; lia].
Qed.

Lemma OSX_cellsA : forall m OS fill, OSX m OS fill ->
  exists pb pp ep dum j148 j284, rw_cells bsegs m OS (os_cellsA OS pb pp ep fill dum j148 j284).
Proof. intros m OS fill (pb & pp & ep & dum & j148 & j284 & H & _). exists pb, (Z_to_bv 64 pp), (Z_to_bv 64 ep), dum, j148, j284. exact H. Qed.

Lemma OSX_transport : forall W m m' OS fill, OSX m OS fill -> munch W m m' -> wmono bsegs m m' -> disjoint_from W OS 288 -> OSX m' OS fill.
Proof.
  intros W m m' OS fill (pb & pp & ep & dum & j148 & j284 & H & PI) MU WM D. exists pb, pp, ep, dum, j148, j284.
  split; [| exact PI]. apply (rw_cells_transport bsegs W m m' _ _ H MU WM). rewrite os_cellsX_size. exact D.
Qed.
Lemma OSX_agree : forall m m' OS fill, OSX m OS fill -> agree_on (fun a => (OS <= a < OS + 288)%Z) m m' -> wmono bsegs m m' -> OSX m' OS fill.
Proof.
  intros m m' OS fill (pb & pp & ep & dum & j148 & j284 & H & PI) AG WM. exists pb, pp, ep, dum, j148, j284.
  split; [| exact PI]. apply (rw_cells_agree bsegs m m' _ _ H); [| exact WM]. intros a Ha. apply AG. rewrite os_cellsX_size in Ha. lia.
Qed.

Lemma os_cellsX_parts : forall m OS pb pp ep flags width fill dum j148 j284,
  rw_cells bsegs m OS (os_cellsX OS pb pp ep flags width fill dum j148 j284) <->
  (rw_cells bsegs m OS (sb_cellsX pb pp ep dum) /\ rw_cells bsegs m (OS + 128) [C8 (Z_to_bv 64 0x168e30)]
   /\ rw_cells bsegs m (OS + 136) (ios_cellsX OS 0x168e58 flags width fill j148 j284)).
Proof.
  intros. unfold os_cellsX.
  rewrite (Startup_glue.rw_cells_app bsegs m OS). rewrite (Startup_glue.rw_cells_app bsegs m _ [_]).
  cbn [sb_cellsX cells_size csize Nat.add].
  replace (OS + Z.of_nat 128)%Z with (OS + 128)%Z by lia. replace (OS + 128 + Z.of_nat 8)%Z with (OS + 136)%Z by lia.
  tauto.
Qed.

Definition os_locA (OS : Z) : Prop :=
  (OS mod 16 = 0)%Z /\ (0x6ce000 <= OS)%Z /\ (OS + 296 <= 2^47)%Z /\ (OS + 296 <= SHADOW_LO \/ 0x10007fff8000 <= OS)%Z.

Lemma os_locA_bounds : forall OS, os_locA OS -> (0x6ce000 <= OS /\ OS + 296 <= 2^47 /\ (OS + 296 <= SHADOW_LO \/ SHADOW_HI <= OS + 8))%Z.
Proof. intros OS (AL & LO & HI & SH). unfold SHADOW_LO, SHADOW_HI in *. lia. Qed.

Definition srcA (RT : rt_sig) (Σ : rts RT) (q BUF CAP : Z) (bs : list byte) : Prop :=
  (ro_bytes bsegs BUF bs /\ (0x10000 <= BUF)%Z /\ (BUF + CAP <= 0x6ce000)%Z /\ (exists a n, In (a, n) ACC_LITS /\ a <= BUF /\ BUF + CAP <= a + n)%Z)
  \/ (q <= BUF /\ BUF + CAP <= USTACK_TOP - 16)%Z
  \/ (exists f k, In (f, k) (rt_frames RT Σ) /\ f <= BUF /\ BUF + CAP <= f + fs_size k - 8)%Z.

Lemma rw_cells_CB_cut3 : forall m A (n : nat) (bs : list byte) (a k : Z),
  (0 <= a)%Z -> (0 <= k)%Z -> (a + k <= Z.of_nat n)%Z -> rw_cells bsegs m A [CB n bs] ->
  exists b1 b2 b3,
    rw_cells bsegs m A [CB (Z.to_nat a) b1] /\ rw_cells bsegs m (A + a) [CB (Z.to_nat k) b2]
    /\ rw_cells bsegs m (A + a + k) [CB (n - Z.to_nat a - Z.to_nat k) b3].
Proof.
  intros m A n bs a k Ha Hk Hn H.
  apply (rw_cells_split_CB bsegs _ _ [] n bs [] [Z.to_nat a; Z.to_nat k; (n - Z.to_nat a - Z.to_nat k)%nat]) in H; [|cbn; lia].
  cbn [mk_CB_cells app] in H.
  apply (proj1 (Startup_glue.rw_cells_app bsegs m A [_] [_; _])) in H. destruct H as [H1 H].
  apply (proj1 (Startup_glue.rw_cells_app bsegs m _ [_] [_])) in H. destruct H as [H2 H3].
  cbn [cells_size csize Nat.add] in H2, H3. rewrite ?Nat.add_0_r in H2, H3. rewrite ?Z2Nat.id in H2, H3 by lia.
  replace (A + a + Z.of_nat (Z.to_nat k + 0))%Z with (A + a + k)%Z in H3 by lia.
  do 3 eexists. split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

Lemma rw_cells_CB_join3 : forall m A (n1 n2 n3 n : nat) (b1 b2 b3 : list byte) A2 A3,
  rw_cells bsegs m A [CB n1 b1] -> rw_cells bsegs m A2 [CB n2 b2] -> rw_cells bsegs m A3 [CB n3 b3] ->
  A2 = (A + Z.of_nat n1)%Z -> A3 = (A2 + Z.of_nat n2)%Z -> (n1 + n2 + n3 = n)%nat ->
  exists bs, rw_cells bsegs m A [CB n bs].
Proof.
  intros m A n1 n2 n3 n b1 b2 b3 A2 A3 H1 H2 H3 -> -> E.
  assert (H23 : rw_cells bsegs m (A + Z.of_nat n1) ([CB n2 b2] ++ [CB n3 b3])).
  { apply Startup_glue.rw_cells_app. split; [exact H2|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact H3. }
  assert (H123 : rw_cells bsegs m A ([CB n1 b1] ++ [CB n2 b2; CB n3 b3])).
  { apply Startup_glue.rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact H23. }
  apply rw_cells_forget in H123. cbn [app cells_size csize Nat.add] in H123.
  replace (n1 + (n2 + (n3 + 0)))%nat with n in H123 by lia. exact H123.
Qed.

Lemma bytes_at_sub : forall m A (bs : list byte) (i k : Z), bytes_at bsegs m A bs -> (0 <= i)%Z -> (0 <= k)%Z -> (i + k <= Z.of_nat (length bs))%Z ->
  bytes_at bsegs m (A + i) (firstn (Z.to_nat k) (skipn (Z.to_nat i) bs)).
Proof.
  intros m A bs i k H Hi Hk Hl.
  rewrite <- (firstn_skipn (Z.to_nat i) bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia. rewrite Z2Nat.id in H by lia.
  rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat i) bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Ltac br_is b tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (symmetry; tac) end; cbv_concl_iota.
Ltac show_pc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc =" pc end.
Ltac show_reg k :=
  lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
    let v := eval cbv beta iota delta [tget] in (tget p R) in
    idtac "x" k "=" v
  end.

Lemma rw_cells_CB_prefix : forall m A (n : nat) (bs : list byte) (k : Z),
  rw_cells bsegs m A [CB n bs] -> (0 <= k)%Z -> (k <= Z.of_nat n)%Z -> exists bs', rw_cells bsegs m A [CB (Z.to_nat k) bs'].
Proof.
  intros m A n bs k H Hk Hn.
  destruct (rw_cells_CB_cut3 m A n bs 0 k ltac:(lia) Hk ltac:(lia) H) as (b1 & b2 & b3 & _ & X & _).
  replace (A + 0)%Z with A in X by lia. exists b2. exact X.
Qed.

Lemma ltu_ZZ : forall x y, (0 <= x < 2^64)%Z -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y mod 2^64)%Z.
Proof. intros x y Hx. rewrite bv_ltu_Z, unsigned_lit_wrap, unsigned_lit_wrap, (Z.mod_small x) by lia. reflexivity. Qed.
Lemma eqb_ZZ : forall x y, bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x mod 2^64 =? y mod 2^64)%Z.
Proof. intros x y. rewrite bv_eqb_Z, !unsigned_lit_wrap. reflexivity. Qed.
Lemma lts_small : forall x y, (0 <= x < 2^63)%Z -> (0 <= y < 2^63)%Z -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y)%Z.
Proof.
  intros x y Hx Hy. rewrite bv_lts_lxor, !unsigned_lit by lia. rewrite !zb_lxor_pow2_small by lia.
  destruct (Z.ltb_spec x y), (Z.ltb_spec (x + 2^63) (y + 2^63)); lia.
Qed.

Lemma le1_Z : forall x, le1 (Z_to_bv 64 x) = [Z_to_bv 8 x].
Proof.
  intros x. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned. apply bv_wrap_bv_wrap. cbv; congruence.
Qed.
Ltac sbZ := rewrite le1_Z; mem_after_store.

Ltac bru b := br_is b ltac:(rewrite ?ltu_ZZ, ?eqb_ZZ by lia; cbn [negb Z.modulo Z.pow Z.pow_pos Pos.iter Z.mul];
                             first [reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia
                                   | apply negb_true_iff; first [apply Z.ltb_ge; lia | apply Z.eqb_neq; lia]
                                   | apply negb_false_iff; first [apply Z.ltb_lt; lia | apply Z.eqb_eq; lia]]).

Lemma shz36_munch : forall W m m' OS, bytes_at bsegs m (shad OS) (repeat z8 36) -> munch W m m' -> (0 <= OS)%Z -> (OS + 288 <= 2^47)%Z ->
  (forall x, (SHADOW_LO <= x < SHADOW_HI)%Z -> outside W x) -> bytes_at bsegs m' (shad OS) (repeat z8 36).
Proof.
  intros W m m' OS SH MU O1 O2 HW. apply (bytes_at_agree bsegs m m' _ _ SH). apply (agree_of_munch W m m' _ MU).
  intros x Hx. apply HW. rewrite repeat_length in Hx. unfold shad, SHB, SHADOW_LO, SHADOW_HI in *. Z.div_mod_to_equations. lia.
Qed.

Lemma client_consts_munch : forall W m m', client_consts m -> munch W m m' -> (forall x, (0 <= x < 0x6ce000)%Z -> outside W x) -> client_consts m'.
Proof.
  intros W m m' (C1 & C2 & C3 & C4) MU HW.
  assert (RO : forall A cs, ro_cells bsegs m A cs -> (0 <= A)%Z -> (A + Z.of_nat (cells_size cs) <= 0x6ce000)%Z -> ro_cells bsegs m' A cs).
  { intros A cs H H1 H2. apply (ro_cells_agree bsegs m m' _ _ H). apply (agree_of_munch W m m' _ MU). intros x Hx. apply HW. lia. }
  unfold client_consts, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  split; [apply (RO _ _ C1); cbn; lia|]. split; [apply (RO _ _ C2); cbn; lia|]. split; [apply (RO _ _ C3); cbn; lia| apply (RO _ _ C4); cbn; lia].
Qed.

Definition EL_XSPUTN_DEPTH : Z := 2288.
Definition os_xsputnX_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo OS N : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 pb (pp ep : Z) dum m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 N) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - EL_XSPUTN_DEPTH, bv_unsigned sp); (OS + 40, OS + 128)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' OS (sb_cellsX pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum) /\ PUTINV OS pp ep.

Definition os_xsputnX_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo OS S N CAP pp ep : Z) (pb : word) (dum bs : list byte),
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - EL_XSPUTN_DEPTH)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  rw_cells bsegs m OS (sb_cellsX pb (Z_to_bv 64 pp) (Z_to_bv 64 ep) dum) -> PUTINV OS pp ep -> os_locA OS -> (OS + 288 <= lo)%Z ->
  bytes_at bsegs m S bs -> Z.of_nat (length bs) = CAP -> (0 <= N <= CAP)%Z -> (0 <= S)%Z -> (S + CAP <= 2^47)%Z ->
  ((S + CAP <= lo /\ (S + CAP <= OS \/ OS + 288 <= S)) \/ bv_unsigned sp <= S)%Z ->
  el_dccA m -> client_consts m -> bytes_at bsegs m (shad OS) (repeat z8 36) -> ((0 < N)%Z -> chkr m S N) -> chkr m (OS + 64) 64 -> ictx m -> mem_inv bsegs m ->
  evt bsegs (os_xsputnX_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo OS N m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OS) (Z_to_bv 64 S) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x111a64) fc None m (seg_rom bsegs)).
