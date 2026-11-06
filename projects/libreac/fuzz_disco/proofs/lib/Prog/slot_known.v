From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_table bcmp_c reac_disco_table_observe_c slot_lib slot_frame slot_observe slot_newent.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require SightLib.
Import ListNotations.
Open Scope Z_scope.

Ltac ccl :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    let v := eval vm_compute in c in
    lazymatch v with
    | true => replace c with true by (vm_compute; reflexivity); cbv iota
    | false => replace c with false by (vm_compute; reflexivity); cbv iota
    end
  end.

Ltac rem_lw v E :=
  lazymatch goal with |- context [Z_to_bv 64 (bv_swrap 32 (bytes_le_to_Z ?x))] =>
    remember (bv_swrap 32 (bytes_le_to_Z x)) as v eqn:E
  end.

Ltac rem_lbu v E :=
  lazymatch goal with |- context [Z_to_bv 64 (bytes_le_to_Z ?x)] =>
    remember (bytes_le_to_Z x) as v eqn:E
  end.

Ltac run_to P :=
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => tryif constr_eq pc P then fail else step
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ccl
  end.

Ltac lv := first [ apply length_sub; lia | rewrite length_firstn, length_skipn; lia ].

Ltac fsub G k n v :=
  first [ change (bytes_le_to_Z (sub G k n)) with v
        | change (bytes_le_to_Z (firstn n (skipn (Z.to_nat k) G))) with v
        | let k' := eval vm_compute in (Z.to_nat k) in change (bytes_le_to_Z (firstn n (skipn k' G))) with v ].

Lemma u1_rng : forall G k, 0 <= u_at G k 1 < 256.
Proof.
  intros G k. unfold u_at. pose proof (ble_range (sub G k 1)) as H.
  assert (L : (length (sub G k 1) <= 1)%nat) by (unfold sub; rewrite length_firstn; lia).
  assert (P : 2 ^ (8 * Z.of_nat (length (sub G k 1))) <= 256).
  { destruct (length (sub G k 1)) as [|[|]]; cbn; lia. }
  lia.
Qed.

Definition want_role (sr orl : Z) : Z := if sr =? 0 then orl else if (orl =? 1) && (sr =? 2) then 1 else sr.

Lemma slot_R24_role : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X orl sr : Z) (G : list byte),
  sp = Z_to_bv 64 X -> 0 < X -> X + 2592 < 2 ^ 63 ->
  rw_cells rsegs m (X + 1024) [CB 24 G] -> rw_cells rsegs m (X + 152) [C8 (Z_to_bv 64 orl)] ->
  s_role G = sr -> sr = 0 \/ sr = 1 \/ sr = 2 -> orl = 0 \/ orl = 1 \/ orl = 2 ->
  evt rsegs (fun ms' => exists a0' a1' : word, ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' (Z_to_bv 64 (want_role sr orl)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f00) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ed4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X orl sr G Esp HX0 HX1 RG RO Esr0 S1 HO.
  subst sp. pose proof (rwc_split _ _ _ _ RG) as (LG & HG & _).
  rdx (X + 1024) G 8 4%nat RB.
  step. rewrite lw_val by lv. rem_lw v Ev.
  assert (Hv : v = sr) by (subst v; rewrite <- Esr0; reflexivity). rewrite Hv. clear Ev Hv.
  destruct S1 as [->|[->| ->]]; destruct HO as [->|[->| ->]];
    run_to 0x13f00; apply evt_done; do 2 eexists; reflexivity.
Qed.

Lemma slot_R24_decl : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X r hd : Z) (T G : list byte),
  sp = Z_to_bv 64 X -> 0 < X -> X + 2592 < 2 ^ 63 ->
  rw_cells rsegs m (X + 1024) [CB 24 G] -> s_hd G = hd -> hd = 0 \/ hd = 1 ->
  rw_cells rsegs m (X + 96) [C8 (Z_to_bv 64 (hd_of T r))] ->
  rw_cells rsegs m (X + 104) [C8 (Z_to_bv 64 (din_of T r))] ->
  rw_cells rsegs m (X + 112) [C8 (Z_to_bv 64 (dout_of T r))] ->
  evt rsegs (fun ms' => exists a0' : word, ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 (Z_to_bv 64 (if hd =? 0 then din_of T r else s_din G)) (Z_to_bv 64 (if hd =? 0 then hd_of T r else 1)) a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (if hd =? 0 then dout_of T r else s_dout G)) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f20) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f00) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X r hd T G Esp HX0 HX1 RG Ehd0 S2 R96 R104 R112.
  subst sp. pose proof (rwc_split _ _ _ _ RG) as (LG & HG & _).
  rdx (X + 1024) G 12 1%nat RB1. rdx (X + 1024) G 13 1%nat RB2. rdx (X + 1024) G 14 1%nat RB3.
  step. rewrite lbu_val by lv. rem_lbu v Ev.
  assert (Hv : v = hd) by (subst v; rewrite <- Ehd0; reflexivity). rewrite Hv. clear Ev Hv.
  step. step. step. step.
  destruct S2 as [->| ->].
  - ccl. apply evt_done. eexists. reflexivity.
  - ccl. step. rewrite lbu_val by lv. step. rewrite lbu_val by lv.
    step. apply evt_done. eexists. reflexivity.
Qed.

Lemma slot_R24_slots : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X r sl : Z) (T G : list byte),
  sp = Z_to_bv 64 X -> 0 < X -> X + 2592 < 2 ^ 63 ->
  rw_cells rsegs m (X + 1024) [CB 24 G] -> s_slots G = sl ->
  rw_cells rsegs m (X + 120) [C8 (Z_to_bv 64 (slots_of T r))] ->
  evt rsegs (fun ms' => exists a0' : word, ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (if sl =? 0 then slots_of T r else sl)) a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f30) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f20) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X r sl T G Esp HX0 HX1 RG Esl0 R120.
  subst sp. pose proof (rwc_split _ _ _ _ RG) as (LG & HG & _).
  rdx (X + 1024) G 16 1%nat RB1.
  step. rewrite lbu_val by lv. rem_lbu v Ev.
  assert (Hv : v = sl) by (subst v; rewrite <- Esl0; reflexivity). rewrite Hv. clear Ev Hv.
  pose proof (u1_rng G 16) as HS. change (u_at G 16 1) with (s_slots G) in HS. rewrite Esl0 in HS.
  step. step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec sl 0) as [E|E]; cbv iota.
  - apply evt_done. eexists. reflexivity.
  - step. apply evt_done. eexists. reflexivity.
Qed.

Lemma slot_R24_fam : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sf ofam : Z),
  a0 = Z_to_bv 64 sf -> s11 = Z_to_bv 64 ofam -> 0 <= sf < 256 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 (Z_to_bv 64 (if sf =? 0 then ofam else sf)) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f44) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f3c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m sf ofam Ea0 Es11 Hsf.
  subst a0 s11.
  step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec sf 0) as [E|E]; cbv iota.
  - apply evt_done. reflexivity.
  - step. apply evt_done. reflexivity.
Qed.

Lemma slot_R24_ch : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X a b : Z),
  sp = Z_to_bv 64 X -> 0 < X -> X + 2592 < 2 ^ 63 ->
  a0 = Z_to_bv 64 (bv_swrap 32 a) -> a1 = Z_to_bv 64 (bv_swrap 32 b) -> t0 = Z_to_bv 64 (bv_swrap 32 b) ->
  0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 ->
  rw_cells rsegs m (X + 136) [C8 (Z_to_bv 64 (bv_swrap 32 a))] ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (bv_swrap 32 (if a <? b then b else a))) t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f5c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f54) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X a b Esp HX0 HX1 Ea0 Ea1 Et0 Ha Hb R136.
  subst sp a0 a1 t0.
  step. rewrite SightLib.sw_ltu by lia.
  destruct (Z.ltb_spec a b) as [E|E]; cbv iota.
  - apply evt_done. reflexivity.
  - step. apply evt_done. reflexivity.
Qed.

Lemma slot_R24_own : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ow oo : Z),
  s6 = Z_to_bv 64 ow -> t0 = Z_to_bv 64 oo -> 0 <= ow <= 1 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (if ow =? 0 then oo else 1)) t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f6c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13f64) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ow oo Es6 Et0 How.
  subst s6 t0.
  step. rewrite eqb_lit by lia.
  destruct (Z.eqb_spec ow 0) as [E|E]; cbv iota.
  - apply evt_done. reflexivity.
  - step. apply evt_done. reflexivity.
Qed.

Lemma ble_if : forall (b : bool) (x y : list byte), bytes_le_to_Z (if b then x else y) = if b then bytes_le_to_Z x else bytes_le_to_Z y.
Proof. intros [|] x y; reflexivity. Qed.

Lemma sw_if : forall (b : bool) (x y : Z), bv_swrap 32 (if b then x else y) = if b then bv_swrap 32 x else bv_swrap 32 y.
Proof. intros [|] x y; reflexivity. Qed.

Lemma role_field : forall T G r, sighting_S1 G -> role_of_e T r = 0 \/ role_of_e T r = 1 \/ role_of_e T r = 2 ->
  bv_swrap 32 (bytes_le_to_Z (if c_role T G r then sub G 8 4 else sub T (48 * r + 8) 4)) =
  want_role (s_role G) (role_of_e T r).
Proof.
  intros T G r S1 HO. rewrite ble_if, sw_if.
  change (bv_swrap 32 (bytes_le_to_Z (sub G 8 4))) with (s_role G).
  change (bv_swrap 32 (bytes_le_to_Z (sub T (48 * r + 8) 4))) with (role_of_e T r).
  unfold c_role, want_role, sighting_S1 in *.
  destruct S1 as [E|[E|E]]; rewrite E; destruct HO as [E2|[E2|E2]]; rewrite E2; reflexivity.
Qed.

Lemma hd_field : forall T G r, sighting_S2 G -> hd_of T r = 0 \/ hd_of T r = 1 ->
  bytes_le_to_Z (if c_decl T G r then [Z_to_bv 8 1] else sub T (48 * r + 12) 1) =
  if s_hd G =? 0 then hd_of T r else 1.
Proof.
  intros T G r [S2 _] HH. rewrite ble_if. change (bytes_le_to_Z (sub T (48 * r + 12) 1)) with (hd_of T r).
  unfold c_decl. destruct S2 as [E|E]; rewrite E; cbn [Z.eqb negb andb].
  - reflexivity.
  - destruct HH as [E2|E2]; rewrite E2; cbn [Z.eqb orb]; [reflexivity|].
    destruct (negb (din_of T r =? s_din G) || negb (dout_of T r =? s_dout G)); reflexivity.
Qed.

Lemma din_field : forall T G r, sighting_S2 G ->
  bytes_le_to_Z (if c_decl T G r then sub G 13 1 else sub T (48 * r + 13) 1) =
  if s_hd G =? 0 then din_of T r else s_din G.
Proof.
  intros T G r [S2 _]. rewrite ble_if. change (bytes_le_to_Z (sub T (48 * r + 13) 1)) with (din_of T r).
  change (bytes_le_to_Z (sub G 13 1)) with (s_din G).
  unfold c_decl. destruct S2 as [E|E]; rewrite E; cbn [Z.eqb negb andb]; [reflexivity|].
  destruct (Z.eqb_spec (hd_of T r) 0); cbn [orb]; [reflexivity|].
  destruct (Z.eqb_spec (din_of T r) (s_din G)); cbn [negb orb]; [|reflexivity].
  destruct (negb (dout_of T r =? s_dout G)); [reflexivity | assumption].
Qed.

Lemma dout_field : forall T G r, sighting_S2 G ->
  bytes_le_to_Z (if c_decl T G r then sub G 14 1 else sub T (48 * r + 14) 1) =
  if s_hd G =? 0 then dout_of T r else s_dout G.
Proof.
  intros T G r [S2 _]. rewrite ble_if. change (bytes_le_to_Z (sub T (48 * r + 14) 1)) with (dout_of T r).
  change (bytes_le_to_Z (sub G 14 1)) with (s_dout G).
  unfold c_decl. destruct S2 as [E|E]; rewrite E; cbn [Z.eqb negb andb]; [reflexivity|].
  destruct (Z.eqb_spec (hd_of T r) 0); cbn [orb]; [reflexivity|].
  destruct (negb (din_of T r =? s_din G)); cbn [orb]; [reflexivity|].
  destruct (Z.eqb_spec (dout_of T r) (s_dout G)); cbn [negb]; [assumption | reflexivity].
Qed.

Lemma slots_field : forall T G r,
  bytes_le_to_Z (if c_slots T G r then sub G 16 1 else sub T (48 * r + 16) 1) =
  if s_slots G =? 0 then slots_of T r else s_slots G.
Proof.
  intros T G r. rewrite ble_if. change (bytes_le_to_Z (sub T (48 * r + 16) 1)) with (slots_of T r).
  change (bytes_le_to_Z (sub G 16 1)) with (s_slots G). unfold c_slots.
  destruct (Z.eqb_spec (s_slots G) 0); cbn [negb andb]; [reflexivity|].
  destruct (Z.eqb_spec (slots_of T r) (s_slots G)); cbn [negb]; [assumption | reflexivity].
Qed.

Lemma fam_field : forall T G r,
  bytes_le_to_Z (if c_fam T G r then sub G 15 1 else sub T (48 * r + 15) 1) =
  if s_fam G =? 0 then fam_of T r else s_fam G.
Proof.
  intros T G r. rewrite ble_if. change (bytes_le_to_Z (sub T (48 * r + 15) 1)) with (fam_of T r).
  change (bytes_le_to_Z (sub G 15 1)) with (s_fam G). unfold c_fam.
  destruct (Z.eqb_spec (s_fam G) 0); cbn [negb andb]; [reflexivity|].
  destruct (Z.eqb_spec (fam_of T r) (s_fam G)); cbn [negb]; [assumption | reflexivity].
Qed.

Lemma ch_field : forall T G r,
  bv_swrap 32 (bytes_le_to_Z (if c_ch T G r then sub G 20 4 else sub T (48 * r + 20) 4)) =
  bv_swrap 32 (if ch_of T r <? s_ch G then s_ch G else ch_of T r).
Proof. intros T G r. rewrite ble_if. unfold c_ch. reflexivity. Qed.

Lemma own_field : forall T ow r, 0 <= ow <= 1 -> owned_of T r = 0 \/ owned_of T r = 1 ->
  bv_swrap 32 (bytes_le_to_Z (if c_own T ow r then Z_to_le_bytes 4 1 else sub T (48 * r + 24) 4)) =
  if ow =? 0 then owned_of T r else 1.
Proof.
  intros T ow r How HO. rewrite ble_if, sw_if.
  change (bv_swrap 32 (bytes_le_to_Z (sub T (48 * r + 24) 4))) with (owned_of T r).
  unfold c_own. assert (E : ow = 0 \/ ow = 1) by lia.
  destruct E as [->| ->]; destruct HO as [E2|E2]; rewrite E2; reflexivity.
Qed.

Lemma u4_rng : forall G k, 0 <= u_at G k 4 < 2 ^ 32.
Proof.
  intros G k. unfold u_at. pose proof (ble_range (sub G k 4)) as H.
  assert (L : (length (sub G k 4) <= 4)%nat) by (unfold sub; rewrite length_firstn; lia).
  assert (P : 2 ^ (8 * Z.of_nat (length (sub G k 4))) <= 2 ^ 32).
  { destruct (length (sub G k 4)) as [|[|[|[|[|]]]]]; cbn; lia. }
  lia.
Qed.

Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] (Ha & Hn & H)].
    rewrite cells_bytes_length in B2 by exact W1.
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply H. lia.
  - intros [[[W1 B1] (Ha & Hn & H1)] [[W2 B2] (Ha2 & Hn2 & H2)]].
    rewrite <- (cells_bytes_length cs1 W1) in B2.
    split; [split; [split; assumption|split; assumption]|].
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))) as [L|L]; [apply H1; lia|].
    replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply H2. lia.
Qed.

Lemma rw_cons_split : forall m A c cs, rw_cells rsegs m A (c :: cs) ->
  rw_cells rsegs m A [c] /\ rw_cells rsegs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs H. change (c :: cs) with ([c] ++ cs) in H. apply rw_cells_app in H.
  cbn [cells_size] in H. rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma rw_app_join : forall m A B cs1 cs2, rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 ->
  B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof. intros m A B cs1 cs2 H1 H2 ->. apply rw_cells_app. split; assumption. Qed.

Lemma zxb8 : forall v, 0 <= v < 256 -> Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 v)) 255) = Z_to_bv 64 v.
Proof.
  intros v Hv. rewrite unsigned_lit by lia. change 255 with (Z.ones 8). rewrite Z.land_ones by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma lor_u : forall a b : word,
  bv_unsigned (Z_to_bv 64 (Z.lor (bv_unsigned a) (bv_unsigned b))) = Z.lor (bv_unsigned a) (bv_unsigned b).
Proof. intros a b. rewrite <- bv_or_unsigned. rewrite Z_to_bv_lit_self. reflexivity. Qed.

Lemma xor_u : forall a b : word,
  bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned a) (bv_unsigned b))) = Z.lxor (bv_unsigned a) (bv_unsigned b).
Proof. intros a b. rewrite <- bv_xor_unsigned. rewrite Z_to_bv_lit_self. reflexivity. Qed.

Lemma and255_u : forall x, bv_unsigned (Z_to_bv 64 (Z.land x 255)) = Z.land x 255.
Proof.
  intros x. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply unsigned_lit.
  pose proof (Z.mod_pos_bound x (2 ^ 8) ltac:(lia)). lia.
Qed.

Lemma b2z_u : forall b : bool, bv_unsigned (Z_to_bv 64 (Z.b2z b)) = Z.b2z b.
Proof. intros [|]; reflexivity. Qed.

Lemma lx255 : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> Z.land (Z.lxor a b) 255 = Z.lxor a b.
Proof.
  intros a b Ha Hb. change 255 with (Z.ones 8). apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.lxor_spec.
  destruct (Z.lt_ge_cases n 8).
  - rewrite Z.ones_spec_low by lia. apply andb_true_r.
  - rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
    rewrite <- (Z.mod_small a (2 ^ 8)), <- (Z.mod_small b (2 ^ 8)) by lia.
    rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma lor_b2z : forall a b : bool, Z.lor (Z.b2z a) (Z.b2z b) = Z.b2z (a || b).
Proof. intros [|] [|]; reflexivity. Qed.

Lemma diff_bool : forall wr orl whd ohd wdi odi wdo odo wsl osl wf of wo oo,
  0 <= wr -> 0 <= orl -> 0 <= wsl -> 0 <= osl -> 0 <= wf -> 0 <= of -> 0 <= wo -> 0 <= oo ->
  0 <= whd < 256 -> 0 <= ohd < 256 -> 0 <= wdi < 256 -> 0 <= odi < 256 -> 0 <= wdo < 256 -> 0 <= odo < 256 ->
  (0 <? Z.lor (Z.lor (Z.lor (Z.lxor wr orl) (Z.land (Z.lxor whd ohd) 255))
                     (Z.lor (Z.land (Z.lxor wdi odi) 255) (Z.land (Z.lxor wdo odo) 255)))
              (Z.lor (Z.lor (Z.lxor wsl osl) (Z.lxor wf of)) (Z.lxor wo oo))) =
  negb ((wr =? orl) && (whd =? ohd) && (wdi =? odi) && (wdo =? odo) && (wsl =? osl) && (wf =? of) && (wo =? oo)).
Proof.
  intros. rewrite !lx255 by lia.
  assert (NN : 0 <= Z.lor (Z.lor (Z.lor (Z.lxor wr orl) (Z.lxor whd ohd)) (Z.lor (Z.lxor wdi odi) (Z.lxor wdo odo)))
                          (Z.lor (Z.lor (Z.lxor wsl osl) (Z.lxor wf of)) (Z.lxor wo oo)))
    by (repeat first [apply Z.lor_nonneg; split | apply Z.lxor_nonneg; split]; intros; lia).
  apply Bool.eq_iff_eq_true. rewrite Z.ltb_lt, Bool.negb_true_iff, <- Bool.not_true_iff_false.
  rewrite !andb_true_iff, !Z.eqb_eq.
  split.
  - intros Hc ((((((E1 & E2) & E3) & E4) & E5) & E6) & E7).
    rewrite E1, E2, E3, E4, E5, E6, E7, !Z.lxor_nilpotent in Hc. vm_compute in Hc. discriminate.
  - intros Hc. destruct (Z.eq_dec (Z.lor (Z.lor (Z.lor (Z.lxor wr orl) (Z.lxor whd ohd)) (Z.lor (Z.lxor wdi odi) (Z.lxor wdo odo)))
                          (Z.lor (Z.lor (Z.lxor wsl osl) (Z.lxor wf of)) (Z.lxor wo oo))) 0) as [Z0|Z0]; [|lia].
    exfalso. apply Hc. rewrite !Z.lor_eq_0_iff in Z0.
    destruct Z0 as (((Z1 & Z2) & (Z3 & Z4)) & ((Z5 & Z6) & Z7)).
    apply (proj1 (Z.lxor_eq_0_iff _ _)) in Z1, Z2, Z3, Z4, Z5, Z6, Z7.
    repeat split; assumption.
Qed.

Lemma slot_R24_diff :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (X wr orl whd ohd wdi odi wdo odo wsl osl wf of wo oo oc sc ret i now rem : Z) (c64 : word),
  sp = Z_to_bv 64 X -> a2 = Z_to_bv 64 wr -> s5 = Z_to_bv 64 whd -> s9 = Z_to_bv 64 wdi -> s7 = Z_to_bv 64 wdo ->
  s1 = Z_to_bv 64 wsl -> s11 = Z_to_bv 64 wf -> s10 = Z_to_bv 64 wo ->
  0 < X -> X + 2592 < 2 ^ 63 ->
  0 <= wr < 2 ^ 64 -> 0 <= orl < 2 ^ 64 -> 0 <= wsl < 2 ^ 64 -> 0 <= osl < 2 ^ 64 -> 0 <= wf < 2 ^ 64 -> 0 <= of < 2 ^ 64 ->
  0 <= wo < 2 ^ 64 -> 0 <= oo < 2 ^ 64 ->
  0 <= whd < 256 -> 0 <= ohd < 256 -> 0 <= wdi < 256 -> 0 <= odi < 256 -> 0 <= wdo < 256 -> 0 <= odo < 256 ->
  0 <= oc < 2 ^ 32 -> 0 <= sc < 2 ^ 32 ->
  ret = Z.b2z (negb (wr =? orl) || negb ((whd =? ohd) && (wdi =? odi) && (wdo =? odo)) || negb (wsl =? osl) ||
               negb (wf =? of) || (oc <? sc) || negb (wo =? oo)) ->
  rw_cells rsegs m (X + 40) [C8 (Z_to_bv 64 (bv_swrap 32 sc)); C8 (Z_to_bv 64 ret); C8 (Z_to_bv 64 of); C8 c64] ->
  rw_cells rsegs m (X + 96) [C8 (Z_to_bv 64 ohd)] -> rw_cells rsegs m (X + 104) [C8 (Z_to_bv 64 odi)] ->
  rw_cells rsegs m (X + 112) [C8 (Z_to_bv 64 odo)] -> rw_cells rsegs m (X + 120) [C8 (Z_to_bv 64 osl)] ->
  rw_cells rsegs m (X + 128) [C8 (Z_to_bv 64 oo)] -> rw_cells rsegs m (X + 136) [C8 (Z_to_bv 64 (bv_swrap 32 oc))] ->
  rw_cells rsegs m (X + 152) [C8 (Z_to_bv 64 orl)] -> rw_cells rsegs m (X + 160) [C8 (Z_to_bv 64 i)] ->
  rw_cells rsegs m (X + 192) [C8 (Z_to_bv 64 rem)] -> rw_cells rsegs m (X + 200) [C8 (Z_to_bv 64 now)] ->
  evt rsegs (fun ms' => exists (a0' a1' a2' a3' a4' a5' a6' a7' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 i) a0' a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 (Z_to_bv 64 rem) s8 s9 s10 (Z_to_bv 64 now) t3 t4 t5 t6)
               F (Z_to_bv 64 R27) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14018) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    X wr orl whd ohd wdi odi wdo odo wsl osl wf of wo oo oc sc ret i now rem c64
    Esp Ea2 Es5 Es9 Es7 Es1 Es11 Es10 HX0 HX1 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 Eret
    R40 R96 R104 R112 R120 R128 R136 R152 R160 R192 R200.
  subst sp a2 s5 s9 s7 s1 s11 s10. unfold R27.
  do 33 step.
  lazymatch goal with |- evt _ _ (MS _ _ (if negb (bv_eqb ?A ?B) then _ else _) _ _ _ _) =>
    replace (bv_eqb A B) with true; [cbn [negb] | symmetry; unfold bv_eqb; apply Z.eqb_eq]
  end.
  2: { rewrite ?v_sltu_b2z. repeat first [rewrite lor_u | rewrite xor_u | rewrite and255_u | rewrite b2z_u].
       rewrite (unsigned_lit wr), (unsigned_lit orl), (unsigned_lit whd), (unsigned_lit ohd), (unsigned_lit wdi),
         (unsigned_lit odi), (unsigned_lit wdo), (unsigned_lit odo), (unsigned_lit wsl), (unsigned_lit osl),
         (unsigned_lit wf), (unsigned_lit of), (unsigned_lit wo), (unsigned_lit oo) by lia.
       change (bv_unsigned (Z_to_bv 64 0)) with 0.
       replace (bv_unsigned (Z_to_bv 64 (bv_swrap 32 oc)) <? bv_unsigned (Z_to_bv 64 (bv_swrap 32 sc))) with (oc <? sc)
         by (symmetry; apply (SightLib.sw_ltu oc sc); lia).
       rewrite diff_bool by lia. rewrite lor_b2z. subst ret. rewrite b2z_u. f_equal.
       destruct (wr =? orl), (whd =? ohd), (wdi =? odi), (wdo =? odo), (wsl =? osl), (wf =? of), (wo =? oo), (oc <? sc);
         reflexivity. }
  apply evt_done. do 8 eexists. reflexivity.
Qed.

Lemma fr_role : forall T G r, sighting_S1 G -> role_of_e T r = 0 \/ role_of_e T r = 1 \/ role_of_e T r = 2 ->
  negb (want_role (s_role G) (role_of_e T r) =? role_of_e T r) = c_role T G r.
Proof.
  intros T G r S1 HO. unfold c_role, want_role, sighting_S1 in *.
  destruct S1 as [E|[E|E]]; rewrite E; destruct HO as [E2|[E2|E2]]; rewrite E2; reflexivity.
Qed.

Lemma fr_decl : forall T G r, sighting_S2 G -> hd_of T r = 0 \/ hd_of T r = 1 ->
  negb (((if s_hd G =? 0 then hd_of T r else 1) =? hd_of T r) &&
        ((if s_hd G =? 0 then din_of T r else s_din G) =? din_of T r) &&
        ((if s_hd G =? 0 then dout_of T r else s_dout G) =? dout_of T r)) = c_decl T G r.
Proof.
  intros T G r [S2 _] HH. unfold c_decl. destruct S2 as [E|E]; rewrite E; cbn [Z.eqb negb andb].
  - rewrite !Z.eqb_refl. reflexivity.
  - destruct HH as [E2|E2]; rewrite E2; cbn [Z.eqb Pos.eqb negb andb orb]; [reflexivity|].
    rewrite (Z.eqb_sym (s_din G)), (Z.eqb_sym (s_dout G)).
    destruct (din_of T r =? s_din G), (dout_of T r =? s_dout G); reflexivity.
Qed.

Lemma fr_slots : forall T G r, negb ((if s_slots G =? 0 then slots_of T r else s_slots G) =? slots_of T r) = c_slots T G r.
Proof.
  intros T G r. unfold c_slots. destruct (s_slots G =? 0); cbn [negb andb]; [rewrite Z.eqb_refl; reflexivity|].
  rewrite Z.eqb_sym. reflexivity.
Qed.

Lemma fr_fam : forall T G r, negb ((if s_fam G =? 0 then fam_of T r else s_fam G) =? fam_of T r) = c_fam T G r.
Proof.
  intros T G r. unfold c_fam. destruct (s_fam G =? 0); cbn [negb andb]; [rewrite Z.eqb_refl; reflexivity|].
  rewrite Z.eqb_sym. reflexivity.
Qed.

Lemma fr_own : forall T ow r, 0 <= ow <= 1 -> owned_of T r = 0 \/ owned_of T r = 1 ->
  negb ((if ow =? 0 then owned_of T r else 1) =? owned_of T r) = c_own T ow r.
Proof.
  intros T ow r How HO. unfold c_own. assert (E : ow = 0 \/ ow = 1) by lia.
  destruct E as [->| ->]; destruct HO as [E2|E2]; rewrite E2; reflexivity.
Qed.
Lemma slot_R24 : bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X now ow r rem i ret : Z) (T G T' j : list byte)
    (jop : word),
  sp = Z_to_bv 64 X -> s5 = Z_to_bv 64 ret -> s6 = Z_to_bv 64 ow -> s7 = Z_to_bv 64 r ->
  s9 = old_w r (fam_of T r) -> s10 = Z_to_bv 64 (n_of T) ->
  0 < X -> X + 2592 < 2 ^ 63 -> 0 <= now < 2 ^ 64 -> 0 <= ow <= 1 -> 0 <= rem < 2 ^ 64 -> 0 <= i < 2 ^ 64 ->
  length T = 400%nat -> length G = 24%nat -> tbl_T1 T -> tbl_T2 T -> tbl_T4 T -> sighting_S1 G -> sighting_S2 G ->
  find_res T (s_mac G) r -> 0 <= r -> observe_model T G ow now T' ret ->
  rw_cells rsegs m (X + 40) (old_cells T r j) -> rw_cells rsegs m (X + 152) [C8 (old_w r (role_of_e T r))] ->
  rw_cells rsegs m (X + 160) [C8 (Z_to_bv 64 i)] -> rw_cells rsegs m (X + 192) [C8 (Z_to_bv 64 rem)] ->
  rw_cells rsegs m (X + 200) [C8 (Z_to_bv 64 now)] -> rw_cells rsegs m (X + 216) [C8 jop] ->
  rw_cells rsegs m (X + 512) [CB 400 T'] -> rw_cells rsegs m (X + 1024) [CB 24 G] -> mem_inv rsegs m ->
  evt rsegs
    (fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s9' s10' t3' t4' t5' t6' w216 : word)
                       (m' : word -> option byte) (j' : list byte),
       ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 i) a0' a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5' s6' (Z_to_bv 64 rem) s8 s9' s10' (Z_to_bv 64 now) t3' t4' t5' t6')
                F (Z_to_bv 64 R27) fc None m' (seg_rom rsegs) /\
       munch [(X + 40, X + 144); (X + 216, X + 224)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
       rw_cells rsegs m' (X + 40) [CB 104 j'] /\ rw_cells rsegs m' (X + 152) [C8 (old_w r (role_of_e T r))] /\
       rw_cells rsegs m' (X + 160) [C8 (Z_to_bv 64 i)] /\ rw_cells rsegs m' (X + 192) [C8 (Z_to_bv 64 rem)] /\
       rw_cells rsegs m' (X + 200) [C8 (Z_to_bv 64 now)] /\ rw_cells rsegs m' (X + 216) [C8 w216] /\
       rw_cells rsegs m' (X + 512) [CB 400 T'] /\ rw_cells rsegs m' (X + 1024) [CB 24 G])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 R24) fc None m (seg_rom rsegs)).
Proof.
  intros BCC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m X now ow r rem i ret T G T' j jop Esp Es5 Es6 Es7 Es9 Es10 HX0 HX1 Hnow How Hrem Hi LT LG T1 T2 T4 S1 S2
    FR Hr0 OM RS RO R160 R192 R200 R216 RT RG MI.
  pose proof (known_arm T G ow now T' ret r FR Hr0 OM) as EK. clear OM.
  rewrite old_w_pos in Es9 by lia. rewrite (old_w_pos r (role_of_e T r)) by lia.
  subst sp s5 s6 s7 s9 s10. unfold R24.
  pose proof T1 as T1'. unfold tbl_T1 in T1'.
  destruct FR as [[E _] | (Hr & EMr & _)]; [lia|].
  destruct (ok_facts T G ow now r T' ret LT LG ltac:(lia) EK)
    as (LT' & EM & E384 & E8 & E12 & E13 & E14 & E15 & E16 & E20 & E24 & E32 & E40 & E392 & Eret).
  pose proof (T2 r ltac:(lia)) as HR2. destruct (T4 r ltac:(lia)) as (HH & _ & HOw).
  pose proof S2 as (S2a & _).
  unfold old_cells in RS. rewrite !old_w_pos in RS, RO by lia.
  apply rw_cons_split in RS. destruct RS as (R40 & RS). cbn [csize] in RS. replace (X + 40 + Z.of_nat 32) with (X + 72) in RS by lia.
  apply rw_cons_split in RS. destruct RS as (R72 & RS). cbn [csize] in RS. replace (X + 72 + Z.of_nat 8) with (X + 80) in RS by lia.
  apply rw_cons_split in RS. destruct RS as (R80 & RS). cbn [csize] in RS. replace (X + 80 + Z.of_nat 8) with (X + 88) in RS by lia.
  apply rw_cons_split in RS. destruct RS as (R88 & RS). cbn [csize] in RS. replace (X + 88 + Z.of_nat 8) with (X + 96) in RS by lia.
  apply rw_cons_split in RS. destruct RS as (R96 & RS). cbn [csize] in RS. replace (X + 96 + Z.of_nat 8) with (X + 104) in RS by lia.
  apply rw_cons_split in RS. destruct RS as (R104 & RS). cbn [csize] in RS. replace (X + 104 + Z.of_nat 8) with (X + 112) in RS by lia.
  apply rw_cons_split in RS. destruct RS as (R112 & RS). cbn [csize] in RS. replace (X + 112 + Z.of_nat 8) with (X + 120) in RS by lia.
  apply rw_cons_split in RS. destruct RS as (R120 & RS). cbn [csize] in RS. replace (X + 120 + Z.of_nat 8) with (X + 128) in RS by lia.
  apply rw_cons_split in RS. destruct RS as (R128 & R136). cbn [csize] in R136. replace (X + 128 + Z.of_nat 8) with (X + 136) in R136 by lia.
  try rewrite (old_w_pos r (fs_of T r)) in R72 by lia. try rewrite (old_w_pos r (hd_of T r)) in R96 by lia.
  try rewrite (old_w_pos r (din_of T r)) in R104 by lia. try rewrite (old_w_pos r (dout_of T r)) in R112 by lia.
  try rewrite (old_w_pos r (slots_of T r)) in R120 by lia. try rewrite (old_w_pos r (owned_of T r)) in R128 by lia.
  try rewrite (old_w_pos r (chs_of T r)) in R136 by lia.
  change (chs_of T r) with (bv_swrap 32 (ch_of T r)) in R136.
  pose proof (rwc_split _ _ _ _ RT) as (LT2 & HT & WT). clear RT.
  pose proof (rwc_bytes _ _ _ _ RG) as HG.
  pose proof (munch_refl [(X + 40, X + 72); (X + 216, X + 224)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  eapply evt_cut.
  { eapply slot_R24_role with (X := X) (orl := role_of_e T r) (sr := s_role G) (G := G);
      try reflexivity; try eassumption; lia. }
  intros ms' (a0' & a1' & ->).
  eapply evt_cut.
  { eapply slot_R24_decl with (X := X) (r := r) (hd := s_hd G) (T := T) (G := G);
      try reflexivity; try eassumption; lia. }
  intros ms' (a0b & ->).
  eapply evt_cut.
  { eapply slot_R24_slots with (X := X) (r := r) (sl := s_slots G) (T := T) (G := G);
      try reflexivity; try eassumption; lia. }
  intros ms' (a0c & ->).
  rdx (X + 1024) G 15 1%nat RB15.
  step. rewrite lbu_val by lv. rem_lbu vf Evf.
  assert (Hvf : vf = s_fam G) by (subst vf; reflexivity). rewrite Hvf. clear Evf Hvf.
  step. step.
  eapply evt_cut.
  { eapply slot_R24_fam with (sf := s_fam G) (ofam := fam_of T r); try reflexivity. apply u1_rng. }
  intros ms' ->.
  rdx (X + 1024) G 20 4%nat RB20.
  step. rewrite lw_val by lv. rem_lw vc Evc.
  assert (Hvc : vc = bv_swrap 32 (s_ch G)) by (subst vc; reflexivity). rewrite Hvc. clear Evc Hvc.
  step. step. step.
  eapply evt_cut.
  { eapply slot_R24_ch with (X := X) (a := ch_of T r) (b := s_ch G); try reflexivity; try eassumption;
      try apply u4_rng; lia. }
  intros ms' ->.
  step. step.
  eapply evt_cut.
  { eapply slot_R24_own with (ow := ow) (oo := owned_of T r); try reflexivity; lia. }
  intros ms' ->.
  step.
  rdx (X + 512) T' 384 4%nat RN. rewrite E384 in RN.
  step. rewrite lw_val by lv. rem_lw vn Evn.
  assert (Hvn : vn = n_of T) by (subst vn; reflexivity). rewrite Hvn. clear Evn Hvn.
  step. nt.
  step. step. step. step. step.
  rewrite (unsigned_lit (r * 64)), (unsigned_lit (r * 16)) by lia.
  replace (r * 64 - r * 16) with (48 * r) by lia.
  step. step. step. step. step. step. step. step.
  eapply evt_cut.
  { eapply BCC with (ls := s_mac G) (rs := s_mac G) (v := 0).
    - rewrite unsigned_lit by lia. rewrite <- EMr. rewrite <- (EM r ltac:(lia)). unfold mac_of.
      apply bytes_at_sub; [exact HT | lia | lia].
    - rewrite unsigned_lit by lia. rewrite <- (Z.add_0_r (X + 1024)). unfold s_mac.
      apply bytes_at_sub; [exact HG | lia | lia].
    - rewrite (unsigned_lit 6) by lia. apply memcmp_same. apply len_mac. exact LG.
    - exact MI. }
  intros ms' PO. unfold memcmp_post in PO.
  destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m3 &
                  Eq & MUc & WMc & MI3 & B1 & B2).
  subst ms'. clear B1 B2.
  transport_after_call rsegs m2 m3 MUc WMc. clear MUc WMc MI.
  rewrite (ret_pc_even 0x13fac) by (first [lia | reflexivity]).
  step. step. ccl.
  rdx (X + 512) T' (48 * r + 8) 4%nat RA. rewrite E8 in RA.
  step. rewrite lw_val by (destruct (c_role T G r); lv). rem_lw w0 Ev.
  assert (Hv : w0 = want_role (s_role G) (role_of_e T r)) by (subst w0; apply role_field; assumption).
  rewrite Hv. clear Ev Hv RA.
  step. nt.
  rdx (X + 512) T' (48 * r + 12) 1%nat RA. rewrite E12 in RA.
  step. rewrite lbu_val by (destruct (c_decl T G r); first [reflexivity | lv]). rem_lbu w1 Ev.
  assert (Hv : w1 = if s_hd G =? 0 then hd_of T r else 1) by (subst w1; apply hd_field; assumption).
  rewrite Hv. clear Ev Hv RA.
  step. nt.
  rdx (X + 512) T' (48 * r + 13) 1%nat RA. rewrite E13 in RA.
  step. rewrite lbu_val by (destruct (c_decl T G r); lv). rem_lbu w2 Ev.
  assert (Hv : w2 = if s_hd G =? 0 then din_of T r else s_din G) by (subst w2; apply din_field; assumption).
  rewrite Hv. clear Ev Hv RA.
  step. rewrite zxb8 by (destruct (s_hd G =? 0); apply u1_rng).
  step. nt.
  rdx (X + 512) T' (48 * r + 14) 1%nat RA. rewrite E14 in RA.
  step. rewrite lbu_val by (destruct (c_decl T G r); lv). rem_lbu w3 Ev.
  assert (Hv : w3 = if s_hd G =? 0 then dout_of T r else s_dout G) by (subst w3; apply dout_field; assumption).
  rewrite Hv. clear Ev Hv RA.
  step. rewrite zxb8 by (destruct (s_hd G =? 0); apply u1_rng).
  step. nt.
  rdx (X + 512) T' (48 * r + 16) 1%nat RA. rewrite E16 in RA.
  step. rewrite lbu_val by (destruct (c_slots T G r); lv). rem_lbu w4 Ev.
  assert (Hv : w4 = if s_slots G =? 0 then slots_of T r else s_slots G) by (subst w4; apply slots_field).
  rewrite Hv. clear Ev Hv RA.
  step. nt.
  rdx (X + 512) T' (48 * r + 15) 1%nat RA. rewrite E15 in RA.
  step. rewrite lbu_val by (destruct (c_fam T G r); lv). rem_lbu w5 Ev.
  assert (Hv : w5 = if s_fam G =? 0 then fam_of T r else s_fam G) by (subst w5; apply fam_field).
  rewrite Hv. clear Ev Hv RA.
  step. nt.
  rdx (X + 512) T' (48 * r + 20) 4%nat RA. rewrite E20 in RA.
  step. rewrite lw_val by (destruct (c_ch T G r); lv). rem_lw w6 Ev.
  assert (Hv : w6 = bv_swrap 32 (if ch_of T r <? s_ch G then s_ch G else ch_of T r)) by (subst w6; apply ch_field).
  rewrite Hv. clear Ev Hv RA.
  step. step. nt.
  rdx (X + 512) T' (48 * r + 24) 4%nat RA. rewrite E24 in RA.
  step. rewrite lw_val by (destruct (c_own T ow r); first [lv | rewrite length_Z_to_le_bytes; reflexivity]). rem_lw w7 Ev.
  assert (Hv : w7 = if ow =? 0 then owned_of T r else 1) by (subst w7; apply own_field; assumption).
  rewrite Hv. clear Ev Hv RA.
  step. nt.
  rdx (X + 512) T' (48 * r + 32) 8%nat RA. rewrite E32 in RA.
  step. rewrite so_ld by lv. rem_lbu w8 Ev.
  assert (Hv : w8 = fs_of T r) by (subst w8; reflexivity).
  rewrite Hv. clear Ev Hv RA.
  step. step. nt.
  rdx (X + 512) T' (48 * r + 40) 8%nat RA. rewrite E40 in RA. rewrite le8_lit in RA by lia.
  step. step. step. nt.
  pose proof (u1_rng T (48 * r + 16)) as U1. change (u_at T (48 * r + 16) 1) with (slots_of T r) in U1.
  pose proof (u1_rng G 16) as U2. change (u_at G 16 1) with (s_slots G) in U2.
  pose proof (u1_rng T (48 * r + 15)) as U3. change (u_at T (48 * r + 15) 1) with (fam_of T r) in U3.
  pose proof (u1_rng G 15) as U4. change (u_at G 15 1) with (s_fam G) in U4.
  assert (WR : 0 <= want_role (s_role G) (role_of_e T r) <= 2).
  { unfold want_role. pose proof S1 as S1'. unfold sighting_S1 in S1'.
    destruct S1' as [E|[E|E]]; rewrite E; destruct HR2 as [E2|[E2|E2]]; rewrite E2; cbn; lia. }
  eapply evt_cut.
  { eapply slot_R24_diff with (X := X) (wr := want_role (s_role G) (role_of_e T r)) (orl := role_of_e T r)
      (whd := if s_hd G =? 0 then hd_of T r else 1) (ohd := hd_of T r)
      (wdi := if s_hd G =? 0 then din_of T r else s_din G) (odi := din_of T r)
      (wdo := if s_hd G =? 0 then dout_of T r else s_dout G) (odo := dout_of T r)
      (wsl := if s_slots G =? 0 then slots_of T r else s_slots G) (osl := slots_of T r)
      (wf := if s_fam G =? 0 then fam_of T r else s_fam G) (of := fam_of T r)
      (wo := if ow =? 0 then owned_of T r else 1) (oo := owned_of T r)
      (oc := ch_of T r) (sc := s_ch G) (ret := ret) (i := i) (now := now) (rem := rem);
      try reflexivity; try eassumption;
      try (destruct (s_hd G =? 0); first [apply u1_rng | lia]);
      try (destruct (s_slots G =? 0); first [apply u1_rng | lia]);
      try (destruct (s_fam G =? 0); first [apply u1_rng | lia]);
      try apply u1_rng; try apply u4_rng; try (unfold want_role; destruct (s_role G =? 0); [|destruct (_ && _)]; lia);
      try (destruct (ow =? 0); lia); try (destruct (s_slots G =? 0); lia); try (destruct (s_fam G =? 0); lia); try lia.
    rewrite Eret. unfold c_any. rewrite <- (fr_role T G r S1 HR2), <- (fr_decl T G r S2 HH), <- (fr_slots T G r),
      <- (fr_fam T G r), <- (fr_own T ow r How HOw). unfold c_ch.
    match goal with |- (if ?b then 1 else 0) = Z.b2z _ => destruct b; reflexivity end. }
  intros ms' (a0d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & ->).
  pose proof (rw_app_join _ _ _ _ _ R128 R136 ltac:(cbn [cells_size csize Nat.add]; lia)) as J. cbn [app] in J.
  pose proof (rw_app_join _ _ _ _ _ R120 J ltac:(cbn [cells_size csize Nat.add]; lia)) as J1. cbn [app] in J1.
  pose proof (rw_app_join _ _ _ _ _ R112 J1 ltac:(cbn [cells_size csize Nat.add]; lia)) as J2. cbn [app] in J2.
  pose proof (rw_app_join _ _ _ _ _ R104 J2 ltac:(cbn [cells_size csize Nat.add]; lia)) as J3. cbn [app] in J3.
  pose proof (rw_app_join _ _ _ _ _ R96 J3 ltac:(cbn [cells_size csize Nat.add]; lia)) as J4. cbn [app] in J4.
  pose proof (rw_app_join _ _ _ _ _ R88 J4 ltac:(cbn [cells_size csize Nat.add]; lia)) as J5. cbn [app] in J5.
  pose proof (rw_app_join _ _ _ _ _ R80 J5 ltac:(cbn [cells_size csize Nat.add]; lia)) as J6. cbn [app] in J6.
  pose proof (rw_app_join _ _ _ _ _ R72 J6 ltac:(cbn [cells_size csize Nat.add]; lia)) as J7. cbn [app] in J7.
  pose proof (rw_app_join _ _ _ _ _ R40 J7 ltac:(cbn [cells_size csize Nat.add]; lia)) as J8. cbn [app] in J8.
  destruct (rw_cells_forget _ _ _ _ J8) as (j' & J9). cbn [cells_size csize Nat.add] in J9.
  apply evt_done. do 21 eexists. exists m3, j'. split; [reflexivity|].
  split; [eapply munch_weaken; [|exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
  split; [exact WM|]. split; [exact MI3|]. split; [exact J9|].
  repeat (split; [eassumption|]). split; [apply rwc_mk; assumption|]. exact RG.
Qed.
