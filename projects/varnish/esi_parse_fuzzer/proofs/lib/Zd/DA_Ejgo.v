(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Image MState Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Spec ShapeAlg PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j AIcpnnp AGlofzw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_Img A_ImgAny.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Ey6n DA_Eg3i DA_Cells DA_Ldix DA_Entry DA_Mib4 DA_Inv.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cells_at_pick : forall segs v A cs k c,
  cells_at segs v A cs -> cell_at cs k = Some c -> cells_at segs v (A + Z.of_nat k) [c].
Proof.
  intros segs v A cs k c [WF B] Hk.
  (first [ pose proof ((cell_at_split cs k c c Hk)) as dR_1; dex2 dR_1 as pre post; dand3 dR_1 as E SZ _ | pose proof ((cell_at_split cs k c c Hk)) as dR_1; dand5 dR_1 as pre post E SZ _ | destruct (cell_at_split cs k c c Hk) as (pre & post & E & SZ & _) ]). rewrite E in WF, B.
  apply cells_wf_app in WF as [W1 [W2 W3]].
  rewrite cells_bytes_app in B. apply bytes_at_app in B as [_ B]. cbn [cells_bytes] in B. apply bytes_at_app in B as [B _].
  rewrite (cells_bytes_length pre W1), SZ in B.
  split; [cbn; split; [exact W2| exact I]|]. cbn [cells_bytes]. rewrite app_nil_r. exact B.
Qed.

Lemma ro_cells_pick : forall segs v A cs k c, ro_cells segs v A cs -> cell_at cs k = Some c -> ro_cells segs v (A + Z.of_nat k) [c].
Proof. intros. eapply cells_at_pick; eassumption. Qed.
Lemma rw_cells_pick : forall segs v A cs k c, rw_cells segs v A cs -> cell_at cs k = Some c -> rw_cells segs v (A + Z.of_nat k) [c].
Proof.
  intros segs v A cs k c [C W] Hk. split; [eapply cells_at_pick; eassumption|].
  (first [ pose proof ((cell_at_split cs k c c Hk)) as dR_2; dex2 dR_2 as pre post; dand3 dR_2 as E SZ _ | pose proof ((cell_at_split cs k c c Hk)) as dR_2; dand5 dR_2 as pre post E SZ _ | destruct (cell_at_split cs k c c Hk) as (pre & post & E & SZ & _) ]).
  (first [ dand3 W as H0 H1 H | destruct W as (H0 & H1 & H) ]). assert (LE : (k + csize c <= cells_size cs)%nat).
  { rewrite E, cells_size_app. cbn [cells_size]. lia. }
  split; [lia|]. split; [cbn [cells_size Nat.add]; lia|]. intros i Hi. cbn [cells_size] in Hi.
  replace (A + Z.of_nat k + i) with (A + (Z.of_nat k + i)) by lia. apply H. lia.
Qed.
(* [comment removed for export] *)
Lemma ro_cells_pick2 : forall segs v A cs k c1 c2,
  ro_cells segs v A cs -> cell_at cs k = Some c1 -> cell_at cs (k + csize c1) = Some c2 ->
  ro_cells segs v (A + Z.of_nat k) [c1; c2].
Proof.
  intros segs v A cs k c1 c2 RO H1 H2.
  pose proof (ro_cells_pick segs v A cs k c1 RO H1) as [W1 B1]. pose proof (ro_cells_pick segs v A cs _ c2 RO H2) as [W2 B2].
  split; [cbn in *; tauto|]. cbn [cells_bytes]. rewrite app_nil_r. apply bytes_at_app. split; [| ].
  - cbn [cells_bytes] in B1. rewrite app_nil_r in B1. exact B1.
  - cbn [cells_bytes] in B2. rewrite app_nil_r in B2. rewrite (cbytes_length c1) by (cbn in W1; tauto).
    replace (A + Z.of_nat k + Z.of_nat (csize c1)) with (A + Z.of_nat (k + csize c1)) by lia. exact B2.
Qed.
Lemma rw_cells_pick2 : forall segs v A cs k c1 c2,
  rw_cells segs v A cs -> cell_at cs k = Some c1 -> cell_at cs (k + csize c1) = Some c2 ->
  rw_cells segs v (A + Z.of_nat k) [c1; c2].
Proof.
  intros segs v A cs k c1 c2 RW H1 H2. split; [apply (ro_cells_pick2 segs v A cs k c1 c2 (proj1 RW) H1 H2)|].
  pose proof (rw_cells_pick segs v A cs k c1 RW H1) as [_ (X0 & X1 & X)]. pose proof (rw_cells_pick segs v A cs _ c2 RW H2) as [_ (Y0 & Y1 & Y)].
  cbn [cells_size Nat.add] in *. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (Z.lt_ge_cases i (Z.of_nat (csize c1))); [apply X; lia|].
  replace (A + Z.of_nat k + i) with (A + Z.of_nat (k + csize c1) + (i - Z.of_nat (csize c1))) by lia. apply Y. lia.
Qed.

(* [comment removed for export] *)
Lemma ro_cells_recast : forall segs v a cs cs', ro_cells segs v a cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> ro_cells segs v a cs'.
Proof. intros segs v a cs cs' [W B] W' E. split; [exact W'|]. rewrite E. exact B. Qed.

(* [comment removed for export] *)
Lemma file_clean_of_file_at : forall v F f,
  file_at v F f -> mf_lock f = -1 -> mf_wpos f = mf_wbase f -> mf_rpos f = mf_rend f ->
  file_clean v F (mf_wpos f) (mf_rpos f).
Proof.
  intros v F f FA HL HW HR. unfold file_at in FA. unfold file_clean.
  pose proof (fun k c H => ro_cells_pick rsegs v F (file_cells f) k c (proj1 FA) H) as P.
  split; [| split; [| split; [| split]]].
  - specialize (P 140%nat (C4 (Z_to_bv 64 (mf_lock f))) eq_refl). rewrite HL in P. change (Z.of_nat 140) with 140 in P.
    apply (ro_cells_recast _ _ _ _ _ P); [cbn; tauto|]. apply bytes_eq_of_unsigned. vm_compute. reflexivity.
  - exact (P 40%nat (C8 (mf_wpos f)) eq_refl).
  - rewrite HW. exact (P 56%nat (C8 (mf_wbase f)) eq_refl).
  - exact (P 8%nat (C8 (mf_rpos f)) eq_refl).
  - rewrite HR. exact (P 16%nat (C8 (mf_rend f)) eq_refl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rw_C1C1_any : forall (M : word -> option byte) a,
  image_bytes rsegs a 2 <> None -> wr_ok_b a 2 = true -> 0 <= a -> a + 2 <= 2^64 ->
  exists b1 b2, rw_cells rsegs M a [C1 b1; C1 b2].
Proof.
  intros M a IMG WB H0 H1. (first [ pose proof ((junk_bytes M a 2 IMG H0 H1)) as dR_4; dex1 dR_4 as junk; destruct dR_4 as [LJ BJ] | pose proof ((junk_bytes M a 2 IMG H0 H1)) as dR_4; dand3 dR_4 as junk LJ BJ | destruct (junk_bytes M a 2 IMG H0 H1) as (junk & LJ & BJ) ]).
  destruct junk as [|b1 [|b2 [|]]]; try (cbn in LJ; lia). exists b1, b2.
  split; [split; [cbn; tauto| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BJ]|].
  cbn [cells_size csize Nat.add]. apply (wr_at_of_b M a 2); assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gsh_okb (r : grec) : bool :=
  match clookup (gsh (g_beg r)) (cl_consts LPA) with
  | Some bs => (Z.of_nat (length bs) =? g_size_rz r / 8) && (0 <=? g_beg r) && (g_beg r <? 2^47)
  | None => false
  end.
Lemma gtab_gsh_ok : forallb gsh_okb gtab = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA}.   (* [comment removed for export] *)

#[using="AI Clg"] Lemma gshadows_of_consts : forall v, consts_hold LPA v -> exists bss, gshadows v gtab bss.
Proof.
  intros v CH. pose proof gtab_gsh_ok as OK. unfold gshadows.
  induction gtab as [|r l IH]; [exists []; constructor|].
  cbn [forallb] in OK. apply andb_prop in OK as [O1 O2]. destruct (IH O2) as [bss GB].
  unfold gsh_okb in O1. destruct (clookup (gsh (g_beg r)) (cl_consts LPA)) as [bs|] eqn:CL; [|discriminate].
  apply andb_prop in O1 as [O1 O4]. apply andb_prop in O1 as [O1 O3].
  apply Z.eqb_eq in O1. apply Z.leb_le in O3. apply Z.ltb_lt in O4.
  pose proof (consts_lookup v _ _ CH CL) as B.
  exists (bs :: bss). constructor; [| exact GB]. unfold gchunk.
  assert (LEN : length bs = Z.to_nat (g_size_rz r / 8)) by lia.
  split; [split; [cbn; split; [exact LEN| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B]|].
  cbn [cells_size csize Nat.add]. pose proof (bytes_at_bound _ _ _ _ B) as BB.
  split; [lia|]. split; [lia|]. intros i Hi. unfold wview, wa.
  (first [ dand3 B as _ _ B | destruct B as (_ & _ & B) ]). specialize (B (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in B by lia. unfold mrd, wa in B.
  destruct (v (Z_to_bv 64 (gsh (g_beg r) + i))) eqn:E; [discriminate|].
  exfalso. rewrite (as_seg_rom_outside LPA) in B; [| unfold in_image; cbn; rewrite unsigned_lit by (unfold gsh in *; lia); unfold gsh in *; lia].
  symmetry in B. apply nth_error_None in B. lia.
Qed.


  Ltac ccell CH a := apply (consts_lookup _ a _ CH); vm_compute; reflexivity.

  Lemma gtab_cells_wf : forall l, cells_wf (gtab_cells l).
  Proof. induction l as [|r l IH]; [exact I|]. cbn [gtab_cells grec_cells app]. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I. exact IH. Qed.

  Lemma dtor_consts_of : forall v, consts_hold LPA v -> dtor_consts v.
  Proof.
    intros v CH. unfold dtor_consts.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - eapply ro_cells_of_bytes_eq; [ccell CH 0xa9808| cbn; tauto| reflexivity].
    - apply ro_C8_of_bytes. ccell CH 0xa8b50.
    - apply ro_C8_of_bytes. ccell CH 0x144660.
    - (* [comment removed for export] *)
      assert (B1 : bytes_at rsegs v 0xa8b60 (le8 (wz 0x1466e8))) by ccell CH 0xa8b60.
      assert (B2 : bytes_at rsegs v 0xa8b68 (le8 (wz 0xb23b8))) by ccell CH 0xa8b68.
      assert (B3 : bytes_at rsegs v 0xa8b70 (le8 (wz 0xb4bb8))) by ccell CH 0xa8b70.
      assert (B4 : bytes_at rsegs v 0xa8b78 (le8 (wz 0xb58a8))) by ccell CH 0xa8b78.
      assert (B5 : bytes_at rsegs v 0xa8b80 (le8 (wz 0xb58b0))) by ccell CH 0xa8b80.
      assert (B6 : bytes_at rsegs v 0xa8b88 (le8 (wz 0xb58a0))) by ccell CH 0xa8b88.
      assert (B7 : bytes_at rsegs v 0xa8b90 (le8 (wz 0xaaa18))) by ccell CH 0xa8b90.
      split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
      repeat (apply bytes_at_app; split; [assumption|]; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add]); assumption.
    - (* [comment removed for export] *)
      assert (B : exists bs, clookup 0xb23b8 (cl_consts LPA) = Some bs /\ (28 <= length bs)%nat /\
                             map bv_unsigned (firstn 4 (skipn 24 bs)) = [1; 0; 0; 0]).
      { eexists. split; [vm_compute; reflexivity|]. split; [vm_compute; lia| vm_compute; reflexivity]. }
      (first [ dex1 B as bs; dand3 B as CL LEN EQ | dand4 B as bs CL LEN EQ | destruct B as (bs & CL & LEN & EQ) ]). pose proof (consts_lookup v _ _ CH CL) as BB.
      pose proof (bytes_at_sub v 0xb23b8 bs 24 4 BB ltac:(lia)) as B4.
      eapply ro_cells_of_bytes_eq; [exact B4| cbn; tauto|]. apply bytes_eq_of_unsigned. rewrite EQ. vm_compute. reflexivity.
    - (* [comment removed for export] *)
      assert (B : exists bs, clookup 0x1466e8 (cl_consts LPA) = Some bs /\ (128 <= length bs)%nat /\
                             map bv_unsigned (firstn 8 (skipn 120 bs)) = [255; 255; 255; 255; 255; 255; 255; 255]).   (* [comment removed for export] *)
      { eexists. split; [vm_compute; reflexivity|]. split; [vm_compute; lia| vm_compute; reflexivity]. }
      (first [ dex1 B as bs; dand3 B as CL LEN EQ | dand4 B as bs CL LEN EQ | destruct B as (bs & CL & LEN & EQ) ]). pose proof (consts_lookup v _ _ CH CL) as BB.
      pose proof (bytes_at_sub v 0x1466e8 bs 120 8 BB ltac:(lia)) as B8.
      eapply ro_cells_of_bytes_eq; [exact B8| cbn; tauto|]. apply bytes_eq_of_unsigned. rewrite EQ. vm_compute. reflexivity.
    - apply ro_C8_of_bytes. ccell CH 0xb4bb8.
    - eapply ro_cells_of_bytes_eq; [ccell CH 0xb5898| cbn; tauto| reflexivity].
    - eapply ro_cells_of_bytes_eq; [ccell CH 0xb441c| cbn; tauto| reflexivity].
    - apply ro_C8_of_bytes. ccell CH 0xaaa18.
    - (* [comment removed for export] *)
      assert (M1 : bytes_at rsegs v 0xb58a0 (le8 (wz 0x7fffffffffff))) by ccell CH 0xb58a0.
      assert (M2 : bytes_at rsegs v 0xb58a8 (le8 (wz 0))) by ccell CH 0xb58a8.
      assert (M3 : bytes_at rsegs v 0xb58b0 (le8 (wz 0))) by ccell CH 0xb58b0.
      split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
      repeat (apply bytes_at_app; split; [assumption|]; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add]); assumption.
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      eapply (ro_cells_of_bytes_eq v GMETA (cells_bytes (gtab_cells gtab)));
        [ apply (consts_lookup _ GMETA _ CH); vm_cast_no_check (@eq_refl (option (list byte)) (Some (cells_bytes (gtab_cells gtab))))
        | apply gtab_cells_wf | reflexivity ].
  Qed.

  (* [comment removed for export] *)
  Lemma rw_of_consts : forall v a cs bs, consts_hold LPA v -> clookup a (cl_consts LPA) = Some bs ->
    cells_wf cs -> cells_bytes cs = bs -> wr_ok_b a (cells_size cs) = true -> 0 <= a -> a + Z.of_nat (cells_size cs) <= 2^64 ->
    rw_cells rsegs v a cs.
  Proof.
    intros v a cs bs CH CL WF E WB H0 H1. split; [exact (ro_cells_of_bytes_eq v a bs cs (consts_lookup v _ _ CH CL) WF E)|].
    apply (wr_at_of_b v a (cells_size cs)); assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma exit_ready : forall A m md tid sof ini,
    ainv A m md -> ccells (aview A m) tid sof ini ->
    exists fin bss b1 b2 b3 b4 junk0 wp0 rp0 wp2 rp2, exit_cells (aview A m) tid ini fin bss b1 b2 b3 b4 junk0 wp0 rp0 wp2 rp2.
  Proof.
    (intros A m md tid sof ini AINV; (first [ intro dR_16; dand4 dR_16 as MC [fe [FOK FE]] SO TR | intros (MC & [fe [FOK FE]] & SO & TR) ])). set (v := aview A m) in *.
    pose proof (consts_hold_ainv LPA A m md AINV) as CH. change (aview A m) with v in CH.
    destruct MC. destruct TR as (I01 & TRI & INCB & SLOT & BF1 & BA1).   (* [comment removed for export] *)
    pose proof mc_fin as FIN. set (fin := Z_to_bv 8 0) in FIN. destruct (gshadows_of_consts v CH) as [bss GSH].
    (first [ pose proof ((rw_C1C1_any v ODR_A ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity) ltac:(unfold ODR_A; lia) ltac:(unfold ODR_A; lia))) as dR_8; dex2 dR_8 as b1 b2; rename dR_8 into OA | pose proof ((rw_C1C1_any v ODR_A ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity) ltac:(unfold ODR_A; lia) ltac:(unfold ODR_A; lia))) as dR_8; dand3 dR_8 as b1 b2 OA | destruct (rw_C1C1_any v ODR_A ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity) ltac:(unfold ODR_A; lia) ltac:(unfold ODR_A; lia)) as (b1 & b2 & OA) ]).
    (first [ pose proof ((rw_C1C1_any v ODR_B ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity) ltac:(unfold ODR_B; lia) ltac:(unfold ODR_B; lia))) as dR_9; dex2 dR_9 as b3 b4; rename dR_9 into OB | pose proof ((rw_C1C1_any v ODR_B ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity) ltac:(unfold ODR_B; lia) ltac:(unfold ODR_B; lia))) as dR_9; dand3 dR_9 as b3 b4 OB | destruct (rw_C1C1_any v ODR_B ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity) ltac:(unfold ODR_B; lia) ltac:(unfold ODR_B; lia)) as (b3 & b4 & OB) ]).
    (first [ dex2 mc_in as wp0 rp0; rename mc_in into FIN0 | dand3 mc_in as wp0 rp0 FIN0 | destruct mc_in as (wp0 & rp0 & FIN0) ]).
    (first [ dex2 FOK as w mo; destruct FOK as [-> Hw] | dand4 FOK as w mo -> Hw | destruct FOK as (w & mo & -> & Hw) ]).
    exists fin, bss, b1, b2, b3, b4, (repeat (Z_to_bv 8 0xf9) 2016), wp0, rp0, w, w0.
    constructor; try assumption.
    - lia.
    - exact (proj1 INCB).   (* [comment removed for export] *)
    - eapply ro_cells_of_bytes_eq; [ccell CH 0x146a60| cbn; tauto| reflexivity].
    - eapply ro_cells_of_bytes_eq; [ccell CH 0xa9848| cbn; tauto| reflexivity].
    - eapply ro_cells_of_bytes_eq; [ccell CH 0xa83d0| cbn; tauto| reflexivity].
    - eapply (rw_of_consts v 0xb1550); [exact CH| vm_compute; reflexivity| cbn; tauto| reflexivity| vm_compute; reflexivity| lia| cbn; lia].
    - eapply ro_cells_of_bytes_eq; [ccell CH 0xa8b40| cbn; tauto| reflexivity].
    - apply ro_C8_of_bytes. ccell CH 0xaa8a0.
    - apply dtor_consts_of. exact CH.
    - eapply (rw_of_consts v ELF_FLAG); [exact CH| vm_compute; reflexivity| cbn; tauto| reflexivity| vm_compute; reflexivity| unfold ELF_FLAG; lia| unfold ELF_FLAG; cbn; lia].
    - eapply (rw_of_consts v MU_GLOBALS); [exact CH| vm_compute; reflexivity| cbn; tauto| reflexivity| vm_compute; reflexivity| unfold MU_GLOBALS; lia| unfold MU_GLOBALS; cbn; lia].
    - (* [comment removed for export] *)
      pose proof (consts_lookup v 0x8000dac0 (repeat (Z_to_bv 8 0xf9) 2016) CH ltac:(vm_compute; reflexivity)) as B.
      assert (E : gsh GMETA = 0x8000dac0) by reflexivity. rewrite E.
      split; [split; [cbn [cells_wf cell_wf]; split; [apply repeat_length| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact B]|].
      cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. unfold wview, wa.
      (first [ dand3 B as _ _ B | destruct B as (_ & _ & B) ]). specialize (B (Z.to_nat i) ltac:(rewrite repeat_length; lia)). rewrite Z2Nat.id in B by lia. unfold mrd, wa in B.
      destruct (v (Z_to_bv 64 (2147539648 + i))) eqn:EV; [discriminate|].
      exfalso. rewrite (as_seg_rom_outside LPA) in B; [| unfold in_image; cbn; rewrite unsigned_lit by lia; lia].
      rewrite nth_error_repeat in B by lia. discriminate.
    - (* [comment removed for export] *) apply (file_clean_of_file_at v STDERR_F (mf_set_mode (mf_set_w stderr0 w w w) mo) FE); reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma stdout_exit_clause : forall v sof fds,
    stdout_at v sof -> (exists g, ro_cells rsegs v SSP_GUARD [C8 g]) -> ro_cells rsegs v SSP_GOT [C8 (wz SSP_GUARD)] ->
    (pending_of sof <> [] -> fd_lookup fds (wz 1) = Some (FdChannel (wz 1))) ->
       (pending_of sof = [] /\ exists wp1 rp1, file_clean v STDOUT_F wp1 rp1)
    \/ (exists wb wp wend bufp bufsz rp1 canary, stdout_pending v wb wp wend bufp bufsz rp1 canary (pending_of sof)
           /\ fd_lookup fds (wz 1) = Some (FdChannel (wz 1))).
  Proof.
    intros v sof fds SO [g CAN] GOT FD1. destruct sof as [|p]; cbn [pending_of stdout_at] in *.
    - left. split; [reflexivity|]. destruct SO as [FA _]. exists w0, w0.
      apply (file_clean_of_file_at v STDOUT_F stdout0 FA); reflexivity.
    - (first [ dex2 SO as mo junk; dand3 SO as FA BUF LEN | dand5 SO as mo junk FA BUF LEN | destruct SO as (mo & junk & FA & BUF & LEN) ]).
      destruct p as [|c p'] eqn:EP.
      + left. split; [reflexivity|]. exists (wz STDOUT_BUF), w0.
        pose proof (file_clean_of_file_at v STDOUT_F (stdout_buffered mo []) FA eq_refl) as FC. cbn [mf_wpos mf_wbase mf_rpos mf_rend stdout_buffered length Z.of_nat] in FC.
        rewrite Z.add_0_r in FC. apply FC; reflexivity.
      + right. rewrite <- EP in *. assert (NE : p <> []) by (rewrite EP; discriminate).
        assert (LP : (1 <= length p)%nat) by (rewrite EP; cbn; lia).
        exists STDOUT_BUF, (STDOUT_BUF + Z.of_nat (length p)), (wz (STDOUT_BUF + 1024)), (wz STDOUT_BUF), (wz 1024), w0, g.
        unfold file_at in FA.
        pose proof (fun k c H => ro_cells_pick rsegs v STDOUT_F (file_cells (stdout_buffered mo p)) k c (proj1 FA) H) as P.
        pose proof (fun k c1 c2 H1 H2 => ro_cells_pick2 rsegs v STDOUT_F (file_cells (stdout_buffered mo p)) k c1 c2 (proj1 FA) H1 H2) as P2.
        pose proof (fun k c1 c2 H1 H2 => rw_cells_pick2 rsegs v STDOUT_F (file_cells (stdout_buffered mo p)) k c1 c2 FA H1 H2) as W2.
        pose proof (fun k c H => rw_cells_pick rsegs v STDOUT_F (file_cells (stdout_buffered mo p)) k c FA H) as W1.
        split; [| exact (FD1 NE)]. constructor.
        * specialize (P 140%nat _ eq_refl). apply (ro_cells_recast _ _ _ _ _ P); [cbn; tauto|]. apply bytes_eq_of_unsigned. vm_compute. reflexivity.
        * exact (W2 32%nat _ _ eq_refl eq_refl).
        * exact (W1 56%nat _ eq_refl).
        * exact (P 72%nat _ eq_refl).
        * exact (P2 88%nat _ _ eq_refl eq_refl).
        * exact (P 120%nat _ eq_refl).
        * exact (P2 8%nat _ _ eq_refl eq_refl).
        * unfold STDOUT_BUF. lia.
        * lia.
        * lia.
        * pose proof (rw_cells_pick rsegs v STDOUT_BUF _ 0%nat _ BUF eq_refl) as [[_ B] _]. cbn [cells_bytes cbytes] in B.
          rewrite app_nil_r, Z.add_0_r in B. exact B.
        * split; [exact GOT| exact CAN].
  Qed.

  (* [comment removed for export] *)
  Lemma exit_via : exit_spec_stmt ->
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (A : AS) (lo tid : Z) (sof : stdout_form) (ini : Z),
      ainv A m md -> mem_inv rsegs (aview A m) -> ccells (aview A m) tid sof ini ->
      ro_cells rsegs (aview A m) SSP_GOT [C8 (wz SSP_GUARD)] ->
      tp = wz TPV ->
      stk rsegs (aview A m) lo (bv_unsigned sp) -> lo + EXIT_STACK <= bv_unsigned sp -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
      (pending_of sof <> [] -> fd_lookup (m_fds md) (wz 1) = Some (FdChannel (wz 1))) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (wz EXIT_ENTRY) fc None m (seg_rom rsegs)) md)
                (t_emit (W 1 (pending_of sof)) (t_exit (bv_and a0 (wz 255)) (m_fs md))).
  Proof.
    intros EXIT. intros until ini. intros AINV MI CC GOT TP ST LO CEIL SPH FD1.
    (first [ pose proof ((exit_ready A m md tid sof ini AINV CC)) as dR_14; dex11 dR_14 as fin bss b1 b2 b3 b4 junk0 wp0 rp0 wp2 rp2; rename dR_14 into EC | pose proof ((exit_ready A m md tid sof ini AINV CC)) as dR_14; dand12 dR_14 as fin bss b1 b2 b3 b4 junk0 wp0 rp0 wp2 rp2 EC | destruct (exit_ready A m md tid sof ini AINV CC) as (fin & bss & b1 & b2 & b3 & b4 & junk0 & wp0 & rp0 & wp2 & rp2 & EC) ]).
    pose proof (as_minv LPA A m md AINV) as [HMI HH]. pose proof (as_hull_segs LPA A m md AINV) as HOFF.
    (first [ dand4 CC as MC FE SO TR | destruct CC as (MC & FE & SO & TR) ]). pose proof (mc_canary _ _ MC) as CAN.
    destruct (stdout_exit_clause (aview A m) sof (m_fds md) SO CAN GOT FD1) as [CL|PN].
    - destruct CL as [E0 CL]. rewrite E0.
      eapply (EXIT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md
                   (ahull A) (alhull A) (aeager A) lo tid ini fin bss b1 b2 b3 b4 junk0 wp0 rp0 wp2 rp2 []);
        try eassumption. left. split; [reflexivity| exact CL].
    - eapply (EXIT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md
                   (ahull A) (alhull A) (aeager A) lo tid ini fin bss b1 b2 b3 b4 junk0 wp0 rp0 wp2 rp2 (pending_of sof));
        try eassumption. right. exact PN.
  Qed.
End S.
