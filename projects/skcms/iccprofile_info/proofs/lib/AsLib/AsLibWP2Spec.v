(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim Hoare Frame LibDefs LibWP2Spec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsFuzzContract AsLibShadow AsLibDefs AsRtSpec.
Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_t1 := (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker.
(* [comment removed for export] *)
Local Ltac el_dm_pose x k := let v := eval vm_compute in k in lazymatch v with Zpos _ =>   (* [comment removed for export] *)
  lazymatch goal with _ : (x = k * (x / k) + x mod k)%Z |- _ => fail | _ =>
    pose proof (Z.div_mod x k ltac:(vm_compute; discriminate)); pose proof (Z.mod_pos_bound x k ltac:(vm_compute; reflexivity)) end end.
Local Ltac el_dm := repeat match goal with
  | |- context [ (?x / ?k)%Z ] => el_dm_pose x k
  | |- context [ (?x mod ?k)%Z ] => el_dm_pose x k
  | H : ?T |- _ => lazymatch T with (_ <= _)%Z => idtac | (_ < _)%Z => idtac | @eq Z _ _ => idtac | _ /\ _ => idtac | _ \/ _ => idtac end;
      match T with context [ (?x / ?k)%Z ] => el_dm_pose x k | context [ (?x mod ?k)%Z ] => el_dm_pose x k end
  end.
Local Ltac el_lia_core3 := first [ el_t1 | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
Local Ltac el_lia_core := first [ el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section Specs.
Variable segs : list Segment.
Variable L : as_lib.
Variable ceil : Z.   (* [comment removed for export] *)

#[local] Notation cell32 := (cell32 segs).
#[local] Notation cell64 := (cell64 segs).
#[local] Notation cell8 := (cell8 segs).
#[local] Notation writable := (writable segs).
#[local] Notation curve_ok := (curve_ok segs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mftc_a2b_pre_as (data : word) (len : Z) (bs : list byte) (mft A : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let a := bv_unsigned A in
  getr regs 10 = mft /\ getr regs 11 = A /\
  as_data_ok ceil mem data len bs /\ inDATA data len (bv_unsigned mft) 48 /\
  writable mem a 400 /\ (a mod 8 = 0) /\ heapish ceil a 400 /\ shz mem a 50 /\
  (bv_unsigned data + len <= a \/ a + 400 <= bv_unsigned data) /\
  as_sb segs L mem /\
  (exists sp, getr regs 2 = sp /\ as_frame segs ceil mem sp 16).

Definition mftc_a2b_post_as (data : word) (len : Z) (bs : list byte) (mft A : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let a := bv_unsigned A in
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned (getr regs 2) - 16), 16); (Z_to_bv 64 (a + 144), 8); (Z_to_bv 64 (a + 296), 8)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
  (r = 1 ->
     exists ic g,
       1 <= ic <= 4 /\ 2 <= g <= 255 /\
       cell32 mem' (a + 144) ic /\ cell32 mem' (a + 296) 0 /\ cell32 mem' (a + 300) 3 /\
       (forall i, 0 <= i < ic -> cell8 mem' (a + 148 + i) g)).

Definition read_mft_common_a2b_contract_as : Prop :=
  forall data len bs mft A,
    fn_contract segs (al_mftc_a2b L) (mftc_a2b_pre_as data len bs mft A) (mftc_a2b_post_as data len bs mft A).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mftc_b2a_pre_as (data : word) (len : Z) (bs : list byte) (mft B : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let b := bv_unsigned B in
  getr regs 10 = mft /\ getr regs 11 = B /\
  as_data_ok ceil mem data len bs /\ inDATA data len (bv_unsigned mft) 48 /\
  writable mem b 400 /\ (b mod 8 = 0) /\ heapish ceil b 400 /\ shz mem b 50 /\
  (bv_unsigned data + len <= b \/ b + 400 <= bv_unsigned data) /\
  as_sb segs L mem /\
  (exists sp, getr regs 2 = sp /\ as_frame segs ceil mem sp 16).

Definition mftc_b2a_post_as (data : word) (len : Z) (bs : list byte) (mft B : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let b := bv_unsigned B in
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned (getr regs 2) - 16), 16); (Z_to_bv 64 (b + 96), 8); (Z_to_bv 64 (b + 392), 8)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
  (r = 1 ->
     exists oc g,
       3 <= oc <= 4 /\ 2 <= g <= 255 /\
       cell32 mem' (b + 96) 3 /\ cell32 mem' (b + 100) 0 /\ cell32 mem' (b + 396) oc /\
       (forall i, 0 <= i < 3 -> cell8 mem' (b + 392 + i) g)).

Definition read_mft_common_b2a_contract_as : Prop :=
  forall data len bs mft B,
    fn_contract segs (al_mftc_b2a L) (mftc_b2a_pre_as data len bs mft B) (mftc_b2a_post_as data len bs mft B).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ITAB_FR : Z := 112.

Definition itab_a2b_pre_as (data : word) (len : Z) (bs : list byte)
    (sp tb A : word) (maxlen bw ite ote ic : Z) (gps : list Z)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let a := bv_unsigned A in
  getr regs 2 = sp /\ getr regs 10 = tb /\ getr regs 11 = Z_to_bv 64 maxlen /\
  getr regs 12 = Z_to_bv 64 bw /\ getr regs 13 = Z_to_bv 64 ite /\ getr regs 14 = Z_to_bv 64 ote /\
  getr regs 15 = A /\
  as_data_ok ceil mem data len bs /\ 0 <= maxlen /\ inDATA data len (bv_unsigned tb) maxlen /\
  (bw = 1 \/ bw = 2) /\ 2 <= ite <= 4096 /\ 2 <= ote <= 4096 /\
  1 <= ic <= 4 /\ Z.of_nat (length gps) = ic /\ Forall (fun g => 2 <= g <= 255) gps /\
  cell32 mem (a + 144) ic /\ cell32 mem (a + 300) 3 /\
  (forall i, 0 <= i < ic -> cell8 mem (a + 148 + i) (nth (Z.to_nat i) gps 0)) /\
  writable mem (a + 0) 400 /\ (a mod 8 = 0) /\ heapish ceil a 400 /\ shz mem a 50 /\
  (bv_unsigned data + len <= a \/ a + 400 <= bv_unsigned data) /\
  as_sb segs L mem /\ as_frame segs ceil mem sp ITAB_FR.

Definition itab_a2b_post_as (data : word) (len : Z) (bs : list byte)
    (sp tb A : word) (maxlen bw ite ote ic : Z) (gps : list Z)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let a := bv_unsigned A in
  let stk := (Z_to_bv 64 (bv_unsigned sp - ITAB_FR), ITAB_FR) in
  exists r, getr regs' 10 = Z_to_bv 64 r /\
  ((r = 0 /\ frame_mod mem mem' [stk])
   \/ (r = 1 /\
       frame_mod mem mem' [stk; (Z_to_bv 64 a, 32 * ic); (Z_to_bv 64 (a + 128), 16); (Z_to_bv 64 (a + 304), 96)] /\
       (forall i, 0 <= i < ic -> curve_ok mem' data len (a + 32 * i)) /\
       (forall i, 0 <= i < 3 -> curve_ok mem' data len (a + 304 + 32 * i)) /\
       exists g8 g16 : word,
         cell64 mem' (a + 128) g8 /\ cell64 mem' (a + 136) g16 /\
         (bw = 1 -> bv_unsigned g16 = 0 /\ inDATA data len (bv_unsigned g8) (3 * zprod gps)) /\
         (bw = 2 -> bv_unsigned g8 = 0 /\ inDATA data len (bv_unsigned g16) (2 * (3 * zprod gps))))).

Definition init_tables_a2b_contract_as : Prop :=
  forall data len bs sp tb A maxlen bw ite ote ic gps,
    fn_contract segs (al_itab_a2b L)
      (itab_a2b_pre_as data len bs sp tb A maxlen bw ite ote ic gps)
      (itab_a2b_post_as data len bs sp tb A maxlen bw ite ote ic gps).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition itab_b2a_pre_as (data : word) (len : Z) (bs : list byte)
    (sp tb B : word) (maxlen bw ite ote oc : Z) (gps : list Z)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let b := bv_unsigned B in
  getr regs 2 = sp /\ getr regs 10 = tb /\ getr regs 11 = Z_to_bv 64 maxlen /\
  getr regs 12 = Z_to_bv 64 bw /\ getr regs 13 = Z_to_bv 64 ite /\ getr regs 14 = Z_to_bv 64 ote /\
  getr regs 15 = B /\
  as_data_ok ceil mem data len bs /\ 0 <= maxlen /\ inDATA data len (bv_unsigned tb) maxlen /\
  (bw = 1 \/ bw = 2) /\ 2 <= ite <= 4096 /\ 2 <= ote <= 4096 /\
  3 <= oc <= 4 /\ Z.of_nat (length gps) = 3 /\ Forall (fun g => 2 <= g <= 255) gps /\
  cell32 mem (b + 96) 3 /\ cell32 mem (b + 396) oc /\
  (forall i, 0 <= i < 3 -> cell8 mem (b + 392 + i) (nth (Z.to_nat i) gps 0)) /\
  writable mem (b + 0) 400 /\ (b mod 8 = 0) /\ heapish ceil b 400 /\ shz mem b 50 /\
  (bv_unsigned data + len <= b \/ b + 400 <= bv_unsigned data) /\
  as_sb segs L mem /\ as_frame segs ceil mem sp ITAB_FR.

Definition itab_b2a_post_as (data : word) (len : Z) (bs : list byte)
    (sp tb B : word) (maxlen bw ite ote oc : Z) (gps : list Z)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let b := bv_unsigned B in
  let stk := (Z_to_bv 64 (bv_unsigned sp - ITAB_FR), ITAB_FR) in
  exists r, getr regs' 10 = Z_to_bv 64 r /\
  ((r = 0 /\ frame_mod mem mem' [stk])
   \/ (r = 1 /\
       frame_mod mem mem' [stk; (Z_to_bv 64 b, 96); (Z_to_bv 64 (b + 248), 32 * oc); (Z_to_bv 64 (b + 376), 16)] /\
       (forall i, 0 <= i < 3 -> curve_ok mem' data len (b + 32 * i)) /\
       (forall i, 0 <= i < oc -> curve_ok mem' data len (b + 248 + 32 * i)) /\
       exists g8 g16 : word,
         cell64 mem' (b + 376) g8 /\ cell64 mem' (b + 384) g16 /\
         (bw = 1 -> bv_unsigned g16 = 0 /\ inDATA data len (bv_unsigned g8) (oc * zprod gps)) /\
         (bw = 2 -> bv_unsigned g8 = 0 /\ inDATA data len (bv_unsigned g16) (2 * (oc * zprod gps))))).

Definition init_tables_b2a_contract_as : Prop :=
  forall data len bs sp tb B maxlen bw ite ote oc gps,
    fn_contract segs (al_itab_b2a L)
      (itab_b2a_pre_as data len bs sp tb B maxlen bw ite ote oc gps)
      (itab_b2a_post_as data len bs sp tb B maxlen bw ite ote oc gps).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A2B_D : Z := 2528.

Definition a2b_pre_as (data : word) (len : Z) (bs : list byte) (sp T A : word) (pcs : Z)
    (fs : Z) (ch : chain)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let a := bv_unsigned A in let t := bv_unsigned T in let s := bv_unsigned sp in
  let AB := al_abi L in
  getr regs 2 = sp /\ getr regs 10 = T /\ getr regs 11 = A /\ getr regs 12 = Z_to_bv 64 pcs /\
  getr regs 13 = Z_to_bv 64 (bv_unsigned data + len) /\ getr regs 4 = Z_to_bv 64 (aa_tp AB) /\
  (pcs = 0 \/ pcs = 1) /\
  as_data_ok ceil mem data len bs /\
  (exists ty, cell32 mem (t + 4) ty) /\ LibDefs.tag_ok segs mem data len t /\
  (t mod 8 = 0) /\ stackish ceil t 24 /\ shz mem t 3 /\ (s <= t) /\
  writable mem a 400 /\ (a mod 8 = 0) /\ heapish ceil a 400 /\ shz mem a 50 /\
  Forall (fun off => shwz mem (a + off + 12) 20) a2b_curve_offsets /\
  (fs + FS_FRAMES5 <= a) /\ (a + 400 <= fs + FS_SIZE) /\
  Forall (fun off => curve_ok mem data len (a + off)) a2b_curve_offsets /\
  (exists g8 g16, cell64 mem (a + 128) g8 /\ cell64 mem (a + 136) g16) /\
  as_frame segs ceil mem sp A2B_D /\ shz mem (s - A2B_D) (A2B_D / 8) /\
  as_env segs ceil AB fs ch mem /\ fs_hdr segs ceil AB fs mem /\ fs_writable segs fs mem /\
  (exists h, acellw segs mem (fs + FS_HINT0) h) /\ fs_flags0_but fs [] mem /\
  (bv_unsigned data + len <= fs \/ fs + FS_SIZE <= bv_unsigned data) /\
  (bv_unsigned data + len <= a \/ a + 400 <= bv_unsigned data).

Definition a2b_post_as (data : word) (len : Z) (bs : list byte) (sp T A : word) (pcs : Z)
    (fs : Z) (ch : chain)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let a := bv_unsigned A in
  frame_mod mem mem' ([(Z_to_bv 64 (bv_unsigned sp - A2B_D), A2B_D); (Z_to_bv 64 a, 400)] ++ fs_mod0 fs) /\
  fs_flags0_but fs [] mem' /\ (exists h', acellw segs mem' (fs + FS_HINT0) h') /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
  (r = 1 ->
     Forall (fun off => curve_ok mem' data len (a + off)) a2b_curve_offsets /\
     a2b_grid_ok segs mem' data len a).

Definition read_a2b_contract_as : Prop :=
  forall data len bs sp T A pcs fs ch,
    fn_contract segs (al_a2b L) (a2b_pre_as data len bs sp T A pcs fs ch) (a2b_post_as data len bs sp T A pcs fs ch).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition b2a_pre_as (data : word) (len : Z) (bs : list byte) (sp T B : word) (pcs : Z)
    (fs : Z) (ch : chain)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let b := bv_unsigned B in let t := bv_unsigned T in let s := bv_unsigned sp in
  let AB := al_abi L in
  getr regs 2 = sp /\ getr regs 10 = T /\ getr regs 11 = B /\ getr regs 12 = Z_to_bv 64 pcs /\
  getr regs 13 = Z_to_bv 64 (bv_unsigned data + len) /\ getr regs 4 = Z_to_bv 64 (aa_tp AB) /\
  (pcs = 0 \/ pcs = 1) /\
  as_data_ok ceil mem data len bs /\
  (exists ty, cell32 mem (t + 4) ty) /\ LibDefs.tag_ok segs mem data len t /\
  (t mod 8 = 0) /\ stackish ceil t 24 /\ shz mem t 3 /\ (s <= t) /\
  writable mem b 400 /\ (b mod 8 = 0) /\ heapish ceil b 400 /\ shz mem b 50 /\
  Forall (fun off => shwz mem (b + off + 12) 20) b2a_curve_offsets /\
  (fs + FS_FRAMES5 <= b) /\ (b + 400 <= fs + FS_SIZE) /\
  Forall (fun off => curve_ok mem data len (b + off)) b2a_curve_offsets /\
  as_frame segs ceil mem sp A2B_D /\ shz mem (s - A2B_D) (A2B_D / 8) /\
  as_env segs ceil AB fs ch mem /\ fs_hdr segs ceil AB fs mem /\ fs_writable segs fs mem /\
  (exists h, acellw segs mem (fs + FS_HINT0) h) /\ fs_flags0_but fs [] mem /\
  (bv_unsigned data + len <= fs \/ fs + FS_SIZE <= bv_unsigned data) /\
  (bv_unsigned data + len <= b \/ b + 400 <= bv_unsigned data).

Definition b2a_post_as (data : word) (len : Z) (bs : list byte) (sp T B : word) (pcs : Z)
    (fs : Z) (ch : chain)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let b := bv_unsigned B in
  frame_mod mem mem' ([(Z_to_bv 64 (bv_unsigned sp - A2B_D), A2B_D); (Z_to_bv 64 b, 400)] ++ fs_mod0 fs) /\
  fs_flags0_but fs [] mem' /\ (exists h', acellw segs mem' (fs + FS_HINT0) h') /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
  (r = 1 -> Forall (fun off => curve_ok mem' data len (b + off)) b2a_curve_offsets).

Definition read_b2a_contract_as : Prop :=
  forall data len bs sp T B pcs fs ch,
    fn_contract segs (al_b2a L) (b2a_pre_as data len bs sp T B pcs fs ch) (b2a_post_as data len bs sp T B pcs fs ch).

End Specs.
