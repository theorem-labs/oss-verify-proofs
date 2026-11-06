(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim Hoare Frame LibDefs FuzzContract.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsFuzzContract AsLibShadow.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record as_lib : Type := AL {
  al_abi      : as_abi;  (* [comment removed for export] *)
  (* [comment removed for export] *)
  al_fuzz     : Z;  al_rte : Z;  al_classify : Z;  al_tfeval : Z;  al_evalcurve : Z;
  al_gettag   : Z;  al_tagxyz : Z;  al_getidx : Z;  al_parse : Z;  al_rcurve : Z;
  al_xyzd50   : Z;  al_a2b : Z;  al_b2a : Z;  al_fitlin : Z;  al_canon : Z;
  al_mftc_a2b : Z;  al_itab_a2b : Z;  al_rcurves : Z;  al_mftc_b2a : Z;  al_itab_b2a : Z;
  (* [comment removed for export] *)
  al_stkmalloc0 : Z;  al_stkmalloc5 : Z;  al_stkfree5 : Z;
  al_setsh00  : Z;  al_setshf8 : Z;  al_imemset : Z;  al_imemcpy : Z;
  al_musl_memset : Z;  al_musl_memcpy : Z;
  (* [comment removed for export] *)
  al_curve_bytes : Z;    (* [comment removed for export] *)
  al_jt_classify : Z;    (* [comment removed for export] *)
  al_f5pat    : Z        (* [comment removed for export] *)
}.

Definition as_asan : as_lib := AL asan_abi
  0x7fee8 0x80328 0x80624 0x80a14 0x80de4
  0x81018 0x81360 0x81624 0x81950 0x82814
  0x838f0 0x83980 0x851b4 0x869e8 0x86d9c
  0x8704c 0x87208 0x87588 0x87668 0x87828
  0x3c8d4 0x3ca48 0x3cc54
  0x53ef4 0x54014 0x514d0 0x51034
  0x98220 0x97e1c
  0x20ea0 0x20e10 0x10338.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition heapish (ceil a n : Z) : Prop := appm a n /\ (a + n <= ceil)%Z.
Definition stackish (ceil a n : Z) : Prop := (AS_STKLO <= ceil <= a)%Z /\ (a + n <= 2 ^ 47)%Z.

Lemma app_shrink : forall a n a' m, appm a n -> (a <= a')%Z -> (0 <= m)%Z -> (a' + m <= a + n)%Z -> appm a' m.
Proof. intros a n a' m (H1 & H2 & H3 & H4 & H5) Ha Hm Hb. unfold appm. lia. Qed.
Lemma heapish_shrink : forall ceil a n a' m, heapish ceil a n -> (a <= a')%Z -> (0 <= m)%Z -> (a' + m <= a + n)%Z -> heapish ceil a' m.
Proof. intros ceil a n a' m [H1 H2] Ha Hm Hb. split; [eapply app_shrink; eassumption | lia]. Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition env_cells (A : as_abi) (mem : word -> option byte) : Prop :=
  (forall a v, In (a, v) (aa_c64 A) -> acell segs mem a 8 v) /\
  (forall a v, In (a, v) (aa_c32 A) -> acell segs mem a 4 v) /\
  (forall a v, In (a, v) (aa_c8 A) -> acell segs mem a 1 v) /\
  (forall a, In a (aa_r64 A) -> areadable segs mem a 8).

Definition env_shb (A : as_abi) (mem : word -> option byte) : Prop :=
  forall a v, In (a, v) (aa_shb A) -> mem (Z_to_bv 64 a) = Some (Z_to_bv 8 v).

Definition env_ro (A : as_abi) (mem : word -> option byte) : Prop :=
  forall lo hi i, In (lo, hi) (aa_ro A) -> (lo <= i < hi)%Z -> mem (Z_to_bv 64 i) = None.

(* [comment removed for export] *)
Record chain : Type := CH { ch_ctx : word; ch_thr : word; ch_t48 : word; ch_t56 : word;
                            ch_dtls : word; ch_v24 : word }.

Definition env_chain (ceil : Z) (A : as_abi) (fs : Z) (c : chain) (mem : word -> option byte) : Prop :=
  acellw segs mem (aa_tsdv A) (ch_ctx c) /\ heap_cell_ok ceil (bv_unsigned (ch_ctx c) + 152) fs /\
  acellw segs mem (bv_unsigned (ch_ctx c) + 152) (ch_thr c) /\
  heap_cell_ok ceil (bv_unsigned (ch_thr c) + 48) fs /\ heap_cell_ok ceil (bv_unsigned (ch_thr c) + 56) fs /\
  acellw segs mem (bv_unsigned (ch_thr c) + 48) (ch_t48 c) /\ acellw segs mem (bv_unsigned (ch_thr c) + 56) (ch_t56 c) /\
  acellw segs mem (aa_tp A + 0x8) (ch_dtls c) /\ (0 < bv_unsigned (ch_dtls c) < 2 ^ 64 - 1)%Z /\
  heap_cell_ok ceil (bv_unsigned (ch_dtls c) + 24) fs /\
  acellw segs mem (bv_unsigned (ch_dtls c) + 24) (ch_v24 c) /\ (bv_unsigned (ch_v24 c) <> 0)%Z.

Definition as_env (ceil : Z) (A : as_abi) (fs : Z) (c : chain) (mem : word -> option byte) : Prop :=
  env_cells A mem /\ env_shb A mem /\ env_ro A mem /\ env_chain ceil A fs c mem.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fs_hdr (ceil : Z) (A : as_abi) (fs : Z) (mem : word -> option byte) : Prop :=
  acell segs mem (aa_tp A + 0) 8 fs /\ acell segs mem (fs + FS_SSL) 8 20 /\ acell segs mem (fs + FS_NEEDSGC) 1 0 /\
  appm fs FS_SIZE /\ (fs + FS_SIZE <= ceil)%Z /\ (fs mod 4096 = 0)%Z.

(* [comment removed for export] *)
Definition fs_flags0_but (fs : Z) (busy : list Z) (mem : word -> option byte) : Prop :=
  forall i, (0 <= i < FS_FLAGS0_LEN)%Z -> ~ In i busy -> mem (Z_to_bv 64 (fs + FS_FLAGS0 + i)) = Some (Z_to_bv 8 0).
Definition fs_flags5_zero (fs : Z) (mem : word -> option byte) : Prop :=
  azero mem (fs + FS_FLAGS5) FS_FLAGS5_LEN.

Definition fs_writable (fs : Z) (mem : word -> option byte) : Prop :=
  awritable segs mem (fs + FS_HINT0) 8 /\ awritable segs mem (fs + FS_HINT5) 8 /\
  awritable segs mem (fs + FS_FLAGS0) FS_FLAGS0_LEN /\ awritable segs mem (fs + FS_FLAGS5) FS_FLAGS5_LEN /\
  awritable segs mem (fs + FS_FRAMES0) FS_FRAMES_LEN /\ awritable segs mem (fs + FS_FRAMES5) FS_FRAMES_LEN /\
  awritable segs mem (AS_SB + (fs + FS_FRAMES0) / 8) FS_SHFRAMES_LEN /\
  awritable segs mem (AS_SB + (fs + FS_FRAMES5) / 8) FS_SHFRAMES_LEN.

(* [comment removed for export] *)
Definition frame0 (fs pos : Z) : Z := (fs + FS_FRAMES0 + 64 * pos)%Z.
Definition frame5 (fs pos : Z) : Z := (fs + FS_FRAMES5 + 2048 * pos)%Z.
Definition pos0 (h : word) : Z := (bv_unsigned h mod 16384)%Z.
Definition pos5 (h : word) : Z := (bv_unsigned h mod 512)%Z.

(* [comment removed for export] *)
Definition fs_mod0 (fs : Z) : list (word * Z) :=
  [ (Z_to_bv 64 (fs + FS_HINT0), 8); (Z_to_bv 64 (fs + FS_FLAGS0), FS_FLAGS0_LEN);
    (Z_to_bv 64 (fs + FS_FRAMES0), FS_FRAMES_LEN); (Z_to_bv 64 (AS_SB + (fs + FS_FRAMES0) / 8), FS_SHFRAMES_LEN) ]%Z.
Definition fs_mod5 (fs : Z) : list (word * Z) :=
  [ (Z_to_bv 64 (fs + FS_HINT5), 8); (Z_to_bv 64 (fs + FS_FLAGS5), FS_FLAGS5_LEN);
    (Z_to_bv 64 (fs + FS_FRAMES5), FS_FRAMES_LEN); (Z_to_bv 64 (AS_SB + (fs + FS_FRAMES5) / 8), FS_SHFRAMES_LEN) ]%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition as_frame (ceil : Z) (mem : word -> option byte) (sp : word) (d : Z) : Prop :=
  stackish ceil (bv_unsigned sp - d) d /\ (bv_unsigned sp mod 16 = 0)%Z /\ writable segs mem (bv_unsigned sp - d) d.

(* [comment removed for export] *)
Definition as_data_ok (ceil : Z) (mem : word -> option byte) (data : word) (len : Z) (bs : list byte) : Prop :=
  data_ok mem data len bs /\ heapish ceil (bv_unsigned data) len /\ (bv_unsigned data mod 16 = 0)%Z /\
  shdata mem (bv_unsigned data) len.

(* [comment removed for export] *)
Definition as_sb (L : as_lib) (mem : word -> option byte) : Prop :=
  exists got cellp, (nth_error (aa_c64 (al_abi L)) 0 = Some (got, cellp)) /\
                    (nth_error (aa_c64 (al_abi L)) 1 = Some (cellp, AS_SB)) /\
                    sbcell segs got cellp mem.

Lemma as_sb_asan : forall mem, as_sb as_asan mem <-> sbcell segs 0x9eaf0 0xa6bb8 mem.
Proof.
  intros mem. unfold as_sb. cbn. split.
  - intros (got & cellp & H1 & H2 & H). congruence.
  - intros H. exists 0x9eaf0%Z, 0xa6bb8%Z. auto.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac expand_cells H :=
  repeat lazymatch goal with
  | |- _ /\ _ => split; [apply H; cbn; tauto | ]
  | |- _ => first [apply H; cbn; tauto | exact I]
  end.

Lemma asan_cells64 : forall mem, env_cells asan_abi mem ->
  acell segs mem 0x9eaf0 8 0xa6bb8 /\ acell segs mem 0xa6bb8 8 AS_SB /\ acell segs mem 0x9eb48 8 0xa6bc0 /\
  acell segs mem 0x9eb10 8 0xa0950 /\ acell segs mem 0xa0950 8 0x98220 /\ acell segs mem 0xa0948 8 0x97e1c /\
  acell segs mem 0x9f658 8 0xa7899 /\ acell segs mem 0xa0888 8 0x98a10 /\ acell segs mem 0x9f7d0 8 1 /\
  acell segs mem 0x9f7d8 8 0xfffffffffffff800 /\ acell segs mem 0x9eaf8 8 0xa78a8 /\ acell segs mem 0xa78a8 8 0 /\
  acell segs mem 0x9eb00 8 0xa78b0 /\ acell segs mem 0x9eb08 8 0xa78a0 /\ acell segs mem 0xa78a0 8 0x7fffffffffff /\
  acell segs mem 0x9eae0 8 0x1386e8 /\ acell segs mem 0x9eb40 8 0x136658 /\ acell segs mem 0x9f7e0 8 0x8 /\
  acell segs mem 0x5d9b68 8 0x5d9b90 /\ acell segs mem 0x5d9b98 8 0x5da370 /\ acell segs mem 0x5d9b18 8 0x5faf18 /\
  acell segs mem 0xa6bc0 4 1 /\ acell segs mem 0xa6424 4 0 /\ acell segs mem 0x136658 4 0 /\
  acell segs mem 0xa7898 1 1 /\ acell segs mem 0xa7899 1 1 /\ acell segs mem 0xa6420 1 1 /\ acell segs mem 0x138771 1 1 /\
  areadable segs mem 0xa78b0 8.
Proof.
  intros mem (C64 & C32 & C8 & R64).
  repeat lazymatch goal with
  | |- acell _ _ _ 8 _ /\ _ => split; [apply C64; cbn; tauto | ]
  | |- acell _ _ _ 4 _ /\ _ => split; [apply C32; cbn; tauto | ]
  | |- acell _ _ _ 1 _ /\ _ => split; [apply C8; cbn; tauto | ]
  | |- areadable _ _ _ _ => apply R64; cbn; tauto
  end.
Qed.

End WithSegs.
