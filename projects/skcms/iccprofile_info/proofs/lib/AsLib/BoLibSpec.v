(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim Hoare Frame LibDefs LibTagsSpec LibWP2Spec LibFPSpec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsFuzzContract AsLibShadow AsLibDefs BoBase AsRtSpec AsLibTagsSpec AsLibCurveSpec AsLibWP2Spec AsLibFPSpec AsLibParseSpec.
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

Definition RCURVES_DB : Z := 2304.
Definition PARSE_DB : Z := 2928.

Section Specs.
Variable segs : list Segment.
Variable L : as_lib.
Variable ceil : Z.   (* [comment removed for export] *)
#[local] Notation cell := (cell segs).
#[local] Notation cell32 := (cell32 segs).
#[local] Notation cell64 := (cell64 segs).
#[local] Notation cell8 := (cell8 segs).
#[local] Notation writable := (writable segs).
#[local] Notation tag_ok := (tag_ok segs).
#[local] Notation curve_ok := (curve_ok segs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition XYZD50_DB : Z := 64.

Definition xtag_ok_bo (mem : word -> option byte) (data : word) (len : Z) (sp : word) (T : word) : Prop :=
  let t := bv_unsigned T in
  (exists ty, cell32 mem (t + 4) ty) /\ tag_ok mem data len t /\
  (t mod 8 = 0) /\ stackish ceil t 24 /\ shz mem t 3 /\
  (bv_unsigned sp <= t \/ t + 24 <= bv_unsigned sp - XYZD50_DB).

Definition xyzd50_pre_bo (data : word) (len : Z) (bs : list byte) (sp T1 T2 T3 M : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let m := bv_unsigned M in
  getr regs 2 = sp /\ getr regs 10 = T1 /\ getr regs 11 = T2 /\ getr regs 12 = T3 /\ getr regs 13 = M /\
  as_data_ok ceil mem data len bs /\
  xtag_ok_bo mem data len sp T1 /\ xtag_ok_bo mem data len sp T2 /\ xtag_ok_bo mem data len sp T3 /\
  writable mem m 36 /\ (m mod 4 = 0) /\ heapish ceil m 36 /\ shz mem (m - m mod 8) 5 /\
  (bv_unsigned data + len <= m \/ m + 36 <= bv_unsigned data) /\
  as_sb segs L mem /\ as_frame segs ceil mem sp XYZD50_DB.

Definition xyzd50_post_bo (data : word) (len : Z) (bs : list byte) (sp T1 T2 T3 M : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - XYZD50_DB), XYZD50_DB); (M, 36)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1).

Definition xyzd50_contract_bo : Prop :=
  forall data len bs sp T1 T2 T3 M,
    fn_contract segs (al_xyzd50 L)
      (xyzd50_pre_bo data len bs sp T1 T2 T3 M)
      (xyzd50_post_bo data len bs sp T1 T2 T3 M).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rcurves_pre_bo (data : word) (len : Z) (bs : list byte)
    (sp buf C : word) (size : Z) (offw : word) (k : Z)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let c := bv_unsigned C in
  let A := al_abi L in
  getr regs 2 = sp /\ getr regs 10 = buf /\ getr regs 11 = Z_to_bv 64 size /\
  getr regs 12 = offw /\ getr regs 13 = Z_to_bv 64 k /\ getr regs 14 = C /\
  as_data_ok ceil mem data len bs /\ 0 <= size < 2 ^ 32 /\
  inDATA data len (bv_unsigned buf) size /\
  0 <= k <= 4 /\ (0 < k -> writable mem c (32 * k)) /\ (c mod 8 = 0) /\
  (0 < k -> heapish ceil c (32 * k) /\ shz mem c (4 * k) /\ forall i, 0 <= i < k -> shwz mem (c + 32 * i + 12) 20) /\
  (bv_unsigned data + len <= c \/ c + 32 * k <= bv_unsigned data) /\
  env_ro A mem /\ env_shb A mem /\ env_cells segs A mem /\
  as_frame segs ceil mem sp RCURVES_DB /\ shz mem (bv_unsigned sp - 96) 12.

Definition rcurves_post_bo (data : word) (len : Z) (bs : list byte)
    (sp buf C : word) (size : Z) (offw : word) (k : Z)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let c := bv_unsigned C in
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - RCURVES_DB), RCURVES_DB); (Z_to_bv 64 c, 32 * k)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
  (r = 1 -> forall i, 0 <= i < k -> curve_ok mem' data len (c + 32 * i)).

Definition read_curves_contract_bo : Prop :=
  forall data len bs sp buf C size offw k,
    fn_contract segs (al_rcurves L)
      (rcurves_pre_bo data len bs sp buf C size offw k)
      (rcurves_post_bo data len bs sp buf C size offw k).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A2B_DB : Z := 2544.

Definition a2b_pre_bo (data : word) (len : Z) (bs : list byte) (sp T A : word) (pcs : Z)
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
  as_frame segs ceil mem sp A2B_DB /\ shz mem (s - A2B_DB) (A2B_DB / 8) /\
  as_env segs ceil AB fs ch mem /\ fs_hdr segs ceil AB fs mem /\ fs_writable segs fs mem /\
  (exists h, acellw segs mem (fs + FS_HINT0) h) /\ fs_flags0_but fs [] mem /\
  (bv_unsigned data + len <= fs \/ fs + FS_SIZE <= bv_unsigned data) /\
  (bv_unsigned data + len <= a \/ a + 400 <= bv_unsigned data).

Definition a2b_post_bo (data : word) (len : Z) (bs : list byte) (sp T A : word) (pcs : Z)
    (fs : Z) (ch : chain)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let a := bv_unsigned A in
  frame_mod mem mem' ([(Z_to_bv 64 (bv_unsigned sp - A2B_DB), A2B_DB); (Z_to_bv 64 a, 400)] ++ fs_mod0 fs) /\
  fs_flags0_but fs [] mem' /\ (exists h', acellw segs mem' (fs + FS_HINT0) h') /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
  (r = 1 ->
     Forall (fun off => curve_ok mem' data len (a + off)) a2b_curve_offsets /\
     a2b_grid_ok segs mem' data len a).

Definition read_a2b_contract_bo : Prop :=
  forall data len bs sp T A pcs fs ch,
    fn_contract segs (al_a2b L) (a2b_pre_bo data len bs sp T A pcs fs ch) (a2b_post_bo data len bs sp T A pcs fs ch).

Definition b2a_pre_bo (data : word) (len : Z) (bs : list byte) (sp T B : word) (pcs : Z)
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
  as_frame segs ceil mem sp A2B_DB /\ shz mem (s - A2B_DB) (A2B_DB / 8) /\
  as_env segs ceil AB fs ch mem /\ fs_hdr segs ceil AB fs mem /\ fs_writable segs fs mem /\
  (exists h, acellw segs mem (fs + FS_HINT0) h) /\ fs_flags0_but fs [] mem /\
  (bv_unsigned data + len <= fs \/ fs + FS_SIZE <= bv_unsigned data) /\
  (bv_unsigned data + len <= b \/ b + 400 <= bv_unsigned data).

Definition b2a_post_bo (data : word) (len : Z) (bs : list byte) (sp T B : word) (pcs : Z)
    (fs : Z) (ch : chain)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let b := bv_unsigned B in
  frame_mod mem mem' ([(Z_to_bv 64 (bv_unsigned sp - A2B_DB), A2B_DB); (Z_to_bv 64 b, 400)] ++ fs_mod0 fs) /\
  fs_flags0_but fs [] mem' /\ (exists h', acellw segs mem' (fs + FS_HINT0) h') /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
  (r = 1 -> Forall (fun off => curve_ok mem' data len (b + off)) b2a_curve_offsets).

Definition read_b2a_contract_bo : Prop :=
  forall data len bs sp T B pcs fs ch,
    fn_contract segs (al_b2a L) (b2a_pre_bo data len bs sp T B pcs fs ch) (b2a_post_bo data len bs sp T B pcs fs ch).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition parse_pre_bo (data : word) (len : Z) (bs : list byte) (sp prio P : word) (fs : Z) (ch : chain)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let p := bv_unsigned P in
  let q := bv_unsigned prio in
  let s := bv_unsigned sp in
  let A := al_abi L in
  getr regs 2 = sp /\ getr regs 10 = data /\ getr regs 11 = Z_to_bv 64 len /\
  getr regs 12 = prio /\ getr regs 13 = Z_to_bv 64 2 /\ getr regs 14 = P /\ getr regs 4 = Z_to_bv 64 (aa_tp A) /\
  as_data_ok ceil mem data len bs /\ (bv_unsigned data + len <= fs \/ fs + FS_SIZE <= bv_unsigned data) /\
  (* [comment removed for export] *)
  cell32 mem q 0 /\ cell32 mem (q + 4) 1 /\ (q mod 8 = 0) /\ heapish ceil q 8 /\ shz mem q 1 /\
  (fs + FS_FRAMES5 <= q) /\ (q + 8 <= fs + FS_SIZE) /\ (q + 8 <= p \/ p + 976 <= q) /\
  (* [comment removed for export] *)
  writable mem p 976 /\ (p mod 64 = 0) /\ heapish ceil p 976 /\ shz mem p 122 /\
  (fs + FS_FRAMES5 <= p) /\ (p + 976 <= fs + FS_SIZE) /\
  (* [comment removed for export] *)
  as_frame segs ceil mem sp PARSE_DB /\ shz mem (s - PARSE_DB) (PARSE_DB / 8) /\
  (* [comment removed for export] *)
  as_env segs ceil A fs ch mem /\ fs_hdr segs ceil A fs mem /\ fs_writable segs fs mem /\
  (exists h, acellw segs mem (fs + FS_HINT0) h) /\ fs_flags0_but fs [] mem.

Definition parse_post_bo (data : word) (len : Z) (bs : list byte) (sp prio P : word) (fs : Z) (ch : chain)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' ([(Z_to_bv 64 (bv_unsigned sp - PARSE_DB), PARSE_DB); (P, 976)] ++ fs_mod0 fs) /\
  fs_flags0_but fs [] mem' /\ (exists h', acellw segs mem' (fs + FS_HINT0) h') /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
    (r = 1 -> parsed_ok segs mem' data len bs (bv_unsigned P)).

Definition parse_contract_bo : Prop :=
  forall data len bs sp prio P fs ch,
    fn_contract segs (al_parse L)
      (parse_pre_bo data len bs sp prio P fs ch)
      (parse_post_bo data len bs sp prio P fs ch).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fitlin_pre_bo (data : word) (len : Z) (bs : list byte)
    (sp C : word) (n : Z) (t8 t16 : word) (fs : Z) (hc : word) (ch : chain)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let s := bv_unsigned sp in
  let c := bv_unsigned C in
  let A := al_abi L in
  let Fc := frame0 fs (pos0 hc) in
  let h := Z_to_bv 64 (bv_unsigned hc + 1) in
  getr regs 2 = sp /\ getr regs 10 = C /\ getr regs 11 = Z_to_bv 64 n /\
  getr regs 12 = Z_to_bv 64 (s + 20) /\ getr regs 13 = Z_to_bv 64 (s + 16) /\
  getr regs 14 = Z_to_bv 64 (Fc + 32) /\ getr regs 4 = Z_to_bv 64 (aa_tp A) /\
  (s mod 32 = 0) /\ stackish ceil (s - FITLIN_D) (FITLIN_D + 24) /\ writable mem (s - FITLIN_D) (FITLIN_D + 24) /\
  shz mem (s + 16) 1 /\ (exists w, cell mem (s + 20) 4 w) /\
  writable mem (Fc + 32) 4 /\ acell segs mem (AS_SB + (Fc + 32) / 8) 1 4 /\
  (c mod 8 = 0) /\ heapish ceil c 32 /\ shz mem c 3 /\ (fs + FS_FRAMES5 <= c) /\ (c + 32 <= fs + FS_SIZE) /\
  table_curve segs mem data len c n t8 t16 /\
  as_data_ok ceil mem data len bs /\ (bv_unsigned data + len <= fs \/ fs + FS_SIZE <= bv_unsigned data) /\
  as_env segs ceil A fs ch mem /\ fs_hdr segs ceil A fs mem /\ fs_writable segs fs mem /\
  acellw segs mem (fs + FS_HINT0) h /\ fs_flags0_but fs [pos0 hc] mem.

Definition fitlin_post_bo (data : word) (len : Z) (bs : list byte)
    (sp C : word) (n : Z) (t8 t16 : word) (fs : Z) (hc : word) (ch : chain)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let s := bv_unsigned sp in
  let Fc := frame0 fs (pos0 hc) in
  let h := Z_to_bv 64 (bv_unsigned hc + 1) in
  let Ff := frame0 fs (pos0 h) in
  frame_mod mem mem' [(Z_to_bv 64 (s - FITLIN_D), FITLIN_D + 24); (Z_to_bv 64 (Fc + 32), 4);
                      (Z_to_bv 64 (fs + FS_HINT0), 8); (Z_to_bv 64 (fs + FS_FLAGS0 + pos0 h), 1);
                      (Z_to_bv 64 Ff, 64); (Z_to_bv 64 (AS_SB + Ff / 8), 8)] /\
  (exists w, cell mem' (s + 20) 4 w) /\ (exists w, cell mem' (Fc + 32) 4 w) /\
  acellw segs mem' (fs + FS_HINT0) (Z_to_bv 64 (bv_unsigned hc + 2)) /\
  mem' (Z_to_bv 64 (fs + FS_FLAGS0 + pos0 h)) = Some (Z_to_bv 8 0) /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ 1 <= r <= n.

Definition fit_linear_contract_bo : Prop :=
  forall data len bs sp C n t8 t16 fs hc ch,
    fn_contract segs (al_fitlin L)
      (fitlin_pre_bo data len bs sp C n t8 t16 fs hc ch)
      (fitlin_post_bo data len bs sp C n t8 t16 fs hc ch).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition usable_pre_bo (P : word) (sp : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let p := bv_unsigned P in
  getr regs 2 = sp /\ getr regs 10 = P /\ (p mod 8 = 0) /\ heapish ceil p 976 /\ shz mem p 122 /\
  bool8 segs mem (p + 964) /\ bool8 segs mem (p + 965) /\ bool8 segs mem (p + 966) /\
  as_sb segs L mem /\ as_frame segs ceil mem sp 16.

Definition usable_post_bo (P : word) (sp : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 16), 16)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1).

Definition usable_contract_bo : Prop :=
  forall P sp, fn_contract segs 0x87418 (usable_pre_bo P sp) (usable_post_bo P sp).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cicp_pre_bo (data : word) (len : Z) (bs : list byte) (sp T C : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let t := bv_unsigned T in
  let c := bv_unsigned C in
  getr regs 2 = sp /\ getr regs 10 = T /\ getr regs 11 = C /\
  as_data_ok ceil mem data len bs /\
  (exists ty, cell32 mem (t + 4) ty) /\ tag_ok mem data len t /\
  (t mod 8 = 0) /\ stackish ceil t 24 /\ shz mem t 3 /\ (bv_unsigned sp <= t) /\
  writable mem c 4 /\ (c mod 8 = 0) /\ heapish ceil c 8 /\ shz mem c 1 /\
  (bv_unsigned data + len <= c \/ c + 4 <= bv_unsigned data) /\
  as_sb segs L mem /\ as_frame segs ceil mem sp 16.

Definition cicp_post_bo (data : word) (len : Z) (bs : list byte) (sp T C : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 16), 16); (C, 4)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1).

Definition cicp_contract_bo : Prop :=
  forall data len bs sp T C,
    fn_contract segs 0x87228 (cicp_pre_bo data len bs sp T C) (cicp_post_bo data len bs sp T C).

End Specs.
