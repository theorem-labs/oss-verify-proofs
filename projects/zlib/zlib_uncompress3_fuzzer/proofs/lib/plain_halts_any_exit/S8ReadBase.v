(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_zlib_uncompress3_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Frame RefMemcpyLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition fds_std : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
   (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

Definition fds_file (path : list byte) (off : word) : list (word * FdEntry) :=
  (Z_to_bv 64 3, FdFile path off) :: fds_std.




Definition mem_eq_outside (M M' : word -> option byte) (rs : list (word * Z)) : Prop :=
  forall a, outside a rs -> M' a = M a.







Definition stack_writable {RCa1 : RunCtx}  (M : word -> option byte) (sp0 : word) : Prop :=
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 6144513)%Z ->
    store_ok (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (bv_unsigned sp0 - 6144513 + d)) m = true.

Definition group_writable {RCa1 : RunCtx}  (M : word -> option byte) (gm : word) : Prop :=
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 69632)%Z ->
    store_ok (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (bv_unsigned gm + d)) m = true.

Definition meta_writable {RCa1 : RunCtx}  (M : word -> option byte) (mb : word) : Prop :=
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 4096)%Z ->
    store_ok (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (bv_unsigned mb + 4096 + d)) m = true.

Definition LA (a : Z) : saddr := SA (ELit 0) a.
Definition MBA (k : Z) : saddr := SA (EVar 2) k.
Definition GMA (k : Z) : saddr := SA (EVar 3) k.
Definition mbx (k : Z) : expr := EAlu ALU_ADD (EVar 2) (ELit k).

Definition kn_M1 : list kentry :=
  [ KImg 0x10000 0x22000;
    KWord (LA 0x93248) 8 (EVar 7);
    KWord (LA 0x9326b) 1 (ELit 0);
    KWord (LA 0x93298) 8 (ELit 4096);
    KWord (LA 0x932d8) 4 (ELit 0);
    KWord (LA 0x932e0) 8 (EVar 8);
    KWord (LA 0x932e8) 4 (ELit 1);
    KWord (LA 0x932ec) 4 (ELit 1);
    KWord (LA 0x932f0) 8 (ELit 0);
    KWord (LA 0x932f8) 8 (mbx 4160);
    KWord (LA 0x93300) 8 (ELit 100);
    KWord (LA 0x93308) 8 (ELit 0);
    KWord (LA 0x93318) 8 (mbx 4096);
    KWord (LA 0x93320) 8 (mbx 4096);
    KWord (LA 0x93328) 8 (mbx 8192);
    KWord (LA 0x93490) 8 (mbx 4120);
    KWord (LA 0x93610) 8 (ELit 1);
    KWord (LA 0x93670) 1 (ELit 1);
    KWord (MBA 4096) 8 (EVar 8);
    KWord (MBA 4104) 8 (ELit 0);
    KWord (MBA 4112) 4 (ELit 101);
    KWord (MBA 4120) 8 (mbx 4120);
    KWord (MBA 4128) 8 (mbx 4120);
    KWord (MBA 4136) 8 (EVar 3);
    KWord (MBA 4144) 4 (ELit 0);
    KWord (MBA 4148) 4 (ELit 0);
    KWord (MBA 4152) 8 (ELit 0x11b18);
    KZero (MBA 4160) (ELit 4032);
    KWord (GMA 0) 8 (mbx 4120);
    KWord (GMA 8) 1 (ELit 0);
    KZero (GMA 9) (ELit 4);
    KWord (GMA 13) 1 (ELit 224);
    KWord (GMA 14) 2 (ELit 1);
    KZero (GMA 16) (ELit 12);
    KWord (GMA 28) 1 (ELit 0);
    KWord (GMA 29) 1 (ELit 160);
    KWord (GMA 30) 2 (ELit 1);
    KWord (GMA 0x10020) 1 (ELit 0);
    KZero (GMA 0x10021) (ELit 4054);
    KWord (GMA 0x10fef) 1 (ELit 0);
    KWord (GMA 0x10ff0) 4 (ELit 4060);
    KZero (GMA 0x10ff4) (ELit 4) ].

Record read_pre {RCa1 : RunCtx}  (sp0 p1 mb gm cw sw : word) (R : bvmap 5 word) (M : word -> option byte) : Prop := READ_PRE {
  rp_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  rp_gp : getr R 3 = Z_to_bv 64 0x10800;
  rp_tp : getr R 4 = Z_to_bv 64 0x72fe0;
  rp_s0 : getr R 8 = Z_to_bv 64 2;
  rp_a0 : getr R 10 = Z_to_bv 64 (bv_unsigned gm + 32);
  rp_s2 : getr R 18 = p1;
  rp_s4 : getr R 20 = Z_to_bv 64 3;
  rp_s5 : getr R 21 = Z_to_bv 64 65536;
  rp_sp0 : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z /\ (bv_unsigned sp0 mod 16 = 0)%Z;
  rp_p1  : (0x7fff80000000 <= bv_unsigned p1 <= 0x800000400000)%Z;
  rp_b   : (0x1000 <= bv_unsigned mb)%Z /\ (bv_unsigned mb + 8192 <= bv_unsigned sp0 - 8388608)%Z
           /\ (bv_unsigned mb mod 4096 = 0)%Z;
  rp_b_img : (bv_unsigned mb + 8192 <= 0x10000 \/ 0x94000 <= bv_unsigned mb)%Z;
  rp_gm  : (0x94000 <= bv_unsigned gm)%Z /\ (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z
           /\ (bv_unsigned gm mod 4096 = 0)%Z;
  rp_gm_b : (bv_unsigned mb + 8192 <= bv_unsigned gm \/ bv_unsigned gm + 69632 <= bv_unsigned mb + 4096)%Z;
  rp_stack : stack_writable M sp0;
  rp_group : group_writable M gm;
  rp_meta  : meta_writable M mb;
  rp_errno : exists e : word, rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 0x72f3c) 4 = Some (word_to_le_bytes 4 e);
  rp_malloc : forall (x0 x1 x4 x5 x6 x9 : word) (extra : list word) (ebs : list (list byte)),
      know_ok (run_segments RSEGS rc_inp rc_sp rc_mb) (Env (vals_ev ([x0; x1; mb; gm; x4; x5; x6; cw; sw; x9] ++ extra)) (blobs_ev ebs)) M kn_M1
}.
Arguments READ_PRE {RCa1}.

Definition iv_disjoint (p q : word * word) : Prop :=
  (bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q)
   \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p))%Z.

Inductive seps : list (word * word) -> Prop :=
| seps_nil : seps []
| seps_cons : forall p l, Forall (iv_disjoint p) l -> seps l -> seps (p :: l).

Definition model_pre (path : list byte) (VM : VmMaps) (stdin0 : AmbIn) (fs0 : Fs) (tid : word) : Model :=
  mkModelA (fds_file path (Z_to_bv 64 0)) VM stdin0 fs0 None (Some tid) None.
Definition model_post (VM : VmMaps) (stdin0 : AmbIn) (fs0 : Fs) (tid : word) : Model :=
  mkModelA fds_std VM stdin0 fs0 None (Some tid) None.



Definition RS : Z := 0x22ed9.

Definition read_regions0 (sp0 gm : word) (L : Z) : list (word * Z) :=
  [(Z_to_bv 64 (bv_unsigned sp0 - 8388608), 8388480%Z); (Z_to_bv 64 (bv_unsigned gm + 32), L); (Z_to_bv 64 RS, 65536%Z)].

Record read_post0 {RCa1 : RunCtx}  (sp0 p1 gm : word) (content : list byte)
       (R0 : bvmap 5 word) (M0 : word -> option byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := READ_POST0 {
  rq_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  rq_gp : getr R 3 = Z_to_bv 64 0x10800;
  rq_tp : getr R 4 = Z_to_bv 64 0x72fe0;
  rq_s0 : getr R 8 = Z_to_bv 64 2;
  rq_s1 : getr R 9 = Z_to_bv 64 (bv_unsigned gm + 32);
  rq_s2 : getr R 18 = p1;
  rq_s3 : getr R 19 = Z_to_bv 64 (Z.of_nat (length content));
  rq_s4 : getr R 20 = Z_to_bv 64 3;
  rq_s5 : getr R 21 = Z_to_bv 64 65536;
  rq_s6 : getr R 22 = Z_to_bv 64 RS;
  rq_s7 : getr R 23 = Z_to_bv 64 0;
  rq_keep : forall r : reg, In r [24; 25; 26; 27]%bv -> getr R r = getr R0 r;
  rq_frame : mem_eq_outside M0 M (read_regions0 sp0 gm (Z.of_nat (length content)));
  rq_grows : mem_grows M0 M;
  rq_content : rdn (run_segments RSEGS rc_inp rc_sp rc_mb) M (Z_to_bv 64 (bv_unsigned gm + 32)) (length content) = Some content;
  rq_stack : stack_writable M sp0;
  rq_group : group_writable M gm }.
Arguments READ_POST0 {RCa1}.


Definition valsr (sp0 p1 b gm : word) (L : Z) (cw sw : word) (R : bvmap 5 word) : list word :=
  [sp0; p1; b; gm; Z_to_bv 64 L; Z_to_bv 64 0; Z_to_bv 64 0; cw; sw; Z_to_bv 64 0] ++ junk_vals R.
Definition ENVr (vals : list word) (content : list byte) : env := Env (vals_ev vals) (blobs_ev [content]).

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
Definition J (i : nat) : expr := EVar (10 + i).



Definition all_regs : list reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma nth_all_regs : forall n, (n < 32)%nat -> nth n all_regs 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.

Lemma regs_ok_by_index : forall E sr R,
  (forall i, (i < 32)%nat -> getr R (nth i all_regs 0%bv) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot]. reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_all_regs in Hx by apply ridx_range.
    rewrite ridx_roundtrip in Hx. exact Hx.
Qed.

Section EntrySym.
Context {RCa1 : RunCtx}.
  Variables (sp0 p1 b gm : word) (L : Z) (cw sw : word) (R : bvmap 5 word) (M : word -> option byte) (content : list byte).
  Hypothesis RP : read_pre sp0 p1 b gm cw sw R M.
  Let vals := valsr sp0 p1 b gm L cw sw R.
  Let E := ENVr vals content.

  Lemma ev0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  Lemma ev1 : ev E 1 = p1. Proof. reflexivity. Qed.
  Lemma ev2 : ev E 2 = b. Proof. reflexivity. Qed.

  Lemma spx_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. rewrite ev0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.


End EntrySym.
