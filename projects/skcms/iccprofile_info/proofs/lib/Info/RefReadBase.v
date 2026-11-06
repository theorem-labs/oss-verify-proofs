(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Frame RefMemcpyLib RefTargetPre RefReadDefs.
From Stdlib Require Import Zify.
Unset Nia Cache.  (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.

(* [comment removed for export] *)
Lemma mem_eq_outside_rdn : forall M M' rs n (a : word),
  mem_eq_outside M M' rs ->
  (forall i, (0 <= i < Z.of_nat n)%Z -> outside (Z_to_bv 64 (bv_unsigned a + i)) rs) ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  rdn RSEGS M' a n = rdn RSEGS M a n.
Proof.
  intros M M' rs n a Hf Ho Hb. symmetry. apply rdn_agree. intros j Hj. symmetry. apply Hf. apply Ho. lia.
Qed.

Lemma mem_eq_outside_store_ok : forall M M' rs n (a : word),
  mem_eq_outside M M' rs ->
  (forall i, (0 <= i < Z.of_nat n)%Z -> outside (Z_to_bv 64 (bv_unsigned a + i)) rs) ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  store_ok RSEGS M a n = true -> store_ok RSEGS M' a n = true.
Proof.
  intros M M' rs n a Hf Ho Hb Hs.
  apply store_ok_of_all; [lia|]. intros x Hx.
  pose proof (store_ok_all RSEGS M n a Hb Hs x Hx) as H1.
  unfold store_ok in *. cbn [store_ok] in *.
  unfold wview in *. pose proof (u64_range a).
  rewrite (Hf x); [exact H1|].
  replace x with (Z_to_bv 64 (bv_unsigned a + (bv_unsigned x - bv_unsigned a))) by (apply bv_eq; rewrite u_small by lia; lia).
  apply Ho. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stack_writable (M : word -> option byte) (sp0 : word) : Prop :=
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 8388608)%Z ->
    store_ok RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 8388608 + d)) m = true.

(* [comment removed for export] *)
Definition group_writable (M : word -> option byte) (gm : word) : Prop :=
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 69632)%Z ->
    store_ok RSEGS M (Z_to_bv 64 (bv_unsigned gm + d)) m = true.

(* [comment removed for export] *)
Definition meta_writable (M : word -> option byte) (mb : word) : Prop :=
  forall d m, (0 <= d)%Z -> (d + Z.of_nat m <= 4096)%Z ->
    store_ok RSEGS M (Z_to_bv 64 (bv_unsigned mb + 4096 + d)) m = true.

(* [comment removed for export] *)
Definition LA (a : Z) : saddr := SA (ELit 0) a.          (* [comment removed for export] *)
Definition MBA (k : Z) : saddr := SA (EVar 2) k.         (* [comment removed for export] *)
Definition GMA (k : Z) : saddr := SA (EVar 3) k.         (* [comment removed for export] *)
Definition mbx (k : Z) : expr := EAlu ALU_ADD (EVar 2) (ELit k).

Definition kn_M1 : list kentry :=
  [ KImg 0x10000 0x20000;                       (* [comment removed for export] *)
    KWord (LA 0x50c58) 8 (EVar 8);              (* [comment removed for export] *)
    KWord (LA 0x50c7b) 1 (ELit 0);              (* [comment removed for export] *)
    KWord (LA 0x50ca8) 8 (ELit 4096);           (* [comment removed for export] *)
    KWord (LA 0x50ce8) 4 (ELit 0);              (* [comment removed for export] *)
    KWord (LA 0x50cf0) 8 (EVar 7);              (* [comment removed for export] *)
    KWord (LA 0x50cf8) 4 (ELit 1);              (* [comment removed for export] *)
    KWord (LA 0x50cfc) 4 (ELit 1);              (* [comment removed for export] *)
    KWord (LA 0x50d00) 8 (ELit 0);              (* [comment removed for export] *)
    KWord (LA 0x50d08) 8 (mbx 4160);            (* [comment removed for export] *)
    KWord (LA 0x50d10) 8 (ELit 100);            (* [comment removed for export] *)
    KWord (LA 0x50d18) 8 (ELit 0);              (* [comment removed for export] *)
    KWord (LA 0x50d28) 8 (mbx 4096);            (* [comment removed for export] *)
    KWord (LA 0x50d30) 8 (mbx 4096);            (* [comment removed for export] *)
    KWord (LA 0x50d38) 8 (mbx 8192);            (* [comment removed for export] *)
    KWord (LA 0x50ea0) 8 (mbx 4120);            (* [comment removed for export] *)
    KWord (LA 0x51020) 8 (ELit 1);              (* [comment removed for export] *)
    KWord (LA 0x51080) 1 (ELit 1);              (* [comment removed for export] *)
    (* [comment removed for export] *)
    KWord (MBA 4096) 8 (EVar 7);                (* [comment removed for export] *)
    KWord (MBA 4104) 8 (ELit 0);                (* [comment removed for export] *)
    KWord (MBA 4112) 4 (ELit 101);              (* [comment removed for export] *)
    KWord (MBA 4120) 8 (mbx 4120);              (* [comment removed for export] *)
    KWord (MBA 4128) 8 (mbx 4120);              (* [comment removed for export] *)
    KWord (MBA 4136) 8 (EVar 3);                (* [comment removed for export] *)
    KWord (MBA 4144) 4 (ELit 0);                (* [comment removed for export] *)
    KWord (MBA 4148) 4 (ELit 0);                (* [comment removed for export] *)
    KWord (MBA 4152) 8 (ELit 0x11b20);          (* [comment removed for export] *)
    KZero (MBA 4160) (ELit 4032);               (* [comment removed for export] *)
    (* [comment removed for export] *)
    KWord (GMA 0) 8 (mbx 4120);                 (* [comment removed for export] *)
    KWord (GMA 8) 1 (ELit 0);                   (* [comment removed for export] *)
    KZero (GMA 9) (ELit 4);                     (* [comment removed for export] *)
    KWord (GMA 13) 1 (ELit 224);                (* [comment removed for export] *)
    KWord (GMA 14) 2 (ELit 1);                  (* [comment removed for export] *)
    KZero (GMA 16) (ELit 12);
    KWord (GMA 28) 1 (ELit 0);                  (* [comment removed for export] *)
    KWord (GMA 29) 1 (ELit 160);                (* [comment removed for export] *)
    KWord (GMA 30) 2 (ELit 1);                  (* [comment removed for export] *)
    KWord (GMA 0x10020) 1 (ELit 0);             (* [comment removed for export] *)
    KZero (GMA 0x10021) (ELit 4054);            (* [comment removed for export] *)
    KWord (GMA 0x10ff7) 1 (ELit 0);             (* [comment removed for export] *)
    KWord (GMA 0x10ff8) 4 (ELit 4060);          (* [comment removed for export] *)
    KZero (GMA 0x10ffc) (ELit 4) ].             (* [comment removed for export] *)

Record read_pre (sp0 p1 mb gm sec cnr : word) (R : bvmap 5 word) (M : word -> option byte) : Prop := READ_PRE {
  (* [comment removed for export] *)
  rp_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  rp_gp : getr R 3 = Z_to_bv 64 0x10800;
  rp_tp : getr R 4 = Z_to_bv 64 0x309e8;
  rp_s0 : getr R 8 = Z_to_bv 64 2;
  rp_a0 : getr R 10 = Z_to_bv 64 (bv_unsigned gm + 32);        (* [comment removed for export] *)
  rp_s2 : getr R 18 = p1;                                      (* [comment removed for export] *)
  rp_s4 : getr R 20 = Z_to_bv 64 3;                            (* [comment removed for export] *)
  rp_s5 : getr R 21 = Z_to_bv 64 65536;                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  rp_sp0 : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z /\ (bv_unsigned sp0 mod 16 = 0)%Z;
  rp_p1  : (0x7fff80000000 <= bv_unsigned p1 <= 0x800000400000)%Z;
  rp_b   : (0x52000 <= bv_unsigned mb)%Z /\ (bv_unsigned mb + 8192 <= 0x7fff7f800000)%Z
           /\ (bv_unsigned mb mod 4096 = 0)%Z;
  rp_gm  : (0x52000 <= bv_unsigned gm)%Z /\ (bv_unsigned gm + 69632 <= bv_unsigned sp0 - 8388608)%Z
           /\ (bv_unsigned gm mod 4096 = 0)%Z;
  rp_gm_b : (bv_unsigned mb + 8192 <= bv_unsigned gm \/ bv_unsigned gm + 69632 <= bv_unsigned mb)%Z;
           (* [comment removed for export] *)
  (* [comment removed for export] *)
  rp_stack : stack_writable M sp0;
  rp_group : group_writable M gm;
  rp_meta  : meta_writable M mb;
  (* [comment removed for export] *)
  rp_errno : exists e : word, rdn RSEGS M (Z_to_bv 64 0x30944) 4 = Some (word_to_le_bytes 4 e);
  (* [comment removed for export] *)
  rp_malloc : forall (x0 x1 x4 x5 x6 : word) (extra : list word) (ebs : list (list byte)),
      know_ok RSEGS (Env (vals_ev ([x0; x1; mb; gm; x4; x5; x6; sec; cnr] ++ extra)) (blobs_ev ebs)) M kn_M1
}.

(* [comment removed for export] *)
Definition vm_pre (VM : VmMaps) (sp0 mb gm : word) : Prop :=
  vm_reserved VM = segments_reserved RSEGS
  /\ (2 ^ 31 <= vm_limit VM)%Z
  /\ vm_init_sp VM = sp0
  /\ map_has (vm_maps VM) gm (Z_to_bv 64 69632) = true
  /\ Forall (fun p => (0 < bv_unsigned (snd p) <= 2 ^ 30)%Z
                      /\ (bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64)%Z) (vm_maps VM)
  /\ (length (vm_maps VM) <= 8)%nat
  /\ (live_bytes (vm_maps VM) <= 2 ^ 20)%Z
  /\ (exists p, In p (vm_maps VM) /\ fst p <> gm
        /\ (bv_unsigned (fst p) <= bv_unsigned mb + 4096)%Z
        /\ (bv_unsigned mb + 8192 <= bv_unsigned (fst p) + bv_unsigned (snd p))%Z)
  /\ seps (vm_maps VM).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition read_regions0 (sp0 gm : word) (L : Z) : list (word * Z) :=
  [(Z_to_bv 64 (bv_unsigned sp0 - 8388608), 8388480%Z); (Z_to_bv 64 0x208d9, 65536%Z);
   (Z_to_bv 64 (bv_unsigned gm + 32), L)].

Record read_post0 (sp0 p1 gm : word) (content : list byte)
       (R0 : bvmap 5 word) (M0 : word -> option byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := READ_POST0 {
  rq_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  rq_gp : getr R 3 = Z_to_bv 64 0x10800;
  rq_tp : getr R 4 = Z_to_bv 64 0x309e8;
  rq_s0 : getr R 8 = Z_to_bv 64 2;
  rq_s1 : getr R 9 = Z_to_bv 64 (bv_unsigned gm + 32);         (* [comment removed for export] *)
  rq_s2 : getr R 18 = p1;
  rq_s3 : getr R 19 = Z_to_bv 64 (Z.of_nat (length content));  (* [comment removed for export] *)
  rq_s4 : getr R 20 = Z_to_bv 64 3;
  rq_s5 : getr R 21 = Z_to_bv 64 65536;                         (* [comment removed for export] *)
  rq_s6 : getr R 22 = Z_to_bv 64 0x208d9;                       (* [comment removed for export] *)
  rq_s7 : getr R 23 = Z_to_bv 64 0;                             (* [comment removed for export] *)
  rq_keep : forall r : reg, In r [24; 25; 26; 27]%bv -> getr R r = getr R0 r;   (* [comment removed for export] *)
  (* [comment removed for export] *)
  rq_frame : mem_eq_outside M0 M (read_regions0 sp0 gm (Z.of_nat (length content)));
  rq_grows : mem_grows M0 M;
  rq_content : rdn RSEGS M (Z_to_bv 64 (bv_unsigned gm + 32)) (length content) = Some content;
  rq_stack : stack_writable M sp0;
  rq_group : group_writable M gm }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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
End WithFP1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
