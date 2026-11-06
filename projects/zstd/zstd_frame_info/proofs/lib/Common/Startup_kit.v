(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import StrFun STRW_tac.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma impl_post_evt : forall segs (atn : node -> machine_state -> Prop) {R} (t : itree node R) Q Q' ms,
  impl segs atn t Q' ms -> (forall r ms', Q' r ms' -> evt segs (Q r) ms') -> impl segs atn t Q ms.
Proof.
  intros segs atn R t; induction t as [r|n k IH]; intros Q Q' ms H HQ; cbn in *.
  - eapply evt_cut; eauto.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

Lemma impl_epost_evt : forall segs (atn : node -> machine_state -> Prop) {A} (t : itree node (exc A)) Q Q' ms,
  impl segs atn t (epost Q') ms -> (forall a ms', Q' a ms' -> evt segs (Q a) ms') -> impl segs atn t (epost Q) ms.
Proof.
  intros segs atn A t Q Q' ms H HQ. eapply impl_post_evt; [exact H|].
  intros [|a] ms' Hp; cbn in *; [apply evt_done; exact I | apply HQ; exact Hp].
Qed.

(* [comment removed for export] *)
Ltac astep := lstep; try (first [if_true | if_false]).
(* [comment removed for export] *)
Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).

(* [comment removed for export] *)
Tactic Notation "icallk" uconstr(SPEC) :=
  (lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
  eapply impl_epost_evt; [ eapply SPEC | ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Notation z64 := (Z_to_bv 64 0).

(* [comment removed for export] *)
Definition td_cells (self prev next sysinfo : word) (tid errno detach : word) (robust locale dtvp dtv0 : word) : list cell :=
  [C8 self; C8 prev; C8 next; C8 sysinfo; C4 tid; C4 errno; C4 detach; CB 76 (repeat (Z_to_bv 8 0) 76);
   C8 robust; CB 24 (repeat (Z_to_bv 8 0) 24); C8 locale; CB 32 (repeat (Z_to_bv 8 0) 32);
   C8 dtvp; CB 16 (repeat (Z_to_bv 8 0) 16); C8 dtv0; CB 112 (repeat (Z_to_bv 8 0) 112)].

(* [comment removed for export] *)
Definition rtd_cells (self prev next sysinfo : word) (tid errno detach : word) (robust locale canary dtvp dtv0 : word) : list cell :=
  [C8 self; C8 prev; C8 next; C8 sysinfo; C4 tid; C4 errno; C4 detach; CB 76 (repeat (Z_to_bv 8 0) 76);
   C8 robust; CB 24 (repeat (Z_to_bv 8 0) 24); C8 locale; CB 24 (repeat (Z_to_bv 8 0) 24); C8 canary;
   C8 dtvp; CB 16 (repeat (Z_to_bv 8 0) 16); C8 dtv0; CB 112 (repeat (Z_to_bv 8 0) 112)].

(* [comment removed for export] *)
Definition libc_cells (can_do : byte) (auxv tls_size tls_align page_size : word) : list cell :=
  [C1 can_do; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64; C8 auxv;
   C8 z64; C8 tls_size; C8 tls_align; C8 z64; C8 page_size; CB 48 (repeat (Z_to_bv 8 0) 48)].

(* [comment removed for export] *)
Definition auxv18 (uid rnd : word) : list word :=
  [Z_to_bv 64 3; Z_to_bv 64 0x10040; Z_to_bv 64 4; Z_to_bv 64 56; Z_to_bv 64 5; Z_to_bv 64 10;
   Z_to_bv 64 6; Z_to_bv 64 4096; Z_to_bv 64 11; uid; Z_to_bv 64 12; uid; Z_to_bv 64 23; z64;
   Z_to_bv 64 25; rnd; z64; z64].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rw_cells_app : forall segs m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] WR].
    pose proof (cells_bytes_length cs1 W1) as L1. rewrite L1 in B2.
    destruct WR as (HA & HN & HW).
    split; [split; [split; assumption|] | split; [split; assumption|]].
    + Local Ltac2 Set LiaHints.tbl := fun () => "00<0>1312117644.13 1312117644.16 19523142197.1919524649394.1524931733050.1324931733050.1631688782959.1339639586408.1548872924203.1353122485812.1953725182937.1563891885185.1900000700?00H00R00\00d00k01501?01F01M01VS2HN2L1S3HN22L1S2L12Hi1lS2HN2L12HiS2HA2HN2L1S3HA12L1S2HN2L1S2HN2L12HiS2HA2HN2L1S2L12HiS2HN2L1S2L12Hi1n".
split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i)%Z with (A + (Z.of_nat (cells_size cs1) + i))%Z by lia. apply HW. lia.
  - intros [[[W1 B1] (HA1 & HN1 & HW1)] [[W2 B2] (HA2 & HN2 & HW2)]].
    pose proof (cells_bytes_length cs1 W1) as L1.
    split; [split; [split; assumption|] |].
    + split; [exact B1|]. rewrite L1. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi. destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))).
      * apply HW1. lia.
      * replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply HW2. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Lemma rd_u64 : forall segs m A (w : word) rest a,
  bytes_at segs m A (le8 w ++ rest) -> a = wa A -> ov_read_bytes segs m a 8 = Some (le8 w).
Proof.
  intros segs m A w rest a B ->.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010<4163150595.6000001S".
assert (L : (0 + 8 <= length (le8 w ++ rest))%nat) by (rewrite app_length, length_le8; lia).
  pose proof (bytes_at_ov_read segs m A (le8 w ++ rest) 0 8 B L) as R.
  rewrite Z.add_0_r in R. rewrite R. f_equal; reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Ltac exact_evt H :=
  lazymatch type of H with evt _ _ ?s1 =>
    lazymatch goal with |- evt _ _ ?s2 =>
      replace s2 with s1; [exact H|];
      cbv delta [mkR]; repeat first [reflexivity | lia | progress f_equal]
    end
  end.

(* [comment removed for export] *)
Lemma rd_u64s_g : forall segs mm A ws (i : nat) w a,
  bytes_at segs mm A (u64s ws) -> nth_error ws i = Some w -> a = wa (A + 8 * Z.of_nat i) ->
  ov_read_bytes segs mm a 8 = Some (le8 w).
Proof.
  intros segs mm A ws i w a B Hn ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E1 & Hlen & Eu & Hlu).
  rewrite Eu in B. apply bytes_at_app in B. destruct B as [_ B]. rewrite Hlu in B.
  eapply rd_u64; [exact B|]. unfold wa. f_equal. Local Ltac2 Set LiaHints.tbl := fun () => "0010>67506505186.1400000:S4Hlen3Hlu".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Ltac ldaux AUXB i :=
  let a := cur_mem_addr in
  let RD := fresh "RD" in
  pose proof (rd_u64s_g _ _ _ _ i _ a AUXB eq_refl ltac:(addr_tac)) as RD;
  zstep; clear RD.

(* [comment removed for export] *)
Ltac join2 H1 H2 :=
  lazymatch type of H2 with rw_cells ?segs ?mm ?A2 ?cs2 =>
  lazymatch type of H1 with rw_cells _ _ ?A ?cs1 =>
    let H := fresh "J" in
    assert (H : rw_cells segs mm A (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app segs mm A cs1 cs2)); split;
            [ exact H1
            | replace (A + Z.of_nat (cells_size cs1))%Z with A2 by (simpl; lia); exact H2 ]);
    clear H1 H2; cbn [app] in H; rename H into H1
  end end.

(* [comment removed for export] *)
Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section StackAddrs.
  Variables (sp0 : word) (argv envp : list (list byte)).
  Notation usp0 := (bv_unsigned sp0).
  (* [comment removed for export] *)
  Definition envp_addr : Z := (usp0 + 8 * (argc argv + 2))%Z.
  (* [comment removed for export] *)
  Definition auxv_addr : Z := (usp0 + 8 * (argc argv + envc envp + 3))%Z.
End StackAddrs.
