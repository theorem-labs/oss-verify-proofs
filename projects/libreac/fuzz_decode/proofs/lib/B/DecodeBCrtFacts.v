(* DecodeBCrtFacts: instance facts of check_round_trip / LLVMFuzzerTestOneInput at image B's record TfibB
   (lib/B/YD2l.v:12; as_const := Tfib_const and as_owned_static := Tfib_owned_static of lib/B/YF0m.v,
   as_code := Tfib_code of lib/B/YF0l.v, as_universe := Tfib_universe of lib/B/YCej.v). lib/B/DecodeBClose.v takes
   them as hypotheses about its record B: HB_CRT_CELLS (:319), HB_RO_RD_UNOWNED (:323), HB_LLVMF_UTRACES (:359),
   HB_CRT_UCTX (:360), HB_CRT_UFIX (:361). Each one is decided by vm_compute over the record's lists through a boolean
   reflection lemma.

   RA_LLVMF is the numeral 0x7ffac: target_run in the pinned image (fuzz_decode.asan-ubsan, sha256 5d05689fd5b19697)
   has `7ffa8: jal 800b0 <LLVMFuzzerTestOneInput>`, and lib/B/YCfn.v:22 and lib/B/YCfl.v:18 define RA_LLVMF as 0x7ffac. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0f YG0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import YD2l.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require YCej.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require check_round_trip_cg LLVMFuzzerTestOneInput_cg.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Module UJ := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.YCej.
Module PL := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.LLVMFuzzerTestOneInput_cg.
Module PC := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.check_round_trip_cg.

(* Membership of a numeric cell (ACell (ANum a) w (AV (ANum v)): every z8 / z4 / z1 row of dec_crt_cells) in a list
   of cells, as a boolean. *)
Definition cnum_b (a : Z) (w : nat) (v : Z) (c : acell) : bool :=
  match c with
  | ACell (ANum a') w' (AV (ANum v')) => (Z.eqb a a' && Nat.eqb w w' && Z.eqb v v')%bool
  | _ => false
  end.
Lemma cnum_In (a : Z) (w : nat) (v : Z) (l : list acell) :
  existsb (cnum_b a w v) l = true -> In (ACell (ANum a) w (AV (ANum v))) l.
Proof.
  intro H. apply existsb_exists in H as [c [Hin Hb]].
  assert (E : c = ACell (ANum a) w (AV (ANum v))).
  { destruct c as [ca cw cv]. destruct ca; cbn in Hb; try discriminate Hb.
    destruct cv as [e|]; cbn in Hb; try discriminate Hb.
    destruct e; cbn in Hb; try discriminate Hb.
    apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
    apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity. }
  subst c. exact Hin.
Qed.

(* A dec_tab_zshadow_at row, as a boolean over the record's as_zero_shadow ranges. *)
Definition zsh_b (zs : list (Z * Z)) (T : Z) : bool :=
  existsb (fun r => (fst r mod 8 =? 0) && (fst r <=? T) && (T + 8 <=? fst r + snd r))%bool zs.
Lemma zsh_b_ok (B : asyms) (T : Z) : zsh_b (as_zero_shadow B) T = true -> PC.dec_tab_zshadow_at B T.
Proof.
  intro H. apply existsb_exists in H as [r [Hin H]].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  exists r. split; [exact Hin|]. split; [apply Z.eqb_eq; exact H1|].
  split; apply Z.leb_le; assumption.
Qed.

Lemma dec_crt_cells_TfibB : @PC.dec_crt_cells TfibB.
Proof.
  unfold PC.dec_crt_cells. intros ly. unfold z8, z4, z1, c8, c4, c1.
  repeat match goal with |- _ /\ _ => split end.
  all: first [ apply zsh_b_ok; vm_compute; reflexivity | apply cnum_In; vm_compute; reflexivity ].
Qed.

(* No byte of an owned static of the list, as a boolean at one address. *)
Definition unowned_b (os : list (Z * Z)) (z : Z) : bool :=
  forallb (fun r => negb ((fst r <=? z) && (z <? fst r + snd r)))%bool os.
Lemma unowned_b_ok (os : list (Z * Z)) (a : Z) : unowned_b os a = true -> ~ Exists (in_zr a) os.
Proof.
  intros H HE. apply Exists_exists in HE as [r [Hin [H1 H2]]].
  unfold unowned_b in H. rewrite forallb_forall in H. specialize (H r Hin).
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.ltb_lt _ _) H2) in H. discriminate H.
Qed.

Lemma dec_ro_rd_unowned_TfibB : PC.dec_ro_rd_unowned TfibB.
Proof.
  unfold PC.dec_ro_rd_unowned. intros a H. apply unowned_b_ok.
  apply (PC.dec_zr_enum (unowned_b (as_owned_static TfibB)) PC.DEC_RO_RD a); [vm_compute; reflexivity | exact H].
Qed.

Lemma dec_crt_ufix_TfibB : @PC.dec_crt_ufix TfibB.
Proof.
  unfold PC.dec_crt_ufix.
  repeat match goal with |- _ /\ _ => split end.
  all: apply UJ.memZL_In; vm_compute; reflexivity.
Qed.

(* Every trace f r, r in L, is a member of U, as a boolean. *)
Lemma all_traces_in (f : Z -> list Z) (L : list Z) (U : list (list Z)) :
  UJ.allb (fun r => UJ.memZL (f r) U) L = true -> forall r, In r L -> In (f r) U.
Proof.
  intros H r Hr. apply UJ.memZL_In. exact (UJ.allb_In (fun r => UJ.memZL (f r) U) L r H Hr).
Qed.

Lemma dec_llvmf_utraces_TfibB : @PL.dec_llvmf_utraces 0x7ffac TfibB.
Proof.
  unfold PL.dec_llvmf_utraces. intros sp Hsp. split.
  - apply (all_traces_in (fun r => PC.dec_utrace (pc_malloc_ra0 (as_code TfibB)) (r :: sp))).
    destruct Hsp as [<-|[<-|[]]]; vm_compute; reflexivity.
  - apply (all_traces_in (fun r => PC.dec_utrace (pc_free_ra0 (as_code TfibB)) (r :: sp))).
    destruct Hsp as [<-|[<-|[]]]; vm_compute; reflexivity.
Qed.

(* The tail free's traces at check_round_trip's call contexts: Tfib_universe carries them as YCej.v's declared override
   rows TRACES_check_round_trip_override (lib/B/YCej.v:57). *)
Lemma dec_crt_uctx_TfibB : @PC.dec_crt_uctx TfibB (@PL.CTX_check_round_trip 0x7ffac).
Proof.
  unfold PC.dec_crt_uctx. intros c Hc. apply UJ.memZL_In.
  exact (UJ.allb_In (fun c => UJ.memZL (PC.dec_utrace (pc_free_ra0 (as_code TfibB)) c) (as_universe TfibB))
    (@PL.CTX_check_round_trip 0x7ffac) c ltac:(vm_compute; reflexivity) Hc).
Qed.
