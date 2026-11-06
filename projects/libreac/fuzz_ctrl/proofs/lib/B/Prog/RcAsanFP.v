From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c.
Import ListNotations.
Open Scope Z_scope.

(* The side-stack state that __asan_stack_malloc_c needs (asan_stack_malloc_contract c), packed for the contracts of
   the functions that take side-stack frames or call one that does (class 1: ctrl_lay_block, reac_ctrl_parse; class
   0: reac_box_model_block). *)

(* Every range of W is apart from every range of D. *)
Definition fp_dj (W D : list ivl) : Prop :=
  Forall (fun w => Forall (fun d => ly_dj (fst w) (snd w) (fst d) (snd d)) D) W.

(* The cells that asan_tls_cells names. *)
Definition fp_tls (TP : Z) (DT TS C T DB : word) (k : Z) : list ivl :=
  [(TLS_INDEX, TLS_INDEX + 16); (REAL_TLS_GET_ADDR, REAL_TLS_GET_ADDR + 8); (TP - 8, TP + 16);
   (bv_unsigned DT + 8, bv_unsigned DT + 16); (TSD_KEY_INITED, TSD_KEY_INITED + 1); (TSD_KEY, TSD_KEY + 4);
   (TP - 88, TP - 80); (bv_unsigned TS + 8 * k, bv_unsigned TS + 8 * k + 8);
   (bv_unsigned C + 152, bv_unsigned C + 160); (bv_unsigned T + 48, bv_unsigned T + 64);
   (GOT_CF, GOT_CF + 8); (CF + 137, CF + 138); (GOT_VERBOSITY, GOT_VERBOSITY + 8); (VERBOSITY, VERBOSITY + 4);
   (DTLS_TPOFF, DTLS_TPOFF + 8); (bv_unsigned DB + 24, bv_unsigned DB + 32)].

(* The bytes that a class-c frame of the side stack, its use and its release can write: the hint word and the flag
   bytes of class c, the class-c frames, and their shadow bytes. *)
Definition fp_w1 (FS : Z) (c : nat) : list ivl :=
  [(fs_hint FS c, fs_hint FS c + 8); (fs_flag FS c 0, fs_flag FS c 0 + fs_M c);
   (fs_frame FS c 0, fs_frame FS c (fs_M c));
   (shadow_addr (fs_frame FS c 0), shadow_addr (fs_frame FS c (fs_M c)))].

Definition fp_w (cs : list nat) (FS : Z) : list ivl := flat_map (fp_w1 FS) cs.

(* The class-c state that __asan_stack_malloc_c reads: the hint word and the fs_M c flag bytes, each 0 or 1. *)
Definition fp_cls (m : word -> option byte) (FS : Z) (c : nat) : Prop :=
  (c <= 6)%nat /\
  exists (h : word) (flags : list byte),
    bytes_at rsegs m (fs_hint FS c) (le8 h)
    /\ bytes_at rsegs m (fs_flag FS c 0) flags /\ Z.of_nat (length flags) = fs_M c
    /\ Forall (fun b => b = Z_to_bv 8 0 \/ b = Z_to_bv 8 1) flags.

(* fp cs m TP FS lo hi W D: with tp = TP and the side stack at FS, the premises of __asan_stack_malloc_c hold, for each
   class c in cs, for every call whose real-stack window is inside [lo, hi); the cells they read (fp_tls and the side
   stack's header [FS, FS + 36864)) are apart from the caller's writes W; the caller's data ranges D are apart from
   fp_w cs FS. *)
Definition fp (cs : list nat) (m : word -> option byte) (TP FS lo hi : Z) (W D : list ivl) : Prop :=
  exists (DT TS C T DB : word) (k : Z),
    asan_tls_cells m TP DT TS C T DB k
    /\ bytes_at rsegs m TP (le8 (Z_to_bv 64 FS)) /\ fs_place m FS
    /\ bytes_at rsegs m (FS + 88) (le8 (Z_to_bv 64 20)) /\ bytes_at rsegs m (FS + 96) [Z_to_bv 8 0]
    /\ Forall (fp_cls m FS) cs
    /\ FS + FS_SIZE <= lo /\ (forall a, lo <= a < hi -> app_mem a)
    /\ fp_dj W (fp_tls TP DT TS C T DB k ++ [(FS, fs_frame FS 0 0)])
    /\ fp_dj D (fp_w cs FS).

(* ----- Free-frame variant of the side-stack write footprint (P9). ----- *)

(* [lo, hi) with each hole [a, b) of holes removed, every produced piece clamped into [lo, hi). *)
Fixpoint cut_ivls0 (lo hi : Z) (holes : list ivl) : list ivl :=
  match holes with
  | [] => [(lo, hi)]
  | (a, b) :: hs => (lo, Z.min a hi) :: cut_ivls0 (Z.max b lo) hi hs
  end.

(* The pieces with lo < hi. An empty piece (p, p) would make fp_dj ask that p is not inside any D range, which
   is false when D spans two adjacent excluded frames. *)
Definition nonempty (l : list ivl) : list ivl := List.filter (fun p => fst p <? snd p) l.

Definition cut_ivls (lo hi : Z) (holes : list ivl) : list ivl := nonempty (cut_ivls0 lo hi holes).

(* The intervals of fp_w1 FS c with, for each frame index j named for class c in X, the one frame
   [fs_frame FS c j, fs_frame FS c (j + 1)) and that frame's shadow removed; the class hint word and the
   flag bytes stay, and whole-class intervals of unaffected classes are left intact (the excluded frame is
   split out of its class's frame interval). *)
Definition fp_wx1 (FS : Z) (X : list (nat * Z)) (c : nat) : list ivl :=
  let js := map snd (filter (fun ci => Nat.eqb (fst ci) c) X) in
  [(fs_hint FS c, fs_hint FS c + 8); (fs_flag FS c 0, fs_flag FS c 0 + fs_M c)]
  ++ cut_ivls (fs_frame FS c 0) (fs_frame FS c (fs_M c))
       (map (fun j => (fs_frame FS c j, fs_frame FS c (j + 1))) js)
  ++ cut_ivls (shadow_addr (fs_frame FS c 0)) (shadow_addr (fs_frame FS c (fs_M c)))
       (map (fun j => (shadow_addr (fs_frame FS c j), shadow_addr (fs_frame FS c (j + 1)))) js).

Definition fp_wx (cs : list nat) (FS : Z) (X : list (nat * Z)) : list ivl :=
  match X with
  | [] => fp_w cs FS
  | _ => flat_map (fp_wx1 FS X) cs
  end.

Lemma fp_wx_nil : forall cs FS, fp_wx cs FS [] = fp_w cs FS.
Proof. reflexivity. Qed.

(* Each produced piece sits inside [lo, hi). *)
Lemma cut_ivls0_in : forall holes lo hi r, In r (cut_ivls0 lo hi holes) -> lo <= fst r /\ snd r <= hi.
Proof.
  induction holes as [|[a b] hs IH]; intros lo hi r Hin; cbn [cut_ivls0] in Hin.
  - destruct Hin as [H|[]]; subst r; cbn [fst snd]; lia.
  - destruct Hin as [H|Hin].
    + subst r; cbn [fst snd]; lia.
    + destruct (IH (Z.max b lo) hi r Hin) as [H1 H2]; split; lia.
Qed.

Lemma nonempty_In : forall l r, In r (nonempty l) -> In r l.
Proof. intros l r Hin. unfold nonempty in Hin. apply filter_In in Hin as [Hin _]. exact Hin. Qed.

Lemma cut_ivls_in : forall holes lo hi r, In r (cut_ivls lo hi holes) -> lo <= fst r /\ snd r <= hi.
Proof. intros holes lo hi r Hin. apply nonempty_In in Hin. exact (cut_ivls0_in holes lo hi r Hin). Qed.

(* Each interval of fp_wx1 is contained in some interval of fp_w1. *)
Lemma fp_wx1_cover : forall FS X c r, In r (fp_wx1 FS X c) ->
  exists r', In r' (fp_w1 FS c) /\ fst r' <= fst r /\ snd r <= snd r'.
Proof.
  intros FS X c r Hin. unfold fp_wx1 in Hin. unfold fp_w1.
  apply in_app_or in Hin as [Hin|Hin].
  - cbn [In] in Hin. destruct Hin as [H|[H|[]]]; subst r.
    + exists (fs_hint FS c, fs_hint FS c + 8). split; [cbn [In]; auto | cbn [fst snd]; lia].
    + exists (fs_flag FS c 0, fs_flag FS c 0 + fs_M c). split; [cbn [In]; auto | cbn [fst snd]; lia].
  - apply in_app_or in Hin as [Hin|Hin].
    + apply cut_ivls_in in Hin as [H1 H2].
      exists (fs_frame FS c 0, fs_frame FS c (fs_M c)).
      split; [cbn [In]; auto | cbn [fst snd] in *; lia].
    + apply cut_ivls_in in Hin as [H1 H2].
      exists (shadow_addr (fs_frame FS c 0), shadow_addr (fs_frame FS c (fs_M c))).
      split; [cbn [In]; auto | cbn [fst snd] in *; lia].
Qed.

Lemma fp_wx_cover : forall cs FS X r, In r (fp_wx cs FS X) ->
  exists r', In r' (fp_w cs FS) /\ fst r' <= fst r /\ snd r <= snd r'.
Proof.
  intros cs FS X r Hin. destruct X as [|p X'].
  - exists r. split; [exact Hin | split; lia].
  - change (fp_wx cs FS (p :: X')) with (flat_map (fp_wx1 FS (p :: X')) cs) in Hin.
    apply in_flat_map in Hin as [c [Hc Hr]].
    destruct (fp_wx1_cover FS (p :: X') c r Hr) as [r' [Hr' Hle]].
    exists r'. split; [apply in_flat_map; exists c; split; assumption | exact Hle].
Qed.

Lemma outside_In : forall B x r, outside B x -> In r B -> ~ (fst r <= x < snd r).
Proof.
  induction B as [|[lo hi] B IH]; intros x r Hout Hin; cbn [outside] in Hout.
  - destruct Hin.
  - destruct Hout as [H1 H2]. destruct Hin as [H|Hin].
    + subst r; cbn [fst snd]; exact H1.
    + exact (IH x r H2 Hin).
Qed.

Lemma outside_of_cover : forall A B x,
  (forall r, In r A -> exists r', In r' B /\ fst r' <= fst r /\ snd r <= snd r') ->
  outside B x -> outside A x.
Proof.
  induction A as [|[lo hi] A IH]; intros B x Hcov Hout; cbn [outside].
  - exact I.
  - split.
    + destruct (Hcov (lo, hi) (or_introl eq_refl)) as [r' [Hin' [H1 H2]]]. cbn [fst snd] in H1, H2.
      pose proof (outside_In B x r' Hout Hin') as Hr'. lia.
    + apply (IH B x); [intros r Hr; apply Hcov; right; exact Hr | exact Hout].
Qed.

Lemma fp_wx_sub_w : forall cs FS X, sub_fp (fp_wx cs FS X) (fp_w cs FS).
Proof.
  intros cs FS X x Hout.
  apply (outside_of_cover (fp_wx cs FS X) (fp_w cs FS) x); [| exact Hout].
  intros r Hr. apply (fp_wx_cover cs FS X r Hr).
Qed.

Lemma fp_dj_cover : forall D A B,
  (forall r, In r A -> exists r', In r' B /\ fst r' <= fst r /\ snd r <= snd r') ->
  fp_dj D B -> fp_dj D A.
Proof.
  intros D A B Hcov H. unfold fp_dj in *.
  eapply Forall_impl; [| exact H]. intros w Hw. cbn beta in Hw.
  apply Forall_forall. intros r Hr. destruct (Hcov r Hr) as [r' [Hin' [H1 H2]]].
  rewrite Forall_forall in Hw. pose proof (Hw r' Hin') as Hd. unfold ly_dj in *. cbn [fst snd] in *. lia.
Qed.

(* fpx cs m TP FS lo hi W D X: fp with the free-frame write footprint fp_wx cs FS X in place of fp_w cs FS. *)
Definition fpx (cs : list nat) (m : word -> option byte) (TP FS lo hi : Z) (W D : list ivl)
    (X : list (nat * Z)) : Prop :=
  exists (DT TS C T DB : word) (k : Z),
    asan_tls_cells m TP DT TS C T DB k
    /\ bytes_at rsegs m TP (le8 (Z_to_bv 64 FS)) /\ fs_place m FS
    /\ bytes_at rsegs m (FS + 88) (le8 (Z_to_bv 64 20)) /\ bytes_at rsegs m (FS + 96) [Z_to_bv 8 0]
    /\ Forall (fp_cls m FS) cs
    /\ FS + FS_SIZE <= lo /\ (forall a, lo <= a < hi -> app_mem a)
    /\ fp_dj W (fp_tls TP DT TS C T DB k ++ [(FS, fs_frame FS 0 0)])
    /\ fp_dj D (fp_wx cs FS X).

Lemma fpx_nil : forall cs m TP FS lo hi W D,
  fpx cs m TP FS lo hi W D [] <-> fp cs m TP FS lo hi W D.
Proof. intros. split; intro H; exact H. Qed.

Lemma fp_fpx : forall cs m TP FS lo hi W D X,
  fp cs m TP FS lo hi W D -> fpx cs m TP FS lo hi W D X.
Proof.
  intros cs m TP FS lo hi W D X
    (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HA & HWd & HDd).
  exists DT, TS, C, T, DB, k.
  split; [exact HT|]. split; [exact HTP|]. split; [exact HP|]. split; [exact H88|].
  split; [exact H96|]. split; [exact HCL|]. split; [exact HFS|]. split; [exact HA|]. split; [exact HWd|].
  apply (fp_dj_cover D (fp_wx cs FS X) (fp_w cs FS)); [| exact HDd].
  intros r Hr. apply (fp_wx_cover cs FS X r Hr).
Qed.
