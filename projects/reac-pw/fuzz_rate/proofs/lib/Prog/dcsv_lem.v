From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Arr Bytes ZBridge FP Image.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import printf_facts_c snprintf_c.
Import ListNotations.
Open Scope Z_scope.

(** Lemmas for the walk of reac_rate_drivable_csv (plain image), Prog/dcsv_walk.v: memory facts not tied to the
    function (most copied from released disco, named at each lemma) and the plain image's facts the walk reads:
    the reserved segments end at 0x51000, the format "%s%d" at 0x10470, the strings "" at 0x1032e and "," at 0x10373
    with the slack bytes after their NUL. *)

(** `sb zero` stores the low byte of x0. *)
Lemma le1_zero : le1 (Z_to_bv 64 0) = [Z_to_bv 8 0].
Proof. reflexivity. Qed.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/tj_lemmas.v:126 *)
Lemma rw_cells_app : forall m A c1 c2,
  rw_cells rsegs m A (c1 ++ c2) <-> rw_cells rsegs m A c1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size c1)) c2.
Proof.
  intros m A c1 c2. unfold rw_cells, cells_at, wr_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, bytes_at_app.
  split.
  - intros [[[W1 W2] [B1 B2]] (Ha & Hl & Hw)].
    rewrite cells_bytes_length in B2 by exact W1.
    split; split; try (split; assumption).
    + split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size c1) + i) with (A + (Z.of_nat (cells_size c1) + i)) by lia. apply Hw. lia.
  - intros [[[W1 B1] (Ha1 & Hl1 & Hw1)] [[W2 B2] (Ha2 & Hl2 & Hw2)]].
    rewrite cells_bytes_length by exact W1.
    split; [split; [split; assumption | split; assumption]|].
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size c1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size c1) + (i - Z.of_nat (cells_size c1))) by lia. apply Hw2. lia.
Qed.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/tj_lemmas.v:147 *)
Lemma bytes_at_mrd : forall m A bs x, bytes_at rsegs m A bs -> A <= x < A + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m A bs x (Ha & Hl & H) Hx.
  replace x with (A + Z.of_nat (Z.to_nat (x - A))) by lia. rewrite H by lia.
  destruct (nth_error bs (Z.to_nat (x - A))) eqn:E; [eexists; reflexivity|].
  apply nth_error_None in E. lia.
Qed.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/tj_lemmas.v:156 *)
Lemma stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) Hm Hw Hc. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hwa (b & Hb)]. split; [apply Hw; exact Hwa|].
  destruct (Hc a Ha) as [Ho | Hb'].
  - exists b. unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact Ho.
  - exact Hb'.
Qed.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/tj_lemmas.v:166 *)
Lemma stk_cb : forall m A n, stk rsegs m A (A + Z.of_nat n) -> exists j, rw_cells rsegs m A [CB n j].
Proof.
  intros m A n H. pose proof H as (H1 & _ & _).
  destruct (stk_carve rsegs m A (A + Z.of_nat n) n H ltac:(lia)) as [_ (j & J)].
  exists j. replace (A + Z.of_nat n - Z.of_nat n) with A in J by lia. exact J.
Qed.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/tj_lemmas.v:173-177 *)
Lemma pf_bytes_app : forall a b, pf_bytes (a ++ b) = pf_bytes a ++ pf_bytes b.
Proof. intros. unfold pf_bytes. apply map_app. Qed.

Lemma length_pf_bytes : forall a, length (pf_bytes a) = length a.
Proof. intros. unfold pf_bytes. apply length_map. Qed.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/tj_lemmas.v:221 *)
Lemma task_mem_munch : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall a : word, ~ outside W (bv_unsigned a) -> wview rsegs m a <> None) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' TK MU HW a b E. destruct (m a) as [b0|] eqn:E0; [exact (TK a b0 E0)|].
  assert (HI : ~ outside W (bv_unsigned a)) by (intros Ho; rewrite (MU a Ho), E0 in E; discriminate).
  pose proof (HW a HI) as W0. unfold wview in W0. rewrite E0 in W0.
  destruct (find_segment rsegs (bv_unsigned a) 1) eqn:EF; [left; discriminate|].
  exfalso. apply W0. reflexivity.
Qed.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/tj_lemmas.v:269 *)
Lemma rwc_stk : forall m A n j, rw_cells rsegs m A [CB n j] -> stk rsegs m A (A + Z.of_nat n).
Proof.
  intros m A n j [[[Lj _] B] (H1 & H2 & HW)]. cbn [cells_size csize cells_bytes cbytes] in *.
  rewrite app_nil_r in B. rewrite Nat.add_0_r in *.
  split; [lia|]. split; [lia|]. intros a Ha. split.
  - replace a with (A + (a - A)) by lia. apply HW. lia.
  - eapply bytes_at_mrd; [exact B|]. rewrite Lj. lia.
Qed.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/tj_lemmas.v:278 *)
Lemma stk_sub : forall m a b a' b', stk rsegs m a b -> a <= a' -> a' <= b' -> b' <= b -> stk rsegs m a' b'.
Proof.
  intros m a b a' b' (H1 & H2 & H) X1 X2 X3. split; [lia|]. split; [lia|]. intros x Hx. apply H. lia.
Qed.

(* from 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/tj_lemmas.v:289 *)
Lemma rwc_cb : forall m A n j, rw_cells rsegs m A [CB n j] -> length j = n /\ bytes_at rsegs m A j.
Proof. intros m A n j [[[Lj _] B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. split; assumption. Qed.

(** Any part [A, A + n) of a stk range, as one CB cell. *)
Lemma stk_cb_at : forall m a b A n, stk rsegs m a b -> a <= A -> A + Z.of_nat n <= b ->
  exists j, rw_cells rsegs m A [CB n j].
Proof. intros m a b A n H H1 H2. apply stk_cb. eapply stk_sub; [exact H | lia | lia | lia]. Qed.

(** A writable cell's region keeps being writable after a step that may write it. *)
Lemma rw_cells_wview : forall m A cs x, rw_cells rsegs m A cs -> A <= x < A + Z.of_nat (cells_size cs) ->
  wview rsegs m (wa x) <> None.
Proof.
  intros m A cs x [_ (H1 & H2 & HW)] Hx. replace x with (A + (x - A)) by lia. apply HW. lia.
Qed.

Lemma stk_wview : forall m lo hi x, stk rsegs m lo hi -> lo <= x < hi -> wview rsegs m (wa x) <> None.
Proof. intros m lo hi x (_ & _ & H) Hx. apply (H x Hx). Qed.

(** The plain image's reserved segments end at 0x51000 (as the contract review's resv_top / img_free_hi): the
    snprintf cell D = S - 176 + 0x18 is at least lo + 5960 >= 0x51fc0, above them. *)
Lemma resv_top : forallb (fun s => bv_unsigned (fst s) + bv_unsigned (snd s) <=? 0x51000)
  (segments_reserved rsegs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma img_free_hi : forall D n, 0x51000 <= D -> pf_img_free D n.
Proof.
  intros D n HD i Hi s Hs. pose proof resv_top as H. rewrite forallb_forall in H.
  specialize (H s Hs). apply Z.leb_le in H. lia.
Qed.

(** "%s%d" and its NUL at FMT_SD = 0x10470 (.rodata). *)
Lemma fmt_sd_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10470 (pf_bytes ([37; 115; 37; 100] ++ [0])).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia | apply ro_bytes_b_sound; vm_compute; reflexivity].
Qed.

(* the shape of 25e3d17bdb50:proofs/libreac/fuzz_disco/lib/Prog/tj_lemmas.v:673 tj_str *)
Lemma dc_str : forall m (A : Z) (s sl : list Z) S' lo D n',
  mem_inv rsegs m -> ro_bytes_b rsegs A (pf_bytes (s ++ [0] ++ sl)) = true ->
  Forall (fun c => 0 < c < 256) s ->
  (- (A + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length sl) ->
  0 < A -> A + Z.of_nat (length s) + 1 + Z.of_nat (length sl) <= 0x50878 -> 0x50878 <= lo -> lo <= D ->
  pf_arg_ok m S' lo D n' (Z_to_bv 64 A) (APtr s).
Proof.
  intros m A s sl S' lo D n' MI RB FA HM HA HE HL HD. cbn [pf_arg_ok]. rewrite unsigned_lit by lia.
  split; [exact FA|]. exists (pf_bytes sl). rewrite length_pf_bytes.
  split; [|split; [lia|split; [lia|split; lia]]].
  rewrite <- pf_bytes_app, <- app_assoc. apply ro_bytes_at; [exact MI | lia | | apply ro_bytes_b_sound; exact RB].
  rewrite length_pf_bytes, !length_app. cbn [length]. lia.
Qed.

(** sep = "" at STR_EMPTY = 0x1032e: slack byte 0x1032f; sep = "," at STR_COMMA = 0x10373: slack 0x10375-0x10377. *)
Lemma dc_s_empty : forall m S' lo D n', mem_inv rsegs m -> 0x50878 <= lo -> lo <= D ->
  pf_arg_ok m S' lo D n' (Z_to_bv 64 0x1032e) (APtr []).
Proof.
  intros m S' lo D n' MI HL HD. eapply (dc_str m _ _ [52]); [exact MI | vm_compute; reflexivity | constructor
    | cbn; lia | lia | cbn; lia | exact HL | exact HD].
Qed.

Lemma dc_s_comma : forall m S' lo D n', mem_inv rsegs m -> 0x50878 <= lo -> lo <= D ->
  pf_arg_ok m S' lo D n' (Z_to_bv 64 0x10373) (APtr [44]).
Proof.
  intros m S' lo D n' MI HL HD. eapply (dc_str m _ _ [110; 111; 116]); [exact MI | vm_compute; reflexivity
    | constructor; [lia | constructor] | cbn; lia | lia | cbn; lia | exact HL | exact HD].
Qed.

Lemma dc_int_arg : forall m S' lo D n' r, 0 <= r < 2^31 -> pf_arg_ok m S' lo D n' (Z_to_bv 64 r) (AInt r).
Proof. intros m S' lo D n' r Hr. cbn [pf_arg_ok]. rewrite unsigned_lit by lia. split; [lia | reflexivity]. Qed.
