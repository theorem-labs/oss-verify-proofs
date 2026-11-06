(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/ProgWorldOwnedRo.v 94fb7929a42 (the blob this tree had at release c5e779efe8c) (a working branch 0e97fddfcea, read by git show, not merged): the same check, soundness lemmas, Section and proofs over image B's OWN record tables (lib.Reusable.YF0m Tfib_owned_static / Tfib_const_abs, ts_owned) and image B's segments (B.Img0.rsegs = lib.Reusable.YB1v.tfibsegs); owned_ro_chk_true is B's own vm_compute.  Differences from A: (1) module paths: A.Img0 / A.ProgWorld / A.ProgWorld_Fs / A.ProgWorldCtlRt -> B.*, A.AB1v / A.AF0m -> lib.Reusable.YB1v / YF0m; (2) A's `Lib.Mem.ro_addr` (6 uses) is written lib.Lib.Mem.ro_addr, the same constant, because lib/Lib/Mem.v also exists as lib/B/Bz/Lib/Mem.v (as lib/B/ProgWorld.v and ProgWorldCtlRt.v write it); (3) every Require names the full directory of the one copy a clean checkout binds; (4) comments name image B, YF0m and this file's writer.  No number is taken from A (the file has none). *)
(* lib/B/ProgWorldOwnedRo.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): DISCHARGE of the named hypothesis
   B.ProgWorld.AR_states_owned_ro (a Theorem Labs lane 23:56Z route (a); owners a Theorem Labs lane = the const rows, a Theorem Labs lane = this lemma).
   Image-B twin of a Theorem Labs lane's lib/A/ProgWorldOwnedRo.v; writer a Theorem Labs lane.
   rule 24: no function proved (a closed check over YF0m's concrete tables and image B's segments).

   THE ROUTE.  Under CtrlTSyms B, as_owned_static B = Tfib_owned_static (ts_owned) and as_const B ly = Tfib_const ly
   (ts_const).  owned_ro_chk is one closed boolean, run once by vm_compute: for every owned range, either no read-only
   segment of image B meets it (ro_free), or every read-only byte x of it is pinned by a closed row
   ACell (ANum s) w (AV (ANum v)) of Tfib_const_abs whose byte at x equals the image byte seg_rom x (byte_ok).  Its
   soundness lemmas are proved once; AR's am_const (ProgWorld_Fs.pw_row) then gives the row over the core's view, so
   the view reads the image byte at every owned read-only address. *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YA0n YG0f YG0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorld ProgWorld_Fs ProgWorldCtlRt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Mem.
Import ListNotations.
Local Open Scope Z_scope.
Local Notation segs := lib.Reusable.YB1v.tfibsegs (only parsing).

(* module gate: the bare names below resolve to LPS's MemImageType / stdpp, never to a lib/A or lib/Reusable module *)
Locate find_segment. Locate seg_writable. Locate seg_base. Locate seg_size. Locate Z_to_bv. Locate bv_unsigned.

(* ---- 1. The check. ---- *)

(* the byte at x of a closed byte-valued row covering x *)
Definition row_byte (c : lib.Reusable.YG0f.acell) (x : Z) : option Z :=
  match c with
  | lib.Reusable.YG0f.ACell (lib.Reusable.YG0f.ANum s) w (lib.Reusable.YG0f.AV (lib.Reusable.YG0f.ANum v)) =>
      if andb (Z.leb s x) (Z.ltb x (s + Z.of_nat w))
      then Some (lib.Reusable.YG0f.le_byte v w (Z.to_nat (x - s))) else None
  | _ => None
  end.

(* image B's byte at x is v *)
Definition rom_eqb (x v : Z) : bool :=
  match lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 x) with
  | Some b => Z.eqb (bv_unsigned b) v
  | None => false
  end.

Definition row_ok (x : Z) (c : lib.Reusable.YG0f.acell) : bool :=
  match row_byte c x with Some v => rom_eqb x v | None => false end.

(* a read-only byte x is pinned by a closed row of Tfib_const_abs carrying the image byte *)
Definition byte_ok (x : Z) : bool :=
  if lib.Lib.Mem.ro_addr B.Img0.rsegs (Z_to_bv 64 x) then existsb (row_ok x) lib.Reusable.YF0m.Tfib_const_abs else true.

Fixpoint bytes_ok (x : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => andb (byte_ok x) (bytes_ok (x + 1) n')
  end.

(* no read-only segment of image B meets the range r *)
Definition ro_free (r : Z * Z) : bool :=
  forallb (fun s => orb (seg_writable s)
                        (orb (Z.leb (fst r + snd r) (Z.of_N (seg_base s)))
                             (Z.leb (Z.of_N (seg_base s) + Z.of_N (seg_size s)) (fst r))))
          B.Img0.rsegs.

Definition range_ok (r : Z * Z) : bool :=
  if ro_free r then true else bytes_ok (fst r) (Z.to_nat (snd r)).

Definition owned_ro_chk : bool := forallb range_ok lib.Reusable.YF0m.Tfib_owned_static.

(* ---- 2. Its soundness. ---- *)

Lemma row_byte_spec : forall c x y, row_byte c x = Some y ->
  exists s w v, c = lib.Reusable.YG0f.ACell (lib.Reusable.YG0f.ANum s) w
                      (lib.Reusable.YG0f.AV (lib.Reusable.YG0f.ANum v)) /\
    s <= x < s + Z.of_nat w /\ y = lib.Reusable.YG0f.le_byte v w (Z.to_nat (x - s)).
Proof.
  intros [ca cw cv] x y. destruct ca; try (intro H; discriminate H).
  destruct cv as [e|mk mv]; try (intro H; discriminate H).
  destruct e; try (intro H; discriminate H).
  intro H. cbv beta iota delta [row_byte] in H.
  match type of H with (if ?t then _ else _) = _ => destruct t eqn:Eb end; [|discriminate H].
  injection H as <-. apply andb_prop in Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  do 3 eexists. split; [reflexivity|]. split; [lia | reflexivity].
Qed.

Lemma byte_ok_row : forall x, lib.Lib.Mem.ro_addr B.Img0.rsegs (Z_to_bv 64 x) = true -> byte_ok x = true ->
  exists s w v b,
    In (lib.Reusable.YG0f.ACell (lib.Reusable.YG0f.ANum s) w (lib.Reusable.YG0f.AV (lib.Reusable.YG0f.ANum v)))
       lib.Reusable.YF0m.Tfib_const_abs /\
    s <= x < s + Z.of_nat w /\
    lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 x) = Some b /\
    bv_unsigned b = lib.Reusable.YG0f.le_byte v w (Z.to_nat (x - s)).
Proof.
  intros x Hro Hok. unfold byte_ok in Hok. rewrite Hro in Hok.
  change (existsb (row_ok x) lib.Reusable.YF0m.Tfib_const_abs = true) in Hok.
  apply existsb_exists in Hok as (c & Hc & Hrow). unfold row_ok in Hrow.
  destruct (row_byte c x) as [y|] eqn:Ey; [|discriminate Hrow].
  destruct (row_byte_spec c x y Ey) as (s & w & v & -> & Hs & ->).
  unfold rom_eqb in Hrow.
  destruct (lib.Reusable.YK11.seg_rom segs (Z_to_bv 64 x)) as [b|] eqn:Er; [|discriminate Hrow].
  apply Z.eqb_eq in Hrow.
  exists s, w, v, b. split; [exact Hc|]. split; [exact Hs|]. split; [reflexivity | exact Hrow].
Qed.

Lemma bytes_ok_sound : forall n x y, bytes_ok x n = true -> x <= y < x + Z.of_nat n -> byte_ok y = true.
Proof.
  induction n as [|n IH]; intros x y H Hy; [lia|].
  cbn [bytes_ok] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec y x) as [->|Hne]; [exact H1|].
  apply (IH (x + 1) y H2). lia.
Qed.

Lemma ro_free_sound : forall (r : Z * Z) (a : word), ro_free r = true -> lib.Lib.Mem.ro_addr B.Img0.rsegs a = true ->
  ~ lib.Reusable.YG0n.in_zr (bv_unsigned a) r.
Proof.
  intros r a Hf Ha Hin. unfold lib.Lib.Mem.ro_addr in Ha.
  match type of Ha with context [find_segment ?l ?x ?n] => destruct (find_segment l x n) as [s|] eqn:E end;
    [|discriminate Ha].
  destruct (B.ProgWorldCtlRt.find_segment_some_spec _ _ _ _ E) as (Hs & Hb1 & Hb2).
  unfold ro_free in Hf. rewrite forallb_forall in Hf. specialize (Hf s Hs). cbv beta in Hf.
  apply negb_true_iff in Ha. rewrite Ha in Hf. cbn [orb] in Hf.
  unfold lib.Reusable.YG0n.in_zr in Hin.
  apply orb_true_iff in Hf as [Hf|Hf]; apply Z.leb_le in Hf; lia.
Qed.

Lemma owned_ro_chk_range : owned_ro_chk = true -> forall r, In r lib.Reusable.YF0m.Tfib_owned_static -> range_ok r = true.
Proof. intros H r Hr. unfold owned_ro_chk in H. rewrite forallb_forall in H. exact (H r Hr). Qed.

(* ---- 3. The check, run once. ---- *)
Lemma owned_ro_chk_true : owned_ro_chk = true.
Proof. time "owned_ro_chk vm_compute" (vm_compute; reflexivity). Time Qed.

(* ---- 4. The discharge. ---- *)
Section OwnedRo.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : lib.Reusable.YG0f.asyms.

(* a pinned owned read-only byte: AR's am_const row over the view reads the image byte *)
Lemma byte_ok_view : forall (TS : lib.Reusable.YF0m.CtrlTSyms B) ly S (W : lib.Reusable.YA0n.world segs)
    (m : word -> option byte) md (a : word),
  lib.Reusable.YG0n.AR segs B ly S W m md -> lib.Lib.Mem.ro_addr B.Img0.rsegs a = true ->
  byte_ok (bv_unsigned a) = true ->
  lib.Reusable.YG0n.aview segs (lib.Reusable.YA0n.w_H W) m (bv_unsigned a) =
  option_map (fun b : byte => bv_unsigned b) (lib.Reusable.YK11.seg_rom segs a).
Proof.
  intros TS ly S W m md a HAR Ha Hok.
  assert (Hro : lib.Lib.Mem.ro_addr B.Img0.rsegs (Z_to_bv 64 (bv_unsigned a)) = true)
    by (rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned; exact Ha).
  destruct (byte_ok_row (bv_unsigned a) Hro Hok) as (s & w & v & b & Hc & Hs & Er & Hb).
  rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned in Er. rewrite Er. cbn [option_map]. rewrite Hb.
  pose proof (B.ProgWorld_Fs.pw_row B TS ly S W m md _ HAR (B.ProgWorld_Fs.pw_in_abs _ ly Hc)) as Hh.
  unfold lib.Reusable.YG0f.cell_holds in Hh.
  cbn [lib.Reusable.YG0f.c_at lib.Reusable.YG0f.c_val lib.Reusable.YG0f.c_w lib.Reusable.YG0f.aeval] in Hh.
  specialize (Hh (Z.to_nat (bv_unsigned a - s)) ltac:(lia)).
  rewrite Z2Nat.id in Hh by lia. replace (s + (bv_unsigned a - s)) with (bv_unsigned a) in Hh by lia.
  exact Hh.
Qed.

Lemma AR_states_owned_ro_of_AR : lib.Reusable.YF0m.CtrlTSyms B -> B.ProgWorld.AR_states_owned_ro B.
Proof.
  intros TS. unfold B.ProgWorld.AR_states_owned_ro.
  intros ly S W m md HAR a Ha Hown.
  rewrite (lib.Reusable.YF0m.ts_owned B TS) in Hown.
  apply Exists_exists in Hown as (r & Hr & Hin).
  pose proof (owned_ro_chk_range owned_ro_chk_true r Hr) as Hrng. unfold range_ok in Hrng.
  destruct (ro_free r) eqn:Ef.
  - exfalso. exact (ro_free_sound r a Ef Ha Hin).
  - apply (byte_ok_view TS ly S W m md a HAR Ha).
    apply (bytes_ok_sound (Z.to_nat (snd r)) (fst r) (bv_unsigned a) Hrng).
    unfold lib.Reusable.YG0n.in_zr in Hin. rewrite Z2Nat.id by lia. lia.
Qed.

End OwnedRo.

Print Assumptions owned_ro_chk_true.
Print Assumptions AR_states_owned_ro_of_AR.
