(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/AllocPackGSF.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_transport; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_transport.lib. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0i YM06 YP09 YM05 YK15 YM02.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO0i YO0f YO0g YO0q YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO04 YO0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import AllocSI AllocGS AllocFree AllocMalloc.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import AllocMB AllocPack AllocPackRoom Contract SlotAgree.
Import ListNotations.
Local Open Scope Z_scope.

(* Mapped multi-slot groups of a small class map exactly their slots and header: alloc_group installs them with
   am_maplen * PGSZ = page_round (class_size sc * cnt + UNIT) and am_last = cnt - 1 (mmap_plan), and no later step
   changes am_maplen, am_sc or am_last of a group of class < 48. Single-slot groups are bounded by WF (mapped_ok). *)
Definition GSFX (X : list sptr) (s : astate) : Prop :=
  forall g am, usedX X s g am -> 0 < am_maplen am -> am_sc am < 48 -> 1 <= am_last am ->
  am_maplen am * PGSZ <= page_round (class_size (am_sc am) * (am_last am + 1) + UNIT).

Definition GSF (s : astate) : Prop := GSFX [] s.

Lemma GSF_init : GSF init_state.
Proof. intros g am H. unfold usedX, MTX, MT in H. cbn in H. discriminate. Qed.

Theorem free_GSF : forall s p tr s', GSF s -> yields (free (Some p) s) tr (tt, s') -> GSF s'.
Proof.
  intros s p tr s' HG Y. pose proof (tall_yields _ _ tr (tt, s') (kr_free (Some p) s) Y) as (_ & _ & _ & Mc).
  cbn [snd] in Mc. intros g a' Hu Hml Hsc Hl. pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
  destruct (Mc g a' Mg) as (a & Ma & L & S & T & _). rewrite L, S, T in *.
  exact (HG g a (usedX_intro [] s g a eq_refl Ma) Hml Hsc Hl).
Qed.

(* The pack resource form of the cut-free contracts: res_ok_pack plus GSF. *)
Definition pack_cf_form : ResForm := {|
  rf_R := pbound; rf_ok := fun A b => res_ok_pack A b /\ GSF A; rf_room := room_pack;
  rf_malloc := pb_malloc; rf_free := pb_free; rf_realloc := pb_realloc |}.

Lemma pack_cf_ok_pack : forall A b, rf_ok pack_cf_form A b -> res_ok_pack A b.
Proof. intros A b H. exact (proj1 H). Qed.

Lemma pack_cf_ok_init : forall b, res_ok_pack init_state b -> rf_ok pack_cf_form init_state b.
Proof. intros b H. exact (conj H GSF_init). Qed.

(* Mapped length of a group of class c holding at most FC c slots. *)
Definition GLEN (c : Z) : Z := page_round (class_size c * FC c + UNIT).

(* Mapped bytes of a reachable pack state with caps: per-class group lengths, and for band 48 the block plus
   3 pages (GS clause 2); map_bytes s <= MAPB caps + ubytes s. *)
Definition MAPB (caps : list Z) : Z :=
  zsumZ (fun c => if nestF c then 0 else (znth c (NF caps) + RED) * GLEN c) (zseq 0 48) + 3 * PGSZ * znth 48 caps.

(* LIVE2 with MAPB in place of MMAX * GMAP. *)
Definition LIVE2c (caps : list Z) (bytes : Z) : Z :=
  MAPB caps + bytes + PGSZ * (NA2 (GALL caps) + 1) + AREA2 (GALL caps).

Definition room_cf_pack (md : Model) (b : pbound) (n : Z) : Prop :=
  room_pack b n /\ LIVE2c (pb_cap b) (pb_bytes b + n) + NONHEAP_CF <= vm_limit (m_vmmaps md).
