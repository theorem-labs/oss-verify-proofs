(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep StoreFast.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF StrwF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AProto MonadF RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepInit_kit__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D Require DrvKitA__A3D. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac split_for_access_post H ::= split_junk_name H.
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition SHOFF : Z := 0x7fff8000.
Definition shd (a : Z) : Z := SHOFF + Z.shiftr a 3.
Definition shn (l : Z) : Z := Z.shiftr l 3.
(* [comment removed for export] *)
Definition SHW_LO : Z := 0x7fffa000.
Definition SHW_LEN : Z := 779776.

(* [comment removed for export] *)
Definition gdT : Type := (Z * Z * Z * Z * Z)%type.
Definition gd_cells (g : gdT) : list cell :=
  let '(beg, sz, swr, nm, md) := g in
  [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 swr); C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 md);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 18446744073709551615)].
Definition gd_ok (g : gdT) : Prop :=
  let '(beg, sz, swr, nm, md) := g in
  beg mod 8 = 0 /\ (swr = 32 \/ swr = 64 \/ swr = 96 \/ swr = 128) /\ 0x10000 <= beg /\ beg + swr <= 0x603000.
Definition gd_okb (g : gdT) : bool :=
  let '(beg, sz, swr, nm, md) := g in
  (beg mod 8 =? 0) && ((swr =? 32) || (swr =? 64) || (swr =? 96) || (swr =? 128)) && (0x10000 <=? beg) && (beg + swr <=? 0x603000).
Lemma gd_okb_ok : forall g, gd_okb g = true -> gd_ok g.
Proof.
  intros ((((beg, sz), swr), nm), md) H. unfold gd_okb in H. unfold gd_ok.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.leb_le in H3. apply Z.leb_le in H4.
  split; [exact H1|]. split; [| split; assumption].
  apply orb_prop in H2 as [H2|H2]; [apply orb_prop in H2 as [H2|H2]; [apply orb_prop in H2 as [H2|H2]|]|]; apply Z.eqb_eq in H2; tauto.
Qed.

(* [comment removed for export] *)
Definition GD69 : list gdT :=
  [ (0x21020, 2, 32, 0x1c21e, 0x21200);
    (0x21040, 10, 32, 0x1ea0c, 0x21200);
    (0x21060, 30, 64, 0x20795, 0x21200);
    (0x210a0, 28, 64, 0x1488e, 0x21200);
    (0x210e0, 21, 64, 0x137c0, 0x21200);
    (0x21120, 22, 64, 0x1d23a, 0x21200);
    (0x21160, 25, 64, 0x188cc, 0x21200);
    (0x211a0, 3, 32, 0x1a5e7, 0x21200);
    (0x211c0, 23, 64, 0x113ac, 0x21200);
    (0x21240, 45, 96, 0x1c21e, 0x21600);
    (0x212a0, 31, 64, 0x1ea0c, 0x21600);
    (0x212e0, 3, 32, 0x20795, 0x21600);
    (0x21300, 3, 32, 0x1488e, 0x21600);
    (0x21320, 54, 96, 0x137c0, 0x21600);
    (0x21380, 24, 64, 0x1d23a, 0x21600);
    (0x213c0, 71, 128, 0x188cc, 0x21600);
    (0x21440, 20, 64, 0x1a5e7, 0x21600);
    (0x21480, 45, 96, 0x113ac, 0x21600);
    (0x214e0, 48, 96, 0x1676f, 0x21600);
    (0x21540, 47, 96, 0x1faa5, 0x21600);
    (0x215a0, 43, 96, 0x113b3, 0x21600);
    (0x21640, 7, 32, 0x20795, 0x21760);
    (0x21660, 18, 64, 0x19800, 0x21760);
    (0x216a0, 33, 96, 0x2028a, 0x21760);
    (0x21700, 45, 96, 0x1ba1a, 0x21760);
    (0x217a0, 3, 32, 0x1c21e, 0x217c0);
    (0x21800, 7, 32, 0x1c21e, 0x21860);
    (0x21820, 25, 64, 0x1ea0c, 0x21860);
    (0x21b80, 24, 64, 0x1c21e, 0x21fc0);
    (0x21bc0, 71, 128, 0x1ea0c, 0x21fc0);
    (0x21c40, 40, 96, 0x20795, 0x21fc0);
    (0x21ca0, 51, 96, 0x1488e, 0x21fc0);
    (0x21d00, 33, 96, 0x137c0, 0x21fc0);
    (0x21d60, 14, 32, 0x1d23a, 0x21fc0);
    (0x21d80, 66, 128, 0x10ae5, 0x21fc0);
    (0x21e00, 60, 96, 0x17ee6, 0x21fc0);
    (0x21e60, 60, 96, 0x176cd, 0x21fc0);
    (0x21ec0, 67, 128, 0x10aed, 0x21fc0);
    (0x21f40, 67, 128, 0x137c7, 0x21fc0);
    (0x22000, 28, 64, 0x16776, 0x22040);
    (0x22080, 24, 64, 0x1c21e, 0x22ca0);
    (0x220c0, 96, 128, 0x1ea0c, 0x22ca0);
    (0x22140, 33, 96, 0x20795, 0x22ca0);
    (0x221a0, 14, 32, 0x1488e, 0x22ca0);
    (0x221c0, 42, 96, 0x137c0, 0x22ca0);
    (0x22220, 53, 96, 0x1d23a, 0x22ca0);
    (0x22280, 76, 128, 0x188cc, 0x22ca0);
    (0x22300, 66, 128, 0x1a5e7, 0x22ca0);
    (0x22380, 51, 96, 0x113ac, 0x22ca0);
    (0x223e0, 73, 128, 0x1676f, 0x22ca0);
    (0x22460, 34, 96, 0x1faa5, 0x22ca0);
    (0x224c0, 59, 96, 0x113b3, 0x22ca0);
    (0x22520, 50, 96, 0x19f4e, 0x22ca0);
    (0x22580, 36, 96, 0x1faad, 0x22ca0);
    (0x225e0, 60, 96, 0x1df86, 0x22ca0);
    (0x22640, 72, 128, 0x1c254, 0x22ca0);
    (0x226c0, 70, 128, 0x19808, 0x22ca0);
    (0x22740, 64, 96, 0x1ba22, 0x22ca0);
    (0x227a0, 75, 128, 0x11b85, 0x22ca0);
    (0x22820, 76, 128, 0x11b8d, 0x22ca0);
    (0x228a0, 71, 128, 0x17eee, 0x22ca0);
    (0x22920, 65, 128, 0x19f56, 0x22ca0);
    (0x229a0, 74, 128, 0x14895, 0x22ca0);
    (0x22a20, 96, 128, 0x13dd0, 0x22ca0);
    (0x22aa0, 49, 96, 0x137cf, 0x22ca0);
    (0x22b00, 57, 96, 0x16fbe, 0x22ca0);
    (0x22b60, 48, 96, 0x10ae5, 0x22ca0);
    (0x22bc0, 96, 128, 0x17ee6, 0x22ca0);
    (0x22c40, 60, 96, 0x176cd, 0x22ca0) ]%Z.

Lemma GD69_ok : Forall gd_ok GD69.
Proof.
  apply Forall_forall. intros g Hg. apply gd_okb_ok.
  assert (C : forallb gd_okb GD69 = true) by (vm_compute; reflexivity).
  exact (proj1 (forallb_forall _ _) C g Hg).
Qed.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT}.

#[using="Type"] Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mdtor_rt (m : mem) : Prop :=
     rw_cells asegs m 0xa5490 [C8 (Z_to_bv 64 0x13e0a0)]                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa54a0 [C8 (Z_to_bv 64 0x140128); C8 (Z_to_bv 64 0xabdf8); C8 (Z_to_bv 64 0xae5f8);
                                C8 (Z_to_bv 64 0xaf2e8); C8 (Z_to_bv 64 0xaf2f0); C8 (Z_to_bv 64 0xaf2e0)]  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa54d0 [C8 (Z_to_bv 64 0xa7360)]                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa7358 [C8 (Z_to_bv 64 0x9e6a0); C8 (Z_to_bv 64 0x9ead4)]              (* [comment removed for export] *)
  /\ rw_cells asegs m 0xae5f8 [C8 (Z_to_bv 64 0x7fff8000)]                                      (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaf2d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                              (* [comment removed for export] *)
  /\ rw_cells asegs m 0xade5c [C1 (Z_to_bv 8 1)]                                                (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1401a0 [C8 (Z_to_bv 64 18446744073709551615)]                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0xabe10 [C4 (Z_to_bv 64 1)].                                              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rt_clear (iv : Z * Z) : Prop :=
  let (lo, hi) := iv in
  lo <= hi /\
  (hi <= 0xa5490 \/ (0xa54d8 <= lo /\ hi <= 0xa7358) \/ (0xa7368 <= lo /\ hi <= 0xabe10) \/ (0xabe14 <= lo /\ hi <= 0xade5c)
   \/ (0xade5d <= lo /\ hi <= 0xae5f8) \/ (0xae600 <= lo /\ hi <= 0xaf2d8) \/ (0xaf2da <= lo /\ hi <= 0x1401a0) \/ 0x1401a8 <= lo).

#[using="Type"] Lemma mdtor_rt_frame : forall m m' W,
  mdtor_rt m -> munch W m m' -> wmono asegs m m' ->
  Forall rt_clear W -> mdtor_rt m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, 0 <= n ->
             ((0xa5490 <= A /\ A + n <= 0xa54d8) \/ (0xa7358 <= A /\ A + n <= 0xa7368) \/ (0xabe10 <= A /\ A + n <= 0xabe14)
              \/ (0xade5c <= A /\ A + n <= 0xade5d) \/ (0xae5f8 <= A /\ A + n <= 0xae600) \/ (0xaf2d8 <= A /\ A + n <= 0xaf2da)
              \/ (0x1401a0 <= A /\ A + n <= 0x1401a8)) -> disjoint_from W A n).
  { intros A n Hn HA. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold mdtor_rt in *.
  (nd_pre PC 9%nat; intros P1 P2 P3 P4 P5 P6 P7 P8 P9; nd_post).
  repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint descs_at (m : mem) (d : Z) (gs : list gdT) : Prop :=
  match gs with
  | [] => True
  | g :: gs' => rw_cells asegs m d (gd_cells g) /\ descs_at m (d + 64) gs'
  end.

#[using="Type"] Lemma gd_cells_size : forall g, cells_size (gd_cells g) = 64%nat.
Proof. intros ((((beg, sz), swr), nm), md). reflexivity. Qed.

#[using="Type"] Lemma descs_at_of_flat : forall gs m d, rw_cells asegs m d (flat_map gd_cells gs) -> descs_at m d gs.
Proof.
  induction gs as [|g gs IH]; intros m d H; cbn [descs_at flat_map]; [exact I|].
  cbn [flat_map] in H. apply (proj1 (rw_cells_app asegs m d (gd_cells g) (flat_map gd_cells gs))) in H as [H1 H2].
  rewrite gd_cells_size in H2. split; [exact H1| apply IH; exact H2].
Qed.

#[using="Type"] Lemma disjoint_from_sub : forall (W : list (Z * Z)) A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> disjoint_from W A' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros A n A' n' H H1 H2; cbn [disjoint_from] in *; [exact I|].
  destruct H as [Ha Hb]. split; [lia| eapply IH; eassumption].
Qed.

#[using="Type"] Lemma descs_at_transport : forall gs m m' W d, descs_at m d gs -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W d (64 * Z.of_nat (length gs)) -> descs_at m' d gs.
Proof.
  induction gs as [|g gs IH]; intros m m' W d H MU WM DJ; cbn [descs_at] in *; [exact I|].
  destruct H as [H1 H2]. cbn [length] in DJ. split.
  - eapply rw_cells_transport; [exact H1| exact MU| exact WM|]. rewrite gd_cells_size.
    change (Z.of_nat 64) with 64. eapply disjoint_from_sub; [exact DJ| lia| lia].
  - eapply IH; [exact H2| exact MU| exact WM|]. eapply disjoint_from_sub; [exact DJ| lia| lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma swr_byte : forall (m : mem) A v, (v = 32 \/ v = 64 \/ v = 96 \/ v = 128) ->
  rw_cells asegs m A [C8 (Z_to_bv 64 v)] -> rw_cells asegs m A [C1 (Z_to_bv 8 v)].
Proof.
  intros m A v [->|[->|[->| ->]]] H.
  all: eapply (rw_cells_hd m A _ [CB 7 (repeat (Z_to_bv 8 0) 7)]); recast H.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition poison_low_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (sb sl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (sb, sb + sl)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].

Definition poison_low_spec__stmt : Prop := forall RNG (sb sl addr size : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  mdtor_rt m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> 0x10000 <= addr -> addr + size <= 0x603000 -> shn size < 0x10000 ->
  sb = shd addr -> sl = shn size ->
  rw_cells asegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG sb sl ->
  evtF asegs RNG (poison_low_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sb sl lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5759c) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 0).
Variable sb : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 1).
Variable sl : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 2).
Variable addr : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 3).
Variable size : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 39).
Variable junk : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 40).
#[using="Type"] Lemma poison_low_spec__body : ltac:(let T := type of (fun (h : poison_low_spec__stmt) => h RNG sb sl addr size ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo junk) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (sb, (sl, (addr, (size, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (lo, junk))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST KH LO MI RT -> -> -> AL SL SZ LOW HIE SMALL -> -> DST RIMG RSTK RSH.
  atop_facts. pose proof RT as RT'. (nd_pre RT' 9%nat; intros PGC GOT GOT80 REAL SHB INI CANP THR RGL; nd_post).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (shd addr, shd addr + shn size)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd addr /\ shd addr + shn size <= 0x800cd000 /\ 0 < shn size).
  { unfold shd, shn, SHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  carve_frame 64%nat ST.
  do 8 hstep.                                          (* [comment removed for export] *)
  hstep. if_true.                                      (* [comment removed for export] *)
  zstep. hstep. if_cases K1; zify_cond K1.              (* [comment removed for export] *)
  { exfalso. apply K1. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
  do 3 hstep.                                          (* [comment removed for export] *)
  do 4 zstep.                                          (* [comment removed for export] *)
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  hstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. hstep. if_cases K8; zify_cond K8.
  { exfalso. apply K8. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact SL. }
  do 2 zstep.                                          (* [comment removed for export] *)
  hstep. if_cases K9; zify_cond K9. 2:{ exfalso. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 3 hstep.                                          (* [comment removed for export] *)
  hstep. if_cases K10; zify_cond K10; [exfalso; lia|]. (* [comment removed for export] *)
  do 5 zstep.                                          (* [comment removed for export] *)
  assert (E1 : (Z.shiftr (addr + size + -8) 3 + 1) mod 18446744073709551616 - Z.shiftr addr 3 = shn size).
  { unfold shn. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  rewrite E1. clear E1. change (2147450880 + Z.shiftr addr 3) with (shd addr).
  hstep. if_false.                                     (* [comment removed for export] *)
  do 3 hstep.                                          (* [comment removed for export] *)
  hstep. if_cases KT; zify_cond KT.                    (* [comment removed for export] *)
  2:{ exfalso. lia. }
  do 3 hstep. do 8 hstep.                              (* [comment removed for export] *)
  hstep.                                               (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply memset_spec; [ rewrite !unsigned_lit by lia; exact DST | exact MI | rewrite !unsigned_lit by lia; exact RSH ]. }
  intros ms' PO. unfold memset_post in PO. unfold poison_low_post. destruct_exs PO.
  (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MU2 WM2 MI2 DST2; nd_post).
  rewrite !unsigned_lit in MU2, DST2 by lia. change (0 mod 256) with 0 in DST2.
  do 16 eexists. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros xq Hxq. cbn in Hxq |- *. tauto. }
  split. { eapply wmono_trans; [exact WM| exact WM2]. }
  split. { exact MI2. }
  split. 2: exact DST2.
  pose proof (rw_cells_transport asegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR'.
  pose proof (stk_transport_disjoint asegs _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST'.
  eapply stk_release in FR'; [| exact ST' | lia]. cbn [cells_size csize Nat.add] in FR'.
  match type of FR' with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in FR' by lia end. exact FR'.
Qed.
End Zd1.
#[using="Type"] Lemma poison_low_spec : ltac:(let t := eval cbv delta [poison_low_spec__stmt] in poison_low_spec__stmt in exact t).
Proof. exact poison_low_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unreg_one_post (spv d sb sl : Z) (gp tp s5 s6 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x41f7c) (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x140128) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 2) (Z_to_bv 64 0x1b3c6) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0xa7360) s8 (Z_to_bv 64 0xabdf8)
                  (Z_to_bv 64 0xae5f8) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x41f7c) fc None m' (seg_rom asegs)
    /\ munch [(sb, sb + sl)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].

Definition unreg_one_spec__stmt : Prop := forall RNG (sb sl : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (spv d beg swr : Z) (gsz gnm gmd gdy glc godr : word) (junk : list byte),
  mem_inv asegs m -> mdtor_rt m ->
  rw_cells asegs m d [C8 (Z_to_bv 64 beg); C8 gsz; C8 (Z_to_bv 64 swr); C8 gnm; C8 gmd; C8 gdy; C8 glc; C8 godr] ->
  rw_cells asegs m (d + 16) [C1 (Z_to_bv 8 swr)] ->
  beg mod 8 = 0 -> swr mod 8 = 0 -> 0 < swr < 256 -> 0x10000 <= beg -> beg + swr <= 0x603000 ->
  0x10000 <= d -> d + 64 <= 0x603000 -> 0 <= spv < 2^64 ->
  sb = shd beg -> sl = shn swr ->
  rw_cells asegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG sb sl ->
  evtF asegs RNG (unreg_one_post spv d sb sl gp tp s5 s6 s8 s11 F fc m)
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x140128) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1b3c6) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0xa7360) s8 (Z_to_bv 64 0xabdf8)
             (Z_to_bv 64 0xae5f8) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41f94) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 0).
Variable sb : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 1).
Variable sl : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 2).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 17).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 18).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 19).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 20).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 21).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 22).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 23).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 24).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 25).
Variable F : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 26).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 27).
Variable m : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 28).
Variable spv : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 29).
Variable d : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 30).
Variable beg : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 31).
Variable swr : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 32).
Variable gsz : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 33).
Variable gnm : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 34).
Variable gmd : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 35).
Variable gdy : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 36).
Variable glc : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 37).
Variable godr : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 38).
Variable junk : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 39).
#[using="Type"] Lemma unreg_one_spec__body : ltac:(let T := type of (fun (h : unreg_one_spec__stmt) => h RNG sb sl ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s11 t3 t4 t5 t6 F fc m spv d beg swr gsz gnm gmd gdy glc godr junk) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (sb, (sl, (ra, (gp, (tp, (t0, (t1, (t2, (s0, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s5, (s6, (s8, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (spv, (d, (beg, (swr, (gsz, (gnm, (gmd, (gdy, (glc, (godr, junk)))))))))))))))))))))))))))))))))))))))) as _.
 intros MI RT D DB AL SL SWR LOW HIE DLO DHI SPV -> -> DST RIMG RSH.
  pose proof RT as RT'. (nd_pre RT' 9%nat; intros PGC GOT GOT80 REAL SHB INI CANP THR RGL; nd_post).
  pose proof (munch_refl [(shd beg, shd beg + shn swr)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd beg /\ shd beg + shn swr <= 0x800cd000 /\ 0 < shn swr < 32).
  { unfold shd, shn, SHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  do 7 hstep.
  hstep. if_false.                                     (* [comment removed for export] *)
  hstep.                                               (* [comment removed for export] *)
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  hstep. if_true.                                      (* [comment removed for export] *)
  hstep. if_false.                                     (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 2 hstep. do 4 zstep.
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  hstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. hstep. if_cases K3; zify_cond K3.
  { exfalso. apply K3. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
  hstep. zstep. rewrite (unsigned_lit8 swr) by lia. hstep. if_cases K4; zify_cond K4.
  { exfalso. apply K4. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact SL. }
  (* [comment removed for export] *)
  do 6 hstep. hstep. if_false.
  (* [comment removed for export] *)
  do 3 hstep. do 5 zstep. hstep. do 3 zstep.
  assert (E1 : (2147450880 + Z.shiftr (beg + swr + -8) 3 + 1) mod 18446744073709551616 - (2147450880 + Z.shiftr beg 3) mod 18446744073709551616
               = shn swr).
  { unfold shn. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  rewrite E1. clear E1. change (2147450880 + Z.shiftr beg 3) with (shd beg).
  hstep. if_cases KT; zify_cond KT. 2:{ exfalso. lia. }  (* [comment removed for export] *)
  do 3 hstep.                                          (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply memset_spec; [ rewrite !unsigned_lit by lia; exact DST | exact MI | rewrite !unsigned_lit by lia; exact RSH ]. }
  intros ms' PO. unfold memset_post in PO. unfold unreg_one_post. destruct_exs PO.
  (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MU2 WM2 MI2 DST2; nd_post).
  rewrite !unsigned_lit in MU2, DST2 by lia. change (0 mod 256) with 0 in DST2.
  cbn [ret_pc reg_get].
  replace (ret_pc (Z_to_bv 64 0x41f7c)) with (Z_to_bv 64 0x41f7c : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  do 17 eexists. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU|]. exact MU2. }
  split. { eapply wmono_trans; [exact WM| exact WM2]. }
  split. { exact MI2. }
  exact DST2.
Qed.
End Zd2.
#[using="Type"] Lemma unreg_one_spec : ltac:(let t := eval cbv delta [unreg_one_spec__stmt] in unreg_one_spec__stmt in exact t).
Proof. exact unreg_one_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unreg_loop_post (spv d' n' : Z) (gp tp s5 s6 s8 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x140128) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 2) (Z_to_bv 64 0x1b3c6) (Z_to_bv 64 d') s5 s6 (Z_to_bv 64 0xa7360) s8 (Z_to_bv 64 0xabdf8)
                  (Z_to_bv 64 0xae5f8) (Z_to_bv 64 n') t3 t4 t5 t6)
             F (Z_to_bv 64 0x41f94) fc None m' (seg_rom asegs)
    /\ munch [(SHW_LO, SHW_LO + SHW_LEN)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

#[using="Type"] Lemma shadow_window : forall beg swr, beg mod 8 = 0 -> swr mod 8 = 0 -> 0 < swr -> 0x10000 <= beg -> beg + swr <= 0x603000 ->
  SHW_LO <= shd beg /\ shd beg + shn swr <= SHW_LO + SHW_LEN /\ 0 < shn swr.
Proof.
  intros beg swr AL SL SZ LOW HIE. unfold shd, shn, SHOFF, SHW_LO, SHW_LEN. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition gd_shw (m : mem) (g : gdT) : Prop := let '(beg, sz, swr, nm, md) := g in wr_at asegs m (shd beg) (shn swr).
#[using="Type"] Lemma gd_shw_transport : forall m m' gs, Forall (gd_shw m) gs -> wmono asegs m m' -> Forall (gd_shw m') gs.
Proof.
  intros m m' gs H WM. eapply Forall_impl; [| exact H]. intros ((((beg, sz), swr), nm), md) Hg. unfold gd_shw in *.
  eapply wr_at_transport; [exact Hg| exact WM].
Qed.

#[using="Type"] Lemma unreg_loop : forall RNG (gs : list gdT) (d n spv : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem),
  mem_inv asegs m -> mdtor_rt m -> descs_at m d gs -> Forall gd_ok gs ->
  Forall (gd_shw m) gs ->
  0x10000 <= d -> d + 64 * Z.of_nat (length gs) <= 0x603000 -> 0 <= spv < 2^64 ->
  Z.of_nat (length gs) < n < 2^32 ->
  rng_aimg RNG -> rng RNG SHW_LO SHW_LEN ->
  evtF asegs RNG (unreg_loop_post spv (d + 64 * Z.of_nat (length gs)) (n - Z.of_nat (length gs)) gp tp s5 s6 s8 F fc m)
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x140128) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1b3c6) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0xa7360) s8 (Z_to_bv 64 0xabdf8)
             (Z_to_bv 64 0xae5f8) (Z_to_bv 64 n) t3 t4 t5 t6)
        F (Z_to_bv 64 0x41f94) fc None m (seg_rom asegs)).
Proof.
  intros RNG gs. induction gs as [|g gs IH];
    intros d n spv ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 t3 t4 t5 t6 F fc m MI RT DA OK WR DLO DHI SPV HN RIMG RISH.
  - apply evtF_done. unfold unreg_loop_post. cbn [length]. replace (d + 64 * Z.of_nat 0) with d by lia. replace (n - Z.of_nat 0) with n by lia.
    do 18 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI].
  - destruct g as ((((beg, sz), swr), nm), md). cbn [descs_at] in DA. destruct DA as [D DA'].
    apply Forall_cons_iff in OK as [OKg OK']. (nd_pre OKg 4%nat; intros AL SWR BLO BHI; nd_post).
    apply Forall_cons_iff in WR as [WRg WR']. unfold gd_shw in WRg.
    cbn [length] in DHI, HN.
    assert (SWRf : swr mod 8 = 0 /\ 0 < swr < 256) by (clear -SWR; destruct SWR as [->|[->|[->| ->]]]; (split; [reflexivity| lia])).
    destruct SWRf as [SL SWRr].
    (pose proof (shadow_window beg swr AL SL ltac:(lia) BLO BHI) as ndP__; nd_pre ndP__ 3%nat; intros SH1 SH2 SH3; nd_post).
    (* [comment removed for export] *)
    pose proof D as D16. unfold gd_cells in D16. apply rw_cells_tl in D16. apply rw_cells_tl in D16. apply rw_cells_hd in D16.
    change (Z.of_nat (csize (C8 (Z_to_bv 64 beg)))) with 8 in D16. change (Z.of_nat (csize (C8 (Z_to_bv 64 sz)))) with 8 in D16.
    replace (d + 8 + 8) with (d + 16) in D16 by lia.
    apply swr_byte in D16; [| exact SWR].
    (* [comment removed for export] *)
    destruct (rw_cells_of_wr_at asegs m (shd beg) (shn swr)) as (junk & _ & DST).
    { exact WRg. }
    { apply no_image_asan. unfold SHW_LO in SH1. lia. }
    { lia. }
    eapply evtF_cut.
    { eapply (unreg_one_spec RNG (shd beg) (shn swr)) with (d := d) (beg := beg) (swr := swr);
        [ exact MI | exact RT | exact D | exact D16 | exact AL | exact SL | exact SWRr | exact BLO | exact BHI | exact DLO | lia | exact SPV
        | reflexivity | reflexivity | exact DST | exact RIMG | eapply rng_sub'; [exact RISH| lia] ]. }
    cbv beta. intros ms' PO. unfold unreg_one_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MU1 WM1 MI1 _; nd_post).
    lazymatch type of MU1 with munch _ _ ?mm => assert (D' : rw_cells asegs mm d (gd_cells (beg, sz, swr, nm, md))) end.
    { eapply rw_cells_transport; [exact D| exact MU1| exact WM1|]. rewrite gd_cells_size. cbn [disjoint_from]. unfold SHW_LO in SH1. lia. }
    unfold gd_cells in D'.
    clear D D16 DST MI.
    (* [comment removed for export] *)
    hstep.
    sf_old_zstep.          (* [comment removed for export] *)
    astep. hstep. hstep. hstep.
    if_cases K; zify_cond K; [exfalso; lia|]. clear K.
    eapply evtF_mono.
    { eapply (IH (d + 64) (n + -1) spv); [exact MI1 | | | exact OK' | | lia | lia | exact SPV | lia | exact RIMG | exact RISH].
      - eapply mdtor_rt_frame; [exact RT| exact MU1| exact WM1|]. apply Forall_cons; [| apply Forall_nil]. cbn. unfold SHW_LO in SH1. lia.
      - eapply descs_at_transport; [exact DA'| exact MU1| exact WM1|]. cbn [disjoint_from]. unfold SHW_LO in SH1. lia.
      - eapply gd_shw_transport; [exact WR'| exact WM1]. }
    cbv beta. intros ms' PO. unfold unreg_loop_post in PO |- *. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 3%nat; intros MU2 WM2 MI2; nd_post).
    cbn [length].
    replace (d + 64 * Z.of_nat (S (length gs))) with (d + 64 + 64 * Z.of_nat (length gs)) by lia.
    replace (n - Z.of_nat (S (length gs))) with (n + -1 - Z.of_nat (length gs)) by lia.
    do 18 eexists. split; [reflexivity|]. split; [| split; [eapply wmono_trans; eassumption| exact MI2]].
    eapply munch_trans; [| exact MU2]. eapply munch_weaken; [| exact MU1]. intros xq Hx. cbn [outside] in Hx |- *. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mdtor_pre (m : mem) : Prop :=
     mdtor_rt m
  /\ rw_cells asegs m 0xa6148 [C8 (Z_to_bv 64 0xa9db0); C8 (Z_to_bv 64 0xaaf30)]     (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaaf40 [C8 (Z_to_bv 64 1)]                                     (* [comment removed for export] *)
  /\ rw_cells asegs m 0xabeb0 [C8 (Z_to_bv 64 0)]                                     (* [comment removed for export] *)
  /\ descs_at m 0xa9db0 GD69                                                          (* [comment removed for export] *)
  /\ rw_cells asegs m 700144 [C8 (Z_to_bv 64 0x5e0c80); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 32); C8 (Z_to_bv 64 0x16fb6);
                                C8 (Z_to_bv 64 0x21200); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x5e0ca0)]
                                                                                      (* [comment removed for export] *)
  /\ (exists b, rw_cells asegs m 0x5e0ca0 [C1 b])                                     (* [comment removed for export] *)
  /\ Forall (gd_shw m) GD69 /\ wr_at asegs m (shd 0x5e0c80) (shn 32)                   (* [comment removed for export] *)
  /\ wr_at asegs m (shd 0xa9db0) (shn 4480).                                          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition MDTOR_KEEP : list (Z * Z) :=
  [(0xa5490, 0xa54d8); (0xa6148, 0xa6158); (0xa7358, 0xa7368); (0xa9db0, 0xaaf30); (0xaaf40, 0xaaf48); (0xabe10, 0xabe14); (0xabeb0, 0xabeb8);
   (0xade5c, 0xade5d); (0xae5f8, 0xae600); (0xaf2d8, 0xaf2da); (0x1401a0, 0x1401a8); (0x5e0ca0, 0x5e0ca1)].
(* [comment removed for export] *)
Definition MDTOR_W : list (Z * Z) := [(0xaaf40, 0xaaf48); (0xabeb0, 0xabeb8); (0x5e0ca0, 0x5e0ca1); (SHW_LO, SHW_LO + SHW_LEN)].

Definition mdtor_pre_frame__stmt : Prop := forall m m' W,
  mdtor_pre m -> munch W m m' -> wmono asegs m m' -> Forall (iv_clear MDTOR_KEEP) W -> mdtor_pre m'.
Section Zd3.   (* [comment removed for export] *)
Variable m : ltac2:(SecDietF.SzSecF.ty 'mdtor_pre_frame__stmt 0).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'mdtor_pre_frame__stmt 1).
Variable W : ltac2:(SecDietF.SzSecF.ty 'mdtor_pre_frame__stmt 2).
#[using="Type"] Lemma mdtor_pre_frame__body : ltac:(let T := type of (fun (h : mdtor_pre_frame__stmt) => h m m' W) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (m, (m', W))) as _.
  intros P MU WM HW.
  assert (K : forall k A n, In k MDTOR_KEEP -> fst k <= A -> A + n <= snd k -> disjoint_from W A n)
    by (intros k A n Hk H1 H2; eapply keep_disjoint; eassumption).
  (nd_pre P 10%nat; intros RT G1 G2 G3 DA D69 [b OD] SH SH69 SHT; nd_post).
  unfold mdtor_pre. split.
  { (nd_pre RT 9%nat; intros P1 P2 P3 P4 P5 P6 P7 P8 P9; nd_post). unfold mdtor_rt.
    repeat match goal with |- _ /\ _ => split end.
    - eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xa5490, 0xa54d8)); [keep_in| cbn; lia| cbn; lia]].
    - eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xa5490, 0xa54d8)); [keep_in| cbn; lia| cbn; lia]].
    - eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xa5490, 0xa54d8)); [keep_in| cbn; lia| cbn; lia]].
    - eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xa7358, 0xa7368)); [keep_in| cbn; lia| cbn; lia]].
    - eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xae5f8, 0xae600)); [keep_in| cbn; lia| cbn; lia]].
    - eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xaf2d8, 0xaf2da)); [keep_in| cbn; lia| cbn; lia]].
    - eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xade5c, 0xade5d)); [keep_in| cbn; lia| cbn; lia]].
    - eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0x1401a0, 0x1401a8)); [keep_in| cbn; lia| cbn; lia]].
    - eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xabe10, 0xabe14)); [keep_in| cbn; lia| cbn; lia]]. }
  split. { eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xa6148, 0xa6158)); [keep_in| cbn; lia| cbn; lia]]. }
  split. { eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xaaf40, 0xaaf48)); [keep_in| cbn; lia| cbn; lia]]. }
  split. { eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xabeb0, 0xabeb8)); [keep_in| cbn; lia| cbn; lia]]. }
  split. { eapply descs_at_transport; [exact DA | exact MU | exact WM | apply (K (0xa9db0, 0xaaf30)); [keep_in| cbn; lia| cbn; lia]]. }
  split. { eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xa9db0, 0xaaf30)); [keep_in| cbn; lia| cbn; lia]]. }
  split. { exists b. eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0x5e0ca0, 0x5e0ca1)); [keep_in| cbn; lia| cbn; lia]]. }
  split. { eapply gd_shw_transport; [exact SH| exact WM]. }
  split; (eapply wr_at_transport; [eassumption| exact WM]).
Qed.
End Zd3.
#[using="Type"] Lemma mdtor_pre_frame : ltac:(let t := eval cbv delta [mdtor_pre_frame__stmt] in mdtor_pre_frame__stmt in exact t).
Proof. exact mdtor_pre_frame__body. Qed.
End CANSEC1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Ltac hstep ::= zstep; fix_lit_store.
Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.
Ltac rt_split := unfold mdtor_rt; repeat match goal with |- _ /\ _ => split end; hyp_by_addr.
Ltac lit_nat := repeat match goal with H : rw_cells _ _ _ [CB (Z.to_nat (Zpos ?p)) _] |- _ =>
                  let v := eval vm_compute in (Z.to_nat (Zpos p)) in change (Z.to_nat (Zpos p)) with v in H; move H at top end.

(* [comment removed for export] *)
Ltac side RIMG RSTK :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- rng _ _ _ => first [ assumption | eapply rng_sub'; [exact RSTK | lia] ]
  | |- rng_aimg _ => exact RIMG
  | |- rw_cells _ _ (?a + ?b) _ => let v := eval vm_compute in (a + b) in change (a + b) with v; hyp_by_addr
  | |- rw_cells _ _ _ _ => hyp_by_addr
  | |- mdtor_rt _ => rt_split
  | |- mem_inv _ _ => hyp_by_addr
  | |- stk _ _ _ _ => hyp_by_addr
  | |- @eq _ _ _ => reflexivity
  | |- Z.lt (shn _) _ => vm_compute; reflexivity
  | |- _ => lia
  end.

Section CANSEC3. Context {rc : runConstT}.
Definition module_dtor_proof__stmt : Prop := module_dtor_stmt mdtor_pre MDTOR_W.
Section Zd4.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 34).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 35).
#[using="Type"] Lemma module_dtor_proof__body : ltac:(let T := type of (fun (h : module_dtor_proof__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, lo)))))))))))))))))))))))))))))))))))) as _.
  unfold module_dtor_stmt.  intros HPRE ST LO KH MI RSTK RIMG RISH.
  unfold MDTOR_DEPTH in LO. atop_facts.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof HPRE as P. unfold mdtor_pre in P.
  (nd_pre P 10%nat; intros RT GSS FLG MTX DA D69 [ob OD] SH SH69 SHT; nd_post).
  pose proof RT as RT'. (nd_pre RT' 9%nat; intros PGC GOT GOT80 REAL SHB INI CANP THR RGL; nd_post).
  pose proof (munch_refl ((bv_unsigned sp - 4096, bv_unsigned sp) :: MDTOR_W)%Z m) as MU. unfold MDTOR_W in MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (RSF : rng RNG (bv_unsigned sp + -272) 272) by (eapply rng_sub'; [exact RSTK | lia]). move RIMG at bottom.
  sort_lits.
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 9 hstep.
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 3 hstep. astep. hstep. hstep. astep. do 2 hstep. astep. do 4 hstep.
  (* [comment removed for export] *)
  carve_frame 176%nat ST.
  do 14 hstep.
  do 5 hstep.                                          (* [comment removed for export] *)
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  astep.                                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  steps_to 0x41e80%Z.
  amo_step. astep. amo_step. astep. astep.
  move MTX after RGL.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  hstep. hstep. astep.
  steps_to 0x41f94%Z.
  (* [comment removed for export] *)
  pose proof GD69_ok as GOK.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (DAc : descs_at mc 0xa9db0 GD69)
      by (eapply descs_at_transport; [exact DA| exact MU| exact WM|]; change (Z.of_nat (length GD69)) with 69; cbn [disjoint_from]; unfold SHW_LO, SHW_LEN; lia);
    pose proof (gd_shw_transport _ _ _ SH WM) as SHc end.
  eapply evtF_cut.
  { eapply (unreg_loop RNG GD69 0xa9db0 70 (bv_unsigned sp + -208));
      [ hyp_by_addr | rt_split | exact DAc | exact GOK | exact SHc | lia | change (Z.of_nat (length GD69)) with 69; lia | lia
      | change (Z.of_nat (length GD69)) with 69; lia | exact RIMG | exact RISH ]. }
  cbv beta. intros ms' PO. unfold unreg_loop_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 3%nat; intros MUc WMc MIc; nd_post).
  change (Z.of_nat (length GD69)) with 69 in *. change (0xa9db0 + 64 * 69) with 700144. change (70 - 69) with 1.
  clear DAc SHc. unfold SHW_LO, SHW_LEN in MUc, MU. cbn [Z.add Pos.add Pos.succ Pos.add_carry] in MUc, MU.
  clear MI. rename MIc into MI.
  lazymatch type of MUc with munch _ ?m0 ?m1 => transport_after_call asegs m0 m1 MUc WMc; clear MUc WMc; try clear m0 end.
  (* [comment removed for export] *)
  (nd_pre (rw_cells_of_wr_at asegs _ (shd 0x5e0c80) (shn 32) SH69 ltac:(apply no_image_asan; vm_compute; discriminate) ltac:(vm_compute; discriminate)) 3%nat; intros j69 _ DST69; nd_post).
  change (shd 0x5e0c80) with 0x800b4190 in DST69. change (shn 32) with 4 in DST69.
  pose proof D69 as B69. apply rw_cells_tl in B69. apply rw_cells_tl in B69. apply rw_cells_hd in B69.
  change (700144 + Z.of_nat (csize (C8 (Z_to_bv 64 0x5e0c80))) + Z.of_nat (csize (C8 (Z_to_bv 64 8)))) with 0xaaf00 in B69.
  apply swr_byte in B69; [| left; reflexivity].
  assert (RX : rng RNG 0x800b4190 4) by (apply (rng_sub' _ _ _ _ _ RISH); lia).
  call (unreg_one_spec RNG 0x800b4190 4). all: side RIMG RSTK. clear RX.
  lit_nat. hstep. hstep. astep.                        (* [comment removed for export] *)
  hstep. hstep. hstep. astep. hstep.
  (* [comment removed for export] *)
  do 6 hstep. hstep.
  (nd_pre (rw_cells_of_wr_at asegs _ (shd 0xa9db0) (shn 4480) SHT ltac:(apply no_image_asan; vm_compute; discriminate) ltac:(vm_compute; discriminate)) 3%nat; intros jT _ DSTT; nd_post).
  change (shd 0xa9db0) with 0x8000d3b6 in DSTT. change (shn 4480) with 560 in DSTT.
  assert (RX : rng RNG 0x8000d3b6 560) by (apply (rng_sub' _ _ _ _ _ RISH); lia).
  call_sp (poison_low_spec RNG 0x8000d3b6 560 0xa9db0 4480). all: side RIMG RSTK. clear RX.
  lit_nat.
  (* [comment removed for export] *)
  steps_to 0x421f0%Z.
  amo_step. astep. amo_step. astep. astep.
  astep.                                               (* [comment removed for export] *)
  steps_to 0x42448%Z.
  (* [comment removed for export] *)
  match goal with H : rw_cells _ _ (bv_unsigned sp + -208) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -32)%Z end.
  hstep. hstep. hstep. hstep.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -32) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -16)%Z end.
  hstep. hstep. hstep.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -16) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
  hstep.
  unfold module_dtor_post. sys_finish.
Qed.
End Zd4.
#[using="Type"] Theorem module_dtor_proof : ltac:(let t := eval cbv delta [module_dtor_proof__stmt] in module_dtor_proof__stmt in exact t).
Proof. exact module_dtor_proof__body. Qed.
End CANSEC3.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StrwF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepInit_kit__A3W.ARepInit_kit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.DrvKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3D.DrvKitA__A3D.ExitA.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac split_for_access_post H ::= split_junk_name H.
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition SHOFF : Z := 0x7fff8000.
Definition shd (a : Z) : Z := SHOFF + Z.shiftr a 3.
Definition shn (l : Z) : Z := Z.shiftr l 3.
(* [comment removed for export] *)
Definition SHW_LO : Z := 0x7fffa000.
Definition SHW_LEN : Z := 780288.

(* [comment removed for export] *)
Definition gdT : Type := (Z * Z * Z * Z * Z)%type.
Definition gd_cells (g : gdT) : list cell :=
  let '(beg, sz, swr, nm, md) := g in
  [C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 swr); C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 md);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 18446744073709551615)].
Definition gd_ok (g : gdT) : Prop :=
  let '(beg, sz, swr, nm, md) := g in
  beg mod 8 = 0 /\ (swr = 32 \/ swr = 64 \/ swr = 96 \/ swr = 128) /\ 0x10000 <= beg /\ beg + swr <= 0x604000.
Definition gd_okb (g : gdT) : bool :=
  let '(beg, sz, swr, nm, md) := g in
  (beg mod 8 =? 0) && ((swr =? 32) || (swr =? 64) || (swr =? 96) || (swr =? 128)) && (0x10000 <=? beg) && (beg + swr <=? 0x604000).
Lemma gd_okb_ok : forall g, gd_okb g = true -> gd_ok g.
Proof.
  intros ((((beg, sz), swr), nm), md) H. unfold gd_okb in H. unfold gd_ok.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.leb_le in H3. apply Z.leb_le in H4.
  split; [exact H1|]. split; [| split; assumption].
  apply orb_prop in H2 as [H2|H2]; [apply orb_prop in H2 as [H2|H2]; [apply orb_prop in H2 as [H2|H2]|]|]; apply Z.eqb_eq in H2; tauto.
Qed.

(* [comment removed for export] *)
Definition GD69 : list gdT :=
  [ (0x21020, 2, 32, 0x1c216, 0x21200);
    (0x21040, 10, 32, 0x1ea0c, 0x21200);
    (0x21060, 30, 64, 0x20795, 0x21200);
    (0x210a0, 28, 64, 0x137c0, 0x21200);
    (0x210e0, 21, 64, 0x1d23a, 0x21200);
    (0x21120, 22, 64, 0x188cc, 0x21200);
    (0x21160, 25, 64, 0x1a5df, 0x21200);
    (0x211a0, 3, 32, 0x113ac, 0x21200);
    (0x211c0, 23, 64, 0x1676f, 0x21200);
    (0x21240, 45, 96, 0x1c216, 0x21600);
    (0x212a0, 31, 64, 0x1ea0c, 0x21600);
    (0x212e0, 3, 32, 0x20795, 0x21600);
    (0x21300, 3, 32, 0x1488e, 0x21600);
    (0x21320, 54, 96, 0x1d23a, 0x21600);
    (0x21380, 24, 64, 0x188cc, 0x21600);
    (0x213c0, 71, 128, 0x1a5df, 0x21600);
    (0x21440, 20, 64, 0x113ac, 0x21600);
    (0x21480, 45, 96, 0x1676f, 0x21600);
    (0x214e0, 48, 96, 0x1faa5, 0x21600);
    (0x21540, 47, 96, 0x113b3, 0x21600);
    (0x215a0, 43, 96, 0x19f46, 0x21600);
    (0x21640, 7, 32, 0x20795, 0x21760);
    (0x21660, 18, 64, 0x2028a, 0x21760);
    (0x216a0, 33, 96, 0x1ba12, 0x21760);
    (0x21700, 45, 96, 0x1cbbc, 0x21760);
    (0x217a0, 3, 32, 0x1c216, 0x217c0);
    (0x21800, 7, 32, 0x1c216, 0x21860);
    (0x21820, 25, 64, 0x1ea0c, 0x21860);
    (0x21b80, 24, 64, 0x1c216, 0x21fc0);
    (0x21bc0, 71, 128, 0x1ea0c, 0x21fc0);
    (0x21c40, 40, 96, 0x20795, 0x21fc0);
    (0x21ca0, 51, 96, 0x1488e, 0x21fc0);
    (0x21d00, 33, 96, 0x137c0, 0x21fc0);
    (0x21d60, 14, 32, 0x1d23a, 0x21fc0);
    (0x21d80, 66, 128, 0x10ae5, 0x21fc0);
    (0x21e00, 60, 96, 0x17ee6, 0x21fc0);
    (0x21e60, 60, 96, 0x176cd, 0x21fc0);
    (0x21ec0, 67, 128, 0x10aed, 0x21fc0);
    (0x21f40, 67, 128, 0x137c7, 0x21fc0);
    (0x22000, 28, 64, 0x16776, 0x22040);
    (0x22080, 24, 64, 0x1c216, 0x22ca0);
    (0x220c0, 96, 128, 0x1ea0c, 0x22ca0);
    (0x22140, 33, 96, 0x20795, 0x22ca0);
    (0x221a0, 14, 32, 0x1488e, 0x22ca0);
    (0x221c0, 42, 96, 0x137c0, 0x22ca0);
    (0x22220, 53, 96, 0x1d23a, 0x22ca0);
    (0x22280, 76, 128, 0x188cc, 0x22ca0);
    (0x22300, 66, 128, 0x1a5df, 0x22ca0);
    (0x22380, 51, 96, 0x113ac, 0x22ca0);
    (0x223e0, 73, 128, 0x1676f, 0x22ca0);
    (0x22460, 34, 96, 0x1faa5, 0x22ca0);
    (0x224c0, 59, 96, 0x113b3, 0x22ca0);
    (0x22520, 50, 96, 0x19f46, 0x22ca0);
    (0x22580, 36, 96, 0x1faad, 0x22ca0);
    (0x225e0, 60, 96, 0x1df86, 0x22ca0);
    (0x22640, 72, 128, 0x1c24c, 0x22ca0);
    (0x226c0, 70, 128, 0x19800, 0x22ca0);
    (0x22740, 64, 96, 0x1ba1a, 0x22ca0);
    (0x227a0, 75, 128, 0x11b85, 0x22ca0);
    (0x22820, 76, 128, 0x11b8d, 0x22ca0);
    (0x228a0, 71, 128, 0x17eee, 0x22ca0);
    (0x22920, 65, 128, 0x19f4e, 0x22ca0);
    (0x229a0, 74, 128, 0x14895, 0x22ca0);
    (0x22a20, 96, 128, 0x13dd0, 0x22ca0);
    (0x22aa0, 49, 96, 0x137cf, 0x22ca0);
    (0x22b00, 57, 96, 0x16fbe, 0x22ca0);
    (0x22b60, 48, 96, 0x10ae5, 0x22ca0);
    (0x22bc0, 96, 128, 0x17ee6, 0x22ca0);
    (0x22c40, 60, 96, 0x176cd, 0x22ca0) ]%Z.

Lemma GD69_ok : Forall gd_ok GD69.
Proof.
  apply Forall_forall. intros g Hg. apply gd_okb_ok.
  assert (C : forallb gd_okb GD69 = true) by (vm_compute; reflexivity).
  exact (proj1 (forallb_forall _ _) C g Hg).
Qed.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT}.

#[using="Type"] Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mdtor_rt (m : mem) : Prop :=
     rw_cells asegs m 0xa5870 [C8 (Z_to_bv 64 0x13e4a0)]                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa5880 [C8 (Z_to_bv 64 0x140528); C8 (Z_to_bv 64 0xac1f8); C8 (Z_to_bv 64 0xae9f8);
                                C8 (Z_to_bv 64 0xaf6e8); C8 (Z_to_bv 64 0xaf6f0); C8 (Z_to_bv 64 0xaf6e0)]  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa58b0 [C8 (Z_to_bv 64 0xa7740)]                                        (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa7738 [C8 (Z_to_bv 64 0x9ea84); C8 (Z_to_bv 64 0x9eeb8)]              (* [comment removed for export] *)
  /\ rw_cells asegs m 0xae9f8 [C8 (Z_to_bv 64 0x7fff8000)]                                      (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaf6d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                              (* [comment removed for export] *)
  /\ rw_cells asegs m 0xae25c [C1 (Z_to_bv 8 1)]                                                (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1405a0 [C8 (Z_to_bv 64 18446744073709551615)]                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0xac210 [C4 (Z_to_bv 64 1)].                                              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition rt_clear (iv : Z * Z) : Prop :=
  let (lo, hi) := iv in
  lo <= hi /\
  (hi <= 0xa5870 \/ (0xa58b8 <= lo /\ hi <= 0xa7738) \/ (0xa7748 <= lo /\ hi <= 0xac210) \/ (0xac214 <= lo /\ hi <= 0xae25c)
   \/ (0xae25d <= lo /\ hi <= 0xae9f8) \/ (0xaea00 <= lo /\ hi <= 0xaf6d8) \/ (0xaf6da <= lo /\ hi <= 0x1405a0) \/ 0x1405a8 <= lo).

#[using="Type"] Lemma mdtor_rt_frame : forall m m' W,
  mdtor_rt m -> munch W m m' -> wmono asegs m m' ->
  Forall rt_clear W -> mdtor_rt m'.
Proof.
  intros m m' W PC MU WM HW.
  assert (D : forall A n, 0 <= n ->
             ((0xa5870 <= A /\ A + n <= 0xa58b8) \/ (0xa7738 <= A /\ A + n <= 0xa7748) \/ (0xac210 <= A /\ A + n <= 0xac214)
              \/ (0xae25c <= A /\ A + n <= 0xae25d) \/ (0xae9f8 <= A /\ A + n <= 0xaea00) \/ (0xaf6d8 <= A /\ A + n <= 0xaf6da)
              \/ (0x1405a0 <= A /\ A + n <= 0x1405a8)) -> disjoint_from W A n).
  { intros A n Hn HA. clear MU. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH]. }
  unfold mdtor_rt in *.
  (nd_pre PC 9%nat; intros P1 P2 P3 P4 P5 P6 P7 P8 P9; nd_post).
  repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply D; cbn; lia]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint descs_at (m : mem) (d : Z) (gs : list gdT) : Prop :=
  match gs with
  | [] => True
  | g :: gs' => rw_cells asegs m d (gd_cells g) /\ descs_at m (d + 64) gs'
  end.

#[using="Type"] Lemma gd_cells_size : forall g, cells_size (gd_cells g) = 64%nat.
Proof. intros ((((beg, sz), swr), nm), md). reflexivity. Qed.

#[using="Type"] Lemma descs_at_of_flat : forall gs m d, rw_cells asegs m d (flat_map gd_cells gs) -> descs_at m d gs.
Proof.
  induction gs as [|g gs IH]; intros m d H; cbn [descs_at flat_map]; [exact I|].
  cbn [flat_map] in H. apply (proj1 (rw_cells_app asegs m d (gd_cells g) (flat_map gd_cells gs))) in H as [H1 H2].
  rewrite gd_cells_size in H2. split; [exact H1| apply IH; exact H2].
Qed.

#[using="Type"] Lemma disjoint_from_sub : forall (W : list (Z * Z)) A n A' n', disjoint_from W A n -> A <= A' -> A' + n' <= A + n -> disjoint_from W A' n'.
Proof.
  induction W as [|[lo hi] W IH]; intros A n A' n' H H1 H2; cbn [disjoint_from] in *; [exact I|].
  destruct H as [Ha Hb]. split; [lia| eapply IH; eassumption].
Qed.

#[using="Type"] Lemma descs_at_transport : forall gs m m' W d, descs_at m d gs -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W d (64 * Z.of_nat (length gs)) -> descs_at m' d gs.
Proof.
  induction gs as [|g gs IH]; intros m m' W d H MU WM DJ; cbn [descs_at] in *; [exact I|].
  destruct H as [H1 H2]. cbn [length] in DJ. split.
  - eapply rw_cells_transport; [exact H1| exact MU| exact WM|]. rewrite gd_cells_size.
    change (Z.of_nat 64) with 64. eapply disjoint_from_sub; [exact DJ| lia| lia].
  - eapply IH; [exact H2| exact MU| exact WM|]. eapply disjoint_from_sub; [exact DJ| lia| lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma swr_byte : forall (m : mem) A v, (v = 32 \/ v = 64 \/ v = 96 \/ v = 128) ->
  rw_cells asegs m A [C8 (Z_to_bv 64 v)] -> rw_cells asegs m A [C1 (Z_to_bv 8 v)].
Proof.
  intros m A v [->|[->|[->| ->]]] H.
  all: eapply (rw_cells_hd m A _ [CB 7 (repeat (Z_to_bv 8 0) 7)]); recast H.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition poison_low_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (sb sl lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (sb, sb + sl)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].

Definition poison_low_spec__stmt : Prop := forall RNG (sb sl addr size : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (junk : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv asegs m ->
  mdtor_rt m ->
  a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 0 ->
  addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> 0x10000 <= addr -> addr + size <= 0x604000 -> shn size < 0x10000 ->
  sb = shd addr -> sl = shn size ->
  rw_cells asegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG sb sl ->
  evtF asegs RNG (poison_low_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sb sl lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x57604) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 0).
Variable sb : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 1).
Variable sl : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 2).
Variable addr : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 3).
Variable size : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 39).
Variable junk : ltac2:(SecDietF.SzSecF.ty 'poison_low_spec__stmt 40).
#[using="Type"] Lemma poison_low_spec__body : ltac:(let T := type of (fun (h : poison_low_spec__stmt) => h RNG sb sl addr size ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo junk) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (sb, (sl, (addr, (size, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (lo, junk))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST KH LO MI RT -> -> -> AL SL SZ LOW HIE SMALL -> -> DST RIMG RSTK RSH.
  atop_facts. pose proof RT as RT'. (nd_pre RT' 9%nat; intros PGC GOT GOT80 REAL SHB INI CANP THR RGL; nd_post).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (shd addr, shd addr + shn size)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd addr /\ shd addr + shn size <= 0x800cd000 /\ 0 < shn size).
  { unfold shd, shn, SHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  carve_frame 64%nat ST.
  do 8 hstep.                                          (* [comment removed for export] *)
  hstep. if_true.                                      (* [comment removed for export] *)
  zstep. hstep. if_cases K1; zify_cond K1.              (* [comment removed for export] *)
  { exfalso. apply K1. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
  do 3 hstep.                                          (* [comment removed for export] *)
  do 4 zstep.                                          (* [comment removed for export] *)
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  hstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. hstep. if_cases K8; zify_cond K8.
  { exfalso. apply K8. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact SL. }
  do 2 zstep.                                          (* [comment removed for export] *)
  hstep. if_cases K9; zify_cond K9. 2:{ exfalso. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 3 hstep.                                          (* [comment removed for export] *)
  hstep. if_cases K10; zify_cond K10; [exfalso; lia|]. (* [comment removed for export] *)
  do 5 zstep.                                          (* [comment removed for export] *)
  assert (E1 : (Z.shiftr (addr + size + -8) 3 + 1) mod 18446744073709551616 - Z.shiftr addr 3 = shn size).
  { unfold shn. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  rewrite E1. clear E1. change (2147450880 + Z.shiftr addr 3) with (shd addr).
  hstep. if_false.                                     (* [comment removed for export] *)
  do 3 hstep.                                          (* [comment removed for export] *)
  hstep. if_cases KT; zify_cond KT.                    (* [comment removed for export] *)
  2:{ exfalso. lia. }
  do 3 hstep. do 8 hstep.                              (* [comment removed for export] *)
  hstep.                                               (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply memset_spec; [ rewrite !unsigned_lit by lia; exact DST | exact MI | rewrite !unsigned_lit by lia; exact RSH ]. }
  intros ms' PO. unfold memset_post in PO. unfold poison_low_post. destruct_exs PO.
  (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MU2 WM2 MI2 DST2; nd_post).
  rewrite !unsigned_lit in MU2, DST2 by lia. change (0 mod 256) with 0 in DST2.
  do 16 eexists. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros xq Hxq. cbn in Hxq |- *. tauto. }
  split. { eapply wmono_trans; [exact WM| exact WM2]. }
  split. { exact MI2. }
  split. 2: exact DST2.
  pose proof (rw_cells_transport asegs _ _ _ _ _ FR MU2 WM2 ltac:(cbn [disjoint_from cells_size csize]; lia)) as FR'.
  pose proof (stk_transport_disjoint asegs _ _ _ _ _ ST MU2 WM2 ltac:(cbn [disjoint_from]; lia)) as ST'.
  eapply stk_release in FR'; [| exact ST' | lia]. cbn [cells_size csize Nat.add] in FR'.
  match type of FR' with stk _ _ _ ?hi => replace hi with (bv_unsigned sp) in FR' by lia end. exact FR'.
Qed.
End Zd1.
#[using="Type"] Lemma poison_low_spec : ltac:(let t := eval cbv delta [poison_low_spec__stmt] in poison_low_spec__stmt in exact t).
Proof. exact poison_low_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unreg_one_post (spv d sb sl : Z) (gp tp s5 s6 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 0x41fe4) (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x140528) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 2) (Z_to_bv 64 0x1b3be) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0xa7740) s8 (Z_to_bv 64 0xac1f8)
                  (Z_to_bv 64 0xae9f8) s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x41fe4) fc None m' (seg_rom asegs)
    /\ munch [(sb, sb + sl)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' sb [CB (Z.to_nat sl) (repeat (Z_to_bv 8 0) (Z.to_nat sl))].

Definition unreg_one_spec__stmt : Prop := forall RNG (sb sl : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (spv d beg swr : Z) (gsz gnm gmd gdy glc godr : word) (junk : list byte),
  mem_inv asegs m -> mdtor_rt m ->
  rw_cells asegs m d [C8 (Z_to_bv 64 beg); C8 gsz; C8 (Z_to_bv 64 swr); C8 gnm; C8 gmd; C8 gdy; C8 glc; C8 godr] ->
  rw_cells asegs m (d + 16) [C1 (Z_to_bv 8 swr)] ->
  beg mod 8 = 0 -> swr mod 8 = 0 -> 0 < swr < 256 -> 0x10000 <= beg -> beg + swr <= 0x604000 ->
  0x10000 <= d -> d + 64 <= 0x604000 -> 0 <= spv < 2^64 ->
  sb = shd beg -> sl = shn swr ->
  rw_cells asegs m sb [CB (Z.to_nat sl) junk] ->
  rng_aimg RNG -> rng RNG sb sl ->
  evtF asegs RNG (unreg_one_post spv d sb sl gp tp s5 s6 s8 s11 F fc m)
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x140528) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1b3be) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0xa7740) s8 (Z_to_bv 64 0xac1f8)
             (Z_to_bv 64 0xae9f8) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41ffc) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 0).
Variable sb : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 1).
Variable sl : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 2).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 17).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 18).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 19).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 20).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 21).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 22).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 23).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 24).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 25).
Variable F : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 26).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 27).
Variable m : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 28).
Variable spv : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 29).
Variable d : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 30).
Variable beg : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 31).
Variable swr : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 32).
Variable gsz : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 33).
Variable gnm : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 34).
Variable gmd : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 35).
Variable gdy : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 36).
Variable glc : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 37).
Variable godr : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 38).
Variable junk : ltac2:(SecDietF.SzSecF.ty 'unreg_one_spec__stmt 39).
#[using="Type"] Lemma unreg_one_spec__body : ltac:(let T := type of (fun (h : unreg_one_spec__stmt) => h RNG sb sl ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 s11 t3 t4 t5 t6 F fc m spv d beg swr gsz gnm gmd gdy glc godr junk) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (sb, (sl, (ra, (gp, (tp, (t0, (t1, (t2, (s0, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s5, (s6, (s8, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (spv, (d, (beg, (swr, (gsz, (gnm, (gmd, (gdy, (glc, (godr, junk)))))))))))))))))))))))))))))))))))))))) as _.
 intros MI RT D DB AL SL SWR LOW HIE DLO DHI SPV -> -> DST RIMG RSH.
  pose proof RT as RT'. (nd_pre RT' 9%nat; intros PGC GOT GOT80 REAL SHB INI CANP THR RGL; nd_post).
  pose proof (munch_refl [(shd beg, shd beg + shn swr)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (SHR : 0x7fffa000 <= shd beg /\ shd beg + shn swr <= 0x800cd000 /\ 0 < shn swr < 32).
  { unfold shd, shn, SHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  do 7 hstep.
  hstep. if_false.                                     (* [comment removed for export] *)
  hstep.                                               (* [comment removed for export] *)
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  hstep. if_true.                                      (* [comment removed for export] *)
  hstep. if_false.                                     (* [comment removed for export] *)
  (* [comment removed for export] *)
  do 2 hstep. do 4 zstep.
  match goal with |- context [Z.land ?x 2147450879] => let v := eval vm_compute in (Z.land x 2147450879) in change (Z.land x 2147450879) with v end.
  hstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. hstep. if_cases K3; zify_cond K3.
  { exfalso. apply K3. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact AL. }
  hstep. zstep. rewrite (unsigned_lit8 swr) by lia. hstep. if_cases K4; zify_cond K4.
  { exfalso. apply K4. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact SL. }
  (* [comment removed for export] *)
  do 6 hstep. hstep. if_false.
  (* [comment removed for export] *)
  do 3 hstep. do 5 zstep. hstep. do 3 zstep.
  assert (E1 : (2147450880 + Z.shiftr (beg + swr + -8) 3 + 1) mod 18446744073709551616 - (2147450880 + Z.shiftr beg 3) mod 18446744073709551616
               = shn swr).
  { unfold shn. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  rewrite E1. clear E1. change (2147450880 + Z.shiftr beg 3) with (shd beg).
  hstep. if_cases KT; zify_cond KT. 2:{ exfalso. lia. }  (* [comment removed for export] *)
  do 3 hstep.                                          (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply memset_spec; [ rewrite !unsigned_lit by lia; exact DST | exact MI | rewrite !unsigned_lit by lia; exact RSH ]. }
  intros ms' PO. unfold memset_post in PO. unfold unreg_one_post. destruct_exs PO.
  (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MU2 WM2 MI2 DST2; nd_post).
  rewrite !unsigned_lit in MU2, DST2 by lia. change (0 mod 256) with 0 in DST2.
  cbn [ret_pc reg_get].
  replace (ret_pc (Z_to_bv 64 0x41fe4)) with (Z_to_bv 64 0x41fe4 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  do 17 eexists. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU|]. exact MU2. }
  split. { eapply wmono_trans; [exact WM| exact WM2]. }
  split. { exact MI2. }
  exact DST2.
Qed.
End Zd2.
#[using="Type"] Lemma unreg_one_spec : ltac:(let t := eval cbv delta [unreg_one_spec__stmt] in unreg_one_spec__stmt in exact t).
Proof. exact unreg_one_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unreg_loop_post (spv d' n' : Z) (gp tp s5 s6 s8 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x140528) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 2) (Z_to_bv 64 0x1b3be) (Z_to_bv 64 d') s5 s6 (Z_to_bv 64 0xa7740) s8 (Z_to_bv 64 0xac1f8)
                  (Z_to_bv 64 0xae9f8) (Z_to_bv 64 n') t3 t4 t5 t6)
             F (Z_to_bv 64 0x41ffc) fc None m' (seg_rom asegs)
    /\ munch [(SHW_LO, SHW_LO + SHW_LEN)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'.

#[using="Type"] Lemma shadow_window : forall beg swr, beg mod 8 = 0 -> swr mod 8 = 0 -> 0 < swr -> 0x10000 <= beg -> beg + swr <= 0x604000 ->
  SHW_LO <= shd beg /\ shd beg + shn swr <= SHW_LO + SHW_LEN /\ 0 < shn swr.
Proof.
  intros beg swr AL SL SZ LOW HIE. unfold shd, shn, SHOFF, SHW_LO, SHW_LEN. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition gd_shw (m : mem) (g : gdT) : Prop := let '(beg, sz, swr, nm, md) := g in wr_at asegs m (shd beg) (shn swr).
#[using="Type"] Lemma gd_shw_transport : forall m m' gs, Forall (gd_shw m) gs -> wmono asegs m m' -> Forall (gd_shw m') gs.
Proof.
  intros m m' gs H WM. eapply Forall_impl; [| exact H]. intros ((((beg, sz), swr), nm), md) Hg. unfold gd_shw in *.
  eapply wr_at_transport; [exact Hg| exact WM].
Qed.

#[using="Type"] Lemma unreg_loop : forall RNG (gs : list gdT) (d n spv : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem),
  mem_inv asegs m -> mdtor_rt m -> descs_at m d gs -> Forall gd_ok gs ->
  Forall (gd_shw m) gs ->
  0x10000 <= d -> d + 64 * Z.of_nat (length gs) <= 0x604000 -> 0 <= spv < 2^64 ->
  Z.of_nat (length gs) < n < 2^32 ->
  rng_aimg RNG -> rng RNG SHW_LO SHW_LEN ->
  evtF asegs RNG (unreg_loop_post spv (d + 64 * Z.of_nat (length gs)) (n - Z.of_nat (length gs)) gp tp s5 s6 s8 F fc m)
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 (Z_to_bv 64 0x140528) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 2) (Z_to_bv 64 0x1b3be) (Z_to_bv 64 d) s5 s6 (Z_to_bv 64 0xa7740) s8 (Z_to_bv 64 0xac1f8)
             (Z_to_bv 64 0xae9f8) (Z_to_bv 64 n) t3 t4 t5 t6)
        F (Z_to_bv 64 0x41ffc) fc None m (seg_rom asegs)).
Proof.
  intros RNG gs. induction gs as [|g gs IH];
    intros d n spv ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s8 t3 t4 t5 t6 F fc m MI RT DA OK WR DLO DHI SPV HN RIMG RISH.
  - apply evtF_done. unfold unreg_loop_post. cbn [length]. replace (d + 64 * Z.of_nat 0) with d by lia. replace (n - Z.of_nat 0) with n by lia.
    do 18 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI].
  - destruct g as ((((beg, sz), swr), nm), md). cbn [descs_at] in DA. destruct DA as [D DA'].
    apply Forall_cons_iff in OK as [OKg OK']. (nd_pre OKg 4%nat; intros AL SWR BLO BHI; nd_post).
    apply Forall_cons_iff in WR as [WRg WR']. unfold gd_shw in WRg.
    cbn [length] in DHI, HN.
    assert (SWRf : swr mod 8 = 0 /\ 0 < swr < 256) by (clear -SWR; destruct SWR as [->|[->|[->| ->]]]; (split; [reflexivity| lia])).
    destruct SWRf as [SL SWRr].
    (pose proof (shadow_window beg swr AL SL ltac:(lia) BLO BHI) as ndP__; nd_pre ndP__ 3%nat; intros SH1 SH2 SH3; nd_post).
    (* [comment removed for export] *)
    pose proof D as D16. unfold gd_cells in D16. apply rw_cells_tl in D16. apply rw_cells_tl in D16. apply rw_cells_hd in D16.
    change (Z.of_nat (csize (C8 (Z_to_bv 64 beg)))) with 8 in D16. change (Z.of_nat (csize (C8 (Z_to_bv 64 sz)))) with 8 in D16.
    replace (d + 8 + 8) with (d + 16) in D16 by lia.
    apply swr_byte in D16; [| exact SWR].
    (* [comment removed for export] *)
    destruct (rw_cells_of_wr_at asegs m (shd beg) (shn swr)) as (junk & _ & DST).
    { exact WRg. }
    { apply no_image_asan. unfold SHW_LO in SH1. lia. }
    { lia. }
    eapply evtF_cut.
    { eapply (unreg_one_spec RNG (shd beg) (shn swr)) with (d := d) (beg := beg) (swr := swr);
        [ exact MI | exact RT | exact D | exact D16 | exact AL | exact SL | exact SWRr | exact BLO | exact BHI | exact DLO | lia | exact SPV
        | reflexivity | reflexivity | exact DST | exact RIMG | eapply rng_sub'; [exact RISH| lia] ]. }
    cbv beta. intros ms' PO. unfold unreg_one_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MU1 WM1 MI1 _; nd_post).
    lazymatch type of MU1 with munch _ _ ?mm => assert (D' : rw_cells asegs mm d (gd_cells (beg, sz, swr, nm, md))) end.
    { eapply rw_cells_transport; [exact D| exact MU1| exact WM1|]. rewrite gd_cells_size. cbn [disjoint_from]. unfold SHW_LO in SH1. lia. }
    unfold gd_cells in D'.
    clear D D16 DST MI.
    (* [comment removed for export] *)
    hstep.
    sf_old_zstep.          (* [comment removed for export] *)
    astep. hstep. hstep. hstep.
    if_cases K; zify_cond K; [exfalso; lia|]. clear K.
    eapply evtF_mono.
    { eapply (IH (d + 64) (n + -1) spv); [exact MI1 | | | exact OK' | | lia | lia | exact SPV | lia | exact RIMG | exact RISH].
      - eapply mdtor_rt_frame; [exact RT| exact MU1| exact WM1|]. apply Forall_cons; [| apply Forall_nil]. cbn. unfold SHW_LO in SH1. lia.
      - eapply descs_at_transport; [exact DA'| exact MU1| exact WM1|]. cbn [disjoint_from]. unfold SHW_LO in SH1. lia.
      - eapply gd_shw_transport; [exact WR'| exact WM1]. }
    cbv beta. intros ms' PO. unfold unreg_loop_post in PO |- *. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 3%nat; intros MU2 WM2 MI2; nd_post).
    cbn [length].
    replace (d + 64 * Z.of_nat (S (length gs))) with (d + 64 + 64 * Z.of_nat (length gs)) by lia.
    replace (n - Z.of_nat (S (length gs))) with (n + -1 - Z.of_nat (length gs)) by lia.
    do 18 eexists. split; [reflexivity|]. split; [| split; [eapply wmono_trans; eassumption| exact MI2]].
    eapply munch_trans; [| exact MU2]. eapply munch_weaken; [| exact MU1]. intros xq Hx. cbn [outside] in Hx |- *. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mdtor_pre (m : mem) : Prop :=
     mdtor_rt m
  /\ rw_cells asegs m 0xa6528 [C8 (Z_to_bv 64 0xaa190); C8 (Z_to_bv 64 0xab310)]     (* [comment removed for export] *)
  /\ rw_cells asegs m 0xab340 [C8 (Z_to_bv 64 1)]                                     (* [comment removed for export] *)
  /\ rw_cells asegs m 0xac2b0 [C8 (Z_to_bv 64 0)]                                     (* [comment removed for export] *)
  /\ descs_at m 0xaa190 GD69                                                          (* [comment removed for export] *)
  /\ rw_cells asegs m 0xab2d0 [C8 (Z_to_bv 64 0x5e1080); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 32); C8 (Z_to_bv 64 0x16fb6);
                                C8 (Z_to_bv 64 0x21200); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x5e10a0)]
                                                                                      (* [comment removed for export] *)
  /\ (exists b, rw_cells asegs m 0x5e10a0 [C1 b])                                     (* [comment removed for export] *)
  /\ Forall (gd_shw m) GD69 /\ wr_at asegs m (shd 0x5e1080) (shn 32)                   (* [comment removed for export] *)
  /\ wr_at asegs m (shd 0xaa190) (shn 4480).                                          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition MDTOR_KEEP : list (Z * Z) :=
  [(0xa5870, 0xa58b8); (0xa6528, 0xa6538); (0xa7738, 0xa7748); (0xaa190, 0xab310); (0xab340, 0xab348); (0xac210, 0xac214); (0xac2b0, 0xac2b8);
   (0xae25c, 0xae25d); (0xae9f8, 0xaea00); (0xaf6d8, 0xaf6da); (0x1405a0, 0x1405a8); (0x5e10a0, 0x5e10a1)].
(* [comment removed for export] *)
Definition MDTOR_W : list (Z * Z) := [(0xab340, 0xab348); (0xac2b0, 0xac2b8); (0x5e10a0, 0x5e10a1); (SHW_LO, SHW_LO + SHW_LEN)].

Definition mdtor_pre_frame__stmt : Prop := forall m m' W,
  mdtor_pre m -> munch W m m' -> wmono asegs m m' -> Forall (iv_clear MDTOR_KEEP) W -> mdtor_pre m'.
Section Zd3.   (* [comment removed for export] *)
Variable m : ltac2:(SecDietF.SzSecF.ty 'mdtor_pre_frame__stmt 0).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'mdtor_pre_frame__stmt 1).
Variable W : ltac2:(SecDietF.SzSecF.ty 'mdtor_pre_frame__stmt 2).
#[using="Type"] Lemma mdtor_pre_frame__body : ltac:(let T := type of (fun (h : mdtor_pre_frame__stmt) => h m m' W) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (m, (m', W))) as _.
  intros P MU WM HW.
  assert (K : forall k A n, In k MDTOR_KEEP -> fst k <= A -> A + n <= snd k -> disjoint_from W A n)
    by (intros k A n Hk H1 H2; eapply keep_disjoint; eassumption).
  (nd_pre P 10%nat; intros RT G1 G2 G3 DA D69 [b OD] SH SH69 SHT; nd_post).
  unfold mdtor_pre. split.
  { (nd_pre RT 9%nat; intros P1 P2 P3 P4 P5 P6 P7 P8 P9; nd_post). unfold mdtor_rt.
    repeat match goal with |- _ /\ _ => split end.
    - eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xa5870, 0xa58b8)); [keep_in| cbn; lia| cbn; lia]].
    - eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xa5870, 0xa58b8)); [keep_in| cbn; lia| cbn; lia]].
    - eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xa5870, 0xa58b8)); [keep_in| cbn; lia| cbn; lia]].
    - eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xa7738, 0xa7748)); [keep_in| cbn; lia| cbn; lia]].
    - eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xae9f8, 0xaea00)); [keep_in| cbn; lia| cbn; lia]].
    - eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xaf6d8, 0xaf6da)); [keep_in| cbn; lia| cbn; lia]].
    - eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xae25c, 0xae25d)); [keep_in| cbn; lia| cbn; lia]].
    - eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0x1405a0, 0x1405a8)); [keep_in| cbn; lia| cbn; lia]].
    - eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xac210, 0xac214)); [keep_in| cbn; lia| cbn; lia]]. }
  split. { eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xa6528, 0xa6538)); [keep_in| cbn; lia| cbn; lia]]. }
  split. { eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xab340, 0xab348)); [keep_in| cbn; lia| cbn; lia]]. }
  split. { eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xac2b0, 0xac2b8)); [keep_in| cbn; lia| cbn; lia]]. }
  split. { eapply descs_at_transport; [exact DA | exact MU | exact WM | apply (K (0xaa190, 0xab310)); [keep_in| cbn; lia| cbn; lia]]. }
  split. { eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0xaa190, 0xab310)); [keep_in| cbn; lia| cbn; lia]]. }
  split. { exists b. eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply (K (0x5e10a0, 0x5e10a1)); [keep_in| cbn; lia| cbn; lia]]. }
  split. { eapply gd_shw_transport; [exact SH| exact WM]. }
  split; (eapply wr_at_transport; [eassumption| exact WM]).
Qed.
End Zd3.
#[using="Type"] Lemma mdtor_pre_frame : ltac:(let t := eval cbv delta [mdtor_pre_frame__stmt] in mdtor_pre_frame__stmt in exact t).
Proof. exact mdtor_pre_frame__body. Qed.
End CANSEC1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

(* [comment removed for export] *)
Ltac hstep ::= zstep; fix_lit_store.
Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.
Ltac rt_split := unfold mdtor_rt; repeat match goal with |- _ /\ _ => split end; hyp_by_addr.
Ltac lit_nat := repeat match goal with H : rw_cells _ _ _ [CB (Z.to_nat (Zpos ?p)) _] |- _ =>
                  let v := eval vm_compute in (Z.to_nat (Zpos p)) in change (Z.to_nat (Zpos p)) with v in H; move H at top end.

(* [comment removed for export] *)
Ltac side RIMG RSTK :=
  lazymatch goal with
  | |- evtF _ _ _ _ => idtac
  | |- rng _ _ _ => first [ assumption | eapply rng_sub'; [exact RSTK | lia] ]
  | |- rng_aimg _ => exact RIMG
  | |- rw_cells _ _ (?a + ?b) _ => let v := eval vm_compute in (a + b) in change (a + b) with v; hyp_by_addr
  | |- rw_cells _ _ _ _ => hyp_by_addr
  | |- mdtor_rt _ => rt_split
  | |- mem_inv _ _ => hyp_by_addr
  | |- stk _ _ _ _ => hyp_by_addr
  | |- @eq _ _ _ => reflexivity
  | |- Z.lt (shn _) _ => vm_compute; reflexivity
  | |- _ => lia
  end.

Section CANSEC3. Context {rc : runConstT}.
Definition module_dtor_proof__stmt : Prop := module_dtor_stmt mdtor_pre MDTOR_W.
Section Zd4.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 0).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 1).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 2).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 3).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 4).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 5).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 6).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 7).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 8).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 9).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 17).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 18).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 19).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 20).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 21).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 22).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 23).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 24).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 25).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 26).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 27).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 28).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 29).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 30).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 31).
Variable F : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 32).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 33).
Variable m : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 34).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'module_dtor_proof__stmt 35).
#[using="Type"] Lemma module_dtor_proof__body : ltac:(let T := type of (fun (h : module_dtor_proof__stmt) => h RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, lo)))))))))))))))))))))))))))))))))))) as _.
  unfold module_dtor_stmt.  intros HPRE ST LO KH MI RSTK RIMG RISH.
  unfold MDTOR_DEPTH in LO. atop_facts.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof HPRE as P. unfold mdtor_pre in P.
  (nd_pre P 10%nat; intros RT GSS FLG MTX DA D69 [ob OD] SH SH69 SHT; nd_post).
  pose proof RT as RT'. (nd_pre RT' 9%nat; intros PGC GOT GOT80 REAL SHB INI CANP THR RGL; nd_post).
  pose proof (munch_refl ((bv_unsigned sp - 4096, bv_unsigned sp) :: MDTOR_W)%Z m) as MU. unfold MDTOR_W in MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (RSF : rng RNG (bv_unsigned sp + -272) 272) by (eapply rng_sub'; [exact RSTK | lia]). move RIMG at bottom.
  sort_lits.
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 9 hstep.
  (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 3 hstep. astep. hstep. hstep. astep. do 2 hstep. astep. do 4 hstep.
  (* [comment removed for export] *)
  carve_frame 176%nat ST.
  do 14 hstep.
  do 5 hstep.                                          (* [comment removed for export] *)
  replace (sx32 (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (vm_compute; reflexivity).
  astep.                                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  steps_to 0x41ee8%Z.
  amo_step. astep. amo_step. astep. astep.
  move MTX after RGL.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  hstep. hstep. astep.
  steps_to 0x41ffc%Z.
  (* [comment removed for export] *)
  pose proof GD69_ok as GOK.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    assert (DAc : descs_at mc 0xaa190 GD69)
      by (eapply descs_at_transport; [exact DA| exact MU| exact WM|]; change (Z.of_nat (length GD69)) with 69; cbn [disjoint_from]; unfold SHW_LO, SHW_LEN; lia);
    pose proof (gd_shw_transport _ _ _ SH WM) as SHc end.
  eapply evtF_cut.
  { eapply (unreg_loop RNG GD69 0xaa190 70 (bv_unsigned sp + -208));
      [ hyp_by_addr | rt_split | exact DAc | exact GOK | exact SHc | lia | change (Z.of_nat (length GD69)) with 69; lia | lia
      | change (Z.of_nat (length GD69)) with 69; lia | exact RIMG | exact RISH ]. }
  cbv beta. intros ms' PO. unfold unreg_loop_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 3%nat; intros MUc WMc MIc; nd_post).
  change (Z.of_nat (length GD69)) with 69 in *. change (0xaa190 + 64 * 69) with 0xab2d0. change (70 - 69) with 1.
  clear DAc SHc. unfold SHW_LO, SHW_LEN in MUc, MU. cbn [Z.add Pos.add Pos.succ Pos.add_carry] in MUc, MU.
  clear MI. rename MIc into MI.
  lazymatch type of MUc with munch _ ?m0 ?m1 => transport_after_call asegs m0 m1 MUc WMc; clear MUc WMc; try clear m0 end.
  (* [comment removed for export] *)
  (nd_pre (rw_cells_of_wr_at asegs _ (shd 0x5e1080) (shn 32) SH69 ltac:(apply no_image_asan; vm_compute; discriminate) ltac:(vm_compute; discriminate)) 3%nat; intros j69 _ DST69; nd_post).
  change (shd 0x5e1080) with 0x800b4210 in DST69. change (shn 32) with 4 in DST69.
  pose proof D69 as B69. apply rw_cells_tl in B69. apply rw_cells_tl in B69. apply rw_cells_hd in B69.
  change (0xab2d0 + Z.of_nat (csize (C8 (Z_to_bv 64 0x5e1080))) + Z.of_nat (csize (C8 (Z_to_bv 64 8)))) with 0xab2e0 in B69.
  apply swr_byte in B69; [| left; reflexivity].
  assert (RX : rng RNG 0x800b4210 4) by (apply (rng_sub' _ _ _ _ _ RISH); lia).
  call (unreg_one_spec RNG 0x800b4210 4). all: side RIMG RSTK. clear RX.
  lit_nat. hstep. hstep. astep.                        (* [comment removed for export] *)
  hstep. hstep. hstep. astep. hstep.
  (* [comment removed for export] *)
  do 6 hstep. hstep.
  (nd_pre (rw_cells_of_wr_at asegs _ (shd 0xaa190) (shn 4480) SHT ltac:(apply no_image_asan; vm_compute; discriminate) ltac:(vm_compute; discriminate)) 3%nat; intros jT _ DSTT; nd_post).
  change (shd 0xaa190) with 0x8000d432 in DSTT. change (shn 4480) with 560 in DSTT.
  assert (RX : rng RNG 0x8000d432 560) by (apply (rng_sub' _ _ _ _ _ RISH); lia).
  call_sp (poison_low_spec RNG 0x8000d432 560 0xaa190 4480). all: side RIMG RSTK. clear RX.
  lit_nat.
  (* [comment removed for export] *)
  steps_to 0x42258%Z.
  amo_step. astep. amo_step. astep. astep.
  astep.                                               (* [comment removed for export] *)
  steps_to 0x424b0%Z.
  (* [comment removed for export] *)
  match goal with H : rw_cells _ _ (bv_unsigned sp + -208) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -32)%Z end.
  hstep. hstep. hstep. hstep.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -32) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -16)%Z end.
  hstep. hstep. hstep.
  match goal with H : rw_cells _ _ (bv_unsigned sp + -16) _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp) end.
  hstep.
  unfold module_dtor_post. sys_finish.
Qed.
End Zd4.
#[using="Type"] Theorem module_dtor_proof : ltac:(let t := eval cbv delta [module_dtor_proof__stmt] in module_dtor_proof__stmt in exact t).
Proof. exact module_dtor_proof__body. Qed.
End CANSEC3.
End TwB.
