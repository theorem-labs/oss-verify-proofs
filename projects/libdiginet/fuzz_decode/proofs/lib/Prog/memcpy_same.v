(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/Prog/memcpy_same.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_decode; 11 image values moved to fuzz_decode's binaries by symbol and offset (provenance/evidence/k2/k2-values.tsv); module path OSSVerify.Proofs.libdiginet.fuzz_decode.lib. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Strw Require Import STRW_tac.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Prog Require Import memcpy_c memcpy_same_c.
(* [comment removed for export] *)
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib.Step.zstep ::= OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require WeqGuard.
Local Ltac OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib.WeqGuard.word_eq_guarded.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Dieta54.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require AndN.   (* [comment removed for export] *)
Local Ltac lia ::= OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope bv_scope.

Lemma ms_upd_bytes_self : forall (cs xs : list byte) k, firstn (length xs) (skipn k cs) = xs ->
  upd_bytes cs k xs = cs.
Proof.
  intros cs xs k E. unfold upd_bytes.
  rewrite (Nat.add_comm k (length xs)), <- skipn_skipn.
  remember (length xs) as j eqn:Hj. rewrite <- E. rewrite !firstn_skipn. reflexivity.
Qed.

Definition st_facts_same (S D n base : Z) (c k kw : nat) (P : Z) : Prop :=
  ((0 <= base)%Z /\ (c + k <= kw)%nat /\ P = base + Z.of_nat c /\ 0 <= P /\ P + Z.of_nat k <= n /\
   S = D /\ 0 <= D /\ D + n <= 2^64)%Z.

Lemma mc_store_ok_same : forall segs m1 S D n src kw base xsw c k P bs a,
  u8arr segs m1 D bs -> copied src bs (Z.to_nat P) -> length src = Z.to_nat n ->
  firstn kw (skipn (Z.to_nat base) src) = xsw ->
  st_facts_same S D n base c k kw P -> a = wa (D + P) -> store_ok segs m1 a k = true.
Proof.
  intros segs m1 S D n src kw base xsw c k P bs a DST [L _] LEN _ (_ & _ & _ & HP & Hk & _) Ha.
  eapply (u8arr_store_ok_n segs m1 D bs P k a DST); [lia | | exact Ha]. rewrite L, LEN. lia.
Qed.

Lemma mc_store_same : forall segs m0 m1 S D n src kw base xsw c k P bs xs a,
  bytes_at segs m1 S src -> u8arr segs m1 D bs -> copied src bs (Z.to_nat P) ->
  mem_inv segs m1 -> munch [(D, D + n)]%Z m0 m1 -> wmono segs m0 m1 ->
  length src = Z.to_nat n -> firstn kw (skipn (Z.to_nat base) src) = xsw ->
  st_facts_same S D n base c k kw P ->
  xs = firstn k (skipn c xsw) -> length xs = k -> a = wa (D + P) ->
  bytes_at segs (write_to_mem m1 a xs) S src /\
  u8arr segs (write_to_mem m1 a xs) D (upd_bytes bs (Z.to_nat P) xs) /\
  copied src (upd_bytes bs (Z.to_nat P) xs) (Z.to_nat (P + Z.of_nat k)) /\
  mem_inv segs (write_to_mem m1 a xs) /\ munch [(D, D + n)]%Z m0 (write_to_mem m1 a xs) /\
  wmono segs m0 (write_to_mem m1 a xs).
Proof.
  intros segs m0 m1 S D n src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW
         (Hb & Hc & HPb & HP & Hk & SAME & D0 & Dn) Hxs Hl Ha.
  pose proof (proj1 CP) as Lbs.
  assert (SOK : store_ok segs m1 a (length xs) = true).
  { rewrite Hl. apply (mc_store_ok_same segs m1 S D n src kw base xsw c k P bs a DST CP LEN HW); [unfold st_facts_same; lia | exact Ha]. }
  assert (Ew : firstn (length xs) (skipn (Z.to_nat P) src) = xs).
  { rewrite Hl, Hxs. eapply window_sub; eauto; lia. }
  subst a. split; [|split; [|split; [|split; [|split]]]].
  - subst D. pose proof (bytes_at_write_inside segs m1 S src P xs SRC HP ltac:(rewrite Hl, LEN; lia)) as H.
    rewrite (ms_upd_bytes_self src xs (Z.to_nat P) Ew) in H. exact H.
  - apply (u8arr_write_bytes segs m1 D bs P xs DST); [lia|]. rewrite Lbs, LEN. lia.
  - rewrite <- Hl. apply copied_updZ; [exact CP | lia | exact Ew | rewrite LEN; lia].
  - apply mem_inv_store; assumption.
  - apply munch_write; [exact MU | lia | lia |]. cbn [inside]. left. lia.
  - apply wmono_write. exact WM.
Qed.

Ltac sst_core HW c k bytes_tac SF :=
  lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
  let xs := eval cbv beta iota delta [firstn skipn] in (firstn k (skipn c xsw)) in
  let kz := eval vm_compute in (Z.of_nat k) in
  lazymatch goal with
  | SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
    MI : mem_inv ?segs ?m, MU : munch _ ?m0 ?m, WM : wmono ?segs ?m0 ?m, LEN : length src = Z.to_nat _
    |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs0) _) =>
     replace bs0 with xs by bytes_tac;
     let SRC' := fresh "SRC" in let DST' := fresh "DST" in let CP' := fresh "CP" in
     let MI' := fresh "MI" in let MU' := fresh "MU" in let WM' := fresh "WM" in
     destruct (mc_store_same segs m0 m S D _ src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW SF
                 ltac:(reflexivity) ltac:(reflexivity) ltac:(addr_tac))
       as (SRC' & DST' & CP' & MI' & MU' & WM');
     change (Z.of_nat k) with kz in CP';
     clear SRC DST CP MI MU WM SF;
     repeat match goal with
     | H : store_ok segs m _ _ = true |- _ => clear H
     | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
     end;
     let m' := fresh "m" in remember (write_to_mem m a xs) as m' eqn:Heqm; clear Heqm; try clear m;
     let bs' := fresh "bs" in remember (upd_bytes bs (Z.to_nat P) xs) as bs' eqn:Heqbs; clear Heqbs; try clear bs;
     rename SRC' into SRC; rename DST' into DST; rename CP' into CP;
     rename MI' into MI; rename MU' into MU; rename WM' into WM
  end end.

Ltac sst HW c k bytes_tac :=
  lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
  lazymatch goal with
  | SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
    MU : munch [(_, _ + ?n)%Z] _ ?m, LEN : length src = Z.to_nat _ |- _ =>
    let a := cur_mem_addr in
    let SF := fresh "SF" in let SOK := fresh "SOK" in
    assert (SF : st_facts_same S D n base c k kw P) by (unfold st_facts_same; lia);
    pose proof (mc_store_ok_same segs m S D n src kw base xsw c k P bs a DST CP LEN HW SF ltac:(addr_tac)) as SOK;
    zstep; [ sst_core HW c k bytes_tac SF | .. ]
  end end.
Ltac sst1 HW c := sst HW c 1%nat by_byte.
Ltac sst4 HW c := sst HW c 4%nat by_lw.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src : list byte).
  Notation S := (bv_unsigned a1).
  Notation D := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Hypothesis LEN : length src = Z.to_nat n.
  Hypothesis AB : (0 <= S /\ S + n <= 2^64 /\ 0 <= D /\ D + n <= 2^64 /\ 0 <= n < 2^64)%Z.
  Hypothesis SAME : S = D.

  Notation POST := (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m).
  (* [comment removed for export] *)
  Notation ST pc mm x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

  (* [comment removed for export] *)
  Definition INV (m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
    bytes_at rsegs m1 S src /\ u8arr rsegs m1 D bs /\ copied src bs (Z.to_nat P) /\
    mem_inv rsegs m1 /\ munch W m m1 /\ wmono rsegs m m1.

  Ltac open_inv H := destruct H as (SRC & DST & CP & MI & MU & WM).
  Ltac inv_tac :=
    lazymatch goal with
    | |- INV _ _ _ => split; [eassumption | split; [eassumption | split; [ | OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib.AndN.rsplit; eassumption ]]];
        lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
          first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
    end.

  (* [comment removed for export] *)
  Ltac fin :=
    lazymatch goal with
    | DST : u8arr _ ?m1 _ ?bs, CP : copied _ ?bs (Z.to_nat ?P) |- _ =>
        let E := fresh "E" in
        pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
        apply rw_cells_of_u8arr in DST; rewrite LEN in DST
    end;
    finish2.

  (* [comment removed for export] *)
  Tactic Notation "use" uconstr(L) :=
    eapply L; first [ inv_tac | idtac ]; try assumption; try (f_equal; lia); try lia;
    try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
    try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).

  Ltac zc := rewrite ?unsigned_lit in * by lia; Z.div_mod_to_equations; lia.

  (* [comment removed for export] *)
  Lemma ms_a8c : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 4 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0x1c060 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SAME.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_2 by lia.
    zstep. if_cases K2; zify_cond K2.
    - destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [exfalso; cbn in K2; lia|]; apply (proj1 (Z.nlt_ge _ _)) in Hl4.
      window P 2%nat HW.
      ld1 HW 0%nat. ld1 HW 1%nat. zstep. zstep.
      sst1 HW 0%nat. sst1 HW 1%nat.
      zstep. zstep. rewrite land_1.
      zstep. if_cases K1; zify_cond K1.
      + zstep. fin.
      + window (P + 2)%Z 1%nat HW1.
        ld1 HW1 0%nat. sst1 HW1 0%nat. zstep. fin.
    - destruct (Z.ltb_spec0 (bv_unsigned r mod 4) 2) as [Hl4|Hl4]; [|exfalso; cbn in K2; lia].
      zstep. rewrite land_1.
      zstep. if_cases K1; zify_cond K1.
      + window P 1%nat HW. ld1 HW 0%nat. sst1 HW 0%nat. zstep. fin.
      + zstep. fin.
  Qed.

  (* [comment removed for export] *)
  Lemma ms_734z : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z -> P = n ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0x1bd08 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SAME.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr HPn -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_4 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (exfalso; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    zstep. use (ms_a8c m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma ms_72cz : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 16 = n)%Z -> P = n ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0x1bd00 m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SAME.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr HPn -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_8 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 16) 8) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (exfalso; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    use (ms_734z m1 bs P).
  Qed.

  Lemma ms_71cz : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> P = n ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0x1bcf0 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SAME.
    intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HPn -> -> ->; open_inv I.
    zstep. zstep. if_cases K32; zify_cond K32; [exfalso; first [lia | zc] |].
    zstep. zstep. if_cases K16; zify_cond K16; [exfalso; first [lia | zc] |].
    use (ms_72cz m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma ms_848 : forall m1 bs (P : Z) (r : word) xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + bv_unsigned r mod 8 = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0x1be1c m1 x5 x6 x7 xa1 r xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SAME.
    intros m1 bs P r xa1 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr -> ->; open_inv I.
    pose proof (bv_unsigned_in_range 64 r) as Rr. unfold bv_modulus in Rr. cbn in Rr.
    zstep. rewrite land_bit_4 by lia.
    zstep. if_cases K; zify_cond K; destruct (Z.ltb_spec0 (bv_unsigned r mod 8) 4) as [Hl|Hl]; try (exfalso; cbn in K; lia); try (lazymatch type of Hl with not _ => apply (proj1 (Z.nlt_ge _ _)) in Hl end).
    - use (ms_a8c m1 bs P).
    - window P 4%nat HW. ld4 HW 0%nat q0. zstep. sst4 HW 0%nat. zstep. zstep.
      use (ms_a8c _ _ (P + 4)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma ms_828 : forall m1 bs (P r : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P)%Z -> (P + r = n)%Z -> (0 <= r < 16)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 r -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0x1bdfc m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SAME.
    intros m1 bs P r xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hr Rr -> -> ->; open_inv I.
    zstep. zstep. if_cases K8; zify_cond K8.
    - use (ms_848 m1 bs P (Z_to_bv 64 r)).
    - window P 8%nat HW. ld4 HW 0%nat q0. ld4 HW 4%nat q1. sst4 HW 0%nat. sst4 HW 4%nat. zstep. zstep.
      use (ms_848 _ _ (P + 8)%Z (Z_to_bv 64 r)).
  Qed.

  (* [comment removed for export] *)
  Lemma ms_7f8 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28,
    Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P)%Z -> (16 <= n - P)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0x1bdcc m1 x5 x6 x7 xa1 xa2 xa3 (Z_to_bv 64 15) x15 x16 x17 x28).
  Proof using AB LEN SAME.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x15 x16 x17 x28 HK I HP Hr -> -> ->; open_inv I.
    window P 16%nat HW.
    ld4 HW 0%nat q0. ld4 HW 4%nat q1. ld4 HW 8%nat q2. ld4 HW 12%nat q3.
    zstep. zstep.
    sst4 HW 0%nat. sst4 HW 4%nat. sst4 HW 8%nat. sst4 HW 12%nat.
    zstep. zstep. if_cases Kl; zify_cond Kl.
    - use (IH (Z.to_nat (n - (P + 16))) ltac:(lia) _ _ (P + 16)%Z).
    - use (ms_828 _ _ (P + 16)%Z (n - (P + 16))%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma ms_7ec : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P <= n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0x1bdc0 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SAME.
    intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP -> -> ->; open_inv I.
    zstep. zstep. if_cases K16; zify_cond K16.
    - use (ms_828 m1 bs P (n - P)%Z).
    - zstep. use (ms_7f8 (Z.to_nat (n - P)) m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma ms_714 : forall m1 bs (P : Z) xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28,
    INV m1 bs P -> (0 <= P <= n)%Z -> ((S + P) mod 4 = 0 \/ P = n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    evt rsegs POST (ST 0x1bce8 m1 x5 x6 x7 xa1 xa2 xa3 x14 x15 x16 x17 x28).
  Proof using AB LEN SAME.
    intros m1 bs P xa1 xa2 xa3 x5 x6 x7 x14 x15 x16 x17 x28 I HP Hal -> -> ->; open_inv I.
    zstep. rewrite land_3. zstep. if_cases Kal; zify_cond Kal.
    - use (ms_7ec m1 bs P).
    - destruct Hal as [Hal|HPn].
      + exfalso. rewrite SAME in Hal. first [lia | zc].
      + use (ms_71cz m1 bs P).
  Qed.

  (* [comment removed for export] *)
  Lemma ms_6e4 : forall (K : nat) m1 bs (P : Z) xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28,
    Z.to_nat (n - P) = K -> INV m1 bs P -> (0 <= P < n)%Z ->
    xa1 = Z_to_bv 64 (S + P) -> xa2 = Z_to_bv 64 (n - P) -> xa3 = Z_to_bv 64 (D + P) ->
    xa4 = Z_to_bv 64 (S + P + 1) ->
    evt rsegs POST (ST 0x1bcb8 m1 x5 x6 x7 xa1 xa2 xa3 xa4 (Z_to_bv 64 1) x16 x17 x28).
  Proof using AB LEN SAME.
    induction K as [K IH] using lt_wf_ind;
      intros m1 bs P xa1 xa2 xa3 xa4 x5 x6 x7 x16 x17 x28 HK I HP -> -> -> ->; open_inv I.
    window P 1%nat HW.
    ld1 HW 0%nat. zstep. zstep. zstep. rewrite land_3.
    sst1 HW 0%nat. zstep. zstep. zstep. if_cases Kal; zify_cond Kal.
    - assert (Hal : ((S + (P + 1)) mod 4 = 0 \/ P + 1 = n)%Z) by (left; first [lia | zc]).
      use (ms_714 _ _ (P + 1)%Z).
    - zstep. zstep. if_cases K1; zify_cond K1.
      + use (IH (Z.to_nat (n - (P + 1))) ltac:(lia) _ _ (P + 1)%Z).
      + assert (Hal : ((S + (P + 1)) mod 4 = 0 \/ P + 1 = n)%Z) by (right; first [lia | zc]).
        zstep. use (ms_714 _ _ (P + 1)%Z).
  Qed.

  (* [comment removed for export] *)
  Lemma memcpy_same_body :
    rw_cells rsegs m D [CB (Z.to_nat n) src] -> bytes_at rsegs m S src -> mem_inv rsegs m ->
    evt rsegs POST (ST 0x1bca0 m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3).
  Proof using AB LEN SAME.
    intros DST0 SRC MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST0) as DST.
    pose proof (copied_0 src src eq_refl) as CP.
    change 0%nat with (Z.to_nat 0) in CP. clear DST0.
    zstep. rewrite land_3. zstep. if_cases Ksal; zify_cond Ksal.
    - zstep. zstep. rewrite land_3. zstep. if_cases Kdal; zify_cond Kdal.
      + exfalso. rewrite SAME in Ksal. first [lia | zc].
      + use (ms_7ec m src 0%Z).
    - zstep. if_cases K0; zify_cond K0.
      + assert (Hal : ((S + 0) mod 4 = 0 \/ 0 = n)%Z) by (right; first [lia | zc]).
        zstep. use (ms_714 m src 0%Z).
      + zstep. zstep. zstep. use (ms_6e4 (Z.to_nat n) m src 0%Z).
  Qed.
End Proofs.

Theorem memcpy_same_holds : memcpy_same_contract.
Proof.
  unfold memcpy_same_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src
    E LEN DST MI.
  subst a1.
  pose proof (proj1 (u8arr_of_rw_cells _ _ _ _ _ DST)) as SRC.
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R.
  eapply memcpy_same_body; try eassumption; try reflexivity.
  cbn. lia.
Qed.
