(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  PropExec CatExec CatSim StoreOk ShapeAlg SpinAlg AsanAcctShape SymExec2 SymExec2Sound SymRun SymDrive SymDriveX HeapIface HeapIfaceA As0DrvKitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).

Definition sr_mainA : list expr :=
  [ELit 0; ELit 0x144bc4; spx (-48); ELit 0x10800; ELit 0x6a1890; EVar 11; EVar 12; EVar 13;
   spx 8; ELit 2; ELit 2; spx 8; spx 32; EVar 19; EVar 20; EVar 21;
   EVar 22; EVar 23; ELit 0xb0980; spx 32; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

Definition kn_mainA : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-8388608)) 8388608;
   KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1); KWord (SA (EVar 0) 16) 8 (EVar 2);
   KImg 0x10000 0x166000; KImg 0x69fe10 0x6a17c0;          (* [comment removed for export] *)
   KImg 0x168d48 0x168e38; KImg 0x168e38 0x168f20; KImg 0x168f20 0x16a100;   (* [comment removed for export] *)
   KWord (SA (ELit 0) 0x6c18d0) 8 (EVar 3);
   (* [comment removed for export] *)
   KWord (SA (ELit 0) 0x6a17c8) 8 (ELit 0x6a17c8); KWord (SA (ELit 0) 0x6a17e8) 4 (EVar 4); KRange (EVar 4) 1 4194303;
   KWord (SA (ELit 0) 0x6a1880) 8 (EVar 3); KWord (SA (ELit 0) 0x6a1860) 8 (ELit 0x6c1b58);
   KWord (SA (ELit 0) 0x6c1b28) 8 (EAlu ALU_ADD (EVar 1) (ELit (-160)));
   KImg 0x168c60 0x168d48; KImg 0x6c1b58 0x6c1b88; KImg 0x6c1c00 0x6c1c04 (* [comment removed for export] *);
   (* [comment removed for export] *)
   KWord (SA (ELit 0) 7084800) 4 (ELit 0); KWord (SA (ELit 0) 7084835) 1 (ELit 0); KWord (SA (ELit 0) 7084272) 8 (ELit 7084280); KWord (SA (ELit 0) 7084264) 4 (ELit 1);
   KWord (SA (ELit 0) 7084288) 8 (ELit 1332024); KWord (SA (ELit 0) 7084544) 8 (ELit 656352); KWord (SA (ELit 0) 7084260) 4 (ELit 0); KWord (SA (ELit 0) 7084280) 8 (ELit 0);
   KWord (SA (ELit 0) 7086232) 8 (ELit 0);
   (* [comment removed for export] *)
   KWord (SA (ELit 0) 7084256) 1 (ELit 0)].
(* [comment removed for export] *)
Definition XC9_CELLS : list (Z * nat * Z) :=
  [(7084800, 4%nat, 0); (7084835, 1%nat, 0); (7084272, 8%nat, 7084280); (7084264, 4%nat, 1); (7084288, 8%nat, 1332024); (7084544, 8%nat, 656352); (7084260, 4%nat, 0); (7084280, 8%nat, 0);
   (7086232, 8%nat, 0); (7084256, 1%nat, 0)].

(* [comment removed for export] *)
Definition auxv_listA (uidz rnd hwz : Z) : list Z := [3; 0x10040; 4; 56; 5; 11; 16; hwz; 6; 4096; 11; uidz; 12; uidz; 23; 0; 25; rnd; 0; 0].
Definition auxv_atA (sp p0 : word) (M0 : word -> option byte) : Prop :=
  exists uidz rnd hwz : Z,
    (forall j, (j < 20)%nat ->
       rdn ASEGS M0 (Z_to_bv 64 (bv_unsigned p0 - 160 + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (nth j (auxv_listA uidz rnd hwz) 0))))
    /\ 0 <= uidz < 2 ^ 32 /\ 0 <= hwz < 2 ^ 64 /\ bv_unsigned sp <= rnd /\ rnd + 16 <= 2 ^ 64
    /\ bv_unsigned sp + 160 <= bv_unsigned p0 <= 2 ^ 47 /\ bv_unsigned p0 mod 8 = 0.

Definition NX_MAIN : nat := 38.
Definition vals_mainA (sp p0 p1 can tid : word) (R : bvmap 5 word) : list word := [sp; p0; p1; can; tid; Z_to_bv 64 0] ++ junk_vals R.
Definition env_mainA (sp p0 p1 can tid : word) (R : bvmap 5 word) : env := Env (vals_ev (vals_mainA sp p0 p1 can tid R)) (blobs_ev []).

Definition all_regsA : list reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma nth_all_regsA : forall n, (n < 32)%nat -> nth n all_regsA 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.
Lemma regs_ok_by_indexA : forall E sr R,
  (forall i, (i < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat i)) = edenot E (nth i sr (ELit 0))) ->
  regs_ok E sr R.
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot]. reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite ridx_roundtrip in Hx. exact Hx.
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Section Pack.
  Variables (sp : word) (envc L0 : Z).
  Variable R : bvmap 5 word.
  Variable MV : word -> option byte.
  #[local] Notation usp := (bv_unsigned sp).
  Hypothesis Hsp : 0x7fff80000000 <= usp <= 2 ^ 47 /\ usp mod 16 = 0.
  Hypothesis Hb : 0 <= envc <= 256 /\ 0 <= L0 <= 131071.
  (* [comment removed for export] *)
  Hypothesis REGS : forall r v, In (r, v)
    [(1, 0x144bc4); (2, usp - 48); (3, 0x10800); (4, 0x6a1890); (8, usp + 8); (9, 2); (10, 2); (11, usp + 8);
     (12, usp + 32); (18, 0xb0980); (19, usp + 32); (20, 0); (21, 0); (22, 0); (23, 0); (24, 0); (25, 0); (26, 0); (27, 0)] ->
    getr R (Z_to_bv 5 r) = Z_to_bv 64 v.
  Hypothesis WORDS :
    rdn ASEGS MV (Z_to_bv 64 usp) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 2))
    /\ rdn ASEGS MV (Z_to_bv 64 (usp + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * envc + 200)))
    /\ rdn ASEGS MV (Z_to_bv 64 (usp + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * envc + L0 + 201))).
  Hypothesis WINDOW : forall d (m : nat), 0 <= d -> d + Z.of_nat m <= 8388608 -> store_ok ASEGS MV (Z_to_bv 64 (usp - 8388608 + d)) m = true.
  Variable can : word.
  Hypothesis GUARD : rdn ASEGS MV (Z_to_bv 64 0x6c18d0) 8 = Some (word_to_le_bytes 8 can).
  Hypothesis IMG : forall lo hi i, In (lo, hi) [(0x10000, 0x166590); (0x1665ac, 0x16a100); (0x68fe0a, 0x6a17c0); (0x6c1b58, 0x6c1b88); (0x6c1c00, 0x6c1c04)] -> lo <= i < hi -> MV (Z_to_bv 64 i) = None.
  (* [comment removed for export] *)
  Variable tid : word.
  Hypothesis TIDR : 1 <= bv_unsigned tid <= 4194303.
  Hypothesis LIBW :
    rdn ASEGS MV (Z_to_bv 64 0x6a17c8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6a17c8))
    /\ rdn ASEGS MV (Z_to_bv 64 0x6a17e8) 4 = Some (word_to_le_bytes 4 tid)
    /\ rdn ASEGS MV (Z_to_bv 64 0x6a1880) 8 = Some (word_to_le_bytes 8 can)
    /\ rdn ASEGS MV (Z_to_bv 64 0x6a1860) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6c1b58))
    /\ rdn ASEGS MV (Z_to_bv 64 0x6c1b28) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * envc + 40))).

  (* [comment removed for export] *)
  Hypothesis XCW : Forall (fun c : Z * nat * Z => rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (snd (fst c)) = Some (word_to_le_bytes (snd (fst c)) (Z_to_bv 64 (snd c)))) XC9_CELLS.

  Let p0 : word := Z_to_bv 64 (usp + 8 * envc + 200).
  Let p1 : word := Z_to_bv 64 (usp + 8 * envc + L0 + 201).
  Let ES : env := env_mainA sp p0 p1 can tid R.

  Lemma ev_junkA : forall i, (i < 32)%nat -> ev ES (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold ES, env_mainA, vals_mainA. cbn [ev]. unfold vals_ev.
    change (6 + i)%nat with (length [sp; p0; p1; can; tid; Z_to_bv 64 0] + i)%nat. rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma spx_valA : forall k, edenot ES (spx k) = Z_to_bv 64 (usp + k).
  Proof.
    intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev ES 0) with sp.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity.
  Qed.

  Theorem main_regs_okA : regs_ok ES sr_mainA R.
  Proof.
    apply regs_ok_by_indexA. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; cbn [nth sr_mainA Z.of_nat Pos.of_succ_nat Pos.succ].
    all: try solve [rewrite ?spx_valA; cbn [edenot]; apply REGS; cbn [In]; repeat (first [left; reflexivity | right])].
    all: try (match goal with |- getr R (Z_to_bv 5 ?z) = edenot ES (EVar _) =>
                let k := eval cbv in (Z.to_nat z) in exact (eq_sym (ev_junkA k ltac:(lia))) end).
    (* [comment removed for export] *) cbn [edenot]. reflexivity.
  Qed.

  Lemma adenot_flat : forall E a n, flat E a n -> adenot E a = Z_to_bv 64 (estart E a).
  Proof. intros E a n Hf. rewrite <- (flat_u E a n Hf). symmetry. apply Z_to_bv_bv_unsigned. Qed.

  Lemma estart_sp : forall off, estart ES (SA (EVar 0) off) = usp + off.
  Proof. intros off. unfold estart. cbn [a_base a_off edenot]. reflexivity. Qed.

  Theorem main_know_okA : know_ok ASEGS ES MV kn_mainA.
  Proof.
    destruct Hsp as (S1 & S2). destruct Hb as (B1 & B2). destruct WORDS as (W0 & W8 & W16). destruct LIBW as (L1 & L2 & L3 & L4 & L5).
    assert (FLIT : forall a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 63 -> flat ES (SA (ELit 0) a) n).
    { intros a n H1 H2 H3. unfold flat, estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia. lia. }
    assert (ALIT : forall a, 0 <= a < 2 ^ 63 -> adenot ES (SA (ELit 0) a) = Z_to_bv 64 a).
    { intros a Ha. rewrite (adenot_flat ES (SA (ELit 0) a) 0 ltac:(apply FLIT; lia)). unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia. reflexivity. }
    assert (FL : forall off n, -8388608 <= off -> 0 <= n -> off + n <= 4096 -> flat ES (SA (EVar 0) off) n).
    { intros off n H1 H2 H3. unfold flat. rewrite estart_sp. lia. }
    assert (XC : forall (i : nat) c, nth_error XC9_CELLS i = Some c ->
                   rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (snd (fst c)) = Some (word_to_le_bytes (snd (fst c)) (Z_to_bv 64 (snd c))))
      by (intros i c Hn; exact (proj1 (Forall_forall _ _) XCW c (nth_error_In _ _ Hn))).
    unfold kn_mainA, know_ok. repeat (apply Forall_cons); [ .. | apply Forall_nil]; cbn [kentry_ok].
    - split; [lia | exact S2].
    - cbn [edenot]. change (ev ES 0) with sp. lia.
    - split; [apply FL; lia|]. intros d m Hd Hm. rewrite estart_sp. replace (usp + -8388608 + d) with (usp - 8388608 + d) by ring. apply WINDOW; assumption.
    - split; [lia|]. split; [apply FL; lia|]. rewrite (adenot_flat ES (SA (EVar 0) 0) 8 ltac:(apply FL; lia)), estart_sp, Z.add_0_r. exact W0.
    - split; [lia|]. split; [apply FL; lia|]. rewrite (adenot_flat ES (SA (EVar 0) 8) 8 ltac:(apply FL; lia)), estart_sp. exact W8.
    - split; [lia|]. split; [apply FL; lia|]. rewrite (adenot_flat ES (SA (EVar 0) 16) 8 ltac:(apply FL; lia)), estart_sp. exact W16.
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x10000 0x166590); [left; reflexivity | lia].
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x68fe0a 0x6a17c0); [right; right; left; reflexivity | lia].
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x1665ac 0x16a100); [right; left; reflexivity | lia].
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x1665ac 0x16a100); [right; left; reflexivity | lia].
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x1665ac 0x16a100); [right; left; reflexivity | lia].
    - split; [lia|]. split; [unfold flat, estart; cbn [a_base a_off edenot]; rewrite (u_small 0) by lia; lia|].
      rewrite adenot_lit0. exact GUARD.
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact L1.
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact L2.
    - cbn [edenot]. change (ev ES 4) with tid. lia.
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact L3.
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact L4.
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia.
      replace (edenot ES (EAlu ALU_ADD (EVar 1) (ELit (-160)))) with (Z_to_bv 64 (usp + 8 * envc + 40)); [exact L5|].
      cbn [edenot]. change (ev ES 1) with p0. rewrite alu_add. unfold v_add, p0. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
      rewrite <- Z.add_mod by lia. f_equal. lia.
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x1665ac 0x16a100); [right; left; reflexivity | lia].
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x6c1b58 0x6c1b88); [right; right; right; left; reflexivity | lia].
    - split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x6c1c00 0x6c1c04); [do 4 right; left; reflexivity | lia].
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 0%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 1%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 2%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 3%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 4%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 5%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 6%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 7%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 8%nat _ eq_refl).
    - split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 9%nat _ eq_refl).
  Qed.
End Pack.
End FPX_1.
