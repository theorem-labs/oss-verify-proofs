(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk Image Mem PropExec.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem HufWalkKit HufWalkKit2 HufWalkKit3 KXTac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXGo KXPost KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import MState Cells Exec Step Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_y4_kit_reload RF_huf_x4body_kit RF_huf_kx_ez.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-overridden".

Notation Y4_FT0 := 0xfdb8 (only parsing).
Notation Y4_FA2 := 0x104a0 (only parsing).
Notation Y4_MUL := 0x10490 (only parsing).
Notation Y4_MV := 0x218a392cd3d5dbf (only parsing).
Notation Y4_IH := 0x15e04 (only parsing).
Notation Y4_IE := 0x16674 (only parsing).

Lemma y4k_mul_rd : forall m, mem_inv usegs m ->
  ov_read_bytes usegs m (Z_to_bv 64 Y4_MUL) 8 = Some (le8 (Z_to_bv 64 Y4_MV)).
Proof.
  intros m MI.
  assert (RC : ro_cells usegs m Y4_MUL [CB (length (le8 (Z_to_bv 64 Y4_MV))) (le8 (Z_to_bv 64 Y4_MV))])
    by (apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | cbn; lia]).
  exact (ro_cells_read_at usegs m _ _ 0 _ 8 _ RC eq_refl eq_refl eq_refl).
Qed.

Lemma y4k_ctz_tab : forall m, mem_inv usegs m -> ztab_fact usegs m Y4_FA2 64 1 [(0, 0, 63)].
Proof. intros m MI. apply ztab_fact_img; [exact MI | lia | vm_compute; reflexivity]. Qed.

Lemma y4k_ctz_rd : forall m i, mem_inv usegs m -> 0 <= i < 64 ->
  exists b, ov_read_bytes usegs m (Z_to_bv 64 (Y4_FA2 + i)) 1 = Some [b] /\ 0 <= bv_unsigned b <= 63.
Proof.
  intros m i MI I.
  destruct (y4k_ctz_tab m MI (Y4_FA2 + i) ltac:(lia) 0 63) as (b & R & B).
  - replace ((Y4_FA2 + i - Y4_FA2) mod 1) with 0 by (rewrite Z.mod_1_r; reflexivity). reflexivity.
  - exists b. rewrite ov_rdn. split; [exact R | exact B].
Qed.

Lemma y4k_modmod : forall a j k, 0 <= j <= k -> (a mod 2^k) mod 2^j = a mod 2^j.
Proof.
  intros a j k J.
  assert (P1 : 2^j <> 0) by (apply Z.pow_nonzero; lia).
  assert (E : 2^k = 2^(k - j) * 2^j) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite (Z.mod_eq a (2^k)) by (apply Z.pow_nonzero; lia).
  rewrite E.
  replace (a - 2^(k - j) * 2^j * (a / (2^(k - j) * 2^j)))
    with (a + (- (2^(k - j) * (a / (2^(k - j) * 2^j)))) * 2^j) by ring.
  apply Z.mod_add; exact P1.
Qed.

Lemma y4k_shl_keep : forall x s K, x mod 2^K <> 0 -> 0 <= K -> 0 <= s -> K + s <= 64 ->
  ((x * 2^s) mod 2^64) mod 2^(K + s) <> 0.
Proof.
  intros x s K NZ K0 S0 KS.
  rewrite y4k_modmod by lia.
  assert (PK : 0 < 2^K) by (apply Z.pow_pos_nonneg; lia).
  assert (PS : 0 < 2^s) by (apply Z.pow_pos_nonneg; lia).
  assert (EKS : 2^(K + s) = 2^K * 2^s) by (apply Z.pow_add_r; lia).
  pose proof (Z.div_mod x (2^K) ltac:(lia)) as DM.
  pose proof (Z.mod_pos_bound x (2^K) PK) as RB.
  remember (x / 2^K) as q eqn:Eq. remember (x mod 2^K) as r eqn:Er.
  assert (X : x * 2^s = r * 2^s + q * 2^(K + s)) by (rewrite EKS, DM; ring).
  rewrite X, Z.mod_add by lia.
  rewrite Z.mod_small by (rewrite EKS; split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_lt_mono_pos_r; lia]).
  intro E. apply Z.mul_eq_0 in E. lia.
Qed.

Lemma y4k_shl_word : forall (b : word) s K, bv_unsigned b mod 2^K <> 0 -> 0 <= K -> 0 <= s -> K + s <= 64 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned b) s)) mod 2^(K + s) <> 0.
Proof.
  intros b s K H K0 S0 KS. rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2 by lia.
  apply y4k_shl_keep; assumption.
Qed.

Lemma y4k_reload_keep : forall v r, 0 <= v -> 0 <= r <= 7 ->
  ((Z.lor v 1 * 2^r) mod 2^64) mod 2^9 <> 0.
Proof.
  intros v r V R E.
  assert (OD : Z.lor v 1 mod 2^1 <> 0).
  { rewrite <- Z.land_ones by lia. change (Z.ones 1) with 1.
    rewrite Z.land_lor_distr_l. change (Z.land 1 1) with 1.
    intro E1. apply Z.lor_eq_0_iff in E1. lia. }
  apply (y4k_shl_keep (Z.lor v 1) r 1 OD ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite <- (y4k_modmod ((Z.lor v 1 * 2^r) mod 2^64) (1 + r) 9) by lia.
  rewrite E. apply Z.mod_0_l. apply Z.pow_nonzero; lia.
Qed.

Lemma y4k_nz_of_mod : forall x K, 0 <= K -> x mod 2^K <> 0 -> x <> 0.
Proof. intros x K K0 H E. subst x. apply H. apply Z.mod_0_l. apply Z.pow_nonzero; lia. Qed.

Lemma y4k_shr_bound : forall x k, 0 <= x < 2^64 -> 0 <= k <= 64 -> 0 <= x / 2^k < 2^(64 - k).
Proof.
  intros x k X K. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] |].
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia |].
  rewrite <- Z.pow_add_r by lia. replace (k + (64 - k)) with 64 by lia. lia.
Qed.

Ltac y4k_reg r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end) end.

Definition y4k_is_uim (segs : list Segment) (a : Z) : bool :=
  match fetch_word segs (Z_to_bv 64 a) with Some w => Z.eqb (bv_unsigned w) 3221229683 | None => false end.

Definition y4k_is_chk (segs : list Segment) (pc : Z) : bool :=
  y4k_is_uim segs pc ||
  match fetch_word segs (Z_to_bv 64 pc) with
  | Some w => match decode_any w with
              | Some (Jal rd imm, _) => Z.eqb (bv_unsigned rd) 0 && y4k_is_uim segs (pc + bv_signed imm)
              | _ => false end
  | None => false end.

Lemma y4k_x2len : forall cells, 2^11 <= Z.of_nat (length cells) ->
  zlen (firstn (Z.to_nat (4 * 2^11)) (x2_bytes' cells)) = 4 * 2^11.
Proof.
  intros cells H. rewrite length_firstn, x2_bytes'_length. lia.
Qed.

Lemma y4k_cells_len : forall cells, x2_table_ok cells 11 -> 2^11 <= Z.of_nat (length cells).
Proof. intros cells (_ & H & _). unfold Zlength in H. exact H. Qed.

Ltac y4k_isck :=
  lazymatch goal with |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch eval vm_compute in (y4k_is_chk segs pc) with true => idtac end end.

Ltac y4k_addr rs imm :=
  let rz := eval vm_compute in (bv_unsigned rs) in let immz := eval vm_compute in (bv_signed imm) in
  let R := y4k_reg rz in lazymatch R with Z_to_bv 64 ?E => constr:(E + immz) end.

Ltac y4k_insn :=
  lazymatch goal with |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w => eval vm_compute in (decode_any w) end end.

Fixpoint y4k_reads_eqb (l1 l2 : list (saddr * nat * bool)) : bool :=
  match l1, l2 with
  | [], [] => true
  | (a, n, s) :: r1, (a', n', s') :: r2 => saddr_eqb a a' && Nat.eqb n n' && Bool.eqb s s' && y4k_reads_eqb r1 r2
  | _, _ => false
  end.

Definition y4k_kn (zks : list zk) (na : nat) (reads0 : list (saddr * nat * bool)) : list kentry :=
  let kn0 := map zk_ent zks in
  let kn1 := (kn0 ++ atom_ranges na) ++ (read_ranges na reads0 ++ []) in
  (kn0 ++ atom_ranges na) ++ ((tab_ranges kn1 (tabs_of zks) na reads0 ++ []) ++ (read_ranges na reads0 ++ [])).

Fixpoint y4k_fix (run : list kentry -> list (saddr * nat * bool)) (zks : list zk) (na : nat)
    (reads0 : list (saddr * nat * bool)) (k : nat) : list (saddr * nat * bool) :=
  let reads := run (y4k_kn zks na reads0) in
  if y4k_reads_eqb reads reads0 then reads0
  else match k with O => reads | S k' => y4k_fix run zks na reads k' end.

Ltac y4k_god DIRS :=
  lazymatch goal with
  | |- kx_pending ?segs ?Q ?F ?fc ?m ?rom ?pc ?stops ?fuel ?xl ?zv ?zs ?zks ?zrs =>
    let na := eval vm_compute in (length zv) in
    let sr := constr:(ELit 0 :: map (fun z => lnorm (zx z)) zs) in
    let kn0 := constr:(map zk_ent zks) in
    let reads0 := eval vm_compute in
      (y4k_fix (fun kn => kx_reads_of na (snd (fst (sym_exec segs fuel true stops (SCR DIRS [] []) (SS pc sr [] kn na) []))))
               zks na [] 64%nat) in
    let ifs := constr:(@nil kentry) in
    let kn1 := constr:((kn0 ++ atom_ranges na) ++ (read_ranges na reads0 ++ ifs)) in
    let tfs := eval vm_compute in (tab_ranges kn1 (tabs_of zks) na reads0) in
    let sfs := constr:(@nil kentry) in
    let kn := constr:((kn0 ++ atom_ranges na) ++ ((tfs ++ sfs) ++ (read_ranges na reads0 ++ ifs))) in
    let r := eval vm_compute in (sym_exec segs fuel true stops (SCR DIRS [] []) (SS pc sr [] kn na) []) in
    lazymatch r with (?ss', ?scs, ?scr') =>
      let reads := eval vm_compute in (kx_reads_of na scs) in
      let ws := constr:(map (Z_to_bv 64) zv) in
      let KXS := fresh "KXxs" in
      pose (KXS := kx_vals segs m ws reads);
      let xs := constr:(KXS) in
      let KXE := fresh "KXE" in
      pose (KXE := kx_env ws xs);
      let E := constr:(KXE) in
      let KXA := fresh "KXA" in
      assert (KXA : forall j, (j < length zv)%nat -> ev KXE j = Z_to_bv 64 (nth j zv 0)) by exact (kE_atom zv KXS);
      let rr := constr:(map zr_reg zrs) in
      let HK := fresh "HK" in let HRR := fresh "HRR" in let HK1 := fresh "HK1" in let HSH := fresh "HSH" in
      assert (HSH : Forall (shz_ok m E) (shz_of zks)) by (cbn [shz_of]; kx_forall);
      assert (HK1 : know_ok segs E m kn1);
      [ unfold know_ok; apply Forall_app; split; [apply Forall_app; split; [ | apply atom_ranges_ok] | apply Forall_app; split ];
        [ apply Forall_map_iff; kx_forall; x4k_know1 segs zv xs m
        | apply (read_ranges_ok segs m ws reads); [ vm_compute; reflexivity | | vm_compute; lia ];
          intros ? ? Hnth; rewrite Nat.sub_diag; exact Hnth
        | constructor ]
      | assert (HK : know_ok segs E m kn);
      [ let HKA := fresh "HKA" in let HKB := fresh "HKB" in
        pose proof (proj1 (Forall_app _ _ _) HK1) as [HKA HKB];
        unfold know_ok; apply Forall_app; split; [exact HKA|]; apply Forall_app; split; [| exact HKB];
        apply Forall_app; split;
        [ let TEQ := fresh "TEQ" in
          assert (TEQ : tab_ranges kn1 (tabs_of zks) na reads0 = tfs) by (vm_compute; reflexivity);
          rewrite <- TEQ; clear TEQ;
          apply (tab_ranges_ok segs m ws reads kn1 (tabs_of zks));
          [ vm_compute; reflexivity | exact HK1 | cbn [tabs_of]; kx_forall; kx_tab1 segs zv xs m
          | intros ? ? Hnth; rewrite Nat.sub_diag; exact Hnth | vm_compute; lia ]
        | constructor ]
      | clear HK1;
        assert (HRR : Forall (region_ok segs m E) rr);
        [ apply Forall_map_iff; kx_forall; kx_region1 segs zv xs m
        | let KXR := fresh "KXR" in
          assert (KXR : regs_ok E sr (mkRl xl)) by kx_regs_ok zv;
          unfold kx_pending;
          refine (kx_run_evt segs fuel stops (SCR DIRS [] []) pc sr kn na ss' scs scr' E (mkRl xl) F fc m rom Q
                    (rfull_mkRl xl) _ KXR HK _ _);
          [ vm_cast_no_check (@eq_refl (sym_state * list sidecond * scripts) r)
          | apply (kx_scs_bulk2 segs m ws reads kn rr (shz_of zks) scs); [ vm_compute; reflexivity | exact HK | exact HRR | exact HSH | ];
            let rest := eval vm_compute in (List.filter (fun s => negb (sc_auto2 na reads kn rr (shz_of zks) s)) scs) in
            let REQ := fresh "REQ" in
            assert (REQ : List.filter (fun s => negb (sc_auto2 na reads kn rr (shz_of zks) s)) scs = rest) by (vm_compute; reflexivity);
            change (length ws) with na; rewrite REQ; clear REQ; change (scs_denot segs m E rest); unfold scs_denot; kx_forall;
            kx_sc_rest segs m ws reads na
          | clear HRR HSH; intros KXLF; cbn [s_log s_regs s_pc] in KXLF |- * ] ] ] ]
    end
  end.

Lemma y4k_tz_sll_e : forall E a s M S,
  (exists K, 0 <= K <= M /\ bv_unsigned (edenot E a) mod 2^K <> 0) ->
  0 <= S -> bv_unsigned (edenot E s) mod 64 <= S -> M + S <= 64 ->
  exists K, 0 <= K <= M + S /\ bv_unsigned (edenot E (EAlu ALU_SLL a s)) mod 2^K <> 0.
Proof.
  intros E a s M S (K & HK & HN) S0 HS HM.
  pose proof (Z.mod_pos_bound (bv_unsigned (edenot E s)) 64 ltac:(lia)) as MB.
  exists (K + bv_unsigned (edenot E s) mod 64). split; [lia|].
  cbn [edenot]. rewrite alu_sll. unfold v_sll.
  apply y4k_shl_word; [exact HN | lia | lia | lia].
Qed.

Lemma y4k_tz_nz : forall (w : word) M, (exists K, 0 <= K <= M /\ bv_unsigned w mod 2^K <> 0) -> bv_unsigned w <> 0.
Proof. intros w M (K & HK & HN) E. apply HN. rewrite E. apply Z.mod_0_l. apply Z.pow_nonzero; lia. Qed.

Lemma y4k_beq_nz : forall (x : word), bv_unsigned x <> 0 -> branch_taken BC_EQ x (Z_to_bv 64 0) = false.
Proof. intros x H. cbn [branch_taken]. rewrite bv_eqb_Z, unsigned_lit_wrap. apply Z.eqb_neq. rewrite Z.mod_0_l by lia. exact H. Qed.

Lemma y4k_sh_add256 : forall E j k S, 0 <= bv_unsigned (ev E j) <= S -> S < 64 ->
  bv_unsigned (edenot E (EAlu ALU_ADD (EVar j) (EMd M_MUL (ELit 256) (EVar k)))) mod 64 <= S.
Proof.
  intros E j k S HJ HS. cbn [edenot alu64 alu mul_div].
  rewrite bv_add_unsigned, bv_mul_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64).
  rewrite unsigned_lit_wrap. change (256 mod 2^64) with 256.
  assert (MM : forall z, (z mod 2^64) mod 64 = z mod 64).
  { intro z. pose proof (y4k_modmod z 6 64 ltac:(lia)) as X. change (2^6) with 64 in X. exact X. }
  rewrite MM, Z.add_mod by lia. rewrite MM.
  replace (256 * bv_unsigned (ev E k)) with ((4 * bv_unsigned (ev E k)) * 64) by ring.
  rewrite Z.mod_mul by lia. rewrite Z.add_0_r, Z.mod_mod by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma y4k_xor_ne : forall E x y, bv_unsigned (edenot E x) <> bv_unsigned (edenot E y) ->
  branch_taken BC_EQ (edenot E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR x y) (ELit 1)))) (edenot E (ELit 0)) = false.
Proof.
  intros E x y H. cbn [edenot branch_taken alu64 alu].
  assert (XN : bv_unsigned (bv_xor (edenot E x) (edenot E y)) <> 0)
    by (rewrite bv_xor_unsigned; intro XE; apply H; apply Z.lxor_eq; exact XE).
  pose proof (bv_unsigned_in_range _ (bv_xor (edenot E x) (edenot E y))) as RX.
  rewrite bv_ltu_Z, unsigned_lit_wrap. change (1 mod 2^64) with 1.
  destruct (Z.ltb_spec (bv_unsigned (bv_xor (edenot E x) (edenot E y))) 1) as [L|L]; [lia|].
  vm_compute. reflexivity.
Qed.

Ltac y4k_cnt X := lazymatch X with EAlu ALU_SLL ?a _ => let c := y4k_cnt a in constr:((c + 1)%Z) | _ => constr:(0%Z) end.

Ltac y4k_shamt :=
  lazymatch goal with
  | |- bv_unsigned (edenot ?E (EVar ?j)) mod 64 <= _ =>
      let R := fresh "R" in kx_range (EVar j) R; cbn [edenot]; rewrite Z.mod_small by lia; lia
  | |- bv_unsigned (edenot ?E (EAlu ALU_ADD (EVar ?j) (EMd M_MUL (ELit 256) (EVar ?k)))) mod 64 <= _ =>
      let R := fresh "R" in kx_range (EVar j) R; apply y4k_sh_add256; lia
  end.

Ltac y4k_tz :=
  lazymatch goal with
  | |- exists K, 0 <= K <= ?M /\ bv_unsigned (edenot ?E (EAlu ALU_SLL ?a ?s)) mod 2^K <> 0 =>
      let M' := eval vm_compute in (M - 11) in
      apply (y4k_tz_sll_e E a s M' 11); [ y4k_tz | lia | y4k_shamt | lia ]
  | |- exists K, 0 <= K <= ?M /\ bv_unsigned (edenot ?E (EVar ?j)) mod 2^K <> 0 =>
      exists 9; split; [lia|];
      lazymatch goal with KXA : forall j, (j < length ?zv)%nat -> ev E j = _ |- _ =>
        cbn [edenot]; rewrite (KXA j) by (cbn [length]; lia); cbn [nth];
        rewrite ?Z_to_bv_bv_unsigned; change (2^9) with 512; assumption end
  end.

Ltac y4k_side :=
  lazymatch goal with
  | |- branch_taken BC_EQ (edenot ?E (EAlu ALU_XOR (ELit 1) (EAlu ALU_SLTU (EAlu ALU_XOR ?x ?y) (ELit 1)))) (edenot ?E (ELit 0)) = false =>
      apply y4k_xor_ne; let R1 := fresh "R" in let R2 := fresh "R" in kx_range x R1; kx_range y R2; lia
  | |- branch_taken BC_EQ (edenot ?E ?X) (edenot ?E (ELit 0)) = false =>
      apply y4k_beq_nz;
      let c := y4k_cnt X in let M := eval vm_compute in (9 + 11 * c) in
      apply (y4k_tz_nz _ M); y4k_tz
  end.

Lemma y4k_evt_R : forall segs Q R R' F pc fc (mm rom : word -> option byte),
  evt segs Q (MS R' F pc fc None mm rom) -> R' = R -> evt segs Q (MS R F pc fc None mm rom).
Proof. intros segs Q R R' F pc fc mm rom H E. subst. exact H. Qed.

Lemma y4k_mod2_land : forall z, z mod 2 = Z.land z 1.
Proof.
  intro z. pose proof (Z.land_ones z 1 ltac:(lia)) as Y. change (Z.ones 1) with 1 in Y. change (2^1) with 2 in Y.
  rewrite Y. reflexivity.
Qed.

Lemma y4k_mod64_2 : forall z, (z mod 2^64) mod 2 = z mod 2.
Proof. intro z. pose proof (y4k_modmod z 1 64 ltac:(lia)) as X. change (2^1) with 2 in X. exact X. Qed.

Lemma y4k_odd_add1 : forall E a, bv_unsigned (edenot E a) mod 2 = 0 ->
  bv_unsigned (edenot E (EAlu ALU_ADD a (ELit 1))) mod 2 = 1.
Proof.
  intros E a H. cbn [edenot alu64 alu]. rewrite bv_add_unsigned, unsigned_lit_wrap. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). change (1 mod 2^64) with 1.
  rewrite y4k_mod64_2, Z.add_mod, H by lia. reflexivity.
Qed.

Lemma y4k_even_add : forall E a b, bv_unsigned (edenot E a) mod 2 = 0 -> bv_unsigned (edenot E b) mod 2 = 0 ->
  bv_unsigned (edenot E (EAlu ALU_ADD a b)) mod 2 = 0.
Proof.
  intros E a b HA HB. cbn [edenot alu64 alu]. rewrite bv_add_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). rewrite y4k_mod64_2, Z.add_mod, HA, HB by lia. reflexivity.
Qed.

Lemma y4k_even_mul : forall E c b, c mod 2 = 0 -> 0 <= c < 2^64 ->
  bv_unsigned (edenot E (EMd M_MUL (ELit c) b)) mod 2 = 0.
Proof.
  intros E c b HC RC. cbn [edenot mul_div]. rewrite bv_mul_unsigned, unsigned_lit_wrap. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64). rewrite (Z.mod_small c) by lia.
  rewrite y4k_mod64_2, Z.mul_mod, HC by lia. reflexivity.
Qed.

Lemma y4k_even_andm2 : forall E a, bv_unsigned (edenot E (EAlu ALU_AND a (ELit (-2)))) mod 2 = 0.
Proof.
  intros E a. cbn [edenot alu64 alu]. rewrite bv_and_unsigned, unsigned_lit_wrap, y4k_mod2_land.
  rewrite <- Z.land_assoc. change (Z.land (-2 mod 2^64) 1) with 0. apply Z.land_0_r.
Qed.

Lemma y4k_and7 : forall E a, bv_unsigned (edenot E (EAlu ALU_AND a (ELit 7))) mod 64 <= 7.
Proof.
  intros E a. cbn [edenot alu64 alu]. rewrite bv_and_unsigned, unsigned_lit_wrap. change (7 mod 2^64) with 7.
  pose proof (Z.land_ones (bv_unsigned (edenot E a)) 3 ltac:(lia)) as Y. change (Z.ones 3) with 7 in Y. rewrite Y.
  change (2^3) with 8. pose proof (Z.mod_pos_bound (bv_unsigned (edenot E a)) 8 ltac:(lia)) as B.
  rewrite (Z.mod_small (bv_unsigned (edenot E a) mod 8) 64) by lia. lia.
Qed.

Lemma y4k_odd_sll : forall E a s, bv_unsigned (edenot E a) mod 2 = 1 -> bv_unsigned (edenot E s) mod 64 <= 7 ->
  bv_unsigned (edenot E (EAlu ALU_SLL a s)) mod 512 <> 0.
Proof.
  intros E a s HA HS.
  destruct (y4k_tz_sll_e E a s 1 7) as (K & HK & HN).
  - exists 1. split; [lia|]. change (2^1) with 2. lia.
  - lia.
  - exact HS.
  - lia.
  - intro E0. apply HN. rewrite <- (y4k_modmod _ K 9) by lia. change (2^9) with 512. rewrite E0.
    apply Z.mod_0_l. apply Z.pow_nonzero; lia.
Qed.

Ltac y4k_even :=
  lazymatch goal with
  | |- bv_unsigned (edenot ?E (EAlu ALU_ADD ?a ?b)) mod 2 = 0 => apply y4k_even_add; y4k_even
  | |- bv_unsigned (edenot ?E (EMd M_MUL (ELit ?c) ?b)) mod 2 = 0 => apply y4k_even_mul; [reflexivity | lia]
  | |- bv_unsigned (edenot ?E (EAlu ALU_AND ?a (ELit (-2)))) mod 2 = 0 => apply y4k_even_andm2
  end.

Ltac y4k_newbits :=
  lazymatch goal with |- bv_unsigned (edenot ?E (EAlu ALU_SLL ?a ?s)) mod 512 <> 0 =>
    apply y4k_odd_sll; [ apply y4k_odd_add1; y4k_even | apply y4k_and7 ] end.

Ltac y4k_ranges :=
  lazymatch goal with XS := kx_vals _ _ ?ws ?reads |- _ =>
    let na := eval vm_compute in (length ws) in
    let nr := eval vm_compute in (length reads) in
    let rec go j k := lazymatch k with
                      | O => idtac
                      | S ?k' => (try (let R := fresh "RR" in kx_range (EVar j) R)); go (S j) k'
                      end in
    go na nr
  end.

Ltac y4k_assoc X :=
  repeat match goal with |- context [X + (?o + ?D)] => rewrite (Z.add_assoc X o D) end.

Lemma y4k_c8_eq : forall segs m A x y, rw_cells segs m A [C8 (Z_to_bv 64 x)] -> x = y ->
  rw_cells segs m A [C8 (Z_to_bv 64 y)].
Proof. intros segs m A x y H E. subst. exact H. Qed.

Ltac y4k_cell1 :=
  lazymatch goal with
  | |- rw_cells ?segs ?m ?A [C8 (Z_to_bv 64 ?y)] =>
      first [ lazymatch goal with H : rw_cells segs m A [C8 (Z_to_bv 64 y)] |- _ => exact H end
            | lazymatch goal with H : rw_cells segs m A [C8 (Z_to_bv 64 ?x)] |- _ =>
                apply (y4k_c8_eq segs m A x y H); rewrite ?kx_mul_m1; lia end ]
  | |- rw_cells ?segs ?m ?A [?c] =>
      lazymatch goal with H : rw_cells segs m A [c] |- _ => exact H end
  end.

Ltac y4k_merge :=
  repeat (lazymatch goal with |- rw_cells ?segs ?m ?A (?c :: ?c' :: ?cs) =>
            apply (proj2 (kx_rwc_cons segs m A c (c' :: cs))); split; [y4k_cell1|]; cbn [csize];
            lazymatch goal with
            | |- rw_cells _ _ (?a + ?b + Z.of_nat ?k) _ =>
                tryif is_Zlit b then
                  (let v := eval vm_compute in (b + Z.of_nat k) in replace (a + b + Z.of_nat k) with (a + v) by lia)
                else (let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v)
            | |- rw_cells _ _ (?a + Z.of_nat ?k) _ =>
                let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v
            end end);
  y4k_cell1.

Lemma y4k_elenZ_kE : forall zv xs e, 0 <= ez zv (kE zv xs) e < 2^64 -> elenZ (kE zv xs) e = ez zv (kE zv xs) e.
Proof.
  intros zv xs e H. unfold elenZ.
  rewrite (ez_ok zv (kE zv xs) (kE_atoms zv xs) e), Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). apply Z.mod_small. exact H.
Qed.

Ltac y4k_munch_wins H WINS :=
  lazymatch goal with
  | KXLF : log_flat ?E ?log, HK : know_ok ?segs ?E ?m0' ?kn |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      lazymatch type of H with
      | munch ?W ?m0 m =>
          let wz0 := kx_wins_reify WINS zv in
          let wz := eval vm_compute in wz0 in
          let LI := fresh "LI" in
          assert (LI : log_inside E log (map (win_ivl E) wz))
            by exact (kx_log_in_ok segs E m0' kn wz log HK ltac:(vm_compute; reflexivity));
          apply (kx_munch_log E W m0 m log) in H; [ | exact KXLF | apply (log_inside_mono E log _ W LI) ];
          [ clear LI
          | clear LI; intros ? ?; cbn [map inside win_ivl fst snd];
            let na := eval vm_compute in (length zv) in
            change E with (kE zv xs);
            repeat match goal with
            | |- context [estart (kE zv xs) ?a] =>
                rewrite (estart_ez_kE zv xs a);
                [ | cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; lia ]
            end;
            repeat match goal with
            | |- context [elenZ (kE zv xs) ?e] =>
                rewrite (y4k_elenZ_kE zv xs e);
                [ | cbv [ez]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; lia ]
            end;
            cbv [ez a_base a_off]; change (length zv) with na; cbv [nth Nat.ltb Nat.leb]; lia ]
      end
    end
  end.

Lemma y4k_cell_store8 : forall segs E M kn m pre a v rest A w0,
  know_ok segs E M kn -> log_flat E (pre ++ SE a 8 v :: rest) -> rw_cells segs m A [C8 w0] ->
  estart E a = A -> kx_apart_b kn pre a (ELit 8) = true ->
  rw_cells segs (mem_denot E m (pre ++ SE a 8 v :: rest)) A [C8 (edenot E v)].
Proof.
  intros segs E M kn m pre a v rest A w0 HK LF RC EA AP.
  eapply kx_cell_store8; [exact LF | exact RC | exact EA |].
  pose proof (proj1 (log_flat_app E pre _ LF)) as LF1.
  pose proof (kx_apart_ok segs E M kn pre a (ELit 8) HK LF1 AP) as LA.
  replace (elenZ E (ELit 8)) with 8 in LA
    by (symmetry; first [rewrite elenZ_lit by lia; reflexivity | rewrite elenZ_lit; reflexivity]).
  rewrite EA in LA. exact LA.
Qed.

Ltac y4k_cell H :=
  lazymatch goal with
  | HLF : log_flat ?E ?log, HK : know_ok ?segs ?E ?m ?kn |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      let na := eval vm_compute in (length zv) in
      lazymatch type of H with
      | rw_cells _ m (?B + ?off) [C8 _] =>
          let rec go pre l :=
            lazymatch l with
            | SE {| a_base := ?ab; a_off := off |} 8%nat ?v :: ?rest =>
                let Hn := fresh "HC" in
                assert (Hn : rw_cells segs (mem_denot E m (pre ++ SE {| a_base := ab; a_off := off |} 8 v :: rest)) (B + off)
                                      [C8 (edenot E v)])
                  by (eapply (y4k_cell_store8 segs E m kn m pre _ v rest (B + off) _ HK);
                      [ change (pre ++ SE {| a_base := ab; a_off := off |} 8 v :: rest) with log; exact HLF
                      | exact H
                      | change E with (kE zv xs); kx_estart_z zv
                      | vm_compute; reflexivity ]);
                change (pre ++ SE {| a_base := ab; a_off := off |} 8 v :: rest) with log in Hn;
                kxz_cell_value Hn zv E xs v;
                clear H; rename Hn into H
            | ?e :: ?rest => let pre' := eval cbn [app] in (pre ++ [e]) in go pre' rest
            | [] => fail "y4k_cell: no 8-byte store at offset" off
            end in
          let l := eval hnf in log in
          go constr:(@nil sentry) l
      end
    end
  end.

Ltac y4k_cells :=
  repeat match goal with
  | HLF : log_flat ?E ?log, H : rw_cells _ ?m _ [C8 _] |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
      y4k_cell H
  end.

Lemma y4k_nb_of : forall u lo hi, lo <= u <= hi -> ((0 <=? lo) && (hi <=? 63))%bool = true ->
  0 <= u mod 2 ^ 64 / 2 ^ (3 mod 64) <= 7.
Proof.
  intros u lo hi R B. apply andb_prop in B. destruct B as [B1 B2].
  apply Z.leb_le in B1. apply Z.leb_le in B2.
  rewrite Z.mod_small by lia. change (2 ^ (3 mod 64)) with 8.
  split; [apply Z.div_pos; lia |].
  assert (u / 8 < 8) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Ltac y4k_nb :=
  lazymatch goal with |- 0 <= bv_unsigned (ev ?E ?j) mod 2 ^ 64 / 2 ^ (3 mod 64) <= 7 =>
    let R := fresh "NR" in kx_range (EVar j) R;
    lazymatch type of R with ?lo <= _ <= ?hi =>
      let u := fresh "u" in
      revert R; generalize (bv_unsigned (ev E j)) as u; intros u R;
      exact (y4k_nb_of u lo hi R eq_refl)
    end
  end.

Ltac y4k_buf OUT LB :=
  let b' := fresh "b'" in let U := fresh "U" in let L := fresh "L" in
  destruct OUT as (b' & U & L); exists b'; split; [exact U | rewrite L; first [exact LB | lia]].
