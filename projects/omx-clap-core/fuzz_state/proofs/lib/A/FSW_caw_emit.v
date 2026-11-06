(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACem.v, with its module paths and module names changed; 1540 of its 1601 lines of code are new or changed and 390 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_pj_string.v, with its module names changed; 1107 of its 1191 lines of code are new or changed and 1517 lines of the source are left out. *)
(* The EMIT LOOP of the inlined expected_body of check_as_written (fs.asan A_check_as_written 0x81590), machine code
   0x817c8 .. 0x81908, C source fuzz_state.c:97-101:

     for (i = 0; n != SIZE_MAX && i < m; i += 4) {
       out[n++] = six[i] << 2 | six[i+1] >> 4;
       if (i + 2 < m) out[n++] = (six[i+1] & 15) << 4 | six[i+2] >> 2;
       if (i + 3 < m) out[n++] = (six[i+2] & 3) << 6 | six[i+3]; }

   `caw_emit_loop` walks it from the loop head 0x817dc to the loop exit 0x8197c in continuation-passing form: the
   goal is an arbitrary `Q`, discharged by the caller's continuation at the exit.  The walk of the rest of the
   function (prologue, scan loop, calls, tail) is a Theorem Labs lane's; this file owns the emit loop and nothing else.

   HEADER: no Axiom, no Parameter, no Admitted, no admit, no Abort, no Hypothesis.  The lemma calls nothing, so it
   carries no callee contract; every premise is an explicit premise of the lemma, owned by its caller (a Theorem Labs lane).
   The Section carries only the three instance variables of the lane ({fx}, {rc}, {SK}), the allocator symbols B and
   the goal Q.

   RULE 24 (no function proved): there is no released ASan-image proof of any fuzz_state function, check_as_written
   included - second-agent check (internal path) (checker
   a Theorem Labs lane 2026-10-28 22:40-22:57Z; ossv proof index v5 built 2026-10-28T21:58:24Z, ossv/recipes@566eb6ffa5df):
   all 54 functions CONFIRM.  fs's RELEASED plain proof (proofs/omx-clap-core/fuzz_state/lib/Prog/
   check_as_written.v at c8557374ad2e) is a TEXT INPUT only: the control-flow template and the pure model
   (lib/Prog/WriterSpec.v six_bytes), never a proof term of this walk.

   METHOD (measured with the engine over the pinned fs.asan, image sha256
   64b53ff86172bb07f93f146e67b81a0354bca88e0a580e93fb1da01406fb76e0):
   - the ASan checks are walked with the TOKEN engine in U form (FSW_K.fsw_run_tok_AJU over YCbn): a shadow `lb`
     becomes a token atom and the following `bnez` is resolved by the engine's slow-block pattern, which asks
     `need x (k+1)`; the SH entry `mkSHE 48 (-4) (-2)` covers six[i] and six[i+1] (always read), and
     `mkSHE 50 0 3` the three out bytes, so those leave NO obligation; six[i+2] and six[i+3] are read only under
     `i+2 < m` / `i+3 < m` and come out as obligations, discharged there from the block's range_addressable.
   - `add a2, s2, s3` (want + n) and `add t0, a0, a1` (six + K) are not atoms: the state carries ALIAS facts
     (YP0e.aliased2 / alias_lin_lookup) mapping them to the atoms 50 / 48, and the regions are based on those.
   - the three loop branches (0x81844 `bgeu K-2, m`, 0x81898 `bgeu K-1, m`, 0x81904 `bltu K, m`) are made decidable
     by `f_conds` entries added at the head (YP06.st_ok_add_cond), one set per case of the remaining sextets, so
     each case is ONE engine run of an exact number of steps: 73 (loop again), 74 (|sx| = 4), 53 (|sx| = 3),
     34 (|sx| = 2).
   - at the head of the next iteration the atoms are re-keyed with YL09.st_ok_reabs (atoms >= 47 are the loop's;
     atoms < 47 are the caller's and are kept, which is what `env_agree 47` in the continuation says). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP05 YL01 YL02 YL07 YL09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AF0l AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSW_K FSW_caw_defs FSW_caw_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module WS := WriterSpec.

(* ---- pure bit facts: the three bytes the group writes ---- *)
Lemma cae_lor_disj : forall a b, Z.land a b = 0 -> Z.lor a b = a + b.
Proof. intros a b H. rewrite <- Z.lxor_lor by exact H. symmetry. apply Z.add_nocarry_lxor. exact H. Qed.
Lemma cae_land_hl : forall x y k, 0 <= k -> 0 <= x -> 0 <= y < 2 ^ k -> Z.land (x * 2 ^ k) y = 0.
Proof.
intros x y k Hk Hx Hy. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i k) as [Hlt|Hge].
- replace (Z.testbit (x * 2 ^ k) i) with false; [reflexivity|].
  symmetry. rewrite <- Z.shiftl_mul_pow2 by exact Hk. apply Z.shiftl_spec_low. exact Hlt.
- replace (Z.testbit y i) with false; [apply andb_false_r|].
  symmetry. apply Z.testbit_false; [exact Hi|].
  rewrite Z.div_small; [reflexivity|]. split; [lia|].
  apply (Z.lt_le_trans _ (2 ^ k)); [lia | apply Z.pow_le_mono_r; lia].
Qed.
Lemma cae_lor_hl : forall x y k, 0 <= k -> 0 <= x -> 0 <= y < 2 ^ k -> Z.lor (x * 2 ^ k) y = x * 2 ^ k + y.
Proof. intros x y k Hk Hx Hy. apply cae_lor_disj. apply cae_land_hl; assumption. Qed.
Lemma cae_lor_lh : forall x y k, 0 <= k -> 0 <= x -> 0 <= y < 2 ^ k -> Z.lor y (x * 2 ^ k) = x * 2 ^ k + y.
Proof. intros x y k Hk Hx Hy. rewrite Z.lor_comm. apply cae_lor_hl; assumption. Qed.

Lemma cae_zcanon_id : forall z, 0 <= z < 2 ^ 64 -> zcanon z = z.
Proof. intros z Hz. apply zcanon_id. unfold M64. lia. Qed.

Lemma cae_U_srl : forall E (a : sv) v e, U E a = v -> 0 <= v < 2 ^ 64 -> 0 <= e < 64 ->
  U E (SAlu ALU_SRL a (SLit e)) = v / 2 ^ e.
Proof.
intros E a v e Ha Hv He. rewrite U_SAlu, U_SLit, Ha. cbn [zalu_raw].
rewrite (cae_zcanon_id e) by lia.
replace (Z.land e 63) with e by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia;
  symmetry; apply Z.mod_small; cbn; lia).
rewrite Z.shiftr_div_pow2 by lia. apply cae_zcanon_id.
assert (0 < 2 ^ e) by (apply Z.pow_pos_nonneg; lia).
split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ v); [apply Z.div_le_upper_bound; nia | lia].
Qed.
Lemma cae_U_sll : forall E (a : sv) v e, U E a = v -> 0 <= v -> 0 <= e < 64 -> v * 2 ^ e < 2 ^ 64 ->
  U E (SAlu ALU_SLL a (SLit e)) = v * 2 ^ e.
Proof.
intros E a v e Ha Hv He Hb. rewrite U_SAlu, U_SLit, Ha. cbn [zalu_raw].
rewrite (cae_zcanon_id e) by lia.
replace (Z.land e 63) with e by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia;
  symmetry; apply Z.mod_small; cbn; lia).
rewrite Z.shiftl_mul_pow2 by lia. apply cae_zcanon_id. split; [apply Z.mul_nonneg_nonneg; [lia|];
  apply Z.pow_nonneg; lia | exact Hb].
Qed.
Lemma cae_U_or : forall E (a b : sv) x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y ->
  Z.lor x y < 2 ^ 64 -> U E (SAlu ALU_OR a b) = Z.lor x y.
Proof.
intros E a b x y Ha Hb Hx Hy Hlt. rewrite U_SAlu, Ha, Hb. cbn [zalu_raw].
apply cae_zcanon_id. split; [apply Z.lor_nonneg; lia | exact Hlt].
Qed.

(* byte 0 = six[i] * 4 + six[i+1] / 16 *)
Lemma cae_byte0 : forall E (p q : sv) u v, U E p = u -> U E q = v -> 0 <= u < 64 -> 0 <= v < 64 ->
  U E (SAlu ALU_OR (SAlu ALU_SRL q (SLit 4)) (SAlu ALU_SLL p (SLit 2))) = u * 4 + v / 16.
Proof.
intros E p q u v Hp Hq Hu Hv.
assert (Hd : 0 <= v / 16 < 4) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Hlor : Z.lor (v / 16) (u * 4) = u * 4 + v / 16).
{ change 4 with (2 ^ 2). apply cae_lor_lh; [lia | lia | change (2 ^ 2) with 4; lia]. }
assert (Hs1 : U E (SAlu ALU_SRL q (SLit 4)) = v / 16)
  by (rewrite (cae_U_srl E q v 4 Hq ltac:(lia) ltac:(lia)); reflexivity).
assert (Hs2 : U E (SAlu ALU_SLL p (SLit 2)) = u * 4)
  by (rewrite (cae_U_sll E p u 2 Hp ltac:(lia) ltac:(lia) ltac:(cbn; lia)); reflexivity).
rewrite (cae_U_or E _ _ _ _ Hs1 Hs2 ltac:(lia) ltac:(lia) ltac:(rewrite Hlor; lia)).
exact Hlor.
Qed.
(* byte 1 = six[i+1] * 16 + six[i+2] / 4   (its low byte is (six[i+1] mod 16) * 16 + six[i+2] / 4) *)
Lemma cae_byte1 : forall E (q r : sv) v w, U E q = v -> U E r = w -> 0 <= v < 64 -> 0 <= w < 64 ->
  U E (SAlu ALU_OR (SAlu ALU_SRL r (SLit 2)) (SAlu ALU_SLL q (SLit 4))) = v * 16 + w / 4.
Proof.
intros E q r v w Hq Hr Hv Hw.
assert (Hd : 0 <= w / 4 < 16) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Hlor : Z.lor (w / 4) (v * 16) = v * 16 + w / 4).
{ change 16 with (2 ^ 4). apply cae_lor_lh; [lia | lia | change (2 ^ 4) with 16; lia]. }
assert (Hs1 : U E (SAlu ALU_SRL r (SLit 2)) = w / 4)
  by (rewrite (cae_U_srl E r w 2 Hr ltac:(lia) ltac:(lia)); reflexivity).
assert (Hs2 : U E (SAlu ALU_SLL q (SLit 4)) = v * 16)
  by (rewrite (cae_U_sll E q v 4 Hq ltac:(lia) ltac:(lia) ltac:(cbn; lia)); reflexivity).
rewrite (cae_U_or E _ _ _ _ Hs1 Hs2 ltac:(lia) ltac:(lia) ltac:(rewrite Hlor; lia)).
exact Hlor.
Qed.
(* byte 2 = six[i+2] * 64 + six[i+3]       (its low byte is (six[i+2] mod 4) * 64 + six[i+3]) *)
Lemma cae_byte2 : forall E (r s : sv) w z, U E r = w -> U E s = z -> 0 <= w < 64 -> 0 <= z < 64 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL r (SLit 6)) s) = w * 64 + z.
Proof.
intros E r s w z Hr Hs Hw Hz.
assert (Hlor : Z.lor (w * 64) z = w * 64 + z).
{ change 64 with (2 ^ 6). apply cae_lor_hl; [lia | lia | change (2 ^ 6) with 64; lia]. }
assert (Hs2 : U E (SAlu ALU_SLL r (SLit 6)) = w * 64)
  by (rewrite (cae_U_sll E r w 6 Hr ltac:(lia) ltac:(lia) ltac:(cbn; lia)); reflexivity).
rewrite (cae_U_or E _ _ _ _ Hs2 Hs ltac:(lia) ltac:(lia) ltac:(rewrite Hlor; lia)).
exact Hlor.
Qed.

Lemma cae_bv8_mod : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof.
intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. exact H.
Qed.

(* the atoms of an extension, read back *)
Lemma cae_ext_lookup : forall (ws : list word) (E : env) (K j : nat),
  (j < length ws)%nat -> ew (extK E K ws) (K + j) = nth j ws (Z_to_bv 64 0).
Proof.
induction ws as [|w ws IH]; intros E K j Hj; cbn [length] in Hj; [lia|].
cbn [extK]. destruct j as [|j].
- rewrite Nat.add_0_r, (proj1 (env_agree_extK (ewset E K w) (S K) ws) K ltac:(lia)).
  cbn [nth]. apply ew_ewset_same.
- replace (K + S j)%nat with (S K + j)%nat by lia. cbn [nth]. apply IH. lia.
Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable Q : world tfibsegs -> config -> Prop.

(* ---- the canonical loop-head state at 0x817dc ----
   atoms: 2 sp, 31 ra (an atom, not the literal 0x815f8: FSW_caw_defs.v caw_regs1), 32 the shadow base, 33 six,
   34 want, 38 m, 47 K = i + 4, 48 six + K, 49 n, 50 want + n,
   51 six + 1 + K, 52-55 the four sextets of the group, 56-65 the dead scratch registers.
   The caller's atoms are all below 47 (ra's 31 among them); every atom from 47 up is the loop's. *)
Definition cae_regs : list sv :=
  [SLit 0; SOff 31 0; SOff 2 (-48); SOff 3 0; SOff 4 0;
   SOff 56 0; SOff 57 0; SOff 58 0;
   SOff 12 0; SOff 11 0;
   SOff 33 0; SOff 47 0; SOff 59 0; SOff 38 0; SOff 33 1;
   SLit (-1); SOff 65 0; SOff 60 0;
   SOff 34 0; SOff 49 0; SOff 32 0;
   SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 61 0; SOff 62 0; SOff 63 0; SOff 64 0].
Definition cae_chunks : list YP09.chunk :=
  [YP09.mkChunk (-5) (CVal 1 (SOff 52 0)); YP09.mkChunk (-4) (CVal 1 (SOff 53 0));
   YP09.mkChunk (-3) (CVal 1 (SOff 54 0)); YP09.mkChunk (-2) (CVal 1 (SOff 55 0))].
(* the k = min 4 |sx| sextets of the group the code really reads, through a7 = six + 1 + K at offsets -5 .. *)
Definition cae_six (k : nat) : YP09.region :=
  YP09.mkRegion (Some 51%nat) (-5) (-5 + Z.of_nat k) 0 0 (firstn k cae_chunks).
(* the bytes the group writes, based at want + n; the window is exactly what this group writes *)
Definition cae_out (k : nat) : YP09.region := YP09.mkRegion (Some 50%nat) 0 3 0 (Z.of_nat k - 1) [].
Definition cae_mem (k : nat) : smem := [cae_six k; cae_out k].
Definition cae_atoms : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
   (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (33%nat, mkAF 4096 CAW_CEIL 0);
   (34%nat, mkAF 4096 CAW_CEIL 0);
   (38%nat, mkAF 0 3145728 0);
   (47%nat, mkAF 4 3145732 0);
   (48%nat, mkAF 4096 (CAW_CEIL + 16) 0);
   (49%nat, mkAF 0 3145728 0);
   (50%nat, mkAF 4096 CAW_CEIL 0);
   (51%nat, mkAF 4096 (CAW_CEIL + 16) 0);
   (52%nat, mkAF 0 63 0); (53%nat, mkAF 0 63 0); (54%nat, mkAF 0 63 0); (55%nat, mkAF 0 63 0)].
Definition cae_alias : list (sv * sv) :=
  [(SAlu ALU_ADD (SOff 33 0) (SOff 47 0), SOff 48 0);
   (SAlu ALU_ADD (SOff 33 1) (SOff 47 0), SOff 51 0);
   (SAlu ALU_ADD (SOff 34 0) (SOff 49 0), SOff 50 0)].
Definition cae_facts (cs : list acond) : facts := mkFacts cae_atoms cs cae_alias.
Definition cae_ss (k : nat) (cs : list acond) : sstate :=
  mkSS 0x817dc cae_regs (cae_mem k) None (cae_facts cs).
Definition cae_SH : list shent := [mkSHE 48 (-4) (-2); mkSHE 50 0 3].
(* the state at the loop exit 0x8197c: the same registers (s3 = atom 49 is the final n), no regions *)
Definition cae_exit_atoms : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
   (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (33%nat, mkAF 4096 CAW_CEIL 0);
   (34%nat, mkAF 4096 CAW_CEIL 0);
   (38%nat, mkAF 0 3145728 0);
   (49%nat, mkAF 0 3145728 0)].
Definition cae_exit_ss : sstate := mkSS 0x8197c cae_regs [] None (mkFacts cae_exit_atoms [] []).
Definition cae_k (sx : list Z) : nat := Nat.min 4 (length sx).
(* the loop's branch conditions, as the engine sees them *)
Definition Clt2 : acond := mkAC BC_LTU (SOff 47 (-2)) (SOff 38 0).
Definition Cge2 : acond := mkAC BC_GEU (SOff 47 (-2)) (SOff 38 0).
Definition Clt1 : acond := mkAC BC_LTU (SOff 47 (-1)) (SOff 38 0).
Definition Cge1 : acond := mkAC BC_GEU (SOff 47 (-1)) (SOff 38 0).
Definition Clt0 : acond := mkAC BC_LTU (SOff 47 0) (SOff 38 0).
Definition Cge0 : acond := mkAC BC_GEU (SOff 47 0) (SOff 38 0).
(* the atoms the loop may re-key; everything below 47 is the caller's and is kept *)
Definition cae_P (n : nat) : bool := Nat.ltb n 47.

(* ---- the engine run, with an exact step count ---- *)
Ltac cae_run_tok tblok HS HJ HARU SHOK Bspan fuel :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of SHOK with
    | sh_ok _ ?Bx ?SH _ _ =>
      lazymatch type of tblok with
      | table_ok _ ?tbl =>
        let K := eval vm_compute in (run_K 0 Bx SH ss) in
        let r := eval vm_compute in (sym_runN_tok segs tbl K Bx Bspan SH fuel ss) in
        lazymatch r with
        | (?st', ?rs) =>
          let Hrun := fresh "Hrun" in
          assert (Hrun : sym_runN_tok segs tbl K Bx Bspan SH fuel ss = (st', rs)) by (vm_compute; reflexivity);
          eapply (fsw_run_tok_AJU _ tbl tblok W fuel E K Bx Bspan SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS
            SHOK ltac:(vm_compute; reflexivity) Hrun I HARU HJ);
          [ clear Hrun; cbn [sh_obls]; srr_obls
          | clear Hrun
          | clear Hrun HS HJ HARU SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
            fsw_aj_after_run_tokU HS HJ HARU SHOK ]
        end
      end end
  | _ => fail "cae_run_tok: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
  end.

(* ---- the shadow entries of the head, from the two blocks ---- *)
Lemma cae_shent_of_ra : forall (E : env) (M : word -> option byte) (nn : nat) (p base len lo hi : Z),
  bv_unsigned (ew E 32) = SHADOW_OFF -> bv_unsigned (ew E nn) = p ->
  range_addressable (rd_of tfibsegs M) SHADOW_OFF base len ->
  in_app base len -> base <= p + lo -> lo <= hi -> p + hi <= base + len ->
  shent_ok tfibsegs caw_Bx E M (mkSHE nn lo hi).
Proof.
intros E M nn p base len lo hi HB Hp HRA Happ Hlo Hlh Hhi.
assert (HBx : U E caw_Bx = SHADOW_OFF) by (unfold caw_Bx; rewrite U_SOff, HB, Z.add_0_r; apply cae_zcanon_id;
  unfold SHADOW_OFF; lia).
assert (Hpn : U E (SOff nn 0) = p) by (rewrite U_SOff, Hp, Z.add_0_r; apply cae_zcanon_id;
  pose proof (u64_range (ew E nn)); unfold in_app, kLowShadowBeg, kHighMemBeg in Happ; lia).
unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HBx, Hpn. split.
- destruct (Z_lt_le_dec lo hi); [|apply range_addressable_nil; lia].
  eapply range_addressable_sub; [exact HRA | lia | lia].
- intros a Ha. cbn [Z.min Z.max] in Ha.
  pose proof ASAN_CEIL_range as [HC1 HC2].
  unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

Lemma cae_mem_ok : forall (k : nat) (E' : env) (M : word -> option byte) (p q : Z) (sx' : list Z),
  (2 <= k <= 4)%nat -> (k <= length sx')%nat ->
  bv_unsigned (ew E' 51) = p + 5 -> bv_unsigned (ew E' 50) = q ->
  (forall j, (j < k)%nat -> ew E' (52 + j) = Z_to_bv 64 (nth j sx' 0)) ->
  Forall (fun v => 0 <= v < 64) sx' ->
  (forall j, (j < k)%nat -> val_mem tfibsegs M (p + Z.of_nat j) 1 (nth j sx' 0)) ->
  (forall o, 0 <= o < Z.of_nat k - 1 -> writable_at tfibsegs M (q + o)) ->
  0 <= p -> p + 4 <= 2 ^ 64 -> 0 <= q -> q + 3 <= 2 ^ 64 ->
  (p + Z.of_nat k <= q \/ q + 3 <= p) ->
  mem_ok tfibsegs E' M (cae_mem k).
Proof.
intros k E' M p q sx' Hk Hlen H51 H50 Hat Hsx Hby Hwr Hp0 Hp1 Hq0 Hq1 Hdisj.
assert (Hnth : forall j, (j < k)%nat -> 0 <= nth j sx' 0 < 64).
{ intros j Hj. rewrite Forall_forall in Hsx. apply Hsx. apply nth_In. lia. }
assert (CH : forall j, (j < k)%nat ->
   YP09.chunk_ok tfibsegs E' M (p + 5) (YP09.mkChunk (-5 + Z.of_nat j) (CVal 1 (SOff (52 + j) 0)))).
{ intros j Hj.
  apply (chunk_ok_val tfibsegs E' M (p + 5) (-5 + Z.of_nat j) 1%N (SOff (52 + j) 0) (nth j sx' 0)).
  - rewrite fsw_SOff0. apply Hat. exact Hj.
  - pose proof (Hnth j Hj). cbn [Z.of_N Z.mul]. cbn. lia.
  - cbn. lia.
  - replace (p + 5 + (-5 + Z.of_nat j)) with (p + Z.of_nat j) by lia. apply Hby. exact Hj. }
unfold mem_ok, cae_mem. split; [|split].
- destruct k as [|[|[|[|[|k0]]]]]; try lia; vm_compute; reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold cae_six, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite H51. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    destruct k as [|[|[|[|[|k0]]]]]; try lia; cbn [firstn cae_chunks];
      repeat (apply Forall_cons;
        [ first [ exact (CH 0%nat ltac:(lia)) | exact (CH 1%nat ltac:(lia))
                | exact (CH 2%nat ltac:(lia)) | exact (CH 3%nat ltac:(lia)) ] | ]);
      apply Forall_nil.
  + unfold cae_out, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite H50. split; [lia|]. split; [lia|]. split; [exact Hwr|]. constructor.
- cbn [pairwise_disjoint all_disjoint]. split; [split; [|exact I]|split; [exact I|exact I]].
  unfold extent_disjoint, cae_six, cae_out.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite H50, H51. lia.
Qed.

Lemma cae_bytes_app : forall (W' : world tfibsegs) (mm : word -> option byte) (pp : Z) (l1 l2 : list Z),
  caw_bytes W' mm pp l1 ->
  (forall j, (j < length l2)%nat -> caw_at W' mm (pp + Z.of_nat (length l1) + Z.of_nat j) (nth j l2 0)) ->
  caw_bytes W' mm pp (l1 ++ l2).
Proof.
intros W' mm pp l1 l2 H1 H2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [Hlt|Hge].
- rewrite app_nth1 by exact Hlt. apply H1. exact Hlt.
- rewrite app_nth2 by exact Hge.
  replace (pp + Z.of_nat j) with (pp + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia.
  apply H2. lia.
Qed.

Lemma cae_bytes_frame : forall (W' : world tfibsegs) (m1 m2 : word -> option byte) (pp lo hi : Z) (l : list Z),
  caw_bytes W' m1 pp l ->
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m2 x = m1 x) ->
  0 <= pp -> pp + Z.of_nat (length l) <= 2 ^ 64 ->
  (pp + Z.of_nat (length l) <= lo \/ hi <= pp) ->
  caw_bytes W' m2 pp l.
Proof.
intros W' m1 m2 pp lo hi l H1 Hfr Hp0 Hp1 Hdj j Hj kk Hk.
assert (kk = 0)%nat by lia. subst kk.
specialize (H1 j Hj 0%nat ltac:(lia)).
rewrite <- H1.
assert (Hx : mrestrict (w_H W') m2 (Z_to_bv 64 (pp + Z.of_nat j + Z.of_nat 0))
           = mrestrict (w_H W') m1 (Z_to_bv 64 (pp + Z.of_nat j + Z.of_nat 0))).
{ unfold mrestrict. destruct (w_H W' (Z_to_bv 64 (pp + Z.of_nat j + Z.of_nat 0))); [reflexivity|].
  apply Hfr. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. lia. }
unfold YP09.mbyte. rewrite Hx. reflexivity.
Qed.

(* the three branch conditions of one iteration, added to the head state *)
Lemma cae_add3 : forall E ms k c1 c2 c3,
  st_ok tfibsegs E (cae_ss k []) ms -> acond_ok E c1 -> acond_ok E c2 -> acond_ok E c3 ->
  st_ok tfibsegs E (cae_ss k [c3; c2; c1]) ms.
Proof.
intros E ms k [b1 x1 y1] [b2 x2 y2] [b3 x3 y3] HS H1 H2 H3.
exact (st_ok_add_cond tfibsegs E _ _ b3 x3 y3
        (st_ok_add_cond tfibsegs E _ _ b2 x2 y2
          (st_ok_add_cond tfibsegs E _ _ b1 x1 y1 HS H1) H2) H3).
Qed.

(* adding the three aliases back after a re-abstraction *)
Lemma cae_st_ok_alias : forall E ss ms a b,
  st_ok tfibsegs E ss ms -> sv_denot E a = sv_denot E b ->
  st_ok tfibsegs E (mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
    (mkFacts (f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) ((a, b) :: f_alias (ss_facts ss)))) ms.
Proof.
intros E ss ms a b (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hab.
unfold st_ok. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
exact (facts_ok_add_alias E (ss_facts ss) a b H9 Hab).
Qed.

(* the shadow cells of the two blocks are untouched by a write inside app memory *)
Lemma cae_ra_keep : forall (W' : world tfibsegs) (m1 m2 : word -> option byte) (a len lo hi : Z),
  range_addressable (rd_of tfibsegs (mrestrict (w_H W') m1)) SHADOW_OFF a len ->
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m2 x = m1 x) ->
  4096 <= lo -> (hi <= kLowShadowBeg \/ kHighMemBeg <= lo) ->
  0 <= a -> a + len <= CAW_CEIL ->
  range_addressable (rd_of tfibsegs (mrestrict (w_H W') m2)) SHADOW_OFF a len.
Proof.
intros W' m1 m2 a len lo hi HRA Hfr Hlo Happ Ha0 Ha1 x Hx.
destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite <- Hs. unfold rd_of. f_equal.
assert (HD : CAW_CEIL / 8 = 17592184995840) by (vm_compute; reflexivity).
assert (Hc : SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < kHighMemBeg).
{ unfold shadow_of_addr. assert (H1 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (H2 : x / 8 <= CAW_CEIL / 8) by (apply Z.div_le_mono; lia).
  rewrite HD in H2. unfold SHADOW_OFF, kHighMemBeg in *. lia. }
assert (Heq : mrestrict (w_H W') m2 (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x))
            = mrestrict (w_H W') m1 (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x))).
{ unfold mrestrict. destruct (w_H W' (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x))); [reflexivity|].
  apply Hfr. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by (unfold SHADOW_OFF, kHighMemBeg in *; lia).
  unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
unfold YP09.mbyte. rewrite Heq. reflexivity.
Qed.

(* a register the run left as `SOff nn z` holds the value of atom nn plus z *)
Lemma cae_reg_val : forall (H : word -> bool) E ss ms (r : bv 5) nn z v,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff nn z ->
  ew E nn = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + z < 2 ^ 64 ->
  getr (ms_regs ms) r = Z_to_bv 64 (v + z).
Proof.
intros Hh E ss ms r nn z v HS Hr Hv Hv1 Hv2.
apply bv_eq. rewrite (st_ok_restrict_reg tfibsegs Hh E ss ms r HS), Hr.
change (bv_unsigned (sv_denot E (SOff nn z)) = bv_unsigned (Z_to_bv 64 (v + z))).
rewrite denot_SOff, Hv. rewrite (unsigned_lit_small v) by lia.
rewrite (unsigned_lit_small (v + z)) by lia. apply cae_zcanon_id. lia.
Qed.

(* the byte a one-byte chunk of a region puts in memory (only its low 8 bits matter) *)
Lemma cae_byte_at : forall (W' : world tfibsegs) (E' : env) (mm : word -> option byte)
    (nn : nat) (bb off v : Z) (e : sv) (lo hi wlo whi : Z) (cs : list YP09.chunk),
  region_ok tfibsegs E' (mrestrict (w_H W') mm) (YP09.mkRegion (Some nn) lo hi wlo whi cs) ->
  bv_unsigned (ew E' nn) = bb ->
  In (YP09.mkChunk off (CVal 1 e)) cs ->
  U E' e mod 256 = v mod 256 ->
  caw_at W' mm (bb + off) v.
Proof.
intros W' E' mm nn bb off v e lo hi wlo whi cs Hreg Hb Hin Hmod.
destruct Hreg as (_ & _ & _ & Hcs).
cbn [YP09.r_base YP09.r_chunks base_val] in Hcs. rewrite Hb in Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
unfold YP09.chunk_ok in Hck. cbn [YP09.c_off YP09.c_val YP09.c_len cv_len] in Hck.
destruct (Hck 0 ltac:(lia)) as (b8 & Hc1 & Hc2).
cbn [cbyte] in Hc1. injection Hc1 as <-. rewrite Z.add_0_r in Hc2.
intros j Hj. assert (j = 0)%nat by lia. subst j. cbn [Z.of_nat]. rewrite Z.add_0_r.
rewrite Hc2. f_equal.
unfold byte_of_word. apply cae_bv8_mod.
replace (8 * 0) with 0 by lia. rewrite Z.shiftr_0_r.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
change (2 ^ 8) with 256. rewrite Z.shiftr_0_r, !Z.mod_mod by lia.
exact Hmod.
Qed.

(* a byte is what it is modulo 256 *)
Lemma cae_at_mod : forall (W' : world tfibsegs) (mm : word -> option byte) (a v1 v2 : Z),
  v1 mod 256 = v2 mod 256 -> caw_at W' mm a v1 -> caw_at W' mm a v2.
Proof.
intros W' mm a v1 v2 H HA j Hj. assert (j = 0)%nat by lia. subst j.
specialize (HA 0%nat ltac:(lia)).
assert (Hle : YO0f.le_byte v1 1 0 = YO0f.le_byte v2 1 0).
{ unfold YO0f.le_byte. do 2 f_equal. change (2 ^ (8 * Z.of_nat 1)) with 256. exact H. }
rewrite HA, Hle. reflexivity.
Qed.

Lemma cae_agree_pd : forall E1 E2, env_agree 47 E1 E2 -> env_agree_pd cae_P PT E1 E2.
Proof.
intros E1 E2 [H1 H2]. split.
- intros nn Hnn. unfold cae_P in Hnn. apply Nat.ltb_lt in Hnn. exact (H1 nn Hnn).
- intros d _. rewrite H2. reflexivity.
Qed.

(* the state at the loop exit, re-keyed onto the canonical atoms *)
Lemma cae_exit_st : forall (W : world tfibsegs) (E1 E2 : env) (ms1 : machine_state) (ssf : sstate) (nf : Z),
  st_ok tfibsegs E1 ssf (restrict (w_H W) ms1) ->
  ss_pc ssf = 0x8197c ->
  reabs_check cae_P ssf cae_regs (mkFacts cae_exit_atoms [] []) = true ->
  env_agree 47 E1 E2 ->
  Forall (fun rj : bv 5 * nat => ew E2 (snd rj) = getr (ms_regs ms1) (fst rj)) (reabs_obl cae_P cae_regs) ->
  ew E2 49 = Z_to_bv 64 nf -> 0 <= nf <= 3145728 ->
  st_ok tfibsegs E2 cae_exit_ss (restrict (w_H W) ms1).
Proof.
intros W E1 E2 ms1 ssf nf HS Hpc Hchk HAG HOB H49 Hnf.
unfold cae_exit_ss. rewrite <- Hpc.
apply (st_ok_reabs tfibsegs cae_P E1 E2 ssf (restrict (w_H W) ms1) cae_regs []
        (mkFacts cae_exit_atoms [] []) HS (cae_agree_pd E1 E2 HAG) Hchk HOB).
- apply Forall_forall. intros nf' Hin. vm_compute in Hin. destruct Hin as [<-|[]].
  cbn [fst snd]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Z.pow_0_r.
  rewrite H49. rewrite (unsigned_lit_small nf) by lia.
  split; [lia|]. split; [apply Z.mod_1_r | lia].
- split; [reflexivity|]. split; [constructor | exact I].
Qed.

(* the state at the head of the next iteration, re-keyed onto the canonical atoms *)
Lemma cae_head_st : forall (W : world tfibsegs) (E1 E2 : env) (ms1 : machine_state) (ssf : sstate) (k : nat)
    (sx' : list Z) (six' want' i' n' : Z),
  st_ok tfibsegs E1 ssf (restrict (w_H W) ms1) ->
  ss_pc ssf = 0x817dc ->
  reabs_check cae_P ssf cae_regs (mkFacts cae_atoms [] []) = true ->
  env_agree 47 E1 E2 ->
  Forall (fun rj : bv 5 * nat => ew E2 (snd rj) = getr (ms_regs ms1) (fst rj)) (reabs_obl cae_P cae_regs) ->
  ew E2 33 = Z_to_bv 64 six' -> ew E2 34 = Z_to_bv 64 want' ->
  ew E2 47 = Z_to_bv 64 (i' + 4) -> ew E2 48 = Z_to_bv 64 (six' + i' + 4) ->
  ew E2 49 = Z_to_bv 64 n' -> ew E2 50 = Z_to_bv 64 (want' + n') ->
  ew E2 51 = Z_to_bv 64 (six' + i' + 5) ->
  ew E2 52 = Z_to_bv 64 (nth 0 sx' 0) -> ew E2 53 = Z_to_bv 64 (nth 1 sx' 0) ->
  ew E2 54 = Z_to_bv 64 (nth 2 sx' 0) -> ew E2 55 = Z_to_bv 64 (nth 3 sx' 0) ->
  Forall (fun v => 0 <= v < 64) sx' ->
  0 <= i' -> i' + 4 <= 3145732 -> 0 <= n' <= 3145728 ->
  4096 <= six' -> six' + i' + 5 <= CAW_CEIL + 16 -> 4096 <= want' -> want' + n' <= CAW_CEIL ->
  mem_ok tfibsegs E2 (ms_mem (restrict (w_H W) ms1)) (cae_mem k) ->
  st_ok tfibsegs E2 (cae_ss k []) (restrict (w_H W) ms1).
Proof.
intros W E1 E2 ms1 ssf k sx' six' want' i' n' HS Hpc Hchk HAG HOB H33 H34 H47 H48 H49 H50 H51
  H52 H53 H54 H55 Hsx' Hi0 Hi1 Hn' H6lo H6hi Hwlo Hwhi HM.
unfold CAW_CEIL in H6hi, Hwhi.
assert (HVj : forall j, 0 <= nth j sx' 0 < 64).
{ intros j. destruct (Nat.lt_ge_cases j (length sx')) as [Hl|Hg].
  - rewrite Forall_forall in Hsx'. apply Hsx'. apply nth_In. exact Hl.
  - rewrite nth_overflow by exact Hg. lia. }
pose proof (HVj 0%nat). pose proof (HVj 1%nat). pose proof (HVj 2%nat). pose proof (HVj 3%nat).
assert (HR : st_ok tfibsegs E2 (mkSS (ss_pc ssf) cae_regs (cae_mem k) None (mkFacts cae_atoms [] []))
               (restrict (w_H W) ms1)).
{ apply (st_ok_reabs tfibsegs cae_P E1 E2 ssf (restrict (w_H W) ms1) cae_regs (cae_mem k)
          (mkFacts cae_atoms [] []) HS (cae_agree_pd E1 E2 HAG) Hchk HOB); [|exact HM].
  apply Forall_forall. intros nf Hin. vm_compute in Hin.
  repeat (destruct Hin as [<-|Hin]); [..|destruct Hin];
    cbn [fst snd]; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Z.pow_0_r;
    (split; [|split; [apply Z.mod_1_r | lia]]);
    first [ rewrite H47 | rewrite H48 | rewrite H49 | rewrite H50 | rewrite H51
          | rewrite H52 | rewrite H53 | rewrite H54 | rewrite H55 ];
    rewrite unsigned_lit_small by lia; unfold CAW_CEIL; lia. }
rewrite Hpc in HR.
assert (Hal3 : sv_denot E2 (SAlu ALU_ADD (SOff 34 0) (SOff 49 0)) = sv_denot E2 (SOff 50 0)).
{ apply bv_eq. change (U E2 (SAlu ALU_ADD (SOff 34 0) (SOff 49 0)) = U E2 (SOff 50 0)).
  rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E2 34 want' H34 ltac:(lia)), (U_atom E2 49 n' H49 ltac:(lia)),
          (U_atom E2 50 (want' + n') H50 ltac:(lia)).
  rewrite cae_zcanon_id by lia. lia. }
assert (Hal2 : sv_denot E2 (SAlu ALU_ADD (SOff 33 1) (SOff 47 0)) = sv_denot E2 (SOff 51 0)).
{ apply bv_eq. change (U E2 (SAlu ALU_ADD (SOff 33 1) (SOff 47 0)) = U E2 (SOff 51 0)).
  rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom_off E2 33 six' 1 H33 ltac:(lia) ltac:(lia)),
          (U_atom E2 47 (i' + 4) H47 ltac:(lia)),
          (U_atom E2 51 (six' + i' + 5) H51 ltac:(lia)).
  rewrite cae_zcanon_id by lia. lia. }
assert (Hal1 : sv_denot E2 (SAlu ALU_ADD (SOff 33 0) (SOff 47 0)) = sv_denot E2 (SOff 48 0)).
{ apply bv_eq. change (U E2 (SAlu ALU_ADD (SOff 33 0) (SOff 47 0)) = U E2 (SOff 48 0)).
  rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E2 33 six' H33 ltac:(lia)), (U_atom E2 47 (i' + 4) H47 ltac:(lia)),
          (U_atom E2 48 (six' + i' + 4) H48 ltac:(lia)).
  rewrite cae_zcanon_id by lia. lia. }
exact (cae_st_ok_alias E2 _ _ _ _
         (cae_st_ok_alias E2 _ _ _ _
            (cae_st_ok_alias E2 _ _ _ _ HR Hal3) Hal2) Hal1).
Qed.

Ltac cae_lk EL LD :=
  lazymatch goal with
  | |- ew _ ?j = _ =>
      let jj := eval compute in (Nat.sub j 47) in
      change j with (47 + jj)%nat; rewrite (EL jj ltac:(lia)); unfold LD; cbn [nth]; reflexivity
  end.

(* ---- the walk of the emit loop: from the head 0x817dc to the exit 0x8197c ---- *)
Lemma caw_emit_loop : forall (L : nat) (sx done : list Z) (E : env) (ms : machine_state) (mdc : Model)
    (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
    (Up : list (Z * Z)) (W : world tfibsegs) (kj six want Lsix Lwant m i n : Z),
  (length sx <= L)%nat ->
  st_ok tfibsegs E (cae_ss (cae_k sx) []) (restrict (w_H W) ms) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Up (ms_mem ms)) mdc kj ->
  ARU tfibsegs B lyc Sc Up W (ms_mem ms) mdc ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  ew E 33 = Z_to_bv 64 six ->
  ew E 34 = Z_to_bv 64 want ->
  ew E 38 = Z_to_bv 64 m ->
  ew E 47 = Z_to_bv 64 (i + 4) ->
  ew E 48 = Z_to_bv 64 (six + i + 4) ->
  ew E 49 = Z_to_bv 64 n ->
  ew E 50 = Z_to_bv 64 (want + n) ->
  ew E 51 = Z_to_bv 64 (six + i + 5) ->
  (forall j, (j < cae_k sx)%nat -> ew E (52 + j) = Z_to_bv 64 (nth j sx 0)) ->
  Forall (fun v => 0 <= v < 64) sx ->
  Z.of_nat (length sx) = m - i -> Z.of_nat (length done) = n ->
  0 <= i < m -> i mod 4 = 0 -> m mod 4 <> 1 -> 4 * n = 3 * i -> m <= 3145728 ->
  in_app six Lsix -> in_app want Lwant -> m <= Lsix -> 3 * (m / 4) + 3 <= Lwant ->
  (six + Lsix <= want \/ want + Lwant <= six) ->
  range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms))) SHADOW_OFF six Lsix ->
  range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms))) SHADOW_OFF want Lwant ->
  (forall a, want <= a < want + Lwant -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms)) a) ->
  (forall a, want <= a < want + Lwant -> awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a) ->
  caw_bytes W (ms_mem ms) (six + i) sx ->
  caw_bytes W (ms_mem ms) want done ->
  (forall (E2 : env) (ms2 : machine_state) (mdc2 : Model),
     env_agree 47 E E2 ->
     st_ok tfibsegs E2 cae_exit_ss (restrict (w_H W) ms2) ->
     ew E2 49 = Z_to_bv 64 (n + Z.of_nat (length (WS.six_bytes sx))) ->
     ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (unpoison Up (ms_mem ms2)) mdc2 kj ->
     ARU tfibsegs B lyc Sc Up W (ms_mem ms2) mdc2 ->
     caw_bytes W (ms_mem ms2) want (done ++ WS.six_bytes sx) ->
     (forall x : word, ~ (want + n <= bv_unsigned x < want + n + Z.of_nat (length (WS.six_bytes sx))) ->
        ms_mem ms2 x = ms_mem ms x) ->
     mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms2)) ->
     range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms2))) SHADOW_OFF six Lsix ->
     range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms2))) SHADOW_OFF want Lwant ->
     SRr tfibsegs W (mkCfg ms2 mdc2) Q) ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
induction L as [|L IH]; intros sx done E ms mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc Up W kj
  six want Lsix Lwant m i n HL HS HJ HARU E32 E33 E34 E38 E47 E48 E49 E50 E51 Esx Hsx64 Hlen Hdlen
  Hi Hi4 Hm4 Hn4 Hmmax Happ6 Happw Hmle Hwfit Hdisj RA6 RAW HWR HAWR HB6 HBd HK.
{ exfalso. destruct sx as [|a sxr]; [cbn [length] in Hlen; lia | cbn [length] in HL; lia]. }
pose proof ASAN_CEIL_range as [HC1 HC2].
assert (H6lo : 4096 <= six) by (destruct Happ6 as [X _]; exact X).
assert (Hwlo : 4096 <= want) by (destruct Happw as [X _]; exact X).
assert (H6hi : six + Lsix <= CAW_CEIL)
  by (destruct Happ6 as [_ [X|[_ X]]]; unfold kLowShadowBeg, CAW_CEIL in *; lia).
assert (Hwhi : want + Lwant <= CAW_CEIL)
  by (destruct Happw as [_ [X|[_ X]]]; unfold kLowShadowBeg, CAW_CEIL in *; lia).
pose proof (Z.div_mod i 4 ltac:(lia)) as Hdm.
assert (Hneq : n = 3 * (i / 4)) by lia.
assert (Hidiv : i / 4 <= m / 4) by (apply Z.div_le_mono; lia).
assert (Hn3 : n + 3 <= Lwant) by lia.
assert (Hn0 : 0 <= n) by lia.
unfold CAW_CEIL in H6hi, Hwhi.
destruct sx as [|s0 [|s1 [|s2 [|s3 rest]]]].
{ exfalso. cbn [length] in Hlen. lia. }
{ exfalso. cbn [length] in Hlen. apply Hm4. replace m with (i + 1) by lia.
  rewrite Zplus_mod, Hi4. reflexivity. }
{ (* ---------------- |sx| = 2: one byte, then the exit ---------------- *)
  cbn [cae_k length Nat.min] in HS, Esx. cbn [length] in Hlen.
  assert (Hm2 : m = i + 2) by lia.
  pose proof (Forall_inv Hsx64) as Hv0. pose proof (Forall_inv (Forall_inv_tail Hsx64)) as Hv1.
  cbv beta in Hv0, Hv1.
  pose proof (Esx 0%nat ltac:(lia)) as E52. pose proof (Esx 1%nat ltac:(lia)) as E53.
  cbn [nth Nat.add] in E52, E53.
  assert (SHOK : sh_ok tfibsegs caw_Bx cae_SH E (mrestrict (w_H W) (ms_mem ms))).
  { unfold sh_ok, cae_SH. constructor; [|constructor; [|constructor]].
    - apply (cae_shent_of_ra E _ 48%nat (six + i + 4) six Lsix);
        [rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia
        | rewrite E48; apply unsigned_lit_small; lia | exact RA6 | exact Happ6 | lia | lia | lia].
    - apply (cae_shent_of_ra E _ 50%nat (want + n) want Lwant);
        [rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia
        | rewrite E50; apply unsigned_lit_small; lia | exact RAW | exact Happw | lia | lia | lia]. }
  assert (HSc : st_ok tfibsegs E (cae_ss 2 [Cge2; Cge1; Cge0]) (restrict (w_H W) ms)).
  { apply (cae_add3 E _ 2%nat Cge0 Cge1 Cge2 HS);
      unfold acond_ok, Cge0, Cge1, Cge2; cbn [ac_c ac_a ac_b];
      rewrite branch_geu_U, (U_atom E 38 m E38 ltac:(lia));
      [ rewrite (U_atom_off E 47 (i + 4) 0 E47 ltac:(lia) ltac:(lia))
      | rewrite (U_atom_off E 47 (i + 4) (-1) E47 ltac:(lia) ltac:(lia))
      | rewrite (U_atom_off E 47 (i + 4) (-2) E47 ltac:(lia) ltac:(lia)) ];
      apply negb_true_iff, Z.ltb_ge; lia. }
  clear HS.
  cae_run_tok caw_tbl_ok HSc HJ HARU SHOK caw_Bspan 34%N.
  { intros aa Haa. destruct Haa as (r & Hr & Hb). cbn [cae_ss cae_mem ss_mem In] in Hr.
    destruct Hr as [<-|[<-|[]]].
    - cbn [cae_six YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. exfalso. lia.
    - cbn [cae_out YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
      rewrite E50 in Hb. rewrite (unsigned_lit_small (want + n)) in Hb by lia.
      apply HAWR. cbn [Z.of_nat] in Hb. lia. }
  lazymatch type of HSc with st_ok _ ?EE _ _ => set (E1 := EE) in * end.
  assert (EQ : forall nn, (nn < 66)%nat -> ew E1 nn = ew E nn).
  { intros nn Hnn. unfold E1. repeat (rewrite ew_ewset_other by lia). reflexivity. }
  assert (Hb50 : bv_unsigned (ew E1 50) = want + n).
  { rewrite (EQ 50%nat ltac:(lia)), E50. apply unsigned_lit_small. lia. }
  assert (R19 : getr (ms_regs ms0) 19%bv = Z_to_bv 64 (n + 1)).
  { apply (cae_reg_val (w_H W) E1 _ ms0 19%bv 49 1 n HSc ltac:(vm_compute; reflexivity)
            ltac:(rewrite (EQ 49%nat ltac:(lia)); exact E49) ltac:(lia) ltac:(lia)). }
  set (LD := [getr (ms_regs ms0) 11%bv; Z_to_bv 64 0; getr (ms_regs ms0) 19%bv;
     Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
     getr (ms_regs ms0) 5%bv; getr (ms_regs ms0) 6%bv; getr (ms_regs ms0) 7%bv;
     getr (ms_regs ms0) 12%bv; getr (ms_regs ms0) 17%bv; getr (ms_regs ms0) 28%bv;
     getr (ms_regs ms0) 29%bv; getr (ms_regs ms0) 30%bv; getr (ms_regs ms0) 31%bv;
     getr (ms_regs ms0) 16%bv]).
  set (E2 := extK E1 47 LD).
  assert (EL : forall j, (j < 19)%nat -> ew E2 (47 + j) = nth j LD (Z_to_bv 64 0)).
  { intros j Hj. unfold E2. apply cae_ext_lookup. unfold LD. cbn [length]. lia. }
  assert (HAG : env_agree 47 E E2).
  { split.
    - intros nn Hnn. unfold E2. rewrite (proj1 (env_agree_extK E1 47 LD) nn Hnn).
      exact (EQ nn ltac:(lia)).
    - unfold E2. rewrite (proj2 (env_agree_extK E1 47 LD)). unfold E1. reflexivity. }
  assert (E2_49 : ew E2 49 = Z_to_bv 64 (n + 1)).
  { change 49%nat with (47 + 2)%nat. rewrite (EL 2%nat ltac:(lia)). unfold LD. cbn [nth]. exact R19. }
  assert (HSX : st_ok tfibsegs E2 cae_exit_ss (restrict (w_H W) ms0)).
  { apply (cae_exit_st W E1 E2 ms0 _ (n + 1) HSc).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - unfold E2. apply env_agree_extK.
    - apply Forall_forall. intros rj Hin. vm_compute in Hin.
      repeat (destruct Hin as [<-|Hin]); [..|destruct Hin]; cbn [fst snd]; cae_lk EL LD.
    - exact E2_49.
    - lia. }
  assert (U52 : U E1 (SOff 52 0) = s0).
  { unfold U. rewrite fsw_SOff0, (EQ 52%nat ltac:(lia)), E52.
    apply unsigned_lit_small. all: lia. }
  assert (U53 : U E1 (SOff 53 0) = s1).
  { unfold U. rewrite fsw_SOff0, (EQ 53%nat ltac:(lia)), E53.
    apply unsigned_lit_small. all: lia. }
  assert (Hd1 : 0 <= s1 / 16 < 4) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (HBY : caw_at W (ms_mem ms0) (want + n) (s0 * 4 + s1 / 16)).
  { pose proof (fsw_region_nth E1 _ _ 1%nat _ HSc ltac:(vm_compute; reflexivity)) as HR.
    cbn [ms_mem restrict] in HR.
    replace (want + n) with (want + n + 0) by lia.
    apply (cae_byte_at W E1 (ms_mem ms0) 50%nat (want + n) 0 (s0 * 4 + s1 / 16)
             (SAlu ALU_OR (SAlu ALU_SRL (SOff 53 0) (SLit 4)) (SAlu ALU_SLL (SOff 52 0) (SLit 2)))
             0 3 0 1 _ HR Hb50 ltac:(cbn [In]; tauto)).
    rewrite (cae_byte0 E1 (SOff 52 0) (SOff 53 0) s0 s1 U52 U53 ltac:(lia) ltac:(lia)).
    reflexivity. }
  assert (HFR : forall x : word, ~ (want + n <= bv_unsigned x < want + n + 1) ->
                 ms_mem ms0 x = ms_mem ms x).
  { intros x Hx. apply HF. intros (r & Hr & Hb). cbn [cae_ss cae_mem ss_mem In] in Hr.
    destruct Hr as [<-|[<-|[]]].
    - cbn [cae_six YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. lia.
    - cbn [cae_out YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
      rewrite E50 in Hb. rewrite (unsigned_lit_small (want + n)) in Hb by lia.
      apply Hx. cbn [Z.of_nat] in Hb. lia. }
  apply (HK E2 ms0 _).
  { exact HAG. }
  { exact HSX. }
  { rewrite caw_six_bytes_2. cbn [length Z.of_nat]. exact E2_49. }
  { exact HJ. }
  { exact HARU. }
  { rewrite caw_six_bytes_2. apply cae_bytes_app.
    - apply (cae_bytes_frame W (ms_mem ms) (ms_mem ms0) want (want + n) (want + n + 1) done HBd HFR);
        lia.
    - intros j Hj. cbn [length] in Hj. assert (j = 0)%nat by lia. subst j. cbn [nth Z.of_nat].
      rewrite Hdlen, Z.add_0_r. exact HBY. }
  { rewrite caw_six_bytes_2. cbn [length Z.of_nat]. exact HFR. }
  { exact HG. }
  { apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) six Lsix (want + n) (want + n + 1) RA6 HFR);
      [lia | destruct Happw as [_ [X|[X _]]]; [left; lia | right; lia] | lia | unfold CAW_CEIL; lia]. }
  { apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) want Lwant (want + n) (want + n + 1) RAW HFR);
      [lia | destruct Happw as [_ [X|[X _]]]; [left; lia | right; lia] | lia | unfold CAW_CEIL; lia]. } }
{ (* ---------------- |sx| = 3: two bytes, then the exit ---------------- *)
  cbn [cae_k length Nat.min] in HS, Esx. cbn [length] in Hlen.
  assert (Hm3 : m = i + 3) by lia.
  pose proof (Forall_inv Hsx64) as Hv0. pose proof (Forall_inv (Forall_inv_tail Hsx64)) as Hv1.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail Hsx64))) as Hv2.
  cbv beta in Hv0, Hv1, Hv2.
  pose proof (Esx 0%nat ltac:(lia)) as E52. pose proof (Esx 1%nat ltac:(lia)) as E53.
  pose proof (Esx 2%nat ltac:(lia)) as E54.
  cbn [nth Nat.add] in E52, E53, E54.
  assert (SHOK : sh_ok tfibsegs caw_Bx cae_SH E (mrestrict (w_H W) (ms_mem ms))).
  { unfold sh_ok, cae_SH. constructor; [|constructor; [|constructor]].
    - apply (cae_shent_of_ra E _ 48%nat (six + i + 4) six Lsix);
        [rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia
        | rewrite E48; apply unsigned_lit_small; lia | exact RA6 | exact Happ6 | lia | lia | lia].
    - apply (cae_shent_of_ra E _ 50%nat (want + n) want Lwant);
        [rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia
        | rewrite E50; apply unsigned_lit_small; lia | exact RAW | exact Happw | lia | lia | lia]. }
  assert (HSc : st_ok tfibsegs E (cae_ss 3 [Clt2; Cge1; Cge0]) (restrict (w_H W) ms)).
  { apply (cae_add3 E _ 3%nat Cge0 Cge1 Clt2 HS).
    - unfold acond_ok, Cge0. cbn [ac_c ac_a ac_b].
      rewrite branch_geu_U, (U_atom_off E 47 (i + 4) 0 E47 ltac:(lia) ltac:(lia)),
              (U_atom E 38 m E38 ltac:(lia)).
      apply negb_true_iff, Z.ltb_ge. lia.
    - unfold acond_ok, Cge1. cbn [ac_c ac_a ac_b].
      rewrite branch_geu_U, (U_atom_off E 47 (i + 4) (-1) E47 ltac:(lia) ltac:(lia)),
              (U_atom E 38 m E38 ltac:(lia)).
      apply negb_true_iff, Z.ltb_ge. lia.
    - unfold acond_ok, Clt2. cbn [ac_c ac_a ac_b].
      rewrite branch_ltu_U, (U_atom_off E 47 (i + 4) (-2) E47 ltac:(lia) ltac:(lia)),
              (U_atom E 38 m E38 ltac:(lia)).
      apply Z.ltb_lt. lia. }
  clear HS.
  cae_run_tok caw_tbl_ok HSc HJ HARU SHOK caw_Bspan 53%N.
  { unfold caw_Bx. rewrite (U_atom E 32 SHADOW_OFF E32 ltac:(unfold SHADOW_OFF; lia)).
    rewrite (U_atom_off E 48 (six + i + 4) (-2) E48 ltac:(lia) ltac:(lia)).
    eapply range_addressable_sub; [exact RA6 | lia | lia]. }
  { intros aa Haa. destruct Haa as (r & Hr & Hb). cbn [cae_ss cae_mem ss_mem In] in Hr.
    destruct Hr as [<-|[<-|[]]].
    - cbn [cae_six YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. exfalso. lia.
    - cbn [cae_out YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
      rewrite E50 in Hb. rewrite (unsigned_lit_small (want + n)) in Hb by lia.
      apply HAWR. cbn [Z.of_nat] in Hb. lia. }
  lazymatch type of HSc with st_ok _ ?EE _ _ => set (E1 := EE) in * end.
  assert (EQ : forall nn, (nn < 66)%nat -> ew E1 nn = ew E nn).
  { intros nn Hnn. unfold E1. repeat (rewrite ew_ewset_other by lia). reflexivity. }
  assert (Hb50 : bv_unsigned (ew E1 50) = want + n).
  { rewrite (EQ 50%nat ltac:(lia)), E50. apply unsigned_lit_small. lia. }
  assert (R19 : getr (ms_regs ms0) 19%bv = Z_to_bv 64 (n + 2)).
  { apply (cae_reg_val (w_H W) E1 _ ms0 19%bv 49 2 n HSc ltac:(vm_compute; reflexivity)
            ltac:(rewrite (EQ 49%nat ltac:(lia)); exact E49) ltac:(lia) ltac:(lia)). }
  set (LD := [getr (ms_regs ms0) 11%bv; Z_to_bv 64 0; getr (ms_regs ms0) 19%bv;
     Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
     getr (ms_regs ms0) 5%bv; getr (ms_regs ms0) 6%bv; getr (ms_regs ms0) 7%bv;
     getr (ms_regs ms0) 12%bv; getr (ms_regs ms0) 17%bv; getr (ms_regs ms0) 28%bv;
     getr (ms_regs ms0) 29%bv; getr (ms_regs ms0) 30%bv; getr (ms_regs ms0) 31%bv;
     getr (ms_regs ms0) 16%bv]).
  set (E2 := extK E1 47 LD).
  assert (EL : forall j, (j < 19)%nat -> ew E2 (47 + j) = nth j LD (Z_to_bv 64 0)).
  { intros j Hj. unfold E2. apply cae_ext_lookup. unfold LD. cbn [length]. lia. }
  assert (HAG : env_agree 47 E E2).
  { split.
    - intros nn Hnn. unfold E2. rewrite (proj1 (env_agree_extK E1 47 LD) nn Hnn).
      exact (EQ nn ltac:(lia)).
    - unfold E2. rewrite (proj2 (env_agree_extK E1 47 LD)). unfold E1. reflexivity. }
  assert (E2_49 : ew E2 49 = Z_to_bv 64 (n + 2)).
  { change 49%nat with (47 + 2)%nat. rewrite (EL 2%nat ltac:(lia)). unfold LD. cbn [nth]. exact R19. }
  assert (HSX : st_ok tfibsegs E2 cae_exit_ss (restrict (w_H W) ms0)).
  { apply (cae_exit_st W E1 E2 ms0 _ (n + 2) HSc).
    - vm_compute; reflexivity.
    - vm_compute; reflexivity.
    - unfold E2. apply env_agree_extK.
    - apply Forall_forall. intros rj Hin. vm_compute in Hin.
      repeat (destruct Hin as [<-|Hin]); [..|destruct Hin]; cbn [fst snd]; cae_lk EL LD.
    - exact E2_49.
    - lia. }
  assert (U52 : U E1 (SOff 52 0) = s0).
  { unfold U. rewrite fsw_SOff0, (EQ 52%nat ltac:(lia)), E52.
    apply unsigned_lit_small. all: lia. }
  assert (U53 : U E1 (SOff 53 0) = s1).
  { unfold U. rewrite fsw_SOff0, (EQ 53%nat ltac:(lia)), E53.
    apply unsigned_lit_small. all: lia. }
  assert (U54 : U E1 (SOff 54 0) = s2).
  { unfold U. rewrite fsw_SOff0, (EQ 54%nat ltac:(lia)), E54.
    apply unsigned_lit_small. all: lia. }
  assert (Hd1 : 0 <= s1 / 16 < 4) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hd2 : 0 <= s2 / 4 < 16) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  pose proof (fsw_region_nth E1 _ _ 1%nat _ HSc ltac:(vm_compute; reflexivity)) as HR.
  cbn [ms_mem restrict] in HR.
  assert (HBY0 : caw_at W (ms_mem ms0) (want + n) (s0 * 4 + s1 / 16)).
  { replace (want + n) with (want + n + 0) by lia.
    apply (cae_byte_at W E1 (ms_mem ms0) 50%nat (want + n) 0 (s0 * 4 + s1 / 16)
             (SAlu ALU_OR (SAlu ALU_SRL (SOff 53 0) (SLit 4)) (SAlu ALU_SLL (SOff 52 0) (SLit 2)))
             0 3 0 2 _ HR Hb50 ltac:(cbn [In]; tauto)).
    rewrite (cae_byte0 E1 (SOff 52 0) (SOff 53 0) s0 s1 U52 U53 ltac:(lia) ltac:(lia)).
    reflexivity. }
  assert (HBY1 : caw_at W (ms_mem ms0) (want + n + 1) ((s1 mod 16) * 16 + s2 / 4)).
  { apply (cae_byte_at W E1 (ms_mem ms0) 50%nat (want + n) 1 ((s1 mod 16) * 16 + s2 / 4)
             (SAlu ALU_OR (SAlu ALU_SRL (SOff 54 0) (SLit 2)) (SAlu ALU_SLL (SOff 53 0) (SLit 4)))
             0 3 0 2 _ HR Hb50 ltac:(cbn [In]; tauto)).
    rewrite (cae_byte1 E1 (SOff 53 0) (SOff 54 0) s1 s2 U53 U54 ltac:(lia) ltac:(lia)).
    replace (s1 * 16) with ((s1 mod 16) * 16 + (s1 / 16) * 256) by (Z.div_mod_to_equations; lia).
    replace ((s1 mod 16) * 16 + (s1 / 16) * 256 + s2 / 4)
       with ((s1 mod 16) * 16 + s2 / 4 + (s1 / 16) * 256) by lia.
    apply Z_mod_plus_full. }
  assert (HFR : forall x : word, ~ (want + n <= bv_unsigned x < want + n + 2) ->
                 ms_mem ms0 x = ms_mem ms x).
  { intros x Hx. apply HF. intros (r & Hr & Hb). cbn [cae_ss cae_mem ss_mem In] in Hr.
    destruct Hr as [<-|[<-|[]]].
    - cbn [cae_six YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. lia.
    - cbn [cae_out YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
      rewrite E50 in Hb. rewrite (unsigned_lit_small (want + n)) in Hb by lia.
      apply Hx. cbn [Z.of_nat] in Hb. lia. }
  apply (HK E2 ms0 _).
  { exact HAG. }
  { exact HSX. }
  { rewrite caw_six_bytes_3. cbn [length Z.of_nat]. exact E2_49. }
  { exact HJ. }
  { exact HARU. }
  { rewrite caw_six_bytes_3. apply cae_bytes_app.
    - apply (cae_bytes_frame W (ms_mem ms) (ms_mem ms0) want (want + n) (want + n + 2) done HBd HFR);
        lia.
    - intros j Hj. cbn [length] in Hj.
      destruct j as [|[|j]]; [| |exfalso; lia]; cbn [nth Z.of_nat]; rewrite Hdlen.
      + rewrite Z.add_0_r. exact HBY0.
      + exact HBY1. }
  { rewrite caw_six_bytes_3. cbn [length Z.of_nat]. exact HFR. }
  { exact HG. }
  { apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) six Lsix (want + n) (want + n + 2) RA6 HFR);
      [lia | destruct Happw as [_ [X|[X _]]]; [left; lia | right; lia] | lia | unfold CAW_CEIL; lia]. }
  { apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) want Lwant (want + n) (want + n + 2) RAW HFR);
      [lia | destruct Happw as [_ [X|[X _]]]; [left; lia | right; lia] | lia | unfold CAW_CEIL; lia]. } }
{ destruct rest as [|s4 rest'].
  { (* ---------------- |sx| = 4: three bytes, then the exit ---------------- *)
    cbn [cae_k length Nat.min] in HS, Esx. cbn [length] in Hlen.
    assert (Hm4e : m = i + 4) by lia.
    pose proof (Forall_inv Hsx64) as Hv0.
    pose proof (Forall_inv (Forall_inv_tail Hsx64)) as Hv1.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail Hsx64))) as Hv2.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail Hsx64)))) as Hv3.
    cbv beta in Hv0, Hv1, Hv2, Hv3.
    pose proof (Esx 0%nat ltac:(lia)) as E52. pose proof (Esx 1%nat ltac:(lia)) as E53.
    pose proof (Esx 2%nat ltac:(lia)) as E54. pose proof (Esx 3%nat ltac:(lia)) as E55.
    cbn [nth Nat.add] in E52, E53, E54, E55.
    assert (SHOK : sh_ok tfibsegs caw_Bx cae_SH E (mrestrict (w_H W) (ms_mem ms))).
    { unfold sh_ok, cae_SH. constructor; [|constructor; [|constructor]].
      - apply (cae_shent_of_ra E _ 48%nat (six + i + 4) six Lsix);
          [rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia
          | rewrite E48; apply unsigned_lit_small; lia | exact RA6 | exact Happ6 | lia | lia | lia].
      - apply (cae_shent_of_ra E _ 50%nat (want + n) want Lwant);
          [rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia
          | rewrite E50; apply unsigned_lit_small; lia | exact RAW | exact Happw | lia | lia | lia]. }
    assert (HSc : st_ok tfibsegs E (cae_ss 4 [Clt2; Clt1; Cge0]) (restrict (w_H W) ms)).
    { apply (cae_add3 E _ 4%nat Cge0 Clt1 Clt2 HS).
      - unfold acond_ok, Cge0. cbn [ac_c ac_a ac_b].
        rewrite branch_geu_U, (U_atom_off E 47 (i + 4) 0 E47 ltac:(lia) ltac:(lia)),
                (U_atom E 38 m E38 ltac:(lia)).
        apply negb_true_iff, Z.ltb_ge. lia.
      - unfold acond_ok, Clt1. cbn [ac_c ac_a ac_b].
        rewrite branch_ltu_U, (U_atom_off E 47 (i + 4) (-1) E47 ltac:(lia) ltac:(lia)),
                (U_atom E 38 m E38 ltac:(lia)).
        apply Z.ltb_lt. lia.
      - unfold acond_ok, Clt2. cbn [ac_c ac_a ac_b].
        rewrite branch_ltu_U, (U_atom_off E 47 (i + 4) (-2) E47 ltac:(lia) ltac:(lia)),
                (U_atom E 38 m E38 ltac:(lia)).
        apply Z.ltb_lt. lia. }
    clear HS.
    cae_run_tok caw_tbl_ok HSc HJ HARU SHOK caw_Bspan 74%N.
    { unfold caw_Bx. rewrite (U_atom E 32 SHADOW_OFF E32 ltac:(unfold SHADOW_OFF; lia)).
      rewrite (U_atom_off E 48 (six + i + 4) (-1) E48 ltac:(lia) ltac:(lia)).
      eapply range_addressable_sub; [exact RA6 | lia | lia]. }
    { unfold caw_Bx. rewrite (U_atom E 32 SHADOW_OFF E32 ltac:(unfold SHADOW_OFF; lia)).
      rewrite (U_atom_off E 48 (six + i + 4) (-2) E48 ltac:(lia) ltac:(lia)).
      eapply range_addressable_sub; [exact RA6 | lia | lia]. }
    { intros aa Haa. destruct Haa as (r & Hr & Hb). cbn [cae_ss cae_mem ss_mem In] in Hr.
      destruct Hr as [<-|[<-|[]]].
      - cbn [cae_six YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. exfalso. lia.
      - cbn [cae_out YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
        rewrite E50 in Hb. rewrite (unsigned_lit_small (want + n)) in Hb by lia.
        apply HAWR. cbn [Z.of_nat] in Hb. lia. }
    lazymatch type of HSc with st_ok _ ?EE _ _ => set (E1 := EE) in * end.
    assert (EQ : forall nn, (nn < 66)%nat -> ew E1 nn = ew E nn).
    { intros nn Hnn. unfold E1. repeat (rewrite ew_ewset_other by lia). reflexivity. }
    assert (Hb50 : bv_unsigned (ew E1 50) = want + n).
    { rewrite (EQ 50%nat ltac:(lia)), E50. apply unsigned_lit_small. lia. }
    assert (R19 : getr (ms_regs ms0) 19%bv = Z_to_bv 64 (n + 3)).
    { apply (cae_reg_val (w_H W) E1 _ ms0 19%bv 49 3 n HSc ltac:(vm_compute; reflexivity)
              ltac:(rewrite (EQ 49%nat ltac:(lia)); exact E49) ltac:(lia) ltac:(lia)). }
    set (LD := [getr (ms_regs ms0) 11%bv; Z_to_bv 64 0; getr (ms_regs ms0) 19%bv;
       Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
       getr (ms_regs ms0) 5%bv; getr (ms_regs ms0) 6%bv; getr (ms_regs ms0) 7%bv;
       getr (ms_regs ms0) 12%bv; getr (ms_regs ms0) 17%bv; getr (ms_regs ms0) 28%bv;
       getr (ms_regs ms0) 29%bv; getr (ms_regs ms0) 30%bv; getr (ms_regs ms0) 31%bv;
       getr (ms_regs ms0) 16%bv]).
    set (E2 := extK E1 47 LD).
    assert (EL : forall j, (j < 19)%nat -> ew E2 (47 + j) = nth j LD (Z_to_bv 64 0)).
    { intros j Hj. unfold E2. apply cae_ext_lookup. unfold LD. cbn [length]. lia. }
    assert (HAG : env_agree 47 E E2).
    { split.
      - intros nn Hnn. unfold E2. rewrite (proj1 (env_agree_extK E1 47 LD) nn Hnn).
        exact (EQ nn ltac:(lia)).
      - unfold E2. rewrite (proj2 (env_agree_extK E1 47 LD)). unfold E1. reflexivity. }
    assert (E2_49 : ew E2 49 = Z_to_bv 64 (n + 3)).
    { change 49%nat with (47 + 2)%nat. rewrite (EL 2%nat ltac:(lia)). unfold LD. cbn [nth]. exact R19. }
    assert (HSX : st_ok tfibsegs E2 cae_exit_ss (restrict (w_H W) ms0)).
    { apply (cae_exit_st W E1 E2 ms0 _ (n + 3) HSc).
      - vm_compute; reflexivity.
      - vm_compute; reflexivity.
      - unfold E2. apply env_agree_extK.
      - apply Forall_forall. intros rj Hin. vm_compute in Hin.
        repeat (destruct Hin as [<-|Hin]); [..|destruct Hin]; cbn [fst snd]; cae_lk EL LD.
      - exact E2_49.
      - lia. }
    assert (U52 : U E1 (SOff 52 0) = s0).
    { unfold U. rewrite fsw_SOff0, (EQ 52%nat ltac:(lia)), E52. apply unsigned_lit_small. all: lia. }
    assert (U53 : U E1 (SOff 53 0) = s1).
    { unfold U. rewrite fsw_SOff0, (EQ 53%nat ltac:(lia)), E53. apply unsigned_lit_small. all: lia. }
    assert (U54 : U E1 (SOff 54 0) = s2).
    { unfold U. rewrite fsw_SOff0, (EQ 54%nat ltac:(lia)), E54. apply unsigned_lit_small. all: lia. }
    assert (U55 : U E1 (SOff 55 0) = s3).
    { unfold U. rewrite fsw_SOff0, (EQ 55%nat ltac:(lia)), E55. apply unsigned_lit_small. all: lia. }
    assert (Hd1 : 0 <= s1 / 16 < 4) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Hd2 : 0 <= s2 / 4 < 16) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    pose proof (fsw_region_nth E1 _ _ 1%nat _ HSc ltac:(vm_compute; reflexivity)) as HR.
    cbn [ms_mem restrict] in HR.
    assert (HBY0 : caw_at W (ms_mem ms0) (want + n) (s0 * 4 + s1 / 16)).
    { replace (want + n) with (want + n + 0) by lia.
      apply (cae_byte_at W E1 (ms_mem ms0) 50%nat (want + n) 0 (s0 * 4 + s1 / 16)
               (SAlu ALU_OR (SAlu ALU_SRL (SOff 53 0) (SLit 4)) (SAlu ALU_SLL (SOff 52 0) (SLit 2)))
               0 3 0 3 _ HR Hb50 ltac:(cbn [In]; tauto)).
      rewrite (cae_byte0 E1 (SOff 52 0) (SOff 53 0) s0 s1 U52 U53 ltac:(lia) ltac:(lia)). reflexivity. }
    assert (HBY1 : caw_at W (ms_mem ms0) (want + n + 1) ((s1 mod 16) * 16 + s2 / 4)).
    { apply (cae_byte_at W E1 (ms_mem ms0) 50%nat (want + n) 1 ((s1 mod 16) * 16 + s2 / 4)
               (SAlu ALU_OR (SAlu ALU_SRL (SOff 54 0) (SLit 2)) (SAlu ALU_SLL (SOff 53 0) (SLit 4)))
               0 3 0 3 _ HR Hb50 ltac:(cbn [In]; tauto)).
      rewrite (cae_byte1 E1 (SOff 53 0) (SOff 54 0) s1 s2 U53 U54 ltac:(lia) ltac:(lia)).
      replace (s1 * 16) with ((s1 mod 16) * 16 + (s1 / 16) * 256) by (Z.div_mod_to_equations; lia).
      replace ((s1 mod 16) * 16 + (s1 / 16) * 256 + s2 / 4)
         with ((s1 mod 16) * 16 + s2 / 4 + (s1 / 16) * 256) by lia.
      apply Z_mod_plus_full. }
    assert (HBY2 : caw_at W (ms_mem ms0) (want + n + 2) ((s2 mod 4) * 64 + s3)).
    { apply (cae_byte_at W E1 (ms_mem ms0) 50%nat (want + n) 2 ((s2 mod 4) * 64 + s3)
               (SAlu ALU_OR (SAlu ALU_SLL (SOff 54 0) (SLit 6)) (SOff 55 0))
               0 3 0 3 _ HR Hb50 ltac:(cbn [In]; tauto)).
      rewrite (cae_byte2 E1 (SOff 54 0) (SOff 55 0) s2 s3 U54 U55 ltac:(lia) ltac:(lia)).
      replace (s2 * 64) with ((s2 mod 4) * 64 + (s2 / 4) * 256) by (Z.div_mod_to_equations; lia).
      replace ((s2 mod 4) * 64 + (s2 / 4) * 256 + s3)
         with ((s2 mod 4) * 64 + s3 + (s2 / 4) * 256) by lia.
      apply Z_mod_plus_full. }
    assert (HFR : forall x : word, ~ (want + n <= bv_unsigned x < want + n + 3) ->
                   ms_mem ms0 x = ms_mem ms x).
    { intros x Hx. apply HF. intros (r & Hr & Hb). cbn [cae_ss cae_mem ss_mem In] in Hr.
      destruct Hr as [<-|[<-|[]]].
      - cbn [cae_six YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. lia.
      - cbn [cae_out YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
        rewrite E50 in Hb. rewrite (unsigned_lit_small (want + n)) in Hb by lia.
        apply Hx. cbn [Z.of_nat] in Hb. lia. }
    apply (HK E2 ms0 _).
    { exact HAG. }
    { exact HSX. }
    { rewrite caw_six_bytes_4, caw_six_bytes_0. cbn [length Z.of_nat]. exact E2_49. }
    { exact HJ. }
    { exact HARU. }
    { rewrite caw_six_bytes_4, caw_six_bytes_0. apply cae_bytes_app.
      - apply (cae_bytes_frame W (ms_mem ms) (ms_mem ms0) want (want + n) (want + n + 3) done HBd HFR);
          lia.
      - intros j Hj. cbn [length] in Hj.
        destruct j as [|[|[|j]]]; [| | |exfalso; lia]; cbn [nth Z.of_nat]; rewrite Hdlen.
        + rewrite Z.add_0_r. exact HBY0.
        + exact HBY1.
        + exact HBY2. }
    { rewrite caw_six_bytes_4, caw_six_bytes_0. cbn [length Z.of_nat]. exact HFR. }
    { exact HG. }
    { apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) six Lsix (want + n) (want + n + 3) RA6 HFR);
        [lia | destruct Happw as [_ [X|[X _]]]; [left; lia | right; lia] | lia | unfold CAW_CEIL; lia]. }
    { apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) want Lwant (want + n) (want + n + 3) RAW HFR);
        [lia | destruct Happw as [_ [X|[X _]]]; [left; lia | right; lia] | lia | unfold CAW_CEIL; lia]. } }
  { destruct rest' as [|s5 rest''].
    { exfalso. cbn [length] in Hlen. apply Hm4. replace m with (i + 5) by lia.
      rewrite Zplus_mod, Hi4. reflexivity. }
    { (* ---------------- |sx| >= 6: three bytes, then the next iteration ---------------- *)
      cbn [cae_k length Nat.min] in HS, Esx. cbn [length] in Hlen.
      assert (Hmlt : i + 4 < m) by lia.
      pose proof (Forall_inv Hsx64) as Hv0.
      pose proof (Forall_inv (Forall_inv_tail Hsx64)) as Hv1.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail Hsx64))) as Hv2.
      pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail Hsx64)))) as Hv3.
      pose proof (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail Hsx64)))) as Hsx'.
      cbv beta in Hv0, Hv1, Hv2, Hv3.
      assert (Hk4 : (2 <= cae_k (s4 :: s5 :: rest'') <= 4)%nat)
        by (unfold cae_k; cbn [length]; lia).
      assert (Hd4 : (i + 4) / 4 = i / 4 + 1)
        by (replace (i + 4) with (i + 1 * 4) by lia; rewrite Z.div_add by lia; reflexivity).
      assert (Hidiv' : (i + 4) / 4 <= m / 4) by (apply Z.div_le_mono; lia).
      assert (Hn6 : n + 6 <= Lwant) by lia.
      pose proof (Esx 0%nat ltac:(lia)) as E52. pose proof (Esx 1%nat ltac:(lia)) as E53.
      pose proof (Esx 2%nat ltac:(lia)) as E54. pose proof (Esx 3%nat ltac:(lia)) as E55.
      cbn [nth Nat.add] in E52, E53, E54, E55.
      assert (SHOK : sh_ok tfibsegs caw_Bx cae_SH E (mrestrict (w_H W) (ms_mem ms))).
      { unfold sh_ok, cae_SH. constructor; [|constructor; [|constructor]].
        - apply (cae_shent_of_ra E _ 48%nat (six + i + 4) six Lsix);
            [rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia
            | rewrite E48; apply unsigned_lit_small; lia | exact RA6 | exact Happ6 | lia | lia | lia].
        - apply (cae_shent_of_ra E _ 50%nat (want + n) want Lwant);
            [rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia
            | rewrite E50; apply unsigned_lit_small; lia | exact RAW | exact Happw | lia | lia | lia]. }
      assert (HSc : st_ok tfibsegs E (cae_ss 4 [Clt2; Clt1; Clt0]) (restrict (w_H W) ms)).
      { apply (cae_add3 E _ 4%nat Clt0 Clt1 Clt2 HS).
        - unfold acond_ok, Clt0. cbn [ac_c ac_a ac_b].
          rewrite branch_ltu_U, (U_atom_off E 47 (i + 4) 0 E47 ltac:(lia) ltac:(lia)),
                  (U_atom E 38 m E38 ltac:(lia)).
          apply Z.ltb_lt. lia.
        - unfold acond_ok, Clt1. cbn [ac_c ac_a ac_b].
          rewrite branch_ltu_U, (U_atom_off E 47 (i + 4) (-1) E47 ltac:(lia) ltac:(lia)),
                  (U_atom E 38 m E38 ltac:(lia)).
          apply Z.ltb_lt. lia.
        - unfold acond_ok, Clt2. cbn [ac_c ac_a ac_b].
          rewrite branch_ltu_U, (U_atom_off E 47 (i + 4) (-2) E47 ltac:(lia) ltac:(lia)),
                  (U_atom E 38 m E38 ltac:(lia)).
          apply Z.ltb_lt. lia. }
      clear HS.
      cae_run_tok caw_tbl_ok HSc HJ HARU SHOK caw_Bspan 73%N.
      { unfold caw_Bx. rewrite (U_atom E 32 SHADOW_OFF E32 ltac:(unfold SHADOW_OFF; lia)).
        rewrite (U_atom_off E 48 (six + i + 4) (-1) E48 ltac:(lia) ltac:(lia)).
        eapply range_addressable_sub; [exact RA6 | lia | lia]. }
      { unfold caw_Bx. rewrite (U_atom E 32 SHADOW_OFF E32 ltac:(unfold SHADOW_OFF; lia)).
        rewrite (U_atom_off E 48 (six + i + 4) (-2) E48 ltac:(lia) ltac:(lia)).
        eapply range_addressable_sub; [exact RA6 | lia | lia]. }
      { intros aa Haa. destruct Haa as (r & Hr & Hb). cbn [cae_ss cae_mem ss_mem In] in Hr.
        destruct Hr as [<-|[<-|[]]].
        - cbn [cae_six YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. exfalso. lia.
        - cbn [cae_out YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
          rewrite E50 in Hb. rewrite (unsigned_lit_small (want + n)) in Hb by lia.
          apply HAWR. cbn [Z.of_nat] in Hb. lia. }
      lazymatch type of HSc with st_ok _ ?EE _ _ => set (E1 := EE) in * end.
      assert (EQ : forall nn, (nn < 66)%nat -> ew E1 nn = ew E nn).
      { intros nn Hnn. unfold E1. repeat (rewrite ew_ewset_other by lia). reflexivity. }
      assert (Hb50 : bv_unsigned (ew E1 50) = want + n).
      { rewrite (EQ 50%nat ltac:(lia)), E50. apply unsigned_lit_small. lia. }
      assert (R11 : getr (ms_regs ms0) 11%bv = Z_to_bv 64 (i + 4 + 4)).
      { apply (cae_reg_val (w_H W) E1 _ ms0 11%bv 47 4 (i + 4) HSc ltac:(vm_compute; reflexivity)
                ltac:(rewrite (EQ 47%nat ltac:(lia)); exact E47) ltac:(lia) ltac:(lia)). }
      assert (R19 : getr (ms_regs ms0) 19%bv = Z_to_bv 64 (n + 3)).
      { apply (cae_reg_val (w_H W) E1 _ ms0 19%bv 49 3 n HSc ltac:(vm_compute; reflexivity)
                ltac:(rewrite (EQ 49%nat ltac:(lia)); exact E49) ltac:(lia) ltac:(lia)). }
      assert (U52 : U E1 (SOff 52 0) = s0).
      { unfold U. rewrite fsw_SOff0, (EQ 52%nat ltac:(lia)), E52. apply unsigned_lit_small. all: lia. }
      assert (U53 : U E1 (SOff 53 0) = s1).
      { unfold U. rewrite fsw_SOff0, (EQ 53%nat ltac:(lia)), E53. apply unsigned_lit_small. all: lia. }
      assert (U54 : U E1 (SOff 54 0) = s2).
      { unfold U. rewrite fsw_SOff0, (EQ 54%nat ltac:(lia)), E54. apply unsigned_lit_small. all: lia. }
      assert (U55 : U E1 (SOff 55 0) = s3).
      { unfold U. rewrite fsw_SOff0, (EQ 55%nat ltac:(lia)), E55. apply unsigned_lit_small. all: lia. }
      assert (Hd1 : 0 <= s1 / 16 < 4) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      assert (Hd2 : 0 <= s2 / 4 < 16) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      pose proof (fsw_region_nth E1 _ _ 1%nat _ HSc ltac:(vm_compute; reflexivity)) as HR.
      cbn [ms_mem restrict] in HR.
      assert (HBY0 : caw_at W (ms_mem ms0) (want + n) (s0 * 4 + s1 / 16)).
      { replace (want + n) with (want + n + 0) by lia.
        apply (cae_byte_at W E1 (ms_mem ms0) 50%nat (want + n) 0 (s0 * 4 + s1 / 16)
                 (SAlu ALU_OR (SAlu ALU_SRL (SOff 53 0) (SLit 4)) (SAlu ALU_SLL (SOff 52 0) (SLit 2)))
                 0 3 0 3 _ HR Hb50 ltac:(cbn [In]; tauto)).
        rewrite (cae_byte0 E1 (SOff 52 0) (SOff 53 0) s0 s1 U52 U53 ltac:(lia) ltac:(lia)). reflexivity. }
      assert (HBY1 : caw_at W (ms_mem ms0) (want + n + 1) ((s1 mod 16) * 16 + s2 / 4)).
      { apply (cae_byte_at W E1 (ms_mem ms0) 50%nat (want + n) 1 ((s1 mod 16) * 16 + s2 / 4)
                 (SAlu ALU_OR (SAlu ALU_SRL (SOff 54 0) (SLit 2)) (SAlu ALU_SLL (SOff 53 0) (SLit 4)))
                 0 3 0 3 _ HR Hb50 ltac:(cbn [In]; tauto)).
        rewrite (cae_byte1 E1 (SOff 53 0) (SOff 54 0) s1 s2 U53 U54 ltac:(lia) ltac:(lia)).
        replace (s1 * 16) with ((s1 mod 16) * 16 + (s1 / 16) * 256) by (Z.div_mod_to_equations; lia).
        replace ((s1 mod 16) * 16 + (s1 / 16) * 256 + s2 / 4)
           with ((s1 mod 16) * 16 + s2 / 4 + (s1 / 16) * 256) by lia.
        apply Z_mod_plus_full. }
      assert (HBY2 : caw_at W (ms_mem ms0) (want + n + 2) ((s2 mod 4) * 64 + s3)).
      { apply (cae_byte_at W E1 (ms_mem ms0) 50%nat (want + n) 2 ((s2 mod 4) * 64 + s3)
                 (SAlu ALU_OR (SAlu ALU_SLL (SOff 54 0) (SLit 6)) (SOff 55 0))
                 0 3 0 3 _ HR Hb50 ltac:(cbn [In]; tauto)).
        rewrite (cae_byte2 E1 (SOff 54 0) (SOff 55 0) s2 s3 U54 U55 ltac:(lia) ltac:(lia)).
        replace (s2 * 64) with ((s2 mod 4) * 64 + (s2 / 4) * 256) by (Z.div_mod_to_equations; lia).
        replace ((s2 mod 4) * 64 + (s2 / 4) * 256 + s3)
           with ((s2 mod 4) * 64 + s3 + (s2 / 4) * 256) by lia.
        apply Z_mod_plus_full. }
      assert (HFR : forall x : word, ~ (want + n <= bv_unsigned x < want + n + 3) ->
                     ms_mem ms0 x = ms_mem ms x).
      { intros x Hx. apply HF. intros (r & Hr & Hb). cbn [cae_ss cae_mem ss_mem In] in Hr.
        destruct Hr as [<-|[<-|[]]].
        - cbn [cae_six YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. lia.
        - cbn [cae_out YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb.
          rewrite E50 in Hb. rewrite (unsigned_lit_small (want + n)) in Hb by lia.
          apply Hx. cbn [Z.of_nat] in Hb. lia. }
      assert (HB6ms0 : caw_bytes W (ms_mem ms0) (six + i) (s0 :: s1 :: s2 :: s3 :: s4 :: s5 :: rest'')).
      { apply (cae_bytes_frame W (ms_mem ms) (ms_mem ms0) (six + i) (want + n) (want + n + 3)
                 (s0 :: s1 :: s2 :: s3 :: s4 :: s5 :: rest'') HB6 HFR);
          [lia | cbn [length]; lia
          | cbn [length]; destruct Hdisj as [X|X]; [left; lia | right; lia]]. }
      assert (HB6' : caw_bytes W (ms_mem ms0) (six + (i + 4)) (s4 :: s5 :: rest'')).
      { intros j Hj. specialize (HB6ms0 (4 + j)%nat ltac:(cbn [length] in Hj |- *; lia)).
        cbn [nth Nat.add] in HB6ms0.
        replace (six + (i + 4) + Z.of_nat j) with (six + i + Z.of_nat (4 + j)) by lia.
        exact HB6ms0. }
      set (LD := [getr (ms_regs ms0) 11%bv; Z_to_bv 64 (six + (i + 4) + 4); getr (ms_regs ms0) 19%bv;
         Z_to_bv 64 (want + (n + 3)); Z_to_bv 64 (six + (i + 4) + 5);
         Z_to_bv 64 (nth 0 (s4 :: s5 :: rest'') 0); Z_to_bv 64 (nth 1 (s4 :: s5 :: rest'') 0);
         Z_to_bv 64 (nth 2 (s4 :: s5 :: rest'') 0); Z_to_bv 64 (nth 3 (s4 :: s5 :: rest'') 0);
         getr (ms_regs ms0) 5%bv; getr (ms_regs ms0) 6%bv; getr (ms_regs ms0) 7%bv;
         getr (ms_regs ms0) 12%bv; getr (ms_regs ms0) 17%bv; getr (ms_regs ms0) 28%bv;
         getr (ms_regs ms0) 29%bv; getr (ms_regs ms0) 30%bv; getr (ms_regs ms0) 31%bv;
         getr (ms_regs ms0) 16%bv]).
      set (E2 := extK E1 47 LD).
      assert (EL : forall j, (j < 19)%nat -> ew E2 (47 + j) = nth j LD (Z_to_bv 64 0)).
      { intros j Hj. unfold E2. apply cae_ext_lookup. unfold LD. cbn [length]. lia. }
      assert (HAG : env_agree 47 E E2).
      { split.
        - intros nn Hnn. unfold E2. rewrite (proj1 (env_agree_extK E1 47 LD) nn Hnn).
          exact (EQ nn ltac:(lia)).
        - unfold E2. rewrite (proj2 (env_agree_extK E1 47 LD)). unfold E1. reflexivity. }
      assert (A47 : ew E2 47 = Z_to_bv 64 (i + 4 + 4)).
      { change 47%nat with (47 + 0)%nat. rewrite (EL 0%nat ltac:(lia)). unfold LD. cbn [nth]. exact R11. }
      assert (A48 : ew E2 48 = Z_to_bv 64 (six + (i + 4) + 4)).
      { change 48%nat with (47 + 1)%nat. rewrite (EL 1%nat ltac:(lia)). unfold LD. cbn [nth]. reflexivity. }
      assert (A49 : ew E2 49 = Z_to_bv 64 (n + 3)).
      { change 49%nat with (47 + 2)%nat. rewrite (EL 2%nat ltac:(lia)). unfold LD. cbn [nth]. exact R19. }
      assert (A50 : ew E2 50 = Z_to_bv 64 (want + (n + 3))).
      { change 50%nat with (47 + 3)%nat. rewrite (EL 3%nat ltac:(lia)). unfold LD. cbn [nth]. reflexivity. }
      assert (A51 : ew E2 51 = Z_to_bv 64 (six + (i + 4) + 5)).
      { change 51%nat with (47 + 4)%nat. rewrite (EL 4%nat ltac:(lia)). unfold LD. cbn [nth]. reflexivity. }
      assert (A52 : ew E2 52 = Z_to_bv 64 (nth 0 (s4 :: s5 :: rest'') 0)).
      { change 52%nat with (47 + 5)%nat. rewrite (EL 5%nat ltac:(lia)). unfold LD. cbn [nth]. reflexivity. }
      assert (A53 : ew E2 53 = Z_to_bv 64 (nth 1 (s4 :: s5 :: rest'') 0)).
      { change 53%nat with (47 + 6)%nat. rewrite (EL 6%nat ltac:(lia)). unfold LD. cbn [nth]. reflexivity. }
      assert (A54 : ew E2 54 = Z_to_bv 64 (nth 2 (s4 :: s5 :: rest'') 0)).
      { change 54%nat with (47 + 7)%nat. rewrite (EL 7%nat ltac:(lia)). unfold LD. cbn [nth]. reflexivity. }
      assert (A55 : ew E2 55 = Z_to_bv 64 (nth 3 (s4 :: s5 :: rest'') 0)).
      { change 55%nat with (47 + 8)%nat. rewrite (EL 8%nat ltac:(lia)). unfold LD. cbn [nth]. reflexivity. }
      assert (A33 : ew E2 33 = Z_to_bv 64 six)
        by (rewrite (proj1 HAG 33%nat ltac:(lia)); exact E33).
      assert (A34 : ew E2 34 = Z_to_bv 64 want)
        by (rewrite (proj1 HAG 34%nat ltac:(lia)); exact E34).
      assert (RA6' : range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms0))) SHADOW_OFF six Lsix).
      { apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) six Lsix (want + n) (want + n + 3) RA6 HFR);
          [lia | destruct Happw as [_ [X|[X _]]]; [left; lia | right; lia] | lia | unfold CAW_CEIL; lia]. }
      assert (RAW' : range_addressable (rd_of tfibsegs (mrestrict (w_H W) (ms_mem ms0))) SHADOW_OFF want Lwant).
      { apply (cae_ra_keep W (ms_mem ms) (ms_mem ms0) want Lwant (want + n) (want + n + 3) RAW HFR);
          [lia | destruct Happw as [_ [X|[X _]]]; [left; lia | right; lia] | lia | unfold CAW_CEIL; lia]. }
      assert (HWR' : forall a, want <= a < want + Lwant ->
                       writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms0)) a).
      { intros a Ha. apply (wview_grows tfibsegs _ _ _ HG). apply HWR. exact Ha. }
      assert (HSN : st_ok tfibsegs E2 (cae_ss (cae_k (s4 :: s5 :: rest'')) [])
                      (restrict (w_H W) ms0)).
      { apply (cae_head_st W E1 E2 ms0 _ (cae_k (s4 :: s5 :: rest'')) (s4 :: s5 :: rest'')
                 six want (i + 4) (n + 3) HSc).
        - vm_compute; reflexivity.
        - vm_compute; reflexivity.
        - unfold E2. apply env_agree_extK.
        - apply Forall_forall. intros rj Hin. vm_compute in Hin.
          repeat (destruct Hin as [<-|Hin]); [..|destruct Hin]; cbn [fst snd]; cae_lk EL LD.
        - exact A33.
        - exact A34.
        - exact A47.
        - exact A48.
        - exact A49.
        - exact A50.
        - exact A51.
        - exact A52.
        - exact A53.
        - exact A54.
        - exact A55.
        - exact Hsx'.
        - lia.
        - lia.
        - lia.
        - lia.
        - unfold CAW_CEIL in *. lia.
        - lia.
        - unfold CAW_CEIL in *. lia.
        - cbn [ms_mem restrict].
          apply (cae_mem_ok (cae_k (s4 :: s5 :: rest'')) E2 _ (six + (i + 4)) (want + (n + 3))
                   (s4 :: s5 :: rest'')).
          + exact Hk4.
          + unfold cae_k. cbn [length]. lia.
          + rewrite A51. apply unsigned_lit_small. unfold CAW_CEIL in *. lia.
          + rewrite A50. apply unsigned_lit_small. unfold CAW_CEIL in *. lia.
          + intros j Hj. destruct j as [|[|[|[|j]]]]; cbn [Nat.add];
              [exact A52 | exact A53 | exact A54 | exact A55 | exfalso; lia].
          + exact Hsx'.
          + intros j Hj. apply HB6'. unfold cae_k in Hj. cbn [length] in Hj |- *. lia.
          + intros o Ho. apply HWR'. lia.
          + lia.
          + unfold CAW_CEIL in *. lia.
          + lia.
          + unfold CAW_CEIL in *. lia.
          + lia. }
      eapply (IH (s4 :: s5 :: rest'')
                 (done ++ [s0 * 4 + s1 / 16; (s1 mod 16) * 16 + s2 / 4; (s2 mod 4) * 64 + s3])
                 E2 ms0 _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc Up W kj six want Lsix Lwant m
                 (i + 4) (n + 3)).
      { cbn [length] in HL |- *. lia. }
      { exact HSN. }
      { exact HJ. }
      { exact HARU. }
      { rewrite (proj1 HAG 32%nat ltac:(lia)). exact E32. }
      { exact A33. }
      { exact A34. }
      { rewrite (proj1 HAG 38%nat ltac:(lia)). exact E38. }
      { exact A47. }
      { exact A48. }
      { exact A49. }
      { exact A50. }
      { exact A51. }
      { intros j Hj. destruct j as [|[|[|[|j]]]]; cbn [Nat.add];
          [exact A52 | exact A53 | exact A54 | exact A55
          | exfalso; unfold cae_k in Hj; cbn [length] in Hj; lia]. }
      { exact Hsx'. }
      { cbn [length] in Hlen |- *. lia. }
      { rewrite length_app. cbn [length]. lia. }
      { lia. }
      { rewrite Zplus_mod, Hi4. reflexivity. }
      { exact Hm4. }
      { lia. }
      { lia. }
      { exact Happ6. }
      { exact Happw. }
      { lia. }
      { lia. }
      { exact Hdisj. }
      { exact RA6'. }
      { exact RAW'. }
      { exact HWR'. }
      { exact HAWR. }
      { exact HB6'. }
      { apply cae_bytes_app.
        - apply (cae_bytes_frame W (ms_mem ms) (ms_mem ms0) want (want + n) (want + n + 3) done HBd HFR);
            lia.
        - intros j Hj. cbn [length] in Hj.
          destruct j as [|[|[|j]]]; [| | |exfalso; lia]; cbn [nth Z.of_nat]; rewrite Hdlen.
          + rewrite Z.add_0_r. exact HBY0.
          + exact HBY1.
          + exact HBY2. }
      { intros E3 ms3 mdc3 HAG3 HSX3 E3_49 HJ3 HARU3 HB3 HFR3 HG3 RA63 RAW3.
        apply (HK E3 ms3 mdc3).
        { split.
          - intros nn Hnn. rewrite (proj1 HAG3 nn Hnn). exact (proj1 HAG nn Hnn).
          - rewrite (proj2 HAG3). exact (proj2 HAG). }
        { exact HSX3. }
        { rewrite caw_six_bytes_4. cbn [length]. rewrite E3_49. f_equal. lia. }
        { exact HJ3. }
        { exact HARU3. }
        { rewrite caw_six_bytes_4. rewrite <- app_assoc in HB3. cbn [app] in HB3. exact HB3. }
        { rewrite caw_six_bytes_4. cbn [length]. intros x Hx.
          assert (H1 : ~ (want + (n + 3) <= bv_unsigned x
                          < want + (n + 3) + Z.of_nat (length (WS.six_bytes (s4 :: s5 :: rest''))))) by lia.
          rewrite (HFR3 x H1). apply HFR. lia. }
        { apply (mem_grows_trans _ (mrestrict (w_H W) (ms_mem ms0))); [exact HG | exact HG3]. }
        { exact RA63. }
        { exact RAW3. } } } } }
Qed.

End W.
(* caw_emit_loop above is this file's only theorem; the walk of the rest of check_as_written is a Theorem Labs lane's. *)
