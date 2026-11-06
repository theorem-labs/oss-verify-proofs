(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new for plugin-hostd/fuzz_reply.asan (R2Cmp, port-reply): the body walk of the
   strrchr interceptor, in the tree's own words (lib/A/Bz), composed from I_pck.v internal_strlen_spec, I_strlen.v
   istrlen_spec, R_small.v / I_ikit.v (the init gate) and I_consts.v rip_stmt. No other pinned binary has this code
   (EvBound), so it is written new, in the form of I_strlen.v / I_strlenw.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/Bz/A/I_strrchr.v, with its module paths, addresses and numbers changed; 261 of its 397 lines of code are new or changed and 235 lines of the source are left out. *)
(* Ported by RtStr from cold/c-asan-rt-fmio-n affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/I_strchrw.v, unchanged. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit IcptSpec
  D_kit I_ikit I_tramp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Notation ISTRCHR_DEPTH := 2224%Z (only parsing).

Lemma tramp_strchr : tramp_step 0x43a28 0x45ae4. Proof. tramp_proof. Qed.

Definition chr_idx (c : Z) (str : list byte) : nat :=
  match find_byte c str with Some i => i | None => length str end.

Definition chr_res (A c : Z) (str : list byte) : Z :=
  match find_byte c str with Some i => A + Z.of_nat i | None => 0 end.

Definition chr_n (A c : Z) (str : list byte) : Z :=
  if chr_res A c str =? 0 then Z.of_nat (length str) + 1 else chr_res A c str - A + 1.

Lemma chr_idx_le : forall c str, (chr_idx c str <= length str)%nat.
Proof.
  intros c str. unfold chr_idx. destruct (find_byte c str) as [i|] eqn:E; [|lia].
  destruct (find_byte_Some _ _ _ E) as (Hi & _ & _). lia.
Qed.

Lemma chr_n_ge : forall A c str, Z.of_nat (chr_idx c str) + 1 <= chr_n A c str.
Proof.
  intros A c str. pose proof (chr_idx_le c str) as L. unfold chr_n, chr_res, chr_idx in *.
  destruct (find_byte c str) as [i|] eqn:E.
  - destruct (Z.eqb_spec (A + Z.of_nat i) 0); lia.
  - cbn. lia.
Qed.

Lemma chr_n_le : forall A c str, chr_n A c str <= Z.of_nat (length str) + 1.
Proof.
  intros A c str. unfold chr_n, chr_res.
  destruct (find_byte c str) as [i|] eqn:E.
  - destruct (find_byte_Some _ _ _ E) as (Hi & _ & _). destruct (Z.eqb_spec (A + Z.of_nat i) 0); lia.
  - cbn. lia.
Qed.

Lemma pad_mono : forall s x y, x + 1 <= y -> x + 1 + (- (s + x + 1)) mod 8 <= y + (- (s + y)) mod 8.
Proof. intros s x y H. Z.div_mod_to_equations. lia. Qed.

Lemma pad_mono2 : forall s x y, x <= y -> x + (- (s + x)) mod 8 <= y + (- (s + y)) mod 8.
Proof. intros s x y H. Z.div_mod_to_equations. lia. Qed.

Lemma nth_firstn_pref : forall (l : list byte) L j, (j < length (firstn L l))%nat -> nth_error (firstn L l) j = nth_error l j.
Proof.
  intros l L j Hj. transitivity (nth_error (firstn L l ++ skipn L l) j).
  - rewrite nth_error_app1 by exact Hj. reflexivity.
  - rewrite firstn_skipn. reflexivity.
Qed.

Lemma firstn_cstr : forall (str slack : list byte) L, (length str < L)%nat ->
  firstn L (str ++ Z_to_bv 8 0 :: slack) = str ++ Z_to_bv 8 0 :: firstn (L - S (length str)) slack.
Proof.
  intros str slack L H. rewrite firstn_app, firstn_all2 by lia.
  destruct (L - length str)%nat as [|k] eqn:E; [lia|]. cbn [firstn].
  replace (L - S (length str))%nat with k by lia. reflexivity.
Qed.

Lemma cstr_byte : forall (str rest : list byte) j, ~ In (Z_to_bv 8 0) str -> 0 <= j <= Z.of_nat (length str) ->
  exists b, nth_error (str ++ Z_to_bv 8 0 :: rest) (Z.to_nat j) = Some b /\ (bv_unsigned b = 0 <-> j = Z.of_nat (length str)).
Proof.
  intros str rest j NZ Hj. destruct (Z.eq_dec j (Z.of_nat (length str))) as [->|NE].
  - exists (Z_to_bv 8 0). rewrite Nat2Z.id, nth_error_app2, Nat.sub_diag by lia.
    split; [reflexivity|]. split; intros; reflexivity.
  - destruct (nth_error str (Z.to_nat j)) as [b|] eqn:E; [| apply nth_error_None in E; lia].
    exists b. rewrite nth_error_app1 by lia. split; [exact E|]. split; [|lia].
    intros Hb. exfalso. apply NZ. replace (Z_to_bv 8 0) with b; [eapply nth_error_In; exact E|].
    apply bv_eq. rewrite Hb. reflexivity.
Qed.

Lemma iislen_loop : forall (k : nat) (j s : Z) (str rest : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  Z.of_nat (length str) - j = Z.of_nat k -> 0 <= j -> s + Z.of_nat (length str) + 1 < 2^64 ->
  bytes_at asegs m s (str ++ Z_to_bv 8 0 :: rest) -> ~ In (Z_to_bv 8 0) str -> mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.of_nat (length str)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) (Z_to_bv 64 j) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x68364) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros j s str rest ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Hk Hj HS BUF NZ MI;
  ( destruct (cstr_byte str rest j NZ ltac:(lia)) as (b & Hn & Hz);
    pose proof (bytes_at_nth1 asegs m s _ _ _ BUF Hn) as BX; rewrite Z2Nat.id in BX by lia;
    pose proof (ro_C1_of_bytes m _ _ BX) as CX;
    pose proof (bytes_at_bound _ _ _ _ BUF) as BB; rewrite length_app in BB; cbn [length] in BB;
    pose proof (byte_range b) as BR;
    pose proof (munch_refl [] m) as MU; pose proof (wmono_refl asegs m) as WM;
    assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia);
    assert (EUj : bv_unsigned (Z_to_bv 64 j) = j) by (apply unsigned_lit; lia);
    assert (EUj1 : bv_unsigned (Z_to_bv 64 (j + 1)) = j + 1) by (apply unsigned_lit; lia);
    assert (EUb : bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b) by (apply unsigned_lit; lia);
    lstep; set (q := s + j) in *; lstep; lstep; lstep;
    if_cases K; zify_cond K; rewrite ?EUb in K; try change (bv_unsigned (Z_to_bv 64 0)) with 0 in K).
  - exfalso. assert (bv_unsigned b = 0) by (apply Hz; lia). lia.
  - lstep. lstep. assert (Ej : j = Z.of_nat (length str)) by lia. rewrite Ej. finish.
  - apply (IH (j + 1) s str rest); [lia| lia| exact HS| exact BUF| exact NZ| exact MI].
  - exfalso. assert (j = Z.of_nat (length str)) by (apply Hz; lia). lia.
Qed.

Lemma iislen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s : Z) (str rest : list byte),
  a0 = Z_to_bv 64 s -> bytes_at asegs m s (str ++ Z_to_bv 8 0 :: rest) -> s + Z.of_nat (length str) + 1 < 2^64 ->
  ~ In (Z_to_bv 8 0) str -> mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.of_nat (length str)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x68360) fc None m (seg_rom asegs)).
Proof.
  intros until rest. intros -> BUF HS NZ MI.
  lstep.
  apply (iislen_loop (length str) 0 s str rest); [lia| lia| exact HS| exact BUF| exact NZ| exact MI].
Qed.

Definition chr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (str full : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (chr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str))
                  a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ bytes_at asegs m' (bv_unsigned a0) full.

Definition chr_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (str slack full : list byte) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  bytes_at asegs m (bv_unsigned a0) full ->
  (forall j, (j < length full)%nat -> nth_error full j = nth_error (str ++ Z_to_bv 8 0 :: slack) j) ->
  ~ In (Z_to_bv 8 0) str ->
  Z.of_nat (chr_idx (bv_unsigned a1 mod 256) str) + 1
    + (- (bv_unsigned a0 + Z.of_nat (chr_idx (bv_unsigned a1 mod 256) str) + 1)) mod 8 <= Z.of_nat (length full) ->
  mem_inv asegs m ->
  0 < bv_unsigned a1 mod 256 ->
  lo <= bv_unsigned sp - 32 ->
  (bv_unsigned a0 + Z.of_nat (length full) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0) ->
  bv_unsigned sp <= 2^47 ->
  evt asegs (chr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str full lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9a9d4) fc None m (seg_rom asegs)).

Definition icells_chr (m : mem) : Prop :=
  ro_cells asegs m 0xa2a40 [C8 (Z_to_bv 64 0x13db28)]
  /\ ro_cells asegs m 0xa2a50 [C8 (Z_to_bv 64 0xabff8)]
  /\ ro_cells asegs m 0xabff8 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ rw_cells asegs m 0xaccd8 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0xa4780 [C8 (Z_to_bv 64 0x9a9d4)]
  /\ ro_cells asegs m 0x13dc1d [C1 (Z_to_bv 8 0)]
  /\ ro_cells asegs m 0x13dc25 [C1 (Z_to_bv 8 1)].

Lemma istrchr_loop : forall (k : nat) (c e : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (a3' a4' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 e) (Z_to_bv 64 e) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x45cd8) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 c) (Z_to_bv 64 e) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x45cc8) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros c e ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    Hk Hc He HB MI.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_false.
    apply evt_done. do 2 eexists. replace e with (c + 1) by lia. reflexivity.
  - destruct (HB c ltac:(lia)) as (b & Hb). pose proof (ro_C1_of_bytes m c b Hb) as CB0.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EUc : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
    assert (EUe : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
    assert (EUc1 : bv_unsigned (Z_to_bv 64 (c + 1)) = c + 1) by (apply unsigned_lit; lia).
    do 3 lstep. lstep. if_true.
    apply (IH (c + 1) e); [lia| lia| lia| intros x Hx; apply HB; lia| assumption].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.
Hypothesis SC : chr_stmt.

Lemma istrchr_rip : forall (sp p r : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2144) -> lo <= sp - ISTRCHR_DEPTH -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 <= r -> p + r + 1 < 2^63 ->
  acc asegs m p (r + 1) -> rng_ok p (r + 1) -> m2s_cells m -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 s1' a0 a1' a2' a3' a4' a5' a6' a7'
                    s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x45c08) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (r + 1)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x45ce0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST LO LOLO SPH D0 N0 DN AC RO M2S MI.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUsp : bv_unsigned (Z_to_bv 64 (sp + -2144)) = sp + -2144) by (apply unsigned_lit; unfold kHighShadowEnd in *; lia).
  destruct (RO ltac:(lia)) as (RIM & N40).
  do 4 lstep.
  pose proof RIP as RIPs. unfold rip_stmt in RIPs.
  call RIPs; [reflexivity| reflexivity| exact AC| lia| exact RIM| exact M2S| rewrite EUsp; exact ST| lia| unfold kHighShadowEnd in *; lia
             | assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EUsp in H; rename H into ST1 end.
  lstep. lstep. lstep. if_true.
  apply evt_done. do 22 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST1].
Qed.

Lemma istrchr_chk : forall (sp p r : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  s0 = Z_to_bv 64 sp ->
  stk asegs m lo (sp + -2144) -> lo <= sp - ISTRCHR_DEPTH -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 <= r -> p + r + 1 < 2^63 ->
  chk_ok m p (r + 1) -> m2s_cells m -> ro_cells asegs m 0xa2a50 [C8 (Z_to_bv 64 0xabff8)] ->
  ro_cells asegs m 0xabff8 [C8 (Z_to_bv 64 0x7fff8000)] -> mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem) (ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' : word),
      ms' = MS (mkR ra' (Z_to_bv 64 (sp + -2144)) gp tp t0' t1' t2' s0 s1' a0 a1' a2' a3' a4' a5' a6' a7'
                    s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 0x45c08) fc None m' (seg_rom asegs)
      /\ munch [(sp - 2224, sp - 2144)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (sp + -2144))
    (MS (mkR ra (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p) (Z_to_bv 64 r) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x45bb4) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros -> ST LO LOLO SPH D0 N0 DN (AC & QW & RO) M2S G2 SHC MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  assert (EUr1 : bv_unsigned (Z_to_bv 64 (r + 1)) = r + 1) by (apply unsigned_lit; lia).
  lstep. lstep. rewrite (lxor_ones64 p) by lia.
  assert (EUnp : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p)) = 18446744073709551615 - p) by (apply unsigned_lit; lia).
  lstep. lstep. lstep. if_false. lstep. lstep.
  destruct (Z_lt_le_dec r 64) as [SMALL|BIG].
  - if_false.
    destruct (QW ltac:(lia)) as (w1 & w2 & W1 & W2).
    do 10 lstep.
    unfold al8, shad, SHB in W1, W2.
    assert (E1 : Z.land ((2147450880 + p ≫ 3) mod 18446744073709551616) 18446744073709551608 = 8 * ((p / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
    assert (E2 : Z.land ((2147450880 + (r + p) ≫ 3) mod 18446744073709551616) 18446744073709551608
                 = 8 * (((p + (r + 1) - 1) / 8 + 2147450880) / 8)).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
      rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. replace (p + (r + 1) - 1) with (r + p) by lia. lia. }
    rewrite E1, E2. clear E1 E2.
    lstep. lstep. lstep. lstep.
    if_cases K.
    + rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      replace (2147450880 + (r + p) / 8) with ((p + (r + 1) - 1) / 8 + 2147450880) by (replace (p + (r + 1) - 1) with (r + p) by lia; lia).
      replace (2147450880 + p / 8) with (p / 8 + 2147450880) by lia.
      pose proof (acc_shadow_bytes m p (r + 1) AC ltac:(lia) D0) as SB. unfold shad, SHB in SB.
      destruct (SB ((p + (r + 1) - 1) / 8 + 2147450880)) as (bl & BL); [Z.div_mod_to_equations; lia|].
      pose proof (ro_C1_of_bytes _ _ _ BL) as CL.
      do 6 lstep. lstep.
      if_cases K2.
      * lstep. lstep. if_cases K3.
        -- apply evt_done. do 22 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (istrchr_rip sp p r); try assumption; lia.
      * zify_cond K2.
        eapply evt_cut.
        { eapply (istrchr_loop (Z.to_nat ((p + (r + 1) - 1) / 8 + 2147450880 - (p / 8 + 2147450880) - 1))).
          - rewrite Nat2Z.inj_succ, Z2Nat.id by (Z.div_mod_to_equations; lia). lia.
          - Z.div_mod_to_equations; lia.
          - Z.div_mod_to_equations; lia.
          - intros x Hx. apply SB. Z.div_mod_to_equations; lia.
          - assumption. }
        intros ms' (a3' & a4' & ->).
        lstep. lstep. if_cases K3.
        -- apply evt_done. do 22 eexists. split; [reflexivity|].
           split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        -- apply (istrchr_rip sp p r); try assumption; lia.
    + apply evt_done. do 22 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  - if_true. lstep. if_true.
    apply (istrchr_rip sp p r); try assumption; lia.
Qed.

Definition istrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - ISTRCHR_DEPTH, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Theorem istrchr_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s : Z) (str slack : list byte) (L : nat) (lo : Z),
  a0 = Z_to_bv 64 s ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRCHR_DEPTH -> kHighShadowEnd < lo -> bv_unsigned sp <= 2^47 ->
  0 <= s -> s + Z.of_nat L <= 2^47 ->
  bytes_at asegs m s (firstn L (str ++ Z_to_bv 8 0 :: slack)) -> ~ In (Z_to_bv 8 0) str ->
  (L <= length str + S (length slack))%nat ->
  0 < bv_unsigned a1 mod 256 ->
  chr_n s (bv_unsigned a1 mod 256) str + (- (s + chr_n s (bv_unsigned a1 mod 256) str)) mod 8 <= Z.of_nat L ->
  (s + Z.of_nat L <= bv_unsigned sp - ISTRCHR_DEPTH \/ bv_unsigned sp <= s) ->
  chk_ok m s (chr_n s (bv_unsigned a1 mod 256) str) -> m2s_cells m -> icells_chr m -> mem_inv asegs m ->
  evt asegs (istrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (chr_res s (bv_unsigned a1 mod 256) str) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x45ae4) fc None m (seg_rom asegs)).
Proof using RIP SC.
  intros until lo. intros -> ST LO LOLO SPH S0 SL BUF NZ LL CP LN SEPS CS M2S IC MI.
  unfold kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - 2224, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof IC as (G70 & G2 & SHC & AI & RS & F5 & F3).
  remember (firstn L (str ++ Z_to_bv 8 0 :: slack)) as full eqn:Efull.
  assert (LF : length full = L) by (rewrite Efull, length_firstn, length_app; cbn [length]; lia).
  assert (PREF : forall j, (j < length full)%nat -> nth_error full j = nth_error (str ++ Z_to_bv 8 0 :: slack) j)
    by (rewrite Efull; apply nth_firstn_pref).
  pose proof (chr_n_ge s (bv_unsigned a1 mod 256) str) as NG.
  pose proof (chr_idx_le (bv_unsigned a1 mod 256) str) as IL.
  pose proof (Z.mod_pos_bound (- (s + chr_n s (bv_unsigned a1 mod 256) str)) 8 ltac:(lia)) as PB.
  pose proof (pad_mono s (Z.of_nat (chr_idx (bv_unsigned a1 mod 256) str)) (chr_n s (bv_unsigned a1 mod 256) str) NG) as PM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EU2144 : bv_unsigned (Z_to_bv 64 (usp + -2144)) = usp + -2144) by (apply unsigned_lit; lia).
  carve_frame 72%nat ST. rename FR into FRs. carve_frame 2072%nat ST.
  do 15 lstep.
  call asan_inited_spec; [exact AI| assumption|].
  lstep. if_false. lstep.
  call try_init_spec; [exact AI| rewrite EU2144; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2144 in H; rename H into ST2 end.
  do 6 lstep.
  call SC; [rewrite EU2144; exact ST2
           | rewrite EUs; exact BUF
           | exact PREF
           | exact NZ
           | rewrite EUs, LF; lia
           | assumption
           | exact CP
           | rewrite EU2144; lia
           | rewrite EUs, EU2144, LF; lia
           | rewrite EU2144; lia
           |].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2144 in H; rename H into ST3 end.
  lazymatch goal with H : bytes_at asegs _ (bv_unsigned (Z_to_bv 64 s)) _ |- _ => rewrite EUs in H; rename H into BUF1 end.
  rewrite EUs.
  lstep. if_false.
  do 3 lstep. lstep. if_false.
  lstep. lstep. if_false.
  lstep.
  destruct (Z.eq_dec (chr_res s (bv_unsigned a1 mod 256) str) 0) as [Er|Ern].
  2:{
    destruct (find_byte (bv_unsigned a1 mod 256) str) as [i|] eqn:FB;
      [| exfalso; apply Ern; unfold chr_res; rewrite FB; reflexivity].
    destruct (find_byte_Some _ _ _ FB) as (Hi & _ & _).
    assert (Er : chr_res s (bv_unsigned a1 mod 256) str = s + Z.of_nat i) by (unfold chr_res; rewrite FB; reflexivity).
    assert (NZr : s + Z.of_nat i <> 0) by congruence.
    assert (EN : chr_n s (bv_unsigned a1 mod 256) str = Z.of_nat i + 1)
      by (unfold chr_n; rewrite Er, (proj2 (Z.eqb_neq _ _) NZr); lia).
    rewrite EN in CS, LN, PB, NG.
    rewrite Er.
    assert (EUr : bv_unsigned (Z_to_bv 64 (s + Z.of_nat i)) = s + Z.of_nat i) by (apply unsigned_lit; lia).
    if_false.
    lstep. lstep.
    replace (s + Z.of_nat i - s) with (Z.of_nat i) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (CS1 : chk_ok mm s (Z.of_nat i + 1))
        by (apply (chk_ok_agree m mm s _ CS ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside];
            split; [lia| exact I]);
      assert (M2S1 : m2s_cells mm) by (destruct M2S as (M1 & M2 & M3); split; [| split];
        [ apply (rw_cells_agree asegs m mm _ _ M1); [| assumption]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
        | apply (rw_cells_agree asegs m mm _ _ M2); [| assumption]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
        | apply (rw_cells_agree asegs m mm _ _ M3); [| assumption]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia ])
    end.
    call (istrchr_chk usp s (Z.of_nat i)); [reflexivity| exact ST3| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia
          | exact CS1| exact M2S1| exact G2| exact SHC| assumption|].
    lazymatch goal with H : stk asegs _ lo (usp + -2144) |- _ => rename H into ST4 end.
    do 11 lstep.
    release_frame FR ST4 (usp + -72). release_frame FRs ST4 usp.
    lstep.
    unfold istrchr_post. sys_finish.
    + rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
    + rewrite EU. assumption.
  }
  assert (EN : chr_n s (bv_unsigned a1 mod 256) str = Z.of_nat (length str) + 1) by (unfold chr_n; rewrite Er; reflexivity).
  rewrite EN in CS, LN, PB, NG.
  rewrite Er.
  if_true.
  rewrite Efull, (firstn_cstr str slack L ltac:(lia)) in BUF1.
  lstep. lstep. lstep.
  call iislen_spec; [reflexivity| exact BUF1| lia| exact NZ| assumption|].
  lstep. lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CS1 : chk_ok mm s (Z.of_nat (length str) + 1))
      by (apply (chk_ok_agree m mm s _ CS ltac:(lia) ltac:(lia)); apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside];
          split; [lia| exact I]);
    assert (M2S1 : m2s_cells mm) by (destruct M2S as (M1 & M2 & M3); split; [| split];
      [ apply (rw_cells_agree asegs m mm _ _ M1); [| assumption]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
      | apply (rw_cells_agree asegs m mm _ _ M2); [| assumption]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
      | apply (rw_cells_agree asegs m mm _ _ M3); [| assumption]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia ])
  end.
  call (istrchr_chk usp s (Z.of_nat (length str))); [reflexivity| exact ST3| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia
        | exact CS1| exact M2S1| exact G2| exact SHC| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2144) |- _ => rename H into ST4 end.
  do 11 lstep.
  release_frame FR ST4 (usp + -72). release_frame FRs ST4 usp.
  lstep.
  unfold istrchr_post. sys_finish.
  + rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
  + rewrite EU. assumption.
Qed.

End WithRIP.
