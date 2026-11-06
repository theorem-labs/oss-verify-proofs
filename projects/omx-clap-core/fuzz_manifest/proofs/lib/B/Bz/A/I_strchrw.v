(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Bz/A/I_strchrw.v: the same statements and proofs, with the module paths and image addresses of the asan-ubsan build. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit IcptSpec
  D_kit I_ikit I_tramp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Abbreviation ISTRCHR_DEPTH := 2224%Z (only parsing).

Local Abbreviation NUL := (Z_to_bv 8 0) (only parsing).
Local Abbreviation w64 z := (Z_to_bv 64 z) (only parsing).
Local Abbreviation ms_at R F pc fc m := (MS R F pc fc None m (seg_rom asegs)) (only parsing).




Lemma tramp_strchr : tramp_step 0x41340 0x42ee8.
Proof.
  unfold tramp_step. intros until m. intro at_body.
  (* one [jal zero] to the interceptor body *)
  lstep. exact at_body.
Qed.

Definition chr_idx (c : Z) (str : list byte) :=
  match find_byte c str with
  | Some i => i
  | None => length str
  end.

Definition chr_res (A : Z) (c : Z) (str : list byte) : Z :=
  match find_byte c str with
  | Some i => A + Z.of_nat i
  | None => 0
  end.

Definition chr_n (A : Z) (c : Z) (str : list byte) : Z :=
  if chr_res A c str =? 0
  then Z.of_nat (length str) + 1
  else chr_res A c str - A + 1.

Lemma chr_idx_le (c : Z) (str : list byte) : (chr_idx c str <= length str)%nat.
Proof.
  unfold chr_idx.
  destruct (find_byte c str) as [i|] eqn:look; [|lia].
  destruct (find_byte_Some _ _ _ look) as [below _]. lia.
Qed.

Lemma chr_n_ge (A c : Z) (str : list byte) : Z.of_nat (chr_idx c str) + 1 <= chr_n A c str.
Proof.
  unfold chr_n, chr_res, chr_idx.
  destruct (find_byte c str) as [i|] eqn:look.
  - destruct (find_byte_Some _ _ _ look) as [below _].
    destruct (A + Z.of_nat i =? 0); lia.
  - rewrite Z.eqb_refl. lia.
Qed.

Lemma chr_n_le (A c : Z) (str : list byte) : chr_n A c str <= Z.of_nat (length str) + 1.
Proof.
  unfold chr_n, chr_res.
  destruct (find_byte c str) as [i|] eqn:look.
  - destruct (find_byte_Some _ _ _ look) as [below _].
    destruct (A + Z.of_nat i =? 0); lia.
  - rewrite Z.eqb_refl. lia.
Qed.

Lemma pad_mono (s x y : Z) : x + 1 <= y -> x + 1 + (- (s + x + 1)) mod 8 <= y + (- (s + y)) mod 8.
Proof.
  intro step_le.
  Z.div_mod_to_equations. lia.
Qed.

Lemma pad_mono2 (s x y : Z) : x <= y -> x + (- (s + x)) mod 8 <= y + (- (s + y)) mod 8.
Proof.
  intro le_xy.
  Z.div_mod_to_equations. lia.
Qed.

Lemma nth_firstn_pref (l : list byte) (L j : nat) :
  (j < length (firstn L l))%nat -> nth_error (firstn L l) j = nth_error l j.
Proof.
  intro inb. rewrite length_firstn in inb.
  rewrite nth_error_firstn.
  destruct (Nat.ltb_spec j L) as [_|out]; [reflexivity | lia].
Qed.

Lemma firstn_cstr (str slack : list byte) (L : nat) : (length str < L)%nat ->
  firstn L (str ++ NUL :: slack) = str ++ NUL :: firstn (L - S (length str)) slack.
Proof.
  (* walk down [str] and [L] together *)
  revert L.
  induction str as [|head tail walk]; intros [|L'] short; cbn [length] in short; try lia.
  - cbn [app firstn length Nat.sub]. rewrite Nat.sub_0_r. reflexivity.
  - cbn [app firstn length Nat.sub]. f_equal. apply walk. lia.
Qed.

Lemma cstr_byte (str rest : list byte) (j : Z) : ~ In NUL str -> 0 <= j <= Z.of_nat (length str) ->
  exists b, nth_error (str ++ NUL :: rest) (Z.to_nat j)
            = Some b /\ (bv_unsigned b = 0 <-> j = Z.of_nat (length str)).
Proof.
  intros nonul range.
  destruct (Z.eq_dec j (Z.of_nat (length str))) as [at_end|before].
  - exists NUL. split.
    + rewrite nth_error_app2 by lia.
      replace (Z.to_nat j - length str)%nat with 0%nat by lia. reflexivity.
    + split; intros _; [exact at_end | reflexivity].
  - assert (idx : (Z.to_nat j < length str)%nat) by lia.
    (* the byte is the [j]-th element of [str], read with [nth] and a NUL default *)
    exists (nth (Z.to_nat j) str NUL). split.
    + rewrite <- (app_nth1 str (NUL :: rest) NUL idx).
      apply nth_error_nth'. rewrite length_app. cbn [length]. lia.
    + split; [| lia].
      intro zero.
      pose proof (nth_In str NUL idx) as member.
      assert (nul_eq : nth (Z.to_nat j) str NUL = NUL) by (apply bv_eq; rewrite zero; reflexivity).
      rewrite nul_eq in member. contradiction.
Qed.

Lemma cr_lits_differ (x y : Z) :
  0 <= x < 2^64 -> 0 <= y < 2^64 -> x <> y ->
  negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y)) = true.
Proof.
  intros x_rng y_rng apart.
  unfold bv_eqb. rewrite !unsigned_lit by lia.
  apply negb_true_iff, Z.eqb_neq. exact apart.
Qed.

Lemma cr_byte_word_nz (b : byte) :
  bv_unsigned b <> 0 -> negb (bv_eqb (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 0)) = true.
Proof.
  intro nz. pose proof (byte_range b) as rng.
  apply cr_lits_differ; lia.
Qed.

Lemma iislen_loop : forall (k : nat) (j s : Z) (str rest : list byte),
  forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word,
  forall F fc (m : mem),
  Z.of_nat (length str) - j = Z.of_nat k -> 0 <= j -> s + Z.of_nat (length str) + 1 < 2^64 ->
  bytes_at asegs m s (str ++ NUL :: rest) -> ~ In NUL str -> mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.of_nat (length str)) m)
    (ms_at (mkR ra sp gp tp t0 t1 t2 s0 s1 (w64 s) (w64 j) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (w64 0x63fac) fc m).
Proof.
  induction k as [|k more];
    intros j s str rest ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m remaining j_nonneg fits src nonul inv;
    destruct (cstr_byte str rest j nonul ltac:(lia)) as (b & pick & zero_iff);
    assert (rd : ov_read_bytes asegs m (wa (s + j)) 1 = Some [b])
      by (eapply u8ro_read; [exact src | exact pick | exact j_nonneg | reflexivity]);
    do 3 zstep.
  - (* the byte at offset j is the terminator: fall out of the loop and return *)
    assert (term : bv_unsigned b = 0) by (apply zero_iff; lia).
    rewrite term. zstep. if_false.
    pose proof (munch_refl [] m) as same_mem. pose proof (wmono_refl asegs m) as same_w.
    do 2 zstep.
    replace j with (Z.of_nat (length str)) by lia.
    sys_finish.
  - (* a non-terminator byte: take the back edge with offset j + 1 *)
    assert (nz : bv_unsigned b <> 0) by (intro z; apply zero_iff in z; lia).
    zstep. if_true_by (cr_byte_word_nz b nz).
    apply (more (j + 1) s str rest); [lia | lia | exact fits | exact src | exact nonul | exact inv].
Qed.

Lemma iislen_spec :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6,
  forall (F : bvmap 5 word) fc (m : mem) (s : Z) (str rest : list byte),
  a0 = w64 s -> bytes_at asegs m s (str ++ NUL :: rest) -> s + Z.of_nat (length str) + 1 < 2^64 ->
  ~ In NUL str -> mem_inv asegs m ->
  evt asegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.of_nat (length str)) m)
    (ms_at (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (w64 0x63fa8) fc m).
Proof.
  intros until rest. intros a0_is src fits nonul inv. subst a0.
  zstep.
  apply (iislen_loop (length str) 0 s str rest); [lia | lia | exact fits | exact src | exact nonul | exact inv].
Qed.

Definition chr_post (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (a0 a1 : word) (str full : list byte) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' : machine_state =>
    exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word, exists m' : mem,
      ms' = ms_at (mkR ra sp gp tp t0 t1 t2 s0 s1 (w64 (chr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str))
                       a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc m'
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m'
      /\ wmono asegs m m'
      /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ bytes_at asegs m' (bv_unsigned a0) full.

Definition chr_stmt :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6,
  forall (F : bvmap 5 word) fc (m : mem) (str slack full : list byte) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  bytes_at asegs m (bv_unsigned a0) full ->
  (forall j, (j < length full)%nat -> nth_error full j = nth_error (str ++ NUL :: slack) j) ->
  ~ In NUL str ->
  Z.of_nat (chr_idx (bv_unsigned a1 mod 256) str) + 1
    + (- (bv_unsigned a0 + Z.of_nat (chr_idx (bv_unsigned a1 mod 256) str) + 1)) mod 8
    <= Z.of_nat (length full) ->
  mem_inv asegs m ->
  0 < bv_unsigned a1 mod 256 ->
  lo <= bv_unsigned sp - 32 ->
  (bv_unsigned a0 + Z.of_nat (length full) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0) ->
  bv_unsigned sp <= 2^47 ->
  evt asegs (chr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str full lo m)
    (ms_at (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (w64 0x92d9c) fc m).

Definition icells_chr (m : mem) :=
  ro_cells asegs m 0x99c88 [C8 (w64 0x133ba8)]
  /\ ro_cells asegs m 0x99c98 [C8 (w64 0xa2078)]
  /\ ro_cells asegs m 0xa2078 [C8 (w64 0x7fff8000)]
  /\ rw_cells asegs m 0xa2d58 [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m 0x9b9d0 [C8 (w64 0x92d9c)]
  /\ ro_cells asegs m 0x133c9d [C1 NUL]
  /\ ro_cells asegs m 0x133ca5 [C1 (Z_to_bv 8 1)].

Lemma istrchr_loop : forall (k : nat) (c e : Z),
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word,
  forall F fc (m : mem),
  e - c = Z.of_nat (S k) -> 0 <= c -> e < 2^64 ->
  (forall x, c <= x < e -> exists b, bytes_at asegs m x [b]) -> mem_inv asegs m ->
  evt asegs
    (fun ms' => exists a3' a4' : word,
       ms' = ms_at (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (w64 e) (w64 e) a3' a4' a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (w64 0x430dc) fc m)
    (ms_at (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (w64 c) (w64 e) a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (w64 0x430cc) fc m).
Proof.
  induction k as [|k more];
    intros c e ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m span c_nonneg e_fits readable inv;
    destruct (readable c ltac:(lia)) as [b cell];
    assert (rd : ov_read_bytes asegs m (wa c) 1 = Some [b])
      by (apply (u8ro_read asegs m c [b] 0 b); [exact cell | reflexivity | lia | f_equal; lia]);
    do 3 zstep.
  - (* last byte of the range: the cursor meets the end and the loop exits *)
    replace (c + 1) with e by lia.
    zstep. if_false.
    sys_finish.
  - (* more bytes remain: the cursor moves on by one *)
    zstep. if_true_by (cr_lits_differ (c + 1) e ltac:(lia) ltac:(lia) ltac:(lia)).
    apply (more (c + 1) e); [lia | lia | exact e_fits | | exact inv].
    intros x x_in. apply readable. lia.
Qed.

Lemma cr_no_wrap (p n : Z) :
  0 <= p -> 0 <= n -> p + n < 2^64 ->
  bv_ltu (Z_to_bv 64 (Z.lxor p 18446744073709551615)) (Z_to_bv 64 n) = false.
Proof.
  intros p_nonneg n_nonneg fits.
  rewrite lxor_ones64 by lia.
  unfold bv_ltu. rewrite !unsigned_lit by lia.
  apply Z.ltb_ge. lia.
Qed.

Lemma cr_shad_shift (a : Z) : 0 <= a -> 2147450880 + a ≫ 3 = shad a.
Proof.
  intro a_nonneg. rewrite Z.shiftr_div_pow2 by lia.
  unfold shad, SHB. change (2 ^ 3) with 8. lia.
Qed.

Lemma cr_shad_range (a : Z) : 0 <= a < 2^63 -> 0 <= shad a < 2^64.
Proof.
  intro a_rng. unfold shad, SHB. Z.div_mod_to_equations. lia.
Qed.

Lemma cr_al8_shift (a : Z) : 0 <= a < 2^63 ->
  Z.land ((2147450880 + a ≫ 3) mod 18446744073709551616) 18446744073709551608 = al8 (shad a).
Proof.
  intro a_rng. rewrite cr_shad_shift by lia.
  pose proof (cr_shad_range a a_rng) as sh_rng.
  rewrite Z.mod_small by lia.
  rewrite land_m8' by lia. reflexivity.
Qed.

Lemma cr_res_floor (A c : Z) (str : list byte) : chr_res A c str <> 0 -> A <= chr_res A c str.
Proof.
  unfold chr_res. destruct (find_byte c str) as [i|]; intro nz; lia.
Qed.

Lemma cr_n_none (A c : Z) (str : list byte) :
  chr_res A c str = 0 -> chr_n A c str = Z.of_nat (length str) + 1.
Proof.
  intro zero. unfold chr_n. rewrite zero. reflexivity.
Qed.

Lemma cr_n_some (A c : Z) (str : list byte) :
  chr_res A c str <> 0 -> chr_n A c str = chr_res A c str - A + 1.
Proof.
  intro nz. unfold chr_n.
  destruct (Z.eqb_spec (chr_res A c str) 0) as [is_zero|_]; [contradiction | reflexivity].
Qed.

(* Calls into the stack frame cannot touch the shadow, so [chk_ok] survives them. *)
Lemma cr_chk_keep (m m' : mem) (p n a b : Z) :
  chk_ok m p n -> 0 <= p -> p + n <= 2^47 -> munch [(a, b)] m m' -> 0x10007fff8000 <= a ->
  chk_ok m' p n.
Proof.
  intros ok p_nonneg p_cap mu a_high.
  apply (chk_ok_agree m m' p n ok p_nonneg p_cap).
  apply (agree_of_munch [(a, b)] m m'); [exact mu |].
  intros x x_in. cbn [outside]. split; [lia | exact I].
Qed.

Section Interceptor.
Context (RIP : rip_stmt) (SC : chr_stmt).

Lemma istrchr_rip :
  forall sp p r : Z,
  forall ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word,
  forall F fc (m : mem) (lo : Z),
  stk asegs m lo (sp + -2144) -> lo <= sp - ISTRCHR_DEPTH -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 <= r -> p + r + 1 < 2^63 ->
  acc asegs m p (r + 1) -> rng_ok p (r + 1) -> m2s_cells m -> mem_inv asegs m ->
  evt asegs
    (fun ms' => exists m' : mem,
       exists ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' : word,
       ms' = ms_at (mkR ra' (w64 (sp + -2144)) gp tp t0' t1' t2' s0 s1' a0 a1' a2' a3' a4' a5' a6' a7'
                        s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6') F (w64 0x4300c) fc m'
       /\ munch [(sp - 2224, sp - 2144)] m m'
       /\ wmono asegs m m'
       /\ mem_inv asegs m'
       /\ stk asegs m' lo (sp + -2144))
    (ms_at (mkR ra (w64 (sp + -2144)) gp tp t0 t1 t2 s0 (w64 (r + 1)) a0 a1 a2 a3 a4 a5 a6 a7
                (w64 p) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (w64 0x430e4) fc m).
Proof using RIP.
  intros sp p r ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
         frame_ok lo_room lo_high sp_small p_nonneg r_nonneg end_small shadow_ok range_ok m2s inv.
  unfold kHighShadowEnd in lo_high.
  assert (sp_word : bv_unsigned (w64 (sp + -2144)) = sp + -2144) by (apply unsigned_lit; lia).
  destruct (range_ok ltac:(lia)) as [in_mem len_cap].
  (* save a0 in s6, pass (p, r + 1) and call __asan_region_is_poisoned *)
  do 4 zstep.
  eapply evt_cut.
  { eapply RIP;
      [ reflexivity | reflexivity | exact shadow_ok | lia | exact in_mem | exact m2s
      | rewrite sp_word; exact frame_ok | rewrite sp_word; lia | exact lo_high | exact inv ]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'
              & -> & mu & wm & inv' & st').
  rewrite sp_word in mu, st'.
  assert (mu_fp : munch [(sp - 2224, sp - 2144)] m m').
  { replace (sp - 2224) with (sp + -2144 - 80) by lia.
    replace (sp - 2144) with (sp + -2144) by lia. exact mu. }
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?back)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 back)) with (Z_to_bv 64 back)
        by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.
  (* the region is clean (result 0): restore a0 and branch to the exit *)
  do 3 zstep. if_true.
  sys_finish.
Qed.

(* At 0x430dc the verdict byte decides: exit, or ask __asan_region_is_poisoned. *)
Local Ltac cr_chk_tail sp p r :=
  do 2 zstep;
  let verdict := fresh "verdict" in
  if_cases verdict;
  [ sys_finish
  | apply (istrchr_rip sp p r); first [ assumption | lia ] ].


Lemma istrchr_chk :
  forall sp p r : Z,
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word,
  forall F fc (m : mem) (lo : Z),
  s0 = w64 sp ->
  stk asegs m lo (sp + -2144) -> lo <= sp - ISTRCHR_DEPTH -> kHighShadowEnd < lo -> sp < 2^63 ->
  0 <= p -> 0 <= r -> p + r + 1 < 2^63 ->
  chk_ok m p (r + 1) -> m2s_cells m -> ro_cells asegs m 0x99c98 [C8 (w64 0xa2078)] ->
  ro_cells asegs m 0xa2078 [C8 (w64 0x7fff8000)] -> mem_inv asegs m ->
  evt asegs
    (fun ms' => exists m' : mem,
       exists ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' t3' t4' t5' t6' : word,
       ms' = ms_at (mkR ra' (w64 (sp + -2144)) gp tp t0' t1' t2' s0 s1' a0 a1' a2' a3' a4' a5' a6' a7'
                        s2' s3' s4' s5' s6' s7 s8 s9 s10 s11 t3' t4' t5' t6') F (w64 0x4300c) fc m'
       /\ munch [(sp - 2224, sp - 2144)] m m'
       /\ wmono asegs m m'
       /\ mem_inv asegs m'
       /\ stk asegs m' lo (sp + -2144))
    (ms_at (mkR ra (w64 (sp + -2144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (w64 p) (w64 r)
                s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (w64 0x42fb8) fc m).
Proof using RIP.
  intros sp p r ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
         _ frame_ok lo_room lo_high sp_small p_nonneg r_nonneg end_small chk m2s got_cell off_cell inv.
  destruct chk as (shadow_ok & quick & range_ok).
  assert (r_word : bv_unsigned (w64 r) = r) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(sp - 2224, sp - 2144)] m) as same_mem.
  pose proof (wmono_refl asegs m) as same_w.
  (* n = r + 1; the end pointer p + n does not wrap *)
  do 5 zstep.
  if_false_by (cr_no_wrap p (r + 1) ltac:(lia) ltac:(lia) ltac:(lia)).
  do 2 zstep.
  destruct (Z.le_gt_cases 64 r) as [wide|narrow].
  - (* n > 64: hand the range to __asan_region_is_poisoned *)
    if_true.
    zstep. if_true_by (cr_lits_differ (r + 1) 0 ltac:(lia) ltac:(lia) ltac:(lia)).
    apply (istrchr_rip sp p r); first [ assumption | lia ].
  - (* n <= 64: look at the shadow words of the first and the last granule *)
    if_false.
    destruct (quick ltac:(lia)) as (w1 & w2 & first_cell & last_cell).
    replace (p + (r + 1) - 1) with (r + p) in last_cell by lia.
    do 10 zstep.
    rewrite (cr_al8_shift p), (cr_al8_shift (r + p)) by lia.
    rewrite (cr_shad_shift p), (cr_shad_shift (r + p)) by lia.
    do 4 zstep.
    if_cases dirty.
    + (* a shadow word is non-zero: inspect the last shadow byte, then OR the bytes in between *)
      destruct (shadow_ok r ltac:(lia)) as (last_b & last_byte & _).
      replace (p + r) with (r + p) in last_byte by lia.
      assert (rd : ov_read_bytes asegs m (wa (shad (r + p))) 1 = Some [last_b])
        by (apply (u8ro_read asegs m (shad (r + p)) [last_b] 0 last_b);
            [exact last_byte | reflexivity | lia | f_equal; lia]).
      do 7 zstep.
      if_cases ascending.
      * cr_chk_tail sp p r.
      * apply negb_false_iff in ascending. unfold bv_ltu in ascending.
        rewrite !unsigned_lit in ascending by (apply cr_shad_range; lia).
        apply Z.ltb_lt in ascending.
        pose proof (cr_shad_range p ltac:(lia)) as lo_rng.
        pose proof (cr_shad_range (r + p) ltac:(lia)) as hi_rng.
        eapply evt_cut.
        { apply (istrchr_loop (Z.to_nat (shad (r + p) - shad p - 1)) (shad p) (shad (r + p)));
            [ lia | lia | lia | | exact inv ].
          intros x x_in. apply (acc_shadow_bytes m p (r + 1) shadow_ok ltac:(lia) p_nonneg).
          replace (p + (r + 1) - 1) with (r + p) by lia. lia. }
        intros ms' (a3' & a4' & ->).
        cr_chk_tail sp p r.
    + (* both shadow words are zero: the range is addressable *)
      sys_finish.
Qed.

Definition istrchr_post (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (r lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' : machine_state =>
    exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word, exists m' : mem,
      ms' = ms_at (mkR ra sp gp tp t0 t1 t2 s0 s1 (w64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (ret_pc ra) fc m'
      /\ munch [(bv_unsigned sp - ISTRCHR_DEPTH, bv_unsigned sp)] m m'
      /\ wmono asegs m m'
      /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp).

(* Run a callee given by [spec_tac] and carry the caller's facts across it. *)
Local Ltac cr_invoke spec_tac :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?mem _) => eapply evt_cut; [ spec_tac | post_call segs mem ]
  end.

(* From 0x42fb8 with s3 = r: check [s, s + r + 1), then unwind the frame and return. *)
Local Ltac cr_check_and_return sp s r n_val chk track FR :=
  cr_invoke ltac:(eapply (istrchr_chk (bv_unsigned sp) s r);
    [ symmetry; apply Z_to_bv_lit_self
    | eassumption
    | lia
    | unfold kHighShadowEnd; lia
    | lia
    | lia
    | lia
    | lia
    | rewrite <- n_val; eapply cr_chk_keep; [ exact chk | lia | lia | exact track | lia ]
    | refine (conj _ (conj _ _)); eassumption
    | eassumption
    | eassumption
    | eassumption ]);
  do 12 zstep;
  lazymatch goal with
  | st : stk asegs _ _ (bv_unsigned sp + -2144) |- _ => release_frame FR st (bv_unsigned sp)
  end;
  sys_finish.


Theorem istrchr_spec :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6,
  forall (F : bvmap 5 word) fc (m : mem) (s : Z) (str slack : list byte) (L : nat) (lo : Z),
  a0 = w64 s ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRCHR_DEPTH -> kHighShadowEnd < lo ->
  bv_unsigned sp <= 2^47 ->
  0 <= s -> s + Z.of_nat L <= 2^47 ->
  bytes_at asegs m s (firstn L (str ++ NUL :: slack)) -> ~ In NUL str ->
  (L <= length str + S (length slack))%nat ->
  0 < bv_unsigned a1 mod 256 ->
  chr_n s (bv_unsigned a1 mod 256) str + (- (s + chr_n s (bv_unsigned a1 mod 256) str)) mod 8 <= Z.of_nat L ->
  (s + Z.of_nat L <= bv_unsigned sp - ISTRCHR_DEPTH \/ bv_unsigned sp <= s) ->
  chk_ok m s (chr_n s (bv_unsigned a1 mod 256) str) -> m2s_cells m -> icells_chr m -> mem_inv asegs m ->
  evt asegs (istrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                          (chr_res s (bv_unsigned a1 mod 256) str) lo m)
    (ms_at (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (w64 0x42ee8) fc m).
Proof using RIP SC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m s str slack L lo a0_is frame_ok lo_room lo_high sp_cap s_nonneg s_cap src nonul L_le
         c_pos fits_pad apart chk m2s cells inv.
  subst a0. unfold kHighShadowEnd in lo_high.
  destruct m2s as (m2s_got & m2s_off & m2s_hi).
  destruct cells as (flags_ptr & got_shadow & off_shadow & inited & real_ptr & strict_flag & on_flag).
  assert (sp_word : bv_unsigned (w64 (bv_unsigned sp + -2144)) = bv_unsigned sp + -2144)
    by (apply unsigned_lit; lia).
  assert (s_word : bv_unsigned (w64 s) = s) by (apply unsigned_lit; lia).
  (* the argument bytes are exactly L long; the frame stores below need it to keep [src] *)
  assert (bytes_len : length (firstn L (str ++ NUL :: slack)) = L)
    by (apply firstn_length_le; rewrite length_app; cbn [length]; lia).
  (* the whole run stays inside [sp - 2224, sp) *)
  pose proof (munch_refl [(bv_unsigned sp - 2224, bv_unsigned sp)] m) as track.
  pose proof (wmono_refl asegs m) as wtrack.
  (* prologue: a 2144-byte frame holding ra and s0-s7 *)
  carve_frame 2144%nat frame_ok.
  do 15 zstep.
  (* asan_inited () == 1 *)
  cr_invoke ltac:(eapply asan_inited_spec; assumption).
  zstep. if_false.
  (* try_init () == 1 *)
  zstep.
  cr_invoke ltac:(eapply try_init_spec; first [ eassumption | rewrite sp_word; eassumption | lia ]).
  rewrite sp_word in *.
  (* REAL(strchr) (s, c) *)
  do 6 zstep.
  cr_invoke ltac:(eapply SC with (str := str) (slack := slack) (full := firstn L (str ++ NUL :: slack)) (lo := lo);
    [ rewrite sp_word; assumption
    | rewrite s_word; assumption
    | intros j j_in; apply nth_firstn_pref; exact j_in
    | exact nonul
    | rewrite s_word, bytes_len;
      pose proof (chr_n_ge s (bv_unsigned a1 mod 256) str) as idx_room;
      pose proof (pad_mono s _ _ idx_room) as idx_pad; lia
    | assumption
    | exact c_pos
    | lia
    | rewrite s_word; lia
    | lia ]).
  rewrite sp_word, s_word in *.
  (* the flag checks: strchr is intercepted, strict_string_checks is off *)
  zstep. if_false.
  do 4 zstep. if_false.
  do 2 zstep. if_false.
  zstep.
  (* the padding after the checked range is never negative *)
  assert (pad_nonneg : 0 <= (- (s + chr_n s (bv_unsigned a1 mod 256) str)) mod 8) by (apply Z.mod_pos_bound; lia).
  destruct (Z.eq_dec (chr_res s (bv_unsigned a1 mod 256) str) 0) as [none|some].
  - (* not found: the checked length is strlen (s) + 1 *)
    pose proof (cr_n_none s (bv_unsigned a1 mod 256) str none) as n_val.
    rewrite none. if_true.
    do 3 zstep.
    cr_invoke ltac:(eapply iislen_spec with (str := str) (rest := firstn (L - S (length str)) slack);
      [ reflexivity
      | rewrite <- (firstn_cstr str slack L) by lia; eassumption
      | lia
      | exact nonul
      | eassumption ]).
    do 2 zstep.
    cr_check_and_return sp s (Z.of_nat (length str)) n_val chk track FR.
  - (* found at index i: the checked length is i + 1 *)
    pose proof (cr_n_some s (bv_unsigned a1 mod 256) str some) as n_val.
    pose proof (cr_res_floor s (bv_unsigned a1 mod 256) str some) as res_floor.
    assert (res_word : bv_unsigned (w64 (chr_res s (bv_unsigned a1 mod 256) str))
                       = chr_res s (bv_unsigned a1 mod 256) str) by (apply unsigned_lit; lia).
    if_false.
    do 2 zstep.
    cr_check_and_return sp s (chr_res s (bv_unsigned a1 mod 256) str - s) n_val chk track FR.
Qed.

End Interceptor.
