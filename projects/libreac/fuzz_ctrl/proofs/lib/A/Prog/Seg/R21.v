(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 1137 of its 1175 lines of code are new or changed and 210 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block.v; 1090 of its 1202 lines of code are new or changed and 1063 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P5.v, with its module names changed; 1590 of its 1705 lines of code are new or changed and 1087 lines of the source are left out. *)
(* Segment R21 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): [0x81924, 0x81abc] (plan-asan 2 row R21).
   Latch 0x81924 .. 0x8195c: the eight 1-byte stores of 0xf8 into the frame's shadow bytes S(fr) + 296 .. + 312
   (s3 = S(fr)), s8 := 36, s7 := b + 1, a0 := [s1 + 128], a1 := 7, `bne s7,a1,815cc`: back to the round-trip head
   Inv_A815cc at turn b + 1 when b <= 5, else 0x8195c `j 81990`. Tail 0x81990 .. 0x81abc (b = 6): the compares of the
   round-trip identity id_rt = RID_7 (frame, s5 = fr + 2176) with the fields of the catalogue row m = [s1 + 112]
   (fw_milli, major, minor, patch at m + 266 .. + 272; has_identity_record at m + 56; the name pointer at m + 280),
   each row load behind an instrumented check whose error path (0x82c2c .. 0x82c8c, 0x82d4c .. 0x82d54) is not
   reached because the row is addressable (registered globals, frame_AG); every `j 82bf4` is not taken by the
   round-trip model facts (B3Rtm.v). With has_identity_record = 0 the code jumps to 0x81ac8 (exit Inv_A81ac8);
   else the strcmp wrapper (Section Hypothesis, plan-asan 8.2) compares the two names, which are equal, and returns
   0 to 0x81ac0 (exit Inv_A81ac0).  Push 5b: FRA carries ro_agree, not mem_inv, so the wrapper runs on the
   normalized memory (MemNorm.evt_normalize, B3Norm's mem_rel transports).  The entry is the official
   Inv_A81924_at (SlotInv.v push 6c); the latch's back edge gives the official Inv_A815cc_at (S b) its
   a0 = fr + 544 (0x81950) and s8 = 36 (0x81948), and passes the spills, s5, and the addressable id record and
   our[] through (the latch's eight shadow stores are S(fr) + 296 .. + 312). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import strcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNorm BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require B3Norm.
Module MNr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.
Module BZr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.BzBridge.
Module B3N := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg.B3Norm.
Import ListNotations.
Open Scope Z_scope.

Lemma r21_swrap32 : forall z, -2 ^ 31 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. Z.div_mod_to_equations. lia.
Qed.

Lemma r21_bv_eqb : forall a b, -2 ^ 63 <= a < 2 ^ 63 -> -2 ^ 63 <= b < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.eqb_spec a b) as [->|Hn]; [apply Z.eqb_refl|]. apply Z.eqb_neq.
  intros E. apply Hn. Z.div_mod_to_equations. lia.
Qed.

Lemma r21_eqb_refl : forall x : word, bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.

(* A whole byte run read in one access. *)
Lemma r21_rdn : forall m a bs (n : nat), bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H Hn.
  pose proof (bytes_at_ov_read rsegs m a bs 0 n H ltac:(lia)) as HR.
  replace (a + Z.of_nat 0) with a in HR by lia.
  assert (E : firstn n (skipn 0 bs) = bs).
  { change (skipn 0 bs) with bs. apply firstn_all2. lia. }
  rewrite E in HR. exact HR.
Qed.

(* ---- The latch 0x81924 .. 0x81958 ---- *)

(* A present, writable byte run gives store_ok for each of its bytes. *)
Lemma r21_stk_store_ok : forall m lo hi a, stk rsegs m lo hi -> lo <= a -> a + 1 <= hi ->
  store_ok rsegs m (wa a) 1%nat = true.
Proof.
  intros m lo hi a (H1 & H2 & H) Hlo Hhi.
  assert (WR : wr_at rsegs m a 1).
  { split; [lia|]. split; [lia|]. intros i Hi. assert (Ei : i = 0) by lia. subst i.
    rewrite Z.add_0_r. exact (proj1 (H a ltac:(lia))). }
  pose proof (wr_at_store_ok rsegs m a 1 0 1%nat WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

(* One shadow store `sb a0,off(s3)` of the latch, with the munch / stk / wmono bookkeeping. *)
Ltac r21_sb SHv off STh MUh WMh :=
  let HS := fresh "HSok" in
  (lazymatch goal with
   | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
       assert (HS : store_ok rsegs mm (wa (SHv + off)) 1%nat = true)
         by (apply (r21_stk_store_ok mm (SHv + 296) (SHv + 313) (SHv + off) STh); lia)
   end);
  step;
  (lazymatch goal with
   | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm ?aa ?bs) _) =>
       apply (munch_write [(SHv + 296, SHv + 313)] _ mm (SHv + off) bs) in MUh;
         [ | lia
           | rewrite length_le1; cbn [Z.of_nat]; lia
           | rewrite length_le1; cbn [inside Z.of_nat]; left; lia ];
       apply (stk_write rsegs mm (SHv + 296) (SHv + 313) (SHv + off) bs) in STh;
         [ | lia | rewrite length_le1; cbn [Z.of_nat]; lia ];
       apply (wmono_write rsegs _ mm aa bs) in WMh
   end);
  clear HS.

Ltac r21_latch_pre SHv A v HQh STh MUh WMh :=
  step;                                                        (* 81924 li a0,-8 *)
  r21_sb SHv 300 STh MUh WMh; r21_sb SHv 306 STh MUh WMh;
  r21_sb SHv 308 STh MUh WMh; r21_sb SHv 312 STh MUh WMh;
  r21_sb SHv 296 STh MUh WMh; r21_sb SHv 297 STh MUh WMh;
  r21_sb SHv 298 STh MUh WMh; r21_sb SHv 299 STh MUh WMh;
  step;                                                        (* 81948 li s8,36 *)
  step;                                                        (* 8194c addiw s7,s7,1 *)
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let HQ2 := fresh "HQ2" in let HR := fresh "HR" in
      pose proof (bytes_at_transport rsegs [(SHv + 296, SHv + 313)] _ mm (A + 128) (le8 (Z_to_bv 64 v)) HQh MUh
                    ltac:(cbn [disjoint_from]; rewrite length_le8; cbn [Z.of_nat];
                          split; [right; lia | exact I])) as HQ2;
      pose proof (r21_rdn mm (A + 128) (le8 (Z_to_bv 64 v)) 8%nat HQ2 (length_le8 _)) as HR
  end;
  step;                                                        (* 81950 ld a0,128(s1) *)
  step.                                                        (* 81954 li a1,7 *)

Lemma r21_latch_next :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SH A bz v : Z),
    s3 = Z_to_bv 64 SH -> s1 = Z_to_bv 64 A -> s7 = Z_to_bv 64 bz -> 0 <= bz <= 5 ->
    0 <= SH -> SH + 313 <= A -> A + 136 <= 2 ^ 64 ->
    stk rsegs m (SH + 296) (SH + 313) ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 v)) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x815cc) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 23 = Z_to_bv 64 (bz + 1) /\
         getr R 25 = s9 /\ getr R 26 = s10 /\ getr R 10 = Z_to_bv 64 v /\ getr R 24 = Z_to_bv 64 36 /\
         munch [(SH + 296, SH + 313)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (SH + 296) (SH + 313))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81924) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m SH A bz v -> -> -> Hb HS0 HSA HA ST HQ.
  pose proof (munch_refl [(SH + 296, SH + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  r21_latch_pre SH A v HQ ST MU WM.
 
  step.                                  (* 81958 bne s7,a1,815cc *)
 
  rewrite ?(MState.unsigned_lit bz) by lia. rewrite ?r21_swrap32 by lia. rewrite ?r21_bv_eqb by lia.
  if_true.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  do 13 (split; [reflexivity|]).
  split; [exact MU|]. split; [exact WM | exact ST].
Qed.

Lemma r21_latch_last :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SH A v : Z),
    s3 = Z_to_bv 64 SH -> s1 = Z_to_bv 64 A -> s7 = Z_to_bv 64 6 ->
    0 <= SH -> SH + 313 <= A -> A + 136 <= 2 ^ 64 ->
    stk rsegs m (SH + 296) (SH + 313) ->
    bytes_at rsegs m (A + 128) (le8 (Z_to_bv 64 v)) ->
    evt rsegs
      (fun ms' => exists (R : bvmap 5 word) (m' : word -> option byte),
         ms' = MS R F (Z_to_bv 64 0x81990) fc None m' (seg_rom rsegs) /\
         getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
         getr R 19 = s3 /\ getr R 21 = s5 /\ getr R 22 = s6 /\ getr R 25 = s9 /\ getr R 26 = s10 /\
         munch [(SH + 296, SH + 313)] m m' /\ wmono rsegs m m' /\ stk rsegs m' (SH + 296) (SH + 313))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81924) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m SH A v -> -> -> HS0 HSA HA ST HQ.
  pose proof (munch_refl [(SH + 296, SH + 313)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  r21_latch_pre SH A v HQ ST MU WM.
  step.                                  (* 81958 bne s7,a1,815cc *)
  rewrite ?(MState.unsigned_lit 6) by lia. rewrite ?r21_swrap32 by lia. rewrite ?r21_bv_eqb by lia.
  if_false.
  step.                                  (* 8195c j 81990 *)
  apply evt_done. do 2 eexists. split; [reflexivity|].
  do 10 (split; [reflexivity|]).
  split; [exact MU|]. split; [exact WM | exact ST].
Qed.

(* ---- The tail 0x81990 .. 0x81abc ---- *)

Lemma r21_sx32_eqb0 : forall h, 0 <= h < 2 ^ 32 -> bv_eqb (sx32 (Z_to_bv 64 h)) (Z_to_bv 64 0) = (h =? 0).
Proof.
  intros h Hh. unfold sx32, bv_eqb. rewrite (MState.unsigned_lit h) by lia.
  rewrite !MState.unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  change (2 ^ 64) with 18446744073709551616.
  destruct (Z.eqb_spec h 0) as [->|Hn]; [reflexivity|]. apply Z.eqb_neq.
  Z.div_mod_to_equations. lia.
Qed.

Lemma r21_eqb0 : forall x, 0 < x < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof. intros x Hx. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

(* `beq` on two equal values: taken. *)
Ltac r21_beq_refl :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with true; [cbv iota | symmetry; apply r21_eqb_refl]
  end.

(* srli of the shadow address: the shifted value is a literal in range. *)
Ltac r21_shfix :=
  repeat match goal with
  | |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?x)) 3] => rewrite (MState.unsigned_lit x) by lia
  end.

Lemma r21_tail_evt : strcmp_wrap_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv lo A S5 mr fw maj mnr pat h nm w144 : Z) (sx : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> s5 = Z_to_bv 64 S5 -> s10 = Z_to_bv 64 ASAN_K ->
    0 <= spv < 2 ^ 64 -> 0 <= A -> A + 152 <= 2 ^ 64 -> 0 <= S5 -> S5 + 38 <= 2 ^ 64 ->
    0 <= mr -> mr + 296 <= 2 ^ 63 -> 0 <= h < 2 ^ 32 ->
    ov_read_bytes rsegs m (wa (S5 + 2)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (A + 144)) 8 = Some (le8 (Z_to_bv 64 w144)) ->
    ov_read_bytes rsegs m (wa (A + 112)) 8 = Some (le8 (Z_to_bv 64 mr)) ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 266) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 268) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 270) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 272) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 56) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa (Z.shiftr (mr + 280) 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0] ->
    ov_read_bytes rsegs m (wa S5) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (mr + 266)) 2 = Some (le2 (Z_to_bv 64 fw)) ->
    ov_read_bytes rsegs m (wa (S5 + 36)) 1 = Some [Z_to_bv 8 1] ->
    ov_read_bytes rsegs m (wa (S5 + 22)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (mr + 268)) 2 = Some (le2 (Z_to_bv 64 maj)) ->
    ov_read_bytes rsegs m (wa (S5 + 24)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (mr + 270)) 2 = Some (le2 (Z_to_bv 64 mnr)) ->
    ov_read_bytes rsegs m (wa (S5 + 26)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 272)) 2 = Some (le2 (Z_to_bv 64 pat)) ->
    ov_read_bytes rsegs m (wa (mr + 56)) 4 = Some (le4 (Z_to_bv 64 h)) ->
    (h <> 0 ->
       ov_read_bytes rsegs m (wa (S5 + 20)) 1 = Some [Z_to_bv 8 1] /\
       ov_read_bytes rsegs m (wa (mr + 280)) 8 = Some (le8 (Z_to_bv 64 nm)) /\ 0 < nm < 2 ^ 64 /\
       bytes_at rsegs m (S5 + 3) (sx ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) sx /\
       bytes_at rsegs m nm (sx ++ [Z_to_bv 8 0]) /\
       Z.of_nat (strcmp_k sx sx) + 1 <= 2^40 /\
       addressable m (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1) /\
       end_in_app (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1) /\
       addressable m nm (Z.of_nat (strcmp_k sx sx) + 1) /\ end_in_app nm (Z.of_nat (strcmp_k sx sx) + 1) /\
       app_mem (S5 + 3 + 7) /\ app_mem (nm + 7) /\
       stk rsegs m lo spv /\ lo + STRCMP_WRAP_K <= spv /\ HIGHMEM_BEG <= lo /\ spv <= APPMEM_END /\
       (S5 + 3 + Z.of_nat (length sx) + 1 <= spv - STRCMP_WRAP_K \/ spv <= S5 + 3) /\
       (nm + Z.of_nat (length sx) + 1 <= spv - STRCMP_WRAP_K \/ spv <= nm) /\
       asan_cells m /\ shadow_rw m /\ MNr.ro_agree rsegs m /\
       bytes_at rsegs m GOT_CF (le8 (wa CF)) /\
       bytes_at rsegs m (CF + 250) [Z_to_bv 8 1] /\ bytes_at rsegs m (CF + 245) [Z_to_bv 8 0]) ->
    evt rsegs
      (fun ms' =>
         (h = 0 /\ exists R : bvmap 5 word,
            ms' = MS R F (Z_to_bv 64 0x81ac8) fc None m (seg_rom rsegs) /\ getr R 10 = Z_to_bv 64 0 /\
            getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
            getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = Z_to_bv 64 w144 /\
            getr R 22 = s6 /\ getr R 25 = s9) \/
         (h <> 0 /\ exists (R : bvmap 5 word) (m' : word -> option byte),
            ms' = MS R F (Z_to_bv 64 0x81ac0) fc None m' (seg_rom rsegs) /\ getr R 10 = Z_to_bv 64 0 /\
            getr R 2 = sp /\ getr R 3 = gp /\ getr R 4 = tp /\ getr R 8 = s0 /\ getr R 9 = s1 /\
            getr R 19 = s3 /\ getr R 26 = s10 /\ getr R 27 = Z_to_bv 64 w144 /\
            getr R 22 = s6 /\ getr R 25 = s9 /\
            munch [(spv - STRCMP_WRAP_K, spv)] m m' /\ wmono rsegs m m' /\ stk rsegs m' lo spv))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81990) fc None m (seg_rom rsegs)).
Proof.
  intros SC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv lo A S5 mr fw maj mnr pat h nm w144 sx -> -> -> -> Hsp HA0 HA1 HS0 HS1 Hm0 Hm1 Hh
    R2 R144 R112 K266 K268 K270 K272 K56 K280 R0 M266 R36 R22 M268 R24 M270 R26 M272 M56 HN.
  step. step. step. if_true.            (* 81990 lbu; 81994 ld s11; 81998 bnez *)
  step. step. step. step. r21_shfix.     (* 819a0 ld; addi 266; srli; add *)
  step. step. step. if_true.           (* 819b0 lb (check); 819b4 lhu; 819b8 beqz *)
  step. step. r21_beq_refl.             (* 819c0 lhu; 819c4 beq *)
  step. step. if_true.                                         (* 819cc lbu 36; 819d0 bnez *)
  step. step. step. step. r21_shfix.                           (* 819d8 .. 819e4 *)
  step. step. step. if_true.                                   (* 819e8 lb; 819ec lhu 22; 819f0 beqz *)
  step. step. r21_beq_refl.                                    (* 819f8 lhu; 819fc beq *)
  step. step. step. step. r21_shfix.                           (* 81a04 .. 81a10 *)
  step. step. step. if_true.                                   (* 81a14 lb; 81a18 lhu 24; 81a1c beqz *)
  step. step. r21_beq_refl.                                    (* 81a24 lhu; 81a28 beq *)
  step. step. step. step. r21_shfix.                           (* 81a30 .. 81a3c *)
  step. step. step. if_true.                                   (* 81a40 lb; 81a44 lhu 26; 81a48 beqz *)
  step. step. r21_beq_refl.                                    (* 81a50 lhu; 81a54 beq *)
  step. step. step. step. r21_shfix.                           (* 81a5c .. 81a68 *)
  step. step. if_true.                                         (* 81a6c lb; 81a70 beqz *)
  step. step.                           (* 81a78 lw; 81a7c beqz a0,81ac8 *)
  destruct (Z.eq_dec h 0) as [E0 | E0].
  - if_true_by (eq_trans (r21_sx32_eqb0 h Hh) (proj2 (Z.eqb_eq h 0) E0)).
    subst h. apply evt_done. left. split; [reflexivity|]. eexists. split; [reflexivity|].
    do 10 (split; [reflexivity|]). reflexivity.
  - if_false_by (eq_trans (r21_sx32_eqb0 h Hh) (proj2 (Z.eqb_neq h 0) E0)).
    destruct (HN E0) as (R20 & R280 & Hnm & HS1x & HS0x & HS2x & HK & HAX & HEX & HAY & HEY & HX7 & HY7 &
                         HST & HLO & HHM & HAE & HSEPx & HSEPy & HAC & HSW & HMIx & HGOT & HCF1 & HCF2).
    step. step. if_true.                                       (* 81a80 lbu 20; 81a84 bnez *)
    step. step. step. step. r21_shfix.                         (* 81a8c .. 81a98 *)
    step. step. if_true.               (* 81a9c lbu (check); 81aa0 beqz *)
    step. step. step.                  (* 81aa8 ld a1; 81aac addi a0,s5,3; 81ab0 bnez *)
    if_true_by (f_equal negb (r21_eqb0 nm Hnm)).
    step.                               (* 81abc jal wrapper_strcmp *)
    (* the wrapper runs on the normalized memory, which has the mem_inv its contract asks for *)
    assert (HHMv : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
    pose proof (MNr.mem_rel_normalize rsegs m HMIx) as REL.
    assert (HS1x0 : bytes_at rsegs (MNr.normalize rsegs m) (S5 + 3) (sx ++ [Z_to_bv 8 0]))
      by exact (proj1 (MNr.bytes_at_rel rsegs m _ _ _ REL) HS1x).
    assert (HS2x0 : bytes_at rsegs (MNr.normalize rsegs m) nm (sx ++ [Z_to_bv 8 0]))
      by exact (proj1 (MNr.bytes_at_rel rsegs m _ _ _ REL) HS2x).
    assert (HAX0 : addressable (MNr.normalize rsegs m) (S5 + 3) (Z.of_nat (strcmp_k sx sx) + 1))
      by exact (proj1 (B3N.b3n_rel_ad m _ _ _ REL) HAX).
    assert (HAY0 : addressable (MNr.normalize rsegs m) nm (Z.of_nat (strcmp_k sx sx) + 1))
      by exact (proj1 (B3N.b3n_rel_ad m _ _ _ REL) HAY).
    assert (HST0 : stk rsegs (MNr.normalize rsegs m) lo spv)
      by exact (proj1 (B3N.b3n_rel_stk m (MNr.normalize rsegs m) lo spv REL ltac:(lia) ltac:(lia)) HST).
    assert (HAC0 : asan_cells (MNr.normalize rsegs m)) by exact (proj1 (B3N.b3n_rel_cells m _ REL) HAC).
    assert (HSW0 : shadow_rw (MNr.normalize rsegs m)) by exact (proj1 (B3N.b3n_rel_sw m _ REL) HSW).
    assert (HMI0 : mem_inv rsegs (MNr.normalize rsegs m)) by exact (MNr.mem_inv_normalize rsegs m).
    assert (HGOT0 : bytes_at rsegs (MNr.normalize rsegs m) GOT_CF (le8 (wa CF)))
      by exact (proj1 (MNr.bytes_at_rel rsegs m _ _ _ REL) HGOT).
    assert (HCF10 : bytes_at rsegs (MNr.normalize rsegs m) (CF + 250) [Z_to_bv 8 1])
      by exact (proj1 (MNr.bytes_at_rel rsegs m _ _ _ REL) HCF1).
    assert (HCF20 : bytes_at rsegs (MNr.normalize rsegs m) (CF + 245) [Z_to_bv 8 0])
      by exact (proj1 (MNr.bytes_at_rel rsegs m _ _ _ REL) HCF2).
    eapply evt_mono.
    { eapply (MNr.evt_normalize rsegs _ _ _ _ _ _ _ _ BZr.wx_apart_asan HMIx).
      eapply SC with (sx := sx) (sy := sx) (lo := lo);
        rewrite ?(MState.unsigned_lit (S5 + 3)) by lia; rewrite ?(MState.unsigned_lit nm) by lia;
        rewrite ?(MState.unsigned_lit spv) by lia; assumption. }
    intros ms' (s0' & PO & HREL & HROS).
    destruct PO as (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E & Hr & Hr0 & MU0 & WM0 & _ & STq0 & _).
    assert (Er : r = Z_to_bv 64 0) by (apply Hr0; reflexivity). subst s0'.
    destruct HREL as (ERg & EF & EP & ES & EV & EC & ERo & HMR).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ERg, EF, EP, ES, EV, EC,
      ERo, HMR.
    assert (EPc : ms_pc_val ms' = Z_to_bv 64 0x81ac0).
    { rewrite EP. apply MState.ret_pc_even; [lia | reflexivity]. }
    pose proof (B3N.b3n_ms_eta ms' ES) as Ems.
    rewrite ERg, EF, EPc, EC, EV, ERo, Er in Ems.
    remember (ms_mem ms') as m' eqn:Em'. clear Em'.
    rewrite (MState.unsigned_lit spv) in MU0, STq0 by lia.
    assert (MUf : munch [(spv - STRCMP_WRAP_K, spv)] m m')
      by exact (B3N.b3n_rel_munch _ m _ m' m0' REL HMR MU0 HROS).
    right. split; [exact E0|]. do 2 eexists. split; [exact Ems|].
    split; [reflexivity|]. do 10 (split; [reflexivity|]).
    split; [exact MUf|]. split.
    { apply (B3N.b3n_rel_wmono [(spv - STRCMP_WRAP_K, spv)] m _ m' m0' REL HMR MUf WM0).
      intros x Ex. apply (B3N.b3n_W_ro _ x); [|exact Ex].
      intros p [<-|[]]. cbn [fst]. lia. }
    exact (proj2 (B3N.b3n_rel_stk m' m0' lo spv HMR ltac:(lia) ltac:(lia)) STq0).
Qed.

(* ---- Full wrapper seg_R21 (B3 recipe).  The latch's eight frame-shadow stores move FRA by Tac_slot.sl_fr_meta
   (the AH / stklo premises per frame-location arm, as A/Prog/Seg/P2.v does for one byte); the strcmp wrapper call
   moves it by the local r21_callee_keep (B3FrCl.b3_fr_cl, the push-5b frame transport across a write set that is
   app memory below sp).  The round-trip model facts are B3Rtm.v. ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06 YN2e YK1j.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require MState Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcRec RcParse RcReply RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcLeaf RcPorts RcEmit RcSynth RcDecl RcMatch RcParseLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_rt_b2 Tac_rt2_b2 Tac_slot
  Tac_fs B3Rtm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require B3FrCl.
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.

Open Scope Z_scope.

Module ACw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AFw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module MMo := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.MemMono.

(* ---- Byte-run helpers (ports of the U twin R23's r23_sub / r23_first1 / r23_first2 / r23_rd1 / r23_rd2) ---- *)

Lemma a_sub : forall m a bs k n, bytes_at rsegs m a bs -> (k + n <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H Hk.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma a_first1 : forall (l : list byte) k, (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l (Z_to_bv 8 0)].
Proof.
  induction l as [|x l IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma a_first2 : forall (l : list byte) k, (k + 2 <= length l)%nat ->
  firstn 2 (skipn k l) = [nth k l (Z_to_bv 8 0); nth (S k) l (Z_to_bv 8 0)].
Proof.
  induction l as [|x l IH]; intros k Hk; cbn in Hk; [lia|].
  destruct k as [|k].
  - destruct l as [|y l]; cbn in Hk; [lia|]. reflexivity.
  - cbn [skipn nth]. apply IH. lia.
Qed.

Lemma a_rd1 : forall m a l k, bytes_at rsegs m a l -> (k < length l)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 1 = Some [nth k l (Z_to_bv 8 0)].
Proof.
  intros m a l k H Hk.
  pose proof (a_sub m a l k 1 H ltac:(lia)) as HB. rewrite a_first1 in HB by lia.
  exact (r21_rdn m _ _ 1%nat HB eq_refl).
Qed.

Lemma a_rd2 : forall m a l k, bytes_at rsegs m a l -> (k + 2 <= length l)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 2 =
  Some (le2 (Z_to_bv 64 (bv_unsigned (nth k l (Z_to_bv 8 0)) + 256 * bv_unsigned (nth (S k) l (Z_to_bv 8 0))))).
Proof.
  intros m a l k H Hk.
  pose proof (a_sub m a l k 2 H ltac:(lia)) as HB. rewrite a_first2 in HB by lia.
  replace (le2 (Z_to_bv 64 (bv_unsigned (nth k l (Z_to_bv 8 0)) + 256 * bv_unsigned (nth (S k) l (Z_to_bv 8 0)))))
    with [nth k l (Z_to_bv 8 0); nth (S k) l (Z_to_bv 8 0)].
  - exact (r21_rdn m _ _ 2%nat HB eq_refl).
  - rewrite <- RcParseLib.rc_le2_pair. f_equal. f_equal. lia.
Qed.

Lemma a_rd4 : forall m a l k, bytes_at rsegs m a l -> (k + 4 <= length l)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 4 = Some (firstn 4 (skipn k l)).
Proof.
  intros m a l k H Hk.
  pose proof (a_sub m a l k 4 H ltac:(lia)) as HB.
  apply (r21_rdn m _ _ 4%nat HB).
  rewrite length_firstn, length_skipn. lia.
Qed.

Lemma a_rd8 : forall m a l k, bytes_at rsegs m a l -> (k + 8 <= length l)%nat ->
  ov_read_bytes rsegs m (wa (a + Z.of_nat k)) 8 = Some (firstn 8 (skipn k l)).
Proof.
  intros m a l k H Hk.
  pose proof (a_sub m a l k 8 H ltac:(lia)) as HB.
  apply (r21_rdn m _ _ 8%nat HB).
  rewrite length_firstn, length_skipn. lia.
Qed.

Lemma a_byte1 : forall b : byte, bv_unsigned b = 1 -> b = Z_to_bv 8 1.
Proof. intros b H. apply bv_eq. rewrite H. reflexivity. Qed.

(* The identity record has 38 bytes at every turn (U twin r23_RID_len). *)
Lemma a_RID_len : forall inp b, length (RID inp b) = 38%nat.
Proof.
  intros inp b. unfold RID. induction b as [|b IH]; [reflexivity|].
  cbn [rt_st].
  destruct (rt_n inp (Z.of_nat b) =? 0); [exact IH|].
  destruct ((Z.of_nat b =? 3) || (Z.of_nat b =? 4)); cbn [fst snd].
  - unfold rp_id. destruct (ir _ _); [apply RcIdentModel.ING_length; exact IH | exact IH].
  - destruct ((Z.of_nat b =? 5) || (Z.of_nat b =? 6)); cbn [fst snd]; [|exact IH].
    unfold fg_id. destruct (fg_rf _ _ _ =? 1); [apply RcIdentModel.ING_length; exact IH | exact IH].
Qed.

(* The fragment state has 72 bytes at every round-trip turn (computed over the 11 catalogue rows, B3Rtm.a_rows). *)
Lemma a_RFG_len : forall inp b, (b <= 7)%nat -> length (RFG inp b) = 72%nat.
Proof.
  intros inp b Hb.
  assert (E : (b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5 \/ b = 6 \/ b = 7)%nat) by lia.
  destruct E as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; a_rows inp; a_fin.
Qed.

(* strcmp's index on two equal strings is their length. *)
Lemma a_strcmp_k_refl : forall l : list byte, strcmp_k l l = length l.
Proof.
  induction l as [|x l IH]; [reflexivity|].
  cbn [strcmp_k length]. rewrite Z.eqb_refl, IH. reflexivity.
Qed.

(* n addressable bytes from n single addressable bytes. *)
Lemma a_addr_join : forall m p n, 0 <= p -> 0 <= n -> p + n <= APPMEM_END ->
  (forall i, 0 <= i < n -> addressable m (p + i) 1) -> addressable m p n.
Proof.
  intros m p n Hp Hn Hend H. split; [exact Hp|]. split; [exact Hn|]. split; [exact Hend|].
  intros i Hi. destruct (H i Hi) as (_ & _ & _ & Hb). pose proof (Hb 0 ltac:(lia)) as Hb0.
  rewrite Z.add_0_r in Hb0. exact Hb0.
Qed.

(* An aligned addressable granule has shadow byte 0, read by the instrumented check of any of its 8 bytes. *)
Lemma a_meta0 : forall m p q, addressable m p 8 -> p mod 8 = 0 -> p <= q < p + 8 ->
  ov_read_bytes rsegs m (wa (Z.shiftr q 3 + ASAN_K)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m p q HA Hal Hq.
  assert (Hp0 : 0 <= p) by (destruct HA as (H & _); exact H).
  assert (E : Z.shiftr q 3 = Z.shiftr p 3).
  { rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. revert Hal Hq Hp0. Z.div_mod_to_equations. lia. }
  rewrite E.
  destruct (meta8 m p HA) as (RC & _). destruct RC as (_ & HB).
  cbn [cells_bytes cbytes app] in HB.
  exact (r21_rdn m _ _ 1%nat HB eq_refl).
Qed.

(* The image's bytes at an address range of the read-only / RELRO image. *)
Lemma a_img_nth : forall n A bs, Image.image_bytes rsegs A n = Some bs ->
  forall k, (k < n)%nat -> seg_rom rsegs (wa (A + Z.of_nat k)) = nth_error bs k.
Proof.
  induction n as [|n IH]; intros A bs H k Hk.
  - lia.
  - change (Image.image_bytes rsegs A (S n)) with
      (match seg_rom rsegs (wa A), Image.image_bytes rsegs (A + 1) n with
       | Some b, Some bs0 => Some (b :: bs0) | _, _ => None end) in H.
    destruct (seg_rom rsegs (wa A)) as [b|] eqn:E1; [|discriminate H].
    destruct (Image.image_bytes rsegs (A + 1) n) as [bs'|] eqn:E2; [|discriminate H].
    injection H as <-. destruct k as [|k]; cbn [nth_error].
    + replace (A + Z.of_nat 0) with A by lia. exact E1.
    + replace (A + Z.of_nat (S k)) with (A + 1 + Z.of_nat k) by lia.
      exact (IH (A + 1) bs' E2 k ltac:(lia)).
Qed.

(* Two word_mem values at the same address agree mod 2^64 (A/Prog/Seg/P2.v p2_wm_congr). *)
Lemma r21_wm_congr : forall (m : word -> option byte) a v1 v2,
  word_mem rsegs m a v1 -> word_mem rsegs m a v2 -> v1 mod 2^64 = v2 mod 2^64.
Proof.
  intros m a v1 v2 H1 H2.
  assert (Hb : forall k, (k < 8)%nat -> le_byte v1 8 k = le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. pose proof (H2 k Hk) as E2.
    rewrite E1 in E2.
    assert (E2' : Z_to_bv 8 (le_byte v1 8 k) = Z_to_bv 8 (le_byte v2 8 k)) by congruence.
    apply (f_equal (@bv_unsigned 8)) in E2'. rewrite !kb_byte_unsigned in E2'. exact E2'. }
  apply Z.bits_inj'. intros j Hj.
  destruct (Z.ltb_spec j 64) as [Hlt|Hge].
  - set (k := Z.to_nat (j / 8)).
    assert (Hk8 : (k < 8)%nat) by (unfold k; apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      apply Z.div_lt_upper_bound; lia).
    pose proof (Hb k Hk8) as Hbk.
    assert (Hoff : 8 * Z.of_nat k + (j - 8 * Z.of_nat k) = j) by lia.
    assert (Hjk : j - 8 * Z.of_nat k = j mod 8) by (unfold k; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      rewrite (Z.div_mod j 8) at 1 by lia; lia).
    assert (Hoff8 : 0 <= j - 8 * Z.of_nat k < 8) by (rewrite Hjk; apply Z.mod_pos_bound; lia).
    assert (HT : Z.testbit (le_byte v1 8 k) (j - 8 * Z.of_nat k)
               = Z.testbit (le_byte v2 8 k) (j - 8 * Z.of_nat k)) by (rewrite Hbk; reflexivity).
    rewrite !le_byte_testbit in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ 8)) in HT by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) in HT by lia.
    rewrite Hoff in HT.
    rewrite !Z.testbit_mod_pow2 by lia.
    rewrite (proj2 (Z.ltb_lt j 64)) by lia. exact HT.
  - rewrite !Z.testbit_mod_pow2 by lia. rewrite (proj2 (Z.ltb_ge j 64)) by lia. reflexivity.
Qed.

(* Every side-stack metadata cell lies in [FS, FS + 36864) (A/Prog/Seg/P2.v p2_fs_meta_range). *)
Lemma r21_fs_meta_range : forall FS q, fs_meta FS q -> FS <= q < FS + 36864.
Proof.
  intros FS q H. split; [|exact (fs_meta_below FS q H)].
  destruct H as [H | [H | [ [c [Hc Hr]] | [c [j [Hc [Hj Heq]]]] ]]].
  - lia.
  - lia.
  - unfold ACw.a_fs_hint in Hr. lia.
  - subst q. exact (proj1 (a_fs_flag_range FS c j Hc Hj)).
Qed.

(* n present bytes form a byte run. *)
Lemma a_bytes_of_present : forall (n : nat) (m : word -> option byte) a,
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall k, (k < n)%nat -> exists b, mrd rsegs m (wa (a + Z.of_nat k)) = Some b) ->
  exists bs, bytes_at rsegs m a bs /\ length bs = n.
Proof.
  induction n as [|n IH]; intros m a Ha Hn H.
  - exists []. split; [|reflexivity]. split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
    intros i Hi. cbn [length] in Hi. lia.
  - destruct (H 0%nat ltac:(lia)) as (b & Hb). replace (a + Z.of_nat 0) with a in Hb by lia.
    destruct (IH m (a + 1) ltac:(lia) ltac:(lia)) as (bs & HBs & HL).
    { intros k Hk. replace (a + 1 + Z.of_nat k) with (a + Z.of_nat (S k)) by lia. apply H. lia. }
    exists (b :: bs). split; [|cbn [length]; lia].
    change (b :: bs) with ([b] ++ bs).
    apply (proj2 (bytes_at_app rsegs m a [b] bs)). split.
    + split; [lia|]. split; [cbn [length Z.of_nat]; lia|].
      intros i Hi. cbn [length] in Hi. assert (Ei : i = 0%nat) by lia. subst i.
      replace (a + Z.of_nat 0) with a by lia. cbn [nth_error]. exact Hb.
    + cbn [length]. replace (a + Z.of_nat 1) with (a + 1) by lia. exact HBs.
Qed.

(* ADDR-KEEP for a run whose write set misses the shadow bytes of the range (AsanRTFacts addressable_kept,
   restricted to the range's own shadow bytes: the latch writes OTHER frame-shadow bytes). *)
Lemma a_addr_keep_rng : forall m m' W p n,
  addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> Frame.outside W (shadow_addr (p + i))) ->
  addressable m' p n.
Proof.
  intros m m' W p n HA MU HO. pose proof HA as (H1 & H2 & H3 & H).
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hk). split; [exact Ha|]. exists b. split; [|exact Hk].
  pose proof (shadow_of_app (p + i) Ha) as IS. pose proof (in_shadow_range _ IS) as IR.
  unfold mrd in Hb |- *. rewrite (MU (wa (shadow_addr (p + i)))); [exact Hb|].
  rewrite Mem.wa_unsigned by lia. exact (HO i Hi).
Qed.

(* One CB cell's rw_cells across a run whose write set W misses the cell's bytes. *)
Lemma r21_rwcb_keep : forall W (m m' : word -> option byte) a n bs,
  munch W m m' -> wmono rsegs m m' ->
  (forall x, a <= x < a + Z.of_nat n -> Frame.outside W x) ->
  rw_cells rsegs m a [CB n bs] -> rw_cells rsegs m' a [CB n bs].
Proof.
  intros W m m' a n bs MU WM HO ((Hwf & Hb) & Hw).
  assert (Hlen : length bs = n) by (destruct Hwf as (Hl & _); exact Hl).
  split; [split; [exact Hwf|]|].
  - apply (a_keep W m m' a _ MU); [|exact Hb]. intros x Hx.
    cbn [cells_bytes cbytes] in Hx. rewrite app_nil_r, Hlen in Hx. exact (HO x Hx).
  - destruct Hw as (Hw0 & Hw1 & Hw). split; [exact Hw0|]. split; [exact Hw1|].
    intros i Hi. exact (WM _ (Hw i Hi)).
Qed.

(* A word cell from its 8 bytes and their writability (the spill [A + 192] as Inv_A81ac0 / Inv_A81ac8 state it). *)
Lemma r21_rw_c8 : forall (m : word -> option byte) a v,
  bytes_at rsegs m a (le8 (Z_to_bv 64 v)) ->
  (forall i, 0 <= i < 8 -> writable_at rsegs m (a + i)) ->
  rw_cells rsegs m a [C8 (Z_to_bv 64 v)].
Proof.
  intros m a v Hb Hw. pose proof Hb as Hbd. apply bytes_at_bound in Hbd. rewrite length_le8 in Hbd.
  split; [split; [cbn; exact (conj I I) | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb]|].
  split; [lia|]. split; [cbn [cells_size csize]; lia|].
  intros i Hi. cbn [cells_size csize] in Hi. exact (Hw i ltac:(lia)).
Qed.

(* RXS (push 10) across a run that keeps the spills [A + 0] .. [A + 224) and the fragment record's addressability
   (R21's latch hands it to Inv_A815cc_at (S b)). *)
Lemma r21_rxs_keep : forall g fr regs regs' (m m' : word -> option byte),
  (forall off v, 0 <= off <= 216 -> spill regs m off v -> spill regs' m' off v) ->
  (addressable m (fr + 2256) 72 -> addressable m' (fr + 2256) 72) ->
  RXS g fr regs m -> RXS g fr regs' m'.
Proof.
  intros g fr regs regs' m m' Hs Ha (H48 & H56 & H88 & H80 & H72 & H16 & H8 & H192 & H216 & HA).
  split; [exact (Hs 48 _ ltac:(lia) H48)|].
  split; [exact (Hs 56 _ ltac:(lia) H56)|].
  split; [exact (Hs 88 _ ltac:(lia) H88)|].
  split; [exact (Hs 80 _ ltac:(lia) H80)|].
  split; [exact (Hs 72 _ ltac:(lia) H72)|].
  split; [exact (Hs 8 _ ltac:(lia) H16)|].
  split; [exact (Hs 0 _ ltac:(lia) H8)|].
  split; [exact (Hs 200 _ ltac:(lia) H192)|].
  split; [exact (Hs 216 _ ltac:(lia) H216) | exact (Ha HA)].
Qed.

(* PRO (push 13B, push 14D) across a run that keeps the spills [A + 32] .. [A + 280), our[]'s 6 bytes addressable
   and the input block: its bytes, and its addressability when it is a live block of the entry heap (R21's latch
   hands PRO to Inv_A815cc_at (S b), its tail to Inv_A81ac0 / Inv_A81ac8). *)
Lemma r21_pro_keep : forall g fr regs regs' (m m' : word -> option byte),
  (forall off v, 32 <= off <= 272 -> spill regs m off v -> spill regs' m' off v) ->
  (addressable m (fr + 2624) 6 -> addressable m' (fr + 2624) 6) ->
  ((0 < g_n g -> In (g_p g, g_n g) (g_H g)) ->
     bytes_at rsegs m (g_p g) (g_in g) -> bytes_at rsegs m' (g_p g) (g_in g)) ->
  (In (g_p g, g_n g) (g_H g) -> addressable m (g_p g) (g_n g) -> addressable m' (g_p g) (g_n g)) ->
  PRO g fr regs m -> PRO g fr regs' m'.
Proof.
  intros g fr regs regs' m m' Hs Ha6 Hb Hia
    (H40 & H120 & H136 & H160 & H168 & H176 & H200 & H248 & HA6 & HIN & HG & H184 & H256 & H264 & H272 & H32).
  split; [exact (Hs 40 _ ltac:(lia) H40)|].
  split; [exact (Hs 120 _ ltac:(lia) H120)|].
  split; [exact (Hs 136 _ ltac:(lia) H136)|].
  split; [exact (Hs 160 _ ltac:(lia) H160)|].
  split; [exact (Hs 168 _ ltac:(lia) H168)|].
  split; [exact (Hs 176 _ ltac:(lia) H176)|].
  split; [exact (Hs 208 _ ltac:(lia) H200)|].
  split; [exact (Hs 248 _ ltac:(lia) H248)|].
  split; [exact (Ha6 HA6)|].
  split; [exact (Hb (fun Hn => proj1 (HG Hn)) HIN)|].
  split; [intros Hn; destruct (HG Hn) as (HH & HA); split; [exact HH | exact (Hia HH HA)]|].
  split; [exact (Hs 184 _ ltac:(lia) H184)|].
  split; [exact (Hs 256 _ ltac:(lia) H256)|].
  split; [exact (Hs 264 _ ltac:(lia) H264)|].
  split; [exact (Hs 272 _ ltac:(lia) H272) | exact (Hs 32 _ ltac:(lia) H32)].
Qed.

(* Every registered global of frame_AG lies in the image, below GT. *)
Definition a_AGb : bool :=
  forallb (fun p => (0 <=? fst p) && (fst p + snd p <=? 6283264)) AFw.frame_AG.

Lemma a_AGb_true : a_AGb = true.
Proof. vm_compute. reflexivity. Qed.

Lemma a_AG_lt : forall a, in_globals AFw.frame_AG a -> 0 <= a < 6283264.
Proof.
  intros a (lo & len & Hin & Hr).
  pose proof a_AGb_true as HB. unfold a_AGb in HB. rewrite forallb_forall in HB.
  specialize (HB (lo, len) Hin). cbn [fst snd] in HB.
  apply andb_true_iff in HB as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* The catalogue is one of the registered globals. *)
Lemma a_cat_inAG : forall a, CAT <= a < CAT + 3256 -> in_globals AFw.frame_AG a.
Proof.
  intros a Ha. exists CAT, 3256. split; [|exact Ha].
  unfold AFw.frame_AG, CAT. cbn [In]. repeat (first [ left; reflexivity | right ]).
Qed.

(* ---- Read-only bytes and the spill base, for the transport across the strcmp wrapper's stack window ---- *)

(* The A image's loaded segments all end at or below 0x5fe000 (= GT), so every read-only address is below it. *)
Lemma r21_hull : forall s, In s rsegs -> Z.of_N (seg_base s) + Z.of_N (seg_size s) <= 6283264.
Proof.
  assert (H : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? 6283264) rsegs = true)
    by (vm_compute; reflexivity).
  intros s Hin. apply Z.leb_le. rewrite forallb_forall in H. exact (H s Hin).
Qed.

(* A read-only address lies in the image, hence below 0x5fe000. *)
Lemma r21_ro_lt : forall a : word, ro_addr rsegs a = true -> bv_unsigned a < 6283264.
Proof.
  intros a H. unfold ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  pose proof (YK1j.find_segment_in rsegs (bv_unsigned a) 1 s E) as Hin.
  pose proof (YK1j.find_segment_range rsegs (bv_unsigned a) 1 s E) as (_ & Hhi).
  pose proof (r21_hull s Hin) as Hb. lia.
Qed.

(* ro_agree is kept by a store whose write set W avoids every read-only address (all in the low image). *)
Lemma r21_ro_keep : forall (mem mem' : word -> option byte) (W : list Frame.ivl),
  ro_agree rsegs mem -> Frame.munch W mem mem' ->
  (forall a : word, ro_addr rsegs a = true -> Frame.outside W (bv_unsigned a)) ->
  ro_agree rsegs mem'.
Proof.
  intros mem mem' W HRO MU Hout a Hro. unfold mrd. rewrite (MU a (Hout a Hro)). exact (HRO a Hro).
Qed.

(* A byte at [A0 + 16, A0 + 312) with Z_to_bv 64 A0 = Z_to_bv 64 A lies outside any [lo, hi) with 0 <= lo and
   hi <= A, for every 64-bit representative A0 of A. *)
Lemma r21_wrap_out : forall A A0 lo hi x, Z_to_bv 64 A = Z_to_bv 64 A0 -> 0 <= A -> A + 312 <= 2 ^ 64 ->
  0 <= lo -> hi <= A -> A0 + 16 <= x < A0 + 312 -> ~ (lo <= x < hi).
Proof.
  intros A A0 lo hi x E H0 H1 Hlo Hhi Hx.
  assert (Ew : A mod 2 ^ 64 = A0 mod 2 ^ 64).
  { apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. exact E. }
  rewrite (Z.mod_small A (2 ^ 64)) in Ew by lia.
  pose proof (Z.div_mod A0 (2 ^ 64) ltac:(lia)) as Hdm. rewrite <- Ew in Hdm.
  remember (A0 / 2 ^ 64) as q eqn:Eq. clear Eq.
  change (2 ^ 64) with 18446744073709551616 in *. lia.
Qed.

Section R21W.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, ACw.AsanAllocAPI ACw.ASYMS AsanRTInv.RT.
Context {SHd : sink_head} {SKd : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SHd SKd ra empty.

(* The allocator laws whose inner lists this file takes apart (Contract.v, a Theorem Labs lane's v1.9 generation), each restated
   once here, so that a law that gains or moves a conjunct breaks this one proof and no use site (a Theorem Labs lane 15:32Z). *)
Local Notation law_AH := (ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_own := (ACw.aa_owned ACw.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_lo := (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_hi := (ACw.aa_stkhi ACw.ASYMS AsanRTInv.RT (APIf rc)).

Lemma r21_law_blocks : forall H mem md p n, law_AH H mem md -> In (p, n) H ->
  p mod 16 = 0 /\ 4096 <= p /\ p + n <= law_lo mem md /\ end_in_app p n /\
  forall a, p <= a < p + n -> app_mem a /\ writable_at rsegs mem a /\ ~ ACw.a_in_img a /\ ~ ACw.a_on_img_page a /\
    ~ ACw.a_in_fs ACw.ASYMS mem a.
Proof. exact (ACw.a_laws_blocks _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r21_law_fs_place : forall H mem md b, law_AH H mem md -> word_mem rsegs mem (ACw.as_tp ACw.ASYMS) b -> 0 <= b < 2 ^ 64 ->
  ACw.GT <= b /\ b + ACw.FS_SIZE <= law_lo mem md /\ b mod 4096 = 0 /\ forall a, b <= a < b + ACw.FS_SIZE -> app_mem a.
Proof. exact (ACw.a_laws_fs_place _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r21_law_fs_ok : forall H mem md FS, law_AH H mem md -> word_mem rsegs mem (ACw.as_tp ACw.ASYMS) FS ->
  0 <= FS < 2 ^ 64 -> ACw.a_fs_ok mem FS.
Proof.
  intros H mem md FS HAH Hw Hb.
  exact (proj1 (ACw.a_laws_fs_state _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) H mem md FS HAH Hw Hb)).
Qed.

Lemma r21_law_store : forall H mem mem' md, law_AH H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ACw.a_store_ok H (law_lo mem md) a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  law_AH H mem' md /\ (forall a, law_own H mem' md a <-> law_own H mem md a) /\ law_lo mem' md = law_lo mem md /\
  law_hi mem' md = law_hi mem md.
Proof. exact (ACw.a_laws_store _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r21_law_fs_store : forall H mem mem' md FS, law_AH H mem md -> word_mem rsegs mem (ACw.as_tp ACw.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ACw.a_store_ok H (law_lo mem md) a -> ~ (FS <= a < FS + ACw.FS_SIZE) ->
     ~ (exists b, FS <= b < FS + ACw.FS_SIZE /\ a = shadow_addr b) -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) -> ACw.a_fs_ok mem' FS ->
  law_AH H mem' md /\ (forall a, law_own H mem' md a <-> law_own H mem md a) /\ law_lo mem' md = law_lo mem md /\
  law_hi mem' md = law_hi mem md.
Proof. exact (ACw.a_laws_fs_store _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc))). Qed.

(* The frame's 3136 bytes are application memory above GT (fra_app), so the frame base is a 64-bit address. *)
Lemma r21_frame_app : forall g fr hb regs mem md,
  FRA B APIf ra g fr hb regs mem md ->
  (forall a, fr <= a < fr + FRAME_BYTES -> app_mem a) /\ ACw.GT <= fr /\ 0 <= fr /\ fr + 8 <= 2 ^ 64.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs mem md HFRA.
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGT & Happ).
  pose proof (Happ fr ltac:(lia)) as Hf0. pose proof (Happ (fr + 7) ltac:(lia)) as Hf7.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hf0, Hf7.
  split; [exact Happ|]. split; [exact HGT|]. split; lia.
Qed.

(* The frame's shadow byte at offset k is the shadow of the frame byte at offset 8 k. *)
Lemma r21_shadow_off : forall fr k, 0 <= k -> shadow_addr (fr + k * 8) = Sfr fr + k.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr k Hk. unfold Sfr, shadow_addr. rewrite Z.div_add by lia. lia.
Qed.

(* FRA and ENT across a write of a range of the frame's own 392 shadow bytes (A/Prog/Seg/P2.v, one byte -> a
   range): FRA by Tac_slot.sl_fr_meta, ENT by Tac_slot.ent_store (the written bytes are the frame's shadow). The
   registered globals' shadow bytes must be outside the written range (their addressability is an FRA fact). *)
Lemma r21_fr_shadow : forall g fr hb regs regs' mem mem' md (lo hi : Z),
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  0 <= lo -> lo <= hi -> hi <= FRAME_SHADOW ->
  Frame.munch [(Sfr fr + lo, Sfr fr + hi)] mem mem' ->
  Frame.wmono rsegs mem mem' ->
  (forall q, Sfr fr + lo <= q < Sfr fr + hi -> exists b, mrd rsegs mem' (wa q) = Some b) ->
  (forall a, in_globals AFw.frame_AG a -> Frame.outside [(Sfr fr + lo, Sfr fr + hi)] (shadow_addr a)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  FRA B APIf ra g fr hb regs' mem' md /\ ENT APIf g hb mem' md.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md lo hi HFRA HENT Hlo Hlh Hhi MU WM HPres HAGout
    E2 E3 E4 E8 E9 E19 E26.
  pose proof (r21_frame_app g fr hb regs mem md HFRA) as (Happ & HGT & Hfr0 & Hfr8b).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (ACw.a_laws_stack_high _ _ _ _ _ ALAWS (hb ++ g_H g) mem md HAH) as Hstkhigh.
  assert (HSfrlo : ASAN_K <= Sfr fr)
    by (unfold Sfr, shadow_addr; pose proof (Z.div_pos fr 8 Hfr0 ltac:(lia)); lia).
  assert (HAlo : HIGHMEM_BEG <= A) by (unfold AFw.SLOT_STACK in Hstklo; lia).
  assert (HAhi : A + 312 <= 2 ^ 64).
  { unfold q64 in Hspill. apply bytes_at_bound in Hspill. rewrite length_le8 in Hspill. lia. }
  (* every written address is the shadow of a frame byte, and so in the shadow map *)
  assert (Hinsh : forall x, Sfr fr + lo <= x < Sfr fr + hi -> in_shadow x).
  { intros x Hx. replace x with (shadow_addr (fr + (x - Sfr fr) * 8))
      by (rewrite r21_shadow_off by lia; lia).
    apply shadow_of_app. apply Happ. lia. }
  assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x).
  { intros x Hx Hwx. exact (WM (Z_to_bv 64 x) Hwx). }
  assert (Hout : forall x, 0 <= x < 2 ^ 64 -> ~ (Sfr fr + lo <= x < Sfr fr + hi) ->
                   mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
  { intros x Hx Hn. apply MU. rewrite MState.unsigned_lit by exact Hx.
    cbn [Frame.outside]. split; [exact Hn | exact I]. }
  assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
            exists b, mbyte rsegs mem' q = Some b).
  { intros q Hq Hb.
    destruct (Z_lt_le_dec q (Sfr fr + lo)) as [H1|H1].
    - unfold mbyte. rewrite (Hout q Hq ltac:(lia)). exact Hb.
    - destruct (Z_lt_le_dec q (Sfr fr + hi)) as [H2|H2].
      + exact (HPres q ltac:(lia)).
      + unfold mbyte. rewrite (Hout q Hq ltac:(lia)). exact Hb. }
  (* AH, the runtime-owned bytes, stklo and stkhi after the write, per frame-location arm *)
  assert (AHSTK : ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
                  (forall a, ACw.aa_owned ACw.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md a <->
                             ACw.aa_owned ACw.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md a) /\
                  ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem' md
                    = ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                  ACw.aa_stkhi ACw.ASYMS AsanRTInv.RT (APIf rc) mem' md
                    = ACw.aa_stkhi ACw.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { destruct Hloc as [(Hs50 & Hspfr & Hreal)|(Hs5fr & HfsbS & Hfs & _)].
    - (* real arm: the written shadow bytes are shadows of real-stack bytes (a_store_ok) *)
      assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
                ~ ACw.a_store_ok (hb ++ g_H g) (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
      { intros x Hx Hnok.
        destruct (Z_lt_le_dec x (Sfr fr + lo)) as [H1|H1]; [exact (Hout x Hx ltac:(lia))|].
        destruct (Z_lt_le_dec x (Sfr fr + hi)) as [H2|H2]; [|exact (Hout x Hx ltac:(lia))].
        exfalso. apply Hnok. right. right. right. exists (fr + (x - Sfr fr) * 8).
        split; [symmetry; rewrite r21_shadow_off by lia; lia|]. right. left.
        specialize (Hreal (fr + (x - Sfr fr) * 8) ltac:(lia)). lia. }
      destruct (r21_law_store (hb ++ g_H g) mem mem' md HAH Hmc Hwrit)
        as (HAH' & Hown' & Hstk' & Hshi').
      split; [exact HAH'|]. split; [exact Hown'|]. split; [exact Hstk' | exact Hshi'].
    - (* side arm: the written shadow bytes are shadows of side-stack bytes (a_laws_fs_store) *)
      pose proof (AsanRTInv.RT_fs_cells _ _ _ HRT) as HFSC.
      destruct HFSC as (_ & _ & _ & _ & (FSw & HFSb & Hfsok) & _).
      apply bytes_at_le8_word in HFSb.
      pose proof (u64_range FSw) as HFSr.
      destruct Hfsok as (HF0 & _ & HFGT & HFapp).
      assert (Happtop : app_mem (bv_unsigned FSw + RT_FS_SIZE - 1)) by (apply HFapp; unfold RT_FS_SIZE; lia).
      unfold AsanRT.RT_GT in HFGT.
      unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END, RT_FS_SIZE in Happtop.
      assert (HinFS : forall a0, fr <= a0 < fr + FRAME_BYTES ->
                bv_unsigned FSw <= a0 < bv_unsigned FSw + ACw.FS_SIZE).
      { intros a0 Ha0. pose proof (Happ a0 Ha0) as Hap0.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hap0.
        specialize (Hfs a0 Ha0). unfold ACw.a_in_fs in Hfs. destruct Hfs as (b & Hb64 & Hwm & Hb2).
        change (ACw.as_tp ACw.ASYMS) with AsanRT.RT_TP in Hwm.
        pose proof (r21_wm_congr mem AsanRT.RT_TP b (bv_unsigned FSw) Hwm HFSb) as Hcong.
        unfold ACw.FS_SIZE in Hb2 |- *.
        assert (Hbeq : b = bv_unsigned FSw)
          by (revert Hcong Hb64 Hb2 Happtop HFGT HFSr Ha0 Hap0 Hfr0; Z.div_mod_to_equations; lia).
        subst b. lia. }
      pose proof (r21_law_fs_ok (hb ++ g_H g) mem md (bv_unsigned FSw) HAH HFSb ltac:(lia))
        as Hfsok0.
      assert (Hmeta : forall q, fs_meta (bv_unsigned FSw) q ->
                Frame.outside [(Sfr fr + lo, Sfr fr + hi)] q).
      { intros q Hq. pose proof (r21_fs_meta_range _ _ Hq) as Hqr.
        assert (Hqa : app_mem q) by (apply HFapp; unfold RT_FS_SIZE; lia).
        cbn [Frame.outside]. split; [|exact I]. intros Hqt.
        exact (app_not_shadow _ Hqa (Hinsh q Hqt)). }
      assert (Hfsok' : ACw.a_fs_ok mem' (bv_unsigned FSw)).
      { apply (a_fs_ok_pres [(Sfr fr + lo, Sfr fr + hi)] mem mem' (bv_unsigned FSw) Hfsok0 MU Hwrit Hpres Hmeta);
          unfold ACw.FS_SIZE; lia. }
      assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
                ~ ACw.a_store_ok (hb ++ g_H g) (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) x ->
                ~ (bv_unsigned FSw <= x < bv_unsigned FSw + ACw.FS_SIZE) ->
                ~ (exists b, bv_unsigned FSw <= b < bv_unsigned FSw + ACw.FS_SIZE /\ x = shadow_addr b) ->
                mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
      { intros x Hx Hnok Hnfs Hnsh.
        destruct (Z_lt_le_dec x (Sfr fr + lo)) as [H1|H1]; [exact (Hout x Hx ltac:(lia))|].
        destruct (Z_lt_le_dec x (Sfr fr + hi)) as [H2|H2]; [|exact (Hout x Hx ltac:(lia))].
        exfalso. apply Hnsh. exists (fr + (x - Sfr fr) * 8).
        split; [apply HinFS; lia | symmetry; rewrite r21_shadow_off by lia; lia]. }
      destruct (r21_law_fs_store (hb ++ g_H g) mem mem' md (bv_unsigned FSw) HAH HFSb
                  ltac:(lia) Hmc Hwrit Hfsok') as (HAH' & Hown' & Hstk' & Hshi').
      split; [exact HAH'|]. split; [exact Hown'|]. split; [exact Hstk' | exact Hshi']. }
  destruct AHSTK as (HAH' & HOWN' & HSTK' & HSHI').
  unfold rg in Hr9.
  assert (HA9 : forall A0, getr regs 9 = Z_to_bv 64 A0 -> A0 mod 2 ^ 64 = A).
  { intros A0 HA0.
    pose proof (f_equal (@bv_unsigned 64) (eq_trans (eq_sym Hr9) HA0)) as E0.
    rewrite !Z_to_bv_unsigned in E0. unfold bv_wrap, bv_modulus in E0.
    change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in E0.
    rewrite (Z.mod_small A (2 ^ 64)) in E0 by (unfold HIGHMEM_BEG in HAlo; lia).
    symmetry; exact E0. }
  assert (HshiHi : Sfr fr + hi <= HIGHMEM_BEG \/ lo = hi).
  { destruct (Z.eq_dec lo hi) as [E|Hne]; [right; exact E|left].
    pose proof (Hinsh (Sfr fr + (hi - 1)) ltac:(lia)) as IS.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in IS |- *. lia. }
  (* the new 392 shadow bytes *)
  destruct Hsh as (sh0 & Hb0 & HL0).
  pose proof (bytes_at_bound rsegs mem (Sfr fr) sh0 Hb0) as Hb0r. rewrite HL0 in Hb0r.
  assert (Hsh' : exists sh, bytes_at rsegs mem' (Sfr fr) sh /\ length sh = Z.to_nat FRAME_SHADOW).
  { apply (a_bytes_of_present (Z.to_nat FRAME_SHADOW) mem' (Sfr fr)); [lia | lia |].
    intros k Hk.
    pose proof (proj2 (proj2 Hb0) k ltac:(lia)) as Hb0k.
    destruct (nth_error sh0 k) as [b|] eqn:Ek; [|exfalso; apply nth_error_None in Ek; lia].
    destruct (Z_lt_le_dec (Sfr fr + Z.of_nat k) (Sfr fr + lo)) as [H1|H1].
    - exists b. unfold mrd, wa in Hb0k |- *. rewrite (Hout (Sfr fr + Z.of_nat k) ltac:(lia) ltac:(lia)). exact Hb0k.
    - destruct (Z_lt_le_dec (Sfr fr + Z.of_nat k) (Sfr fr + hi)) as [H2|H2].
      + exact (HPres (Sfr fr + Z.of_nat k) ltac:(lia)).
      + exists b. unfold mrd, wa in Hb0k |- *. rewrite (Hout (Sfr fr + Z.of_nat k) ltac:(lia) ltac:(lia)). exact Hb0k. }
  assert (HAG' : forall a, in_globals AFw.frame_AG a -> addressable mem' a 1).
  { intros a Ha. exact (addr1_munch _ mem mem' a MU (HAGout a Ha) (HAG a Ha)). }
  split.
  { apply (sl_fr_meta B APIf ra empty FF g fr hb regs regs' mem mem'
             md [(Sfr fr + lo, Sfr fr + hi)] HFRA MU WM); try assumption.
    - apply (r21_ro_keep mem mem' _ Hro MU). intros a Ha.
      pose proof (r21_ro_lt a Ha) as Hlt. cbn [Frame.outside]. split; [|exact I].
      unfold ASAN_K in HSfrlo. lia.
    - unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB,
        RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI,
        RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN. cbn [disjoint_from]. unfold ASAN_K in HSfrlo.
      repeat split; (lia || exact I).
    - intros x Hx Hnb Hnsh. cbn [Frame.outside]. split; [|exact I]. lia.
    - intros A0 HA0 HA0r x Hx. cbn [Frame.outside]. split; [|exact I].
      pose proof (HA9 A0 HA0) as HA0e. unfold HIGHMEM_BEG in HAlo.
      destruct HshiHi as [Hhx|Hhx]; unfold HIGHMEM_BEG in *; revert Hx HA0e; Z.div_mod_to_equations; lia.
    - intros x Hx. cbn [Frame.outside]. split; [|exact I].
      destruct HshiHi as [Hhx|Hhx]; unfold HIGHMEM_BEG in *; lia.
    - intros A0 HA0 HA0r x Hx. cbn [Frame.outside]. split; [|exact I].
      pose proof (HA9 A0 HA0) as HA0e. unfold HIGHMEM_BEG in HAlo.
      destruct HshiHi as [Hhx|Hhx]; unfold HIGHMEM_BEG in *; revert Hx HA0e; Z.div_mod_to_equations; lia.
    - intros x Hx. left. cbn [Frame.outside]. split; [|exact I].
      unfold AFw.SLOT_STACK in *. unfold HIGHMEM_BEG in *.
      destruct HshiHi as [Hhx|Hhx]; lia. }
  assert (HWcase : forall x, 0 <= x < 2 ^ 64 -> Frame.outside [(Sfr fr + lo, Sfr fr + hi)] x \/
    (g_S g - AFw.SLOT_STACK <= x < g_S g) \/ (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
  { intros x Hx.
    destruct (Z_le_gt_dec (Sfr fr + lo) x) as [H1|H1];
      [ destruct (Z_lt_ge_dec x (Sfr fr + hi)) as [H2|H2];
        [ right; right; right; lia
        | left; cbn [Frame.outside]; split; [lia | exact I] ]
      | left; cbn [Frame.outside]; split; [lia | exact I] ]. }
  eapply ent_store;
    [ exact HENT | exact HFRA | exact MU | exact HWcase | exact HSTK' | exact HSHI'
    | intros a _ Hw; exact (proj2 (HOWN' a) Hw) ].
Qed.

(* A spill is a word at s1 + off: the spill's own base is the FRA base A (both are 64-bit addresses). *)
Lemma a_spill_A : forall regs m off w A, rg regs 9 A -> HIGHMEM_BEG <= A -> A + 312 <= 2 ^ 64 ->
  0 <= off <= 304 -> spill regs m off w -> q64 m (A + off) w.
Proof.
  intros regs m off w A HA HAlo HAhi Hoff (A0 & HA0 & HQ).
  assert (E : A0 = A).
  { unfold rg in HA, HA0. rewrite HA in HA0.
    apply (f_equal (@bv_unsigned 64)) in HA0. rewrite !Z_to_bv_unsigned in HA0.
    unfold bv_wrap, bv_modulus in HA0. change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z in HA0.
    rewrite (Z.mod_small A (2 ^ 64)) in HA0 by (unfold HIGHMEM_BEG in HAlo; lia).
    unfold q64 in HQ. apply bytes_at_bound in HQ. rewrite length_le8 in HQ.
    unfold HIGHMEM_BEG in HAlo. revert HA0 HQ. Z.div_mod_to_equations. lia. }
  subst A0. exact HQ.
Qed.

(* ---- Push 7 (7A / 7B) and push 9: the pointer spills [A + 144] = fr + 2688, [A + 192] = fr + 2768,
   [A + 280] = fr + 3040 and [A + 240] = fr + 3056 and the frame cells at fr + 2688 (38 bytes), fr + 2768 (72),
   fr + 3040 (1) and fr + 3056 (32), in the B3 cuts' order.  R21P7 is the block R21 carries from the 0x81924
   entry through the latch (back to Inv_A815cc_at, or to Inv_A81990_l); r21_p7_keep moves it across a run whose
   write set misses the spill area [A + 24, A + 312) and the frame; r21_p7_exit turns it into the record block of
   Inv_A81ac0 / Inv_A81ac8 (s11 = fr + 2688 from 0x81994 `ld s11,144(s1)`, the spill [A + 192] as a readable and
   writable word cell, the spills [A + 280] / [A + 240] as words).  A later set of the same kind is added to
   these three only. ---- *)
Definition R21P7 (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
  (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
  spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
  (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]).

Lemma r21_p7_keep : forall fr regs regs' m m' W A,
  rg regs 9 A -> HIGHMEM_BEG <= A -> A + 312 <= 2 ^ 64 -> getr regs' 9 = getr regs 9 ->
  munch W m m' -> wmono rsegs m m' ->
  (forall x, A + 24 <= x < A + 312 -> Frame.outside W x) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x) ->
  R21P7 fr regs m -> R21P7 fr regs' m'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros fr regs regs' m m' W A HA HAlo HAhi E9 MU WM HOA HOF
    (H144 & H208 & (idb & Hi) & (junk & Hj) & H280 & H240 & (jy & Hy) & (sc & Hsc)).
  assert (KS : forall off v, 24 <= off <= 304 -> spill regs m off v -> spill regs' m' off v).
  { intros off v Hoff Hs. pose proof (a_spill_A regs m off v A HA HAlo HAhi ltac:(lia) Hs) as HQ.
    exists A. split; [unfold rg in HA |- *; rewrite E9; exact HA|].
    unfold q64 in HQ |- *. apply (a_keep W m m' _ _ MU); [|exact HQ].
    intros x Hx. rewrite length_le8 in Hx. apply HOA. lia. }
  assert (KC : forall ca cn cbs, fr <= ca -> ca + Z.of_nat cn <= fr + FRAME_BYTES ->
            rw_cells rsegs m ca [CB cn cbs] -> rw_cells rsegs m' ca [CB cn cbs]).
  { intros ca cn cbs Ha1 Ha2 HC. apply (r21_rwcb_keep W m m' _ _ _ MU WM); [|exact HC].
    intros x Hx. apply HOF. lia. }
  split; [exact (KS 144 (fr + 2688) ltac:(lia) H144)|].
  split; [exact (KS 192 (fr + 2768) ltac:(lia) H208)|].
  split; [exists idb; exact (KC (fr + 2688) 38%nat idb ltac:(lia) ltac:(lia) Hi)|].
  split; [exists junk; exact (KC (fr + 2768) 72%nat junk ltac:(lia) ltac:(lia) Hj)|].
  split; [exact (KS 280 (fr + 3040) ltac:(lia) H280)|].
  split; [exact (KS 240 (fr + 3056) ltac:(lia) H240)|].
  split; [exists jy; exact (KC (fr + 3040) 1%nat jy ltac:(lia) ltac:(lia) Hy)|].
  exists sc. exact (KC (fr + 3056) 32%nat sc ltac:(lia) ltac:(lia) Hsc).
Qed.

Lemma r21_p7_exit : forall fr regs m A,
  getr regs 9 = Z_to_bv 64 A -> HIGHMEM_BEG <= A -> A + 312 <= 2 ^ 64 -> rg regs 27 (fr + 2688) ->
  (forall i, 0 <= i < 8 -> writable_at rsegs m (A + 192 + i)) ->
  R21P7 fr regs m ->
  exists (A0 : Z) (idb junk : list byte),
    getr regs 9 = Z_to_bv 64 A0 /\ rg regs 27 (fr + 2688) /\ 0 <= A0 < 2 ^ 64 /\
    rw_cells rsegs m (A0 + 192) [C8 (Z_to_bv 64 (fr + 2768))] /\
    rw_cells rsegs m (fr + 2688) [CB 38 idb] /\
    rw_cells rsegs m (fr + 2768) [CB 72 junk] /\
    q64 m (A0 + 280) (fr + 3040) /\ q64 m (A0 + 240) (fr + 3056) /\
    (exists jy junk2 : list byte, rw_cells rsegs m (fr + 3040) [CB 1 jy] /\ rw_cells rsegs m (fr + 3056) [CB 32 junk2]).
Proof.
  intros fr regs m A HA HAlo HAhi H27 HW
    (_ & H208 & (idb & Hi) & (junk & Hj) & H280 & H240 & (jy & Hy) & (sc & Hsc)).
  exists A, idb, junk.
  split; [exact HA|]. split; [exact H27|]. split; [unfold HIGHMEM_BEG in HAlo; lia|].
  split.
  { apply r21_rw_c8; [exact (a_spill_A regs m 192 (fr + 2768) A HA HAlo HAhi ltac:(lia) H208) | exact HW]. }
  split; [exact Hi|]. split; [exact Hj|].
  split; [exact (a_spill_A regs m 280 (fr + 3040) A HA HAlo HAhi ltac:(lia) H280)|].
  split; [exact (a_spill_A regs m 240 (fr + 3056) A HA HAlo HAhi ltac:(lia) H240)|].
  exists jy, sc. split; [exact Hy | exact Hsc].
Qed.

(* Push 11A: the exits' CUR g (c0 (g_in g)) from the round trip's CUR g 7, when s6 / s9 are kept and
   c0 (g_in g) = 7. *)
Lemma r21_cur_exit : forall g regs regs',
  CUR g 7 regs -> getr regs' 22 = getr regs 22 -> getr regs' 25 = getr regs 25 -> c0 (g_in g) = 7 ->
  CUR g (c0 (g_in g)) regs'.
Proof.
  intros g regs regs' (Hc0 & Hc22 & Hc25) E22 E25 Ec0. rewrite Ec0. unfold CUR, rg in *.
  split; [exact Hc0|]. split; [rewrite E22; exact Hc22 | rewrite E25; exact Hc25].
Qed.

(* FRA and ENT move across a program callee whose post is a munch of its own stack window [sp - K, sp) with the
   window [sp - FN_STACK, sp) still backed (the strcmp wrapper at 0x81abc), and across the lazy-page
   materialization md -> md' of the run. The callee's window is app memory at or above HIGHMEM_BEG <= stklo <=
   sp - FN_STACK (a_store_ok, so AH, the owned bytes, stklo and stkhi by a_laws_store), below the spill base
   A >= sp and the saved registers at S >= A, apart from the frame (the caller's disjunction), and above the
   frame's shadow and the image. *)
Lemma r21_callee_keep : forall g fr hb regs regs' mem mem' md md' K,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  Frame.munch [(ACw.aspZ regs - K, ACw.aspZ regs)] mem mem' -> Frame.wmono rsegs mem mem' ->
  stk rsegs mem' (ACw.aspZ regs - FN_STACK) (ACw.aspZ regs) ->
  0 <= K <= FN_STACK ->
  (ACw.aspZ regs <= fr \/ fr + FRAME_BYTES <= ACw.aspZ regs - K) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md' /\ ENT APIf g hb mem' md'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr hb regs regs' mem mem' md md' K HFRA HENT MU WM HSTKm HK Hfrd E2 E3 E4 E8 E9 E19 E26 Hmat.
  pose proof (r21_frame_app g fr hb regs mem md HFRA) as (Happ & HGT & Hfr0 & Hfr8b).
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwinlo & Hwinstk).
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (ACw.a_laws_stack_high _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc))
                (hb ++ g_H g) mem md HAH) as Hhigh.
  rewrite Haspz in MU, HSTKm, Hwinlo, Hwinstk, Hfrd.
  unfold rg in Hr9.
  assert (HSS : AFw.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HHB : HIGHMEM_BEG = 17594333495296) by reflexivity.
  assert (HAPPv : APPMEM_END = 140737488355328) by reflexivity.
  assert (HAb : 0 <= A /\ A + 312 <= 2 ^ 64).
  { pose proof Hwin as (Hw0 & Hw1 & _). lia. }
  assert (Hfrhi : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Hq.
    unfold app_mem, LOWMEM_END in Hq. unfold ACw.GT in HGT. lia. }
  assert (Hlo : HIGHMEM_BEG <= sp - K) by lia.
  assert (Hout : forall x, x < sp - K \/ sp <= x -> Frame.outside [(sp - K, sp)] x).
  { intros x Hx. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (HWR : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
    by (intros a _ Hw; exact (WM (Z_to_bv 64 a) Hw)).
  assert (P1 : forall a, 0 <= a < 2 ^ 64 ->
            ~ ACw.a_store_ok (hb ++ g_H g) (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
            mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hn. apply MU. rewrite MState.unsigned_lit by exact Ha. apply Hout.
    destruct (Z_lt_le_dec a (sp - K)) as [H1|H1]; [left; exact H1|].
    destruct (Z_lt_le_dec a sp) as [H2|H2]; [|right; exact H2].
    exfalso. apply Hn. unfold ACw.a_store_ok. right. left. split; lia. }
  destruct (r21_law_store (hb ++ g_H g)
              mem mem' md HAH P1 HWR) as (HAH' & HOWN' & HSTK' & HSHI').
  assert (HRDM : MMo.rd_mono mem mem').
  { apply (MMo.rd_mono_list [(sp - K, sp)] mem mem' MU).
    constructor; [|constructor].
    cbn [fst snd]. intros y Hy. exact (MMo.rd_of_stk mem' (sp - FN_STACK) sp HSTKm y ltac:(lia)). }
  assert (HFRAmd : FRA B APIf ra g fr hb regs' mem' md).
  { apply (B3FrCl.b3_fr_cl B APIf ra empty FF g fr hb regs regs' mem mem' md [(sp - K, sp)] HFRA MU WM);
      try assumption.
    - apply (r21_ro_keep mem mem' _ Hro MU). intros a Hroa.
      pose proof (r21_ro_lt a Hroa) as Hlt. apply Hout. left. lia.
    - cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right. lia.
    - unfold rt_disjoint. cbn [disjoint_from].
      unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK,
        RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
      repeat split; left; lia.
    - intros x Hx. apply Hout. left. lia.
    - intros x Hx. apply Hout. destruct Hfrd as [Hd|Hd]; [right; lia | left; lia].
    - intros A0 HA0 _ x Hx. cbn [Frame.outside]. split; [|exact I].
      apply (r21_wrap_out A A0 (sp - K) sp x ltac:(rewrite <- Hr9; exact HA0)); lia.
    - intros A0 HA0 _ x Hx. cbn [Frame.outside]. split; [|exact I].
      apply (r21_wrap_out A A0 (sp - K) sp x ltac:(rewrite <- Hr9; exact HA0)); lia.
    - intros x Hx. apply Hout. right. lia.
    - intros x Hx. apply Hout. left. unfold Sfr, shadow_addr, ASAN_K in Hx.
      pose proof (Z.div_mod fr 8 ltac:(lia)). pose proof (Z.mod_pos_bound fr 8 ltac:(lia)). lia.
    - (* the window is above stklo, the FakeStack below it (a_laws_fs_place) *)
      intros FS x Hwtp HFS Hx _.
      pose proof (r21_law_fs_place
                    (hb ++ g_H g) mem md FS HAH Hwtp HFS) as (_ & HFSstk & _ & _).
      apply Hout. left. lia. }
  split.
  - apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md' HFRAmd); try reflexivity. exact Hmat.
  - assert (HWcase : forall x, 0 <= x < 2 ^ 64 -> Frame.outside [(sp - K, sp)] x \/
      (g_S g - AFw.SLOT_STACK <= x < g_S g) \/ (fr <= x < fr + FRAME_BYTES) \/ (Sfr fr <= x < Sfr fr + FRAME_SHADOW)).
    { intros x Hx.
      destruct (Z_le_gt_dec (sp - K) x) as [A1|A1]; destruct (Z_lt_ge_dec x sp) as [A2|A2];
        first [ right; left; lia | left; apply Hout; lia ]. }
    assert (HENT1 : ENT APIf g hb mem' md).
    { eapply ent_store;
        [ exact HENT | exact HFRA | exact MU | exact HWcase | exact HSTK' | exact HSHI'
        | intros a _ Hw; exact (proj2 (HOWN' a) Hw) ]. }
    eapply ent_mat; [exact HENT1 | exact Hmat].
Qed.

(* ---- The cut bodies of R21 ---- *)

(* 0x81990, R21's own mid cut: the tail's entry (b = 6, the latch not taken). The registered globals'
   addressability, the sp bound and the frame placement are FRA facts since push 5 (frame_AG,
   g_S g < APPMEM_END, fra_frame), so the cut does not repeat them. Push 7 / push 9: the block R21P7 (spills
   [A + 144] = fr + 2688, [A + 192] = fr + 2768, [A + 280] = fr + 3040, [A + 240] = fr + 3056 and the cells at
   fr + 2688 / fr + 2768 / fr + 3040 / fr + 3056), which the tail hands to Inv_A81ac0 / Inv_A81ac8 by
   r21_p7_exit (and [A + 144] as push 12A's own conjunct). Push 11A: CUR g 7 (s6 / s9 from the 0x81924 entry's
   RB; no instruction of 0x81924 .. 0x81ac8 and not the strcmp wrapper writes s6 / s9), which is the exits' CUR g
   (c0 (g_in g)) since 7 <= g_n g. Push 13B: PRO, from the 0x81924 entry to the two exits (the latch's stores hit
   only the frame's shadow bytes S(fr) + 296 .. + 312, the strcmp wrapper only its stack window). Push 14A: the
   spill-152 bound is Q + 187 <= S(fr) + 328, the exits' form (Q = S(fr) + 68: 255 <= 328). *)
Definition Inv_A81990_l (g : ghost) (c : config) : Prop :=
  CUTST B APIf ra g 0x81990 [] (fun fr regs m =>
    g_n g < 2 ^ 26 /\ OURb g fr m /\ CUR g 7 regs /\ PRO g fr regs m /\
    rg regs 21 (fr + 2176) /\ IDBr g fr (RID (g_in g) 7) m /\
    spill regs m 112 (mrow (g_in g)) /\
    R21P7 fr regs m /\
    (exists Q, spill regs m 152 Q /\ Sfr fr <= Q /\ Q + 187 <= Sfr fr + 328) /\
    addressable m (fr + 2176) 38) c.

(* The exits of the tail are the official Inv_A81ac0 (the strcmp return) and Inv_A81ac8 (has_identity_record = 0:
   0x81ac0 `beqz a0,81ac8` falls into it). *)

(* The frame's own 392 shadow bytes are the only ones the latch writes, so every frame byte and every byte at or
   above HIGHMEM_BEG is outside the write set. *)
Lemma seg_R21_latch : forall b : nat,
  Hat B APIf ra (Inv_A815cc_at B APIf ra) (S b) ->
  Hcut B APIf ra Inv_A81990_l ->
  Hat B APIf ra (Inv_A81924_at (fx:=fx) B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros b Hnext Hmid g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hb6 & H23 & HOUR & HOUTA & HRB & Hs128 &
                    HPRO & Hs104 & Hs96 & Hs64 & H21 & Hs112 & Hs144 & Hs208 & HRWid & HRWjk & Hs280 & Hs240 &
                    HRWjy & HRWsc & Hs152 & HADid & HRXS).
  (* the push 7 / push 9 block: the eight conjuncts between [A + 112] and [A + 152], in R21P7's order *)
  assert (HP7 : R21P7 fr regs mem)
    by exact (conj Hs144 (conj Hs208 (conj HRWid (conj HRWjk (conj Hs280 (conj Hs240 (conj HRWjy HRWsc))))))).
  subst c.
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (r21_frame_app g fr [] regs mem md HFRA) as (Happ & HGT & Hfr0 & Hfr8b).
  pose proof (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (ACw.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH) as Hstkhigh.
  destruct HRB as (Hb6' & HCUR & HOUR2 & H23' & HID & HFG).
  assert (HAlo : HIGHMEM_BEG <= A) by (unfold AFw.SLOT_STACK in Hstklo; lia).
  assert (HAhi : A + 312 <= 2 ^ 64).
  { unfold q64 in Hspill. apply bytes_at_bound in Hspill. rewrite length_le8 in Hspill. lia. }
  assert (Hfr8 : fr mod 8 = 0) by (revert Hfrm; Z.div_mod_to_equations; lia).
  assert (Hinsh : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> in_shadow x).
  { intros x Hx. replace x with (shadow_addr (fr + (x - Sfr fr) * 8))
      by (rewrite r21_shadow_off by lia; lia).
    apply shadow_of_app. apply Happ. lia. }
  assert (HSfrhi : Sfr fr + FRAME_SHADOW <= HIGHMEM_BEG).
  { pose proof (Hinsh (Sfr fr + FRAME_SHADOW - 1) ltac:(lia)) as IS.
    unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in IS |- *. lia. }
  assert (HSfr0 : 0 <= Sfr fr)
    by (unfold Sfr, shadow_addr; pose proof (Z.div_pos fr 8 Hfr0 ltac:(lia)); unfold ASAN_K; lia).
  assert (HSfr2 : Sfr fr + FRAME_SHADOW <= 2 ^ 64)
    by (destruct Hsh as (sh0 & Hb0 & HL0); apply bytes_at_bound in Hb0; rewrite HL0 in Hb0; lia).
  assert (HSTK : stk rsegs mem (Sfr fr + 296) (Sfr fr + 313)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    exact (AsanRTInv.RT_shadow_rw _ _ _ HRT a (Hinsh a ltac:(lia))). }
  (* outside the write set *)
  assert (Hfout : forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside [(Sfr fr + 296, Sfr fr + 313)] x).
  { intros x Hx. cbn [Frame.outside]. split; [|exact I]. intros Hin.
    exact (app_not_shadow x (Happ x Hx) (Hinsh x ltac:(lia))). }
  assert (Hhout : forall x, HIGHMEM_BEG <= x -> Frame.outside [(Sfr fr + 296, Sfr fr + 313)] x).
  { intros x Hx. cbn [Frame.outside]. split; [|exact I]. lia. }
  assert (Hsout : forall x, in_globals AFw.frame_AG x ->
            Frame.outside [(Sfr fr + 296, Sfr fr + 313)] (shadow_addr x)).
  { intros x Hx. pose proof (a_AG_lt x Hx) as Hxr. cbn [Frame.outside]. split; [|exact I].
    unfold Sfr, shadow_addr, ACw.GT in *. revert HGT Hxr. Z.div_mod_to_equations. lia. }
  assert (Hidout : forall i, 0 <= i < 38 ->
            Frame.outside [(Sfr fr + 296, Sfr fr + 313)] (shadow_addr (fr + 2176 + i))).
  { intros i Hi. cbn [Frame.outside]. split; [|exact I].
    unfold Sfr, shadow_addr. revert Hfr8 Hi. Z.div_mod_to_equations. lia. }
  pose proof (a_spill_A regs mem 128 (fr + 544) A Hr9 HAlo HAhi ltac:(lia) Hs128) as HQ128.
  unfold q64 in HQ128.
  unfold rg in Hr19, Hr9.
  (* PRO's input block: a live block of the entry heap (a_laws_blocks), so application memory (outside the
     latch's write set, which is frame shadow memory) and apart from the frame (on the real arm the frame is at or
     above stklo, on the side arm it is in the side stack, which no block byte is), so its shadow bytes are not
     the frame's S(fr) + 296 .. + 312 *)
  assert (INB : In (g_p g, g_n g) (g_H g) -> forall x, g_p g <= x < g_p g + g_n g ->
            Frame.outside [(Sfr fr + 296, Sfr fr + 313)] x /\
            Frame.outside [(Sfr fr + 296, Sfr fr + 313)] (shadow_addr x)).
  { intros Hin x Hx.
    destruct (r21_law_blocks ([] ++ g_H g) mem md (g_p g) (g_n g) HAH Hin)
      as (_ & _ & Hpend & _ & Hpb).
    destruct (Hpb x Hx) as (Happx & _ & _ & _ & Hnfsx).
    assert (Hxfr : ~ (fr <= x < fr + FRAME_BYTES)).
    { intros Hxf. destruct Hloc as [(H0' & Hspfr & Hreal)|(Hfr0' & HfsbS & Hfs & _)].
      - pose proof (Hreal x Hxf). lia.
      - exact (Hnfsx (Hfs x Hxf)). }
    split.
    - cbn [Frame.outside]. split; [|exact I]. intros Hxw.
      exact (app_not_shadow x Happx (Hinsh x ltac:(lia))).
    - cbn [Frame.outside]. split; [|exact I].
      unfold Sfr, shadow_addr. revert Hfr8 Hxfr. Z.div_mod_to_equations. lia. }
  (* PRO across the latch's shadow stores (both arms): the spills are above HIGHMEM_BEG <= A, our[]'s shadow
     byte S(fr) + 328 is not one of S(fr) + 296 .. + 312 *)
  assert (KPRO : forall regs' mem', getr regs' 9 = getr regs 9 ->
            munch [(Sfr fr + 296, Sfr fr + 313)] mem mem' -> PRO g fr regs mem -> PRO g fr regs' mem').
  { intros regs' mem' E9 MU. apply (r21_pro_keep g fr regs regs' mem mem').
    - intros off v Hoff Hs. pose proof (a_spill_A regs mem off v A Hr9 HAlo HAhi ltac:(lia) Hs) as HQ.
      exists A. split; [unfold rg; rewrite E9; exact Hr9|].
      unfold q64 in HQ |- *. apply (a_keep _ mem mem' _ _ MU); [|exact HQ].
      intros x Hx. rewrite length_le8 in Hx. apply Hhout. lia.
    - intros HA6. apply (a_addr_keep_rng mem mem' _ (fr + 2624) 6 HA6 MU). intros i Hi.
      cbn [Frame.outside]. split; [|exact I].
      unfold Sfr, shadow_addr. revert Hfr8 Hi. Z.div_mod_to_equations. lia.
    - intros Hin HIN. apply (a_keep _ mem mem' _ _ MU); [|exact HIN].
      intros x Hx. rewrite <- g_n_len in Hx. exact (proj1 (INB (Hin ltac:(lia)) x Hx)).
    - intros Hin HA. apply (a_addr_keep_rng mem mem' _ (g_p g) (g_n g) HA MU). intros i Hi.
      exact (proj2 (INB Hin (g_p g + i) ltac:(lia))). }
  rewrite SEGS.
  destruct (Nat.eq_dec b 6) as [E6|E6].
  - (* b = 6: the latch is not taken; fall into the tail at 0x81990 *)
    subst b. unfold rg in H23. replace (Z.of_nat 6) with 6 in H23 by reflexivity.
    eapply (sl_run_lib regs (Z_to_bv 64 0x81924) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x81990 /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
         getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\
         getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
         munch [(Sfr fr + 296, Sfr fr + 313)] mem mem' /\ wmono rsegs mem mem' /\
         stk rsegs mem' (Sfr fr + 296) (Sfr fr + 313))
      (Post B APIf ra g)).
    + exact Hhalt.
    + unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
      eapply evt_mono.
      * apply r21_latch_last with (SH := Sfr fr) (A := A) (v := fr + 544);
          [ exact Hr19 | exact Hr9 | exact H23 | lia | lia | lia | exact HSTK | exact HQ128 ].
      * intros ms' (R & m' & Hms & P2 & P3 & P4 & P8 & P9 & P19 & P21 & P22 & P25 & P26 & MUq & WMq & STq).
        exists R, (Z_to_bv 64 0x81990), m'. split; [exact Hms|].
        split; [reflexivity|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
        split; [exact P9|]. split; [exact P19|]. split; [exact P21|]. split; [exact P22|].
        split; [exact P25|]. split; [exact P26|]. split; [exact MUq|]. split; [exact WMq|].
        exact STq.
    + intros R pc' mem' regs'' md'
        (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K25 & K26 & MU & WM & STk) Hreg Hmat.
      subst pc'.
      assert (HFE : FRA B APIf ra g fr [] regs'' mem' md /\ ENT APIf g [] mem' md).
      { apply (r21_fr_shadow g fr [] regs regs'' mem mem' md 296 313 HFRA HENT
                 ltac:(lia) ltac:(lia) ltac:(lia) MU WM);
          [ intros q Hq; destruct (proj2 (proj2 STk) q Hq) as (_ & Hbq); exact Hbq
          | exact Hsout
          | rewrite Hreg; exact K2 | rewrite Hreg; exact K3 | rewrite Hreg; exact K4
          | rewrite Hreg; exact K8 | rewrite Hreg; exact K9 | rewrite Hreg; exact K19
          | rewrite Hreg; exact K26 ]. }
      destruct HFE as (HFRAmd & HENT1).
      assert (HFRA' : FRA B APIf ra g fr [] regs'' mem' md').
      { apply (sl_fra_move B APIf ra g fr [] regs'' regs'' mem' md md' HFRAmd);
          try reflexivity. exact Hmat. }
      assert (HENT' : ENT APIf g [] mem' md') by (eapply ent_mat; [exact HENT1 | exact Hmat]).
      rewrite <- SEGS. apply Hmid. exists regs'', mem', md', fr.
      split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
      split; [exact Hgn|].
      split.
      { unfold OURb in HOUR |- *. apply (a_keep _ mem mem' _ _ MU); [|exact HOUR].
        intros x Hx. apply Hfout. rewrite OUR_length in Hx. lia. }
      split.
      { (* CUR g 7: the latch writes neither s6 nor s9 *)
        destruct HCUR as (Hc0 & Hc22 & Hc25). unfold CUR, rg in *.
        split; [exact Hc0|]. split; [rewrite Hreg, K22; exact Hc22 | rewrite Hreg, K25; exact Hc25]. }
      split; [exact (KPRO regs'' mem' ltac:(rewrite Hreg; exact K9) MU HPRO)|].
      split.
      { unfold rg in H21 |- *. rewrite Hreg, K21. exact H21. }
      split.
      { unfold IDBr in HID |- *. apply (a_keep _ mem mem' _ _ MU); [|exact HID].
        intros x Hx. apply Hfout. rewrite a_RID_len in Hx. lia. }
      split.
      { pose proof (a_spill_A regs mem 112 (mrow (g_in g)) A Hr9 HAlo HAhi ltac:(lia) Hs112) as HQ0.
        exists A. split; [unfold rg; rewrite Hreg, K9; exact Hr9|].
        unfold q64 in HQ0 |- *. apply (a_keep _ mem mem' _ _ MU); [|exact HQ0].
        intros x Hx. rewrite length_le8 in Hx. apply Hhout. lia. }
      split.
      { (* the record block: the latch writes neither the spill area (above HIGHMEM_BEG) nor a frame byte *)
        assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
        apply (r21_p7_keep fr regs regs'' mem mem' _ A Hr9 HAlo HAhi E9 MU WM); [|exact Hfout | exact HP7].
        intros x Hx. apply Hhout. lia. }
      split.
      { pose proof (a_spill_A regs mem 152 (Sfr fr + 68) A Hr9 HAlo HAhi ltac:(lia) Hs152) as HQw.
        exists (Sfr fr + 68). split; [|lia].
        exists A. split; [unfold rg; rewrite Hreg, K9; exact Hr9|].
        unfold q64 in HQw |- *. apply (a_keep _ mem mem' _ _ MU); [|exact HQw].
        intros x Hx. rewrite length_le8 in Hx. apply Hhout. lia. }
      { apply (a_addr_keep_rng mem mem' _ (fr + 2176) 38 HADid MU). exact Hidout. }
  - (* b <= 5: the latch is taken, back to the round-trip head at turn b + 1 *)
    assert (Hb5 : (b <= 5)%nat) by lia.
    unfold rg in H23.
    eapply (sl_run_lib regs (Z_to_bv 64 0x81924) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x815cc /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
         getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\
         getr R 22 = getr regs 22 /\
         getr R 23 = Z_to_bv 64 (Z.of_nat b + 1) /\ getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\
         getr R 10 = Z_to_bv 64 (fr + 544) /\ getr R 24 = Z_to_bv 64 36 /\
         munch [(Sfr fr + 296, Sfr fr + 313)] mem mem' /\ wmono rsegs mem mem' /\
         stk rsegs mem' (Sfr fr + 296) (Sfr fr + 313))
      (Post B APIf ra g)).
    + exact Hhalt.
    + unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
      eapply evt_mono.
      * apply r21_latch_next with (SH := Sfr fr) (A := A) (bz := Z.of_nat b) (v := fr + 544);
          [ exact Hr19 | exact Hr9 | exact H23 | lia | lia | lia | lia | exact HSTK | exact HQ128 ].
      * intros ms' (R & m' & Hms & P2 & P3 & P4 & P8 & P9 & P19 & P21 & P22 & P23 & P25 & P26 & P10 & P24 &
                    MUq & WMq & STq).
        exists R, (Z_to_bv 64 0x815cc), m'. split; [exact Hms|].
        split; [reflexivity|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
        split; [exact P9|]. split; [exact P19|]. split; [exact P21|]. split; [exact P22|]. split; [exact P23|].
        split; [exact P25|]. split; [exact P26|]. split; [exact P10|]. split; [exact P24|].
        split; [exact MUq|]. split; [exact WMq|].
        exact STq.
    + intros R pc' mem' regs'' md'
        (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K25 & K26 & K10 & K24 & MU & WM & STk) Hreg Hmat.
      subst pc'.
      assert (HFE : FRA B APIf ra g fr [] regs'' mem' md /\ ENT APIf g [] mem' md).
      { apply (r21_fr_shadow g fr [] regs regs'' mem mem' md 296 313 HFRA HENT
                 ltac:(lia) ltac:(lia) ltac:(lia) MU WM);
          [ intros q Hq; destruct (proj2 (proj2 STk) q Hq) as (_ & Hbq); exact Hbq
          | exact Hsout
          | rewrite Hreg; exact K2 | rewrite Hreg; exact K3 | rewrite Hreg; exact K4
          | rewrite Hreg; exact K8 | rewrite Hreg; exact K9 | rewrite Hreg; exact K19
          | rewrite Hreg; exact K26 ]. }
      destruct HFE as (HFRAmd & HENT1).
      assert (HFRA' : FRA B APIf ra g fr [] regs'' mem' md').
      { apply (sl_fra_move B APIf ra g fr [] regs'' regs'' mem' md md' HFRAmd);
          try reflexivity. exact Hmat. }
      assert (HENT' : ENT APIf g [] mem' md') by (eapply ent_mat; [exact HENT1 | exact Hmat]).
      (* the spills the head reads, kept: the latch writes only the frame's shadow, below HIGHMEM_BEG <= A *)
      assert (KS : forall off v, 0 <= off <= 304 -> spill regs mem off v -> spill regs'' mem' off v).
      { intros off v Hoff Hs. pose proof (a_spill_A regs mem off v A Hr9 HAlo HAhi Hoff Hs) as HQ.
        exists A. split; [unfold rg; rewrite Hreg, K9; exact Hr9|].
        unfold q64 in HQ |- *. apply (a_keep _ mem mem' _ _ MU); [|exact HQ].
        intros x Hx. rewrite length_le8 in Hx. apply Hhout. lia. }
      rewrite <- SEGS. apply Hnext. exists regs'', mem', md', fr.
      split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
      split; [exact Hgn|].
      split.
      { unfold RS, RB.
        split; [lia|].
        split.
        { destruct HCUR as (Hc0 & Hc22 & Hc25). unfold CUR, rg in *.
          split; [exact Hc0|]. split; [rewrite Hreg, K22; exact Hc22 | rewrite Hreg, K25; exact Hc25]. }
        split.
        { unfold OURb in HOUR |- *. apply (a_keep _ mem mem' _ _ MU); [|exact HOUR].
          intros x Hx. apply Hfout. rewrite OUR_length in Hx. lia. }
        split.
        { unfold rg. rewrite Hreg, K23. f_equal. lia. }
        split.
        { unfold IDBr in HID |- *. apply (a_keep _ mem mem' _ _ MU); [|exact HID].
          intros x Hx. apply Hfout. rewrite a_RID_len in Hx. lia. }
        { unfold FGBr in HFG |- *. apply (a_keep _ mem mem' _ _ MU); [|exact HFG].
          intros x Hx. apply Hfout. rewrite (a_RFG_len (g_in g) (S b) ltac:(lia)) in Hx. lia. } }
      split.
      { (* out[]'s shadow bytes S(fr) + 68 .. + 254 are not the latch's S(fr) + 296 .. + 312 *)
        apply (outa_munch fr mem mem' [(Sfr fr + 296, Sfr fr + 313)] HOUTA MU). intros i Hi.
        cbn [Frame.outside]. split; [|exact I].
        unfold Sfr, shadow_addr. revert Hfr8 Hi. Z.div_mod_to_equations. lia. }
      (* the official Inv_A815cc_at body after OUTA, in its order *)
      split; [exact (KS 128 (fr + 544) ltac:(lia) Hs128)|].
      split; [exact (KPRO regs'' mem' ltac:(rewrite Hreg; exact K9) MU HPRO)|].
      split; [exact (KS 104 0x21140 ltac:(lia) Hs104)|].
      split; [exact (KS 96 0x1234 ltac:(lia) Hs96)|].
      split; [unfold a0v, rg; rewrite Hreg; exact K10|].
      split; [unfold rg; rewrite Hreg; exact K24|].
      split; [exact (KS 64 0xe38f0000 ltac:(lia) Hs64)|].
      split; [exact (KS 112 (mrow (g_in g)) ltac:(lia) Hs112)|].
      split; [unfold rg in H21 |- *; rewrite Hreg, K21; exact H21|].
      split; [exact (KS 152 (Sfr fr + 68) ltac:(lia) Hs152)|].
      (* the record block (push 7), kept as in the b = 6 branch, in Inv_A815cc_at's order *)
      assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
      destruct (r21_p7_keep fr regs regs'' mem mem' _ A Hr9 HAlo HAhi E9 MU WM
                  (fun x Hx => Hhout x ltac:(lia)) Hfout HP7)
        as (H144' & H208' & HRWid' & HRWjk' & H280' & H240' & HRWjy' & HRWsc').
      split; [exact H144'|].
      split; [apply (a_addr_keep_rng mem mem' _ (fr + 2176) 38 HADid MU); exact Hidout|].
      split; [exact H208'|]. split; [exact HRWid'|]. split; [exact HRWjk'|].
      split; [exact H280'|]. split; [exact H240'|]. split; [exact HRWjy'|]. split; [exact HRWsc'|].
      (* RXS (push 10), loop-carried: the latch writes no spill (all above HIGHMEM_BEG) and the fragment record's
         shadow bytes S(fr) + 282 .. + 290 are not the latch's S(fr) + 296 .. + 312 *)
      apply (r21_rxs_keep g fr regs regs'' mem mem' (fun xoff xv Ho H => KS xoff xv ltac:(lia) H)); [|exact HRXS].
      intros HA72. apply (a_addr_keep_rng mem mem' _ (fr + 2256) 72 HA72 MU). intros i Hi.
      cbn [Frame.outside]. split; [|exact I].
      unfold Sfr, shadow_addr. revert Hfr8 Hi. Z.div_mod_to_equations. lia.
Qed.

(* The image's read-only bytes of a checked run are in memory (ro_agree). *)
Lemma a_ro_bytes : forall (bs : list byte) (m : word -> option byte) A, ro_agree rsegs m ->
  Image.ro_bytes_b rsegs A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at rsegs m A bs.
Proof.
  induction bs as [|b bs IH]; intros m A Hro HB HA Hl.
  - split; [lia|]. split; [cbn [length Z.of_nat]; lia|]. intros i Hi; cbn [length] in Hi; lia.
  - change (Image.ro_bytes_b rsegs A (b :: bs)) with
      (match seg_rom rsegs (wa A) with
       | Some b' => (bv_eqb b b' && ro_addr rsegs (wa A) && Image.ro_bytes_b rsegs (A + 1) bs)%bool
       | None => false end) in HB.
    destruct (seg_rom rsegs (wa A)) as [b'|] eqn:E; [|discriminate HB].
    apply andb_prop in HB as [HB1 HB3]. apply andb_prop in HB1 as [HBe HBro].
    unfold bv_eqb in HBe. apply Z.eqb_eq in HBe. apply bv_eq in HBe. subst b'.
    cbn [length] in Hl.
    assert (HB' : bytes_at rsegs m (A + 1) bs) by (apply IH; [exact Hro | exact HB3 | lia | lia]).
    split; [lia|]. split; [cbn [length]; lia|].
    intros i Hi. destruct i as [|i].
    + replace (A + Z.of_nat 0) with A by lia. cbn [nth_error]. rewrite (Hro (wa A) HBro). exact E.
    + replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. cbn [nth_error].
      cbn [length] in Hi. exact (proj2 (proj2 HB') i ltac:(lia)).
Qed.

(* The image's RELRO bytes are in memory (G_img_c). *)
Lemma a_relro_bytes : forall (mem : word -> option byte) (A : Z) (n : nat) bs,
  ms_segs B = rsegs -> G_img_c B AFw.frame_RELRO mem ->
  Image.image_bytes rsegs A n = Some bs ->
  (forall k, (k < n)%nat -> in_globals AFw.frame_RELRO (A + Z.of_nat k)) ->
  0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  bytes_at rsegs mem A bs.
Proof.
  intros mem A n bs SEGS HG HI Hin HA Hn.
  pose proof (Image.image_bytes_length rsegs n A bs HI) as HL.
  unfold G_img_c in HG. rewrite SEGS in HG.
  split; [lia|]. split; [rewrite HL; lia|].
  intros i Hi. rewrite HL in Hi.
  rewrite <- (a_img_nth n A bs HI i Hi). exact (HG (A + Z.of_nat i) (Hin i Hi)).
Qed.

(* The catalogue row of the round trip is a RELRO global. *)
Lemma a_cat_inRELRO : forall a, CAT <= a < CAT + 3256 -> in_globals AFw.frame_RELRO a.
Proof.
  intros a Ha. exists 0x9e348, 9344. split; [|unfold CAT in Ha; lia].
  unfold AFw.frame_RELRO. cbn [In]. repeat (first [ left; reflexivity | right ]).
Qed.

Hypothesis SCMP : strcmp_wrap_contract.

Lemma seg_R21_tail :
  Hcut B APIf ra (Inv_A81ac0 B APIf ra) -> Hcut B APIf ra (Inv_A81ac8 (fx:=fx) B APIf ra) ->
  Hcut B APIf ra Inv_A81990_l.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros Hex68 Hex70 g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (regs & mem & md & fr & Ec & HFRA & HENT & Hgn & HOUR & HCUR & HPRO & H21 & HID & Hs112 &
                    HP7 & HQ152 & HADid).
  subst c.
  (* push 11A: on the round trip c0 (g_in g) = Z.min (g_n g) 7 = 7, since CUR g 7 gives 7 <= g_n g *)
  assert (Ec0 : c0 (g_in g) = 7).
  { destruct HCUR as (Hc0 & _). unfold c0. change (nlen (g_in g)) with (g_n g). lia. }
  pose proof HFRA as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (r21_frame_app g fr [] regs mem md HFRA) as (Happ & HGT & Hfr0 & Hfr8b).
  pose proof (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc)) as ALAWS.
  pose proof (ACw.a_laws_stack_high _ _ _ _ _ ALAWS ([] ++ g_H g) mem md HAH) as Hstkhigh.
  unfold rg in Hr9, Hr19, H21.
  (* the callee window below sp (fra_win) and the frame's placement against it (fra_frame), from FRA *)
  pose proof (fra_win B APIf ra g fr [] regs mem md HFRA) as (Hwinlo & Hwinstk).
  pose proof (fra_frame B APIf ra g fr [] regs mem md HFRA) as (Hfrpl & _ & _ & _).
  assert (HFRWIN : ACw.aspZ regs <= fr \/ fr + FRAME_BYTES <= ACw.aspZ regs - FN_STACK).
  { destruct (Hfrpl FN_STACK ltac:(unfold FN_STACK, AFw.SLOT_STACK; lia)) as [H|H];
      [right; exact H | left; exact H]. }
  rewrite Haspz in Hwinlo, Hwinstk.
  assert (HspA : sp <= APPMEM_END) by lia.
  assert (HAlo : HIGHMEM_BEG <= A) by (unfold AFw.SLOT_STACK in Hstklo; lia).
  assert (HAhi : A + 312 <= 2 ^ 64).
  { unfold q64 in Hspill. apply bytes_at_bound in Hspill. rewrite length_le8 in Hspill. lia. }
  assert (Hfrhi : fr + FRAME_BYTES <= APPMEM_END).
  { pose proof (Happ (fr + FRAME_BYTES - 1) ltac:(lia)) as Hq. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in Hq.
    unfold ACw.GT in HGT. unfold APPMEM_END. lia. }
  (* the catalogue row *)
  pose proof (a_istar_range (g_in g)) as Hi11.
  assert (Hmr : mrow (g_in g) = CAT + CAT_ROW * istar (g_in g)) by reflexivity.
  assert (Hmrlo : CAT <= mrow (g_in g) /\ mrow (g_in g) + 296 <= CAT + 3256)
    by (rewrite Hmr; unfold CAT_ROW; lia).
  assert (Hmr8 : mrow (g_in g) mod 8 = 0) by (rewrite Hmr; unfold CAT, CAT_ROW; Z.div_mod_to_equations; lia).
  assert (NROW : bytes_at rsegs mem (mrow (g_in g)) (rowb (istar (g_in g)))).
  { apply (a_relro_bytes mem (mrow (g_in g)) 296 _ SEGS Hgimg);
      [ rewrite Hmr; exact (a_row_img (istar (g_in g)) Hi11)
      | intros k Hk; apply a_cat_inRELRO; unfold CAT in *; lia
      | unfold CAT in *; lia | unfold CAT in *; lia ]. }
  pose proof (a_row_len (istar (g_in g))) as HROWL.
  pose proof (a_RID_len (g_in g) 7) as HIDL.
  unfold IDBr in HID.
  (* the model facts *)
  destruct (a_rtm_fw (g_in g)) as (Ehf & Efw).
  destruct (a_rtm_ver (g_in g)) as (Ehv & Emaj & Emin & Epat).
  destruct (a_row_facts (istar (g_in g)) Hi11) as (Hh32 & Ehid & Hnmf).
  destruct (a_row_le (istar (g_in g)) Hi11) as (L56 & L280).
  (* addressability of the row's granules *)
  assert (HADrow : forall p, CAT <= p -> p + 8 <= CAT + 3256 -> addressable mem p 8).
  { intros p Hp1 Hp2. apply a_addr_join; [unfold CAT in *; lia | lia | unfold CAT, APPMEM_END in *; lia |].
    intros i Hi. apply HAG. apply a_cat_inAG. lia. }
  (* the spill words the tail loads *)
  pose proof HP7 as (Hs144 & _).
  pose proof (a_spill_A regs mem 144 (fr + 2688) A Hr9 HAlo HAhi ltac:(lia) Hs144) as HQ144.
  pose proof (a_spill_A regs mem 112 (mrow (g_in g)) A Hr9 HAlo HAhi ltac:(lia) Hs112) as HQ112.
  unfold q64 in HQ144, HQ112.
  assert (R144 : ov_read_bytes rsegs mem (wa (A + 144)) 8 = Some (le8 (Z_to_bv 64 (fr + 2688))))
    by exact (r21_rdn mem _ _ 8%nat HQ144 (length_le8 _)).
  (* the spill word [A + 192] is writable: it is in the entry-anchored slot window (g_S g - 4096 < sp <= A and
     A + 416 <= g_S g) *)
  assert (HW208 : forall i, 0 <= i < 8 -> writable_at rsegs mem (A + 192 + i)).
  { intros i Hi. destruct Hwin as (_ & _ & Hwv).
    exact (proj1 (Hwv (A + 192 + i) ltac:(unfold AFw.SLOT_STACK; lia))). }
  assert (R112 : ov_read_bytes rsegs mem (wa (A + 112)) 8 = Some (le8 (Z_to_bv 64 (mrow (g_in g)))))
    by exact (r21_rdn mem _ _ 8%nat HQ112 (length_le8 _)).
  (* the identity record's bytes *)
  assert (R2 : ov_read_bytes rsegs mem (wa (fr + 2176 + 2)) 1 = Some [Z_to_bv 8 1]).
  { pose proof (a_rd1 mem (fr + 2176) (RID (g_in g) 7) 2 HID ltac:(rewrite HIDL; lia)) as H.
    replace (fr + 2176 + Z.of_nat 2) with (fr + 2176 + 2) in H by lia.
    rewrite (a_byte1 (nth 2 (RID (g_in g) 7) (Z_to_bv 8 0)) Ehf) in H. exact H. }
  assert (R36 : ov_read_bytes rsegs mem (wa (fr + 2176 + 36)) 1 = Some [Z_to_bv 8 1]).
  { pose proof (a_rd1 mem (fr + 2176) (RID (g_in g) 7) 36 HID ltac:(rewrite HIDL; lia)) as H.
    replace (fr + 2176 + Z.of_nat 36) with (fr + 2176 + 36) in H by lia.
    rewrite (a_byte1 (nth 36 (RID (g_in g) 7) (Z_to_bv 8 0)) Ehv) in H. exact H. }
  assert (R0 : ov_read_bytes rsegs mem (wa (fr + 2176)) 2 =
               Some (le2 (Z_to_bv 64 (fw_milli (RID (g_in g) 7))))).
  { pose proof (a_rd2 mem (fr + 2176) (RID (g_in g) 7) 0 HID ltac:(rewrite HIDL; lia)) as H.
    replace (fr + 2176 + Z.of_nat 0) with (fr + 2176) in H by lia. exact H. }
  assert (R22 : ov_read_bytes rsegs mem (wa (fr + 2176 + 22)) 2 =
                Some (le2 (Z_to_bv 64 (major (RID (g_in g) 7))))).
  { pose proof (a_rd2 mem (fr + 2176) (RID (g_in g) 7) 22 HID ltac:(rewrite HIDL; lia)) as H.
    replace (fr + 2176 + Z.of_nat 22) with (fr + 2176 + 22) in H by lia. exact H. }
  assert (R24 : ov_read_bytes rsegs mem (wa (fr + 2176 + 24)) 2 =
                Some (le2 (Z_to_bv 64 (minor (RID (g_in g) 7))))).
  { pose proof (a_rd2 mem (fr + 2176) (RID (g_in g) 7) 24 HID ltac:(rewrite HIDL; lia)) as H.
    replace (fr + 2176 + Z.of_nat 24) with (fr + 2176 + 24) in H by lia. exact H. }
  assert (R26 : ov_read_bytes rsegs mem (wa (fr + 2176 + 26)) 2 =
                Some (le2 (Z_to_bv 64 (patch (RID (g_in g) 7))))).
  { pose proof (a_rd2 mem (fr + 2176) (RID (g_in g) 7) 26 HID ltac:(rewrite HIDL; lia)) as H.
    replace (fr + 2176 + Z.of_nat 26) with (fr + 2176 + 26) in H by lia. exact H. }
  (* the row's bytes *)
  assert (M266 : ov_read_bytes rsegs mem (wa (mrow (g_in g) + 266)) 2 =
                 Some (le2 (Z_to_bv 64 (fw_milli (RID (g_in g) 7))))).
  { pose proof (a_rd2 mem (mrow (g_in g)) (rowb (istar (g_in g))) 266 NROW ltac:(rewrite HROWL; lia)) as H.
    replace (mrow (g_in g) + Z.of_nat 266) with (mrow (g_in g) + 266) in H by lia.
    rewrite Efw. exact H. }
  assert (M268 : ov_read_bytes rsegs mem (wa (mrow (g_in g) + 268)) 2 =
                 Some (le2 (Z_to_bv 64 (major (RID (g_in g) 7))))).
  { pose proof (a_rd2 mem (mrow (g_in g)) (rowb (istar (g_in g))) 268 NROW ltac:(rewrite HROWL; lia)) as H.
    replace (mrow (g_in g) + Z.of_nat 268) with (mrow (g_in g) + 268) in H by lia.
    rewrite Emaj. exact H. }
  assert (M270 : ov_read_bytes rsegs mem (wa (mrow (g_in g) + 270)) 2 =
                 Some (le2 (Z_to_bv 64 (minor (RID (g_in g) 7))))).
  { pose proof (a_rd2 mem (mrow (g_in g)) (rowb (istar (g_in g))) 270 NROW ltac:(rewrite HROWL; lia)) as H.
    replace (mrow (g_in g) + Z.of_nat 270) with (mrow (g_in g) + 270) in H by lia.
    rewrite Emin. exact H. }
  assert (M272 : ov_read_bytes rsegs mem (wa (mrow (g_in g) + 272)) 2 =
                 Some (le2 (Z_to_bv 64 (patch (RID (g_in g) 7))))).
  { pose proof (a_rd2 mem (mrow (g_in g)) (rowb (istar (g_in g))) 272 NROW ltac:(rewrite HROWL; lia)) as H.
    replace (mrow (g_in g) + Z.of_nat 272) with (mrow (g_in g) + 272) in H by lia.
    rewrite Epat. exact H. }
  assert (M56 : ov_read_bytes rsegs mem (wa (mrow (g_in g) + 56)) 4 =
                Some (le4 (Z_to_bv 64 (RcSynth.rw32 (rowb (istar (g_in g))) 56)))).
  { pose proof (a_rd4 mem (mrow (g_in g)) (rowb (istar (g_in g))) 56 NROW ltac:(rewrite HROWL; lia)) as H.
    replace (mrow (g_in g) + Z.of_nat 56) with (mrow (g_in g) + 56) in H by lia.
    rewrite <- L56. exact H. }
  (* the instrumented checks of the row's granules *)
  assert (K266 : ov_read_bytes rsegs mem (wa (Z.shiftr (mrow (g_in g) + 266) 3 + ASAN_K)) 1 =
                 Some [Z_to_bv 8 0]).
  { apply (a_meta0 mem (mrow (g_in g) + 264));
      [apply HADrow; unfold CAT in *; lia | revert Hmr8; Z.div_mod_to_equations; lia | lia]. }
  assert (K268 : ov_read_bytes rsegs mem (wa (Z.shiftr (mrow (g_in g) + 268) 3 + ASAN_K)) 1 =
                 Some [Z_to_bv 8 0]).
  { apply (a_meta0 mem (mrow (g_in g) + 264));
      [apply HADrow; unfold CAT in *; lia | revert Hmr8; Z.div_mod_to_equations; lia | lia]. }
  assert (K270 : ov_read_bytes rsegs mem (wa (Z.shiftr (mrow (g_in g) + 270) 3 + ASAN_K)) 1 =
                 Some [Z_to_bv 8 0]).
  { apply (a_meta0 mem (mrow (g_in g) + 264));
      [apply HADrow; unfold CAT in *; lia | revert Hmr8; Z.div_mod_to_equations; lia | lia]. }
  assert (K272 : ov_read_bytes rsegs mem (wa (Z.shiftr (mrow (g_in g) + 272) 3 + ASAN_K)) 1 =
                 Some [Z_to_bv 8 0]).
  { apply (a_meta0 mem (mrow (g_in g) + 272));
      [apply HADrow; unfold CAT in *; lia | revert Hmr8; Z.div_mod_to_equations; lia | lia]. }
  assert (K56 : ov_read_bytes rsegs mem (wa (Z.shiftr (mrow (g_in g) + 56) 3 + ASAN_K)) 1 =
                Some [Z_to_bv 8 0]).
  { apply (a_meta0 mem (mrow (g_in g) + 56));
      [apply HADrow; unfold CAT in *; lia | revert Hmr8; Z.div_mod_to_equations; lia | lia]. }
  assert (K280 : ov_read_bytes rsegs mem (wa (Z.shiftr (mrow (g_in g) + 280) 3 + ASAN_K)) 1 =
                 Some [Z_to_bv 8 0]).
  { apply (a_meta0 mem (mrow (g_in g) + 280));
      [apply HADrow; unfold CAT in *; lia | revert Hmr8; Z.div_mod_to_equations; lia | lia]. }
  (* the runtime cells the strcmp wrapper reads *)
  pose proof (AsanRTInv.RT_cf_cells _ _ _ HRT) as HCFC.
  destruct HCFC as (HCgot & _ & _ & _ & _ & _ & HC240 & _).
  assert (HGOT : bytes_at rsegs mem GOT_CF (le8 (wa CF))) by exact HCgot.
  assert (HCF1 : bytes_at rsegs mem (CF + 250) [Z_to_bv 8 1]).
  { pose proof (a_sub mem (RT_CF + 240) (cf_b [0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0])
                  10 1 HC240 ltac:(vm_compute; lia)) as X.
    rewrite a_first1 in X by (vm_compute; lia).
    replace (nth 10 (cf_b [0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0]) (Z_to_bv 8 0))
      with (Z_to_bv 8 1) in X by reflexivity.
    replace (RT_CF + 240 + Z.of_nat 10) with (CF + 250) in X by (unfold CF, RT_CF; lia). exact X. }
  assert (HCF2 : bytes_at rsegs mem (CF + 245) [Z_to_bv 8 0]).
  { pose proof (a_sub mem (RT_CF + 240) (cf_b [0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0])
                  5 1 HC240 ltac:(vm_compute; lia)) as X.
    rewrite a_first1 in X by (vm_compute; lia).
    replace (nth 5 (cf_b [0; 0; 0; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0]) (Z_to_bv 8 0))
      with (Z_to_bv 8 0) in X by reflexivity.
    replace (RT_CF + 240 + Z.of_nat 5) with (CF + 245) in X by (unfold CF, RT_CF; lia). exact X. }
  (* the name strings, when the row has an identity record *)
  assert (HN : RcSynth.rw32 (rowb (istar (g_in g))) 56 <> 0 ->
     ov_read_bytes rsegs mem (wa (fr + 2176 + 20)) 1 = Some [Z_to_bv 8 1] /\
     ov_read_bytes rsegs mem (wa (mrow (g_in g) + 280)) 8 =
       Some (le8 (Z_to_bv 64 (RcSynth.rname (rowb (istar (g_in g)))))) /\
     0 < RcSynth.rname (rowb (istar (g_in g))) < 2 ^ 64 /\
     bytes_at rsegs mem (fr + 2176 + 3) (removelast (rt_nb (g_in g)) ++ [Z_to_bv 8 0]) /\
     ~ In (Z_to_bv 8 0) (removelast (rt_nb (g_in g))) /\
     bytes_at rsegs mem (RcSynth.rname (rowb (istar (g_in g))))
       (removelast (rt_nb (g_in g)) ++ [Z_to_bv 8 0]) /\
     Z.of_nat (strcmp_k (removelast (rt_nb (g_in g))) (removelast (rt_nb (g_in g)))) + 1 <= 2 ^ 40 /\
     addressable mem (fr + 2176 + 3)
       (Z.of_nat (strcmp_k (removelast (rt_nb (g_in g))) (removelast (rt_nb (g_in g)))) + 1) /\
     end_in_app (fr + 2176 + 3)
       (Z.of_nat (strcmp_k (removelast (rt_nb (g_in g))) (removelast (rt_nb (g_in g)))) + 1) /\
     addressable mem (RcSynth.rname (rowb (istar (g_in g))))
       (Z.of_nat (strcmp_k (removelast (rt_nb (g_in g))) (removelast (rt_nb (g_in g)))) + 1) /\
     end_in_app (RcSynth.rname (rowb (istar (g_in g))))
       (Z.of_nat (strcmp_k (removelast (rt_nb (g_in g))) (removelast (rt_nb (g_in g)))) + 1) /\
     app_mem (fr + 2176 + 3 + 7) /\ app_mem (RcSynth.rname (rowb (istar (g_in g))) + 7) /\
     stk rsegs mem (sp - FN_STACK) sp /\ sp - FN_STACK + STRCMP_WRAP_K <= sp /\
     HIGHMEM_BEG <= sp - FN_STACK /\ sp <= APPMEM_END /\
     (fr + 2176 + 3 + Z.of_nat (length (removelast (rt_nb (g_in g)))) + 1 <= sp - STRCMP_WRAP_K \/
      sp <= fr + 2176 + 3) /\
     (RcSynth.rname (rowb (istar (g_in g))) + Z.of_nat (length (removelast (rt_nb (g_in g)))) + 1 <=
        sp - STRCMP_WRAP_K \/ sp <= RcSynth.rname (rowb (istar (g_in g)))) /\
     asan_cells mem /\ shadow_rw mem /\ ro_agree rsegs mem /\
     bytes_at rsegs mem GOT_CF (le8 (wa CF)) /\
     bytes_at rsegs mem (CF + 250) [Z_to_bv 8 1] /\ bytes_at rsegs mem (CF + 245) [Z_to_bv 8 0]).
  { intros Hh0.
    assert (Hhid : RcEmit.em_hid (rowb (istar (g_in g))) <> 0)
      by (intros E; apply Hh0; apply Ehid; exact E).
    destruct (Hnmf Hhid) as (Hnm0 & Hnm1 & HRO & HAGnm).
    assert (Hn6 : rt_n (g_in g) 6 <> 0) by (apply (proj2 (a_rtm_hid (g_in g))); exact Hhid).
    destruct (a_rtm_name (g_in g) Hn6) as (Ehn & Efn & Elast & Hall & Hlen16).
    apply andb_true_iff in Hlen16 as [Hl1 Hl2]. apply Nat.leb_le in Hl1. apply Nat.leb_le in Hl2.
    assert (Enb : rt_nb (g_in g) = removelast (rt_nb (g_in g)) ++ [Z_to_bv 8 0]).
    { change (Z_to_bv 8 0) with (zb 0). rewrite <- Elast.
      apply app_removelast_last. intros E. rewrite E in Hl1. cbn [length] in Hl1. lia. }
    assert (HLsx : (length (removelast (rt_nb (g_in g))) + 1 = length (rt_nb (g_in g)))%nat)
      by (rewrite Enb at 2; rewrite length_app; cbn [length]; lia).
    rewrite a_strcmp_k_refl.
    assert (R20 : ov_read_bytes rsegs mem (wa (fr + 2176 + 20)) 1 = Some [Z_to_bv 8 1]).
    { pose proof (a_rd1 mem (fr + 2176) (RID (g_in g) 7) 20 HID ltac:(rewrite HIDL; lia)) as H.
      replace (fr + 2176 + Z.of_nat 20) with (fr + 2176 + 20) in H by lia.
      rewrite (a_byte1 (nth 20 (RID (g_in g) 7) (Z_to_bv 8 0)) Ehn) in H. exact H. }
    assert (R280 : ov_read_bytes rsegs mem (wa (mrow (g_in g) + 280)) 8 =
                   Some (le8 (Z_to_bv 64 (RcSynth.rname (rowb (istar (g_in g))))))).
    { pose proof (a_rd8 mem (mrow (g_in g)) (rowb (istar (g_in g))) 280 NROW ltac:(rewrite HROWL; lia)) as H.
      replace (mrow (g_in g) + Z.of_nat 280) with (mrow (g_in g) + 280) in H by lia.
      rewrite <- L280. exact H. }
    assert (HBX : bytes_at rsegs mem (fr + 2176 + 3) (removelast (rt_nb (g_in g)) ++ [Z_to_bv 8 0])).
    { rewrite <- Enb.
      assert (Es : firstn (length (rt_nb (g_in g))) (skipn 3 (RID (g_in g) 7)) = rt_nb (g_in g)).
      { rewrite <- Efn at 2. unfold model_name, RcIdentModel.get, RcIdentModel.OFF_NAME,
          RcIdentModel.NAME_CAP. rewrite firstn_firstn. f_equal. lia. }
      pose proof (a_sub mem (fr + 2176) (RID (g_in g) 7) 3 (length (rt_nb (g_in g))) HID
                    ltac:(rewrite HIDL; lia)) as X.
      rewrite Es in X. replace (fr + 2176 + Z.of_nat 3) with (fr + 2176 + 3) in X by lia. exact X. }
    assert (HBY : bytes_at rsegs mem (RcSynth.rname (rowb (istar (g_in g)))) (rt_nb (g_in g)))
      by (apply (a_ro_bytes (rt_nb (g_in g)) mem _ Hro); [exact HRO | lia | lia]).
    assert (HNin : ~ In (Z_to_bv 8 0) (removelast (rt_nb (g_in g)))).
    { intros Hin. pose proof (proj1 (forallb_forall _ _) Hall (Z_to_bv 8 0) Hin) as X.
      vm_compute in X. discriminate X. }
    assert (HAY : addressable mem (RcSynth.rname (rowb (istar (g_in g))))
                    (Z.of_nat (length (removelast (rt_nb (g_in g)))) + 1)).
    { apply a_addr_join; [lia | lia | unfold APPMEM_END; lia |].
      intros i Hi. apply HAG. replace (RcSynth.rname (rowb (istar (g_in g))) + i)
        with (RcSynth.rname (rowb (istar (g_in g))) + Z.of_nat (Z.to_nat i)) by lia.
      apply HAGnm.
      assert (HLen : length (img_cstr (RcSynth.rname (rowb (istar (g_in g)))) 16)
                   = length (rt_nb (g_in g))) by reflexivity.
      rewrite HLen. lia. }
    assert (HAX : addressable mem (fr + 2176 + 3)
                    (Z.of_nat (length (removelast (rt_nb (g_in g)))) + 1)).
    { apply (addressable_sub mem (fr + 2176) 38 3
               (Z.of_nat (length (removelast (rt_nb (g_in g)))) + 1) HADid); lia. }
    split; [exact R20|]. split; [exact R280|]. split; [lia|].
    split; [exact HBX|]. split; [exact HNin|].
    split; [rewrite <- Enb; exact HBY|].
    split; [lia|]. split; [exact HAX|].
    split; [right; apply Happ; lia|]. split; [exact HAY|].
    split; [right; unfold app_mem, LOWMEM_END; left; lia|].
    split; [apply Happ; lia|].
    split; [unfold app_mem, LOWMEM_END; left; lia|].
    split; [exact Hwinstk|].
    split; [unfold STRCMP_WRAP_K, FN_STACK, AFw.SLOT_STACK; lia|].
    split; [lia|].
    split; [exact HspA|].
    split.
    { destruct HFRWIN as [Hw|Hw]; rewrite Haspz in Hw;
        [right; lia | left; unfold STRCMP_WRAP_K, FN_STACK, AFw.SLOT_STACK in *; lia]. }
    split.
    { left. unfold STRCMP_WRAP_K, AFw.SLOT_STACK in *. unfold HIGHMEM_BEG in *. lia. }
    split; [exact (AsanRTInv.RT_cells _ _ _ HRT)|].
    split; [exact (AsanRTInv.RT_shadow_rw _ _ _ HRT)|].
    split; [exact Hro|].
    split; [exact HGOT|]. split; [exact HCF1 | exact HCF2]. }
  (* sp is a 64-bit address *)
  assert (Hspb : 0 <= sp < 2 ^ 64).
  { pose proof Hwin as (Hwlo & Hwhi & _). unfold APPMEM_END in HspA. unfold AFw.SLOT_STACK in Hwlo. lia. }
  rewrite SEGS.
  eapply (sl_run_lib regs (Z_to_bv 64 0x81990) mem md
    (fun R pc' mem' =>
       (RcSynth.rw32 (rowb (istar (g_in g))) 56 = 0 /\ pc' = Z_to_bv 64 0x81ac8 /\ mem' = mem /\
        getr R 10 = Z_to_bv 64 0 /\
        getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
        getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 26 = getr regs 26 /\
        getr R 27 = Z_to_bv 64 (fr + 2688) /\ getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25) \/
       (RcSynth.rw32 (rowb (istar (g_in g))) 56 <> 0 /\ pc' = Z_to_bv 64 0x81ac0 /\
        getr R 10 = Z_to_bv 64 0 /\
        getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
        getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 26 = getr regs 26 /\
        getr R 27 = Z_to_bv 64 (fr + 2688) /\ getr R 22 = getr regs 22 /\ getr R 25 = getr regs 25 /\
        munch [(sp - STRCMP_WRAP_K, sp)] mem mem' /\ wmono rsegs mem mem' /\
        stk rsegs mem' (sp - FN_STACK) sp))
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    eapply evt_mono.
    + apply (r21_tail_evt SCMP) with (spv := sp) (lo := sp - FN_STACK) (A := A) (S5 := fr + 2176)
        (mr := mrow (g_in g)) (fw := fw_milli (RID (g_in g) 7)) (maj := major (RID (g_in g) 7))
        (mnr := minor (RID (g_in g) 7)) (pat := patch (RID (g_in g) 7))
        (h := RcSynth.rw32 (rowb (istar (g_in g))) 56) (nm := RcSynth.rname (rowb (istar (g_in g))))
        (w144 := fr + 2688) (sx := removelast (rt_nb (g_in g)));
        try assumption;
        try (unfold HIGHMEM_BEG, APPMEM_END, CAT, CAT_ROW, FN_STACK, AFw.SLOT_STACK in *; lia).
    + intros ms' [(E0 & R & Hms & P10 & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P27 & P22 & P25)
                 |(E0 & R & m' & Hms & P10 & P2 & P3 & P4 & P8 & P9 & P19 & P26 & P27 & P22 & P25 & MUq & WMq &
                   STq)].
      * exists R, (Z_to_bv 64 0x81ac8), mem. split; [exact Hms|]. left.
        split; [exact E0|]. split; [reflexivity|]. split; [reflexivity|].
        split; [exact P10|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
        split; [exact P8|]. split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P27|].
        split; [exact P22 | exact P25].
      * exists R, (Z_to_bv 64 0x81ac0), m'. split; [exact Hms|]. right.
        split; [exact E0|]. split; [reflexivity|].
        split; [exact P10|]. split; [exact P2|]. split; [exact P3|]. split; [exact P4|].
        split; [exact P8|]. split; [exact P9|]. split; [exact P19|]. split; [exact P26|]. split; [exact P27|].
        split; [exact P22|]. split; [exact P25|].
        split; [exact MUq|]. split; [exact WMq | exact STq].
  - intros R pc' mem' regs'' md' HK Hreg Hmat.
    destruct HK as [(E0 & Hpc & Hm & P10 & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K27 & K22 & K25)
                   |(E0 & Hpc & P10 & K2 & K3 & K4 & K8 & K9 & K19 & K26 & K27 & K22 & K25 & MUk & WMk & STk)].
    + subst pc' mem'.
      assert (HFRA' : FRA B APIf ra g fr [] regs'' mem md').
      { apply (sl_fra_move B APIf ra g fr [] regs regs'' mem md md' HFRA);
          [ rewrite Hreg; exact K2 | rewrite Hreg; exact K3 | rewrite Hreg; exact K4
          | rewrite Hreg; exact K8 | rewrite Hreg; exact K9 | rewrite Hreg; exact K19
          | rewrite Hreg; exact K26 | exact Hmat ]. }
      assert (HENT' : ENT APIf g [] mem md') by (eapply ent_mat; [exact HENT | exact Hmat]).
      rewrite <- SEGS. apply Hex70. exists regs'', mem, md', fr.
      split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
      split; [exact Hgn|]. split; [exact HOUR|].
      split; [exact (r21_cur_exit g regs regs'' HCUR ltac:(rewrite Hreg; exact K22)
                       ltac:(rewrite Hreg; exact K25) Ec0)|].
      (* PRO and [A + 144] (push 12A / 13B): memory is unchanged and s1 is kept *)
      assert (KS0 : forall off v, spill regs mem off v -> spill regs'' mem off v).
      { intros off v (A0 & HA0 & HQ0). exists A0.
        split; [unfold rg in HA0 |- *; rewrite Hreg, K9; exact HA0 | exact HQ0]. }
      split; [exact (r21_pro_keep g fr regs regs'' mem mem (fun off v _ H => KS0 off v H) (fun H => H)
                       (fun _ H => H) (fun _ H => H) HPRO)|].
      split; [exact (KS0 144 (fr + 2688) Hs144)|].
      split; [unfold a0v, rg; rewrite Hreg; exact P10|].
      split.
      { destruct HQ152 as (Q & HsQ & HQ1 & HQ2). exists Q.
        split; [|split; [exact HQ1 | exact HQ2]].
        destruct HsQ as (A0 & HA0 & HQ0). exists A0.
        split; [unfold rg in HA0 |- *; rewrite Hreg, K9; exact HA0 | exact HQ0]. }
      (* the record block (push 7B): memory is unchanged, s1 and s11 = fr + 2688 are kept *)
      assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
      apply (r21_p7_exit fr regs'' mem A ltac:(rewrite E9; exact Hr9) HAlo HAhi
               ltac:(unfold rg; rewrite Hreg; exact K27) HW208).
      exact (r21_p7_keep fr regs regs'' mem mem [] A Hr9 HAlo HAhi E9 (fun x _ => eq_refl) (fun x H => H)
               (fun _ _ => I) (fun _ _ => I) HP7).
    + subst pc'.
      assert (HFE : FRA B APIf ra g fr [] regs'' mem' md' /\ ENT APIf g [] mem' md').
      { apply (r21_callee_keep g fr [] regs regs'' mem mem' md md' STRCMP_WRAP_K HFRA HENT);
          [ rewrite Haspz; exact MUk | exact WMk | rewrite Haspz; exact STk
          | unfold STRCMP_WRAP_K, FN_STACK, AFw.SLOT_STACK; lia
          | destruct HFRWIN as [Hw|Hw];
            [left; exact Hw | right; unfold STRCMP_WRAP_K, FN_STACK, AFw.SLOT_STACK in *; lia]
          | rewrite Hreg; exact K2 | rewrite Hreg; exact K3 | rewrite Hreg; exact K4
          | rewrite Hreg; exact K8 | rewrite Hreg; exact K9 | rewrite Hreg; exact K19
          | rewrite Hreg; exact K26 | exact Hmat ]. }
      destruct HFE as (HFRA' & HENT').
      assert (Hwout : forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside [(sp - STRCMP_WRAP_K, sp)] x).
      { intros x Hx. cbn [Frame.outside]. split; [|exact I].
        destruct HFRWIN as [Hw|Hw]; rewrite Haspz in Hw;
          unfold STRCMP_WRAP_K, FN_STACK, AFw.SLOT_STACK in *; lia. }
      rewrite <- SEGS. apply Hex68. exists regs'', mem', md', fr.
      split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
      split; [exact Hgn|].
      split.
      { unfold OURb in HOUR |- *. apply (a_keep _ mem mem' _ _ MUk); [|exact HOUR].
        intros x Hx. apply Hwout. rewrite OUR_length in Hx. lia. }
      split; [exact (r21_cur_exit g regs regs'' HCUR ltac:(rewrite Hreg; exact K22)
                       ltac:(rewrite Hreg; exact K25) Ec0)|].
      (* PRO and [A + 144] (push 12A / 13B) across the strcmp wrapper: it writes only [sp - STRCMP_WRAP_K, sp),
         at or above HIGHMEM_BEG and below the spill area (sp <= A); our[]'s and the input block's shadow bytes
         are shadow memory, below the window; the input block is a live block of the entry heap (a_laws_blocks),
         below stklo <= sp - FN_STACK *)
      assert (EK : STRCMP_WRAP_K <= FN_STACK) by (unfold STRCMP_WRAP_K, FN_STACK, AFw.SLOT_STACK; lia).
      assert (HKlo : HIGHMEM_BEG <= sp - STRCMP_WRAP_K) by lia.
      assert (Hshw : forall x, app_mem x -> Frame.outside [(sp - STRCMP_WRAP_K, sp)] (shadow_addr x)).
      { intros x Hx. pose proof (shadow_of_app x Hx) as Hs. cbn [Frame.outside]. split; [|exact I].
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hs, HKlo. lia. }
      assert (INB : In (g_p g, g_n g) (g_H g) -> forall x, g_p g <= x < g_p g + g_n g ->
                Frame.outside [(sp - STRCMP_WRAP_K, sp)] x /\
                Frame.outside [(sp - STRCMP_WRAP_K, sp)] (shadow_addr x)).
      { intros Hin x Hx.
        destruct (r21_law_blocks ([] ++ g_H g) mem md (g_p g) (g_n g) HAH Hin)
          as (_ & _ & Hpend & _ & Hpb).
        destruct (Hpb x Hx) as (Happx & _).
        split; [|exact (Hshw x Happx)].
        cbn [Frame.outside]. split; [|exact I].
        lia. }
      split.
      { apply (r21_pro_keep g fr regs regs'' mem mem'); [| | | | exact HPRO].
        - intros off v Hoff Hs. pose proof (a_spill_A regs mem off v A Hr9 HAlo HAhi ltac:(lia) Hs) as HQ.
          exists A. split; [unfold rg; rewrite Hreg, K9; exact Hr9|].
          unfold q64 in HQ |- *. apply (a_keep _ mem mem' _ _ MUk); [|exact HQ].
          intros x Hx. rewrite length_le8 in Hx. cbn [Frame.outside]. split; [|exact I]. lia.
        - intros HA6. apply (a_addr_keep_rng mem mem' _ (fr + 2624) 6 HA6 MUk). intros i Hi.
          apply Hshw. apply Happ. lia.
        - intros Hin HIN. apply (a_keep _ mem mem' _ _ MUk); [|exact HIN].
          intros x Hx. rewrite <- g_n_len in Hx. exact (proj1 (INB (Hin ltac:(lia)) x Hx)).
        - intros Hin HA. apply (a_addr_keep_rng mem mem' _ (g_p g) (g_n g) HA MUk). intros i Hi.
          exact (proj2 (INB Hin (g_p g + i) ltac:(lia))). }
      split.
      { exists A. split; [unfold rg; rewrite Hreg, K9; exact Hr9|].
        unfold q64. apply (a_keep _ mem mem' _ _ MUk); [|exact HQ144].
        intros x Hx. rewrite length_le8 in Hx. cbn [Frame.outside]. split; [|exact I]. lia. }
      split; [unfold a0v, rg; rewrite Hreg; exact P10|].
      split.
      { destruct HQ152 as (Q & HsQ & HQ1 & HQ2).
        pose proof (a_spill_A regs mem 152 Q A Hr9 HAlo HAhi ltac:(lia) HsQ) as HQw.
        exists Q. split; [|split; [exact HQ1 | exact HQ2]].
        exists A. split; [unfold rg; rewrite Hreg, K9; exact Hr9|].
        unfold q64 in HQw |- *. apply (a_keep _ mem mem' _ _ MUk); [|exact HQw].
        intros x Hx. rewrite length_le8 in Hx. cbn [Frame.outside]. split; [|exact I]. lia. }
      (* the record block (push 7B): the strcmp wrapper writes only [sp - STRCMP_WRAP_K, sp), below the spill
         area (sp <= A) and apart from the frame; s1 and s11 = fr + 2688 are callee-saved *)
      assert (E9 : getr regs'' 9 = getr regs 9) by (rewrite Hreg; exact K9).
      apply (r21_p7_exit fr regs'' mem' A ltac:(rewrite E9; exact Hr9) HAlo HAhi
               ltac:(unfold rg; rewrite Hreg; exact K27)).
      * intros i Hi. exact (WMk (Z_to_bv 64 (A + 192 + i)) (HW208 i Hi)).
      * apply (r21_p7_keep fr regs regs'' mem mem' _ A Hr9 HAlo HAhi E9 MUk WMk); [|exact Hwout | exact HP7].
        intros x Hx. cbn [Frame.outside]. split; [|exact I]. lia.
Qed.

Lemma seg_R21 : forall b : nat,
  Hat B APIf ra (Inv_A815cc_at B APIf ra) (S b) ->
  Hcut B APIf ra (Inv_A81ac0 B APIf ra) ->
  Hcut B APIf ra (Inv_A81ac8 (fx:=fx) B APIf ra) ->
  Hat B APIf ra (Inv_A81924_at (fx:=fx) B APIf ra) b.
Proof. intros b H1 H2 H3. exact (seg_R21_latch b H1 (seg_R21_tail H2 H3)). Qed.
End R21W.
