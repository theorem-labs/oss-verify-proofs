From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts CommandModel CommandTac
  rec_code_declared_c rec_code_declared SlotSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* The Kind A runs of LLVMFuzzerTestOneInput (plain 0x14048, frame 176) stated in SlotSpec.v, except run_words. *)

Lemma sr_app_split : forall m A cs1 cs2, rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  destruct Hw as (Ha & Hn & Hw). rewrite cells_size_app in Hn, Hw.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia. apply Hw. lia.
Qed.

Lemma sr_swrap_small : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with (2^31) by reflexivity. replace (bv_modulus 32) with (2^32) by reflexivity.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma sr_wa_var : forall (m : word -> option byte) (x : word) bs,
  write_to_mem m x bs = write_to_mem m (wa (bv_unsigned x + Z.of_nat 0)) bs.
Proof. intros m x bs. f_equal. symmetry. apply wa_of_var. lia. Qed.



Lemma run_g_strnlen_ok : run_g_strnlen_spec.
Proof.
  unfold run_g_strnlen_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 3 step. apply evt_done. reflexivity.
Qed.

Lemma run_g_ca_ok : run_g_ca_spec.
Proof.
  unfold run_g_ca_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPR.
  do 2 step. apply evt_done. reflexivity.
Qed.

Lemma run_g_cw_ok : run_g_cw_spec.
Proof.
  unfold run_g_cw_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPR.
  do 2 step. apply evt_done. reflexivity.
Qed.

Lemma run_g_cr_ok : run_g_cr_spec.
Proof.
  unfold run_g_cr_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 step. apply evt_done. reflexivity.
Qed.

Lemma run_g_crt_ok : run_g_crt_spec.
Proof.
  unfold run_g_crt_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPR.
  do 4 step. apply evt_done. reflexivity.
Qed.

Lemma run_g_f1_ok : run_g_f1_spec.
Proof.
  unfold run_g_f1_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 step. apply evt_done. reflexivity.
Qed.

Lemma run_g_f2_ok : run_g_f2_spec.
Proof.
  unfold run_g_f2_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 step. apply evt_done. reflexivity.
Qed.

Lemma run_g_f3_ok : run_g_f3_spec.
Proof.
  unfold run_g_f3_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 step. apply evt_done. reflexivity.
Qed.

Lemma run_g_m0_ok : run_g_m0_spec.
Proof.
  unfold run_g_m0_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A0R.
  do 4 step. apply evt_done. reflexivity.
Qed.

Lemma run_g_m1_ok : run_g_m1_spec.
Proof.
  unfold run_g_m1_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m j
    MI IE SPR CJ.
  unfold IMG_END in IE.
  pose proof (munch_refl [(bv_unsigned sp + 40, bv_unsigned sp + 48)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step.
  apply evt_done. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma sr_arr_size : forall L0, 0 <= L0 <= 8192 ->
  Z.land (4 * L0) 18446744073709551608 = 8 * (L0 / 2).
Proof.
  intros L0 HL.
  assert (H : forallb (fun k => Z.eqb (Z.land (4 * k) 18446744073709551608) (8 * (k / 2)))
                (map Z.of_nat (seq 0 (Z.to_nat 8193))) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Z.eqb_eq. apply H.
  apply in_map_iff. exists (Z.to_nat L0). split; [lia|]. apply in_seq. lia.
Qed.

Lemma run_g_m2_ok : run_g_m2_spec.
Proof.
  unfold run_g_m2_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc m j L0
    MI IE SPR HL CJ.
  unfold IMG_END in IE.
  pose proof (munch_refl [(bv_unsigned sp + 48, bv_unsigned sp + 56)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 6 step.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split.
  { unfold arr_size. rewrite (unsigned_lit L0) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    rewrite (unsigned_lit (L0 * 2^2)) by lia. replace (L0 * 2^2) with (4 * L0) by lia.
    rewrite sr_arr_size by lia. reflexivity. }
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma run_tail_ok : run_tail_spec.
Proof.
  unfold run_tail_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S6 S01.
  pose proof (bv_unsigned_in_range 64 s6) as R6. unfold bv_modulus in R6. cbn in R6.
  step. if_cases HZ.
  - zify_cond HZ. step. apply evt_done. right. split; [lia|]. do 3 eexists. reflexivity.
  - zify_cond HZ. do 4 step. if_cases HB.
    + zify_cond HB. apply evt_done. left. split; [lia|]. split; [lia|].
      rewrite sr_swrap_small by lia. reflexivity.
    + zify_cond HB. step. apply evt_done. right. split; [lia|]. do 3 eexists. reflexivity.
Qed.

Lemma run_epi_ok : run_epi_spec.
Proof.
  unfold run_epi_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    ra0 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 jq MI IE SPR GQ QC SV.
  pose proof (munch_refl [(G_QUIT, G_QUIT + 4)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply bytes_ro8 in GQ.
  unfold GOT_GQUIT, G_QUIT, IMG_END, SAVE in *.
  do 3 step.
  do 16 step.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma run_big_ok : run_big_spec.
Proof.
  unfold run_big_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    MI ST LO IE BIG.
  unfold IMG_END in IE.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 176%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 176%nat junk [] [72; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR;
    [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 14 step. do 3 step. if_cases HZ.
  2: { exfalso. zify_cond HZ. rewrite Z.shiftr_div_pow2 in HZ by lia. Z.div_mod_to_equations. lia. }
  do 16 step.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma run_pro_ok : run_pro_spec.
Proof.
  unfold run_pro_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    MI ST LO IE SMALL.
  unfold IMG_END in IE.
  pose proof (bv_unsigned_in_range 64 a1) as RA1. unfold bv_modulus in RA1. cbn in RA1.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 176%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 176%nat junk [] [72; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR;
    [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 14 step. do 3 step. if_cases HZ.
  { exfalso. zify_cond HZ. rewrite Z.shiftr_div_pow2 in HZ by lia. Z.div_mod_to_equations. lia. }
  do 2 step.
  apply evt_done.
  match goal with H : rw_cells rsegs ?mm (bv_unsigned sp + -176) _ |- _ =>
    apply (sr_app_split mm (bv_unsigned sp + -176) [CB 72 (firstn 72 junk)] (SAVE ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) in H;
    destruct H as [FR1 FR2] end.
  cbn [cells_size csize Nat.add] in FR2.
  replace (bv_unsigned sp + -176 + Z.of_nat 72) with (bv_unsigned sp - 104) in FR2 by lia.
  do 17 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma run_init_ok : run_init_spec.
Proof.
  unfold run_init_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m jsh jl
    MI IE SPR GG GN GC SH JL.
  pose proof (munch_refl [(bv_unsigned sp, bv_unsigned sp + 24); (G_REC + 944, G_REC + 960)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  apply bytes_ro8 in GG, GN, GC.
  unfold GOT_GREC, G_REC, GOT_NCODES, NCODES_A, GOT_CODES, REC_CODES, IMG_END, LOC0, MASK in *.
  change (212296 + 944) with 213240 in *. change (212296 + 960) with 213256 in *.
  apply (rw_cells_split_CB rsegs _ _ [] 16%nat jsh [] [8; 8]%nat) in SH; [|reflexivity].
  apply (rw_cells_split_CB rsegs _ _ [] 40%nat jl [] [8; 8; 8; 16]%nat) in JL; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in SH, JL.
  do 5 step.
  step. if_cases HZ.
  - zify_cond HZ. step. apply evt_done.
    destruct (rw_cells_forget _ _ _ _ JL) as [jl' JL']. cbn [cells_size csize Nat.add] in JL'.
    do 17 eexists. exists [].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. left. split; [lia|]. reflexivity.
  - zify_cond HZ. do 8 step.
    match goal with H : rw_cells rsegs ?mm (bv_unsigned sp) _ |- _ =>
      assert (HS : store_ok rsegs mm sp 8 = true)
        by (eapply (rw_cells_store_ok_at rsegs mm (bv_unsigned sp) _ 0%nat);
            [exact H | reflexivity | reflexivity | symmetry; apply wa_of_var; lia]) end.
    step. clear HS. rewrite sr_wa_var. mem_after_store.
    do 3 step. apply evt_done.
    destruct (rw_cells_forget _ _ _ _ JL) as [jl' JL']. cbn [cells_size csize Nat.add] in JL'.
    do 3 eexists. exists (Z_to_bv 64 0). do 14 eexists.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. right. split; [lia|]. split; [eassumption|]. reflexivity.
Qed.

Lemma sr_ro_c1 : forall m A bs, bytes_at rsegs m A bs -> ro_cells rsegs m A (map C1 bs).
Proof.
  intros m A bs H. split.
  - clear H. induction bs as [|b bs IH]; cbn; [exact I|]. split; [exact I|exact IH].
  - replace (cells_bytes (map C1 bs)) with bs; [exact H|].
    clear H. induction bs as [|b bs IH]; cbn; [reflexivity|]. f_equal. exact IH.
Qed.

Lemma sr_nth_skipn : forall (l r : list Z) i v, skipn i l = v :: r -> nth i l 0 = v.
Proof.
  induction l as [|x l IH]; intros r i v H; destruct i as [|i]; cbn in H |- *; try discriminate.
  - inversion H; reflexivity.
  - eapply IH; exact H.
Qed.

Lemma sr_remw : forall h : byte,
  v_remw (Z_to_bv 64 (Z.shiftr (bv_unsigned (zxb h)) 1)) (Z_to_bv 64 58) =
  Z_to_bv 64 (Z.of_nat (Z.to_nat ((bv_unsigned h / 2) mod 58))).
Proof.
  intros h. pose proof (bv_unsigned_in_range 8 h) as R. unfold bv_modulus in R. cbn in R.
  unfold v_remw, zxb. rewrite (unsigned_lit (bv_unsigned h)) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
  replace (bv_wrap 32 (bv_unsigned (Z_to_bv 64 58)) =? 0) with false by reflexivity.
  replace (bv_swrap 32 (bv_unsigned (Z_to_bv 64 58))) with 58 by reflexivity.
  rewrite (unsigned_lit (bv_unsigned h / 2)) by (Z.div_mod_to_equations; lia).
  rewrite (sr_swrap_small (bv_unsigned h / 2)) by (Z.div_mod_to_equations; lia).
  rewrite Z.rem_mod_nonneg by (first [Z.div_mod_to_equations; lia | lia]).
  rewrite (sr_swrap_small ((bv_unsigned h / 2) mod 58)) by (Z.div_mod_to_equations; lia).
  rewrite Z2Nat.id by (Z.div_mod_to_equations; lia). reflexivity.
Qed.

Definition head_post (sp gp tp s4 s5 s10 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (mi p n : Z) (hdr : list byte) (sbw hbw : word) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR (Z_to_bv 64 0x14184) sp gp tp t0' t1' t2'
                    (Z_to_bv 64 (p + hdr_n n)) (Z_to_bv 64 (msg_len n hdr))
                    (Z_to_bv 64 (p + hdr_n n)) (Z_to_bv 64 (msg_len n hdr)) a2' a3' a4' a5' a6' a7'
                    sbw hbw s4 s5 (Z_to_bv 64 mi) (Z_to_bv 64 n) (Z_to_bv 64 (n - hdr_n n))
                    (Z_to_bv 64 MASK) s10 (Z_to_bv 64 32) t3' t4' t5' t6')
             F (Z_to_bv 64 0x14374) fc None m' (seg_rom rsegs) /\
      munch [(G_REC, G_REC + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' G_REC [C4 (Z_to_bv 64 (msg_rf hdr)); C4 (Z_to_bv 64 (msg_cd hdr))].

Lemma sr_zxb : forall h : byte, bv_unsigned (zxb h) = bv_unsigned h.
Proof.
  intros h. pose proof (bv_unsigned_in_range 8 h) as R. unfold bv_modulus in R. cbn in R.
  unfold zxb. apply unsigned_lit. lia.
Qed.

Lemma sr_hbyte_range : forall hdr k, 0 <= hbyte hdr k < 256.
Proof.
  intros hdr k. unfold hbyte. pose proof (bv_unsigned_in_range 8 (nth k hdr (Z_to_bv 8 0))) as R.
  unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma sr_lor_bytes : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 -> Z.lor (hi * 256) lo = lo + 256 * hi.
Proof.
  intros lo hi Hl Hh.
  assert (H : forallb (fun h => forallb (fun l => Z.eqb (Z.lor (h * 256) l) (l + 256 * h))
                 (map Z.of_nat (seq 0 (Z.to_nat 256)))) (map Z.of_nat (seq 0 (Z.to_nat 256))) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  assert (Ih : In hi (map Z.of_nat (seq 0 (Z.to_nat 256))))
    by (apply in_map_iff; exists (Z.to_nat hi); split; [lia|]; apply in_seq; lia).
  specialize (H hi Ih). rewrite forallb_forall in H.
  assert (Il : In lo (map Z.of_nat (seq 0 (Z.to_nat 256))))
    by (apply in_map_iff; exists (Z.to_nat lo); split; [lia|]; apply in_seq; lia).
  apply Z.eqb_eq. exact (H lo Il).
Qed.

Lemma sr_lor : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 ->
  Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 hi)) 8))) (bv_unsigned (Z_to_bv 64 lo)) =
  lo + 256 * hi.
Proof.
  intros lo hi Hl Hh.
  rewrite (unsigned_lit hi) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite (unsigned_lit (hi * 256)) by lia. rewrite (unsigned_lit lo) by lia.
  apply sr_lor_bytes; assumption.
Qed.

Lemma sr_m64_eq : forall n k, 0 < n <= 2 ^ 64 -> 0 < k < 2 ^ 64 -> n mod 18446744073709551616 = k -> n = k.
Proof.
  intros n k Hn Hk H. destruct (Z.eq_dec n (2 ^ 64)) as [E|E].
  - subst n. vm_compute in H. lia.
  - rewrite Z.mod_small in H by lia. exact H.
Qed.

Lemma sr_m64_ne : forall n k, 0 < n <= 2 ^ 64 -> 0 < k < 2 ^ 64 -> n mod 18446744073709551616 <> k -> n <> k.
Proof. intros n k Hn Hk H E. subst n. apply H. apply Z.mod_small. lia. Qed.

(* 0x14140 .. jal send_message: the code table read and the two stores into g_rec. *)
Lemma head_tail : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s8 s10 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (mi p n : Z) (h0 : byte) (hr jsv jrc : list byte) (sbw hbw : word),
  mem_inv rsegs m ->
  IMG_END <= bv_unsigned sp -> bv_unsigned sp + 176 <= 2 ^ 64 ->
  bytes_at rsegs m p (h0 :: hr) ->
  rw_cells rsegs m (bv_unsigned sp) (LOC0 jsv) ->
  rw_cells rsegs m G_REC [CB 8 jrc] ->
  bytes_at rsegs m (G_REC + 944) (le8 sbw) -> bytes_at rsegs m (G_REC + 952) (le8 hbw) ->
  s0 = Z_to_bv 64 (p + hdr_n n) -> s1 = Z_to_bv 64 (msg_len n (h0 :: hr)) -> s8 = Z_to_bv 64 (n - hdr_n n) ->
  evt rsegs (head_post sp gp tp s4 s5 s10 F fc m mi p n (h0 :: hr) sbw hbw)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p) s3 s4 s5 (Z_to_bv 64 mi)
             (Z_to_bv 64 n) s8 (Z_to_bv 64 MASK) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14140) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s8 s10 t3 t4 t5 t6 F fc m mi p n h0 hr jsv jrc
    sbw hbw MI IE SPR HB L0C GR SB HBW E0 E1 E8.
  unfold head_post.
  pose proof (munch_refl [(G_REC, G_REC + 8)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (rec_codes_in_image m MI) as RC.
  remember (Z.to_nat ((bv_unsigned h0 / 2) mod 58)) as i eqn:Ei.
  assert (IL : (i < 58)%nat).
  { subst i. pose proof (Z.mod_pos_bound (bv_unsigned h0 / 2) 58 ltac:(lia)). lia. }
  destruct (skipn i rec_codes) as [|v l] eqn:SK.
  { exfalso. pose proof (f_equal (@length Z) SK) as E. rewrite length_skipn, rec_codes_length in E. cbn in E. lia. }
  pose proof (code_read m i v l RC SK) as RD.
  pose proof (skipn_forall _ rec_codes l i v rec_codes_range SK) as Hv. cbv beta in Hv.
  assert (VCD : msg_cd (h0 :: hr) = v).
  { unfold msg_cd, hbyte. cbn [nth]. rewrite <- Ei. exact (sr_nth_skipn _ _ _ _ SK). }
  assert (VRF : msg_rf (h0 :: hr) = Z.land (bv_unsigned h0) 1).
  { unfold msg_rf, hbyte. cbn [nth]. symmetry. apply (Z.land_ones (bv_unsigned h0) 1). lia. }
  rewrite VCD, VRF. clear VCD VRF.
  apply bytes_ro8 in SB, HBW. apply sr_ro_c1 in HB. cbn [map] in HB.
  unfold LOC0, G_REC, REC_CODES, IMG_END, MASK in *.
  change (212296 + 944) with 213240 in *. change (212296 + 952) with 213248 in *. change (212296 + 8) with 212304 in *.
  apply (rw_cells_split_CB rsegs _ _ [] 8%nat jrc [] [4; 4]%nat) in GR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in GR.
  subst s0 s1 s8.
  do 4 step.
  rewrite sr_remw, <- Ei.
  do 3 step.
  replace (Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.of_nat i))) 2) with (4 * Z.of_nat i)
    by (rewrite unsigned_lit by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
  step.
  rewrite (sx32_lit v Hv).
  do 4 step. rewrite sr_zxb.
  do 5 step.
  apply evt_done. do 14 eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

(* 0x14124 .. 0x14140: the length min(min(lo + 256 hi, n - hdr_n n), 8192). *)
Lemma head_min : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s8 s10 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (mi p n : Z) (h0 : byte) (hr jsv jrc : list byte) (sbw hbw : word),
  mem_inv rsegs m ->
  IMG_END <= bv_unsigned sp -> bv_unsigned sp + 176 <= 2 ^ 64 ->
  0 < n -> n <= 2 ^ 64 ->
  bytes_at rsegs m p (h0 :: hr) ->
  rw_cells rsegs m (bv_unsigned sp) (LOC0 jsv) ->
  rw_cells rsegs m G_REC [CB 8 jrc] ->
  bytes_at rsegs m (G_REC + 944) (le8 sbw) -> bytes_at rsegs m (G_REC + 952) (le8 hbw) ->
  s0 = Z_to_bv 64 (p + hdr_n n) ->
  a0 = Z_to_bv 64 (hbyte (h0 :: hr) 1) -> a1 = Z_to_bv 64 (hbyte (h0 :: hr) 2) ->
  s8 = Z_to_bv 64 (n - hdr_n n) ->
  evt rsegs (head_post sp gp tp s4 s5 s10 F fc m mi p n (h0 :: hr) sbw hbw)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 p) s3 s4 s5 (Z_to_bv 64 mi)
             (Z_to_bv 64 n) s8 (Z_to_bv 64 MASK) s10 (Z_to_bv 64 32) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14124) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s8 s10 t3 t4 t5 t6 F fc m mi p n h0 hr jsv jrc
    sbw hbw MI IE SPR NP NR HB L0C GR SB HBW E0 EA0 EA1 E8.
  pose proof (sr_hbyte_range (h0 :: hr) 1) as R1.
  pose proof (sr_hbyte_range (h0 :: hr) 2) as R2.
  assert (RK : 0 <= n - hdr_n n < 2 ^ 64) by (unfold hdr_n; lia).
  subst a0 a1 s8.
  do 2 step.
  rewrite sr_lor by (apply sr_hbyte_range).
  step. if_cases HB1; zify_cond HB1.
  - do 2 step. if_cases HB2; zify_cond HB2.
    + eapply head_tail; try eassumption; [f_equal; unfold msg_len; lia | reflexivity].
    + step. eapply head_tail; try eassumption; [f_equal; unfold msg_len; lia | reflexivity].
  - do 3 step. if_cases HB2; zify_cond HB2.
    + eapply head_tail; try eassumption; [f_equal; unfold msg_len; lia | reflexivity].
    + step. eapply head_tail; try eassumption; [f_equal; unfold msg_len; lia | reflexivity].
Qed.

Lemma run_head_ok : run_head_spec.
Proof.
  unfold run_head_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s8 s10 t3 t4 t5 t6 F fc m mi p n hdr jsv jrc
    sbw hbw MI IE SPR MIR NP P0 PN HB HL L0C GR SB HBW.
  match goal with |- evt rsegs _ ?S => change (evt rsegs (head_post sp gp tp s4 s5 s10 F fc m mi p n hdr sbw hbw) S) end.
  assert (NR : n <= 2 ^ 64) by lia.
  destruct hdr as [|h0 hr]; [unfold hdr_n in HL; cbn [length] in HL; lia|].
  pose proof (sr_ro_c1 _ _ _ HB) as HBc. cbn [map] in HBc.
  do 3 step. if_cases HZ; zify_cond HZ.
  - apply sr_m64_ne in HZ; [|lia|lia].
    destruct hr as [|h1 hr]; [unfold hdr_n in HL; cbn [length] in HL; lia|]. cbn [map] in HBc.
    do 3 step. if_cases HZ2; zify_cond HZ2.
    + apply sr_m64_ne in HZ2; [|lia|lia].
      destruct hr as [|h2 hr]; [unfold hdr_n in HL; cbn [length] in HL; lia|]. cbn [map] in HBc.
      do 3 step.
      eapply head_min; try eassumption;
        first [reflexivity | (f_equal; unfold hdr_n; lia)].
    + apply sr_m64_eq in HZ2; [|lia|lia]. subst n.
      destruct hr as [|h2 hr]; [|unfold hdr_n in HL; cbn [length] in HL; lia].
      do 4 step.
      eapply head_min; try eassumption;
        first [reflexivity | (f_equal; unfold hdr_n; lia)].
  - apply sr_m64_eq in HZ; [|lia|lia]. subst n.
    destruct hr as [|h1 hr]; [|unfold hdr_n in HL; cbn [length] in HL; lia].
    do 5 step.
    eapply head_min; try eassumption;
      first [reflexivity | (f_equal; unfold hdr_n; lia)].
Qed.
